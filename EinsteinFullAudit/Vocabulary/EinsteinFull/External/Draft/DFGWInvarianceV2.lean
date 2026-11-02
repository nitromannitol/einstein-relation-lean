import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Order.Hom.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Diffusion.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction

/-! Vocabulary for `EinsteinFull.External.Draft.DFGWInvarianceV2`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinFull.External.Draft

open MeasureTheory ProbabilityTheory Filter EinsteinRelation

open scoped NNReal Topology

/-- A cadlag path `[0, ∞) → ℝᵈ`: right continuous with left limits. -/
structure CadlagPath (d : ℕ) where
  toFun : ℝ≥0 → Vec d
  right_continuous : ∀ t, ContinuousWithinAt toFun (Set.Ici t) t
  left_limit : ∀ t : ℝ≥0, 0 < t → ∃ l : Vec d, Tendsto toFun (𝓝[<] t) (𝓝 l)

/-- A continuous path as a cadlag path. -/
def Path.toCadlag {d : ℕ} (γ : Path d) : CadlagPath d where
  toFun := γ
  right_continuous _ := γ.continuous.continuousWithinAt
  left_limit t _ := ⟨γ t, γ.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩

/-- J1 convergence in `D([0,∞); ℝᵈ)` (Billingsley 1999, Theorem 16.1): there are increasing
homeomorphisms `λₙ` of `[0, ∞)` with `sup_t |λₙ t - t| → 0` and
`sup_{t ≤ T} ‖xₙ (λₙ t) - y t‖ → 0` for every `T`. -/
def SkorokhodTendsto {d : ℕ} (x : ℕ → CadlagPath d) (y : CadlagPath d) : Prop :=
  ∃ lam : ℕ → ℝ≥0 ≃o ℝ≥0,
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t : ℝ≥0, |((lam n t : ℝ≥0) : ℝ) - t| ≤ ε) ∧
    ∀ (T : ℝ≥0) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
      ‖(x n).toFun (lam n t) - y.toFun t‖ ≤ ε

/-- A test for weak convergence in `D`: bounded and J1-continuous. -/
def IsSkorokhodTest {d : ℕ} (F : CadlagPath d → ℝ) : Prop :=
  (∃ C : ℝ, ∀ x, |F x| ≤ C) ∧
    ∀ (x : ℕ → CadlagPath d) (y : CadlagPath d), SkorokhodTendsto x y →
      Tendsto (fun n => F (x n)) atTop (𝓝 (F y))

variable {S : Type*} [TopologicalSpace S]

/-- The Borel sigma-algebra on continuous trajectories. -/
instance dfgwTrajectoryMeasurableSpace : MeasurableSpace C(ℝ, S) := borel C(ℝ, S)

instance dfgwTrajectoryBorelSpace : BorelSpace C(ℝ, S) := ⟨rfl⟩

/-- The forward time shift of trajectories, `(θ_τ η)(t) = η(t + τ)`. -/
def dfgwShift (τ : ℝ) (η : C(ℝ, S)) : C(ℝ, S) :=
  η.comp ⟨fun t => t + τ, continuous_id.add continuous_const⟩

/-- The time reflection of trajectories about `τ`, `(R_τ η)(t) = η(2τ - t)`. -/
def dfgwRefl (τ : ℝ) (η : C(ℝ, S)) : C(ℝ, S) :=
  η.comp ⟨fun t => 2 * τ - t, continuous_const.sub continuous_id⟩

variable [mS : MeasurableSpace S]

/-- The sigma-algebra `F_I` of the coordinates at times in `I` (p.789). -/
def dfgwCoordSigma (I : Set ℝ) : MeasurableSpace C(ℝ, S) :=
  ⨆ t ∈ I, MeasurableSpace.comap (fun η : C(ℝ, S) => η t) mS

/-- The past filtration `F_(-∞, t]`, `t ≥ 0`. -/

def dfgwPast [BorelSpace S] : Filtration ℝ≥0 (dfgwTrajectoryMeasurableSpace (S := S)) where
  seq t := dfgwCoordSigma (Set.Iic (t : ℝ))
  mono' _ _ hst := iSup₂_le fun u hu =>
    le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Iic _) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η u) mS) u
      (Set.Iic_subset_Iic.2 (by exact_mod_cast hst) hu) le_rfl
  le' _ := iSup₂_le fun u _ =>
    (continuous_eval_const u).measurable.comap_le

/-- Section 2, pp.789–790, on the trajectory space: a stationary, reversible, ergodic Markov
process with invariant probability measure `μ` and transition kernels `T`. -/
structure IsDFGWTrajectoryProcess (P : Measure C(ℝ, S)) (μ : Measure S)
    (T : ℝ≥0 → Kernel S S) : Prop where
  probability : IsProbabilityMeasure P
  invariant_probability : IsProbabilityMeasure μ
  marginal : ∀ t, P.map (fun η : C(ℝ, S) => η t) = μ
  stationary : ∀ τ, P.map (dfgwShift τ) = P
  reversible : ∀ τ, P.map (dfgwRefl τ) = P
  markov_kernel : ∀ t, IsMarkovKernel (T t)
  markov : ∀ (t : ℝ≥0) (f : S → ℝ), Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
    P[fun η => f (η t) | dfgwCoordSigma (Set.Iic 0)] =ᵐ[P] fun η => ∫ y, f y ∂T t (η 0)
  ergodic : ∀ A : Set S, MeasurableSet A →
    (∀ t, ∀ᵐ x ∂μ, x ∈ A → T t x A = 1) → μ A = 0 ∨ μ A = 1

/-- Source (2.3)–(2.5) and A.1–A.4 on the trajectory space: an adapted, antisymmetric,
integrable, covariant and additive family `X a b`, `a ≤ b`, with a measurable continuous version
`Y` of `t ↦ X 0 t`. -/
structure IsDFGWTrajectoryFamily {d : ℕ} (P : Measure C(ℝ, S))
    (X : ℝ → ℝ → C(ℝ, S) → Vec d) (Y : C(ℝ, S) → Path d) : Prop where
  adapted : ∀ a b, a ≤ b → Measurable[dfgwCoordSigma (Set.Icc a b)] (X a b)
  antisymmetric : ∀ a b, a ≤ b →
    (fun η => X a b (dfgwRefl ((a + b) / 2) η)) =ᵐ[P] fun η => -X a b η
  integrable : ∀ a b, a ≤ b → Integrable (X a b) P
  covariant : ∀ a b τ, a ≤ b → (fun η => X a b (dfgwShift τ η)) =ᵐ[P] X (a + τ) (b + τ)
  additive : ∀ a b c, a ≤ b → b ≤ c → (fun η => X a b η + X b c η) =ᵐ[P] X a c
  version_measurable : Measurable Y
  version : ∀ᵐ η ∂P, ∀ t : ℝ≥0, Y η t = X 0 t η

/-- DRAFT literature input `external:DFGW#invariance`, V2: Theorem 2.2 of De Masi, Ferrari,
Goldstein and Wick (printed pp.801–802) with Remarks 1 and 3, on the continuous trajectory space.
Hypotheses: `S` second countable, the Borel sigma-algebra of `C(ℝ, S)` equal to the coordinate
sigma-algebra, and `L²(μ)` separable; (2.39), the mean forward velocity as a
strong L¹ limit; (2.40), the compensated process is a square-integrable martingale; part (ii),
the velocity is square integrable. Conclusions: the matrix `C` of (2.42) and `D` of (2.41), the
time integral of (2.41) converging absolutely (Remark 3), the limit (2.43), and convergence of the
laws of `ε X_[0, ε⁻² ·]` to Brownian motion with diffusion matrix `D` in the Skorokhod space. -/
def dfgwInvarianceStmtV2 : Prop :=
  ∀ (d : ℕ) (S : Type) [TopologicalSpace S] [SecondCountableTopology S] [MeasurableSpace S]
    [BorelSpace S] (P : Measure C(ℝ, S)) (μ : Measure S) (T : ℝ≥0 → Kernel S S)
    (X : ℝ → ℝ → C(ℝ, S) → Vec d) (Y : C(ℝ, S) → Path d),
    IsDFGWTrajectoryProcess P μ T →
    dfgwCoordSigma (S := S) Set.univ = dfgwTrajectoryMeasurableSpace (S := S) →
    TopologicalSpace.SeparableSpace (Lp ℝ 2 μ) →
    IsDFGWTrajectoryFamily P X Y →
    ∀ φ : S → Vec d, MemLp φ 2 μ →
    Tendsto (fun δ : ℝ => ∫ η, ‖δ⁻¹ • (P[X 0 δ | dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0) →
    (∀ t : ℝ≥0, MemLp (fun η => X 0 t η - ∫ τ in (0 : ℝ)..t, φ (η τ)) 2 P) →
    Martingale (fun (t : ℝ≥0) η => X 0 t η - ∫ τ in (0 : ℝ)..t, φ (η τ)) dfgwPast P →
    ∃ C D : Mat d,
      (∀ e : Vec d, dot e (C.mulVec e) =
        ∫ η, dot e (X 0 1 η - ∫ τ in (0 : ℝ)..1, φ (η τ)) ^ 2 ∂P) ∧
      (∀ i j : Fin d,
        IntegrableOn (fun t : ℝ => ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ) (Set.Ioi 0) ∧
        D i j = C i j - 2 * ∫ t in Set.Ioi (0 : ℝ),
          ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ) ∧
      (∀ (e : Vec d) (t : ℝ≥0), Tendsto
        (fun ε : ℝ => ∫ η, dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t)) ^ 2 ∂P)
        (𝓝[>] 0) (𝓝 (dot e (D.mulVec e) * t))) ∧
      ∃ W : Measure (Path d), IsBrownianLaw D W ∧
        ∀ F : CadlagPath d → ℝ, IsSkorokhodTest F →
          Tendsto (fun ε : ℝ => ∫ η, F (Path.toCadlag (rescalePath ε (Y η))) ∂P)
            (𝓝[>] 0) (𝓝 (∫ γ, F (Path.toCadlag γ) ∂W))

end EinsteinFull.External.Draft
