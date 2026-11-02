import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.Basic
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
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction

/-! Vocabulary for `EinsteinRelation.Diffusion.Basic`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory Filter

open scoped BigOperators Topology NNReal

namespace EinsteinRelation

/-- Continuous paths indexed by nonnegative real time. -/
abbrev Path (d : ℕ) := C(ℝ≥0, Vec d)

instance (d : ℕ) : MeasurableSpace (Path d) := borel (Path d)

instance (d : ℕ) : BorelSpace (Path d) := ⟨rfl⟩

/-- The coordinate process on continuous-path space. -/
def pathPosition {d : ℕ} (t : ℝ≥0) (γ : Path d) : Vec d := γ t

theorem measurable_pathPosition {d : ℕ} (t : ℝ≥0) :
    Measurable (pathPosition (d := d) t) :=
  (continuous_eval_const t).measurable

/-- The past σ-algebras of the canonical coordinate process. -/
noncomputable def pathFiltration (d : ℕ) : Filtration ℝ≥0 (borel (Path d)) :=
  Filtration.natural (pathPosition (d := d))
    (fun t => (measurable_pathPosition t).stronglyMeasurable)

/-- A test function minus its initial value and integrated generator. -/
noncomputable def compensatedTest {d : ℕ}
    (L : (Vec d → ℝ) → Vec d → ℝ) (f : Vec d → ℝ)
    (t : ℝ≥0) (γ : Path d) : ℝ :=
  f (γ t) - f (γ 0) - ∫ u in (0 : ℝ)..(t : ℝ), L f (γ u.toNNReal)

/-- The conservative martingale problem at the given starting point.
Integrability is explicit because the martingale predicate alone does not
include it in the pinned Mathlib version. -/

def SolvesMartingaleProblem {d : ℕ}
    (L : (Vec d → ℝ) → Vec d → ℝ) (x : Vec d) (P : Measure (Path d)) : Prop :=
  IsProbabilityMeasure P ∧ (∀ᵐ γ ∂P, γ 0 = x) ∧
  ∀ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
    (∀ t : ℝ≥0, ∀ᵐ γ ∂P,
      IntervalIntegrable (fun u : ℝ => L f (γ u.toNNReal)) volume 0 (t : ℝ)) ∧
    (∀ t, Integrable (compensatedTest L f t) P) ∧
    Martingale (compensatedTest L f) (pathFiltration d) P

/-- Quenched path laws, jointly measurable in starting point and environment. -/
abbrev QuenchedPathLaws (d : ℕ) := ProbabilityTheory.Kernel (Vec d × FieldPair d) (Path d)

/-- Restriction of a quenched path-law kernel to starting point zero. -/
def originLaw {d : ℕ} (P : QuenchedPathLaws d) :
    ProbabilityTheory.Kernel (FieldPair d) (Path d) :=
  P.comap (fun ω => (0, ω)) (measurable_const.prodMk measurable_id)

/-- Quenched path-law kernels indexed by force magnitude. -/
abbrev DiffusionFamily (d : ℕ) := ℝ → QuenchedPathLaws d

/-- The physical diffusion family, started at the origin, for almost every
environment at each nonnegative fixed force. -/
def IsPhysicalDiffusionFamily {d : ℕ} {Λ₀ r₀ : ℝ} (i : Fin d)
    (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d) : Prop :=
  ∀ lam : ℝ, 0 ≤ lam → ∀ᵐ ω ∂Q.measure,
    SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (P lam (0, ω))

/-- The pathwise velocity appearing in the law of large numbers. -/
def HasPathVelocity {d : ℕ} (γ : Path d) (v : Vec d) : Prop :=
  Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • γ t) atTop (𝓝 v)

/-- The quenched almost-sure limit, for almost every environment. -/
def HasQuenchedVelocity {d : ℕ} (Q : Measure (FieldPair d))
    (P : ProbabilityTheory.Kernel (FieldPair d) (Path d)) (v : Vec d) : Prop :=
  ∀ᵐ ω ∂Q, ∀ᵐ γ ∂P ω, HasPathVelocity γ v

/-- Diffusive scaling `ε γ(ε⁻² t)` of an actual continuous path. -/
noncomputable def rescalePath {d : ℕ} (ε : ℝ) (γ : Path d) : Path d :=
  ⟨fun t => ε • γ ((ε⁻¹ ^ 2).toNNReal * t), by
    first
      | fun_prop
      | exact continuous_const.fun_smul
          (γ.continuous.comp (continuous_const.fun_mul continuous_id))⟩

/-- The centered Brownian law with covariance `E[Wₜ ⊗ Wₜ] = t covariance`,
specified on continuous paths by all Gaussian finite-dimensional characteristic
functions. Symmetry excludes an invisible antisymmetric part of `covariance`. -/

def IsBrownianLaw {d : ℕ} (covariance : Mat d) (W : Measure (Path d)) : Prop :=
  IsProbabilityMeasure W ∧ covariance.transpose = covariance ∧
  (∀ ξ : Vec d, 0 ≤ dot ξ (covariance.mulVec ξ)) ∧ (∀ᵐ γ ∂W, γ 0 = 0) ∧
  ∀ (n : ℕ) (t : Fin n → ℝ≥0) (ξ : Fin n → Vec d),
    (∫ γ, Complex.exp (Complex.I * ((∑ k, dot (ξ k) (γ (t k))) : ℂ)) ∂W) =
      Complex.exp (((-(1 / 2 : ℝ)) *
        ∑ k, ∑ l, (min (t k) (t l) : ℝ) * dot (ξ k) (covariance.mulVec (ξ l))) : ℂ)

/-- The annealed unforced invariance principle in the topology of locally
uniform convergence on continuous paths. Tests are bounded continuous functions;
the force is fixed to zero before the diffusive scaling limit. -/
def HasDiffusivity {d : ℕ} (Q : Measure (FieldPair d))
    (P₀ : ProbabilityTheory.Kernel (FieldPair d) (Path d)) (covariance : Mat d) : Prop :=
  ∃ W : Measure (Path d), IsBrownianLaw covariance W ∧
    ∀ F : BoundedContinuousFunction (Path d) ℝ,
      Tendsto (fun ε : ℝ => ∫ ω, ∫ γ, F (rescalePath ε γ) ∂P₀ ω ∂Q)
        (𝓝[Set.Ioi 0] 0) (𝓝 (∫ γ, F γ ∂W))

end EinsteinRelation
