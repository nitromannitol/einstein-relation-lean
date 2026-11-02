import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.Regeneration.SupportedIntegralLocality
import EinsteinFull.Work.W1.GMPKilledSemigroupSupport
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import EinsteinFull.Work.W1.GMPDeterministicRestartSupport
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.GridLimit
import EinsteinRelation.Diffusion.CanonicalKernelStrongContinuitySupport
import EinsteinFull.Calculus.C8GMPRealizationExists
import MarkovProcess.Semigroup.Resolvent
import EinsteinFull.Work.W1.PhysicalCompactZeroBoundaryCoreSupport

/-!
Partial support for `app:factorization#past-kernel` (paper/main.tex:1499).
These results use the supplied regeneration coupling itself. Time-zero tests
have constant expectations, and tests supported below a negative level vanish
because the origin path starts at zero. Positive histories at nonnegative levels
still require locality for the weak divergence-form diffusion. For the supplied
GMP realization we prove nonnegative transition pairing symmetry, reversal of
finite equally spaced observation grids, and detailed balance for the actual
strict-survival killed law on every open domain at every time. The latter uses
closed-core approximation, decreasing dyadic grids, and physical σ-finite
exhaustion. The actual killed L² operator is self-adjoint on the full physical
space and the interior carrier. Its literal short-time quadratic forms are
nonnegative and increase under time halving. Twice the killed quotient bounds
the whole-space quotient; a datum with bounded killed quotients belongs to
the supplied weighted H¹ domain and the existing interior L² carrier.
Natural time dilation decreases these quotients. The supplied whole-space
energy bounds every finite dyadic product of projected transition steps,
uniformly in the number of monitoring times. These steps have the literal
endpoint-indicator representatives. Deterministic restart identifies every such
product with its literal path-grid expectation; closed-set dyadic grids converge
to continuous-path survival for every bounded Borel endpoint test. Iterating the
grid limit with an interior exhaustion recovers the actual strict-survival law
on every open domain. Consequently the actual killed form quotients of the
existing weighted H¹₀ domain are bounded by the literal physical energy at every
positive time. This follows first for the smooth interior span and then by closure
in the full weighted H¹ norm. The actual interior contraction semigroup has a
Laplace resolvent with uniform killed-quotient, full weighted H¹ energy, and
graph-norm bounds. On compact interior regions its H¹ representative belongs
to the existing H¹₀ domain of the larger open set. Strict survival in positively
separated interior regions increases to survival in the original domain, also
for endpoint-integrable tests. Bounded compact-interior H¹₀ lifts and
Banach–Alaoglu then put the actual killed resolvent, and every actual generator
domain vector, in the existing H¹₀ domain on every open set. Normalized actual
resolvents have shift-independent form bounds for data with bounded killed
quotients. Their strong limit proves that the actual killed form domain is
exactly the value image of the existing H¹₀ space. The mixed form identity and
identification with the variational evolution remain open.
-/

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- The actual supplied coupling starts at the origin on almost every fibre. -/
theorem regenerationCoupling_ae_origin_start
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ z ∂K (0, ω), z.1 0 = 0 := by
  filter_upwards [hK.2.1.1, hK.2.2.1] with ω hm hP
  obtain ⟨_, r, hr⟩ := hP
  have hstart : ∀ᵐ γ ∂P (0, ω), γ 0 = 0 := by
    rw [hr 0]
    exact r.pathLaw_starts_at 0
  rw [← hm] at hstart
  exact ae_of_ae_map measurable_fst.aemeasurable hstart

/-- The time-zero expectation is the literal value at the constant origin
history; the time step is arbitrary and no coin is observed. -/
theorem regenerationCoupling_integral_zero_history
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K)
    (Δ : ℝ≥0) (H : Regeneration.CoupledSample d → ℝ)
    (hH : Measurable[Regeneration.finiteHistorySigma Δ 0] H) :
    (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q.measure]
      fun _ => H (⟨fun _ => 0, continuous_const⟩, fun _ => false) := by
  filter_upwards [hK.1.1,
    regenerationCoupling_ae_origin_start hd Q lam l δ h₀ h₁ P K hK] with ω hp hs
  let : IsProbabilityMeasure (K (0, ω)) := hp
  exact Regeneration.integral_zero_history_eq Δ (K (0, ω)) 0 hs H hH

/-- The exact past-kernel locality conclusion holds at history length zero,
with the original joint-field sigma algebra and buffer. -/
theorem regenerationCoupling_past_kernel_zero_history
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K)
    (v : ℝ) (H : Regeneration.CoupledSample d → ℝ)
    (hH : Measurable[Regeneration.finiteHistorySigma
      (Regeneration.Renewal.regenDelta lam) 0] H) :
    ∃ A : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d |
        x (Regeneration.Renewal.forceCoord hd) ≤ v + 3 * (l / lam)}] A ∧
      (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q.measure] A := by
  exact ⟨_, measurable_const,
    regenerationCoupling_integral_zero_history hd Q lam l δ h₀ h₁ P K hK _ H hH⟩

/-- At every finite history length, a test supported strictly below the
starting level has the zero local version under the supplied coupling. -/
theorem regenerationCoupling_past_kernel_negative_level
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K)
    (m : ℕ) (v : ℝ) (hv : v < 0) (H : Regeneration.CoupledSample d → ℝ)
    (hsupport : ∀ z, (¬ ∀ t : ℝ≥0,
      t ≤ (m : ℝ≥0) * Regeneration.Renewal.regenDelta lam →
        z.1 t (Regeneration.Renewal.forceCoord hd) ≤ v) → H z = 0) :
    ∃ A : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d |
        x (Regeneration.Renewal.forceCoord hd) ≤ v + 3 * (l / lam)}] A ∧
      (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q.measure] A := by
  refine ⟨fun _ => 0, measurable_const, ?_⟩
  filter_upwards [regenerationCoupling_ae_origin_start hd Q lam l δ h₀ h₁ P K hK]
    with ω hstart
  apply integral_eq_zero_of_ae
  filter_upwards [hstart] with z hz
  apply hsupport z
  intro hbelow
  have hzero := hbelow 0 zero_le
  rw [hz] at hzero
  exact (not_le_of_gt hv) hzero

end EinsteinFull.Blueprint

namespace EinsteinFull

open EinsteinRelation EinsteinRelation.Diffusion ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
  {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
  (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)

/-- Detailed balance transports the transition of a restricted physical measure
to a density with respect to the same physical measure. -/
theorem gmpTransition_restrict_bind (t : ℝ≥0) (A : Set (Vec d))
    (hA : MeasurableSet A) :
    ((physicalReversibleMeasure ω hd lam).restrict A).bind (G.transitionKernel t) =
      (physicalReversibleMeasure ω hd lam).withDensity
        (fun y => G.transitionKernel t y A) := by
  ext B hB
  rw [Measure.bind_apply hB (Kernel.aemeasurable _), withDensity_apply _ hB]
  exact G.transitionKernel_reversible t A B hA hB

/-- Setwise detailed balance for the supplied transition law extends to every
nonnegative measurable terminal test, including tests of infinite integral. -/
theorem gmpTransition_setLIntegral_symm (t : ℝ≥0) (A : Set (Vec d))
    (hA : MeasurableSet A) (g : Vec d → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in A, ∫⁻ y, g y ∂G.transitionKernel t x
      ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ y, g y * G.transitionKernel t y A ∂physicalReversibleMeasure ω hd lam := by
  have h := congrArg (fun μ : Measure (Vec d) => ∫⁻ y, g y ∂μ)
    (gmpTransition_restrict_bind G t A hA)
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (Kernel.measurable_coe _ hA) hg] at h
  simpa only [Pi.mul_apply, mul_comm] using h

/-- The actual GMP transition operators are symmetric on all nonnegative
measurable tests, for the actual physical reversible measure. -/
theorem gmpTransition_lintegral_symm (t : ℝ≥0)
    (f g : Vec d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * (∫⁻ y, g y ∂G.transitionKernel t x)
      ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ y, g y * (∫⁻ x, f x ∂G.transitionKernel t y)
        ∂physicalReversibleMeasure ω hd lam := by
  let := G.transitionKernel_isMarkovKernel t
  have hmeasure : ((physicalReversibleMeasure ω hd lam).withDensity f).bind
      (G.transitionKernel t) = (physicalReversibleMeasure ω hd lam).withDensity
        (fun y => ∫⁻ x, f x ∂G.transitionKernel t y) := by
    ext B hB
    rw [Measure.bind_apply hB (Kernel.aemeasurable _), withDensity_apply _ hB,
      lintegral_withDensity_eq_lintegral_mul _ hf (Kernel.measurable_coe _ hB)]
    exact (gmpTransition_setLIntegral_symm G t B hB f hf).symm
  have h := congrArg (fun μ : Measure (Vec d) => ∫⁻ y, g y ∂μ) hmeasure
  have hmf : Measurable (fun y => ∫⁻ x, f x ∂G.transitionKernel t y) :=
    Measurable.lintegral_kernel_prod_right' (hf.comp measurable_snd)
  have hmg : Measurable (fun x => ∫⁻ y, g y ∂G.transitionKernel t x) :=
    Measurable.lintegral_kernel_prod_right' (hg.comp measurable_snd)
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hf hmg,
    lintegral_withDensity_eq_lintegral_mul _ hmf hg] at h
  simpa only [Pi.mul_apply, mul_comm] using h

/-- One actual transition, retained only when both grid endpoints lie in `V`.
This is a discrete observation operator, not the continuous exit-killed law. -/
def gmpGridStep (V : Set (Vec d)) (t : ℝ≥0) (f : Vec d → ℝ≥0∞) :
    Vec d → ℝ≥0∞ :=
  V.indicator (fun x => ∫⁻ y in V, f y ∂G.transitionKernel t x)

/-- Measurability of the actual transition with two endpoint restrictions. -/
theorem measurable_gmpGridStep (V : Set (Vec d)) (hV : MeasurableSet V)
    (t : ℝ≥0) (f : Vec d → ℝ≥0∞) (hf : Measurable f) :
    Measurable (gmpGridStep G V t f) := by
  let := G.transitionKernel_isMarkovKernel t
  unfold gmpGridStep
  apply Measurable.indicator _ hV
  simp_rw [← lintegral_indicator hV]
  exact Measurable.lintegral_kernel_prod_right'
    ((hf.indicator hV).comp measurable_snd)

/-- Retaining both endpoints preserves the supplied physical detailed balance. -/
theorem gmpGridStep_lintegral_symm (V : Set (Vec d)) (hV : MeasurableSet V)
    (t : ℝ≥0) (f g : Vec d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * gmpGridStep G V t g x ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ x, g x * gmpGridStep G V t f x ∂physicalReversibleMeasure ω hd lam := by
  have htest (a b : Vec d → ℝ≥0∞) :
      (fun x => a x * gmpGridStep G V t b x) =
        (fun x => V.indicator a x *
          (∫⁻ y, V.indicator b y ∂G.transitionKernel t x)) := by
    funext x
    rw [lintegral_indicator hV]
    by_cases hx : x ∈ V <;> simp [gmpGridStep, hx]
  rw [htest f g, htest g f]
  exact gmpTransition_lintegral_symm G t _ _ (hf.indicator hV) (hg.indicator hV)

/-- Every finite equally spaced observation grid has physical reversal
symmetry. The number of steps, time increment, and observation set are arbitrary. -/
theorem gmpGridStep_iterate_lintegral_symm (V : Set (Vec d)) (hV : MeasurableSet V)
    (t : ℝ≥0) (n : ℕ) (f g : Vec d → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * (gmpGridStep G V t)^[n] g x
      ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ x, g x * (gmpGridStep G V t)^[n] f x
        ∂physicalReversibleMeasure ω hd lam := by
  have hm (k : ℕ) (a : Vec d → ℝ≥0∞) (ha : Measurable a) :
      Measurable ((gmpGridStep G V t)^[k] a) := by
    induction k with
    | zero => exact ha
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact measurable_gmpGridStep G V hV t _ ih
  induction n generalizing f g with
  | zero => exact lintegral_congr fun x => mul_comm _ _
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    calc
      _ = ∫⁻ x, gmpGridStep G V t g x * (gmpGridStep G V t)^[n] f x
          ∂physicalReversibleMeasure ω hd lam :=
        ih f _ hf (measurable_gmpGridStep G V hV t g hg)
      _ = ∫⁻ x, (gmpGridStep G V t)^[n] f x * gmpGridStep G V t g x
          ∂physicalReversibleMeasure ω hd lam :=
        lintegral_congr fun x => mul_comm _ _
      _ = ∫⁻ x, g x * gmpGridStep G V t ((gmpGridStep G V t)^[n] f) x
          ∂physicalReversibleMeasure ω hd lam :=
        gmpGridStep_lintegral_symm G V hV t _ g (hm n f hf) hg
      _ = _ := by rw [Function.iterate_succ_apply']

/-- An actual finite path observation, including both grid endpoints. -/
def gmpGridEvent (V : Set (Vec d)) (t : ℝ≥0) (A : Set (Vec d)) : ℕ → Set (Path d)
  | 0 => (pathPosition 0) ⁻¹' (V ∩ A)
  | n + 1 => (pathPosition 0) ⁻¹' V ∩ (gmpShiftPath t) ⁻¹' gmpGridEvent V t A n

/-- Every finite path grid event is measurable. -/
theorem measurableSet_gmpGridEvent (V : Set (Vec d)) (hV : MeasurableSet V)
    (t : ℝ≥0) (A : Set (Vec d)) (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet (gmpGridEvent V t A n) := by
  induction n with
  | zero => exact (measurable_pathPosition 0) (hV.inter hA)
  | succ n ih =>
    exact ((measurable_pathPosition 0) hV).inter ((measurable_gmpShiftPath t) ih)

/-- Restricting an actual fibre by its initial position is a literal indicator
at the supplied starting point. -/
theorem gmpPathLaw_start_restrict (V : Set (Vec d)) (E : Set (Path d)) (x : Vec d) :
    G.pathLaw x ((pathPosition 0) ⁻¹' V ∩ E) =
      V.indicator (fun y => G.pathLaw y E) x := by
  classical
  have heq : (pathPosition 0) ⁻¹' V ∩ E =ᵐ[G.pathLaw x]
      (if x ∈ V then E else ∅) := by
    filter_upwards [G.pathLaw_starts_at x] with γ hγ
    by_cases hx : x ∈ V <;> simp [hγ, hx]
  rw [measure_congr heq]
  by_cases hx : x ∈ V <;> simp [hx]

/-- The actual FDD-derived deterministic restart identifies one further
finite observation with one application of the supplied transition kernel. -/
theorem gmpGridEvent_succ_probability (V : Set (Vec d)) (hV : MeasurableSet V)
    (t : ℝ≥0) (A : Set (Vec d)) (hA : MeasurableSet A) (n : ℕ) (x : Vec d) :
    G.pathLaw x (gmpGridEvent V t A (n + 1)) =
      V.indicator (fun z => ∫⁻ y, G.pathLaw y (gmpGridEvent V t A n)
        ∂G.transitionKernel t z) x := by
  rw [gmpGridEvent, gmpPathLaw_start_restrict]
  have heq (z : Vec d) : G.pathLaw z ((gmpShiftPath t) ⁻¹' gmpGridEvent V t A n) =
      ∫⁻ y, G.pathLaw y (gmpGridEvent V t A n) ∂G.transitionKernel t z := by
    rw [← Measure.map_apply (measurable_gmpShiftPath t)
      (measurableSet_gmpGridEvent V hV t A hA n),
      ← Kernel.map_apply _ (measurable_gmpShiftPath t), gmpPathLaw_map_shift,
      Kernel.comp_apply' _ _ _ (measurableSet_gmpGridEvent V hV t A hA n)]
  simp_rw [heq]

/-- Actual grid probabilities vanish outside their required initial set. -/
theorem gmpGridEvent_probability_indicator (V : Set (Vec d))
    (t : ℝ≥0) (A : Set (Vec d)) (k : ℕ) :
    V.indicator (fun y => G.pathLaw y (gmpGridEvent V t A k)) =
      (fun y => G.pathLaw y (gmpGridEvent V t A k)) := by
    funext y
    by_cases hy : y ∈ V
    · exact Set.indicator_of_mem hy _
    · rw [Set.indicator_of_notMem hy]
      have hsub : gmpGridEvent V t A k ⊆ (pathPosition 0) ⁻¹' V ∩ Set.univ := by
        cases k with
        | zero => exact fun γ hγ => ⟨hγ.1, Set.mem_univ _⟩
        | succ k => exact fun γ hγ => ⟨hγ.1, Set.mem_univ _⟩
      have hz := measure_mono (μ := G.pathLaw y) hsub
      rw [gmpPathLaw_start_restrict, Set.indicator_of_notMem hy] at hz
      exact (le_antisymm hz bot_le).symm

/-- Actual finite-grid probabilities are precisely the iterates whose physical
reversal symmetry was proved above. This uses the supplied path FDDs through
the already proved deterministic restart, rather than an additional Markov premise. -/
theorem gmpGridEvent_probability_eq_iterate (V : Set (Vec d)) (hV : MeasurableSet V)
    (t : ℝ≥0) (A : Set (Vec d)) (hA : MeasurableSet A) (n : ℕ) :
    (fun x => G.pathLaw x (gmpGridEvent V t A n)) =
      (gmpGridStep G V t)^[n] (V.indicator (A.indicator (fun _ => 1))) := by
  let := G.pathLaw_isMarkovKernel
  induction n with
  | zero =>
    funext x
    change G.pathLaw x ((pathPosition 0) ⁻¹' (V ∩ A)) = _
    rw [← Measure.map_apply (measurable_pathPosition 0) (hV.inter hA),
      G.pathLaw_endpoint, G.transitionKernel_zero, Kernel.id_apply,
      Measure.dirac_apply' x (hV.inter hA)]
    by_cases hv : x ∈ V <;> by_cases ha : x ∈ A <;>
      simp [hv, ha]
  | succ n ih =>
    funext x
    rw [gmpGridEvent_succ_probability G V hV t A hA n x,
      Function.iterate_succ_apply', ← ih]
    simp only [gmpGridStep]
    simp_rw [← lintegral_indicator hV, gmpGridEvent_probability_indicator]

/-- Detailed balance for actual finite-grid path observations, under the
actual physical reversible measure, with no extra symmetry premise. -/
theorem gmpGridEvent_physical_balance (V : Set (Vec d)) (hV : MeasurableSet V)
    (t : ℝ≥0) (n : ℕ) (A B : Set (Vec d))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ x in A, G.pathLaw x (gmpGridEvent V t B n)
      ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ x in B, G.pathLaw x (gmpGridEvent V t A n)
        ∂physicalReversibleMeasure ω hd lam := by
  have hpair (C D : Set (Vec d)) (hC : MeasurableSet C) :
      (∫⁻ x in C, G.pathLaw x (gmpGridEvent V t D n)
        ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ x, V.indicator (C.indicator (fun _ => 1)) x *
        G.pathLaw x (gmpGridEvent V t D n) ∂physicalReversibleMeasure ω hd lam := by
    rw [← lintegral_indicator hC]
    apply lintegral_congr
    intro x
    have hp := congrFun (gmpGridEvent_probability_indicator G V t D n) x
    by_cases hv : x ∈ V <;> by_cases hc : x ∈ C <;>
      simp [hv, hc] at hp ⊢
    all_goals simp_all
  rw [hpair A B hA, hpair B A hB]
  simp_rw [congrFun (gmpGridEvent_probability_eq_iterate G V hV t B hB n),
    congrFun (gmpGridEvent_probability_eq_iterate G V hV t A hA n)]
  exact gmpGridStep_iterate_lintegral_symm G V hV t n _ _
    ((measurable_const.indicator hA).indicator hV)
    ((measurable_const.indicator hB).indicator hV)

/-- Closed inner approximations of the open killing domain. -/
def gmpSurvivalCore (U : Set (Vec d)) (n : ℕ) : Set (Vec d) :=
  (Metric.thickening (1 / (n + 1 : ℝ)) Uᶜ)ᶜ

/-- Every inner approximation is closed. -/
theorem isClosed_gmpSurvivalCore (U : Set (Vec d)) (n : ℕ) :
    IsClosed (gmpSurvivalCore U n) :=
  Metric.isOpen_thickening.isClosed_compl

/-- The inner approximations lie in the actual killing domain. -/
theorem gmpSurvivalCore_subset (U : Set (Vec d)) (n : ℕ) :
    gmpSurvivalCore U n ⊆ U := by
  intro x hx
  by_contra hout
  exact hx (Metric.self_subset_thickening (by positivity) Uᶜ hout)

/-- The closed inner approximations increase to the open domain. -/
theorem monotone_gmpSurvivalCore (U : Set (Vec d)) : Monotone (gmpSurvivalCore U) := by
  intro m n hmn x hx hn
  apply hx
  exact Metric.thickening_mono (by gcongr) Uᶜ hn

/-- Strict survival of the actual continuous path is a countable increasing
union of closed-core survival events. The closed interval includes both endpoints. -/
theorem localitySurvival_iff_exists_core (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (γ : Path d) :
    (t : ℝ≥0∞) < localityExitTime U γ ↔
      ∃ n : ℕ, ∀ s : ℝ≥0, s ≤ t → γ s ∈ gmpSurvivalCore U n := by
  rw [lt_localityExitTime_iff U hU]
  constructor
  · intro hsurv
    let C := γ '' Set.Icc 0 t
    have hC : IsCompact C := isCompact_Icc.image γ.continuous
    have hCU : C ⊆ U := by
      rintro _ ⟨s, hs, rfl⟩
      exact hsurv s hs.2
    obtain ⟨ε, hε, hsep⟩ := hCU.disjoint_compl_right.exists_thickenings hC hU.isClosed_compl
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨n, fun s hs => ?_⟩
    intro hbad
    exact Set.disjoint_left.mp hsep
      (Metric.self_subset_thickening hε C ⟨s, ⟨bot_le, hs⟩, rfl⟩)
      (Metric.thickening_mono hn.le Uᶜ hbad)
  · rintro ⟨n, hn⟩ s hs
    exact gmpSurvivalCore_subset U n (hn s hs)

/-- Each closed-core survival condition is a closed event on continuous paths. -/
theorem isClosed_gmpCoreSurvival (U : Set (Vec d)) (n : ℕ) (t : ℝ≥0) :
    IsClosed {γ : Path d | ∀ s : ℝ≥0, s ≤ t → γ s ∈ gmpSurvivalCore U n} := by
  simpa only [Set.MapsTo, Set.mem_Icc, zero_le, true_and] using
    ContinuousMap.isClosed_setOfPred_mapsTo (isClosed_gmpSurvivalCore U n) (Set.Icc 0 t)

/-- The actual strict-survival endpoint measure is the increasing supremum of
closed-core endpoint measures. No transition-law identification is assumed. -/
theorem gmpKilledEndpointKernel_eq_iSup_core (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d) (A : Set (Vec d)) (hA : MeasurableSet A) :
    gmpKilledEndpointKernel G U hU t x A =
      ⨆ n : ℕ, G.pathLaw x
        ((pathPosition t) ⁻¹' A ∩
          {γ : Path d | ∀ s : ℝ≥0, s ≤ t → γ s ∈ gmpSurvivalCore U n}) := by
  rw [gmpKilledEndpointKernel_apply, Measure.map_apply (measurable_pathPosition t) hA,
    Measure.restrict_apply ((measurable_pathPosition t) hA)]
  have heq : (pathPosition t) ⁻¹' A ∩
      {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ} =
      ⋃ n : ℕ, (pathPosition t) ⁻¹' A ∩
        {γ : Path d | ∀ s : ℝ≥0, s ≤ t → γ s ∈ gmpSurvivalCore U n} := by
    ext γ
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      Set.mem_iUnion, localitySurvival_iff_exists_core U hU t γ]
    constructor
    · rintro ⟨ha, n, hn⟩
      exact ⟨n, ha, hn⟩
    · rintro ⟨n, ha, hn⟩
      exact ⟨ha, n, hn⟩
  rw [heq]
  apply Monotone.measure_iUnion
  intro m n hmn γ hγ
  exact ⟨hγ.1, fun s hs => monotone_gmpSurvivalCore U hmn (hγ.2 s hs)⟩

/-- Closed-core survival is determined by any dense sequence in the time
interval; closedness is essential here. -/
theorem gmpCoreSurvival_iff_dense (U : Set (Vec d)) (n : ℕ) (t : ℝ≥0)
    (q : ℕ → Set.Icc (0 : ℝ≥0) t) (hq : DenseRange q) (γ : Path d) :
    (∀ s : ℝ≥0, s ≤ t → γ s ∈ gmpSurvivalCore U n) ↔
      ∀ k : ℕ, γ (q k) ∈ gmpSurvivalCore U n := by
  constructor
  · intro h k
    exact h (q k) (q k).property.2
  · intro h s hs
    exact hq.induction_on (p := fun r => γ r.val ∈ gmpSurvivalCore U n)
      ⟨s, bot_le, hs⟩
      ((isClosed_gmpSurvivalCore U n).preimage
        (γ.continuous.comp continuous_subtype_val)) h

/-- An explicit finite-observation approximation of the actual exit-killed
law. The supremum is over inner cores and the infimum over increasing finite
prefixes of a dense sequence; no symmetry or locality premise is introduced. -/
theorem gmpKilledEndpointKernel_eq_iSup_iInf_grid
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (q : ℕ → Set.Icc (0 : ℝ≥0) t) (hq : DenseRange q)
    (x : Vec d) (A : Set (Vec d)) (hA : MeasurableSet A) :
    gmpKilledEndpointKernel G U hU t x A =
      ⨆ n : ℕ, ⨅ m : ℕ, G.pathLaw x
        ((pathPosition t) ⁻¹' A ∩
          {γ : Path d | ∀ k : ℕ, k ≤ m → γ (q k) ∈ gmpSurvivalCore U n}) := by
  let := G.pathLaw_isMarkovKernel
  rw [gmpKilledEndpointKernel_eq_iSup_core G U hU t x A hA]
  congr 1
  funext n
  have heq : (pathPosition t) ⁻¹' A ∩
      {γ : Path d | ∀ s : ℝ≥0, s ≤ t → γ s ∈ gmpSurvivalCore U n} =
      ⋂ m : ℕ, (pathPosition t) ⁻¹' A ∩
        {γ : Path d | ∀ k : ℕ, k ≤ m → γ (q k) ∈ gmpSurvivalCore U n} := by
    ext γ
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iInter,
      gmpCoreSurvival_iff_dense U n t q hq γ]
    constructor
    · rintro ⟨ha, hk⟩ m
      exact ⟨ha, fun k _ => hk k⟩
    · intro h
      exact ⟨(h 0).1, fun k => (h k).2 k le_rfl⟩
  rw [heq]
  apply Antitone.measure_iInter
  · intro m m' hmm' γ hγ
    exact ⟨hγ.1, fun k hk => hγ.2 k (hk.trans hmm')⟩
  · intro m
    apply MeasurableSet.nullMeasurableSet
    apply ((measurable_pathPosition t) hA).inter
    simpa only [Set.ofPred_forall, Set.preimage, pathPosition] using
      (MeasurableSet.iInter fun k => MeasurableSet.iInter fun (_ : k ≤ m) =>
        (measurable_pathPosition (q k)) (isClosed_gmpSurvivalCore U n).measurableSet)
  · exact ⟨0, measure_ne_top _ _⟩

open Filter Topology
open SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift

/-- The recursive actual grid event observes precisely the equally spaced
positions, including the initial point and the terminal endpoint. -/
theorem gmpGridEvent_iff (V : Set (Vec d)) (t : ℝ≥0) (A : Set (Vec d))
    (n : ℕ) (γ : Path d) :
    γ ∈ gmpGridEvent V t A n ↔
      (∀ k : ℕ, k ≤ n → γ ((k : ℝ≥0) * t) ∈ V) ∧ γ ((n : ℝ≥0) * t) ∈ A := by
  induction n generalizing γ with
  | zero => simp [gmpGridEvent, pathPosition]
  | succ n ih =>
    change (γ 0 ∈ V ∧ gmpShiftPath t γ ∈ gmpGridEvent V t A n) ↔ _
    rw [ih]
    have hadd (k : ℕ) : t + (k : ℝ≥0) * t = (k + 1 : ℕ) * t := by
      push_cast
      ring
    simp only [gmpShiftPath, ContinuousMap.coe_mk, hadd]
    constructor
    · rintro ⟨hzero, hgrid, hend⟩
      refine ⟨?_, hend⟩
      intro k hk
      cases k with
      | zero => simpa using hzero
      | succ k => exact hgrid k (Nat.le_of_succ_le_succ hk)
    · rintro ⟨hgrid, hend⟩
      exact ⟨by simpa using hgrid 0 (Nat.zero_le _),
        (fun k hk => hgrid (k + 1) (Nat.succ_le_succ hk)), hend⟩

/-- A dyadic observation of the actual path, with a specified terminal set. -/
def gmpDyadicEvent (V : Set (Vec d)) (t : ℝ≥0) (A : Set (Vec d))
    (m : ℕ) : Set (Path d) :=
  (pathPosition t) ⁻¹' A ∩
    {γ | ∀ k : ℕ, k ≤ 2 ^ m → γ (dyadicTime t m k) ∈ V}

/-- A dyadic observation is the equal-spacing actual grid with exactly `2^m` steps. -/
theorem gmpDyadicEvent_eq_grid (V : Set (Vec d)) (t : ℝ≥0)
    (A : Set (Vec d)) (m : ℕ) :
    gmpDyadicEvent V t A m = gmpGridEvent V (t / (2 ^ m : ℕ)) A (2 ^ m) := by
  have htime (k : ℕ) (hk : k ≤ 2 ^ m) :
      dyadicTime t m k = (k : ℝ≥0) * (t / (2 ^ m : ℕ)) := by
    simp only [dyadicTime, min_eq_left hk]
    ring
  have hend : ((2 ^ m : ℕ) : ℝ≥0) * (t / (2 ^ m : ℕ)) = t := by
    field_simp
  ext γ
  rw [gmpGridEvent_iff]
  change (γ t ∈ A ∧ ∀ k : ℕ, k ≤ 2 ^ m → γ (dyadicTime t m k) ∈ V) ↔ _
  simp only [hend]
  constructor
  · rintro ⟨ha, hv⟩
    exact ⟨fun k hk => htime k hk ▸ hv k hk, ha⟩
  · rintro ⟨hv, ha⟩
    exact ⟨ha, fun k hk => (htime k hk).symm ▸ hv k hk⟩

/-- Finite dyadic path observations are measurable. -/
theorem measurableSet_gmpDyadicEvent (V : Set (Vec d)) (hV : MeasurableSet V)
    (t : ℝ≥0) (A : Set (Vec d)) (hA : MeasurableSet A) (m : ℕ) :
    MeasurableSet (gmpDyadicEvent V t A m) := by
  rw [gmpDyadicEvent_eq_grid]
  exact measurableSet_gmpGridEvent V hV _ A hA _

/-- Refining a dyadic grid retains all previous observations. -/
theorem antitone_gmpDyadicEvent (V : Set (Vec d)) (t : ℝ≥0)
    (A : Set (Vec d)) : Antitone (gmpDyadicEvent V t A) := by
  apply antitone_nat_of_succ_le
  intro m γ hγ
  refine ⟨hγ.1, fun k hk => ?_⟩
  have hle : 2 * k ≤ 2 ^ (m + 1) := by
    rw [pow_succ]
    omega
  simpa only [dyadicTime_succ_two_mul] using hγ.2 (2 * k) hle

/-- Closed-set survival of a continuous actual path is exactly survival at all
nested dyadic grids. The endpoint test is retained throughout the limit. -/
theorem gmpClosedSurvival_eq_iInter_dyadic (V : Set (Vec d)) (hV : IsClosed V)
    (t : ℝ≥0) (A : Set (Vec d)) :
    (pathPosition t) ⁻¹' A ∩ {γ : Path d | ∀ s : ℝ≥0, s ≤ t → γ s ∈ V} =
      ⋂ m : ℕ, gmpDyadicEvent V t A m := by
  ext γ
  constructor
  · rintro ⟨ha, hsurv⟩
    exact Set.mem_iInter.mpr fun m => ⟨ha, fun k _ => hsurv _ (dyadicTime_le t m k)⟩
  · intro hγ
    have hgrid := Set.mem_iInter.mp hγ
    refine ⟨(hgrid 0).1, fun s hs => ?_⟩
    choose k hkle hk using fun m => exists_dyadicTime_close t m hs
    have hzero : Tendsto (fun m : ℕ => (t : ℝ) / 2 ^ m) atTop (𝓝 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
      have h' := h.const_mul (t : ℝ)
      simpa [div_pow, div_eq_mul_inv] using h'
    have htime : Tendsto (fun m => dyadicTime t m (k m)) atTop (𝓝 s) := by
      rw [← NNReal.tendsto_coe, tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun m => dist_nonneg) (fun m => ?_) hzero
      rw [Real.dist_eq]
      exact hk m
    exact hV.mem_of_tendsto ((γ.continuous.tendsto s).comp htime)
      (Eventually.of_forall fun m => (hgrid m).2 (k m) (hkle m))

/-- The actual closed-survival endpoint probability is the decreasing limit
of actual dyadic-grid probabilities. -/
theorem gmpClosedSurvival_probability_eq_iInf (V : Set (Vec d)) (hV : IsClosed V)
    (t : ℝ≥0) (x : Vec d) (A : Set (Vec d)) (hA : MeasurableSet A) :
    G.pathLaw x ((pathPosition t) ⁻¹' A ∩
      {γ : Path d | ∀ s : ℝ≥0, s ≤ t → γ s ∈ V}) =
      ⨅ m : ℕ, G.pathLaw x (gmpDyadicEvent V t A m) := by
  let := G.pathLaw_isMarkovKernel
  rw [gmpClosedSurvival_eq_iInter_dyadic V hV]
  exact (antitone_gmpDyadicEvent V t A).measure_iInter
    (fun m => (measurableSet_gmpDyadicEvent V hV.measurableSet t A hA m).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩

/-- On a finite physical start set, decreasing dyadic survival probabilities
can be passed through the physical integral. -/
theorem gmpClosedSurvival_lintegral_eq_iInf (V : Set (Vec d)) (hV : IsClosed V)
    (t : ℝ≥0) (A B : Set (Vec d)) (hB : MeasurableSet B)
    (hAfin : physicalReversibleMeasure ω hd lam A ≠ ∞) :
    (∫⁻ x in A, G.pathLaw x ((pathPosition t) ⁻¹' B ∩
      {γ : Path d | ∀ s : ℝ≥0, s ≤ t → γ s ∈ V})
      ∂physicalReversibleMeasure ω hd lam) =
      ⨅ m : ℕ, ∫⁻ x in A, G.pathLaw x (gmpDyadicEvent V t B m)
        ∂physicalReversibleMeasure ω hd lam := by
  let := G.pathLaw_isMarkovKernel
  simp_rw [gmpClosedSurvival_probability_eq_iInf G V hV t _ B hB]
  apply lintegral_iInf
  · intro m
    exact G.pathLaw.measurable_coe (measurableSet_gmpDyadicEvent V hV.measurableSet t B hB m)
  · intro m n hmn x
    exact measure_mono (antitone_gmpDyadicEvent V t B hmn)
  · apply ne_top_of_le_ne_top hAfin
    calc
      _ ≤ ∫⁻ _ in A, (1 : ℝ≥0∞) ∂physicalReversibleMeasure ω hd lam :=
        lintegral_mono fun _ => prob_le_one
      _ = _ := by simp

/-- Actual closed-survival path probabilities retain physical detailed balance
on finite physical start and end sets. -/
theorem gmpClosedSurvival_physical_balance_of_finite (V : Set (Vec d)) (hV : IsClosed V)
    (t : ℝ≥0) (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAfin : physicalReversibleMeasure ω hd lam A ≠ ∞)
    (hBfin : physicalReversibleMeasure ω hd lam B ≠ ∞) :
    (∫⁻ x in A, G.pathLaw x ((pathPosition t) ⁻¹' B ∩
      {γ : Path d | ∀ s : ℝ≥0, s ≤ t → γ s ∈ V})
      ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ x in B, G.pathLaw x ((pathPosition t) ⁻¹' A ∩
        {γ : Path d | ∀ s : ℝ≥0, s ≤ t → γ s ∈ V})
        ∂physicalReversibleMeasure ω hd lam := by
  rw [gmpClosedSurvival_lintegral_eq_iInf G V hV t A B hB hAfin,
    gmpClosedSurvival_lintegral_eq_iInf G V hV t B A hA hBfin]
  apply iInf_congr
  intro m
  simp_rw [gmpDyadicEvent_eq_grid]
  exact gmpGridEvent_physical_balance G V hV.measurableSet _ _ A B hA hB

/-- Increasing closed cores recover the physical integral of the actual
strict-survival endpoint kernel, including infinite integrals. -/
theorem gmpKilledEndpointKernel_lintegral_eq_iSup_core (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (A B : Set (Vec d)) (hB : MeasurableSet B) :
    (∫⁻ x in A, gmpKilledEndpointKernel G U hU t x B
      ∂physicalReversibleMeasure ω hd lam) =
      ⨆ n : ℕ, ∫⁻ x in A, G.pathLaw x ((pathPosition t) ⁻¹' B ∩
        {γ : Path d | ∀ s : ℝ≥0, s ≤ t → γ s ∈ gmpSurvivalCore U n})
        ∂physicalReversibleMeasure ω hd lam := by
  simp_rw [gmpKilledEndpointKernel_eq_iSup_core G U hU t _ B hB]
  apply lintegral_iSup
  · intro n
    exact G.pathLaw.measurable_coe (((measurable_pathPosition t) hB).inter
      (isClosed_gmpCoreSurvival U n t).measurableSet)
  · intro m n hmn x
    apply measure_mono
    intro γ hγ
    exact ⟨hγ.1, fun s hs => monotone_gmpSurvivalCore U hmn (hγ.2 s hs)⟩

/-- Detailed balance for the actual killed endpoint law on finite physical
sets, obtained from actual path observations rather than an association premise. -/
theorem gmpKilledEndpointKernel_physical_balance_of_finite (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAfin : physicalReversibleMeasure ω hd lam A ≠ ∞)
    (hBfin : physicalReversibleMeasure ω hd lam B ≠ ∞) :
    (∫⁻ x in A, gmpKilledEndpointKernel G U hU t x B
      ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ x in B, gmpKilledEndpointKernel G U hU t x A
        ∂physicalReversibleMeasure ω hd lam := by
  rw [gmpKilledEndpointKernel_lintegral_eq_iSup_core G U hU t A B hB,
    gmpKilledEndpointKernel_lintegral_eq_iSup_core G U hU t B A hA]
  apply iSup_congr
  intro n
  exact gmpClosedSurvival_physical_balance_of_finite G _
    (isClosed_gmpSurvivalCore U n) t A B hA hB hAfin hBfin

/-- The actual GMP endpoint kernel killed on an arbitrary open set satisfies
detailed balance for the actual physical reversible measure, at every time.
No association of the killed law with a variational evolution is assumed. -/
theorem gmpKilledEndpointKernel_physical_balance (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ x in A, gmpKilledEndpointKernel G U hU t x B
      ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ x in B, gmpKilledEndpointKernel G U hU t x A
        ∂physicalReversibleMeasure ω hd lam := by
  let μ := physicalReversibleMeasure ω hd lam
  let K := gmpKilledEndpointKernel G U hU t
  let : SigmaFinite μ := physicalReversibleMeasure_sigmaFinite hd ω lam
  have hmono (C : Set (Vec d)) : Monotone (fun n => C ∩ spanningSets μ n) := by
    intro m n hmn
    exact Set.inter_subset_inter_right C (monotone_spanningSets μ hmn)
  have hunion (C : Set (Vec d)) : (⋃ n : ℕ, C ∩ spanningSets μ n) = C := by
    rw [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
  have hstart (C : Set (Vec d)) (f : Vec d → ℝ≥0∞) :
      (∫⁻ x in C, f x ∂μ) = ⨆ n : ℕ, ∫⁻ x in C ∩ spanningSets μ n, f x ∂μ := by
    conv_lhs => rw [← hunion C]
    exact setLIntegral_iUnion_of_directed f (hmono C).directed_le
  have hend (C D : Set (Vec d)) (hD : MeasurableSet D) :
      (∫⁻ x in C, K x D ∂μ) =
        ⨆ n : ℕ, ∫⁻ x in C, K x (D ∩ spanningSets μ n) ∂μ := by
    have heq (x : Vec d) : K x D = ⨆ n : ℕ, K x (D ∩ spanningSets μ n) := by
      rw [← (hmono D).measure_iUnion, hunion D]
    simp_rw [heq]
    apply lintegral_iSup
    · intro n
      exact K.measurable_coe (hD.inter (measurableSet_spanningSets μ n))
    · intro m n hmn x
      exact measure_mono (hmono D hmn)
  have hfinite (C : Set (Vec d)) (n : ℕ) : μ (C ∩ spanningSets μ n) ≠ ∞ :=
    ne_top_of_le_ne_top (measure_spanningSets_lt_top μ n).ne
      (measure_mono Set.inter_subset_right)
  change (∫⁻ x in A, K x B ∂μ) = ∫⁻ x in B, K x A ∂μ
  calc
    _ = ⨆ m : ℕ, ⨆ n : ℕ,
        ∫⁻ x in A ∩ spanningSets μ m, K x (B ∩ spanningSets μ n) ∂μ := by
      rw [hstart A]
      exact iSup_congr fun m => hend _ B hB
    _ = ⨆ m : ℕ, ⨆ n : ℕ,
        ∫⁻ x in B ∩ spanningSets μ n, K x (A ∩ spanningSets μ m) ∂μ := by
      apply iSup_congr
      intro m
      apply iSup_congr
      intro n
      exact gmpKilledEndpointKernel_physical_balance_of_finite G U hU t _ _
        (hA.inter (measurableSet_spanningSets μ m))
        (hB.inter (measurableSet_spanningSets μ n)) (hfinite A m) (hfinite B n)
    _ = ⨆ n : ℕ, ⨆ m : ℕ,
        ∫⁻ x in B ∩ spanningSets μ n, K x (A ∩ spanningSets μ m) ∂μ := iSup_comm
    _ = ∫⁻ x in B, K x A ∂μ := by
      rw [hstart B]
      exact iSup_congr fun n => (hend _ A hA).symm

/-- The actual killed endpoint law is reversible in the standard kernel API. -/
theorem gmpKilledEndpointKernel_isReversible (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) :
    Kernel.IsReversible (gmpKilledEndpointKernel G U hU t)
      (physicalReversibleMeasure ω hd lam) := by
  intro A B hA hB
  exact gmpKilledEndpointKernel_physical_balance G U hU t A B hA hB

/-- Finite-measure indicators have their literal killed-probability representative,
including at time zero. -/
theorem gmpKilledL2_indicatorConst_ae_eq (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (B : Set (Vec d)) (hB : MeasurableSet B)
    (hBfin : physicalReversibleMeasure ω hd lam B ≠ ∞) (c : ℝ) :
    gmpKilledL2Operator G U hU t (indicatorConstLp 2 hB hBfin c) =ᵐ[
      physicalReversibleMeasure ω hd lam]
      fun x => (gmpKilledEndpointKernel G U hU t x B).toReal * c := by
  let := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  filter_upwards [gmpKilledL2_ae_eq G U hU t (indicatorConstLp 2 hB hBfin c),
    ae_ae_gmpKilledEndpointKernel_of_ae G U hU t
      (indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := hBfin) (c := c))] with x hx hinput
  change gmpKilledL2 G U hU t (indicatorConstLp 2 hB hBfin c) x = _
  rw [hx, integral_congr_ae hinput, integral_indicator hB]
  simp only [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]

/-- Detailed balance gives symmetry on finite-measure indicator functions. -/
theorem gmpKilledL2_inner_indicatorConst_symm (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAfin : physicalReversibleMeasure ω hd lam A ≠ ∞)
    (hBfin : physicalReversibleMeasure ω hd lam B ≠ ∞) (a b : ℝ) :
    ⟪gmpKilledL2Operator G U hU t (indicatorConstLp 2 hA hAfin a),
      indicatorConstLp 2 hB hBfin b⟫_ℝ =
    ⟪indicatorConstLp 2 hA hAfin a,
      gmpKilledL2Operator G U hU t (indicatorConstLp 2 hB hBfin b)⟫_ℝ := by
  let μ := physicalReversibleMeasure ω hd lam
  let K := gmpKilledEndpointKernel G U hU t
  let := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  have hpair (C D : Set (Vec d)) (hC : MeasurableSet C) (hD : MeasurableSet D)
      (hCfin : μ C ≠ ∞) (hDfin : μ D ≠ ∞) (c e : ℝ) :
      ⟪indicatorConstLp 2 hC hCfin c,
        gmpKilledL2Operator G U hU t (indicatorConstLp 2 hD hDfin e)⟫_ℝ =
      c * e * (∫⁻ x in C, K x D ∂μ).toReal := by
    rw [L2.inner_indicatorConstLp_eq_inner_setIntegral ℝ]
    have hrep := gmpKilledL2_indicatorConst_ae_eq G U hU t D hD hDfin e
    rw [integral_congr_ae (ae_restrict_of_ae hrep), integral_mul_const]
    rw [integral_toReal ((K.measurable_coe hD).aemeasurable)
      (Filter.Eventually.of_forall fun x => measure_lt_top (K x) D)]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [real_inner_comm, hpair B A hB hA hBfin hAfin b a,
    hpair A B hA hB hAfin hBfin a b,
    gmpKilledEndpointKernel_physical_balance G U hU t A B hA hB]
  ring

/-- The actual killed expectation is symmetric on the whole physical L² space. -/
theorem gmpKilledL2Operator_isSymmetric (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) :
    (gmpKilledL2Operator G U hU t).toLinearMap.IsSymmetric := by
  let T := gmpKilledL2Operator G U hU t
  have hclosed (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
      IsClosed {f | ⟪T f, g⟫_ℝ = ⟪f, T g⟫_ℝ} :=
    isClosed_eq (T.continuous.inner continuous_const)
      (continuous_id.inner continuous_const)
  have hind (A : Set (Vec d)) (hA : MeasurableSet A)
      (hAfin : physicalReversibleMeasure ω hd lam A ≠ ∞) (a : ℝ) :
      ∀ g, ⟪T (indicatorConstLp 2 hA hAfin a), g⟫_ℝ =
        ⟪indicatorConstLp 2 hA hAfin a, T g⟫_ℝ := by
    refine Lp.induction (by norm_num)
      (fun g => ⟪T (indicatorConstLp 2 hA hAfin a), g⟫_ℝ =
        ⟪indicatorConstLp 2 hA hAfin a, T g⟫_ℝ) ?_ ?_ ?_
    · intro b B hB hBfin
      exact gmpKilledL2_inner_indicatorConst_symm G U hU t A B hA hB hAfin hBfin.ne a b
    · intro f g hf hg _ ihf ihg
      simp only [map_add, inner_add_right, ihf, ihg]
    · exact isClosed_eq (continuous_const.inner continuous_id)
        (continuous_const.inner T.continuous)
  intro f g
  refine Lp.induction (by norm_num)
    (fun f => ⟪T f, g⟫_ℝ = ⟪f, T g⟫_ℝ) ?_ ?_ (hclosed g) f
  · intro a A hA hAfin
    exact hind A hA hAfin.ne a g
  · intro f₁ f₂ hf₁ hf₂ _ ih₁ ih₂
    simp only [map_add, inner_add_left, ih₁, ih₂]

/-- The actual killed physical L² contraction is self-adjoint. -/
theorem gmpKilledL2Operator_isSelfAdjoint (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) : IsSelfAdjoint (gmpKilledL2Operator G U hU t) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (gmpKilledL2Operator_isSymmetric G U hU t)

/-- Symmetry holds on the exact carrier of the zero-boundary evolution. -/
theorem gmpKilledInteriorOperator_isSymmetric (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) :
    (gmpKilledInteriorOperator G U hU t).toLinearMap.IsSymmetric := by
  intro f g
  exact gmpKilledL2Operator_isSymmetric G U hU t f.val g.val

/-- The killed operator is self-adjoint on the exact interior carrier as well. -/
theorem gmpKilledInteriorOperator_isSelfAdjoint (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) : IsSelfAdjoint (gmpKilledInteriorOperator G U hU t) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (gmpKilledInteriorOperator_isSymmetric G U hU t)

/-- Actual killed correlations are the squared norms at half time. -/
theorem gmpKilledL2_inner_eq_half_norm_sq (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ⟪gmpKilledL2Operator G U hU t f, f⟫_ℝ =
      ‖gmpKilledL2Operator G U hU (t / 2) f‖ ^ 2 := by
  have htime : t / 2 + t / 2 = t := add_halves t
  have hcomp := gmpKilledL2Operator_add_time G U hU (t / 2) (t / 2)
  rw [htime] at hcomp
  rw [hcomp, ContinuousLinearMap.comp_apply]
  exact (gmpKilledL2Operator_isSymmetric G U hU (t / 2)
    (gmpKilledL2Operator G U hU (t / 2) f) f).trans (real_inner_self_eq_norm_sq _)

/-- The killed contraction is nonnegative as a quadratic operator. -/
theorem gmpKilledL2_inner_nonneg (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    0 ≤ ⟪gmpKilledL2Operator G U hU t f, f⟫_ℝ := by
  rw [gmpKilledL2_inner_eq_half_norm_sq]
  positivity

/-- The actual killed quadratic difference is nonnegative. -/
theorem gmpKilledL2_inner_sub_nonneg (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    0 ≤ ⟪f - gmpKilledL2Operator G U hU t f, f⟫_ℝ := by
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  have h := (real_inner_le_norm (gmpKilledL2Operator G U hU t f) f).trans
    (mul_le_mul_of_nonneg_right (gmpKilledL2_norm_le G U hU t f) (norm_nonneg f))
  nlinarith

/-- The literal short-time kernel form equals the actual L² quadratic form. -/
theorem gmpKilledFormDifferenceQuotient_eq_inner (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) t f =
      (1 / (t : ℝ)) * ⟪f - gmpKilledL2Operator G U hU t f, f⟫_ℝ := by
  unfold semigroupFormDifferenceQuotient
  congr 1
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f (gmpKilledL2Operator G U hU t f),
    gmpKilledL2_ae_eq G U hU t f] with x hsub hrep
  change _ = inner ℝ ((f - gmpKilledL2Operator G U hU t f) x) (f x)
  rw [hsub]
  change _ = inner ℝ (f x - gmpKilledL2 G U hU t f x) (f x)
  rw [hrep]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The actual killed form difference quotient has the expected sign at every time. -/
theorem gmpKilledFormDifferenceQuotient_nonneg (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    0 ≤ semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel G U hU) t f := by
  rw [gmpKilledFormDifferenceQuotient_eq_inner]
  exact mul_nonneg (by positivity) (gmpKilledL2_inner_sub_nonneg G U hU t f)

/-- The killed quadratic difference controls the actual L² displacement. -/
theorem gmpKilledL2_norm_sub_sq_le_inner (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖f - gmpKilledL2Operator G U hU t f‖ ^ 2 ≤
      2 * ⟪f - gmpKilledL2Operator G U hU t f, f⟫_ℝ := by
  rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq,
    real_inner_comm f]
  have hn : ‖gmpKilledL2Operator G U hU t f‖ ≤ ‖f‖ :=
    gmpKilledL2_norm_le G U hU t f
  have hp := norm_nonneg (gmpKilledL2Operator G U hU t f)
  nlinarith

/-- Halving time increases the actual killed form difference quotient. -/
theorem gmpKilledFormDifferenceQuotient_double_le (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) (t + t) f ≤
      semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) t f := by
  rw [gmpKilledFormDifferenceQuotient_eq_inner, gmpKilledFormDifferenceQuotient_eq_inner]
  have he : ⟪gmpKilledL2Operator G U hU (t + t) f, f⟫_ℝ =
      ‖gmpKilledL2Operator G U hU t f‖ ^ 2 := by
    rw [gmpKilledL2Operator_add_time, ContinuousLinearMap.comp_apply]
    exact (gmpKilledL2Operator_isSymmetric G U hU t
      (gmpKilledL2Operator G U hU t f) f).trans (real_inner_self_eq_norm_sq _)
  rw [inner_sub_left, inner_sub_left, real_inner_self_eq_norm_sq, he]
  have hnorm := sq_nonneg ‖f - gmpKilledL2Operator G U hU t f‖
  rw [norm_sub_sq_real, real_inner_comm (gmpKilledL2Operator G U hU t f) f] at hnorm
  have htpos : 0 < (t : ℝ) := ht
  rw [NNReal.coe_add]
  field_simp
  nlinarith

/-- Reflecting the survival contribution is dominated by the whole endpoint expectation. -/
theorem abs_two_mul_integral_gmpKilled_sub_transition_le (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d) (f : Vec d → ℝ) (hf : Measurable f)
    (hi : Integrable f (G.transitionKernel t x)) :
    |2 * (∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) -
      ∫ y, f y ∂G.transitionKernel t x| ≤ ∫ y, |f y| ∂G.transitionKernel t x := by
  let S := {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ}
  have hS : MeasurableSet S := measurableSet_localitySurvival U hU t
  have hF : Integrable (fun γ => f (pathPosition t γ)) (G.pathLaw x) := by
    rw [← G.pathLaw_endpoint t x] at hi
    exact (integrable_map_measure hf.aestronglyMeasurable
      (measurable_pathPosition t).aemeasurable).mp hi
  have hsplit := integral_add_compl hS hF
  have habs := integral_add_compl hS hF.norm
  rw [integral_gmpKilledEndpointKernel G U hU t x f hf, integral_indicator hS,
    ← G.pathLaw_endpoint t x,
    integral_map (measurable_pathPosition t).aemeasurable hf.aestronglyMeasurable,
    integral_map (measurable_pathPosition t).aemeasurable (by simpa only [Real.norm_eq_abs] using hf.norm.aestronglyMeasurable)]
  calc
    _ = |(∫ γ in S, f (pathPosition t γ) ∂G.pathLaw x) -
        ∫ γ in Sᶜ, f (pathPosition t γ) ∂G.pathLaw x| := by congr 1; linarith
    _ ≤ |∫ γ in S, f (pathPosition t γ) ∂G.pathLaw x| +
        |∫ γ in Sᶜ, f (pathPosition t γ) ∂G.pathLaw x| := abs_sub _ _
    _ ≤ (∫ γ in S, |f (pathPosition t γ)| ∂G.pathLaw x) +
        ∫ γ in Sᶜ, |f (pathPosition t γ)| ∂G.pathLaw x := by
      simpa only [Real.norm_eq_abs] using add_le_add
        (norm_integral_le_integral_norm (μ := (G.pathLaw x).restrict S)
          (fun γ => f (pathPosition t γ)))
        (norm_integral_le_integral_norm (μ := (G.pathLaw x).restrict Sᶜ)
          (fun γ => f (pathPosition t γ)))
    _ = _ := by simpa only [Real.norm_eq_abs] using habs

/-- The supplied whole-space L² action retains its literal endpoint integral. -/
theorem gmpTransitionL2_ae_eq (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    G.kernelL2Action hd hL t f =ᵐ[physicalReversibleMeasure ω hd lam]
      fun x => ∫ y, f y ∂G.transitionKernel t x := by
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    physicalReversibleMeasure_sigmaFinite hd ω lam
  let := G.transitionKernel_isMarkovKernel t
  exact WeightedKernelL2.kernelIntegralL2_coe (G.transitionKernel_invariant hd hL t) f

/-- Physical L² inputs are integrable under almost every supplied whole endpoint law. -/
theorem ae_integrable_gmpTransitionKernel (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, Integrable f (G.transitionKernel t x) := by
  let := G.transitionKernel_isMarkovKernel t
  have hint : Integrable (fun y => f y ^ 2)
      (G.transitionKernel t ∘ₘ physicalReversibleMeasure ω hd lam) := by
    rw [G.transitionKernel_invariant hd hL t]
    exact (Lp.memLp f).integrable_sq
  filter_upwards [Measure.ae_integrable_of_integrable_comp hint] with x hx
  exact ((memLp_two_iff_integrable_sq (Lp.stronglyMeasurable f).aestronglyMeasurable).mpr hx).integrable (by norm_num)

/-- Survival reflection is contractive on the actual physical L² space. -/
theorem gmpKilledL2_reflection_norm_le (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖(2 : ℝ) • gmpKilledL2Operator G U hU t f - G.kernelL2Action hd hL t f‖ ≤ ‖f‖ := by
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    physicalReversibleMeasure_sigmaFinite hd ω lam
  let := G.transitionKernel_isMarkovKernel t
  let a : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
    (Lp.memLp f).norm.toLp (fun x => ‖f x‖)
  have ha : a =ᵐ[physicalReversibleMeasure ω hd lam] fun x => ‖f x‖ :=
    (Lp.memLp f).norm.coeFn_toLp
  have hrep : G.kernelL2Action hd hL t a =ᵐ[physicalReversibleMeasure ω hd lam]
      fun x => ∫ y, |f y| ∂G.transitionKernel t x := by
    refine (gmpTransitionL2_ae_eq G t a).trans ?_
    have ha' : a =ᵐ[G.transitionKernel t ∘ₘ physicalReversibleMeasure ω hd lam]
        fun x => ‖f x‖ := by
      rw [G.transitionKernel_invariant hd hL t]
      exact ha
    filter_upwards [Measure.ae_ae_of_ae_comp ha'] with x hx
    apply integral_congr_ae
    filter_upwards [hx] with y hy
    exact hy.trans (Real.norm_eq_abs _)
  have hn : ‖a‖ = ‖f‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable f), ← Lp.norm_def]
  calc
    _ ≤ ‖G.kernelL2Action hd hL t a‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [Lp.coeFn_sub ((2 : ℝ) • gmpKilledL2Operator G U hU t f)
          (G.kernelL2Action hd hL t f),
        Lp.coeFn_smul (2 : ℝ) (gmpKilledL2Operator G U hU t f),
        gmpKilledL2_ae_eq G U hU t f, gmpTransitionL2_ae_eq G t f,
        hrep, ae_integrable_gmpTransitionKernel G t f] with x hsub hsmul hk hp habs hi
      rw [hsub]
      simp only [Pi.sub_apply]
      rw [hsmul]
      change ‖2 * gmpKilledL2 G U hU t f x - G.kernelL2Action hd hL t f x‖ ≤ _
      rw [hk, hp, habs, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (abs_two_mul_integral_gmpKilled_sub_transition_le G U hU t x f
        (Lp.stronglyMeasurable f).measurable hi).trans (le_abs_self _)
    _ ≤ ‖a‖ := G.kernelL2Action_norm_le hd hL t a
    _ = ‖f‖ := hn

/-- The supplied whole-space form quotient equals its actual L² quadratic difference. -/
theorem gmpTransitionFormDifferenceQuotient_eq_inner (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    semigroupFormDifferenceQuotient ω hd lam G.transitionKernel t f =
      (1 / (t : ℝ)) * ⟪f - G.kernelL2Action hd hL t f, f⟫_ℝ := by
  unfold semigroupFormDifferenceQuotient
  congr 1
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f (G.kernelL2Action hd hL t f),
    gmpTransitionL2_ae_eq G t f] with x hsub hrep
  change _ = inner ℝ ((f - G.kernelL2Action hd hL t f) x) (f x)
  rw [hsub]
  change _ = inner ℝ (f x - G.kernelL2Action hd hL t f x) (f x)
  rw [hrep]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The whole-space quadratic difference is controlled by twice the killed difference. -/
theorem gmpTransition_inner_sub_le_two_mul_killed (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ⟪f - G.kernelL2Action hd hL t f, f⟫_ℝ ≤
      2 * ⟪f - gmpKilledL2Operator G U hU t f, f⟫_ℝ := by
  have h := (real_inner_le_norm
    ((2 : ℝ) • gmpKilledL2Operator G U hU t f - G.kernelL2Action hd hL t f) f).trans
      (mul_le_mul_of_nonneg_right (gmpKilledL2_reflection_norm_le G U hU t f)
        (norm_nonneg f))
  rw [inner_sub_left, real_inner_smul_left] at h
  rw [inner_sub_left, inner_sub_left, real_inner_self_eq_norm_sq]
  nlinarith

/-- The literal whole-space form quotient is controlled by twice the killed quotient. -/
theorem gmpTransitionFormDifferenceQuotient_le_two_mul_killed
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    semigroupFormDifferenceQuotient ω hd lam G.transitionKernel t f ≤
      2 * semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) t f := by
  rw [gmpTransitionFormDifferenceQuotient_eq_inner, gmpKilledFormDifferenceQuotient_eq_inner]
  have h := mul_le_mul_of_nonneg_left
    (gmpTransition_inner_sub_le_two_mul_killed G U hU t f)
    (show 0 ≤ 1 / (t : ℝ) by positivity)
  nlinarith

/-- Bounded actual killed form quotients imply membership in the supplied whole-space H¹ domain. -/
theorem physicalH1Member_of_bounded_gmpKilledFormDifferenceQuotient
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∃ C : ℝ, ∀ t : ℝ≥0, 0 < t → semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel G U hU) t f ≤ C) :
    physicalH1Member ω hd lam f := by
  apply (G.closedForm_domain f (Lp.memLp f)).mp
  obtain ⟨C, hC⟩ := hf
  exact ⟨2 * C, fun t ht =>
    (gmpTransitionFormDifferenceQuotient_le_two_mul_killed G U hU t f).trans
      (mul_le_mul_of_nonneg_left (hC t ht) (by norm_num))⟩

/-- Bounded actual killed form quotients also force the original datum into the interior carrier. -/
theorem mem_physicalZeroBoundaryL2_of_bounded_gmpKilledFormDifferenceQuotient
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∃ C : ℝ, ∀ t : ℝ≥0, 0 < t → semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel G U hU) t f ≤ C) :
    f ∈ physicalZeroBoundaryL2 U hd ω lam L hω := by
  obtain ⟨C, hC⟩ := hf
  have hbound : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0,
      ‖f - gmpKilledL2 G U hU t f‖ ^ 2 ≤ (2 * C) * (t : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < (t : ℝ) := ht
    have hq := hC t ht
    rw [gmpKilledFormDifferenceQuotient_eq_inner] at hq
    have he : ⟪f - gmpKilledL2Operator G U hU t f, f⟫_ℝ ≤ C * (t : ℝ) := by
      apply (div_le_iff₀ htpos).mp
      simpa only [div_eq_mul_inv, one_div, mul_comm, one_mul, mul_one] using hq
    have hn := gmpKilledL2_norm_sub_sq_le_inner G U hU t f
    change ‖f - gmpKilledL2 G U hU t f‖ ^ 2 ≤ _ at hn
    nlinarith
  have hleft : Tendsto (fun t : ℝ≥0 => ‖f - gmpKilledL2 G U hU t f‖ ^ 2)
      (𝓝[>] 0) (𝓝 (‖f - physicalZeroBoundaryProjection U hd ω lam L hω f‖ ^ 2)) :=
    (tendsto_const_nhds.sub
      ((tendsto_gmpKilledL2_at_zero G U hU f).mono_left nhdsWithin_le_nhds)).norm.pow 2
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] 0) (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun t : ℝ≥0 => (2 * C) * (t : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hcoe
  have hn : ‖f - physicalZeroBoundaryProjection U hd ω lam L hω f‖ = 0 := by
    nlinarith [le_of_tendsto_of_tendsto hleft hright hbound,
      norm_nonneg (f - physicalZeroBoundaryProjection U hd ω lam L hω f)]
  have heq : f = physicalZeroBoundaryProjection U hd ω lam L hω f :=
    sub_eq_zero.mp (norm_eq_zero.mp hn)
  rw [heq]
  exact physicalZeroBoundaryProjection_mem U hd ω lam L hω _

/-- Actual killed correlations have nonnegative second differences. -/
theorem gmpKilledL2_correlation_second_difference_nonneg
    (U : Set (Vec d)) (hU : IsOpen U) (s t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    0 ≤ ⟪gmpKilledL2Operator G U hU (s + (t + t)) f, f⟫_ℝ -
      2 * ⟪gmpKilledL2Operator G U hU (s + t) f, f⟫_ℝ +
      ⟪gmpKilledL2Operator G U hU s f, f⟫_ℝ := by
  let T := gmpKilledL2Operator G U hU
  have hleft : ⟪T s (T t f), f⟫_ℝ = ⟪T (s + t) f, f⟫_ℝ := by
    dsimp only [T]
    rw [gmpKilledL2Operator_add_time, ContinuousLinearMap.comp_apply]
  have hright : ⟪T s f, T t f⟫_ℝ = ⟪T (s + t) f, f⟫_ℝ := by
    calc
      _ = ⟪T t (T s f), f⟫_ℝ :=
        (gmpKilledL2Operator_isSymmetric G U hU t (T s f) f).symm
      _ = _ := by
        dsimp only [T]
        rw [show s + t = t + s from add_comm s t,
          gmpKilledL2Operator_add_time, ContinuousLinearMap.comp_apply]
  have hboth : ⟪T s (T t f), T t f⟫_ℝ =
      ⟪T (s + (t + t)) f, f⟫_ℝ := by
    calc
      _ = ⟪T t (T s (T t f)), f⟫_ℝ :=
        (gmpKilledL2Operator_isSymmetric G U hU t (T s (T t f)) f).symm
      _ = _ := by
        dsimp only [T]
        rw [show s + (t + t) = t + (s + t) by ac_rfl,
          gmpKilledL2Operator_add_time, ContinuousLinearMap.comp_apply,
          gmpKilledL2Operator_add_time, ContinuousLinearMap.comp_apply]
  have hp := gmpKilledL2_inner_nonneg G U hU s (f - T t f)
  change 0 ≤ ⟪T s (f - T t f), f - T t f⟫_ℝ at hp
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    hleft, hright, hboth] at hp
  linarith

/-- The correlation drop in each subsequent equal time step is no larger than the first. -/
theorem gmpKilledL2_correlation_increment_le
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (n : ℕ) :
    ⟪gmpKilledL2Operator G U hU (n • t) f, f⟫_ℝ -
      ⟪gmpKilledL2Operator G U hU ((n + 1) • t) f, f⟫_ℝ ≤
      ⟪gmpKilledL2Operator G U hU 0 f, f⟫_ℝ -
        ⟪gmpKilledL2Operator G U hU t f, f⟫_ℝ := by
  induction n with
  | zero => simp only [zero_nsmul, zero_add, one_nsmul, le_refl]
  | succ n ih =>
    have hp := gmpKilledL2_correlation_second_difference_nonneg G U hU (n • t) t f
    simp only [succ_nsmul] at ih ⊢
    rw [← add_assoc] at hp
    linarith

/-- Natural dilation of time decreases actual killed form quotients on the interior carrier. -/
theorem gmpKilledFormDifferenceQuotient_nsmul_le
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) (n : ℕ) (hn : 0 < n) :
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) (n • t) f ≤
      semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) t f := by
  have hz : gmpKilledL2Operator G U hU 0 f = f := by
    exact congrArg Subtype.val (gmpKilledInteriorOperator_zero G U hU ⟨f, hf⟩)
  have hbound : ∀ m : ℕ,
      ⟪f - gmpKilledL2Operator G U hU (m • t) f, f⟫_ℝ ≤
        (m : ℝ) * ⟪f - gmpKilledL2Operator G U hU t f, f⟫_ℝ := by
    intro m
    induction m with
    | zero => simp only [zero_nsmul, hz, sub_self, inner_zero_left, Nat.cast_zero, zero_mul,
        le_refl]
    | succ m ih =>
      have hi := gmpKilledL2_correlation_increment_le G U hU t f m
      rw [hz] at hi
      simp only [inner_sub_left] at ih ⊢
      push_cast
      nlinarith
  rw [gmpKilledFormDifferenceQuotient_eq_inner, gmpKilledFormDifferenceQuotient_eq_inner]
  have htpos : 0 < (t : ℝ) := ht
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  simp only [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast]
  have he := hbound n
  simp only [nsmul_eq_mul] at he
  have hdiv : ⟪f - gmpKilledL2Operator G U hU (↑n * t) f, f⟫_ℝ /
      ((n : ℝ) * (t : ℝ)) ≤
      ⟪f - gmpKilledL2Operator G U hU t f, f⟫_ℝ / (t : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hnpos htpos) htpos).mpr
    nlinarith
  simpa only [div_eq_mul_inv, one_div, mul_one, mul_comm] using hdiv

/-- With no spatial boundary, the literal killed endpoint law is the supplied whole law. -/
theorem gmpKilledEndpointKernel_univ :
    gmpKilledEndpointKernel G Set.univ isOpen_univ = G.transitionKernel := by
  funext t
  have hsurv : {γ : Path d | (t : ℝ≥0∞) < localityExitTime Set.univ γ} = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro γ
    exact (lt_localityExitTime_iff Set.univ isOpen_univ γ t).mpr
      (fun _ _ => Set.mem_univ _)
  ext x A hA
  rw [gmpKilledEndpointKernel_apply, hsurv, Measure.restrict_univ, G.pathLaw_endpoint]

/-- Natural time dilation decreases the supplied whole-space form quotients. -/
theorem gmpTransitionFormDifferenceQuotient_nsmul_le (t : ℝ≥0) (ht : 0 < t)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (n : ℕ) (hn : 0 < n) :
    semigroupFormDifferenceQuotient ω hd lam G.transitionKernel (n • t) f ≤
      semigroupFormDifferenceQuotient ω hd lam G.transitionKernel t f := by
  have hf : f ∈ physicalZeroBoundaryL2 Set.univ hd ω lam L hω := by
    apply (mem_physicalZeroBoundaryL2_iff_zero_off Set.univ isOpen_univ hd ω lam L hω f).mpr
    exact ae_of_all _ fun x hx => False.elim (hx (Set.mem_univ x))
  simpa only [gmpKilledEndpointKernel_univ] using
    gmpKilledFormDifferenceQuotient_nsmul_le G Set.univ isOpen_univ t ht f hf n hn

/-- The supplied short-time energy controls the whole-space quotient at every positive time. -/
theorem gmpTransitionFormDifferenceQuotient_le_physicalH1FormEnergy
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω hd lam] f)
    (u : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f) (t : ℝ≥0) (ht : 0 < t) :
    semigroupFormDifferenceQuotient ω hd lam G.transitionKernel t f ≤
      physicalH1FormEnergy ω hd lam u := by
  let δ : ℕ → ℝ≥0 := fun n => t / ((n + 1 : ℕ) : ℝ≥0)
  have hδpos : ∀ n, 0 < δ n := fun n => div_pos ht (by positivity)
  have hδzero : Tendsto δ atTop (𝓝 0) := by
    exact (tendsto_const_div_atTop_nhds_zero_nat t).comp (tendsto_add_atTop_nat 1)
  have hδ : Tendsto δ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδzero, Eventually.of_forall hδpos⟩
  have hlim := (G.closedForm_value f q hq u hu).comp hδ
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  have he : (n + 1) • δ n = t := by
    dsimp only [δ]
    rw [nsmul_eq_mul]
    exact mul_div_cancel₀ t (by positivity)
  simpa only [he, Function.comp_apply] using
    gmpTransitionFormDifferenceQuotient_nsmul_le G (δ n) (hδpos n) f (n + 1)
      (Nat.succ_pos n)

/-- The whole-space killed L² action is the literal supplied transition action. -/
theorem gmpKilledL2Operator_univ_apply (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    gmpKilledL2Operator G Set.univ isOpen_univ t f = G.kernelL2Action hd hL t f := by
  apply Lp.ext
  filter_upwards [gmpKilledL2_ae_eq G Set.univ isOpen_univ t f,
    gmpTransitionL2_ae_eq G t f] with x hk hp
  exact (hk.trans (by rw [gmpKilledEndpointKernel_univ])).trans hp.symm

/-- One whole-space transition, projected onto the actual interior L² carrier at both ends. -/
def gmpMonitoredStepL2Operator (V : Set (Vec d)) (t : ℝ≥0) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  physicalZeroBoundaryProjection V hd ω lam L hω ∘L
    gmpKilledL2Operator G Set.univ isOpen_univ t ∘L
      physicalZeroBoundaryProjection V hd ω lam L hω

/-- Every projected whole-space step is self-adjoint for the actual physical measure. -/
theorem gmpMonitoredStepL2Operator_isSelfAdjoint (V : Set (Vec d)) (t : ℝ≥0) :
    IsSelfAdjoint (gmpMonitoredStepL2Operator G V t) :=
  (gmpKilledL2Operator_isSelfAdjoint G Set.univ isOpen_univ t).conj_starProjection
    (physicalZeroBoundaryL2 V hd ω lam L hω)

/-- Finite monitoring retains the physical L² contraction bound. -/
theorem gmpMonitoredStepL2Operator_norm_le (V : Set (Vec d)) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖gmpMonitoredStepL2Operator G V t f‖ ≤ ‖f‖ := by
  exact ((physicalZeroBoundaryL2 V hd ω lam L hω).norm_starProjection_apply_le _).trans
    ((gmpKilledL2_norm_le G Set.univ isOpen_univ t _).trans
      ((physicalZeroBoundaryL2 V hd ω lam L hω).norm_starProjection_apply_le f))

/-- On an interior datum, projection does not change the one-step quadratic difference. -/
theorem gmpMonitoredStepL2Operator_inner_sub_eq (V : Set (Vec d)) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 V hd ω lam L hω) :
    ⟪f - gmpMonitoredStepL2Operator G V t f, f⟫_ℝ =
      ⟪f - G.kernelL2Action hd hL t f, f⟫_ℝ := by
  have hproj : physicalZeroBoundaryProjection V hd ω lam L hω f = f :=
    (physicalZeroBoundaryL2 V hd ω lam L hω).starProjection_mem_subspace_eq_self ⟨f, hf⟩
  have hpair := (physicalZeroBoundaryL2 V hd ω lam L hω).starProjection_isSymmetric
    (gmpKilledL2Operator G Set.univ isOpen_univ t f) f
  change ⟪physicalZeroBoundaryProjection V hd ω lam L hω
      (gmpKilledL2Operator G Set.univ isOpen_univ t f), f⟫_ℝ =
    ⟪gmpKilledL2Operator G Set.univ isOpen_univ t f,
      physicalZeroBoundaryProjection V hd ω lam L hω f⟫_ℝ at hpair
  rw [hproj, gmpKilledL2Operator_univ_apply] at hpair
  simp only [gmpMonitoredStepL2Operator, ContinuousLinearMap.comp_apply, hproj,
    gmpKilledL2Operator_univ_apply, inner_sub_left, hpair]

/-- The quadratic loss under dyadically many actual monitored steps grows at most linearly. -/
theorem gmpMonitoredStepL2Operator_pow_energy_le (V : Set (Vec d)) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (n : ℕ) :
    ⟪f - (gmpMonitoredStepL2Operator G V t ^ (2 ^ n)) f, f⟫_ℝ ≤
      (2 : ℝ) ^ n * ⟪f - gmpMonitoredStepL2Operator G V t f, f⟫_ℝ := by
  let B := gmpMonitoredStepL2Operator G V t
  induction n with
  | zero => simp only [pow_zero, pow_one, one_mul, le_refl]
  | succ n ih =>
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((gmpMonitoredStepL2Operator_isSelfAdjoint G V t).pow (2 ^ n))
    have hcorr : ⟪(B ^ (2 ^ (n + 1))) f, f⟫_ℝ = ‖(B ^ (2 ^ n)) f‖ ^ 2 := by
      rw [show 2 ^ (n + 1) = 2 ^ n + 2 ^ n by omega, pow_add]
      change ⟪(B ^ (2 ^ n)) ((B ^ (2 ^ n)) f), f⟫_ℝ = _
      exact (hsym ((B ^ (2 ^ n)) f) f).trans (real_inner_self_eq_norm_sq _)
    have hn := sq_nonneg ‖f - (B ^ (2 ^ n)) f‖
    rw [norm_sub_sq_real, real_inner_comm ((B ^ (2 ^ n)) f) f] at hn
    have hdouble : ⟪f - (B ^ (2 ^ (n + 1))) f, f⟫_ℝ ≤
        2 * ⟪f - (B ^ (2 ^ n)) f, f⟫_ℝ := by
      simp only [inner_sub_left, real_inner_self_eq_norm_sq, hcorr]
      nlinarith
    calc
      _ ≤ 2 * ⟪f - (B ^ (2 ^ n)) f, f⟫_ℝ := hdouble
      _ ≤ 2 * ((2 : ℝ) ^ n * ⟪f - B f, f⟫_ℝ) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ (2 : ℝ)]; ring

/-- Uniform finite-monitoring energy bound from the supplied weighted H¹ energy. -/
theorem gmpMonitoredStepL2Operator_pow_energy_le_physicalH1FormEnergy
    (V : Set (Vec d)) (t : ℝ≥0) (ht : 0 < t)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 V hd ω lam L hω)
    (q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω hd lam] f)
    (u : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f) (n : ℕ) :
    ⟪f - (gmpMonitoredStepL2Operator G V t ^ (2 ^ n)) f, f⟫_ℝ ≤
      (2 : ℝ) ^ n * (t : ℝ) * physicalH1FormEnergy ω hd lam u := by
  have hwhole := gmpTransitionFormDifferenceQuotient_le_physicalH1FormEnergy G f q hq u hu t ht
  rw [gmpTransitionFormDifferenceQuotient_eq_inner] at hwhole
  have hsingle : ⟪f - gmpMonitoredStepL2Operator G V t f, f⟫_ℝ ≤
      (t : ℝ) * physicalH1FormEnergy ω hd lam u := by
    rw [gmpMonitoredStepL2Operator_inner_sub_eq G V t f hf]
    rw [mul_comm (t : ℝ)]
    apply (div_le_iff₀ (show 0 < (t : ℝ) from ht)).mp
    simpa only [div_eq_mul_inv, one_div, mul_one, mul_comm] using hwhole
  calc
    _ ≤ (2 : ℝ) ^ n * ⟪f - gmpMonitoredStepL2Operator G V t f, f⟫_ℝ :=
      gmpMonitoredStepL2Operator_pow_energy_le G V t f n
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsingle (by positivity :
        0 ≤ (2 : ℝ) ^ n)

/-- A monitored step has the literal endpoint-indicator representative on every open set. -/
theorem gmpMonitoredStepL2Operator_ae_eq (V : Set (Vec d)) (hV : IsOpen V) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    gmpMonitoredStepL2Operator G V t f =ᵐ[physicalReversibleMeasure ω hd lam]
      V.indicator (fun x => ∫ y, V.indicator f y ∂G.transitionKernel t x) := by
  let g := physicalZeroBoundaryProjection V hd ω lam L hω f
  let p := gmpKilledL2Operator G Set.univ isOpen_univ t g
  have hrep : p =ᵐ[physicalReversibleMeasure ω hd lam]
      fun x => ∫ y, g y ∂G.transitionKernel t x := by
    simpa only [p, gmpKilledL2Operator_apply, gmpKilledEndpointKernel_univ] using
      gmpKilledL2_ae_eq G Set.univ isOpen_univ t g
  have hi : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      g =ᵐ[G.transitionKernel t x] V.indicator f := by
    simpa only [g, Filter.EventuallyEq, gmpKilledEndpointKernel_univ] using
      ae_ae_gmpKilledEndpointKernel_of_ae G Set.univ isOpen_univ t
        (physicalZeroBoundaryProjection_ae_eq_indicator V hV hd ω lam L hω f)
  filter_upwards [physicalZeroBoundaryProjection_ae_eq_indicator V hV hd ω lam L hω p,
    hrep, hi] with x hout hp hin
  change physicalZeroBoundaryProjection V hd ω lam L hω p x = _
  rw [hout]
  by_cases hx : x ∈ V
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hp]
    exact integral_congr_ae hin
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-- At fixed total time the finite-monitoring energy bound is uniform in the dyadic grid. -/
theorem gmpMonitoredStepL2Operator_dyadic_energy_le_physicalH1FormEnergy
    (V : Set (Vec d)) (T : ℝ≥0) (hT : 0 < T)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 V hd ω lam L hω)
    (q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω hd lam] f)
    (u : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f) (n : ℕ) :
    ⟪f - (gmpMonitoredStepL2Operator G V (T / 2 ^ n) ^ (2 ^ n)) f, f⟫_ℝ ≤
      (T : ℝ) * physicalH1FormEnergy ω hd lam u := by
  have he : (2 : ℝ) ^ n * ((T / 2 ^ n : ℝ≥0) : ℝ) = (T : ℝ) := by
    simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
    exact mul_div_cancel₀ (T : ℝ) (by positivity)
  simpa only [he] using gmpMonitoredStepL2Operator_pow_energy_le_physicalH1FormEnergy
    G V (T / 2 ^ n) (div_pos hT (by positivity)) f hf q hq u hu n

/-- The literal endpoint test retained by every observation of an equally spaced grid. -/
def gmpGridTest (V : Set (Vec d)) (t : ℝ≥0) (φ : Vec d → ℝ)
    (n : ℕ) : Path d → ℝ :=
  (gmpGridEvent V t Set.univ n).indicator (fun γ => φ (γ (n • t)))

/-- Every finite-grid endpoint test is Borel measurable. -/
theorem measurable_gmpGridTest (V : Set (Vec d)) (hV : MeasurableSet V)
    (t : ℝ≥0) (φ : Vec d → ℝ) (hφ : Measurable φ) (n : ℕ) :
    Measurable (gmpGridTest V t φ n) :=
  (hφ.comp (measurable_pathPosition (n • t))).indicator
    (measurableSet_gmpGridEvent V hV t Set.univ MeasurableSet.univ n)

/-- Finite monitoring preserves the bound on a bounded endpoint test. -/
theorem abs_gmpGridTest_le (V : Set (Vec d)) (t : ℝ≥0) (φ : Vec d → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hφB : ∀ y, |φ y| ≤ B) (n : ℕ) (γ : Path d) :
    |gmpGridTest V t φ n γ| ≤ B := by
  by_cases hγ : γ ∈ gmpGridEvent V t Set.univ n
  · simpa only [gmpGridTest, Set.indicator_of_mem hγ] using hφB (γ (n • t))
  · simpa only [gmpGridTest, Set.indicator_of_notMem hγ, abs_zero] using hB

/-- Removing the first grid observation gives the same literal test on the shifted path. -/
theorem gmpGridTest_succ (V : Set (Vec d)) (t : ℝ≥0) (φ : Vec d → ℝ)
    (n : ℕ) (γ : Path d) :
    gmpGridTest V t φ (n + 1) γ =
      V.indicator (fun _ => gmpGridTest V t φ n (gmpShiftPath t γ)) (γ 0) := by
  classical
  have htime : γ ((n + 1) • t) = gmpShiftPath t γ (n • t) := by
    change γ ((n + 1) • t) = γ (t + n • t)
    rw [succ_nsmul, add_comm]
  unfold gmpGridTest
  rw [gmpGridEvent]
  simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage]
  change (if γ 0 ∈ V ∧ gmpShiftPath t γ ∈ gmpGridEvent V t Set.univ n then
      φ (γ ((n + 1) • t)) else 0) = _
  by_cases hv : γ 0 ∈ V <;>
    by_cases he : gmpShiftPath t γ ∈ gmpGridEvent V t Set.univ n <;>
    simp only [hv, he, htime, and_true, and_false, ite_true, ite_false]

/-- The expectation of the actual retained endpoint test under the supplied path law. -/
def gmpGridExpectation (V : Set (Vec d)) (t : ℝ≥0) (φ : Vec d → ℝ)
    (n : ℕ) (x : Vec d) : ℝ :=
  ∫ γ, gmpGridTest V t φ n γ ∂G.pathLaw x

/-- The actual finite-grid expectation is a Borel function of the initial position. -/
theorem measurable_gmpGridExpectation (V : Set (Vec d)) (hV : MeasurableSet V)
    (t : ℝ≥0) (φ : Vec d → ℝ) (hφ : Measurable φ) (n : ℕ) :
    Measurable (gmpGridExpectation G V t φ n) :=
  (measurable_gmpGridTest V hV t φ hφ n).stronglyMeasurable.integral_kernel.measurable

/-- At zero steps the retained endpoint test is the literal initial-set indicator. -/
theorem gmpGridExpectation_zero (V : Set (Vec d)) (t : ℝ≥0) (φ : Vec d → ℝ)
    (x : Vec d) : gmpGridExpectation G V t φ 0 x = V.indicator φ x := by
  classical
  let := G.pathLaw_isMarkovKernel
  have he : gmpGridTest V t φ 0 =ᵐ[G.pathLaw x] fun _ => V.indicator φ x := by
    filter_upwards [G.pathLaw_starts_at x] with γ hγ
    change γ 0 = x at hγ
    simp only [gmpGridTest, gmpGridEvent, zero_nsmul, Set.inter_univ,
      Set.indicator, Set.mem_preimage]
    change (if γ 0 ∈ V then φ (γ 0) else 0) = _
    rw [hγ]
  rw [gmpGridExpectation, integral_congr_ae he, integral_const]
  simp

/-- Deterministic restart gives the exact recursion for bounded finite-grid tests. -/
theorem gmpGridExpectation_succ (V : Set (Vec d)) (hV : MeasurableSet V)
    (t : ℝ≥0) (φ : Vec d → ℝ) (hφ : Measurable φ)
    (B : ℝ) (hB : 0 ≤ B) (hφB : ∀ y, |φ y| ≤ B) (n : ℕ) (x : Vec d) :
    gmpGridExpectation G V t φ (n + 1) x =
      V.indicator (fun z => ∫ y, gmpGridExpectation G V t φ n y
        ∂G.transitionKernel t z) x := by
  classical
  let := G.pathLaw_isMarkovKernel
  let := G.transitionKernel_isMarkovKernel t
  let H := gmpGridTest V t φ n
  have hH : Measurable H := measurable_gmpGridTest V hV t φ hφ n
  have hHB (γ : Path d) : |H γ| ≤ B := abs_gmpGridTest_le V t φ B hB hφB n γ
  have hrestart : (∫ γ, H (gmpShiftPath t γ) ∂G.pathLaw x) =
      ∫ y, (∫ γ, H γ ∂G.pathLaw y) ∂G.transitionKernel t x := by
    have hi : Integrable H ((G.pathLaw ∘ₖ G.transitionKernel t) x) :=
      (integrable_const B).mono' hH.aestronglyMeasurable
        (ae_of_all _ fun γ => by simpa only [Real.norm_eq_abs] using hHB γ)
    rw [← integral_map (measurable_gmpShiftPath t).aemeasurable hH.aestronglyMeasurable,
      ← Kernel.map_apply _ (measurable_gmpShiftPath t), gmpPathLaw_map_shift,
      Kernel.integral_comp hi]
  have he : gmpGridTest V t φ (n + 1) =ᵐ[G.pathLaw x]
      fun γ => V.indicator (fun _ => H (gmpShiftPath t γ)) x := by
    filter_upwards [G.pathLaw_starts_at x] with γ hγ
    change γ 0 = x at hγ
    rw [gmpGridTest_succ, hγ]
  rw [gmpGridExpectation, integral_congr_ae he]
  by_cases hx : x ∈ V
  · simp only [Set.indicator_of_mem hx]
    exact hrestart
  · simp only [Set.indicator_of_notMem hx, integral_zero]

/-- Grid expectations vanish at starting points outside the first observation set. -/
theorem gmpGridExpectation_indicator (V : Set (Vec d)) (t : ℝ≥0) (φ : Vec d → ℝ)
    (n : ℕ) : V.indicator (gmpGridExpectation G V t φ n) =
      gmpGridExpectation G V t φ n := by
  funext x
  by_cases hx : x ∈ V
  · exact Set.indicator_of_mem hx _
  · rw [Set.indicator_of_notMem hx]
    have he : gmpGridTest V t φ n =ᵐ[G.pathLaw x] fun _ => 0 := by
      filter_upwards [G.pathLaw_starts_at x] with γ hγ
      change γ 0 = x at hγ
      have hn : γ ∉ gmpGridEvent V t Set.univ n := by
        cases n with
        | zero =>
          intro h
          exact hx (hγ ▸ h.1)
        | succ n =>
          intro h
          exact hx (hγ ▸ h.1)
      exact Set.indicator_of_notMem hn _
    rw [gmpGridExpectation, integral_congr_ae he, integral_zero]

/-- Every power of the monitored L² operator represents the actual finite path grid.
The bounded Borel endpoint test is an actual representative of the interior datum. -/
theorem gmpMonitoredStepL2Operator_pow_ae_eq_gridExpectation
    (V : Set (Vec d)) (hV : IsOpen V) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 V hd ω lam L hω)
    (φ : Vec d → ℝ) (hφ : Measurable φ)
    (hφf : φ =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (B : ℝ) (hB : 0 ≤ B) (hφB : ∀ y, |φ y| ≤ B) (n : ℕ) :
    (gmpMonitoredStepL2Operator G V t ^ n) f =ᵐ[physicalReversibleMeasure ω hd lam]
      gmpGridExpectation G V t φ n := by
  let A := gmpMonitoredStepL2Operator G V t
  have hproj : physicalZeroBoundaryProjection V hd ω lam L hω f = f :=
    (physicalZeroBoundaryL2 V hd ω lam L hω).starProjection_mem_subspace_eq_self ⟨f, hf⟩
  induction n with
  | zero =>
    have hrep := physicalZeroBoundaryProjection_ae_eq_indicator V hV hd ω lam L hω f
    rw [hproj] at hrep
    filter_upwards [hrep, hφf] with x hp hφx
    change f x = gmpGridExpectation G V t φ 0 x
    rw [gmpGridExpectation_zero, hp]
    by_cases hx : x ∈ V
    · simpa only [Set.indicator_of_mem hx] using hφx.symm
    · simp only [Set.indicator_of_notMem hx]
  | succ n ih =>
    have hind : V.indicator ((A ^ n) f) =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpGridExpectation G V t φ n := by
      filter_upwards [ih] with x hx
      have hsame := congrFun (gmpGridExpectation_indicator G V t φ n) x
      by_cases hv : x ∈ V
      · simpa only [Set.indicator_of_mem hv] using hx
      · rw [Set.indicator_of_notMem hv] at hsame ⊢
        exact hsame
    have hi : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        ∀ᵐ y ∂G.transitionKernel t x,
          V.indicator ((A ^ n) f) y = gmpGridExpectation G V t φ n y := by
      simpa only [gmpKilledEndpointKernel_univ] using
        ae_ae_gmpKilledEndpointKernel_of_ae G Set.univ isOpen_univ t hind
    rw [pow_succ']
    change A ((A ^ n) f) =ᵐ[physicalReversibleMeasure ω hd lam] _
    filter_upwards [gmpMonitoredStepL2Operator_ae_eq G V hV t ((A ^ n) f), hi]
      with x hstep hin
    rw [hstep, gmpGridExpectation_succ G V hV.measurableSet t φ hφ B hB hφB n x]
    by_cases hx : x ∈ V
    · simp only [Set.indicator_of_mem hx]
      exact integral_congr_ae hin
    · simp only [Set.indicator_of_notMem hx]

/-- The actual finite-grid loss equals the monitored-operator quadratic loss. -/
theorem gmpMonitoredStepL2Operator_pow_inner_sub_eq_gridExpectation
    (V : Set (Vec d)) (hV : IsOpen V) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 V hd ω lam L hω)
    (φ : Vec d → ℝ) (hφ : Measurable φ)
    (hφf : φ =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (B : ℝ) (hB : 0 ≤ B) (hφB : ∀ y, |φ y| ≤ B) (n : ℕ) :
    ⟪f - (gmpMonitoredStepL2Operator G V t ^ n) f, f⟫_ℝ =
      ∫ x, (f x - gmpGridExpectation G V t φ n x) * f x
        ∂physicalReversibleMeasure ω hd lam := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f ((gmpMonitoredStepL2Operator G V t ^ n) f),
    gmpMonitoredStepL2Operator_pow_ae_eq_gridExpectation G V hV t f hf φ hφ hφf B hB hφB n]
    with x hsub hgrid
  rw [hsub]
  simp only [Pi.sub_apply, hgrid]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- Literal finite path monitoring obeys the uniform weighted Sobolev energy bound. -/
theorem gmpGridExpectation_dyadic_energy_le_physicalH1FormEnergy
    (V : Set (Vec d)) (hV : IsOpen V) (T : ℝ≥0) (hT : 0 < T)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 V hd ω lam L hω)
    (φ : Vec d → ℝ) (hφ : Measurable φ)
    (hφf : φ =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (B : ℝ) (hB : 0 ≤ B) (hφB : ∀ y, |φ y| ≤ B)
    (q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω hd lam] f)
    (u : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f) (n : ℕ) :
    (∫ x, (f x - gmpGridExpectation G V (T / 2 ^ n) φ (2 ^ n) x) * f x
      ∂physicalReversibleMeasure ω hd lam) ≤
      (T : ℝ) * physicalH1FormEnergy ω hd lam u := by
  rw [← gmpMonitoredStepL2Operator_pow_inner_sub_eq_gridExpectation
    G V hV (T / 2 ^ n) f hf φ hφ hφf B hB hφB (2 ^ n)]
  exact gmpMonitoredStepL2Operator_dyadic_energy_le_physicalH1FormEnergy
    G V T hT f hf q hq u hu n

/-- Bounded endpoint tests give a uniform bound on every actual grid expectation. -/
theorem abs_gmpGridExpectation_le (V : Set (Vec d)) (t : ℝ≥0) (φ : Vec d → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hφB : ∀ y, |φ y| ≤ B) (n : ℕ) (x : Vec d) :
    |gmpGridExpectation G V t φ n x| ≤ B := by
  let := G.pathLaw_isMarkovKernel
  have hi := norm_integral_le_of_norm_le_const (μ := G.pathLaw x)
    (f := gmpGridTest V t φ n)
    (ae_of_all _ fun γ => by
      simpa only [Real.norm_eq_abs] using abs_gmpGridTest_le V t φ B hB hφB n γ)
  simpa only [gmpGridExpectation, probReal_univ, mul_one, Real.norm_eq_abs] using hi

/-- At dyadic spacing the finite-grid test has the fixed physical terminal time. -/
theorem gmpGridTest_dyadic_eq (V : Set (Vec d)) (T : ℝ≥0) (φ : Vec d → ℝ)
    (n : ℕ) :
    gmpGridTest V (T / 2 ^ n) φ (2 ^ n) =
      (gmpDyadicEvent V T Set.univ n).indicator (fun γ => φ (γ T)) := by
  have he := gmpDyadicEvent_eq_grid V T Set.univ n
  simp only [Nat.cast_pow, Nat.cast_ofNat] at he
  have ht : (2 ^ n : ℕ) • (T / 2 ^ n) = T := by
    simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact mul_div_cancel₀ T (by positivity)
  rw [gmpGridTest, ← he, ht]

/-- Actual finite-grid expectations on a closed set converge to the continuous-path
closed-survival expectation, with the same fixed endpoint test and physical time. -/
theorem tendsto_gmpGridExpectation_dyadic_closed (V : Set (Vec d)) (hV : IsClosed V)
    (T : ℝ≥0) (φ : Vec d → ℝ) (hφ : Measurable φ)
    (B : ℝ) (hφB : ∀ y, |φ y| ≤ B) (x : Vec d) :
    Tendsto (fun n => gmpGridExpectation G V (T / 2 ^ n) φ (2 ^ n) x) atTop
      (𝓝 (∫ γ, {γ : Path d | ∀ s : ℝ≥0, s ≤ T → γ s ∈ V}.indicator
        (fun γ => φ (γ T)) γ ∂G.pathLaw x)) := by
  let := G.pathLaw_isMarkovKernel
  have hm (n : ℕ) : MeasurableSet (gmpDyadicEvent V T Set.univ n) :=
    measurableSet_gmpDyadicEvent V hV.measurableSet T Set.univ MeasurableSet.univ n
  have hi : Integrable (fun γ : Path d => φ (γ T)) (G.pathLaw x) :=
    (integrable_const B).mono' (hφ.comp (measurable_pathPosition T)).aestronglyMeasurable
      (ae_of_all _ fun γ => by simpa only [Real.norm_eq_abs] using hφB (γ T))
  have hs : {γ : Path d | ∀ s : ℝ≥0, s ≤ T → γ s ∈ V} =
      ⋂ n : ℕ, gmpDyadicEvent V T Set.univ n := by
    simpa only [Set.preimage_univ, Set.univ_inter] using
      gmpClosedSurvival_eq_iInter_dyadic V hV T Set.univ
  change Tendsto (fun n => ∫ γ, gmpGridTest V (T / 2 ^ n) φ (2 ^ n) γ
    ∂G.pathLaw x) atTop _
  simp_rw [gmpGridTest_dyadic_eq, integral_indicator (hm _)]
  rw [hs, integral_indicator (MeasurableSet.iInter hm)]
  exact (antitone_gmpDyadicEvent V T Set.univ).tendsto_setIntegral hm hi.integrableOn

/-- Survival at every dyadic observation within a fixed spatial region. -/
def gmpDyadicSurvival (V : Set (Vec d)) (T : ℝ≥0) : Set (Path d) :=
  ⋂ n : ℕ, gmpDyadicEvent V T Set.univ n

/-- The full dyadic-survival event remains measurable for every Borel region. -/
theorem measurableSet_gmpDyadicSurvival (V : Set (Vec d)) (hV : MeasurableSet V)
    (T : ℝ≥0) : MeasurableSet (gmpDyadicSurvival V T) :=
  MeasurableSet.iInter fun n =>
    measurableSet_gmpDyadicEvent V hV T Set.univ MeasurableSet.univ n

/-- Enlarging the spatial region enlarges the full dyadic-survival event. -/
theorem gmpDyadicSurvival_mono {V W : Set (Vec d)} (hVW : V ⊆ W) (T : ℝ≥0) :
    gmpDyadicSurvival V T ⊆ gmpDyadicSurvival W T := by
  intro γ hγ
  exact Set.mem_iInter.mpr fun n =>
    ⟨(Set.mem_iInter.mp hγ n).1,
      fun k hk => hVW ((Set.mem_iInter.mp hγ n).2 k hk)⟩

/-- Continuous paths surviving all dyadic observations stay in the spatial closure. -/
theorem gmpDyadicSurvival_subset_closedSurvival (V : Set (Vec d)) (T : ℝ≥0) :
    gmpDyadicSurvival V T ⊆
      {γ : Path d | ∀ s : ℝ≥0, s ≤ T → γ s ∈ closure V} := by
  intro γ hγ
  have hc := gmpDyadicSurvival_mono (V := V) subset_closure T hγ
  have he := gmpClosedSurvival_eq_iInter_dyadic (closure V) isClosed_closure T Set.univ
  unfold gmpDyadicSurvival at hc
  rw [← he] at hc
  exact hc.2

/-- The bounded endpoint expectation retained by the entire dyadic grid. -/
def gmpDyadicExpectation (V : Set (Vec d)) (T : ℝ≥0) (φ : Vec d → ℝ)
    (x : Vec d) : ℝ :=
  ∫ γ, (gmpDyadicSurvival V T).indicator (fun γ => φ (γ T)) γ ∂G.pathLaw x

/-- The limiting grid expectation is Borel in the actual initial position. -/
theorem measurable_gmpDyadicExpectation (V : Set (Vec d)) (hV : MeasurableSet V)
    (T : ℝ≥0) (φ : Vec d → ℝ) (hφ : Measurable φ) :
    Measurable (gmpDyadicExpectation G V T φ) :=
  ((hφ.comp (measurable_pathPosition T)).indicator
    (measurableSet_gmpDyadicSurvival V hV T)).stronglyMeasurable.integral_kernel.measurable

/-- A bounded endpoint test bounds the limiting grid expectation uniformly. -/
theorem abs_gmpDyadicExpectation_le (V : Set (Vec d)) (T : ℝ≥0) (φ : Vec d → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hφB : ∀ y, |φ y| ≤ B) (x : Vec d) :
    |gmpDyadicExpectation G V T φ x| ≤ B := by
  let := G.pathLaw_isMarkovKernel
  have hb (γ : Path d) :
      ‖(gmpDyadicSurvival V T).indicator (fun γ => φ (γ T)) γ‖ ≤ B := by
    by_cases hγ : γ ∈ gmpDyadicSurvival V T
    · simpa only [Set.indicator_of_mem hγ, Real.norm_eq_abs] using hφB (γ T)
    · simpa only [Set.indicator_of_notMem hγ, norm_zero] using hB
  have hi := norm_integral_le_of_norm_le_const (μ := G.pathLaw x) (ae_of_all _ hb)
  simpa only [gmpDyadicExpectation, probReal_univ, mul_one, Real.norm_eq_abs] using hi

/-- Refining a finite grid gives the literal grid-intersection expectation for any
Borel spatial region; no closedness or boundary regularity is assumed. -/
theorem tendsto_gmpGridExpectation_dyadic (V : Set (Vec d)) (hV : MeasurableSet V)
    (T : ℝ≥0) (φ : Vec d → ℝ) (hφ : Measurable φ)
    (B : ℝ) (hφB : ∀ y, |φ y| ≤ B) (x : Vec d) :
    Tendsto (fun n => gmpGridExpectation G V (T / 2 ^ n) φ (2 ^ n) x) atTop
      (𝓝 (gmpDyadicExpectation G V T φ x)) := by
  let := G.pathLaw_isMarkovKernel
  have hm (n : ℕ) : MeasurableSet (gmpDyadicEvent V T Set.univ n) :=
    measurableSet_gmpDyadicEvent V hV T Set.univ MeasurableSet.univ n
  have hi : Integrable (fun γ : Path d => φ (γ T)) (G.pathLaw x) :=
    (integrable_const B).mono' (hφ.comp (measurable_pathPosition T)).aestronglyMeasurable
      (ae_of_all _ fun γ => by simpa only [Real.norm_eq_abs] using hφB (γ T))
  change Tendsto (fun n => ∫ γ, gmpGridTest V (T / 2 ^ n) φ (2 ^ n) γ
    ∂G.pathLaw x) atTop _
  simp_rw [gmpGridTest_dyadic_eq, integral_indicator (hm _)]
  rw [gmpDyadicExpectation, gmpDyadicSurvival,
    integral_indicator (MeasurableSet.iInter hm)]
  exact (antitone_gmpDyadicEvent V T Set.univ).tendsto_setIntegral hm hi.integrableOn

/-- Open interior regions at a positive distance from the complement of the killing domain. -/
def gmpSurvivalInterior (U : Set (Vec d)) (n : ℕ) : Set (Vec d) :=
  (Metric.cthickening (1 / (n + 1 : ℝ)) Uᶜ)ᶜ

/-- Every interior region is open. -/
theorem isOpen_gmpSurvivalInterior (U : Set (Vec d)) (n : ℕ) :
    IsOpen (gmpSurvivalInterior U n) := Metric.isClosed_cthickening.isOpen_compl

/-- The closure of each interior region stays inside the actual killing domain. -/
theorem closure_gmpSurvivalInterior_subset (U : Set (Vec d)) (n : ℕ) :
    closure (gmpSurvivalInterior U n) ⊆ U := by
  apply Set.Subset.trans _ (gmpSurvivalCore_subset U n)
  apply closure_minimal _ (isClosed_gmpSurvivalCore U n)
  intro x hx hbad
  exact hx (Metric.thickening_subset_cthickening _ _ hbad)

/-- The open interior regions increase as their distance threshold decreases. -/
theorem monotone_gmpSurvivalInterior (U : Set (Vec d)) :
    Monotone (gmpSurvivalInterior U) := by
  intro m n hmn x hx hn
  exact hx (Metric.cthickening_mono (by gcongr) Uᶜ hn)

/-- Each earlier closed core lies in the next open interior region. -/
theorem gmpSurvivalCore_subset_survivalInterior_succ (U : Set (Vec d)) (n : ℕ) :
    gmpSurvivalCore U n ⊆ gmpSurvivalInterior U (n + 1) := by
  intro x hx hbad
  apply hx
  exact Metric.cthickening_subset_thickening' (by positivity)
    (by apply one_div_lt_one_div_of_lt; positivity; norm_num) Uᶜ hbad

/-- Exhausting interior regions after the full time-grid limit recovers actual strict
survival, including both endpoints, for every continuous supplied path. -/
theorem localitySurvival_eq_iUnion_dyadicInterior (U : Set (Vec d)) (hU : IsOpen U)
    (T : ℝ≥0) :
    {γ : Path d | (T : ℝ≥0∞) < localityExitTime U γ} =
      ⋃ n : ℕ, gmpDyadicSurvival (gmpSurvivalInterior U n) T := by
  ext γ
  constructor
  · intro hγ
    obtain ⟨n, hn⟩ := (localitySurvival_iff_exists_core U hU T γ).mp hγ
    refine Set.mem_iUnion.mpr ⟨n + 1, Set.mem_iInter.mpr fun m => ⟨Set.mem_univ _, ?_⟩⟩
    intro k hk
    exact gmpSurvivalCore_subset_survivalInterior_succ U n
      (hn (dyadicTime T m k) (dyadicTime_le T m k))
  · intro hγ
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hγ
    apply (lt_localityExitTime_iff U hU γ T).mpr
    intro s hs
    exact closure_gmpSurvivalInterior_subset U n
      (gmpDyadicSurvival_subset_closedSurvival _ T hn s hs)

/-- The iterated grid/interior limit is the actual strict-survival killed expectation. -/
theorem tendsto_gmpDyadicExpectation_survivalInterior (U : Set (Vec d)) (hU : IsOpen U)
    (T : ℝ≥0) (φ : Vec d → ℝ) (hφ : Measurable φ)
    (B : ℝ) (hφB : ∀ y, |φ y| ≤ B) (x : Vec d) :
    Tendsto (fun n => gmpDyadicExpectation G (gmpSurvivalInterior U n) T φ x) atTop
      (𝓝 (∫ y, φ y ∂gmpKilledEndpointKernel G U hU T x)) := by
  let := G.pathLaw_isMarkovKernel
  have hm (n : ℕ) := measurableSet_gmpDyadicSurvival (gmpSurvivalInterior U n)
    (isOpen_gmpSurvivalInterior U n).measurableSet T
  have hi : Integrable (fun γ : Path d => φ (γ T)) (G.pathLaw x) :=
    (integrable_const B).mono' (hφ.comp (measurable_pathPosition T)).aestronglyMeasurable
      (ae_of_all _ fun γ => by simpa only [Real.norm_eq_abs] using hφB (γ T))
  have hmono : Monotone (fun n => gmpDyadicSurvival (gmpSurvivalInterior U n) T) :=
    fun m n hmn => gmpDyadicSurvival_mono (monotone_gmpSurvivalInterior U hmn) T
  rw [integral_gmpKilledEndpointKernel G U hU T x φ hφ,
    localitySurvival_eq_iUnion_dyadicInterior U hU T]
  change Tendsto (fun n => ∫ γ, _ ∂G.pathLaw x) atTop _
  simp_rw [integral_indicator (hm _)]
  rw [integral_indicator (MeasurableSet.iUnion hm)]
  exact tendsto_setIntegral_of_monotone hm hmono hi.integrableOn

/-- Every compact subset of an open domain lies in one of its open interior regions. -/
theorem exists_subset_gmpSurvivalInterior (U : Set (Vec d)) (hU : IsOpen U)
    (C : Set (Vec d)) (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ n : ℕ, C ⊆ gmpSurvivalInterior U n := by
  obtain ⟨ε, hε, hsep⟩ := hCU.disjoint_compl_right.exists_thickenings hC hU.isClosed_compl
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n, fun x hx hbad => ?_⟩
  exact Set.disjoint_left.mp hsep (Metric.self_subset_thickening hε C hx)
    (Metric.cthickening_subset_thickening' hε hn Uᶜ hbad)

/-- Uniformly bounded pointwise limits pass through the physical quadratic pairing
against an integrable L² datum; the bound uses its actual square and absolute value. -/
theorem tendsto_physicalL2_loss_of_uniform_bound
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hif : Integrable f (physicalReversibleMeasure ω hd lam))
    (F : ℕ → Vec d → ℝ) (hF : ∀ n, Measurable (F n))
    (H : Vec d → ℝ) (hFH : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (H x)))
    (B : ℝ) (hFB : ∀ n x, |F n x| ≤ B) :
    Tendsto (fun n => ∫ x, (f x - F n x) * f x ∂physicalReversibleMeasure ω hd lam)
      atTop (𝓝 (∫ x, (f x - H x) * f x ∂physicalReversibleMeasure ω hd lam)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => f x ^ 2 + B * |f x|)
  · intro n
    exact ((Lp.aestronglyMeasurable f).sub (hF n).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)
  · exact (Lp.memLp f).integrable_sq.add (hif.abs.const_mul B)
  · intro n
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |f x - F n x| * |f x| ≤ (|f x| + |F n x|) * |f x| :=
          mul_le_mul_of_nonneg_right (abs_sub (f x) (F n x)) (abs_nonneg _)
        _ ≤ (|f x| + B) * |f x| := by gcongr; exact hFB n x
        _ = f x ^ 2 + B * |f x| := by nlinarith [sq_abs (f x)]
  · exact ae_of_all _ fun x => (tendsto_const_nhds.sub (hFH x)).mul tendsto_const_nhds

/-- The actual dyadic-grid energy bound persists after refining all time observations. -/
theorem gmpDyadicExpectation_energy_le_physicalH1FormEnergy
    (V : Set (Vec d)) (hV : IsOpen V) (T : ℝ≥0) (hT : 0 < T)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 V hd ω lam L hω)
    (hif : Integrable f (physicalReversibleMeasure ω hd lam))
    (φ : Vec d → ℝ) (hφ : Measurable φ)
    (hφf : φ =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (B : ℝ) (hB : 0 ≤ B) (hφB : ∀ y, |φ y| ≤ B)
    (q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω hd lam] f)
    (u : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    (∫ x, (f x - gmpDyadicExpectation G V T φ x) * f x
      ∂physicalReversibleMeasure ω hd lam) ≤
      (T : ℝ) * physicalH1FormEnergy ω hd lam u := by
  apply le_of_tendsto (tendsto_physicalL2_loss_of_uniform_bound f hif
    (fun n => gmpGridExpectation G V (T / 2 ^ n) φ (2 ^ n))
    (fun n => measurable_gmpGridExpectation G V hV.measurableSet _ φ hφ _)
    (gmpDyadicExpectation G V T φ)
    (tendsto_gmpGridExpectation_dyadic G V hV.measurableSet T φ hφ B hφB)
    B (fun n x => abs_gmpGridExpectation_le G V _ φ B hB hφB _ x))
  exact Eventually.of_forall fun n => gmpGridExpectation_dyadic_energy_le_physicalH1FormEnergy
    G V hV T hT f hf φ hφ hφf B hB hφB q hq u hu n

/-- The actual killed quadratic loss is bounded by the supplied physical H¹ energy
on every continuous compactly supported interior datum, for arbitrary open domains. -/
theorem gmpKilledL2_energy_le_physicalH1FormEnergy_of_compactSupport
    (U : Set (Vec d)) (hU : IsOpen U) (T : ℝ≥0) (hT : 0 < T)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (φ : Vec d → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφf : φ =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω hd lam] f)
    (u : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    ⟪f - gmpKilledL2Operator G U hU T f, f⟫_ℝ ≤
      (T : ℝ) * physicalH1FormEnergy ω hd lam u := by
  let : IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd lam) :=
    SpatialDirichlet.densityWeightedMeasure_locallyFinite _
      (physicalReversibleDensity_continuous ω hd lam)
  obtain ⟨B, hφB⟩ := hφc.exists_bound_of_continuous hφ
  have hB : 0 ≤ B := (norm_nonneg (φ 0)).trans (hφB 0)
  have hφabs : ∀ y, |φ y| ≤ B := by simpa only [Real.norm_eq_abs] using hφB
  have hiφ : Integrable φ (physicalReversibleMeasure ω hd lam) :=
    hφ.integrable_of_hasCompactSupport hφc
  have hif : Integrable f (physicalReversibleMeasure ω hd lam) := hiφ.congr hφf
  obtain ⟨N, hN⟩ := exists_subset_gmpSurvivalInterior U hU (tsupport φ) hφc hφU
  have hf (n : ℕ) (hn : N ≤ n) :
      f ∈ physicalZeroBoundaryL2 (gmpSurvivalInterior U n) hd ω lam L hω := by
    apply (mem_physicalZeroBoundaryL2_iff_zero_off _
      (isOpen_gmpSurvivalInterior U n) hd ω lam L hω f).mpr
    filter_upwards [hφf] with x hx hxV
    rw [← hx]
    exact image_eq_zero_of_notMem_tsupport
      (fun hxφ => hxV (monotone_gmpSurvivalInterior U hn (hN hxφ)))
  have hlim := tendsto_physicalL2_loss_of_uniform_bound f hif
    (fun n => gmpDyadicExpectation G (gmpSurvivalInterior U n) T φ)
    (fun n => measurable_gmpDyadicExpectation G _
      (isOpen_gmpSurvivalInterior U n).measurableSet T φ hφ.measurable)
    (fun x => ∫ y, φ y ∂gmpKilledEndpointKernel G U hU T x)
    (tendsto_gmpDyadicExpectation_survivalInterior G U hU T φ hφ.measurable B hφabs)
    B (fun n x => abs_gmpDyadicExpectation_le G _ T φ B hB hφabs x)
  have hbound : (∫ x, (f x - ∫ y, φ y ∂gmpKilledEndpointKernel G U hU T x) * f x
      ∂physicalReversibleMeasure ω hd lam) ≤
      (T : ℝ) * physicalH1FormEnergy ω hd lam u := by
    apply le_of_tendsto hlim
    exact eventually_atTop.mpr ⟨N, fun n hn =>
      gmpDyadicExpectation_energy_le_physicalH1FormEnergy G _
        (isOpen_gmpSurvivalInterior U n) T hT f (hf n hn) hif
        φ hφ.measurable hφf B hB hφabs q hq u hu⟩
  have heq : ⟪f - gmpKilledL2Operator G U hU T f, f⟫_ℝ =
      ∫ x, (f x - ∫ y, φ y ∂gmpKilledEndpointKernel G U hU T x) * f x
        ∂physicalReversibleMeasure ω hd lam := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f (gmpKilledL2Operator G U hU T f),
      gmpKilledL2_ae_eq G U hU T f] with x hs hk
    rw [hs]
    change inner ℝ (f x - gmpKilledL2 G U hU T f x) (f x) = _
    rw [hk, ← integral_gmpKilledEndpointKernel_congr_ae G U hU T hT x φ f hφf]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  exact heq ▸ hbound

/-- The actual killed form quotients of continuous compactly supported interior
H¹ data are bounded by their physical energy, at every positive time. -/
theorem gmpKilledFormDifferenceQuotient_le_physicalH1FormEnergy_of_compactSupport
    (U : Set (Vec d)) (hU : IsOpen U) (T : ℝ≥0) (hT : 0 < T)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (φ : Vec d → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφf : φ =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω hd lam] f)
    (u : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) T f ≤
      physicalH1FormEnergy ω hd lam u := by
  rw [gmpKilledFormDifferenceQuotient_eq_inner]
  have hb := gmpKilledL2_energy_le_physicalH1FormEnergy_of_compactSupport
    G U hU T hT f φ hφ hφc hφU hφf q hq u hu
  rw [one_div, ← div_eq_inv_mul]
  exact (div_le_iff₀ (show 0 < (T : ℝ) from hT)).mpr (by simpa only [mul_comm] using hb)

open Blueprint EinsteinRelation.SpatialDirichlet

include hL hω in
/-- The literal physical energy is continuous in the existing full weighted H¹ norm. -/
theorem continuous_physicalH1FormEnergy :
    Continuous (fun u : PhysicalH1Space hd lam =>
      physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u)) := by
  change Continuous (fun u : GMPForceH1 hd lam =>
    physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u))
  let J := gmpPhysicalH1ValueContinuousLinear hd ω lam L hω
  let E := gmpPhysicalH1Energy hd ω lam L hω
  have hsymm (u v : GMPForceH1 hd lam) : E u v = E v u :=
    gmpPhysicalH1Energy_symm hd ω lam L hω u v
  have hadd (u v w : GMPForceH1 hd lam) : E (u + v) w = E u w + E v w :=
    gmpPhysicalH1Energy_add_left hd ω lam L hL hω u v w
  have hsmul (c : ℝ) (u v : GMPForceH1 hd lam) : E (c • u) v = c * E u v :=
    gmpPhysicalH1Energy_smul_left hd ω lam L hω c u v
  let B : GMPForceH1 hd lam →ₗ[ℝ] GMPForceH1 hd lam →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => inner ℝ (J u) (J v) + E u v)
      (by intro u v w; rw [J.map_add, inner_add_left, hadd]; ring)
      (by intro c u v; rw [J.map_smul, real_inner_smul_left, hsmul]; simp only [smul_eq_mul]; ring)
      (by intro u v w; rw [J.map_add, inner_add_right, hsymm u (v+w), hadd,
          hsymm v u, hsymm w u]; ring)
      (by intro c u v; rw [J.map_smul, inner_smul_right, hsymm u (c • v), hsmul,
          hsymm v u]; simp only [smul_eq_mul]; ring)
  let C := B.mkContinuous₂ (Real.exp (2 * L) * (1 + L / 2)) (fun u v => by
    change |inner ℝ (J u) (J v) + E u v| ≤ _
    change |inner ℝ (gmpPhysicalH1Value hd ω lam L hω u)
      (gmpPhysicalH1Value hd ω lam L hω v) +
      gmpPhysicalH1Energy hd ω lam L hω u v| ≤ _
    rw [gmpPhysicalH1Energy_eq_source]
    have hb := sourcePhysicalResolventForm_bounded hd ω lam L 1 hL hω zero_lt_one u v
    simp only [one_mul] at hb
    convert hb using 1
    rfl)
  have hC : Continuous (fun u : GMPForceH1 hd lam => C u u) :=
    (C.continuous.clm_apply continuous_id)
  have hE : Continuous (fun u : GMPForceH1 hd lam => E u u) := by
    convert hC.sub (J.continuous.inner J.continuous) using 1
    funext u
    change E u u = inner ℝ (J u) (J u) + E u u - inner ℝ (J u) (J u)
    ring
  convert hE using 1
  funext u
  exact (gmpPhysicalH1Energy_eq_source hd ω lam L hω u u).trans
    (sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd lam L hω u) |>.symm

/-- Every member of the existing smooth interior span has a literal compactly
supported smooth scalar representative. -/
theorem physicalH1SmoothCore_exists_spatialTest (U : Set (Vec d))
    (u : PhysicalH1Space hd lam) (hu : u ∈ physicalH1SmoothCore U hd lam) :
    ∃ φ : Vec d → ℝ, IsSpatialTest U φ ∧
      densityWeightedH1SpaceValue u =ᵐ[EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam] φ := by
  induction hu using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨φ, hφ, rfl⟩ := hv
      exact ⟨φ, hφ, physicalH1SmoothTest_value hd lam φ hφ.1 hφ.2.1⟩
  | zero =>
      refine ⟨0, ⟨contDiff_const, ?_, ?_⟩, ?_⟩
      · exact HasCompactSupport.zero
      · simp
      · have hz := (gmpForceH1ValueContinuousLinear hd lam).map_zero
        change densityWeightedH1SpaceValue (0 : PhysicalH1Space hd lam) = 0 at hz
        rw [hz]
        exact Lp.coeFn_zero _ _ _
  | add v w hv hw hvφ hwφ =>
      obtain ⟨φ, hφ, hvφ⟩ := hvφ
      obtain ⟨ψ, hψ, hwψ⟩ := hwφ
      refine ⟨φ + ψ, ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, ?_⟩, ?_⟩
      · exact (tsupport_add φ ψ).trans (Set.union_subset hφ.2.2 hψ.2.2)
      · have hsum := (gmpForceH1ValueContinuousLinear hd lam).map_add v w
        change densityWeightedH1SpaceValue (v + w) =
          densityWeightedH1SpaceValue v + densityWeightedH1SpaceValue w at hsum
        rw [hsum]
        exact (Lp.coeFn_add _ _).trans (hvφ.add hwψ)
  | smul c v hv hvφ =>
      obtain ⟨φ, hφ, hvφ⟩ := hvφ
      refine ⟨c • φ, ⟨contDiff_const.smul hφ.1, hφ.2.1.smul_left, ?_⟩, ?_⟩
      · exact (tsupport_smul_subset_right (fun _ : Vec d => c) φ).trans hφ.2.2
      · have hsc := (gmpForceH1ValueContinuousLinear hd lam).map_smul c v
        change densityWeightedH1SpaceValue (c • v) = c • densityWeightedH1SpaceValue v at hsc
        rw [hsc]
        exact (Lp.coeFn_smul _ _).trans (hvφ.const_smul c)

/-- The actual killed energy estimate holds for every element of the existing
smooth interior span, using its literal compactly supported representative. -/
theorem gmpKilledL2_energy_le_physicalH1FormEnergy_of_smoothCore
    (U : Set (Vec d)) (hU : IsOpen U) (T : ℝ≥0) (hT : 0 < T)
    (u : PhysicalH1Space hd lam) (hu : u ∈ physicalH1SmoothCore U hd lam) :
    inner ℝ (gmpPhysicalH1Value hd ω lam L hω u -
      gmpKilledL2Operator G U hU T (gmpPhysicalH1Value hd ω lam L hω u))
      (gmpPhysicalH1Value hd ω lam L hω u) ≤
      (T : ℝ) * physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u) := by
  obtain ⟨φ, hφ, huφ⟩ := physicalH1SmoothCore_exists_spatialTest U u hu
  let e := densityWeightedH1GraphEquiv (physicalForceWeight hd lam)
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
  let q := e.symm u
  have hqvalue : densityWeightedH1Value (physicalForceWeight hd lam) q =
      densityWeightedH1SpaceValue u := by
    calc
      _ = densityWeightedH1SpaceValue (e q) :=
        (gmpForceH1_graphEquiv_value hd lam q).symm
      _ = _ := congrArg densityWeightedH1SpaceValue (e.apply_symm_apply u)
  have hf := gmpPhysicalH1Value_ae_eq hd ω lam L hω u
  have hrep := gmpH1Representative_value_ae (physicalForceWeight hd lam)
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam) u
  have hac := Measure.absolutelyContinuous_of_le_smul
    (sourcePhysicalMeasure_le_reduced ω hd lam L hω)
  have hφf : φ =ᵐ[physicalReversibleMeasure ω hd lam]
      gmpPhysicalH1Value hd ω lam L hω u := (hac.ae_eq huφ).symm.trans hf.symm
  have hqf : densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω hd lam] gmpPhysicalH1Value hd ω lam L hω u := by
    rw [hqvalue]
    exact hf.symm
  exact gmpKilledL2_energy_le_physicalH1FormEnergy_of_compactSupport G U hU T hT
    (gmpPhysicalH1Value hd ω lam L hω u) φ hφ.1.continuous hφ.2.1 hφ.2.2 hφf
    q hqf (physicalH1SpaceRepresentative hd lam u) ((hac.ae_eq hrep).trans hf.symm)

/-- The actual killed loss is bounded by the literal physical energy throughout
the already constructed H¹₀ domain, by closure of its smooth interior span. -/
theorem gmpKilledL2_energy_le_physicalH1FormEnergy_of_zeroBoundary
    (U : Set (Vec d)) (hU : IsOpen U) (T : ℝ≥0) (hT : 0 < T)
    (u : PhysicalH1Space hd lam) (hu : u ∈ physicalH1ZeroBoundary U hd lam) :
    inner ℝ (gmpPhysicalH1Value hd ω lam L hω u -
      gmpKilledL2Operator G U hU T (gmpPhysicalH1Value hd ω lam L hω u))
      (gmpPhysicalH1Value hd ω lam L hω u) ≤
      (T : ℝ) * physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u) := by
  let J : PhysicalH1Space hd lam →L[ℝ] Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
    gmpPhysicalH1ValueContinuousLinear hd ω lam L hω
  let K := gmpKilledL2Operator G U hU T
  have hclosed : IsClosed {v : PhysicalH1Space hd lam |
      inner ℝ (J v - K (J v)) (J v) ≤ (T : ℝ) *
        physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam v)} :=
    isClosed_le ((J.continuous.sub (K.continuous.comp J.continuous)).inner J.continuous)
      (continuous_const.mul (continuous_physicalH1FormEnergy (hL := hL) (hω := hω)))
  have hcore : (physicalH1SmoothCore U hd lam : Set (PhysicalH1Space hd lam)) ⊆
      {v : PhysicalH1Space hd lam | inner ℝ (J v - K (J v)) (J v) ≤
        (T : ℝ) * physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam v)} :=
    fun v hv => gmpKilledL2_energy_le_physicalH1FormEnergy_of_smoothCore G U hU T hT v hv
  change u ∈ closure (physicalH1SmoothCore U hd lam : Set (PhysicalH1Space hd lam)) at hu
  exact closure_minimal hcore hclosed hu

/-- Every member of the existing H¹₀ domain has bounded actual killed form
quotients at every positive time, with its unchanged physical energy as bound. -/
theorem gmpKilledFormDifferenceQuotient_le_of_zeroBoundary
    (U : Set (Vec d)) (hU : IsOpen U) (T : ℝ≥0) (hT : 0 < T)
    (u : PhysicalH1Space hd lam) (hu : u ∈ physicalH1ZeroBoundary U hd lam) :
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) T
      (gmpPhysicalH1Value hd ω lam L hω u) ≤
      physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u) := by
  rw [gmpKilledFormDifferenceQuotient_eq_inner]
  have hb := gmpKilledL2_energy_le_physicalH1FormEnergy_of_zeroBoundary G U hU T hT u hu
  rw [one_div, ← div_eq_inv_mul]
  exact (div_le_iff₀ (show 0 < (T : ℝ) from hT)).mpr (by simpa only [mul_comm] using hb)

/-- The supplied strict-survival operators, on their existing interior carrier,
form an actual strongly continuous contraction semigroup. -/
def gmpKilledInteriorSemigroup (U : Set (Vec d)) (hU : IsOpen U) :
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (physicalZeroBoundaryL2 U hd ω lam L hω) where
  operator := gmpKilledInteriorOperator G U hU
  operator_zero := by
    apply ContinuousLinearMap.ext
    intro f
    exact gmpKilledInteriorOperator_zero G U hU f
  operator_add := gmpKilledInteriorOperator_add_time G U hU
  opNorm_le_one := fun t =>
    (gmpKilledInteriorOperator G U hU t).opNorm_le_bound zero_le_one (fun f => by
      simpa only [one_mul] using gmpKilledInteriorOperator_norm_le G U hU t f)
  continuous_orbit := continuous_gmpKilledInteriorOperator_apply G U hU

/-- Generator-domain data move by at most time times the norm of the actual
killed generator. The estimate holds at every nonnegative time. -/
theorem gmpKilledInteriorSemigroup_norm_sub_le (U : Set (Vec d)) (hU : IsOpen U)
    (u : (gmpKilledInteriorSemigroup G U hU).generatorDomain) (t : ℝ≥0) :
    ‖gmpKilledInteriorSemigroup G U hU t u.val - u.val‖ ≤
      ‖(gmpKilledInteriorSemigroup G U hU).generator u‖ * (t : ℝ) := by
  let S := gmpKilledInteriorSemigroup G U hU
  change ‖S t u.val - u.val‖ ≤ ‖S.generator u‖ * (t : ℝ)
  rw [S.operator_sub_eq_integral u t]
  exact S.norm_orbitIntegral_le (S.generator u) t

/-- Every datum in the actual killed generator domain has uniformly bounded
literal killed form quotients. -/
theorem gmpKilledFormDifferenceQuotient_le_generator_norm
    (U : Set (Vec d)) (hU : IsOpen U)
    (u : (gmpKilledInteriorSemigroup G U hU).generatorDomain)
    (t : ℝ≥0) (ht : 0 < t) :
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) t
      u.val.val ≤ ‖(gmpKilledInteriorSemigroup G U hU).generator u‖ * ‖u.val‖ := by
  rw [gmpKilledFormDifferenceQuotient_eq_inner, one_div, ← div_eq_inv_mul]
  apply (div_le_iff₀ (show 0 < (t : ℝ) from ht)).mpr
  have hn := gmpKilledInteriorSemigroup_norm_sub_le G U hU u t
  have hi := real_inner_le_norm
    (u.val.val - gmpKilledL2Operator G U hU t u.val.val) u.val.val
  have he : ‖u.val.val - gmpKilledL2Operator G U hU t u.val.val‖ =
      ‖gmpKilledInteriorSemigroup G U hU t u.val - u.val‖ := by
    change ‖u.val.val - (gmpKilledInteriorOperator G U hU t u.val).val‖ = _
    rw [norm_sub_rev]
    rfl
  rw [he] at hi
  change _ ≤ ‖gmpKilledInteriorSemigroup G U hU t u.val - u.val‖ * ‖u.val‖ at hi
  exact hi.trans (calc
    _ ≤ (‖(gmpKilledInteriorSemigroup G U hU).generator u‖ * (t : ℝ)) * ‖u.val‖ :=
      mul_le_mul_of_nonneg_right hn (norm_nonneg u.val)
    _ = _ := by ring)

/-- The actual killed resolvent is the Laplace transform of the literal
strict-survival operators on the existing physical interior L² space. -/
def gmpKilledInteriorResolvent (U : Set (Vec d)) (hU : IsOpen U)
    (μ : MarkovProcess.Semigroup.PositiveShift) :
    physicalZeroBoundaryL2 U hd ω lam L hω →L[ℝ] physicalZeroBoundaryL2 U hd ω lam L hω :=
  (gmpKilledInteriorSemigroup G U hU).resolvent μ

/-- Contractivity gives a domain-independent resolvent bound. -/
theorem gmpKilledInteriorResolvent_norm_le (U : Set (Vec d)) (hU : IsOpen U)
    (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    ‖gmpKilledInteriorResolvent G U hU μ f‖ ≤ (μ : ℝ)⁻¹ * ‖f‖ := by
  exact ((gmpKilledInteriorResolvent G U hU μ).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right
      ((gmpKilledInteriorSemigroup G U hU).opNorm_resolvent_le μ) (norm_nonneg f))

/-- The actual killed resolvent has bounded actual killed form quotients,
uniformly in time and in the open killing region. -/
theorem gmpKilledFormDifferenceQuotient_resolvent_le
    (U : Set (Vec d)) (hU : IsOpen U) (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) (t : ℝ≥0) (ht : 0 < t) :
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) t
      (gmpKilledInteriorResolvent G U hU μ f).val ≤
      2 * (μ : ℝ)⁻¹ * ‖f‖ ^ 2 := by
  let S := gmpKilledInteriorSemigroup G U hU
  let u : S.generatorDomain := ⟨S.resolvent μ f, S.resolvent_mem_generatorDomain μ f⟩
  have hμ : 0 < (μ : ℝ) := μ.property
  have hu : ‖u.val‖ ≤ (μ : ℝ)⁻¹ * ‖f‖ :=
    gmpKilledInteriorResolvent_norm_le G U hU μ f
  have hgen : ‖S.generator u‖ ≤ 2 * ‖f‖ := by
    rw [S.generator_resolvent μ f]
    calc
      ‖(μ : ℝ) • S.resolvent μ f - f‖ ≤ ‖(μ : ℝ) • S.resolvent μ f‖ + ‖f‖ := norm_sub_le _ _
      _ = (μ : ℝ) * ‖u.val‖ + ‖f‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
      _ ≤ (μ : ℝ) * ((μ : ℝ)⁻¹ * ‖f‖) + ‖f‖ := by gcongr
      _ = 2 * ‖f‖ := by rw [← mul_assoc, mul_inv_cancel₀ hμ.ne']; ring
  have hq := gmpKilledFormDifferenceQuotient_le_generator_norm G U hU u t ht
  exact hq.trans (calc
    ‖S.generator u‖ * ‖u.val‖ ≤ (2 * ‖f‖) * ((μ : ℝ)⁻¹ * ‖f‖) :=
      mul_le_mul hgen hu (norm_nonneg _) (by positivity)
    _ = 2 * (μ : ℝ)⁻¹ * ‖f‖ ^ 2 := by ring)

/-- Resolvent regularization by the actual killed law belongs to the supplied
full weighted H¹ domain. No boundary-domain identification is assumed. -/
theorem physicalH1Member_gmpKilledInteriorResolvent
    (U : Set (Vec d)) (hU : IsOpen U) (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    physicalH1Member ω hd lam (gmpKilledInteriorResolvent G U hU μ f).val := by
  exact physicalH1Member_of_bounded_gmpKilledFormDifferenceQuotient G U hU _
    ⟨2 * (μ : ℝ)⁻¹ * ‖f‖ ^ 2,
      fun t ht => gmpKilledFormDifferenceQuotient_resolvent_le G U hU μ f t ht⟩

/-- A bound on actual killed quotients controls the literal physical energy of
any existing full weighted H¹ representative of the datum. -/
theorem physicalH1FormEnergy_le_two_mul_of_killed_bound
    (U : Set (Vec d)) (hU : IsOpen U) (u : PhysicalH1Space hd lam)
    (C : ℝ) (hC : ∀ t : ℝ≥0, 0 < t →
      semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) t
        (gmpPhysicalH1Value hd ω lam L hω u) ≤ C) :
    physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u) ≤ 2 * C := by
  let e := densityWeightedH1GraphEquiv (physicalForceWeight hd lam)
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
  let q := e.symm u
  have hqvalue : densityWeightedH1Value (physicalForceWeight hd lam) q =
      densityWeightedH1SpaceValue u := by
    calc
      _ = densityWeightedH1SpaceValue (e q) := (gmpForceH1_graphEquiv_value hd lam q).symm
      _ = _ := congrArg densityWeightedH1SpaceValue (e.apply_symm_apply u)
  have hval := gmpPhysicalH1Value_ae_eq hd ω lam L hω u
  have hq : densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω hd lam] gmpPhysicalH1Value hd ω lam L hω u := by
    rw [hqvalue]
    exact hval.symm
  have hrep := (Measure.absolutelyContinuous_of_le_smul
    (sourcePhysicalMeasure_le_reduced ω hd lam L hω)).ae_eq
      (gmpH1Representative_value_ae (physicalForceWeight hd lam)
        (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam) u)
  have hlim := G.closedForm_value (gmpPhysicalH1Value hd ω lam L hω u) q hq
    (physicalH1SpaceRepresentative hd lam u) (hrep.trans hval.symm)
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (gmpTransitionFormDifferenceQuotient_le_two_mul_killed G U hU t _).trans
    (mul_le_mul_of_nonneg_left (hC t ht) (by norm_num))

/-- The actual killed resolvent has a full weighted H¹ representative with
uniform physical-energy and graph-norm bounds. The constants are independent
of the killing region, as required for interior exhaustion. -/
theorem gmpKilledInteriorResolvent_exists_h1_bounded
    (U : Set (Vec d)) (hU : IsOpen U) (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    ∃ u : PhysicalH1Space hd lam,
      gmpPhysicalH1Value hd ω lam L hω u = (gmpKilledInteriorResolvent G U hU μ f).val ∧
      physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u) ≤
        4 * (μ : ℝ)⁻¹ * ‖f‖ ^ 2 ∧
      (Real.exp (-2 * L) * min 1 ((1 / 2 : ℝ) * L⁻¹)) * ‖u‖ ^ 2 ≤
        ((μ : ℝ)⁻¹ ^ 2 + 4 * (μ : ℝ)⁻¹) * ‖f‖ ^ 2 := by
  obtain ⟨u, hu⟩ := (gmpPhysicalH1Value_range_iff hd ω lam L hω _).mpr
    (physicalH1Member_gmpKilledInteriorResolvent G U hU μ f)
  have hE : physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u) ≤
      4 * (μ : ℝ)⁻¹ * ‖f‖ ^ 2 := by
    have h := physicalH1FormEnergy_le_two_mul_of_killed_bound G U hU u
      (2 * (μ : ℝ)⁻¹ * ‖f‖ ^ 2) (fun t ht => by
        rw [hu]
        exact gmpKilledFormDifferenceQuotient_resolvent_le G U hU μ f t ht)
    nlinarith only [h]
  refine ⟨u, hu, hE, ?_⟩
  have hm : ‖gmpPhysicalH1Value hd ω lam L hω u‖ ^ 2 ≤ (μ : ℝ)⁻¹ ^ 2 * ‖f‖ ^ 2 := by
    rw [hu]
    have h := gmpKilledInteriorResolvent_norm_le G U hU μ f
    have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
    have hs' : ‖gmpKilledInteriorResolvent G U hU μ f‖ ^ 2 ≤
        (μ : ℝ)⁻¹ ^ 2 * ‖f‖ ^ 2 := by simpa only [mul_pow] using hs
    convert hs' using 1
    rfl
  have hc := gmpPhysicalH1Energy_coercive hd ω lam L hL hω u
  have heq : gmpPhysicalH1Energy hd ω lam L hω u u =
      physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u) :=
    (gmpPhysicalH1Energy_eq_source hd ω lam L hω u u).trans
      (sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd lam L hω u)
  rw [heq] at hc
  change (Real.exp (-2 * L) * min 1 ((1 / 2 : ℝ) * L⁻¹)) * ‖(u : GMPForceH1 hd lam)‖ ^ 2 ≤ _
  exact hc.trans (calc
    _ ≤ (μ : ℝ)⁻¹ ^ 2 * ‖f‖ ^ 2 + 4 * (μ : ℝ)⁻¹ * ‖f‖ ^ 2 := add_le_add hm hE
    _ = _ := by ring)

/-- A full physical H¹ element supported in a compact interior region lies in
its actual smooth zero-boundary core closure. The compact interior condition is
essential; exterior-zero support in an arbitrary open domain does not suffice. -/
theorem physicalH1Space_mem_zeroBoundary_of_compact_interior
    (U V K : Set (Vec d)) (hU : IsOpen U) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKU : K ⊆ U) (u : PhysicalH1Space hd lam)
    (hu : gmpPhysicalH1Value hd ω lam L hω u ∈ physicalZeroBoundaryL2 V hd ω lam L hω) :
    u ∈ physicalH1ZeroBoundary U hd lam := by
  have hz := physicalZeroBoundaryL2_zero_off V hd ω lam L hω _ hu
  have hv := gmpPhysicalH1Value_ae_eq hd ω lam L hω u
  have hsupport : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      x ∉ K → densityWeightedH1SpaceValue u x = 0 := by
    filter_upwards [hz, hv] with x hx he hxK
    exact he.symm.trans (hx (fun hxV => hxK (hVK hxV)))
  have hac := Measure.absolutelyContinuous_of_le_smul
    (sourceReducedMeasure_le_physical ω hd lam L hω)
  exact physicalH1Space_compact_mem_zeroBoundary hd lam u hK hU hKU (hac.ae_le hsupport)

/-- The actual killed resolvent on a compact interior region has a representative
in the existing H¹₀ domain of the larger open set, with uniform energy and graph
bounds. No boundary regularity of the larger domain is assumed. -/
theorem gmpKilledInteriorResolvent_exists_zeroBoundary_bounded
    (U V K : Set (Vec d)) (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKU : K ⊆ U) (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 V hd ω lam L hω) :
    ∃ u : PhysicalH1Space hd lam,
      u ∈ physicalH1ZeroBoundary U hd lam ∧
      gmpPhysicalH1Value hd ω lam L hω u = (gmpKilledInteriorResolvent G V hV μ f).val ∧
      physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u) ≤
        4 * (μ : ℝ)⁻¹ * ‖f‖ ^ 2 ∧
      (Real.exp (-2 * L) * min 1 ((1 / 2 : ℝ) * L⁻¹)) * ‖u‖ ^ 2 ≤
        ((μ : ℝ)⁻¹ ^ 2 + 4 * (μ : ℝ)⁻¹) * ‖f‖ ^ 2 := by
  obtain ⟨u, hu, hE, hn⟩ := gmpKilledInteriorResolvent_exists_h1_bounded G V hV μ f
  refine ⟨u, physicalH1Space_mem_zeroBoundary_of_compact_interior
    (ω := ω) (L := L) (hω := hω) U V K hU hK hVK hKU u ?_,
    hu, hE, hn⟩
  rw [hu]
  exact (gmpKilledInteriorResolvent G V hV μ f).property

/-- Strict survival in an arbitrary open domain is the increasing union of
strict survival in the positively separated interior regions. -/
theorem localitySurvival_eq_iUnion_survivalInterior (U : Set (Vec d)) (hU : IsOpen U)
    (T : ℝ≥0) :
    {γ : Path d | (T : ℝ≥0∞) < localityExitTime U γ} =
      ⋃ n : ℕ, {γ : Path d | (T : ℝ≥0∞) < localityExitTime (gmpSurvivalInterior U n) γ} := by
  ext γ
  constructor
  · intro hγ
    obtain ⟨n, hn⟩ := (localitySurvival_iff_exists_core U hU T γ).mp hγ
    refine Set.mem_iUnion.mpr ⟨n + 1, ?_⟩
    apply (lt_localityExitTime_iff _ (isOpen_gmpSurvivalInterior U (n + 1)) γ T).mpr
    intro t ht
    exact gmpSurvivalCore_subset_survivalInterior_succ U n (hn t ht)
  · intro hγ
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hγ
    apply (lt_localityExitTime_iff U hU γ T).mpr
    intro t ht
    exact closure_gmpSurvivalInterior_subset U n (subset_closure
      ((lt_localityExitTime_iff _ (isOpen_gmpSurvivalInterior U n) γ T).mp hn t ht))

/-- The actual killed endpoint integrals converge under the interior exhaustion.
Endpoint integrability suffices; the test need not be bounded or compactly supported. -/
theorem tendsto_integral_gmpKilledEndpointKernel_survivalInterior
    (U : Set (Vec d)) (hU : IsOpen U) (T : ℝ≥0)
    (φ : Vec d → ℝ) (hφ : Measurable φ) (x : Vec d)
    (hi : Integrable φ (G.transitionKernel T x)) :
    Tendsto (fun n => ∫ y, φ y ∂gmpKilledEndpointKernel G (gmpSurvivalInterior U n)
      (isOpen_gmpSurvivalInterior U n) T x) atTop
      (𝓝 (∫ y, φ y ∂gmpKilledEndpointKernel G U hU T x)) := by
  have hm (n : ℕ) := measurableSet_localitySurvival (gmpSurvivalInterior U n)
    (isOpen_gmpSurvivalInterior U n) T
  have hmono : Monotone (fun n => {γ : Path d |
      (T : ℝ≥0∞) < localityExitTime (gmpSurvivalInterior U n) γ}) := by
    intro m n hmn γ hγ
    apply (lt_localityExitTime_iff _ (isOpen_gmpSurvivalInterior U n) γ T).mpr
    intro t ht
    exact monotone_gmpSurvivalInterior U hmn
      ((lt_localityExitTime_iff _ (isOpen_gmpSurvivalInterior U m) γ T).mp hγ t ht)
  have hipush : Integrable φ ((G.pathLaw x).map (pathPosition T)) := by
    rw [G.pathLaw_endpoint]
    exact hi
  have hipath := hipush.comp_measurable (measurable_pathPosition T)
  simp_rw [integral_gmpKilledEndpointKernel G _ _ T x φ hφ]
  rw [localitySurvival_eq_iUnion_survivalInterior U hU T]
  simp_rw [integral_indicator (hm _)]
  rw [integral_indicator (MeasurableSet.iUnion hm)]
  exact tendsto_setIntegral_of_monotone hm hmono hipath.integrableOn

/-- Bounded open interiors whose closures stay inside the killing region. -/
def gmpCompactSurvivalInterior (U : Set (Vec d)) (n : ℕ) : Set (Vec d) :=
  gmpSurvivalInterior U n ∩ Metric.ball 0 (n + 1 : ℝ)

/-- The bounded interior exhaustion consists of open sets. -/
theorem isOpen_gmpCompactSurvivalInterior (U : Set (Vec d)) (n : ℕ) :
    IsOpen (gmpCompactSurvivalInterior U n) :=
  (isOpen_gmpSurvivalInterior U n).inter Metric.isOpen_ball

/-- Every bounded interior has compact closure, in the existing Euclidean carrier. -/
theorem isCompact_closure_gmpCompactSurvivalInterior (U : Set (Vec d)) (n : ℕ) :
    IsCompact (closure (gmpCompactSurvivalInterior U n)) := by
  apply (isCompact_closedBall (0 : Vec d) (n + 1 : ℝ)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  exact fun _ hx => Metric.ball_subset_closedBall hx.2

/-- The compact closures lie in the literal original region. -/
theorem closure_gmpCompactSurvivalInterior_subset (U : Set (Vec d)) (n : ℕ) :
    closure (gmpCompactSurvivalInterior U n) ⊆ U :=
  (closure_mono Set.inter_subset_left).trans (closure_gmpSurvivalInterior_subset U n)

/-- The compact interior regions increase with the exhaustion index. -/
theorem monotone_gmpCompactSurvivalInterior (U : Set (Vec d)) :
    Monotone (gmpCompactSurvivalInterior U) := by
  intro m n hmn x hx
  exact ⟨monotone_gmpSurvivalInterior U hmn hx.1,
    Metric.ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hmn 1) hx.2⟩

/-- Every compact subset of an open region eventually lies in the bounded interiors. -/
theorem exists_subset_gmpCompactSurvivalInterior (U : Set (Vec d)) (hU : IsOpen U)
    (C : Set (Vec d)) (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ n : ℕ, C ⊆ gmpCompactSurvivalInterior U n := by
  obtain ⟨N, hN⟩ := exists_subset_gmpSurvivalInterior U hU C hC hCU
  obtain ⟨r, hr⟩ := hC.isBounded.subset_ball (0 : Vec d)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  refine ⟨max N n, fun x hx => ⟨monotone_gmpSurvivalInterior U (Nat.le_max_left N n) (hN hx), ?_⟩⟩
  apply Metric.ball_subset_ball (ε₁ := r) _ (hr hx)
  have hh : (n : ℝ) ≤ max N n := by exact_mod_cast Nat.le_max_right N n
  linarith

/-- Compact interior survival increases to the actual strict-survival event. -/
theorem localitySurvival_eq_iUnion_compactSurvivalInterior
    (U : Set (Vec d)) (hU : IsOpen U) (T : ℝ≥0) :
    {γ : Path d | (T : ℝ≥0∞) < localityExitTime U γ} =
      ⋃ n : ℕ, {γ : Path d | (T : ℝ≥0∞) <
        localityExitTime (gmpCompactSurvivalInterior U n) γ} := by
  ext γ
  constructor
  · intro hγ
    have hsurv := (lt_localityExitTime_iff U hU γ T).mp hγ
    obtain ⟨n, hn⟩ := exists_subset_gmpCompactSurvivalInterior U hU
      (γ '' Set.Icc 0 T) (isCompact_Icc.image γ.continuous) (by
        rintro _ ⟨t, ht, rfl⟩
        exact hsurv t ht.2)
    exact Set.mem_iUnion.mpr ⟨n, (lt_localityExitTime_iff _
      (isOpen_gmpCompactSurvivalInterior U n) γ T).mpr
        (fun t ht => hn ⟨t, ⟨bot_le, ht⟩, rfl⟩)⟩
  · intro hγ
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hγ
    apply (lt_localityExitTime_iff U hU γ T).mpr
    intro t ht
    exact closure_gmpCompactSurvivalInterior_subset U n (subset_closure
      ((lt_localityExitTime_iff _ (isOpen_gmpCompactSurvivalInterior U n) γ T).mp hn t ht))

/-- Endpoint-integrable actual killed expectations converge along compact interiors. -/
theorem tendsto_integral_gmpKilledEndpointKernel_compactSurvivalInterior
    (U : Set (Vec d)) (hU : IsOpen U) (T : ℝ≥0)
    (φ : Vec d → ℝ) (hφ : Measurable φ) (x : Vec d)
    (hi : Integrable φ (G.transitionKernel T x)) :
    Tendsto (fun n => ∫ y, φ y ∂gmpKilledEndpointKernel G (gmpCompactSurvivalInterior U n)
      (isOpen_gmpCompactSurvivalInterior U n) T x) atTop
      (𝓝 (∫ y, φ y ∂gmpKilledEndpointKernel G U hU T x)) := by
  have hm (n : ℕ) := measurableSet_localitySurvival (gmpCompactSurvivalInterior U n)
    (isOpen_gmpCompactSurvivalInterior U n) T
  have hmono : Monotone (fun n => {γ : Path d |
      (T : ℝ≥0∞) < localityExitTime (gmpCompactSurvivalInterior U n) γ}) := by
    intro m n hmn γ hγ
    apply (lt_localityExitTime_iff _ (isOpen_gmpCompactSurvivalInterior U n) γ T).mpr
    intro t ht
    exact monotone_gmpCompactSurvivalInterior U hmn
      ((lt_localityExitTime_iff _ (isOpen_gmpCompactSurvivalInterior U m) γ T).mp hγ t ht)
  have hipush : Integrable φ ((G.pathLaw x).map (pathPosition T)) := by
    rw [G.pathLaw_endpoint]
    exact hi
  have hipath := hipush.comp_measurable (measurable_pathPosition T)
  simp_rw [integral_gmpKilledEndpointKernel G _ _ T x φ hφ]
  rw [localitySurvival_eq_iUnion_compactSurvivalInterior U hU T]
  simp_rw [integral_indicator (hm _)]
  rw [integral_indicator (MeasurableSet.iUnion hm)]
  exact tendsto_setIntegral_of_monotone hm hmono hipath.integrableOn

/-- Actual compact-interior killed operators converge strongly on the full
physical L² space. This is a path-survival limit, not an assumed form convergence. -/
theorem tendsto_gmpKilledL2_compactSurvivalInterior
    (U : Set (Vec d)) (hU : IsOpen U) (T : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Tendsto (fun n => gmpKilledL2 G (gmpCompactSurvivalInterior U n)
      (isOpen_gmpCompactSurvivalInterior U n) T f) atTop
      (𝓝 (gmpKilledL2 G U hU T f)) := by
  let m := physicalReversibleMeasure ω hd lam
  let v (n : ℕ) := gmpKilledL2 G (gmpCompactSurvivalInterior U n)
    (isOpen_gmpCompactSurvivalInterior U n) T f
  let w := gmpKilledL2 G U hU T f
  let b (x : Vec d) := ∫ y, f y ^ 2 ∂G.transitionKernel T x
  have hint : Integrable (fun y => f y ^ 2) (G.transitionKernel T ∘ₘ m) := by
    rw [G.transitionKernel_invariant hd hL T]
    exact (Lp.memLp f).integrable_sq
  have hb : Integrable b m := by
    have h := Measure.integrable_integral_norm_of_integrable_comp hint
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, sq_abs] using h
  have hsq (V : Set (Vec d)) (hV : IsOpen V) :
      ∀ᵐ x ∂m, (gmpKilledL2 G V hV T f x) ^ 2 ≤ b x := by
    filter_upwards [gmpKilledL2_ae_eq G V hV T f,
      sq_integral_gmpKilledEndpointKernel_le G V hV T f,
      Measure.ae_integrable_of_integrable_comp hint] with x hx hs hi
    rw [hx]
    exact hs.trans (integral_mono_measure (gmpKilledEndpointKernel_le G V hV T x)
      (ae_of_all _ fun _ => sq_nonneg _) hi)
  have hpoint : ∀ᵐ x ∂m, Tendsto (fun n => v n x) atTop (𝓝 (w x)) := by
    filter_upwards [ae_all_iff.mpr (fun n => gmpKilledL2_ae_eq G
      (gmpCompactSurvivalInterior U n) (isOpen_gmpCompactSurvivalInterior U n) T f),
      gmpKilledL2_ae_eq G U hU T f,
      ae_integrable_gmpTransitionKernel G T f] with x hn hx hi
    simp_rw [v, w, hn, hx]
    exact tendsto_integral_gmpKilledEndpointKernel_compactSurvivalInterior G U hU T
      f (Lp.stronglyMeasurable f).measurable x hi
  have hlim : Tendsto (fun n => ∫ x, (v n x - w x) ^ 2 ∂m) atTop (𝓝 (0 : ℝ)) := by
    have ht := tendsto_integral_of_dominated_convergence (fun x => 4 * b x)
      (fun n => (((Lp.stronglyMeasurable (v n)).sub (Lp.stronglyMeasurable w)).pow 2).aestronglyMeasurable)
      (hb.const_mul 4) (fun n => by
        filter_upwards [hsq (gmpCompactSurvivalInterior U n)
          (isOpen_gmpCompactSurvivalInterior U n), hsq U hU] with x hv hw
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change (v n x) ^ 2 ≤ b x at hv
        change (w x) ^ 2 ≤ b x at hw
        change (v n x - w x) ^ 2 ≤ 4 * b x
        nlinarith only [hv, hw, sq_nonneg (v n x + w x)]) (by
        filter_upwards [hpoint] with x hx
        simpa using (hx.sub tendsto_const_nhds).pow 2)
    simpa only [Pi.pow_apply, Pi.sub_apply, sub_self, zero_pow (by decide : 2 ≠ 0),
      integral_zero] using ht
  have hnorm : Tendsto (fun n => ‖v n - w‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    convert hlim using 1
    funext n
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (v n) w] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial, pow_two, Pi.sub_apply]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  change Tendsto (fun n => ‖v n - w‖) atTop (𝓝 0)
  have hs : Tendsto (fun n => Real.sqrt (‖v n - w‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hnorm
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hs

include G in
/-- Interior restriction converges strongly along the compact survival exhaustion. -/
theorem tendsto_physicalZeroBoundaryProjection_compactSurvivalInterior
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Tendsto (fun n => physicalZeroBoundaryProjection (gmpCompactSurvivalInterior U n)
      hd ω lam L hω f) atTop (𝓝 (physicalZeroBoundaryProjection U hd ω lam L hω f)) := by
  simpa only [gmpKilledL2_zero] using
    tendsto_gmpKilledL2_compactSurvivalInterior G U hU 0 f

/-- The actual killed Laplace resolvents converge strongly along compact interior
regions, with the datum restricted by the existing physical interior projections. -/
theorem tendsto_gmpKilledInteriorResolvent_compactSurvivalInterior
    (U : Set (Vec d)) (hU : IsOpen U) (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Tendsto (fun n => (gmpKilledInteriorResolvent G (gmpCompactSurvivalInterior U n)
      (isOpen_gmpCompactSurvivalInterior U n) μ
      ⟨physicalZeroBoundaryProjection (gmpCompactSurvivalInterior U n) hd ω lam L hω f,
        physicalZeroBoundaryProjection_mem (gmpCompactSurvivalInterior U n) hd ω lam L hω f⟩).val)
      atTop (𝓝 ((gmpKilledInteriorResolvent G U hU μ
        ⟨physicalZeroBoundaryProjection U hd ω lam L hω f,
          physicalZeroBoundaryProjection_mem U hd ω lam L hω f⟩).val)) := by
  let p (V : Set (Vec d)) : physicalZeroBoundaryL2 V hd ω lam L hω :=
    ⟨physicalZeroBoundaryProjection V hd ω lam L hω f,
      physicalZeroBoundaryProjection_mem V hd ω lam L hω f⟩
  let F (V : Set (Vec d)) (hV : IsOpen V) (t : ℝ) :=
    (physicalZeroBoundaryL2 V hd ω lam L hω).subtypeL
      ((gmpKilledInteriorSemigroup G V hV).laplaceIntegrand μ (p V) t)
  have hF (V : Set (Vec d)) (hV : IsOpen V) (t : ℝ) :
      F V hV t = Real.exp (-(μ : ℝ) * t) • gmpKilledL2 G V hV (Real.toNNReal t) f := by
    change Real.exp (-(μ : ℝ) * t) • gmpKilledL2 G V hV (Real.toNNReal t)
      (physicalZeroBoundaryProjection V hd ω lam L hω f) = _
    rw [gmpKilledL2_projection]
  have hcont (V : Set (Vec d)) (hV : IsOpen V) : Continuous (F V hV) :=
    (physicalZeroBoundaryL2 V hd ω lam L hω).subtypeL.continuous.comp
      ((gmpKilledInteriorSemigroup G V hV).continuous_laplaceIntegrand μ (p V))
  have hbound (V : Set (Vec d)) (hV : IsOpen V) (t : ℝ) :
      ‖F V hV t‖ ≤ Real.exp (-(μ : ℝ) * t) * ‖f‖ := by
    rw [hF, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (gmpKilledL2_norm_le G V hV _ f)
      (Real.exp_pos _).le
  have hint (V : Set (Vec d)) (hV : IsOpen V) :
      (∫ t in Set.Ioi (0 : ℝ), F V hV t) =
        (gmpKilledInteriorResolvent G V hV μ (p V)).val := by
    exact (physicalZeroBoundaryL2 V hd ω lam L hω).subtypeL.integral_comp_comm
      ((gmpKilledInteriorSemigroup G V hV).integrableOn_laplaceIntegrand μ.property (p V))
  have ht := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) (f := F U hU)
    (fun t => Real.exp (-(μ : ℝ) * t) * ‖f‖)
    (fun n => (hcont (gmpCompactSurvivalInterior U n)
      (isOpen_gmpCompactSurvivalInterior U n)).aestronglyMeasurable.restrict)
    ((exp_neg_integrableOn_Ioi 0 μ.property).mul_const ‖f‖)
    (fun n => ae_of_all _ fun t => hbound (gmpCompactSurvivalInterior U n)
      (isOpen_gmpCompactSurvivalInterior U n) t)
    (ae_of_all _ fun t => by
      simp_rw [hF]
      exact tendsto_const_nhds.smul
        (tendsto_gmpKilledL2_compactSurvivalInterior G U hU (Real.toNNReal t) f))
  simpa only [hint, p] using ht


/-- A strong limit of bounded Hilbert-space lifts still has a bounded lift.
Banach–Alaoglu is applied to the Hilbert dual, and the adjoint identifies its
weak cluster point with the supplied strong limit. No separability is needed. -/
theorem exists_bounded_hilbert_lift_of_tendsto
    {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : H →L[ℝ] F) (x : ℕ → H) (R : ℝ) (hx : ∀ n, ‖x n‖ ≤ R)
    (y : F) (hy : Tendsto (fun n => A (x n)) atTop (𝓝 y)) :
    ∃ u : H, A u = y ∧ ‖u‖ ≤ R := by
  let qn (n : ℕ) : WeakDual ℝ H := StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (x n))
  obtain ⟨q, hq, hc⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) R).exists_mapClusterPt
    (u := qn) (f := atTop) (Filter.tendsto_principal.mpr (Filter.Eventually.of_forall (fun n => by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, qn,
        StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hx n)))
  let u : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual q)
  refine ⟨u, ?_, ?_⟩
  · apply ext_inner_right ℝ
    intro z
    have ht : Tendsto (fun n => qn n (A.adjoint z)) atTop (𝓝 (inner ℝ y z)) := by
      change Tendsto (fun n => inner ℝ (x n) (A.adjoint z)) atTop (𝓝 (inner ℝ y z))
      simp_rw [A.adjoint_inner_right]
      exact hy.inner (tendsto_const_nhds (x := z))
    have he := hc.continuousAt_comp (WeakDual.eval_continuous (A.adjoint z)).continuousAt
    have hscalar : q (A.adjoint z) = inner ℝ y z :=
      eq_of_nhds_neBot (he.clusterPt.mono ht)
    rw [← A.adjoint_inner_right]
    exact (InnerProductSpace.toDual_symm_apply (x := A.adjoint z)).trans hscalar
  · simpa only [u, LinearIsometryEquiv.norm_map, Set.mem_preimage,
      Metric.mem_closedBall, dist_zero_right] using hq


/-- On every open set, the actual killed resolvent has a representative in the
existing H¹₀ domain. Compact-interior resolvents supply uniformly bounded lifts;
their actual strong L² limit supplies the boundary-domain inclusion. -/
theorem gmpKilledInteriorResolvent_exists_zeroBoundary
    (U : Set (Vec d)) (hU : IsOpen U) (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    ∃ u : PhysicalH1Space hd lam,
      u ∈ physicalH1ZeroBoundary U hd lam ∧
      gmpPhysicalH1Value hd ω lam L hω u = (gmpKilledInteriorResolvent G U hU μ f).val ∧
      physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u) ≤
        4 * (μ : ℝ)⁻¹ * ‖f‖ ^ 2 ∧
      (Real.exp (-2 * L) * min 1 ((1 / 2 : ℝ) * L⁻¹)) * ‖u‖ ^ 2 ≤
        ((μ : ℝ)⁻¹ ^ 2 + 4 * (μ : ℝ)⁻¹) * ‖f‖ ^ 2 := by
  let V := gmpCompactSurvivalInterior U
  let p (n : ℕ) : physicalZeroBoundaryL2 (V n) hd ω lam L hω :=
    ⟨physicalZeroBoundaryProjection (V n) hd ω lam L hω f.val,
      physicalZeroBoundaryProjection_mem (V n) hd ω lam L hω f.val⟩
  have hex (n : ℕ) := gmpKilledInteriorResolvent_exists_zeroBoundary_bounded G
    U (V n) (closure (V n)) hU (isOpen_gmpCompactSurvivalInterior U n)
    (isCompact_closure_gmpCompactSurvivalInterior U n) subset_closure
    (closure_gmpCompactSurvivalInterior_subset U n) μ (p n)
  choose u hu hval _henergy hbound using hex
  let c := Real.exp (-2 * L) * min 1 ((1 / 2 : ℝ) * L⁻¹)
  let D := (μ : ℝ)⁻¹ ^ 2 + 4 * (μ : ℝ)⁻¹
  have hc : 0 < c := mul_pos (Real.exp_pos _)
    (lt_min zero_lt_one (mul_pos (by norm_num) (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hL))))
  have hD : 0 ≤ D := add_nonneg (sq_nonneg _)
    (mul_nonneg (by norm_num) (inv_nonneg.mpr μ.property.le))
  have hp (n : ℕ) : ‖p n‖ ≤ ‖f‖ :=
    (physicalZeroBoundaryL2 (V n) hd ω lam L hω).norm_starProjection_apply_le f.val
  have hn (n : ℕ) : ‖u n‖ ≤ Real.sqrt (D * ‖f‖ ^ 2 / c) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hc).mpr
    calc
      ‖u n‖ ^ 2 * c = c * ‖u n‖ ^ 2 := mul_comm _ _
      _ ≤ D * ‖p n‖ ^ 2 := hbound n
      _ ≤ D * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hp n) 2) hD
  let A := (gmpPhysicalH1ValueContinuousLinear hd ω lam L hω).comp
    (physicalH1ZeroBoundary U hd lam).subtypeL
  have ht : Tendsto (fun n => A ⟨u n, hu n⟩) atTop
      (𝓝 ((gmpKilledInteriorResolvent G U hU μ f).val)) := by
    have ht := tendsto_gmpKilledInteriorResolvent_compactSurvivalInterior G U hU μ f.val
    have hf : physicalZeroBoundaryProjection U hd ω lam L hω f.val = f.val :=
      (physicalZeroBoundaryL2 U hd ω lam L hω).starProjection_eq_self_iff.mpr f.property
    simp only [hf] at ht
    convert ht using 1
    funext n
    exact hval n
  obtain ⟨w, hw, _⟩ := exists_bounded_hilbert_lift_of_tendsto A
    (fun n => ⟨u n, hu n⟩) (Real.sqrt (D * ‖f‖ ^ 2 / c)) hn _ ht
  obtain ⟨v, hv, hE, hb⟩ := gmpKilledInteriorResolvent_exists_h1_bounded G U hU μ f
  have hwv : w.val = v := gmpPhysicalH1Value_injective hd ω lam L hω (hw.trans hv.symm)
  exact ⟨v, hwv ▸ w.property, hv, hE, hb⟩


/-- Every vector in the actual killed generator domain has a representative in
the existing zero-boundary H¹ graph, by inversion with its actual resolvent. -/
theorem gmpKilledInteriorGenerator_exists_zeroBoundary
    (U : Set (Vec d)) (hU : IsOpen U)
    (v : (gmpKilledInteriorSemigroup G U hU).generatorDomain) :
    ∃ u : PhysicalH1Space hd lam, u ∈ physicalH1ZeroBoundary U hd lam ∧
      gmpPhysicalH1Value hd ω lam L hω u = v.val.val := by
  let S := gmpKilledInteriorSemigroup G U hU
  let μ : MarkovProcess.Semigroup.PositiveShift := ⟨1, Set.mem_Ioi.mpr zero_lt_one⟩
  obtain ⟨u, hu, hv, _hE, _hb⟩ := gmpKilledInteriorResolvent_exists_zeroBoundary G U hU μ
    ((μ : ℝ) • v.val - S.generator v)
  refine ⟨u, hu, hv.trans ?_⟩
  exact congrArg Subtype.val (S.resolvent_smul_sub_generator μ v)

/-- On the actual killed generator domain, the literal form quotient converges
to the negative generator pairing. -/
theorem gmpKilledFormDifferenceQuotient_tendsto_generator
    (U : Set (Vec d)) (hU : IsOpen U)
    (u : (gmpKilledInteriorSemigroup G U hU).generatorDomain) :
    Tendsto (fun t => semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel G U hU) t u.val.val)
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (-inner ℝ ((gmpKilledInteriorSemigroup G U hU).generator u) u.val)) := by
  have ht := ((gmpKilledInteriorSemigroup G U hU).tendsto_generator u).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := u.val))
  apply ht.neg.congr
  intro t
  rw [gmpKilledFormDifferenceQuotient_eq_inner]
  change -(inner ℝ ((t : ℝ)⁻¹ •
    (gmpKilledL2Operator G U hU t u.val.val - u.val.val)) u.val.val) = _
  rw [real_inner_smul_left, inner_sub_left, inner_sub_left, one_div]
  change -((t : ℝ)⁻¹ *
    (inner ℝ (gmpKilledL2Operator G U hU t u.val.val) u.val.val -
      inner ℝ u.val.val u.val.val)) = _
  ring

/-- Every positive-time actual killed quotient of generator-domain data is
bounded by its exact negative generator pairing. -/
theorem gmpKilledFormDifferenceQuotient_le_neg_generator_inner
    (U : Set (Vec d)) (hU : IsOpen U)
    (u : (gmpKilledInteriorSemigroup G U hU).generatorDomain)
    (t : ℝ≥0) (ht : 0 < t) :
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) t
      u.val.val ≤ -inner ℝ ((gmpKilledInteriorSemigroup G U hU).generator u) u.val := by
  let a (n : ℕ) : ℝ≥0 := t / (n + 1 : ℕ)
  have ha (n : ℕ) : 0 < a n := div_pos ht (by positivity)
  have ht0 : Tendsto a atTop (𝓝[>] (0 : ℝ≥0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall ha⟩
    exact (tendsto_const_div_atTop_nhds_zero_nat t).comp (tendsto_add_atTop_nat 1)
  apply ge_of_tendsto ((gmpKilledFormDifferenceQuotient_tendsto_generator G U hU u).comp ht0)
  exact Filter.Eventually.of_forall fun n => by
    have h := gmpKilledFormDifferenceQuotient_nsmul_le G U hU (a n) (ha n)
      u.val.val u.val.property (n + 1) (Nat.succ_pos n)
    have he : (n + 1) • a n = t := by
      simp only [a, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      exact mul_div_cancel₀ t (by positivity)
    rwa [he] at h

/-- Bounded actual killed quotients control the defect of each normalized
Laplace resolvent. The estimate uses the literal exponentially weighted orbits. -/
theorem gmpKilledInteriorResolvent_inner_defect_le
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) (C : ℝ)
    (hC : ∀ t : ℝ≥0, 0 < t → semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel G U hU) t f.val ≤ C)
    (μ : MarkovProcess.Semigroup.PositiveShift) :
    inner ℝ (f - (μ : ℝ) • gmpKilledInteriorResolvent G U hU μ f) f ≤
      4 * (μ : ℝ)⁻¹ * C := by
  let S := gmpKilledInteriorSemigroup G U hU
  have hμ : 0 < (μ : ℝ) := μ.property
  have hh : 0 < (μ : ℝ) / 2 := half_pos hμ
  have hC0 : 0 ≤ C := (gmpKilledFormDifferenceQuotient_nonneg G U hU 1 f.val).trans
    (hC 1 zero_lt_one)
  let w (t : ℝ) := Real.exp (-(μ : ℝ) * t) • (f - S (Real.toNNReal t) f)
  have hwfun : w = (fun t : ℝ => Real.exp (-(μ : ℝ) * t) • f) -
      S.laplaceIntegrand μ f := by
    funext t
    simp only [w, Pi.sub_apply, S.laplaceIntegrand_apply, smul_sub]
  have hi : IntegrableOn w (Set.Ioi 0) := by
    rw [hwfun]
    exact ((exp_neg_integrableOn_Ioi 0 hμ).smul_const f).sub
      (S.integrableOn_laplaceIntegrand hμ f)
  have hw : (∫ t in Set.Ioi (0 : ℝ), w t) =
      (μ : ℝ)⁻¹ • f - S.resolvent μ f := by
    rw [hwfun]
    change (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(μ : ℝ) * t) • f - S.laplaceIntegrand μ f t) = _
    rw [integral_sub ((exp_neg_integrableOn_Ioi 0 hμ).smul_const f)
      (S.integrableOn_laplaceIntegrand hμ f), integral_smul_const,
      MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hμ]
    rfl
  have htexp (t : ℝ) : t * Real.exp (-(μ : ℝ) * t) ≤
      2 * (μ : ℝ)⁻¹ * Real.exp (-((μ : ℝ) / 2) * t) := by
    have hx : ((μ : ℝ) / 2) * t ≤ Real.exp (((μ : ℝ) / 2) * t) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    have hx' := mul_le_mul_of_nonneg_right hx (Real.exp_pos (-(μ : ℝ) * t)).le
    rw [← Real.exp_add] at hx'
    have he : ((μ : ℝ) / 2) * t + -(μ : ℝ) * t = -((μ : ℝ) / 2) * t := by ring
    rw [he] at hx'
    calc
      _ ≤ Real.exp (-((μ : ℝ) / 2) * t) / ((μ : ℝ) / 2) :=
        (le_div_iff₀ hh).mpr (by nlinarith only [hx'])
      _ = _ := by field_simp [hμ.ne']
  have hb : (∫ t in Set.Ioi (0 : ℝ), inner ℝ f (w t)) ≤
      2 * (μ : ℝ)⁻¹ * C * ((μ : ℝ) / 2)⁻¹ := by
    rw [← MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hh, ← integral_const_mul]
    apply integral_mono_ae (hi.const_inner f)
      ((exp_neg_integrableOn_Ioi 0 hh).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < Real.toNNReal t := Real.toNNReal_pos.mpr ht
    have hq := hC (Real.toNNReal t) ht'
    rw [gmpKilledFormDifferenceQuotient_eq_inner, Real.coe_toNNReal t ht.le,
      one_div, ← div_eq_inv_mul] at hq
    have hq' : inner ℝ (f - S (Real.toNNReal t) f) f ≤ C * t :=
      (div_le_iff₀ ht).mp hq
    calc
      inner ℝ f (w t) = Real.exp (-(μ : ℝ) * t) *
          inner ℝ (f - S (Real.toNNReal t) f) f := by
        change inner ℝ f.val (Real.exp (-(μ : ℝ) * t) •
          (f.val - (S (Real.toNNReal t) f).val)) = _
        rw [real_inner_smul_right, real_inner_comm]
        rfl
      _ ≤ Real.exp (-(μ : ℝ) * t) * (C * t) :=
        mul_le_mul_of_nonneg_left hq' (Real.exp_pos _).le
      _ = C * (t * Real.exp (-(μ : ℝ) * t)) := by ring
      _ ≤ C * (2 * (μ : ℝ)⁻¹ * Real.exp (-((μ : ℝ) / 2) * t)) :=
        mul_le_mul_of_nonneg_left (htexp t) hC0
      _ = _ := by ring
  rw [integral_inner hi, hw] at hb
  have he : inner ℝ (f - (μ : ℝ) • gmpKilledInteriorResolvent G U hU μ f) f =
      (μ : ℝ) * inner ℝ f ((μ : ℝ)⁻¹ • f - S.resolvent μ f) := by
    change inner ℝ (f.val - (μ : ℝ) • (S.resolvent μ f).val) f.val =
      (μ : ℝ) * inner ℝ f.val ((μ : ℝ)⁻¹ • f.val - (S.resolvent μ f).val)
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (S.resolvent μ f).val f.val]
    field_simp [hμ.ne']
  rw [he]
  calc
    _ ≤ (μ : ℝ) * (2 * (μ : ℝ)⁻¹ * C * ((μ : ℝ) / 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hb hμ.le
    _ = _ := by
      field_simp [hμ.ne']
      ring

/-- Actual normalized killed resolvents preserve a uniform form bound, up to a
fixed numerical factor independent of the positive shift and the killing set. -/
theorem gmpKilledFormDifferenceQuotient_scaledResolvent_le
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) (C : ℝ)
    (hC : ∀ t : ℝ≥0, 0 < t → semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel G U hU) t f.val ≤ C)
    (μ : MarkovProcess.Semigroup.PositiveShift) (t : ℝ≥0) (ht : 0 < t) :
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) t
      (((μ : ℝ) • gmpKilledInteriorResolvent G U hU μ f).val) ≤ 4 * C := by
  have hμ : 0 < (μ : ℝ) := μ.property
  let S := gmpKilledInteriorSemigroup G U hU
  let v : S.generatorDomain := ⟨S.resolvent μ f, S.resolvent_mem_generatorDomain μ f⟩
  let r : S.generatorDomain := (μ : ℝ) • v
  have hgen : S.generator r = (μ : ℝ) • ((μ : ℝ) • v.val - f) := by
    change S.generator ((μ : ℝ) • v) = _
    rw [map_smul]
    exact congrArg ((μ : ℝ) • ·) (S.generator_resolvent μ f)
  have he : -inner ℝ (S.generator r) r.val =
      (μ : ℝ) * inner ℝ (f - r.val) f - (μ : ℝ) * ‖f - r.val‖ ^ 2 := by
    rw [hgen]
    change -inner ℝ ((μ : ℝ) • (r.val.val - f.val)) r.val.val =
      (μ : ℝ) * inner ℝ (f.val - r.val.val) f.val -
        (μ : ℝ) * ‖f.val - r.val.val‖ ^ 2
    rw [← real_inner_self_eq_norm_sq]
    simp only [real_inner_smul_left, inner_sub_left, inner_sub_right]
    rw [real_inner_comm r.val.val f.val]
    ring
  have hb := mul_le_mul_of_nonneg_left
    (gmpKilledInteriorResolvent_inner_defect_le G U hU f C hC μ) μ.property.le
  have hb' : (μ : ℝ) * inner ℝ (f - r.val) f ≤ 4 * C := by
    change (μ : ℝ) * inner ℝ
      (f - (μ : ℝ) • gmpKilledInteriorResolvent G U hU μ f) f ≤ _
    calc
      _ ≤ (μ : ℝ) * (4 * (μ : ℝ)⁻¹ * C) := hb
      _ = _ := by field_simp [hμ.ne']
  have hg : -inner ℝ (S.generator r) r.val ≤ 4 * C := by
    rw [he]
    exact (sub_le_self _ (mul_nonneg μ.property.le (sq_nonneg _))).trans hb'
  exact (gmpKilledFormDifferenceQuotient_le_neg_generator_inner G U hU r t ht).trans hg

/-- Bounded literal killed form quotients give a representative in the actual
completed zero-boundary H¹ space, on every open domain. Normalized resolvents
supply bounded H¹₀ lifts whose values converge strongly to the original datum. -/
theorem exists_zeroBoundary_of_bounded_gmpKilledFormDifferenceQuotient
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∃ C : ℝ, ∀ t : ℝ≥0, 0 < t → semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel G U hU) t f ≤ C) :
    ∃ u : PhysicalH1Space hd lam, u ∈ physicalH1ZeroBoundary U hd lam ∧
      gmpPhysicalH1Value hd ω lam L hω u = f := by
  obtain ⟨C, hC⟩ := hf
  let f₀ : physicalZeroBoundaryL2 U hd ω lam L hω :=
    ⟨f, mem_physicalZeroBoundaryL2_of_bounded_gmpKilledFormDifferenceQuotient G U hU f ⟨C, hC⟩⟩
  let S := gmpKilledInteriorSemigroup G U hU
  let R := S.toContractiveResolvent
  let μ (n : ℕ) : MarkovProcess.Semigroup.PositiveShift :=
    ⟨(n : ℝ) + 1, Set.mem_Ioi.mpr (by positivity)⟩
  have hμ : Tendsto μ atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro α
    obtain ⟨n, hn⟩ := exists_nat_ge (α : ℝ)
    refine ⟨n, fun m hm => ?_⟩
    change (α : ℝ) ≤ (m : ℝ) + 1
    exact hn.trans ((Nat.cast_le.mpr hm).trans (le_add_of_nonneg_right zero_le_one))
  have hex (n : ℕ) : ∃ u : PhysicalH1Space hd lam,
      u ∈ physicalH1ZeroBoundary U hd lam ∧
      gmpPhysicalH1Value hd ω lam L hω u = (R.scaledOperator (μ n) f₀).val := by
    obtain ⟨u, hu, hv, _hE, _hb⟩ :=
      gmpKilledInteriorResolvent_exists_zeroBoundary G U hU (μ n) f₀
    refine ⟨(μ n : ℝ) • u, (physicalH1ZeroBoundary U hd lam).smul_mem _ hu, ?_⟩
    exact ((gmpPhysicalH1ValueContinuousLinear hd ω lam L hω).map_smul
      (μ n : ℝ) (u : GMPForceH1 hd lam)).trans
        (congrArg (fun z => (μ n : ℝ) • z) hv)
  choose u hu hv using hex
  have hE (n : ℕ) : physicalH1FormEnergy ω hd lam
      (physicalH1SpaceRepresentative hd lam (u n)) ≤ 8 * C := by
    have he := physicalH1FormEnergy_le_two_mul_of_killed_bound G U hU (u n) (4 * C)
      (fun t ht => by
        rw [hv n]
        exact gmpKilledFormDifferenceQuotient_scaledResolvent_le G U hU f₀ C hC (μ n) t ht)
    linarith only [he]
  have hm (n : ℕ) : ‖gmpPhysicalH1Value hd ω lam L hω (u n)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [hv n]
    exact pow_le_pow_left₀ (norm_nonneg _) (R.norm_scaledOperator_apply_le (μ n) f₀) 2
  let c := Real.exp (-2 * L) * min 1 ((1 / 2 : ℝ) * L⁻¹)
  have hc : 0 < c := mul_pos (Real.exp_pos _)
    (lt_min zero_lt_one (mul_pos (by norm_num) (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hL))))
  have hb (n : ℕ) : c * ‖u n‖ ^ 2 ≤ ‖f‖ ^ 2 + 8 * C := by
    have hb := gmpPhysicalH1Energy_coercive hd ω lam L hL hω (u n)
    have heq : gmpPhysicalH1Energy hd ω lam L hω (u n) (u n) =
        physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam (u n)) :=
      (gmpPhysicalH1Energy_eq_source hd ω lam L hω (u n) (u n)).trans
        (sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd lam L hω (u n))
    rw [heq] at hb
    exact hb.trans (add_le_add (hm n) (hE n))
  have hn (n : ℕ) : ‖u n‖ ≤ Real.sqrt ((‖f‖ ^ 2 + 8 * C) / c) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using hb n
  let A := (gmpPhysicalH1ValueContinuousLinear hd ω lam L hω).comp
    (physicalH1ZeroBoundary U hd lam).subtypeL
  have ht : Tendsto (fun n => A ⟨u n, hu n⟩) atTop (𝓝 f) := by
    have ht := (R.tendsto_scaledOperator_apply f₀).comp hμ
    have ht' := ((physicalZeroBoundaryL2 U hd ω lam L hω).subtypeL.continuous.tendsto f₀).comp ht
    exact ht'.congr (fun n => (hv n).symm)
  obtain ⟨w, hw, _⟩ := exists_bounded_hilbert_lift_of_tendsto A
    (fun n => ⟨u n, hu n⟩) (Real.sqrt ((‖f‖ ^ 2 + 8 * C) / c)) hn f ht
  exact ⟨w.val, w.property, hw⟩

/-- The actual killed form domain is exactly the value image of the existing
zero-boundary H¹ space. The boundary space keeps its original smooth-core closure. -/
theorem gmpKilledFormDomain_iff_zeroBoundary
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (∃ C : ℝ, ∀ t : ℝ≥0, 0 < t → semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel G U hU) t f ≤ C) ↔
      ∃ u : PhysicalH1Space hd lam, u ∈ physicalH1ZeroBoundary U hd lam ∧
        gmpPhysicalH1Value hd ω lam L hω u = f := by
  constructor
  · exact exists_zeroBoundary_of_bounded_gmpKilledFormDifferenceQuotient G U hU f
  · rintro ⟨u, hu, rfl⟩
    exact ⟨physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u),
      fun t ht => gmpKilledFormDifferenceQuotient_le_of_zeroBoundary G U hU t ht u hu⟩

/-- Bounded lifts under an injective continuous Hilbert-space map converge
against every continuous linear functional when their images converge strongly.
Only weak compactness is used; no compactness of the original embedding is assumed. -/
theorem tendsto_functional_of_bounded_hilbert_lifts
    {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : H →L[ℝ] F) (hA : Function.Injective A)
    (x : ℕ → H) (R : ℝ) (hx : ∀ n, ‖x n‖ ≤ R)
    (y : H) (hy : Tendsto (fun n => A (x n)) atTop (𝓝 (A y)))
    (ell : H →L[ℝ] ℝ) :
    Tendsto (fun n => ell (x n)) atTop (𝓝 (ell y)) := by
  let qn (n : ℕ) : WeakDual ℝ H := StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (x n))
  let qy : WeakDual ℝ H := StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y)
  have hw : Tendsto qn atTop (𝓝 qy) := by
    apply (WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) R).tendsto_nhds_of_unique_mapClusterPt
    · exact Filter.Eventually.of_forall fun n => by
        simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, qn,
          StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hx n
    · intro q _hq hc
      let u : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual q)
      have hau : A u = A y := by
        apply ext_inner_right ℝ
        intro z
        have ht : Tendsto (fun n => qn n (A.adjoint z)) atTop (𝓝 (inner ℝ (A y) z)) := by
          change Tendsto (fun n => inner ℝ (x n) (A.adjoint z)) atTop (𝓝 (inner ℝ (A y) z))
          simp_rw [A.adjoint_inner_right]
          exact hy.inner (tendsto_const_nhds (x := z))
        have he := hc.continuousAt_comp (WeakDual.eval_continuous (A.adjoint z)).continuousAt
        have hscalar : q (A.adjoint z) = inner ℝ (A y) z :=
          eq_of_nhds_neBot (he.clusterPt.mono ht)
        rw [← A.adjoint_inner_right]
        exact (InnerProductSpace.toDual_symm_apply (x := A.adjoint z)).trans hscalar
      have huy : u = y := hA hau
      apply WeakDual.toStrongDual.injective
      ext z
      change q z = inner ℝ y z
      rw [← huy]
      exact (InnerProductSpace.toDual_symm_apply (x := z)).symm
  let z : H := (InnerProductSpace.toDual ℝ H).symm ell
  have he := ((WeakDual.eval_continuous z).tendsto qy).comp hw
  have heq (v : H) : inner ℝ v z = ell v :=
    (real_inner_comm v z).symm.trans (InnerProductSpace.toDual_symm_apply (x := v))
  change Tendsto (fun n => inner ℝ (x n) z) atTop (𝓝 (inner ℝ y z)) at he
  simpa only [heq] using he

/-- The actual physical mass-plus-energy form as a continuous bilinear map
on the existing weighted H¹ space. -/
noncomputable def gmpPhysicalH1ResolventBilinear
    (μ : MarkovProcess.Semigroup.PositiveShift) :
    PhysicalH1Space hd lam →L[ℝ] PhysicalH1Space hd lam →L[ℝ] ℝ := by
  let J := gmpPhysicalH1ValueContinuousLinear hd ω lam L hω
  let E := gmpPhysicalH1Energy hd ω lam L hω
  have hsymm (u v : GMPForceH1 hd lam) : E u v = E v u :=
    gmpPhysicalH1Energy_symm hd ω lam L hω u v
  have hadd (u v w : GMPForceH1 hd lam) : E (u + v) w = E u w + E v w :=
    gmpPhysicalH1Energy_add_left hd ω lam L hL hω u v w
  have hsmul (c : ℝ) (u v : GMPForceH1 hd lam) : E (c • u) v = c * E u v :=
    gmpPhysicalH1Energy_smul_left hd ω lam L hω c u v
  let B : GMPForceH1 hd lam →ₗ[ℝ] GMPForceH1 hd lam →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => (μ : ℝ) * inner ℝ (J u) (J v) + E u v)
      (by intro u v w; rw [J.map_add, inner_add_left, hadd]; ring)
      (by intro c u v; rw [J.map_smul, real_inner_smul_left, hsmul]; simp only [smul_eq_mul]; ring)
      (by intro u v w; rw [J.map_add, inner_add_right, hsymm u (v+w), hadd,
          hsymm v u, hsymm w u]; ring)
      (by intro c u v; rw [J.map_smul, inner_smul_right, hsymm u (c • v), hsmul,
          hsymm v u]; simp only [smul_eq_mul]; ring)
  exact B.mkContinuous₂ (Real.exp (2 * L) * ((μ : ℝ) + L / 2)) (fun u v => by
    change |(μ : ℝ) * inner ℝ (gmpPhysicalH1Value hd ω lam L hω u)
      (gmpPhysicalH1Value hd ω lam L hω v) +
      gmpPhysicalH1Energy hd ω lam L hω u v| ≤ _
    rw [gmpPhysicalH1Energy_eq_source]
    exact sourcePhysicalResolventForm_bounded hd ω lam L (μ : ℝ) hL hω μ.property u v)

/-- This continuous bilinear map retains the actual speed measure, matrix
coefficient and weighted weak gradient, without changing the physical form. -/
theorem gmpPhysicalH1ResolventBilinear_apply
    (μ : MarkovProcess.Semigroup.PositiveShift) (u v : PhysicalH1Space hd lam) :
    gmpPhysicalH1ResolventBilinear (hd := hd) (hL := hL) (hω := hω) μ u v =
      (μ : ℝ) * inner ℝ (gmpPhysicalH1Value hd ω lam L hω u)
        (gmpPhysicalH1Value hd ω lam L hω v) +
      gmpPhysicalH1Energy hd ω lam L hω u v := rfl

/-- Compact-interior actual killed resolvents admit lifts in the original
H¹₀(U) whose values converge strongly and whose every continuous linear test
converges to the unique actual killed-resolvent lift on U. -/
theorem gmpKilledInteriorResolvent_exists_zeroBoundary_weakExhaustion
    (U : Set (Vec d)) (hU : IsOpen U) (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    let V := gmpCompactSurvivalInterior U
    let p (n : ℕ) : physicalZeroBoundaryL2 (V n) hd ω lam L hω :=
      ⟨physicalZeroBoundaryProjection (V n) hd ω lam L hω f.val,
        physicalZeroBoundaryProjection_mem (V n) hd ω lam L hω f.val⟩
    ∃ u : physicalH1ZeroBoundary U hd lam,
      ∃ v : ℕ → physicalH1ZeroBoundary U hd lam,
        gmpPhysicalH1Value hd ω lam L hω u.val = (gmpKilledInteriorResolvent G U hU μ f).val ∧
        (∀ n, gmpPhysicalH1Value hd ω lam L hω (v n).val =
          (gmpKilledInteriorResolvent G (V n) (isOpen_gmpCompactSurvivalInterior U n) μ (p n)).val) ∧
        ∀ ell : physicalH1ZeroBoundary U hd lam →L[ℝ] ℝ,
          Tendsto (fun n => ell (v n)) atTop (𝓝 (ell u)) := by
  let V := gmpCompactSurvivalInterior U
  let p (n : ℕ) : physicalZeroBoundaryL2 (V n) hd ω lam L hω :=
    ⟨physicalZeroBoundaryProjection (V n) hd ω lam L hω f.val,
      physicalZeroBoundaryProjection_mem (V n) hd ω lam L hω f.val⟩
  obtain ⟨u, hu, hv, _hE, _hb⟩ := gmpKilledInteriorResolvent_exists_zeroBoundary G U hU μ f
  have hex (n : ℕ) := gmpKilledInteriorResolvent_exists_zeroBoundary_bounded G
    U (V n) (closure (V n)) hU (isOpen_gmpCompactSurvivalInterior U n)
    (isCompact_closure_gmpCompactSurvivalInterior U n) subset_closure
    (closure_gmpCompactSurvivalInterior_subset U n) μ (p n)
  choose v hvm hvval _hvE hvbound using hex
  let c := Real.exp (-2 * L) * min 1 ((1 / 2 : ℝ) * L⁻¹)
  let D := (μ : ℝ)⁻¹ ^ 2 + 4 * (μ : ℝ)⁻¹
  have hc : 0 < c := mul_pos (Real.exp_pos _)
    (lt_min zero_lt_one (mul_pos (by norm_num) (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hL))))
  have hD : 0 ≤ D := add_nonneg (sq_nonneg _)
    (mul_nonneg (by norm_num) (inv_nonneg.mpr μ.property.le))
  have hp (n : ℕ) : ‖p n‖ ≤ ‖f‖ :=
    (physicalZeroBoundaryL2 (V n) hd ω lam L hω).norm_starProjection_apply_le f.val
  have hn (n : ℕ) : ‖v n‖ ≤ Real.sqrt (D * ‖f‖ ^ 2 / c) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hc).mpr
    calc
      ‖v n‖ ^ 2 * c = c * ‖v n‖ ^ 2 := mul_comm _ _
      _ ≤ D * ‖p n‖ ^ 2 := hvbound n
      _ ≤ D * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hp n) 2) hD
  let A := (gmpPhysicalH1ValueContinuousLinear hd ω lam L hω).comp
    (physicalH1ZeroBoundary U hd lam).subtypeL
  have hA : Function.Injective A := by
    intro a b hab
    apply Subtype.ext
    exact gmpPhysicalH1Value_injective hd ω lam L hω hab
  have ht : Tendsto (fun n => A ⟨v n, hvm n⟩) atTop (𝓝 (A ⟨u, hu⟩)) := by
    have ht := tendsto_gmpKilledInteriorResolvent_compactSurvivalInterior G U hU μ f.val
    have hf : physicalZeroBoundaryProjection U hd ω lam L hω f.val = f.val :=
      (physicalZeroBoundaryL2 U hd ω lam L hω).starProjection_eq_self_iff.mpr f.property
    simp only [hf] at ht
    change Tendsto (fun n => gmpPhysicalH1Value hd ω lam L hω (v n)) atTop
      (𝓝 (gmpPhysicalH1Value hd ω lam L hω u))
    rw [hv]
    exact ht.congr (fun n => (hvval n).symm)
  refine ⟨⟨u, hu⟩, (fun n => ⟨v n, hvm n⟩), hv, hvval, ?_⟩
  intro ell
  exact tendsto_functional_of_bounded_hilbert_lifts A hA
    (fun n => ⟨v n, hvm n⟩) (Real.sqrt (D * ‖f‖ ^ 2 / c)) hn ⟨u, hu⟩ ht ell

/-- The physical mixed resolvent form passes through the actual compact-interior
killed-resolvent exhaustion, against every original H¹₀(U) test. This is a limit
statement; it does not assume that either resolvent solves the variational equation. -/
theorem gmpKilledInteriorResolvent_exists_zeroBoundary_mixedExhaustion
    (U : Set (Vec d)) (hU : IsOpen U) (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    let V := gmpCompactSurvivalInterior U
    let p (n : ℕ) : physicalZeroBoundaryL2 (V n) hd ω lam L hω :=
      ⟨physicalZeroBoundaryProjection (V n) hd ω lam L hω f.val,
        physicalZeroBoundaryProjection_mem (V n) hd ω lam L hω f.val⟩
    ∃ u : physicalH1ZeroBoundary U hd lam,
      ∃ v : ℕ → physicalH1ZeroBoundary U hd lam,
        gmpPhysicalH1Value hd ω lam L hω u.val = (gmpKilledInteriorResolvent G U hU μ f).val ∧
        (∀ n, gmpPhysicalH1Value hd ω lam L hω (v n).val =
          (gmpKilledInteriorResolvent G (V n) (isOpen_gmpCompactSurvivalInterior U n) μ (p n)).val) ∧
        ∀ w : physicalH1ZeroBoundary U hd lam,
          Tendsto (fun n => (μ : ℝ) *
            inner ℝ (gmpPhysicalH1Value hd ω lam L hω (v n).val)
              (gmpPhysicalH1Value hd ω lam L hω w.val) +
            gmpPhysicalH1Energy hd ω lam L hω (v n).val w.val) atTop
            (𝓝 ((μ : ℝ) * inner ℝ (gmpPhysicalH1Value hd ω lam L hω u.val)
              (gmpPhysicalH1Value hd ω lam L hω w.val) +
              gmpPhysicalH1Energy hd ω lam L hω u.val w.val)) := by
  obtain ⟨u, v, hu, hv, ht⟩ :=
    gmpKilledInteriorResolvent_exists_zeroBoundary_weakExhaustion G U hU μ f
  refine ⟨u, v, hu, hv, ?_⟩
  intro w
  let B := gmpPhysicalH1ResolventBilinear (hd := hd) (lam := lam) (hL := hL) (hω := hω) μ
  let ell := (B.flip w.val).comp (physicalH1ZeroBoundary U hd lam).subtypeL
  simpa only [ell, B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    Submodule.subtypeL_apply, gmpPhysicalH1ResolventBilinear_apply] using ht ell

/-- The mixed short-time quotient of the actual killed resolvent has its
literal generator limit against every test in the existing interior L² carrier. -/
theorem gmpKilledInteriorResolvent_tendsto_mixedQuotient
    (U : Set (Vec d)) (hU : IsOpen U) (μ : MarkovProcess.Semigroup.PositiveShift)
    (f g : physicalZeroBoundaryL2 U hd ω lam L hω) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      inner ℝ ((gmpKilledInteriorResolvent G U hU μ f).val -
        gmpKilledL2Operator G U hU t (gmpKilledInteriorResolvent G U hU μ f).val) g.val)
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (inner ℝ (f - (μ : ℝ) • gmpKilledInteriorResolvent G U hU μ f) g)) := by
  let S := gmpKilledInteriorSemigroup G U hU
  let v : S.generatorDomain := ⟨S.resolvent μ f, S.resolvent_mem_generatorDomain μ f⟩
  have ht := ((S.tendsto_generator v).inner (𝕜 := ℝ) (tendsto_const_nhds (x := g))).neg
  have he : -inner ℝ (S.generator v) g =
      inner ℝ (f - (μ : ℝ) • gmpKilledInteriorResolvent G U hU μ f) g := by
    change -inner ℝ (S.generator ⟨S.resolvent μ f, S.resolvent_mem_generatorDomain μ f⟩) g = _
    rw [S.generator_resolvent]
    change -inner ℝ ((μ : ℝ) • (S.resolvent μ f).val - f.val) g.val =
      inner ℝ (f.val - (μ : ℝ) • (S.resolvent μ f).val) g.val
    simp only [inner_sub_left, real_inner_smul_left]
    ring
  rw [he] at ht
  apply ht.congr
  intro t
  change -inner ℝ ((t : ℝ)⁻¹ •
    (gmpKilledL2Operator G U hU t (gmpKilledInteriorResolvent G U hU μ f).val -
      (gmpKilledInteriorResolvent G U hU μ f).val)) g.val = _
  rw [real_inner_smul_left, inner_sub_left, inner_sub_left]
  ring


/-- Pull the actual killed generator domain back to the original completed
zero-boundary graph. No replacement boundary space is used. -/
def gmpKilledGeneratorFormDomain (U : Set (Vec d)) (hU : IsOpen U) :
    Submodule ℝ (physicalH1ZeroBoundary U hd lam) :=
  (gmpKilledInteriorSemigroup G U hU).generatorDomain.comap
    (physicalZeroBoundaryInteriorValue U hd ω lam L hω).toLinearMap

/-- Normalized actual killed resolvents weakly approximate every vector of the
original H¹₀ domain, with all approximants in the actual generator domain. -/
theorem gmpKilledGeneratorFormDomain_exists_weakApproximation
    (U : Set (Vec d)) (hU : IsOpen U) (u : physicalH1ZeroBoundary U hd lam) :
    let μ (n : ℕ) : MarkovProcess.Semigroup.PositiveShift :=
      ⟨(n : ℝ) + 1, Set.mem_Ioi.mpr (by positivity)⟩
    ∃ v : ℕ → physicalH1ZeroBoundary U hd lam,
      (∀ n, physicalZeroBoundaryInteriorValue U hd ω lam L hω (v n) =
        (μ n : ℝ) • gmpKilledInteriorResolvent G U hU (μ n)
          (physicalZeroBoundaryInteriorValue U hd ω lam L hω u)) ∧
      (∀ n, v n ∈ gmpKilledGeneratorFormDomain G U hU) ∧
      ∀ ell : physicalH1ZeroBoundary U hd lam →L[ℝ] ℝ,
        Tendsto (fun n => ell (v n)) atTop (𝓝 (ell u)) := by
  let μ (n : ℕ) : MarkovProcess.Semigroup.PositiveShift :=
    ⟨(n : ℝ) + 1, Set.mem_Ioi.mpr (by positivity)⟩
  let S := gmpKilledInteriorSemigroup G U hU
  let R := S.toContractiveResolvent
  let J := physicalZeroBoundaryInteriorValue U hd ω lam L hω
  let f := J u
  let C := physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u.val)
  have hC (t : ℝ≥0) (ht : 0 < t) : semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel G U hU) t f.val ≤ C :=
    gmpKilledFormDifferenceQuotient_le_of_zeroBoundary G U hU t ht u.val u.property
  have hex (n : ℕ) : ∃ v : physicalH1ZeroBoundary U hd lam,
      J v = R.scaledOperator (μ n) f := by
    obtain ⟨v, hv, hval, _hE, _hb⟩ :=
      gmpKilledInteriorResolvent_exists_zeroBoundary G U hU (μ n) f
    refine ⟨(μ n : ℝ) • (⟨v, hv⟩ : physicalH1ZeroBoundary U hd lam), ?_⟩
    rw [J.map_smul]
    apply congrArg (fun z => (μ n : ℝ) • z)
    exact Subtype.ext hval
  choose v hv using hex
  have hE (n : ℕ) : physicalH1FormEnergy ω hd lam
      (physicalH1SpaceRepresentative hd lam (v n).val) ≤ 8 * C := by
    have he := physicalH1FormEnergy_le_two_mul_of_killed_bound G U hU (v n).val (4 * C)
      (fun t ht => by
        change semigroupFormDifferenceQuotient ω hd lam
          (gmpKilledEndpointKernel G U hU) t (J (v n)).val ≤ 4 * C
        rw [hv n]
        exact gmpKilledFormDifferenceQuotient_scaledResolvent_le G U hU f C hC (μ n) t ht)
    linarith only [he]
  have hm (n : ℕ) : ‖gmpPhysicalH1Value hd ω lam L hω (v n).val‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    change ‖J (v n)‖ ^ 2 ≤ ‖f‖ ^ 2
    rw [hv n]
    exact pow_le_pow_left₀ (norm_nonneg _) (R.norm_scaledOperator_apply_le (μ n) f) 2
  let c := Real.exp (-2 * L) * min 1 ((1 / 2 : ℝ) * L⁻¹)
  have hc : 0 < c := mul_pos (Real.exp_pos _)
    (lt_min zero_lt_one (mul_pos (by norm_num) (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hL))))
  have hb (n : ℕ) : c * ‖v n‖ ^ 2 ≤ ‖f‖ ^ 2 + 8 * C := by
    have he := gmpPhysicalH1Energy_coercive hd ω lam L hL hω (v n).val
    have heq : gmpPhysicalH1Energy hd ω lam L hω (v n).val (v n).val =
        physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam (v n).val) :=
      (gmpPhysicalH1Energy_eq_source hd ω lam L hω (v n).val (v n).val).trans
        (sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd lam L hω (v n).val)
    rw [heq] at he
    exact he.trans (add_le_add (hm n) (hE n))
  have hn (n : ℕ) : ‖v n‖ ≤ Real.sqrt ((‖f‖ ^ 2 + 8 * C) / c) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using hb n
  have hμ : Tendsto μ atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro α
    obtain ⟨n, hn⟩ := exists_nat_ge (α : ℝ)
    refine ⟨n, fun m hm => ?_⟩
    change (α : ℝ) ≤ (m : ℝ) + 1
    exact hn.trans ((Nat.cast_le.mpr hm).trans (le_add_of_nonneg_right zero_le_one))
  have ht : Tendsto (fun n => J (v n)) atTop (𝓝 (J u)) :=
    ((R.tendsto_scaledOperator_apply f).comp hμ).congr (fun n => (hv n).symm)
  have hJ : Function.Injective J := by
    intro a b hab
    apply Subtype.ext
    exact gmpPhysicalH1Value_injective hd ω lam L hω (congrArg Subtype.val hab)
  refine ⟨v, hv, ?_, ?_⟩
  · intro n
    change J (v n) ∈ S.generatorDomain
    rw [hv n]
    exact S.generatorDomain.smul_mem _ (S.resolvent_mem_generatorDomain (μ n) f)
  · exact tendsto_functional_of_bounded_hilbert_lifts J hJ v
      (Real.sqrt ((‖f‖ ^ 2 + 8 * C) / c)) hn u ht

/-- The actual killed generator domain is a form core in the original full
weighted H¹₀ norm on every open set. Weak normalized-resolvent approximation
annihilates the orthogonal complement of its graph pullback. -/
theorem dense_gmpKilledGeneratorFormDomain (U : Set (Vec d)) (hU : IsOpen U) :
    Dense (gmpKilledGeneratorFormDomain G U hU : Set (physicalH1ZeroBoundary U hd lam)) := by
  let M := gmpKilledGeneratorFormDomain G U hU
  have horth : Mᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro u hu
    change u = 0
    obtain ⟨v, _hval, hv, ht⟩ :=
      gmpKilledGeneratorFormDomain_exists_weakApproximation G U hU u
    have hz (n : ℕ) : inner ℝ u (v n) = 0 :=
      (Submodule.mem_orthogonal' M u).mp hu (v n) (hv n)
    have hlim := ht (InnerProductSpace.toDual ℝ (physicalH1ZeroBoundary U hd lam) u)
    change Tendsto (fun n => inner ℝ u (v n)) atTop (𝓝 (inner ℝ u u)) at hlim
    have he : inner ℝ u u = 0 := tendsto_nhds_unique (hlim.congr hz) tendsto_const_nhds
    exact (inner_self_eq_zero.mp he)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [← M.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]

/-- Every original zero-boundary graph vector can be approximated in its full
H¹ norm by a graph vector whose physical value belongs to the actual killed
generator domain. -/
theorem exists_gmpKilledGeneratorFormDomain_norm_sub_lt
    (U : Set (Vec d)) (hU : IsOpen U) (u : physicalH1ZeroBoundary U hd lam)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v ∈ gmpKilledGeneratorFormDomain G U hU, ‖v - u‖ < ε := by
  obtain ⟨v, hv, hdist⟩ := (dense_gmpKilledGeneratorFormDomain G U hU).exists_dist_lt u hε
  exact ⟨v, hv, by simpa only [dist_eq_norm, norm_sub_rev] using hdist⟩

end EinsteinFull
