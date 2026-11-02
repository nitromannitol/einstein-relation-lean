import EinsteinFull.Calculus.ComplexTranslationSupport
import EinsteinFull.Calculus.S4MartingaleSllnSupport
import EinsteinFull.Calculus.ComplexGeneratorSpatialSupport
import EinsteinRelation.Correctors.HorizontalCharacterizationSupport
import EinsteinFull.Calculus.S4ReducedCoefficientSupport
import EinsteinRelation.Entropy.EllipticRegularity
import EinsteinFull.Frozen.ComplexHorizontalGradient
import EinsteinFull.Frozen.ReducedLawProbability
import EinsteinFull.Frozen.ReducedLawStationary
import EinsteinRelation.Environment.ReductionEmbedding
import EinsteinRelation.Correctors.HorizontalCoreLpApproximation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Value and horizontal H1 approximation at the physical starting environment.

Point-start convergence follows along an L2 subsequence. Horizontal convolution
also approximates a given function and its actual gradient together. The scalar
generator commutator has a scale-uniform L2 bound and converges to zero for
each fixed L2 vector field, retaining the actual coefficients. The actual
resolvent has a mollified generator graph approximation. Passing that approximation
through the supplied process occupation remains a separate obligation. -/

open MeasureTheory Filter
open scoped Topology NNReal ENNReal Convolution

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- A given reduced-law L2 approximation has a subsequence converging at the
physical starting environment on one full event. -/
theorem c17_exists_point_start_subsequence_of_L2_tendsto
    {E : Type*} [NormedAddCommGroup E]
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {F : ℕ → FieldPair d → E} (hF : ∀ n, MemLp (F n) 2 (reducedLaw Q))
    {f : Lp E 2 (reducedLaw Q)}
    (hlim : Filter.Tendsto (fun n => (hF n).toLp (F n)) Filter.atTop (𝓝 f)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
        ∀ᵐ ω ∂Q.measure,
          Filter.Tendsto (fun n => F (ns n) (reduce ω)) Filter.atTop
            (𝓝 (f (reduce ω))) := by
  obtain ⟨ns, hns, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  have hrep : ∀ᵐ ρ ∂reducedLaw Q, ∀ n, (hF n).toLp (F n) ρ = F n ρ :=
    ae_all_iff.mpr fun n => (hF n).coeFn_toLp
  have hfull : ∀ᵐ ρ ∂reducedLaw Q,
      Filter.Tendsto (fun n => F (ns n) ρ) Filter.atTop (𝓝 (f ρ)) := by
    filter_upwards [hpoint, hrep] with ρ hρ hrep
    simpa only [hrep] using hρ
  exact (Probability.measurableEmbedding_reduce d).ae_map_iff
    (μ := Q.measure) |>.mp hfull

/-- Horizontal core representatives may approximate an actual reduced-law L2
class both in L2 and at the physical starting environment on one full event.
This is value approximation only; it supplies no generator-residual estimate. -/
theorem c17_exists_horizontalCore_point_start_approximation
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (f : Lp ℝ 2 (reducedLaw Q)) :
    ∃ F : ℕ → FieldPair d → ℝ, (∀ n, IsHorizontalTest (F n)) ∧
      ∃ hF : ∀ n, MemLp (F n) 2 (reducedLaw Q),
        Filter.Tendsto (fun n => (hF n).toLp (F n)) Filter.atTop (𝓝 f) ∧
        ∀ᵐ ω ∂Q.measure,
          Filter.Tendsto (fun n => F n (reduce ω)) Filter.atTop (𝓝 (f (reduce ω))) := by
  let _ : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨F, hHor, hF, hlim⟩ := Correctors.exists_horizontalCore_Lp_approximation
    (reducedLaw Q) (reducedLaw_stationary Q) f
  obtain ⟨ns, hns, hpoint⟩ := c17_exists_point_start_subsequence_of_L2_tendsto Q hF hlim
  exact ⟨fun n => F (ns n), fun n => hHor (ns n), fun n => hF (ns n),
    hlim.comp hns.tendsto_atTop, hpoint⟩


private theorem c17_integrable_complex_mollifier_orbit
    {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (ε : ℝ) (f : Lp ℂ 2 Q) :
    Integrable (fun x : Vec d => (mollifier d x : ℂ) •
      complexTranslation Q hQ (ε • x) f) := by
  have hκ : Integrable (mollifier d) :=
    (contDiff_mollifier d).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_mollifier d)
  have hc : Continuous (fun x : Vec d => complexTranslation Q hQ (ε • x) f) :=
    (continuous_complexTranslation Q hQ).comp
      ((continuous_id.const_smul ε).prodMk continuous_const)
  apply (hκ.mul_const ‖f‖).mono'
    (((Complex.continuous_ofReal.comp (contDiff_mollifier d).continuous).smul hc).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    change ‖(mollifier d x : ℂ) • complexTranslation Q hQ (ε • x) f‖ ≤
      mollifier d x * ‖f‖
    simp only [norm_smul, norm_complexTranslation, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mollifier_nonneg d x), le_refl]

/-- The actual unit-mass horizontal convolution, as a bounded operator on
complex L2. No process association or generator estimate enters its definition. -/
def c17ComplexHorizontalMollify {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (ε : ℝ) :
    Lp ℂ 2 Q →L[ℂ] Lp ℂ 2 Q :=
  (show Lp ℂ 2 Q →ₗ[ℂ] Lp ℂ 2 Q from
    { toFun := fun f => ∫ x : Vec d, (mollifier d x : ℂ) •
        complexTranslation Q hQ (ε • x) f
      map_add' := fun f g => by
        simp only [map_add, smul_add]
        exact integral_add (c17_integrable_complex_mollifier_orbit Q hQ ε f)
          (c17_integrable_complex_mollifier_orbit Q hQ ε g)
      map_smul' := fun c f => by
        simp only [map_smul, smul_comm (mollifier d _ : ℂ) c, integral_smul,
          RingHom.id_apply] }).mkContinuous 1 (fun f => by
    have hκ : Integrable (mollifier d) :=
      (contDiff_mollifier d).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_mollifier d)
    have hb := norm_integral_le_of_norm_le (hκ.mul_const ‖f‖)
      (Filter.Eventually.of_forall fun x : Vec d =>
        show ‖(mollifier d x : ℂ) • complexTranslation Q hQ (ε • x) f‖ ≤
            mollifier d x * ‖f‖ from by
          simp only [norm_smul, norm_complexTranslation, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg d x), le_refl])
    change ‖∫ x : Vec d, (mollifier d x : ℂ) •
      complexTranslation Q hQ (ε • x) f‖ ≤ 1 * ‖f‖
    simpa only [integral_mul_const, integral_mollifier, one_mul] using hb)

/-- Horizontal convolution commutes with the literal translation action. -/
theorem c17_complexHorizontalMollify_translation {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ε : ℝ) (y : Vec d) (f : Lp ℂ 2 Q) :
    c17ComplexHorizontalMollify Q hQ ε (complexTranslation Q hQ y f) =
      complexTranslation Q hQ y (c17ComplexHorizontalMollify Q hQ ε f) := by
  change (∫ x : Vec d, (mollifier d x : ℂ) •
      complexTranslation Q hQ (ε • x) (complexTranslation Q hQ y f)) =
    complexTranslation Q hQ y (∫ x : Vec d, (mollifier d x : ℂ) •
      complexTranslation Q hQ (ε • x) f)
  rw [← (complexTranslation Q hQ y).integral_comp_comm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [map_smul, ← complexTranslation_add, add_comm y]

/-- Convolution preserves the actual strong derivative relation, with the
same convolution applied to its derivative. -/
theorem c17_complexHorizontalMollify_derivative {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {i : Fin d} {f g : Lp ℂ 2 Q}
    (hf : HasComplexHorizontalDerivative Q hQ i f g) (ε : ℝ) :
    HasComplexHorizontalDerivative Q hQ i (c17ComplexHorizontalMollify Q hQ ε f)
      (c17ComplexHorizontalMollify Q hQ ε g) := by
  have h := ((c17ComplexHorizontalMollify Q hQ ε).continuous.tendsto g).comp hf
  change Filter.Tendsto (fun t : ℝ => c17ComplexHorizontalMollify Q hQ ε
    ((t : ℂ)⁻¹ • (complexTranslation Q hQ (t • unitVector i) f - f)))
    (𝓝[≠] (0 : ℝ)) (𝓝 (c17ComplexHorizontalMollify Q hQ ε g)) at h
  simpa only [HasComplexHorizontalDerivative, map_smul, map_sub,
    c17_complexHorizontalMollify_translation] using h

/-- The genuine complex horizontal convolution is an L2 approximate identity. -/
theorem c17_tendsto_complexHorizontalMollify {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : Lp ℂ 2 Q) :
    Filter.Tendsto (fun ε : ℝ => c17ComplexHorizontalMollify Q hQ ε f)
      (𝓝 0) (𝓝 f) := by
  have hκ : Integrable (mollifier d) :=
    (contDiff_mollifier d).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_mollifier d)
  have hf_eq : (∫ x : Vec d, (mollifier d x : ℂ) • f) = f := by
    rw [integral_smul_const, integral_complex_ofReal, integral_mollifier]
    simp only [Complex.ofReal_one, one_smul]
  have hcont (ε : ℝ) : Continuous (fun x : Vec d =>
      (mollifier d x : ℂ) • complexTranslation Q hQ (ε • x) f) :=
    (Complex.continuous_ofReal.comp (contDiff_mollifier d).continuous).smul
      ((continuous_complexTranslation Q hQ).comp
        ((continuous_id.const_smul ε).prodMk continuous_const))
  have hpt (x : Vec d) : Filter.Tendsto (fun ε : ℝ =>
      (mollifier d x : ℂ) • complexTranslation Q hQ (ε • x) f)
      (𝓝 0) (𝓝 ((mollifier d x : ℂ) • f)) := by
    have hc : Continuous (fun ε : ℝ => ε • x) := by fun_prop
    have hz : Filter.Tendsto (fun ε : ℝ => ε • x) (𝓝 0) (𝓝 0) := by
      simpa only [zero_smul] using hc.tendsto 0
    exact ((tendsto_complexTranslation_zero Q hQ f).comp hz).const_smul _
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun x : Vec d => mollifier d x * ‖f‖)
    (Filter.Eventually.of_forall fun ε : ℝ => (hcont ε).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ε : ℝ => Filter.Eventually.of_forall fun x =>
      show ‖(mollifier d x : ℂ) • complexTranslation Q hQ (ε • x) f‖ ≤
          mollifier d x * ‖f‖ from by
        simp only [norm_smul, norm_complexTranslation, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg d x), le_refl])
    (hκ.mul_const ‖f‖) (Filter.Eventually.of_forall hpt)
  rw [hf_eq] at h
  exact h

/-- A single actual H1 function and its supplied gradient are approximated
simultaneously. This does not assert generator-domain graph approximation. -/
theorem c17_complexHorizontalMollify_H1_approximation {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {f : Lp ℂ 2 Q} {G : Fin d → Lp ℂ 2 Q}
    (hf : HasComplexHorizontalGradient Q hQ f G) :
    (∀ ε : ℝ, HasComplexHorizontalGradient Q hQ
      (c17ComplexHorizontalMollify Q hQ ε f)
      (fun i => c17ComplexHorizontalMollify Q hQ ε (G i))) ∧
    Filter.Tendsto (fun ε : ℝ => c17ComplexHorizontalMollify Q hQ ε f)
      (𝓝 0) (𝓝 f) ∧
    ∀ i, Filter.Tendsto (fun ε : ℝ => c17ComplexHorizontalMollify Q hQ ε (G i))
      (𝓝 0) (𝓝 (G i)) := by
  exact ⟨fun ε i => c17_complexHorizontalMollify_derivative Q hQ (hf i) ε,
    c17_tendsto_complexHorizontalMollify Q hQ f,
    fun i => c17_tendsto_complexHorizontalMollify Q hQ (G i)⟩


/-- The actual reduced coefficient entries are almost surely Lipschitz, with the
coordinate-norm constant obtained from the original Euclidean regularity bound. -/
theorem c17_ae_reducedCoefficient_lipschitz
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ w ∂reducedLaw Q, ∀ j k : Fin d,
      LipschitzWith
        (Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d))
        (fun y => w.1 y j k) := by
  apply (Probability.measurableEmbedding_reduce d).ae_map_iff.mpr
  filter_upwards [Q.regular] with ω hω
  exact fun j k => reducedCoefficient_lipschitz
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter) hω j k

/-- The first-derivative commutator of the unforced generator is in L2 for an
actual L2 vector field under the actual reduced law. -/
theorem c17_unforced_generator_commutator_memLp
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {δ : ℝ} (hδ : 0 < δ) {V : FieldPair d → Vec d}
    (hVm : Measurable V) (hV : ∀ j, MemLp (fun w => V w j) 2 (reducedLaw Q)) :
    MemLp (Entropy.commOp hd 0 (Calculus.unitMassScaledMollifier d δ) V)
      2 (reducedLaw Q) := by
  let _ : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  exact Entropy.memLp_commOp hd 0 (reducedLaw_stationary Q) hδ
    (c17_ae_reducedCoefficient_lipschitz Q) hVm hV

/-- A scale-uniform scalar L2 bound for the actual unforced generator
commutator. This estimates the divergence commutator itself, rather than only
the undifferentiated flux. It does not assert occupation continuity. -/
theorem c17_unforced_generator_commutator_L2_bound
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {V : FieldPair d → Vec d}
    (hVm : Measurable V) (hV : ∀ j, MemLp (fun w => V w j) 2 (reducedLaw Q)) :
    Real.sqrt (∫ w, (Entropy.commOp hd 0
      (Calculus.unitMassScaledMollifier d δ) V w) ^ 2 ∂reducedLaw Q) ≤
      Entropy.commConst d 0
        (Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d)) *
        ∑ j, Real.sqrt (∫ w, V w j ^ 2 ∂reducedLaw Q) := by
  let _ : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let C := Entropy.commConst d 0
    (Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d))
  let R := Entropy.commOp hd 0 (Calculus.unitMassScaledMollifier d δ) V
  have hRm : Measurable R := Entropy.measurable_commOp hd 0
    (Entropy.contDiff_unitMassScaledMollifier δ) hVm
  have hR : MemLp R 2 (reducedLaw Q) :=
    c17_unforced_generator_commutator_memLp hd Q hδ hVm hV
  have hb := Entropy.abs_integral_mul_commOp_le hd 0 (reducedLaw_stationary Q)
    hδ hδ1 (c17_ae_reducedCoefficient_lipschitz Q) hRm hR hVm hV
  have hI : 0 ≤ ∫ w, R w ^ 2 ∂reducedLaw Q :=
    integral_nonneg fun w => sq_nonneg (R w)
  have hs : (Real.sqrt (∫ w, R w ^ 2 ∂reducedLaw Q)) ^ 2 =
      ∫ w, R w ^ 2 ∂reducedLaw Q := Real.sq_sqrt hI
  have hb' : (Real.sqrt (∫ w, R w ^ 2 ∂reducedLaw Q)) ^ 2 ≤
      C * Real.sqrt (∫ w, R w ^ 2 ∂reducedLaw Q) *
        ∑ j, Real.sqrt (∫ w, V w j ^ 2 ∂reducedLaw Q) := by
    rw [hs]
    simpa only [R, C, ← pow_two, abs_of_nonneg hI] using hb
  have hC : 0 ≤ C := Entropy.commConst_nonneg d 0 _
  have hS : 0 ≤ ∑ j, Real.sqrt (∫ w, V w j ^ 2 ∂reducedLaw Q) :=
    Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
  change Real.sqrt (∫ w, R w ^ 2 ∂reducedLaw Q) ≤ C * _
  by_cases hz : Real.sqrt (∫ w, R w ^ 2 ∂reducedLaw Q) = 0
  · rw [hz]
    exact mul_nonneg hC hS
  · have hp := lt_of_le_of_ne (Real.sqrt_nonneg
        (∫ w, R w ^ 2 ∂reducedLaw Q)) (Ne.symm hz)
    nlinarith


/-- Under the actual reduced law, the smooth-test scalar generator residual is
exactly the first-derivative commutator. The coefficient field is not smoothed. -/
theorem c17_unforced_generator_commutator_identity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {δ : ℝ} (hδ : 0 < δ) {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) :
    (fun w => envGenerator hd 0
        (horizontalMollify (Calculus.unitMassScaledMollifier d δ) F) w -
      horizontalMollify (Calculus.unitMassScaledMollifier d δ)
        (envGenerator hd 0 F) w) =ᵐ[reducedLaw Q]
      Entropy.commOp hd 0 (Calculus.unitMassScaledMollifier d δ)
        (fun w j => horizontalDerivative j F w) := by
  have hB : ∀ᵐ w ∂reducedLaw Q, ∀ x j k,
      |w.1 x j k| ≤ Real.exp (2 * Λ₀) * Λ₀ := by
    apply (Probability.measurableEmbedding_reduce d).ae_map_iff.mpr
    filter_upwards [Q.regular] with ω hω
    exact fun x j k => abs_reducedCoefficient_le
      (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter) hω x j k
  filter_upwards [hB, c17_ae_reducedCoefficient_lipschitz Q] with w hB hL
  exact Entropy.envGenerator_horizontalMollify_sub hd 0
    (Entropy.contDiff_unitMassScaledMollifier δ)
    (Entropy.hasCompactSupport_unitMassScaledMollifier hδ) hF hB hL

/-- The actual smooth-test scalar generator residual obeys the uniform L2
commutator estimate with the gradient of the same test on the right. -/
theorem c17_unforced_smoothed_generator_residual_L2_bound
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) :
    Real.sqrt (∫ w, (envGenerator hd 0
        (horizontalMollify (Calculus.unitMassScaledMollifier d δ) F) w -
      horizontalMollify (Calculus.unitMassScaledMollifier d δ)
        (envGenerator hd 0 F) w) ^ 2 ∂reducedLaw Q) ≤
      Entropy.commConst d 0
        (Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d)) *
        ∑ j, Real.sqrt (∫ w, (horizontalDerivative j F w) ^ 2 ∂reducedLaw Q) := by
  let _ : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have heq := c17_unforced_generator_commutator_identity hd Q hδ hF
  have hi := integral_congr_ae (heq.mono fun w hw => congrArg (fun a : ℝ => a ^ 2) hw)
  rw [hi]
  exact c17_unforced_generator_commutator_L2_bound hd Q hδ hδ1
    (Measurable.of_eval fun j => hF.measurable_derivative j)
    (fun j => hF.memLp_derivative (reducedLaw Q) 2 j)


private theorem c17_tendsto_eLpNorm_add_zero
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    {f g : ι → α → ℝ}
    (hf : Filter.Tendsto (fun i => eLpNorm (f i) 2 μ) l (𝓝 0))
    (hg : Filter.Tendsto (fun i => eLpNorm (g i) 2 μ) l (𝓝 0)) :
    Filter.Tendsto (fun i => eLpNorm (fun x => f i x + g i x) 2 μ) l (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using hf.add hg) (fun _ => bot_le)
    (fun _ => eLpNorm_add_le (by norm_num))

private theorem c17_tendsto_eLpNorm_sum_zero
    {α ι β : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    (s : Finset β) {f : β → ι → α → ℝ}
    (hf : ∀ b ∈ s, Filter.Tendsto (fun i => eLpNorm (f b i) 2 μ) l (𝓝 0)) :
    Filter.Tendsto (fun i => eLpNorm (fun x => ∑ b ∈ s, f b i x) 2 μ) l (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : ι => (0 : ℝ≥0∞)) l (𝓝 0))
  | @insert b s hb ih =>
    simp only [Finset.sum_insert hb]
    exact c17_tendsto_eLpNorm_add_zero (hf b (Finset.mem_insert_self _ _))
      (ih fun c hc => hf c (Finset.mem_insert_of_mem hc))

private theorem c17_tendsto_eLpNorm_bounded_mul_zero
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    {a : α → ℝ} (ha : Measurable a) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, |a x| ≤ C) {f : ι → α → ℝ}
    (hfm : ∀ i, Measurable (f i))
    (hf : Filter.Tendsto (fun i => eLpNorm (f i) 2 μ) l (𝓝 0)) :
    Filter.Tendsto (fun i => eLpNorm (fun x => a x * f i x) 2 μ) l (𝓝 0) := by
  have hb : ∀ i, eLpNorm (fun x => a x * f i x) 2 μ ≤
      ‖C‖ₑ * eLpNorm (f i) 2 μ := by
    intro i
    calc
      _ ≤ eLpNorm (fun x => C * f i x) 2 μ :=
        eLpNorm_mono_ae (ha.mul (hfm i)).aestronglyMeasurable (hC.mono fun x hx => by
          simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self C)) (abs_nonneg _))
      _ = _ := by
        change eLpNorm (C • f i) 2 μ = _
        exact eLpNorm_const_smul C (f i) 2 μ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using (ENNReal.Tendsto.const_mul hf
      (Or.inr (by simp : ‖C‖ₑ ≠ ∞)))) (fun _ => bot_le) hb

/-- On each fixed smooth horizontal test, the actual unforced generator of its
mollification converges to its generator in reduced-law L2. Both derivatives
are mollified while the actual coefficient field is retained. -/
theorem c17_tendsto_unforced_smoothed_test_generator
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) :
    Filter.Tendsto (fun δ => eLpNorm (fun w =>
      envGenerator hd 0 (horizontalMollify (Calculus.unitMassScaledMollifier d δ) F) w -
        envGenerator hd 0 F w) 2 (reducedLaw Q)) (𝓝[>] 0) (𝓝 0) := by
  let _ : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let L := Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d)
  have hB : ∀ᵐ w ∂reducedLaw Q, ∀ x j k,
      |w.1 x j k| ≤ Real.exp (2 * Λ₀) * Λ₀ := by
    apply (Probability.measurableEmbedding_reduce d).ae_map_iff.mpr
    filter_upwards [Q.regular] with ω hω
    exact fun x j k => abs_reducedCoefficient_le
      (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter) hω x j k
  have hentry (j k : Fin d) : Measurable fun w : FieldPair d => w.1 0 j k :=
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k).measurable
  have hlim (H : FieldPair d → ℝ) (hH : IsHorizontalTest H) :=
    Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier
      (reducedLaw Q) (reducedLaw_stationary Q) 2 ENNReal.ofNat_ne_top hH.1
      (hH.memLp (reducedLaw Q) 2)
  have hm (H : FieldPair d → ℝ) (hH : IsHorizontalTest H) (δ : ℝ) :
      Measurable (fun w => horizontalMollify
        (Calculus.unitMassScaledMollifier d δ) H w - H w) :=
    (measurable_horizontalMollify _
      (Entropy.contDiff_unitMassScaledMollifier δ).continuous.measurable hH.1).sub hH.1
  have hterms (j k : Fin d) : Filter.Tendsto (fun δ => eLpNorm (fun w =>
      Entropy.coeffDeriv w j k 0 *
        (horizontalMollify (Calculus.unitMassScaledMollifier d δ)
          (horizontalDerivative j F) w - horizontalDerivative j F w) +
      w.1 0 j k * (horizontalMollify (Calculus.unitMassScaledMollifier d δ)
        (horizontalDerivative k (horizontalDerivative j F)) w -
          horizontalDerivative k (horizontalDerivative j F) w)) 2 (reducedLaw Q))
      (𝓝[>] 0) (𝓝 0) := by
    apply c17_tendsto_eLpNorm_add_zero
    · apply c17_tendsto_eLpNorm_bounded_mul_zero (measurable_fderiv_entry_zero j k _)
        (C := (L : ℝ) * ‖unitVector (d := d) k‖)
      · exact (c17_ae_reducedCoefficient_lipschitz Q).mono fun w hw =>
          Entropy.abs_coeffDeriv_le (hw j k) 0
      · exact hm _ (hF.horizontalDerivative j)
      · exact hlim _ (hF.horizontalDerivative j)
    · exact c17_tendsto_eLpNorm_bounded_mul_zero (hentry j k)
        (hB.mono fun w hw => hw 0 j k)
        (hm _ ((hF.horizontalDerivative j).horizontalDerivative k))
        (hlim _ ((hF.horizontalDerivative j).horizontalDerivative k))
  have hsum := c17_tendsto_eLpNorm_sum_zero (μ := reducedLaw Q) Finset.univ
    (fun k _ => c17_tendsto_eLpNorm_sum_zero Finset.univ (fun j _ => hterms j k))
  have hfinal := c17_tendsto_eLpNorm_bounded_mul_zero
    (a := fun _ : FieldPair d => (1 / 2 : ℝ)) measurable_const
    (C := (1 / 2 : ℝ)) (Filter.Eventually.of_forall fun _ => by norm_num)
    (fun δ => Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun j _ =>
      ((measurable_fderiv_entry_zero j k _).mul (hm _ (hF.horizontalDerivative j) δ)).add
        ((hentry j k).mul (hm _ ((hF.horizontalDerivative j).horizontalDerivative k) δ))) hsum
  apply hfinal.congr'
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  congr 1
  funext w
  have h1 (j : Fin d) := funext (Entropy.horizontalDerivative_horizontalMollify_eq
    (Entropy.contDiff_unitMassScaledMollifier δ)
    (Entropy.hasCompactSupport_unitMassScaledMollifier hδ) hF j)
  have h2 (j k : Fin d) := funext (Entropy.horizontalDerivative_horizontalMollify_eq
    (Entropy.contDiff_unitMassScaledMollifier δ)
    (Entropy.hasCompactSupport_unitMassScaledMollifier hδ) (hF.horizontalDerivative j) k)
  simp only [Pi.mul_apply, Pi.add_apply, envGenerator, h1, h2, zero_mul, add_zero, Entropy.coeffDeriv,
    mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring



private theorem c17_commutator_core_component
    {d : ℕ} {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ) {F : FieldPair d → ℝ} (hF : IsHorizontalTest F)
    {w : FieldPair d} {K : ℝ} {L : NNReal}
    (hB : ∀ x j k, |w.1 x j k| ≤ K)
    (hL : ∀ j k, LipschitzWith L fun y => w.1 y j k) (j k : Fin d) :
    (∫ x, (κ x * Entropy.coeffDeriv w j k 0 -
      coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) * F (translate x w)) =
      Entropy.coeffDeriv w j k 0 * horizontalMollify κ F w +
        w.1 0 j k * horizontalMollify κ (horizontalDerivative k F) w -
        horizontalMollify κ (fun v => Entropy.coeffDeriv v j k 0 * F v +
          v.1 0 j k * horizontalDerivative k F v) w := by
  obtain ⟨M0, M1, M2, -, -, hb0, hb1, -⟩ := hF.exists_bounds
  have hψd : Differentiable ℝ (orbit F w) := (hF.2.1 w).differentiable (by simp)
  have hψL : LipschitzWith (d * M1).toNNReal (orbit F w) :=
    lipschitzWith_of_coordinateDerivative_le hψd (fun x k => hb1 w x k)
  have hψc := (hF.2.1 w).continuous
  have hψ1c := Entropy.continuous_orbitDeriv hF w k
  have hAc : Continuous fun x : Vec d => w.1 x j k := (hL j k).continuous
  have hI0 : Integrable fun x => κ x * orbit F w x :=
    (hκ.continuous.mul hψc).integrable_of_hasCompactSupport hκc.mul_right
  have hI1 : Integrable fun x => κ x * Entropy.orbitDeriv F w k x :=
    (hκ.continuous.mul hψ1c).integrable_of_hasCompactSupport hκc.mul_right
  have hIc : Integrable fun x => κ x *
      (Entropy.coeffDeriv w j k x * orbit F w x) :=
    Entropy.integrable_kernel_mul_bdd hκ.continuous hκc
      ((Entropy.measurable_coeffDeriv w j k).mul hψc.measurable)
      (C := ((L : ℝ) * ‖unitVector (d := d) k‖) * M0)
      (fun x => by
        rw [abs_mul]
        exact mul_le_mul (Entropy.abs_coeffDeriv_le (hL j k) x) (hb0 w x)
          (abs_nonneg _) (by positivity))
  have hIa : Integrable fun x => κ x * (w.1 x j k * Entropy.orbitDeriv F w k x) :=
    (hκ.continuous.mul (hAc.mul hψ1c)).integrable_of_hasCompactSupport hκc.mul_right
  have hId : Integrable fun x => coordinateDerivative k κ x *
      ((w.1 0 j k - w.1 x j k) * orbit F w x) :=
    (((hκ.continuous_fderiv (by simp)).clm_apply continuous_const).mul
      ((continuous_const.sub hAc).mul hψc)).integrable_of_hasCompactSupport
        ((hκc.fderiv_apply (𝕜 := ℝ) (unitVector k)).mul_right)
  have hIBP := Entropy.integral_kernel_coeff_deriv hκ hκc (hL j k)
    (fun x => hB x j k) hψL hψd k
  have htrans (x : Vec d) : Entropy.coeffDeriv (translate x w) j k 0 =
      Entropy.coeffDeriv w j k x := by
    have h := fderiv_comp_add_left (𝕜 := ℝ) (f := fun z : Vec d => w.1 z j k)
      (x := (0 : Vec d)) x
    rw [add_zero] at h
    exact congrArg (fun T : Vec d →L[ℝ] ℝ => T (unitVector k)) h
  have hentry (x : Vec d) : (translate x w).1 0 j k = w.1 x j k := by
    change w.1 (x + 0) j k = _
    rw [add_zero]
  have hInt : (∫ x, κ x * (w.1 0 j k - w.1 x j k) *
      fderiv ℝ (orbit F w) x (unitVector k)) =
      w.1 0 j k * (∫ x, κ x * Entropy.orbitDeriv F w k x) -
        ∫ x, κ x * (w.1 x j k * Entropy.orbitDeriv F w k x) := by
    rw [← integral_const_mul, ← integral_sub (hI1.const_mul _) hIa]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by unfold Entropy.orbitDeriv; ring
  rw [hInt] at hIBP
  have hR : (∫ x, (-(coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) +
      κ x * Entropy.coeffDeriv w j k x) * orbit F w x) =
      -(∫ x, coordinateDerivative k κ x * ((w.1 0 j k - w.1 x j k) * orbit F w x)) +
        ∫ x, κ x * (Entropy.coeffDeriv w j k x * orbit F w x) := by
    rw [← integral_neg]
    change _ = (∫ x, (- (fun y => coordinateDerivative k κ y *
      ((w.1 0 j k - w.1 y j k) * orbit F w y))) x) + _
    rw [← integral_add hId.neg hIc]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Pi.neg_apply]; ring)
  change _ = (∫ x, (-(coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) +
    κ x * Entropy.coeffDeriv w j k x) * orbit F w x) at hIBP
  rw [hR] at hIBP
  have hm0 : horizontalMollify κ F w = ∫ x, κ x * orbit F w x := rfl
  have hm1 : horizontalMollify κ (horizontalDerivative k F) w =
      ∫ x, κ x * Entropy.orbitDeriv F w k x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change κ x * horizontalDerivative k F (translate x w) = _
      rw [horizontalDerivative_translate]
      rfl
  have hmflux : horizontalMollify κ (fun v => Entropy.coeffDeriv v j k 0 * F v +
      v.1 0 j k * horizontalDerivative k F v) w =
      (∫ x, κ x * (Entropy.coeffDeriv w j k x * orbit F w x)) +
        ∫ x, κ x * (w.1 x j k * Entropy.orbitDeriv F w k x) := by
    rw [← integral_add hIc hIa]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change κ x * (Entropy.coeffDeriv (translate x w) j k 0 * F (translate x w) +
        (translate x w).1 0 j k * horizontalDerivative k F (translate x w)) = _
      rw [htrans, hentry, horizontalDerivative_translate]
      simp only [Entropy.orbitDeriv, coordinateDerivative, orbit]
      ring
  have hleft : (∫ x, (κ x * Entropy.coeffDeriv w j k 0 -
      coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) * F (translate x w)) =
      Entropy.coeffDeriv w j k 0 * (∫ x, κ x * orbit F w x) -
        ∫ x, coordinateDerivative k κ x * ((w.1 0 j k - w.1 x j k) * orbit F w x) := by
    rw [← integral_const_mul, ← integral_sub (hI0.const_mul _) hId]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by unfold orbit; ring)
  rw [hm0, hm1, hmflux, hleft]
  linarith

private theorem c17_ae_reducedCoefficient_bound
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ w ∂reducedLaw Q, ∀ x j k, |w.1 x j k| ≤ Real.exp (2 * Λ₀) * Λ₀ := by
  apply (Probability.measurableEmbedding_reduce d).ae_map_iff.mpr
  filter_upwards [Q.regular] with ω hω
  exact fun x j k => abs_reducedCoefficient_le
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter) hω x j k

private theorem c17_core_fluxDerivative_memLp
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) (j k : Fin d) :
    MemLp (fun w => Entropy.coeffDeriv w j k 0 * F w +
      w.1 0 j k * horizontalDerivative k F w) 2 (reducedLaw Q) := by
  let _ : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hc : MemLp (fun w => Entropy.coeffDeriv w j k 0 * F w) 2 (reducedLaw Q) :=
    (hF.memLp (reducedLaw Q) 2).of_le_mul
      (((measurable_fderiv_entry_zero j k _).mul hF.1).aestronglyMeasurable)
      ((c17_ae_reducedCoefficient_lipschitz Q).mono fun w hw => by
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (Entropy.abs_coeffDeriv_le (hw j k) 0)
          (abs_nonneg _))
  have ha := Entropy.memLp_mul_entry (hF.memLp_derivative (reducedLaw Q) 2 k)
    (c17_ae_reducedCoefficient_bound Q) j k
  refine MemLp.ae_eq ?_ (hc.add ha)
  exact Filter.Eventually.of_forall fun w => by simp only [Pi.add_apply]; ring

/-- Cancellation of the actual unforced commutator on vectors whose individual
components are horizontal core tests. No gradient constraint is imposed. -/
theorem c17_tendsto_unforced_commutator_horizontalTests
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {V : FieldPair d → Vec d} (hV : ∀ j, IsHorizontalTest (fun w => V w j)) :
    Filter.Tendsto (fun δ : ℝ => eLpNorm
      (Entropy.commOp hd 0 (Calculus.unitMassScaledMollifier d δ) V) 2 (reducedLaw Q))
      (𝓝[>] 0) (𝓝 0) := by
  let _ : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let L := Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d)
  let H (j k : Fin d) (w : FieldPair d) :=
    Entropy.coeffDeriv w j k 0 * V w j + w.1 0 j k * horizontalDerivative k (fun v => V v j) w
  have hentry (j k : Fin d) : Measurable fun w : FieldPair d => w.1 0 j k :=
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k).measurable
  have hHm (j k : Fin d) : Measurable (H j k) :=
    ((measurable_fderiv_entry_zero j k _).mul (hV j).1).add
      ((hentry j k).mul ((hV j).measurable_derivative k))
  have hm (F : FieldPair d → ℝ) (hF : Measurable F) (δ : ℝ) :
      Measurable (fun w => horizontalMollify (Calculus.unitMassScaledMollifier d δ) F w - F w) :=
    (measurable_horizontalMollify _
      (Entropy.contDiff_unitMassScaledMollifier δ).continuous.measurable hF).sub hF
  have hlim (F : FieldPair d → ℝ) (hF : Measurable F) (hF2 : MemLp F 2 (reducedLaw Q)) :=
    Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier
      (reducedLaw Q) (reducedLaw_stationary Q) 2 ENNReal.ofNat_ne_top hF hF2
  let R (j k : Fin d) (δ : ℝ) (w : FieldPair d) :=
    Entropy.coeffDeriv w j k 0 *
      (horizontalMollify (Calculus.unitMassScaledMollifier d δ) (fun v => V v j) w - V w j) +
    w.1 0 j k * (horizontalMollify (Calculus.unitMassScaledMollifier d δ)
      (horizontalDerivative k (fun v => V v j)) w - horizontalDerivative k (fun v => V v j) w) +
    (-1 : ℝ) * (horizontalMollify (Calculus.unitMassScaledMollifier d δ) (H j k) w - H j k w)
  have hRm (j k : Fin d) (δ : ℝ) : Measurable (R j k δ) :=
    (((measurable_fderiv_entry_zero j k _).mul (hm _ (hV j).1 δ)).add
      ((hentry j k).mul (hm _ ((hV j).measurable_derivative k) δ))).add
      (measurable_const.mul (hm _ (hHm j k) δ))
  have hR (j k : Fin d) : Filter.Tendsto (fun δ => eLpNorm (R j k δ) 2 (reducedLaw Q))
      (𝓝[>] 0) (𝓝 0) := by
    apply c17_tendsto_eLpNorm_add_zero
    · apply c17_tendsto_eLpNorm_add_zero
      · exact c17_tendsto_eLpNorm_bounded_mul_zero (measurable_fderiv_entry_zero j k _)
          ((c17_ae_reducedCoefficient_lipschitz Q).mono fun w hw =>
            Entropy.abs_coeffDeriv_le (hw j k) 0)
          (hm _ (hV j).1) (hlim _ (hV j).1 ((hV j).memLp (reducedLaw Q) 2))
      · exact c17_tendsto_eLpNorm_bounded_mul_zero (hentry j k)
          ((c17_ae_reducedCoefficient_bound Q).mono fun w hw => hw 0 j k)
          (hm _ ((hV j).measurable_derivative k))
          (hlim _ ((hV j).measurable_derivative k) ((hV j).memLp_derivative (reducedLaw Q) 2 k))
    · exact c17_tendsto_eLpNorm_bounded_mul_zero
        (a := fun _ : FieldPair d => (-1 : ℝ)) measurable_const (C := (1 : ℝ))
        (Filter.Eventually.of_forall fun _ => by norm_num)
        (hm _ (hHm j k)) (hlim _ (hHm j k) (c17_core_fluxDerivative_memLp Q (hV j) j k))
  have hs := c17_tendsto_eLpNorm_sum_zero (μ := reducedLaw Q) Finset.univ
    (fun j _ => c17_tendsto_eLpNorm_sum_zero Finset.univ (fun k _ => hR j k))
  have hfinal := c17_tendsto_eLpNorm_bounded_mul_zero
    (a := fun _ : FieldPair d => (1 / 2 : ℝ)) measurable_const (C := (1 / 2 : ℝ))
    (Filter.Eventually.of_forall fun _ => by norm_num)
    (fun δ => Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => hRm j k δ) hs
  apply hfinal.congr'
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  apply eLpNorm_congr_ae
  filter_upwards [c17_ae_reducedCoefficient_bound Q,
    c17_ae_reducedCoefficient_lipschitz Q] with w hwB hwL
  let κ := Calculus.unitMassScaledMollifier d δ
  have hκ := Entropy.contDiff_unitMassScaledMollifier (d := d) δ
  have hκc := Entropy.hasCompactSupport_unitMassScaledMollifier (d := d) hδ
  have hI (j k : Fin d) : Integrable fun x => (κ x * Entropy.coeffDeriv w j k 0 -
      coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) * V (translate x w) j := by
    have hc : Continuous (fun x => (κ x * Entropy.coeffDeriv w j k 0 -
        coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) * V (translate x w) j) :=
      ((hκ.continuous.mul continuous_const).sub
      (((hκ.continuous_fderiv (by simp)).clm_apply continuous_const).mul
        (continuous_const.sub (hwL j k).continuous))).mul ((hV j).2.1 w).continuous
    exact hc.integrable_of_hasCompactSupport
      ((hκc.mul_right.sub (hκc.fderiv_apply (𝕜 := ℝ) (unitVector k)).mul_right).mul_right)
  change (1 / 2 : ℝ) * (∑ j, ∑ k, R j k δ w) = _
  rw [Finset.mul_sum]
  unfold Entropy.commOp
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun x => Entropy.commKernel hd 0 κ w j x * V (translate x w) j) =
      fun x => (1 / 2 : ℝ) * ∑ k,
        (κ x * Entropy.coeffDeriv w j k 0 -
          coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) * V (translate x w) j := by
    funext x
    simp only [Entropy.commKernel, zero_mul, add_zero, Entropy.coeffDeriv, mul_assoc, Finset.sum_mul]
  rw [he, integral_const_mul, integral_finset_sum _ (fun k _ => hI j k)]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [c17_commutator_core_component hκ hκc (hV j) hwB hwL j k]
  dsimp [R, H]
  ring

private theorem c17_sqrt_integral_sq_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) :
    Real.sqrt (∫ x, f x ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  congr 1
  · exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs])
  · simp

private theorem c17_sqrt_integral_sq_triangle
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g h : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (he : ∀ᵐ x ∂μ, f x = g x + h x) :
    Real.sqrt (∫ x, f x ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, g x ^ 2 ∂μ) + Real.sqrt (∫ x, h x ^ 2 ∂μ) := by
  rw [c17_sqrt_integral_sq_eq hf, c17_sqrt_integral_sq_eq hg, c17_sqrt_integral_sq_eq hh]
  calc
    _ ≤ (eLpNorm g 2 μ + eLpNorm h 2 μ).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hg.eLpNorm_ne_top, hh.eLpNorm_ne_top⟩)
        ((eLpNorm_congr_ae he).le.trans (eLpNorm_add_le (by norm_num)))
    _ = _ := ENNReal.toReal_add hg.eLpNorm_ne_top hh.eLpNorm_ne_top

/-- Strong scalar commutator cancellation for each fixed actual L2 vector field
under the reduced environment law. The coefficients remain the original
Lipschitz coefficients, and the vector need not be a scalar gradient. -/
theorem c17_tendsto_unforced_commutator_L2_zero
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {V : FieldPair d → Vec d} (hVm : Measurable V)
    (hV : ∀ j, MemLp (fun w => V w j) 2 (reducedLaw Q)) :
    Filter.Tendsto (fun δ : ℝ => Real.sqrt (∫ w,
      (Entropy.commOp hd 0 (Calculus.unitMassScaledMollifier d δ) V w) ^ 2 ∂reducedLaw Q))
      (𝓝[>] 0) (𝓝 0) := by
  classical
  let _ : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  choose F hHor hFm hlim using fun j => Correctors.exists_horizontalCore_Lp_approximation
    (reducedLaw Q) (reducedLaw_stationary Q) ((hV j).toLp (fun w => V w j))
  let W (n : ℕ) (w : FieldPair d) (j : Fin d) := F j n w
  have hWm (n : ℕ) : Measurable (W n) := measurable_pi_lambda fun j => (hHor j n).1
  have hW (n : ℕ) (j : Fin d) : MemLp (fun w => W n w j) 2 (reducedLaw Q) := hFm j n
  have hDm (n : ℕ) : Measurable (fun w j => V w j - W n w j) :=
    measurable_pi_lambda fun j => ((measurable_pi_apply j).comp hVm).sub (hHor j n).1
  have hD (n : ℕ) (j : Fin d) : MemLp (fun w => V w j - W n w j) 2 (reducedLaw Q) :=
    (hV j).sub (hW n j)
  have happrox (j : Fin d) : Filter.Tendsto
      (fun n => Real.sqrt (∫ w, (V w j - W n w j) ^ 2 ∂reducedLaw Q))
      Filter.atTop (𝓝 0) := by
    have he := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (F j) (hFm j)
      (fun w => V w j) (hV j)).mp (hlim j)
    have he' : Filter.Tendsto
        (fun n => eLpNorm (fun w => V w j - W n w j) 2 (reducedLaw Q))
        Filter.atTop (𝓝 0) :=
      he.congr fun n => eLpNorm_sub_comm _ _ _ _
    exact Entropy.tendsto_sqrt_integral_sq (fun n => hD n j) he'
  let C := Entropy.commConst d 0
    (Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d))
  have herror : Filter.Tendsto (fun n => C * ∑ j,
      Real.sqrt (∫ w, (V w j - W n w j) ^ 2 ∂reducedLaw Q)) Filter.atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero, mul_zero] using
      (tendsto_finset_sum Finset.univ (fun j _ => happrox j)).const_mul C
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := ((tendsto_order.mp herror).2 (ε / 2) (by linarith)).exists
  have hcoreNorm := c17_tendsto_unforced_commutator_horizontalTests hd Q (fun j => hHor j n)
  have hcoreReal : Filter.Tendsto (fun δ : ℝ =>
      (eLpNorm (Entropy.commOp hd 0 (Calculus.unitMassScaledMollifier d δ) (W n))
        2 (reducedLaw Q)).toReal) (𝓝[>] 0) (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def, W] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcoreNorm
  have hcore : Filter.Tendsto (fun δ : ℝ => Real.sqrt (∫ w,
      (Entropy.commOp hd 0 (Calculus.unitMassScaledMollifier d δ) (W n) w) ^ 2 ∂reducedLaw Q))
      (𝓝[>] 0) (𝓝 0) := by
    apply hcoreReal.congr'
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    exact (c17_sqrt_integral_sq_eq
      (c17_unforced_generator_commutator_memLp hd Q hδ (hWm n) (hW n))).symm
  have hδ1 : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ≤ 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_le_nhds zero_lt_one)
  filter_upwards [self_mem_nhdsWithin, hδ1,
    (tendsto_order.mp hcore).2 (ε / 2) (by linarith)] with δ (hδ : 0 < δ) hδle hc
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsub := Entropy.commOp_sub_ae hd 0 (reducedLaw_stationary Q) hδ
    (c17_ae_reducedCoefficient_lipschitz Q) hVm (hWm n) hV (hW n)
  have htriangle := c17_sqrt_integral_sq_triangle
    (c17_unforced_generator_commutator_memLp hd Q hδ hVm hV)
    (c17_unforced_generator_commutator_memLp hd Q hδ (hDm n) (hD n))
    (c17_unforced_generator_commutator_memLp hd Q hδ (hWm n) (hW n))
    (hsub.mono fun w hw => by linarith)
  have hbound := c17_unforced_generator_commutator_L2_bound hd Q hδ hδle (hDm n) (hD n)
  have htotal := htriangle.trans (add_le_add hbound le_rfl)
  change _ < ε
  change C * _ < ε / 2 at hn
  linarith

private theorem c17_translation_scalarProjection {d : ℕ}
    (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (L : ℂ →L[ℝ] ℝ) (x : Vec d) (f : Lp ℂ 2 Q) :
    L.compLpL 2 Q (complexTranslation Q hQ x f) =
      translationLp Q hQ x (L.compLpL 2 Q f) := by
  apply Lp.ext
  have he := (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae
    (L.coeFn_compLpL f)
  filter_upwards [L.coeFn_compLpL (complexTranslation Q hQ x f),
    coeFn_complexTranslation Q hQ x f,
    coeFn_translationLp Q hQ x (L.compLpL 2 Q f), he] with w ha hb hc hd
  rw [ha, hb, hc, hd]

private theorem c17_derivative_scalarProjection {d : ℕ}
    (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (L : ℂ →L[ℝ] ℝ) {i : Fin d} {f g : Lp ℂ 2 Q}
    (hf : HasComplexHorizontalDerivative Q hQ i f g) :
    HasHorizontalLpDerivative Q hQ i (L.compLpL 2 Q f)
      (L.compLpL 2 Q g) := by
  have h := ((L.compLpL 2 Q).continuous.tendsto g).comp hf
  change Filter.Tendsto (fun t : ℝ => L.compLpL 2 Q
    ((t : ℂ)⁻¹ • (complexTranslation Q hQ (t • unitVector i) f - f)))
    (𝓝[≠] (0 : ℝ)) (𝓝 (L.compLpL 2 Q g)) at h
  apply h.congr
  intro t
  rw [← Complex.ofReal_inv, Complex.coe_smul]
  calc
    _ = (t⁻¹ : ℝ) • L.compLpL 2 Q
        (complexTranslation Q hQ (t • unitVector i) f - f) :=
      (L.compLpL 2 Q).map_smul _ _
    _ = _ := by
      rw [(L.compLpL 2 Q).map_sub, c17_translation_scalarProjection]

private theorem c17_gradient_scalarProjection_weakPairing {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {f : Lp ℂ 2 Q} {G : Fin d → Lp ℂ 2 Q}
    (hG : HasComplexHorizontalGradient Q hQ f G) (L : ℂ →L[ℝ] ℝ)
    (i : Fin d) (H : FieldPair d → ℝ) (hH : IsHorizontalTest H) :
    (∫ w, L (f w) * horizontalDerivative i H w ∂Q) =
      -(∫ w, L (G i w) * H w ∂Q) := by
  have hp := (Correctors.hasHorizontalLpDerivative_to_weak
    (c17_derivative_scalarProjection Q hQ L (hG i)) H hH).2.2
  calc
    (∫ w, L (f w) * horizontalDerivative i H w ∂Q) =
        ∫ w, (L.compLpL 2 Q f) w * horizontalDerivative i H w ∂Q := by
      apply integral_congr_ae
      filter_upwards [L.coeFn_compLpL f] with w hw
      rw [hw]
    _ = -(∫ w, (L.compLpL 2 Q (G i)) w * H w ∂Q) := hp
    _ = -(∫ w, L (G i w) * H w ∂Q) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [L.coeFn_compLpL (G i)] with w hw
      rw [hw]

/-- Real scalar projections of the supplied strong complex gradient identify
all first classical derivatives of its mollified orbit, on one full event for
each positive scale. This uses the given gradient itself. -/
theorem c17_complex_gradient_mollified_orbit_derivative {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {f : Lp ℂ 2 Q} {G : Fin d → Lp ℂ 2 Q}
    (hG : HasComplexHorizontalGradient Q hQ f G) (L : ℂ →L[ℝ] ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᵐ w ∂Q, ∀ i : Fin d,
      coordinateDerivative i
        (orbit (horizontalMollify (Calculus.unitMassScaledMollifier d δ)
          (fun v => L (f v))) w) 0 =
        horizontalMollify (Calculus.unitMassScaledMollifier d δ)
          (fun v => L (G i v)) w := by
  apply ae_all_iff.mpr
  intro i
  exact Calculus.ae_orbit_derivative_mollify_eq hQ hδ hδ1
    (L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable)
    ((L.comp_memLp' (Lp.memLp f)).integrable (by norm_num))
    (L.continuous.measurable.comp (Lp.stronglyMeasurable (G i)).measurable)
    ((L.comp_memLp' (Lp.memLp (G i))).integrable (by norm_num)) i
    (c17_gradient_scalarProjection_weakPairing Q hQ hG L i)

/-- The actual unforced resolvent and its supplied gradient satisfy the
literal spatial weak resolvent equation for each compact smooth kernel. The
source is the original L2 datum, rather than a chosen graph representative. -/
theorem c17_unforced_resolvent_spatial_flux {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (g : Lp ℂ 2 (reducedLaw Q)) {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q i s hs g) G)
    (κ : Vec d → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) :
    ∀ᵐ w ∂reducedLaw Q,
      (s : ℂ) * (∫ x, unforcedComplexResolvent Q i s hs g (translate x w) * (κ x : ℂ)) -
        (∫ x, g (translate x w) * (κ x : ℂ)) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j,
        (∑ k, (w.1 x j k : ℂ) * G k (translate x w)) *
          (coordinateDerivative j κ x : ℂ)) := by
  let _ : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let u := unforcedComplexResolvent Q i s hs g
  have hrep : ((s : ℂ) • u - g : Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
      (fun w => (s : ℂ) * u w - g w) := by
    filter_upwards [Lp.coeFn_sub ((s : ℂ) • u) g, Lp.coeFn_smul (s : ℂ) u] with w ha hb
    simp only [ha, Pi.sub_apply, hb, Pi.smul_apply, smul_eq_mul]
  have horbit := ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable ((s : ℂ) • u - g)).measurable
    ((measurable_const.mul (Lp.stronglyMeasurable u).measurable).sub
      (Lp.stronglyMeasurable g).measurable) hrep
  have he := (unforcedComplexResolvent_spec Q i s hs g).spatial_flux_fixedTest hG κ hκ hκc
  filter_upwards [he, horbit,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) u,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) g]
    with w hw hwe hu hg
  have hui := integrable_spatial_mul_test hu hκ.continuous hκc
  have hgi := integrable_spatial_mul_test hg hκ.continuous hκc
  have hl : (∫ x, ((s : ℂ) • u - g : Lp ℂ 2 (reducedLaw Q)) (translate x w) * (κ x : ℂ)) =
      (s : ℂ) * (∫ x, u (translate x w) * (κ x : ℂ)) -
        (∫ x, g (translate x w) * (κ x : ℂ)) := by
    calc
      _ = ∫ x, (s : ℂ) * (u (translate x w) * (κ x : ℂ)) -
          g (translate x w) * (κ x : ℂ) := by
        apply integral_congr_ae
        filter_upwards [hwe] with x hx
        rw [hx]
        simp only [Pi.sub_apply, Pi.mul_apply]
        ring
      _ = _ := by rw [integral_sub (hui.const_mul (s : ℂ)) hgi, integral_const_mul]
  rw [hl] at hw
  simpa only [zero_mul, add_zero] using hw

private theorem c17_locallyIntegrable_reflected {d : ℕ} {u : Vec d → ℝ}
    (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u 2 (volume.restrict K)) :
    LocallyIntegrable (fun x => u (-x)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hnK := hK.image continuous_neg
  let _ : IsFiniteMeasure (volume.restrict ((fun x : Vec d => -x) '' K)) :=
    isFiniteMeasure_restrict.mpr hnK.measure_ne_top
  have hi := (hu _ hnK).integrable (by norm_num)
  exact ((Measure.measurePreserving_neg (volume : Measure (Vec d))).integrableOn_image
    (Homeomorph.neg (Vec d)).measurableEmbedding).mp hi

private theorem c17_contDiff_orbit_mollified {d : ℕ} {κ : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    {u : FieldPair d → ℝ} (w : FieldPair d)
    (hu : LocallyIntegrable (fun x : Vec d => u (translate (-x) w)) volume) :
    ContDiff ℝ (⊤ : ℕ∞) (orbit (horizontalMollify κ u) w) := by
  have hc := hκc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ hu
  have he : orbit (horizontalMollify κ u) w = fun y : Vec d =>
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun x => u (translate (-x) w))) (-y) :=
    funext (orbit_horizontalMollify_eq_convolution κ u w)
  rw [he]
  exact hc.comp contDiff_id.neg

private theorem c17_coordinateDerivative_orbit_mollified {d : ℕ} {κ : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    {u : FieldPair d → ℝ} (w : FieldPair d)
    (hu : LocallyIntegrable (fun x : Vec d => u (translate (-x) w)) volume)
    (i : Fin d) :
    (fun y => coordinateDerivative i (orbit (horizontalMollify κ u) w) y) =
      fun y => -orbit (horizontalMollify (coordinateDerivative i κ) u) w y := by
  funext y
  let B := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (Vec d)
  have hκ1 : ContDiff ℝ 1 κ := hκ.of_le (by simp)
  have hK := hκc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ1 hu (-y)
  have hneg : HasFDerivAt (fun x : Vec d => -x) (-ContinuousLinearMap.id ℝ (Vec d)) y :=
    (hasFDerivAt_id y).fun_neg
  have hint : Integrable (fun t => B (fderiv ℝ κ t) (u (translate (-(-y - t)) w))) volume :=
    (hκc.fderiv ℝ).convolutionExists_left B
      (hκ1.continuous_fderiv (by simp)) hu (-y)
  have hD : (fderiv ℝ κ ⋆[B, volume] (fun x => u (translate (-x) w))) (-y) (unitVector i) =
      ((coordinateDerivative i κ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun x => u (translate (-x) w))) (-y) := by
    simp only [convolution_def]
    rw [ContinuousLinearMap.integral_apply hint (unitVector i)]
    rfl
  have he : orbit (horizontalMollify κ u) w = fun z : Vec d =>
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun x => u (translate (-x) w))) (-z) :=
    funext (orbit_horizontalMollify_eq_convolution κ u w)
  have hfd : fderiv ℝ (fun z : Vec d =>
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun x => u (translate (-x) w))) (-z)) y = _ :=
    (hK.comp y hneg).fderiv
  rw [he, coordinateDerivative, hfd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, map_neg]
  rw [hD]
  simpa only [orbit] using congrArg Neg.neg
    (orbit_horizontalMollify_eq_convolution (coordinateDerivative i κ) u w y).symm

/-- At each positive scale the same supplied complex gradient determines both
first and second classical orbit derivatives of the literal mollification.
The second derivative is expressed by differentiating the kernel once. -/
theorem c17_complex_gradient_mollified_orbit_derivatives {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {f : Lp ℂ 2 Q} {G : Fin d → Lp ℂ 2 Q}
    (hG : HasComplexHorizontalGradient Q hQ f G) (L : ℂ →L[ℝ] ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᵐ w ∂Q, ∀ j k : Fin d,
      horizontalDerivative j (horizontalMollify (Calculus.unitMassScaledMollifier d δ)
        (fun v => L (f v))) w =
        horizontalMollify (Calculus.unitMassScaledMollifier d δ) (fun v => L (G j v)) w ∧
      horizontalDerivative k (horizontalDerivative j
        (horizontalMollify (Calculus.unitMassScaledMollifier d δ) (fun v => L (f v)))) w =
        -horizontalMollify (coordinateDerivative k (Calculus.unitMassScaledMollifier d δ))
          (fun v => L (G j v)) w := by
  let κ := Calculus.unitMassScaledMollifier d δ
  let u : FieldPair d → ℝ := fun w => L (f w)
  let v : Fin d → FieldPair d → ℝ := fun j w => L (G j w)
  have hκ : ContDiff ℝ (⊤ : ℕ∞) κ := Entropy.contDiff_unitMassScaledMollifier δ
  have hκc : HasCompactSupport κ := Entropy.hasCompactSupport_unitMassScaledMollifier hδ
  have hum : Measurable u := L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable
  have hvm (j) : Measurable (v j) :=
    L.continuous.measurable.comp (Lp.stronglyMeasurable (G j)).measurable
  have hκj (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j κ) :=
    ((contDiff_infty_iff_fderiv.mp hκ).2).clm_apply contDiff_const
  have hκjc (j : Fin d) : HasCompactSupport (coordinateDerivative j κ) :=
    hκc.fderiv_apply ℝ (unitVector j)
  have hlocu : ∀ᵐ w ∂Q, LocallyIntegrable (fun x : Vec d => u (translate (-x) w)) volume := by
    filter_upwards [ae_complex_orbit_memLp_on_all_compacts Q hQ f] with w hw
    exact c17_locallyIntegrable_reflected fun K hK => L.comp_memLp' (hw K hK)
  have hlocv (j) : ∀ᵐ w ∂Q, LocallyIntegrable (fun x : Vec d => v j (translate (-x) w)) volume := by
    filter_upwards [ae_complex_orbit_memLp_on_all_compacts Q hQ (G j)] with w hw
    exact c17_locallyIntegrable_reflected fun K hK => L.comp_memLp' (hw K hK)
  have hfirst := c17_complex_gradient_mollified_orbit_derivative Q hQ hG L hδ hδ1
  have hker (j : Fin d) : (fun w => -horizontalMollify (coordinateDerivative j κ) u w) =ᵐ[Q]
      horizontalMollify κ (v j) := by
    filter_upwards [hfirst, hlocu] with w hw hwu
    have he := congrFun (c17_coordinateDerivative_orbit_mollified hκ hκc w hwu j) 0
    simpa only [orbit, translate_zero] using he.symm.trans (hw j)
  have horbit (j : Fin d) := Entropy.ae_ae_translate_eq hQ
    (measurable_horizontalMollify _ (hκj j).continuous.measurable hum).neg
    (measurable_horizontalMollify _ hκ.continuous.measurable (hvm j)) (hker j)
  filter_upwards [hfirst, hlocu, ae_all_iff.mpr hlocv, ae_all_iff.mpr horbit]
    with w hw hwu hwv hwe
  intro j k
  refine ⟨hw j, ?_⟩
  have heq : (fun y => -orbit (horizontalMollify (coordinateDerivative j κ) u) w y) =
      orbit (horizontalMollify κ (v j)) w :=
    MeasureTheory.Measure.eq_of_ae_eq (hwe j)
      (c17_contDiff_orbit_mollified (hκj j) (hκjc j) w hwu).continuous.neg
      (c17_contDiff_orbit_mollified hκ hκc w (hwv j)).continuous
  have hgrad : orbit (horizontalDerivative j (horizontalMollify κ u)) w =
      orbit (horizontalMollify κ (v j)) w := by
    calc
      _ = fun y => coordinateDerivative j (orbit (horizontalMollify κ u) w) y := by
        funext y
        exact Entropy.horizontalDerivative_translate_eq_orbitDeriv _ w j y
      _ = _ := (c17_coordinateDerivative_orbit_mollified hκ hκc w hwu j).trans heq
  change coordinateDerivative k (orbit (horizontalDerivative j (horizontalMollify κ u)) w) 0 = _
  rw [hgrad]
  simpa only [orbit, translate_zero] using
    congrFun (c17_coordinateDerivative_orbit_mollified hκ hκc w (hwv j) k) 0

private theorem c17_localL2_locallyIntegrable {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] {u : Vec d → E}
    (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u 2 (volume.restrict K)) :
    LocallyIntegrable u volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  exact (hu K hK).integrable (by norm_num)

private theorem c17_commOp_locallyIntegrable {d : ℕ} (hd : 2 ≤ d)
    {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    (V : FieldPair d → Vec d) (w : FieldPair d)
    (hV : ∀ j, LocallyIntegrable (fun x : Vec d => V (translate x w) j) volume) :
    Entropy.commOp hd 0 κ V w = (1 / 2 : ℝ) * ∑ j, ∑ k,
      (Entropy.coeffDeriv w j k 0 * horizontalMollify κ (fun v => V v j) w -
        w.1 0 j k * horizontalMollify (coordinateDerivative k κ) (fun v => V v j) w +
        ∫ x, coordinateDerivative k κ x * w.1 x j k * V (translate x w) j) := by
  have hD (k : Fin d) : Continuous (coordinateDerivative k κ) :=
    (hκ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDc (k : Fin d) : HasCompactSupport (coordinateDerivative k κ) :=
    hκc.fderiv_apply ℝ (unitVector k)
  have hI0 (j) : Integrable (fun x => κ x * V (translate x w) j) := by
    simpa only [smul_eq_mul] using
      (hV j).integrable_smul_left_of_hasCompactSupport hκ.continuous hκc
  have hI1 (j k) : Integrable (fun x => coordinateDerivative k κ x * V (translate x w) j) := by
    simpa only [smul_eq_mul] using
      (hV j).integrable_smul_left_of_hasCompactSupport (hD k) (hDc k)
  have hI2 (j k) : Integrable
      (fun x => coordinateDerivative k κ x * w.1 x j k * V (translate x w) j) := by
    have ha : Continuous (fun x : Vec d => w.1 x j k) :=
      (continuous_apply k).comp ((continuous_apply j).comp w.1.continuous)
    simpa only [smul_eq_mul, Pi.mul_apply] using
      (hV j).integrable_smul_left_of_hasCompactSupport ((hD k).mul ha) (hDc k).mul_right
  have hT (j k) : Integrable (fun x =>
      Entropy.coeffDeriv w j k 0 * (κ x * V (translate x w) j) -
        w.1 0 j k * (coordinateDerivative k κ x * V (translate x w) j) +
        coordinateDerivative k κ x * w.1 x j k * V (translate x w) j) :=
    ((hI0 j).const_mul (Entropy.coeffDeriv w j k 0)).sub
      ((hI1 j k).const_mul (w.1 0 j k)) |>.add (hI2 j k)
  unfold Entropy.commOp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc
    _ = ∫ x, (1 / 2 : ℝ) * ∑ k,
        (Entropy.coeffDeriv w j k 0 * (κ x * V (translate x w) j) -
          w.1 0 j k * (coordinateDerivative k κ x * V (translate x w) j) +
          coordinateDerivative k κ x * w.1 x j k * V (translate x w) j) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Entropy.commKernel, zero_mul, add_zero, Finset.sum_mul,
        Entropy.coeffDeriv]
      rw [mul_assoc]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun k _ => hT j k)]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      calc
        _ = (∫ x, Entropy.coeffDeriv w j k 0 * (κ x * V (translate x w) j) -
            w.1 0 j k * (coordinateDerivative k κ x * V (translate x w) j)) +
            ∫ x, coordinateDerivative k κ x * w.1 x j k * V (translate x w) j :=
          integral_add (((hI0 j).const_mul _).sub ((hI1 j k).const_mul _)) (hI2 j k)
        _ = _ := by
          rw [integral_sub ((hI0 j).const_mul _) ((hI1 j k).const_mul _),
            integral_const_mul, integral_const_mul]
          rfl

private theorem c17_projection_mul_real (L : ℂ →L[ℝ] ℝ) (z : ℂ) (r : ℝ) :
    L (z * (r : ℂ)) = L z * r := by
  simpa only [Complex.real_smul, smul_eq_mul, mul_comm] using L.map_smul r z

private theorem c17_projection_spatial_integral {d : ℕ} (L : ℂ →L[ℝ] ℝ)
    {u : Vec d → ℂ}
    (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u 2 (volume.restrict K))
    {κ : Vec d → ℝ} (hκ : Continuous κ) (hκc : HasCompactSupport κ) :
    L (∫ x, u x * (κ x : ℂ)) = ∫ x, κ x * L (u x) := by
  rw [← L.integral_comp_comm (integrable_spatial_mul_test hu hκ hκc)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => (c17_projection_mul_real L (u x) (κ x)).trans (mul_comm _ _)

/-- Each real scalar projection of the actual resolvent satisfies its literal
mollified spatial flux equation, with the supplied gradient and unchanged coefficients. -/
theorem c17_unforced_resolvent_projected_spatial_flux {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (g : Lp ℂ 2 (reducedLaw Q)) {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q i s hs g) G)
    (L : ℂ →L[ℝ] ℝ) (κ : Vec d → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) :
    ∀ᵐ w ∂reducedLaw Q,
      s * horizontalMollify κ (fun v => L (unforcedComplexResolvent Q i s hs g v)) w -
        horizontalMollify κ (fun v => L (g v)) w =
      -(1 / 2 : ℝ) * ∑ j, ∑ k,
        ∫ x, coordinateDerivative k κ x * w.1 x j k * L (G j (translate x w)) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let u := unforcedComplexResolvent Q i s hs g
  have hsymm : ∀ᵐ w ∂reducedLaw Q, ∀ x j k, w.1 x j k = w.1 x k j := by
    apply (Probability.measurableEmbedding_reduce d).ae_map_iff.mpr
    filter_upwards [Q.regular] with ω hω
    intro x j k
    exact (congrFun (congrFun (reducedCoefficient_symm hω x) j) k).symm
  filter_upwards [c17_unforced_resolvent_spatial_flux Q i s hs g hG κ hκ hκc,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) u,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (G j)), hsymm] with w hw hu hg hGl hS
  have hD (j : Fin d) : Continuous (coordinateDerivative j κ) :=
    (hκ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDc (j : Fin d) : HasCompactSupport (coordinateDerivative j κ) :=
    hκc.fderiv_apply ℝ (unitVector j)
  have hA (j k : Fin d) : Continuous (fun x : Vec d => w.1 x j k) :=
    (continuous_apply k).comp ((continuous_apply j).comp w.1.continuous)
  have hT (j k : Fin d) : Integrable
      (fun x => G k (translate x w) * ((w.1 x j k * coordinateDerivative j κ x : ℝ) : ℂ)) :=
    integrable_spatial_mul_test (hGl k) ((hA j k).mul (hD j)) (hDc j).mul_left
  have hflux : (∫ x, ∑ j, (∑ k, (w.1 x j k : ℂ) * G k (translate x w)) *
        (coordinateDerivative j κ x : ℂ)) =
      ∑ j, ∑ k, ∫ x, G k (translate x w) *
        ((w.1 x j k * coordinateDerivative j κ x : ℝ) : ℂ) := by
    calc
      _ = ∫ x, ∑ j, ∑ k, G k (translate x w) *
          ((w.1 x j k * coordinateDerivative j κ x : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [] with x
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        push_cast
        ring
      _ = _ := by
        rw [integral_finsetSum _ (fun j _ => integrable_finset_sum _ (fun k _ => hT j k))]
        exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ (fun k _ => hT j k)
  have hfluxL : L (∫ x, ∑ j, (∑ k, (w.1 x j k : ℂ) * G k (translate x w)) *
        (coordinateDerivative j κ x : ℂ)) =
      ∑ j, ∑ k, ∫ x, coordinateDerivative k κ x * w.1 x j k * L (G j (translate x w)) := by
    rw [hflux, map_sum]
    simp only [map_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [c17_projection_spatial_integral L (κ := fun x => w.1 x k j * coordinateDerivative k κ x)
      (hGl j) ((hA k j).mul (hD k)) (hDc k).mul_left]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by dsimp only; rw [hS x k j]; ring
  have hp := congrArg L hw
  have hc : ∀ z : ℂ, L ((s : ℂ) * z) = s * L z := by
    intro z
    rw [mul_comm, c17_projection_mul_real, mul_comm]
  have hh : ∀ z : ℂ, L (-(1 / 2 : ℂ) * z) = -(1 / 2 : ℝ) * L z := by
    intro z
    have he : -(1 / 2 : ℂ) * z = z * ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [he, c17_projection_mul_real, mul_comm]
  rw [map_sub, hc, hh,
    c17_projection_spatial_integral L hu hκ.continuous hκc,
    c17_projection_spatial_integral L hg hκ.continuous hκc, hfluxL] at hp
  exact hp

/-- The actual unforced resolvent has the literal mollified generator residual.
The commutator uses the same supplied gradient and the original coefficient field. -/
theorem c17_unforced_resolvent_mollified_graph_residual {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q i s hs g) G)
    (L : ℂ →L[ℝ] ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᵐ w ∂reducedLaw Q,
      s * horizontalMollify (Calculus.unitMassScaledMollifier d δ)
          (fun v => L (unforcedComplexResolvent Q i s hs g v)) w -
        envGenerator hd 0 (horizontalMollify (Calculus.unitMassScaledMollifier d δ)
          (fun v => L (unforcedComplexResolvent Q i s hs g v))) w - L (g w) =
      horizontalMollify (Calculus.unitMassScaledMollifier d δ) (fun v => L (g v)) w -
        L (g w) - Entropy.commOp hd 0 (Calculus.unitMassScaledMollifier d δ)
          (fun v j => L (G j v)) w := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let κ := Calculus.unitMassScaledMollifier d δ
  let u : FieldPair d → ℝ := fun v => L (unforcedComplexResolvent Q i s hs g v)
  let V : FieldPair d → Vec d := fun v j => L (G j v)
  have hκ : ContDiff ℝ (⊤ : ℕ∞) κ := Entropy.contDiff_unitMassScaledMollifier δ
  have hκc : HasCompactSupport κ := Entropy.hasCompactSupport_unitMassScaledMollifier hδ
  filter_upwards [c17_unforced_resolvent_projected_spatial_flux Q i s hs g hG L κ hκ hκc,
    c17_complex_gradient_mollified_orbit_derivatives (reducedLaw Q)
      (reducedLaw_stationary Q) hG L hδ hδ1,
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (G j))] with w hf hD hGl
  have hV (j) : LocallyIntegrable (fun x : Vec d => V (translate x w) j) volume :=
    c17_localL2_locallyIntegrable fun K hK => L.comp_memLp' (hGl j K hK)
  have hC := c17_commOp_locallyIntegrable hd hκ hκc V w hV
  have hA : envGenerator hd 0 (horizontalMollify κ u) w =
      (1 / 2 : ℝ) * ∑ j, ∑ k,
        (Entropy.coeffDeriv w j k 0 * horizontalMollify κ (fun v => V v j) w -
          w.1 0 j k * horizontalMollify (coordinateDerivative k κ) (fun v => V v j) w) := by
    simp only [envGenerator, zero_mul, add_zero]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [(hD j k).1, (hD j k).2]
    dsimp [κ, V, Entropy.coeffDeriv]
    ring
  simp only [Finset.sum_add_distrib] at hC
  change s * horizontalMollify κ u w - envGenerator hd 0 (horizontalMollify κ u) w -
      L (g w) = horizontalMollify κ (fun v => L (g v)) w - L (g w) -
        Entropy.commOp hd 0 κ V w
  linarith [hf, hA, hC]

/-- The literal mollified graph residual of the actual unforced resolvent
converges to zero in reduced-law L2, for every real scalar projection. -/
theorem c17_tendsto_unforced_resolvent_mollified_graph_residual {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q i s hs g) G) (L : ℂ →L[ℝ] ℝ) :
    Filter.Tendsto (fun δ : ℝ => Real.sqrt (∫ w,
      (s * horizontalMollify (Calculus.unitMassScaledMollifier d δ)
          (fun v => L (unforcedComplexResolvent Q i s hs g v)) w -
        envGenerator hd 0 (horizontalMollify (Calculus.unitMassScaledMollifier d δ)
          (fun v => L (unforcedComplexResolvent Q i s hs g v))) w - L (g w)) ^ 2
      ∂reducedLaw Q)) (𝓝[>] 0) (𝓝 0) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let f : FieldPair d → ℝ := fun w => L (g w)
  let V : FieldPair d → Vec d := fun w j => L (G j w)
  let A (δ : ℝ) (w : FieldPair d) :=
    horizontalMollify (Calculus.unitMassScaledMollifier d δ) f w - f w
  let C (δ : ℝ) := Entropy.commOp hd 0 (Calculus.unitMassScaledMollifier d δ) V
  have hfm : Measurable f := L.continuous.measurable.comp (Lp.stronglyMeasurable g).measurable
  have hf : MemLp f 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp g)
  have hVm : Measurable V := measurable_pi_lambda fun j =>
    L.continuous.measurable.comp (Lp.stronglyMeasurable (G j)).measurable
  have hV (j) : MemLp (fun w => V w j) 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp (G j))
  have hA (δ : ℝ) (hδ : 0 < δ) : MemLp (A δ) 2 (reducedLaw Q) :=
    (Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q) hδ
      ENNReal.ofNat_ne_top hfm hf).sub hf
  have hC (δ : ℝ) (hδ : 0 < δ) : MemLp (C δ) 2 (reducedLaw Q) :=
    c17_unforced_generator_commutator_memLp hd Q hδ hVm hV
  have hAlim : Filter.Tendsto (fun δ => Real.sqrt (∫ w, A δ w ^ 2 ∂reducedLaw Q))
      (𝓝[>] 0) (𝓝 0) := by
    have he := Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier
      (reducedLaw Q) (reducedLaw_stationary Q) 2 ENNReal.ofNat_ne_top hfm hf
    have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
    simp only [ENNReal.toReal_zero] at hr
    apply hr.congr'
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    exact (c17_sqrt_integral_sq_eq (hA δ hδ)).symm
  have hClim := c17_tendsto_unforced_commutator_L2_zero hd Q hVm hV
  have hδ1 : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ≤ 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_le_nhds zero_lt_one)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using hAlim.add hClim)
    (Filter.Eventually.of_forall fun δ => Real.sqrt_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin, hδ1] with δ (hδ : 0 < δ) hδle
  have he := c17_unforced_resolvent_mollified_graph_residual hd Q i s hs g hG L hδ hδle
  have hR := MemLp.ae_eq (he.mono fun w hw => hw.symm) ((hA δ hδ).sub (hC δ hδ))
  have ht := c17_sqrt_integral_sq_triangle hR (hA δ hδ) (hC δ hδ).neg
    (he.mono fun w hw => by change _ = A δ w + -(C δ w); simpa only [A, C, f, V, sub_eq_add_neg] using hw)
  simpa only [Pi.neg_apply, neg_sq] using ht


/-- Expanding compact spatial tests eventually agree locally with the actual
mollified resolvent orbit, and therefore with its literal textbook generator.
This is pointwise cutoff passage; passing path expectations requires occupation
integrability separately. -/
theorem c17_unforced_resolvent_compact_orbit_tests {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (g : Lp ℂ 2 (reducedLaw Q)) (L : ℂ →L[ℝ] ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ w ∂reducedLaw Q, ∃ ψ : ℕ → Vec d → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) ∧ HasCompactSupport (ψ n)) ∧
      ∀ y, ∀ᶠ n in Filter.atTop,
        ψ n =ᶠ[𝓝 y] orbit (horizontalMollify (Calculus.unitMassScaledMollifier d δ)
          (fun v => L (unforcedComplexResolvent Q i s hs g v))) w ∧
        External.Draft.svGenerator (reducedCoefficient w)
            (forcedDrift (reducedCoefficient w) i 0) (ψ n) y =
          External.Draft.svGenerator (reducedCoefficient w)
            (forcedDrift (reducedCoefficient w) i 0)
            (orbit (horizontalMollify (Calculus.unitMassScaledMollifier d δ)
              (fun v => L (unforcedComplexResolvent Q i s hs g v))) w) y := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let u := unforcedComplexResolvent Q i s hs g
  let κ := Calculus.unitMassScaledMollifier d δ
  have hκ : ContDiff ℝ (⊤ : ℕ∞) κ := Entropy.contDiff_unitMassScaledMollifier δ
  have hκc : HasCompactSupport κ := Entropy.hasCompactSupport_unitMassScaledMollifier hδ
  obtain ⟨χ, hχ, _, _, hχ1, hχ0⟩ := exists_cutoff d
  filter_upwards [ae_complex_orbit_memLp_on_all_compacts
    (reducedLaw Q) (reducedLaw_stationary Q) u] with w hw
  have hloc : LocallyIntegrable (fun x : Vec d => L (u (translate (-x) w))) volume :=
    c17_locallyIntegrable_reflected fun K hK => L.comp_memLp' (hw K hK)
  let f := orbit (horizontalMollify κ (fun v => L (u v))) w
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := c17_contDiff_orbit_mollified hκ hκc w hloc
  refine ⟨fun n => cutoffFn χ ((n : ℝ) + 1) f, ?_, ?_⟩
  · intro n
    exact ⟨contDiff_cutoffFn hχ hf _, hasCompactSupport_cutoffFn f (by positivity) hχ0⟩
  · intro y
    have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (Filter.eventually_gt_atTop ‖y‖)] with n hn
    have he := cutoffFn_eventuallyEq f (by positivity) hχ1 hn
    exact ⟨he, svGenerator_congr _ _ he⟩


/-- The environment generator and the same symmetric spatial diffusion
operator agree pointwise along an orbit. -/
theorem c17_envGenerator_eq_svGenerator {d : ℕ} (hd : 2 ≤ d)
    (w : FieldPair d) (F : FieldPair d → ℝ) (i : Fin d)
    (hsym : ∀ x j k, w.1 x j k = w.1 x k j) (x : Vec d) :
    envGenerator hd 0 F (translate x w) =
      External.Draft.svGenerator (fun y => w.1 y)
        (forcedDrift (fun y => w.1 y) i 0) (orbit F w) x := by
  rw [envGenerator_translate]
  simp only [zero_mul, add_zero, External.Draft.svGenerator, forcedDrift,
    matrixDivDrift, coordinateDerivative]
  have hcoeff (j k : Fin d) :
      (fun y => w.1 y j k) = (fun y => w.1 y k j) := funext fun y => hsym y j k
  have hsecond :
      (∑ k, ∑ j, w.1 x j k *
        fderiv ℝ (fun y => fderiv ℝ (orbit F w) y (unitVector j)) x (unitVector k)) =
      ∑ k, ∑ j, w.1 x k j *
        fderiv ℝ (fun y => fderiv ℝ (orbit F w) y (unitVector j)) x (unitVector k) := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym x j k]
  have hfirst :
      (∑ k, ∑ j, fderiv ℝ (fun y => w.1 y j k) x (unitVector k) *
        fderiv ℝ (orbit F w) x (unitVector j)) =
      ∑ j, (∑ k, fderiv ℝ (fun y => w.1 y k j) x (unitVector k)) *
        fderiv ℝ (orbit F w) x (unitVector j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcoeff j k]
  have hdrift :
      (∑ j, ((1 / 2 : ℝ) * ∑ k, fderiv ℝ (fun y => w.1 y k j) x (unitVector k)) *
        fderiv ℝ (orbit F w) x (unitVector j)) =
      (1 / 2 : ℝ) * ∑ j, (∑ k, fderiv ℝ (fun y => w.1 y k j) x (unitVector k)) *
        fderiv ℝ (orbit F w) x (unitVector j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [Finset.sum_add_distrib]
  rw [hsecond, hfirst, hdrift]
  ring



/-- Expanding cutoffs agree with the original function near the entire range
of each continuous path on a fixed finite time interval. -/
theorem c17_cutoff_eventually_eq_on_path {d : ℕ} (χ f : Vec d → ℝ)
    (hχ : ∀ y, ‖y‖ ≤ 1 → χ y = 1) (γ : Path d) (t : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ≥0, u ≤ t →
      cutoffFn χ ((n : ℝ) + 1) f =ᶠ[𝓝 (γ u)] f := by
  obtain ⟨R, hR⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).image
    γ.continuous).isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt R
  filter_upwards [eventually_ge_atTop N] with n hn
  have hRn : R < (n : ℝ) + 1 := by
    have hn' : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith
  intro u hu
  apply cutoffFn_eventuallyEq f (by positivity) hχ
  exact lt_of_le_of_lt (hR _ ⟨u, ⟨bot_le, hu⟩, rfl⟩) hRn

/-- The corresponding local generators agree uniformly on each finite path segment. -/
theorem c17_cutoff_generator_eventually_eq_on_path {d : ℕ}
    (A : Vec d → Mat d) (b : Vec d → Vec d) (χ f : Vec d → ℝ)
    (hχ : ∀ y, ‖y‖ ≤ 1 → χ y = 1) (γ : Path d) (t : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ≥0, u ≤ t →
      External.Draft.svGenerator A b (cutoffFn χ ((n : ℝ) + 1) f) (γ u) =
        External.Draft.svGenerator A b f (γ u) := by
  filter_upwards [c17_cutoff_eventually_eq_on_path χ f hχ γ t] with n hn
  intro u hu
  exact svGenerator_congr A b (hn u hu)

private theorem c17_fderiv_product {d : ℕ} {f g : Vec d → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (y v : Vec d) :
    fderiv ℝ (fun z => f z * g z) y v =
      f y * fderiv ℝ g y v + g y * fderiv ℝ f y v := by
  rw [show fderiv ℝ (fun z => f z * g z) y = _ from
    ((hf y).hasFDerivAt.mul (hg y).hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]

private theorem c17_fderiv_product_second {d : ℕ} {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (2 : ℕ∞) f) (hg : ContDiff ℝ (2 : ℕ∞) g)
    (y : Vec d) (j k : Fin d) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => f w * g w) z (unitVector k)) y
      (unitVector j) =
      f y * fderiv ℝ (fun z => fderiv ℝ g z (unitVector k)) y (unitVector j) +
      g y * fderiv ℝ (fun z => fderiv ℝ f z (unitVector k)) y (unitVector j) +
      fderiv ℝ f y (unitVector j) * fderiv ℝ g y (unitVector k) +
      fderiv ℝ g y (unitVector j) * fderiv ℝ f y (unitVector k) := by
  have hfd := hf.differentiable (by simp)
  have hgd := hg.differentiable (by simp)
  have hdF : Differentiable ℝ (fun z => fderiv ℝ f z (unitVector k)) :=
    ((hf.fderiv_right (by norm_num)).clm_apply contDiff_const).differentiable one_ne_zero
  have hdG : Differentiable ℝ (fun z => fderiv ℝ g z (unitVector k)) :=
    ((hg.fderiv_right (by norm_num)).clm_apply contDiff_const).differentiable one_ne_zero
  rw [show (fun z => fderiv ℝ (fun w => f w * g w) z (unitVector k)) =
    (fun z => f z * fderiv ℝ g z (unitVector k) +
      g z * fderiv ℝ f z (unitVector k)) from
    funext fun z => c17_fderiv_product hfd hgd z _]
  have hh := ((hfd y).hasFDerivAt.mul (hdG y).hasFDerivAt).add
    ((hgd y).hasFDerivAt.mul (hdF y).hasFDerivAt)
  rw [show fderiv ℝ (fun z => f z * fderiv ℝ g z (unitVector k) +
      g z * fderiv ℝ f z (unitVector k)) y = _ from hh.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The textbook generator product rule, without any coefficient regularity. -/
theorem c17_svGenerator_product {d : ℕ} (A : Vec d → Mat d)
    (b : Vec d → Vec d) (f g : Vec d → ℝ)
    (hf : ContDiff ℝ (2 : ℕ∞) f) (hg : ContDiff ℝ (2 : ℕ∞) g) (y : Vec d) :
    External.Draft.svGenerator A b (fun z => f z * g z) y =
      f y * External.Draft.svGenerator A b g y +
      g y * External.Draft.svGenerator A b f y +
      (1 / 2 : ℝ) * ∑ j, ∑ k, A y j k *
        (fderiv ℝ f y (unitVector j) * fderiv ℝ g y (unitVector k) +
          fderiv ℝ g y (unitVector j) * fderiv ℝ f y (unitVector k)) := by
  unfold External.Draft.svGenerator
  simp only [c17_fderiv_product_second hf hg]
  simp only [c17_fderiv_product (hf.differentiable (by simp))
    (hg.differentiable (by simp))]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [mul_left_comm _ (f y), mul_left_comm _ (g y), ← Finset.mul_sum]
  ring

/-- First coordinate derivative of a rescaled cutoff. -/
private theorem c17_scaled_fderiv {d : ℕ} {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (2 : ℕ∞) χ) (a : ℝ) (y : Vec d) (j : Fin d) :
    fderiv ℝ (fun z : Vec d => χ (a • z)) y (unitVector j) =
      a * fderiv ℝ χ (a • y) (unitVector j) := by
  have hd := ((hχ.differentiable (by simp)) (a • y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_smul a)
  have hd' : fderiv ℝ (fun z : Vec d => χ (a • z)) y =
      (fderiv ℝ χ (a • y)).comp (a • ContinuousLinearMap.id ℝ (Vec d)) := by
    simpa only [Function.comp_def] using hd.fderiv
  rw [hd']
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- Second coordinate derivative of a rescaled cutoff. -/
private theorem c17_scaled_fderiv_second {d : ℕ} {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (2 : ℕ∞) χ) (a : ℝ) (y : Vec d) (j k : Fin d) :
    fderiv ℝ (fun z => fderiv ℝ (fun w : Vec d => χ (a • w)) z
      (unitVector k)) y (unitVector j) =
      a * a * fderiv ℝ (fun z => fderiv ℝ χ z (unitVector k)) (a • y)
        (unitVector j) := by
  have hd : Differentiable ℝ (fun z => fderiv ℝ χ z (unitVector k)) :=
    ((hχ.fderiv_right (by norm_num)).clm_apply contDiff_const).differentiable one_ne_zero
  rw [show (fun z => fderiv ℝ (fun w : Vec d => χ (a • w)) z (unitVector k)) =
      (fun z => a * fderiv ℝ χ (a • z) (unitVector k)) from
    funext fun z => c17_scaled_fderiv hχ a z k]
  have hcomp := ((hd (a • y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_smul a)).const_mul a
  have hcomp' : fderiv ℝ (fun z : Vec d => a * fderiv ℝ χ (a • z) (unitVector k)) y =
      (a • fderiv ℝ (fun z => fderiv ℝ χ z (unitVector k)) (a • y)).comp
        (a • ContinuousLinearMap.id ℝ (Vec d)) := by
    ext v
    simpa only [Function.comp_def, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply] using congrArg (fun T : Vec d →L[ℝ] ℝ => T v) hcomp.fderiv
  rw [hcomp']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

/-- Uniform generator bound for all rescalings with scale at most one. -/
private theorem c17_scaled_generator_bound {d : ℕ} {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (2 : ℕ∞) χ) (hc : HasCompactSupport χ)
    (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C : ℝ, ∀ (A : Vec d → Mat d) (b : Vec d → Vec d) (a : ℝ),
      0 ≤ a → a ≤ 1 → (∀ y j k, |A y j k| ≤ M) →
      (∀ y j, |b y j| ≤ N) → ∀ y,
        |External.Draft.svGenerator A b (fun z => χ (a • z)) y| ≤ C := by
  have h1 : ∀ j : Fin d, ∃ B : ℝ, ∀ x,
      ‖fderiv ℝ χ x (unitVector j)‖ ≤ B := fun j =>
    (continuous_fderiv_apply_first hχ j).bounded_above_of_compact_support
      (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (unitVector j))
  have h2 : ∀ j k : Fin d, ∃ B : ℝ, ∀ x,
      ‖fderiv ℝ (fun z => fderiv ℝ χ z (unitVector k)) x (unitVector j)‖ ≤ B :=
    fun j k => (continuous_fderiv_apply_second hχ j k).bounded_above_of_compact_support
      (HasCompactSupport.fderiv_apply (𝕜 := ℝ)
        (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (unitVector k)) (unitVector j))
  choose B1 hB1 using h1
  choose B2 hB2 using h2
  refine ⟨(1 / 2 : ℝ) * ∑ j, ∑ k, M * B2 j k + ∑ j, N * B1 j, ?_⟩
  intro A b a ha ha1 hA hb y
  have ha2 : a * a ≤ 1 := by nlinarith
  unfold External.Draft.svGenerator
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [c17_scaled_fderiv_second hχ]
    simp only [abs_mul, abs_of_nonneg ha]
    have hbase : |fderiv ℝ (fun z => fderiv ℝ χ z (unitVector k)) (a • y)
        (unitVector j)| ≤ B2 j k := by simpa only [Real.norm_eq_abs] using hB2 j k (a • y)
    have hs : a * a * |fderiv ℝ (fun z => fderiv ℝ χ z (unitVector k)) (a • y)
        (unitVector j)| ≤ B2 j k := by
      calc
        _ ≤ 1 * |fderiv ℝ (fun z => fderiv ℝ χ z (unitVector k)) (a • y)
            (unitVector j)| := mul_le_mul_of_nonneg_right ha2 (abs_nonneg _)
        _ ≤ B2 j k := by simpa using hbase
    exact mul_le_mul (hA y j k) hs (mul_nonneg (mul_nonneg ha ha) (abs_nonneg _)) hM
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [c17_scaled_fderiv hχ, abs_mul, abs_mul, abs_of_nonneg ha]
    have hbase : |fderiv ℝ χ (a • y) (unitVector j)| ≤ B1 j := by
      simpa only [Real.norm_eq_abs] using hB1 j (a • y)
    have hs : a * |fderiv ℝ χ (a • y) (unitVector j)| ≤ B1 j := by
      calc
        _ ≤ 1 * |fderiv ℝ χ (a • y) (unitVector j)| :=
          mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
        _ ≤ B1 j := by simpa using hbase
    exact mul_le_mul (hb y j) hs (mul_nonneg ha (abs_nonneg _)) hN

/-- A product-rule majorant in terms of the free generator and first derivatives. -/
theorem c17_svGenerator_product_bound {d : ℕ} (A : Vec d → Mat d)
    (b : Vec d → Vec d) (h f : Vec d → ℝ)
    (hh : ContDiff ℝ (2 : ℕ∞) h) (hf : ContDiff ℝ (2 : ℕ∞) f) (y : Vec d)
    (C D M : ℝ) (hD : 0 ≤ D)
    (hval : |h y| ≤ 1) (hgen : |External.Draft.svGenerator A b h y| ≤ C)
    (hder : ∀ j, |fderiv ℝ h y (unitVector j)| ≤ D)
    (hA : ∀ j k, |A y j k| ≤ M) :
    |External.Draft.svGenerator A b (fun z => h z * f z) y| ≤
      |External.Draft.svGenerator A b f y| + C * |f y| +
      (1 / 2 : ℝ) * ∑ j, ∑ k, M * D *
        (|fderiv ℝ f y (unitVector j)| + |fderiv ℝ f y (unitVector k)|) := by
  rw [c17_svGenerator_product A b h f hh hf y]
  have hfirst : |h y * External.Draft.svGenerator A b f y| ≤
      |External.Draft.svGenerator A b f y| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right hval
      (abs_nonneg (External.Draft.svGenerator A b f y))
  have hsecond : |f y * External.Draft.svGenerator A b h y| ≤ C * |f y| := by
    rw [abs_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hgen (abs_nonneg (f y))
  have hsum : |∑ j, ∑ k, A y j k *
      (fderiv ℝ h y (unitVector j) * fderiv ℝ f y (unitVector k) +
       fderiv ℝ f y (unitVector j) * fderiv ℝ h y (unitVector k))| ≤
      ∑ j, ∑ k, M * D *
        (|fderiv ℝ f y (unitVector j)| + |fderiv ℝ f y (unitVector k)|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    have hinner := abs_add_le (fderiv ℝ h y (unitVector j) * fderiv ℝ f y (unitVector k))
      (fderiv ℝ f y (unitVector j) * fderiv ℝ h y (unitVector k))
    rw [abs_mul, abs_mul] at hinner
    have hinner' : |fderiv ℝ h y (unitVector j)| *
        |fderiv ℝ f y (unitVector k)| +
        |fderiv ℝ f y (unitVector j)| * |fderiv ℝ h y (unitVector k)| ≤
        D * (|fderiv ℝ f y (unitVector j)| +
          |fderiv ℝ f y (unitVector k)|) := by
      have hj := mul_le_mul_of_nonneg_right (hder j)
        (abs_nonneg (fderiv ℝ f y (unitVector k)))
      have hk := mul_le_mul_of_nonneg_left (hder k)
        (abs_nonneg (fderiv ℝ f y (unitVector j)))
      nlinarith
    calc
      |A y j k| * |fderiv ℝ h y (unitVector j) * fderiv ℝ f y (unitVector k) +
          fderiv ℝ f y (unitVector j) * fderiv ℝ h y (unitVector k)| ≤
          |A y j k| * (D * (|fderiv ℝ f y (unitVector j)| +
            |fderiv ℝ f y (unitVector k)|)) :=
        mul_le_mul_of_nonneg_left (hinner.trans hinner') (abs_nonneg _)
      _ ≤ M * (D * (|fderiv ℝ f y (unitVector j)| +
            |fderiv ℝ f y (unitVector k)|)) :=
        mul_le_mul_of_nonneg_right (hA j k)
          (mul_nonneg hD (add_nonneg (abs_nonneg _) (abs_nonneg _)))
      _ = M * D * (|fderiv ℝ f y (unitVector j)| +
            |fderiv ℝ f y (unitVector k)|) := by ring

  have ht := abs_add_le (h y * External.Draft.svGenerator A b f y +
    f y * External.Draft.svGenerator A b h y)
    ((1 / 2 : ℝ) * ∑ j, ∑ k, A y j k *
      (fderiv ℝ h y (unitVector j) * fderiv ℝ f y (unitVector k) +
       fderiv ℝ f y (unitVector j) * fderiv ℝ h y (unitVector k)))
  have ht' := abs_add_le (h y * External.Draft.svGenerator A b f y)
    (f y * External.Draft.svGenerator A b h y)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
  linarith

/-- Uniform product-generator majorant for cutoffs at radii at least one. -/
theorem c17_cutoff_generator_majorant {d : ℕ} {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (A : Vec d → Mat d) (b : Vec d → Vec d) (R : ℝ),
      1 ≤ R → (∀ y j k, |A y j k| ≤ M) →
      (∀ y j, |b y j| ≤ N) → ∀ (f : Vec d → ℝ),
      ContDiff ℝ (2 : ℕ∞) f → ∀ y,
      |External.Draft.svGenerator A b (cutoffFn χ R f) y| ≤
        |External.Draft.svGenerator A b f y| + C * |f y| +
        (1 / 2 : ℝ) * ∑ j, ∑ k, M * D *
          (|fderiv ℝ f y (unitVector j)| + |fderiv ℝ f y (unitVector k)|) := by
  obtain ⟨C, hC⟩ := c17_scaled_generator_bound (contDiff_two_of_top hχ) hc M N hM hN
  obtain ⟨D, hD⟩ := exists_cutoff_deriv_bound hχ hc
  refine ⟨max C 0, max D 0, le_max_right _ _, le_max_right _ _, ?_⟩
  intro A b R hR hA hb f hf y
  have hR0 : 0 < R := by linarith
  have ha0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0.le
  have ha1 : R⁻¹ ≤ 1 := (inv_le_one₀ hR0).2 hR
  have hval : |χ (R⁻¹ • y)| ≤ 1 := by rw [abs_of_nonneg (hχ01 _).1]; exact (hχ01 _).2
  have hgen : |External.Draft.svGenerator A b (fun z => χ (R⁻¹ • z)) y| ≤ max C 0 :=
    (hC A b R⁻¹ ha0 ha1 hA hb y).trans (le_max_left _ _)
  have hder : ∀ j, |fderiv ℝ (fun z : Vec d => χ (R⁻¹ • z)) y (unitVector j)| ≤ max D 0 := by
    intro j
    rw [c17_scaled_fderiv (contDiff_two_of_top hχ), abs_mul, abs_of_nonneg ha0]
    calc
      R⁻¹ * |fderiv ℝ χ (R⁻¹ • y) (unitVector j)| ≤
          1 * |fderiv ℝ χ (R⁻¹ • y) (unitVector j)| :=
        mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
      _ ≤ max D 0 := by simpa using (hD (R⁻¹ • y) j).trans (le_max_left D 0)
  exact c17_svGenerator_product_bound A b (fun z => χ (R⁻¹ • z)) f
    ((contDiff_two_of_top hχ).comp (contDiff_const_smul _)) hf y (max C 0) (max D 0) M
    (le_max_right _ _) hval hgen hder (hA y)



/-- Transfer a literal residual's square-integral limit to the L2 norms
of measurable representatives that agree almost everywhere. -/
theorem c17_representative_L2_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (r a : ℕ → α → ℝ) (hr : ∀ n, MemLp (r n) 2 μ)
    (he : ∀ n, r n =ᵐ[μ] a n)
    (hlim : Tendsto (fun n => Real.sqrt (∫ x, (a n x) ^ 2 ∂μ)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖(hr n).toLp (r n)‖) atTop (𝓝 0) := by
  apply hlim.congr
  intro n
  rw [Lp.norm_toLp]
  have hnorm : Real.sqrt (∫ x, (r n x) ^ 2 ∂μ) =
      (eLpNorm (r n) 2 μ).toReal := by
    rw [(hr n).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    congr 1
    · exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs])
    · simp
  rw [← hnorm]
  congr 1
  exact integral_congr_ae ((he n).mono fun x hx => by change a n x ^ 2 = r n x ^ 2; rw [hx])

/-- Measurable representatives of the literal mollified graph residual,
with norms tending to zero along the standard positive scales. -/
theorem c17_resolvent_residual_representatives {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q i s hs g) G) (L : ℂ →L[ℝ] ℝ) :
    ∃ (r : ℕ → FieldPair d → ℝ) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q)),
      (∀ n, Measurable (r n)) ∧
      (∀ n, r n =ᵐ[reducedLaw Q] fun w =>
        s * horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (unforcedComplexResolvent Q i s hs g v)) w -
        envGenerator hd 0 (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (unforcedComplexResolvent Q i s hs g v))) w - L (g w)) ∧
      Tendsto (fun n => ‖(hr n).toLp (r n)‖) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let f : FieldPair d → ℝ := fun w => L (g w)
  let V : FieldPair d → Vec d := fun w j => L (G j w)
  let r (n : ℕ) (w : FieldPair d) :=
    horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) f w - f w -
      Entropy.commOp hd 0 (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V w
  have hfm : Measurable f := L.continuous.measurable.comp (Lp.stronglyMeasurable g).measurable
  have hf : MemLp f 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp g)
  have hVm : Measurable V := measurable_pi_lambda fun j =>
    L.continuous.measurable.comp (Lp.stronglyMeasurable (G j)).measurable
  have hV (j) : MemLp (fun w => V w j) 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp (G j))
  have hm (n) : Measurable (r n) :=
    ((measurable_horizontalMollify _
      (Entropy.contDiff_unitMassScaledMollifier _).continuous.measurable hfm).sub hfm).sub
      (Entropy.measurable_commOp hd 0 (Entropy.contDiff_unitMassScaledMollifier _) hVm)
  have hr (n) : MemLp (r n) 2 (reducedLaw Q) :=
    ((Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q)
      (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top hfm hf).sub hf).sub
      (c17_unforced_generator_commutator_memLp hd Q (Entropy.scaleSeq_pos n) hVm hV)
  have he (n) : r n =ᵐ[reducedLaw Q] fun w =>
      s * horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (unforcedComplexResolvent Q i s hs g v)) w -
      envGenerator hd 0 (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (unforcedComplexResolvent Q i s hs g v))) w - L (g w) := by
    filter_upwards [c17_unforced_resolvent_mollified_graph_residual hd Q i s hs g hG L
      (Entropy.scaleSeq_pos n) (Entropy.scaleSeq_le_one n)] with w hw
    exact hw.symm
  refine ⟨r, hr, hm, he, ?_⟩
  apply c17_representative_L2_tendsto (reducedLaw Q) r _ hr he
  exact (c17_tendsto_unforced_resolvent_mollified_graph_residual hd Q i s hs g hG L).comp
    Entropy.tendsto_scaleSeq



end EinsteinFull
