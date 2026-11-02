import EinsteinFull.Calculus.S3LocalAvSupport
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0400_2
import EinsteinFull.Work.W7.ClockFiniteRangeSupport
import EinsteinFull.Calculus.ComplexTranslationSupport
import EinsteinFull.Calculus.ComplexLpSupport
import EinsteinRelation.Environment.LocalIntegralMeasurability

/-!
# Gaussian averages of local centered fields on the reduced joint law

A centered class `f ∈ L²(reducedLaw Q)` that is local in a Euclidean ball of radius `R` has
translates `T_x f`, `T_y f` that are orthogonal as soon as `|x - y| ≥ 2R + |r₀| + 1`, by the joint
finite range of `reducedLaw Q`. A Schur test with the heat kernel then gives
`ρ^d ‖Φ_ρ * f‖² ≤ (2 R_c)^d ‖f‖²` for every `ρ > 0`.
-/

open MeasureTheory

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinFull.S3LocalAv

variable {d : ℕ} {Λ r₀ : ℝ}

/-- `f` has an a.e.-representative measurable for the joint restriction to the Euclidean ball of
radius `R`. -/
def IsLocalRep (Q : EnvironmentLaw d Λ r₀) (R : ℝ) (f : Lp ℂ 2 (reducedLaw Q)) : Prop :=
  ∃ g : FieldPair d → ℂ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < R}] g ∧
      g =ᵐ[reducedLaw Q] (f : FieldPair d → ℂ)

/-- Translates of a centered local class by well-separated vectors are orthogonal. -/
theorem inner_translate_eq_zero (Q : EnvironmentLaw d Λ r₀) {R Rc : ℝ}
    (hRc : 2 * R + (|r₀| + 1) ≤ Rc)
    (f : Lp ℂ 2 (reducedLaw Q)) (hf0 : ∫ ω, f ω ∂reducedLaw Q = 0) (hloc : IsLocalRep Q R f)
    (x y : Vec d) (hxy : Rc ≤ euclideanNorm (x - y)) :
    inner ℂ (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y f) = 0 := by
  letI := reducedLaw_probability Q
  obtain ⟨g, hg, hgf⟩ := hloc
  have hst := reducedLaw_stationary Q
  have hmp : ∀ z : Vec d, MeasurePreserving (translate z) (reducedLaw Q) (reducedLaw Q) :=
    fun z => measurePreserving_translate (reducedLaw Q) hst z
  have hWm : ∀ z : Vec d, MeasurableSet {p : Vec d | euclideanNorm (p - z) < R} :=
    fun z => measurableSet_euclideanBall z R
  have hgm : ∀ z : Vec d, Measurable[localSigma {p : Vec d | euclideanNorm (p - z) < R}]
      (fun ω => g (translate z ω)) := by
    intro z
    refine hg.comp (measurable_translate_localSigma z ?_)
    intro u hu
    show euclideanNorm (z + u - z) < R
    rw [add_sub_cancel_left]
    exact hu
  have hTz : ∀ z : Vec d, complexTranslation (reducedLaw Q) hst z f =ᵐ[reducedLaw Q]
      fun ω => g (translate z ω) := by
    intro z
    have h1 := coeFn_complexTranslation (reducedLaw Q) hst z f
    have h2 : (fun ω => g (translate z ω)) =ᵐ[reducedLaw Q]
        fun ω => (f : FieldPair d → ℂ) (translate z ω) :=
      (hmp z).quasiMeasurePreserving.ae_eq_comp hgf
    exact h1.trans h2.symm
  have hmeanB : ∫ ω, g (translate y ω) ∂reducedLaw Q = 0 := by
    have h1 : ∫ ω, g (translate y ω) ∂reducedLaw Q =
        ∫ ω, (f : FieldPair d → ℂ) (translate y ω) ∂reducedLaw Q :=
      integral_congr_ae ((hmp y).quasiMeasurePreserving.ae_eq_comp hgf)
    have h2 := integral_map (μ := reducedLaw Q) (hmp y).measurable.aemeasurable
      (f := (f : FieldPair d → ℂ)) (by rw [hst y]; exact Lp.aestronglyMeasurable f)
    rw [hst y] at h2
    rw [h1, ← h2, hf0]
  have hinner : inner ℂ (complexTranslation (reducedLaw Q) hst x f)
      (complexTranslation (reducedLaw Q) hst y f) =
        ∫ ω, starRingEnd ℂ (g (translate x ω)) * g (translate y ω) ∂reducedLaw Q := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hTz x, hTz y] with ω hx hy
    simp only [hx, hy, RCLike.inner_apply]
    try ring
  have hsep : ∀ p ∈ {p : Vec d | euclideanNorm (p - x) < R},
      ∀ q ∈ {p : Vec d | euclideanNorm (p - y) < R}, |r₀| + 1 ≤ euclideanNorm (p - q) := by
    intro p hp q hq
    have hp' : euclideanNorm (x - p) < R := by
      rw [euclideanNorm_sub_comm']
      exact hp
    have hq' : euclideanNorm (q - y) < R := hq
    have e1 : x - y = ((x - p) + (p - q)) + (q - y) := by abel
    have h1 := TimeChange.euclideanNorm_add_le ((x - p) + (p - q)) (q - y)
    have h2 := TimeChange.euclideanNorm_add_le (x - p) (p - q)
    have h3 : Rc ≤ euclideanNorm (((x - p) + (p - q)) + (q - y)) := by rw [← e1]; exact hxy
    linarith
  have hi := reducedLaw_hasFiniteRange Q _ _ (hWm x) (hWm y)
    ⟨|r₀| + 1, by linarith [le_abs_self r₀], hsep⟩
  have hAm : Measurable[localSigma {p : Vec d | euclideanNorm (p - x) < R}]
      (fun ω => starRingEnd ℂ (g (translate x ω))) :=
    Complex.continuous_conj.measurable.comp (hgm x)
  have hind : ProbabilityTheory.IndepFun (fun ω => starRingEnd ℂ (g (translate x ω)))
      (fun ω => g (translate y ω)) (reducedLaw Q) :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hi hAm.comap_le) (hgm y).comap_le
  have hA_ae : AEStronglyMeasurable (fun ω => g (translate x ω)) (reducedLaw Q) :=
    (Lp.aestronglyMeasurable (complexTranslation (reducedLaw Q) hst x f)).congr (hTz x)
  have hB_ae : AEStronglyMeasurable (fun ω => g (translate y ω)) (reducedLaw Q) :=
    (Lp.aestronglyMeasurable (complexTranslation (reducedLaw Q) hst y f)).congr (hTz y)
  have hAc : AEStronglyMeasurable (fun ω => starRingEnd ℂ (g (translate x ω))) (reducedLaw Q) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hA_ae
  rw [hinner, hind.integral_fun_mul_eq_mul_integral hAc hB_ae, hmeanB, mul_zero]

/-- The Schur test for the Gaussian average of a centered local class. -/
theorem gaussianAverage_local_sq_le (Q : EnvironmentLaw d Λ r₀) {R Rc : ℝ} (hR : 0 ≤ R)
    (hRc : 2 * R + (|r₀| + 1) ≤ Rc)
    (f : Lp ℂ 2 (reducedLaw Q)) (hf0 : ∫ ω, f ω ∂reducedLaw Q = 0) (hloc : IsLocalRep Q R f)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ d * ‖fluxGaussianAverageCLM Q (ρ ^ 2) (by positivity) f‖ ^ 2 ≤
      (2 * Rc) ^ d * ‖f‖ ^ 2 := by
  letI := reducedLaw_probability Q
  have hst := reducedLaw_stationary Q
  have hs : 0 < ρ ^ 2 := by positivity
  have hRc0 : 0 ≤ Rc := by
    have h1 : 0 ≤ |r₀| := abs_nonneg r₀
    linarith
  have hint := integrable_isotropicGaussian_integrand Q (ρ ^ 2) hs f
  have hΦint := Correctors.integrable_euclideanHeatKernel (d := d) hs
  have hΦ0 : ∀ y : Vec d, 0 ≤ Correctors.euclideanHeatKernel (ρ ^ 2) y :=
    fun y => Correctors.euclideanHeatKernel_nonneg hs.le y
  have hg : fluxGaussianAverageCLM Q (ρ ^ 2) hs f = ∫ x : Vec d,
      (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
        complexTranslation (reducedLaw Q) hst x f := rfl
  -- the Schur bound for each fixed translate
  have hA : ∀ x : Vec d, ‖inner ℂ (complexTranslation (reducedLaw Q) hst x f)
      (fluxGaussianAverageCLM Q (ρ ^ 2) hs f)‖ ≤ (ρ ^ d)⁻¹ * ‖f‖ ^ 2 * (2 * Rc) ^ d := by
    intro x
    have h1 : inner ℂ (complexTranslation (reducedLaw Q) hst x f)
        (fluxGaussianAverageCLM Q (ρ ^ 2) hs f) =
          ∫ y : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) y : ℂ) *
            inner ℂ (complexTranslation (reducedLaw Q) hst x f)
              (complexTranslation (reducedLaw Q) hst y f) := by
      have h := ContinuousLinearMap.integral_comp_comm
        (innerSL ℂ (complexTranslation (reducedLaw Q) hst x f)) hint
      simp only [innerSL_apply_apply, inner_smul_right] at h
      rw [hg]
      exact h.symm
    have hbd : ∀ y : Vec d, ‖(Correctors.euclideanHeatKernel (ρ ^ 2) y : ℂ) *
        inner ℂ (complexTranslation (reducedLaw Q) hst x f)
          (complexTranslation (reducedLaw Q) hst y f)‖ ≤
        {z : Vec d | euclideanNorm (z - x) < Rc}.indicator
          (fun _ => (ρ ^ d)⁻¹ * ‖f‖ ^ 2) y := by
      intro y
      by_cases hy : y ∈ {z : Vec d | euclideanNorm (z - x) < Rc}
      · rw [Set.indicator_of_mem hy, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (hΦ0 y)]
        apply mul_le_mul (euclideanHeatKernel_le_pow_inv hρ y) _ (norm_nonneg _) (by positivity)
        calc ‖inner ℂ (complexTranslation (reducedLaw Q) hst x f)
              (complexTranslation (reducedLaw Q) hst y f)‖
            ≤ ‖complexTranslation (reducedLaw Q) hst x f‖ *
                ‖complexTranslation (reducedLaw Q) hst y f‖ := norm_inner_le_norm _ _
          _ = ‖f‖ ^ 2 := by
              rw [norm_complexTranslation, norm_complexTranslation]
              ring
      · rw [Set.indicator_of_notMem hy]
        have hy' : Rc ≤ euclideanNorm (x - y) := by
          rw [euclideanNorm_sub_comm']
          exact not_lt.mp hy
        rw [inner_translate_eq_zero Q hRc f hf0 hloc x y hy', mul_zero, norm_zero]
    have hI : Integrable (fun y : Vec d => {z : Vec d | euclideanNorm (z - x) < Rc}.indicator
        (fun _ => (ρ ^ d)⁻¹ * ‖f‖ ^ 2) y) :=
      (integrableOn_const (measure_euclideanBall_ne_top x hRc0)).integrable_indicator
        (measurableSet_euclideanBall x Rc)
    rw [h1]
    calc ‖∫ y : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) y : ℂ) *
            inner ℂ (complexTranslation (reducedLaw Q) hst x f)
              (complexTranslation (reducedLaw Q) hst y f)‖
        ≤ ∫ y : Vec d, {z : Vec d | euclideanNorm (z - x) < Rc}.indicator
            (fun _ => (ρ ^ d)⁻¹ * ‖f‖ ^ 2) y :=
          norm_integral_le_of_norm_le hI (Filter.Eventually.of_forall hbd)
      _ ≤ (ρ ^ d)⁻¹ * ‖f‖ ^ 2 * (2 * Rc) ^ d :=
          integral_indicator_euclideanBall_le x hRc0 _ (by positivity)
  -- integrate the Schur bound against the kernel
  have hB : ‖fluxGaussianAverageCLM Q (ρ ^ 2) hs f‖ ^ 2 ≤
      (ρ ^ d)⁻¹ * ‖f‖ ^ 2 * (2 * Rc) ^ d := by
    set g := fluxGaussianAverageCLM Q (ρ ^ 2) hs f with hgdef
    have h1 : ‖g‖ ^ 2 = ‖inner ℂ g g‖ := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    have h2 : inner ℂ g g = ∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) *
        inner ℂ g (complexTranslation (reducedLaw Q) hst x f) := by
      have h := ContinuousLinearMap.integral_comp_comm (innerSL ℂ g) hint
      simp only [innerSL_apply_apply, inner_smul_right] at h
      conv_lhs => rw [hgdef]
      rw [hg]
      exact h.symm
    rw [h1, h2]
    calc ‖∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) *
            inner ℂ g (complexTranslation (reducedLaw Q) hst x f)‖
        ≤ ∫ x : Vec d, Correctors.euclideanHeatKernel (ρ ^ 2) x *
            ((ρ ^ d)⁻¹ * ‖f‖ ^ 2 * (2 * Rc) ^ d) := by
          refine norm_integral_le_of_norm_le (hΦint.mul_const _)
            (Filter.Eventually.of_forall fun x => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hΦ0 x), norm_inner_symm]
          exact mul_le_mul_of_nonneg_left (hA x) (hΦ0 x)
      _ = (ρ ^ d)⁻¹ * ‖f‖ ^ 2 * (2 * Rc) ^ d := by
          rw [integral_mul_const, Correctors.integral_euclideanHeatKernel hs, one_mul]
  have hρd : ρ ^ d ≠ 0 := by positivity
  calc ρ ^ d * ‖fluxGaussianAverageCLM Q (ρ ^ 2) hs f‖ ^ 2
      ≤ ρ ^ d * ((ρ ^ d)⁻¹ * ‖f‖ ^ 2 * (2 * Rc) ^ d) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (2 * Rc) ^ d * ‖f‖ ^ 2 := by
        field_simp

/-- Coordinatewise Gaussian average of a vector of classes at heat-kernel variance `s`. -/
def avgV (Q : EnvironmentLaw d Λ r₀) (s : ℝ) (hs : 0 < s)
    (F : Fin d → Lp ℂ 2 (reducedLaw Q)) : Fin d → Lp ℂ 2 (reducedLaw Q) :=
  fun j => fluxGaussianAverageCLM Q s hs (F j)

/-- The vector Gaussian average of a centered local vector field, at spatial scale `ρ`. -/
theorem avgV_vnorm_le (Q : EnvironmentLaw d Λ r₀) {R Rc : ℝ} (hR : 0 ≤ R)
    (hRc : 2 * R + (|r₀| + 1) ≤ Rc)
    (F : Fin d → Lp ℂ 2 (reducedLaw Q)) (hF0 : ∀ j, ∫ ω, F j ω ∂reducedLaw Q = 0)
    (hFloc : ∀ j, IsLocalRep Q R (F j)) {ρ : ℝ} (hρ : 0 < ρ) :
    Real.sqrt (ρ ^ d) * vnorm (avgV Q (ρ ^ 2) (by positivity) F) ≤
      Real.sqrt ((2 * Rc) ^ d) * vnorm F := by
  have hρd : 0 < Real.sqrt (ρ ^ d) := Real.sqrt_pos.mpr (by positivity)
  have hcoord : ∀ j, ‖avgV Q (ρ ^ 2) (by positivity) F j‖ ≤
      (Real.sqrt ((2 * Rc) ^ d) / Real.sqrt (ρ ^ d)) * ‖F j‖ := by
    intro j
    have h := gaussianAverage_local_sq_le Q hR hRc (F j) (hF0 j) (hFloc j) hρ
    rw [div_mul_eq_mul_div, le_div_iff₀ hρd, mul_comm]
    calc Real.sqrt (ρ ^ d) * ‖avgV Q (ρ ^ 2) (by positivity) F j‖
        = Real.sqrt (ρ ^ d * ‖avgV Q (ρ ^ 2) (by positivity) F j‖ ^ 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt ((2 * Rc) ^ d * ‖F j‖ ^ 2) := Real.sqrt_le_sqrt h
      _ = Real.sqrt ((2 * Rc) ^ d) * ‖F j‖ := by
          rw [Real.sqrt_mul (pow_nonneg (by linarith [abs_nonneg r₀]) d),
            Real.sqrt_sq (norm_nonneg _)]
  have hv := vnorm_le_mul (div_nonneg (Real.sqrt_nonneg _) hρd.le) hcoord
  calc Real.sqrt (ρ ^ d) * vnorm (avgV Q (ρ ^ 2) (by positivity) F)
      ≤ Real.sqrt (ρ ^ d) * ((Real.sqrt ((2 * Rc) ^ d) / Real.sqrt (ρ ^ d)) * vnorm F) :=
        mul_le_mul_of_nonneg_left hv hρd.le
    _ = Real.sqrt ((2 * Rc) ^ d) * vnorm F := by
        field_simp

end EinsteinFull.Blueprint
