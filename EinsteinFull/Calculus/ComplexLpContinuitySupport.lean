import EinsteinFull.Calculus.ComplexLowExponentExtensionSupport
import Mathlib.Topology.EMetricSpace.Lipschitz

/-! Strong continuity of the actual dense lower-Lp extensions. -/
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The actual probability-law inclusion has norm at most one. -/
theorem norm_complexL2ToLp_le (hp2 : p ≤ 2) (f : Lp ℂ 2 μ) :
    ‖complexL2ToLp μ hp2 f‖ ≤ ‖f‖ := by
  have h := ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := f) hp2)
  simpa only [Lp.norm_def, complexL2ToLp_apply] using h

/-- The literal L2 inclusion is continuous into the lower-Lp norm. -/
def complexL2ToLpCLM (hp2 : p ≤ 2) : Lp ℂ 2 μ →L[ℂ] Lp ℂ p μ :=
  (complexL2ToLp μ hp2).mkContinuous 1 (fun f => by
    simpa only [one_mul] using norm_complexL2ToLp_le μ hp2 f)

private theorem norm_exp_damped_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : F →L[ℂ] F) (a : ℝ) (hA : ‖A‖ ≤ Real.exp a) :
    ‖(Real.exp (-a) : ℂ) • A‖ ≤ 1 := by
  calc
    _ = Real.exp (-a) * ‖A‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-a) * Real.exp a := mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

private theorem continuous_damped_extension_on_L2
    (hp2 : p ≤ 2) (hp : p ≠ ⊤)
    (A : ℝ≥0 → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : ℝ)
    (hcont : ∀ f, Continuous (fun t => A t f))
    (hA : ∀ t f, eLpNorm (A t f) p μ ≤
      eLpNorm f p μ * ENNReal.ofReal (Real.exp (c * (t : ℝ)))) (f : Lp ℂ 2 μ) :
    Continuous (fun t : ℝ≥0 => (Real.exp (-(c * (t : ℝ))) : ℂ) •
      complexL2OperatorLpExtension μ hp2 (A t) (complexL2ToLp μ hp2 f)) := by
  have he (t : ℝ≥0) := complexL2OperatorLpExtension_apply μ hp2 hp (A t)
    (Real.exp_pos _).le (hA t) f
  simp_rw [he]
  exact (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp ((continuous_const.mul NNReal.continuous_coe).neg))).smul
      ((complexL2ToLpCLM μ hp2).continuous.comp (hcont f))

private theorem continuous_undamped_family {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (B : ℝ≥0 → F →L[ℂ] F) (c : ℝ)
    (hB : Continuous (fun ft : F × ℝ≥0 => B ft.2 ft.1)) :
    Continuous (fun tf : ℝ≥0 × F =>
      (Real.exp (c * (tf.1 : ℝ)) : ℂ) • B tf.1 tf.2) := by
  have hs : Continuous (fun tf : ℝ≥0 × F => (Real.exp (c * (tf.1 : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul
        (NNReal.continuous_coe.comp continuous_fst)))
  exact hs.smul (hB.comp continuous_swap)

/-- Joint time/data continuity follows from actual L2 continuity and the
proved exponential bound, using density and globally contractive damping. -/
theorem continuous_complexL2OperatorLpExtension_of_exp_bound
    (hp2 : p ≤ 2) (hp : p ≠ ⊤)
    (A : ℝ≥0 → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : ℝ)
    (hcont : ∀ f, Continuous (fun t => A t f))
    (hA : ∀ t f, eLpNorm (A t f) p μ ≤
      eLpNorm f p μ * ENNReal.ofReal (Real.exp (c * (t : ℝ)))) :
    Continuous (fun tf : ℝ≥0 × Lp ℂ p μ =>
      complexL2OperatorLpExtension μ hp2 (A tf.1) tf.2) := by
  let E (t : ℝ≥0) : Lp ℂ p μ →L[ℂ] Lp ℂ p μ := complexL2OperatorLpExtension μ hp2 (A t)
  let B (t : ℝ≥0) : Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
    (Real.exp (-(c * (t : ℝ))) : ℂ) • E t
  have hnorm (t : ℝ≥0) : ‖B t‖ ≤ 1 := norm_exp_damped_le (E t) _
    (norm_complexL2OperatorLpExtension_le μ hp2 hp (A t) (Real.exp_pos _).le (hA t))
  have hB : Continuous (fun ft : Lp ℂ p μ × ℝ≥0 => B ft.2 ft.1) := by
    apply continuous_prod_of_dense_continuous_lipschitzWith _ 1
      (denseRange_complexL2ToLp μ hp2 hp)
    · rintro _ ⟨f, rfl⟩
      exact continuous_damped_extension_on_L2 μ hp2 hp A c hcont hA f
    · intro t
      exact ContinuousLinearMap.lipschitzWith_of_opNorm_le (f := B t) (K := 1) (hnorm t)
  have hc := continuous_undamped_family B c hB
  convert hc using 1
  funext tf
  simp only [B, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.ofReal_mul,
    ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one, one_smul, E]

private theorem continuous_family_apply {F : Type*} [TopologicalSpace F]
    (E : ℝ≥0 → F → F) (hE : Continuous (fun tf : ℝ≥0 × F => E tf.1 tf.2))
    (f : F) : Continuous (fun t => E t f) :=
  hE.comp (continuous_id.prodMk continuous_const)

/-- The genuine lower-Lp extension preserves the complete C0 semigroup laws. -/
theorem complexL2OperatorLpExtension_c0
    (hp2 : p ≤ 2) (hp : p ≠ ⊤)
    (A : ℝ≥0 → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : ℝ)
    (hzero : A 0 = ContinuousLinearMap.id ℂ _)
    (hadd : ∀ s t, A (s+t) = (A s).comp (A t))
    (hcont : ∀ f, Continuous (fun t => A t f))
    (hA : ∀ t f, eLpNorm (A t f) p μ ≤
      eLpNorm f p μ * ENNReal.ofReal (Real.exp (c * (t : ℝ)))) :
    let E := fun t => complexL2OperatorLpExtension μ hp2 (A t)
    E 0 = ContinuousLinearMap.id ℂ _ ∧
    (∀ s t, E (s+t) = (E s).comp (E t)) ∧
    (∀ f, Continuous (fun t => E t f)) := by
  refine ⟨?_, ?_, ?_⟩
  · change complexL2OperatorLpExtension μ hp2 (A 0) = _
    rw [hzero, complexL2OperatorLpExtension_id μ hp2 hp]
  · intro s t
    change complexL2OperatorLpExtension μ hp2 (A (s+t)) = _
    rw [hadd, complexL2OperatorLpExtension_comp μ hp2 hp (A s) (A t)
      (Real.exp_pos _).le (Real.exp_pos _).le (hA s) (hA t)]
  · intro f
    exact continuous_family_apply _
      (continuous_complexL2OperatorLpExtension_of_exp_bound μ hp2 hp A c hcont hA) f

/-- Every actual forward family acts as a C0 semigroup on genuine Lp, 1<p<=2. -/
theorem IsComplexEnvironmentSemigroup.LpExtension_c0_below_two
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal hp.le)⟩
    let E := fun t => complexL2OperatorLpExtension (p := ENNReal.ofReal p) (reducedLaw Q)
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) (P t)
    E 0 = ContinuousLinearMap.id ℂ _ ∧
    (∀ s t, E (s+t) = (E s).comp (E t)) ∧
    (∀ f, Continuous (fun t => E t f)) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hp.le)⟩
  exact complexL2OperatorLpExtension_c0 (reducedLaw Q) _ ENNReal.ofReal_ne_top P
    ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
      (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (Real.conjExponent p - 1)) ^ 2)
    hP.1 hP.2.1 hP.2.2.1 (fun t f => hP.eLpNorm_growth_below_two hp hp2 f t)

/-- The actual bilinear transpose likewise acts as a C0 semigroup on genuine lower Lp. -/
theorem IsComplexTransposeSemigroup.LpExtension_c0_below_two
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal hp.le)⟩
    let E := fun t => complexL2OperatorLpExtension (p := ENNReal.ofReal p) (reducedLaw Q)
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) (T t)
    E 0 = ContinuousLinearMap.id ℂ _ ∧
    (∀ s t, E (s+t) = (E s).comp (E t)) ∧
    (∀ f, Continuous (fun t => E t f)) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hp.le)⟩
  exact complexL2OperatorLpExtension_c0 (reducedLaw Q) _ ENNReal.ofReal_ne_top T
    ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) * (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2)
    (hT.zero hP) (hT.add hP) (hT.continuous_apply hP)
    (fun t f => hT.eLpNorm_growth_below_two hP hp hp2 f t)

end EinsteinFull
