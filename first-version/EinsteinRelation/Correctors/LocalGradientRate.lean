import EinsteinRelation.Correctors.LocalConditionedGradient

/-! # The inverse-radius error of the local gradient

Source: `paper/main.tex:968–977`. The conditional averaging error decays as
`R^(-d/2)` and the derivative-of-weight correction as `R⁻¹`. Their sum has
the claimed inverse-radius rate in every dimension at least two.
-/

open MeasureTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- The dimensional decay used at the end of Proposition 5.3, including the
weight-derivative error. Source: `paper/main.tex:968–977`. -/
theorem corrector_conditional_gradient_rate_le {d : ℕ} (hd : 2 ≤ d)
    {R A B : ℝ} (hR : 1 ≤ R) (hA : 0 ≤ A) :
    2 * A * R ^ (-(d : ℝ) / 2) + B * R⁻¹ ≤ (2 * A + B) * R⁻¹ := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hexp : -(d : ℝ) / 2 ≤ -1 := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hR hexp
  rw [Real.rpow_neg_one] at hpow
  have hterm : 2 * A * R ^ (-(d : ℝ) / 2) ≤ 2 * A * R⁻¹ :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  calc
    2 * A * R ^ (-(d : ℝ) / 2) + B * R⁻¹ ≤ 2 * A * R⁻¹ + B * R⁻¹ :=
      add_le_add hterm le_rfl
    _ = (2 * A + B) * R⁻¹ := by ring

/-- Add the actual weight-derivative correction to the conditional mean
gradient without replacing the source Euclidean norm.
Source: `paper/main.tex:968–977`. -/
theorem eLpNorm_corrected_local_gradient_rate_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d : ℕ} (hd : 2 ≤ d) {p R A B : ℝ}
    (hp : 1 ≤ p) (hR : 1 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {V H f : Ω → Vec d} (hVm : Measurable V) (hHm : Measurable H) (hfm : Measurable f)
    (hV : eLpNorm (fun ω => euclideanNorm (V ω - f ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (2 * (A * R ^ (-(d : ℝ) / 2))))
    (hH : eLpNorm (fun ω => euclideanNorm (H ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (B * R⁻¹)) :
    eLpNorm (fun ω => euclideanNorm (V ω + H ω - f ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal ((2 * A + B) * R⁻¹) := by
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hVJ : AEStronglyMeasurable (fun ω => J (V ω - f ω)) μ :=
    (J.continuous.measurable.comp (hVm.sub hfm)).aestronglyMeasurable
  have hHJ : AEStronglyMeasurable (fun ω => J (H ω)) μ :=
    (J.continuous.measurable.comp hHm).aestronglyMeasurable
  have hVb : eLpNorm (fun ω => J (V ω - f ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (2 * (A * R ^ (-(d : ℝ) / 2))) := by
    simpa only [TimeChange.euclideanNorm_eq_norm_toLp, eLpNorm_norm] using hV
  have hHb : eLpNorm (fun ω => J (H ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (B * R⁻¹) := by
    simpa only [TimeChange.euclideanNorm_eq_norm_toLp, eLpNorm_norm] using hH
  have heq : (fun ω => J (V ω + H ω - f ω)) =
      (fun ω => J (V ω - f ω)) + (fun ω => J (H ω)) := by
    funext ω
    simp only [map_add, map_sub, Pi.add_apply]
    abel
  simp_rw [TimeChange.euclideanNorm_eq_norm_toLp]
  rw [eLpNorm_norm]
  change eLpNorm (fun ω => J (V ω + H ω - f ω)) (ENNReal.ofReal p) μ ≤ _
  rw [heq]
  calc
    _ ≤ eLpNorm (fun ω => J (V ω - f ω)) (ENNReal.ofReal p) μ +
        eLpNorm (fun ω => J (H ω)) (ENNReal.ofReal p) μ :=
      eLpNorm_add_le hVJ hHJ (ENNReal.one_le_ofReal.mpr hp)
    _ ≤ ENNReal.ofReal (2 * (A * R ^ (-(d : ℝ) / 2))) +
        ENNReal.ofReal (B * R⁻¹) := add_le_add hVb hHb
    _ = ENNReal.ofReal (2 * A * R ^ (-(d : ℝ) / 2) + B * R⁻¹) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (corrector_conditional_gradient_rate_le hd hR hA)

/-- The complete gradient-error averaging step of Proposition 5.3, using
the conditional error of Lemma 5.2 and the separate derivative correction.
Source: `paper/main.tex:968–977`. All fields are literal coordinate fields,
and the version identity uses the source coefficient observations. -/
theorem local_center_conditioned_euclidean_corrected_gradient_rate {d : ℕ}
    (hd : 2 ≤ d) {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ]
    {R : ℝ} (hR : 1 ≤ R)
    (ν : Measure {y : Vec d // euclideanNorm y ≤ R}) [SigmaFinite ν]
    {p A B : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : {y : Vec d // euclideanNorm y ≤ R} → ℝ)
    (hwm : Measurable w) (hwi : Integrable w ν) (hw0 : ∀ y, 0 ≤ w y)
    (hw : (∫ y, w y ∂ν) = 1)
    (f : FieldPair d → Vec d) (hf : Integrable f μ) (hfm : Measurable f)
    (htail : eLpNorm (fun ω => euclideanNorm
      (f ω - μ[f | reducedCoefficientObservationSigma
        {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (A * R ^ (-(d : ℝ) / 2)))
    (u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Vec d)
    (hu : Measurable u)
    (hversion : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      (fun ω => u (y, ω)) =ᵐ[μ]
        μ[f | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}])
    (H : FieldPair d → Vec d) (hHm : Measurable H)
    (hH : eLpNorm (fun ω => euclideanNorm (H ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (B * R⁻¹)) :
    eLpNorm (fun ω => euclideanNorm
      ((∫ y, w y • u (y, ω) ∂ν) + H ω - f ω)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal ((2 * A + B) * R⁻¹) := by
  have havg := local_center_conditioned_euclidean_gradient_bound hR ν hp (by positivity)
    w hwm hwi hw0 hw f hf hfm htail u hu hversion
  have hVm : Measurable (fun ω => ∫ y, w y • u (y, ω) ∂ν) := by
    have hm : Measurable (fun z => w z.1 • u z) :=
      (hwm.comp measurable_fst).smul hu
    exact (hm.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
  exact eLpNorm_corrected_local_gradient_rate_le hd hp hR hA hB hVm hHm hfm havg.2.2 hH

end EinsteinRelation.Correctors
