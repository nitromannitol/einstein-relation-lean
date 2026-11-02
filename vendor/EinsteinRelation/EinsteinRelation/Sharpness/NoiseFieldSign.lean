import EinsteinRelation.Sharpness.NoiseField
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Sign of the literal smoothed noise field

Source paper/main.tex:1212–1216, internal actual nondegeneracy route: `h = ζ * tanh(K * W)`.
These are deterministic statements about one actual sample `W`. Negating the distribution
negates the field, and a pointwise sign of the inner mollified noise on the support of `ζ`
forces the sign of the whole field. Probability-level consumers must supply the local sign on a
positive-probability event. No Gaussian, stationarity, or uniform-sign conclusion is assumed here.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- The real hyperbolic tangent is continuous (local copy of the NoiseField helper). -/
private theorem continuous_tanh_signField : Continuous Real.tanh := by
  have heq : Real.tanh = fun t => Real.sinh t / Real.cosh t :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [heq]
  exact Real.continuous_sinh.div₀ Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')

/-- A strictly positive argument has strictly positive hyperbolic tangent. -/
private theorem tanh_pos_of_pos_signField {t : ℝ} (ht : 0 < t) : 0 < Real.tanh t := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr ht) (Real.cosh_pos t)

/-- Negating an actual distribution sample negates its outer-mollified value pointwise. -/
private theorem mollifiedNoise_neg_sample {d : ℕ} (W : NoiseSample d) (K : NoiseTest d)
    (x : Vec d) : mollifiedNoise (-W) K x = -mollifiedNoise W K x :=
  rfl

/-- Negating the sample reverses the literal two-stage field `ζ * tanh(K * W)`. -/
theorem smoothedNoiseField_neg {d : ℕ} (ζ K : NoiseTest d) (W : NoiseSample d) (x : Vec d) :
    smoothedNoiseField ζ K (-W) x = -smoothedNoiseField ζ K W x := by
  have hpt : ∀ y : Vec d, ζ y * Real.tanh (mollifiedNoise (-W) K (x-y)) =
      -(ζ y * Real.tanh (mollifiedNoise W K (x-y))) := by
    intro y
    rw [mollifiedNoise_neg_sample, Real.tanh_neg]
    ring
  simp only [smoothedNoiseField_apply]
  simp_rw [hpt]
  rw [integral_neg]

/-- If the inner mollified noise is strictly positive wherever `ζ` is nonzero, the literal field
is strictly positive at `x`: the integrand is nonnegative everywhere and nonzero at a point of
`ζ ≠ 0`. -/
theorem smoothedNoiseField_pos_of_local_pos {d : ℕ} (ζ K : NoiseTest d)
    (W : NoiseSample d) (x : Vec d) (hζ : ∀ y : Vec d, 0 ≤ ζ y) (hζne : ζ ≠ 0)
    (hpos : ∀ y : Vec d, ζ y ≠ 0 → 0 < mollifiedNoise W K (x-y)) :
    0 < smoothedNoiseField ζ K W x := by
  have hex : ∃ y0 : Vec d, ζ y0 ≠ 0 := by
    by_contra h
    apply hζne
    ext y
    exact Classical.not_not.mp (not_exists.mp h y)
  obtain ⟨y0, hy0⟩ := hex
  have hcont : Continuous (fun y : Vec d => ζ y * Real.tanh (mollifiedNoise W K (x-y))) :=
    ζ.contDiff.continuous.mul (continuous_tanh_signField.comp
      ((continuous_mollifiedNoise W K).comp (continuous_const.sub continuous_id)))
  have hsupp : HasCompactSupport (fun y : Vec d => ζ y * Real.tanh (mollifiedNoise W K (x-y))) :=
    ζ.hasCompactSupport.mul_right
  have hnonneg : ∀ y : Vec d, 0 ≤ ζ y * Real.tanh (mollifiedNoise W K (x-y)) := by
    intro y
    by_cases hy : ζ y = 0
    · simp only [hy, zero_mul, le_refl]
    · exact mul_nonneg (hζ y) (tanh_pos_of_pos_signField (hpos y hy)).le
  have hnonzero : ζ y0 * Real.tanh (mollifiedNoise W K (x-y0)) ≠ 0 :=
    (mul_pos (lt_of_le_of_ne (hζ y0) (Ne.symm hy0))
      (tanh_pos_of_pos_signField (hpos y0 hy0))).ne'
  change 0 < ∫ y : Vec d, ζ y * Real.tanh (mollifiedNoise W K (x-y))
  exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp (fun y => hnonneg y) hnonzero

/-- If the inner mollified noise is strictly negative wherever `ζ` is nonzero, the literal field
is strictly negative at `x`. This follows from the positive case applied to `-W`, using the
sign reversal `smoothedNoiseField_neg`. -/
theorem smoothedNoiseField_neg_of_local_neg {d : ℕ} (ζ K : NoiseTest d)
    (W : NoiseSample d) (x : Vec d) (hζ : ∀ y : Vec d, 0 ≤ ζ y) (hζne : ζ ≠ 0)
    (hneg : ∀ y : Vec d, ζ y ≠ 0 → mollifiedNoise W K (x-y) < 0) :
    smoothedNoiseField ζ K W x < 0 := by
  have hposNeg : 0 < smoothedNoiseField ζ K (-W) x :=
    smoothedNoiseField_pos_of_local_pos ζ K (-W) x hζ hζne (fun y hy => by
      rw [mollifiedNoise_neg_sample]
      exact neg_pos.mpr (hneg y hy))
  rw [smoothedNoiseField_neg] at hposNeg
  exact neg_pos.mp hposNeg

end EinsteinRelation.Sharpness
