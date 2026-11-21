import Mathlib.MeasureTheory.Function.L2Space

/-! # Cauchy–Schwarz for real integrals

The square of an `L²` pairing is bounded by the product of the two second moments.
-/

open MeasureTheory

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The square of an integral pairing is at most the product of the second moments. -/
theorem integral_mul_sq_le (f g : Ω → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (∫ ω, f ω * g ω ∂P) ^ 2 ≤ (∫ ω, f ω ^ 2 ∂P) * ∫ ω, g ω ^ 2 ∂P := by
  let F : Lp ℝ 2 P := hf.toLp f
  let G : Lp ℝ 2 P := hg.toLp g
  have hfg : inner ℝ F G = ∫ ω, f ω * g ω ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with ω hωf hωg
    change inner ℝ (F ω) (G ω) = _
    rw [hωf, hωg]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm]
  have hff : inner ℝ F F = ∫ ω, f ω ^ 2 ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hf] with ω hω
    change inner ℝ (F ω) (F ω) = _
    rw [hω]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]
  have hgg : inner ℝ G G = ∫ ω, g ω ^ 2 ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hg] with ω hω
    change inner ℝ (G ω) (G ω) = _
    rw [hω]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]
  have h := real_inner_mul_inner_self_le F G
  rw [hfg, hff, hgg] at h
  nlinarith

end EinsteinFull.External.DFGW
