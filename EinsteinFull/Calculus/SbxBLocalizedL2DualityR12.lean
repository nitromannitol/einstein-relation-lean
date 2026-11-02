import EinsteinFull.External.Source.GMPDirichletSpectralKernel
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open MeasureTheory
open EinsteinRelation
open EinsteinFull.External.Source.GMP

noncomputable section
namespace EinsteinFull

/-- Testing against the indicator of the function itself bounds its localized
weighted energy. The tests are supported almost everywhere in the given set. -/
theorem sbxB_localized_l2_duality {d : ℕ} (ρ : Vec d → ℝ) (R : ℝ)
    (V : Set (Vec d)) (hV : MeasurableSet V)
    (g : Lp ℝ 2 (dirichletVolume ρ R)) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
      (∀ᵐ x ∂(dirichletVolume ρ R), x ∉ V → f x = 0) →
      |inner ℝ g f| ≤ C * ‖f‖) :
    (∫ x in V, |g x| ^ 2 ∂(dirichletVolume ρ R)) ≤ C ^ 2 := by
  let μ := dirichletVolume ρ R
  let hp : MemLp (V.indicator (fun x => g x)) 2 μ := (Lp.memLp g).indicator hV
  let f : Lp ℝ 2 μ := hp.toLp _
  have hf : ∀ᵐ x ∂μ, f x = V.indicator (fun x => g x) x := hp.coeFn_toLp
  have hs : ∀ᵐ x ∂μ, x ∉ V → f x = 0 := by
    filter_upwards [hf] with x hx hnot
    rw [hx, Set.indicator_of_notMem hnot]
  have heq : (∫ x in V, |g x| ^ 2 ∂μ) = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_indicator hV]
    apply integral_congr_ae
    filter_upwards [hf] with x hx
    by_cases hxV : x ∈ V
    · simp only [Set.indicator_of_mem hxV, hx, Real.inner_apply, pow_two, abs_mul_abs_self]
    · simp only [Set.indicator_of_notMem hxV, hx, Real.inner_apply, mul_zero]
  have hpair : inner ℝ g f = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf] with x hx
    by_cases hxV : x ∈ V
    · simp only [hx, Set.indicator_of_mem hxV]
    · simp only [hx, Set.indicator_of_notMem hxV, Real.inner_apply, mul_zero]
  have hh := h f hs
  rw [hpair, abs_of_nonneg (sq_nonneg _)] at hh
  have hnorm : ‖f‖ ≤ C := by
    by_cases hz : ‖f‖ = 0
    · simpa [hz] using hC
    · have hp' : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  rw [heq]
  nlinarith [norm_nonneg f]

#print axioms sbxB_localized_l2_duality
end EinsteinFull
