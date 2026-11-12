import EinsteinRelation.Correctors.AKMHeatKernelBounds

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- On a bounded positive cylinder the scalar kernel has a Gaussian
 envelope in its initial point. Source: AKM E.1 (E.7);
`paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_local_gaussian_envelope {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hR : 0 < R) :
    ∃ D κ : ℝ, 0 ≤ D ∧ 0 < κ ∧ ∀ (t : ℝ), t ∈ Set.Ioo a b →
      ∀ x ∈ originBall d R, ∀ y : Vec d,
        |P t x y| ≤ D * Real.exp (-κ * euclideanSq y) := by
  let α := K⁻¹ / 2
  have hα : 0 < α := half_pos (inv_pos.mpr hK)
  have hbound := hP.2.2.2.2.2.2.2.1 α hα (half_lt_self (inv_pos.mpr hK))
  have hC : 0 ≤ C α := by
    have hh := (hbound 1 zero_lt_one 0 0).1
    simpa [euclideanSq,dot] using (abs_nonneg (P 1 0 0)).trans hh
  have hsq (v : Vec d) : 0 ≤ euclideanSq v := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hb : 0 < b := ha.trans hab
  let κ := α/(8*b)
  let M := α*R^2/(4*a)
  refine ⟨C α*a^(-(d : ℝ)/2)*Real.exp M,κ,by positivity,by dsimp [κ]; positivity,?_⟩
  intro t ht x hx y
  have ht0 : 0 < t := ha.trans ht.1
  have hxy : euclideanSq y ≤ 2*euclideanSq (x-y)+2*euclideanSq x := by
    unfold euclideanSq dot
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (2*x j-y j)]
  have hx2 : euclideanSq x ≤ R^2 := by
    have hn := (show euclideanNorm x < R from hx)
    have hn0 : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
    have hs : euclideanNorm x^2 = euclideanSq x :=
      Real.sq_sqrt (hsq x)
    nlinarith
  have hdivx : α*R^2/(4*t) ≤ α*R^2/(4*a) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (mul_nonneg hα.le (sq_nonneg R)) (sub_nonneg.mpr ht.1.le)]
  have hdivy : α*euclideanSq y/(8*b) ≤ α*euclideanSq y/(8*t) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (mul_nonneg hα.le (hsq y))
      (sub_nonneg.mpr ht.2.le)]
  have he : -α*euclideanSq (x-y)/(4*t) ≤ M + -κ*euclideanSq y := by
    have hlocal : -α*euclideanSq (x-y)/(4*t) ≤
        α*R^2/(4*t)-α*euclideanSq y/(8*t) := by
      have hh : -α*euclideanSq (x-y)*2 ≤ α*R^2*2-α*euclideanSq y := by
        nlinarith [mul_le_mul_of_nonneg_left hxy hα.le]
      convert (div_le_div_of_nonneg_right hh (by positivity : 0 ≤ 8*t)) using 1 <;> field_simp <;> ring
    dsimp only [M,κ]
    have heq : -(α/(8*b))*euclideanSq y = -(α*euclideanSq y/(8*b)) := by ring
    rw [heq]
    linarith
  have hp : t^(-(d : ℝ)/2) ≤ a^(-(d : ℝ)/2) :=
    Real.rpow_le_rpow_of_nonpos ha ht.1.le (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  calc
    _ ≤ C α*t^(-(d : ℝ)/2)*Real.exp (-α*euclideanSq (x-y)/(4*t)) := (hbound t ht0 x y).1
    _ ≤ C α*a^(-(d : ℝ)/2)*Real.exp (M + -κ*euclideanSq y) := by
      gcongr
    _ = _ := by rw [Real.exp_add]; ring

end EinsteinRelation.Correctors
