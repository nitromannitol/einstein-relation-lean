import EinsteinRelation.Correctors.AKMHeatKernelBounds
import EinsteinRelation.Correctors.SemigroupPrescribedGradient

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- On any translated bounded positive cylinder the scalar kernel has a
Gaussian envelope in the displacement from the cylinder center. Source: AKM E.1 (E.7);
`paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_translated_gaussian_envelope {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hR : 0 < R) :
    ∃ D κ : ℝ, 0 ≤ D ∧ 0 < κ ∧ ∀ (t : ℝ), t ∈ Set.Ioo a b →
      ∀ x ∈ originBall d R, ∀ v y : Vec d,
        |P t (v+x) y| ≤ D * Real.exp (-κ * euclideanSq (y-v)) := by
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
  intro t ht x hx v y
  have ht0 : 0 < t := ha.trans ht.1
  have hxy : euclideanSq (y-v) ≤ 2*euclideanSq (v+x-y)+2*euclideanSq x := by
    unfold euclideanSq dot
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    simp only [Pi.sub_apply,Pi.add_apply]
    nlinarith [sq_nonneg (2*x j-(y j-v j))]
  have hx2 : euclideanSq x ≤ R^2 := by
    have hn := (show euclideanNorm x < R from hx)
    have hn0 : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
    have hs : euclideanNorm x^2 = euclideanSq x :=
      Real.sq_sqrt (hsq x)
    nlinarith
  have hdivx : α*R^2/(4*t) ≤ α*R^2/(4*a) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (mul_nonneg hα.le (sq_nonneg R)) (sub_nonneg.mpr ht.1.le)]
  have hdivy : α*euclideanSq (y-v)/(8*b) ≤ α*euclideanSq (y-v)/(8*t) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (mul_nonneg hα.le (hsq (y-v)))
      (sub_nonneg.mpr ht.2.le)]
  have he : -α*euclideanSq (v+x-y)/(4*t) ≤ M + -κ*euclideanSq (y-v) := by
    have hlocal : -α*euclideanSq (v+x-y)/(4*t) ≤
        α*R^2/(4*t)-α*euclideanSq (y-v)/(8*t) := by
      have hh : -α*euclideanSq (v+x-y)*2 ≤ α*R^2*2-α*euclideanSq (y-v) := by
        nlinarith [mul_le_mul_of_nonneg_left hxy hα.le]
      convert (div_le_div_of_nonneg_right hh (by positivity : 0 ≤ 8*t)) using 1 <;> field_simp <;> ring
    dsimp only [M,κ]
    have heq : -(α/(8*b))*euclideanSq (y-v) = -(α*euclideanSq (y-v)/(8*b)) := by ring
    rw [heq]
    linarith
  have hp : t^(-(d : ℝ)/2) ≤ a^(-(d : ℝ)/2) :=
    Real.rpow_le_rpow_of_nonpos ha ht.1.le (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  calc
    _ ≤ C α*t^(-(d : ℝ)/2)*Real.exp (-α*euclideanSq (v+x-y)/(4*t)) := (hbound t ht0 (v+x) y).1
    _ ≤ C α*a^(-(d : ℝ)/2)*Real.exp (M + -κ*euclideanSq (y-v)) := by
      gcongr
    _ = _ := by rw [Real.exp_add]; ring

/-- Local scalar energies have a Gaussian bound in the displacement of
any cylinder center from the initial point. Source: AKM E.1 (E.7);
`paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_translated_scalar_gaussian_energy {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hR : 0 < R) :
    ∃ D κ : ℝ, 0 ≤ D ∧ 0 < κ ∧ ∀ v y : Vec d,
      (∫ z in Set.Ioo a b ×ˢ originBall d R, (P z.1 (v+z.2) y)^2) ≤
        D * Real.exp (-(2*κ) * euclideanSq (y-v)) := by
  obtain ⟨D,κ,hD,hκ,hbound⟩ := akm_heatKernel_translated_gaussian_envelope hK hP ha hab hR
  let S := Set.Ioo a b ×ˢ originBall d R
  have hcomp := isCompact_closure_originBall d R
  letI : IsFiniteMeasure (volume.restrict (originBall d R)) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
      (hcomp.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  have hvol : (volume : Measure (ℝ × Vec d)).restrict S =
      (volume.restrict (Set.Ioo a b)).prod (volume.restrict (originBall d R)) := by
    simp only [S,Measure.prod_restrict,← Measure.volume_eq_prod]
  letI : IsFiniteMeasure (volume.restrict S) := by rw [hvol]; infer_instance
  have hSm : MeasurableSet S := by
    apply measurableSet_Ioo.prod
    unfold originBall euclideanNorm euclideanSq dot
    exact measurableSet_lt (by fun_prop) measurable_const
  refine ⟨D^2 * volume.real S,κ,mul_nonneg (sq_nonneg _) measureReal_nonneg,hκ,?_⟩
  intro v y
  have hc : ContinuousOn (fun z : ℝ × Vec d => P z.1 (v+z.2) y) S :=
    hP.1.comp ((continuous_fst.prodMk
      ((continuous_const.add continuous_snd).prodMk continuous_const)).continuousOn)
      (fun z hz => ⟨ha.trans hz.1.1,Set.mem_univ _⟩)
  have hi : MemLp (fun z : ℝ × Vec d => P z.1 (v+z.2) y) 2 (volume.restrict S) := by
    apply MemLp.of_bound (hc.aestronglyMeasurable hSm) (D*Real.exp (-κ*euclideanSq (y-v)))
    filter_upwards [ae_restrict_mem hSm] with z hz
    exact hbound z.1 hz.1 z.2 hz.2 v y
  calc
    _ ≤ ∫ _z in S, D^2 * Real.exp (-(2*κ)*euclideanSq (y-v)) := by
      apply integral_mono_ae hi.integrable_sq (integrable_const _)
      filter_upwards [ae_restrict_mem hSm] with z hz
      have hh := pow_le_pow_left₀ (abs_nonneg _) (hbound z.1 hz.1 z.2 hz.2 v y) 2
      rw [sq_abs,mul_pow] at hh
      convert hh using 1
      simp_rw [pow_two]
      rw [← Real.exp_add]
      congr 2
      ring
    _ = _ := by simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]; ring

end EinsteinRelation.Correctors
