import EinsteinRelation.Correctors.AKMHeatKernelGaussianData
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- Gaussian section energies give a weighted product L² bound, including
bounded scalar initial data. Source: AKM E.1 (E.7)–(E.8);
`paper/main.tex:787–792,850`. -/
theorem memLp_gaussian_weighted_product {d : ℕ} {S : Type*}
    [MeasurableSpace S] (ν : Measure S) [SFinite ν]
    {κ D B : ℝ} (_hκ : 0 < κ) (hD : 0 ≤ D) (_hB : 0 ≤ B)
    (hg : Integrable (fun y : Vec d => Real.exp (-κ * euclideanSq y)) volume)
    {f : Vec d × S → ℝ} (hfm : Measurable f)
    (hf : ∀ y, MemLp (fun z => f (y,z)) 2 ν)
    (he : ∀ y, (∫ z, f (y,z)^2 ∂ν) ≤ D * Real.exp (-(2*κ) * euclideanSq y))
    {b : Vec d → ℝ} (hbm : Measurable b) (hbb : ∀ y, |b y| ≤ B) :
    MemLp (fun z : Vec d × S => f z * b z.1 /
      Real.sqrt (Real.exp (-κ * euclideanSq z.1))) 2 (volume.prod ν) := by
  let w : Vec d → ℝ := fun y => Real.exp (-κ*euclideanSq y)
  have hwm : Measurable w := by unfold w euclideanSq dot; fun_prop
  have hwp (y : Vec d) : 0 < w y := Real.exp_pos _
  let g : Vec d × S → ℝ := fun z => f z*b z.1/Real.sqrt (w z.1)
  have hgm : Measurable g := hfm.mul (hbm.comp measurable_fst) |>.div
    (hwm.sqrt.comp measurable_fst)
  have hsq (z : Vec d × S) : g z^2 = (b z.1^2/w z.1)*f z^2 := by
    dsimp only [g]
    rw [div_pow,mul_pow,Real.sq_sqrt (hwp _).le]
    ring
  have hi (y : Vec d) : Integrable (fun z => g (y,z)^2) ν := by
    simpa only [hsq] using (hf y).integrable_sq.const_mul (b y^2/w y)
  have hbound (y : Vec d) : (∫ z, g (y,z)^2 ∂ν) ≤ D*B^2*w y := by
    simp_rw [hsq]
    rw [integral_const_mul]
    have hb2 : b y^2 ≤ B^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hbb y) 2
    have hex : Real.exp (-(2*κ)*euclideanSq y) = w y*w y := by
      dsimp only [w]
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ (b y^2/w y)*(D*Real.exp (-(2*κ)*euclideanSq y)) :=
        mul_le_mul_of_nonneg_left (he y) (div_nonneg (sq_nonneg _) (hwp y).le)
      _ = D*b y^2*w y := by rw [hex]; field_simp
      _ ≤ _ := by gcongr
  apply (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hgm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi,?_⟩
  have hm : AEStronglyMeasurable (fun y => ∫ z, g (y,z)^2 ∂ν) volume :=
    (hgm.pow_const 2).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hb := hg.const_mul (D*B^2)
  have heq : (fun y => ∫ z, ‖g (y,z)^2‖ ∂ν) = fun y => ∫ z, g (y,z)^2 ∂ν := by
    funext y
    exact integral_congr_ae (ae_of_all _ fun z => Real.norm_of_nonneg (sq_nonneg _))
  rw [heq]
  apply hb.mono' hm
  filter_upwards with y
  rw [Real.norm_of_nonneg (integral_nonneg fun z => sq_nonneg _)]
  exact hbound y

end EinsteinRelation.Correctors
