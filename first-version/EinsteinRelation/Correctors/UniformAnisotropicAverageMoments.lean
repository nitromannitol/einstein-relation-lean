import EinsteinRelation.Correctors.UniformLinearKernelMass
import EinsteinRelation.Correctors.AnisotropicAverageMass
import EinsteinRelation.Correctors.RadialAverageMomentBounds

/-! # Uniform moments of the anisotropic averaging remainder

Source: `paper/main.tex:1041–1042`. The determinant normalization and
bounded coordinate map give the inverse-scale estimate before the law.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- Derivative masses of the normalized anisotropic average are uniform
in the coordinate map (`paper/main.tex:1003–1007,1041–1042`). -/
theorem anisotropicAverage_uniform_derivative_bound {d : ℕ}
    {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Vec d ≃L[ℝ] Vec d),
      (∀ i j : Fin d, |(B (unitVector i)) j| ≤ b) →
      ∀ cs : List (Fin d), cs.length = n → ∀ r : ℝ, 0 < r →
      (∫ x : Vec d, |coordinateIterate cs (anisotropicAverage B r) x|) ≤ C / r ^ n := by
  obtain ⟨A, hA, hmass⟩ := KernelCalculus.exists_integral_abs_coordinateIterate_order_bound
    (radialAverage d 1) n
  refine ⟨1 + ((d : ℝ) * b) ^ n * A, by positivity, fun B hB cs hcs r hr => ?_⟩
  have hm (ds : List (Fin d)) (hds : ds.length = cs.length) :
      (∫ x : Vec d, |coordinateIterate ds (radialAverage d r) x|) ≤ A / r ^ n := by
    rw [integral_abs_coordinateIterate_radialAverage hr ds, hds, hcs, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hmass ds (hds.trans hcs)) (by positivity)
      |>.trans_eq (mul_comm _ _)
  have hu := KernelCalculus.integral_abs_coordinateIterate_comp_linear_bound B hb hB
    (radialAverage_contDiff hr) (radialAverage_hasCompactSupport hr) cs hm
  have he : coordinateIterate cs (anisotropicAverage B r) = fun x =>
      |B.toContinuousLinearMap.det| * coordinateIterate cs (fun y => radialAverage d r (B y)) x :=
    KernelCalculus.coordinateIterate_const_mul ((radialAverage_contDiff hr).comp B.contDiff) cs _
  rw [he]
  simp_rw [abs_mul, abs_abs]
  rw [integral_const_mul]
  rw [hcs] at hu
  apply hu.trans
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr.le _)

/-- The Laplacian of the normalized averaging kernel has uniform inverse
square mass (`paper/main.tex:1041–1042`). -/
theorem anisotropicAverage_uniform_laplacian_bound {d : ℕ}
    {b : ℝ} (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Vec d ≃L[ℝ] Vec d),
      (∀ i j : Fin d, |(B (unitVector i)) j| ≤ b) →
      ∀ R : ℝ, 0 < R → (∫ x : Vec d, |coordLaplacian (anisotropicAverage B R) x|) ≤ C / R ^ 2 := by
  obtain ⟨A, hA, hmass⟩ := anisotropicAverage_uniform_derivative_bound hb 2
  refine ⟨1 + d * A, by positivity, fun B hB R hR => ?_⟩
  apply (integral_abs_coordLaplacian_le (anisotropicAverage_contDiff B hR)
    (anisotropicAverage_hasCompactSupport B hR)).trans
  calc
    _ ≤ ∑ _i : Fin d, A / R ^ 2 :=
      Finset.sum_le_sum fun i _ => hmass B hB [i, i] rfl R hR
    _ = ((d : ℝ) * A) / R ^ 2 := by simp [mul_div_assoc]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

/-- The actual largest-scale averaging remainder has uniform inverse-scale
moments under the scalar averaging assumption (`paper/main.tex:1041–1042`). -/
theorem eLpNorm_anisotropicAverage_uniform_le {d : ℕ}
    {b : ℝ} (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Vec d ≃L[ℝ] Vec d),
      (∀ i j : Fin d, |(T (unitVector i)) j| ≤ b) →
      ∀ (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q],
      IsStationary Q → ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
      ∀ (M R : ℝ), 0 < M → 0 < R →
      ∀ (f : FieldPair d → ℝ), Measurable f →
      (∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) p Q ≤
        ENNReal.ofReal (M * ((Real.sqrt (1 + t))⁻¹ + R⁻¹))) →
      eLpNorm (horizontalMollify (anisotropicAverage T R) f) p Q ≤ ENNReal.ofReal (C * M / R) := by
  obtain ⟨B, hB, hbound⟩ := anisotropicAverage_uniform_laplacian_bound hb
  refine ⟨4 + 3 * B, by positivity,
    fun T hT Q _ hQ p hp hpt M R hM hR f hf hheat => ?_⟩
  have hK := anisotropicAverage_contDiff T hR
  have hKc := anisotropicAverage_hasCompactSupport T hR
  have hmass : (∫ x : Vec d, |anisotropicAverage T R x|) ≤ 2 * (R ^ 2 / R ^ 2) := by
    simp only [abs_of_nonneg (anisotropicAverage_nonneg T hR _), integral_anisotropicAverage T hR,
      div_self (pow_ne_zero 2 hR.ne')]
    norm_num
  have ht := horizontalMollify_heatTransfer_ae hQ hK hKc hf
    (integrable_of_heatSmoothed_bound hp hf hheat) (sq_pos_of_pos hR)
  have h := eLpNorm_convolution_le_of_heatTransfer hQ hp hpt hK.continuous.measurable
    (hK.continuous.integrable_of_hasCompactSupport hKc)
    (contDiff_coordLaplacian hK).continuous.measurable (integrable_coordLaplacian_of_smooth hK hKc)
    (by norm_num : (0 : ℝ) < 2) hB hM hR hR (sq_pos_of_pos hR) le_rfl
    hmass (hbound T hT R hR) hf hheat ht
  convert h using 1
  congr 1
  field_simp
  ring

end EinsteinRelation.Correctors
