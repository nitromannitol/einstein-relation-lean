import EinsteinRelation.Correctors.UniformLinearKernelMass
import EinsteinRelation.Correctors.AnisotropicDyadicKernels

/-! # Environment-uniform anisotropic band masses

Source: `paper/main.tex:1015–1018`. The constants precede the coordinate
map and hence the environment law.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- All derivatives of a given order of the actual anisotropic band have
one common mass bound over bounded coordinate maps (`paper/main.tex:1015–1018`). -/
theorem anisotropicBandKernel_uniform_derivative_bound {d : ℕ} (hd : 2 ≤ d)
    {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Vec d ≃L[ℝ] Vec d),
      (∀ i j : Fin d, |(B (unitVector i)) j| ≤ b) →
      ∀ cs : List (Fin d), cs.length = n → ∀ r : ℝ, 0 < r →
      (∫ x : Vec d, |coordinateIterate cs (anisotropicBandKernel B r) x|) ≤
        C * (r ^ 2 / r ^ n) := by
  obtain ⟨A, hA, hmass⟩ := KernelCalculus.exists_integral_abs_coordinateIterate_order_bound
    (radialBandKernel d 1) n
  let C : ℝ := 1 + 2 * (((d : ℝ) * b) ^ n * A)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun B hB cs hcs r hr => ?_⟩
  have hu := KernelCalculus.integral_abs_coordinateIterate_comp_linear_bound B hb hB
    (radialBandKernel_contDiff hd (by norm_num : (0 : ℝ) < 1))
    (radialBandKernel_hasCompactSupport hd (by norm_num : (0 : ℝ) < 1)) cs
    (fun ds hds => hmass ds (hds.trans hcs))
  rw [hcs] at hu
  have he : coordinateIterate cs (anisotropicBandKernel B 1) = fun x =>
      (2 * |B.toContinuousLinearMap.det|) *
        coordinateIterate cs (fun y => radialBandKernel d 1 (B y)) x :=
    KernelCalculus.coordinateIterate_const_mul
      ((radialBandKernel_contDiff hd (by norm_num : (0 : ℝ) < 1)).comp B.contDiff) cs _
  have hbase : (∫ x : Vec d, |coordinateIterate cs (anisotropicBandKernel B 1) x|) ≤ C := by
    rw [he]
    simp only [abs_mul, abs_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [integral_const_mul]
    dsimp only [C]
    nlinarith only [hu]
  obtain ⟨D, -, hD⟩ := anisotropicBandKernel_derivative_bounds hd B cs
  have hD1 : D ≤ C := by simpa only [one_pow, div_one, mul_one] using (hD 1 (by norm_num)).2.symm.trans_le hbase
  rw [(hD r hr).2, hcs]
  exact mul_le_mul_of_nonneg_right hD1 (by positivity)

end EinsteinRelation.Correctors
