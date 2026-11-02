import EinsteinFull.Calculus.C17TubeParabolicScaling
import EinsteinFull.Calculus.C13TubeGeneralChainAssembly

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- The parabolic affine change of variables on a source cylinder. -/
theorem c17_parabolic_integral_rescale {d : ℕ} (y : PDE.Vec d)
    {r : ℝ} (hr : 0 < r) (a b : ℝ) (f : ℝ × PDE.Vec d → ℝ) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) 1,
      f (r^2*z.1, y+r • z.2)) =
      (r^2 * r^d)⁻¹ * ∫ z in Set.Ioo (r^2*a) (r^2*b) ×ˢ sourceBall y r, f z := by
  have ht := c13_affine_time_integral (d := d) 0 (r^2) a b (sq_pos_of_pos hr)
    (sourceBall (0 : PDE.Vec d) 1) (fun z => f (z.1, y + r • z.2))
  simp only [zero_add] at ht
  have hs := PDE.Parabolic.Rescale.integral_comp_of_map_eq_smul
    (c17_spacetime_affine_embedding y hr)
    (c17_spacetime_affine_map_cylinder y hr (r^2*a) (r^2*b)) f
  have hp : 0 ≤ (r^d)⁻¹ := inv_nonneg.mpr (pow_nonneg hr.le d)
  simp only [Module.finrank_fin_fun, abs_of_pos (pow_pos hr d),
    ENNReal.toReal_ofReal hp, smul_eq_mul] at hs
  rw [hs] at ht
  have hn : r^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hr)
  rw [mul_inv]
  calc
    _ = (r^2)⁻¹ * ((r^2) * (∫ z in Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) 1,
      f (r^2*z.1, y+r • z.2))) := by rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    _ = (r^2)⁻¹ * ((r^d)⁻¹ * ∫ z in Set.Ioo (r^2*a) (r^2*b) ×ˢ sourceBall y r, f z) := by rw [ht]
    _ = _ := by ring

/-- The solution energy keeps its Lebesgue density under parabolic rescaling. -/
theorem c17_parabolic_weighted_solution_energy {d : ℕ} (y : PDE.Vec d)
    {r : ℝ} (hr : 0 < r) (a b : ℝ) (ρ : PDE.Vec d → ℝ)
    (u : ℝ × PDE.Vec d → ℝ) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) 1,
      ρ (y+r • z.2) * u (r^2*z.1, y+r • z.2)^2) =
      (r^2 * r^d)⁻¹ * ∫ z in Set.Ioo (r^2*a) (r^2*b) ×ˢ sourceBall y r,
        ρ z.2 * u z^2 :=
  c17_parabolic_integral_rescale y hr a b (fun z => ρ z.2 * u z^2)

/-- The scaled gradient contributes two additional powers of the radius. -/
theorem c17_parabolic_weighted_gradient_energy {d : ℕ} (y : PDE.Vec d)
    {r : ℝ} (hr : 0 < r) (a b : ℝ) (ρ : PDE.Vec d → ℝ)
    (G : ℝ × PDE.Vec d → PDE.Vec d) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) 1,
      ρ (y+r • z.2) * euclideanNorm (r • G (r^2*z.1, y+r • z.2))^2) =
      (r^2 * (r^2 * r^d)⁻¹) * ∫ z in Set.Ioo (r^2*a) (r^2*b) ×ˢ sourceBall y r,
        ρ z.2 * euclideanNorm (G z)^2 := by
  calc
    _ = ∫ z in Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) 1,
        r^2 * (ρ (y+r • z.2) * euclideanNorm (G (r^2*z.1, y+r • z.2))^2) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [TimeChange.euclideanNorm_smul, abs_of_pos hr]
          ring
    _ = r^2 * (∫ z in Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) 1,
        ρ (y+r • z.2) * euclideanNorm (G (r^2*z.1, y+r • z.2))^2) := by
          rw [integral_const_mul]
    _ = _ := by
      rw [c17_parabolic_integral_rescale y hr a b (fun z => ρ z.2 * euclideanNorm (G z)^2)]
      ring

end EinsteinFull.Calculus
