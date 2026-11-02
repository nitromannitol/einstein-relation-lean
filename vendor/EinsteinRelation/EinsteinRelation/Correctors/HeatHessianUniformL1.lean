import EinsteinRelation.Correctors.HeatHessianDilation

/-! Source: `paper/main.tex:716,748`. Unit-time Gaussian integrability
and exact parabolic scaling give one uniform positive-time Hessian bound. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- A finite family of unit-time masses controls every mixed Gaussian
Hessian by `C/t`, with the constant chosen before time and coordinates. -/
theorem heatKernel_mixedHessian_uniform_L1_of_unit {d : ℕ}
    (hunit : ∀ i j : Fin d, Integrable (coordinateDerivative j
      (coordinateDerivative i (euclideanHeatKernel (d := d) 1))) volume) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ i j : Fin d,
      Integrable (coordinateDerivative j
        (coordinateDerivative i (euclideanHeatKernel (d := d) t))) volume ∧
      (∫ x, |coordinateDerivative j
        (coordinateDerivative i (euclideanHeatKernel (d := d) t)) x|) ≤ C / t := by
  let m : Fin d → Fin d → ℝ := fun i j => ∫ x,
    |coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel (d := d) 1)) x|
  have hm (i j : Fin d) : 0 ≤ m i j := integral_nonneg (fun _ => abs_nonneg _)
  let C : ℝ := 1 + ∑ i, ∑ j, m i j
  have hsum : 0 ≤ ∑ i, ∑ j, m i j := Finset.sum_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => hm i j))
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro t ht i j
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hst : Real.sqrt t ^ 2 * 1 = t := by rw [Real.sq_sqrt ht.le, mul_one]
  have hscale := integrable_heatKernel_mixedHessian_scale (Real.sqrt t) 1 hs
    (by norm_num) i j (hunit i j)
  rw [hst, Real.sq_sqrt ht.le] at hscale
  refine ⟨hscale.1, ?_⟩
  have hmC : m i j ≤ C := by
    have hrow : m i j ≤ ∑ j, m i j :=
      Finset.single_le_sum (fun j _ => hm i j) (Finset.mem_univ j)
    have htotal : (∑ j, m i j) ≤ ∑ i, ∑ j, m i j :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hm i j))
        (Finset.mem_univ i)
    dsimp [C]
    linarith
  rw [hscale.2]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hmC (inv_nonneg.mpr ht.le)

end EinsteinRelation.Correctors
