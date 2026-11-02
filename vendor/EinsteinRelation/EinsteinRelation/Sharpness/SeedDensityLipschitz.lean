import EinsteinRelation.Sharpness.DivergenceProfileBounds
import EinsteinRelation.Sharpness.ScaledSeedGradientLipschitz
namespace EinsteinRelation.Sharpness
private theorem densityLip_coord {d : ℕ} (k : Fin d) (v : Vec d) : |v k| ≤ euclideanNorm v := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  unfold euclideanSq dot
  rw [pow_two]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ k)

/-- Source main.tex1212–1231: the actual density of the fixed scaled seed is uniformly
Lipschitz in literal Euclidean distance. Its constant precedes every sample and point. -/
theorem exists_uniform_seedField_density_euclidean_lipschitz {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ)) (δ : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (W : NoiseSample d) (x y : Vec d),
      |densityField i δ (fun z => ε * seedField d W z) x -
        densityField i δ (fun z => ε * seedField d W z) y| ≤ L * euclideanNorm (x-y) := by
  obtain ⟨M, _hM, hbox⟩ := exists_uniform_scaled_seedField_jet_box ε hgrad
  obtain ⟨C, B, _hC, hB, _hbound, hLip⟩ :=
    exists_coefficientDivergenceProfile_bound_and_lipschitz d i M
  obtain ⟨G, hG, hGLip⟩ := exists_uniform_scaled_seedField_gradient_euclidean_lipschitz d ε
  obtain ⟨H, hH, hHLip⟩ := exists_uniform_scaled_seedField_hessian_euclidean_lipschitz d ε
  refine ⟨|δ/2| * B * (G+H), mul_nonneg (mul_nonneg (abs_nonneg _) hB) (add_nonneg hG hH), ?_⟩
  intro W x y
  let J (z : Vec d) : Vec d × (Fin d → Fin d → ℝ) :=
    (gradient (fun t => ε * seedField d W t) z,
     fun m n => coordinateDerivative m (coordinateDerivative n (fun t => ε * seedField d W t)) z)
  have hD : 0 ≤ euclideanNorm (x-y) := Real.sqrt_nonneg _
  have hN : 0 ≤ (G+H) * euclideanNorm (x-y) := mul_nonneg (add_nonneg hG hH) hD
  have hJ : ‖J x - J y‖ ≤ (G+H) * euclideanNorm (x-y) := by
    apply norm_prod_le_iff.mpr
    constructor
    · apply (pi_norm_le_iff_of_nonneg hN).mpr
      intro k
      change |(gradient (fun t => ε * seedField d W t) x - gradient (fun t => ε * seedField d W t) y) k| ≤ _
      exact ((densityLip_coord k _).trans (hGLip W x y)).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hH) hD)
    · apply (pi_norm_le_iff_of_nonneg hN).mpr
      intro m
      apply (pi_norm_le_iff_of_nonneg hN).mpr
      intro n
      change |coordinateDerivative m (coordinateDerivative n (fun t => ε * seedField d W t)) x -
        coordinateDerivative m (coordinateDerivative n (fun t => ε * seedField d W t)) y| ≤ _
      exact (hHLip W m n x y).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hG) hD)
  have hj : ∀ z, jacobianFactor i (gradient (fun t => ε * seedField d W t) z) ≠ 0 := by
    intro z
    have hz := (jacobianFactor_bounds i _ (hgrad W z)).1
    linarith
  have hprofile (z : Vec d) : densityField i δ (fun t => ε * seedField d W t) z =
      1 + δ/2 * coefficientDivergenceProfile i (J z) := by
    unfold densityField
    rw [divergence_coefficientField_column_eq_profile i _ (contDiff_const.mul (contDiff_seedField d W)) hj]
  rw [hprofile x, hprofile y]
  calc
    |1 + δ/2 * coefficientDivergenceProfile i (J x) - (1 + δ/2 * coefficientDivergenceProfile i (J y))| =
        |δ/2| * |coefficientDivergenceProfile i (J x) - coefficientDivergenceProfile i (J y)| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |δ/2| * (B * ‖J x-J y‖) :=
      mul_le_mul_of_nonneg_left (hLip _ (hbox W x) _ (hbox W y)) (abs_nonneg _)
    _ ≤ |δ/2| * (B * ((G+H) * euclideanNorm (x-y))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJ hB) (abs_nonneg _)
    _ = _ := by ring
end EinsteinRelation.Sharpness
