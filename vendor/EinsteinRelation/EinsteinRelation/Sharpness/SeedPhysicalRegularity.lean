import EinsteinRelation.Sharpness.SeedPhysicalLipschitz
import EinsteinRelation.Sharpness.Ellipticity
namespace EinsteinRelation.Sharpness
/-- Source main.tex1212–1231: one deterministic ellipticity/regularity parameter works for
all literal physical samples of a fixed admissible scaled seed and density. The constant
precedes the sample map, samples and law; all spatial norms are Euclidean. -/
theorem exists_uniform_seedField_physical_regularity {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ)) (δ : ℝ)
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3/4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5/4 : ℝ)) :
    ∃ Λ : ℝ, 4 ≤ Λ ∧ ∀ F : NoiseSample d → FieldPair d,
      (∀ (W : NoiseSample d) (x : Vec d),
        (F W).1 x = physicalCoefficientField i δ (fun y => ε * seedField d W y) x ∧
        (F W).2 x = potentialField i δ (fun y => ε * seedField d W y) x) →
      ∀ W : NoiseSample d, IsRegular Λ (F W) := by
  obtain ⟨A,hA,hALip⟩ := exists_uniform_seedField_physicalCoefficient_operator_lipschitz i ε hgrad δ (fun W x => (hμ W x).1)
  obtain ⟨V,hV,hVLip⟩ := exists_uniform_seedField_potential_euclidean_lipschitz i ε hgrad δ (fun W x => (hμ W x).1)
  let Λ := 4+A+V
  have hΛ : (4:ℝ) ≤ Λ := by dsimp [Λ]; linarith
  have hAΛ : A ≤ Λ := by dsimp [Λ]; linarith
  have hVΛ : V ≤ Λ := by dsimp [Λ]; linarith
  refine ⟨Λ,hΛ,fun F hchar W => ?_⟩
  have ha : ((F W).1 : Vec d → Mat d) = physicalCoefficientField i δ (fun y => ε * seedField d W y) :=
    funext fun x => (hchar W x).1
  have hv : ((F W).2 : Vec d → ℝ) = potentialField i δ (fun y => ε * seedField d W y) :=
    funext fun x => (hchar W x).2
  have he := physicalCoefficientField_isElliptic i δ (fun y => ε * seedField d W y) (hgrad W) (hμ W)
  refine ⟨?_,?_,?_,?_⟩
  · intro x
    rw [ha]
    refine ⟨(he x).1,fun ξ => ?_⟩
    have hsq : 0 ≤ euclideanSq ξ := by
      change 0 ≤ ∑ j : Fin d, ξ j * ξ j
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg (ξ j)
    exact ⟨(mul_le_mul_of_nonneg_right (inv_anti₀ (by norm_num : (0:ℝ)<4) hΛ) hsq).trans ((he x).2 ξ).1,
      ((he x).2 ξ).2.trans (mul_le_mul_of_nonneg_right hΛ hsq)⟩
  · intro x
    rw [hv]
    exact (potentialField_abs_le i δ _ (hμ W) x).trans (by linarith)
  · intro x y ξ
    rw [ha]
    exact (hALip W x y ξ).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAΛ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  · intro x y
    rw [hv]
    exact (hVLip W x y).trans (mul_le_mul_of_nonneg_right hVΛ (Real.sqrt_nonneg _))
end EinsteinRelation.Sharpness
