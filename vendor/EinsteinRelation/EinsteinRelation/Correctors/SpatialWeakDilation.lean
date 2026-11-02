import EinsteinRelation.Correctors.SpatialDilationTests
import EinsteinRelation.Correctors.SpatialLocalL2Dilation
import EinsteinRelation.Correctors.SpatialBallLocalL2

/-!
# Spatial dilation of weak gradients and divergence

Source: `paper/main.tex:693-702`. Inverse-dilated smooth tests and the
Haar change of variables prove the weak chain rule without choosing
pointwise derivatives.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

private theorem locallyIntegrable_of_ball_memLp {d : ℕ} (u : Vec d → ℝ)
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) :
    LocallyIntegrableOn u Set.univ volume := by
  rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
  intro K hK
  letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  exact (memLp_on_compacts_of_euclidean_balls u hu K hK).integrable (by norm_num)

/-- Positive spatial dilation gives the actual distributional scalar chain rule. -/
theorem hasWeakGradient_dilation {d : ℕ} (u : Vec d → ℝ) (g : Vec d → Vec d)
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hg : ∀ R : ℝ, 0 < R → MemLp g 2 (volume.restrict (ball 0 R)))
    (hw : HasWeakGradient Set.univ u g) (r c : ℝ) (hr : 0 < r) :
    HasWeakGradient Set.univ (fun x => c * u (r • x))
      (fun x => (c * r) • g (r • x)) := by
  have hu' := memLp_two_on_euclidean_balls_dilation u hu r c hr
  have hg' := memLp_two_on_euclidean_balls_dilation g hg r (c * r) hr
  intro j
  refine ⟨locallyIntegrable_of_ball_memLp _ (by simpa only [smul_eq_mul] using hu'),
    locallyIntegrable_of_ball_memLp _ (fun R hR =>
      (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).comp_memLp' (hg' R hR)), ?_⟩
  intro φ hφ
  obtain ⟨hψ, hchain⟩ := isSpatialTest_inv_dilation φ hφ r hr
  let ψ : Vec d → ℝ := fun x => φ (r⁻¹ • x)
  have hchain' (x : Vec d) (j : Fin d) :
      coordinateDerivative j ψ (r • x) = r⁻¹ * coordinateDerivative j φ x := hchain x j
  have hsrc := (hw j).2.2 ψ hψ
  simp only [Measure.restrict_univ] at hsrc ⊢
  have hscaled : (∫ x, u (r • x) * coordinateDerivative j ψ (r • x)) =
      -(∫ x, g (r • x) j * ψ (r • x)) := by
    rw [Measure.integral_comp_smul volume (fun x => u x * coordinateDerivative j ψ x) r,
      Measure.integral_comp_smul volume (fun x => g x j * ψ x) r, hsrc, smul_neg]
  have hψeq (x : Vec d) : ψ (r • x) = φ x := by
    simp only [ψ, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  simp only [hchain', hψeq, mul_left_comm (u _), integral_const_mul] at hscaled
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  calc
    c * (∫ x, u (r • x) * coordinateDerivative j φ x) =
        (c * r) * (r⁻¹ * (∫ x, u (r • x) * coordinateDerivative j φ x)) := by
      rw [← mul_assoc, mul_assoc c r r⁻¹, mul_inv_cancel₀ hr.ne', mul_one]
    _ = -(c * (r * (∫ x, g (r • x) j * φ x))) := by
      rw [hscaled, mul_neg, mul_assoc]

/-- Constant dilation preserves zero weak divergence, with one aggregate test pairing. -/
theorem hasWeakDivergence_zero_dilation {d : ℕ} (F : Vec d → Vec d)
    (hF : ∀ R : ℝ, 0 < R → MemLp F 2 (volume.restrict (ball 0 R)))
    (hw : HasWeakDivergence Set.univ F (fun _ => 0)) (r c : ℝ) (hr : 0 < r) :
    HasWeakDivergence Set.univ (fun x => c • F (r • x)) (fun _ => 0) := by
  have hF' := memLp_two_on_euclidean_balls_dilation F hF r c hr
  refine ⟨fun j => locallyIntegrable_of_ball_memLp _ (fun R hR =>
    (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).comp_memLp' (hF' R hR)),
    locallyIntegrableOn_zero, ?_⟩
  intro φ hφ
  obtain ⟨hψ, hchain⟩ := isSpatialTest_inv_dilation φ hφ r hr
  let ψ : Vec d → ℝ := fun x => φ (r⁻¹ • x)
  have hchain' (x : Vec d) (j : Fin d) :
      coordinateDerivative j ψ (r • x) = r⁻¹ * coordinateDerivative j φ x := hchain x j
  have hsrc := hw.2.2 ψ hψ
  simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] at hsrc ⊢
  have hscaled : (∫ x, dot (F (r • x)) (gradient ψ (r • x))) = 0 := by
    rw [Measure.integral_comp_smul volume (fun x => dot (F x) (gradient ψ x)) r,
      hsrc, smul_zero]
  have hdot (x : Vec d) : dot (F (r • x)) (gradient ψ (r • x)) =
      r⁻¹ * dot (F (r • x)) (gradient φ x) := by
    simp only [dot, gradient, hchain', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [hdot, integral_const_mul] at hscaled
  have hz := (mul_eq_zero.mp hscaled).resolve_left (inv_ne_zero hr.ne')
  have hdotc (x : Vec d) : dot (c • F (r • x)) (gradient φ x) =
      c * dot (F (r • x)) (gradient φ x) := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  simp only [hdotc, integral_const_mul, hz, mul_zero]

end EinsteinRelation.Correctors
