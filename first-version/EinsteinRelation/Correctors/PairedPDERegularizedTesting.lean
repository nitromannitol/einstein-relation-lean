import EinsteinRelation.Correctors.PairedPDERegularizationDerivative

/-! # Testing the actual equation with a regularized energy field

Source: `paper/main.tex:832–840`. The test is the outer compact cutoff
times a regularization of the actual cutoff solution. It is admissible
without differentiating the solution, and is exercised in the actual
parabolic weak equation below.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- A double cutoff produces an admissible regularized energy test from
the actual weak solution. Its weak-equation integrand is genuinely
integrable. Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_regularized_cutoff_test {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : MeasurableSet U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ ρ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) :
    let ψ := fun z : ℝ × Vec d =>
      ζ z * ∫ w : ℝ × Vec d, ζ w * u w * ρ (z - w)
    ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ interior I ×ˢ U ∧
      Integrable (fun z => -(u z) * fderiv ℝ ψ z (1, 0) +
        dot ((A z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0, unitVector j))) (volume.restrict (I ×ˢ U)) ∧
      (∫ z in I ×ˢ U, -(u z) * fderiv ℝ ψ z (1, 0) +
        dot ((A z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0, unitVector j))) = 0 := by
  dsimp only
  have hf := parabolicSolution_cutoff_memLp_global hI hU hsol hζ.continuous hζc
    (hζsupp.trans (Set.prod_mono interior_subset Set.Subset.rfl))
  have hconv : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => ∫ w : ℝ × Vec d, ζ w * u w * ρ (z - w)) :=
    hρc.contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ)
      (hf.locallyIntegrable (by norm_num)) hρ
  have hc := hζ.mul hconv
  have hcc : HasCompactSupport (fun z : ℝ × Vec d =>
      ζ z * ∫ w : ℝ × Vec d, ζ w * u w * ρ (z - w)) := hζc.mul_right
  have hs : tsupport (fun z : ℝ × Vec d =>
      ζ z * ∫ w : ℝ × Vec d, ζ w * u w * ρ (z - w)) ⊆ interior I ×ˢ U :=
    tsupport_mul_subset_left.trans hζsupp
  exact ⟨hc, hcc, hs, parabolicSolution_test_integrable hK A hsol hc hcc,
    hsol.2.2.2.2 _ hc hcc hs⟩

end EinsteinRelation.Correctors
