import EinsteinFull.Calculus.SbxBCenteredLocalReturnClosureR15

open MeasureTheory EinsteinRelation
open EinsteinRelation.Regeneration
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal

namespace EinsteinFull

/-- Centered survival for the complete regeneration time at every positive
width, uniformly over the full signed-force range. -/
theorem b_centered_survival_unconditional_r15 :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
          (h0 : 0 < |lam|) (h1 : |lam| ≤ 1),
          ∃ P : QuenchedPathLaws d,
            IsGMPReducedKernel hd Q.ellipticity_parameter Q |lam| h0.le h1 P ∧
            ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
              ENNReal.ofReal ε ≤ P (x, ω)
                {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta |lam|),
                  euclideanNorm (γ s - x) ≤ (l / |lam|) / 2} := by
  intro d hd Λ₀ r₀ l hl
  exact b_centered_tube_of_local_return b_centered_local_return_unconditional_r15
    hd Λ₀ r₀ l hl

#print axioms b_centered_survival_unconditional_r15

end EinsteinFull
