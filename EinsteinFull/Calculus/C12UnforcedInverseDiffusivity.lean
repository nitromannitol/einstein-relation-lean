import EinsteinFull.Blueprint.G4.node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clock
import EinsteinRelation.Diffusion.TimeChangeCovariance
import EinsteinRelation.Clock.CentredClockField
import EinsteinRelation.Correctors.HomogenizedMatrixBounds

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The supplied unforced physical law inherits the full matrix covariance
from the supplied reduced law by inversion of their actual path clock. -/
theorem supplied_unforced_inverse_diffusivity_of_rate :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
      (Q : EnvironmentLaw d Λ₀ r₀),
      ∀ X Y : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (physicalGenerator (⟨0, by omega⟩ : Fin d) ω 0)
          0 (X (0, ω))) →
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0)
          0 (Y (0, ω))) →
      (∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular Λ₀ ω,
        X (0, ω) = (Y (0, ω)).map
          (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)) →
      HasReducedClockRate Q Y (∫ ω, ω.2 0 ∂reducedLaw Q) →
      HasDiffusivity Q.measure (originLaw Y) (homogenizedCoefficient Q) →
      HasDiffusivity Q.measure (originLaw X)
        ((∫ ω, ω.2 0 ∂reducedLaw Q)⁻¹ • homogenizedCoefficient Q) := by
  intro d hd Λ₀ r₀ Q X Y _hX hY hmap hrate hdiff
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) := by
    filter_upwards [hY] with ω hω
    exact hω.1
  have hmap' : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω,
      X (0, ω) = (Y (0, ω)).map
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω) := by
    filter_upwards [hmap] with ω hω
    obtain ⟨hreg, heq⟩ := hω
    intro _hreg'
    exact heq
  have hm : 0 < ∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Q :=
    lt_of_lt_of_le
      (inv_pos.mpr (Clock.sourceReducedBound_pos Q.ellipticity_parameter))
      (reducedClockMean_bounds Q).1
  exact TimeChangeCovariance.hasDiffusivity_of_timeChange Q
    (fun _ => X) (fun _ => Y) hprob hmap' hm hrate hdiff

end EinsteinFull.Blueprint
