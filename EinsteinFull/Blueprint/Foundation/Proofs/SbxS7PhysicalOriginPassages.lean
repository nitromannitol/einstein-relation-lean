import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.Regeneration.GMPVelocityTransfer

/-!
Finite rounded passages of the physical origin process of GMP after all finite restarts, from
its positive velocity along the force (`EinsteinFull.Regeneration.gmp_physical_origin_velocity`).
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- The GMP velocity law supplies finite passages of its physical origin
process after all finite restarts. This conclusion stays under that physical
law; applying it to a supplied reduced law requires internal law transport. -/
theorem coupling_scope_gmp_physical_origin_passages_finite {d : ℕ}
    (hd : 2 ≤ d) {L r : ℝ} (Q : EnvironmentLaw d L r)
    {lam : ℝ} (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (hP : IsGMPPhysicalOriginLaw hd Q.ellipticity_parameter Q lam h₀.le h₁ P)
    (Δ : ℝ≥0) (R : ℝ) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂P ω, ∀ (s : ℝ≥0) (a : ℝ) (n : ℕ),
      Regeneration.passageSequence Δ lam R a (Regeneration.pathTimeShift γ s)
        (EinsteinRelation.External.GantertSection7Support.firstCoordinateIndex hd) n ≠ ⊤ := by
  obtain ⟨v, hv, hpos, _hunique⟩ :=
    EinsteinFull.Regeneration.gmp_physical_origin_velocity hd Q h₀ h₁ P hP
  filter_upwards [hv] with ω hω
  filter_upwards [hω] with γ hγ s a n
  exact ConditionalTrialExhaustion.shifted_passageSequence_ne_top_of_escape
    Δ lam R γ (EinsteinRelation.External.GantertSection7Support.firstCoordinateIndex hd)
    (ConditionalTrialExhaustion.directional_escape_of_positive_velocity
      γ v (EinsteinRelation.External.GantertSection7Support.firstCoordinateIndex hd)
      hγ hpos) s a n

end EinsteinFull.Blueprint
