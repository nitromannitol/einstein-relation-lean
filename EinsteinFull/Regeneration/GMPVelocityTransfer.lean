import EinsteinFull.External.GMPVelocity
import EinsteinRelation.Environment.TranslationErgodicitySupport
import EinsteinRelation.Diffusion.Velocity

/-! # Consuming the source physical velocity law

Finite range and stationarity supply source ergodicity for the actual joint
environment law. Its source physical origin process therefore has a unique
deterministic quenched velocity with strictly positive longitudinal component.
The probability laws needed for uniqueness come from that process realization.
-/

open MeasureTheory

namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.External.GantertSection7Support

/-- The source physical process has one positive-force velocity, without an
additional ergodicity premise on the actual finite-range environment law. -/
theorem gmp_physical_origin_velocity {d : ℕ} (hd : 2 ≤ d) {L R : ℝ}
    (Q : EnvironmentLaw d L R) {lam : ℝ} (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (hP : IsGMPPhysicalOriginLaw hd Q.ellipticity_parameter Q lam h₀.le h₁ P) :
    ∃ v : Vec d, HasQuenchedVelocity Q.measure P v ∧
      0 < v (firstCoordinateIndex hd) ∧
      ∀ w : Vec d, HasQuenchedVelocity Q.measure P w → w = v := by
  have herg : IsTranslationErgodic Q.measure :=
    fun A hA hInv => Localization.environmentLaw_translation_ergodic Q hd A hA hInv
  obtain ⟨v, hv, hpos⟩ := External.gmp_velocity d hd L R Q herg lam h₀ h₁ P hP
  letI : IsProbabilityMeasure Q.measure := Q.probability
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (P ω) := by
    filter_upwards [hP] with ω hω
    obtain ⟨_, r, hr⟩ := hω
    rw [hr]
    exact r.pathLaw_isMarkovKernel.isProbabilityMeasure 0
  exact ⟨v, hv, hpos, fun _ hw => hw.unique hprob hv⟩

end EinsteinFull.Regeneration
