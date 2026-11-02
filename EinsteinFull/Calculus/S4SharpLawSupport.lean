import EinsteinFull.Blueprint.Roots.node_sharp_u2E_example
import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_positive_u2D_coefficient
import EinsteinFull.Calculus.S1SharpSmoothSet

/-! The sharpness example `sharp.example` from the positive-coefficient node, given the
existence of a unit white-noise law (the single literature input, AKM Proposition 5.14).
The environment law is the pushforward of the white-noise law by the physical pair, with
stationarity and finite range from the vendor seed-space results. -/

open MeasureTheory

namespace EinsteinFull.Calculus.S4

open EinsteinRelation EinsteinRelation.Sharpness EinsteinFull.Work.W8
open EinsteinFull.Blueprint

/-- `sharp.example` follows from `sharp.example#positive-coefficient` once a unit white-noise
law exists in every dimension `d ≥ 2`. -/
theorem sharp_example_of_whiteNoise
    (hW : ∀ d : ℕ, 2 ≤ d → ∃ P : Measure (NoiseSample d), External.IsWhiteNoiseLaw P)
    (hpos : node_sharp_u2E_example_u23_positive_u2D_coefficientStmt) :
    node_sharp_u2E_exampleStmt := by
  intro d hd
  obtain ⟨P, hP⟩ := hW d hd
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨D, S, hr, -, hreg, hS, hmem, hsm⟩ :=
    EinsteinFull.Calculus.S1.exists_sharpData (⟨0, by omega⟩ : Fin d)
  have hF : Measurable (physicalPair (⟨0, by omega⟩ : Fin d)) := measurable_physicalPair _
  have hstat : IsStationary (P.map (physicalPair (⟨0, by omega⟩ : Fin d))) :=
    sharpPhysicalPair_isStationary (⟨0, by omega⟩ : Fin d) (clockParameter _) (seedScale d)
      corrector_gradient_bound (density_bounds _) hP
  have hfr : HasFiniteRange 4 (P.map (physicalPair (⟨0, by omega⟩ : Fin d))) :=
    sharpPhysicalPair_hasFiniteRange (⟨0, by omega⟩ : Fin d) (clockParameter _) (seedScale d)
      corrector_gradient_bound (density_bounds _) hP
  let Q : EnvironmentLaw d D.ellipticity D.dependenceRange :=
    { measure := P.map (physicalPair (⟨0, by omega⟩ : Fin d))
      probability := inferInstance
      ellipticity_parameter := D.one_le_ellipticity
      range_parameter := D.one_le_dependenceRange
      regular := (ae_map_iff hF.aemeasurable (measurableSet_isRegular_fieldPair _)).mpr
        (ae_of_all P hreg)
      stationary := hstat
      finiteRange := by rw [hr]; exact hfr }
  refine ⟨D, Q, ?_, ?_⟩
  · have h : ∀ᵐ ω ∂Q.measure, ω ∈ S :=
      (ae_map_iff hF.aemeasurable hS).mpr (ae_of_all P hmem)
    exact h.mono hsm
  · obtain ⟨-, -, hc⟩ := hpos d hd P hP D Q rfl
    obtain ⟨hc0, -, hlim⟩ := hc
    exact ⟨_, hc0, hlim⟩

end EinsteinFull.Calculus.S4
