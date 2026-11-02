import EinsteinFull.Work.W8.SharpnessConstructionSupport
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.HomogenizedCoefficient
import EinsteinRelation.Sharpness.SeedFieldStationarity

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

/-- Graph node `sharp.example#seed-ergodicity`, `paper/main.tex:1572–1572`.
Ergodicity is on the Borel continuous seed-field carrier, with invariance
under all spatial shifts. No coefficient-carrier ergodicity is substituted. -/
def node_sharp_u2E_example_u23_seed_u2D_ergodicityStmt : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d) (P : Measure (NoiseSample d)),
    External.IsWhiteNoiseLaw P →
    let shift : Vec d → C(Vec d, ℝ) → C(Vec d, ℝ) := fun x H =>
      ⟨fun y => H (x + y), H.continuous.comp (continuous_const.add continuous_id)⟩
    letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
    (∀ E : Set C(Vec d, ℝ), MeasurableSet E →
      (∀ x : Vec d, ∀ᵐ H ∂seedFieldLaw P, shift x H ∈ E ↔ H ∈ E) →
      seedFieldLaw P E = 0 ∨ seedFieldLaw P E = 1) ∧
    (∀ F : C(Vec d, ℝ) → ℝ, Measurable F →
      (∀ x : Vec d, ∀ᵐ H ∂seedFieldLaw P, F (shift x H) = F H) →
      ∃ c : ℝ, ∀ᵐ H ∂seedFieldLaw P, F H = c)

end EinsteinFull.Blueprint
