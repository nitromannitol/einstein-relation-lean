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

/-- Graph node `sharp.example#smooth-seed`, `paper/main.tex:1528–1533`.
The canonical admissible choice K = zeta = mollifierNoiseTest is fixed before
the noise law. The scale is the adopted deterministic seedScale; finite range
is joint independence of whole seed evaluation processes. -/
def node_sharp_u2E_example_u23_smooth_u2D_seedStmt : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d) (P : Measure (NoiseSample d)),
    External.IsWhiteNoiseLaw P →
    let shift : Vec d → C(Vec d, ℝ) → C(Vec d, ℝ) := fun x H =>
      ⟨fun y => H (x + y), H.continuous.comp (continuous_const.add continuous_id)⟩
    (∀ (W : NoiseSample d), ContDiff ℝ (⊤ : ℕ∞) (seedField d W)) ∧
    (∀ x : Vec d, Integrable (fun W => seedField d W x) P ∧
      (∫ W, seedField d W x ∂P) = 0) ∧
    (∀ x : Vec d, (seedFieldLaw P).map (shift x) = seedFieldLaw P) ∧
    (∀ (S T : Type) (xs : S → Vec d) (ys : T → Vec d),
      (∀ s t, 4 < euclideanNorm (xs s - ys t)) →
      ProbabilityTheory.IndepFun (fun W => fun s => seedField d W (xs s))
        (fun W => fun t => seedField d W (ys t)) P) ∧
    (∀ k : List (Fin d), ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : NoiseSample d) (x : Vec d),
      |iteratedCoordinateDerivative k (seedField d W) x| ≤ C) ∧
    0 < EinsteinFull.Work.W8.seedScale d ∧
    (∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (EinsteinFull.Work.W8.corrector W) x) ≤ (1 / 4 : ℝ))

end EinsteinFull.Blueprint
