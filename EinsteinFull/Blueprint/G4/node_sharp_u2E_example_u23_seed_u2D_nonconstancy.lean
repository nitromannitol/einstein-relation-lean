import EinsteinFull.Work.W8.SharpnessConstructionSupport
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.HomogenizedCoefficient

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

/-- Graph node `sharp.example#seed-nonconstancy`, `paper/main.tex:1529–1529`.
Nondegeneracy and positive variance concern the same literal two-stage
convolution as smooth-seed, under a supplied Gaussian white-noise law. -/
def node_sharp_u2E_example_u23_seed_u2D_nonconstancyStmt : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d) (P : Measure (NoiseSample d)),
    External.IsWhiteNoiseLaw P →
    (¬ ∃ c : ℝ, ∀ᵐ W ∂P, seedField d W 0 = c) ∧
    (¬ ∀ᵐ W ∂P, ∀ x : Vec d, seedField d W x = seedField d W 0) ∧
    0 < ∫ W, (seedField d W 0 - ∫ U, seedField d U 0 ∂P) ^ 2 ∂P

end EinsteinFull.Blueprint
