import EinsteinRelation.Environment.Basic
import EinsteinRelation.Environment.Reduction
import EinsteinRelation.Frozen.ValidAnnealedLawCarriers.CoordinatePathLawInput
import EinsteinRelation.Frozen.DensityCarriers.ReducedLaplaceObservedLaw

open MeasureTheory
open EinsteinRelation.Frozen.ValidAnnealedLawCarriers

noncomputable section

namespace EinsteinRelation.Frozen.DensityCarriers

/-- A nonnegative measurable density `rho` of the reduced Laplace-time law
`reducedLaplaceObservedLaw I s` with respect to the reduced reference law of the
environment law `I.Q`, which is `Measure.map reduce I.Q`, the body of `reducedReferenceLaw`
(source: `paper/main.tex:198-208` for `reduce`, `237-240` for the reduced canonical space,
`431-437` for `ρ_s` as the density of the law of the environment at an exponential time). -/
def IsReducedLaplaceDensity {d : ℕ} {hd : 2 ≤ d}
    (I : CoordinatePathLawInput d hd) (s : {r : ℝ // 0 < r}) (rho : FieldPair d → ℝ) : Prop :=
  Measurable rho ∧ (∀ w, 0 ≤ rho w) ∧
    reducedLaplaceObservedLaw I s =
      (Measure.map EinsteinRelation.reduce I.Q).withDensity (fun w => ENNReal.ofReal (rho w))

end EinsteinRelation.Frozen.DensityCarriers
