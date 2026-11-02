import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.LatticeConvolutionPower
import EinsteinFull.Work.W5.UniformLatticeRenewalProof
import EinsteinFull.Work.W5.RenewalNearOneSupport

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation
open EinsteinFull.Work.W5

/-- Graph node `rt:factorization#small-indices`, `paper/main.tex:329–341`.
The first possible regeneration time is at least two grid steps, so the
actual n=0 and n=1 slice is empty. This proves vacuity for either measure
without a finiteness, independence or positive no-return assumption. -/
def node_rt_u3A_factorization_u23_small_u2D_indicesStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (lam l : ℝ), 0 < lam → 0 < l →
    ∀ n : ℕ, n ≤ 1 →
      {ωz : FieldPair d × Regeneration.CoupledSample d |
        regenerationTime hd lam l 1 ωz.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} = ∅

end EinsteinFull.Blueprint
