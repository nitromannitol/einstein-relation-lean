import EinsteinFull.Blueprint.Roots.Draft.SbxCTailRootR01
import EinsteinFull.Blueprint.G1.Draft.SbxCLocalMixingUniformR06

/-! Conditional full-range tail summation from uniform local mixing. -/

namespace EinsteinFull.Blueprint.SbxCTailCanonicalEdgesR13

/-- Uniform full-range local mixing combines with the endpoint and annular inputs. -/
theorem tail_sum_full_range_of_uniform_nodes
    (hsmall : node_p_u3A_tail_u23_small_u2D_endpointsStmt)
    (hann : node_p_u3A_tail_u23_annuliStmt)
    (hLM : SbxCLocalMixingUniformR06.localMixingUniformFullRangeSmoothStmt) :
    SbxS6TailSumFullRangeR02.tailSumFullRangeStmt :=
  tail_sum_full_range_of_canonical_local_mixing hsmall hann
    (SbxCLocalMixingUniformR06.localMixingFullRange_of_uniform hLM)

end EinsteinFull.Blueprint.SbxCTailCanonicalEdgesR13
