import EinsteinFull.Blueprint.G4.Draft.SbxS6TailSumFullRangeR02
import EinsteinFull.Blueprint.G1.Draft.SbxS6LocalMixingFullRangeR02

/-! Conditional full-range tail assembly. The predecessor is a draft interface. -/

namespace EinsteinFull.Blueprint

/-- The full-range summation implies the unchanged tail statement. -/
theorem node_p_u3A_tail_of_deps
    (hsum : SbxS6TailSumFullRangeR02.tailSumFullRangeStmt) : node_p_u3A_tailStmt :=
  SbxS6TailSumFullRangeR02.tail_of_full_range_sum hsum

/-- The endpoint and annular inputs combine with canonical full-range local mixing. -/
theorem tail_sum_full_range_of_canonical_local_mixing
    (hsmall : node_p_u3A_tail_u23_small_u2D_endpointsStmt)
    (hann : node_p_u3A_tail_u23_annuliStmt)
    (hlm : SbxS6Section3R02.localMixingFullRangeSmoothStmt) :
    SbxS6TailSumFullRangeR02.tailSumFullRangeStmt :=
  SbxS6TailSumFullRangeR02.tail_sum_full_range_of_local_mixing hsmall hann hlm

end EinsteinFull.Blueprint
