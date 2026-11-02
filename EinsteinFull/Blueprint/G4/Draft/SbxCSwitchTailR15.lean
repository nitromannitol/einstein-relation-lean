import EinsteinFull.Blueprint.G4.Draft.SbxCTailCanonicalEdgesR13

/-! Conditional full-range tail summation for the Section 3 switch. -/

namespace EinsteinFull.Blueprint.SbxCSwitchTailR15

/-- The endpoint, annular, and uniform local mixing inputs imply full-range summation. -/
theorem tailSum_of_deps
    (hsmall : node_p_u3A_tail_u23_small_u2D_endpointsStmt)
    (hann : node_p_u3A_tail_u23_annuliStmt)
    (hLM : SbxCLocalMixingUniformR06.localMixingUniformFullRangeSmoothStmt) :
    SbxS6TailSumFullRangeR02.tailSumFullRangeStmt :=
  SbxCTailCanonicalEdgesR13.tail_sum_full_range_of_uniform_nodes hsmall hann hLM

end EinsteinFull.Blueprint.SbxCSwitchTailR15
