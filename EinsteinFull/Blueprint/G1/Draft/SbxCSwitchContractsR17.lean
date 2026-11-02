import EinsteinFull.Blueprint.G1.Draft.SbxCManyCycleUniformR06
import EinsteinFull.Blueprint.G1.Draft.SbxCMRenewalUniformR06
import EinsteinFull.Blueprint.G1.Draft.SbxCFixedRadiusUniformR07
import EinsteinFull.Blueprint.G1.Draft.SbxCPhaseUniformR07
import EinsteinFull.Blueprint.G4.Draft.SbxS6TailSumFullRangeR02
import EinsteinFull.Blueprint.G1.Draft.SbxCLocalMixingUniformR06

/-! Canonical names for the reviewed Section 3 switch contracts. -/

namespace EinsteinFull.Blueprint

/-- Many-cycle moment contract, `SbxCManyCycleUniformR06.lean:13`;
review `scope-repair-20261101-s3-consumers`, `rt:many-cycle-moment`. -/
def node_rt_u3A_many_u2D_cycle_u2D_momentStmtV2 : Prop :=
  SbxCManyCycleUniformR06.manyCycleSmoothStmt

/-- m-renewal contract, `SbxCMRenewalUniformR06.lean:14`;
review `scope-repair-20261101-s3-consumers`, `rt:m-renewal`. -/
def node_rt_u3A_m_u2D_renewalStmtV2 : Prop :=
  SbxCMRenewalUniformR06.phaseMRenewalSmoothStmt

/-- Fixed-radius contract, `SbxCFixedRadiusUniformR07.lean:96`;
review `scope-repair-20261101-s3-consumers`, `rt:local-mixing#fixed-radius`. -/
def node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radiusStmtV4 : Prop :=
  SbxCFixedRadiusUniformR07.fixedRadiusUniformStmtV3

/-- Phase-error contract, `SbxCPhaseUniformR07.lean:60`;
review `scope-repair-20261101-s3-consumers`, `rt:local-mixing#phase-error`. -/
def node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmtV4 : Prop :=
  SbxCPhaseUniformR07.phaseUniformStmt

/-- Full-range tail summation, `SbxS6TailSumFullRangeR02.lean:36`;
review `scope-repair-20261101-s3-smooth-freeze`, `p:tail#sum`. -/
def node_p_u3A_tail_u23_sumStmtV2 : Prop :=
  SbxS6TailSumFullRangeR02.tailSumFullRangeStmt

/-- Full-range k/m decomposition contract, `SbxCLocalMixingUniformR06.lean:10`;
review `scope-repair-20261101-s3-consumers`, `rt:km-decomp`.
Its coupling and signed decomposition producer remains open. -/
def node_rt_u3A_km_u2D_decompStmtV4 : Prop :=
  SbxCLocalMixingUniformR06.kmDecompUniformFullRangeSmoothStmt

end EinsteinFull.Blueprint
