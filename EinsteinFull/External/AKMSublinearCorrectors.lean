import EinsteinFull.External.Draft.AKMSublinearCorrectorsV2
import EinsteinFull.Homogenization.SourceCorrectorSublinear

namespace EinsteinFull.External

/-- Exact source-reviewed AKM Lemma 3.17 / Proposition 6.2, proved in
`EinsteinFull.Homogenization.SourceCorrectorSublinear` as `akmSublinearCorrectorsStmtV2_holds`.
All stationary, horizontal, smooth and complex-force applications remain internal. -/
theorem akm_sublinear_correctors : EinsteinFull.External.Draft.akmSublinearCorrectorsStmtV2 :=
  akmSublinearCorrectorsStmtV2_holds

end EinsteinFull.External
