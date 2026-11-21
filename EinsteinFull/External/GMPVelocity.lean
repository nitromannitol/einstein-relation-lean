import EinsteinFull.External.Draft.GMPVelocity
import EinsteinFull.Regeneration.GMPVelocityProof

namespace EinsteinFull.External

/-- Reviewed GMP positive small-force quenched velocity law and strict positive
force projection, for the source physical origin process, proved in
`EinsteinFull.Regeneration.GMPVelocityProof` as `gmp_velocity_holds`. This exact source
alias retains translation ergodicity and the source force range. The internal
regeneration ratio and signed/reduced-process transfers are not inputs.
Direct-PDF evidence: literature-gmp-velocity-v1. -/
theorem gmp_velocity : EinsteinFull.External.Draft.gmpVelocityStmt :=
  gmp_velocity_holds

end EinsteinFull.External
