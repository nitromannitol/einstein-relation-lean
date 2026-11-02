import EinsteinFull.Frozen.EndpointIndex
import Mathlib.Data.Real.Basic

namespace EinsteinFull

/-- The transpose equation has drift -zeta, the velocity and clock equations +zeta. -/
def endpointDriftSign {d : ℕ} (ν : EndpointIndex d) : ℝ :=
  match ν with
  | .inr true => -1
  | _ => 1

end EinsteinFull
