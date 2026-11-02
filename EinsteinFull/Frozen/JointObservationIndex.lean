import Mathlib.Data.Fin.Basic

namespace EinsteinFull

/-- Indices for the d-by-d commutator and the one clock coordinate. -/
abbrev JointObservationIndex (d : ℕ) := (Fin d × Fin d) ⊕ Unit

end EinsteinFull
