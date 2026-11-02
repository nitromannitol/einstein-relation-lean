import Mathlib.Data.Fin.Basic

namespace EinsteinFull

/-- Indices for velocity endpoints (inl i), transpose (inr true), and clock (inr false). -/
abbrev EndpointIndex (d : ℕ) := Fin d ⊕ Bool

end EinsteinFull
