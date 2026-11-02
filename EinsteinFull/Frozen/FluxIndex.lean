import Mathlib.Data.Fin.Basic

namespace EinsteinFull

/-- Velocity flux columns (inl i) and the transpose flux (inr unit). -/
abbrev FluxIndex (d : ℕ) := Fin d ⊕ Unit

end EinsteinFull
