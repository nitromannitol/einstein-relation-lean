import EinsteinRelation.Environment.Basic

namespace EinsteinFull

/-- The deterministic data in Section 1, including the dimension parameter; the derivative sequence is indexed
by natural numbers and its zeroth value is unused. -/
structure StructuralData (dimension : ℕ) where
  ellipticity : ℝ
  dependenceRange : ℝ
  derivativeBound : ℕ → ℝ
  one_le_ellipticity : 1 ≤ ellipticity
  one_le_dependenceRange : 1 ≤ dependenceRange
  derivativeBound_pos : ∀ k : ℕ, 1 ≤ k → 0 < derivativeBound k

end EinsteinFull
