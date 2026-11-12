import EinsteinRelation.Calculus.HorizontalTranslationPrimitive
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # Coordinate translation paths for the small-scale flux

Source: `paper/main.tex:1021–1029`. Coordinate segments give a concrete
local primitive for the translation difference used in the residual flux.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation

/-- The first `k` coordinates of a displacement (`paper/main.tex:1021–1029`). -/
def coordinatePrefix {d : ℕ} (z : Vec d) (k : ℕ) : Vec d :=
  fun j => if j.val < k then z j else 0

/-- The `i`th coordinate segment of the displacement path
(`paper/main.tex:1021–1029`). -/
def coordinateSegment {d : ℕ} (z : Vec d) (i : Fin d) (t : ℝ) : Vec d :=
  coordinatePrefix z i.val + t • unitVector i

/-- A literal orbit primitive along each segment of the coordinate path
(`paper/main.tex:1021–1029`). -/
def coordinatePathFlux {d : ℕ} (f : FieldPair d → ℝ) (z : Vec d)
    (ω : FieldPair d) : Vec d :=
  fun i => ∫ t in (0 : ℝ)..z i, f (translate (coordinateSegment z i t) ω)

end EinsteinRelation
