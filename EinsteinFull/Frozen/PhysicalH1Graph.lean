import EinsteinFull.Frozen.PhysicalForceMeasure
import EinsteinRelation.Calculus.Weak
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic

open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- The full complex physical H1 graph: L2 classes whose actual representatives
have the displayed distributional derivatives. The reference weak derivative
is with respect to dx. The public reference measure is Lebesgue measure or
one of the source physical gauge measures; arbitrary singular measures are excluded. -/
def IsPhysicalH1Graph {d : ℕ} (m : Measure (Vec d))
    (_hm : m = volume ∨ ∃ (i : Fin d) (lam : ℝ), m = physicalForceMeasure i lam)
    (u : Lp ℂ 2 m) (G : Fin d → Lp ℂ 2 m) : Prop :=
  (∀ j : Fin d, HasWeakPartialDerivative Set.univ j
    (fun x => (u x).re) (fun x => (G j x).re)) ∧
  (∀ j : Fin d, HasWeakPartialDerivative Set.univ j
    (fun x => (u x).im) (fun x => (G j x).im))

end EinsteinFull
