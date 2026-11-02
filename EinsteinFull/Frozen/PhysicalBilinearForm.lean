import EinsteinFull.Frozen.PhysicalH1Graph
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open scoped ENNReal
open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- The literal bilinear shifted-gradient form. At real force its value on
(conjugate u,u) is the Hermitian energy. Complex force continues both shifts
bilinearly, so no conjugate force enters. L2 arguments and L infinity
coefficients make both integrands genuinely integrable on the entire domain. -/
noncomputable def physicalBilinearForm {d : ℕ} (m : Measure (Vec d))
    (a : Vec d → Mat d)
    (_ha : ∀ j k : Fin d, MemLp (fun x => (a x j k : ℂ)) ∞ m) (i : Fin d) (s : ℝ) (ζ : ℂ)
    (u : Lp ℂ 2 m) (G : Fin d → Lp ℂ 2 m)
    (v : Lp ℂ 2 m) (H : Fin d → Lp ℂ 2 m) : ℂ :=
  (s : ℂ) * (∫ x, u x * v x ∂m) + (1 / 2 : ℂ) *
    ∫ x, ∑ j : Fin d, ∑ k : Fin d,
      (G j x - ζ * (unitVector i j : ℂ) * u x) * (a x j k : ℂ) *
      (H k x - ζ * (unitVector i k : ℂ) * v x) ∂m

end EinsteinFull
