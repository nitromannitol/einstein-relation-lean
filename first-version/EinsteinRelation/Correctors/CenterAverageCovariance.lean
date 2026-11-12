import EinsteinRelation.Calculus.HorizontalSobolev
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Local corrector center averaging

Source: `paper/main.tex:926–938`.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:926–938`. Translation of a covariant family
and the center integration variable makes its weighted average an orbit
of its value at the origin. -/
theorem centerAverage_eq_orbit {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (w : Vec d → ℝ) (u : Vec d → Vec d → FieldPair d → E)
    (hcov : ∀ (y x : Vec d) (ω : FieldPair d),
      u (x + y) x ω = u y 0 (translate x ω)) (x : Vec d) (ω : FieldPair d) :
    (∫ y, w (x - y) • u y x ω ∂volume) =
      (∫ y, w (0 - y) • u y 0 (translate x ω) ∂volume) := by
  rw [← integral_add_left_eq_self (fun y => w (x - y) • u y x ω) x]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [hcov]
    congr 1
    abel_nf

/-- Translating a single center-zero local version supplies exact covariance
before center averaging. Source: `paper/main.tex:913–938`. -/
theorem centerAverage_translatedField_eq_orbit {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : Vec d → ℝ) (F : Vec d → FieldPair d → E) (x : Vec d) (ω : FieldPair d) :
    (∫ y, w (x - y) • F (x - y) (translate y ω) ∂volume) =
      (∫ y, w (0 - y) • F (0 - y) (translate y (translate x ω)) ∂volume) := by
  apply centerAverage_eq_orbit w (fun y z a => F (z - y) (translate y a)) _ x ω
  intro y z a
  dsimp only
  rw [translate_add, add_comm y z]
  congr 1
  abel_nf

end EinsteinRelation.Correctors
