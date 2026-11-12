import EinsteinRelation.Correctors.LocalCorrectorFieldAssembly
import EinsteinRelation.Correctors.CenterAverageCovariance
import EinsteinRelation.Correctors.LocalMollifierSpatialTest

/-! # Common fields obtained by translating the center-zero versions

Source: `paper/main.tex:913–938`. The same center-zero scalar, gradient and
skew versions define all five fields. Coordinate integrals retain the actual
Euclidean and Frobenius norms in subsequent estimates.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The five literal center averages at the origin, obtained from one set
of center-zero versions. Source: `paper/main.tex:921–938`. -/
noncomputable def centeredMollifierFields {d : ℕ} (R : ℝ)
    (u : FieldPair d → Vec d → ℝ) (G : FieldPair d → Vec d → Vec d)
    (S : FieldPair d → Vec d → Mat d) : LocalCorrectorFields d where
  scalar ω := ∫ y, Calculus.unitMassScaledMollifier d R (-y) * u (translate y ω) (-y)
  skew ω j k := ∫ y, Calculus.unitMassScaledMollifier d R (-y) * S (translate y ω) (-y) j k
  gradientAverage ω j := ∫ y,
    Calculus.unitMassScaledMollifier d R (-y) * G (translate y ω) (-y) j
  scalarCorrection ω j := ∫ y,
    u (translate y ω) (-y) * coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y)
  skewCorrection ω j := ∫ y,
    ((S (translate y ω) (-y)).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (-y))) j

/-- Translation of the center variable identifies every field with the
corresponding spatial average. Source: `paper/main.tex:926–938`. -/
theorem centeredMollifierFields_translate {d : ℕ} (R : ℝ)
    (u : FieldPair d → Vec d → ℝ) (G : FieldPair d → Vec d → Vec d)
    (S : FieldPair d → Vec d → Mat d) (x : Vec d) (ω : FieldPair d) :
    let f := centeredMollifierFields R u G S
    f.scalar (translate x ω) =
        ∫ y, Calculus.unitMassScaledMollifier d R (x - y) * u (translate y ω) (x - y) ∧
    (∀ j k, f.skew (translate x ω) j k =
        ∫ y, Calculus.unitMassScaledMollifier d R (x - y) * S (translate y ω) (x - y) j k) ∧
    (∀ j, f.gradientAverage (translate x ω) j =
        ∫ y, Calculus.unitMassScaledMollifier d R (x - y) * G (translate y ω) (x - y) j) ∧
    (∀ j, f.scalarCorrection (translate x ω) j =
        ∫ y, u (translate y ω) (x - y) *
          coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (x - y)) ∧
    (∀ j, f.skewCorrection (translate x ω) j =
        ∫ y, ((S (translate y ω) (x - y)).mulVec
          (gradient (Calculus.unitMassScaledMollifier d R) (x - y))) j) := by
  have h (w : Vec d → ℝ) (F : Vec d → FieldPair d → ℝ) :
      (∫ y, w (-y) * F (-y) (translate y (translate x ω))) =
        ∫ y, w (x - y) * F (x - y) (translate y ω) := by
    simpa only [zero_sub, smul_eq_mul] using
      (centerAverage_translatedField_eq_orbit w F x ω).symm
  refine ⟨h _ (fun z a => u a z), fun j k => h _ (fun z a => S a z j k),
    fun j => h _ (fun z a => G a z j), fun j => ?_, fun j => ?_⟩
  · simpa only [mul_comm] using h (coordinateDerivative j (Calculus.unitMassScaledMollifier d R))
      (fun z a => u a z)
  · change (∫ y, ((S (translate y (translate x ω)) (-y)).mulVec
        (gradient (Calculus.unitMassScaledMollifier d R) (-y))) j) = _
    rw [← integral_add_left_eq_self (fun y =>
      ((S (translate y ω) (x - y)).mulVec
        (gradient (Calculus.unitMassScaledMollifier d R) (x - y))) j) x]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only
      rw [show x - (x + y) = -y by abel, translate_add, add_comm x y]

end EinsteinRelation.Correctors
