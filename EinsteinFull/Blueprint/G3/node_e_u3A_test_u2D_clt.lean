import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ScaledJointPairing
import EinsteinFull.Frozen.SchwartzTestNorm

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:test-clt`, `paper/main.tex:887–896`.
The joint field is the literal frozen commutator and centered clock. The
constant precedes the law, scale and complex Schwartz test. The same bound
therefore includes real tests; the Euclidean test norm is the frozen one. -/
def node_e_u3A_test_u2D_cltStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (D : StructuralData d)
    (N : ℕ), 2 * d + 10 < N →
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
        HasSmoothBounds D Q →
        ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q),
          IsJointObservation Q Z →
          ∀ (R : ℝ) (hR : 1 ≤ R)
            (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))),
            ‖scaledJointPairing Q R (by linarith) Z F‖ ≤ C * schwartzTestNorm N F

end EinsteinFull.Blueprint
