import EinsteinFull.Work.W8.SharpnessConstructionSupport
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.HomogenizedCoefficient

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

/-- Graph node `app:sharp-fields`, `paper/main.tex:1534–1541`.
The adopted fixed positive delta precedes structural data and the actual
joint physical pushforward law. EnvironmentLaw retains joint finite range. -/
def node_app_u3A_sharp_u2D_fieldsStmt : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d),
    let first : Fin d := ⟨0, by omega⟩
    0 < EinsteinFull.Work.W8.clockParameter first ∧
    (∀ (W : NoiseSample d) (x : Vec d),
      let ψ := EinsteinFull.Work.W8.corrector W
      let δ := EinsteinFull.Work.W8.clockParameter first
      let ω := EinsteinFull.Work.W8.physicalPair first W
      let J := jacobian first (gradient ψ x)
      reducedCoefficient ω x = J.det • (J⁻¹ * (J⁻¹).transpose) ∧
      clockDensity ω x = 1 + δ / 2 *
        divergence (fun y => (reducedCoefficient ω y).mulVec (unitVector first)) x ∧
      (3 / 4 : ℝ) ≤ clockDensity ω x ∧ clockDensity ω x ≤ (5 / 4 : ℝ) ∧
      ω.1 x = (clockDensity ω x)⁻¹ • reducedCoefficient ω x ∧
      ω.2 x = -(1 / 2 : ℝ) * Real.log (clockDensity ω x)) ∧
    ∃ D : StructuralData d,
      (∀ W : NoiseSample d, IsSmoothWithBounds D.derivativeBound
        (EinsteinFull.Work.W8.physicalPair first W)) ∧
      (∀ W : NoiseSample d, IsElliptic D.ellipticity
        (reducedCoefficient (EinsteinFull.Work.W8.physicalPair first W))) ∧
      (∀ k : List (Fin d), ∃ C : ℝ, 0 ≤ C ∧
        ∀ (W : NoiseSample d) (x : Vec d),
          |iteratedCoordinateDerivative k
            (fun y => clockDensity (EinsteinFull.Work.W8.physicalPair first W) y) x| ≤ C ∧
          ∀ i j : Fin d, |iteratedCoordinateDerivative k
            (fun y => reducedCoefficient (EinsteinFull.Work.W8.physicalPair first W) y i j) x| ≤ C) ∧
      ∀ P : Measure (NoiseSample d), External.IsWhiteNoiseLaw P →
      ∃ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        Q.measure = P.map (EinsteinFull.Work.W8.physicalPair first) ∧
        HasSmoothBounds D Q ∧
        (∫ ω, clockDensity ω 0 ∂Q.measure) = 1

end EinsteinFull.Blueprint
