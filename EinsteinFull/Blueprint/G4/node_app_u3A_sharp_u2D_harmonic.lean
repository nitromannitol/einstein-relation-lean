import EinsteinFull.Work.W8.SharpnessConstructionSupport
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.HomogenizedCoefficient

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

/-- Graph node `app:sharp-harmonic`, `paper/main.tex:1543–1552`.
The actual constructed harmonic coordinate has constant signed generator.
The reduced velocity conclusion is for each fixed nonzero force and actual
quenched martingale-problem kernel, with no strong-law premise. -/
def node_app_u3A_sharp_u2D_harmonicStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d)),
    External.IsWhiteNoiseLaw P →
    let first : Fin d := ⟨0, by omega⟩
    ∀ (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      Q.measure = P.map (EinsteinFull.Work.W8.physicalPair first) →
      (∀ (W : NoiseSample d) (x : Vec d),
        let ψ := EinsteinFull.Work.W8.corrector W
        let ω := EinsteinFull.Work.W8.physicalPair first W
        let J := jacobian first (gradient ψ x)
        J.mulVec (unitVector first) = J.det • unitVector first ∧
        J.transpose.mulVec (unitVector first) = unitVector first + gradient ψ x ∧
        (reducedCoefficient ω x).mulVec (unitVector first + gradient ψ x) =
          unitVector first ∧
        ∀ lam : ℝ, reducedGenerator first ω lam (fun y => y first + ψ y) x = lam) ∧
      (homogenizedCoefficient Q).mulVec (unitVector first) = unitVector first ∧
      (∀ (X : DiffusionFamily d), IsSignedPhysicalFamily first Q X →
        ∀ covariance : Mat d, HasDiffusivity Q.measure (originLaw (X 0)) covariance →
          covariance.mulVec (unitVector first) = unitVector first) ∧
      ∀ (lam : ℝ), lam ≠ 0 → ∀ Y : QuenchedPathLaws d,
        (∀ᵐ ω ∂Q.measure,
          SolvesMartingaleProblem (reducedGenerator first ω lam) 0 (Y (0, ω))) →
        ∃ ell : Vec d, HasQuenchedVelocity Q.measure (originLaw Y) ell ∧ ell first = lam

end EinsteinFull.Blueprint
