import EinsteinFull.Work.W8.SharpnessConstructionSupport
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.HomogenizedCoefficient

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

/-- Graph node `sharp.example#positive-coefficient`, `paper/main.tex:1567–1572`.
The coefficient is the literal positive seed-gradient energy for this law.
No positive uniform lower bound over laws is asserted. The physical response
uses the exact frozen right-hand sharpness normalization. -/
def node_sharp_u2E_example_u23_positive_u2D_coefficientStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d)),
    External.IsWhiteNoiseLaw P →
    let first : Fin d := ⟨0, by omega⟩
    ∀ (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      Q.measure = P.map (EinsteinFull.Work.W8.physicalPair first) →
      (∀ (W : NoiseSample d) (x : Vec d),
        let ψ := EinsteinFull.Work.W8.corrector W
        reducedCoefficient (EinsteinFull.Work.W8.physicalPair first W) x first first =
          1 - gradient ψ x first + euclideanSq (gradient ψ x) / (1 + gradient ψ x first)) ∧
      (∫ W, gradient (EinsteinFull.Work.W8.corrector W) 0 first ∂P) = 0 ∧
      let δ := EinsteinFull.Work.W8.clockParameter first
      let c₀ := δ * ∫ W, euclideanSq (gradient (EinsteinFull.Work.W8.corrector W) 0) /
        (1 + gradient (EinsteinFull.Work.W8.corrector W) 0 first) ∂P
      0 < c₀ ∧
      c₀ = δ * ((∫ ω, reducedCoefficient ω 0 first first ∂Q.measure) - 1) ∧
      ∀ X : DiffusionFamily d, IsSignedPhysicalFamily first Q X →
        ∀ covariance : Mat d, HasDiffusivity Q.measure (originLaw (X 0)) covariance →
        ∀ velocity : ℝ → Vec d,
          (∀ (lam : ℝ), 0 < lam →
            HasQuenchedVelocity Q.measure (originLaw (X lam)) (velocity lam)) →
          Tendsto (fun lam : ℝ =>
            dot ((lam⁻¹ • velocity lam) - covariance.mulVec (unitVector first))
              (unitVector first) / lam) (𝓝[>] (0 : ℝ)) (𝓝 c₀)

end EinsteinFull.Blueprint
