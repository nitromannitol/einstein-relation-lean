import EinsteinFull.Work.W8.SharpnessConstructionSupport
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.HomogenizedCoefficient

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

/-- Graph node `app:sharp-clock`, `paper/main.tex:1554–1564`.
The deterministic average is concluded from the actual clock and the bounded
corrector occupation identity. There is no invariant steady-state assumption. -/
def node_app_u3A_sharp_u2D_clockStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d)),
    External.IsWhiteNoiseLaw P →
    let first : Fin d := ⟨0, by omega⟩
    ∀ (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      Q.measure = P.map (EinsteinFull.Work.W8.physicalPair first) →
      (∀ (W : NoiseSample d) (x : Vec d) (lam : ℝ),
        let ψ := EinsteinFull.Work.W8.corrector W
        let ω := EinsteinFull.Work.W8.physicalPair first W
        dot ((reducedCoefficient ω x).mulVec (unitVector first)) (gradient ψ x) =
          1 - reducedCoefficient ω x first first ∧
        reducedGenerator first ω lam ψ x =
          (1 - clockDensity ω x) / EinsteinFull.Work.W8.clockParameter first +
            lam * (1 - reducedCoefficient ω x first first)) ∧
      ∀ (lam : ℝ), lam ≠ 0 → ∀ Y : QuenchedPathLaws d,
        (∀ᵐ ω ∂Q.measure,
          SolvesMartingaleProblem (reducedGenerator first ω lam) 0 (Y (0, ω))) →
        ∃ η avg : ℝ, HasReducedClockRate Q Y η ∧
          η = 1 - EinsteinFull.Work.W8.clockParameter first * lam * (avg - 1) ∧
          (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω,
            Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
              reducedCoefficient ω (γ u.toNNReal) first first) atTop (𝓝 avg)) ∧
          (∀ᵐ W ∂P,
            ∀ᵐ γ ∂originLaw Y (EinsteinFull.Work.W8.physicalPair first W),
              Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
                reducedGenerator first (EinsteinFull.Work.W8.physicalPair first W) lam
                  (EinsteinFull.Work.W8.corrector W) (γ u.toNNReal)) atTop (𝓝 0))

end EinsteinFull.Blueprint
