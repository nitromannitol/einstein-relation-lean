import EinsteinFull.Work.W8.SharpnessConstructionSupport
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.HomogenizedCoefficient

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

/-- Graph node `sharp.example#clock-continuity`, `paper/main.tex:1565–1565`.
The actual long-time average is taken first at each positive force.
Only afterwards is its right-hand force limit taken. The replacement-pair
admissibility and clock expansion are internal graph dependencies. -/
def node_sharp_u2E_example_u23_clock_u2D_continuityStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d)),
    External.IsWhiteNoiseLaw P →
    let first : Fin d := ⟨0, by omega⟩
    ∀ (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      Q.measure = P.map (EinsteinFull.Work.W8.physicalPair first) →
      ∀ Y : DiffusionFamily d,
        (∀ (lam : ℝ), 0 < lam → ∀ᵐ ω ∂Q.measure,
          SolvesMartingaleProblem (reducedGenerator first ω lam) 0 (Y lam (0, ω))) →
        ∃ avg : ℝ → ℝ,
          (∀ (lam : ℝ), 0 < lam → ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw (Y lam) ω,
            Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
              reducedCoefficient ω (γ u.toNNReal) first first) atTop (𝓝 (avg lam))) ∧
          Tendsto avg (𝓝[>] (0 : ℝ))
            (𝓝 (∫ ω, reducedCoefficient ω 0 first first ∂Q.measure))

end EinsteinFull.Blueprint
