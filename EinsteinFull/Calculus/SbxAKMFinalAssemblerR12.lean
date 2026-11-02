import EinsteinFull.Calculus.SbxACouplingFromSetwiseR11
import EinsteinFull.Calculus.SbxAKMSignedAssemblyR11
import EinsteinFull.Blueprint.G1.Draft.SbxCSwitchContractsR17

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint

/-- The signed k/m contract from its predecessors and all-regular setwise domination. -/
theorem a_km_decomp_of_deps_and_setwise_r12
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmtV4)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmtV2)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
    (hsetwise : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ),
      ∀ l : ℝ, 1 ≤ l → ∃ c : ℝ, 0 < c ∧
      ∀ (Q : EnvironmentLaw d Λ r),
      ∀ (μ : ℝ) (h0 : 0 < μ) (h1 : μ ≤ 1),
        ∃ P : QuenchedPathLaws d,
          IsGMPReducedKernel hd Q.ellipticity_parameter Q μ h0.le h1 P ∧
          ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
            ENNReal.ofReal (c * μ ^ d) •
              (volume : Measure (Vec d)).restrict
                (endpointBall (Renewal.forceCoord hd) (l / μ) x) ≤
            ((P (x, ω)).restrict {γ | ∀ t : ℝ≥0, t ≤ Renewal.regenDelta μ →
              γ t ∈ couplingRegion (Renewal.forceCoord hd) (l / μ) x}).map
                (fun γ => γ (Renewal.regenDelta μ))) :
    node_rt_u3A_km_u2D_decompStmtV4 := by
  exact SbxAKMSignedAssemblyR11.a_uniform_km_of_exact_predecessors_and_actual_couplings
    hfactor hphase hmany hrem
    (Calculus.SbxACouplingFromSetwiseR11.a_uniform_actual_coupling_half_mass_of_setwise hsetwise)

end EinsteinFull.Blueprint

