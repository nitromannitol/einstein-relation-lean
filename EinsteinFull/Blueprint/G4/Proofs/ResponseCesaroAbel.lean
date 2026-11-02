import EinsteinFull.Calculus.C5ResponseClockWitness
import EinsteinFull.Calculus.C5ResponseObservationAbel
import EinsteinFull.Calculus.C9ResponsePathTransport
import EinsteinFull.Calculus.C16FoundationInstantiation
import EinsteinFull.Calculus.S4SmoothGeneratorSupport
import EinsteinFull.Blueprint.G4.node_p_u3A_response_u23_core_u2D_extension

/-!
# Cesàro and Abel limits of the response observations

`p:response#cesaro-abel` from the smooth-scope time-change identities and real-force
semigroup. On a smooth environment the reduced martingale problem is the textbook one,
whose positive-time occupation measure is absolutely continuous. This gives the null
occupation that identifies the semigroup means with the path expectations.
-/

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

/-- On environments with smooth bounds, every reduced law spends almost no positive time
in a Lebesgue-null set. -/
theorem response_null_occupation_of_smooth {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) :
    ∀ᵐ ω ∂Q.measure, ∀ N : Set (Vec d), MeasurableSet N →
      (volume : Measure (Vec d)) N = 0 →
      ∀ᵐ γ ∂Y (0, ω), ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        γ t.toNNReal ∉ N := by
  filter_upwards [Q.regular, hQ, hY] with ω hω hsm hYω
  have hocc := foundation_reduced_textbook_averaged_occupation_ac_of_two_le hd
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter) hω (⟨0, by omega⟩ : Fin d) lam
    ((reducedGenerator_solves_iff hsm.1 _ lam 0 (Y (0, ω))).1 hYω)
  intro N _hN hNzero
  apply c16_ae_path_of_averaged_occupation (Y (0, ω)) hocc (p := fun x => x ∉ N)
  exact ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hNzero)

/-- `p:response#cesaro-abel`. The velocity and clock rate of the supplied law come from
the time-change identities; the semigroup path expectations and the null occupation turn
them into Cesàro limits, and the uniform observation bounds give the Abel limits. The
core-extension premise is retained in graph order. -/
@[nolint unusedArguments]
theorem node_p_u3A_response_u23_cesaro_u2D_abel_of_deps
    (h0 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (_h1 : node_p_u3A_response_u23_core_u2D_extensionStmt)
    (h2 : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2) :
    node_p_u3A_response_u23_cesaro_u2D_abelStmt := by
  classical
  intro d hd D Q hQ β a μ hβ ha hμ lam hlam P hP Y hY
  choose Y₀ hY₀ using fun l : ℝ =>
    c16_reduced_mp_exists d hd D.ellipticity D.dependenceRange Q (⟨0, by omega⟩ : Fin d) l
  have hocc := response_null_occupation_of_smooth hd D Q hQ lam Y hY
  obtain ⟨velocity, η, hv, hη, hclockCesaro, hclockAbel, hbounds⟩ :=
    response_clock_witness_of_family_and_occupation h0 h2 d hd D Q hQ μ hμ
      Y₀ hY₀ lam hlam P hP Y hY hocc
  have hdriftCesaro := response_velocity_cesaro_of_rate_of_occupation
    h2 d hd D Q hQ β a hβ ha lam P hP Y hY hocc velocity hv
  have hdriftAbel := (response_observation_abel_of_cesaro
    h2 d hd D Q hQ β a μ hβ ha hμ lam P hP Y hY velocity η hdriftCesaro hclockCesaro).1
  exact ⟨velocity, η, hv, hη, fun i => ⟨hdriftCesaro i, hdriftAbel i⟩,
    hclockCesaro, hclockAbel, hbounds⟩

end EinsteinFull.Blueprint
