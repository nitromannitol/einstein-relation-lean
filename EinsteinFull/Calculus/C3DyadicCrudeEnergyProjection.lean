import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_local
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_local_u23_crude_u2D_energy
import EinsteinFull.Calculus.C1CrudeEnergySupport

open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- The local estimate supplies the same gradient witness for the crude energy bound. -/
theorem c3_dyadic_crude_energy_of_forced_local
    (hlocal : node_l_u3A_forced_u2D_localStmt) :
    node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt := by
  intro d hd D
  obtain ⟨α, Cdet, c, N, hα, hCdet, hc, hlocal⟩ := hlocal d hd D
  obtain ⟨C, Cp, hC, hCp, hlocal⟩ := hlocal 2 (by norm_num)
  refine ⟨2 * Cdet, N, by linarith, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, V, hgrad, hmom, hloc, hbound⟩ :=
    hlocal Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, ?_, ?_⟩
  · intro t ht
    exact (hgrad t (by linarith)).2.1
  · intro t ht hζ
    have hb := hbound t (by linarith) hζ
    have hnonneg : 0 ≤ Cdet * (2 + (t : ℝ)) ^ N *
        Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ)) := by positivity
    have hdouble := twice_crudeEnergyBound_le (C := Cdet) (t := (t : ℝ))
      (z := ‖ζ‖) (by linarith) t.coe_nonneg N
    constructor
    · filter_upwards [hb] with ω hω
      exact hω.trans ((le_mul_of_one_le_left hnonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hdouble)
    · intro ρ hρ x
      exact (norm_add_localSpatialEnergy_le_of_ae_bound Q _ _ hnonneg hb t ρ hρ x).mono
        (fun _ hω => hω.trans hdouble)

end EinsteinFull.Blueprint
