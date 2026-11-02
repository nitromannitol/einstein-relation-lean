import EinsteinFull.Calculus.C1LocalTimeGradientMomentAssembly
import EinsteinFull.Calculus.C4LocalTimeMomentAssembly
import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- The exact local-time estimate, assembled from the gradient and derivative
moments on the same actual endpoint witnesses. -/
theorem node_e_u3A_local_u2D_time_of_deps
    (h0 : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (h1 : node_e_u3A_lp_u2D_growthStmt) :
    node_e_u3A_local_u2D_timeStmt := by
  intro d hd D p hp
  obtain ⟨Cg, Cpg, hCg, hCpg, hgradient⟩ :=
    local_time_gradient_moment_of_deps h0 h1 d hd D p hp
  obtain ⟨Cv, Cpv, hCv, hCpv, hderivative⟩ :=
    local_time_derivative_moment_of_deps h0 h1 d hd D p hp
  refine ⟨2 * max Cg Cv, max Cpg Cpv, ?_,
    hCpg.trans_le (le_max_left _ _), ?_⟩
  · have hmax : 1 ≤ max Cg Cv := hCg.trans (le_max_left _ _)
    linarith only [hmax]
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, V, hGV, hgm⟩ := hgradient Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨H, W, hHW, hwm⟩ := hderivative Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, V, hGV, ?_⟩
  intro t ht U U₈
  obtain ⟨hu, hg⟩ := hgm t ht
  obtain ⟨_, hw⟩ := hwm t ht
  refine ⟨hu, ?_⟩
  intro ρ x hρ
  obtain ⟨hGm, hGb⟩ := hg ρ x hρ
  obtain ⟨hWm, hWb⟩ := hw ρ x hρ
  have hVW : V t = W t := (hGV t ht).2.2.unique (hHW t ht).2.2
  rw [← hVW] at hWm hWb
  have hp' : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hp])
  exact local_time_combined_energy_moment_bound Q t ht ρ
    (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (G t) (V t) hp' ζ
    hCg hCv ENNReal.toReal_nonneg hGm hWm hGb hWb

end EinsteinFull.Blueprint
