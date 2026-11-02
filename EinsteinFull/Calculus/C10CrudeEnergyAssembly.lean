import EinsteinFull.Calculus.C4CrudeEnergyFirstStrip
import EinsteinFull.Calculus.C1CrudeEnergyLargeTime
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_local_u23_crude_u2D_energy

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private lemma c10_grow_bound (E C : ℝ) (n N : ℕ)
    (hE : 0 ≤ E) (hEC : E ≤ C) (hn : n ≤ N) (t : ℝ≥0) (ζ : ℂ) :
    E * (2 + (t : ℝ)) ^ n * Real.exp (E * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
      C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
  have hp : (2 + (t : ℝ)) ^ n ≤ (2 + (t : ℝ)) ^ N :=
    pow_le_pow_right₀ (by linarith [t.coe_nonneg]) hn
  apply mul_le_mul
  · exact mul_le_mul hEC hp (by positivity) (hE.trans hEC)
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hEC (sq_nonneg _)) t.coe_nonneg
  · exact Real.exp_nonneg _
  · exact mul_nonneg (hE.trans hEC) (by positivity)

/-- Assemble the endpoint and local energy bounds over the full time range. -/
theorem c10_crude_energy_of_deps :
    node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt →
    node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt := by
  intro hkernel d hd D
  obtain ⟨Cs, Ns, hCs, hs⟩ := crudeEnergy_first_strip_of_pointKernel d hd D
  obtain ⟨Cl, Nl, hCl, hl⟩ := crudeEnergy_large_time_of_pointKernel hkernel d hd D
  refine ⟨max Cs Cl, max Ns Nl, hCs.trans (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨Gs, hGs, hbs⟩ := hs Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨Gl, hGl, hbl⟩ := hl Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  let G := fun (t : ℝ≥0) => if (t : ℝ) < 2 then Gs t else Gl t
  refine ⟨G, ?_, ?_⟩
  · intro t ht
    by_cases h : (t : ℝ) < 2
    · simpa only [G, ite_eq_left h] using hGs t ht h
    · simpa only [G, ite_eq_right h] using hGl t (le_of_not_gt h)
  · intro t ht hζ
    by_cases h : (t : ℝ) < 2
    · have hd := c10_grow_bound Cs (max Cs Cl) Ns (max Ns Nl)
        (zero_le_one.trans hCs) (le_max_left _ _) (le_max_left _ _) t ζ
      obtain ⟨hp, he⟩ := hbs t ht h hζ
      constructor
      · simpa only [G, ite_eq_left h] using hp.mono (fun _ hω => hω.trans hd)
      · intro ρ hρ x
        simpa only [G, ite_eq_left h] using (he ρ hρ x).mono (fun _ hω => hω.trans hd)
    · have hd := c10_grow_bound Cl (max Cs Cl) Nl (max Ns Nl)
        (zero_le_one.trans hCl) (le_max_right _ _) (le_max_right _ _) t ζ
      obtain ⟨hp, he⟩ := hbl t (le_of_not_gt h) hζ
      constructor
      · simpa only [G, ite_eq_right h] using hp.mono (fun _ hω => hω.trans hd)
      · intro ρ hρ x
        simpa only [G, ite_eq_right h] using (he ρ hρ x).mono (fun _ hω => hω.trans hd)

/-- The crude-energy node follows from the point-kernel node. -/
theorem node_l_u3A_forced_u2D_local_u23_crude_u2D_energy_of_deps :
    node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt →
    node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt :=
  c10_crude_energy_of_deps

end EinsteinFull.Blueprint
