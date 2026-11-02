import EinsteinFull.Calculus.C4DyadicClosedInitialization

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

theorem c15_dyadic_actual_average_majorant_finite (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T b : ℝ) (hT : 1 ≤ T) (hb : 0 < b) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ‖ζ‖ ≤ 2 → ∀ growth : ℝ, 0 ≤ growth → let S : Set ℝ := {z | ∃ t : ℝ≥0, ∃ s : ℝ, ∃ hs : 0 < s, 1 ≤ (t : ℝ) ∧ (t : ℝ) ≤ T ∧ b*(t : ℝ) ≤ s ∧ z = ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ / (Real.exp (growth*‖ζ‖^2*(t : ℝ)) * ((s) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (s) ^ (-(d : ℝ)/4)))}; S.Nonempty ∧ BddAbove S ∧ 0 ≤ sSup S ∧ sSup S ≤ C ∧ ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → (t : ℝ) ≤ T → ∀ s : ℝ, b*(t : ℝ) ≤ s → ∀ hs : 0 < s, ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤ sSup S * (Real.exp (growth*‖ζ‖^2*(t : ℝ)) * ((s) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (s) ^ (-(d : ℝ)/4))) := by
  obtain ⟨C, hC, hbound⟩ := c4_dyadic_bounded_time_initial_average_of_forced_local hlocal d hd D T (by linarith)
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν hζ growth hg
  dsimp only
  have hw (s : ℝ) (hs : 0 < s) : 0 < s ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * s ^ (-(d : ℝ)/4) := by
    have h₁ : 0 < s ^ (-(1/2+(d : ℝ)/4)) := Real.rpow_pos_of_pos hs _
    have h₂ : 0 ≤ ‖ζ‖ * s ^ (-(d : ℝ)/4) := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hs.le _)
    linarith
  have hden (t : ℝ≥0) (s : ℝ) (hs : 0 < s) : 0 < Real.exp (growth*‖ζ‖^2*(t : ℝ)) * (s ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * s ^ (-(d : ℝ)/4)) := mul_pos (Real.exp_pos _) (hw s hs)
  let S : Set ℝ := {z | ∃ t : ℝ≥0, ∃ s : ℝ, ∃ hs : 0 < s, 1 ≤ (t : ℝ) ∧ (t : ℝ) ≤ T ∧ b*(t : ℝ) ≤ s ∧ z = ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ / (Real.exp (growth*‖ζ‖^2*(t : ℝ)) * (s ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * s ^ (-(d : ℝ)/4)))}
  change S.Nonempty ∧ BddAbove S ∧ 0 ≤ sSup S ∧ sSup S ≤ C ∧ _
  have hn : S.Nonempty := by
    refine ⟨_, ⟨1, b, hb, by norm_num, by simpa using hT, by simp, rfl⟩⟩
  have hupper : ∀ z ∈ S, z ≤ C := by
    intro z hz
    obtain ⟨t, s, hs, ht, htT, hbs, rfl⟩ := hz
    apply (div_le_iff₀ (hden t s hs)).2
    have he : 1 ≤ Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) := Real.one_le_exp (by positivity)
    have hw' := (hw s hs).le
    have hc : 0 ≤ C := by linarith
    have hh := hbound Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν hζ t htT s hs
    exact hh.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hw' he) hc)
  have hbdd : BddAbove S := ⟨C, hupper⟩
  refine ⟨hn, hbdd, ?_, csSup_le hn hupper, ?_⟩
  · obtain ⟨z, hz⟩ := hn
    have hz0 : 0 ≤ z := by
      obtain ⟨t, s, hs, ht, htT, hbs, rfl⟩ := hz
      exact div_nonneg (norm_nonneg _) (hden t s hs).le
    exact le_trans hz0 (le_csSup hbdd hz)
  · intro t ht htT s hbs hs
    have hm : ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ / (Real.exp (growth*‖ζ‖^2*(t : ℝ)) * (s ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * s ^ (-(d : ℝ)/4))) ∈ S := ⟨t, s, hs, ht, htT, hbs, rfl⟩
    exact (div_le_iff₀ (hden t s hs)).1 (le_csSup hbdd hm)

end EinsteinFull.Blueprint
