import EinsteinFull.Regeneration.SuccessiveSlabExits

/-!
# Backward hitting from successive slab exits

Comparison at the actual slab exits extends to every path time, yielding the
backward-hitting bound of GMP Lemma 4.1.
-/

open MeasureTheory Filter ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration Finset
open scoped NNReal ENNReal Topology ProbabilityTheory

namespace EinsteinFull.Regeneration

/-- Finite successive slab exits and embedded-walk domination give the source
backward-hitting estimate with constants independent of the path law and force. -/
theorem backward_hitting_le_of_slab_walk (L : ℝ) (hL : 0 < L) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (γ : Ω → Path d) (i : Fin d)
      (X : ℕ → Ω → ℝ), (∀ n, Measurable (X n)) → iIndepFun X μ →
      (∀ n, ∀ᵐ ω ∂μ, X n ω ∈ Set.Icc (-1 : ℝ) 1) →
      (∀ n, (∫ ω, X n ω ∂μ) = (1 / 5 : ℝ)) →
      ∀ lam : ℝ, 0 < lam →
      (∀ᵐ ω ∂μ, ∀ n, coordinateSlabExit
        (pathTimeShift (γ ω) (successiveSlabExitTime (γ ω) i (L / lam) n)) i (L / lam) ≠ ⊤) →
      (∀ n, ∀ᵐ ω ∂μ, (L / lam) * (∑ j ∈ range n, X j ω) ≤
        γ ω (successiveSlabExitTime (γ ω) i (L / lam) n) i - γ ω 0 i) →
      ∀ u : ℝ, μ {ω | firstHittingBelow (γ ω) i (-u) ≠ ⊤} ≤
        ENNReal.ofReal (C * Real.exp (-κ * lam * u)) := by
  obtain ⟨κ, C, hκ, hC, hwalk⟩ := backward_hitting_le_of_biased_walk L hL
  refine ⟨κ, C, hκ, hC, ?_⟩
  intro Ω _ μ _ d γ i X hX hind hbound hmean lam hlam hfinite hcompare u
  let τ : ℕ → Ω → ℝ≥0 := fun n ω => successiveSlabExitTime (γ ω) i (L / lam) n
  have hzero : ∀ᵐ ω ∂μ, τ 0 ω = 0 := Filter.Eventually.of_forall (fun _ => rfl)
  have htop : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (τ n ω : ℝ)) atTop atTop := by
    filter_upwards [hfinite] with ω hω
    exact NNReal.tendsto_coe_atTop.mpr
      (successive_slab_exit_times_tendsto_atTop (γ ω) i (L / lam) (div_pos hL hlam) hω)
  have hslab : ∀ᵐ ω ∂μ, ∀ n t, τ n ω ≤ t → t ≤ τ (n + 1) ω →
      -(L / lam) ≤ γ ω t i - γ ω (τ n ω) i := by
    filter_upwards [hfinite] with ω hω n t hlo hhi
    exact successive_slab_exit_confinement (γ ω) i (L / lam) (div_pos hL hlam) n (hω n) t hlo hhi
  have hcover := all_time_domination_of_slab_exits μ γ i X τ lam L hzero htop hslab hcompare
  exact hwalk μ γ i X hX hind hbound hmean lam hlam hcover u

end EinsteinFull.Regeneration
