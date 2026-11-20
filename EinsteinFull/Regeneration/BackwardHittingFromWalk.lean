import EinsteinFull.Regeneration.DowncrossingMaximum
import EinsteinFull.Regeneration.BiasedWalkTail

/-!
# Backward hitting from a comparison walk

A path that stays above a biased comparison walk between slab exits satisfies
the backward-crossing estimate of GMP Lemma 4.1.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace EinsteinFull.Regeneration

/-- All-time path domination by the comparison walk gives an exponential
backward-crossing bound at the source spatial scale. -/
theorem backward_hitting_le_of_biased_walk {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (γ : Ω → Path d) (i : Fin d)
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, X n ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ n, (∫ ω, X n ω ∂μ) = (1 / 5 : ℝ))
    (lam L : ℝ) (hlam : 0 < lam) (hL : 0 < L)
    (hcover : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ∃ n : ℕ,
      (L / lam) * ((∑ j ∈ range n, X j ω) - 1) ≤ γ ω t i - γ ω 0 i) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ u : ℝ,
      μ {ω | firstHittingBelow (γ ω) i (-u) ≠ ⊤} ≤ ENNReal.ofReal (C * Real.exp (-κ * lam * u)) := by
  let F : ℝ≥0∞ := (1 - ENNReal.ofReal (Real.exp (-(1 / 50 : ℝ))))⁻¹
  have hFfin : F ≠ ⊤ := biased_walk_geometric_factor_lt_top.ne
  let κ : ℝ := 1 / (5 * L)
  let C : ℝ := Real.exp (1 / 5) * (F.toReal + 1)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨κ, C, hκ, hC, ?_⟩
  intro u
  let m : ℝ := lam * u / L - 1
  have hsub : ∀ᵐ ω ∂μ, ω ∈ {ω | firstHittingBelow (γ ω) i (-u) ≠ ⊤} →
      ω ∈ {ω | ∃ n : ℕ, ∑ j ∈ range n, X j ω ≤ -m} := by
    filter_upwards [hcover] with ω hc hf
    obtain ⟨t, ht⟩ := exists_crossing_of_firstHittingBelow_ne_top (γ ω) i (-u) hf
    obtain ⟨n, hn⟩ := hc t
    refine ⟨n, ?_⟩
    have hn' : ((∑ j ∈ range n, X j ω) - 1) * (L / lam) ≤ -u := by
      simpa only [mul_comm] using hn.trans ht
    have hdiv : (∑ j ∈ range n, X j ω) - 1 ≤ (-u) / (L / lam) :=
      (le_div_iff₀ (div_pos hL hlam)).2 hn'
    have he : (-u) / (L / lam) = -(lam * u / L) := by field_simp
    rw [he] at hdiv
    dsimp [m]
    linarith
  have hr := biased_walk_ever_below μ X hX hind hbound hmean m
  have hF : F = ENNReal.ofReal F.toReal := (ENNReal.ofReal_toReal hFfin).symm
  have hexp : Real.exp (-m / 5) * F.toReal ≤ C * Real.exp (-κ * lam * u) := by
    have he : -m / 5 = 1 / 5 + (-κ * lam * u) := by
      dsimp [m, κ]
      field_simp
      ring
    rw [he, Real.exp_add]
    dsimp [C]
    have hFn : 0 ≤ F.toReal := ENNReal.toReal_nonneg
    nlinarith [hFn, Real.exp_pos (1 / 5 : ℝ), Real.exp_pos (-κ * lam * u)]
  calc
    _ ≤ μ {ω | ∃ n : ℕ, ∑ j ∈ range n, X j ω ≤ -m} := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (Real.exp (-m / 5)) * F := hr
    _ = ENNReal.ofReal (Real.exp (-m / 5) * F.toReal) := by
      calc
        _ = ENNReal.ofReal (Real.exp (-m / 5)) * ENNReal.ofReal F.toReal :=
          congrArg (fun z => ENNReal.ofReal (Real.exp (-m / 5)) * z) hF
        _ = _ := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hexp

end EinsteinFull.Regeneration
