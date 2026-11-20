import EinsteinFull.Regeneration.AdaptedConditionalDrift
import EinsteinFull.Regeneration.BackwardHittingFromWalk

/-!
# Backward hitting from adapted increments

Bounded adapted increments with positive conditional drift have a geometric
lower-tail union bound, without an independent comparison sequence.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace EinsteinFull.Regeneration

/-- The probability of ever reaching a lower level has an exponential bound. -/
theorem adapted_walk_ever_below {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (X : ℕ → Ω → ℝ) (hX : StronglyAdapted ℱ X)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean0 : (1 / 5 : ℝ) ≤ ∫ ω, X 0 ω ∂μ)
    (hdrift : ∀ j, ∀ᵐ ω ∂μ, (1 / 5 : ℝ) ≤ μ[X (j + 1) | ℱ j] ω) (m : ℝ) :
    μ {ω | ∃ n : ℕ, ∑ j ∈ range n, X j ω ≤ -m} ≤
      ENNReal.ofReal (Real.exp (-m / 20)) *
        (1 - ENNReal.ofReal (Real.exp (-(1 / 200 : ℝ))))⁻¹ := by
  have hpoint (n : ℕ) : μ {ω | ∑ j ∈ range n, X j ω ≤ -m} ≤
      ENNReal.ofReal (Real.exp (-m / 20 - (n : ℝ) / 200)) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [neg_div, measureReal_def] using
      adapted_walk_lower_tail_of_conditional_drift μ ℱ X hX hbound hmean0 hdrift n (-m)
  have hfactor (n : ℕ) : ENNReal.ofReal (Real.exp (-m / 20 - (n : ℝ) / 200)) =
      ENNReal.ofReal (Real.exp (-m / 20)) *
        ENNReal.ofReal (Real.exp (-(1 / 200 : ℝ))) ^ n := by
    rw [← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
    positivity
  have hevent : {ω | ∃ n : ℕ, ∑ j ∈ range n, X j ω ≤ -m} =
      ⋃ n : ℕ, {ω | ∑ j ∈ range n, X j ω ≤ -m} := by
    ext ω
    simp
  rw [hevent]
  calc
    _ ≤ ∑' n : ℕ, μ {ω | ∑ j ∈ range n, X j ω ≤ -m} := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp (-m / 20 - (n : ℝ) / 200)) :=
      ENNReal.tsum_le_tsum hpoint
    _ = ENNReal.ofReal (Real.exp (-m / 20)) *
        (1 - ENNReal.ofReal (Real.exp (-(1 / 200 : ℝ))))⁻¹ := by
      simp_rw [hfactor, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- The geometric factor in the adapted backward bound is finite. -/
theorem adapted_walk_geometric_factor_lt_top :
    (1 - ENNReal.ofReal (Real.exp (-(1 / 200 : ℝ))))⁻¹ < ⊤ := by
  rw [ENNReal.inv_lt_top, tsub_pos_iff_lt, ENNReal.ofReal_lt_one, Real.exp_lt_one_iff]
  norm_num

/-- All-time domination by an adapted walk gives the scaled backward-hitting bound. -/
theorem backward_hitting_le_of_adapted_walk (L : ℝ) (hL : 0 < L) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (γ : Ω → Path d) (i : Fin d)
      (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ),
      StronglyAdapted ℱ X →
      (∀ j, ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc (-1 : ℝ) 1) →
      (1 / 5 : ℝ) ≤ (∫ ω, X 0 ω ∂μ) →
      (∀ j, ∀ᵐ ω ∂μ, (1 / 5 : ℝ) ≤ μ[X (j + 1) | ℱ j] ω) →
      ∀ lam : ℝ, 0 < lam →
      (∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ∃ n : ℕ,
        (L / lam) * ((∑ j ∈ range n, X j ω) - 1) ≤ γ ω t i - γ ω 0 i) →
      ∀ u : ℝ, μ {ω | firstHittingBelow (γ ω) i (-u) ≠ ⊤} ≤
        ENNReal.ofReal (C * Real.exp (-κ * lam * u)) := by
  let F : ℝ≥0∞ := (1 - ENNReal.ofReal (Real.exp (-(1 / 200 : ℝ))))⁻¹
  have hFfin : F ≠ ⊤ := adapted_walk_geometric_factor_lt_top.ne
  let κ : ℝ := 1 / (20 * L)
  let C : ℝ := Real.exp (1 / 20) * (F.toReal + 1)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨κ, C, hκ, hC, ?_⟩
  intro Ω _ _ μ _ d γ i ℱ X hX hbound hmean0 hdrift lam hlam hcover u
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
  have hr := adapted_walk_ever_below μ ℱ X hX hbound hmean0 hdrift m
  have hF : F = ENNReal.ofReal F.toReal := (ENNReal.ofReal_toReal hFfin).symm
  have hexp : Real.exp (-m / 20) * F.toReal ≤ C * Real.exp (-κ * lam * u) := by
    have he : -m / 20 = 1 / 20 + (-κ * lam * u) := by
      dsimp [m, κ]
      field_simp
      ring
    rw [he, Real.exp_add]
    dsimp [C]
    have hFn : 0 ≤ F.toReal := ENNReal.toReal_nonneg
    nlinarith [hFn, Real.exp_pos (1 / 20 : ℝ), Real.exp_pos (-κ * lam * u)]
  calc
    _ ≤ μ {ω | ∃ n : ℕ, ∑ j ∈ range n, X j ω ≤ -m} := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (Real.exp (-m / 20)) * F := hr
    _ = ENNReal.ofReal (Real.exp (-m / 20) * F.toReal) := by
      calc
        _ = ENNReal.ofReal (Real.exp (-m / 20)) * ENNReal.ofReal F.toReal :=
          congrArg (fun z => ENNReal.ofReal (Real.exp (-m / 20)) * z) hF
        _ = _ := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hexp

end EinsteinFull.Regeneration
