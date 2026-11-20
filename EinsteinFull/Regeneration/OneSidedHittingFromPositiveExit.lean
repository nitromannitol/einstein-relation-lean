import EinsteinFull.Regeneration.GMPForwardFromPositiveExit

/-!
# One-sided hitting from positive slab exits

The forward-hitting estimate yields the one-sided deterministic-time bound
used in GMP equation (4.9), conditional on its positive-exit estimate.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Positive slab exits imply a uniform deterministic-time one-sided hitting bound. -/
theorem uniform_supplied_one_sided_hitting_of_positive_exit
    (d : ℕ) (hd : 2 ≤ d) (Λ r L : ℝ) (hL : 1 ≤ L) :
    ∃ g : ℝ, 0 < g ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (P : QuenchedPathLaws d),
        IsGMPReducedKernel hd Q.ellipticity_parameter Q μ hμ.le hμ1 P →
        (∀ᵐ ω ∂Q.measure, ∀ y : Vec d, (2 / 3 : ℝ) ≤ (P (y, ω)).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ}) →
        ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (a : ℝ), 0 ≤ a → μ * a ≤ 2 * L →
          P (x, ω) {γ | (Real.toNNReal (g / μ ^ 2) : ℝ≥0∞) ≤
            firstHittingAbove γ (Renewal.forceCoord hd) a} ≤ ENNReal.ofReal (1 / 15 : ℝ) := by
  obtain ⟨g₀, hg₀, hforward⟩ := uniform_supplied_forward_hitting_of_positive_exit d hd Λ r L hL
  let g := 400 * g₀ * (2 * L + 20)
  have hg : 0 < g := by dsimp [g]; positivity
  refine ⟨g, hg, ?_⟩
  intro Q μ hμ hμ1 P hP hpositive
  filter_upwards [hforward Q μ hμ hμ1 P hP hpositive] with ω hω
  intro x a ha habound
  have htime : (Real.toNNReal (g / μ ^ 2) : ℝ) = g / μ ^ 2 :=
    Real.coe_toNNReal _ (div_nonneg hg.le (sq_nonneg μ))
  have hcancel : -(1 / (400 * g₀)) * μ ^ 2 * (g / μ ^ 2) = -(2 * L + 20) := by
    dsimp [g]
    field_simp
  have harg : (1 / 200 : ℝ) + (-(1 / (400 * g₀)) * μ ^ 2 *
      (Real.toNNReal (g / μ ^ 2) : ℝ) + μ * a) ≤ -19 := by
    rw [htime, hcancel]
    linarith
  have hexp : Real.exp (-19 : ℝ) ≤ (1 / 15 : ℝ) := by
    have hlarge : (15 : ℝ) ≤ Real.exp 19 := by
      have h := Real.add_one_le_exp 19
      linarith
    rw [show (-19 : ℝ) = -(19 : ℝ) by norm_num, Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 15) hlarge
  calc
    _ ≤ ENNReal.ofReal (Real.exp (1 / 200) *
        Real.exp (-(1 / (400 * g₀)) * μ ^ 2 *
          (Real.toNNReal (g / μ ^ 2) : ℝ) + μ * a)) := hω x _ a ha
    _ ≤ ENNReal.ofReal (Real.exp (-19 : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr harg
    _ ≤ ENNReal.ofReal (1 / 15 : ℝ) := ENNReal.ofReal_le_ofReal hexp

/-- GMP's one-sided time bound holds uniformly for starts in the slab. -/
theorem uniform_supplied_slab_to_upper_hitting_of_positive_exit
    (d : ℕ) (hd : 2 ≤ d) (Λ r L : ℝ) (hL : 1 ≤ L) :
    ∃ g : ℝ, 0 < g ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (P : QuenchedPathLaws d),
        IsGMPReducedKernel hd Q.ellipticity_parameter Q μ hμ.le hμ1 P →
        (∀ᵐ ω ∂Q.measure, ∀ y : Vec d, (2 / 3 : ℝ) ≤ (P (y, ω)).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ}) →
        ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
          -(L / μ) ≤ x (Renewal.forceCoord hd) → x (Renewal.forceCoord hd) ≤ L / μ →
          P (x, ω) {γ | (Real.toNNReal (g / μ ^ 2) : ℝ≥0∞) ≤
            firstHittingAbove γ (Renewal.forceCoord hd)
              (L / μ - γ 0 (Renewal.forceCoord hd))} ≤ ENNReal.ofReal (1 / 15 : ℝ) := by
  obtain ⟨g, hg, hforward⟩ := uniform_supplied_one_sided_hitting_of_positive_exit d hd Λ r L hL
  refine ⟨g, hg, ?_⟩
  intro Q μ hμ hμ1 P hP hpositive
  filter_upwards [hP, hforward Q μ hμ hμ1 P hP hpositive] with ω hω hbound
  obtain ⟨hω, G, hrow⟩ := hω
  intro x hxlo hxhi
  have ha : 0 ≤ L / μ - x (Renewal.forceCoord hd) := sub_nonneg.mpr hxhi
  have hscale : μ * (L / μ - x (Renewal.forceCoord hd)) ≤ 2 * L := by
    have h := mul_le_mul_of_nonneg_left hxlo hμ.le
    have he : μ * (L / μ) = L := by field_simp
    nlinarith
  have hstart : ∀ᵐ γ ∂P (x, ω), γ 0 = x := by
    rw [hrow x]
    exact G.pathLaw_starts_at x
  calc
    _ ≤ P (x, ω) {γ | (Real.toNNReal (g / μ ^ 2) : ℝ≥0∞) ≤
        firstHittingAbove γ (Renewal.forceCoord hd) (L / μ - x (Renewal.forceCoord hd))} := by
      apply measure_mono_ae
      filter_upwards [hstart] with γ hγ
      simp only [hγ]
      exact le_rfl
    _ ≤ _ := hbound x _ ha hscale

end EinsteinFull.Regeneration
