import EinsteinFull.Regeneration.UniformNoBacktracking
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Choosing the regeneration scale

An exponential backward-crossing estimate is at most one half after choosing
the dimensionless regeneration scale sufficiently large.
-/

open MeasureTheory Filter EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- Choose a dimensionless scale uniformly before the force and environment. -/
theorem exists_large_regeneration_scale (κ C r₀ : ℝ) (hκ : 0 < κ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
      ∀ l : ℝ, l₀ ≤ l → ∀ lam : ℝ, 0 < lam →
        C * Real.exp (-κ * lam * (l / lam)) ≤ 1 / 2 := by
  have harg : Tendsto (fun l : ℝ => -κ * l) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hκ)
  have hlim : Tendsto (fun l : ℝ => C * Real.exp (-κ * l)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (Real.tendsto_exp_atBot.comp harg).const_mul C
  have hevent : ∀ᶠ l : ℝ in atTop, C * Real.exp (-κ * l) < 1 / 2 :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨L, hL⟩ := eventually_atTop.mp hevent
  let l₀ := max (max L 1) (r₀ + 1)
  have hL₀ : L ≤ l₀ := (le_max_left L 1).trans (le_max_left _ _)
  have h1 : 1 ≤ l₀ := (le_max_right L 1).trans (le_max_left _ _)
  have hr : r₀ + 1 ≤ l₀ := le_max_right _ _
  refine ⟨l₀, by linarith, by linarith, ?_⟩
  intro l hl lam hlam
  have he : -κ * lam * (l / lam) = -κ * l := by field_simp
  rw [he]
  exact (hL l (hL₀.trans hl)).le

/-- A uniform exponential crossing estimate gives the no-backtracking bound after
choosing the scale independently of the law and force. -/
theorem uniform_no_backtracking_of_exponential_crossing (d : ℕ) (hd : 2 ≤ d)
    (Λ₀ r₀ κ C : ℝ) (hκ : 0 < κ)
    (hback : ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (l δ : ℝ),
      IsRegenerationCoupling hd Q lam l δ h0.le h1 P K →
      ∀ᵐ ω ∂Q.measure, ∀ x u, 0 ≤ u →
        P (x, ω) {γ | firstHittingBelow γ (Renewal.forceCoord hd) (-u) ≠ ⊤} ≤
          ENNReal.ofReal (C * Real.exp (-κ * lam * u))) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
        (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (δ : ℝ),
      IsRegenerationCoupling hd Q lam l δ h0.le h1 P K →
        ∀ᵐ ω ∂Q.measure, ∀ x, ENNReal.ofReal (1 / 2 : ℝ) ≤
          P (x, ω) {γ | NoBacktracking (l / lam) γ (Renewal.forceCoord hd)} := by
  obtain ⟨l₀, hl₀, hsep, hsmall⟩ := exists_large_regeneration_scale κ C r₀ hκ
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl Q lam h0 h1 P K δ hK
  have hscale : 0 ≤ l / lam := div_nonneg (hl₀.le.trans hl) h0.le
  apply uniform_no_backtracking_of_crossing_bound hd Q lam h0 h1 l δ P K hK
  filter_upwards [hback Q lam h0 h1 P K l δ hK] with ω hω x
  exact (hω x (l / lam) hscale).trans (ENNReal.ofReal_le_ofReal (hsmall l hl lam h0))

end EinsteinFull.Regeneration
