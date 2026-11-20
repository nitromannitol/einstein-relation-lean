import EinsteinFull.Regeneration.KilledSurvivalIteration
import MarkovProcess.Path.ExitTime

/-!
# Finite exit from a uniform escape bound

A uniform one-step escape probability gives arbitrarily small survival
probabilities by the killed semigroup, and therefore finite exit almost surely.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Diffusion EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Uniform one-step escape implies almost-sure finite exit for every start. -/
theorem gmp_ae_exitTime_ne_top_of_survival_bound
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (τ : ℝ≥0) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hstep : ∀ x, G.pathLaw x {γ : Path d | ∀ t : ℝ≥0, t ≤ τ → γ t ∈ U} ≤
      ENNReal.ofReal (1 - δ)) (x : Vec d) :
    ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤ := by
  apply ae_iff.mpr
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨n, hn⟩ := exists_gmp_survival_le δ (ε : ℝ) hδ hδ1 (by exact_mod_cast hε)
  have hsub : {γ : Path d | ¬ MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤} ⊆
      {γ : Path d | ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * τ → γ t ∈ U} := by
    intro γ hγ t _
    have htop : MarkovProcess.ContinuousPath.exitTime U γ = ⊤ := not_ne_iff.mp hγ
    exact (MarkovProcess.ContinuousPath.exitTime_eq_top_iff U γ).mp htop t
  have h := (measure_mono hsub).trans (hn G U hU τ hstep x)
  simpa only [bot_eq_zero, zero_add, ENNReal.ofReal_coe_nnreal] using h

end EinsteinFull.Regeneration
