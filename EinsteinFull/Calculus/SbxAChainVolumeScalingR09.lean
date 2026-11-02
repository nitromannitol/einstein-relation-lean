import EinsteinFull.Calculus.SbxAKilledChainDominationR09
import EinsteinFull.Calculus.C12TubeNativeLowerChaining

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace EinsteinFull

/-- Scaling and translation of the volume of a source ball. -/
theorem a_sourceBall_volume_scale {d : ℕ} (r μ : ℝ) (hr : 0 < r) (hμ : 0 < μ)
    (x : Vec d) :
    volume (sourceBall x (r / μ)) =
      ENNReal.ofReal ((μ⁻¹) ^ d) * volume (sourceBall (0 : Vec d) r) := by
  have hx := Calculus.c12_sourceBall_volume x (div_pos hr hμ)
  have h0 := Calculus.c12_sourceBall_volume (0 : Vec d) hr
  rw [← ENNReal.ofReal_toReal hx.2.1, ← ENNReal.ofReal_toReal h0.2.1,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [hx.2.2.2, h0.2.2.2, div_pow, inv_pow]
  ring

/-- The chain coefficient has the same force power as a single step. -/
theorem a_chain_volume_coefficient {d : ℕ} (a r : ℝ) (ha : 0 < a) (hr : 0 < r)
    (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (μ : ℝ), 0 < μ → ∀ centers : ℕ → Vec d,
      ENNReal.ofReal (a * μ ^ d) ^ (n+1) *
        ∏ j ∈ Finset.range n, volume (sourceBall (centers (j+1)) (r / μ)) =
      ENNReal.ofReal (c * μ ^ d) := by
  let v : ℝ := (volume (sourceBall (0 : Vec d) r)).toReal
  let c : ℝ := a ^ (n+1) * v ^ n
  have hv : 0 < v := (Calculus.c12_sourceBall_volume (0 : Vec d) hr).2.2.1
  have hvtop := (Calculus.c12_sourceBall_volume (0 : Vec d) hr).2.1
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro μ hμ centers
  have hvol : ∀ j, volume (sourceBall (centers (j+1)) (r / μ)) =
      ENNReal.ofReal ((μ⁻¹) ^ d * v) := by
    intro j
    rw [a_sourceBall_volume_scale r μ hr hμ, ← ENNReal.ofReal_toReal hvtop,
      ← ENNReal.ofReal_mul (by positivity)]
  simp_rw [hvol]
  simp only [Finset.prod_const, Finset.card_range]
  rw [← ENNReal.ofReal_pow, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_mul (by positivity)] <;> try positivity
  congr 1
  dsimp [c]
  have hm : μ ^ d ≠ 0 := pow_ne_zero d (ne_of_gt hμ)
  have hcancel : (μ ^ d) ^ n * ((μ ^ d)⁻¹) ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hm, one_pow]
  rw [mul_pow, mul_pow, pow_succ, inv_pow]
  calc
    _ = (a ^ (n+1) * v ^ n * μ ^ d) *
        ((μ ^ d) ^ n * ((μ ^ d)⁻¹) ^ n) := by ring
    _ = _ := by rw [hcancel, mul_one]; ring

/-- The actual killed-chain domination, with arbitrary endpoint sets and a
uniform coefficient for equal-radius intermediate balls. -/
theorem a_actual_killed_chain_scaled {d : ℕ}
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (μ : ℝ), 0 < μ →
      ∀ {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
        {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
        (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
        (U : Set (Vec d)) (hU : IsOpen U) (τ : ℝ≥0)
        (A : ℕ → Set (Vec d)) (centers : ℕ → Vec d),
      (∀ j, MeasurableSet (A j)) → (∀ j, A j ⊆ U) →
      (∀ j ∈ Finset.range n, A (j+1) = sourceBall (centers (j+1)) (r / μ)) →
      (∀ k z, z ∈ A k → ENNReal.ofReal (a * μ ^ d) •
          (volume : Measure (Vec d)).restrict (A (k+1)) ≤
            gmpKilledEndpointKernel G U hU τ z) →
      ∀ x ∈ A 0, ENNReal.ofReal (c * μ ^ d) •
          (volume : Measure (Vec d)).restrict (A (n+1)) ≤
            gmpKilledEndpointKernel G U hU (((n+1 : ℕ) : ℝ≥0) * τ) x := by
  obtain ⟨c, hc, hcoeff⟩ := a_chain_volume_coefficient (d := d) a r ha hr n
  refine ⟨c, hc, ?_⟩
  intro μ hμ hd L hL ω hω lam h₀ h₁ G U hU τ A centers hA hAU hballs hstep x hx
  have h := a_actual_killed_chain_domination G U hU τ (ENNReal.ofReal (a * μ ^ d))
    A hA hAU hstep n x hx
  have hp : (∏ j ∈ Finset.range n, (volume : Measure (Vec d)) (A (j+1))) =
      ∏ j ∈ Finset.range n, volume (sourceBall (centers (j+1)) (r / μ)) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hballs j hj]
  rw [hp, hcoeff μ hμ centers] at h
  exact h

end EinsteinFull
