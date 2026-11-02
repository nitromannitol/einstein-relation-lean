import EinsteinFull.Work.W1.GMPKilledSemigroupSupport

/-! Setwise domination for actual killed paths. The one-step estimate is a
separate analytic input; this file proves its finite-chain consequence. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
noncomputable section

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
  {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
  (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)

/-- Survival in a smaller open domain implies survival in the larger one. -/
theorem a_gmpKilledEndpointKernel_mono_domain
    (V U : Set (Vec d)) (hV : IsOpen V) (hU : IsOpen U) (hVU : V ⊆ U)
    (t : ℝ≥0) (x : Vec d) :
    gmpKilledEndpointKernel G V hV t x ≤ gmpKilledEndpointKernel G U hU t x := by
  rw [gmpKilledEndpointKernel_apply, gmpKilledEndpointKernel_apply]
  apply Measure.map_mono _ (measurable_pathPosition t)
  apply Measure.restrict_mono_set
  intro γ hγ
  apply (lt_localityExitTime_iff U hU γ t).2
  intro s hs
  exact hVU ((lt_localityExitTime_iff V hV γ t).1 hγ s hs)

/-- A local setwise one-step lower estimate propagates along a finite chain
of measurable sets for the actual GMP killed kernel. -/
theorem a_actual_killed_chain_domination
    (U : Set (Vec d)) (hU : IsOpen U) (τ : ℝ≥0) (a : ℝ≥0∞)
    (A : ℕ → Set (Vec d)) (hA : ∀ j, MeasurableSet (A j))
    (hAU : ∀ j, A j ⊆ U)
    (hstep : ∀ k z, z ∈ A k →
      a • (volume : Measure (Vec d)).restrict (A (k+1)) ≤
        gmpKilledEndpointKernel G U hU τ z) :
    ∀ n : ℕ, ∀ x ∈ A 0,
      (a ^ (n+1) * ∏ j ∈ Finset.range n, (volume : Measure (Vec d)) (A (j+1))) •
        (volume : Measure (Vec d)).restrict (A (n+1)) ≤
          gmpKilledEndpointKernel G U hU (((n+1 : ℕ) : ℝ≥0) * τ) x := by
  classical
  intro n
  induction n generalizing A with
  | zero =>
      intro x hx
      simpa using hstep 0 x hx
  | succ n ih =>
      intro x hx
      let B : ℕ → Set (Vec d) := fun j => A (j+1)
      have hB : ∀ j, MeasurableSet (B j) := fun j => hA (j+1)
      have hBU : ∀ j, B j ⊆ U := fun j => hAU (j+1)
      have hBs : ∀ k z, z ∈ B k →
          a • (volume : Measure (Vec d)).restrict (B (k+1)) ≤
            gmpKilledEndpointKernel G U hU τ z := by
        intro k z hz
        simpa [B, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep (k+1) z hz
      have htail := ih B hB hBU hBs
      let c : ℝ≥0∞ := a ^ (n+1) * ∏ j ∈ Finset.range n,
        (volume : Measure (Vec d)) (B (j+1))
      letI := isFiniteKernel_gmpKilledEndpointKernel G U hU τ
      letI := isFiniteKernel_gmpKilledEndpointKernel G U hU (((n+1 : ℕ) : ℝ≥0) * τ)
      apply Measure.le_iff.2
      intro S hS
      have hp : ∀ y, (A 1).indicator (fun _ => c * (volume : Measure (Vec d)).restrict (B (n+1)) S) y ≤
          gmpKilledEndpointKernel G U hU (((n+1 : ℕ) : ℝ≥0) * τ) y S := by
        intro y
        by_cases hy : y ∈ A 1
        · simpa [Set.indicator_of_mem hy, Measure.smul_apply, c] using htail y hy S
        · simp only [Set.indicator_of_notMem hy, zero_le]
      have hmass : a * (volume : Measure (Vec d)) (A 1) ≤
          gmpKilledEndpointKernel G U hU τ x (A 1) := by
        simpa [Measure.smul_apply, Measure.restrict_apply, hA 1] using hstep 0 x hx (A 1)
      calc
        _ = (c * (volume : Measure (Vec d)).restrict (B (n+1)) S) *
              (a * (volume : Measure (Vec d)) (A 1)) := by
                simp [Measure.smul_apply, B, c, Finset.prod_range_succ', pow_succ,
                  Nat.add_comm, Nat.add_left_comm, mul_assoc, mul_comm, mul_left_comm]
        _ ≤ (c * (volume : Measure (Vec d)).restrict (B (n+1)) S) *
              gmpKilledEndpointKernel G U hU τ x (A 1) := by simpa only [mul_comm] using mul_le_mul_left hmass (c * (volume : Measure (Vec d)).restrict (B (n+1)) S)
        _ = ∫⁻ y, (A 1).indicator (fun _ => c * (volume : Measure (Vec d)).restrict (B (n+1)) S) y ∂gmpKilledEndpointKernel G U hU τ x := by
              rw [lintegral_indicator_const (hA 1)]
        _ ≤ ∫⁻ y, gmpKilledEndpointKernel G U hU (((n+1 : ℕ) : ℝ≥0) * τ) y S ∂gmpKilledEndpointKernel G U hU τ x := lintegral_mono hp
        _ = _ := by
          rw [show (((n+1+1 : ℕ) : ℝ≥0) * τ) = τ + (((n+1 : ℕ) : ℝ≥0) * τ) by
            simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]; ac_rfl,
            gmpKilledEndpointKernel_add, Kernel.comp_apply' _ _ _ hS]

end
end EinsteinFull
