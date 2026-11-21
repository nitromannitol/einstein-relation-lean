import EinsteinFull.Regeneration.SuccessiveSlabExits

/-!
# Slab exits from successful runs

A path with arbitrarily late long runs of successful bridge intervals cannot
remain in a bounded coordinate slab.
-/

open Filter Set MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- Consecutive successful intervals accumulate their coordinate gains. -/
theorem successful_run_coordinate_gain {d : ℕ} (γ : Path d) (bits : ℕ → Bool)
    (i : Fin d) (Δ : ℝ≥0) (R : ℝ)
    (hg : ∀ n, bits n = true →
      γ ((n : ℝ≥0) * Δ) i + 8 * R ≤ γ (((n + 1 : ℕ) : ℝ≥0) * Δ) i)
    (n N : ℕ) (hb : ∀ k < N, bits (n + k) = true) :
    γ ((n : ℝ≥0) * Δ) i + (N : ℝ) * (8 * R) ≤
      γ (((n + N : ℕ) : ℝ≥0) * Δ) i := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev := ih (fun k hk => hb k (by omega))
    have hnext := hg (n + N) (hb N (by omega))
    have hidx : n + N + 1 = n + (N + 1) := by omega
    rw [hidx] at hnext
    simp only [Nat.cast_add, Nat.cast_one] at hprev hnext ⊢
    linarith

/-- Arbitrarily late successful runs force every shifted coordinate slab exit to be finite. -/
theorem coordinate_slab_exit_finite_of_successful_runs {d : ℕ}
    (γ : Path d) (bits : ℕ → Bool) (i : Fin d) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R r : ℝ) (hR : 0 < R)
    (hg : ∀ n, bits n = true →
      γ ((n : ℝ≥0) * Δ) i + 8 * R ≤ γ (((n + 1 : ℕ) : ℝ≥0) * Δ) i)
    (hb : ∀ N M : ℕ, ∃ n ≥ M, ∀ k < N, bits (n + k) = true)
    (t : ℝ≥0) : coordinateSlabExit (pathTimeShift γ t) i r ≠ ⊤ := by
  intro htop
  have hstay := (MarkovProcess.ContinuousPath.exitTime_eq_top_iff
    (coordinateSlab i ((pathTimeShift γ t) 0) r) (pathTimeShift γ t)).mp htop
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * r / (8 * R))
  have hN' : 2 * r < (N : ℝ) * (8 * R) := by
    have hp : 0 < 8 * R := by positivity
    exact (div_lt_iff₀ hp).mp hN
  obtain ⟨M, hM⟩ := exists_nat_gt ((t : ℝ) / (Δ : ℝ))
  have hM' : t ≤ (M : ℝ≥0) * Δ := by
    have hp : 0 < (Δ : ℝ) := by exact_mod_cast hΔ
    have hh := (div_lt_iff₀ hp).mp hM
    exact_mod_cast hh.le
  obtain ⟨n, hn, hbits⟩ := hb N M
  have hMN : (M : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast hn
  have hnt : t ≤ (n : ℝ≥0) * Δ := hM'.trans (mul_le_mul_left hMN Δ)
  have hnn : (n : ℝ≥0) ≤ ((n + N : ℕ) : ℝ≥0) := by exact_mod_cast (Nat.le_add_right n N)
  have hnt' : t ≤ ((n + N : ℕ) : ℝ≥0) * Δ := hnt.trans (mul_le_mul_left hnn Δ)
  have h₁ := hstay (((n : ℝ≥0) * Δ) - t)
  have h₂ := hstay ((((n + N : ℕ) : ℝ≥0) * Δ) - t)
  simp only [coordinateSlab, Set.mem_ofPred_eq, pathTimeShift, ContinuousMap.coe_mk,
    add_zero] at h₁ h₂
  rw [add_tsub_cancel_of_le hnt] at h₁
  rw [add_tsub_cancel_of_le hnt'] at h₂
  have hgain := successful_run_coordinate_gain γ bits i Δ R hg n N hbits
  have h₁' := (abs_lt.mp h₁).1
  have h₂' := (abs_lt.mp h₂).2
  linarith

end EinsteinFull.Regeneration
