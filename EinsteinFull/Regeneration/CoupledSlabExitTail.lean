import EinsteinFull.Regeneration.CoupledSlabExitFiniteness

/-!
# Slab exit tails from fresh runs

Successful bridge runs give a geometric survival bound for the initial
force-coordinate slab under the regeneration coupling.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Survival in a slab excludes every successful block whose gain spans the slab. -/
theorem failed_blocks_of_slab_survival {d : ℕ} (γ : Path d) (bits : ℕ → Bool)
    (i : Fin d) (Δ : ℝ≥0) (R r : ℝ) (N m : ℕ)
    (hwidth : 2 * r ≤ (N : ℝ) * (8 * R))
    (hg : ∀ n, bits n = true →
      γ ((n : ℝ≥0) * Δ) i + 8 * R ≤ γ (((n + 1 : ℕ) : ℝ≥0) * Δ) i)
    (hsurvive : ((((m * N : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) < coordinateSlabExit γ i r) :
    (γ, bits) ∈ failedSuccessfulBlocks 0 N m := by
  intro j hj hrun
  have hj0 : j * N ≤ m * N := Nat.mul_le_mul_right N (Nat.le_of_lt hj)
  have hj1 : j * N + N ≤ m * N := by nlinarith
  have ht0 : ((j * N : ℕ) : ℝ≥0) * Δ ≤ ((m * N : ℕ) : ℝ≥0) * Δ :=
    mul_le_mul_left (by exact_mod_cast hj0) Δ
  have ht1 : (((j * N + N : ℕ) : ℝ≥0) * Δ) ≤ ((m * N : ℕ) : ℝ≥0) * Δ :=
    mul_le_mul_left (by exact_mod_cast hj1) Δ
  have hm0 := MarkovProcess.ContinuousPath.mem_of_lt_exitTime (coordinateSlab i (γ 0) r) γ
    (((j * N : ℕ) : ℝ≥0) * Δ) ((by exact_mod_cast ht0 :
      ((((j * N : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ≤
      ((((m * N : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)).trans_lt hsurvive)
  have hm1 := MarkovProcess.ContinuousPath.mem_of_lt_exitTime (coordinateSlab i (γ 0) r) γ
    ((((j * N + N : ℕ) : ℝ≥0) * Δ)) ((by exact_mod_cast ht1 :
      (((((j * N + N : ℕ) : ℝ≥0) * Δ : ℝ≥0)) : ℝ≥0∞) ≤
      ((((m * N : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)).trans_lt hsurvive)
  have hrun' : ∀ k < N, bits (j * N + k) = true := by
    simpa [successfulRun] using hrun
  have hgain := successful_run_coordinate_gain γ bits i Δ R hg (j * N) N hrun'
  change |γ (((j * N : ℕ) : ℝ≥0) * Δ) i - γ 0 i| < r at hm0
  change |γ (((j * N + N : ℕ) : ℝ≥0) * Δ) i - γ 0 i| < r at hm1
  have hlow := (abs_lt.mp hm0).1
  have hhigh := (abs_lt.mp hm1).2
  linarith

/-- The coupled slab survival probability decays geometrically over blocks of successful bridges. -/
theorem coupled_coordinate_slab_survival_le {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (r : ℝ) (N m : ℕ) (hwidth : 2 * r ≤ (N : ℝ) * (8 * (l / lam))) :
    annealedCoupledLaw Q.measure K {q |
      ((((m * N : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) <
        coordinateSlabExit q.2.1 (Renewal.forceCoord hd) r} ≤
      ENNReal.ofReal (1 - δ ^ N) ^ m := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  have hgain := EinsteinFull.Blueprint.ae_gain_annealed hd Q lam h0 h1 l δ P K hK
  have hsub : ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      q ∈ {q | ((((m * N : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) <
        coordinateSlabExit q.2.1 (Renewal.forceCoord hd) r} →
      q ∈ {q | q.2 ∈ failedSuccessfulBlocks 0 N m} := by
    filter_upwards [hgain] with q hg hsurvive
    exact failed_blocks_of_slab_survival q.2.1 q.2.2 (Renewal.forceCoord hd)
      (Renewal.regenDelta lam) (l / lam) r N m hwidth hg hsurvive
  exact (measure_mono_ae hsub).trans
    (measure_failedSuccessfulBlocks_le Q.measure K hK.1 (Renewal.regenDelta lam)
      δ hδ hδ1 hK.2.2.2.1 0 N m)

end EinsteinFull.Regeneration
