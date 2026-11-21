import EinsteinFull.Regeneration.SlabInitialEnergy

/-!
# Uniform initial slab scale

At the source transverse radius the cutoff constant is uniformly bounded,
so the initial energy terms share a single exponential envelope.
-/

namespace EinsteinFull.Regeneration

/-- The profile and cutoff errors have a uniform initial-energy envelope. -/
theorem slab_initial_source_terms_le (n : ℕ) (s lam Λ L : ℝ)
    (hs : 0 < s) (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hL : 1 ≤ L) :
    let d : ℝ := n + 1
    let R := Real.exp (s * L / d)
    let α := (Λ + 4 * Λ ^ 2 / lam) * (4 * ((32 * d) / (R / 2)) ^ 2)
    let D := 3 * Λ * Real.exp s * 2 ^ n +
      2 * ((Λ + 4 * Λ ^ 2 / lam) * (4 * (64 * d) ^ 2)) * (2 ^ n / s)
    3 * (Λ * (Real.exp s * 2 ^ n * Real.exp (-(s * L / d)))) +
      2 * α * ((2 ^ n / s) * Real.exp ((s * (2 * d - 1) / d) * L)) ≤
      D * Real.exp ((s * (2 * d - 1) / d) * L) := by
  dsimp only
  let d : ℝ := n + 1
  let R := Real.exp (s * L / d)
  let K : ℝ := (32 * d) / (R / 2)
  let K₀ : ℝ := 64 * d
  let C : ℝ := Λ + 4 * Λ ^ 2 / lam
  let P : ℝ := Real.exp ((s * (2 * d - 1) / d) * L)
  have hd : 0 < d := by dsimp [d]; positivity
  have hL0 : 0 ≤ L := by linarith
  have hR : 1 ≤ R := by
    dsimp [R]
    exact Real.one_le_exp (div_nonneg (mul_nonneg hs.le hL0) hd.le)
  have hK0 : 0 ≤ K := by dsimp [K, R]; positivity
  have hKmax : K ≤ K₀ := by
    dsimp only [K, K₀]
    apply (div_le_iff₀ (by positivity : 0 < R / 2)).2
    nlinarith
  have hKsq : K ^ 2 ≤ K₀ ^ 2 := pow_le_pow_left₀ hK0 hKmax 2
  have hC : 0 ≤ C := by dsimp [C]; exact add_nonneg hΛ (div_nonneg (by positivity) hlam.le)
  have hα : C * (4 * K ^ 2) ≤ C * (4 * K₀ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hC
    nlinarith
  have hexps : Real.exp (-(s * L / d)) ≤ P := by
    apply Real.exp_le_exp.mpr
    have hfactor : 0 ≤ 2 * d - 1 := by
      have hn : (0 : ℝ) ≤ n := by positivity
      dsimp [d]
      linarith
    have hrate : 0 ≤ (s * (2 * d - 1) / d) * L := by positivity
    have hneg : -(s * L / d) ≤ 0 := neg_nonpos.mpr (div_nonneg (mul_nonneg hs.le hL0) hd.le)
    linarith
  have hB : 0 ≤ (2 : ℝ) ^ n / s := by positivity
  have hP : 0 ≤ P := (Real.exp_pos _).le
  have hprof := mul_le_mul_of_nonneg_left hexps
    (show 0 ≤ 3 * Λ * Real.exp s * (2 : ℝ) ^ n by positivity)
  have herror := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα
    (show 0 ≤ 2 by norm_num)) (mul_nonneg hB hP)
  change 3 * (Λ * (Real.exp s * 2 ^ n * Real.exp (-(s * L / d)))) +
      2 * (C * (4 * K ^ 2)) * ((2 ^ n / s) * P) ≤
    (3 * Λ * Real.exp s * 2 ^ n + 2 * (C * (4 * K₀ ^ 2)) * (2 ^ n / s)) * P
  nlinarith only [hprof, herror]

end EinsteinFull.Regeneration
