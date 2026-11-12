import EinsteinRelation.External.GilbargTrudinger

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Half-Hölder bounds survive spatial dilation and scalar multiplication.
Source: `paper/main.tex:735-743`. -/
theorem exists_holderBound_half_dilation {d : ℕ}
    (f : Vec d → ℝ) (R s r c K : ℝ) (hs : 0 < s) (_hr : 0 < r)
    (hsr : s * r ≤ R) (hf : HolderBound (ball 0 R) (1 / 2) f K) :
    ∃ C : ℝ, HolderBound (ball 0 r) (1 / 2) (fun x => c * f (s • x)) C := by
  rcases hf with ⟨S, H, hS, hH, hK, hS_bound, hH_bound⟩
  set C := |c| * (S + H * (s ^ (1/2 : ℝ))) with hC_def
  refine ⟨C, ?_⟩
  set S' := |c| * S with hS'_def
  set H' := |c| * H * (s ^ (1/2 : ℝ)) with hH'_def
  have hS'_nonneg : 0 ≤ S' := by
    rw [hS'_def]
    exact mul_nonneg (abs_nonneg c) hS
  have hsqrt_nonneg : 0 ≤ s ^ (1/2 : ℝ) := Real.rpow_nonneg hs.le (1/2 : ℝ)
  have hH'_nonneg : 0 ≤ H' := by
    rw [hH'_def]
    have h_abs_c : 0 ≤ |c| := abs_nonneg c
    have h_mul : 0 ≤ |c| * H := mul_nonneg h_abs_c hH
    exact mul_nonneg h_mul hsqrt_nonneg
  have h_sum_eq : S' + H' = C := by
    rw [hS'_def, hH'_def, hC_def]
    ring
  have h_sum_le : S' + H' ≤ C := le_of_eq h_sum_eq
  refine ⟨S', H', hS'_nonneg, hH'_nonneg, h_sum_le, ?_, ?_⟩
  · -- sup bound
    intro x hx
    dsimp [ball] at hx
    have hx_norm : euclideanNorm x < r := by simpa using hx
    have hx' : s • x ∈ ball 0 R := by
      dsimp [ball]
      calc
        euclideanNorm (s • x - 0) = euclideanNorm (s • x) := by simp
        _ = s * euclideanNorm x := Environment.AKMTestIntegralSupport.euclideanNorm_smul s hs.le x
        _ < s * r := mul_lt_mul_of_pos_left hx_norm hs
        _ ≤ R := hsr
    dsimp
    rw [hS'_def]
    calc
      |c * f (s • x)| = |c| * |f (s • x)| := abs_mul c (f (s • x))
      _ ≤ |c| * S := mul_le_mul_of_nonneg_left (hS_bound (s • x) hx') (abs_nonneg c)
  · -- Hölder seminorm
    intro x hx y hy
    dsimp [ball] at hx hy
    have hx_norm : euclideanNorm x < r := by simpa using hx
    have hy_norm : euclideanNorm y < r := by simpa using hy
    have hx' : s • x ∈ ball 0 R := by
      dsimp [ball]
      calc
        euclideanNorm (s • x - 0) = euclideanNorm (s • x) := by simp
        _ = s * euclideanNorm x := Environment.AKMTestIntegralSupport.euclideanNorm_smul s hs.le x
        _ < s * r := mul_lt_mul_of_pos_left hx_norm hs
        _ ≤ R := hsr
    have hy' : s • y ∈ ball 0 R := by
      dsimp [ball]
      calc
        euclideanNorm (s • y - 0) = euclideanNorm (s • y) := by simp
        _ = s * euclideanNorm y := Environment.AKMTestIntegralSupport.euclideanNorm_smul s hs.le y
        _ < s * r := mul_lt_mul_of_pos_left hy_norm hs
        _ ≤ R := hsr
    have hnorm_nonneg : 0 ≤ euclideanNorm (x - y) := Real.sqrt_nonneg _
    have h_mul_rpow : (s * euclideanNorm (x - y)) ^ (1/2 : ℝ) =
        s ^ (1/2 : ℝ) * (euclideanNorm (x - y)) ^ (1/2 : ℝ) :=
      Real.mul_rpow (z := 1/2) hs.le hnorm_nonneg
    dsimp
    have htemp : euclideanNorm (s • (x - y)) = s * euclideanNorm (x - y) :=
      Environment.AKMTestIntegralSupport.euclideanNorm_smul s hs.le (x - y)
    calc
      |(c * f (s • x)) - (c * f (s • y))| = |c * (f (s • x) - f (s • y))| := by
        congr 1
        ring
      _ = |c| * |f (s • x) - f (s • y)| := abs_mul c (f (s • x) - f (s • y))
      _ ≤ |c| * (H * euclideanNorm ((s • x) - (s • y)) ^ (1/2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hH_bound (s • x) hx' (s • y) hy') (abs_nonneg c)
      _ = |c| * H * euclideanNorm ((s • x) - (s • y)) ^ (1/2 : ℝ) := by ring
      _ = |c| * H * euclideanNorm (s • (x - y)) ^ (1/2 : ℝ) := by
        rw [← smul_sub s x y]
      _ = |c| * H * (s * euclideanNorm (x - y)) ^ (1/2 : ℝ) := by
        rw [htemp]
      _ = |c| * H * (s ^ (1/2 : ℝ) * (euclideanNorm (x - y)) ^ (1/2 : ℝ)) := by
        rw [h_mul_rpow]
      _ = (|c| * H * (s ^ (1/2 : ℝ))) * ((euclideanNorm (x - y)) ^ (1/2 : ℝ)) := by ring
      _ = H' * ((euclideanNorm (x - y)) ^ (1/2 : ℝ)) := by rw [hH'_def]
