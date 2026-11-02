import EinsteinRelation.Correctors.AKMParabolicIntegrability
import EinsteinRelation.Entropy.FisherCauchySchwarz
import Mathlib.Tactic

/-! # Absorption of the paired cutoff cross term

Source: `paper/main.tex:822–830`. Completing an actual Euclidean square
absorbs the cutoff error for symmetric anisotropic coefficients.
-/

namespace EinsteinRelation.Correctors

open Environment.AKMTestIntegralSupport

/-- The weighted principal energy controls the cutoff cross term, with
an explicit `4 n² K²` error. Source: `paper/main.tex:822–830`. -/
theorem paired_cutoff_coercivity {d : ℕ} {K : ℝ} (hK : 0 < K)
    (A : Coefficient d K) (x g h : Vec d) (v χ : ℝ) (_hχ : 0 ≤ χ)
    (n : ℕ) (hn : 1 ≤ n) :
    χ^(2*n) * euclideanSq g ≤
      2 * (χ^(2*n) * dot g ((A x).mulVec g) +
        (2*n : ℕ) * χ^(2*n-1) * v * dot ((A x).mulVec g) h) +
      4*(n : ℝ)^2*K^2*χ^(2*n-2)*v^2*euclideanSq h := by
  let α := χ^n
  let β := 2*(n : ℝ)*χ^(n-1)*v
  have hbound := mulVec_euclideanNorm_le_of_quadratic (A x) hK (A.symmetric x)
    (fun w => (euclideanSq_nonneg_fisher w).trans (A.elliptic x w).1)
    (fun w => (A.elliptic x w).2) h
  have hsq : euclideanSq ((A x).mulVec h) ≤ K^2 * euclideanSq h := by
    have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hK.le (Real.sqrt_nonneg _))).2 hbound
    simpa only [euclideanNorm, mul_pow, Real.sq_sqrt (euclideanSq_nonneg_fisher _)] using hs
  have hcross : dot g ((A x).mulVec h) = dot ((A x).mulVec g) h := by
    rw [dot_mulVec_swap (A x) (A.symmetric x)]
    exact dotProduct_comm _ _
  have he : euclideanSq (α • g + β • ((A x).mulVec h)) =
      α^2 * euclideanSq g + 2*α*β*dot ((A x).mulVec g) h +
        β^2 * euclideanSq ((A x).mulVec h) := by
    change dotProduct (α • g + β • ((A x).mulVec h))
      (α • g + β • ((A x).mulVec h)) = _
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    change α * (α * dot g g + β * dot ((A x).mulVec h) g) +
      β * (α * dot g ((A x).mulVec h) + β * dot ((A x).mulVec h) ((A x).mulVec h)) = _
    rw [show dot ((A x).mulVec h) g = dot g ((A x).mulVec h) from dotProduct_comm _ _, hcross]
    unfold euclideanSq
    ring
  have hp := euclideanSq_nonneg_fisher (α • g + β • ((A x).mulVec h))
  rw [he] at hp
  have hE := mul_le_mul_of_nonneg_left (A.elliptic x g).1 (sq_nonneg α)
  have hErr := mul_le_mul_of_nonneg_left hsq (sq_nonneg β)
  have hmain : α^2 * euclideanSq g ≤
      2 * (α^2 * dot g ((A x).mulVec g) + α*β*dot ((A x).mulVec g) h) +
        β^2 * (K^2 * euclideanSq h) := by
    nlinarith only [hp, hE, hErr]
  have hα : α^2 = χ^(2*n) := by
    dsimp only [α]
    rw [← pow_mul, Nat.mul_comm]
  have hαβ : α*β = 2*(n : ℝ)*χ^(2*n-1)*v := by
    have hn' : n + (n-1) = 2*n-1 := by omega
    dsimp only [α, β]
    calc
      χ^n * (2*(n : ℝ)*χ^(n-1)*v) = 2*(n : ℝ)*(χ^n*χ^(n-1))*v := by ring
      _ = _ := by rw [← pow_add, hn']
  have hβ : β^2 = 4*(n : ℝ)^2*χ^(2*n-2)*v^2 := by
    have hn' : (n-1)*2 = 2*n-2 := by omega
    dsimp only [β]
    simp only [mul_pow, ← pow_mul, hn']
    ring
  rw [hα, hαβ, hβ] at hmain
  push_cast
  convert hmain using 1
  ring

end EinsteinRelation.Correctors
