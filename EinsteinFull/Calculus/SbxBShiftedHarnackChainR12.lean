import EinsteinFull.Calculus.C9TubeNativeHarnackComparison
import EinsteinFull.Calculus.SbxBCappedTubeChainR02

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology

namespace EinsteinFull.Calculus

/-- A scaled pointwise comparison on one parabolic cylinder. The two points
are separated by at most one quarter of the square root of the elapsed time. -/
def BScaledUnitPointwiseHarnack (d : ℕ) (κ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (T : ℝ), 0 < T →
    ∀ (v : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo 0 (2*T)) (sourceBall 0 R) v G →
    ContinuousOn v (Set.Ioo 0 (2*T) ×ˢ sourceBall 0 R) →
    (∀ p ∈ Set.Ioo 0 (2*T) ×ˢ sourceBall 0 R, 0 ≤ v p) →
    ∀ (s δ : ℝ), 0 < δ → 0 < s - δ → s + 2*δ < 2*T →
    ∀ x y : Vec d, sourceBall x (2*Real.sqrt δ) ⊆ sourceBall 0 R →
    euclideanNorm (y-x)^2 ≤ δ/16 → v (s,x) ≤ C * v (s+δ,y)

/-- Iteration of one-step comparisons, with a constant fixed before the
function and the points being compared. -/
theorem b_pointwise_chain_iterate (C : ℝ) (hC : 0 ≤ C) (n : ℕ)
    (a : ℕ → ℝ) (hstep : ∀ k < n, a k ≤ C * a (k+1)) :
    a 0 ≤ C ^ n * a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
    have hlast := hstep n (Nat.lt_succ_self n)
    calc
      a 0 ≤ C ^ n * a n := hprev
      _ ≤ C ^ n * (C * a (n+1)) :=
        mul_le_mul_of_nonneg_left hlast (pow_nonneg hC n)
      _ = C ^ (n+1) * a (n+1) := by rw [pow_succ]; ring

/-- A bounded Euclidean displacement is traversed in finitely many local
parabolic comparisons. The constant depends only on the unit constant and
on the two prescribed displacement parameters. -/
theorem b_shifted_pointwise_harnack_of_scaled_unit
    (d : ℕ) (κ A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    (hunit : BScaledUnitPointwiseHarnack d κ) :
    ∃ H : ℝ, 0 < H ∧ ∀ (R : ℝ), 0 < R →
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (t : ℝ), 0 < t → ∀ (v : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo 0 (2*t)) (sourceBall 0 R) v G →
      ContinuousOn v (Set.Ioo 0 (2*t) ×ˢ sourceBall 0 R) →
      (∀ p ∈ Set.Ioo 0 (2*t) ×ˢ sourceBall 0 R, 0 ≤ v p) →
      ∀ z ∈ sourceBall (0 : Vec d) R, ∀ y ∈ sourceBall (0 : Vec d) R,
      sourceBall y ((A+B+2)*Real.sqrt t) ⊆ sourceBall 0 R →
      euclideanNorm (z-y) ≤ (A+B)*Real.sqrt t →
      v (t/4,z) ≤ H * v (3*t/4,y) := by
  obtain ⟨C, hC, hlocal⟩ := hunit
  have hD : 0 ≤ A+B := by linarith
  obtain ⟨n, hn, hnτ, hncap, _, hndist⟩ :=
    b_exists_capped_native_substeps (1/2) 1 (1/16) 8 (4*(A+B))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let q : ℝ := (1/2 : ℝ) / n
  have hq : 0 < q := hnτ
  have hqcap : q ≤ 1/16 := by simpa [q] using hncap
  have hqdist : ((A+B)/(n : ℝ))^2 ≤ q/16 := by
    have heq : ((4*(A+B))/(n : ℝ))^2 = 16*((A+B)/(n : ℝ))^2 := by ring
    rw [heq] at hndist
    linarith
  refine ⟨C^n, pow_pos hC n, ?_⟩
  intro R hR ρ α hell t ht v G hcal hcont hnonneg z hz y hy hball hzy
  let δ : ℝ := t*q
  have hδ : 0 < δ := mul_pos ht hq
  have hδcap : δ ≤ t/16 := by
    dsimp [δ]
    nlinarith [mul_le_mul_of_nonneg_left hqcap ht.le]
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsqδ : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  have hsqδlt : Real.sqrt δ < Real.sqrt t := Real.sqrt_lt_sqrt hδ.le (by linarith)
  have hsqpow : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hxy : euclideanNorm (y-z) ≤ (A+B)*Real.sqrt t := by
    simpa only [← neg_sub z y, Entropy.euclideanNorm_neg'] using hzy
  have hscaled : (((A+B)*Real.sqrt t)/(n : ℝ))^2 ≤ δ/16 := by
    have hh := mul_le_mul_of_nonneg_right hqdist ht.le
    dsimp [δ]
    rw [← hsqpow] at hh
    nlinarith [sq_nonneg ((A+B)/(n : ℝ) * Real.sqrt t),
      show (((A+B)*Real.sqrt t)/(n : ℝ))^2 =
        ((A+B)/(n : ℝ))^2 * Real.sqrt t^2 by ring]
  have hmarginz : euclideanNorm (z-y) + 2*Real.sqrt δ <
      (A+B+2)*Real.sqrt t := by nlinarith
  have hmarginy : euclideanNorm (y-y) + 2*Real.sqrt δ <
      (A+B+2)*Real.sqrt t := by
    simp only [sub_self, euclideanNorm, euclideanSq, dot, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, Real.sqrt_zero, zero_add]
    nlinarith [mul_nonneg hD hsq.le]
  let a : ℕ → ℝ := fun k => v (t/4 + (k : ℝ)*δ, b_tube_segment_center z y n k)
  have hstep : ∀ k < n, a k ≤ C*a (k+1) := by
    intro k hk
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt hk
    have htime0 : 0 < t/4 + (k : ℝ)*δ - δ := by
      have : 0 ≤ (k : ℝ)*δ := by positivity
      linarith
    have htime1 : t/4 + (k : ℝ)*δ + 2*δ < 2*t := by
      have hkn := mul_le_mul_of_nonneg_right hk' hδ.le
      have hnδ : (n : ℝ)*δ = t/2 := by
        dsimp [δ,q]
        field_simp
      nlinarith
    have hinside : sourceBall (b_tube_segment_center z y n k) (2*Real.sqrt δ) ⊆
        sourceBall 0 R := by
      intro w hw
      apply hball
      exact b_equispaced_segment_margin_ball y z y w n k
        ((A+B+2)*Real.sqrt t) (2*Real.sqrt δ) hn (Nat.le_of_lt hk)
        hmarginz hmarginy hw
    have hdist := b_equispaced_segment_step z y n k ((A+B)*Real.sqrt t) (δ/16) hn
      (mul_nonneg hD hsq.le) hxy hscaled
    have h := hlocal R hR ρ α hell t ht v G hcal hcont hnonneg
      (t/4 + (k : ℝ)*δ) δ hδ htime0 htime1 _ _ hinside hdist
    have htime : t/4 + ((k+1 : ℕ) : ℝ)*δ = t/4 + (k : ℝ)*δ + δ := by
      push_cast
      ring
    simpa only [a, htime] using h
  have hiter := b_pointwise_chain_iterate C hC.le n a hstep
  have hend := b_tube_segment_center_endpoints z y n hn
  have hnδ : (n : ℝ)*δ = t/2 := by
    dsimp [δ,q]
    field_simp
  have htime : t/4 + t/2 = 3*t/4 := by ring
  simpa [a, hend.1, hend.2, hnδ, htime] using hiter

#print axioms b_shifted_pointwise_harnack_of_scaled_unit

end EinsteinFull.Calculus
