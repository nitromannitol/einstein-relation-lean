import EinsteinFull.Calculus.C18TubeUniformNearDiagonalAssembly
import EinsteinFull.Calculus.C11TubeRescaledWeightedSemigroup
import EinsteinFull.Calculus.C12TubeNativeLowerChaining
import EinsteinFull.Calculus.C13TubeKilledComparison
import EinsteinFull.Calculus.SunaS7SuppliedKilledFDD

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open scoped ENNReal NNReal

namespace EinsteinFull.Calculus

/-- Every positive-time strict-survival endpoint row of the supplied law
is absolutely continuous with respect to volume, for every starting point. -/
theorem c12_supplied_killed_endpoint_absolutelyContinuous {d : ℕ}
    {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
    {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    EinsteinFull.gmpKilledEndpointKernel G U hU t x ≪ (volume : Measure (Vec d)) := by
  exact EinsteinFull.gmpKilledEndpointKernel_absolutelyContinuous_volume G U hU t ht x

/-- A weighted kernel chain using the quarter-distance near-diagonal bound. -/
theorem c12_quarter_near_diagonal_finite_chain {d : ℕ} (R h κ c v : ℝ)
    (hR : 0 < R) (hh : 0 < h) (hhR : h ≤ R^2) (hκ : 0 < κ) (hc : 0 < c)
    (hv : 0 ≤ v) (ρ : Vec d → ℝ) (q : ℝ → Vec d → Vec d → ℝ)
    (hρ : ∀ z, κ ≤ ρ z) (hq : ∀ s, 0 < s → ∀ x y, 0 ≤ q s x y)
    (hint : ∀ s t, 0 < s → 0 < t → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
      IntegrableOn (fun z => q s x z * q t z y * ρ z) (sourceBall 0 R))
    (hsemi : ∀ s t, 0 < s → 0 < t → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
      q (s+t) x y = ∫ z in sourceBall 0 R, q s x z * q t z y * ρ z)
    (hnear : ∀ s, 0 < s → s ≤ R^2 → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
      euclideanSq (x-y) ≤ s/4 → c * Real.rpow s (-(d : ℝ)/2) ≤ q s x y)
    (S : ℕ → Set (Vec d)) (hS : ∀ n, MeasurableSet (S n))
    (hSU : ∀ n, S n ⊆ sourceBall 0 R)
    (hvol : ∀ n, v ≤ (volume (S n)).toReal)
    (hstep : ∀ n, ∀ x ∈ S n, ∀ y ∈ S (n+1), euclideanSq (x-y) ≤ h/4)
    (x : Vec d) (hx : x ∈ S 0) :
    ∀ n y, y ∈ S (n+1) →
      (c * Real.rpow h (-(d : ℝ)/2)) *
        ((c * Real.rpow h (-(d : ℝ)/2)) * κ * v)^n ≤ q ((n+1 : ℕ) * h) x y := by
  let U : Set (Vec d) := sourceBall 0 R
  have hfin : volume U ≠ ⊤ := (c12_sourceBall_volume (0 : Vec d) hR).2.1
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hfin
  have hv' : ∀ n, v ≤ ((volume.restrict U) (S n)).toReal := by
    intro n
    rw [Measure.restrict_apply (hS n), Set.inter_eq_left.mpr (hSU n)]
    exact hvol n
  have hstep' : ∀ n, ∀ x ∈ S n, ∀ y ∈ S (n+1),
      c * Real.rpow h (-(d : ℝ)/2) ≤ q h x y := by
    intro n x hx y hy
    exact hnear h hh hhR x (hSU n hx) y (hSU (n+1) hy) (hstep n x hx y hy)
  exact c12_weighted_real_semigroup_finite_chain (volume.restrict U) ρ κ
    (c * Real.rpow h (-(d : ℝ)/2)) v h hκ.le
    (mul_nonneg hc.le (Real.rpow_pos_of_pos hh _).le) hv hh hρ q hq U S hS hSU
    hv' hstep' hint hsemi x hx

/-- Chain geometry for a near-diagonal estimate at squared radius `h / 4`. -/
theorem c12_quarter_chain_admissible_balls {d : ℕ} (R t : ℝ) (hR : 0 < R)
    (ht : 0 < t) (htR : t ≤ R^2 / 64) (x y : Vec d)
    (hx : x ∈ sourceBall 0 (R/2)) (hy : y ∈ sourceBall 0 (R/2)) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 16 * euclideanSq (x-y) / t + 2 ∧
      let h := t / (N : ℝ)
      ∃ S : ℕ → Set (Vec d),
        (∀ n, MeasurableSet (S n) ∧ S n ⊆ sourceBall 0 R ∧
          (volume (S n)).toReal = (Real.sqrt (h/4) / 8)^d *
            (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal ∧
          ∀ z ∈ S n, ∀ w ∈ S (n+1), euclideanSq (z-w) ≤ h/4) ∧
        x ∈ S 0 ∧ y ∈ S N := by
  have ht4 : 0 < t/4 := by positivity
  have ht4R : t/4 ≤ R^2/64 := by nlinarith [sq_nonneg R]
  obtain ⟨N, hN, hbound, S, hS, hxS, hyS⟩ :=
    c12_chain_admissible_balls R (t/4) hR ht4 ht4R x y hx hy
  refine ⟨N, hN, ?_, S, ?_, hxS, hyS⟩
  · convert hbound using 1 <;> ring
  · intro n
    convert hS n using 1 <;> congr 2 <;> ring

/-- Quarter-distance chain with a prescribed step-time cap and interior margin. -/
theorem c12_quarter_chain_balls_with_time_cap {d : ℕ} (R t τ : ℝ)
    (hR : 0 < R) (ht : 0 < t) (hτ : 0 < τ) (htR : t ≤ R^2/64)
    (x y : Vec d) (hx : x ∈ sourceBall 0 (R/2)) (hy : y ∈ sourceBall 0 (R/2)) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 16 * euclideanSq (x-y) / t + t/τ + 2 ∧
      let h := t / (N : ℝ)
      h ≤ τ ∧ ∃ S : ℕ → Set (Vec d),
        (∀ n, MeasurableSet (S n) ∧ S n ⊆ sourceBall 0 (3*R/4) ∧
          (volume (S n)).toReal = (Real.sqrt (h/4) / 8)^d *
            (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal ∧
          ∀ z ∈ S n, ∀ w ∈ S (n+1), euclideanSq (z-w) ≤ h/4) ∧
        x ∈ S 0 ∧ y ∈ S N := by
  have hsym (z w : Vec d) : euclideanSq (z-w) = euclideanSq (w-z) := by
    unfold euclideanSq dot
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.sub_apply]
    ring
  have hD : 0 ≤ euclideanSq (x-y) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  let D := euclideanSq (x-y) + t^2 / (16*τ)
  have hD' : 0 ≤ D := by dsimp [D]; positivity
  have ht4 : 0 < t/4 := by positivity
  obtain ⟨N, hN, hlo, hhi⟩ := c12_chain_step_count D (t/4) hD' ht4
  have hformula : 4 * D / (t/4) = 16 * euclideanSq (x-y) / t + t/τ := by
    dsimp [D]
    field_simp
    <;> ring
  rw [hformula] at hlo hhi
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let h : ℝ := t / (N : ℝ)
  have hh : 0 < h := div_pos ht hNr
  have hcap : h ≤ τ := by
    apply (div_le_iff₀ hNr).2
    have htτ : t/τ ≤ (N : ℝ) := by
      have : 0 ≤ 16 * euclideanSq (x-y) / t := by positivity
      linarith
    have := (div_le_iff₀ hτ).1 htτ
    nlinarith
  have hNt : 4 * euclideanNorm (y-x)^2 ≤ (N : ℝ) * (t/4) := by
    rw [← TimeChange.euclideanSq_eq_sq_euclideanNorm, ← hsym]
    have hd : 16 * euclideanSq (x-y) / t ≤ (N : ℝ) := by
      have : 0 ≤ t/τ := by positivity
      linarith
    have := (div_le_iff₀ ht).1 hd
    nlinarith
  have hstep := c12_chain_step_length (euclideanNorm (y-x)) (t/4) N
    (Real.sqrt_nonneg _) ht4 hNr hNt
  let u : ℕ → ℝ := fun k => (min k N : ℕ) / (N : ℝ)
  let a : ℕ → Vec d := fun k => (1-u k) • x + u k • y
  have ha0 : a 0 = x := by simp [a, u]
  have haN : a N = y := by simp [a, u, ne_of_gt hNr]
  have hcent := c12_chain_centers N hN (R/2) (h/4) x y hx hy (by
    convert hstep using 1 <;> dsimp [h] <;> congr 2 <;> ring)
  have hle : h ≤ t := by
    dsimp [h]
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    exact div_le_self ht.le hn
  have hs : Real.sqrt (h/4) ≤ R := by
    have hs2 := Real.sq_sqrt (show 0 ≤ h/4 by positivity)
    have hs0 := Real.sqrt_nonneg (h/4)
    nlinarith [sq_nonneg R]
  have hball := c12_chain_balls N (R/2) (3*R/4) (h/4) (by positivity)
    a x y ha0 haN hcent.1 hcent.2 (by linarith)
  refine ⟨N, hN, hhi, hcap, ?_⟩
  let S : ℕ → Set (Vec d) := fun n => sourceBall (a n) (Real.sqrt (h/4) / 8)
  refine ⟨S, ?_, hball.2⟩
  intro n
  obtain ⟨hm, hsub, hv, hd⟩ := hball.1 n
  refine ⟨hm, hsub, hv, ?_⟩
  intro z hz w hw
  rw [hsym z w]
  exact hd z hz w hw

/-- The quarter-radius chain retains a positive time-independent volume factor. -/
theorem c12_quarter_chain_volume_time_cancellation (d : ℕ) (h : ℝ) (hh : 0 < h) :
    Real.rpow h (-(d : ℝ)/2) * (Real.sqrt (h/4)/8)^d = (16 : ℝ)⁻¹^d := by
  have hs : Real.sqrt (h/4) = Real.sqrt h / 2 := by
    rw [Real.sqrt_div hh.le]
    norm_num
  rw [hs]
  have heq : Real.sqrt h / 2 / 8 = (Real.sqrt h / 8) * (1/2 : ℝ) := by ring
  rw [heq, mul_pow, ← mul_assoc, c12_chain_volume_time_cancellation d h hh, ← mul_pow]
  norm_num

open Classical in
/-- A quarter-distance chain for the actual rescaled normalized spectral kernel. -/
theorem c12_rescaled_normalized_quarter_chain {d : ℕ}
    (S t κ c lam : ℝ) (hS : 0 < S) (ht : 0 < t) (htS : t ≤ S^2/64)
    (hκ : 0 < κ) (hc : 0 < c) (ρ : Vec d → ℝ)
    (K : ℝ → Vec d → Vec d → ℝ) (x y : Vec d)
    (hx : x ∈ sourceBall 0 (S/2)) (hy : y ∈ sourceBall 0 (S/2)) :
    let q : ℝ → Vec d → Vec d → ℝ := fun s x y =>
      if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
        (lam⁻¹)^d * K (s / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
    let w : Vec d → ℝ := fun z => max κ (ρ (lam⁻¹ • z))
    (∀ s, 0 < s → ∀ x y, 0 ≤ q s x y) →
    (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      IntegrableOn (fun z => q s x z * q u z y * w z) (sourceBall 0 S)) →
    (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      q (s+u) x y = ∫ z in sourceBall 0 S, q s x z * q u z y * w z) →
    (∀ s, 0 < s → s ≤ S^2 → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      euclideanSq (x-y) ≤ s/4 → c*Real.rpow s (-(d:ℝ)/2) ≤ q s x y) →
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 16 * euclideanSq (x-y) / t + 2 ∧
      let h := t / (N : ℝ)
      let v := (Real.sqrt (h/4) / 8)^d *
        (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal
      (c * Real.rpow h (-(d:ℝ)/2)) *
        ((c * Real.rpow h (-(d:ℝ)/2)) * κ * v)^(N-1) ≤ q t x y := by
  dsimp only
  intro hq hint hsemi hnear
  obtain ⟨N, hN, hbound, B, hB, hxB, hyB⟩ :=
    c12_quarter_chain_admissible_balls S t hS ht htS x y hx hy
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  let h : ℝ := t / (n+1 : ℕ)
  let v : ℝ := (Real.sqrt (h/4) / 8)^d *
    (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal
  have hh : 0 < h := by dsimp [h]; positivity
  have hle : h ≤ t := by
    dsimp [h]
    exact div_le_self ht.le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
  have hhS : h ≤ S^2 := by nlinarith [sq_nonneg S]
  have hv : 0 ≤ v := by
    dsimp [v]
    positivity
  have hchain := c12_quarter_near_diagonal_finite_chain S h κ c v hS hh hhS hκ hc hv
    (fun z => max κ (ρ (lam⁻¹ • z))) _ (fun z => le_max_left _ _) hq hint hsemi hnear
    B (fun n => (hB n).1) (fun n => (hB n).2.1)
    (fun n => by rw [(hB n).2.2.1]) (fun n => (hB n).2.2.2) x hxB n y hyB
  have htime : ((n+1 : ℕ) : ℝ) * h = t := by dsimp [h]; field_simp
  rw [htime] at hchain
  refine ⟨n+1, by omega, hbound, ?_⟩
  simpa only [Nat.add_sub_cancel] using hchain

open Classical in
/-- A rescaled native-kernel chain using only interior local quarter bounds. -/
theorem c12_rescaled_normalized_local_quarter_chain {d : ℕ}
    (S t τ κ c lam : ℝ) (hS : 0 < S) (ht : 0 < t) (hτ : 0 < τ)
    (htS : t ≤ S^2/64) (hκ : 0 < κ) (hc : 0 < c)
    (ρ : Vec d → ℝ) (K : ℝ → Vec d → Vec d → ℝ) (x y : Vec d)
    (hx : x ∈ sourceBall 0 (S/2)) (hy : y ∈ sourceBall 0 (S/2)) :
    let q : ℝ → Vec d → Vec d → ℝ := fun s x y =>
      if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
        (lam⁻¹)^d * K (s / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
    let w : Vec d → ℝ := fun z => max κ (ρ (lam⁻¹ • z))
    (∀ s, 0 < s → ∀ x y, 0 ≤ q s x y) →
    (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      IntegrableOn (fun z => q s x z * q u z y * w z) (sourceBall 0 S)) →
    (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      q (s+u) x y = ∫ z in sourceBall 0 S, q s x z * q u z y * w z) →
    (∀ s, 0 < s → s ≤ τ → ∀ x ∈ sourceBall 0 (3*S/4),
      ∀ y ∈ sourceBall 0 (3*S/4), euclideanSq (x-y) ≤ s/4 →
        c*Real.rpow s (-(d:ℝ)/2) ≤ q s x y) →
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 16 * euclideanSq (x-y) / t + t/τ + 2 ∧
      let h := t / (N : ℝ)
      let v := (Real.sqrt (h/4) / 8)^d *
        (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal
      (c * Real.rpow h (-(d:ℝ)/2)) *
        ((c * Real.rpow h (-(d:ℝ)/2)) * κ * v)^(N-1) ≤ q t x y := by
  dsimp only
  intro hq hint hsemi hnear
  let q : ℝ → Vec d → Vec d → ℝ := fun s x y =>
    if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
      (lam⁻¹)^d * K (s / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
  let w : Vec d → ℝ := fun z => max κ (ρ (lam⁻¹ • z))
  obtain ⟨N, hN, hbound, hcap, B, hB, hxB, hyB⟩ :=
    c12_quarter_chain_balls_with_time_cap S t τ hS ht hτ htS x y hx hy
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  let h : ℝ := t / (n+1 : ℕ)
  let v : ℝ := (Real.sqrt (h/4) / 8)^d *
    (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal
  have hh : 0 < h := by dsimp [h]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  let U : Set (Vec d) := sourceBall 0 S
  have hfin : volume U ≠ ⊤ := (c12_sourceBall_volume (0 : Vec d) hS).2.1
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hfin
  have hsub : ∀ k, B k ⊆ U := by
    intro k z hz
    have hz' := (hB k).2.1 hz
    change euclideanNorm (z - 0) < 3*S/4 at hz'
    change euclideanNorm (z - 0) < S
    linarith
  have hvol : ∀ k, v ≤ ((volume.restrict U) (B k)).toReal := by
    intro k
    rw [Measure.restrict_apply (hB k).1, Set.inter_eq_left.mpr (hsub k), (hB k).2.2.1]
  have hstep : ∀ k, ∀ z ∈ B k, ∀ z' ∈ B (k+1),
      c * Real.rpow h (-(d:ℝ)/2) ≤ q h z z' := by
    intro k z hz z' hz'
    exact hnear h hh hcap z ((hB k).2.1 hz) z' ((hB (k+1)).2.1 hz')
      ((hB k).2.2.2 z hz z' hz')
  have hchain := c12_weighted_real_semigroup_finite_chain (volume.restrict U) w κ
    (c * Real.rpow h (-(d : ℝ)/2)) v h hκ.le
    (mul_nonneg hc.le (Real.rpow_pos_of_pos hh _).le) hv hh (fun z => le_max_left _ _)
    q hq U B (fun k => (hB k).1) hsub hvol hstep hint hsemi x hxB n y hyB
  have htime : ((n+1 : ℕ) : ℝ) * h = t := by dsimp [h]; field_simp
  rw [htime] at hchain
  refine ⟨n+1, by omega, hbound, ?_⟩
  simpa only [Nat.add_sub_cancel] using hchain

open Classical in
/-- Gaussian propagation for the rescaled normalized spectral kernel using a
quarter-distance near-diagonal hypothesis. -/
theorem c12_rescaled_normalized_quarter_gaussian {d : ℕ}
    (κ c : ℝ) (hκ : 0 < κ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S t lam : ℝ), 0 < S → 0 < t → t ≤ S^2/64 →
    ∀ (ρ : Vec d → ℝ) (K : ℝ → Vec d → Vec d → ℝ),
    let q : ℝ → Vec d → Vec d → ℝ := fun s x y =>
      if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
        (lam⁻¹)^d * K (s / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
    let w : Vec d → ℝ := fun z => max κ (ρ (lam⁻¹ • z))
    (∀ s, 0 < s → ∀ x y, 0 ≤ q s x y) →
    (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      IntegrableOn (fun z => q s x z * q u z y * w z) (sourceBall 0 S)) →
    (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      q (s+u) x y = ∫ z in sourceBall 0 S, q s x z * q u z y * w z) →
    (∀ s, 0 < s → s ≤ S^2 → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      euclideanSq (x-y) ≤ s/4 → c*Real.rpow s (-(d:ℝ)/2) ≤ q s x y) →
    ∀ x ∈ sourceBall 0 (S/2), ∀ y ∈ sourceBall 0 (S/2),
      C⁻¹ * Real.rpow t (-(d:ℝ)/2) * Real.exp (-C * euclideanSq (x-y) / t) ≤ q t x y := by
  let V : ℝ := (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal
  have hV : 0 < V := by
    have hv := c12_sourceBall_volume (0 : Vec d) (by norm_num : (0 : ℝ) < 1)
    have hp := hv.2.2.1
    rw [hv.2.2.2] at hp
    simpa [V] using hp
  let b : ℝ := c * κ * (16 : ℝ)⁻¹^d * V
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨C, hC, habs⟩ := c12_gaussian_absorb_chain c b hc hb
  refine ⟨4*C, by positivity, ?_⟩
  intro S t lam hS ht htS ρ K q w hq hint hsemi hnear x hx y hy
  obtain ⟨N, hN, hNbound, hchain⟩ :=
    c12_rescaled_normalized_quarter_chain S t κ c lam hS ht htS hκ hc ρ K x y hx hy
      hq hint hsemi hnear
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  let h : ℝ := t / (n+1 : ℕ)
  let v : ℝ := (Real.sqrt (h/4)/8)^d * V
  have hh : 0 < h := by dsimp [h]; positivity
  have hle : h ≤ t := by
    dsimp [h]
    exact div_le_self ht.le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
  have hfactor : (c * Real.rpow h (-(d:ℝ)/2)) * κ * v = b := by
    dsimp [v, b]
    calc
      _ = c * κ * (Real.rpow h (-(d:ℝ)/2) * (Real.sqrt (h/4)/8)^d) * V := by
        simp only [Real.rpow_eq_pow]
        ac_rfl
      _ = _ := by rw [c12_quarter_chain_volume_time_cancellation d h hh]
  change (c * Real.rpow h (-(d:ℝ)/2)) *
    ((c * Real.rpow h (-(d:ℝ)/2)) * κ * v)^n ≤ q t x y at hchain
  rw [hfactor] at hchain
  have hD : 0 ≤ euclideanSq (x-y) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hn : (n : ℝ) ≤ 4 * (4 * euclideanSq (x-y) / t) + 2 := by
    have hn' : (n : ℝ) ≤ (n.succ : ℝ) := by exact_mod_cast Nat.le_succ n
    apply hn'.trans
    convert hNbound using 1 <;> ring
  have hexp : -(d : ℝ)/2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num)
  have hp : Real.rpow t (-(d:ℝ)/2) ≤ Real.rpow h (-(d:ℝ)/2) :=
    Real.rpow_le_rpow_of_nonpos hh hle hexp
  have hbound := habs (4 * euclideanSq (x-y)/t) n (Real.rpow t (-(d:ℝ)/2))
    (by positivity) (Real.rpow_pos_of_pos ht _).le hn
  have hcoeff : (4*C)⁻¹ ≤ C⁻¹ := by
    apply (inv_le_inv₀ (by positivity) hC).2
    linarith
  have heq : -(4*C) * euclideanSq (x-y) / t = -C * (4 * euclideanSq (x-y)/t) := by ring
  rw [heq]
  calc
    _ ≤ C⁻¹ * Real.rpow t (-(d:ℝ)/2) *
        Real.exp (-C * (4 * euclideanSq (x-y)/t)) := by
      gcongr
      exact (Real.rpow_pos_of_pos ht _).le
    _ ≤ c * Real.rpow t (-(d:ℝ)/2) * b^n := hbound
    _ ≤ c * Real.rpow h (-(d:ℝ)/2) * b^n := by gcongr
    _ ≤ q t x y := hchain

/-- A Gaussian lower bound is uniform on two fixed Euclidean balls. -/
theorem c12_fixed_step_density_lower {d : ℕ}
 (q : ℝ → Vec d → Vec d → ℝ) (t r c C : ℝ)
 (ht : 0 < t) (hr : 0 < r) (hc : 0 < c) (hC : 0 < C)
 (hgauss : ∀ x y, c * Real.rpow t (-(d:ℝ)/2) *
   Real.exp (-C*euclideanSq (x-y)/t) ≤ q t x y)
 (a b : Vec d) (D : ℝ) (hD : 0 ≤ D) (hab : euclideanNorm (a-b) ≤ D) :
 ∃ cstar : ℝ, 0 < cstar ∧ ∀ x ∈ sourceBall a r,
 ∀ y ∈ sourceBall b r, cstar ≤ q t x y := by
  let cstar := c * Real.rpow t (-(d : ℝ)/2) * Real.exp (-C*(D+2*r)^2/t)
  have hpos : 0 < cstar := by dsimp [cstar]; positivity
  refine ⟨cstar, hpos, ?_⟩
  intro x hx y hy
  have hdist := c12_sourceBall_pair_distance r b a y x hy hx
  have hn : 0 ≤ euclideanNorm (x-y) := Real.sqrt_nonneg _
  have hbound : euclideanNorm (x-y) ≤ D + 2*r := by linarith
  have hsq : euclideanSq (x-y) ≤ (D+2*r)^2 := by
    rw [TimeChange.euclideanSq_eq_sq_euclideanNorm]
    nlinarith
  have he : Real.exp (-C*(D+2*r)^2/t) ≤
      Real.exp (-C*euclideanSq (x-y)/t) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (by nlinarith) ht.le
  calc
    cstar ≤ c * Real.rpow t (-(d:ℝ)/2) *
        Real.exp (-C*euclideanSq (x-y)/t) := by
      exact mul_le_mul_of_nonneg_left he (mul_nonneg hc.le (Real.rpow_pos_of_pos ht _).le)
    _ ≤ q t x y := hgauss x y

/-- The same Gaussian constant works for all pairs of centers at bounded
separation and for every kernel satisfying the bound on the two balls. -/
theorem c12_uniform_gaussian_ball_lower {d : ℕ} (t r c C D : ℝ)
    (ht : 0 < t) (hr : 0 < r) (hc : 0 < c) (hC : 0 < C) (hD : 0 ≤ D) :
    ∃ v : ℝ, 0 < v ∧ ∀ (a b : Vec d), euclideanNorm (a-b) ≤ D →
      ∀ (q : ℝ → Vec d → Vec d → ℝ),
      (∀ x ∈ sourceBall a r, ∀ y ∈ sourceBall b r,
        c * Real.rpow t (-(d:ℝ)/2) * Real.exp (-C*euclideanSq (x-y)/t) ≤ q t x y) →
      ∀ x ∈ sourceBall a r, ∀ y ∈ sourceBall b r, v ≤ q t x y := by
  let v := c * Real.rpow t (-(d:ℝ)/2) * Real.exp (-C*(D+2*r)^2/t)
  refine ⟨v, by dsimp [v]; positivity, ?_⟩
  intro a b hab q hgauss x hx y hy
  have hdist := c12_sourceBall_pair_distance r b a y x hy hx
  have hn : 0 ≤ euclideanNorm (x-y) := Real.sqrt_nonneg _
  have hbound : euclideanNorm (x-y) ≤ D + 2*r := by linarith
  have hsq : euclideanSq (x-y) ≤ (D+2*r)^2 := by
    rw [TimeChange.euclideanSq_eq_sq_euclideanNorm]
    nlinarith
  have he : Real.exp (-C*(D+2*r)^2/t) ≤
      Real.exp (-C*euclideanSq (x-y)/t) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (by nlinarith) ht.le
  exact (mul_le_mul_of_nonneg_left he
    (mul_nonneg hc.le (Real.rpow_pos_of_pos ht _).le)).trans (hgauss x hx y hy)

/-- Chaining gives a fixed positive lower bound on two interior balls, with
its constant selected before the density and the heat kernel. -/
theorem c12_fixed_step_native_lower {d : ℕ} (κ c R t r : ℝ)
    (hκ : 0 < κ) (hc : 0 < c) (hR : 0 < R) (ht : 0 < t)
    (htR : t ≤ R^2/64) (hr : 0 < r) (a b : Vec d) (D : ℝ)
    (hD : 0 ≤ D) (hab : euclideanNorm (a-b) ≤ D)
    (ha : sourceBall a r ⊆ sourceBall 0 (R/2))
    (hb : sourceBall b r ⊆ sourceBall 0 (R/2)) :
    ∃ v : ℝ, 0 < v ∧ ∀ (ρ : Vec d → ℝ) (q : ℝ → Vec d → Vec d → ℝ),
      Measurable ρ → (∀ z, κ ≤ ρ z) →
      (∀ s, 0 < s → ∀ x y, 0 ≤ q s x y) →
      (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
        IntegrableOn (fun z => q s x z * q u z y * ρ z) (sourceBall 0 R)) →
      (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
        q (s+u) x y = ∫ z in sourceBall 0 R, q s x z * q u z y * ρ z) →
      (∀ s, 0 < s → s ≤ R^2 → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
        euclideanSq (x-y) ≤ s → c*Real.rpow s (-(d:ℝ)/2) ≤ q s x y) →
      ∀ x ∈ sourceBall a r, ∀ y ∈ sourceBall b r, v ≤ q t x y := by
  obtain ⟨C, hC, hchain⟩ := c12_native_gaussian_lower_of_near_diagonal (d := d) κ c hκ hc
  let model : ℝ → Vec d → Vec d → ℝ := fun s x y =>
    C⁻¹ * Real.rpow s (-(d:ℝ)/2) * Real.exp (-C * euclideanSq (x-y) / s)
  obtain ⟨v, hv, hbound⟩ := c12_fixed_step_density_lower model t r C⁻¹ C ht hr
    (inv_pos.mpr hC) hC (fun _ _ => le_rfl) a b D hD hab
  refine ⟨v, hv, ?_⟩
  intro ρ q hmeas hρ hq hint hsemi hnear x hx y hy
  exact (hbound x hx y hy).trans
    (hchain R hR ρ q hmeas hρ hq hint hsemi hnear t ht htR x (ha hx) y (hb hy))

/-- The chaining lower bound has one constant for every admissible pair of
centers, chosen before the coefficients and kernel. -/
theorem c12_uniform_native_ball_lower {d : ℕ} (κ c R t r D : ℝ)
    (hκ : 0 < κ) (hc : 0 < c) (hR : 0 < R) (ht : 0 < t)
    (htR : t ≤ R^2/64) (hr : 0 < r) (hD : 0 ≤ D) :
    ∃ v : ℝ, 0 < v ∧ ∀ (ρ : Vec d → ℝ) (q : ℝ → Vec d → Vec d → ℝ),
      Measurable ρ → (∀ z, κ ≤ ρ z) →
      (∀ s, 0 < s → ∀ x y, 0 ≤ q s x y) →
      (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
        IntegrableOn (fun z => q s x z * q u z y * ρ z) (sourceBall 0 R)) →
      (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
        q (s+u) x y = ∫ z in sourceBall 0 R, q s x z * q u z y * ρ z) →
      (∀ s, 0 < s → s ≤ R^2 → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
        euclideanSq (x-y) ≤ s → c*Real.rpow s (-(d:ℝ)/2) ≤ q s x y) →
      ∀ (a b : Vec d), euclideanNorm (a-b) ≤ D →
      sourceBall a r ⊆ sourceBall 0 (R/2) →
      sourceBall b r ⊆ sourceBall 0 (R/2) →
      ∀ x ∈ sourceBall a r, ∀ y ∈ sourceBall b r, v ≤ q t x y := by
  obtain ⟨C, hC, hchain⟩ := c12_native_gaussian_lower_of_near_diagonal (d := d) κ c hκ hc
  obtain ⟨v, hv, hbound⟩ := c12_uniform_gaussian_ball_lower (d := d) t r C⁻¹ C D
    ht hr (inv_pos.mpr hC) hC hD
  refine ⟨v, hv, ?_⟩
  intro ρ q hmeas hρ hq hint hsemi hnear a b hab ha hb
  apply hbound a b hab q
  intro x hx y hy
  exact hchain R hR ρ q hmeas hρ hq hint hsemi hnear t ht htR x (ha hx) y (hb hy)

/-- Fixed constants yield literal rescaled tube-piece domination when the
supplied killed endpoint law has the displayed weighted spectral density.
The association hypothesis refers to that same supplied law and kernel. -/
theorem c12_rescaled_piece_lower_of_spectral_association {d : ℕ}
    (eps h c C κ : ℝ) (heps : 0 < eps) (hh : 0 < h)
    (hc : 0 < c) (hC : 0 < C) (hκ : 0 < κ)
    (a b : Vec d) (hab : euclideanNorm (b-a) ≤ eps / 16) :
    ∃ cstar : ℝ, 0 < cstar ∧
    ∀ {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
      {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1},
    ∀ (_ : 0 < lam) (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd L hL ω hω lam h₀ h₁)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d) (R : ℝ)
      (K : ℝ → Vec d → Vec d → ℝ) (gradK : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K gradK →
    (∀ y ∈ sourceBall b (eps/16), κ ≤ ρ (lam⁻¹ • (y-b))) →
    (IsSpectralDirichletFundamentalSolution ρ α R K gradK →
      ∀ x ∈ sourceBall a (eps/16), ∀ y ∈ sourceBall b (eps/16),
      c * Real.rpow h (-(d:ℝ)/2) * Real.exp (-C*euclideanSq (x-y)/h) ≤ (lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b))) →
    ∀ (U : Set (Vec d)) (hU : IsOpen U),
    U = {z | euclideanNorm (z-b) < eps/4} →
    (∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ((EinsteinFull.gmpKilledEndpointKernel G
        ((fun z : Vec d => lam • z) ⁻¹' U)
        (hU.preimage (continuous_id.const_smul lam)) (h / lam^2).toNNReal
        (lam⁻¹ • x)).map (fun z => lam • z)) A =
      ∫⁻ y in A, ENNReal.ofReal (ρ (lam⁻¹ • (y-b)) * ((lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b))))) →
    ∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ENNReal.ofReal cstar * volume A ≤
      G.pathLaw (lam⁻¹ • x) {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
        euclideanNorm (lam • Y ((u : ℝ) / lam^2).toNNReal - a) < eps/2) ∧
        lam • Y (h / lam^2).toNNReal ∈ A} := by
  let q : ℝ → Vec d → Vec d → ℝ := fun t x y =>
    c * Real.rpow t (-(d:ℝ)/2) * Real.exp (-C*euclideanSq (x-y)/t)
  have hab' : euclideanNorm (a-b) ≤ eps/16 := by
    have he : euclideanNorm (a-b) = euclideanNorm (b-a) := by
      rw [← neg_sub b a, show -(b-a) = (-1 : ℝ) • (b-a) by ext i; simp,
        TimeChange.euclideanNorm_smul]
      norm_num
    rw [he]; exact hab
  obtain ⟨v, hv, hvbound⟩ := c12_fixed_step_density_lower q h (eps/16) c C hh
    (div_pos heps (by norm_num)) hc hC (fun _ _ => le_rfl) a b (eps/16)
    (div_nonneg heps.le (by norm_num)) hab'
  refine ⟨κ*v, mul_pos hκ hv, ?_⟩
  intro hd L hL ω hω lam h₀ h₁ hlam G ρ α R K gradK _hK hρ hgauss U hU hUeq hassoc x hx A hA hsub
  refine EinsteinFull.c13_piece_density_of_endpoint_killed_density G eps heps a b hab
    hlam h hh.le (lam⁻¹ • x) (κ*v) U hU hUeq ?_ A hA hsub
  intro A hA hsub
  rw [hassoc x hx A hA hsub]
  have hlower : ∀ᵐ y ∂(volume : Measure (Vec d)).restrict A,
      ENNReal.ofReal (κ*v) ≤ ENNReal.ofReal (ρ (lam⁻¹ • (y-b)) * ((lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b)))) := by
    filter_upwards [ae_restrict_mem hA] with y hy
    have hy' := hsub hy
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul (hρ y hy') ((hvbound x hx y hy').trans (hgauss _hK x hx y hy'))
      hv.le (hκ.le.trans (hρ y hy'))
  have h := lintegral_mono_ae hlower
  simpa only [lintegral_const, Measure.restrict_apply_univ] using h


/-- One constant controls every pair of adjacent renewal centers for the
same supplied killed law and its associated weighted spectral kernel. -/
theorem c12_uniform_rescaled_piece_lower_of_spectral_association {d : ℕ}
    (eps h c C κ : ℝ) (heps : 0 < eps) (hh : 0 < h)
    (hc : 0 < c) (hC : 0 < C) (hκ : 0 < κ) :
    ∃ cstar : ℝ, 0 < cstar ∧
    ∀ (a b : Vec d), euclideanNorm (b-a) ≤ eps / 16 →
    ∀ {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
      {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1},
    ∀ (_ : 0 < lam) (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd L hL ω hω lam h₀ h₁)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d) (R : ℝ)
      (K : ℝ → Vec d → Vec d → ℝ) (gradK : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K gradK →
    (∀ y ∈ sourceBall b (eps/16), κ ≤ ρ (lam⁻¹ • (y-b))) →
    (IsSpectralDirichletFundamentalSolution ρ α R K gradK →
      ∀ x ∈ sourceBall a (eps/16), ∀ y ∈ sourceBall b (eps/16),
      c * Real.rpow h (-(d:ℝ)/2) * Real.exp (-C*euclideanSq (x-y)/h) ≤ (lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b))) →
    ∀ (U : Set (Vec d)) (hU : IsOpen U),
    U = {z | euclideanNorm (z-b) < eps/4} →
    (∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ((EinsteinFull.gmpKilledEndpointKernel G
        ((fun z : Vec d => lam • z) ⁻¹' U)
        (hU.preimage (continuous_id.const_smul lam)) (h / lam^2).toNNReal
        (lam⁻¹ • x)).map (fun z => lam • z)) A =
      ∫⁻ y in A, ENNReal.ofReal (ρ (lam⁻¹ • (y-b)) * ((lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b))))) →
    ∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ENNReal.ofReal cstar * volume A ≤
      G.pathLaw (lam⁻¹ • x) {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
        euclideanNorm (lam • Y ((u : ℝ) / lam^2).toNNReal - a) < eps/2) ∧
        lam • Y (h / lam^2).toNNReal ∈ A} := by
  obtain ⟨v, hv, hvbound⟩ := c12_uniform_gaussian_ball_lower (d := d) h (eps/16) c C
    (eps/16) hh (div_pos heps (by norm_num)) hc hC (div_nonneg heps.le (by norm_num))
  refine ⟨κ*v, mul_pos hκ hv, ?_⟩
  intro a b hab hd L hL ω hω lam h₀ h₁ hlam G ρ α R K gradK hK hρ hgauss U hU hUeq hassoc x hx A hA hsub
  have hab' : euclideanNorm (a-b) ≤ eps/16 := by
    have he : euclideanNorm (a-b) = euclideanNorm (b-a) := by
      rw [← neg_sub b a, show -(b-a) = (-1 : ℝ) • (b-a) by ext i; simp,
        TimeChange.euclideanNorm_smul]
      norm_num
    rw [he]; exact hab
  refine EinsteinFull.c13_piece_density_of_endpoint_killed_density G eps heps a b hab
    hlam h hh.le (lam⁻¹ • x) (κ*v) U hU hUeq ?_ A hA hsub
  intro A hA hsub
  rw [hassoc x hx A hA hsub]
  have hlower : ∀ᵐ y ∂(volume : Measure (Vec d)).restrict A,
      ENNReal.ofReal (κ*v) ≤ ENNReal.ofReal (ρ (lam⁻¹ • (y-b)) * ((lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b)))) := by
    filter_upwards [ae_restrict_mem hA] with y hy
    have hy' := hsub hy
    apply ENNReal.ofReal_le_ofReal
    have hbound := hvbound a b hab'
      (fun _ x y => (lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b)))
      (hgauss hK) x hx y hy'
    exact mul_le_mul (hρ y hy') hbound
      hv.le (hκ.le.trans (hρ y hy'))
  have h := lintegral_mono_ae hlower
  simpa only [lintegral_const, Measure.restrict_apply_univ] using h

open Classical in
/-- The normalized semigroup on the scaled ball gives the truncated,
clipped-weight semigroup used by the native lower chain. -/
theorem c12_normalized_semigroup_of_unclipped {d : ℕ}
    (lam R κ : ℝ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (K : ℝ → Vec d → Vec d → ℝ)
    (hell : IsUniformlyElliptic κ ρ α)
    (hsemigroup :
      let S := lam * R
      let q : ℝ → Vec d → Vec d → ℝ := fun t x y =>
        (lam⁻¹)^d * K (t / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y)
      ∀ s t : ℝ, 0 < s → 0 < t → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
        IntegrableOn (fun z => q s x z * q t z y * ρ (lam⁻¹ • z)) (sourceBall 0 S) ∧
        q (s+t) x y = ∫ z in sourceBall 0 S, q s x z * q t z y * ρ (lam⁻¹ • z)) :
    let S := lam * R
    let q : ℝ → Vec d → Vec d → ℝ := fun t x y =>
      if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
        (lam⁻¹)^d * K (t / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
    let w : Vec d → ℝ := fun z => max κ (ρ (lam⁻¹ • z))
    ∀ s t : ℝ, 0 < s → 0 < t → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      IntegrableOn (fun z => q s x z * q t z y * w z) (sourceBall 0 S) ∧
      q (s+t) x y = ∫ z in sourceBall 0 S, q s x z * q t z y * w z := by
  dsimp only at hsemigroup ⊢
  intro s t hs ht x hx y hy
  obtain ⟨hint, hcomp⟩ := hsemigroup s t hs ht x hx y hy
  have hB := (c17_isOpen_sourceBall (0 : Vec d) (lam * R)).measurableSet
  have heq : ∀ z ∈ sourceBall (0 : Vec d) (lam * R),
      ((lam⁻¹)^d * K (s / lam^2) (lam⁻¹ • x) (lam⁻¹ • z) / ρ (lam⁻¹ • z)) *
        ((lam⁻¹)^d * K (t / lam^2) (lam⁻¹ • z) (lam⁻¹ • y) / ρ (lam⁻¹ • y)) * ρ (lam⁻¹ • z) =
      (if x ∈ sourceBall 0 (lam * R) ∧ z ∈ sourceBall 0 (lam * R) then
        (lam⁻¹)^d * K (s / lam^2) (lam⁻¹ • x) (lam⁻¹ • z) / ρ (lam⁻¹ • z) else 0) *
      (if z ∈ sourceBall 0 (lam * R) ∧ y ∈ sourceBall 0 (lam * R) then
        (lam⁻¹)^d * K (t / lam^2) (lam⁻¹ • z) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0) *
        max κ (ρ (lam⁻¹ • z)) := by
    intro z hz
    rw [if_pos ⟨hx, hz⟩, if_pos ⟨hz, hy⟩, max_eq_right (hell.2.2 (lam⁻¹ • z)).1]
  refine ⟨hint.congr_fun heq hB, ?_⟩
  rw [if_pos ⟨hx, hy⟩, hcomp]
  exact setIntegral_congr_fun hB heq

open Classical in
/-- Native near-diagonal and weighted semigroup estimates for the actual
rescaled spectral kernel imply the supplied-law tube-piece lower bound. The
kernel is zero off its scaled Dirichlet ball, and the weight is clipped below
by κ; the semigroup hypothesis is stated for that clipped weight. -/
theorem c12_native_rescaled_piece_lower_normalized {d : ℕ}
    (eps h κ c S : ℝ) (heps : 0 < eps) (hh : 0 < h)
    (hκ : 0 < κ) (hc : 0 < c) (hS : 0 < S) (hhS : h ≤ S^2/64) :
    ∃ cstar : ℝ, 0 < cstar ∧
    ∀ (a b : Vec d), euclideanNorm (b-a) ≤ eps / 16 →
    sourceBall (a-b) (eps/16) ⊆ sourceBall 0 (S/2) →
    sourceBall (0 : Vec d) (eps/16) ⊆ sourceBall 0 (S/2) →
    ∀ {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
      {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1},
    ∀ (_ : 0 < lam) (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd L hL ω hω lam h₀ h₁)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d) (R : ℝ)
      (K : ℝ → Vec d → Vec d → ℝ) (gradK : ℝ → Vec d → Vec d → Vec d),
    ∀ (_hSR : S = lam * R),
    let q : ℝ → Vec d → Vec d → ℝ := fun s x y =>
      if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
        (lam⁻¹)^d * K (s / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
    let w : Vec d → ℝ := fun z => max κ (ρ (lam⁻¹ • z))
    IsSpectralDirichletFundamentalSolution ρ α R K gradK →
    (∀ y ∈ sourceBall b (eps/16), κ ≤ ρ (lam⁻¹ • (y-b))) →
    Measurable w →
    (∀ s, 0 < s → ∀ x y, 0 ≤ q s x y) →
    (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      IntegrableOn (fun z => q s x z * q u z y * w z) (sourceBall 0 S)) →
    (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      q (s+u) x y = ∫ z in sourceBall 0 S, q s x z * q u z y * w z) →
    (IsSpectralDirichletFundamentalSolution ρ α R K gradK →
      ∀ s, 0 < s → s ≤ S^2 → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      euclideanSq (x-y) ≤ s → c*Real.rpow s (-(d:ℝ)/2) ≤ q s x y) →
    ∀ (U : Set (Vec d)) (hU : IsOpen U),
    U = {z | euclideanNorm (z-b) < eps/4} →
    (∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ((EinsteinFull.gmpKilledEndpointKernel G
        ((fun z : Vec d => lam • z) ⁻¹' U)
        (hU.preimage (continuous_id.const_smul lam)) (h / lam^2).toNNReal
        (lam⁻¹ • x)).map (fun z => lam • z)) A =
      ∫⁻ y in A, ENNReal.ofReal (ρ (lam⁻¹ • (y-b)) * ((lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b)) / ρ (lam⁻¹ • (y-b))))) →
    ∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ENNReal.ofReal cstar * volume A ≤
      G.pathLaw (lam⁻¹ • x) {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
        euclideanNorm (lam • Y ((u : ℝ) / lam^2).toNNReal - a) < eps/2) ∧
        lam • Y (h / lam^2).toNNReal ∈ A} := by
  obtain ⟨v, hv, hvbound⟩ := c12_uniform_native_ball_lower (d := d) κ c S h
    (eps/16) (eps/16) hκ hc hS hh hhS (by positivity) (by positivity)
  refine ⟨κ*v, mul_pos hκ hv, ?_⟩
  intro a b hab ha hb hd L hL ω hω lam h₀ h₁ hlam G ρ α R K gradK _hSR q w hK hρ hmeas hq hint hsemi hnear U hU hUeq hassoc x hx A hA hsub
  have hab' : euclideanNorm ((a-b) - 0) ≤ eps/16 := by
    have he : euclideanNorm (a-b) = euclideanNorm (b-a) := by
      rw [← neg_sub b a, show -(b-a) = (-1 : ℝ) • (b-a) by ext i; simp,
        TimeChange.euclideanNorm_smul]
      norm_num
    simpa only [sub_zero, he] using hab
  have hxb : x-b ∈ sourceBall (a-b) (eps/16) := by
    simpa only [sourceBall, Set.mem_ofPred_eq, sub_sub_sub_cancel_right] using hx
  have hall := hvbound w q hmeas (fun z => le_max_left _ _) hq hint hsemi (hnear hK)
    (a-b) 0 hab' ha hb (x-b) hxb
  refine EinsteinFull.c13_piece_density_of_endpoint_killed_density G eps heps a b hab
    hlam h hh.le (lam⁻¹ • x) (κ*v) U hU hUeq ?_ A hA hsub
  intro A hA hsub
  rw [hassoc x hx A hA hsub]
  have hlower : ∀ᵐ y ∂(volume : Measure (Vec d)).restrict A,
      ENNReal.ofReal (κ*v) ≤ ENNReal.ofReal (ρ (lam⁻¹ • (y-b)) * ((lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b)) / ρ (lam⁻¹ • (y-b)))) := by
    filter_upwards [ae_restrict_mem hA] with y hy
    have hy' := hsub hy
    have hyb : y-b ∈ sourceBall 0 (eps/16) := by
      simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hy'
    have hxS : x-b ∈ sourceBall 0 S := by
      have hxhalf : euclideanNorm ((x-b)-0) < S/2 := ha hxb
      change euclideanNorm ((x-b)-0) < S
      exact lt_of_lt_of_le hxhalf (by linarith)
    have hyS : y-b ∈ sourceBall 0 S := by
      have hyhalf : euclideanNorm ((y-b)-0) < S/2 := hb hyb
      change euclideanNorm ((y-b)-0) < S
      exact lt_of_lt_of_le hyhalf (by linarith)
    have hbound := hall (y-b) hyb
    dsimp only [q] at hbound
    rw [if_pos ⟨hxS, hyS⟩] at hbound
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul (hρ y hy') hbound hv.le (hκ.le.trans (hρ y hy'))
  have h := lintegral_mono_ae hlower
  simpa only [lintegral_const, Measure.restrict_apply_univ] using h

open Classical in
/-- The supplied-law endpoint lower bound from quarter-distance native estimates. -/
theorem c12_native_rescaled_piece_lower_normalized_quarter {d : ℕ}
    (eps h κ c S : ℝ) (heps : 0 < eps) (hh : 0 < h)
    (hκ : 0 < κ) (hc : 0 < c) (hS : 0 < S) (hhS : h ≤ S^2/64) :
    ∃ cstar : ℝ, 0 < cstar ∧
    ∀ (a b : Vec d), euclideanNorm (b-a) ≤ eps / 16 →
    sourceBall (a-b) (eps/16) ⊆ sourceBall 0 (S/2) →
    sourceBall (0 : Vec d) (eps/16) ⊆ sourceBall 0 (S/2) →
    ∀ {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
      {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1},
    ∀ (_ : 0 < lam) (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd L hL ω hω lam h₀ h₁)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d) (R : ℝ)
      (K : ℝ → Vec d → Vec d → ℝ) (gradK : ℝ → Vec d → Vec d → Vec d),
    ∀ (_hSR : S = lam * R),
    let q : ℝ → Vec d → Vec d → ℝ := fun s x y =>
      if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
        (lam⁻¹)^d * K (s / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
    let w : Vec d → ℝ := fun z => max κ (ρ (lam⁻¹ • z))
    IsSpectralDirichletFundamentalSolution ρ α R K gradK →
    (∀ y ∈ sourceBall b (eps/16), κ ≤ ρ (lam⁻¹ • (y-b))) →
    Measurable w →
    (∀ s, 0 < s → ∀ x y, 0 ≤ q s x y) →
    (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      IntegrableOn (fun z => q s x z * q u z y * w z) (sourceBall 0 S)) →
    (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      q (s+u) x y = ∫ z in sourceBall 0 S, q s x z * q u z y * w z) →
    (IsSpectralDirichletFundamentalSolution ρ α R K gradK →
      ∀ s, 0 < s → s ≤ S^2 → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      euclideanSq (x-y) ≤ s/4 → c*Real.rpow s (-(d:ℝ)/2) ≤ q s x y) →
    ∀ (U : Set (Vec d)) (hU : IsOpen U),
    U = {z | euclideanNorm (z-b) < eps/4} →
    (∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ((EinsteinFull.gmpKilledEndpointKernel G
        ((fun z : Vec d => lam • z) ⁻¹' U)
        (hU.preimage (continuous_id.const_smul lam)) (h / lam^2).toNNReal
        (lam⁻¹ • x)).map (fun z => lam • z)) A =
      ∫⁻ y in A, ENNReal.ofReal (ρ (lam⁻¹ • (y-b)) * ((lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b)) / ρ (lam⁻¹ • (y-b))))) →
    ∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ENNReal.ofReal cstar * volume A ≤
      G.pathLaw (lam⁻¹ • x) {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
        euclideanNorm (lam • Y ((u : ℝ) / lam^2).toNNReal - a) < eps/2) ∧
        lam • Y (h / lam^2).toNNReal ∈ A} := by
  obtain ⟨C, hC, hgauss⟩ := c12_rescaled_normalized_quarter_gaussian (d := d) κ c hκ hc
  obtain ⟨v, hv, hvbound⟩ := c12_uniform_gaussian_ball_lower (d := d) h
    (eps/16) C⁻¹ C (eps/16) hh (by positivity) (inv_pos.mpr hC) hC (by positivity)
  refine ⟨κ*v, mul_pos hκ hv, ?_⟩
  intro a b hab ha hb hd L hL ω hω lam h₀ h₁ hlam G ρ α R K gradK _hSR q w hK hρ _hmeas hq hint hsemi hnear U hU hUeq hassoc x hx A hA hsub
  have hab' : euclideanNorm ((a-b) - 0) ≤ eps/16 := by
    have he : euclideanNorm (a-b) = euclideanNorm (b-a) := by
      rw [← neg_sub b a, show -(b-a) = (-1 : ℝ) • (b-a) by ext i; simp,
        TimeChange.euclideanNorm_smul]
      norm_num
    simpa only [sub_zero, he] using hab
  have hxb : x-b ∈ sourceBall (a-b) (eps/16) := by
    simpa only [sourceBall, Set.mem_ofPred_eq, sub_sub_sub_cancel_right] using hx
  have hball := hvbound (a-b) 0 hab' q (by
    intro z hz y hy
    exact hgauss S h lam hS hh hhS ρ K hq hint hsemi (hnear hK) z (ha hz) y (hb hy))
  have hall := hball (x-b) hxb
  refine EinsteinFull.c13_piece_density_of_endpoint_killed_density G eps heps a b hab
    hlam h hh.le (lam⁻¹ • x) (κ*v) U hU hUeq ?_ A hA hsub
  intro A hA hsub
  rw [hassoc x hx A hA hsub]
  have hlower : ∀ᵐ y ∂(volume : Measure (Vec d)).restrict A,
      ENNReal.ofReal (κ*v) ≤ ENNReal.ofReal (ρ (lam⁻¹ • (y-b)) * ((lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b)) / ρ (lam⁻¹ • (y-b)))) := by
    filter_upwards [ae_restrict_mem hA] with y hy
    have hy' := hsub hy
    have hyb : y-b ∈ sourceBall 0 (eps/16) := by
      simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hy'
    have hxS : x-b ∈ sourceBall 0 S := by
      have hxhalf : euclideanNorm ((x-b)-0) < S/2 := ha hxb
      change euclideanNorm ((x-b)-0) < S
      exact lt_of_lt_of_le hxhalf (by linarith)
    have hyS : y-b ∈ sourceBall 0 S := by
      have hyhalf : euclideanNorm ((y-b)-0) < S/2 := hb hyb
      change euclideanNorm ((y-b)-0) < S
      exact lt_of_lt_of_le hyhalf (by linarith)
    have hbound := hall (y-b) hyb
    dsimp only [q] at hbound
    rw [if_pos ⟨hxS, hyS⟩] at hbound
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul (hρ y hy') hbound hv.le (hκ.le.trans (hρ y hy'))
  have h := lintegral_mono_ae hlower
  simpa only [lintegral_const, Measure.restrict_apply_univ] using h

/-- Parabolic scaling cancels the spatial Jacobian against the power of time
in a normalized near-diagonal lower bound. -/
theorem c12_normalized_near_diagonal_scaling {d : ℕ}
    (lam s c k : ℝ) (hlam : 0 < lam) (hs : 0 < s)
    (h : c * Real.rpow (s / lam^2) (-(d : ℝ)/2) ≤ k) :
    c * Real.rpow s (-(d : ℝ)/2) ≤ (lam⁻¹)^d * k := by
  have hp : (lam^2 : ℝ) ^ (-(d : ℝ)/2) = (lam^d)⁻¹ := by
    rw [← Real.rpow_natCast lam d, ← Real.rpow_neg hlam.le, ← Real.rpow_two lam,
      ← Real.rpow_mul hlam.le]
    congr 1
    ring
  have hr : Real.rpow (s / lam^2) (-(d : ℝ)/2) =
      Real.rpow s (-(d : ℝ)/2) * lam^d := by
    change (s / lam^2 : ℝ) ^ (-(d : ℝ)/2) = s ^ (-(d : ℝ)/2) * lam^d
    rw [Real.div_rpow hs.le (sq_nonneg lam), hp]
    simp
  rw [hr] at h
  have hk := mul_le_mul_of_nonneg_left h (pow_nonneg (inv_nonneg.mpr hlam.le) d)
  have hcancel : (lam⁻¹)^d * lam^d = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hlam.ne', one_pow]
  calc
    c * Real.rpow s (-(d : ℝ)/2) =
        (lam⁻¹)^d * (c * (Real.rpow s (-(d : ℝ)/2) * lam^d)) := by
          rw [show (lam⁻¹)^d * (c * (Real.rpow s (-(d : ℝ)/2) * lam^d)) =
            ((lam⁻¹)^d * lam^d) * (c * Real.rpow s (-(d : ℝ)/2)) by ring,
            hcancel, one_mul]
    _ ≤ (lam⁻¹)^d * k := hk

/-- C18's local native estimate after the parabolic Jacobian normalization.
The interior and time restrictions are kept explicitly at the native scale. -/
theorem c12_native_local_quarter_bound_scaled
    (d : ℕ) (hd : 2 ≤ d) (κ δ H : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) :
    ∃ c η : ℝ, 0 < c ∧ 0 < η ∧ ∀ R : ℝ, 0 < R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r t : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < t → t ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K t x y) →
    (∀ (x y : Vec d) (r t : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < t → t ≤ δ*r^2 → euclideanSq (x-y) ≤ t →
      K (2*t) x x / ρ x ≤ H * (K (4*t) x y / ρ y)) →
    ∀ (lam s : ℝ), 0 < lam → 0 < s → ∀ (x y : Vec d) (r : ℝ),
      0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R → y ∈ sourceBall 0 R →
      s / lam^2 ≤ η*r^2 → euclideanSq (x-y) ≤ (s / lam^2)/4 →
      c * Real.rpow s (-(d : ℝ)/2) ≤ (lam⁻¹)^d * K (s / lam^2) x y / ρ y := by
  obtain ⟨c, η, hc, hη, hnear⟩ :=
    c18_native_uniform_near_diagonal_rescaled_of_mass_comparison d hd κ δ H hκ hδ hH
  refine ⟨c, η, hc, hη, ?_⟩
  intro R hR ρ α hell K G hK hmass hcompare lam s hlam hs x y r hr hball hy htime hdist
  have h := hnear R hR ρ α hell K G hK hmass hcompare x y r (s / lam^2)
    hr hball hy (div_pos hs (sq_pos_of_pos hlam)) htime hdist
  have hscaled := c12_normalized_near_diagonal_scaling (d := d) lam s c
    (K (s / lam^2) x y / ρ y) hlam hs h
  simpa only [mul_div_assoc] using hscaled

open Classical in
/-- C18's estimate on the rescaled interior ball with an explicit time cap. -/
theorem c12_native_local_quarter_bound_on_interior
    (d : ℕ) (hd : 2 ≤ d) (κ δ H : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) :
    ∃ c η : ℝ, 0 < c ∧ 0 < η ∧ ∀ R : ℝ, 0 < R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r t : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < t → t ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K t x y) →
    (∀ (x y : Vec d) (r t : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < t → t ≤ δ*r^2 → euclideanSq (x-y) ≤ t →
      K (2*t) x x / ρ x ≤ H * (K (4*t) x y / ρ y)) →
    ∀ (lam S : ℝ), 0 < lam → S = lam*R → ∀ s, 0 < s → s ≤ η*S^2/64 →
    ∀ x ∈ sourceBall 0 (3*S/4), ∀ y ∈ sourceBall 0 (3*S/4),
      euclideanSq (x-y) ≤ s/4 →
      c * Real.rpow s (-(d:ℝ)/2) ≤
        (lam⁻¹)^d * K (s / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) := by
  obtain ⟨c, η, hc, hη, hlocal⟩ :=
    c12_native_local_quarter_bound_scaled d hd κ δ H hκ hδ hH
  refine ⟨c, η, hc, hη, ?_⟩
  intro R hR ρ α hell K G hK hmass hcompare lam S hlam hSR s hs htime x hx y hy hdist
  have hinner (z : Vec d) (hz : z ∈ sourceBall 0 (3*S/4)) :
      lam⁻¹ • z ∈ sourceBall 0 (3*R/4) := by
    change euclideanNorm (lam⁻¹ • z - 0) < 3*R/4
    simp only [sub_zero, TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hlam)]
    have hz' : euclideanNorm z < 3*S/4 := by simpa [sourceBall] using hz
    rw [hSR] at hz'
    apply (inv_mul_lt_iff₀ hlam).2
    nlinarith
  have hball : sourceBall (lam⁻¹ • x) (2*(R/8)) ⊆ sourceBall 0 R := by
    intro z hz
    have hz' := c12_sourceBall_nested (3*R/4) (2*(R/8)) (lam⁻¹ • x) z (hinner x hx) hz
    change euclideanNorm (z-0) < R
    change euclideanNorm (z-0) < 3*R/4 + 2*(R/8) at hz'
    linarith
  have hyR : lam⁻¹ • y ∈ sourceBall 0 R := by
    have hy' := hinner y hy
    change euclideanNorm (lam⁻¹ • y - 0) < 3*R/4 at hy'
    change euclideanNorm (lam⁻¹ • y - 0) < R
    linarith
  have ht : s / lam^2 ≤ η * (R/8)^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hlam)).2
    rw [hSR] at htime
    nlinarith
  have hsq : euclideanSq (lam⁻¹ • x - lam⁻¹ • y) =
      euclideanSq (x-y) / lam^2 := by
    rw [← smul_sub, TimeChange.euclideanSq_eq_sq_euclideanNorm,
      TimeChange.euclideanSq_eq_sq_euclideanNorm, TimeChange.euclideanNorm_smul,
      abs_of_pos (inv_pos.mpr hlam), mul_pow]
    field_simp
  have hd' : euclideanSq (lam⁻¹ • x - lam⁻¹ • y) ≤ (s/lam^2)/4 := by
    rw [hsq]
    convert (div_le_div_iff_of_pos_right (sq_pos_of_pos hlam)).2 hdist using 1 <;> ring
  exact hlocal R hR ρ α hell K G hK hmass hcompare lam s hlam hs
    (lam⁻¹ • x) (lam⁻¹ • y) (R/8) (by positivity) hball hyR ht hd'

open Classical in
/-- The C18 local estimate chains through the actual normalized spectral kernel. -/
theorem c12_native_rescaled_local_chain_of_mass_comparison
    (d : ℕ) (hd : 2 ≤ d) (κ δ H : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) :
    ∃ c η : ℝ, 0 < c ∧ 0 < η ∧ ∀ (R S t lam : ℝ),
    0 < R → 0 < S → 0 < t → 0 < lam → S = lam * R → t ≤ S^2/64 →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K u x y) →
    (∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)) →
    ∀ x ∈ sourceBall 0 (S/2), ∀ y ∈ sourceBall 0 (S/2),
    let q : ℝ → Vec d → Vec d → ℝ := fun u x y =>
      if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
        (lam⁻¹)^d * K (u / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 16 * euclideanSq (x-y) / t + t/(η*S^2/64) + 2 ∧
      let h := t / (N : ℝ)
      let v := (Real.sqrt (h/4) / 8)^d *
        (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal
      (c * Real.rpow h (-(d:ℝ)/2)) *
        ((c * Real.rpow h (-(d:ℝ)/2)) * κ * v)^(N-1) ≤ q t x y := by
  obtain ⟨c, η, hc, hη, hlocal⟩ :=
    c12_native_local_quarter_bound_on_interior d hd κ δ H hκ hδ hH
  refine ⟨c, η, hc, hη, ?_⟩
  intro R S t lam hR hS ht hlam hSR htS ρ α hell K G hK hmass hcompare x hx y hy
  have hsem := c12_normalized_semigroup_of_unclipped lam R κ ρ α K hell
    (c11_rescaled_weighted_semigroup lam R κ hlam hR hκ ρ α hell K G hK)
  rw [← hSR] at hsem
  let q : ℝ → Vec d → Vec d → ℝ := fun u x y =>
    if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
      (lam⁻¹)^d * K (u / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
  have hq : ∀ u, 0 < u → ∀ x y, 0 ≤ q u x y := by
    intro u hu x y
    dsimp only [q]
    split_ifs with hxy
    · have hscaled (z : Vec d) (hz : z ∈ sourceBall 0 S) :
          lam⁻¹ • z ∈ sourceBall 0 R := by
        change euclideanNorm (lam⁻¹ • z - 0) < R
        simp only [sub_zero, TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hlam)]
        have hz' : euclideanNorm z < S := by simpa [sourceBall] using hz
        rw [hSR] at hz'
        exact (inv_mul_lt_iff₀ hlam).2 hz'
      exact div_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr hlam.le) _)
        ((hK.1 (lam⁻¹ • y) (hscaled y hxy.2)).2.1
          (u / lam^2) (div_pos hu (sq_pos_of_pos hlam)) (lam⁻¹ • x) (hscaled x hxy.1)))
        (hκ.le.trans (hell.2.2 (lam⁻¹ • y)).1)
    · exact le_rfl
  have hnear : ∀ u, 0 < u → u ≤ η*S^2/64 → ∀ x ∈ sourceBall 0 (3*S/4),
      ∀ y ∈ sourceBall 0 (3*S/4), euclideanSq (x-y) ≤ u/4 →
      c*Real.rpow u (-(d:ℝ)/2) ≤ q u x y := by
    intro u hu htime x hx y hy hdist
    have hsub (z : Vec d) (hz : z ∈ sourceBall 0 (3*S/4)) : z ∈ sourceBall 0 S := by
      change euclideanNorm (z-0) < 3*S/4 at hz
      change euclideanNorm (z-0) < S
      linarith
    dsimp only [q]
    rw [if_pos ⟨hsub x hx, hsub y hy⟩]
    exact hlocal R hR ρ α hell K G hK hmass hcompare lam S hlam hSR u hu htime x hx y hy hdist
  exact c12_rescaled_normalized_local_quarter_chain S t (η*S^2/64) κ c lam hS ht
    (by positivity) htS hκ hc ρ K x y hx hy hq
    (fun s u hs hu x hx y hy => (hsem s u hs hu x hx y hy).1)
    (fun s u hs hu x hx y hy => (hsem s u hs hu x hx y hy).2) hnear

open Classical in
/-- Gaussian propagation for the native normalized kernel under C18 mass and comparison. -/
theorem c12_native_rescaled_gaussian_of_mass_comparison
    (d : ℕ) (hd : 2 ≤ d) (κ δ H : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (R S t lam : ℝ),
    0 < R → 0 < S → 0 < t → 0 < lam → S = lam * R → t ≤ S^2/64 →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K u x y) →
    (∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)) →
    ∀ x ∈ sourceBall 0 (S/2), ∀ y ∈ sourceBall 0 (S/2),
    let q : ℝ → Vec d → Vec d → ℝ := fun u x y =>
      if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
        (lam⁻¹)^d * K (u / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
    A * Real.rpow t (-(d:ℝ)/2) *
      Real.exp (-B * euclideanSq (x-y) / t) ≤ q t x y := by
  obtain ⟨c, η, hc, hη, hchain⟩ :=
    c12_native_rescaled_local_chain_of_mass_comparison d hd κ δ H hκ hδ hH
  let V : ℝ := (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal
  have hV : 0 < V := by
    have hv := c12_sourceBall_volume (0 : Vec d) (by norm_num : (0 : ℝ) < 1)
    have hp := hv.2.2.1
    rw [hv.2.2.2] at hp
    simpa [V] using hp
  let b : ℝ := c * κ * (16 : ℝ)⁻¹^d * V
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨C, hC, habs⟩ := c12_gaussian_absorb_chain c b hc hb
  refine ⟨C⁻¹ * Real.exp (-C/(4*η)), 4*C, by positivity, by positivity, ?_⟩
  intro R S t lam hR hS ht hlam hSR htS ρ α hell K G hK hmass hcompare x hx y hy
  obtain ⟨N, hN, hNbound, hkernel⟩ :=
    hchain R S t lam hR hS ht hlam hSR htS ρ α hell K G hK hmass hcompare x hx y hy
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  let h : ℝ := t / (n+1 : ℕ)
  let v : ℝ := (Real.sqrt (h/4)/8)^d * V
  have hh : 0 < h := by dsimp [h]; positivity
  have hle : h ≤ t := by
    dsimp [h]
    exact div_le_self ht.le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
  have hfactor : (c * Real.rpow h (-(d:ℝ)/2)) * κ * v = b := by
    dsimp [v, b]
    calc
      _ = c * κ * (Real.rpow h (-(d:ℝ)/2) * (Real.sqrt (h/4)/8)^d) * V := by
        simp only [Real.rpow_eq_pow]
        ac_rfl
      _ = _ := by rw [c12_quarter_chain_volume_time_cancellation d h hh]
  change (c * Real.rpow h (-(d:ℝ)/2)) *
    ((c * Real.rpow h (-(d:ℝ)/2)) * κ * v)^n ≤ _ at hkernel
  rw [hfactor] at hkernel
  have hD : 0 ≤ euclideanSq (x-y) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hcap : t / (η*S^2/64) ≤ 1/η := by
    have hden : 0 < η*S^2/64 := by positivity
    apply (div_le_iff₀ hden).2
    have hi : 0 < η := hη
    field_simp
    nlinarith
  have hn : (n : ℝ) ≤ 4 * (4 * euclideanSq (x-y) / t + 1/(4*η)) + 2 := by
    have hn' : (n : ℝ) ≤ (n.succ : ℝ) := by exact_mod_cast Nat.le_succ n
    have := hn'.trans hNbound
    have hrecip : 4 * (1/(4*η)) = 1/η := by
      field_simp
    have hdist : 4 * (4 * euclideanSq (x-y) / t) =
        16 * euclideanSq (x-y) / t := by ring
    linarith
  have hexp : -(d : ℝ)/2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num)
  have hp : Real.rpow t (-(d:ℝ)/2) ≤ Real.rpow h (-(d:ℝ)/2) :=
    Real.rpow_le_rpow_of_nonpos hh hle hexp
  have hbound := habs (4 * euclideanSq (x-y)/t + 1/(4*η)) n
    (Real.rpow t (-(d:ℝ)/2)) (by positivity) (Real.rpow_pos_of_pos ht _).le hn
  have heq : -C * (4 * euclideanSq (x-y)/t + 1/(4*η)) =
      -C/(4*η) + (-(4*C) * euclideanSq (x-y)/t) := by ring
  rw [heq, Real.exp_add] at hbound
  calc
    _ = C⁻¹ * Real.rpow t (-(d:ℝ)/2) *
        (Real.exp (-C/(4*η)) * Real.exp (-(4*C)*euclideanSq (x-y)/t)) := by ring
    _ ≤ c * Real.rpow t (-(d:ℝ)/2) * b^n := hbound
    _ ≤ c * Real.rpow h (-(d:ℝ)/2) * b^n := by gcongr
    _ ≤ _ := hkernel

open Classical in
/-- The native Gaussian estimate supplies the same-law fixed-tube bound. -/
theorem c12_native_rescaled_piece_lower_of_mass_comparison {d : ℕ} (hd : 2 ≤ d)
    (eps h κ δ H S : ℝ) (heps : 0 < eps) (hh : 0 < h)
    (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) (hS : 0 < S) (hhS : h ≤ S^2/64) :
    ∃ cstar : ℝ, 0 < cstar ∧
    ∀ (a b : Vec d), euclideanNorm (b-a) ≤ eps / 16 →
    sourceBall (a-b) (eps/16) ⊆ sourceBall 0 (S/2) →
    sourceBall (0 : Vec d) (eps/16) ⊆ sourceBall 0 (S/2) →
    ∀ {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
      {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1},
    ∀ (_ : 0 < lam) (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd L hL ω hω lam h₀ h₁)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d) (R : ℝ)
      (K : ℝ → Vec d → Vec d → ℝ) (gradK : ℝ → Vec d → Vec d → Vec d),
    ∀ (_hSR : S = lam * R),
    let q : ℝ → Vec d → Vec d → ℝ := fun s x y =>
      if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
        (lam⁻¹)^d * K (s / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
    0 < R → IsUniformlyElliptic κ ρ α →
    IsSpectralDirichletFundamentalSolution ρ α R K gradK →
    (∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K u x y) →
    (∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)) →
    ∀ (U : Set (Vec d)) (hU : IsOpen U),
    U = {z | euclideanNorm (z-b) < eps/4} →
    (∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ((EinsteinFull.gmpKilledEndpointKernel G
        ((fun z : Vec d => lam • z) ⁻¹' U)
        (hU.preimage (continuous_id.const_smul lam)) (h / lam^2).toNNReal
        (lam⁻¹ • x)).map (fun z => lam • z)) A =
      ∫⁻ y in A, ENNReal.ofReal (ρ (lam⁻¹ • (y-b)) * ((lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b)) / ρ (lam⁻¹ • (y-b))))) →
    ∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ENNReal.ofReal cstar * volume A ≤
      G.pathLaw (lam⁻¹ • x) {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
        euclideanNorm (lam • Y ((u : ℝ) / lam^2).toNNReal - a) < eps/2) ∧
        lam • Y (h / lam^2).toNNReal ∈ A} := by
  obtain ⟨C, D, hC, hD, hgauss⟩ :=
    c12_native_rescaled_gaussian_of_mass_comparison d hd κ δ H hκ hδ hH
  obtain ⟨v, hv, hvbound⟩ := c12_uniform_gaussian_ball_lower (d := d) h
    (eps/16) C D (eps/16) hh (by positivity) hC hD (by positivity)
  refine ⟨κ*v, mul_pos hκ hv, ?_⟩
  intro a b hab ha hb L hL ω hω lam h₀ h₁ hlam G ρ α R K gradK hSR q hR hell hK hmass hcompare U hU hUeq hassoc x hx A hA hsub
  have hρ : ∀ y ∈ sourceBall b (eps/16), κ ≤ ρ (lam⁻¹ • (y-b)) := by
    intro y hy
    exact (hell.2.2 (lam⁻¹ • (y-b))).1
  have hab' : euclideanNorm ((a-b) - 0) ≤ eps/16 := by
    have he : euclideanNorm (a-b) = euclideanNorm (b-a) := by
      rw [← neg_sub b a, show -(b-a) = (-1 : ℝ) • (b-a) by ext i; simp,
        TimeChange.euclideanNorm_smul]
      norm_num
    simpa only [sub_zero, he] using hab
  have hxb : x-b ∈ sourceBall (a-b) (eps/16) := by
    simpa only [sourceBall, Set.mem_ofPred_eq, sub_sub_sub_cancel_right] using hx
  have hball := hvbound (a-b) 0 hab' q (by
    intro z hz y hy
    exact hgauss R S h lam hR hS hh hlam hSR hhS ρ α hell K gradK hK hmass hcompare z (ha hz) y (hb hy))
  have hall := hball (x-b) hxb
  refine EinsteinFull.c13_piece_density_of_endpoint_killed_density G eps heps a b hab
    hlam h hh.le (lam⁻¹ • x) (κ*v) U hU hUeq ?_ A hA hsub
  intro A hA hsub
  rw [hassoc x hx A hA hsub]
  have hlower : ∀ᵐ y ∂(volume : Measure (Vec d)).restrict A,
      ENNReal.ofReal (κ*v) ≤ ENNReal.ofReal (ρ (lam⁻¹ • (y-b)) * ((lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b)) / ρ (lam⁻¹ • (y-b)))) := by
    filter_upwards [ae_restrict_mem hA] with y hy
    have hy' := hsub hy
    have hyb : y-b ∈ sourceBall 0 (eps/16) := by
      simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hy'
    have hxS : x-b ∈ sourceBall 0 S := by
      have hxhalf : euclideanNorm ((x-b)-0) < S/2 := ha hxb
      change euclideanNorm ((x-b)-0) < S
      exact lt_of_lt_of_le hxhalf (by linarith)
    have hyS : y-b ∈ sourceBall 0 S := by
      have hyhalf : euclideanNorm ((y-b)-0) < S/2 := hb hyb
      change euclideanNorm ((y-b)-0) < S
      exact lt_of_lt_of_le hyhalf (by linarith)
    have hbound := hall (y-b) hyb
    dsimp only [q] at hbound
    rw [if_pos ⟨hxS, hyS⟩] at hbound
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul (hρ y hy') hbound hv.le (hκ.le.trans (hρ y hy'))
  have h := lintegral_mono_ae hlower
  simpa only [lintegral_const, Measure.restrict_apply_univ] using h

open Classical in
/-- The elliptic native kernel supplies the weighted semigroup and positivity. -/
theorem c12_native_rescaled_piece_lower_of_elliptic_quarter {d : ℕ}
    (eps h κ c S : ℝ) (heps : 0 < eps) (hh : 0 < h)
    (hκ : 0 < κ) (hc : 0 < c) (hS : 0 < S) (hhS : h ≤ S^2/64) :
    ∃ cstar : ℝ, 0 < cstar ∧
    ∀ (a b : Vec d), euclideanNorm (b-a) ≤ eps / 16 →
    sourceBall (a-b) (eps/16) ⊆ sourceBall 0 (S/2) →
    sourceBall (0 : Vec d) (eps/16) ⊆ sourceBall 0 (S/2) →
    ∀ {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
      {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1},
    ∀ (_ : 0 < lam) (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd L hL ω hω lam h₀ h₁)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d) (R : ℝ)
      (K : ℝ → Vec d → Vec d → ℝ) (gradK : ℝ → Vec d → Vec d → Vec d),
    ∀ (_hSR : S = lam * R),
    let q : ℝ → Vec d → Vec d → ℝ := fun s x y =>
      if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
        (lam⁻¹)^d * K (s / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
    let w : Vec d → ℝ := fun z => max κ (ρ (lam⁻¹ • z))
    IsUniformlyElliptic κ ρ α →
    IsSpectralDirichletFundamentalSolution ρ α R K gradK →
    (IsSpectralDirichletFundamentalSolution ρ α R K gradK →
      ∀ s, 0 < s → s ≤ S^2 → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      euclideanSq (x-y) ≤ s/4 → c*Real.rpow s (-(d:ℝ)/2) ≤ q s x y) →
    ∀ (U : Set (Vec d)) (hU : IsOpen U),
    U = {z | euclideanNorm (z-b) < eps/4} →
    (∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ((EinsteinFull.gmpKilledEndpointKernel G
        ((fun z : Vec d => lam • z) ⁻¹' U)
        (hU.preimage (continuous_id.const_smul lam)) (h / lam^2).toNNReal
        (lam⁻¹ • x)).map (fun z => lam • z)) A =
      ∫⁻ y in A, ENNReal.ofReal (ρ (lam⁻¹ • (y-b)) * ((lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b)) / ρ (lam⁻¹ • (y-b))))) →
    ∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ENNReal.ofReal cstar * volume A ≤
      G.pathLaw (lam⁻¹ • x) {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
        euclideanNorm (lam • Y ((u : ℝ) / lam^2).toNNReal - a) < eps/2) ∧
        lam • Y (h / lam^2).toNNReal ∈ A} := by
  obtain ⟨cstar, hcstar, hbound⟩ :=
    c12_native_rescaled_piece_lower_normalized_quarter (d := d) eps h κ c S
      heps hh hκ hc hS hhS
  refine ⟨cstar, hcstar, ?_⟩
  intro a b hab ha hb hd L hL ω hω lam h₀ h₁ hlam G ρ α R K gradK hSR q w hell hK hnear U hU hUeq hassoc x hx A hA hsub
  have hR : 0 < R := by
    rw [hSR] at hS
    exact pos_of_mul_pos_right hS hlam.le
  have hsem := c12_normalized_semigroup_of_unclipped lam R κ ρ α K hell
    (c11_rescaled_weighted_semigroup lam R κ hlam hR hκ ρ α hell K gradK hK)
  rw [← hSR] at hsem
  have hq : ∀ s, 0 < s → ∀ x y, 0 ≤ q s x y := by
    intro s hs x y
    dsimp only [q]
    split_ifs with hxy
    · have hscaled (z : Vec d) (hz : z ∈ sourceBall 0 S) :
          lam⁻¹ • z ∈ sourceBall 0 R := by
        change euclideanNorm (lam⁻¹ • z - 0) < R
        simp only [sub_zero, TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hlam)]
        have hz' : euclideanNorm z < S := by simpa [sourceBall] using hz
        rw [hSR] at hz'
        exact (inv_mul_lt_iff₀ hlam).2 hz'
      exact div_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr hlam.le) _)
        ((hK.1 (lam⁻¹ • y) (hscaled y hxy.2)).2.1
          (s / lam^2) (div_pos hs (sq_pos_of_pos hlam)) (lam⁻¹ • x) (hscaled x hxy.1)))
        (hκ.le.trans (hell.2.2 (lam⁻¹ • y)).1)
    · exact le_rfl
  apply hbound a b hab ha hb hlam G ρ α R K gradK hSR hK
    (fun y _ => (hell.2.2 (lam⁻¹ • (y-b))).1)
    ((measurable_const.max (hell.1.comp (continuous_id.const_smul lam⁻¹).measurable)))
    hq (fun s t hs ht x hx y hy => (hsem s t hs ht x hx y hy).1)
    (fun s t hs ht x hx y hy => (hsem s t hs ht x hx y hy).2)
    hnear U hU hUeq hassoc x hx A hA hsub

/-- One constant works for both prescribed renewal step lengths and for all
admissible consecutive centers, before the coefficient field and law are chosen. -/
theorem c12_renewal_rescaled_piece_lower_of_spectral_association {d : ℕ}
    (eps c C κ : ℝ) (N : ℕ) (heps : 0 < eps) (hN : 0 < N)
    (hc : 0 < c) (hC : 0 < C) (hκ : 0 < κ) :
    ∃ cstar : ℝ, 0 < cstar ∧
    ∀ (j : ℕ), j = 2 ∨ j = 3 →
    let h : ℝ := ((j : ℝ) - 1) / N
    ∀ (a b : Vec d), euclideanNorm (b-a) ≤ eps / 16 →
    ∀ {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
      {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1},
    ∀ (_ : 0 < lam) (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd L hL ω hω lam h₀ h₁)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d) (R : ℝ)
      (K : ℝ → Vec d → Vec d → ℝ) (gradK : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K gradK →
    (∀ y ∈ sourceBall b (eps/16), κ ≤ ρ (lam⁻¹ • (y-b))) →
    (IsSpectralDirichletFundamentalSolution ρ α R K gradK →
      ∀ x ∈ sourceBall a (eps/16), ∀ y ∈ sourceBall b (eps/16),
      c * Real.rpow h (-(d:ℝ)/2) * Real.exp (-C*euclideanSq (x-y)/h) ≤ (lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b))) →
    ∀ (U : Set (Vec d)) (hU : IsOpen U),
    U = {z | euclideanNorm (z-b) < eps/4} →
    (∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ((EinsteinFull.gmpKilledEndpointKernel G
        ((fun z : Vec d => lam • z) ⁻¹' U)
        (hU.preimage (continuous_id.const_smul lam)) (h / lam^2).toNNReal
        (lam⁻¹ • x)).map (fun z => lam • z)) A =
      ∫⁻ y in A, ENNReal.ofReal (ρ (lam⁻¹ • (y-b)) * ((lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b))))) →
    ∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ENNReal.ofReal cstar * volume A ≤
      G.pathLaw (lam⁻¹ • x) {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
        euclideanNorm (lam • Y ((u : ℝ) / lam^2).toNNReal - a) < eps/2) ∧
        lam • Y (h / lam^2).toNNReal ∈ A} := by
  have h2 : 0 < (((2 : ℕ) : ℝ) - 1) / N := by positivity
  have h3 : 0 < (((3 : ℕ) : ℝ) - 1) / N := by positivity
  obtain ⟨v2, hv2, hbound2⟩ :=
    c12_uniform_rescaled_piece_lower_of_spectral_association (d := d)
      eps ((((2 : ℕ) : ℝ) - 1) / N) c C κ heps h2 hc hC hκ
  obtain ⟨v3, hv3, hbound3⟩ :=
    c12_uniform_rescaled_piece_lower_of_spectral_association (d := d)
      eps ((((3 : ℕ) : ℝ) - 1) / N) c C κ heps h3 hc hC hκ
  refine ⟨min v2 v3, lt_min hv2 hv3, ?_⟩
  intro j hj
  rcases hj with rfl | rfl
  · dsimp only
    intro a b hab hd L hL ω hω lam h₀ h₁ hlam G ρ α R K gradK hK hρ hgauss U hU hUeq hassoc x hx A hA hsub
    exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal (min_le_left v2 v3)) (volume A)).trans
      (hbound2 a b hab hlam G ρ α R K gradK hK hρ hgauss U hU hUeq hassoc x hx A hA hsub)
  · dsimp only
    intro a b hab hd L hL ω hω lam h₀ h₁ hlam G ρ α R K gradK hK hρ hgauss U hU hUeq hassoc x hx A hA hsub
    exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal (min_le_right v2 v3)) (volume A)).trans
      (hbound3 a b hab hlam G ρ α R K gradK hK hρ hgauss U hU hUeq hassoc x hx A hA hsub)

open Classical in
/-- A common native-chain constant for the two prescribed renewal step lengths. -/
theorem c12_renewal_native_rescaled_piece_lower_normalized {d : ℕ}
    (eps κ c S : ℝ) (N : ℕ) (heps : 0 < eps) (hN : 0 < N)
    (hκ : 0 < κ) (hc : 0 < c) (hS : 0 < S)
    (hsmall : ∀ j : ℕ, j = 2 ∨ j = 3 → ((j : ℝ) - 1) / N ≤ S^2/64) :
    ∃ cstar : ℝ, 0 < cstar ∧
    ∀ (j : ℕ), j = 2 ∨ j = 3 →
    let h : ℝ := ((j : ℝ) - 1) / N
    ∀ (a b : Vec d), euclideanNorm (b-a) ≤ eps / 16 →
    sourceBall (a-b) (eps/16) ⊆ sourceBall 0 (S/2) →
    sourceBall (0 : Vec d) (eps/16) ⊆ sourceBall 0 (S/2) →
    ∀ {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
      {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1},
    ∀ (_ : 0 < lam) (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd L hL ω hω lam h₀ h₁)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d) (R : ℝ)
      (K : ℝ → Vec d → Vec d → ℝ) (gradK : ℝ → Vec d → Vec d → Vec d),
    ∀ (_hSR : S = lam * R),
    let q : ℝ → Vec d → Vec d → ℝ := fun s x y =>
      if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
        (lam⁻¹)^d * K (s / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
    let w : Vec d → ℝ := fun z => max κ (ρ (lam⁻¹ • z))
    IsSpectralDirichletFundamentalSolution ρ α R K gradK →
    (∀ y ∈ sourceBall b (eps/16), κ ≤ ρ (lam⁻¹ • (y-b))) →
    Measurable w →
    (∀ s, 0 < s → ∀ x y, 0 ≤ q s x y) →
    (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      IntegrableOn (fun z => q s x z * q u z y * w z) (sourceBall 0 S)) →
    (∀ s u, 0 < s → 0 < u → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      q (s+u) x y = ∫ z in sourceBall 0 S, q s x z * q u z y * w z) →
    (IsSpectralDirichletFundamentalSolution ρ α R K gradK →
      ∀ s, 0 < s → s ≤ S^2 → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      euclideanSq (x-y) ≤ s → c*Real.rpow s (-(d:ℝ)/2) ≤ q s x y) →
    ∀ (U : Set (Vec d)) (hU : IsOpen U),
    U = {z | euclideanNorm (z-b) < eps/4} →
    (∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ((EinsteinFull.gmpKilledEndpointKernel G
        ((fun z : Vec d => lam • z) ⁻¹' U)
        (hU.preimage (continuous_id.const_smul lam)) (h / lam^2).toNNReal
        (lam⁻¹ • x)).map (fun z => lam • z)) A =
      ∫⁻ y in A, ENNReal.ofReal (ρ (lam⁻¹ • (y-b)) * ((lam⁻¹)^d * K (h / lam^2) (lam⁻¹ • (x-b)) (lam⁻¹ • (y-b)) / ρ (lam⁻¹ • (y-b))))) →
    ∀ x ∈ sourceBall a (eps/16), ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ sourceBall b (eps/16) →
      ENNReal.ofReal cstar * volume A ≤
      G.pathLaw (lam⁻¹ • x) {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
        euclideanNorm (lam • Y ((u : ℝ) / lam^2).toNNReal - a) < eps/2) ∧
        lam • Y (h / lam^2).toNNReal ∈ A} := by
  have h2 : 0 < (((2 : ℕ) : ℝ) - 1) / N := by positivity
  have h3 : 0 < (((3 : ℕ) : ℝ) - 1) / N := by positivity
  obtain ⟨v2, hv2, hbound2⟩ :=
    c12_native_rescaled_piece_lower_normalized (d := d)
      eps ((((2 : ℕ) : ℝ) - 1) / N) κ c S heps h2 hκ hc hS (hsmall 2 (Or.inl rfl))
  obtain ⟨v3, hv3, hbound3⟩ :=
    c12_native_rescaled_piece_lower_normalized (d := d)
      eps ((((3 : ℕ) : ℝ) - 1) / N) κ c S heps h3 hκ hc hS (hsmall 3 (Or.inr rfl))
  refine ⟨min v2 v3, lt_min hv2 hv3, ?_⟩
  intro j hj
  rcases hj with rfl | rfl
  · dsimp only
    intro a b hab ha hb hd L hL ω hω lam h₀ h₁ hlam G ρ α R K gradK hSR hK hρ hmeas hq hint hsemi hnear U hU hUeq hassoc x hx A hA hsub
    exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal (min_le_left v2 v3)) (volume A)).trans
      (hbound2 a b hab ha hb hlam G ρ α R K gradK hSR hK hρ hmeas hq hint hsemi hnear U hU hUeq hassoc x hx A hA hsub)
  · dsimp only
    intro a b hab ha hb hd L hL ω hω lam h₀ h₁ hlam G ρ α R K gradK hSR hK hρ hmeas hq hint hsemi hnear U hU hUeq hassoc x hx A hA hsub
    exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal (min_le_right v2 v3)) (volume A)).trans
      (hbound3 a b hab ha hb hlam G ρ α R K gradK hSR hK hρ hmeas hq hint hsemi hnear U hU hUeq hassoc x hx A hA hsub)

end EinsteinFull.Calculus
