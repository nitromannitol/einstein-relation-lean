import EinsteinFull.Calculus.C10TestBlocksSupport
import EinsteinFull.Calculus.S3LocalAvSupport
import EinsteinFull.Calculus.S1SharpStructuralData
import EinsteinFull.Frozen.StructuralData

/-! Deterministic lattice estimates for the actual Euclidean Gaussian envelope
in the forced-flux gain. The Gaussian width remains an arbitrary supplied
parameter, so consumers can retain their previously chosen structural data. -/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation
open EinsteinFull.Calculus.C10TestBlocks

/-- A polynomial times the Gaussian is bounded by completing the square. -/
lemma flux_lattice_polynomial_gaussian_le (N : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (1 + u) ^ N * Real.exp (-u ^ 2) ≤ Real.exp ((N : ℝ) ^ 2 / 4) := by
  calc
    _ ≤ (Real.exp u) ^ N * Real.exp (-u ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using Real.add_one_le_exp u) N
    _ = Real.exp ((N : ℝ) * u - u ^ 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (u - (N : ℝ) / 2)])

/-- The integer cell containing the observation point is uniformly close in
Euclidean norm; the bound uses the same coordinate carrier as the manuscript. -/
lemma flux_lattice_floor_distance (d : ℕ) (r : ℝ) (hr : 0 < r) (x : Vec d) :
    euclideanNorm (x - covarianceTileCenter r (fun i => ⌊x i / r⌋)) ≤
      (d : ℝ) * r := by
  have hc (i : Fin d) : |x i - r * (⌊x i / r⌋ : ℝ)| ≤ r := by
    have hlo := Int.floor_le (x i / r)
    have hhi := Int.lt_floor_add_one (x i / r)
    have h₁ : r * (⌊x i / r⌋ : ℝ) ≤ x i := by
      simpa only [mul_comm] using (le_div_iff₀ hr).mp hlo
    have h₂ : x i < r * ((⌊x i / r⌋ : ℝ) + 1) := by
      simpa only [mul_comm] using (div_lt_iff₀ hr).mp hhi
    rw [abs_of_nonneg (sub_nonneg.mpr h₁)]
    linarith
  calc
    _ ≤ ∑ i, |x i - r * (⌊x i / r⌋ : ℝ)| := by
      exact EinsteinFull.Calculus.S1.euclideanNorm_le_sum_abs _
    _ ≤ ∑ _i : Fin d, r := Finset.sum_le_sum fun i _ => hc i
    _ = _ := by simp

/-- Translation of the integer index preserves the mesh-normalized decay
mass. The observation point will only determine this integer translation. -/
lemma flux_lattice_shifted_decay (d : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (m : Fin d → ℤ) :
    Summable (fun z : Fin d → ℤ =>
      ((1 + euclideanNorm (covarianceTileCenter a (z - m))) ^ (2 * d))⁻¹) ∧
    a ^ d * (∑' z : Fin d → ℤ,
      ((1 + euclideanNorm (covarianceTileCenter a (z - m))) ^ (2 * d))⁻¹) ≤
      3 ^ d := by
  let e : (Fin d → ℤ) ≃ (Fin d → ℤ) :=
    { toFun := fun z => z - m
      invFun := fun z => z + m
      left_inv := by intro z; simp
      right_inv := by intro z; simp }
  have hs := summable_lattice_euclidean_decay (d := d) (N := 2 * d) ha le_rfl
  refine ⟨e.summable_iff.mpr hs, ?_⟩
  change a ^ d * (∑' z,
    ((1 + euclideanNorm (covarianceTileCenter a (e z))) ^ (2 * d))⁻¹) ≤ 3 ^ d
  rw [e.tsum_eq (fun z : Fin d → ℤ =>
    ((1 + euclideanNorm (covarianceTileCenter a z)) ^ (2 * d))⁻¹)]
  exact mesh_tsum_lattice_euclidean_decay_le ha ha1 le_rfl

/-- The enlarged mesh controls distance from every point of the ball to
the integer cell containing the observation point. -/
lemma flux_lattice_enlarged_distance (d : ℕ) (r ρ R : ℝ)
    (hr : 0 < r) (hρ : 0 < ρ) (hR : 0 ≤ R) (x y : Vec d)
    (z : Fin d → ℤ)
    (hy : euclideanNorm (y - covarianceTileCenter r z) ≤ R * r) :
    1 + euclideanNorm (covarianceTileCenter (r / (r + ρ))
        (z - fun i => ⌊x i / r⌋)) ≤
      (1 + R + (d : ℝ)) * (1 + euclideanNorm (x - y) / ρ) := by
  let m : Fin d → ℤ := fun i => ⌊x i / r⌋
  let c := covarianceTileCenter r z
  let b := covarianceTileCenter r m
  have hsum : 0 < r + ρ := add_pos hr hρ
  have hn : 0 ≤ euclideanNorm (x - y) := Real.sqrt_nonneg _
  have he : covarianceTileCenter (r / (r + ρ)) (z - m) =
      (r + ρ)⁻¹ • (c - b) := by
    ext i
    simp only [covarianceTileCenter, Pi.sub_apply, Int.cast_sub, Pi.smul_apply,
      smul_eq_mul, c, b]
    ring
  have hc : euclideanNorm (c - b) ≤ euclideanNorm (x - y) + (R + d) * r := by
    have hdecomp : c - b = (c - y) + (y - x) + (x - b) := by abel
    rw [hdecomp]
    have h₁ := TimeChange.euclideanNorm_add_le ((c - y) + (y - x)) (x - b)
    have h₂ := TimeChange.euclideanNorm_add_le (c - y) (y - x)
    rw [S3LocalAv.euclideanNorm_sub_comm' c y, S3LocalAv.euclideanNorm_sub_comm' y x] at h₂
    have h₃ := flux_lattice_floor_distance d r hr x
    change euclideanNorm (x - b) ≤ (d : ℝ) * r at h₃
    change euclideanNorm (y - c) ≤ R * r at hy
    linarith
  have hnorm : euclideanNorm (covarianceTileCenter (r / (r + ρ)) (z - m)) ≤
      euclideanNorm (x - y) / ρ + R + d := by
    rw [he, TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hsum),
      inv_mul_eq_div]
    apply (div_le_iff₀ hsum).mpr
    have he₁ : euclideanNorm (x - y) / ρ * (r + ρ) =
        euclideanNorm (x - y) / ρ * r + euclideanNorm (x - y) := by
      field_simp
    have hnon := mul_nonneg (div_nonneg hn hρ.le) hr.le
    have hnon₂ := mul_nonneg (add_nonneg hR (Nat.cast_nonneg d)) hρ.le
    nlinarith only [hc, he₁, hnon, hnon₂]
  change 1 + euclideanNorm (covarianceTileCenter (r / (r + ρ)) (z - m)) ≤ _
  have hnon := mul_nonneg (add_nonneg hR (Nat.cast_nonneg d)) (div_nonneg hn hρ.le)
  nlinarith only [hnorm, hnon]

/-- Pointwise Gaussian domination by a translated summable lattice weight.
No constant depends on the center, radius scale, or Gaussian width. -/
lemma flux_lattice_gaussian_le_weight (d : ℕ) (r ρ R A : ℝ)
    (hr : 0 < r) (hρ : 0 < ρ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (x y : Vec d) (z : Fin d → ℤ)
    (hy : euclideanNorm (y - covarianceTileCenter r z) ≤ R * r) :
    A * Real.exp (-euclideanNorm (x - y) ^ 2 / ρ ^ 2) ≤
      A * ((1 + R + (d : ℝ)) ^ d * Real.exp ((d : ℝ) ^ 2 / 4)) *
        ((1 + euclideanNorm (covarianceTileCenter (r / (r + ρ))
          (z - fun i => ⌊x i / r⌋))) ^ d)⁻¹ := by
  let u := euclideanNorm (x - y) / ρ
  let w := 1 + euclideanNorm (covarianceTileCenter (r / (r + ρ))
    (z - fun i => ⌊x i / r⌋))
  have hu : 0 ≤ u := div_nonneg (Real.sqrt_nonneg _) hρ.le
  have hw : 0 < w := add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _)
  have he : -euclideanNorm (x - y) ^ 2 / ρ ^ 2 = -u ^ 2 := by
    dsimp [u]
    ring
  rw [he]
  have hbound : w ^ d * Real.exp (-u ^ 2) ≤
      (1 + R + (d : ℝ)) ^ d * Real.exp ((d : ℝ) ^ 2 / 4) := by
    calc
      _ ≤ ((1 + R + (d : ℝ)) * (1 + u)) ^ d * Real.exp (-u ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hw.le (flux_lattice_enlarged_distance d r ρ R hr hρ hR x y z hy) d)
          (Real.exp_nonneg _)
      _ = (1 + R + (d : ℝ)) ^ d * ((1 + u) ^ d * Real.exp (-u ^ 2)) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (flux_lattice_polynomial_gaussian_le d u hu)
        (by positivity)
  have hp : Real.exp (-u ^ 2) ≤
      ((1 + R + (d : ℝ)) ^ d * Real.exp ((d : ℝ) ^ 2 / 4)) / w ^ d :=
    (le_div_iff₀ (pow_pos hw d)).mpr (by simpa only [mul_comm] using hbound)
  simpa only [div_eq_mul_inv, mul_assoc, w] using mul_le_mul_of_nonneg_left hp hA

/-- The literal supremum over a Euclidean ball around a lattice center. -/
noncomputable def fluxLatticeEnvelope (d : ℕ) (r ρ R A : ℝ) (x : Vec d)
    (z : Fin d → ℤ) : ℝ :=
  sSup ((fun y : Vec d => A * Real.exp (-euclideanNorm (x - y) ^ 2 / ρ ^ 2)) ''
    {y : Vec d | euclideanNorm (y - covarianceTileCenter r z) ≤ R * r})

/-- The supremum keeps the pointwise Gaussian decay bound, including its
nonnegativity; boundedness of its range is proved before using `sSup`. -/
lemma flux_lattice_envelope_le_weight (d : ℕ) (r ρ R A : ℝ)
    (hr : 0 < r) (hρ : 0 < ρ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (x : Vec d) (z : Fin d → ℤ) :
    0 ≤ fluxLatticeEnvelope d r ρ R A x z ∧
    fluxLatticeEnvelope d r ρ R A x z ≤
      A * ((1 + R + (d : ℝ)) ^ d * Real.exp ((d : ℝ) ^ 2 / 4)) *
        ((1 + euclideanNorm (covarianceTileCenter (r / (r + ρ))
          (z - fun i => ⌊x i / r⌋))) ^ d)⁻¹ := by
  let c := covarianceTileCenter r z
  have hc : euclideanNorm (c - c) ≤ R * r := by
    simp only [sub_self, euclideanNorm, euclideanSq, dot, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, Real.sqrt_zero]
    exact mul_nonneg hR hr.le
  have hb : BddAbove ((fun y : Vec d =>
      A * Real.exp (-euclideanNorm (x - y) ^ 2 / ρ ^ 2)) ''
      {y : Vec d | euclideanNorm (y - c) ≤ R * r}) := by
    refine ⟨A, ?_⟩
    rintro _ ⟨y, _, rfl⟩
    calc
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg ρ))) hA
      _ = A := mul_one A
  constructor
  · exact (mul_nonneg hA (Real.exp_nonneg _)).trans (le_csSup hb ⟨c, hc, rfl⟩)
  · exact csSup_le ⟨_, c, hc, rfl⟩ (by
      rintro _ ⟨y, hy, rfl⟩
      exact flux_lattice_gaussian_le_weight d r ρ R A hr hρ hR hA x y z hy)

/-- The actual Euclidean-ball envelope is square summable at every positive
mesh and Gaussian width, with the correct effective-volume bound. -/
theorem flux_lattice_envelope_square_sum_le (d : ℕ) (r ρ R A : ℝ)
    (hr : 0 < r) (hρ : 0 < ρ) (hR : 0 ≤ R) (hA : 0 ≤ A) (x : Vec d) :
    let a := r / (r + ρ)
    let B := (1 + R + (d : ℝ)) ^ d * Real.exp ((d : ℝ) ^ 2 / 4)
    Summable (fun z : Fin d → ℤ => (fluxLatticeEnvelope d r ρ R A x z) ^ 2) ∧
    (∑' z : Fin d → ℤ, (fluxLatticeEnvelope d r ρ R A x z) ^ 2) ≤
      (A * B) ^ 2 * (3 : ℝ) ^ d / a ^ d := by
  dsimp only
  let a := r / (r + ρ)
  let B := (1 + R + (d : ℝ)) ^ d * Real.exp ((d : ℝ) ^ 2 / 4)
  let m : Fin d → ℤ := fun i => ⌊x i / r⌋
  let w : (Fin d → ℤ) → ℝ := fun z =>
    ((1 + euclideanNorm (covarianceTileCenter a (z - m))) ^ (2 * d))⁻¹
  have ha : 0 < a := div_pos hr (add_pos hr hρ)
  have ha1 : a ≤ 1 := (div_le_one (add_pos hr hρ)).mpr (by linarith)
  obtain ⟨hs, ht⟩ := flux_lattice_shifted_decay d ha ha1 m
  change Summable w at hs
  change a ^ d * (∑' z, w z) ≤ 3 ^ d at ht
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound (z : Fin d → ℤ) :
      (fluxLatticeEnvelope d r ρ R A x z) ^ 2 ≤ (A * B) ^ 2 * w z := by
    obtain ⟨h0, hz⟩ := flux_lattice_envelope_le_weight d r ρ R A hr hρ hR hA x z
    have hp := pow_le_pow_left₀ h0 hz 2
    simpa only [B, w, a, m, mul_pow, inv_pow, ← pow_mul, Nat.mul_comm d 2] using hp
  have hsum : Summable (fun z : Fin d → ℤ =>
      (fluxLatticeEnvelope d r ρ R A x z) ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hbound (hs.mul_left ((A * B) ^ 2))
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' z, (A * B) ^ 2 * w z := hsum.tsum_le_tsum hbound (hs.mul_left _)
    _ = (A * B) ^ 2 * (∑' z, w z) := tsum_mul_left
    _ ≤ (A * B) ^ 2 * ((3 : ℝ) ^ d / a ^ d) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ (pow_pos ha d)).mpr (by nlinarith only [ht]))
        (sq_nonneg _)
    _ = _ := by ring

/-- Taking the square root of the effective-volume estimate. -/
theorem flux_lattice_envelope_l2_le (d : ℕ) (r ρ R A : ℝ)
    (hr : 0 < r) (hρ : 0 < ρ) (hR : 0 ≤ R) (hA : 0 ≤ A) (x : Vec d) :
    Summable (fun z : Fin d → ℤ => (fluxLatticeEnvelope d r ρ R A x z) ^ 2) ∧
    Real.sqrt (∑' z : Fin d → ℤ, (fluxLatticeEnvelope d r ρ R A x z) ^ 2) ≤
      ((1 + R + (d : ℝ)) ^ d * Real.exp ((d : ℝ) ^ 2 / 4) *
        (3 : ℝ) ^ ((d : ℝ) / 2)) * A * ((r + ρ) / r) ^ ((d : ℝ) / 2) := by
  obtain ⟨hs, ht⟩ := flux_lattice_envelope_square_sum_le d r ρ R A hr hρ hR hA x
  refine ⟨hs, (Real.sqrt_le_sqrt ht).trans_eq ?_⟩
  let B := (1 + R + (d : ℝ)) ^ d * Real.exp ((d : ℝ) ^ 2 / 4)
  change Real.sqrt ((A * B) ^ 2 * (3 : ℝ) ^ d / (r / (r + ρ)) ^ d) = _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  rw [mul_div_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hA hB)]
  have he : Real.sqrt ((3 : ℝ) ^ d / (r / (r + ρ)) ^ d) =
      (3 : ℝ) ^ ((d : ℝ) / 2) * ((r + ρ) / r) ^ ((d : ℝ) / 2) := by
    rw [← div_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    have hid : (3 : ℝ) / (r / (r + ρ)) = 3 * ((r + ρ) / r) := by field_simp
    rw [hid, show (d : ℝ) * (1 / 2) = (d : ℝ) / 2 by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  rw [he]
  dsimp [B]
  ring

/-- Exchange of the two dimensionless ratios gives the exact lattice
normalization used in the gain statement. -/
lemma flux_lattice_scale_identity (d : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    s ^ (-(d : ℝ) / 2) * (1 + Real.sqrt s / r) ^ ((d : ℝ) / 2) =
      r ^ (-(d : ℝ) / 2) * s ^ (-(d : ℝ) / 4) *
        (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have he : 1 + Real.sqrt s / r = (Real.sqrt s / r) * (1 + r / Real.sqrt s) := by
    field_simp
    ring
  rw [he, Real.mul_rpow (by positivity) (by positivity),
    Real.div_rpow (Real.sqrt_nonneg s) hr.le,
    Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
  have hsum : s ^ (-(d : ℝ) / 2) * s ^ ((1 / 2 : ℝ) * ((d : ℝ) / 2)) =
      s ^ (-(d : ℝ) / 4) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have hrneg : r ^ (-(d : ℝ) / 2) = (r ^ ((d : ℝ) / 2))⁻¹ := by
    rw [neg_div, Real.rpow_neg hr.le]
  rw [hrneg]
  calc
    _ = (r ^ ((d : ℝ) / 2))⁻¹ *
        (s ^ (-(d : ℝ) / 2) * s ^ ((1 / 2 : ℝ) * ((d : ℝ) / 2))) *
        (1 + r / s ^ (1 / 2 : ℝ)) ^ ((d : ℝ) / 2) := by ring
    _ = _ := by rw [hsum]

/-- The prescribed exponent choice leaves the required strict decay margin. -/
lemma flux_lattice_exponent_margin (d : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    -1 - κ / 2 + (κ / (16 * ((d : ℝ) + 2))) * ((d : ℝ) + 1 - κ) ≤
      -1 - κ / 4 := by
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hden : 0 < 16 * ((d : ℝ) + 2) := by positivity
  have he : κ / (16 * ((d : ℝ) + 2)) * ((d : ℝ) + 1 - κ) ≤ κ / 4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hκ.le hd]
  linarith only [he]

/-- The inflation factor at the mesoscopic radius has the required time
power, for every nonnegative supplied exponent. -/
lemma flux_lattice_inflation_le (d : ℕ) (η t s : ℝ)
    (hη : 0 ≤ η) (ht : 1 ≤ t) (hs : 1 ≤ s) :
    (1 + t ^ (1 / 2 + η) / Real.sqrt s) ^ ((d : ℝ) / 2) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * t ^ (η * (d : ℝ) / 2) *
        (1 + t / s) ^ ((d : ℝ) / 4) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hηt : 1 ≤ t ^ η := Real.one_le_rpow ht hη
  have hq : 0 ≤ t / s := div_nonneg ht0.le hs0.le
  have hroot : 1 ≤ Real.sqrt (1 + t / s) := by
    exact Real.one_le_sqrt.mpr (by linarith only [hq])
  have hroot' : Real.sqrt t / Real.sqrt s ≤ Real.sqrt (1 + t / s) := by
    rw [← Real.sqrt_div ht0.le]
    exact Real.sqrt_le_sqrt (by linarith)
  have hr : t ^ (1 / 2 + η) = Real.sqrt t * t ^ η := by
    rw [Real.rpow_add ht0, Real.sqrt_eq_rpow]
  have hscalar : 1 + t ^ (1 / 2 + η) / Real.sqrt s ≤
      2 * t ^ η * Real.sqrt (1 + t / s) := by
    rw [hr, mul_comm (Real.sqrt t) (t ^ η), mul_div_assoc]
    have h₁ := mul_le_mul_of_nonneg_left hroot' (Real.rpow_nonneg ht0.le η)
    have h₂ : 1 ≤ t ^ η * Real.sqrt (1 + t / s) :=
      one_le_mul_of_one_le_of_one_le hηt hroot
    nlinarith only [h₁, h₂]
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + t ^ (1 / 2 + η) / Real.sqrt s)
    hscalar (by positivity : 0 ≤ (d : ℝ) / 2)
  calc
    _ ≤ (2 * t ^ η * Real.sqrt (1 + t / s)) ^ ((d : ℝ) / 2) := hp
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg ht0.le _),
        ← Real.rpow_mul ht0.le, Real.sqrt_eq_rpow,
        ← Real.rpow_mul (by positivity : 0 ≤ 1 + t / s)]
      congr 2 <;> ring

/-- Uniform square summability for the actual Gaussian at arbitrary positive
radius and smoothing scale. The constant precedes every scale and center. -/
theorem flux_lattice_gaussian_square_sum (d : ℕ) (Cenv : ℝ) (hCenv : 1 ≤ Cenv) :
    ∃ C : ℝ, 0 < C ∧ ∀ r s : ℝ, 0 < r → 0 < s → ∀ x : Vec d,
      let R := 2 * Real.sqrt (d : ℝ) + 2
      let W := fun z : Fin d → ℤ => sSup
        ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
          Real.exp (-euclideanNorm (x - y) ^ 2 / (Cenv * s))) ''
            {y : Vec d | euclideanNorm (y - fun j => r * (z j : ℝ)) ≤ R * r})
      Summable (fun z : Fin d → ℤ => (W z) ^ 2) ∧
      Real.sqrt (∑' z : Fin d → ℤ, (W z) ^ 2) ≤
        C * r ^ (-(d : ℝ) / 2) * s ^ (-(d : ℝ) / 4) *
          (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) := by
  let R := 2 * Real.sqrt (d : ℝ) + 2
  let C₀ := (1 + R + (d : ℝ)) ^ d * Real.exp ((d : ℝ) ^ 2 / 4) *
    (3 : ℝ) ^ ((d : ℝ) / 2)
  have hCenv0 : 0 < Cenv := lt_of_lt_of_le zero_lt_one hCenv
  have hCroot : 1 ≤ Real.sqrt Cenv := Real.one_le_sqrt.mpr hCenv
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀ * (Real.sqrt Cenv) ^ ((d : ℝ) / 2), by positivity, ?_⟩
  intro r s hr hs x
  let ρ := Real.sqrt (Cenv * s)
  have hρ : 0 < ρ := Real.sqrt_pos.mpr (mul_pos hCenv0 hs)
  have hρeq : ρ = Real.sqrt Cenv * Real.sqrt s := Real.sqrt_mul hCenv0.le s
  have hρsq : ρ ^ 2 = Cenv * s := Real.sq_sqrt (mul_nonneg hCenv0.le hs.le)
  have hsum := flux_lattice_envelope_l2_le d r ρ R (s ^ (-(d : ℝ) / 2))
    hr hρ hR (Real.rpow_nonneg hs.le _) x
  simp only [fluxLatticeEnvelope, hρsq] at hsum
  dsimp only
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  change C₀ * s ^ (-(d : ℝ) / 2) * ((r + ρ) / r) ^ ((d : ℝ) / 2) ≤ _
  have hratio : (r + ρ) / r ≤ Real.sqrt Cenv * (1 + Real.sqrt s / r) := by
    rw [hρeq]
    have hid : (r + Real.sqrt Cenv * Real.sqrt s) / r =
        1 + Real.sqrt Cenv * (Real.sqrt s / r) := by field_simp
    rw [hid]
    nlinarith only [hCroot]
  calc
    _ ≤ C₀ * s ^ (-(d : ℝ) / 2) *
        (Real.sqrt Cenv * (1 + Real.sqrt s / r)) ^ ((d : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hratio (by positivity)) (by positivity)
    _ = (C₀ * (Real.sqrt Cenv) ^ ((d : ℝ) / 2)) *
        (s ^ (-(d : ℝ) / 2) * (1 + Real.sqrt s / r) ^ ((d : ℝ) / 2)) := by
      rw [Real.mul_rpow (Real.sqrt_nonneg _) (by positivity)]
      ring
    _ = _ := by
      rw [flux_lattice_scale_identity d r s hr hs]
      ring

/-- The deterministic lattice estimate with the already chosen structural
exponent and Gaussian width retained verbatim. -/
theorem carverS_flux_lattice_square_sum_fixed_parameters (d : ℕ) (hd : 2 ≤ d)
    (κ Cenv : ℝ) (hκ : 0 < κ) (hCenv : 1 ≤ Cenv) :
    ∃ Clat : ℝ, 0 < Clat ∧ ∀ t s : ℝ, 1 ≤ t → 1 ≤ s → ∀ x : Vec d,
      let η := κ / (16 * ((d : ℝ) + 2))
      let r := t ^ (1 / 2 + η)
      let R := 2 * Real.sqrt (d : ℝ) + 2
      let W := fun z : Fin d → ℤ => sSup
        ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
          Real.exp (-euclideanNorm (x - y) ^ 2 / (Cenv * s))) ''
            {y : Vec d | euclideanNorm (y - fun j => r * (z j : ℝ)) ≤ R * r})
      Summable (fun z : Fin d → ℤ => (W z) ^ 2) ∧
      Real.sqrt (∑' z : Fin d → ℤ, (W z) ^ 2) ≤
        Clat * r ^ (-(d : ℝ) / 2) * s ^ (-(d : ℝ) / 4) *
          (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) ∧
      (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) ≤
        Clat * t ^ (η * (d : ℝ) / 2) * (1 + t / s) ^ ((d : ℝ) / 4) := by
  obtain ⟨C, hC, h⟩ := flux_lattice_gaussian_square_sum d Cenv hCenv
  refine ⟨max C ((2 : ℝ) ^ ((d : ℝ) / 2)), lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro t s ht hs x
  dsimp only
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hη : 0 ≤ κ / (16 * ((d : ℝ) + 2)) := by positivity
  obtain ⟨hsum, hbound⟩ := h (t ^ (1 / 2 + κ / (16 * ((d : ℝ) + 2)))) s
    (Real.rpow_pos_of_pos ht0 _) hs0 x
  refine ⟨hsum, hbound.trans ?_, (flux_lattice_inflation_le d _ t s hη ht hs).trans ?_⟩
  · gcongr
    exact le_max_left _ _
  · gcongr
    exact le_max_right _ _

/-- Deterministic lattice square sum and exponent arithmetic in the exact
structural quantifier order of the forced-flux gain. -/
theorem carverS_flux_lattice_square_sum : ∀ (d : ℕ) (hd : 2 ≤ d),
    ∃ κ η η₀ ε Clat : ℝ, ∃ L : ℕ → ℕ,
      0 < κ ∧ κ < 1 / 2 ∧ η = κ / (16 * ((d : ℝ) + 2)) ∧
      η₀ = η / 4 ∧ ε = κ / 8 ∧ 0 < ε ∧ 0 < η₀ ∧
      0 < Clat ∧
      -1 - κ / 2 + η * ((d : ℝ) + 1 - κ) ≤ -1 - κ / 4 ∧
      (∀ t s : ℝ, 1 ≤ t → 1 ≤ s → ∀ x : Vec d,
        let r := t ^ (1 / 2 + η)
        let R := 2 * Real.sqrt (d : ℝ) + 2
        let W := fun z : Fin d → ℤ => sSup
          ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
            Real.exp (-euclideanNorm (x - y) ^ 2 / s)) ''
              {y : Vec d | euclideanNorm
                (y - fun j => r * (z j : ℝ)) ≤ R * r})
        Summable (fun z : Fin d → ℤ => (W z) ^ 2) ∧
        Real.sqrt (∑' z : Fin d → ℤ, (W z) ^ 2) ≤
          Clat * r ^ (-(d : ℝ) / 2) * s ^ (-(d : ℝ) / 4) *
            (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) ∧
        (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) ≤
          Clat * t ^ (η * (d : ℝ) / 2) * (1 + t / s) ^ ((d : ℝ) / 4)) := by
  intro d hd
  let κ : ℝ := 1 / 4
  let η := κ / (16 * ((d : ℝ) + 2))
  have hκ : 0 < κ := by norm_num [κ]
  have hκhalf : κ < 1 / 2 := by norm_num [κ]
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C, hC, h⟩ := carverS_flux_lattice_square_sum_fixed_parameters d hd κ 1 hκ le_rfl
  refine ⟨κ, η, η / 4, κ / 8, C, fun _ => 0, hκ, hκhalf, rfl, rfl, rfl,
    by positivity, by positivity, hC, flux_lattice_exponent_margin d κ hκ, ?_⟩
  simpa only [one_mul] using h

end EinsteinFull.Blueprint
