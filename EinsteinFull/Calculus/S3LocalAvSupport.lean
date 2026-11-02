import EinsteinFull.Frozen.GaussianAveragingSeminorm
import EinsteinRelation.TimeChange.EuclideanTransport
import EinsteinRelation.Correctors.HeatKernelConvolution
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Elementary support for the local averaging estimate `e:local-av`

Euclidean-norm facts on the coordinate carrier, the Euclidean `ℓ²`-norm `vnorm` of a vector of
classes, the volume of Euclidean balls, the sup bound of the heat kernel, and the real-analysis
tail estimate for the annulus sum.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull.S3LocalAv

open EinsteinRelation

section Norm

variable {d : ℕ}

theorem euclideanSq_nonneg' (x : Vec d) : 0 ≤ euclideanSq x := by
  show 0 ≤ ∑ i, x i * x i
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem continuous_euclideanNorm' : Continuous (fun x : Vec d => euclideanNorm x) := by
  unfold euclideanNorm euclideanSq dot
  exact Real.continuous_sqrt.comp
    (continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i))

theorem euclideanNorm_neg' (x : Vec d) : euclideanNorm (-x) = euclideanNorm x := by
  have h := TimeChange.euclideanNorm_smul (-1 : ℝ) x
  simpa using h

theorem euclideanNorm_sub_comm' (x y : Vec d) : euclideanNorm (x - y) = euclideanNorm (y - x) := by
  rw [← neg_sub y x, euclideanNorm_neg']

theorem euclideanNorm_sub_le' (x y : Vec d) :
    euclideanNorm (x - y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [sub_eq_add_neg]
  refine (TimeChange.euclideanNorm_add_le x (-y)).trans (le_of_eq ?_)
  rw [euclideanNorm_neg']

theorem abs_apply_le_euclideanNorm (x : Vec d) (i : Fin d) : |x i| ≤ euclideanNorm x := by
  apply Real.abs_le_sqrt
  show (x i) ^ 2 ≤ ∑ j, x j * x j
  rw [sq]
  exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
    (Finset.mem_univ i)

theorem measurableSet_euclideanBall (x : Vec d) (R : ℝ) :
    MeasurableSet {y : Vec d | euclideanNorm (y - x) < R} :=
  (isOpen_lt (continuous_euclideanNorm'.comp (continuous_id.sub continuous_const))
    continuous_const).measurableSet

theorem volume_euclideanBall_le (x : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    volume {y : Vec d | euclideanNorm (y - x) < R} ≤ ENNReal.ofReal ((2 * R) ^ d) := by
  have hsub : {y : Vec d | euclideanNorm (y - x) < R} ⊆
      Set.Icc (fun i => x i - R) (fun i => x i + R) := by
    intro y hy
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h2 : |y i - x i| < R :=
        lt_of_le_of_lt (abs_apply_le_euclideanNorm (y - x) i) hy
      have h3 := (abs_lt.mp h2).1
      show x i - R ≤ y i
      linarith
    · have h2 : |y i - x i| < R :=
        lt_of_le_of_lt (abs_apply_le_euclideanNorm (y - x) i) hy
      have h3 := (abs_lt.mp h2).2
      show y i ≤ x i + R
      linarith
  calc volume {y : Vec d | euclideanNorm (y - x) < R}
      ≤ volume (Set.Icc (fun i => x i - R) (fun i => x i + R)) := measure_mono hsub
    _ = ∏ i : Fin d, ENNReal.ofReal ((x i + R) - (x i - R)) := Real.volume_Icc_pi
    _ = ENNReal.ofReal ((2 * R) ^ d) := by
      have h : ∀ i : Fin d, (x i + R) - (x i - R) = 2 * R := fun i => by ring
      simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [ENNReal.ofReal_pow (by positivity)]

theorem integral_indicator_euclideanBall_le (x : Vec d) {R : ℝ} (hR : 0 ≤ R) (c : ℝ)
    (hc : 0 ≤ c) :
    ∫ y, {y : Vec d | euclideanNorm (y - x) < R}.indicator (fun _ => c) y ≤ c * (2 * R) ^ d := by
  rw [integral_indicator_const c (measurableSet_euclideanBall x R), smul_eq_mul]
  have h : volume.real {y : Vec d | euclideanNorm (y - x) < R} ≤ (2 * R) ^ d := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (volume_euclideanBall_le x hR)
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  calc volume.real {y : Vec d | euclideanNorm (y - x) < R} * c ≤ (2 * R) ^ d * c :=
        mul_le_mul_of_nonneg_right h hc
    _ = c * (2 * R) ^ d := mul_comm _ _

theorem measure_euclideanBall_ne_top (x : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    volume {y : Vec d | euclideanNorm (y - x) < R} ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (volume_euclideanBall_le x hR)

end Norm

section Kernel

variable {d : ℕ}

theorem euclideanHeatKernel_le_pow_inv {ρ : ℝ} (hρ : 0 < ρ) (y : Vec d) :
    Correctors.euclideanHeatKernel (ρ ^ 2) y ≤ (ρ ^ d)⁻¹ := by
  unfold Correctors.euclideanHeatKernel
  have ht : 0 < ρ ^ 2 := by positivity
  have h1 : (4 * Real.pi * ρ ^ 2) ^ (-(d : ℝ) / 2) =
      (4 * Real.pi) ^ (-(d : ℝ) / 2) * (ρ ^ d)⁻¹ := by
    rw [Real.mul_rpow (by positivity) ht.le]
    congr 1
    rw [← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ.le, ← Real.rpow_natCast ρ d,
      ← Real.rpow_neg hρ.le]
    congr 1
    push_cast
    ring
  have h2 : (4 * Real.pi) ^ (-(d : ℝ) / 2) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · have := Real.pi_gt_three
      linarith
    · have h := (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
      linarith
  have h3 : Real.exp (-(euclideanSq y) / (4 * ρ ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [euclideanSq_nonneg' y]) (by positivity)
  have h4 : 0 ≤ (4 * Real.pi) ^ (-(d : ℝ) / 2) := by positivity
  have h5 : 0 ≤ (ρ ^ d)⁻¹ := by positivity
  rw [h1]
  calc (4 * Real.pi) ^ (-(d : ℝ) / 2) * (ρ ^ d)⁻¹ * Real.exp (-(euclideanSq y) / (4 * ρ ^ 2))
      ≤ 1 * (ρ ^ d)⁻¹ * 1 := by
        apply mul_le_mul (mul_le_mul h2 le_rfl h5 zero_le_one) h3 (Real.exp_pos _).le
        positivity
    _ = (ρ ^ d)⁻¹ := by ring

end Kernel

section Vnorm

variable {E : Type*} [NormedAddCommGroup E] {d : ℕ}

/-- The Euclidean `ℓ²`-norm across the coordinates of a vector of classes. -/
noncomputable def vnorm (F : Fin d → E) : ℝ := Real.sqrt (∑ j, ‖F j‖ ^ 2)

theorem vnorm_nonneg (F : Fin d → E) : 0 ≤ vnorm F := Real.sqrt_nonneg _

theorem vnorm_eq_norm (F : Fin d → E) :
    vnorm F = ‖(WithLp.toLp 2 F : PiLp 2 fun _ : Fin d => E)‖ := by
  rw [PiLp.norm_eq_of_L2]
  rfl

theorem vnorm_add_le (F G : Fin d → E) : vnorm (F + G) ≤ vnorm F + vnorm G := by
  rw [vnorm_eq_norm, vnorm_eq_norm, vnorm_eq_norm]
  exact norm_add_le (WithLp.toLp 2 F : PiLp 2 fun _ : Fin d => E) (WithLp.toLp 2 G)

theorem vnorm_sub_le (F G : Fin d → E) : vnorm (F - G) ≤ vnorm F + vnorm G := by
  rw [vnorm_eq_norm, vnorm_eq_norm, vnorm_eq_norm]
  exact norm_sub_le (WithLp.toLp 2 F : PiLp 2 fun _ : Fin d => E) (WithLp.toLp 2 G)

theorem vnorm_le_mul {F G : Fin d → E} {c : ℝ} (hc : 0 ≤ c) (h : ∀ j, ‖F j‖ ≤ c * ‖G j‖) :
    vnorm F ≤ c * vnorm G := by
  unfold vnorm
  calc Real.sqrt (∑ j, ‖F j‖ ^ 2) ≤ Real.sqrt (c ^ 2 * ∑ j, ‖G j‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        calc ‖F j‖ ^ 2 ≤ (c * ‖G j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h j) 2
          _ = c ^ 2 * ‖G j‖ ^ 2 := mul_pow _ _ _
    _ = c * Real.sqrt (∑ j, ‖G j‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem vnorm_zero : vnorm (0 : Fin d → E) = 0 := by
  simp [vnorm]

end Vnorm

section Tail

/-- The annulus terms of the local averaging estimate. -/
noncomputable def annulus (d : ℕ) (c m A s : ℝ) (n : ℕ) : ℝ :=
  (((n : ℝ) + 1) * Real.sqrt s) ^ ((d : ℝ) / 2) *
    min m (max m A * Real.exp (-c * (n : ℝ) ^ 2))

theorem annulus_nonneg (d : ℕ) {c m A s : ℝ} (hm : 0 ≤ m) (n : ℕ) :
    0 ≤ annulus d c m A s n := by
  unfold annulus
  apply mul_nonneg
  · exact Real.rpow_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) _
  · exact le_min hm (mul_nonneg (le_max_of_le_left hm) (Real.exp_pos _).le)

theorem summable_gauss_weight (d : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * Real.exp (-r * (n : ℝ) ^ 2) := by
  have hf := (Real.summable_pow_mul_exp_neg_nat_mul d hr)
  have hf1 : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ d * Real.exp (-r * ((n + 1 : ℕ) : ℝ)) :=
    (summable_nat_add_iff 1).2 hf
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hf1.mul_left (Real.exp r))
  have h1 : ((n : ℝ) + 1) ^ ((d : ℝ) / 2) ≤ ((n : ℝ) + 1) ^ d := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have h := (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    linarith
  have h2 : Real.exp (-r * (n : ℝ) ^ 2) ≤ Real.exp r * Real.exp (-r * ((n + 1 : ℕ) : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    push_cast
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast Nat.le_self_pow two_ne_zero n
    nlinarith [mul_le_mul_of_nonneg_left hn hr.le]
  calc ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * Real.exp (-r * (n : ℝ) ^ 2)
      ≤ ((n : ℝ) + 1) ^ d * (Real.exp r * Real.exp (-r * ((n + 1 : ℕ) : ℝ))) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ = Real.exp r * (((n + 1 : ℕ) : ℝ) ^ d * Real.exp (-r * ((n + 1 : ℕ) : ℝ))) := by
        push_cast
        ring

/-- The pure real-analysis tail estimate for the annulus sum. -/
theorem annulus_tail (d : ℕ) {c A₀ a : ℝ} (hc : 0 < c) (hA₀ : 0 < A₀) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s m A : ℝ, 1 ≤ s → 0 ≤ m → 0 ≤ A →
      m ≤ A₀ * s ^ (-(d : ℝ) / 4) → A ≤ A₀ * (2 + s) ^ a →
      Summable (annulus d c m A s) ∧
      ∑' n, annulus d c m A s n ≤ C * Real.log (2 + s) ^ (d + 1) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set G : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * Real.exp (-(c / 2) * (n : ℝ) ^ 2)
    with hG
  have hGs := summable_gauss_weight d (show 0 < c / 2 by positivity)
  have hG0 : 0 ≤ G := tsum_nonneg fun n => by positivity
  set κ : ℝ := (2 / c) * ((d : ℝ) / 4 + a) + 2 / Real.log 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  refine ⟨A₀ * (κ ^ (d + 1) + G / Real.log 2 ^ (d + 1)) + 1, by positivity, ?_⟩
  intro s m A hs1 hm hA hms hAs
  have hs0 : 0 < s := by linarith
  set L : ℝ := Real.log (2 + s) with hL
  have hLl : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hL0 : 0 < L := lt_of_lt_of_le hl2 hLl
  -- the polynomial factors
  set q : ℝ := Real.sqrt s ^ ((d : ℝ) / 2) with hq
  have hq' : q = s ^ ((d : ℝ) / 4) := by
    rw [hq, Real.sqrt_eq_rpow, ← Real.rpow_mul hs0.le]
    congr 1
    ring
  have hqs : q * s ^ (-(d : ℝ) / 4) = 1 := by
    rw [hq', ← Real.rpow_add hs0, show (d : ℝ) / 4 + -(d : ℝ) / 4 = 0 by ring, Real.rpow_zero]
  have hq0 : 0 ≤ q := by rw [hq']; positivity
  have hm1 : m * q ≤ A₀ := by
    calc m * q ≤ (A₀ * s ^ (-(d : ℝ) / 4)) * q := mul_le_mul_of_nonneg_right hms hq0
      _ = A₀ * (q * s ^ (-(d : ℝ) / 4)) := by ring
      _ = A₀ := by rw [hqs, mul_one]
  have hs2 : 1 ≤ (2 + s) ^ a := Real.one_le_rpow (by linarith) ha
  have hB : max m A ≤ A₀ * (2 + s) ^ a := by
    refine max_le ?_ hAs
    have h1 : s ^ (-(d : ℝ) / 4) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hs1 (by linarith)
    calc m ≤ A₀ * s ^ (-(d : ℝ) / 4) := hms
      _ ≤ A₀ * 1 := mul_le_mul_of_nonneg_left h1 hA₀.le
      _ ≤ A₀ * (2 + s) ^ a := mul_le_mul_of_nonneg_left hs2 hA₀.le
  have hqL : q ≤ Real.exp (L * ((d : ℝ) / 4)) := by
    rw [hq', ← Real.rpow_def_of_pos (by linarith : (0 : ℝ) < 2 + s)]
    exact Real.rpow_le_rpow hs0.le (by linarith) (by positivity)
  have hBL : (2 + s) ^ a = Real.exp (L * a) :=
    Real.rpow_def_of_pos (by linarith : (0 : ℝ) < 2 + s) a
  -- the splitting index
  set X : ℝ := (2 / c) * ((d : ℝ) / 4 + a) * L with hX
  have hX0 : 0 ≤ X := by positivity
  set N : ℕ := ⌈Real.sqrt X⌉₊ with hN
  have hNX : X ≤ (N : ℝ) ^ 2 := by
    have h1 : Real.sqrt X ≤ N := Nat.le_ceil _
    exact (Real.sqrt_le_iff.mp h1).2
  have hNle : (N : ℝ) ≤ κ * L := by
    have h1 : (N : ℝ) < Real.sqrt X + 1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    have h2 : Real.sqrt X ≤ X + 1 := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by positivity, by nlinarith⟩
    have h3 : 2 ≤ 2 / Real.log 2 * L := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      nlinarith
    calc (N : ℝ) ≤ X + 2 := by linarith
      _ ≤ κ * L := by
        rw [hκ, hX]
        nlinarith
  -- the two bounds for each term
  have hbound : ∀ n : ℕ, annulus d c m A s n ≤
      (if n < N then A₀ * ((n : ℝ) + 1) ^ ((d : ℝ) / 2) else 0) +
        A₀ * (((n : ℝ) + 1) ^ ((d : ℝ) / 2) * Real.exp (-(c / 2) * (n : ℝ) ^ 2)) := by
    intro n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hv0 : 0 ≤ A₀ * (((n : ℝ) + 1) ^ ((d : ℝ) / 2) * Real.exp (-(c / 2) * (n : ℝ) ^ 2)) := by
      positivity
    have hsplit : annulus d c m A s n =
        ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * q * min m (max m A * Real.exp (-c * (n : ℝ) ^ 2)) := by
      unfold annulus
      rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)]
    by_cases hnN : n < N
    · rw [if_pos hnN]
      have : annulus d c m A s n ≤ A₀ * ((n : ℝ) + 1) ^ ((d : ℝ) / 2) := by
        rw [hsplit]
        calc ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * q *
              min m (max m A * Real.exp (-c * (n : ℝ) ^ 2))
            ≤ ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * q * m :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
          _ = ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * (m * q) := by ring
          _ ≤ ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * A₀ :=
              mul_le_mul_of_nonneg_left hm1 (by positivity)
          _ = A₀ * ((n : ℝ) + 1) ^ ((d : ℝ) / 2) := mul_comm _ _
      linarith
    · rw [if_neg hnN, zero_add]
      have hnN' : N ≤ n := not_lt.mp hnN
      have hcn : (d / 4 + a) * L ≤ c / 2 * (n : ℝ) ^ 2 := by
        have h1 : (N : ℝ) ≤ n := by exact_mod_cast hnN'
        have h2 : (N : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg N) h1 2
        have h3 : (2 / c) * ((d : ℝ) / 4 + a) * L ≤ (n : ℝ) ^ 2 := hNX.trans h2
        have h4 : ((d : ℝ) / 4 + a) * L ≤ c / 2 * (n : ℝ) ^ 2 := by
          have := mul_le_mul_of_nonneg_left h3 (show 0 ≤ c / 2 by positivity)
          calc ((d : ℝ) / 4 + a) * L = c / 2 * ((2 / c) * ((d : ℝ) / 4 + a) * L) := by
                field_simp
            _ ≤ _ := this
        exact h4
      have hmin : min m (max m A * Real.exp (-c * (n : ℝ) ^ 2)) ≤
          A₀ * Real.exp (L * a) * Real.exp (-c * (n : ℝ) ^ 2) := by
        refine (min_le_right _ _).trans ?_
        rw [← hBL]
        exact mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le
      rw [hsplit]
      calc ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * q *
            min m (max m A * Real.exp (-c * (n : ℝ) ^ 2))
          ≤ ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * q *
              (A₀ * Real.exp (L * a) * Real.exp (-c * (n : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hmin (by positivity)
        _ ≤ ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * Real.exp (L * ((d : ℝ) / 4)) *
              (A₀ * Real.exp (L * a) * Real.exp (-c * (n : ℝ) ^ 2)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hqL (by positivity)
        _ = A₀ * (((n : ℝ) + 1) ^ ((d : ℝ) / 2) *
              Real.exp (L * ((d : ℝ) / 4 + a) + -c * (n : ℝ) ^ 2)) := by
            rw [Real.exp_add, mul_add, Real.exp_add]
            ring
        _ ≤ A₀ * (((n : ℝ) + 1) ^ ((d : ℝ) / 2) * Real.exp (-(c / 2) * (n : ℝ) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ hA₀.le
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.exp_le_exp.2
            nlinarith
  -- summability of the comparison sequences
  have hu : Summable fun n : ℕ =>
      (if n < N then A₀ * ((n : ℝ) + 1) ^ ((d : ℝ) / 2) else 0) := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    rw [Finset.mem_range] at hn
    rw [if_neg hn]
  have hv : Summable fun n : ℕ =>
      A₀ * (((n : ℝ) + 1) ^ ((d : ℝ) / 2) * Real.exp (-(c / 2) * (n : ℝ) ^ 2)) :=
    hGs.mul_left A₀
  have hsum : Summable (annulus d c m A s) :=
    Summable.of_nonneg_of_le (annulus_nonneg d hm) hbound (hu.add hv)
  refine ⟨hsum, ?_⟩
  have h1 : ∑' n, annulus d c m A s n ≤
      ∑' n : ℕ, ((if n < N then A₀ * ((n : ℝ) + 1) ^ ((d : ℝ) / 2) else 0) +
        A₀ * (((n : ℝ) + 1) ^ ((d : ℝ) / 2) * Real.exp (-(c / 2) * (n : ℝ) ^ 2))) :=
    hsum.tsum_le_tsum hbound (hu.add hv)
  rw [hu.tsum_add hv, tsum_mul_left, ← hG] at h1
  have hu1 : ∑' n : ℕ, (if n < N then A₀ * ((n : ℝ) + 1) ^ ((d : ℝ) / 2) else 0) ≤
      A₀ * (N : ℝ) ^ (d + 1) := by
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
      rw [Finset.mem_range] at hn
      rw [if_neg hn])]
    calc ∑ n ∈ Finset.range N, (if n < N then A₀ * ((n : ℝ) + 1) ^ ((d : ℝ) / 2) else 0)
        ≤ ∑ n ∈ Finset.range N, A₀ * (N : ℝ) ^ d := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
          apply mul_le_mul_of_nonneg_left _ hA₀.le
          have hn1 : (n : ℝ) + 1 ≤ N := by exact_mod_cast Nat.add_one_le_iff.mpr hn
          calc ((n : ℝ) + 1) ^ ((d : ℝ) / 2) ≤ ((n : ℝ) + 1) ^ d := by
                rw [← Real.rpow_natCast]
                apply Real.rpow_le_rpow_of_exponent_le
                  (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
                linarith
            _ ≤ (N : ℝ) ^ d := pow_le_pow_left₀ (by positivity) hn1 d
      _ = A₀ * (N : ℝ) ^ (d + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_succ]
          ring
  have hN1 : (N : ℝ) ^ (d + 1) ≤ κ ^ (d + 1) * L ^ (d + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg N) hNle (d + 1)
  have hLpow : Real.log 2 ^ (d + 1) ≤ L ^ (d + 1) := pow_le_pow_left₀ hl2.le hLl (d + 1)
  have hlp : 0 < Real.log 2 ^ (d + 1) := by positivity
  have hG1 : G ≤ G / Real.log 2 ^ (d + 1) * L ^ (d + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlp]
    exact mul_le_mul_of_nonneg_left hLpow hG0
  calc ∑' n, annulus d c m A s n ≤ A₀ * (N : ℝ) ^ (d + 1) + A₀ * G := by linarith
    _ ≤ A₀ * (κ ^ (d + 1) * L ^ (d + 1)) + A₀ * (G / Real.log 2 ^ (d + 1) * L ^ (d + 1)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hN1 hA₀.le
        · exact mul_le_mul_of_nonneg_left hG1 hA₀.le
    _ = A₀ * (κ ^ (d + 1) + G / Real.log 2 ^ (d + 1)) * L ^ (d + 1) := by ring
    _ ≤ (A₀ * (κ ^ (d + 1) + G / Real.log 2 ^ (d + 1)) + 1) * L ^ (d + 1) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Tail

end EinsteinFull.S3LocalAv
