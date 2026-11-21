import EinsteinRelation.External.AKMEnergyDensity
import EinsteinRelation.TimeChange.EuclideanTransport
import EinsteinRelation.Correctors.HeatKernelConvolution
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Gaussian-weighted energies from energies on balls

If a nonnegative function `f` satisfies `∫_{B_R} f ≤ M R^d` for every `R ≥ R₀`, then its average
against the heat kernel of variance `2s` centered at a point `x` with `|x| ≤ √s` is at most
`C_d M` as soon as `s ≥ R₀²`. The proof decomposes space into the shells
`(k+2)√s ≤ |y| < (k+3)√s`, on which the kernel is at most `(4πs)^(-d/2) e^(-(k+1)²/4)`. This is
the form in which the energy bounds of a corrector above its minimal scale enter the heat
formula (6.7) of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.External.AKM EinsteinRelation.Correctors

variable {d : ℕ}

/-- The shell sum of the Gaussian-weighted energy bound. -/
noncomputable def gaussianShellSum (d : ℕ) : ℝ :=
  ∑' k : ℕ, Real.exp (-((k : ℝ) + 1) ^ 2 / 4) * ((k : ℝ) + 3) ^ d

theorem summable_gaussianShell (d : ℕ) :
    Summable fun k : ℕ => Real.exp (-((k : ℝ) + 1) ^ 2 / 4) * ((k : ℝ) + 3) ^ d := by
  have hs : Summable fun n : ℕ => (n : ℝ) ^ d * Real.exp (-(1 / 4) * n) :=
    Real.summable_pow_mul_exp_neg_nat_mul d (by norm_num)
  have hs3 : Summable fun k : ℕ =>
      ((k + 3 : ℕ) : ℝ) ^ d * Real.exp (-(1 / 4) * ((k + 3 : ℕ) : ℝ)) :=
    (summable_nat_add_iff 3).mpr hs
  refine (hs3.mul_left (Real.exp (1 / 2))).of_nonneg_of_le (fun k => by positivity) fun k => ?_
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : Real.exp (-((k : ℝ) + 1) ^ 2 / 4) ≤
      Real.exp (1 / 2) * Real.exp (-(1 / 4) * ((k : ℝ) + 3)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc Real.exp (-((k : ℝ) + 1) ^ 2 / 4) * ((k : ℝ) + 3) ^ d
      ≤ Real.exp (1 / 2) * Real.exp (-(1 / 4) * ((k : ℝ) + 3)) * ((k : ℝ) + 3) ^ d := by
        gcongr
    _ = Real.exp (1 / 2) * (((k : ℝ) + 3) ^ d * Real.exp (-(1 / 4) * ((k : ℝ) + 3))) := by
        ring

theorem gaussianShellSum_nonneg (d : ℕ) : 0 ≤ gaussianShellSum d :=
  tsum_nonneg fun k => by positivity

theorem continuous_euclideanNorm : Continuous (euclideanNorm (d := d)) := by
  unfold euclideanNorm euclideanSq dot
  fun_prop

theorem measurableSet_ball_zero (R : ℝ) : MeasurableSet (ball (0 : Vec d) R) :=
  (isOpen_lt (continuous_euclideanNorm.comp (continuous_id.sub continuous_const))
    continuous_const).measurableSet

theorem euclideanSq_eq_euclideanNorm_sq (v : Vec d) : euclideanSq v = euclideanNorm v ^ 2 := by
  have h : 0 ≤ euclideanSq v := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun l _ => mul_self_nonneg (v l)
  rw [euclideanNorm, Real.sq_sqrt h]

/-- The pointwise shell bound for the heat kernel. -/
theorem ofReal_exp_le_shells {s : ℝ} (hs0 : 0 < s) {x y : Vec d}
    (hx : euclideanNorm x ≤ Real.sqrt s) :
    ENNReal.ofReal (Real.exp (-euclideanSq (y - x) / (4 * s))) ≤
      (ball (0 : Vec d) (2 * Real.sqrt s)).indicator 1 y +
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (-((k : ℝ) + 1) ^ 2 / 4)) *
          (ball (0 : Vec d) (((k : ℝ) + 3) * Real.sqrt s)).indicator 1 y := by
  set ρ := Real.sqrt s with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr hs0
  have hρs : ρ ^ 2 = s := Real.sq_sqrt hs0.le
  set n := ⌊euclideanNorm y / ρ⌋₊ with hn
  have hy0 : 0 ≤ euclideanNorm y / ρ := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hlt : euclideanNorm y / ρ < n + 1 := Nat.lt_floor_add_one _
  have hle : (n : ℝ) ≤ euclideanNorm y / ρ := Nat.floor_le hy0
  by_cases h1 : n ≤ 1
  · have hy : y ∈ ball (0 : Vec d) (2 * ρ) := by
      show euclideanNorm (y - 0) < 2 * ρ
      rw [sub_zero]
      have hn1 : (n : ℝ) ≤ 1 := by exact_mod_cast h1
      have h2 : euclideanNorm y / ρ < 2 := by linarith
      rwa [div_lt_iff₀ hρ0] at h2
    have hsq : 0 ≤ euclideanSq (y - x) := by
      rw [euclideanSq_eq_euclideanNorm_sq]
      positivity
    calc ENNReal.ofReal (Real.exp (-euclideanSq (y - x) / (4 * s))) ≤ 1 := by
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr ?_)
          exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      _ = (ball (0 : Vec d) (2 * ρ)).indicator 1 y := by
          rw [Set.indicator_of_mem hy]
          rfl
      _ ≤ _ := le_self_add
  · push Not at h1
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
    rw [hk] at hle hlt
    push_cast at hle hlt
    have hyk : ((k : ℝ) + 2) * ρ ≤ euclideanNorm y := by rwa [le_div_iff₀ hρ0] at hle
    have hyk' : euclideanNorm y < ((k : ℝ) + 3) * ρ := by
      rw [div_lt_iff₀ hρ0] at hlt
      linarith
    have hy : y ∈ ball (0 : Vec d) (((k : ℝ) + 3) * ρ) := by
      show euclideanNorm (y - 0) < ((k : ℝ) + 3) * ρ
      rwa [sub_zero]
    have htri : euclideanNorm y ≤ euclideanNorm (y - x) + euclideanNorm x := by
      have h := TimeChange.euclideanNorm_add_le (y - x) x
      rwa [sub_add_cancel] at h
    have hyx : ((k : ℝ) + 1) * ρ ≤ euclideanNorm (y - x) := by linarith
    have hsq : ((k : ℝ) + 1) ^ 2 * s ≤ euclideanSq (y - x) := by
      rw [euclideanSq_eq_euclideanNorm_sq, ← hρs]
      have h0 : 0 ≤ ((k : ℝ) + 1) * ρ := by positivity
      nlinarith
    have hexp : Real.exp (-euclideanSq (y - x) / (4 * s)) ≤
        Real.exp (-((k : ℝ) + 1) ^ 2 / 4) := by
      refine Real.exp_le_exp.mpr ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc ENNReal.ofReal (Real.exp (-euclideanSq (y - x) / (4 * s)))
        ≤ ENNReal.ofReal (Real.exp (-((k : ℝ) + 1) ^ 2 / 4)) *
            (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator 1 y := by
          rw [Set.indicator_of_mem hy, Pi.one_apply, mul_one]
          exact ENNReal.ofReal_le_ofReal hexp
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-((k : ℝ) + 1) ^ 2 / 4)) *
            (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator 1 y :=
          ENNReal.le_tsum (f := fun k : ℕ => ENNReal.ofReal (Real.exp (-((k : ℝ) + 1) ^ 2 / 4)) *
            (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator 1 y) k
      _ ≤ _ := le_add_self

theorem one_le_natCast_add_three (k : ℕ) : (1 : ℝ) ≤ k + 3 := by
  have := Nat.cast_nonneg (α := ℝ) k
  linarith

theorem rpow_mul_sqrt_pow {s : ℝ} (hs0 : 0 < s) :
    (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.sqrt s ^ d = (4 * Real.pi) ^ (-(d : ℝ) / 2) := by
  rw [Real.mul_rpow (by positivity) hs0.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hs0.le, mul_assoc, ← Real.rpow_add hs0,
    show -(d : ℝ) / 2 + 1 / 2 * d = 0 by ring, Real.rpow_zero, mul_one]

/-- **Gaussian-weighted energy.** If `∫_{B_R} f ≤ M R^d` for every `R ≥ R₀`, then for
`s ≥ R₀²` and `|x| ≤ √s`, `∫ f(y) Φ_s(y - x) dy ≤ (4π)^(-d/2) (2^d + Σ_k e^(-(k+1)²/4)(k+3)^d) M`. -/
theorem lintegral_mul_heatKernel_le {f : Vec d → ℝ≥0∞} (hf : Measurable f) {M R₀ : ℝ}
    (hM : 0 ≤ M) (hR₀ : 0 < R₀)
    (hball : ∀ R : ℝ, R₀ ≤ R → ∫⁻ y in ball 0 R, f y ≤ ENNReal.ofReal (M * R ^ d))
    {s : ℝ} (hs : R₀ ^ 2 ≤ s) {x : Vec d} (hx : euclideanNorm x ≤ Real.sqrt s) :
    ∫⁻ y, f y * ENNReal.ofReal (euclideanHeatKernel s (y - x)) ≤
      ENNReal.ofReal ((4 * Real.pi) ^ (-(d : ℝ) / 2) * (2 ^ d + gaussianShellSum d) * M) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  set ρ := Real.sqrt s with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr hs0
  have hρR : R₀ ≤ ρ := Real.le_sqrt_of_sq_le hs
  set c := (4 * Real.pi * s) ^ (-(d : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  set e : ℕ → ℝ := fun k => Real.exp (-((k : ℝ) + 1) ^ 2 / 4) with he
  have hdom : ∀ y, f y * ENNReal.ofReal (euclideanHeatKernel s (y - x)) ≤
      ENNReal.ofReal c * ((ball (0 : Vec d) (2 * ρ)).indicator f y +
        ∑' k : ℕ, ENNReal.ofReal (e k) * (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator f y) := by
    intro y
    have hK : euclideanHeatKernel s (y - x) = c * Real.exp (-euclideanSq (y - x) / (4 * s)) :=
      rfl
    have hsh := ofReal_exp_le_shells (d := d) hs0 (y := y) hx
    rw [hK, ENNReal.ofReal_mul hc0]
    have hind : ∀ (A : Set (Vec d)), f y * A.indicator 1 y = A.indicator f y := by
      intro A
      by_cases hyA : y ∈ A
      · rw [Set.indicator_of_mem hyA, Set.indicator_of_mem hyA, Pi.one_apply, mul_one]
      · rw [Set.indicator_of_notMem hyA, Set.indicator_of_notMem hyA, mul_zero]
    calc f y * (ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-euclideanSq (y - x) / (4 * s))))
        = ENNReal.ofReal c * (f y * ENNReal.ofReal (Real.exp (-euclideanSq (y - x) / (4 * s)))) :=
          by ring
      _ ≤ ENNReal.ofReal c * (f y * ((ball (0 : Vec d) (2 * ρ)).indicator 1 y +
          ∑' k : ℕ, ENNReal.ofReal (e k) *
            (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator 1 y)) := by
          gcongr
      _ = _ := by
          rw [mul_add, hind, ← ENNReal.tsum_mul_left]
          congr 2
          refine tsum_congr fun k => ?_
          rw [← hind]
          ring
  have hmeasI : ∀ R : ℝ, Measurable ((ball (0 : Vec d) R).indicator f) :=
    fun R => hf.indicator (measurableSet_ball_zero R)
  have hball' : ∀ R : ℝ, R₀ ≤ R →
      ∫⁻ y, (ball (0 : Vec d) R).indicator f y ≤ ENNReal.ofReal (M * R ^ d) := by
    intro R hR
    rw [lintegral_indicator (measurableSet_ball_zero R)]
    exact hball R hR
  have hsum : Summable fun k => e k * ((k : ℝ) + 3) ^ d := summable_gaussianShell d
  calc ∫⁻ y, f y * ENNReal.ofReal (euclideanHeatKernel s (y - x))
      ≤ ∫⁻ y, ENNReal.ofReal c * ((ball (0 : Vec d) (2 * ρ)).indicator f y +
          ∑' k : ℕ, ENNReal.ofReal (e k) *
            (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator f y) := lintegral_mono hdom
    _ = ENNReal.ofReal c * ((∫⁻ y, (ball (0 : Vec d) (2 * ρ)).indicator f y) +
          ∑' k : ℕ, ENNReal.ofReal (e k) *
            ∫⁻ y, (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator f y) := by
        have htsum : ∫⁻ y, ∑' k : ℕ, ENNReal.ofReal (e k) *
              (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator f y =
            ∑' k : ℕ, ENNReal.ofReal (e k) *
              ∫⁻ y, (ball (0 : Vec d) (((k : ℝ) + 3) * ρ)).indicator f y := by
          rw [lintegral_tsum fun k => ((hmeasI _).const_mul _).aemeasurable]
          exact tsum_congr fun k => lintegral_const_mul _ (hmeasI _)
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (hmeasI _), htsum]
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal (M * (2 * ρ) ^ d) +
          ∑' k : ℕ, ENNReal.ofReal (e k) * ENNReal.ofReal (M * (((k : ℝ) + 3) * ρ) ^ d)) := by
        gcongr with k
        all_goals first
          | exact hball' _ (by linarith)
          | exact hball' _ (le_trans hρR (le_mul_of_one_le_left hρ0.le (one_le_natCast_add_three _)))
    _ = ENNReal.ofReal ((4 * Real.pi) ^ (-(d : ℝ) / 2) * (2 ^ d + gaussianShellSum d) * M) := by
        have he0 : ∀ k, 0 ≤ e k := fun k => (Real.exp_pos _).le
        have hterm : ∀ k : ℕ, ENNReal.ofReal (e k) * ENNReal.ofReal (M * (((k : ℝ) + 3) * ρ) ^ d) =
            ENNReal.ofReal (M * ρ ^ d * (e k * ((k : ℝ) + 3) ^ d)) := by
          intro k
          rw [← ENNReal.ofReal_mul (he0 k)]
          congr 1
          rw [mul_pow]
          ring
        have h1 : ∑' k : ℕ, ENNReal.ofReal (e k) * ENNReal.ofReal (M * (((k : ℝ) + 3) * ρ) ^ d) =
            ENNReal.ofReal (M * ρ ^ d * gaussianShellSum d) := by
          simp_rw [hterm]
          rw [← ENNReal.ofReal_tsum_of_nonneg
            (fun k => mul_nonneg (by positivity) (mul_nonneg (he0 k) (by positivity)))
            (hsum.mul_left _), tsum_mul_left]
          rfl
        rw [h1, ← ENNReal.ofReal_add (by positivity)
            (mul_nonneg (by positivity) (gaussianShellSum_nonneg d)),
          ← ENNReal.ofReal_mul hc0]
        congr 1
        have h := rpow_mul_sqrt_pow (d := d) hs0
        rw [← hρ, ← hc] at h
        calc c * (M * (2 * ρ) ^ d + M * ρ ^ d * gaussianShellSum d)
            = (c * ρ ^ d) * (2 ^ d + gaussianShellSum d) * M := by rw [mul_pow]; ring
          _ = _ := by rw [h]

end EinsteinFull.Homogenization
