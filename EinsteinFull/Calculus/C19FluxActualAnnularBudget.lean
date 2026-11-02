import EinsteinFull.Calculus.C1FluxGeneralTestAssembly
import EinsteinFull.Calculus.K7AnnularConstants

noncomputable section
open scoped BigOperators
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The annular residual is absorbed into the actual Gaussian-envelope rate. -/
theorem c19_actual_schwartz_annular_residual_absorbed
    (d : ℕ) {η κ Cloc : ℝ} (hη : 0 < η) (hκ : κ < 1) (hCloc : 1 ≤ Cloc) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ (t : ℝ), T ≤ t → ∀ ζ : ℂ,
      ‖ζ‖ * Real.sqrt t ≤ t ^ (η / 4) → ∀ (s : ℝ), 0 < s →
    ∀ (k Lb : ℕ) (K growth ctest : ℝ), 1 ≤ K → 0 ≤ growth → 0 < ctest →
    ∀ z : Vec d,
    let r := t ^ (1 / 2 + η)
    let R := 2 * Real.sqrt (d : ℝ) + 2
    let E := sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
        {y : Vec d | euclideanNorm (y-z) ≤ R*r})
    let A := ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
      Real.exp (-4 ^ n * ((1 / Cloc) / 2))
    ((2 + t) ^ Cloc * Real.exp (Cloc * ‖ζ‖ ^ 2 * t) * r ^ d *
      s ^ (-(k : ℝ) / 2) * E) *
      (∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
        Real.exp (-4 ^ n * (t ^ (2 * η) / Cloc))) ≤
    A * (K * Real.exp (growth * ‖ζ‖ ^ 2 * t / 2) *
      t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ) *
      s ^ (-(k : ℝ) / 2) * E * (1 + t / s) ^ Lb) := by
  obtain ⟨T, hT1, hT⟩ := EinsteinFull.Calculus.K7.annular_constant_domination d hη hκ hCloc
  refine ⟨T, hT1, fun t ht ζ hζ s hs k Lb K growth ctest hK hg hc z => ?_⟩
  intro r R E A
  have ht1 : 1 ≤ t := hT1.trans ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hC0 : 0 < Cloc := lt_of_lt_of_le zero_lt_one hCloc
  have hτ : 1 / Cloc ≤ t ^ (2 * η) / Cloc :=
    div_le_div_of_nonneg_right (Real.one_le_rpow ht1 (by positivity)) hC0.le
  have htail := EinsteinFull.Calculus.K7.annular_series_shift d (one_div_pos.mpr hC0) hτ
  have hdom := hT t ht ‖ζ‖ (norm_nonneg ζ) hζ s hs k Lb K growth hK hg
  have hA : 0 ≤ A := tsum_nonneg fun _ =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_nonneg _)
  have hR : 0 ≤ R * r := by dsimp [R, r]; positivity
  have hE : 0 ≤ E := (c1_gaussian_ball_sup s ctest (R * r) hs hc hR z).1
  let L := (2 + t) ^ Cloc * Real.exp (Cloc * ‖ζ‖ ^ 2 * t) * r ^ d * s ^ (-(k : ℝ) / 2)
  let F := K * Real.exp (growth * ‖ζ‖ ^ 2 * t / 2) *
    t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ) *
    s ^ (-(k : ℝ) / 2) * (1 + t / s) ^ Lb
  have hL : 0 ≤ L := by dsimp [L, r]; positivity
  have hLsum : L * (∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
      Real.exp (-4 ^ n * (t ^ (2 * η) / Cloc))) ≤ A * F := by
    calc _ ≤ L * (Real.exp (-(t ^ (2 * η) / Cloc) / 2) * A) :=
        mul_le_mul_of_nonneg_left htail hL
      _ = (L * Real.exp (-(t ^ (2 * η) / Cloc) / 2)) * A := by ring
      _ ≤ F * A := mul_le_mul_of_nonneg_right hdom hA
      _ = A * F := by ring
  have h := mul_le_mul_of_nonneg_right hLsum hE
  dsimp only [L, F] at h
  convert h using 1 <;> ring
