import EinsteinRelation.Correctors.ShortTimeWindowLp
import EinsteinRelation.Correctors.CutoffNearestMesh

/-! Source: `paper/main.tex:722,756`. Both errors between rescaled
cutoffs and the literal source mesh have summable squared moment bounds. -/
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- The integer endpoint rounding window has an `O(1/n)` moment bound.
The time integral is the genuine Bochner integral on the indicated set. -/
theorem eLpNorm_integer_rounding_window_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {g : Ω × ℝ → ℝ} (hg : Measurable g)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ t : ℝ, 0 < t →
      eLpNorm (fun ω => g (ω, t)) p μ ≤ ENNReal.ofReal (C / t)) (n : ℕ) :
    let s : ℝ := c * ((n : ℝ) + 1)
    let t : ℝ := ((⌊s⌋₊ + 1 : ℕ) : ℝ)
    eLpNorm (fun ω => ∫ u in Set.Icc s t, g (ω, u)) p μ ≤
      ENNReal.ofReal ((C / c) / ((n : ℝ) + 1)) := by
  dsimp only
  have hn : 0 < (n : ℝ) + 1 := by positivity
  let s : ℝ := c * ((n : ℝ) + 1)
  have hs : 0 < s := mul_pos hc hn
  obtain ⟨_, hst, hratio⟩ := (cutoff_nearest_mesh_ratios hs).1
  apply (eLpNorm_short_time_window_le hp hpt hg hs hst hC
    (fun t ht => hbound t (hs.trans_le ht.1))).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    C * (((⌊s⌋₊ + 1 : ℕ) : ℝ) - s) / s
        = C * ((((⌊s⌋₊ + 1 : ℕ) : ℝ) - s) / s) := by ring
    _ ≤ C * (1 / s) := mul_le_mul_of_nonneg_left hratio hC.le
    _ = (C / c) / ((n : ℝ) + 1) := by dsimp [s]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- The reciprocal endpoint rounding window also has an `O(1/n)`
moment bound, without replacing the literal rescaled cutoff. -/
theorem eLpNorm_reciprocal_rounding_window_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {g : Ω × ℝ → ℝ} (hg : Measurable g)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ t : ℝ, 0 < t →
      eLpNorm (fun ω => g (ω, t)) p μ ≤ ENNReal.ofReal (C / t)) (n : ℕ) :
    let s : ℝ := c / ((n : ℝ) + 1)
    let t : ℝ := (((⌊s⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹
    eLpNorm (fun ω => ∫ u in Set.Icc t s, g (ω, u)) p μ ≤
      ENNReal.ofReal ((C * c) / ((n : ℝ) + 1)) := by
  dsimp only
  have hn : 0 < (n : ℝ) + 1 := by positivity
  let s : ℝ := c / ((n : ℝ) + 1)
  have hs : 0 < s := div_pos hc hn
  obtain ⟨ht, hts, hratio⟩ := (cutoff_nearest_mesh_ratios hs).2
  apply (eLpNorm_short_time_window_le hp hpt hg ht hts hC
    (fun t ht' => hbound t (ht.trans_le ht'.1))).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    C * (s - (((⌊s⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹) /
        (((⌊s⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹ =
        C * ((s - (((⌊s⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹) /
          (((⌊s⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹) := by ring
    _ ≤ C * s := mul_le_mul_of_nonneg_left hratio hC.le
    _ = (C * c) / ((n : ℝ) + 1) := by dsimp [s]; ring

end EinsteinRelation.Correctors
