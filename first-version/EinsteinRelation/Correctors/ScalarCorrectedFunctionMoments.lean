import EinsteinRelation.Correctors.CoordinateFieldMomentBounds
import EinsteinRelation.Correctors.ScalarCorrectedFunction

/-! # Moments of the scalar corrected band and its gradient

Source: `paper/main.tex:1070–1082`. Hölder at orders `4p` and `2p`
controls the literal corrected fields at a single scale.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- The corrected function has moment of scale `r+a`
(`paper/main.tex:1070–1076`). -/
theorem scalarCorrected_function_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} {p r a A B : ℝ} (hp : 1 ≤ p) (hr : 1 ≤ r) (ha : 0 ≤ a)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (u : Ω → ℝ) (Du : Ω → Vec d) (phi : Fin d → Ω → ℝ)
    (hu : Measurable u) (hDu : Measurable Du)
    (hphi : ∀ j, Measurable (phi j))
    (hub : eLpNorm u (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (B * r))
    (hDub : ∀ i, eLpNorm (fun ω => Du ω i) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal B)
    (hphib : ∀ j, eLpNorm (phi j) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (A * a)) :
    eLpNorm (fun ω => u ω + ∑ j, phi j ω * Du ω j) (ENNReal.ofReal (2 * p)) μ ≤
      ENNReal.ofReal ((B + 4 * (d : ℝ) * A * B) * (r + a)) := by
  have hr0 : 0 < r := by linarith
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p) := ENNReal.one_le_ofReal.mpr (by linarith)
  have hqq : ENNReal.ofReal (2 * p) ≤ ENNReal.ofReal (4 * p) := ENNReal.ofReal_le_ofReal (by linarith)
  have hDum (i : Fin d) : Measurable (fun ω => Du ω i) := (measurable_pi_apply i).comp hDu
  have hsum := eLpNorm_sum_mul_le_of_bounds hp (mul_nonneg hA ha) hB Finset.univ
    (fun j _ => hphi j) (fun j _ => hDum j) (fun j _ => hphib j) (fun j _ => hDub j)
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  calc
    _ ≤ eLpNorm u (ENNReal.ofReal (2 * p)) μ +
        eLpNorm (fun ω => ∑ j, phi j ω * Du ω j) (ENNReal.ofReal (2 * p)) μ :=
      eLpNorm_add_le (f := u) (g := fun ω => ∑ j, phi j ω * Du ω j) hu.aestronglyMeasurable
        (Finset.measurable_sum _ fun j _ => (hphi j).mul (hDum j)).aestronglyMeasurable hq
    _ ≤ ENNReal.ofReal (B * r) + ENNReal.ofReal ((d : ℝ) * (A * a * B)) :=
      add_le_add ((eLpNorm_le_eLpNorm_of_exponent_le hqq hu.aestronglyMeasurable).trans hub) hsum
    _ = ENNReal.ofReal (B * r + (d : ℝ) * (A * a * B)) :=
      (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hdb : 0 ≤ (d : ℝ) * A * B := by positivity
      nlinarith [mul_nonneg hdb (show 0 ≤ r by linarith), mul_nonneg hdb ha])

/-- The two correction terms in a gradient coordinate have bounded moment
(`paper/main.tex:1077–1082`). -/
theorem scalarCorrected_gradient_sums_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} {p r a A B : ℝ} (hp : 1 ≤ p) (hr : 1 ≤ r) (ha : 0 ≤ a)
    (har : a ≤ 3 * r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (X Y Z W : Fin d → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (hY : ∀ j, Measurable (Y j))
    (hZ : ∀ j, Measurable (Z j)) (hW : ∀ j, Measurable (W j))
    (hXb : ∀ j, eLpNorm (X j) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal B)
    (hYb : ∀ j, eLpNorm (Y j) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal A)
    (hZb : ∀ j, eLpNorm (Z j) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (A * a))
    (hWb : ∀ j, eLpNorm (W j) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (B / r)) :
    eLpNorm (fun ω => (∑ j, X j ω * Y j ω) + ∑ j, Z j ω * W j ω)
      (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal (4 * (d : ℝ) * A * B) := by
  have hr0 : 0 < r := by linarith
  have hs₁ := eLpNorm_sum_mul_le_of_bounds hp hB hA Finset.univ
    (fun j _ => hX j) (fun j _ => hY j) (fun j _ => hXb j) (fun j _ => hYb j)
  have hs₂ := eLpNorm_sum_mul_le_of_bounds hp (mul_nonneg hA ha) (div_nonneg hB hr0.le) Finset.univ
    (fun j _ => hZ j) (fun j _ => hW j) (fun j _ => hZb j) (fun j _ => hWb j)
  simp only [Finset.card_univ, Fintype.card_fin] at hs₁ hs₂
  have hm₁ : Measurable (fun ω => ∑ j, X j ω * Y j ω) :=
    Finset.measurable_sum _ fun j _ => (hX j).mul (hY j)
  have hm₂ : Measurable (fun ω => ∑ j, Z j ω * W j ω) :=
    Finset.measurable_sum _ fun j _ => (hZ j).mul (hW j)
  calc
    _ ≤ eLpNorm (fun ω => ∑ j, X j ω * Y j ω) (ENNReal.ofReal (2 * p)) μ +
          eLpNorm (fun ω => ∑ j, Z j ω * W j ω) (ENNReal.ofReal (2 * p)) μ :=
      eLpNorm_add_le hm₁.aestronglyMeasurable hm₂.aestronglyMeasurable
        (ENNReal.one_le_ofReal.mpr (by linarith))
    _ ≤ ENNReal.ofReal ((d : ℝ) * (B * A)) +
        ENNReal.ofReal ((d : ℝ) * (A * a * (B / r))) := add_le_add hs₁ hs₂
    _ = ENNReal.ofReal ((d : ℝ) * (B * A) + (d : ℝ) * (A * a * (B / r))) :=
      (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hdAB : 0 ≤ (d : ℝ) * A * B := by positivity
      have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ hr0).mpr har) hdAB
      have hh' : (d : ℝ) * (A * a * (B / r)) ≤ 3 * (d : ℝ) * A * B := by
        convert hh using 1 <;> ring
      nlinarith only [hh'])

end EinsteinRelation.Correctors
