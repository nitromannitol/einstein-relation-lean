import EinsteinRelation.Correctors.AKMStretchedExponentialMoments
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Quantitative polynomial tails of the actual AKM random radius

Source: `paper/main.tex:798–806,860–869`. The stretched-exponential
radius bound supplies all finite moments and polynomial rare-event bounds.
No tail assumption on the radius is added.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM

/-- Positive powers preserve the stretched-exponential bound with the
corresponding exponent and scale. Source: `paper/main.tex:798–806,860–869`. -/
theorem stretchedExponential_rpow {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω)
    {s θ a : ℝ} (hθ : 0 < θ) (ha : 0 < a)
    (hbound : StretchedExponentialBound P s θ X) :
    StretchedExponentialBound P (s/a) (θ^a) (fun ω => (X ω)^a) := by
  unfold StretchedExponentialBound at *
  refine (le_of_eq (lintegral_congr ?_)).trans hbound
  intro ω
  rw [max_eq_left (Real.rpow_nonneg (hX ω) a), max_eq_left (hX ω),
    ← Real.div_rpow (hX ω) hθ.le,
    ← Real.rpow_mul (div_nonneg (hX ω) hθ.le)]
  congr 3
  field_simp

/-- All positive powers of the actual random radius have every finite
moment. This supplies the random factor in the good-event gradient estimate.
Source: `paper/main.tex:798–806,860–869`. -/
theorem radius_rpow_moments_of_stretchedExponential
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Ω → ℝ} (hXm : Measurable X) (hX : ∀ ω, 0 ≤ X ω)
    {s θ a m : ℝ} (hs : 0 < s) (hθ : 0 < θ) (ha : 0 < a) (hm : 0 < m)
    (hbound : StretchedExponentialBound P s θ X) :
    MemLp (fun ω => (X ω)^a) (ENNReal.ofReal m) P ∧
      eLpNorm (fun ω => (X ω)^a) (ENNReal.ofReal m) P ≤
        ENNReal.ofReal ((2 * (m/(s/a))^(m/(s/a)))^(1/m) * θ^a) := by
  have hpower := stretchedExponential_rpow P hX hθ ha hbound
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ (X ω)^a :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hX ω) a
  exact ⟨memLp_of_stretchedExponential P (div_pos hs ha) (Real.rpow_pos_of_pos hθ a)
      hm (hXm.pow_const a).aestronglyMeasurable hnonneg hpower,
    eLpNorm_le_of_stretchedExponential P (div_pos hs ha) (Real.rpow_pos_of_pos hθ a)
      hm hnonneg hpower⟩

/-- Markov's inequality turns the cited stretched-exponential radius bound
into every polynomial upper tail, with an explicit constant independent of
the law and radius. Source: `paper/main.tex:798–806,860–869`. -/
theorem measure_radius_gt_le_of_stretchedExponential
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Ω → ℝ} (hXm : Measurable X) (hX : ∀ ω, 0 ≤ X ω)
    {s θ q : ℝ} (hs : 0 < s) (hθ : 0 < θ) (hq : 0 < q)
    (hbound : StretchedExponentialBound P s θ X) {R : ℝ} (hR : 0 < R) :
    P {ω | R < X ω} ≤
      ENNReal.ofReal ((2 * (q/s)^(q/s) * θ^q) * R^(-q)) := by
  have hmoment := lintegral_rpow_le_of_stretchedExponential P hs hθ hq
    (Filter.Eventually.of_forall hX) hbound
  have hRp : 0 < R^q := Real.rpow_pos_of_pos hR q
  have hm : Measurable (fun ω => ENNReal.ofReal ((X ω)^q)) :=
    (hXm.pow_const q).ennreal_ofReal
  calc
    P {ω | R < X ω} ≤ P {ω | ENNReal.ofReal (R^q) ≤ ENNReal.ofReal ((X ω)^q)} := by
      apply measure_mono
      intro ω hω
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hR.le hω.le hq.le)
    _ ≤ (∫⁻ ω, ENNReal.ofReal ((X ω)^q) ∂P) / ENNReal.ofReal (R^q) :=
      meas_ge_le_lintegral_div hm.aemeasurable (ne_of_gt (ENNReal.ofReal_pos.mpr hRp))
        ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * (q/s)^(q/s) * θ^q) / ENNReal.ofReal (R^q) := by
      gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos hRp, div_eq_mul_inv, ← Real.rpow_neg hR.le]

end EinsteinRelation.Correctors
