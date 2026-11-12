import EinsteinRelation.Correctors.CoordinateFieldMomentBounds

/-! # Moments under bounded coefficient multiplication

Source: `paper/main.tex:1056–1075`. Bounds for actual matrix coefficients
reduce the flux-error estimate to coordinate moments.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- A bounded random multiplier preserves an explicit moment bound
(`paper/main.tex:1056–1075`). -/
theorem eLpNorm_bounded_mul_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : ℝ≥0∞} {L B : ℝ} (hL : 0 ≤ L)
    {a X : Ω → ℝ} (ha : ∀ᵐ ω ∂μ, |a ω| ≤ L)
    (hX : eLpNorm X p μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => a ω * X ω) p μ ≤ ENNReal.ofReal (L * B) := by
  have hmul : eLpNorm (fun ω => a ω * X ω) p μ ≤ ENNReal.ofReal L * eLpNorm X p μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    filter_upwards [ha] with ω hω
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)
  exact hmul.trans ((mul_le_mul_right hX _).trans_eq (ENNReal.ofReal_mul hL).symm)

/-- Each coordinate of a matrix product has the corresponding finite sum
moment bound (`paper/main.tex:1056–1075`). -/
theorem eLpNorm_matrix_mulVec_le_of_coordinate_bounds
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    {a : Ω → Mat d} {X : Ω → Vec d} (ha : Measurable a) (hX : Measurable X)
    (hab : ∀ᵐ ω ∂μ, ∀ i j, |a ω i j| ≤ L)
    (hXb : ∀ i, eLpNorm (fun ω => X ω i) p μ ≤ ENNReal.ofReal B) (i : Fin d) :
    eLpNorm (fun ω => (a ω).mulVec (X ω) i) p μ ≤ ENNReal.ofReal ((d : ℝ) * (L * B)) := by
  have hsum := eLpNorm_finset_sum_le_of_bound Finset.univ
    (fun j ω => a ω i j * X ω j)
    (fun j _ => ((((continuous_id : Continuous (fun M : Mat d => M)).matrix_elem i j).measurable.comp ha).mul
      ((measurable_pi_apply j).comp hX)).aestronglyMeasurable) hp
    (fun _ => L * B) (fun _ _ => mul_nonneg hL hB)
    (fun j _ => eLpNorm_bounded_mul_le hL (hab.mono fun _ hω => hω i j) (hXb j))
  simpa only [Matrix.mulVec, dotProduct, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using hsum

end EinsteinRelation.Correctors
