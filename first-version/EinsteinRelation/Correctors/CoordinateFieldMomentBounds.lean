import EinsteinRelation.Correctors.ScalarGlobalMomentBounds
import EinsteinRelation.Correctors.EuclideanCoordinateMomentBound

/-! # Euclidean field bounds from coordinate moments

Source: `paper/main.tex:1037–1041,1070–1082`. Coordinate moment estimates
control the actual Euclidean norm without changing the norm on `Vec`.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- Uniform coordinate moments control the manuscript's Euclidean norm
(`paper/main.tex:1037–1041,1070–1082`). -/
theorem eLpNorm_euclideanNorm_le_of_coordinate_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} {p C : ℝ} (hp : 2 ≤ p) (hC : 0 ≤ C)
    {V : Ω → Vec d} (hV : Measurable V)
    (hb : ∀ i, eLpNorm (fun ω => V ω i) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C) :
    eLpNorm (fun ω => euclideanNorm (V ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (Real.sqrt d * C) := by
  let W : Ω → EuclideanSpace ℝ (Fin d) := fun ω => WithLp.toLp 2 (V ω)
  have hW : Measurable W := (WithLp.measurable_toLp 2 (Vec d)).comp hV
  have h := (eLpNorm_euclidean_le_sqrt_card μ p C hp hC W hW hb).2
  rw [← eLpNorm_norm] at h
  simpa only [W, Fintype.card_fin, ← TimeChange.euclideanNorm_eq_norm_toLp] using h

/-- Hölder with explicit real bounds on the two factors
(`paper/main.tex:1070–1075`). -/
theorem eLpNorm_mul_le_of_bounds {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p A B : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXb : eLpNorm X (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal A)
    (hYb : eLpNorm Y (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => X ω * Y ω) (ENNReal.ofReal (2 * p)) μ ≤
      ENNReal.ofReal (A * B) := by
  exact (eLpNorm_mul_le_holder_four hp hX.aestronglyMeasurable hY.aestronglyMeasurable).trans
    ((mul_le_mul' hXb hYb).trans_eq (ENNReal.ofReal_mul hA).symm)

/-- A finite sum of products obeys the corresponding real bound
(`paper/main.tex:1070–1075`). -/
theorem eLpNorm_sum_mul_le_of_bounds {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p A B : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (s : Finset ι) {X Y : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hXb : ∀ i ∈ s, eLpNorm (X i) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal A)
    (hYb : ∀ i ∈ s, eLpNorm (Y i) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => ∑ i ∈ s, X i ω * Y i ω) (ENNReal.ofReal (2 * p)) μ ≤
      ENNReal.ofReal ((s.card : ℝ) * (A * B)) := by
  have hsum := eLpNorm_finset_sum_le_of_bound s (fun i ω => X i ω * Y i ω)
    (fun i hi => ((hX i hi).mul (hY i hi)).aestronglyMeasurable)
    (ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ 2 * p))
    (fun _ => A * B) (fun _ _ => mul_nonneg hA hB)
    (fun i hi => eLpNorm_mul_le_of_bounds hp hA (hX i hi) (hY i hi) (hXb i hi) (hYb i hi))
  simpa only [Finset.sum_const, nsmul_eq_mul] using hsum

end EinsteinRelation.Correctors
