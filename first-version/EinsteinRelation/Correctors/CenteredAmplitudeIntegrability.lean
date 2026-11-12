import EinsteinRelation.Correctors.CoordinateMomentProjections
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Dominated integrability of centered scalar and tensor amplitudes,
used in `paper/main.tex:872–894`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- A joint amplitude bound about fixed scalar and matrix references
supplies the marginal integrability needed for conditional expectation.
Source: `paper/main.tex:886–894`. -/
theorem integrable_scalar_and_entries_of_joint_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {d : ℕ} (f : Ω → ℝ) (S : Ω → Mat d) (E : Ω → ℝ)
    (hf : Measurable f) (hS : Measurable S) (hE : Integrable E μ)
    (c : ℝ) (A : Mat d)
    (hb : ∀ᵐ ω ∂μ, |f ω-c| + frobeniusNorm (S ω-A) ≤ E ω) :
    Integrable f μ ∧ ∀ i j, Integrable (fun ω => S ω i j) μ := by
  constructor
  · apply (hE.add (integrable_const |c|)).mono' hf.aestronglyMeasurable
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs]
    have ht : |f ω| ≤ |f ω-c| + |c| := by
      simpa only [sub_add_cancel] using abs_add_le (f ω-c) c
    have hn : 0 ≤ frobeniusNorm (S ω-A) := Real.sqrt_nonneg _
    dsimp only [Pi.add_apply]
    linarith
  · intro i j
    have hm : Measurable (fun ω => S ω i j) :=
      ((continuous_apply j).comp (continuous_apply i) :
        Continuous (fun M : Mat d => M i j)).measurable.comp hS
    apply (hE.add (integrable_const |A i j|)).mono' hm.aestronglyMeasurable
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs]
    have he : |S ω i j-A i j| ≤ frobeniusNorm (S ω-A) :=
      abs_entry_le_frobeniusNorm (S ω-A) i j
    have ht : |S ω i j| ≤ |S ω i j-A i j| + |A i j| := by
      simpa only [sub_add_cancel] using abs_add_le (S ω i j-A i j) (A i j)
    dsimp only [Pi.add_apply]
    linarith [abs_nonneg (f ω-c)]
end EinsteinRelation.Correctors
