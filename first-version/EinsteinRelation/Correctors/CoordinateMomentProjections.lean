import EinsteinRelation.Correctors.CoordinateFieldMomentBounds
import EinsteinRelation.Correctors.RadialPoissonKernel
import EinsteinRelation.Environment.MatrixNorm

/-! # Projecting Euclidean and Frobenius moments onto coordinates

Source: `paper/main.tex:1037–1041,1070–1082`. These estimates retain the
geometric norms in the source while exposing scalar Hölder factors.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- A matrix entry is bounded by its Frobenius norm
(`paper/main.tex:1070–1075`). -/
theorem abs_entry_le_frobeniusNorm {d : ℕ} (S : Mat d) (i j : Fin d) :
    |S i j| ≤ frobeniusNorm S := by
  unfold frobeniusNorm
  apply Real.abs_le_sqrt
  rw [sq]
  exact (Finset.single_le_sum (f := fun k => S i k * S i k)
    (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun k => ∑ l, S k l * S k l)
      (fun k _ => Finset.sum_nonneg fun l _ => mul_self_nonneg _) (Finset.mem_univ i))

/-- Coordinate projection of a Euclidean moment (`paper/main.tex:1070–1082`). -/
theorem eLpNorm_coordinate_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d : ℕ} {p : ℝ≥0∞} (V : Ω → Vec d) (i : Fin d) :
    eLpNorm (fun ω => V ω i) p μ ≤ eLpNorm (fun ω => euclideanNorm (V ω)) p μ := by
  apply eLpNorm_mono_real
  intro ω
  simpa only [Real.norm_eq_abs] using abs_coord_le_euclideanNorm (V ω) i

/-- Entry projection of a Frobenius moment (`paper/main.tex:1070–1075`). -/
theorem eLpNorm_entry_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d : ℕ} {p : ℝ≥0∞} (S : Ω → Mat d) (i j : Fin d) :
    eLpNorm (fun ω => S ω i j) p μ ≤ eLpNorm (fun ω => frobeniusNorm (S ω)) p μ := by
  apply eLpNorm_mono_real
  intro ω
  simpa only [Real.norm_eq_abs] using abs_entry_le_frobeniusNorm (S ω) i j

end EinsteinRelation.Correctors
