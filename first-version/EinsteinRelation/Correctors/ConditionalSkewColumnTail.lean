import EinsteinRelation.Correctors.CoordinateMomentProjections
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Euclidean column tails from the source Frobenius conditional tail

Source: `paper/main.tex:825–835,948–963`. The matrix conditional tail in
Lemma 5.2 controls the Euclidean column tails used by the literal skew
correction. Vector conditional expectations are identified with their
entrywise scalar versions before comparing the geometric norms.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- A column's actual Euclidean norm is bounded by the matrix Frobenius
norm. Source: `paper/main.tex:825–835,948–963`. -/
theorem euclideanNorm_column_le_frobeniusNorm {d : ℕ} (S : Mat d) (k : Fin d) :
    euclideanNorm (fun j => S j k) ≤ frobeniusNorm S := by
  unfold euclideanNorm euclideanSq dot frobeniusNorm frobeniusSq
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  exact Finset.single_le_sum (fun ℓ _ => mul_self_nonneg (S j ℓ)) (Finset.mem_univ k)

/-- A vector conditional expectation of a matrix column agrees with the
entrywise scalar conditional expectations. Source: `paper/main.tex:825–835`. -/
theorem condExp_column_ae_eq_entrywise {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) (m : MeasurableSpace Ω) (S : Ω → Mat d) (k : Fin d)
    (hS : Integrable (fun ω j => S ω j k) μ) :
    μ[fun ω j => S ω j k | m] =ᵐ[μ]
      (fun ω j => μ[fun a => S a j k | m] ω) := by
  have hcoord (j : Fin d) :
      (fun ω => μ[fun a ℓ => S a ℓ k | m] ω j) =ᵐ[μ]
        μ[fun a => S a j k | m] := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).comp_condExp_comm (m := m) hS
  filter_upwards [ae_all_iff.mpr hcoord] with ω hω
  exact funext hω

/-- The exact entrywise Frobenius tail of Lemma 5.2 bounds each Euclidean
column tail required by the skew correction. Source: `paper/main.tex:948–963`. -/
theorem eLpNorm_conditional_column_sub_le_frobenius {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) (m : MeasurableSpace Ω) (S : Ω → Mat d)
    (k : Fin d) (hS : Integrable (fun ω j => S ω j k) μ) (p : ENNReal) :
    eLpNorm (fun ω => euclideanNorm ((fun j => S ω j k) -
      μ[fun a j => S a j k | m] ω)) p μ ≤
      eLpNorm (fun ω => frobeniusNorm (fun j ℓ =>
        S ω j ℓ - μ[fun a => S a j ℓ | m] ω)) p μ := by
  apply eLpNorm_mono_ae
  filter_upwards [condExp_column_ae_eq_entrywise (mΩ := mΩ) μ m S k hS] with ω hω
  rw [hω]
  change |Real.sqrt _| ≤ |Real.sqrt _|
  rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  exact euclideanNorm_column_le_frobeniusNorm
    (fun j ℓ => S ω j ℓ - μ[fun a => S a j ℓ | m] ω) k

end EinsteinRelation.Correctors
