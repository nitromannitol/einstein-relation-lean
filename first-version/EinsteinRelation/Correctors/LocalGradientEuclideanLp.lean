import EinsteinRelation.Correctors.LocalConditioningBounds

/-! # Euclidean conditional gradient errors

Source: `paper/main.tex:968–973`. Conditional expectation is initially defined
on the coordinate carrier. Transport to Euclidean space preserves both its
conditional versions and the manuscript's norm, with no dimension factor.
-/

open MeasureTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- Conditional expectation commutes with the Euclidean identification of the
coordinate carrier. Source: `paper/main.tex:968–973`. -/
theorem ae_toLp_condExp {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
    {d : ℕ} {m : MeasurableSpace Ω} {f : Ω → Vec d} (hf : Integrable f μ) :
    (fun ω => WithLp.toLp 2 (μ[f | m] ω)) =ᵐ[μ]
      μ[fun ω => (WithLp.toLp 2 (f ω) : EuclideanSpace ℝ (Fin d)) | m] := by
  letI : MeasurableSpace Ω := m₀
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp_condExp_comm hf

/-- The conditional gradient error has exactly the Euclidean `Lp` norm after
transport. Source: `paper/main.tex:968–973`. -/
theorem eLpNorm_euclidean_condExp_error_eq {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} {d : ℕ} {m : MeasurableSpace Ω} {f : Ω → Vec d}
    (hf : Integrable f μ) (p : ℝ≥0∞) :
    eLpNorm (fun ω => euclideanNorm (μ[f | m] ω - f ω)) p μ =
      eLpNorm (μ[fun ω => (WithLp.toLp 2 (f ω) : EuclideanSpace ℝ (Fin d)) | m] -
        (fun ω => WithLp.toLp 2 (f ω))) p μ := by
  letI : MeasurableSpace Ω := m₀
  have heq : (fun ω => euclideanNorm (μ[f | m] ω - f ω)) =ᵐ[μ]
      fun ω => ‖μ[fun ω => (WithLp.toLp 2 (f ω) : EuclideanSpace ℝ (Fin d)) | m] ω -
        WithLp.toLp 2 (f ω)‖ := by
    filter_upwards [ae_toLp_condExp (μ := μ) (f := f) (m := m) hf] with ω hω
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
    exact congrArg (fun v => ‖v - WithLp.toLp 2 (f ω)‖) hω
  exact (eLpNorm_congr_ae heq).trans (eLpNorm_norm _)

/-- The opposite order of the conditional error has the same exact Euclidean
transport. Source: `paper/main.tex:968–973`. -/
theorem eLpNorm_euclidean_sub_condExp_error_eq {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} {d : ℕ} {m : MeasurableSpace Ω} {f : Ω → Vec d}
    (hf : Integrable f μ) (p : ℝ≥0∞) :
    eLpNorm (fun ω => euclideanNorm (f ω - μ[f | m] ω)) p μ =
      eLpNorm ((fun ω => (WithLp.toLp 2 (f ω) : EuclideanSpace ℝ (Fin d))) -
        μ[fun ω => (WithLp.toLp 2 (f ω) : EuclideanSpace ℝ (Fin d)) | m]) p μ := by
  letI : MeasurableSpace Ω := m₀
  calc
    _ = eLpNorm (fun ω => euclideanNorm (μ[f | m] ω - f ω)) p μ := by
      apply eLpNorm_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        dsimp only
        rw [TimeChange.euclideanNorm_eq_norm_toLp, TimeChange.euclideanNorm_eq_norm_toLp]
        exact norm_sub_rev _ _
    _ = _ := (eLpNorm_euclidean_condExp_error_eq (m := m) hf p).trans
      (eLpNorm_sub_comm _ _ p μ)

/-- The exact Euclidean version of the nested-ball comparison for the gradient
in Proposition 5.3. Source: `paper/main.tex:968–973`. -/
theorem eLpNorm_euclidean_corrector_local_gradient_error_le {d : ℕ}
    {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ]
    {R : ℝ} (hR : 1 ≤ R) {y : Vec d} (hy : euclideanNorm y ≤ R)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {f : FieldPair d → Vec d}
    (hf : Integrable f μ) :
    eLpNorm (fun ω => euclideanNorm
      (μ[f | reducedCoefficientObservationSigma
        {z : Vec d | euclideanNorm (z - y) < 32 * R}] ω - f ω)) p μ ≤
      2 * eLpNorm (fun ω => euclideanNorm
        (f ω - μ[f | reducedCoefficientObservationSigma
          {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω)) p μ := by
  have hJ : Integrable (fun ω => (WithLp.toLp 2 (f ω) : EuclideanSpace ℝ (Fin d))) μ :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.integrable_comp hf
  rw [eLpNorm_euclidean_condExp_error_eq hf, eLpNorm_euclidean_sub_condExp_error_eq hf]
  exact eLpNorm_corrector_local_gradient_error_le hR hy hp hpt hJ

end EinsteinRelation.Correctors
