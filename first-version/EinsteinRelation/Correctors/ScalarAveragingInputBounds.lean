import EinsteinRelation.Correctors.ScalarDecompositionGlue
import EinsteinRelation.Correctors.CoordinateFieldMomentBounds

/-! # Moment inputs from the actual scalar averaging predicate

Source: `paper/main.tex:971–974,1028–1041`. Only the prescribed value
`M (4p)` enters the estimates, with no monotonicity assumption on `M`.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- The averaging predicate gives an actual measurable, square-integrable
field and a positive uniform heat bound at order `4p`
(`paper/main.tex:971–974,1028–1041`). -/
theorem scalarAveraging_input_bounds {d : ℕ} {Λ₀ r₀ p R M4p : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hp : 1 ≤ p) (hR : 2 ≤ R)
    (M : ℝ → ℝ) (hM : M (4 * p) = M4p) (f : FieldPair d → ℝ)
    (hf : Carriers.IsScalarAveragingField Q M R f) :
    Measurable f ∧ MemLp f 2 (reducedEnvironmentLaw Q) ∧
    (∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) (ENNReal.ofReal (4 * p))
      (reducedEnvironmentLaw Q) ≤
      ENNReal.ofReal ((1 + |M4p|) * ((Real.sqrt (1 + t))⁻¹ + R⁻¹))) ∧
    eLpNorm f (ENNReal.ofReal (4 * p)) (reducedEnvironmentLaw Q) ≤
      ENNReal.ofReal (2 * (1 + |M4p|)) ∧
    eLpNorm f (ENNReal.ofReal (2 * p)) (reducedEnvironmentLaw Q) ≤
      ENNReal.ofReal (2 * (1 + |M4p|)) := by
  have hfm : Measurable f := hf.1.mono (Probability.localSigma_le_borel _) le_rfl
  have hheat (t : ℝ) (ht : 0 ≤ t) := hf.2 (4 * p) (by linarith) t ht
  have hh (t : ℝ) (ht : 0 ≤ t) : eLpNorm (heatSmoothed t f) (ENNReal.ofReal (4 * p))
      (reducedEnvironmentLaw Q) ≤
      ENNReal.ofReal ((1 + |M4p|) * ((Real.sqrt (1 + t))⁻¹ + R⁻¹)) := by
    apply (hheat t ht).trans
    apply ENNReal.ofReal_le_ofReal
    rw [hM]
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self M4p]) (by positivity)
  have hzero : heatSmoothed 0 f = f := by funext ω; simp [heatSmoothed]
  have hfb : eLpNorm f (ENNReal.ofReal (4 * p)) (reducedEnvironmentLaw Q) ≤
      ENNReal.ofReal (2 * (1 + |M4p|)) := by
    have h := hh 0 le_rfl
    simp only [hzero, add_zero, Real.sqrt_one, inv_one] at h
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    have hRi : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    nlinarith [abs_nonneg M4p]
  have hfp : MemLp f (ENNReal.ofReal (4 * p)) (reducedEnvironmentLaw Q) :=
    ⟨hfm.aestronglyMeasurable, hfb.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hfm, hfp.mono_exponent ?_, hh, hfb, ?_⟩
  · exact_mod_cast (ENNReal.ofReal_le_ofReal (show (2 : ℝ) ≤ 4 * p by linarith))
  · exact (eLpNorm_le_eLpNorm_of_exponent_le
      (ENNReal.ofReal_le_ofReal (show 2 * p ≤ 4 * p by linarith)) hfm.aestronglyMeasurable).trans hfb

end EinsteinRelation.Correctors
