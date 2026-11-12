import EinsteinRelation.Environment.MatrixNorm
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
/-- Source: `paper/main.tex:709-716,743-745`. Joint measurability of the
scalar representative suffices to split the combined lower average;
the tensor representative need not be jointly measurable. -/
theorem lintegral_laverage_centered_scalar_flux_add
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Measure X) [SFinite P] [SFinite μ]
    {d : ℕ} (f : Ω → X → ℝ) (S : Ω → X → Mat d) (p : ℝ)
    (hf : Measurable (Function.uncurry f)) :
    (∫⁻ ω, (⨍⁻ x,
      ENNReal.ofReal (|f ω x - ⨍ y, f ω y ∂μ| ^ p) +
      ENNReal.ofReal (frobeniusNorm (S ω x -
        Matrix.of (fun j k => ⨍ y, S ω y j k ∂μ)) ^ p) ∂μ) ∂P) =
    (∫⁻ ω, (⨍⁻ x, ENNReal.ofReal (|f ω x - ⨍ y, f ω y ∂μ| ^ p) ∂μ) ∂P) +
    (∫⁻ ω, (⨍⁻ x, ENNReal.ofReal (frobeniusNorm (S ω x -
      Matrix.of (fun j k => ⨍ y, S ω y j k ∂μ)) ^ p) ∂μ) ∂P) := by
  let A : Ω → X → ℝ≥0∞ := fun ω x => ENNReal.ofReal (|f ω x - ⨍ y, f ω y ∂μ| ^ p)
  let B : Ω → X → ℝ≥0∞ := fun ω x => ENNReal.ofReal (frobeniusNorm (S ω x -
    Matrix.of (fun j k => ⨍ y, S ω y j k ∂μ)) ^ p)
  have hm : Measurable (fun ω => ⨍ y, f ω y ∂μ) :=
    (hf.stronglyMeasurable.integral_prod_right' (ν := (μ Set.univ)⁻¹ • μ)).measurable
  have hA : Measurable (Function.uncurry A) :=
    ((continuous_abs.measurable.comp (hf.sub (hm.comp measurable_fst))).pow_const p).ennreal_ofReal
  have heq (ω : Ω) : (⨍⁻ x, A ω x + B ω x ∂μ) = (⨍⁻ x, A ω x ∂μ) + (⨍⁻ x, B ω x ∂μ) :=
    lintegral_add_left (hA.of_uncurry_left (x := ω)) _
  change (∫⁻ ω, ⨍⁻ x, A ω x + B ω x ∂μ ∂P) = _
  simp_rw [heq]
  exact lintegral_add_left (hA.lintegral_prod_right (ν := (μ Set.univ)⁻¹ • μ)) _
end EinsteinRelation.Correctors
