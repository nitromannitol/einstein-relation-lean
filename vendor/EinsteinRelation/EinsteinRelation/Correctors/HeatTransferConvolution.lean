import EinsteinRelation.Calculus.HorizontalMollification
import EinsteinRelation.Calculus.HorizontalTranslationLp
import EinsteinRelation.Correctors.IntegralMoment

/-!
# Moment bounds for signed spatial kernels

The spatial Minkowski step in Proposition 6.1, Step 2 (`paper/main.tex:1018–1031`),
uses kernels such as derivatives of `K_r` and their Laplacians. They need not be
nonnegative or have unit mass. This file proves the bound for any integrable
signed kernel, using the actual translations of a stationary environment law.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- Spatial convolution with a signed integrable kernel has moment norm at most
the kernel's `L¹` mass times the moment bound of the field. It also has an
almost everywhere absolutely convergent orbit integral
(`paper/main.tex:1018–1031`). -/
theorem horizontalMollify_moment_le
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {m C : ℝ} (hm : 1 ≤ m) (hC : 0 ≤ C)
    {K : Vec d → ℝ} (hK : Measurable K) (hKi : Integrable K)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfn : eLpNorm f (ENNReal.ofReal m) Q ≤ ENNReal.ofReal C) :
    (∀ᵐ ω ∂Q, Integrable (fun x => K x * f (translate x ω))) ∧
    MemLp (horizontalMollify K f) (ENNReal.ofReal m) Q ∧
    eLpNorm (horizontalMollify K f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal ((∫ x, |K x|) * C) := by
  have hfm : MemLp f (ENNReal.ofReal m) Q := hfn.trans_lt ENNReal.ofReal_lt_top
  have hj : Measurable (fun z : Vec d × FieldPair d => K z.1 * f (translate z.1 z.2)) :=
    (hK.comp measurable_fst).mul (hf.comp Probability.continuous_translate.measurable)
  have hsec : ∀ x : Vec d,
      MemLp (fun ω => K x * f (translate x ω)) (ENNReal.ofReal m) Q ∧
      eLpNorm (fun ω => K x * f (translate x ω)) (ENNReal.ofReal m) Q ≤
        ENNReal.ofReal (|K x| * C) := by
    intro x
    have hmp := measurePreserving_translate Q hQ x
    refine ⟨(hfm.comp_measurePreserving hmp).const_mul _, ?_⟩
    calc
      eLpNorm (fun ω => K x * f (translate x ω)) (ENNReal.ofReal m) Q =
          ‖K x‖ₑ * eLpNorm f (ENNReal.ofReal m) Q := by
        change eLpNorm (K x • (f ∘ translate x)) (ENNReal.ofReal m) Q = _
        rw [eLpNorm_const_smul, eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hmp]
      _ ≤ ‖K x‖ₑ * ENNReal.ofReal C := mul_le_mul_right hfn _
      _ = ENNReal.ofReal (|K x| * C) := by
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, ENNReal.ofReal_mul (abs_nonneg _)]
  have hKm : Measurable (fun x : Vec d => |K x| * C) := hK.norm.mul measurable_const
  have h := integral_moment_le Q (volume : Measure (Vec d)) hm
    (fun x => |K x| * C) hKm
    (fun x => mul_nonneg (abs_nonneg _) hC) (hKi.abs.mul_const C)
    (fun z => K z.1 * f (translate z.1 z.2)) hj hsec
  rw [integral_mul_const] at h
  exact h

end EinsteinRelation.Correctors
