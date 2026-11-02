import EinsteinFull.Calculus.ComplexLowExponentGrowthSupport
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.Normed.Operator.Extend

/-! Genuine finite Lp extensions of the actual L2 operators, below two. -/
open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {p : ℝ≥0∞}

/-- The actual inclusion from L2 to a lower exponent, with identical AE class. -/
def complexL2ToLp (hp2 : p ≤ 2) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ p μ where
  toFun f := ⟨f.1, Lp.antitone hp2 f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The L2 inclusion preserves the actual representative. -/
theorem complexL2ToLp_apply (hp2 : p ≤ 2) (f : Lp ℂ 2 μ) :
    (complexL2ToLp μ hp2 f : α → ℂ) = f := rfl

variable [Fact (1 ≤ p)]

/-- Simple functions prove density of the actual L2 inclusion at every finite
lower exponent; no density premise is imposed on the extension. -/
theorem denseRange_complexL2ToLp (hp2 : p ≤ 2) (hp : p ≠ ⊤) :
    DenseRange (complexL2ToLp μ hp2) := by
  apply (Lp.simpleFunc.denseRange (E := ℂ) (μ := μ) hp).mono
  rintro _ ⟨g, rfl⟩
  have h₂ : MemLp (Lp.simpleFunc.toSimpleFunc g) 2 μ :=
    ((Lp.simpleFunc.toSimpleFunc g).memLp_top μ).mono_exponent le_top
  refine ⟨h₂.toLp _, ?_⟩
  apply Lp.ext
  exact h₂.coeFn_toLp.trans (Lp.simpleFunc.toSimpleFunc_eq_toFun g)

/-- Extend an actual L2 operator through the dense lower-Lp inclusion.
Agreement and bounds below are proved from the genuine Lp estimate. -/
def complexL2OperatorLpExtension (hp2 : p ≤ 2)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  ((complexL2ToLp μ hp2).comp A.toLinearMap).extendOfNorm (complexL2ToLp μ hp2)

omit [Fact (1 ≤ p)] in
private theorem norm_complexL2ToLp_le_of_bound (hp2 : p ≤ 2)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ f : Lp ℂ 2 μ, eLpNorm (A f) p μ ≤ eLpNorm f p μ * ENNReal.ofReal C)
    (f : Lp ℂ 2 μ) :
    ‖complexL2ToLp μ hp2 (A f)‖ ≤ C * ‖complexL2ToLp μ hp2 f‖ := by
  have htop := ((Lp.memLp f).mono_exponent hp2).eLpNorm_ne_top
  have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top htop ENNReal.ofReal_ne_top) (hA f)
  simpa only [Lp.norm_def, complexL2ToLp_apply, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC, mul_comm] using hb

/-- The bounded extension agrees with the actual L2 operator on all L2 data. -/
theorem complexL2OperatorLpExtension_apply (hp2 : p ≤ 2) (hp : p ≠ ⊤)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ f : Lp ℂ 2 μ, eLpNorm (A f) p μ ≤ eLpNorm f p μ * ENNReal.ofReal C)
    (f : Lp ℂ 2 μ) :
    complexL2OperatorLpExtension μ hp2 A (complexL2ToLp μ hp2 f) =
      complexL2ToLp μ hp2 (A f) :=
  LinearMap.extendOfNorm_eq (denseRange_complexL2ToLp μ hp2 hp)
    ⟨C, norm_complexL2ToLp_le_of_bound μ hp2 A hC hA⟩ f

/-- The original leading constant is retained on every datum of genuine Lp. -/
theorem norm_complexL2OperatorLpExtension_le (hp2 : p ≤ 2) (hp : p ≠ ⊤)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ f : Lp ℂ 2 μ, eLpNorm (A f) p μ ≤ eLpNorm f p μ * ENNReal.ofReal C) :
    ‖complexL2OperatorLpExtension μ hp2 A‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_complexL2ToLp μ hp2 hp) hC
    (norm_complexL2ToLp_le_of_bound μ hp2 A hC hA)

/-- The genuine Lp extension is uniquely determined by its actual L2 action. -/
theorem complexL2OperatorLpExtension_unique (hp2 : p ≤ 2) (hp : p ≠ ⊤)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ f : Lp ℂ 2 μ, eLpNorm (A f) p μ ≤ eLpNorm f p μ * ENNReal.ofReal C)
    (B : Lp ℂ p μ →L[ℂ] Lp ℂ p μ)
    (hB : ∀ f, B (complexL2ToLp μ hp2 f) = complexL2ToLp μ hp2 (A f)) :
    complexL2OperatorLpExtension μ hp2 A = B := by
  apply ContinuousLinearMap.ext
  intro f
  refine (denseRange_complexL2ToLp μ hp2 hp).induction_on f
    (isClosed_eq (complexL2OperatorLpExtension μ hp2 A).continuous B.continuous) ?_
  intro g
  rw [complexL2OperatorLpExtension_apply μ hp2 hp A hC hA, hB]

/-- Extension preserves the identity on the entire genuine Lp space. -/
theorem complexL2OperatorLpExtension_id (hp2 : p ≤ 2) (hp : p ≠ ⊤) :
    complexL2OperatorLpExtension μ hp2 (ContinuousLinearMap.id ℂ (Lp ℂ 2 μ)) =
      ContinuousLinearMap.id ℂ (Lp ℂ p μ) := by
  apply complexL2OperatorLpExtension_unique μ hp2 hp _ (C := 1) zero_le_one
  · intro f
    simp only [ContinuousLinearMap.id_apply, ENNReal.ofReal_one, mul_one, le_refl]
  · intro f
    rfl

/-- Extension preserves composition when both actual operators satisfy the
proved lower-Lp estimates. -/
theorem complexL2OperatorLpExtension_comp (hp2 : p ≤ 2) (hp : p ≠ ⊤)
    (A B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ f : Lp ℂ 2 μ, eLpNorm (A f) p μ ≤ eLpNorm f p μ * ENNReal.ofReal C)
    (hB : ∀ f : Lp ℂ 2 μ, eLpNorm (B f) p μ ≤ eLpNorm f p μ * ENNReal.ofReal D) :
    complexL2OperatorLpExtension μ hp2 (A.comp B) =
      (complexL2OperatorLpExtension μ hp2 A).comp
        (complexL2OperatorLpExtension μ hp2 B) := by
  apply complexL2OperatorLpExtension_unique μ hp2 hp _ (C := C * D) (mul_nonneg hC hD)
  · intro f
    calc
      _ ≤ eLpNorm (B f) p μ * ENNReal.ofReal C := hA (B f)
      _ ≤ (eLpNorm f p μ * ENNReal.ofReal D) * ENNReal.ofReal C :=
        mul_le_mul_left (hB f) _
      _ = _ := by rw [ENNReal.ofReal_mul hC]; ac_rfl
  · intro f
    rw [ContinuousLinearMap.comp_apply,
      complexL2OperatorLpExtension_apply μ hp2 hp B hD hB,
      complexL2OperatorLpExtension_apply μ hp2 hp A hC hA,
      ContinuousLinearMap.comp_apply]

end EinsteinFull
