import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Moment control on the large-radius event

Source: `paper/main.tex:798–806`. On the event `r < 4*X`, the indicator
is bounded by `4*X/r`. Hölder therefore recovers an inverse-radius factor
from higher moments, without an independence assumption.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- The real exponents `2m,2m,m` form a Hölder triple for positive `m`.
Source: `paper/main.tex:798–806`. -/
theorem holderTriple_double_ofReal {m : ℝ} (hm : 0 < m) :
    ENNReal.HolderTriple (ENNReal.ofReal (2*m)) (ENNReal.ofReal (2*m))
      (ENNReal.ofReal m) := by
  have h2m : 0 < 2*m := mul_pos two_pos hm
  rw [ENNReal.holderTriple_iff, ← ENNReal.ofReal_inv_of_pos h2m,
    ← ENNReal.ofReal_inv_of_pos hm,
    ← ENNReal.ofReal_add (inv_nonneg.mpr h2m.le) (inv_nonneg.mpr h2m.le)]
  congr 1
  field_simp
  ring

/-- An actual bad-radius restriction gains `1/r` using only the two higher
moments. Source: `paper/main.tex:798–806`. -/
theorem badRadius_eLpNorm_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X E : Ω → ℝ} (hXm : Measurable X) (hX : ∀ ω, 0 ≤ X ω)
    {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    (hXLp : MemLp X (ENNReal.ofReal (2*m)) P)
    (hELp : MemLp E (ENNReal.ofReal (2*m)) P) :
    MemLp ({ω | r < 4*X ω}.indicator E) (ENNReal.ofReal m) P ∧
      eLpNorm ({ω | r < 4*X ω}.indicator E) (ENNReal.ofReal m) P ≤
        ENNReal.ofReal (4/r) *
          (eLpNorm X (ENNReal.ofReal (2*m)) P *
            eLpNorm E (ENNReal.ofReal (2*m)) P) := by
  haveI := holderTriple_double_ofReal hm
  have hprod : MemLp (fun ω => X ω * E ω) (ENNReal.ofReal m) P := hELp.mul' hXLp
  have hS : MeasurableSet {ω | r < 4*X ω} :=
    measurableSet_lt measurable_const (measurable_const.mul hXm)
  have hdom : ∀ᵐ ω ∂P,
      ‖{ω | r < 4*X ω}.indicator E ω‖ ≤ (4/r) * ‖X ω * E ω‖ := by
    apply ae_of_all
    intro ω
    by_cases hω : r < 4*X ω
    · have hmem : ω ∈ {ω | r < 4*X ω} := hω
      rw [Set.indicator_of_mem hmem, norm_mul, Real.norm_of_nonneg (hX ω)]
      have hcoef : 1 ≤ (4/r) * X ω := by
        calc
          1 ≤ (4*X ω)/r := (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hω.le)
          _ = _ := by ring
      calc
        ‖E ω‖ = 1 * ‖E ω‖ := (one_mul _).symm
        _ ≤ ((4/r) * X ω) * ‖E ω‖ :=
          mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
        _ = _ := by ring
    · have hmem : ω ∉ {ω | r < 4*X ω} := hω
      rw [Set.indicator_of_notMem hmem,norm_zero]
      exact mul_nonneg (div_nonneg (by norm_num) hr.le) (norm_nonneg _)
  refine ⟨hprod.of_le_mul (hELp.1.indicator hS) hdom,?_⟩
  calc
    _ ≤ ENNReal.ofReal (4/r) * eLpNorm (fun ω => X ω * E ω) (ENNReal.ofReal m) P :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom _
    _ ≤ _ := mul_le_mul_right
      (eLpNorm_smul_le_mul_eLpNorm (𝕜 := ℝ) (E := ℝ)
        (p := ENNReal.ofReal (2*m)) (q := ENNReal.ofReal (2*m))
        (r := ENNReal.ofReal m) (f := E) (φ := X) hELp.1 hXLp.1) _

end EinsteinRelation.Correctors
