import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! # Inclusion of `L²` into `L¹` on a probability space

The natural inclusion is a contraction with dense range.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The natural linear inclusion of `L²` into `L¹`. -/
noncomputable def lpTwoToOneLinear : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 1 P where
  toFun f := ⟨f.1, Lp.antitone (by norm_num : (1 : ℝ≥0∞) ≤ 2) f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `L²`-to-`L¹` inclusion is contractive on a probability space. -/
theorem norm_lpTwoToOneLinear_le (f : Lp ℝ 2 P) : ‖lpTwoToOneLinear P f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

/-- The continuous inclusion of `L²` into `L¹`. -/
noncomputable def lpTwoToOne : Lp ℝ 2 P →L[ℝ] Lp ℝ 1 P :=
  (lpTwoToOneLinear P).mkContinuous 1 (fun f => by simpa using norm_lpTwoToOneLinear_le P f)

/-- The inclusion preserves the underlying almost-everywhere function. -/
theorem lpTwoToOne_ae (f : Lp ℝ 2 P) : lpTwoToOne P f =ᵐ[P] f := by
  exact ae_of_all P fun _ => rfl

/-- The `L²`-to-`L¹` inclusion has dense range. -/
theorem denseRange_lpTwoToOne : DenseRange (lpTwoToOne P) := by
  let L := (LinearMap.range (lpTwoToOne P).toLinearMap).topologicalClosure
  have hall : ∀ f : Lp ℝ 1 P, f ∈ L := by
    refine Lp.induction (by simp : (1 : ℝ≥0∞) ≠ ∞) (fun f => f ∈ L) ?_ ?_
      (Submodule.isClosed_topologicalClosure _)
    · intro c A hA hfin
      change indicatorConstLp 1 hA hfin.ne c ∈ L
      apply Submodule.le_topologicalClosure
      refine ⟨indicatorConstLp 2 hA hfin.ne c, ?_⟩
      change lpTwoToOne P (indicatorConstLp 2 hA hfin.ne c) = indicatorConstLp 1 hA hfin.ne c
      apply Lp.ext
      filter_upwards [lpTwoToOne_ae P (indicatorConstLp 2 hA hfin.ne c),
        indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hfin.ne) (c := c),
        indicatorConstLp_coeFn (p := 1) (hs := hA) (hμs := hfin.ne) (c := c)] with x h1 h2 h3
      rw [h1, h2, h3]
    · intro f g hf hg hdisj hfm hgm
      exact L.add_mem hfm hgm
  change Dense (Set.range (lpTwoToOne P))
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_iff_forall.mpr
  intro f
  exact hall f

end EinsteinFull.External.DFGW
