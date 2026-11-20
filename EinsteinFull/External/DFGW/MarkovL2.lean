import EinsteinFull.External.DFGW.ShiftedMarkov
import EinsteinFull.External.DFGW.TransitionOperator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! # The Markov property for square-integrable observables

The Markov property extends from bounded observables to the entire stationary `L²` space.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Conditional expectation of a later `L²` observable equals the transition operator
at the earlier state. -/
theorem condExp_shifted_L2 (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (s t : ℝ≥0) (f : Lp ℝ 2 μ) :
    P[fun η : C(ℝ, S) => f (η ((t : ℝ) + s)) |
      Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] =ᵐ[P]
      fun η => transitionOperator hP t f (η s) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let hσ : Draft.dfgwCoordSigma (S := S) (Set.Iic (s : ℝ)) ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S) := (Draft.dfgwPast (S := S)).le s
  let hEval (u : ℝ) : MeasurePreserving (fun η : C(ℝ, S) => η u) P μ :=
    ⟨(continuous_eval_const u).measurable, hP.marginal u⟩
  let A : Lp ℝ 2 μ → Lp ℝ 2 P := fun g =>
    (condExpL2 ℝ ℝ hσ (Lp.compMeasurePreserving _ (hEval ((t : ℝ) + s)) g) : Lp ℝ 2 P)
  let B : Lp ℝ 2 μ → Lp ℝ 2 P := fun g =>
    Lp.compMeasurePreserving _ (hEval s) (transitionOperator hP t g)
  have hAcont : Continuous A := by
    exact continuous_subtype_val.comp ((condExpL2 ℝ ℝ hσ).continuous.comp
      (Lp.isometry_compMeasurePreserving (E := ℝ) (p := 2) (hEval ((t : ℝ) + s))).continuous)
  have hBcont : Continuous B :=
    (Lp.isometry_compMeasurePreserving (E := ℝ) (p := 2) (hEval s)).continuous.comp
      (transitionOperator hP t).continuous
  have hsimple : ∀ z : Lp.simpleFunc ℝ 2 μ, A z = B z := by
    intro z
    let u := Lp.simpleFunc.toSimpleFunc z
    have hu : Measurable u := u.measurable
    have hub : ∃ C, ∀ x, |u x| ≤ C := by
      obtain ⟨C, hC⟩ := u.exists_forall_norm_le
      exact ⟨C, fun x => by simpa only [Real.norm_eq_abs] using hC x⟩
    have huL2 : MemLp u 2 μ := Lp.simpleFunc.memLp z
    have huZ : huL2.toLp u = (z : Lp ℝ 2 μ) := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp huL2).trans (Lp.simpleFunc.toSimpleFunc_eq_toFun z)
    have hfu : MemLp (fun η : C(ℝ, S) => u (η ((t : ℝ) + s))) 2 P :=
      huL2.comp_measurePreserving (hEval ((t : ℝ) + s))
    have hleft : A z =ᵐ[P] P[fun η : C(ℝ, S) => u (η ((t : ℝ) + s)) |
        Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] := by
      change (condExpL2 ℝ ℝ hσ (Lp.compMeasurePreserving _ (hEval ((t : ℝ) + s)) z) : Lp ℝ 2 P) =ᵐ[P] _
      rw [← huZ, Lp.toLp_compMeasurePreserving]
      exact hfu.condExpL2_ae_eq_condExp hσ
    have hκ : T t ∘ₘ μ ≤ μ := le_of_eq (kernel_comp_eq hP t)
    have huRep : (u : S → ℝ) =ᵐ[μ] (z : Lp ℝ 2 μ) := Lp.simpleFunc.toSimpleFunc_eq_toFun z
    have hker := MarkovProcess.kernelIntegral_congr_ae hκ huRep
    have hker' := (hEval s).quasiMeasurePreserving.ae hker
    have hop := (hEval s).quasiMeasurePreserving.ae (transitionOperator_ae_eq hP t z)
    have hB := Lp.coeFn_compMeasurePreserving (transitionOperator hP t z) (hEval s)
    have hm := condExp_shifted hP (s : ℝ) t u hu hub
    apply Lp.ext
    filter_upwards [hleft, hB, hm, hop, hker'] with η hl hb hmη ho hk
    change A z η = B z η
    simp only [Function.comp_apply] at hb ho hk
    rw [hl, hb, hmη, ho]
    change MarkovProcess.kernelIntegral (T t) u (η s) =
      MarkovProcess.kernelIntegral (T t) (z : Lp ℝ 2 μ) (η s)
    exact hk
  have hall : A = B := (Lp.simpleFunc.denseRange (E := ℝ) (μ := μ) (p := 2) (by simp)).equalizer
    hAcont hBcont (funext hsimple)
  have hfut := (Lp.memLp f).comp_measurePreserving (hEval ((t : ℝ) + s))
  have hleft : A f =ᵐ[P] P[fun η : C(ℝ, S) => f (η ((t : ℝ) + s)) |
      Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] := by
    change (condExpL2 ℝ ℝ hσ (Lp.compMeasurePreserving _ (hEval ((t : ℝ) + s)) f) : Lp ℝ 2 P) =ᵐ[P] _
    have heq : hfut.toLp (fun η => f (η ((t : ℝ) + s))) =
        Lp.compMeasurePreserving _ (hEval ((t : ℝ) + s)) f := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp hfut).trans
        (Lp.coeFn_compMeasurePreserving f (hEval ((t : ℝ) + s))).symm
    rw [← heq]
    exact hfut.condExpL2_ae_eq_condExp hσ
  have hright := Lp.coeFn_compMeasurePreserving (transitionOperator hP t f) (hEval s)
  change B f =ᵐ[P] _ at hright
  rw [← hall] at hright
  exact hleft.symm.trans hright

end EinsteinFull.External.DFGW
