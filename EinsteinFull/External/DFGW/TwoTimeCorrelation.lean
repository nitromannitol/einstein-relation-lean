import EinsteinFull.External.DFGW.JointLaw
import EinsteinFull.External.DFGW.CorrelationRepresentation

/-! # Correlations at two times

The two-time law identifies correlations of square-integrable state observables with the
transition-semigroup pairing.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The initial-to-later state correlation equals the transition-semigroup pairing. -/
theorem integral_eval_zero_mul_eval (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f g : S → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (t : ℝ≥0) :
    (∫ η : C(ℝ, S), f (η 0) * g (η t) ∂P) =
      inner ℝ (hf.toLp f) (transitionOperator hP t (hg.toLp g)) := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let : IsMarkovKernel (T t) := hP.markov_kernel t
  let ν := μ ⊗ₘ T t
  have hfst : MeasurePreserving Prod.fst ν μ :=
    ⟨measurable_fst, Measure.fst_compProd μ (T t)⟩
  have hsnd : MeasurePreserving Prod.snd ν μ := by
    refine ⟨measurable_snd, ?_⟩
    change (μ ⊗ₘ T t).snd = μ
    rw [Measure.snd_compProd, kernel_comp_eq hP t]
  have hfg : Integrable (fun z : S × S => f z.1 * g z.2) ν := by
    have h := (hf.comp_measurePreserving hfst).integrable_mul (hg.comp_measurePreserving hsnd)
    exact h.congr (ae_of_all _ fun z => by rfl)
  let ev : C(ℝ, S) → S × S := fun η => (η 0, η t)
  have hev : Measurable ev := (continuous_eval_const 0).measurable.prodMk
    (continuous_eval_const (t : ℝ)).measurable
  have hmap : P.map ev = ν := map_pair_eq_compProd hP t
  calc
    _ = ∫ z : S × S, f z.1 * g z.2 ∂P.map ev := by
      symm
      apply integral_map hev.aemeasurable
      rw [hmap]
      exact hfg.aestronglyMeasurable
    _ = ∫ x, f x * ∫ y, g y ∂T t x ∂μ := by
      rw [hmap, Measure.integral_compProd hfg]
      simp only [integral_const_mul]
    _ = _ := integral_mul_kernel_eq_inner hP t f g hf hg

/-- Stationarity expresses a correlation at arbitrary times by the time difference. -/
theorem integral_eval_mul_eval_add (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f g : S → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (s : ℝ) (t : ℝ≥0) :
    (∫ η : C(ℝ, S), f (η s) * g (η ((t : ℝ) + s)) ∂P) =
      inner ℝ (hf.toLp f) (transitionOperator hP t (hg.toLp g)) := by
  have hev (u : ℝ) : MeasurePreserving (fun η : C(ℝ, S) => η u) P μ :=
    ⟨(continuous_eval_const u).measurable, hP.marginal u⟩
  have hfg : Integrable (fun η : C(ℝ, S) => f (η 0) * g (η t)) P := by
    have h := (hf.comp_measurePreserving (hev 0)).integrable_mul
      (hg.comp_measurePreserving (hev t))
    exact h.congr (ae_of_all P fun η => by rfl)
  have hm : AEStronglyMeasurable (fun η : C(ℝ, S) => f (η 0) * g (η t))
      (P.map (Draft.dfgwShift s)) := by
    rw [hP.stationary]
    exact hfg.aestronglyMeasurable
  have hmap := integral_map (measurable_shift s).aemeasurable hm
  rw [hP.stationary] at hmap
  change (∫ η : C(ℝ, S), f (η 0) * g (η t) ∂P) =
    ∫ η : C(ℝ, S), f (η (0 + s)) * g (η ((t : ℝ) + s)) ∂P at hmap
  have heq : (∫ η : C(ℝ, S), f (η s) * g (η ((t : ℝ) + s)) ∂P) =
      ∫ η : C(ℝ, S), f (η 0) * g (η t) ∂P := by
    simpa only [zero_add] using hmap.symm
  rw [heq]
  exact integral_eval_zero_mul_eval hP f g hf hg t

end EinsteinFull.External.DFGW
