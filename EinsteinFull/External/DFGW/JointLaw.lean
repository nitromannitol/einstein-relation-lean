import EinsteinFull.External.DFGW.KernelInvariant

/-! # Two-time joint law

The Markov property identifies the joint law of the initial and later state with the
composition-product of the stationary marginal and the transition kernel.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The two-time joint law is the composition-product of the marginal and transition kernel. -/
theorem map_pair_eq_compProd (hP : Draft.IsDFGWTrajectoryProcess P μ T) (t : ℝ≥0) :
    P.map (fun η : C(ℝ, S) => (η 0, η t)) = μ ⊗ₘ T t := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let : IsMarkovKernel (T t) := hP.markov_kernel t
  let e : C(ℝ, S) → S × S := fun η => (η 0, η t)
  have he : Measurable e := (continuous_eval_const 0).measurable.prodMk
    (continuous_eval_const (t : ℝ)).measurable
  change P.map e = μ ⊗ₘ T t
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply he (hA.prod hB), Measure.compProd_apply_prod hA hB]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by
    exact ne_of_lt (lt_of_le_of_lt
      (lintegral_mono fun x => measure_mono (Set.subset_univ B)) (by simp)))).1
  have h := integral_kernel_mul_eq_correlation hP (B.indicator (fun _ => (1 : ℝ)))
    (A.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hB)
    (measurable_const.indicator hA)
    ⟨1, fun x => by by_cases hx : x ∈ B <;> simp [hx]⟩
    ⟨1, fun x => by by_cases hx : x ∈ A <;> simp [hx]⟩ t
  simp_rw [integral_indicator hB, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def] at h
  have hl : (fun x => ((T t x) B).toReal * A.indicator (fun _ => (1 : ℝ)) x) =
      A.indicator (fun x => ((T t x) B).toReal) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hr : (fun η : C(ℝ, S) => B.indicator (fun _ => (1 : ℝ)) (η t) *
      A.indicator (fun _ => (1 : ℝ)) (η 0)) =
      (e ⁻¹' (A ×ˢ B)).indicator (fun _ => (1 : ℝ)) := by
    funext η
    by_cases ha : η 0 ∈ A <;> by_cases hb : η t ∈ B <;>
      simp [e, ha, hb]
  rw [hl, integral_indicator hA, integral_toReal ((T t).measurable_coe hB).aemeasurable
    (ae_of_all _ fun x => measure_lt_top (T t x) B), hr,
    integral_indicator (he (hA.prod hB)), setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def] at h
  exact h.symm

end EinsteinFull.External.DFGW
