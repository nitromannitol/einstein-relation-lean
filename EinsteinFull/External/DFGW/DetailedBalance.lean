import EinsteinFull.External.DFGW.KernelInvariant

/-! # Detailed balance of transition kernels

The joint law of two states at a fixed time separation is invariant under exchanging the states.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The stationary kernel measure has equal mass on transposed measurable rectangles. -/
theorem compProd_prod_comm (hP : Draft.IsDFGWTrajectoryProcess P μ T) (t : ℝ≥0)
    {A B : Set S} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (μ ⊗ₘ T t) (A ×ˢ B) = (μ ⊗ₘ T t) (B ×ˢ A) := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let : IsMarkovKernel (T t) := hP.markov_kernel t
  have h := integral_kernel_mul_comm hP (B.indicator (fun _ => (1 : ℝ)))
    (A.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hB)
    (measurable_const.indicator hA)
    ⟨1, fun x => by by_cases hx : x ∈ B <;> simp [hx]⟩
    ⟨1, fun x => by by_cases hx : x ∈ A <;> simp [hx]⟩ t
  simp_rw [integral_indicator hB, integral_indicator hA, setIntegral_const, smul_eq_mul,
    mul_one, measureReal_def] at h
  have ha : (fun x => ((T t x) B).toReal * A.indicator (fun _ => (1 : ℝ)) x) =
      A.indicator (fun x => ((T t x) B).toReal) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hb : (fun x => ((T t x) A).toReal * B.indicator (fun _ => (1 : ℝ)) x) =
      B.indicator (fun x => ((T t x) A).toReal) := by
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [ha, hb, integral_indicator hA, integral_indicator hB] at h
  rw [integral_toReal ((T t).measurable_coe hB).aemeasurable
    (ae_of_all _ fun x => measure_lt_top (T t x) B),
    integral_toReal ((T t).measurable_coe hA).aemeasurable
      (ae_of_all _ fun x => measure_lt_top (T t x) A)] at h
  rw [Measure.compProd_apply_prod hA hB, Measure.compProd_apply_prod hB hA]
  apply (ENNReal.toReal_eq_toReal_iff' ?_ ?_).1 h
  · exact ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x => measure_mono (Set.subset_univ B))
      (by simp))
  · exact ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x => measure_mono (Set.subset_univ A))
      (by simp))

/-- The stationary kernel measure is invariant under exchanging its coordinates. -/
theorem compProd_map_swap_eq (hP : Draft.IsDFGWTrajectoryProcess P μ T) (t : ℝ≥0) :
    (μ ⊗ₘ T t).map Prod.swap = μ ⊗ₘ T t := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let : IsMarkovKernel (T t) := hP.markov_kernel t
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply measurable_swap (hA.prod hB)]
  have hs : Prod.swap ⁻¹' (A ×ˢ B) = B ×ˢ A := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, Prod.swap_prod_mk, Set.mem_prod, and_comm]
  rw [hs]
  exact compProd_prod_comm hP t hB hA

end EinsteinFull.External.DFGW
