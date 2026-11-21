import EinsteinFull.External.DFGW.ShiftedMarkov
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Chapman–Kolmogorov identity

The Markov property and stationarity imply the transition composition law almost everywhere
with respect to the stationary marginal.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Chapman–Kolmogorov for a bounded measurable observable, at almost every initial state. -/
theorem kernel_integral_add_ae (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (s t : ℝ≥0) (f : S → ℝ) (hf : Measurable f)
    (hfb : ∃ C, ∀ x, |f x| ≤ C) :
    (fun x => ∫ z, (∫ y, f y ∂T t z) ∂T s x) =ᵐ[μ]
      fun x => ∫ y, f y ∂T (s + t) x := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsMarkovKernel (T t) := hP.markov_kernel t
  let : IsMarkovKernel (T s) := hP.markov_kernel s
  let : IsMarkovKernel (T (s + t)) := hP.markov_kernel (s + t)
  obtain ⟨C, hC⟩ := hfb
  let F : S → ℝ := fun x => ∫ y, f y ∂T t x
  have hF : Measurable F := (hf.stronglyMeasurable.integral_kernel (κ := T t)).measurable
  have hFb : ∃ C, ∀ x, |F x| ≤ C := by
    refine ⟨C, fun x => ?_⟩
    have h := norm_integral_le_of_norm_le_const (μ := T t x) (f := f) (C := C)
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hC y)
    simpa only [F, Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
      mul_one] using h
  have hσ : Draft.dfgwCoordSigma (S := S) (Set.Iic 0) ≤
      Draft.dfgwCoordSigma (Set.Iic (s : ℝ)) := by
    apply iSup₂_le
    intro u hu
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Iic (s : ℝ)) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance) u
      (by change u ≤ (s : ℝ); have : u ≤ 0 := hu; linarith [s.coe_nonneg]) le_rfl
  have hσs : Draft.dfgwCoordSigma (S := S) (Set.Iic (s : ℝ)) ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S) := (Draft.dfgwPast (S := S)).le s
  have hshift := condExp_shifted hP (s : ℝ) t f hf ⟨C, hC⟩
  have hcongr := condExp_congr_ae (m := Draft.dfgwCoordSigma (S := S) (Set.Iic 0)) hshift
  have htower := condExp_condExp_of_le (μ := P)
    (f := fun η : C(ℝ, S) => f (η ((t : ℝ) + s))) hσ hσs
  have hsum := hP.markov (s + t) f hf ⟨C, hC⟩
  have hcomp := hP.markov s F hF hFb
  have heval : (fun η : C(ℝ, S) =>
      ∫ z, F z ∂T s (η 0)) =ᵐ[P] fun η => ∫ y, f y ∂T (s + t) (η 0) := by
    have hsum' : P[fun η : C(ℝ, S) => f (η ((t : ℝ) + s)) |
        Draft.dfgwCoordSigma (Set.Iic 0)] =ᵐ[P]
        fun η => ∫ y, f y ∂T (s + t) (η 0) := by
      simpa only [NNReal.coe_add, add_comm] using hsum
    exact hcomp.symm.trans (hcongr.symm.trans (htower.trans hsum'))
  have hleft : Measurable fun x => ∫ z, F z ∂T s x :=
    (hF.stronglyMeasurable.integral_kernel (κ := T s)).measurable
  have hright : Measurable fun x => ∫ y, f y ∂T (s + t) x :=
    (hf.stronglyMeasurable.integral_kernel (κ := T (s + t))).measurable
  have he : Measurable (fun η : C(ℝ, S) => η 0) := (continuous_eval_const 0).measurable
  rw [← hP.marginal 0]
  exact (ae_map_iff he.aemeasurable (measurableSet_eq_fun hleft hright)).2 heval

end EinsteinFull.External.DFGW
