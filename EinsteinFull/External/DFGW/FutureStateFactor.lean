import EinsteinFull.External.DFGW.KernelSemigroup
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Factoring a future state from a past observable

The Markov property replaces a future state factor by its transition expectation inside
conditional expectations at earlier times.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- In a conditional expectation at time zero, a later state factor may be replaced by its
transition expectation at the intermediate time. -/
theorem condExp_past_mul_future_state (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (s t : ℝ≥0) (A : C(ℝ, S) → ℝ)
    (hA : StronglyMeasurable[Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] A)
    (hAi : Integrable A P) (g : S → ℝ) (hg : Measurable g)
    (hgb : ∃ C, ∀ x, |g x| ≤ C) :
    P[fun η : C(ℝ, S) => A η * g (η ((t : ℝ) + s)) |
      Draft.dfgwCoordSigma (Set.Iic 0)] =ᵐ[P]
    P[fun η : C(ℝ, S) => A η * ∫ y, g y ∂T t (η s) |
      Draft.dfgwCoordSigma (Set.Iic 0)] := by
  let : IsProbabilityMeasure P := hP.probability
  obtain ⟨C, hC⟩ := hgb
  have hσ : Draft.dfgwCoordSigma (S := S) (Set.Iic 0) ≤
      Draft.dfgwCoordSigma (Set.Iic (s : ℝ)) := by
    apply iSup₂_le
    intro u hu
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Iic (s : ℝ)) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance) u
      (by change u ≤ (s : ℝ); have : u ≤ 0 := hu; linarith [s.coe_nonneg]) le_rfl
  have hσs : Draft.dfgwCoordSigma (S := S) (Set.Iic (s : ℝ)) ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S) := (Draft.dfgwPast (S := S)).le s
  let B : C(ℝ, S) → ℝ := fun η => g (η ((t : ℝ) + s))
  have hB : Integrable B P := Integrable.of_bound
    (hg.comp (continuous_eval_const _).measurable).aestronglyMeasurable C
    (ae_of_all P fun η => by simpa only [B, Real.norm_eq_abs] using hC (η ((t : ℝ) + s)))
  have hAB : Integrable (A * B) P := hAi.mul_bdd
    (hg.comp (continuous_eval_const _).measurable).aestronglyMeasurable
    (ae_of_all P fun η => by simpa only [B, Real.norm_eq_abs, Function.comp_apply] using hC (η ((t : ℝ) + s)))
  have hpull := condExp_mul_of_stronglyMeasurable_left hA hAB hB
  have hmark := condExp_shifted hP (s : ℝ) t g hg ⟨C, hC⟩
  have hstep : P[A * B | Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] =ᵐ[P]
      fun η : C(ℝ, S) => A η * ∫ y, g y ∂T t (η s) := by
    filter_upwards [hpull, hmark] with η hp hm
    simpa only [Pi.mul_apply, B] using hp.trans (congrArg (fun z => A η * z) hm)
  have htower := condExp_condExp_of_le (μ := P) (f := A * B) hσ hσs
  have hcongr := condExp_congr_ae (m := Draft.dfgwCoordSigma (Set.Iic 0)) hstep
  exact htower.symm.trans hcongr

end EinsteinFull.External.DFGW
