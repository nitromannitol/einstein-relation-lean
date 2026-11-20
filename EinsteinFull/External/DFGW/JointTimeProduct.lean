import EinsteinFull.External.DFGW.TimeIntegralBound
import Mathlib.MeasureTheory.Integral.Prod

/-! # Joint integrability for time-integrated observables

An integrated square-integrable observable times a second stationary observable is integrable
jointly in the trajectory and time variables.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The product of a time-integrated observable and a time-evaluated observable is jointly
integrable. -/
theorem integrable_joint_time_integral_mul (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f g : S → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun z : ℝ × C(ℝ, S) =>
      (∫ u in (0 : ℝ)..t, f (z.2 u)) * g (z.2 z.1))
      ((volume.restrict (Set.Ioc 0 t)).prod P) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 t)
  let A : C(ℝ, S) → ℝ := fun η => ∫ u in (0 : ℝ)..t, f (η u)
  let G : ℝ × C(ℝ, S) → ℝ := fun z => g (z.2 z.1)
  have hA : MemLp A 2 P := (time_integral_memLp_and_sq_le hP f hf ht).1
  have hA1 : Integrable (fun z : ℝ × C(ℝ, S) => A z.2) (ν.prod P) :=
    (hA.integrable one_le_two).comp_snd ν
  have hA2 : Integrable (fun z : ℝ × C(ℝ, S) => (A z.2) ^ 2) (ν.prod P) :=
    hA.integrable_sq.comp_snd ν
  have hAprod : MemLp (fun z : ℝ × C(ℝ, S) => A z.2) 2 (ν.prod P) :=
    (memLp_two_iff_integrable_sq hA1.aestronglyMeasurable).2 hA2
  have hG1 : Integrable G (ν.prod P) := integrable_joint_observable hP g (hg.integrable one_le_two) 0 t
  have hG2 : Integrable (fun z : ℝ × C(ℝ, S) => (G z) ^ 2) (ν.prod P) :=
    integrable_joint_observable hP (fun x => g x ^ 2) hg.integrable_sq 0 t
  have hGprod : MemLp G 2 (ν.prod P) :=
    (memLp_two_iff_integrable_sq hG1.aestronglyMeasurable).2 hG2
  have h := hAprod.integrable_mul hGprod
  exact h.congr (ae_of_all _ fun z => by rfl)

end EinsteinFull.External.DFGW
