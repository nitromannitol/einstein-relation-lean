import EinsteinFull.External.DFGW.FutureStateFactor
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Future cylinder observables

Finite ordered products of state observables and their iterated transition expectations.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A finite ordered product, with successive nonnegative time increments. -/
def futureCylinder : List (ℝ≥0 × (S → ℝ)) → ℝ → C(ℝ, S) → ℝ
  | [], _, _ => 1
  | (t, f) :: xs, s, η => f (η ((t : ℝ) + s)) * futureCylinder xs ((t : ℝ) + s) η

/-- Successive transition expectations of a finite ordered product. -/
noncomputable def futureCylinderKernel (T : ℝ≥0 → Kernel S S) : List (ℝ≥0 × (S → ℝ)) → S → ℝ
  | [], _ => 1
  | (t, f) :: xs, x => ∫ y, f y * futureCylinderKernel T xs y ∂T t x

/-- A cylinder is admissible when each of its state observables is measurable and bounded. -/
def FutureCylinderAdmissible (xs : List (ℝ≥0 × (S → ℝ))) : Prop :=
  ∀ p ∈ xs, Measurable p.2 ∧ ∃ C : ℝ, ∀ x, |p.2 x| ≤ C

/-- Admissible future cylinders and their transition expectations are measurable and bounded. -/
theorem futureCylinder_measurable_bounded (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (xs : List (ℝ≥0 × (S → ℝ))) (hxs : FutureCylinderAdmissible xs) :
    (Measurable (futureCylinderKernel T xs) ∧
      (∃ C : ℝ, ∀ x, |futureCylinderKernel T xs x| ≤ C)) ∧
    ∀ s : ℝ, Measurable (futureCylinder xs s) ∧
      (∃ C : ℝ, ∀ η, |futureCylinder xs s η| ≤ C) := by
  induction xs with
  | nil =>
    constructor
    · exact ⟨measurable_const, ⟨1, fun _ => by simp [futureCylinderKernel]⟩⟩
    · intro s
      exact ⟨measurable_const, ⟨1, fun _ => by simp [futureCylinder]⟩⟩
  | cons p xs ih =>
    obtain ⟨t, f⟩ := p
    have hf := hxs (t, f) (by simp)
    have htail : FutureCylinderAdmissible xs := fun p hp => hxs p (by simp [hp])
    obtain ⟨⟨hkm, C, hC⟩, hpath⟩ := ih htail
    obtain ⟨hfm, D, hD⟩ := hf
    let : IsMarkovKernel (T t) := hP.markov_kernel t
    have hprod : Measurable (fun x => f x * futureCylinderKernel T xs x) := hfm.mul hkm
    have hbound (x : S) : |f x * futureCylinderKernel T xs x| ≤ D * C := by
      rw [abs_mul]
      exact mul_le_mul (hD x) (hC x) (abs_nonneg _) ((abs_nonneg _).trans (hD x))
    constructor
    · constructor
      · exact hprod.stronglyMeasurable.integral_kernel.measurable
      · refine ⟨D * C, fun x => ?_⟩
        have h := norm_integral_le_of_norm_le_const (μ := T t x)
          (f := fun y => f y * futureCylinderKernel T xs y) (C := D * C)
          (ae_of_all _ hbound)
        simpa only [futureCylinderKernel, Real.norm_eq_abs, measureReal_def, measure_univ,
          ENNReal.toReal_one, mul_one] using h
    · intro s
      obtain ⟨hxm, E, hE⟩ := hpath ((t : ℝ) + s)
      constructor
      · exact (hfm.comp (continuous_eval_const _).measurable).mul hxm
      · refine ⟨D * E, fun η => ?_⟩
        change |f (η ((t : ℝ) + s)) * futureCylinder xs ((t : ℝ) + s) η| ≤ D * E
        rw [abs_mul]
        exact mul_le_mul (hD (η ((t : ℝ) + s))) (hE η) (abs_nonneg _)
          ((abs_nonneg (f (η ((t : ℝ) + s)))).trans (hD (η ((t : ℝ) + s))))

end EinsteinFull.External.DFGW
