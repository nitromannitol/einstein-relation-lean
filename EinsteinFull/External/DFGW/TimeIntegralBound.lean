import EinsteinFull.External.DFGW.TimeAverage
import Mathlib.MeasureTheory.Function.L2Space

/-! # Second-moment bound for time-integrated observables

A time integral of a square-integrable stationary observable has second moment at most the
square of elapsed time times the observable's stationary second moment.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

/-- The square of a time integral is bounded by time times the integral of the square. -/
theorem intervalIntegral_sq_le (g : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hg : IntervalIntegrable g volume 0 t)
    (hgsq : IntervalIntegrable (fun u => g u ^ 2) volume 0 t) :
    (∫ u in (0 : ℝ)..t, g u) ^ 2 ≤ t * ∫ u in (0 : ℝ)..t, g u ^ 2 := by
  rcases eq_or_lt_of_le ht with hzero | hpos
  · subst t
    simp
  let I := ∫ u in (0 : ℝ)..t, g u
  let c := I / t
  have hexp : (fun u => (g u - c) ^ 2) =
      (fun u => (g u ^ 2 - (2 * c) * g u) + c ^ 2) := by
    funext u
    ring
  have hnonneg : 0 ≤ ∫ u in (0 : ℝ)..t, (g u - c) ^ 2 :=
    intervalIntegral.integral_nonneg ht (fun _ _ => sq_nonneg _)
  rw [hexp, intervalIntegral.integral_add (hgsq.sub (hg.const_mul _))
    intervalIntegrable_const, intervalIntegral.integral_sub hgsq (hg.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hnonneg
  simp only [sub_zero, smul_eq_mul] at hnonneg
  have hid : t * ((∫ u in (0 : ℝ)..t, g u ^ 2) - 2 * c * I + t * c ^ 2) =
      t * (∫ u in (0 : ℝ)..t, g u ^ 2) - I ^ 2 := by
    dsimp only [c]
    field_simp
    ring
  have hh := mul_nonneg ht hnonneg
  change 0 ≤ t * ((∫ u in (0 : ℝ)..t, g u ^ 2) - 2 * c * I + t * c ^ 2) at hh
  rw [hid] at hh
  exact sub_nonneg.mp hh

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The second moment of an integrated stationary observable is bounded by `t²` times its
stationary second moment. -/
theorem time_integral_memLp_and_sq_le (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (g : S → ℝ) (hg : MemLp g 2 μ) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (fun η : C(ℝ, S) => ∫ u in (0 : ℝ)..t, g (η u)) 2 P ∧
      (∫ η : C(ℝ, S), (∫ u in (0 : ℝ)..t, g (η u)) ^ 2 ∂P) ≤
        t ^ 2 * ∫ x, g x ^ 2 ∂μ := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  have hgint := hg.integrable one_le_two
  have hgsq := hg.integrable_sq
  have hprod := integrable_joint_observable hP g hgint 0 t
  have hprodsq := integrable_joint_observable hP (fun x => g x ^ 2) hgsq 0 t
  have hpath : ∀ᵐ η ∂P, IntervalIntegrable (fun u => g (η u)) volume 0 t ∧
      IntervalIntegrable (fun u => g (η u) ^ 2) volume 0 t := by
    filter_upwards [hprod.prod_left_ae, hprodsq.prod_left_ae] with η hη hηsq
    exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hη,
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hηsq⟩
  have hmean := integral_time_observable hP g hgint ht
  have hmeansq := integral_time_observable hP (fun x => g x ^ 2) hgsq ht
  have hbound : ∀ᵐ η ∂P, (∫ u in (0 : ℝ)..t, g (η u)) ^ 2 ≤
      t * ∫ u in (0 : ℝ)..t, g (η u) ^ 2 := by
    filter_upwards [hpath] with η hη
    exact intervalIntegral_sq_le (fun u => g (η u)) ht hη.1 hη.2
  have hi : Integrable (fun η : C(ℝ, S) => (∫ u in (0 : ℝ)..t, g (η u)) ^ 2) P := by
    apply (hmeansq.1.const_mul t).mono' (hmean.1.aestronglyMeasurable.pow 2)
    filter_upwards [hbound] with η hη
    change ‖(∫ u in (0 : ℝ)..t, g (η u)) ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hη
  constructor
  · exact (memLp_two_iff_integrable_sq hmean.1.aestronglyMeasurable).2 hi
  · have hb := integral_mono_ae hi (hmeansq.1.const_mul t) hbound
    rw [integral_const_mul, hmeansq.2] at hb
    nlinarith

end EinsteinFull.External.DFGW
