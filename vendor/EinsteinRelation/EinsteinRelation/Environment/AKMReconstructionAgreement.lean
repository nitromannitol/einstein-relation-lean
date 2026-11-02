import EinsteinRelation.Environment.AKMContinuousReconstruction
import EinsteinRelation.Correctors.CommonScalarOrbitTests
import EinsteinRelation.Mobility.DriftBoundPointwise
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Agreement of raw coefficients with their measurable reconstruction

Source: `paper/main.tex:693-702`, AKM (0.11). The common spatial-test
argument applies to bounded coefficient entries, although raw point
evaluation is not measurable in the coefficient parameter.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Environment.AKMTestIntegralSupport
open Correctors StationaryCurlRealization ReductionImageV3

/-- The normalized ellipticity hypotheses bound every raw matrix entry
in local L²; spatial measurability follows from local integrability. -/
theorem coefficient_entry_memLp_on_compact {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (a : Coefficient d K) (i j : Fin d) (S : Set (Vec d)) (hS : IsCompact S) :
    MemLp (fun x => a.field x i j) 2 (volume.restrict S) := by
  letI : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
  apply MemLp.of_bound (a.locally_integrable i j).aestronglyMeasurable.restrict K
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]
    have hn (ξ : Vec d) : 0 ≤ euclideanSq ξ := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    exact abs_entry_le_of_quadratic_bounds hK (a.field x) (a.symmetric x)
      (fun ξ => (hn ξ).trans (a.elliptic x ξ).1) (fun ξ => (a.elliptic x ξ).2) i j

private theorem continuous_memLp_on_compact {d : ℕ} (f : Vec d → ℝ)
    (hf : Continuous f) (S : Set (Vec d)) (hS : IsCompact S) :
    MemLp f 2 (volume.restrict S) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  exact ContinuousOn.integrableOn_compact hS (hf.norm.pow 2).continuousOn

/-- Equality of each smooth observation almost surely yields one event
of spatial equality, without requiring jointly measurable raw entries. -/
theorem ae_coefficient_field_eq_reconstruction_of_observations {d : ℕ} (hd : 0 < d)
    {K : ℝ} (hK : 0 ≤ K) (P : Measure (Coefficient d K))
    (R : Coefficient d K → CoefficientField d)
    (hobs : ∀ (u : SmoothCompactTest d) (i j : Fin d), ∀ᵐ a ∂P,
      testIntegral a u i j = ∫ x, u x * R a x i j) :
    ∀ᵐ a ∂P, a.field =ᵐ[volume] (R a : Vec d → Mat d) := by
  let k : Fin d := ⟨0, hd⟩
  have hr (a : Coefficient d K) (i j : Fin d) : Continuous (fun x => R a x i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (R a).continuous)
  have hc (i j : Fin d) : ∀ᵐ a ∂P, ∀ ψ : SpatialTest d,
      (∫ x, (0 : ℝ) * coordinateDerivative k ψ x) =
        -(∫ x, (a.field x i j - R a x i j) * ψ x) := by
    apply SpatialScalar.ae_allTests_of_ae_fixedTest P (fun _ _ => (0 : ℝ))
      (fun a x => a.field x i j - R a x i j) k
    · exact ae_of_all _ fun a S hS => ⟨MemLp.zero,
        (coefficient_entry_memLp_on_compact hK a i j S hS).sub
          (continuous_memLp_on_compact _ (hr a i j) S hS)⟩
    · intro ψ
      let u : SmoothCompactTest d := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport⟩
      filter_upwards [hobs u i j] with a ha
      have haI := integrable_testIntegrand a u i j
      have hRI : Integrable (fun x => ψ x * R a x i j) volume :=
        (hr a i j).locallyIntegrable.integrable_smul_left_of_hasCompactSupport
          ψ.contDiff.continuous ψ.hasCompactSupport
      simp only [zero_mul, integral_zero]
      rw [show (fun x => (a.field x i j - R a x i j) * ψ x) =
          (fun x => ψ x * a.field x i j - ψ x * R a x i j) by funext x; ring,
        integral_sub haI hRI]
      change (0 : ℝ) = -((∫ x, u x * a.field x i j) - ∫ x, u x * R a x i j)
      change (∫ x, u x * a.field x i j) = ∫ x, u x * R a x i j at ha
      rw [ha, sub_self, neg_zero]
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (hc i)] with a ha
  have he (i j : Fin d) : (fun x => a.field x i j - R a x i j) =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((a.locally_integrable i j).sub (hr a i j).locallyIntegrable)
    intro ψ hψ hψc
    have h := ha i j (⟨ψ, hψ, hψc, Set.subset_univ _⟩ : SpatialTest d)
    simp only [zero_mul, integral_zero] at h
    change (0 : ℝ) = -(∫ x, (a.field x i j - R a x i j) * ψ x) at h
    simpa only [neg_eq_zero, Pi.sub_apply, smul_eq_mul, mul_comm] using h.symm
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (he i)] with x hx
  ext i j
  exact sub_eq_zero.mp (hx i j)

/-- Under the actual AKM law the reconstructed continuous field and the
literal raw coefficient agree spatially almost everywhere on one event. -/
theorem ae_actualCoefficientLaw_field_eq_reconstruction {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d) (hR : Measurable R)
    (hReq : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩) :
    ∀ᵐ a ∂actualCoefficientLaw Q, a.field =ᵐ[volume] (R a : Vec d → Mat d) := by
  apply ae_coefficient_field_eq_reconstruction_of_observations
    (lt_of_lt_of_le (by norm_num : 0 < 2) (Fact.out : 2 ≤ d))
    (by unfold AKMUpperEllipticity
        exact mul_nonneg (ellipticityScale_pos Q.ellipticity_parameter).le
          (ellipticityScale_pos Q.ellipticity_parameter).le) (actualCoefficientLaw Q) R
  intro u i j
  have he : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      R p.1 p.2 i j) := by
    have hc : Continuous (fun p : CoefficientField d × Vec d => p.1 p.2 i j) := by fun_prop
    exact hc.measurable.comp ((hR.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun a => ∫ x, u x * R a x i j) :=
    ((u.smooth.continuous.measurable.comp measurable_snd).mul he).stronglyMeasurable.integral_prod_right.measurable
  apply (ae_map_iff (measurable_project Q.ellipticity_parameter).aemeasurable
    (measurableSet_eq_fun (measurable_testIntegral u i j) hm)).mpr
  exact ae_of_all _ fun ω => by
    have hc : Continuous (project (r₀ := r₀) Q.ellipticity_parameter ω).field := by
      change Continuous (fun x => ellipticityScale L • reducedCoefficient ω.1 (r₀ • x))
      exact (((Real.continuous_exp.comp (continuous_const.mul ω.1.2.continuous)).smul
        ω.1.1.continuous).const_smul (ellipticityScale L)).comp (continuous_id.const_smul r₀)
    rw [hReq _ hc]
    rfl

end EinsteinRelation.Environment.AKMTestIntegralSupport
