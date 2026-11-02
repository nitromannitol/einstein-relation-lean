import EinsteinFull.Calculus.C13TubeWeightedRenormalization
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- A continuously differentiable function of a forward average is absolutely
continuous on an interior interval. -/
theorem c11_C1_forward_average_interval_absolutelyContinuous
    {a b c e h : ℝ} (hac : a < c) (hce : c ≤ e) (heb : e + h < b)
    (hh : 0 ≤ h) (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioo a b) volume)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) :
    AbsolutelyContinuousOnInterval
      (fun t => F (h⁻¹ * (∫ s in (0 : ℝ)..h, f (t + s)))) c e := by
  let g := (Set.Ioo a b).indicator f
  have hg : Integrable g volume := hf.integrable_indicator measurableSet_Ioo
  have hv : AbsolutelyContinuousOnInterval
      (fun t => h⁻¹ * (∫ s in (0 : ℝ)..h, f (t + s))) c e := by
    apply ((c18_forward_integral_absolutelyContinuous hg.locallyIntegrable h c e).const_mul h⁻¹).congr
    intro t ht
    have ht' : t ∈ Set.Icc c e := by simpa [Set.uIcc_of_le hce] using ht
    apply congrArg (fun z : ℝ => h⁻¹ * z)
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) h := by simpa [Set.uIcc_of_le hh] using hs
    have hts : t + s ∈ Set.Ioo a b := by constructor <;> linarith [ht'.1, ht'.2, hs'.1, hs'.2]
    exact Set.indicator_of_mem hts f
  obtain ⟨C, hC⟩ := hv.exists_bound
  obtain ⟨K, hK⟩ := hF.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_Icc (-C) C) isCompact_Icc
  apply hK.comp_absolutelyContinuousOnInterval ?_ hv
  intro t ht
  have htC := hC t ht
  rw [Real.norm_eq_abs, abs_le] at htC
  exact htC

/-- Integration by parts for a C¹ nonlinearity of the density-weighted
forward time average. -/
theorem c11_weighted_C1_forward_average_integration_by_parts
    {a b c e h : ℝ} (hac : a < c) (hce : c ≤ e) (heb : e + h < b)
    (hh : 0 ≤ h) (ρ : ℝ) (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioo a b) volume)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (ψ : ℝ → ℝ)
    (hψ : AbsolutelyContinuousOnInterval ψ c e) (hc : ψ c = 0) (he : ψ e = 0) :
    (∫ t in c..e, (ρ * F (h⁻¹ * (∫ s in (0 : ℝ)..h, f (t + s)))) * deriv ψ t) =
      -∫ t in c..e, (ρ * (deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, f (t + s))) *
        (h⁻¹ * (f (t + h) - f t)))) * ψ t := by
  let v : ℝ → ℝ := fun t => ρ * F (h⁻¹ * (∫ s in (0 : ℝ)..h, f (t + s)))
  have hv := (c11_C1_forward_average_interval_absolutelyContinuous hac hce heb hh f hf F hF).const_mul ρ
  have hparts := hv.integral_mul_deriv_eq_deriv_mul hψ
  have heq : (∫ t in c..e, deriv v t * ψ t) =
      ∫ t in c..e, (ρ * (deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, f (t + s))) *
        (h⁻¹ * (f (t + h) - f t)))) * ψ t := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le hce]
    apply (ae_restrict_iff' measurableSet_Ioc).mp
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [c13_weighted_forward_average_chain_interval_ae a b c e ρ h
      hac.le heb.le hh f hf F hF] with t ht
    rw [ht.deriv]
  rw [heq, hc, he] at hparts
  simpa [v] using hparts

/-- Integration by parts on almost every spatial slice for a C² nonlinearity
and a smooth spacetime test. -/
theorem c11_weighted_caloric_spacetime_C2_set_integration_by_parts_ae
    {d : ℕ} {a b c e h r : ℝ} (hac : a < c) (hce : c ≤ e)
    (heb : e + h < b) (hh : 0 ≤ h)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (ψ : ℝ × Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo c e ×ˢ sourceBall y r) :
    ∀ᵐ x ∂volume.restrict (sourceBall y r),
      (∫ t in Set.Ioo c e, (ρ x * F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (t + s, x)))) *
        deriv (fun q => ψ (q, x)) t) =
        -∫ t in Set.Ioo c e, (ρ x * (deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (t + s, x))) *
          (h⁻¹ * (u (t + h, x) - u (t, x))))) * ψ (t, x) := by
  haveI : IsFiniteMeasure (volume.restrict (sourceBall y r)) :=
    isFiniteMeasure_restrict.mpr (c18_sourceBall_measure_ne_top y r)
  have hf : IsFiniteMeasure ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall y r))) := inferInstance
  have hf' : IsFiniteMeasure (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
    rwa [Measure.prod_restrict] at hf
  haveI := hf'
  have hi : Integrable u ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall y r))) := by
    rw [Measure.prod_restrict]
    exact memLp_one_iff_integrable.mp (hu.1.mono_exponent (by norm_num))
  filter_upwards [hi.prod_left_ae] with x hx
  have hs : ContDiff ℝ 1 (fun t => ψ (t, x)) :=
    (hψ.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  have hc : ψ (c, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    exact (lt_irrefl c) (hsp hm).1.1
  have he : ψ (e, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    exact (lt_irrefl e) (hsp hm).1.2
  have hparts := c11_weighted_C1_forward_average_integration_by_parts hac hce heb hh
    (ρ x) (fun t => u (t, x)) hx F (hF.of_le (by norm_num)) (fun t => ψ (t, x))
    hs.contDiffOn.absolutelyContinuousOnInterval hc he
  simpa only [intervalIntegral.integral_of_le hce, ← restrict_Ioo_eq_restrict_Ioc] using hparts

end EinsteinFull.Calculus
