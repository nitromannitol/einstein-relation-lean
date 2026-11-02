import EinsteinRelation.Correctors.CenteredCorrectorFluxSupport
import EinsteinRelation.Correctors.StationarySpatialRealizationSupport
import Mathlib.Analysis.Convolution

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors

private theorem fderiv_convolution_apply {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) {g : Vec d → ℝ}
    (hg : LocallyIntegrable g volume) (w v : Vec d) :
    (fderiv ℝ ψ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (Vec d),
        volume] g) w v =
      ((fun x => fderiv ℝ ψ x v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) w := by
  have hint : Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL
      (Vec d) (fderiv ℝ ψ t) (g (w - t))) volume :=
    (hψc.fderiv ℝ).convolutionExists_left
      ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (Vec d))
      (hψ.continuous_fderiv (by simp)) hg w
  simp only [convolution_def]
  rw [ContinuousLinearMap.integral_apply hint v]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => rfl

theorem horizontalMollify_horizontalDerivative_formula {d : ℕ} {ζ : Vec d → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    {F : FieldPair d → ℝ} (hF : Measurable F) (hb : ∃ M : ℝ, ∀ ω, |F ω| ≤ M)
    (i : Fin d) (ω : FieldPair d) :
    horizontalDerivative i (horizontalMollify ζ F) ω =
      -∫ x : Vec d, coordinateDerivative i ζ x * F (translate x ω) := by
  obtain ⟨M, hM⟩ := hb
  let g : Vec d → ℝ := fun x => orbit F ω (-x)
  have hg : LocallyIntegrable g volume := by
    have hm : Measurable g := (measurable_orbit hF ω).comp continuous_neg.measurable
    refine (locallyIntegrable_const (μ := volume) M).mono hm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, g, orbit] using
        (hM (translate (-x) ω)).trans (le_abs_self M)
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (mod_cast le_top)
  have hconv := hζc.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hζ1 hg (0 : Vec d)
  have hneg : HasFDerivAt (fun x : Vec d => -x)
      (-ContinuousLinearMap.id ℝ (Vec d)) 0 := (hasFDerivAt_id 0).fun_neg
  have hconv' : HasFDerivAt (fun x => (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
      ((fderiv ℝ ζ ⋆[ContinuousLinearMap.precompL (Vec d)
        (ContinuousLinearMap.lsmul ℝ ℝ), volume] g) 0) (-0) := by
    simpa using hconv
  have hcomp := hconv'.comp 0 hneg
  have hOrbit : orbit (horizontalMollify ζ F) ω =
      fun y : Vec d => (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-y) := by
    funext y
    exact orbit_horizontalMollify_eq_convolution ζ F ω y
  have hconvD := fderiv_convolution_apply hζ1 hζc hg 0 (unitVector i)
  have hfd : fderiv ℝ (fun y : Vec d =>
      (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-y)) 0 =
      ((fderiv ℝ ζ ⋆[ContinuousLinearMap.precompL (Vec d)
        (ContinuousLinearMap.lsmul ℝ ℝ), volume] g) 0).comp
        (-ContinuousLinearMap.id ℝ (Vec d)) := by
    simpa only [Function.comp_def] using hcomp.fderiv
  change coordinateDerivative i (orbit (horizontalMollify ζ F) ω) 0 = _
  rw [hOrbit, coordinateDerivative, hfd]
  rw [ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, map_neg]
  rw [hconvD]
  simp only [convolution_lsmul, smul_eq_mul, coordinateDerivative, g, orbit]
  ring_nf

/-- The actual centered corrector flux has locally square-integrable spatial sections on one
common full-measure event, for every compact spatial set. -/
theorem canonicalCenteredCorrectorFlux_ae_spatial_memLp_on_all_compacts
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x : Vec d => canonicalCenteredCorrectorFlux Q i (translate x ω)) 2
        (volume.restrict K) := by
  exact StationarySpatialRealization.ae_spatialRealization_memLp_on_all_compacts
    (reducedEnvironmentLaw_stationary Q) (canonicalCenteredCorrectorFlux Q i)

private theorem contDiff_coordinateDerivative {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j ψ) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ ψ x (unitVector j))
  exact ((contDiff_infty_iff_fderiv.mp hψ).2).clm_apply contDiff_const

/-- A fixed compactly supported smooth Euclidean test has a genuinely integrable pairing with
the spatial realization of the canonical centered flux for almost every environment. This is
the integrability half of its samplewise distributional divergence statement. -/
theorem canonicalCenteredCorrectorFlux_fixedTest_integrable
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      Integrable (fun x : Vec d => ∑ j : Fin d,
        coordinateDerivative j ψ x * canonicalCenteredCorrectorFlux Q i
          (translate x ω) j) volume := by
  filter_upwards [canonicalCenteredCorrectorFlux_ae_spatial_memLp_on_all_compacts Q i]
    with ω hω
  have hloc : ∀ j : Fin d,
      LocallyIntegrable (fun x : Vec d => canonicalCenteredCorrectorFlux Q i
        (translate x ω) j) volume := by
    intro j
    rw [locallyIntegrable_iff]
    intro K hK
    letI : IsFiniteMeasure (volume.restrict K) :=
      (isFiniteMeasure_restrict).2 hK.measure_ne_top
    have hvec : MemLp (fun x : Vec d => canonicalCenteredCorrectorFlux Q i
        (translate x ω)) 2 (volume.restrict K) := hω K hK
    have hcoord : MemLp (fun x : Vec d => canonicalCenteredCorrectorFlux Q i
        (translate x ω) j) 2 (volume.restrict K) := by
      apply hvec.of_le_mul (c := 1)
      · have hv : Measurable (fun x : Vec d => canonicalCenteredCorrectorFlux Q i
            (translate x ω)) :=
          (Lp.stronglyMeasurable (canonicalCenteredCorrectorFlux Q i)).measurable.comp
            (Probability.continuous_translate.measurable.comp
              (measurable_id.prodMk measurable_const))
        exact (((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j).continuous).measurable.comp
          hv).aestronglyMeasurable
      · filter_upwards [] with x
        simpa only [one_mul] using PiLp.norm_apply_le
          (canonicalCenteredCorrectorFlux Q i (translate x ω)) j
    exact hcoord.integrable (by norm_num)
  apply integrable_finset_sum Finset.univ
  intro j hj
  have hcont : Continuous (coordinateDerivative j ψ) :=
    (contDiff_coordinateDerivative hψ j).continuous
  have hcs : HasCompactSupport (coordinateDerivative j ψ) := by
    simpa only [coordinateDerivative] using! hψc.fderiv_apply ℝ (unitVector j)
  simpa only [smul_eq_mul] using
    (hloc j).integrable_smul_left_of_hasCompactSupport hcont hcs

end EinsteinRelation.Correctors
