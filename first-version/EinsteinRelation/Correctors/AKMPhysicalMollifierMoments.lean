import EinsteinRelation.Correctors.AKMPhysicalScaleMoments
import EinsteinRelation.Correctors.AKMFluxConvolutionMeasurability
import EinsteinRelation.Correctors.MollifierDilationTransport
import EinsteinRelation.Correctors.AKMCarrierIdentificationTransport
import EinsteinRelation.Correctors.AKMLocalCorrectorSpecialization

/-! # Physical gradient and centered-flux mollifier moments

Source: `paper/main.tex:789–810,948–955`. The actual source gradient and
centered flux are pulled back to the physical law, with amplitudes `2` and
`2 / ellipticityScale L`. Their estimates cover every physical radius.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Moment transport of a literal dilated mollifier convolution along a
measure-preserving map. Source: `paper/main.tex:789–810,948–955`. -/
theorem eLpNorm_mollifier_dilation_comp_measurePreserving
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {d : ℕ} {μ : Measure Ω} {ν : Measure A} {T : Ω → A}
    (hT : MeasurePreserving T μ ν) (f : A → Vec d → ℝ)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (c : ℝ) (y : Vec d)
    (p : ENNReal)
    (hf : AEStronglyMeasurable (fun a => (f a
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier d (R / r)) (r⁻¹ • y)) ν) :
    eLpNorm (fun ω => ((fun x => c * f (T ω) (r⁻¹ • x))
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier d R) y) p μ =
      ‖c‖ₑ * eLpNorm (fun a => (f a
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier d (R / r)) (r⁻¹ • y)) p ν := by
  simp_rw [convolution_mollifier_dilation _ hr hR c y]
  change eLpNorm (c • ((fun a => (f a
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier d (R / r)) (r⁻¹ • y)) ∘ T)) p μ = _
  rw [eLpNorm_const_smul, eLpNorm_comp_measurePreserving hf hT]

/-- The physical source gradient and centered flux have `C/R` coordinate
mollifier moments, with the constant preceding the law, direction and source
potential. Source: `paper/main.tex:948–955`. -/
theorem correctorWeakH2_physicalLaw_gradient_flux_moments (hAKM : CorrectorWeakH2)
    (L r₀ m : ℝ) (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw 2 L r₀,
      ∀ e : Vec 2, euclideanNorm e ≤ 1 →
        ∀ (φ : Coefficient 2 (AKMUpperEllipticity L) → Vec 2 → ℝ)
          (G : Coefficient 2 (AKMUpperEllipticity L) → Vec 2 → Vec 2),
          IsFirstOrderCorrector (actualCoefficientLaw Q) e φ G →
            ∀ R : ℝ, 1 ≤ R → ∀ y : Vec 2, euclideanNorm y ≤ R → ∀ j : Fin 2,
              eLpNorm (fun ω : PhysicalField 2 L => ((fun x : Vec 2 => 2 *
                  G (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j)
                ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
                  Calculus.unitMassScaledMollifier 2 R) y)
                (ENNReal.ofReal m) (physicalReferenceLaw Q) +
              eLpNorm (fun ω : PhysicalField 2 L => ((fun x : Vec 2 => (2 / ellipticityScale L) *
                  (((project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)).mulVec
                    (e + G (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)) -
                      firstOrderMeanFlux (actualCoefficientLaw Q) e G) j)
                ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
                  Calculus.unitMassScaledMollifier 2 R) y)
                (ENNReal.ofReal m) (physicalReferenceLaw Q) ≤ ENNReal.ofReal (C * R⁻¹) := by
  obtain ⟨C, hC, hbound⟩ := correctorWeakH2_physical_scale_gradient_flux_moments
    hAKM (AKMUpperEllipticity L) 1 m r₀ hr₀ (one_lt_AKMUpperEllipticity hL)
      (by norm_num) (by norm_num) hm
  have hr : 0 < r₀ := zero_lt_one.trans_le hr₀
  have hκ : 0 < ellipticityScale L := ellipticityScale_pos hL
  let M : ℝ := max 2 (2 / ellipticityScale L)
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨M * C, by positivity, ?_⟩
  intro Q e he φ G hc R hR y hy j
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hζ : Continuous (Calculus.unitMassScaledMollifier 2 (R / r₀)) :=
    (Entropy.contDiff_unitMassScaledMollifier _).continuous
  have hgm : Measurable (fun A => ((fun x => G A x j)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier 2 (R / r₀)) (r₀⁻¹ • y)) :=
    (measurable_random_convolution_joint (fun A x => G A x j)
      ((measurable_pi_apply j).comp hc.1.1) hζ).comp
        (measurable_const.prodMk measurable_id)
  have hcenter : Measurable (fun A : Coefficient 2 (AKMUpperEllipticity L) =>
      (r₀⁻¹ • y, A)) := measurable_const.prodMk measurable_id
  have hqm := (measurable_rawFlux_convolution_joint
    (d := 2) (K := AKMUpperEllipticity L) G hc.1.1 e
      (firstOrderMeanFlux (actualCoefficientLaw Q) e G) j hζ).comp hcenter
  have hgnorm := eLpNorm_mollifier_dilation_comp_measurePreserving
    (measurePreserving_akmProject Q) (fun A x => G A x j)
    (r := r₀) (R := R) hr hR0 2 y (ENNReal.ofReal m) hgm.aestronglyMeasurable
  have hqnorm := eLpNorm_mollifier_dilation_comp_measurePreserving
    (measurePreserving_akmProject Q)
    (fun (A : Coefficient 2 (AKMUpperEllipticity L)) x => ((A.field x).mulVec (e + G A x) -
      firstOrderMeanFlux (actualCoefficientLaw Q) e G) j)
    (r := r₀) (R := R) hr hR0 (2 / ellipticityScale L) y
    (ENNReal.ofReal m) hqm.aestronglyMeasurable
  rw [hgnorm, hqnorm,
    Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2),
    Real.enorm_eq_ofReal (div_nonneg (by norm_num) hκ.le)]
  have hb := hbound (actualCoefficientLaw Q) (isAdmissibleLaw_actualCoefficientLaw Q)
    e he φ G hc R hR y hy j
  let a := eLpNorm (fun A => ((fun x => G A x j)
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Calculus.unitMassScaledMollifier 2 (R / r₀)) (r₀⁻¹ • y))
        (ENNReal.ofReal m) (actualCoefficientLaw Q)
  let b := eLpNorm (fun A : Coefficient 2 (AKMUpperEllipticity L) => ((fun x =>
    ((A.field x).mulVec (e + G A x) - firstOrderMeanFlux (actualCoefficientLaw Q) e G) j)
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Calculus.unitMassScaledMollifier 2 (R / r₀)) (r₀⁻¹ • y))
        (ENNReal.ofReal m) (actualCoefficientLaw Q)
  change ENNReal.ofReal 2 * a + ENNReal.ofReal (2 / ellipticityScale L) * b ≤ _
  change a + b ≤ ENNReal.ofReal (C * R⁻¹) at hb
  have h2 : ENNReal.ofReal 2 ≤ ENNReal.ofReal M :=
    ENNReal.ofReal_le_ofReal (le_max_left 2 (2 / ellipticityScale L))
  have hscale : ENNReal.ofReal (2 / ellipticityScale L) ≤ ENNReal.ofReal M :=
    ENNReal.ofReal_le_ofReal (le_max_right 2 (2 / ellipticityScale L))
  calc
    ENNReal.ofReal 2 * a + ENNReal.ofReal (2 / ellipticityScale L) * b ≤
        ENNReal.ofReal M * a + ENNReal.ofReal M * b :=
      add_le_add (mul_le_mul_left h2 a) (mul_le_mul_left hscale b)
    _ = ENNReal.ofReal M * (a + b) := (mul_add _ _ _).symm
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal (C * R⁻¹) := mul_le_mul_right hb _
    _ = ENNReal.ofReal ((M * C) * R⁻¹) := by
      rw [← ENNReal.ofReal_mul hM.le, mul_assoc]

end EinsteinRelation.Correctors
