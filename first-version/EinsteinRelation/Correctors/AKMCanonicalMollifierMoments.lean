import EinsteinRelation.Correctors.AKMPhysicalMollifierMoments
import EinsteinRelation.Correctors.AKMSpatialFluxIdentification
import EinsteinRelation.Correctors.AKMLocalCanonicalIdentificationSourceCell

/-! # Canonical mollifier moments from the actual source identification

Source: `paper/main.tex:948–955`. The canonical production gradient and
centered flux inherit the AKM mollifier estimate on the reduced law. The
source corrector and its spatial identification are explicit internal
obligations; neither is replaced by an extra literature assumption.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The source estimate becomes the coordinate convolution estimate for the
production canonical gradient and centered flux. The same constant works
for every law and every identified source. Source: `paper/main.tex:948–955`. -/
theorem correctorWeakH2_canonical_gradient_flux_moments (hAKM : CorrectorWeakH2)
    (L r₀ m : ℝ) (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw 2 L r₀) (i : Fin 2)
      (φ : Coefficient 2 (AKMUpperEllipticity L) → Vec 2 → ℝ)
      (G : Coefficient 2 (AKMUpperEllipticity L) → Vec 2 → Vec 2),
      IsFirstOrderCorrector (actualCoefficientLaw Q) (halfDirection i) φ G →
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec 2)),
        (2 : ℝ) • (halfDirection i + G (project (r₀ := r₀) Q.ellipticity_parameter ω) x) =
          (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q))
              (translate (r₀ • x) (reduce ω.1))).ofLp) →
      ∀ R : ℝ, 1 ≤ R → ∀ y : Vec 2, euclideanNorm y ≤ R → ∀ j : Fin 2,
        eLpNorm (fun ω => ((fun x => ((canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q))
              (translate x ω)).ofLp j)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            Calculus.unitMassScaledMollifier 2 R) y)
          (ENNReal.ofReal m) (reducedEnvironmentLaw Q) +
        eLpNorm (fun ω => ((fun x => ((canonicalCorrectorFlux Q i (translate x ω)).ofLp -
            (expectedCorrectorFlux Q i).ofLp) j)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            Calculus.unitMassScaledMollifier 2 R) y)
          (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (C * R⁻¹) := by
  obtain ⟨C, hC, hbound⟩ := correctorWeakH2_physicalLaw_gradient_flux_moments
    hAKM L r₀ m hL hr₀ hm
  letI : Fact (2 ≤ 2) := ⟨le_rfl⟩
  have hr : r₀ ≠ 0 := (zero_lt_one.trans_le hr₀).ne'
  have hκ : ellipticityScale L ≠ 0 := (ellipticityScale_pos hL).ne'
  refine ⟨C, hC, ?_⟩
  intro Q i φ G hc hid R hR y hy j
  have hmean : firstOrderMeanFlux (actualCoefficientLaw Q) (halfDirection i) G =
      (ellipticityScale L / 2) • (expectedCorrectorFlux Q i).ofLp :=
    akmLocal_meanFlux_sourceCell_of_canonical_gradient Q i G hc.1.1 hid
  have hflux := ae_akmFlux_eq_scaled_canonicalFlux Q i G hid
  let f : FieldPair 2 → ℝ := fun ω => ((fun x => ((canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q))
        (translate x ω)).ofLp j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier 2 R) y
  let q : FieldPair 2 → ℝ := fun ω => ((fun x =>
      ((canonicalCorrectorFlux Q i (translate x ω)).ofLp -
        (expectedCorrectorFlux Q i).ofLp) j)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier 2 R) y
  have ht : Measurable (fun p : FieldPair 2 × Vec 2 => translate p.2 p.1) :=
    Probability.continuous_translate.measurable.comp measurable_swap
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ))
  have hfg : Measurable (fun p : FieldPair 2 × Vec 2 =>
      ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin 2)) 2
        (reducedEnvironmentLaw Q)) (translate p.2 p.1)).ofLp) :=
    J.continuous.measurable.comp ((Lp.stronglyMeasurable _).measurable.comp ht)
  have hfq : Measurable (fun p : FieldPair 2 × Vec 2 =>
      (canonicalCorrectorFlux Q i (translate p.2 p.1)).ofLp -
        (expectedCorrectorFlux Q i).ofLp) :=
    (J.continuous.measurable.comp
      ((Lp.stronglyMeasurable _).measurable.comp ht)).sub measurable_const
  have hfm : Measurable f :=
    (measurable_random_convolution_joint (fun ω x =>
      ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin 2)) 2
        (reducedEnvironmentLaw Q)) (translate x ω)).ofLp j)
      ((measurable_pi_apply j).comp hfg)
      (Entropy.contDiff_unitMassScaledMollifier R).continuous).comp
        (measurable_const.prodMk measurable_id)
  have hcenter : Measurable (fun ω : FieldPair 2 => (y, ω)) :=
    measurable_const.prodMk measurable_id
  have hqm :=
    (measurable_random_convolution_joint (fun ω x =>
      ((canonicalCorrectorFlux Q i (translate x ω)).ofLp -
        (expectedCorrectorFlux Q i).ofLp) j)
      ((measurable_pi_apply j).comp hfq)
      (Entropy.contDiff_unitMassScaledMollifier R).continuous).comp
        hcenter
  change Measurable q at hqm
  have hfEq : (fun ω : PhysicalField 2 L => ((fun x : Vec 2 => 2 *
      G (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier 2 R) y) =ᵐ[physicalReferenceLaw Q]
      f ∘ (fun ω => reduce ω.1) := by
    filter_upwards [hid] with ω hω
    apply integral_congr_ae
    have hs := (Measure.quasiMeasurePreserving_smul
      (volume : Measure (Vec 2)) (inv_ne_zero hr)).ae hω
    filter_upwards [hs] with x hx
    simp only [smul_smul, mul_inv_cancel₀ hr, one_smul] at hx
    have hj := congrFun hx j
    have hu : 2 * halfDirection i j = (correctorUnitVector i).ofLp j := by
      by_cases hji : j = i <;> simp [halfDirection, correctorUnitVector, unitVector, hji]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, PiLp.add_apply] at hj
    change (2 * G (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j) *
      Calculus.unitMassScaledMollifier 2 R (y - x) = _
    have he : 2 * G (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j =
        ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin 2)) 2
          (reducedEnvironmentLaw Q)) (translate x (reduce ω.1))).ofLp j := by linarith
    rw [he]
    rfl
  have hqEq : (fun ω : PhysicalField 2 L => ((fun x : Vec 2 => (2 / ellipticityScale L) *
      (((project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)).mulVec
        (halfDirection i + G (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)) -
          firstOrderMeanFlux (actualCoefficientLaw Q) (halfDirection i) G) j)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier 2 R) y) =ᵐ[physicalReferenceLaw Q]
      q ∘ (fun ω => reduce ω.1) := by
    filter_upwards [hflux] with ω hω
    apply integral_congr_ae
    have hs := (Measure.quasiMeasurePreserving_smul
      (volume : Measure (Vec 2)) (inv_ne_zero hr)).ae hω
    filter_upwards [hs] with x hx
    simp only [smul_smul, mul_inv_cancel₀ hr, one_smul] at hx
    change ((2 / ellipticityScale L) *
      (((project (r₀ := r₀) Q.ellipticity_parameter ω).field (r₀⁻¹ • x)).mulVec
        (halfDirection i + G (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)) -
          firstOrderMeanFlux (actualCoefficientLaw Q) (halfDirection i) G) j) *
      Calculus.unitMassScaledMollifier 2 R (y - x) =
      (((canonicalCorrectorFlux Q i (translate x (reduce ω.1))).ofLp -
        (expectedCorrectorFlux Q i).ofLp) j) *
          Calculus.unitMassScaledMollifier 2 R (y - x)
    rw [hx, hmean]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hκ]
  have hb := hbound Q (halfDirection i) (halfDirection_mem_ball i).le
    φ G hc R hR y hy j
  rw [eLpNorm_congr_ae hfEq, eLpNorm_congr_ae hqEq,
    eLpNorm_comp_measurePreserving hfm.aestronglyMeasurable
      (measurePreserving_physicalReduction Q),
    eLpNorm_comp_measurePreserving hqm.aestronglyMeasurable
      (measurePreserving_physicalReduction Q)] at hb
  exact hb

end EinsteinRelation.Correctors
