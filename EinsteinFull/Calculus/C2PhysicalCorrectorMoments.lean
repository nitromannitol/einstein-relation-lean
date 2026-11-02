import EinsteinFull.Calculus.C2SmoothMomentsSupport
import EinsteinFull.Calculus.C2CanonicalLocalH1
import EinsteinFull.Calculus.C3CanonicalCorrectorSupport
import EinsteinFull.Calculus.C4HalfDirectionCorrector
import EinsteinRelation.Correctors.SpatialAverageDilation
import EinsteinRelation.External.AKMSourceCorrectorIdentification
import EinsteinRelation.Correctors.AKMLocalCorrectorSpecialization

/-! Dependence-range ball energy moments of the canonical physical corrector.
The potential is `2 * r₀ * φ(x / r₀)` for the very same half-direction
source corrector furnished by the checked global producer. -/

open MeasureTheory
noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport ReductionImageV3
open Calculus.C4HalfDirectionCorrector

private theorem euclideanSq_ofLp_eq_norm_sq {d : ℕ}
    (u : EuclideanSpace ℝ (Fin d)) : euclideanSq u.ofLp = ‖u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [euclideanSq, dot, Real.norm_eq_abs, pow_two]

/-- Euclidean RMS gradient on the physical dependence-range ball. -/
def canonicalCorrectorPhysicalBallEnergy {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (z : Vec d) (ω : FieldPair d) : ℝ :=
  Real.sqrt (⨍ x in ball z r₀, euclideanSq
    (((canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
        (translate x ω)).ofLp))

private theorem measurable_physicalBallEnergy {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (z : Vec d) :
    Measurable (canonicalCorrectorPhysicalBallEnergy Q i z) := by
  have ht : Measurable (fun p : FieldPair d × Vec d => translate p.2 p.1) :=
    Probability.continuous_translate.measurable.comp (measurable_snd.prodMk measurable_fst)
  have hg := (Lp.stronglyMeasurable (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))).measurable.comp ht
  unfold canonicalCorrectorPhysicalBallEnergy
  simp only [euclideanSq_ofLp_eq_norm_sq, average_eq, smul_eq_mul]
  exact (measurable_const.mul
    ((hg.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable)).sqrt

/-- Exact same-witness transport: the factor two is in the doubled source
corrector and the physical ball has radius `r₀`. No energy identity is assumed. -/
theorem ae_canonicalCorrectorPhysicalBallEnergy_eq_source
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q,
      canonicalCorrectorPhysicalBallEnergy Q i 0 (reduce ω.1) =
        Real.sqrt (⨍ y in ball 0 1, euclideanSq
          ((doubledCorrector Q i φ).grad
            (project (r₀ := r₀) Q.ellipticity_parameter ω) y)) := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  filter_upwards [hid] with ω hω
  have hi := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
    (inv_ne_zero hr.ne')).ae hω
  have heq : (fun x => euclideanSq (((canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
        (translate x (reduce ω.1))).ofLp)) =ᵐ[volume]
      (fun x => euclideanSq ((doubledCorrector Q i φ).grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x))) := by
    filter_upwards [hi] with x hx
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at hx
    congr 1
    rw [doubledCorrector_grad]
    ext j
    have hj := congrFun hx j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, PiLp.add_apply,
      halfDirection, correctorUnitVector, unitVector, Pi.single_apply] at hj ⊢
    split_ifs at hj ⊢ <;> linarith only [hj]
  unfold canonicalCorrectorPhysicalBallEnergy
  rw [average_congr (ae_restrict_of_ae heq)]
  congr 1
  simpa only [originBall_eq_gt_ball] using average_originBall_inv_smul
    (fun y => euclideanSq ((doubledCorrector Q i φ).grad
      (project (r₀ := r₀) Q.ellipticity_parameter ω) y)) hr

private theorem physicalBallEnergy_translate {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (z : Vec d) (ω : FieldPair d) :
    canonicalCorrectorPhysicalBallEnergy Q i z ω =
      canonicalCorrectorPhysicalBallEnergy Q i 0 (translate z ω) := by
  unfold canonicalCorrectorPhysicalBallEnergy
  congr 1
  simp only [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
  rw [show volume.real (ball z r₀) = volume.real (ball (0 : Vec d) r₀) from
    congrArg ENNReal.toReal (volume_euclideanBall_center z r₀)]
  congr 1
  rw [← (measurePreserving_add_center_ball z r₀).integral_comp
    (MeasurableEquiv.addRight z).measurableEmbedding]
  simp only [translate_add]

/-- Every positive real moment is bounded uniformly in the law, coordinate
and ball center. The checked producer is instantiated internally; its same
half-direction witness has physical potential `2 r₀ φ(r₀⁻¹ x)` and gradient
`2 ∇φ(r₀⁻¹ x)`, as in `ae_canonicalCorrector_physical_localH1`. This is a
prerequisite of smooth moments, with no Schauder or Gaussian claim. -/
theorem canonicalCorrector_physical_ball_energy_moments
    (d : ℕ) (hd : 2 ≤ d) (L p : ℝ) (hL : 1 ≤ L) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (z : Vec d),
      (∫⁻ ω, ENNReal.ofReal
        (canonicalCorrectorPhysicalBallEnergy Q i z (reduce ω.1) ^ p)
          ∂physicalReferenceLaw Q) ≤ ENNReal.ofReal C := by
  let : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨C, hC, hbound⟩ := sourceCorrector_unit_gradient_moments d hd
    (AKMUpperEllipticity L) p (one_lt_AKMUpperEllipticity hL) hp
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i z
  obtain ⟨φ, hid⟩ := exists_akmCorrector_global_gradient_identification_from_pde Q i
  let ψ := (doubledCorrector Q i φ).toSourceCorrector
  have hs := hbound (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q)
    (correctorUnitVector i).ofLp (euclideanNorm_correctorUnitVector i) ψ
  have hm : Measurable (fun a : Coefficient d (AKMUpperEllipticity L) =>
      ENNReal.ofReal ((Real.sqrt (⨍ y in ball 0 1, euclideanSq (ψ.grad a y))) ^ p)) := by
    have hsq : Measurable (fun q : Coefficient d (AKMUpperEllipticity L) × Vec d =>
        euclideanSq (ψ.grad q.1 q.2)) := by
      unfold euclideanSq dot
      exact Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp ψ.measurable_grad).mul
          ((measurable_pi_apply j).comp ψ.measurable_grad)
    simp only [average_eq, smul_eq_mul]
    exact ((measurable_const.mul
      hsq.stronglyMeasurable.integral_prod_right'.measurable).sqrt.pow_const p).ennreal_ofReal
  have hzero : (∫⁻ ω, ENNReal.ofReal
      (canonicalCorrectorPhysicalBallEnergy Q i 0 (reduce ω.1) ^ p)
        ∂physicalReferenceLaw Q) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal ((Real.sqrt (⨍ y in ball 0 1,
          euclideanSq (ψ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y))) ^ p)
            ∂physicalReferenceLaw Q := by
        apply lintegral_congr_ae
        filter_upwards [ae_canonicalCorrectorPhysicalBallEnergy_eq_source Q i φ hid]
          with ω hω
        rw [hω]
        rfl
      _ = _ := (measurePreserving_akmProject Q).lintegral_comp hm
      _ ≤ _ := hs
  have hmE := ((measurable_physicalBallEnergy Q i 0).pow_const p).ennreal_ofReal
  have hred := measurePreserving_physicalReduction Q
  have hshift := EinsteinRelation.measurePreserving_translate (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) z
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (canonicalCorrectorPhysicalBallEnergy Q i z ω ^ p)
        ∂reducedEnvironmentLaw Q := hred.lintegral_comp
          (((measurable_physicalBallEnergy Q i z).pow_const p).ennreal_ofReal)
    _ = ∫⁻ ω, ENNReal.ofReal
        (canonicalCorrectorPhysicalBallEnergy Q i 0 (translate z ω) ^ p)
          ∂reducedEnvironmentLaw Q := by
      apply lintegral_congr
      intro ω
      rw [physicalBallEnergy_translate Q i z ω]
    _ = ∫⁻ ω, ENNReal.ofReal (canonicalCorrectorPhysicalBallEnergy Q i 0 ω ^ p)
        ∂reducedEnvironmentLaw Q := hshift.lintegral_comp hmE
    _ = _ := (hred.lintegral_comp hmE).symm
    _ ≤ _ := hzero

end EinsteinFull
