import EinsteinRelation.Correctors.AKMPhysicalScalarLocalData
import EinsteinRelation.Correctors.AKMPhysicalScalarSobolev
import EinsteinRelation.Correctors.AffineAnnealedGradient
import EinsteinRelation.Correctors.StationaryOriginMoment
import EinsteinRelation.Correctors.GTFourBallCoefficientSupport
import EinsteinRelation.Mobility.CorrectorGradientMoments
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger
open Environment.AKMTestIntegralSupport ReductionImageV3

/-- Source: `paper/main.tex:727-731`. The actual affine canonical gradient
has all finite moments, using the frozen radius-four AKM and GT estimates. -/
theorem exists_canonicalAffineGradient_moment_bound_of_literature
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h68 : FluxGradientEstimate) (h614 : FluxStationaryEstimate)
    (h615 : FluxPlanarL2Estimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    (d : ℕ) [Fact (2 ≤ d)] (L r₀ p : ℝ)
    (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d),
      (∫⁻ ρ, ENNReal.ofReal (‖correctorUnitVector i +
        (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ρ‖ ^ p)
        ∂reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C := by
  have hd := (Fact.out : 2 ≤ d)
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hB : 0 < sourceReducedBound L := by unfold sourceReducedBound; positivity
  have hΛ : 0 < ((d : ℝ) + 1) * sourceReducedBound L := by positivity
  have hK : 0 < sourceReducedBound L + 3 * (Real.exp (2 * L) * (L + 2 * L ^ 2)) := by
    positivity
  obtain ⟨A, hA, hdata⟩ := exists_physical_scalar_local_L2_data
    h45 h46 h68 h614 h615 hP d L r₀ p hL hr₀ hp
  obtain ⟨B, hBp, hbound⟩ := affine_annealed_local_gradient_moment_of_GT
    h817 h832 h836 d hd (sourceReducedBound L)⁻¹
      (((d : ℝ) + 1) * sourceReducedBound L)
      (sourceReducedBound L + 3 * (Real.exp (2 * L) * (L + 2 * L ^ 2)))
      (1 / 2) p (inv_pos.mpr hB) hΛ hK (by norm_num) (by norm_num) (by linarith)
  refine ⟨B * (max A 0 + 1), by positivity, ?_⟩
  intro Q i
  letI := physicalReferenceLaw_probability Q
  obtain ⟨φ, c, hid, hmoment⟩ := hdata Q i
  let G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
    canonicalCorrectorGradient Q i
  let u : PhysicalField d L → Vec d → ℝ := fun ω x =>
    (2 * r₀) * φ.potential
      (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)
  let g : PhysicalField d L → Vec d → Vec d := fun ω x =>
    (G (translate x (reduce ω.1))).ofLp
  have hcoeff := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (reduced_gt_coefficient_hypotheses_ball_four Q)
  have hweak := ae_physicalAKMPotential_affine_weakSolution Q i φ hid
  have hloc := hbound (physicalReferenceLaw Q) (fun ω => (reduce ω.1).1)
    u g c i A (by
      filter_upwards [hcoeff, hweak] with ω hc hw
      refine ⟨(hc 0).1, (hc 0).2, (hw 0 4 (by norm_num) (c ω)).1, ?_⟩
      simpa [u, g, G] using (hw 0 4 (by norm_num) (c ω)).2) hmoment
  let ν : Measure (Vec d) := volume.restrict (ball 0 1)
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict_euclideanBall 0 1 (by norm_num)
  have hν : ν Set.univ ≠ 0 := by
    simpa only [ν, Measure.restrict_apply_univ] using
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d 1 (by norm_num))).1.ne'
  apply lintegral_origin_rpow_le_of_physical_local_bound
    (physicalReferenceLaw Q) (reducedEnvironmentLaw Q)
    (measurePreserving_physicalReduction Q) (reducedEnvironmentLaw_stationary Q)
    (fun ρ => correctorUnitVector i + G ρ)
    (measurable_const.add (Lp.stronglyMeasurable G).measurable) ν hν p
    (by linarith) (ENNReal.ofReal (B * (max A 0 + 1)))
  convert hloc using 1
  apply lintegral_congr
  intro ω
  apply lintegral_congr
  intro x
  congr 2
  change ‖correctorUnitVector i + G (translate x (reduce ω.1))‖ =
    euclideanNorm (unitVector i + (G (translate x (reduce ω.1))).ofLp)
  rw [TimeChange.euclideanNorm_eq_norm_toLp]
  rfl
  simp [ν]

/-- Source: `paper/main.tex:709-716,727-731`. The gradient assertion of
Lemma 5.1 with precisely the existing production carrier and quantifiers. -/
theorem correctorGradientMoments_of_literature
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h68 : FluxGradientEstimate) (h614 : FluxStationaryEstimate)
    (h615 : FluxPlanarL2Estimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) : CorrectorGradientMoments := by
  intro d hd L r₀ p hp
  letI : Fact (2 ≤ d) := ⟨hd⟩
  by_cases hL : 1 ≤ L
  · by_cases hr₀ : 1 ≤ r₀
    · obtain ⟨C, hC, hmoment⟩ :=
        exists_canonicalAffineGradient_moment_bound_of_literature
          h45 h46 h68 h614 h615 hP h817 h832 h836 d L r₀ p hL hr₀ hp
      refine ⟨2 ^ p * (max C 0 + 1), ?_⟩
      intro Q i
      let G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
        canonicalCorrectorGradient Q i
      have hpoint : ∀ᵐ ρ ∂reducedEnvironmentLaw Q,
          ‖G ρ‖ ≤ 1 * ‖correctorUnitVector i + G ρ‖ + 1 := by
        filter_upwards with ρ
        have hn : ‖correctorUnitVector i‖ = 1 := by simp [correctorUnitVector]
        calc
          _ = ‖(correctorUnitVector i + G ρ) - correctorUnitVector i‖ := by simp
          _ ≤ ‖correctorUnitVector i + G ρ‖ + ‖correctorUnitVector i‖ := norm_sub_le _ _
          _ = _ := by rw [hn, one_mul]
      have hb := lintegral_norm_rpow_le_of_unit_energy (reducedEnvironmentLaw Q)
        (K := 1) (by norm_num) (by linarith : 0 ≤ p)
        (fun ρ => norm_nonneg (correctorUnitVector i + G ρ)) hpoint (hmoment Q i)
      simpa only [StationarySpatialRealization.spatialRealization, translate_zero,
        TimeChange.euclideanNorm_eq_norm_toLp, WithLp.toLp_ofLp,
        Real.one_rpow, one_mul] using hb
    · exact ⟨0, fun Q _ => (hr₀ Q.range_parameter).elim⟩
  · exact ⟨0, fun Q _ => (hL Q.ellipticity_parameter).elim⟩
end EinsteinRelation.Correctors
