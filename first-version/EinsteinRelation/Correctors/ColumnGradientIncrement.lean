import EinsteinRelation.Correctors.ReducedGradientIncrement
import EinsteinRelation.Correctors.ColumnEuclideanInitialEnergy
import EinsteinRelation.Correctors.AKMActualPairedEnergyTrace

/-! # Actual column increments in stationary L2

Source: `paper/main.tex:800–808`. Initial energy, spatial membership and
coordinate identities are derived from the specified actual flow. The
only estimate to instantiate is its sharp local RMS decay.
-/

open MeasureTheory Set
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Sharp local gradient RMS decay bounds the difference of actual
stationary zero-based column integrals. Source: `paper/main.tex:800–808`. -/
theorem column_gradient_increment_bound
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hG : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G p.1 p.2))
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    {C α T S : ℝ} (hC : 0 < C) (hα : 0 < α) (hT : 1 ≤ T) (hTS : T ≤ S)
    (hdecay : ∀ t : ℝ, 1 ≤ t →
      eLpNorm (fun A => vectorRms volume (originBall d 1) (fun x => G A (t,x))) 2
        (actualCoefficientLaw Q) ≤ ENNReal.ofReal (C*t^(-1-α)))
    (YS YT : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (heS : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (YS (translate x (reduce ω.1))).ofLp = fun j => ∫ t in Ioo 0 S,
        G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) j)
    (heT : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (YT (translate x (reduce ω.1))).ofLp = fun j => ∫ t in Ioo 0 T,
        G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) j) :
    ‖YS-YT‖ ≤ (C/α)*T^(-α) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hS0 : 0 < S := hT0.trans_le hTS
  have hK : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  have hr : r₀ ≠ 0 := (zero_lt_one.trans_le Q.range_parameter).ne'
  have hv := ENNReal.toReal_pos_iff.mp (show 0 < (volume (originBall d 1)).toReal by
    simpa only [originBall,ball,sub_zero] using ball_volume_pos_finite d 1 zero_lt_one)
  let ν : Measure (Vec d) := (volume (originBall d 1))⁻¹ • volume.restrict (originBall d 1)
  letI : IsProbabilityMeasure ν := ⟨by
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hv.1.ne' hv.2.ne⟩
  have hν : ν ≪ volume :=
    Measure.smul_absolutelyContinuous.trans (Measure.restrict_le_self.absolutelyContinuous)
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hJG : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => J (G p.1 p.2)) := J.continuous.measurable.comp hG
  have hfinite : ∀ᵐ A ∂actualCoefficientLaw Q, MemLp (fun z => J (G A z)) 2
      ((volume.restrict (Ioo 0 S)).prod ν) := by
    filter_upwards [hflow,ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow]
      with A hA hb
    exact semigroup_initial_euclidean_energy hK hA.1
      (hG.comp (measurable_const.prodMk measurable_id)) hb hS0 zero_lt_one
  have hsections : ∀ᵐ A ∂actualCoefficientLaw Q,
      ∀ᵐ t ∂volume.restrict (Ioi T), MemLp (fun x => J (G A (t,x))) 2 ν := by
    filter_upwards [hflow] with A hA
    have hs := semigroupSolution_gradient_tail_slice_memLp hA.1
      (hG.comp (measurable_const.prodMk measurable_id)) hT0 zero_lt_one
    filter_upwards [hs] with t ht
    exact J.toContinuousLinearMap.comp_memLp' (ht.smul_measure (ENNReal.inv_ne_top.mpr hv.1.ne'))
  have hsq (v : Vec d) : ‖J v‖^2 = euclideanSq v := by
    change ‖WithLp.toLp 2 v‖^2 = _
    rw [← TimeChange.euclideanNorm_eq_norm_toLp]
    exact Real.sq_sqrt (euclideanSq_nonneg_fisher _)
  have hb : ∀ᵐ t ∂volume.restrict (Ioi T),
      eLpNorm (fun A => Real.sqrt (∫ x, ‖J (G A (t,x))‖^2 ∂ν)) 2
        (actualCoefficientLaw Q) ≤ ENNReal.ofReal (C*t^(-1-α)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    simpa only [hsq, vectorRms,setAverage_eq'] using hdecay t (hT.trans ht.le)
  have hcoord : ∀ᵐ A ∂actualCoefficientLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ τ : ℝ, τ ≤ S → (∫ t in Ioo 0 τ, J (G A (t,x))).ofLp =
        fun j => ∫ t in Ioo 0 τ, G A (t,x) j := by
    filter_upwards [hflow,ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow]
      with A hA hAb
    exact semigroup_initial_euclidean_coordinates hK hA.1
      (hG.comp (measurable_const.prodMk measurable_id)) hAb hS0
  apply reduced_gradient_increment_bound Q ν hν (fun A z => J (G A z)) hJG
    hC hα hT0 hTS hfinite hsections hb YS YT
  filter_upwards [heS,heT,(measurePreserving_akmProject Q).quasiMeasurePreserving.ae hcoord]
    with ω hωS hωT hωc
  filter_upwards [(Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) hr).ae hωS,
    (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) hr).ae hωT,hωc]
    with x hxS hxT hxc
  have hxS' : (YS (translate (r₀ • x) (reduce ω.1))).ofLp =
      fun j => ∫ t in Ioo 0 S, G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,x) j := by
    simpa only [smul_smul,inv_mul_cancel₀ hr,one_smul] using hxS
  have hxT' : (YT (translate (r₀ • x) (reduce ω.1))).ofLp =
      fun j => ∫ t in Ioo 0 T, G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,x) j := by
    simpa only [smul_smul,inv_mul_cancel₀ hr,one_smul] using hxT
  apply WithLp.ofLp_injective
  change (YS (translate (r₀ • x) (reduce ω.1))).ofLp -
    (YT (translate (r₀ • x) (reduce ω.1))).ofLp = _
  rw [hxS',hxT',WithLp.ofLp_sub,hxc S le_rfl,hxc T hTS]

end EinsteinRelation.Correctors
