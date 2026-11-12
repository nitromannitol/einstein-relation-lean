import EinsteinRelation.Correctors.CanonicalColumnRmsRemainderAeDecay
import EinsteinRelation.Correctors.SpecifiedColumnCopyEstimates
import EinsteinRelation.Correctors.CoupledSpatialRms
import EinsteinRelation.Correctors.UniformInitialEnergy

/-! # Coupled spatial energy of the canonical gradient

Source: `paper/main.tex:842–854`. The actual finite-time paired column
and both marginal remainders control the stationary canonical gradient.
All time integrals retain their actual initial energy classes.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3
open NormalizedSpatialRepresentativeSupport

/-- The actual finite-time column integral is spatially L2. Its time
sections are integrable through zero. Source: `paper/main.tex:842–849`. -/
theorem physical_column_time_integral_data
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hG : Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G z.1 z.2))
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) :
    let ν : Measure (Vec d) := (volume (originBall d ρ))⁻¹ • volume.restrict (originBall d ρ)
    ∀ᵐ ω ∂physicalReferenceLaw Q,
      MemLp (fun x => ∫ t in Ioo 0 T, (WithLp.toLp 2
        (G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,x)) :
          EuclideanSpace ℝ (Fin d))) 2 ν ∧
      ∀ᵐ x ∂ν, IntegrableOn
        (fun t => G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,x)) (Ioo 0 T) := by
  dsimp only
  let ν : Measure (Vec d) := (volume (originBall d ρ))⁻¹ • volume.restrict (originBall d ρ)
  have hv := ENNReal.toReal_pos_iff.mp (show 0 < (volume (originBall d ρ)).toReal by
    simpa only [originBall,ball,sub_zero] using ball_volume_pos_finite d ρ hρ)
  letI : IsProbabilityMeasure ν := ⟨by
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hv.1.ne' hv.2.ne⟩
  have hK : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  have hactual : ∀ᵐ A ∂actualCoefficientLaw Q,
      MemLp (fun x => ∫ t in Ioo 0 T,
        (WithLp.toLp 2 (G A (t,x)) : EuclideanSpace ℝ (Fin d))) 2 ν ∧
      ∀ᵐ x ∂ν, IntegrableOn (fun t => G A (t,x)) (Ioo 0 T) := by
    filter_upwards [hflow,ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow]
      with A hA hb
    have he := semigroup_initial_euclidean_energy hK hA.1
      (hG.comp (measurable_const.prodMk measurable_id)) hb hT hρ
    refine ⟨(time_integral_memLp_two ν hT.le he).1,?_⟩
    filter_upwards [(he.integrable (by norm_num)).prod_left_ae] with x hx
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.integrable_comp_iff.mp hx
  exact (measurePreserving_akmProject Q).quasiMeasurePreserving.ae hactual

/-- Difference of finite-time Euclidean column integrals has exactly the
spatial RMS appearing in the checked paired-flow estimate. Integrability
through zero justifies subtraction inside the time integral.
Source: `paper/main.tex:842–849`. -/
theorem physical_paired_time_integral_rms
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hG : Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G z.1 z.2))
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) (R : ℝ) (y : Point d) :
    let ν : Measure (Vec d) := (volume (originBall d ρ))⁻¹ • volume.restrict (originBall d ρ)
    let H := fun (ω : PhysicalField d L) (x : Vec d) =>
      ∫ t in Ioo 0 T, (WithLp.toLp 2
        (G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,x)) : EuclideanSpace ℝ (Fin d))
    ∀ᵐ z ∂recenteredPhysicalCopyLaw Q R y,
      MemLp (fun x => H z.1 x-H z.2 x) 2 ν ∧
      Real.sqrt (∫ x, ‖H z.1 x-H z.2 x‖^2 ∂ν) =
        vectorRms volume (originBall d ρ) (fun x => ∫ t in Icc 0 T,
          G (project (r₀ := r₀) Q.ellipticity_parameter z.1) (t,x) -
          G (project (r₀ := r₀) Q.ellipticity_parameter z.2) (t,x)) := by
  dsimp only
  obtain ⟨_,_,hfst,hsnd,_⟩ := recenteredPhysicalCopy_properties Q R y
  have hh := physical_column_time_integral_data Q i u G hG hflow hT hρ
  filter_upwards [hfst.quasiMeasurePreserving.ae hh,hsnd.quasiMeasurePreserving.ae hh]
    with z h₁ h₂
  refine ⟨h₁.1.sub h₂.1,?_⟩
  unfold vectorRms
  rw [setAverage_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards [h₁.2,h₂.2] with x hx₁ hx₂
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  change ‖(∫ t in Ioo 0 T, J (G _ (t,x)))-(∫ t in Ioo 0 T, J (G _ (t,x)))‖^2 = _
  rw [J.integral_comp_comm,J.integral_comp_comm,← J.map_sub,
    ← integral_sub hx₁ hx₂,← integral_Icc_eq_integral_Ioo]
  change ‖WithLp.toLp 2 _‖^2 = _
  rw [← TimeChange.euclideanNorm_eq_norm_toLp]
  exact Real.sq_sqrt (euclideanSq_nonneg_fisher _)

/-- The actual canonical gradient has the sharp coupled spatial energy
rate on the double ball. No stationary identification, time-zero energy,
or marginal tail estimate is assumed. The constant precedes the law,
column, specified flow, radius and center.
Source: `paper/main.tex:842–854`. -/
theorem canonical_gradient_paired_spatial_decay
    (hdecay : ParabolicSemigroupKernelDecay) (hreg : ParabolicLargeScale)
    (d : ℕ) (hd : 2 ≤ d) (L r₀ m : ℝ) (hL : 1 ≤ L) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
      (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => u z.1 z.2) →
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => G z.1 z.2) →
      (∀ᵐ A ∂actualCoefficientLaw Q,
        IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
        HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) →
      (∀ᵐ A ∂actualCoefficientLaw Q, ∀ t : ℝ, 0 < t →
        HasWeakGradient univ (fun x => u A (t,x)) (fun x => G A (t,x))) →
      ∀ R : ℝ, 1 ≤ R → ∀ y : Point d,
      let ν : Measure (Vec d) :=
        (volume (originBall d (2*R)))⁻¹ • volume.restrict (originBall d (2*R))
      let F := fun (ω : PhysicalField d L) (x : Vec d) =>
        (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • x) (reduce ω.1))
      (∀ᵐ z ∂recenteredPhysicalCopyLaw Q (r₀*R) y,
        MemLp (fun x => F z.1 x-F z.2 x) 2 ν) ∧
      MemLp (fun z => Real.sqrt (∫ x, ‖F z.1 x-F z.2 x‖^2 ∂ν))
        (ENNReal.ofReal m) (recenteredPhysicalCopyLaw Q (r₀*R) y) ∧
      eLpNorm (fun z => Real.sqrt (∫ x, ‖F z.1 x-F z.2 x‖^2 ∂ν))
        (ENNReal.ofReal m) (recenteredPhysicalCopyLaw Q (r₀*R) y) ≤
          ENNReal.ofReal (C*R^(-(d : ℝ)/2)) := by
  obtain ⟨B,hB,hfinite⟩ := recenteredPhysicalCopy_doubleBall_integrated_gradient_decay_of_kernelDecay
    hdecay d hd L r₀ m hL hm
  obtain ⟨K,hK,htail⟩ := actual_canonical_column_large_ball_remainder
    hdecay hreg d hd L r₀ m hL hm
  refine ⟨B+2*K,by positivity,?_⟩
  intro Q i u G hu hG hflow hweak R hR y
  dsimp only
  let ν : Measure (Vec d) :=
    (volume (originBall d (2*R)))⁻¹ • volume.restrict (originBall d (2*R))
  let F : PhysicalField d L × Vec d → EuclideanSpace ℝ (Fin d) := fun z =>
    (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
        (translate (r₀ • z.2) (reduce z.1.1))
  let H : PhysicalField d L × Vec d → EuclideanSpace ℝ (Fin d) := fun z =>
    ∫ t in Ioo 0 (4*R^2), WithLp.toLp 2
      (G (project (r₀ := r₀) Q.ellipticity_parameter z.1) (t,z.2))
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hT : 1 ≤ 4*R^2 := by nlinarith [sq_nonneg (R-1)]
  have hρ : 1 ≤ 2*R := by linarith
  have hFm : Measurable F :=
    (Lp.stronglyMeasurable (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))).measurable.comp
      (Probability.continuous_translate.measurable.comp
      ((measurable_const.smul measurable_snd).prodMk
        ((measurePreserving_physicalReduction Q).measurable.comp measurable_fst)))
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hHm : Measurable H :=
    ((J.continuous.measurable.comp hG).comp
      (((measurePreserving_akmProject Q).measurable.comp measurable_fst.fst).prodMk
        (measurable_snd.prodMk measurable_fst.snd))).stronglyMeasurable.integral_prod_right'.measurable
  have hrem := htail Q i u G hu hG hflow hweak (2*R) (4*R^2) hρ hT
  have hfin := hfinite Q i u G hu hG hflow R hR y
  have heq := physical_paired_time_integral_rms Q i u G hG hflow
    (zero_lt_one.trans_le hT) (zero_lt_one.trans_le hρ) (r₀*R) y
  obtain ⟨_,_,hfst,hsnd,_⟩ := recenteredPhysicalCopy_properties Q (r₀*R) y
  have hv := ENNReal.toReal_pos_iff.mp
    (show 0 < (volume (originBall d (2*R))).toReal by
      simpa only [originBall,ball,sub_zero] using ball_volume_pos_finite d (2*R) (by positivity))
  letI : IsProbabilityMeasure ν := ⟨by
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hv.1.ne' hv.2.ne⟩
  have hb : eLpNorm (fun z : PhysicalField d L × PhysicalField d L =>
      Real.sqrt (∫ x, ‖H (z.1,x)-H (z.2,x)‖^2 ∂ν))
      (ENNReal.ofReal m) (recenteredPhysicalCopyLaw Q (r₀*R) y) ≤
        ENNReal.ofReal (B*R^(-(d : ℝ)/2)) := by
    exact (eLpNorm_congr_ae (heq.mono fun _ hz => hz.2)).trans_le hfin.2
  obtain ⟨hloc,hmem,hbound⟩ := coupled_spatial_rms_approximation
    (physicalReferenceLaw Q) (recenteredPhysicalCopyLaw Q (r₀*R) y) ν
    Prod.fst Prod.snd hfst hsnd F H hFm hHm
    (ENNReal.one_le_ofReal.mpr (one_le_two.trans hm))
    (mul_nonneg hB.le (Real.rpow_nonneg hR0.le _))
    (mul_nonneg hK.le (Real.rpow_nonneg (by positivity) _))
    hrem.1 (heq.mono fun _ hz => hz.1) hrem.2.2 hb
  refine ⟨hloc,hmem,hbound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hpow : (4*R^2)^(-((d : ℝ)/4)) ≤ R^(-(d : ℝ)/2) := by
    calc
      _ ≤ (R^2)^(-((d : ℝ)/4)) :=
        Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hR0) (by nlinarith [sq_nonneg R])
          (by linarith [Nat.cast_nonneg (α := ℝ) d])
      _ = _ := by
        rw [← Real.rpow_natCast_mul hR0.le]
        congr 1
        ring
  calc
    B*R^(-(d : ℝ)/2)+2*(K*(4*R^2)^(-((d : ℝ)/4))) ≤
        B*R^(-(d : ℝ)/2)+2*(K*R^(-(d : ℝ)/2)) := by gcongr
    _ = _ := by ring

end EinsteinRelation.Correctors
