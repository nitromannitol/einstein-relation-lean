import EinsteinFull.Calculus.C2CorrectorSchauderSupport
import EinsteinRelation.Correctors.AKMPhysicalScalarSobolev
import EinsteinRelation.Mobility.CorrectorGradientMoments
import PDEFoundation.PDE.CoefficientForcingScale
import EinsteinFull.Calculus.C2CorrectorPointwiseMoments
import EinsteinFull.Calculus.S2GaussianDeconvMoments
import EinsteinRelation.Correctors.SpatialMomentAverage
import EinsteinRelation.TimeChange.EuclideanTransport

/-! Gaussian averaging of the actual canonical gradient, conditional on its
explicit pointwise moments. This analytic transfer is not the smooth-moments
source-node reduction. The Gaussian is the literal frozen anisotropic kernel. -/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Correctors

/-- The three Gaussian conclusions at `paper/main.tex:880–885`, from explicit
pointwise Lᵠ inputs at `q = max p 2`. The constant is chosen before the law,
coordinate, center and positive scale. No smoothness or higher moments are
inferred from the canonical L² construction. -/
theorem correctorGaussian_moments_of_pointwise (p : ℝ) (hp : 1 ≤ p)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 2 ≤ d) (L r₀ : ℝ)
      (Q : EnvironmentLaw d L r₀) (i : Fin d),
      MemLp (fun ω => correctorGradient Q i ω)
        (ENNReal.ofReal (max p 2)) (reducedLaw Q) →
      eLpNorm (fun ω => correctorGradient Q i ω)
        (ENNReal.ofReal (max p 2)) (reducedLaw Q) ≤ ENNReal.ofReal M →
      ∀ (z : Vec d) (r : ℝ) (hr : 0 < r),
        (∀ᵐ ω ∂reducedLaw Q, Integrable (fun x : Vec d =>
          (homogenizedGaussianKernel Q ⟨0, by omega⟩ (r ^ 2)
            (sq_pos_of_pos hr) 0 (z - x)).re *
          euclideanSq (unitVector i +
            WithLp.ofLp (correctorGradient Q i (translate x ω))))) ∧
        MemLp (fun ω => Real.sqrt (∫ x : Vec d,
          (homogenizedGaussianKernel Q ⟨0, by omega⟩ (r ^ 2)
            (sq_pos_of_pos hr) 0 (z - x)).re *
          euclideanSq (unitVector i +
            WithLp.ofLp (correctorGradient Q i (translate x ω)))))
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (∫ ω, (Real.sqrt (∫ x : Vec d,
          (homogenizedGaussianKernel Q ⟨0, by omega⟩ (r ^ 2)
            (sq_pos_of_pos hr) 0 (z - x)).re *
          euclideanSq (unitVector i +
            WithLp.ofLp (correctorGradient Q i (translate x ω))))) ^ p
          ∂reducedLaw Q) ≤ C := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  refine ⟨(1 + M) ^ p + 1, by positivity, ?_⟩
  intro d hd L r₀ Q i hmem hb z r hr
  have hprob : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let q := max p 2
  have hq : 2 ≤ q := le_max_right _ _
  have hpq : ENNReal.ofReal p ≤ ENNReal.ofReal q :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  let k : Vec d → ℝ := fun x =>
    anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) (z - x)
  have hk : Measurable k :=
    ((contDiff_anisotropicGaussian _ _).continuous.comp
      (continuous_const.sub continuous_id)).measurable
  have hk0 (x) : 0 ≤ k x := anisotropicGaussian_nonneg _ (sq_pos_of_pos hr) _
  have hki : Integrable k :=
    (integrable_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) _
      (sq_pos_of_pos hr)).comp_sub_left z
  have hmass : (∫ x, k x) = 1 := by
    dsimp only [k]
    rw [integral_sub_left_eq_self,
      integral_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) _ (sq_pos_of_pos hr)]
  let ν : Measure (Vec d) := volume.withDensity (fun x => ENNReal.ofReal (k x))
  have hν : IsProbabilityMeasure ν := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hki (ae_of_all _ hk0), hmass]
    exact ENNReal.ofReal_one⟩
  let a : EuclideanSpace ℝ (Fin d) := correctorUnitVector i
  have ha : ‖a‖ = 1 := by simp [a, correctorUnitVector]
  let g : FieldPair d × Vec d → EuclideanSpace ℝ (Fin d) :=
    fun v => a + correctorGradient Q i (translate v.2 v.1)
  have hg : Measurable g := measurable_const.add (measurable_correctorGradient_orbit Q i)
  have hcol (x : Vec d) :
      MemLp (fun ω => g (ω, x)) (ENNReal.ofReal q) (reducedLaw Q) ∧
      eLpNorm (fun ω => g (ω, x)) (ENNReal.ofReal q) (reducedLaw Q) ≤
        ENNReal.ofReal (1 + M) := by
    have ht := measurePreserving_translate (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) x
    have hmx := hmem.comp_measurePreserving ht
    have hx : eLpNorm (fun ω => correctorGradient Q i (translate x ω))
        (ENNReal.ofReal q) (reducedLaw Q) ≤ ENNReal.ofReal M := by
      exact (eLpNorm_comp_measurePreserving hmem.aestronglyMeasurable ht).trans_le hb
    refine ⟨(memLp_const a).add hmx, ?_⟩
    calc
      _ ≤ eLpNorm (fun _ : FieldPair d => a) (ENNReal.ofReal q) (reducedLaw Q) +
          eLpNorm (fun ω => correctorGradient Q i (translate x ω))
            (ENNReal.ofReal q) (reducedLaw Q) :=
        eLpNorm_add_le (by
          simpa only [ENNReal.ofReal_one] using
            ENNReal.ofReal_le_ofReal (show 1 ≤ q by linarith))
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal M := by
        gcongr
        rw [eLpNorm_const' a (ENNReal.ofReal_ne_zero_iff.mpr (by linarith : 0 < q))
          ENNReal.ofReal_ne_top]
        simp [← ofReal_norm, ha]
      _ = _ := (ENNReal.ofReal_add (by norm_num) hM).symm
  obtain ⟨hsp, hs, hsb⟩ := spatialL2_average_moment_le
    (reducedLaw Q) ν hq (by positivity : 0 ≤ 1 + M) g hg hcol
  have heq (ω : FieldPair d) :
      (∫ x, ‖g (ω, x)‖ ^ 2 ∂ν) = ∫ x : Vec d,
        (homogenizedGaussianKernel Q ⟨0, by omega⟩ (r ^ 2)
          (sq_pos_of_pos hr) 0 (z - x)).re *
        euclideanSq (unitVector i +
          WithLp.ofLp (correctorGradient Q i (translate x ω))) := by
    rw [integral_withDensity_eq_integral_toReal_smul (hk.ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (hk0 x), smul_eq_mul,
      homogenizedGaussianKernel_zero_eq_ofReal]
    simp only [Complex.ofReal_re]
    congr 1
    have hn := TimeChange.euclideanNorm_eq_norm_toLp
      (unitVector i + WithLp.ofLp (correctorGradient Q i (translate x ω)))
    have hn0 : 0 ≤ euclideanSq
        (unitVector i + WithLp.ofLp (correctorGradient Q i (translate x ω))) :=
      by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    rw [← Real.sq_sqrt hn0]
    congr 1
    exact hn.symm
  have hAE : ∀ᵐ ω ∂reducedLaw Q, Integrable (fun x : Vec d =>
      (homogenizedGaussianKernel Q ⟨0, by omega⟩ (r ^ 2)
        (sq_pos_of_pos hr) 0 (z - x)).re *
      euclideanSq (unitVector i +
        WithLp.ofLp (correctorGradient Q i (translate x ω)))) := by
    filter_upwards [hsp] with ω hω
    have hi := (memLp_two_iff_integrable_sq_norm hω.aestronglyMeasurable).mp hω
    have hi' := (integrable_withDensity_iff_integrable_smul' hk.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hi
    have hreal : (fun x => (ENNReal.ofReal (k x)).toReal • ‖g (ω, x)‖ ^ 2) =
        fun x => (homogenizedGaussianKernel Q ⟨0, by omega⟩ (r ^ 2)
          (sq_pos_of_pos hr) 0 (z - x)).re *
          euclideanSq (unitVector i +
            WithLp.ofLp (correctorGradient Q i (translate x ω))) := by
      funext x
      rw [ENNReal.toReal_ofReal (hk0 x), smul_eq_mul,
        homogenizedGaussianKernel_zero_eq_ofReal]
      simp only [Complex.ofReal_re]
      congr 1
      have hn := TimeChange.euclideanNorm_eq_norm_toLp
        (unitVector i + WithLp.ofLp (correctorGradient Q i (translate x ω)))
      have hn0 : 0 ≤ euclideanSq
          (unitVector i + WithLp.ofLp (correctorGradient Q i (translate x ω))) := by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
      rw [← Real.sq_sqrt hn0]
      congr 1
      exact hn.symm
    rw [hreal] at hi'
    exact hi'
  have hspmem := hs.mono_exponent hpq
  have hspbound : eLpNorm (fun ω => Real.sqrt (∫ x, ‖g (ω, x)‖ ^ 2 ∂ν))
      (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal (1 + M) :=
    (eLpNorm_le_eLpNorm_of_exponent_le hpq).trans hsb
  have hmoment : (∫ ω, (Real.sqrt (∫ x, ‖g (ω, x)‖ ^ 2 ∂ν)) ^ p
      ∂reducedLaw Q) ≤ (1 + M) ^ p := by
    have hi := hspmem.integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    simp only [ENNReal.toReal_ofReal hp0.le,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hi
    have hpow := ENNReal.rpow_le_rpow hspbound hp0.le
    rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hp0)
      ENNReal.ofReal_ne_top hspmem.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0] at hpow
    have hnn : ∀ ω, 0 ≤ (Real.sqrt (∫ x, ‖g (ω, x)‖ ^ 2 ∂ν)) ^ p :=
      fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ 1 + M) hp0.le] at hpow
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (1 + M) ^ p)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hnn)]
    convert hpow using 1
    apply lintegral_congr
    intro ω
    rw [Real.enorm_of_nonneg (Real.sqrt_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) hp0.le]
  simp_rw [heq] at hspmem hmoment
  exact ⟨hAE, hspmem, hmoment.trans (le_add_of_nonneg_right zero_le_one)⟩

open EinsteinRelation.Environment.AKMTestIntegralSupport ReductionImageV3

private theorem pdeBall_eq {d : ℕ} (R : ℝ) (hR : 0 < R) :
    PDE.euclideanBall (0 : Vec d) R = External.AKM.ball 0 R := by
  ext x
  exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR

/-- The canonical physical gradient obeys the deterministic Schauder bound on
its dependence-range half ball. The coefficient and potential are the same
ones used by the canonical source-corrector identification. -/
theorem exists_canonicalCorrector_physical_halfBall_bound
    (d : ℕ) (hd : 2 ≤ d) (L R : ℝ) (hL : 1 ≤ L) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : EnvironmentLaw d L R) (i : Fin d),
      ∀ᵐ ω ∂physicalReferenceLaw Q,
      ∀ᵐ x ∂volume.restrict (External.AKM.ball 0 (R * (1 / 2))),
        ‖correctorGradient Q i (translate x (reduce ω.1))‖ ≤
          K * (1 + canonicalCorrectorPhysicalBallEnergy Q i 0 (reduce ω.1)) := by
  let : Fact (2 ≤ d) := ⟨hd⟩
  let B := sourceReducedBound L
  let A := Real.exp (2 * L) * (L + 2 * L ^ 2)
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hB : 0 < B := by dsimp [B, sourceReducedBound]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨K, hK, hb⟩ := exists_uniform_affine_schauder_rescaled_ball_bound
    d (by omega) (B ^ 2) (2 * B * A * R) (by positivity)
  refine ⟨K, hK, ?_⟩
  intro Q i
  obtain ⟨φ, hid⟩ := exists_akmCorrector_global_gradient_identification_from_pde Q i
  filter_upwards [ae_physicalAKMPotential_affine_weakSolution Q i φ hid] with ω hweak
  have hc := sourceReducedBound_support hL ω.2
  have hw := (hweak 0 R hR 0).2
  rw [← pdeBall_eq R hR] at hw
  let u := pdeH1OfSpatialWeakSolution hw
  have hsol : PDE.IsWeakDivergenceFormSolutionOn
      (fun x => B • (reduce ω.1).1 x) (PDE.euclideanBall 0 R) u 0 0 := by
    convert (pdeH1OfSpatialWeakSolution_isSolution hw).smul_coefficient_source_forcing B
      using 1 <;> ext x <;> simp
  have hell : ∀ x ∈ PDE.euclideanBall 0 R,
      PDE.IsEllipticMatrix 1 (B ^ 2) (B • (reduce ω.1).1 x) := by
    intro x _
    exact ParabolicBridge.isEllipticMatrix_smul_of_symm_bounds hc.1
      (hc.2.1 x).1 (fun ξ => ((hc.2.1 x).2 ξ).1)
      (fun ξ => ((hc.2.1 x).2 ξ).2)
  have hholder : PDE.EuclideanMatrixHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) 1)
      (PDE.DGNM.blowUpCoeff (fun x => B • (reduce ω.1).1 x) 0 R)
      (1 / 2) (2 * B * A * R) := by
    change PDE.EuclideanMatrixHolderSeminormLE _
      (fun y => B • reducedCoefficient ω.1 (R • y + 0)) _ _
    simpa only [add_zero] using
      matrixHolder_half_normalized_pullback hA hB.le hR hc.2.2.2.1
  have hbound := hb _ 0 R hR hell hholder u hsol i
  have hgrad (x : Vec d) : u.grad x - PDE.basisVec i =
      (correctorGradient Q i (translate x (reduce ω.1))).ofLp := by
    change unitVector i + _ - PDE.basisVec i = _
    rw [show PDE.basisVec i = unitVector i from rfl, add_sub_cancel_left]
    rfl
  have heq : Real.sqrt (PDE.integralAverage (PDE.euclideanBall (0 : Vec d) 1)
      (fun y => PDE.vecNormSq (u.grad (R • y + 0) - PDE.basisVec i))) =
      canonicalCorrectorPhysicalBallEnergy Q i 0 (reduce ω.1) := by
    simp only [add_zero, hgrad]
    unfold canonicalCorrectorPhysicalBallEnergy
    congr 1
    rw [pdeBall_eq 1 (by norm_num)]
    change (volume.real (External.AKM.ball (0 : Vec d) 1))⁻¹ *
      (∫ y in External.AKM.ball (0 : Vec d) 1, euclideanSq
        ((correctorGradient Q i (translate (R • y) (reduce ω.1))).ofLp)) = _
    convert (show _ from
      setAverage_euclideanBall_smul
        (fun x => euclideanSq ((correctorGradient Q i (translate x (reduce ω.1))).ofLp))
        R 1 hR (by norm_num)) using 1 <;>
      simp only [setAverage_eq, smul_eq_mul, mul_one, correctorGradient]
    all_goals rfl

  rw [heq] at hbound
  have hbound' : ∀ᵐ x ∂volume.restrict (External.AKM.ball 0 (R * (1 / 2))),
      PDE.vecEuclideanNorm (u.grad x - PDE.basisVec i) ≤
        K * (1 + canonicalCorrectorPhysicalBallEnergy Q i 0 (reduce ω.1)) := by
    have hm : PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (R * (1 / 2))) =
        volume.restrict (External.AKM.ball 0 (R * (1 / 2))) := by
      unfold PDE.volumeOn
      rw [pdeBall_eq _ (by positivity)]
    rw [hm] at hbound
    exact hbound
  filter_upwards [hbound'] with x hx
  rw [hgrad] at hx
  change euclideanNorm _ ≤ _ at hx
  simpa only [TimeChange.euclideanNorm_eq_norm_toLp, WithLp.toLp_ofLp] using hx

/-- All positive canonical-gradient moments follow from the same physical
half-ball Schauder estimate and the source dependence-range energy moments. -/
theorem canonicalCorrector_pointwise_positive_moments
    (d : ℕ) (hd : 2 ≤ d) (L R p : ℝ)
    (hL : 1 ≤ L) (hR : 0 < R) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L R) (i : Fin d),
      (∫⁻ ω, ENNReal.ofReal (‖correctorGradient Q i ω‖ ^ p) ∂reducedLaw Q) ≤
        ENNReal.ofReal C := by
  obtain ⟨K, hK, hb⟩ := exists_canonicalCorrector_physical_halfBall_bound d hd L R hL hR
  obtain ⟨C, hC, hE⟩ := canonicalCorrector_physical_ball_energy_moments d hd L p hL hp
  refine ⟨K ^ p * (2 ^ p * (max C 0 + 1)), by positivity, ?_⟩
  intro Q i
  let := physicalReferenceLaw_probability Q
  let := reducedLaw_probability Q
  let ν : Measure (Vec d) := volume.restrict (External.AKM.ball 0 (R * (1 / 2)))
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict_euclideanBall 0 _ (by positivity)
  have hν : ν Set.univ ≠ 0 := by
    simpa only [ν, Measure.restrict_apply_univ] using
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d _ (by positivity))).1.ne'
  let E := fun (ω : PhysicalField d L) => canonicalCorrectorPhysicalBallEnergy Q i 0 (reduce ω.1)
  have hE0 (ω) : 0 ≤ E ω := Real.sqrt_nonneg _
  have hsum := lintegral_norm_rpow_le_of_unit_energy (physicalReferenceLaw Q)
    (G := fun ω => (1 + E ω : ℝ)) (K := 1) (by norm_num) hp.le hE0
    (ae_of_all _ (fun ω => by
      rw [Real.norm_of_nonneg (add_nonneg zero_le_one (hE0 ω)), one_mul, add_comm]))
    (hE Q i 0)
  have hsum' : (∫⁻ ω, ENNReal.ofReal ((1 + E ω) ^ p) ∂physicalReferenceLaw Q) ≤
      ENNReal.ofReal (2 ^ p * (max C 0 + 1)) := by
    have hn (ω) : ‖(1 + E ω : ℝ)‖ = 1 + E ω := Real.norm_of_nonneg (add_nonneg zero_le_one (hE0 ω))
    simpa only [hn, Real.one_rpow, one_mul] using hsum
  apply (ENNReal.mul_le_mul_iff_right hν (measure_ne_top ν Set.univ)).mp
  rw [← lintegral_physical_correctorGradient_spatial_moment Q i ν p]
  calc
    _ ≤ ∫⁻ ω, ν Set.univ * ENNReal.ofReal ((K * (1 + E ω)) ^ p)
        ∂physicalReferenceLaw Q := by
      apply lintegral_mono_ae
      filter_upwards [hb Q i] with ω hω
      calc
        _ ≤ ∫⁻ _x, ENNReal.ofReal ((K * (1 + E ω)) ^ p) ∂ν :=
          lintegral_mono_ae (hω.mono fun x hx =>
            ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) hx hp.le))
        _ = _ := by rw [lintegral_const, mul_comm]
    _ = ν Set.univ * (ENNReal.ofReal (K ^ p) *
        ∫⁻ ω, ENNReal.ofReal ((1 + E ω) ^ p) ∂physicalReferenceLaw Q) := by
      have hm (ω) : (K * (1 + E ω)) ^ p = K ^ p * (1 + E ω) ^ p :=
        Real.mul_rpow hK.le (add_nonneg zero_le_one (hE0 ω))
      simp_rw [hm, ENNReal.ofReal_mul (Real.rpow_nonneg hK.le _)]
      rw [lintegral_const_mul', lintegral_const_mul']
      · exact ENNReal.ofReal_ne_top
      · exact measure_ne_top ν Set.univ
    _ ≤ _ := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hK.le _)]
      gcongr

end EinsteinFull
