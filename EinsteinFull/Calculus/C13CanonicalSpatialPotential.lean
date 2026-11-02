import EinsteinFull.Calculus.C2BallPoincareFromPDE
import EinsteinFull.Calculus.C2CorrectorSchauderSupport
import EinsteinFull.Calculus.C5CorrectorUniformSublinearity
import EinsteinRelation.Correctors.CanonicalHarmonicFromPoincare
import DGNMStatements.DeGiorgiHolder
import HoleFillingStatements.PlanarHolder
import PDEFoundation.Measure.LpPower
import PDEFoundation.PDE.CoefficientForcingScale
import EinsteinRelation.Correctors.GTTwoBallCoefficientSupport
import EinsteinRelation.Correctors.HarmonicRepresentativeNormalization
import EinsteinRelation.Correctors.AKMSublinearWeakPotential
import EinsteinRelation.Correctors.NormBallVolumeBound
import EinsteinRelation.Correctors.MemLpAffinePullback
import EinsteinRelation.Correctors.RegularRepresentativeSelection
import EinsteinRelation.Correctors.WeakGradientCentering
import EinsteinRelation.Correctors.SpatialDivergencePushforward
import EinsteinRelation.Correctors.AKMCarrierIdentificationTransport
import EinsteinRelation.Correctors.PairedParabolicEquation
import EinsteinRelation.Calculus.ZeroWeakGradientConstant
import EinsteinRelation.Calculus.WeakGradientTranslation
import Mathlib.MeasureTheory.Integral.Indicator

/-! Spatial weak harmonic coordinates and scale-independent interior estimates.
The canonical gradient is retained literally; no regular-realization premise is used. -/

open MeasureTheory Filter Topology

noncomputable section

namespace EinsteinFull

open EinsteinRelation EinsteinRelation.Correctors
open EinsteinRelation.External.AKM EinsteinRelation.External.GilbargTrudinger
open EinsteinRelation.Correctors.StationarySpatialRealization

/-- On one common full-measure set, every positive-radius ball admits a weak
harmonic coordinate with the actual canonical variational gradient. -/
theorem ae_canonical_ball_weakSolution {d : ℕ} (hd : 2 ≤ d) {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ R : ℝ, 0 < R →
      ∃ (u : Vec d → ℝ) (g : Vec d → Vec d),
        WeakSolution (ball 0 R) ω.1 u g ∧
        (∀ x, g x = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x ω)).ofLp) := by
  letI : Fact (2 ≤ d) := ⟨hd⟩
  let G := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  filter_upwards [ae_exists_spatial_weakPotential_of_closed_gradient
      ballPoincareEstimate_from_pde (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) G (canonicalCorrectorGradient Q i).property,
    ae_spatialRealization_memLp_on_all_compacts (reducedEnvironmentLaw_stationary Q) G,
    ae_canonicalCorrectorFlux_hasWeakDivergence Q i,
    ae_spatial_canonicalCorrectorFlux Q i measurable_id] with ω hpot hG hdiv hflux
  intro R hR
  obtain ⟨u, hu, hweak⟩ := hpot R hR
  have hg : MemLp (fun x => (G (translate x ω)).ofLp) 2
      (volume.restrict (ball (0 : Vec d) R)) := by
    apply memLp_pi_iff.mpr
    intro j
    exact ((hG (Metric.closedBall 0 R) (isCompact_closedBall _ _)).mono_measure
      (Measure.restrict_mono_set volume
        (euclideanBall_subset_coordinateClosedBall R hR.le))).eval_piLp j
  have hdiv' : HasWeakDivergence (ball (0 : Vec d) R)
      (fun x => (ω.1 x).mulVec (unitVector i + (G (translate x ω)).ofLp))
      (fun _ => 0) := by
    apply (HasWeakDivergence.restrict_subset (Set.subset_univ _)
      MeasurableSet.univ hdiv).congr_ae (ae_restrict_of_ae hflux) (ae_eq_refl _)
  refine ⟨(fun x => x i + u x), (fun x => unitVector i + (G (translate x ω)).ofLp),
    affine_weakSolution_of_weakPotential R hR i ω.1 u _ hu hg hweak hdiv', ?_⟩
  intro x
  rfl

/-- AKM's normalized oscillation gives vanishing L² energy on the fixed
unit ball after dilation. The ball volume and Jacobian are explicit. -/
theorem centered_rescaled_energy_tendsto_zero {d : ℕ} (ψ : Vec d → ℝ)
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
      (⨍ x in ball 0 R, (ψ x - ⨍ y in ball 0 R, ψ y ∂volume)^2 ∂volume))
      atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => ∫ y in ball (0 : Vec d) 1,
      (R⁻¹ * (ψ (R • y) - ⨍ x in ball 0 R, ψ x ∂volume))^2 ∂volume)
      atTop (𝓝 0) := by
  have hV : volume.real (ball (0 : Vec d) 1) ≠ 0 :=
    (ball_volume_pos_finite d 1 zero_lt_one).ne'
  have hid (R : ℝ) (hR : 0 < R) :
      (∫ y in ball (0 : Vec d) 1,
        (R⁻¹ * (ψ (R • y) - ⨍ x in ball 0 R, ψ x ∂volume))^2 ∂volume) =
      volume.real (ball (0 : Vec d) 1) *
        (R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
          (ψ x - ⨍ y in ball 0 R, ψ y ∂volume)^2 ∂volume))^2 := by
    let m := ⨍ x in ball 0 R, ψ x ∂volume
    have hscale := integral_unitBall_inv_smul (fun x => (ψ x - m)^2) (inv_pos.mpr hR)
    simp only [inv_inv, inv_pow] at hscale
    have hnonneg : 0 ≤ ⨍ x in ball 0 R, (ψ x - m)^2 ∂volume := by
      rw [setAverage_eq, smul_eq_mul]
      exact mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
    change (∫ y in ball (0 : Vec d) 1, (R⁻¹ * (ψ (R • y) - m))^2 ∂volume) = _
    simp_rw [mul_pow]
    rw [integral_const_mul, hscale, Real.sq_sqrt hnonneg,
      setAverage_eq, smul_eq_mul, paired_ball_volume_scale hR]
    field_simp [hR.ne', hV] <;> ring
  have ht := (hsub.pow 2).const_mul (volume.real (ball (0 : Vec d) 1))
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (hid R hR).symm

/-- On the unit ball the affine coordinate contributes only a fixed
volume term to the centered harmonic energy. -/
theorem coordinate_add_energy_le {d : ℕ} (i : Fin d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball (0 : Vec d) 1))) :
    (∫ y in ball (0 : Vec d) 1, (y i + f y)^2 ∂volume) ≤
      2 * volume.real (ball (0 : Vec d) 1) +
        2 * ∫ y in ball (0 : Vec d) 1, (f y)^2 ∂volume := by
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) 1)) :=
    isFiniteMeasure_restrict.mpr
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d 1 zero_lt_one)).2.ne
  have hcoord : MemLp (fun y : Vec d => y i) 2
      (volume.restrict (ball (0 : Vec d) 1)) := by
    apply (memLp_const (1 : ℝ)).of_le (continuous_apply i).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (paired_isOpen_ball 0 1).measurableSet] with y hy
    change |y i| ≤ |(1 : ℝ)|
    have hy' : euclideanNorm y < 1 := by simpa only [ball, Set.mem_setOf_eq, sub_zero] using hy
    simpa only [abs_one] using
      (Regeneration.coordinate_abs_le_euclideanNorm y i).trans hy'.le
  have hint := integral_mono_ae (hcoord.add hf).integrable_sq
    ((integrable_const (2 : ℝ)).add (hf.integrable_sq.const_mul 2)) (by
      filter_upwards [ae_restrict_mem (paired_isOpen_ball 0 1).measurableSet] with y hy
      have hy' : euclideanNorm y < 1 := by simpa only [ball, Set.mem_setOf_eq, sub_zero] using hy
      have hc : |y i| ≤ 1 :=
        (Regeneration.coordinate_abs_le_euclideanNorm y i).trans hy'.le
      have hc2 : (y i)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hc
      change (y i + f y)^2 ≤ 2 + 2 * (f y)^2
      nlinarith [sq_nonneg (y i - f y)])
  change (∫ y in ball (0 : Vec d) 1, (y i + f y)^2 ∂volume) ≤
    ∫ y in ball (0 : Vec d) 1, (2 + 2 * (f y)^2) ∂volume at hint
  simpa only [integral_add (integrable_const (2 : ℝ)) (hf.integrable_sq.const_mul 2),
    integral_const_mul, integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
    mul_comm (volume (ball (0 : Vec d) 1)).toReal 2] using hint

/-- One global canonical weak potential has the AKM full-radius L²
sublinearity and produces a harmonic coordinate on every positive-radius ball.
All assertions use the same physical field and the same scalar potential. -/
theorem ae_physical_canonical_sublinear_weak_potential {d : ℕ} (hd : 2 ≤ d)
    {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q, ∃ ψ : Vec d → ℝ,
      HasWeakGradient Set.univ ψ (fun x => ((canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate x (reduce ω.1))).ofLp) ∧
      (∀ R : ℝ, 0 < R → MemLp ψ 2 (volume.restrict (ball 0 R))) ∧
      Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
        (⨍ x in ball 0 R, (ψ x - ⨍ y in ball 0 R, ψ y ∂volume)^2 ∂volume))
        atTop (𝓝 0) ∧
      ∀ R : ℝ, 0 < R → WeakSolution (ball 0 R) (reduce ω.1).1
        (fun x => x i + ψ x)
        (fun x => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x (reduce ω.1))).ofLp) := by
  letI : Fact (2 ≤ d) := ⟨hd⟩
  let H := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  obtain ⟨G, _, hpot, hid⟩ := exists_akm_sublinear_global_weakPotential
    ballPoincareEstimate_from_pde Q i
  have hπ := Environment.AKMTestIntegralSupport.measurable_project
    (d := d) (r₀ := r₀) Q.ellipticity_parameter
  have hphysical := ae_of_ae_map hπ.aemeasurable hpot
  have hdiv := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_canonicalCorrectorFlux_hasWeakDivergence Q i)
  have hflux := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_spatial_canonicalCorrectorFlux Q i measurable_id)
  filter_upwards [hphysical, hid, hdiv, hflux] with ω hω hidω hdivω hfluxω
  obtain ⟨hG, ψ, hψweak, hψ, hsub⟩ := hω
  have hw : HasWeakGradient Set.univ ψ
      (fun x => (H (translate x (reduce ω.1))).ofLp) := by
    intro j
    apply (hψweak j).congr_ae (ae_eq_refl _)
    simpa only [Measure.restrict_univ, H] using!
      hidω.mono (fun x hx => congrArg (fun z => z.ofLp j) hx)
  refine ⟨ψ, hw, hψ, hsub, ?_⟩
  intro R hR
  have hg : MemLp (fun x => (H (translate x (reduce ω.1))).ofLp) 2
      (volume.restrict (ball (0 : Vec d) R)) := by
    have heq := ae_restrict_of_ae (s := ball (0 : Vec d) R) hidω
    have hmem := (memLp_congr_ae heq).mp (hG R hR)
    apply memLp_pi_iff.mpr
    intro j
    exact hmem.eval_piLp j
  have hweak : HasWeakGradient (ball 0 R) ψ
      (fun x => (H (translate x (reduce ω.1))).ofLp) := fun j =>
    HasWeakPartialDerivative.restrict_subset (Set.subset_univ _) MeasurableSet.univ (hw j)
  have hdiv' : HasWeakDivergence (ball (0 : Vec d) R)
      (fun x => ((reduce ω.1).1 x).mulVec
        (unitVector i + (H (translate x (reduce ω.1))).ofLp)) (fun _ => 0) := by
    apply (HasWeakDivergence.restrict_subset (Set.subset_univ _)
      MeasurableSet.univ hdivω).congr_ae (ae_restrict_of_ae hfluxω) (ae_eq_refl _)
  exact affine_weakSolution_of_weakPotential R hR i (reduce ω.1).1 ψ _
    (hψ R hR) hg hweak hdiv'

/-- Interior scalar Hölder regularity in every source dimension. The exponent
and constant depend only on dimension and ellipticity, before the coefficient
field and weak solution are chosen. -/
theorem exists_uniform_harmonic_holder_estimate (d : ℕ) (hd : 2 ≤ d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ α C : ℝ, 0 < α ∧ 0 ≤ C ∧
      ∀ a : PDE.CoeffField d,
        (∀ i j, AEMeasurable (fun x => a x i j)
          (PDE.volumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1))) →
        (∀ x ∈ PDE.euclideanBall (0 : PDE.Vec d) 1, PDE.IsEllipticMatrix 1 Λ (a x)) →
        ∀ u : PDE.H1Function (PDE.euclideanBall (0 : PDE.Vec d) 1),
          PDE.IsWeakDivergenceFormSolutionOn a _ u 0 0 →
          ∃ v : PDE.Vec d → ℝ,
            v =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2))] u.toFun ∧
            PDE.EuclideanHolderSeminormLE (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2))
              v α (C * Real.sqrt (∫ x in PDE.euclideanBall (0 : PDE.Vec d) 1,
                u.toFun x ^ 2)) := by
  by_cases hd2 : d = 2
  · subst d
    obtain ⟨C, hC, hreg⟩ := PDE.exists_planarHolder_constant
    refine ⟨(C * Λ) ^ (-(1 / 2 : ℝ)), C * Real.sqrt Λ,
      Real.rpow_pos_of_pos (mul_pos hC (by linarith)) _, by positivity, ?_⟩
    intro a hmeas hell u hsol
    obtain ⟨v, hv, M, H, hM, hH, hbound⟩ := hreg Λ a hmeas hell u hsol
    have hM0 : 0 ≤ M := (abs_nonneg _).trans
      (hM 0 (PDE.center_mem_euclideanBall 0 (by norm_num)))
    refine ⟨v, hv, ?_⟩
    exact (show PDE.EuclideanHolderSeminormLE _ v _ H from hH).mono_const
      (by linarith)
  · have hd3 : 3 ≤ d := by omega
    obtain ⟨C, hC, hreg⟩ := PDE.exists_deGiorgi_holder_constant d hd3
    obtain ⟨α, hα, _, _, hαreg⟩ := hreg Λ hΛ
    refine ⟨α, C * Λ ^ ((d : ℝ) / 4), hα, by positivity, ?_⟩
    intro a hmeas hell u hsol
    obtain ⟨v, M, H, hv, hM, hH, _, hholder, hbound⟩ := hαreg a hmeas hell u hsol
    have hnorm : (eLpNorm u.toFun 2
        (PDE.volumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1))).toReal =
        Real.sqrt (∫ x in PDE.euclideanBall (0 : PDE.Vec d) 1, u.toFun x ^ 2) := by
      rw [← PDE.toReal_eLpNorm_two_sq_eq_integral_sq u.memL2,
        Real.sqrt_sq ENNReal.toReal_nonneg]
    have hbound' := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top u.memL2.eLpNorm_ne_top) hbound
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ M + H),
      ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ C * Λ ^ ((d : ℝ) / 4)),
      hnorm] at hbound'
    exact ⟨v, hv, hholder.mono_const (by linarith)⟩

/-- The proved Schauder estimate supplies a half-Hölder representative of the
weak gradient for Hölder coefficients. No smooth-coefficient hypothesis or
external regular-representative input is needed. -/
theorem exists_holder_harmonic_gradient_halfBall {d : ℕ} (hd : 0 < d) {Λ M : ℝ}
    (hM : 0 ≤ M) (a : PDE.CoeffField d)
    (ha : PDE.EuclideanMatrixHolderSeminormLE
      (PDE.euclideanBall (0 : PDE.Vec d) 1) a (1 / 2) M)
    (hell : ∀ x ∈ PDE.euclideanBall (0 : PDE.Vec d) 1,
      PDE.IsEllipticMatrix 1 Λ (a x))
    (u : PDE.H1Function (PDE.euclideanBall (0 : PDE.Vec d) 1))
    (hu : PDE.IsWeakDivergenceFormSolutionOn a _ u 0 0) :
    ∃ (G : PDE.Vec d → PDE.Vec d) (K : ℝ), 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE
        (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2)) G (1 / 2) K ∧
      G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2))] u.grad := by
  obtain ⟨C, hC, hs⟩ := PDE.exists_schauderC1alpha_constant hd (Λ := Λ)
  obtain ⟨ε, hε, hεfour, hsmall⟩ := exists_schauder_half_scale C M hC hM
  let ha' : ∃ K : ℝ, 0 ≤ K ∧ PDE.EuclideanMatrixHolderSeminormLE
      (PDE.euclideanBall (0 : PDE.Vec d) 1) a (1 / 2) K := ⟨M, hM, ha⟩
  let hF : ∃ K : ℝ, 0 ≤ K ∧ PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : PDE.Vec d) 1) (0 : PDE.Vec d → PDE.Vec d)
      (1 / 2) K := ⟨0, le_refl _, by
        intro x hx y hy
        simp [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]⟩
  have hsmall' : ε ^ (1 / 2 : ℝ) * PDE.euclideanMatrixHolderSeminormOn
      (PDE.euclideanBall (0 : PDE.Vec d) 1) a (1 / 2) ha' ≤
      C⁻¹ * (1 / 2) * (1 - 1 / 2) :=
    (mul_le_mul_of_nonneg_left (PDE.euclideanMatrixHolderSeminormOn_le ha' hM ha)
      (Real.rpow_nonneg hε.le _)).trans hsmall
  obtain ⟨G, hG, _, heq, _⟩ := hs
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    hε hεfour a 0 hell ha' hF hsmall' u hu
  obtain ⟨K, hK, hh⟩ := hG
  exact ⟨G, K, hK, hh, heq⟩

/-- Dilation and amplitude normalization preserve the same interior estimate:
neither the exponent nor the constant depends on the physical radius. -/
theorem exists_uniform_rescaled_harmonic_holder_estimate (d : ℕ) (hd : 2 ≤ d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ α C : ℝ, 0 < α ∧ 0 ≤ C ∧
      ∀ (R : ℝ), 0 < R → ∀ a : PDE.CoeffField d,
        (∀ i j, AEMeasurable (fun x => a x i j)
          (PDE.volumeOn (PDE.euclideanBall (0 : PDE.Vec d) R))) →
        (∀ x ∈ PDE.euclideanBall (0 : PDE.Vec d) R, PDE.IsEllipticMatrix 1 Λ (a x)) →
        ∀ u : PDE.H1Function (PDE.euclideanBall (0 : PDE.Vec d) R),
          PDE.IsWeakDivergenceFormSolutionOn a _ u 0 0 →
          ∃ v : PDE.Vec d → ℝ,
            v =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2))]
              (fun y => R⁻¹ * u.toFun (R • y)) ∧
            PDE.EuclideanHolderSeminormLE (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2))
              v α (C * Real.sqrt (∫ y in PDE.euclideanBall (0 : PDE.Vec d) 1,
                (R⁻¹ * u.toFun (R • y)) ^ 2)) := by
  obtain ⟨α, C, hα, hC, hreg⟩ := exists_uniform_harmonic_holder_estimate d hd Λ hΛ
  refine ⟨α, C, hα, hC, ?_⟩
  intro R hR a hmeas hell u hsol
  let w := R⁻¹ • PDE.DGNM.blowUp u 0 hR (Set.Subset.refl _)
  have hw : PDE.IsWeakDivergenceFormSolutionOn
      (PDE.DGNM.blowUpCoeff a 0 R) _ w 0 0 :=
    PDE.DGNM.solutionOn_smul (PDE.DGNM.solutionOn_blowUp
      (PDE.isOpen_euclideanBall 0 R) hsol 0 hR (Set.Subset.refl _)) R⁻¹
  have hwfun (y : PDE.Vec d) : w.toFun y = R⁻¹ * u.toFun (R • y) := by
    simp [w]
  obtain ⟨v, hv, hh⟩ := hreg (PDE.DGNM.blowUpCoeff a 0 R)
    (PDE.DGNM.blowUpCoeff_aemeasurable hmeas 0 hR (Set.Subset.refl _))
    (PDE.DGNM.blowUpCoeff_elliptic hell 0 hR (Set.Subset.refl _)) w hw
  rw [show w.toFun = (fun y => R⁻¹ * u.toFun (R • y)) from funext hwfun] at hv hh
  exact ⟨v, hv, hh⟩

/-- The canonical variational coordinates satisfy the scale-independent
estimate, on a common full-measure set and with the literal orbit gradient. -/
theorem ae_canonical_rescaled_harmonic_holder {d : ℕ} (hd : 2 ≤ d)
    {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ α C : ℝ, 0 < α ∧ 0 ≤ C ∧
      ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ R : ℝ, 0 < R →
        ∃ (u : Vec d → ℝ) (g : Vec d → Vec d) (v : Vec d → ℝ),
          WeakSolution (ball 0 R) ω.1 u g ∧
          (∀ x, g x = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x ω)).ofLp) ∧
          v =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2))]
            (fun y => R⁻¹ * u (R • y)) ∧
          PDE.EuclideanHolderSeminormLE (PDE.euclideanBall (0 : Vec d) (1 / 2))
            v α (C * Real.sqrt (∫ y in PDE.euclideanBall (0 : Vec d) 1,
              (R⁻¹ * u (R • y)) ^ 2)) := by
  let B := sourceReducedBound L
  have hB1 : 1 ≤ B := by
    have hL := Q.ellipticity_parameter
    dsimp [B, sourceReducedBound]
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity))
      (by nlinarith [sq_nonneg L])
  obtain ⟨α, C, hα, hC, hreg⟩ :=
    exists_uniform_rescaled_harmonic_holder_estimate d hd (B ^ 2) (by nlinarith)
  refine ⟨α, C, hα, hC, ?_⟩
  filter_upwards [ae_canonical_ball_weakSolution hd Q i,
    ActualImageLpStateTransport.ae_reducedEnvironmentLaw_mem_image Q] with ω hw hω
  rcases hω with ⟨η, hη, rfl⟩
  have hc := sourceReducedBound_support Q.ellipticity_parameter hη
  intro R hR
  obtain ⟨u, g, hweak, hg⟩ := hw R hR
  have hball : PDE.euclideanBall (0 : Vec d) R = ball 0 R := by
    ext x
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR
  have hweak' := hweak
  rw [← hball] at hweak'
  let w := pdeH1OfSpatialWeakSolution hweak'
  have hsol : PDE.IsWeakDivergenceFormSolutionOn
      (fun x => B • (reduce η).1 x) _ w 0 0 := by
    convert (pdeH1OfSpatialWeakSolution_isSolution hweak').smul_coefficient_source_forcing B
      using 1 <;> ext x <;> simp
  have hell : ∀ x ∈ PDE.euclideanBall (0 : Vec d) R,
      PDE.IsEllipticMatrix 1 (B ^ 2) (B • (reduce η).1 x) := by
    intro x _
    exact ParabolicBridge.isEllipticMatrix_smul_of_symm_bounds hc.1
      (hc.2.1 x).1 (fun ξ => ((hc.2.1 x).2 ξ).1)
      (fun ξ => ((hc.2.1 x).2 ξ).2)
  have hmeas : ∀ j k, AEMeasurable (fun x => (B • (reduce η).1 x) j k)
      (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) R)) := by
    intro j k
    exact (continuous_const.mul ((continuous_apply k).comp
      ((continuous_apply j).comp (reduce η).1.continuous))).measurable.aemeasurable
  obtain ⟨v, hv, hh⟩ := hreg R hR _ hmeas hell w hsol
  exact ⟨u, g, v, hweak, hg, hv, hh⟩

/-- Lowering the exponent on the diameter-one interior ball keeps the constant. -/
theorem holder_halfBall_lower_exponent {d : ℕ} {v : PDE.Vec d → ℝ}
    {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hh : PDE.EuclideanHolderSeminormLE
      (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2)) v α K) :
    PDE.EuclideanHolderSeminormLE (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2))
      v (min α 1) K := by
  intro x hx y hy
  have hx' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 1 / 2)).mp hx
  have hy' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 1 / 2)).mp hy
  simp only [sub_zero] at hx' hy'
  have ht := PDE.vecEuclideanNorm_add_le x (-y)
  rw [PDE.vecEuclideanNorm_neg] at ht
  change PDE.vecEuclideanNorm (x - y) ≤ _ at ht
  exact (hh x hx y hy).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge' (PDE.vecEuclideanNorm_nonneg _)
      (by linarith) (le_min hα.le zero_le_one) (min_le_left α 1)) hK)

/-- Transport a normalized estimate back to the physical unit ball. The energy
on the doubled ball is the energy of the same scalar weak representative. -/
theorem physical_holder_of_rescaled {d : ℕ} {u v : Vec d → ℝ} {α C : ℝ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (hv : v =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2))]
      (fun y => (2 : ℝ)⁻¹ * u ((2 : ℝ) • y)))
    (hh : PDE.EuclideanHolderSeminormLE (PDE.euclideanBall (0 : Vec d) (1 / 2))
      v α (C * Real.sqrt (∫ y in PDE.euclideanBall (0 : Vec d) 1,
        ((2 : ℝ)⁻¹ * u ((2 : ℝ) • y)) ^ 2))) :
    ∃ w : Vec d → ℝ,
      w =ᵐ[volume.restrict (ball (0 : Vec d) 1)] u ∧
      ∀ x y, euclideanNorm x < 1 → euclideanNorm y < 1 →
        |w x - w y| ≤ (2 * C + 1) *
          Real.sqrt (∫ z in ball (0 : Vec d) 2, (u z) ^ 2 ∂volume) *
            euclideanNorm (x - y) ^ min α 1 := by
  have hball (R : ℝ) (hR : 0 < R) :
      PDE.euclideanBall (0 : Vec d) R = ball 0 R := by
    ext x
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR
  have henergy : (∫ y in PDE.euclideanBall (0 : Vec d) 1,
      ((2 : ℝ)⁻¹ * u ((2 : ℝ) • y)) ^ 2) ≤
      ∫ z in ball (0 : Vec d) 2, (u z) ^ 2 ∂volume := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have hs := PDE.DGNM.setIntegral_comp_affineScale_ball (0 : Vec d)
      (r := 2) (by norm_num) 1 (fun x => (u x) ^ 2)
    simp only [add_zero, mul_one] at hs
    rw [hs, hball 2 (by norm_num)]
    have hp : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have hi : (0 : ℝ) ≤ ∫ z in ball (0 : Vec d) 2, (u z) ^ 2 ∂volume :=
      integral_nonneg (fun _ => sq_nonneg _)
    have hinv : (2 ^ d : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hp
    have hinv0 : (0 : ℝ) ≤ (2 ^ d : ℝ)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hinv hi]
  let w : Vec d → ℝ := fun x => 2 * v ((2 : ℝ)⁻¹ • x)
  refine ⟨w, ?_, ?_⟩
  · have ht : ∀ᵐ y ∂PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2)),
        w ((2 : ℝ) • y + 0) = u ((2 : ℝ) • y + 0) := by
      filter_upwards [hv] with y hy
      simp only [w, add_zero, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
        one_smul, hy]
      ring
    have ht' := (PDE.DGNM.ae_comp_affineScale_ball_iff (0 : Vec d)
      (r := 2) (by norm_num) (1 / 2) (P := fun x => w x = u x)).mp ht
    norm_num only [mul_one_div, div_self (by norm_num : (2 : ℝ) ≠ 0)] at ht'
    change ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1), w x = u x
    change ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : Vec d) 1), w x = u x at ht'
    rw [hball 1 (by norm_num)] at ht'
    exact ht'
  · intro x y hx hy
    have hx' : (2 : ℝ)⁻¹ • x ∈ PDE.euclideanBall (0 : Vec d) (1 / 2) := by
      rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)]
      simp only [sub_zero, PDE.vecEuclideanNorm_smul]
      change |(2 : ℝ)⁻¹| * euclideanNorm x < 1 / 2
      norm_num
      linarith
    have hy' : (2 : ℝ)⁻¹ • y ∈ PDE.euclideanBall (0 : Vec d) (1 / 2) := by
      rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)]
      simp only [sub_zero, PDE.vecEuclideanNorm_smul]
      change |(2 : ℝ)⁻¹| * euclideanNorm y < 1 / 2
      norm_num
      linarith
    have hh' := holder_halfBall_lower_exponent hα (by positivity) hh
      _ hx' _ hy'
    have hn : PDE.vecEuclideanNorm ((2 : ℝ)⁻¹ • x - (2 : ℝ)⁻¹ • y) ≤
        euclideanNorm (x - y) := by
      rw [← smul_sub, PDE.vecEuclideanNorm_smul]
      change |(2 : ℝ)⁻¹| * euclideanNorm (x - y) ≤ euclideanNorm (x - y)
      norm_num
      exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (by norm_num)
    have hp := Real.rpow_le_rpow (PDE.vecEuclideanNorm_nonneg _) hn
      (le_min hα.le zero_le_one)
    have hs := Real.sqrt_le_sqrt henergy
    have hbound := mul_le_mul
      (mul_le_mul_of_nonneg_left hs hC) hp
      (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg _) _)
      (mul_nonneg hC (Real.sqrt_nonneg _))
    change C * _ * _ ≤ C * _ * _ at hbound
    have hn0 : 0 ≤ euclideanNorm (x - y) ^ min α 1 :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hE0 : 0 ≤ Real.sqrt (∫ z in ball (0 : Vec d) 2, (u z) ^ 2 ∂volume) :=
      Real.sqrt_nonneg _
    calc
      |w x - w y| = 2 * |v ((2 : ℝ)⁻¹ • x) - v ((2 : ℝ)⁻¹ • y)| := by
        dsimp [w]
        rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * ((C * Real.sqrt (∫ z in ball (0 : Vec d) 2, (u z) ^ 2 ∂volume)) *
          euclideanNorm (x - y) ^ min α 1) :=
        mul_le_mul_of_nonneg_left (hh'.trans hbound) (by norm_num)
      _ ≤ (2 * C + 1) * Real.sqrt (∫ z in ball (0 : Vec d) 2, (u z) ^ 2 ∂volume) *
          euclideanNorm (x - y) ^ min α 1 := by nlinarith [mul_nonneg hE0 hn0]

/-- The uniform rescaled estimate applies to every prescribed weak potential
on one coefficient event, so later gauges can be chosen compatibly across radii. -/
theorem ae_reduced_uniform_rescaled_harmonic_holder {d : ℕ} (hd : 2 ≤ d) {L r : ℝ}
    (Q : EnvironmentLaw d L r) :
    ∃ α C : ℝ, 0 < α ∧ 0 ≤ C ∧
      ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ R : ℝ, 0 < R →
        ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
          WeakSolution (ball 0 R) ω.1 u g → ∃ v : Vec d → ℝ,
            v =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2))]
              (fun y => R⁻¹ * u (R • y)) ∧
            PDE.EuclideanHolderSeminormLE (PDE.euclideanBall (0 : Vec d) (1 / 2))
              v α (C * Real.sqrt (∫ y in PDE.euclideanBall (0 : Vec d) 1,
                (R⁻¹ * u (R • y)) ^ 2)) := by
  let B := sourceReducedBound L
  have hB1 : 1 ≤ B := by
    have hL := Q.ellipticity_parameter
    dsimp [B, sourceReducedBound]
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity))
      (by nlinarith [sq_nonneg L])
  obtain ⟨α, C, hα, hC, hreg⟩ :=
    exists_uniform_rescaled_harmonic_holder_estimate d hd (B ^ 2) (by nlinarith)
  refine ⟨α, C, hα, hC, ?_⟩
  filter_upwards [ActualImageLpStateTransport.ae_reducedEnvironmentLaw_mem_image Q]
    with ω hω
  rcases hω with ⟨η, hη, rfl⟩
  have hc := sourceReducedBound_support Q.ellipticity_parameter hη
  intro R hR u g hw
  have hball : PDE.euclideanBall (0 : Vec d) R = ball 0 R := by
    ext x
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR
  rw [← hball] at hw
  let w := pdeH1OfSpatialWeakSolution hw
  have hsol : PDE.IsWeakDivergenceFormSolutionOn
      (fun x => B • (reduce η).1 x) _ w 0 0 := by
    convert (pdeH1OfSpatialWeakSolution_isSolution hw).smul_coefficient_source_forcing B
      using 1 <;> ext x <;> simp
  have hell : ∀ x ∈ PDE.euclideanBall (0 : Vec d) R,
      PDE.IsEllipticMatrix 1 (B ^ 2) (B • (reduce η).1 x) := by
    intro x _
    exact ParabolicBridge.isEllipticMatrix_smul_of_symm_bounds hc.1
      (hc.2.1 x).1 (fun ξ => ((hc.2.1 x).2 ξ).1)
      (fun ξ => ((hc.2.1 x).2 ξ).2)
  have hmeas : ∀ j k, AEMeasurable (fun x => (B • (reduce η).1 x) j k)
      (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) R)) := by
    intro j k
    exact (continuous_const.mul ((continuous_apply k).comp
      ((continuous_apply j).comp (reduce η).1.continuous))).measurable.aemeasurable
  obtain ⟨v, hv, hh⟩ := hreg R hR _ hmeas hell w hsol
  exact ⟨v, hv, hh⟩

/-- One full-measure coefficient event supplies the same interior estimate for
all weak scalar harmonic functions, including any constant shift. -/
theorem ae_reduced_uniform_physical_holder {d : ℕ} (hd : 2 ≤ d) {L r : ℝ}
    (Q : EnvironmentLaw d L r) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
        WeakSolution (ball 0 2) ω.1 u g → ∃ v : Vec d → ℝ,
          v =ᵐ[volume.restrict (ball (0 : Vec d) 1)] u ∧
          ∀ x y, euclideanNorm x < 1 → euclideanNorm y < 1 →
            |v x - v y| ≤ C * Real.sqrt (∫ z in ball (0 : Vec d) 2, (u z)^2 ∂volume) *
              euclideanNorm (x-y)^α := by
  obtain ⟨α, C, hα, hC, hreg⟩ := ae_reduced_uniform_rescaled_harmonic_holder hd Q
  refine ⟨min α 1, 2 * C + 1, lt_min hα zero_lt_one, min_le_right _ _, by positivity, ?_⟩
  filter_upwards [hreg] with ω hω
  intro u g hw
  obtain ⟨v, hv, hh⟩ := hω 2 (by norm_num) u g hw
  exact physical_holder_of_rescaled (u := u) (v := v) hα hC hv hh

/-- Canonical weak harmonic coordinates have a genuine scalar Hölder
representative on the unit ball, with constants chosen before the environment. -/
theorem canonical_spatial_harmonic_holder {d : ℕ} (hd : 2 ≤ d) {L r : ℝ}
    (Q : EnvironmentLaw d L r) (i : Fin d) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∃ (u v : Vec d → ℝ) (g : Vec d → Vec d),
        WeakSolution (ball 0 2) ω.1 u g ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1), v x = u x) ∧
        (∀ x y, euclideanNorm x < 1 → euclideanNorm y < 1 →
          |v x - v y| ≤ C * Real.sqrt (∫ z in ball (0 : Vec d) 2, (u z)^2 ∂volume) *
            euclideanNorm (x-y)^α) ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 2),
          g x = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x ω)).ofLp) := by
  obtain ⟨α, C, hα, hC, hreg⟩ := ae_canonical_rescaled_harmonic_holder hd Q i
  refine ⟨min α 1, 2 * C + 1, lt_min hα zero_lt_one, min_le_right _ _, by positivity, ?_⟩
  filter_upwards [hreg] with ω hω
  obtain ⟨u, g, v, hw, hg, hv, hh⟩ := hω 2 (by norm_num)
  obtain ⟨w, hwu, hwh⟩ := physical_holder_of_rescaled (u := u) (v := v) hα hC hv hh
  exact ⟨u, w, g, hw, hwu, hwh, ae_of_all _ hg⟩

/-- The source Euclidean Hölder bound gives continuity in the actual carrier. -/
theorem continuousOn_unitBall_of_euclidean_holder {d : ℕ} {v : Vec d → ℝ}
    {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hh : ∀ x y, euclideanNorm x < 1 → euclideanNorm y < 1 →
      |v x - v y| ≤ K * euclideanNorm (x-y)^α) :
    ContinuousOn v (ball (0 : Vec d) 1) := by
  have hball : PDE.euclideanBall (0 : Vec d) 1 = ball 0 1 := by
    ext x
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)
  have hh' : PDE.EuclideanHolderSeminormLE (PDE.euclideanBall (0 : Vec d) 1)
      v α K := by
    intro x hx y hy
    rw [hball] at hx hy
    exact hh x y (by simpa only [ball, Set.mem_ofPred_eq, sub_zero] using hx)
      (by simpa only [ball, Set.mem_ofPred_eq, sub_zero] using hy)
  rw [← hball]
  exact hh'.continuousOn hα hK

/-- Continuous rescaled versions on every ball determine one continuous
representative of the original global volume class. -/
theorem exists_continuous_representative_of_rescaled_holder {d : ℕ}
    (f : Vec d → ℝ) {α : ℝ} (hα : 0 < α)
    (h : ∀ R : ℝ, 0 < R → ∃ (v : Vec d → ℝ) (K : ℝ), 0 ≤ K ∧
      v =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2))]
        (fun y => R⁻¹ * f (R • y)) ∧
      PDE.EuclideanHolderSeminormLE (PDE.euclideanBall (0 : Vec d) (1 / 2))
        v α K) :
    ∃ w : Vec d → ℝ, Continuous w ∧ w =ᵐ[volume] f := by
  suffices hv : ∀ n : ℕ, ∃ w : Vec d → ℝ,
      ContinuousOn w (Metric.ball 0 ((n : ℝ) + 1)) ∧
      f =ᵐ[volume.restrict (Metric.ball 0 ((n : ℝ) + 1))] w by
    obtain ⟨hc, he⟩ := continuous_spatialRegularRepresentative_of_ball_versions f hv
    exact ⟨_, hc, he.symm⟩
  intro n
  let R : ℝ := 2 * ((d : ℝ) + 1) * ((n : ℝ) + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨v, K, hK, he, hh⟩ := h R hR
  let w : Vec d → ℝ := fun x => R * v (R⁻¹ • x)
  have hin (x : Vec d) (hx : x ∈ Metric.ball (0 : Vec d) ((n : ℝ) + 1)) :
      x ∈ PDE.euclideanBall (0 : Vec d) (R * (1 / 2)) := by
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)]
    simp only [sub_zero] at *
    change euclideanNorm x < R * (1 / 2)
    have hx' : ‖x‖ < (n : ℝ) + 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    have hb := (euclideanNorm_le_dimension_mul_norm x).trans_lt
      (mul_lt_mul_of_pos_left hx' (by positivity : 0 < (d : ℝ) + 1))
    dsimp [R]
    nlinarith
  have hscale (x : Vec d) (hx : x ∈ Metric.ball (0 : Vec d) ((n : ℝ) + 1)) :
      R⁻¹ • x ∈ PDE.euclideanBall (0 : Vec d) (1 / 2) := by
    have hx' := hin x hx
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)] at hx'
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)]
    simp only [sub_zero] at hx' ⊢
    rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_lt_iff₀ hR).mpr hx'
  refine ⟨w, ?_, ?_⟩
  · have hlin : Continuous (fun x : Vec d => R⁻¹ • x) :=
      continuous_id.const_smul R⁻¹
    exact continuousOn_const.mul ((hh.continuousOn hα hK).comp hlin.continuousOn hscale)
  · have ht : ∀ᵐ y ∂PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2)),
        w (R • y + 0) = f (R • y + 0) := by
      filter_upwards [he] with y hy
      simp only [w, add_zero, smul_smul, inv_mul_cancel₀ hR.ne', one_smul, hy]
      field_simp
    have ht' := (PDE.DGNM.ae_comp_affineScale_ball_iff (0 : Vec d)
      hR (1 / 2) (P := fun x => w x = f x)).mp ht
    have hr : w =ᵐ[volume.restrict (Metric.ball 0 ((n : ℝ) + 1))] f :=
      ae_restrict_of_ae_restrict_of_subset (fun x hx => hin x hx) ht'
    exact hr.symm

/-- Choosing a continuous version and fixing its value at zero preserves
the actual weak gradient and the full-radius centered AKM limit. -/
theorem continuous_origin_gauge_of_ae {d : ℕ} {ψ w : Vec d → ℝ}
    {G : Vec d → Vec d} (hc : Continuous w) (he : w =ᵐ[volume] ψ)
    (hw : HasWeakGradient Set.univ ψ G)
    (hm : ∀ R : ℝ, 0 < R → MemLp ψ 2 (volume.restrict (ball 0 R)))
    (hs : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
      (⨍ x in ball 0 R, (ψ x - ⨍ y in ball 0 R, ψ y ∂volume)^2 ∂volume))
      atTop (𝓝 0)) :
    ∃ χ : Vec d → ℝ, Continuous χ ∧ χ 0 = 0 ∧
      HasWeakGradient Set.univ χ G ∧
      (∀ R : ℝ, 0 < R → MemLp χ 2 (volume.restrict (ball 0 R))) ∧
      Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
        (⨍ x in ball 0 R, (χ x - ⨍ y in ball 0 R, χ y ∂volume)^2 ∂volume))
        atTop (𝓝 0) := by
  let χ : Vec d → ℝ := fun x => w x - w 0
  have hw' : HasWeakGradient Set.univ w G := by
    intro j
    apply (hw j).congr_ae
    · simpa only [Measure.restrict_univ] using he.symm
    · exact ae_eq_refl _
  have hmem (R : ℝ) (hR : 0 < R) : MemLp w 2 (volume.restrict (ball 0 R)) :=
    (memLp_congr_ae (ae_restrict_of_ae he)).mpr (hm R hR)
  refine ⟨χ, hc.sub continuous_const, sub_self _, hasWeakGradient_sub_const _ hw' _, ?_, ?_⟩
  · intro R hR
    letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr
        (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2.ne
    exact (hmem R hR).sub (memLp_const _)
  · apply hs.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hvol := ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)
    letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr hvol.2.ne
    have hmean : (⨍ y in ball 0 R, χ y ∂volume) =
        (⨍ y in ball 0 R, ψ y ∂volume) - w 0 := by
      calc
        _ = (⨍ y in ball 0 R, w y ∂volume) - ⨍ y in ball 0 R, w 0 ∂volume := by
          simpa only [χ, Pi.sub_apply] using
            (average_sub (f := w) (g := fun _ : Vec d => w 0)
              ((hmem R hR).integrable (by norm_num)) (integrable_const (w 0)))
        _ = _ := by
          rw [setAverage_const hvol.1.ne' hvol.2.ne,
            average_congr (ae_restrict_of_ae he)]
    have hsq : (⨍ x in ball 0 R, (χ x - ⨍ y in ball 0 R, χ y ∂volume)^2 ∂volume) =
        ⨍ x in ball 0 R, (ψ x - ⨍ y in ball 0 R, ψ y ∂volume)^2 ∂volume := by
      apply average_congr
      filter_upwards [ae_restrict_of_ae he] with x hx
      rw [hmean]
      dsimp only [χ]
      rw [hx]
      ring
    rw [hsq]

/-- The actual physical-law corrector has one global continuous version,
normalized at zero, with its canonical weak gradient and AKM sublinearity. -/
theorem ae_physical_continuous_canonical_sublinear_weak_potential {d : ℕ}
    (hd : 2 ≤ d) {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q, ∃ χ : Vec d → ℝ,
      Continuous χ ∧ χ 0 = 0 ∧
      HasWeakGradient Set.univ χ (fun x => ((canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate x (reduce ω.1))).ofLp) ∧
      (∀ R : ℝ, 0 < R → MemLp χ 2 (volume.restrict (ball 0 R))) ∧
      Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
        (⨍ x in ball 0 R, (χ x - ⨍ y in ball 0 R, χ y ∂volume)^2 ∂volume))
        atTop (𝓝 0) := by
  obtain ⟨α, C, hα, hC, hreg⟩ := ae_reduced_uniform_rescaled_harmonic_holder hd Q
  have hphysical := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae hreg
  filter_upwards [ae_physical_canonical_sublinear_weak_potential hd Q i, hphysical]
    with ω hpot hregω
  obtain ⟨ψ, hw, hm, hs, hharm⟩ := hpot
  obtain ⟨w, hwcont, hwψ⟩ := exists_continuous_representative_of_rescaled_holder
      (fun x => x i + ψ x) hα (by
    intro R hR
    obtain ⟨v, hv, hh⟩ := hregω R hR _ _ (hharm R hR)
    exact ⟨v, _, mul_nonneg hC (Real.sqrt_nonneg _), hv, hh⟩)
  have he : (fun x => w x - x i) =ᵐ[volume] ψ := by
    filter_upwards [hwψ] with x hx
    rw [hx]
    ring
  exact continuous_origin_gauge_of_ae (hwcont.sub (continuous_apply i)) he hw hm hs

/-- The canonical Hölder representative may be normalized at the origin.
The energy bound is reapplied to the shifted weak potential itself. -/
theorem canonical_spatial_harmonic_holder_normalized {d : ℕ} (hd : 2 ≤ d) {L r : ℝ}
    (Q : EnvironmentLaw d L r) (i : Fin d) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∃ (u v : Vec d → ℝ) (g : Vec d → Vec d),
        WeakSolution (ball 0 2) ω.1 u g ∧ v 0 = 0 ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1), v x = u x) ∧
        (∀ x y, euclideanNorm x < 1 → euclideanNorm y < 1 →
          |v x - v y| ≤ C * Real.sqrt (∫ z in ball (0 : Vec d) 2, (u z)^2 ∂volume) *
            euclideanNorm (x-y)^α) ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 2),
          g x = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x ω)).ofLp) := by
  obtain ⟨α, C, hα, hα1, hC, hreg⟩ := ae_reduced_uniform_physical_holder hd Q
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  filter_upwards [hreg, ae_canonical_ball_weakSolution hd Q i] with ω hω hpot
  obtain ⟨u, g, hw, hg⟩ := hpot 2 (by norm_num)
  obtain ⟨v, hvu, hvh⟩ := hω u g hw
  have hvfinite := ball_volume_pos_finite d 2 (by norm_num)
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) 2)) :=
    isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp hvfinite).2.ne
  have hw' := weakSolution_sub_const hw (v 0)
  obtain ⟨w, hwu, hwh⟩ := hω _ g hw'
  have heq : w =ᵐ[volume.restrict (ball (0 : Vec d) 1)] (fun x => v x - v 0) := by
    filter_upwards [hwu, hvu] with x hx hvx
    simpa only [hvx] using hx
  have hopen : IsOpen (ball (0 : Vec d) 1) := by
    have hball : PDE.euclideanBall (0 : Vec d) 1 = ball 0 1 := by
      ext x
      exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)
    rw [← hball]
    exact PDE.isOpen_euclideanBall _ _
  have heq' := Measure.eqOn_open_of_ae_eq heq hopen
    (continuousOn_unitBall_of_euclidean_holder hα (by positivity) hwh)
    ((continuousOn_unitBall_of_euclidean_holder hα (by positivity) hvh).sub continuousOn_const)
  have hz : (0 : Vec d) ∈ ball (0 : Vec d) 1 := by
    simp [ball, euclideanNorm, euclideanSq, dot]
  refine ⟨_, w, g, hw', ?_, hwu, hwh, ae_of_all _ hg⟩
  simpa only [sub_self] using heq' hz

/-- Subtracting the affine coordinate preserves a uniform Hölder estimate.
The exponent is lowered to at most one on this diameter-one ball. -/
theorem harmonic_holder_sub_coordinate {d : ℕ} {v : PDE.Vec d → ℝ}
    {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hh : PDE.EuclideanHolderSeminormLE
      (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2)) v α K) (i : Fin d) :
    PDE.EuclideanHolderSeminormLE (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2))
      (fun x => v x - x i) (min α 1) (K + 1) := by
  intro x hx y hy
  have hx' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 1 / 2)).mp hx
  have hy' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 1 / 2)).mp hy
  simp only [sub_zero] at hx' hy'
  have ht0 := PDE.vecEuclideanNorm_nonneg (x - y)
  have ht1 : PDE.vecEuclideanNorm (x - y) ≤ 1 := by
    have ht := PDE.vecEuclideanNorm_add_le x (-y)
    rw [PDE.vecEuclideanNorm_neg] at ht
    change PDE.vecEuclideanNorm (x - y) ≤ _ at ht
    linarith
  have hβ : 0 ≤ min α 1 := le_min hα.le zero_le_one
  have hpow := Real.rpow_le_rpow_of_exponent_ge' ht0 ht1 hβ (min_le_left α 1)
  have hlin : PDE.vecEuclideanNorm (x - y) ≤
      PDE.vecEuclideanNorm (x - y) ^ min α 1 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' ht0 ht1 hβ (min_le_right α 1)
  calc
    |(v x - x i) - (v y - y i)| = |(v x - v y) - (x i - y i)| := by
      congr 1; ring
    _ ≤ |v x - v y| + |x i - y i| := abs_sub _ _
    _ ≤ K * PDE.vecEuclideanNorm (x - y) ^ α + PDE.vecEuclideanNorm (x - y) :=
      add_le_add (hh x hx y hy) (PDE.abs_apply_le_vecEuclideanNorm (x - y) i)
    _ ≤ K * PDE.vecEuclideanNorm (x - y) ^ min α 1 +
        PDE.vecEuclideanNorm (x - y) ^ min α 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hpow hK) hlin
    _ = (K + 1) * PDE.vecEuclideanNorm (x - y) ^ min α 1 := by ring

/-- The AKM global potential and the scale estimates hold on one physical-law
event. Each scale is centered by the mean of that same global potential. -/
theorem ae_physical_canonical_centered_corrector_holder {d : ℕ} (hd : 2 ≤ d)
    {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
      ∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q, ∃ ψ : Vec d → ℝ,
        HasWeakGradient Set.univ ψ (fun x => ((canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x (reduce ω.1))).ofLp) ∧
        (∀ R : ℝ, 0 < R → MemLp ψ 2 (volume.restrict (ball 0 R))) ∧
        Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
          (⨍ x in ball 0 R, (ψ x - ⨍ y in ball 0 R, ψ y ∂volume)^2 ∂volume))
          atTop (𝓝 0) ∧
        Tendsto (fun R : ℝ => ∫ y in ball (0 : Vec d) 1,
          (R⁻¹ * (ψ (R • y) - ⨍ x in ball 0 R, ψ x ∂volume))^2 ∂volume)
          atTop (𝓝 0) ∧
        ∀ R : ℝ, 0 < R → ∃ v : Vec d → ℝ,
          v =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2))]
            (fun y => R⁻¹ * (ψ (R • y) - ⨍ x in ball 0 R, ψ x ∂volume)) ∧
          PDE.EuclideanHolderSeminormLE (PDE.euclideanBall (0 : Vec d) (1 / 2))
            v α (C * Real.sqrt (∫ y in PDE.euclideanBall (0 : Vec d) 1,
              (R⁻¹ * ((R • y) i + ψ (R • y) -
                ⨍ x in ball 0 R, ψ x ∂volume)) ^ 2) + 1) := by
  obtain ⟨α, C, hα, hC, hreg⟩ := ae_reduced_uniform_rescaled_harmonic_holder hd Q
  have hphysical := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae hreg
  refine ⟨min α 1, C, lt_min hα zero_lt_one, min_le_right _ _, hC, ?_⟩
  filter_upwards [ae_physical_canonical_sublinear_weak_potential hd Q i, hphysical]
    with ω hpot hω
  obtain ⟨ψ, hweak, hmem, hsub, hsol⟩ := hpot
  refine ⟨ψ, hweak, hmem, hsub, centered_rescaled_energy_tendsto_zero ψ hsub, ?_⟩
  intro R hR
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2.ne
  let m := ⨍ x in ball 0 R, ψ x ∂volume
  obtain ⟨v, hv, hh⟩ := hω R hR _ _ (weakSolution_sub_const (hsol R hR) m)
  refine ⟨fun y => v y - y i, ?_,
    harmonic_holder_sub_coordinate hα (by positivity) hh i⟩
  filter_upwards [hv] with y hy
  rw [hy]
  dsimp [m]
  simp only [Pi.smul_apply, smul_eq_mul, mul_sub, mul_add, ← mul_assoc,
    inv_mul_cancel₀ hR.ne', one_mul]
  ring

/-- The actual centered canonical corrector has one deterministic Hölder
constant at every sufficiently large scale, together with vanishing normalized
L² energy. The threshold may depend on the environment; the exponent and
constant precede the environment and all radii. -/
theorem ae_physical_canonical_eventual_uniform_holder {d : ℕ} (hd : 2 ≤ d)
    {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ α K : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < K ∧
      ∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q, ∃ ψ : Vec d → ℝ,
        HasWeakGradient Set.univ ψ (fun x => ((canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x (reduce ω.1))).ofLp) ∧
        (∀ R : ℝ, 0 < R → MemLp ψ 2 (volume.restrict (ball 0 R))) ∧
        Tendsto (fun R : ℝ => ∫ y in ball (0 : Vec d) 1,
          (R⁻¹ * (ψ (R • y) - ⨍ x in ball 0 R, ψ x ∂volume))^2 ∂volume)
          atTop (𝓝 0) ∧
        ∀ᶠ R : ℝ in atTop, ∃ v : Vec d → ℝ,
          v =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2))]
            (fun y => R⁻¹ * (ψ (R • y) - ⨍ x in ball 0 R, ψ x ∂volume)) ∧
          PDE.EuclideanHolderSeminormLE (PDE.euclideanBall (0 : Vec d) (1 / 2))
            v α K := by
  obtain ⟨α, C, hα, hα1, hC, hpot⟩ :=
    ae_physical_canonical_centered_corrector_holder hd Q i
  let K := C * Real.sqrt (2 * volume.real (ball (0 : Vec d) 1) + 2) + 1
  refine ⟨α, K, hα, hα1, by dsimp [K]; positivity, ?_⟩
  filter_upwards [hpot] with ω hω
  obtain ⟨ψ, hweak, hmem, _, hL2, hholder⟩ := hω
  refine ⟨ψ, hweak, hmem, hL2, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ), hL2.eventually (gt_mem_nhds zero_lt_one)]
    with R hR hsmall
  obtain ⟨v, hv, hh⟩ := hholder R hR
  let m := ⨍ x in ball 0 R, ψ x ∂volume
  let f : Vec d → ℝ := fun y => R⁻¹ * (ψ (R • y) - m)
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) 1)) :=
    isFiniteMeasure_restrict.mpr
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d 1 zero_lt_one)).2.ne
  have hf : MemLp f 2 (volume.restrict (ball (0 : Vec d) 1)) := by
    have hm := memLp_comp_affine_ball hR (hmem R hR)
    simp only [zero_add] at hm
    exact (hm.sub (memLp_const m)).const_mul R⁻¹
  have henergy : (∫ y in PDE.euclideanBall (0 : Vec d) 1,
      (R⁻¹ * ((R • y) i + ψ (R • y) - m))^2 ∂volume) ≤
      2 * volume.real (ball (0 : Vec d) 1) + 2 := by
    have heq : (fun y : Vec d => R⁻¹ * ((R • y) i + ψ (R • y) - m)) =
        (fun y => y i + f y) := by
      funext y
      dsimp [f]
      simp only [Pi.smul_apply, smul_eq_mul, mul_sub, mul_add, ← mul_assoc,
        inv_mul_cancel₀ hR.ne', one_mul]
      ring
    have hball : PDE.euclideanBall (0 : Vec d) 1 = ball 0 1 := by
      ext y
      exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one
    change (∫ y in PDE.euclideanBall (0 : Vec d) 1,
      ((fun z : Vec d => R⁻¹ * ((R • z) i + ψ (R • z) - m)) y)^2 ∂volume) ≤ _
    rw [heq, hball]
    have hb := coordinate_add_energy_le i hf
    have hs : (∫ y in ball (0 : Vec d) 1, (f y)^2 ∂volume) < 1 := hsmall
    linarith
  refine ⟨v, hv, ?_⟩
  have hK : C * Real.sqrt (∫ y in PDE.euclideanBall (0 : Vec d) 1,
      (R⁻¹ * ((R • y) i + ψ (R • y) - m))^2 ∂volume) + 1 ≤ K :=
    add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt henergy) hC)
      (le_refl (1 : ℝ))
  intro x hx y hy
  exact (hh x hx y hy).trans
    (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg _) _))

/-- The affine term is removed explicitly from the actual rescaled harmonic
coordinate. The resulting exponent is positive and at most one, uniformly in
the radius. The remaining factor is the displayed normalized harmonic energy. -/
theorem ae_canonical_rescaled_corrector_holder {d : ℕ} (hd : 2 ≤ d)
    {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
      ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ R : ℝ, 0 < R →
        ∃ (u : Vec d → ℝ) (g : Vec d → Vec d) (v : Vec d → ℝ),
          WeakSolution (ball 0 R) ω.1 u g ∧
          (∀ x, g x = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x ω)).ofLp) ∧
          v =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2))]
            (fun y => R⁻¹ * (u (R • y) - (R • y) i)) ∧
          PDE.EuclideanHolderSeminormLE (PDE.euclideanBall (0 : Vec d) (1 / 2))
            v α (C * Real.sqrt (∫ y in PDE.euclideanBall (0 : Vec d) 1,
              (R⁻¹ * u (R • y)) ^ 2) + 1) := by
  obtain ⟨α, C, hα, hC, hreg⟩ := ae_canonical_rescaled_harmonic_holder hd Q i
  refine ⟨min α 1, C, lt_min hα zero_lt_one, min_le_right _ _, hC, ?_⟩
  filter_upwards [hreg] with ω hω
  intro R hR
  obtain ⟨u, g, v, hw, hg, hv, hh⟩ := hω R hR
  refine ⟨u, g, (fun y => v y - y i), hw, hg, ?_,
    harmonic_holder_sub_coordinate hα (by positivity) hh i⟩
  filter_upwards [hv] with y hy
  rw [hy]
  simp only [Pi.smul_apply, smul_eq_mul, mul_sub, ← mul_assoc,
    inv_mul_cancel₀ hR.ne', one_mul]

open Environment.AKMTestIntegralSupport

/-- Pointwise symmetric ellipticity is a closed event on continuous fields. -/
theorem isClosed_continuous_elliptic_fields {d : ℕ} (B : ℝ) :
    IsClosed {a : CoefficientField d | IsElliptic B a} := by
  have hc (x ξ : Vec d) : Continuous
      (fun a : CoefficientField d => dot ξ ((a x).mulVec ξ)) := by
    unfold dot
    exact continuous_finset_sum _ fun j _ => continuous_const.mul
      ((continuous_apply j).comp
        ((continuous_eval_const x).matrix_mulVec continuous_const))
  simp only [IsElliptic, Set.setOf_forall, Set.setOf_and]
  exact isClosed_iInter fun x =>
    (isClosed_eq (continuous_eval_const x).matrix_transpose (continuous_eval_const x)).inter
      (isClosed_iInter fun ξ => (isClosed_le continuous_const (hc x ξ)).inter
        (isClosed_le (hc x ξ) continuous_const))

/-- Undoing the normalization gives a continuous elliptic coefficient on the
actual coefficient law, with pointwise agreement on every physical project. -/
theorem exists_measurable_reduced_akm_coefficient {d : ℕ} {L r : ℝ}
    (Q : EnvironmentLaw d L r) :
    ∃ A : Coefficient d (AKMUpperEllipticity L) → CoefficientField d,
      Measurable A ∧
      (∀ᵐ a ∂actualCoefficientLaw Q, IsElliptic (sourceReducedBound L) (A a)) ∧
      ∀ ω : ReductionImageV3.PhysicalField d L,
        A (Environment.AKMTestIntegralSupport.project (r₀ := r)
          Q.ellipticity_parameter ω) = (reduce ω.1).1 := by
  obtain ⟨R, hR, hReq⟩ :=
    Environment.AKMTestIntegralSupport.exists_measurable_continuous_reconstruction
      (d := d) (K := AKMUpperEllipticity L)
  let A := akmReducedReconstruction r R
  have hA : Measurable A := (measurable_rescaleCoefficientField d _ _).comp hR
  have hid (ω : ReductionImageV3.PhysicalField d L) :
      A (Environment.AKMTestIntegralSupport.project (r₀ := r)
        Q.ellipticity_parameter ω) = (reduce ω.1).1 :=
    akmReducedReconstruction_project Q.ellipticity_parameter
      (zero_lt_one.trans_le Q.range_parameter).ne' R hReq ω
  refine ⟨A, hA, ?_, hid⟩
  apply (ae_map_iff
    (Environment.AKMTestIntegralSupport.measurable_project Q.ellipticity_parameter).aemeasurable
    ((isClosed_continuous_elliptic_fields (sourceReducedBound L)).measurableSet.preimage hA)).mpr
  exact ae_of_all _ fun ω => by
    rw [hid ω]
    exact (sourceReducedBound_support Q.ellipticity_parameter ω.property).2.1

/-- Every continuous symmetric uniformly elliptic coefficient admits a global
continuous representative of a prescribed affine harmonic weak potential. -/
theorem exists_continuous_affine_weak_potential {d : ℕ} (hd : 2 ≤ d)
    (B : ℝ) (hB : 1 ≤ B) (a : CoefficientField d) (ha : IsElliptic B a)
    (i : Fin d) (ψ : Vec d → ℝ) (g : Vec d → Vec d)
    (hharm : ∀ R : ℝ, 0 < R →
      WeakSolution (ball 0 R) a (fun x => x i + ψ x) (fun x => unitVector i + g x)) :
    ∃ w : Vec d → ℝ, Continuous w ∧ w =ᵐ[volume] ψ := by
  obtain ⟨α, C, hα, hC, hreg⟩ :=
    exists_uniform_rescaled_harmonic_holder_estimate d hd (B ^ 2) (by nlinarith)
  obtain ⟨w, hw, he⟩ := exists_continuous_representative_of_rescaled_holder
      (fun x => x i + ψ x) hα (by
    intro R hR
    have hball : PDE.euclideanBall (0 : Vec d) R = ball 0 R := by
      ext x
      exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR
    have hsol := hharm R hR
    rw [← hball] at hsol
    let u := pdeH1OfSpatialWeakSolution hsol
    have hu : PDE.IsWeakDivergenceFormSolutionOn (fun x => B • a x) _ u 0 0 := by
      convert (pdeH1OfSpatialWeakSolution_isSolution hsol).smul_coefficient_source_forcing B
        using 1 <;> ext x <;> simp
    have hell : ∀ x ∈ PDE.euclideanBall (0 : Vec d) R,
        PDE.IsEllipticMatrix 1 (B ^ 2) (B • a x) := by
      intro x _
      exact ParabolicBridge.isEllipticMatrix_smul_of_symm_bounds hB (ha x).1
        (fun ξ => ((ha x).2 ξ).1) (fun ξ => ((ha x).2 ξ).2)
    have hm : ∀ j k, AEMeasurable (fun x => (B • a x) j k)
        (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) R)) := by
      intro j k
      exact (continuous_const.mul ((continuous_apply k).comp
        ((continuous_apply j).comp a.continuous))).measurable.aemeasurable
    obtain ⟨v, hv, hh⟩ := hreg R hR _ hm hell u hu
    exact ⟨v, _, mul_nonneg hC (Real.sqrt_nonneg _), hv, hh⟩)
  refine ⟨fun x => w x - x i, hw.sub (continuous_apply i), ?_⟩
  filter_upwards [he] with x hx
  rw [hx]
  ring

/-- The canonical flux remains divergence-free after measurable reconstruction
on the actual raw coefficient carrier. -/
theorem ae_reconstructed_canonical_flux_divergence {d : ℕ} [Fact (2 ≤ d)]
    {L r : ℝ} (Q : EnvironmentLaw d L r) (i : Fin d)
    (A : Coefficient d (AKMUpperEllipticity L) → CoefficientField d)
    (hA : Measurable A)
    (hAid : ∀ ω : ReductionImageV3.PhysicalField d L,
      A (Environment.AKMTestIntegralSupport.project (r₀ := r)
        Q.ellipticity_parameter ω) = (reduce ω.1).1)
    (G : Coefficient d (AKMUpperEllipticity L) → Vec d → EuclideanSpace ℝ (Fin d))
    (hG : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => G p.1 p.2))
    (hid : ∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q,
      ∀ᵐ x ∂(volume : Measure (Vec d)),
        G (Environment.AKMTestIntegralSupport.project (r₀ := r)
          Q.ellipticity_parameter ω) x = (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x (reduce ω.1))) :
    ∀ᵐ a ∂actualCoefficientLaw Q, HasWeakDivergence Set.univ
      (fun x => (A a x).mulVec (unitVector i + (G a x).ofLp)) (fun _ => 0) := by
  let π := Environment.AKMTestIntegralSupport.project (d := d) (r₀ := r) Q.ellipticity_parameter
  have hπ := Environment.AKMTestIntegralSupport.measurable_project
    (d := d) (r₀ := r) Q.ellipticity_parameter
  let J := fun (a : Coefficient d (AKMUpperEllipticity L)) (x : Vec d) =>
    (A a x).mulVec (unitVector i + (G a x).ofLp)
  have hAj : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      A p.1 p.2) := continuous_eval.measurable.comp
    ((hA.comp measurable_fst).prodMk measurable_snd)
  have hGj := (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp hG
  have hJ : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      J p.1 p.2) := (show Continuous (fun p : Mat d × Vec d => p.1.mulVec p.2) from
    continuous_fst.matrix_mulVec continuous_snd).measurable.comp
      (hAj.prodMk (measurable_const.add hGj))
  have hsource := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    ((ae_spatialRealization_memLp_on_all_compacts (reducedEnvironmentLaw_stationary Q)
      (canonicalCorrectorFlux Q i)).and (ae_canonicalCorrectorFlux_hasWeakDivergence Q i))
  have hflux := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_spatial_canonicalCorrectorFlux Q i measurable_id)
  have heq : ∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q,
      J (π ω) =ᵐ[volume]
        (fun x => (canonicalCorrectorFlux Q i (translate x (reduce ω.1))).ofLp) := by
    filter_upwards [hid, hflux] with ω hg hf
    filter_upwards [hg, hf] with x hx hfx
    dsimp only [J, π]
    rw [hAid ω, hx]
    exact hfx.symm
  let C := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  have hlocal : ∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q,
      ∀ K : Set (Vec d), IsCompact K → MemLp (J (π ω)) 2 (volume.restrict K) := by
    filter_upwards [hsource, heq] with ω hω he
    intro K hK
    exact (memLp_congr_ae (ae_restrict_of_ae he)).mpr (C.comp_memLp' (hω.1 K hK))
  have hweak : ∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q,
      HasWeakDivergence Set.univ (J (π ω)) (fun _ => 0) := by
    filter_upwards [hsource, heq] with ω hω he
    apply hω.2.congr_ae
    · simpa only [Measure.restrict_univ] using he.symm
    · exact ae_eq_refl _
  exact ae_weakDivergence_zero_of_pullback _ π hπ J hJ hlocal hweak

/-- The same jointly measurable AKM gradient admits a continuous origin-zero
sublinear weak potential on the literal actual coefficient law. -/
theorem exists_continuous_akm_sublinear_weakPotential
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) (i : Fin d) :
    ∃ G : Coefficient d (AKMUpperEllipticity L) → Vec d → EuclideanSpace ℝ (Fin d),
      Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => G p.1 p.2) ∧
      (∀ᵐ a ∂actualCoefficientLaw Q, ∃ χ : Vec d → ℝ,
        Continuous χ ∧ χ 0 = 0 ∧
        HasWeakGradient Set.univ χ (fun x => (G a x).ofLp) ∧
        (∀ R : ℝ, 0 < R → MemLp χ 2 (volume.restrict (ball 0 R))) ∧
        Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
          (⨍ x in ball 0 R, (χ x - ⨍ y in ball 0 R, χ y ∂volume)^2 ∂volume))
          atTop (𝓝 0)) ∧
      (∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q,
        ∀ᵐ x ∂(volume : Measure (Vec d)),
          G (Environment.AKMTestIntegralSupport.project (r₀ := r)
            Q.ellipticity_parameter ω) x = (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x (reduce ω.1))) := by
  obtain ⟨G, hG, hpot, hid⟩ := exists_akm_sublinear_global_weakPotential
    ballPoincareEstimate_from_pde Q i
  obtain ⟨A, hA, hell, hAid⟩ := exists_measurable_reduced_akm_coefficient Q
  have hdiv := ae_reconstructed_canonical_flux_divergence Q i A hA hAid G hG hid
  refine ⟨G, hG, ?_, hid⟩
  filter_upwards [hpot, hell, hdiv] with a hp ha hdiva
  obtain ⟨hGlocal, ψ, hw, hm, hs⟩ := hp
  have hharm (R : ℝ) (hR : 0 < R) : WeakSolution (ball 0 R) (A a)
      (fun x => x i + ψ x) (fun x => unitVector i + (G a x).ofLp) := by
    have hg : MemLp (fun x => (G a x).ofLp) 2 (volume.restrict (ball 0 R)) := by
      apply memLp_pi_iff.mpr
      intro j
      exact (hGlocal R hR).eval_piLp j
    exact affine_weakSolution_of_weakPotential R hR i (A a) ψ _ (hm R hR) hg
      (fun j => HasWeakPartialDerivative.restrict_subset
        (Set.subset_univ _) MeasurableSet.univ (hw j))
      (HasWeakDivergence.restrict_subset (Set.subset_univ _) MeasurableSet.univ hdiva)
  have hB : 1 ≤ sourceReducedBound L := by
    dsimp [sourceReducedBound]
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by linarith [Q.ellipticity_parameter]))
      (by nlinarith [Q.ellipticity_parameter, sq_nonneg L])
  obtain ⟨w, hc, he⟩ := exists_continuous_affine_weak_potential Fact.out
    (sourceReducedBound L) hB (A a) ha i ψ (fun x => (G a x).ofLp) hharm
  exact continuous_origin_gauge_of_ae hc he hw hm hs

/-- An eventual uniform Hölder bound suffices for the deterministic L² upgrade. -/
theorem eventual_holder_l2_small_implies_uniform_small {d : ℕ} (hd : 1 ≤ d)
    (f : ℕ → Vec d → ℝ) (α C : ℝ) (hα : 0 < α) (hC : 0 ≤ C)
    (hmem : ∀ n, MemLp (f n) 2 (volume.restrict (ball (0 : Vec d) 1)))
    (hholder : ∀ᶠ n in atTop, ∀ x y, euclideanNorm x < 1 → euclideanNorm y < 1 →
      |f n x - f n y| ≤ C * euclideanNorm (x-y)^α)
    (hL2 : Tendsto (fun n => ∫ x in ball (0 : Vec d) 1, (f n x)^2 ∂volume)
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x,
      euclideanNorm x ≤ 1/2 → |f n x| ≤ ε := by
  classical
  let P := fun n => ∀ x y, euclideanNorm x < 1 → euclideanNorm y < 1 →
    |f n x - f n y| ≤ C * euclideanNorm (x-y)^α
  let g := fun n x => if P n then f n x else 0
  have he : g =ᶠ[atTop] f := hholder.mono fun n hn => by
    funext x
    exact ite_eq_left hn
  have hm : ∀ n, MemLp (g n) 2 (volume.restrict (ball (0 : Vec d) 1)) := by
    intro n
    by_cases hp : P n
    · simpa only [g, ite_eq_left hp] using hmem n
    · simpa only [g, ite_eq_right hp] using
        (MemLp.zero' : MemLp (fun _ : Vec d => (0 : ℝ)) 2 _)
  have hh : ∀ n x y, euclideanNorm x < 1 → euclideanNorm y < 1 →
      |g n x - g n y| ≤ C * euclideanNorm (x-y)^α := by
    intro n x y hx hy
    by_cases hp : P n
    · simpa only [g, ite_eq_left hp] using hp x y hx hy
    · simp only [g, ite_eq_right hp, sub_self, abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hl : Tendsto (fun n => ∫ x in ball (0 : Vec d) 1, (g n x)^2 ∂volume)
      atTop (𝓝 0) := hL2.congr' (he.symm.mono fun n hn => by rw [hn])
  intro ε hε
  filter_upwards [holder_l2_small_implies_uniform_small hd g α C hα hC hm hh hl ε hε,
    he] with n hn heq
  simpa only [heq] using hn

/-- Centered AKM sublinearity and eventual scale-independent Hölder control
force uniform sublinearity of the origin-zero potential at all real radii. -/
theorem uniform_sublinearity_of_rescaled_holder {d : ℕ} (hd : 1 ≤ d)
    (χ : Vec d → ℝ) (hzero : χ 0 = 0)
    (hmem : ∀ R : ℝ, 0 < R → MemLp χ 2 (volume.restrict (ball 0 R)))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
      (⨍ x in ball 0 R, (χ x - ⨍ y in ball 0 R, χ y ∂volume)^2 ∂volume))
      atTop (𝓝 0)) (α C : ℝ) (hα : 0 < α) (hC : 0 ≤ C)
    (hholder : ∀ᶠ R : ℝ in atTop, ∀ x y,
      euclideanNorm x < 1 → euclideanNorm y < 1 →
      |R⁻¹ * (χ (R • x) - χ (R • y))| ≤ C * euclideanNorm (x-y)^α) :
    ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → |χ x|/(t+1) ≤ ε := by
  let S := fun n : ℕ => 2 * ((n : ℝ) + 1)
  have hS (n : ℕ) : 0 < S n := by dsimp [S]; positivity
  have ht : Tendsto S atTop atTop := Tendsto.const_mul_atTop (by norm_num)
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  let f := fun n x => (S n)⁻¹ *
    (χ (S n • x) - ⨍ y in ball 0 (S n), χ y ∂volume)
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) 1)) :=
    isFiniteMeasure_restrict.mpr
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d 1 zero_lt_one)).2.ne
  have hm : ∀ n, MemLp (f n) 2 (volume.restrict (ball (0 : Vec d) 1)) := by
    intro n
    have hp := memLp_comp_affine_ball (hS n) (hmem (S n) (hS n))
    simp only [zero_add] at hp
    exact (hp.sub (memLp_const _)).const_mul _
  have hh : ∀ᶠ n in atTop, ∀ x y, euclideanNorm x < 1 → euclideanNorm y < 1 →
      |f n x - f n y| ≤ C * euclideanNorm (x-y)^α := by
    filter_upwards [ht.eventually hholder] with n hn
    intro x y hx hy
    convert hn x y hx hy using 1
    congr 1
    dsimp [f]
    ring
  have hl := (centered_rescaled_energy_tendsto_zero χ hsub).comp ht
  have hsmall := eventual_holder_l2_small_implies_uniform_small hd f α C hα hC hm hh hl
  apply real_scale_uniform_sublinearity_of_nat_scale
  intro ε hε
  filter_upwards [hsmall (ε / 4) (by positivity)] with n hn
  intro x hx
  have hn0 : 0 < (n : ℝ) + 1 := by positivity
  have hy : euclideanNorm ((S n)⁻¹ • x) ≤ 1/2 := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr (hS n))]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hz := (mul_le_mul_of_nonneg_left hx (inv_pos.mpr (hS n)).le)
    dsimp [S] at hz ⊢
    nlinarith [inv_mul_cancel₀ (hS n).ne']
  have hz : euclideanNorm (0 : Vec d) ≤ 1/2 := by
    simp only [euclideanNorm, euclideanSq, dot, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, Real.sqrt_zero]
    norm_num
  have he : f n ((S n)⁻¹ • x) - f n 0 = (S n)⁻¹ * χ x := by
    dsimp [f]
    rw [smul_smul, mul_inv_cancel₀ (hS n).ne', one_smul, smul_zero, hzero]
    ring
  have hb : |(S n)⁻¹ * χ x| ≤ ε / 2 := by
    rw [← he]
    exact (abs_sub _ _).trans (by linarith [hn _ hy, hn 0 hz])
  have hb' : |χ x| ≤ ε / 2 * S n := (div_le_iff₀ (hS n)).mp (by
    simpa only [abs_mul, abs_of_pos (inv_pos.mpr (hS n)), div_eq_mul_inv, mul_comm]
      using hb)
  apply (div_le_iff₀ hn0).mpr
  dsimp [S] at hb'
  nlinarith

/-- A continuous affine harmonic potential satisfying the centered AKM limit
has one Hölder constant for all sufficiently large rescaled half-balls. -/
theorem exists_eventual_rescaled_corrector_holder {d : ℕ} (hd : 2 ≤ d)
    (B : ℝ) (hB : 1 ≤ B) (a : CoefficientField d) (ha : IsElliptic B a)
    (i : Fin d) (χ : Vec d → ℝ) (hc : Continuous χ)
    (hmem : ∀ R : ℝ, 0 < R → MemLp χ 2 (volume.restrict (ball 0 R)))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
      (⨍ x in ball 0 R, (χ x - ⨍ y in ball 0 R, χ y ∂volume)^2 ∂volume))
      atTop (𝓝 0)) (g : Vec d → Vec d)
    (hharm : ∀ R : ℝ, 0 < R →
      WeakSolution (ball 0 R) a (fun x => x i + χ x) (fun x => unitVector i + g x)) :
    ∃ α K : ℝ, 0 < α ∧ 0 ≤ K ∧ ∀ᶠ R : ℝ in atTop,
      PDE.EuclideanHolderSeminormLE (PDE.euclideanBall (0 : Vec d) (1/2))
        (fun y => R⁻¹ * (χ (R • y) - ⨍ x in ball 0 R, χ x ∂volume)) α K := by
  obtain ⟨α, C, hα, hC, hreg⟩ :=
    exists_uniform_rescaled_harmonic_holder_estimate d hd (B ^ 2) (by nlinarith)
  let K := C * Real.sqrt (2 * volume.real (ball (0 : Vec d) 1) + 2) + 1
  refine ⟨min α 1, K, lt_min hα zero_lt_one, by dsimp [K]; positivity, ?_⟩
  have hL2 := centered_rescaled_energy_tendsto_zero χ hsub
  filter_upwards [eventually_gt_atTop (0 : ℝ), hL2.eventually (gt_mem_nhds zero_lt_one)]
    with R hR hsmall
  let m := ⨍ x in ball 0 R, χ x ∂volume
  let f : Vec d → ℝ := fun y => R⁻¹ * (χ (R • y) - m)
  have hball : PDE.euclideanBall (0 : Vec d) R = ball 0 R := by
    ext x
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2.ne
  have hsol := weakSolution_sub_const (hharm R hR) m
  rw [← hball] at hsol
  let u := pdeH1OfSpatialWeakSolution hsol
  have hu : PDE.IsWeakDivergenceFormSolutionOn (fun x => B • a x) _ u 0 0 := by
    convert (pdeH1OfSpatialWeakSolution_isSolution hsol).smul_coefficient_source_forcing B
      using 1 <;> ext x <;> simp
  have hell : ∀ x ∈ PDE.euclideanBall (0 : Vec d) R,
      PDE.IsEllipticMatrix 1 (B ^ 2) (B • a x) := by
    intro x _
    exact ParabolicBridge.isEllipticMatrix_smul_of_symm_bounds hB (ha x).1
      (fun ξ => ((ha x).2 ξ).1) (fun ξ => ((ha x).2 ξ).2)
  have hm : ∀ j k, AEMeasurable (fun x => (B • a x) j k)
      (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) R)) := by
    intro j k
    exact (continuous_const.mul ((continuous_apply k).comp
      ((continuous_apply j).comp a.continuous))).measurable.aemeasurable
  obtain ⟨v, hv, hh⟩ := hreg R hR _ hm hell u hu
  have hv' : (fun y => v y - y i) =ᵐ[
      PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1/2))] f := by
    filter_upwards [hv] with y hy
    rw [hy]
    change R⁻¹ * ((R • y) i + χ (R • y) - m) - y i = f y
    dsimp [f]
    simp only [Pi.smul_apply, smul_eq_mul, mul_sub, mul_add, ← mul_assoc,
      inv_mul_cancel₀ hR.ne', one_mul]
    ring
  have hfcont : Continuous f :=
    continuous_const.mul ((hc.comp (continuous_id.const_smul R)).sub continuous_const)
  have hvh := harmonic_holder_sub_coordinate hα (by positivity) hh i
  have heq := Measure.eqOn_open_of_ae_eq hv' (PDE.isOpen_euclideanBall _ _)
    (hvh.continuousOn (lt_min hα zero_lt_one) (by positivity)) hfcont.continuousOn
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) 1)) :=
    isFiniteMeasure_restrict.mpr
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d 1 zero_lt_one)).2.ne
  have hf : MemLp f 2 (volume.restrict (ball (0 : Vec d) 1)) := by
    have hm := memLp_comp_affine_ball hR (hmem R hR)
    simp only [zero_add] at hm
    exact (hm.sub (memLp_const m)).const_mul R⁻¹
  have henergy : (∫ y in PDE.euclideanBall (0 : Vec d) 1,
      (R⁻¹ * ((R • y) i + χ (R • y) - m))^2 ∂volume) ≤
      2 * volume.real (ball (0 : Vec d) 1) + 2 := by
    have heq : (fun y : Vec d => R⁻¹ * ((R • y) i + χ (R • y) - m)) =
        (fun y => y i + f y) := by
      funext y
      dsimp [f]
      simp only [Pi.smul_apply, smul_eq_mul, mul_sub, mul_add, ← mul_assoc,
        inv_mul_cancel₀ hR.ne', one_mul]
      ring
    have hball : PDE.euclideanBall (0 : Vec d) 1 = ball 0 1 := by
      ext y
      exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one
    change (∫ y in PDE.euclideanBall (0 : Vec d) 1,
      ((fun z : Vec d => R⁻¹ * ((R • z) i + χ (R • z) - m)) y)^2 ∂volume) ≤ _
    rw [heq, hball]
    have hb := coordinate_add_energy_le i hf
    have hs : (∫ y in ball (0 : Vec d) 1, (f y)^2 ∂volume) < 1 := hsmall
    linarith
  have hK : C * Real.sqrt (∫ y in PDE.euclideanBall (0 : Vec d) 1,
      (R⁻¹ * ((R • y) i + χ (R • y) - m))^2 ∂volume) + 1 ≤ K :=
    add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt henergy) hC)
      (le_refl (1 : ℝ))
  intro x hx y hy
  change |f x - f y| ≤ _
  rw [← heq hx, ← heq hy]
  exact (hvh x hx y hy).trans
    (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg _) _))

/-- Ellipticity upgrades the centered AKM limit of an origin-zero continuous
corrector to uniform sublinearity on every expanding Euclidean ball. -/
theorem uniform_sublinearity_of_affine_harmonic {d : ℕ} (hd : 2 ≤ d)
    (B : ℝ) (hB : 1 ≤ B) (a : CoefficientField d) (ha : IsElliptic B a)
    (i : Fin d) (χ : Vec d → ℝ) (hc : Continuous χ) (hzero : χ 0 = 0)
    (hmem : ∀ R : ℝ, 0 < R → MemLp χ 2 (volume.restrict (ball 0 R)))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
      (⨍ x in ball 0 R, (χ x - ⨍ y in ball 0 R, χ y ∂volume)^2 ∂volume))
      atTop (𝓝 0)) (g : Vec d → Vec d)
    (hharm : ∀ R : ℝ, 0 < R →
      WeakSolution (ball 0 R) a (fun x => x i + χ x) (fun x => unitVector i + g x)) :
    ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → |χ x|/(t+1) ≤ ε := by
  obtain ⟨α, K, hα, hK, hh⟩ :=
    exists_eventual_rescaled_corrector_holder hd B hB a ha i χ hc hmem hsub g hharm
  apply uniform_sublinearity_of_rescaled_holder (by omega) χ hzero hmem hsub α (2*K)
    hα (mul_nonneg (by norm_num) hK)
  have ht : Tendsto (fun R : ℝ => 2 * R) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  filter_upwards [ht.eventually hh, eventually_gt_atTop (0 : ℝ)] with R hholder hR
  intro x y hx hy
  have hin (z : Vec d) (hz : euclideanNorm z < 1) :
      (1/2 : ℝ) • z ∈ PDE.euclideanBall (0 : Vec d) (1/2) := by
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)]
    simp only [sub_zero]
    change euclideanNorm ((1/2 : ℝ) • z) < 1/2
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    linarith
  have hscale (z : Vec d) : (2*R) • ((1/2 : ℝ) • z) = R • z := by
    rw [smul_smul]
    congr 1
    ring
  have hb : |(2*R)⁻¹ * (χ (R • x) - χ (R • y))| ≤
      K * euclideanNorm ((1/2 : ℝ) • x - (1/2 : ℝ) • y)^α := by
    convert hholder _ (hin x hx) _ (hin y hy) using 1
    dsimp only
    · rw [hscale x, hscale y]
      congr 1
      ring
    · rfl
  have hnorm : euclideanNorm ((1/2 : ℝ) • x - (1/2 : ℝ) • y) ≤
      euclideanNorm (x-y) := by
    rw [← smul_sub, TimeChange.euclideanNorm_smul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    exact mul_le_of_le_one_left (PDE.vecEuclideanNorm_nonneg (x-y)) (by norm_num)
  have hp := Real.rpow_le_rpow (Real.sqrt_nonneg _) hnorm hα.le
  have heq : R⁻¹ * (χ (R • x) - χ (R • y)) =
      2 * ((2*R)⁻¹ * (χ (R • x) - χ (R • y))) := by
    field_simp [hR.ne']
    <;> ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |(2*R)⁻¹ * (χ (R • x) - χ (R • y))| ≤
        2 * (K * euclideanNorm ((1/2 : ℝ) • x - (1/2 : ℝ) • y)^α) := by
      exact mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 2 * (K * euclideanNorm (x-y)^α) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hK) (by norm_num)
    _ = (2*K) * euclideanNorm (x-y)^α := by ring

/-- The jointly measurable canonical AKM gradient admits a continuous,
origin-zero potential that is uniformly sublinear on the actual coefficient law.
The physical-law gradient identification is retained for the same gradient. -/
theorem exists_uniformly_sublinear_canonical_corrector
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) (i : Fin d) :
    ∃ G : Coefficient d (AKMUpperEllipticity L) → Vec d → EuclideanSpace ℝ (Fin d),
      Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => G p.1 p.2) ∧
      (∀ᵐ a ∂actualCoefficientLaw Q, ∃ χ : Vec d → ℝ,
        Continuous χ ∧ χ 0 = 0 ∧
        HasWeakGradient Set.univ χ (fun x => (G a x).ofLp) ∧
        (∀ R : ℝ, 0 < R → MemLp χ 2 (volume.restrict (ball 0 R))) ∧
        Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
          (⨍ x in ball 0 R, (χ x - ⨍ y in ball 0 R, χ y ∂volume)^2 ∂volume))
          atTop (𝓝 0) ∧
        ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
          ∀ x, euclideanNorm x ≤ (t+1)*R → |χ x|/(t+1) ≤ ε) ∧
      (∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q,
        ∀ᵐ x ∂(volume : Measure (Vec d)),
          G (Environment.AKMTestIntegralSupport.project (r₀ := r)
            Q.ellipticity_parameter ω) x = (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x (reduce ω.1))) := by
  obtain ⟨G, hG, hpot, hid⟩ := exists_akm_sublinear_global_weakPotential
    ballPoincareEstimate_from_pde Q i
  obtain ⟨A, hA, hell, hAid⟩ := exists_measurable_reduced_akm_coefficient Q
  have hdiv := ae_reconstructed_canonical_flux_divergence Q i A hA hAid G hG hid
  refine ⟨G, hG, ?_, hid⟩
  filter_upwards [hpot, hell, hdiv] with a hp ha hdiva
  obtain ⟨hGlocal, ψ, hw, hm, hs⟩ := hp
  have hmake (φ : Vec d → ℝ)
      (hwφ : HasWeakGradient Set.univ φ (fun x => (G a x).ofLp))
      (hmφ : ∀ R : ℝ, 0 < R → MemLp φ 2 (volume.restrict (ball 0 R)))
      (R : ℝ) (hR : 0 < R) : WeakSolution (ball 0 R) (A a)
      (fun x => x i + φ x) (fun x => unitVector i + (G a x).ofLp) := by
    have hg : MemLp (fun x => (G a x).ofLp) 2 (volume.restrict (ball 0 R)) := by
      apply memLp_pi_iff.mpr
      intro j
      exact (hGlocal R hR).eval_piLp j
    exact affine_weakSolution_of_weakPotential R hR i (A a) φ _ (hmφ R hR) hg
      (fun j => HasWeakPartialDerivative.restrict_subset
        (Set.subset_univ _) MeasurableSet.univ (hwφ j))
      (HasWeakDivergence.restrict_subset (Set.subset_univ _) MeasurableSet.univ hdiva)
  have hB : 1 ≤ sourceReducedBound L := by
    dsimp [sourceReducedBound]
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by linarith [Q.ellipticity_parameter]))
      (by nlinarith [Q.ellipticity_parameter, sq_nonneg L])
  obtain ⟨w, hc, he⟩ := exists_continuous_affine_weak_potential Fact.out
    (sourceReducedBound L) hB (A a) ha i ψ (fun x => (G a x).ofLp) (hmake ψ hw hm)
  obtain ⟨χ, hcχ, hzχ, hwχ, hmχ, hsχ⟩ := continuous_origin_gauge_of_ae hc he hw hm hs
  exact ⟨χ, hcχ, hzχ, hwχ, hmχ, hsχ,
    uniform_sublinearity_of_affine_harmonic Fact.out (sourceReducedBound L) hB
      (A a) ha i χ hcχ hzχ hmχ hsχ _ (hmake χ hwχ hmχ)⟩

/-- Under the physical reference law, the canonical corrector has a continuous,
origin-zero potential uniformly sublinear at every positive spatial scale. -/
theorem ae_physical_uniformly_sublinear_canonical_corrector
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) (i : Fin d) :
    ∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q, ∃ χ : Vec d → ℝ,
      Continuous χ ∧ χ 0 = 0 ∧
      (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∀ x, euclideanNorm x ≤ (t+1)*R → |χ x|/(t+1) ≤ ε) ∧
      HasWeakGradient Set.univ χ (fun x =>
        ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) (translate x (reduce ω.1))).ofLp) ∧
      (∀ R : ℝ, 0 < R → MemLp χ 2 (volume.restrict (ball 0 R))) := by
  obtain ⟨G, _, hpot, hid⟩ := exists_uniformly_sublinear_canonical_corrector Q i
  have hπ := Environment.AKMTestIntegralSupport.measurable_project
    (d := d) (r₀ := r) Q.ellipticity_parameter
  have hphysical := ae_of_ae_map hπ.aemeasurable hpot
  filter_upwards [hphysical, hid] with ω hω hidω
  obtain ⟨χ, hc, hz, hw, hm, _, hs⟩ := hω
  refine ⟨χ, hc, hz, (fun R ε hR hε => hs R hR ε hε), ?_, hm⟩
  intro j
  apply (hw j).congr_ae (ae_eq_refl _)
  simpa only [Measure.restrict_univ] using!
    hidω.mono (fun x hx => congrArg (fun z => z.ofLp j) hx)

/-- The same continuous, origin-zero uniformly sublinear canonical corrector
produces a weak harmonic coordinate on every positive-radius ball. -/
theorem ae_physical_uniform_canonical_harmonic_coordinate
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) (i : Fin d) :
    ∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q, ∃ χ : Vec d → ℝ,
      Continuous χ ∧ χ 0 = 0 ∧
      HasWeakGradient Set.univ χ (fun x =>
        ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) (translate x (reduce ω.1))).ofLp) ∧
      (∀ R : ℝ, 0 < R → MemLp χ 2 (volume.restrict (ball 0 R))) ∧
      (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∀ x, euclideanNorm x ≤ (t+1)*R → |χ x|/(t+1) ≤ ε) ∧
      (∀ R : ℝ, 0 < R → WeakSolution (ball 0 R) (reduce ω.1).1
        (fun x => x i + χ x)
        (fun x => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x (reduce ω.1))).ofLp)) := by
  let H := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  obtain ⟨G, _, hpot, hid⟩ := exists_akm_sublinear_global_weakPotential
    ballPoincareEstimate_from_pde Q i
  have hπ := Environment.AKMTestIntegralSupport.measurable_project
    (d := d) (r₀ := r) Q.ellipticity_parameter
  have hphysical := ae_of_ae_map hπ.aemeasurable hpot
  have hdiv := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_canonicalCorrectorFlux_hasWeakDivergence Q i)
  have hflux := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_spatial_canonicalCorrectorFlux Q i measurable_id)
  filter_upwards [ae_physical_uniformly_sublinear_canonical_corrector Q i,
    hphysical, hid, hdiv, hflux] with ω hχ hGω hidω hdivω hfluxω
  obtain ⟨χ, hc, hz, hs, hw, hm⟩ := hχ
  refine ⟨χ, hc, hz, hw, hm, hs, ?_⟩
  intro R hR
  have hg : MemLp (fun x => (H (translate x (reduce ω.1))).ofLp) 2
      (volume.restrict (ball (0 : Vec d) R)) := by
    have heq := ae_restrict_of_ae (s := ball (0 : Vec d) R) hidω
    have hmem := (memLp_congr_ae heq).mp (hGω.1 R hR)
    apply memLp_pi_iff.mpr
    intro j
    exact hmem.eval_piLp j
  have hweak : HasWeakGradient (ball 0 R) χ
      (fun x => (H (translate x (reduce ω.1))).ofLp) := fun j =>
    HasWeakPartialDerivative.restrict_subset (Set.subset_univ _) MeasurableSet.univ (hw j)
  have hdiv' : HasWeakDivergence (ball (0 : Vec d) R)
      (fun x => ((reduce ω.1).1 x).mulVec
        (unitVector i + (H (translate x (reduce ω.1))).ofLp)) (fun _ => 0) := by
    apply (HasWeakDivergence.restrict_subset (Set.subset_univ _)
      MeasurableSet.univ hdivω).congr_ae (ae_restrict_of_ae hfluxω) (ae_eq_refl _)
  exact affine_weakSolution_of_weakPotential R hR i (reduce ω.1).1 χ _
    (hm R hR) hg hweak hdiv'

/-- Continuous weak potentials of the same gradient agree when both vanish at the origin. -/
theorem continuous_normalized_weak_potential_unique {d : ℕ}
    {u v : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : Continuous u) (hv : Continuous v) (hu0 : u 0 = 0) (hv0 : v 0 = 0)
    (hDu : HasWeakGradient Set.univ u G) (hDv : HasWeakGradient Set.univ v G) : u = v := by
  have hdiff := hasWeakGradient_sub hDu hDv
  have hzero (j : Fin d) (ψ : Vec d → ℝ) (hψ : IsSpatialTest Set.univ ψ) :
      (∫ x, (u x - v x) * coordinateDerivative j ψ x) = 0 := by
    have heq := (hdiff j).2.2 ψ hψ
    simpa only [Measure.restrict_univ, Pi.sub_apply, sub_self, zero_mul,
      integral_zero, neg_zero] using heq
  obtain ⟨c, hc⟩ := ae_eq_const_of_zero_weak_gradient
    (hu.sub hv).locallyIntegrable hzero
  have hconst : (fun x => u x - v x) = fun _ => c :=
    MeasureTheory.Measure.eq_of_ae_eq hc (hu.sub hv) continuous_const
  have hc0 : c = 0 := by
    have heq := congrFun hconst 0
    simpa only [hu0, hv0, sub_self] using heq.symm
  funext x
  have heq := congrFun hconst x
  exact sub_eq_zero.mp (heq.trans hc0)

/-- The normalized continuous potential of a translated gradient is the centered translate. -/
theorem normalized_weak_potential_translate {d : ℕ}
    {u v : Vec d → ℝ} {G : Vec d → Vec d} (y : Vec d)
    (hu : Continuous u) (hv : Continuous v) (hv0 : v 0 = 0)
    (hDu : HasWeakGradient Set.univ u G)
    (hDv : HasWeakGradient Set.univ v (fun x => G (y+x))) :
    ∀ x, v x = u (y+x) - u y := by
  have hcenter : Continuous (fun x => u (y+x) - u y) :=
    (hu.comp (continuous_const.add continuous_id)).sub continuous_const
  have hcenter0 : u (y + 0) - u y = 0 := by
    rw [add_zero, sub_self]
  have hDcenter := hasWeakGradient_sub_const Set.univ (hDu.translated y) (u y)
  exact congrFun (continuous_normalized_weak_potential_unique
    hv hcenter hv0 hcenter0 hDv hDcenter)

/-- Normalized continuous potentials of shifted gradients satisfy the additive cocycle identity. -/
theorem normalized_weak_potential_cocycle {d : ℕ}
    (χ : Vec d → Vec d → ℝ) (G : Vec d → Vec d)
    (hc : ∀ y, Continuous (χ y)) (h0 : ∀ y, χ y 0 = 0)
    (hD : ∀ y, HasWeakGradient Set.univ (χ y) (fun x => G (y+x)))
    (y z x : Vec d) : χ (y+z) x = χ y (z+x) - χ y z := by
  exact normalized_weak_potential_translate (G := fun t => G (y+t)) z
    (hc y) (hc (y+z)) (h0 (y+z)) (hD y)
    (by simpa only [add_assoc] using hD (y+z)) x

/-- Uniform sublinearity controls centered increments uniformly in both points. -/
theorem uniform_two_point_sublinearity {d : ℕ} (χ : Vec d → Vec d)
    (hsub : ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ x)/(t+1) ≤ ε) :
    ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y, euclideanNorm x ≤ (t+1)*R → euclideanNorm y ≤ (t+1)*R →
        euclideanNorm (χ (y+x) - χ y)/(t+1) ≤ ε := by
  intro R ε hR hε
  filter_upwards [hsub (2*R) (ε/2) (by positivity) (by positivity),
    eventually_ge_atTop (0 : ℝ)] with t h ht
  have htpos : 0 < t+1 := by linarith only [ht]
  intro x y hx hy
  have hyx : euclideanNorm (y+x) ≤ (t+1)*(2*R) := calc
    euclideanNorm (y+x) ≤ euclideanNorm y + euclideanNorm x :=
      TimeChange.euclideanNorm_add_le y x
    _ ≤ (t+1)*R + (t+1)*R := add_le_add hy hx
    _ = (t+1)*(2*R) := by ring
  have hy' : euclideanNorm y ≤ (t+1)*(2*R) :=
    hy.trans (mul_le_mul_of_nonneg_left (by linarith only [hR]) htpos.le)
  have hneg : euclideanNorm (-χ y) = euclideanNorm (χ y) := by
    simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
      TimeChange.euclideanNorm_smul (-1) (χ y)
  have htriangle : euclideanNorm (χ (y+x) - χ y) ≤
      euclideanNorm (χ (y+x)) + euclideanNorm (χ y) := by
    simpa only [sub_eq_add_neg, hneg] using
      TimeChange.euclideanNorm_add_le (χ (y+x)) (-χ y)
  calc
    euclideanNorm (χ (y+x) - χ y)/(t+1) ≤
        (euclideanNorm (χ (y+x)) + euclideanNorm (χ y))/(t+1) :=
      div_le_div_of_nonneg_right htriangle htpos.le
    _ = euclideanNorm (χ (y+x))/(t+1) + euclideanNorm (χ y)/(t+1) :=
      add_div _ _ _
    _ ≤ ε/2 + ε/2 := add_le_add (h (y+x) hyx) (h y hy')
    _ = ε := by ring

/-- Joint tightness and uniform sublinearity control the centered corrector
increment in probability, with one spatial radius for both endpoints. -/
@[nolint unusedArguments]
theorem two_point_corrector_remainder_of_tightness
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (χ : Vec d → Vec d) (X Y : ℕ → Ω → Vec d)
    (hsub : ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ x)/(t+1) ≤ ε)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ n,
      μ {ω | R < euclideanNorm (X n ω)/((n:ℝ)+1) ∨
        R < euclideanNorm (Y n ω)/((n:ℝ)+1)} ≤ ENNReal.ofReal δ) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      μ {ω | ε < euclideanNorm (χ (Y n ω + X n ω) - χ (Y n ω))/((n:ℝ)+1)} ≤
        ENNReal.ofReal δ := by
  intro ε δ hε hδ
  obtain ⟨R, hR, htail⟩ := htight δ hδ
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (uniform_two_point_sublinearity χ hsub R ε hR hε)] with n hn
  refine (measure_mono ?_).trans (htail n)
  intro ω hω
  change R < euclideanNorm (X n ω)/((n:ℝ)+1) ∨
    R < euclideanNorm (Y n ω)/((n:ℝ)+1)
  by_contra houtside
  have hscale : 0 < (n : ℝ) + 1 := by positivity
  have hx : euclideanNorm (X n ω) ≤ ((n : ℝ) + 1) * R := by
    simpa only [mul_comm] using
      (div_le_iff₀ hscale).mp (le_of_not_gt (not_or.mp houtside).1)
  have hy : euclideanNorm (Y n ω) ≤ ((n : ℝ) + 1) * R := by
    simpa only [mul_comm] using
      (div_le_iff₀ hscale).mp (le_of_not_gt (not_or.mp houtside).2)
  exact (not_lt_of_ge (hn (X n ω) (Y n ω) hx hy)) hω

/-- Almost-sure uniform spatial sublinearity controls random centered corrector
increments in probability under joint tightness of both endpoints. -/
theorem random_two_point_corrector_remainder_of_tightness
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (χ : Ω → Vec d → Vec d)
    (hχ : Measurable (fun z : Ω × Vec d => χ z.1 z.2))
    (hcont : ∀ᵐ ω ∂μ, Continuous (χ ω))
    (hsub : ∀ᵐ ω ∂μ, ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε)
    (X Y : ℕ → Ω → Vec d) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (htight : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ n,
      μ {ω | R < euclideanNorm (X n ω)/((n:ℝ)+1) ∨
        R < euclideanNorm (Y n ω)/((n:ℝ)+1)} ≤ ENNReal.ofReal δ) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      μ {ω | ε < euclideanNorm (χ ω (Y n ω+X n ω)-χ ω (Y n ω))/((n:ℝ)+1)} ≤
        ENNReal.ofReal δ := by
  classical
  intro ε δ hε hδ
  obtain ⟨R, hR, htail⟩ := htight (δ/2) (half_pos hδ)
  let E : ℕ → Set Ω := fun n =>
    {ω | ε < euclideanNorm (χ ω (Y n ω+X n ω)-χ ω (Y n ω))/((n:ℝ)+1) ∧
      euclideanNorm (X n ω) ≤ ((n:ℝ)+1)*R ∧
      euclideanNorm (Y n ω) ≤ ((n:ℝ)+1)*R}
  have hnorm : Continuous (euclideanNorm (d := d)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hE (n : ℕ) : MeasurableSet (E n) := by
    have hdiff : Measurable (fun ω => χ ω (Y n ω+X n ω)-χ ω (Y n ω)) :=
      (hχ.comp (measurable_id.prodMk ((hY n).add (hX n)))).sub
        (hχ.comp (measurable_id.prodMk (hY n)))
    exact (measurableSet_lt measurable_const
      ((hnorm.measurable.comp hdiff).div_const _)).inter
      ((measurableSet_le (hnorm.measurable.comp (hX n)) measurable_const).inter
        (measurableSet_le (hnorm.measurable.comp (hY n)) measurable_const))
  have hvanish : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ω ∈ E n ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hcont.and hsub] with ω hω
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (uniform_two_point_sublinearity (χ ω) hω.2 R ε hR hε)] with n hn
    have hnot : ω ∉ E n := by
      rintro ⟨hbad, hx, hy⟩
      exact (not_lt_of_ge (hn (X n ω) (Y n ω) hx hy)) hbad
    simpa only [Set.mem_empty_iff_false, iff_false] using hnot
  have hmeasure : Tendsto (fun n => μ (E n)) atTop (𝓝 0) := by
    simpa only [measure_empty] using
      tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        MeasurableSet.empty hE hvanish
  filter_upwards [hmeasure.eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hδ)))] with n hn
  have hcover :
      {ω | ε < euclideanNorm (χ ω (Y n ω+X n ω)-χ ω (Y n ω))/((n:ℝ)+1)} ⊆
        {ω | R < euclideanNorm (X n ω)/((n:ℝ)+1) ∨
          R < euclideanNorm (Y n ω)/((n:ℝ)+1)} ∪ E n := by
    intro ω hbad
    by_cases ht : R < euclideanNorm (X n ω)/((n:ℝ)+1) ∨
        R < euclideanNorm (Y n ω)/((n:ℝ)+1)
    · exact Or.inl ht
    · right
      have hscale : 0 < (n : ℝ)+1 := by positivity
      refine ⟨hbad, ?_, ?_⟩
      · simpa only [mul_comm] using
          (div_le_iff₀ hscale).mp (le_of_not_gt (not_or.mp ht).1)
      · simpa only [mul_comm] using
          (div_le_iff₀ hscale).mp (le_of_not_gt (not_or.mp ht).2)
  calc
    μ _ ≤ μ ({ω | R < euclideanNorm (X n ω)/((n:ℝ)+1) ∨
        R < euclideanNorm (Y n ω)/((n:ℝ)+1)} ∪ E n) := measure_mono hcover
    _ ≤ μ {ω | R < euclideanNorm (X n ω)/((n:ℝ)+1) ∨
        R < euclideanNorm (Y n ω)/((n:ℝ)+1)} + μ (E n) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ/2) + ENNReal.ofReal (δ/2) := add_le_add (htail n) hn.le
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le]
      congr 1
      ring

/-- Almost-sure uniform sublinearity controls random centered corrector increments
at any positive scale tending to infinity, including the diffusive scale `√(n+1)`. -/
theorem random_two_point_corrector_remainder_at_scales
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (χ : Ω → Vec d → Vec d)
    (hχ : Measurable (fun z : Ω × Vec d => χ z.1 z.2))
    (hcont : ∀ᵐ ω ∂μ, Continuous (χ ω))
    (hsub : ∀ᵐ ω ∂μ, ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (X Y : ℕ → Ω → Vec d) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (htight : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ n,
      μ {ω | R < euclideanNorm (X n ω)/(ρ n) ∨
        R < euclideanNorm (Y n ω)/(ρ n)} ≤ ENNReal.ofReal δ) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      μ {ω | ε < euclideanNorm (χ ω (Y n ω+X n ω)-χ ω (Y n ω))/(ρ n)} ≤
        ENNReal.ofReal δ := by
  classical
  intro ε δ hε hδ
  obtain ⟨R, hR, htail⟩ := htight (δ/2) (half_pos hδ)
  let E : ℕ → Set Ω := fun n =>
    {ω | ε < euclideanNorm (χ ω (Y n ω+X n ω)-χ ω (Y n ω))/(ρ n) ∧
      euclideanNorm (X n ω) ≤ (ρ n)*R ∧
      euclideanNorm (Y n ω) ≤ (ρ n)*R}
  have hnorm : Continuous (euclideanNorm (d := d)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hE (n : ℕ) : MeasurableSet (E n) := by
    have hdiff : Measurable (fun ω => χ ω (Y n ω+X n ω)-χ ω (Y n ω)) :=
      (hχ.comp (measurable_id.prodMk ((hY n).add (hX n)))).sub
        (hχ.comp (measurable_id.prodMk (hY n)))
    exact (measurableSet_lt measurable_const
      ((hnorm.measurable.comp hdiff).div_const _)).inter
      ((measurableSet_le (hnorm.measurable.comp (hX n)) measurable_const).inter
        (measurableSet_le (hnorm.measurable.comp (hY n)) measurable_const))
  have hshift : Tendsto (fun n => ρ n - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hρ
  have hvanish : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ω ∈ E n ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hcont.and hsub] with ω hω
    filter_upwards [hshift.eventually
      (uniform_two_point_sublinearity (χ ω) hω.2 R ε hR hε)] with n hn
    simp only [sub_add_cancel] at hn
    have hnot : ω ∉ E n := by
      rintro ⟨hbad, hx, hy⟩
      exact (not_lt_of_ge (hn (X n ω) (Y n ω) hx hy)) hbad
    simpa only [Set.mem_empty_iff_false, iff_false] using hnot
  have hmeasure : Tendsto (fun n => μ (E n)) atTop (𝓝 0) := by
    simpa only [measure_empty] using
      tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        MeasurableSet.empty hE hvanish
  filter_upwards [hmeasure.eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hδ)))] with n hn
  have hcover :
      {ω | ε < euclideanNorm (χ ω (Y n ω+X n ω)-χ ω (Y n ω))/(ρ n)} ⊆
        {ω | R < euclideanNorm (X n ω)/(ρ n) ∨
          R < euclideanNorm (Y n ω)/(ρ n)} ∪ E n := by
    intro ω hbad
    by_cases ht : R < euclideanNorm (X n ω)/(ρ n) ∨
        R < euclideanNorm (Y n ω)/(ρ n)
    · exact Or.inl ht
    · right
      have hscale : 0 < ρ n := hρpos n
      refine ⟨hbad, ?_, ?_⟩
      · simpa only [mul_comm] using
          (div_le_iff₀ hscale).mp (le_of_not_gt (not_or.mp ht).1)
      · simpa only [mul_comm] using
          (div_le_iff₀ hscale).mp (le_of_not_gt (not_or.mp ht).2)
  calc
    μ _ ≤ μ ({ω | R < euclideanNorm (X n ω)/(ρ n) ∨
        R < euclideanNorm (Y n ω)/(ρ n)} ∪ E n) := measure_mono hcover
    _ ≤ μ {ω | R < euclideanNorm (X n ω)/(ρ n) ∨
        R < euclideanNorm (Y n ω)/(ρ n)} + μ (E n) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ/2) + ENNReal.ofReal (δ/2) := add_le_add (htail n) hn.le
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le]
      congr 1
      ring

/-- A uniform scaled second-moment bound gives the joint tightness needed for
random centered corrector increments to vanish in probability. -/
theorem random_two_point_corrector_remainder_of_second_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (χ : Ω → Vec d → Vec d)
    (hχ : Measurable (fun z : Ω × Vec d => χ z.1 z.2))
    (hcont : ∀ᵐ ω ∂μ, Continuous (χ ω))
    (hsub : ∀ᵐ ω ∂μ, ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (X Y : ℕ → Ω → Vec d) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (C : ℝ) (hC : 0 ≤ C)
    (hX2 : ∀ n, MemLp (fun ω => euclideanNorm (X n ω)) 2 μ)
    (hY2 : ∀ n, MemLp (fun ω => euclideanNorm (Y n ω)) 2 μ)
    (hmom : ∀ n, (∫ ω, (euclideanNorm (X n ω))^2 +
      (euclideanNorm (Y n ω))^2 ∂μ) ≤ C*(ρ n)^2) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      μ {ω | ε < euclideanNorm (χ ω (Y n ω+X n ω)-χ ω (Y n ω))/ρ n} ≤
        ENNReal.ofReal δ := by
  apply random_two_point_corrector_remainder_at_scales μ χ hχ hcont hsub
    ρ hρpos hρ X Y hX hY
  intro δ hδ
  let R : ℝ := Real.sqrt (C/δ+1)
  have hratio : 0 ≤ C/δ := div_nonneg hC hδ.le
  have hR : 0 < R := Real.sqrt_pos.mpr (by linarith only [hratio])
  have hRsq : R^2 = C/δ+1 := Real.sq_sqrt (by linarith only [hratio])
  have hbound : C ≤ δ*R^2 := by
    rw [hRsq, mul_add, mul_div_cancel₀ _ hδ.ne']
    linarith only [hδ]
  refine ⟨R, hR, fun n => ?_⟩
  let f : Ω → ℝ := fun ω => (euclideanNorm (X n ω))^2 +
    (euclideanNorm (Y n ω))^2
  have hf : Integrable f μ := (hX2 n).integrable_sq.add (hY2 n).integrable_sq
  have hfnonneg : ∀ ω, 0 ≤ f ω := fun ω => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hscale : 0 < R^2*(ρ n)^2 := mul_pos (sq_pos_of_pos hR) (sq_pos_of_pos (hρpos n))
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall hfnonneg) hf (R^2*(ρ n)^2)
  have htail : μ.real {ω | R^2*(ρ n)^2 ≤ f ω} ≤ δ := by
    apply (mul_le_mul_iff_right₀ hscale).mp
    calc
      (R^2*(ρ n)^2)*μ.real {ω | R^2*(ρ n)^2 ≤ f ω} ≤ ∫ ω, f ω ∂μ := hmarkov
      _ ≤ C*(ρ n)^2 := hmom n
      _ ≤ (δ*R^2)*(ρ n)^2 := mul_le_mul_of_nonneg_right hbound (sq_nonneg _)
      _ = (R^2*(ρ n)^2)*δ := by ring
  have hcover : {ω | R < euclideanNorm (X n ω)/ρ n ∨
      R < euclideanNorm (Y n ω)/ρ n} ⊆ {ω | R^2*(ρ n)^2 ≤ f ω} := by
    intro ω hω
    rcases hω with hx | hy
    · have hx' : R*ρ n < euclideanNorm (X n ω) := (lt_div_iff₀ (hρpos n)).mp hx
      have hs := sq_le_sq₀ (mul_pos hR (hρpos n)).le
        (show 0 ≤ euclideanNorm (X n ω) from Real.sqrt_nonneg _)
      have hsq : (R*ρ n)^2 ≤ (euclideanNorm (X n ω))^2 := hs.mpr hx'.le
      rw [mul_pow] at hsq
      exact hsq.trans (le_add_of_nonneg_right (sq_nonneg _))
    · have hy' : R*ρ n < euclideanNorm (Y n ω) := (lt_div_iff₀ (hρpos n)).mp hy
      have hs := sq_le_sq₀ (mul_pos hR (hρpos n)).le
        (show 0 ≤ euclideanNorm (Y n ω) from Real.sqrt_nonneg _)
      have hsq : (R*ρ n)^2 ≤ (euclideanNorm (Y n ω))^2 := hs.mpr hy'.le
      rw [mul_pow] at hsq
      exact hsq.trans (le_add_of_nonneg_left (sq_nonneg _))
  calc
    μ _ ≤ μ {ω | R^2*(ρ n)^2 ≤ f ω} := measure_mono hcover
    _ = ENNReal.ofReal (μ.real {ω | R^2*(ρ n)^2 ≤ f ω}) := by rw [ofReal_measureReal]
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal htail

open scoped NNReal in
/-- Uniform spatial sublinearity and compact-time joint tightness make the
random centered corrector increment vanish uniformly on each time interval. -/
@[nolint unusedArguments]
theorem random_two_point_corrector_remainder_uniform_time
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (χ : Ω → Vec d → Vec d)
    (hχ : Measurable (fun z : Ω × Vec d => χ z.1 z.2))
    (hcont : ∀ᵐ ω ∂μ, Continuous (χ ω))
    (hsub : ∀ᵐ ω ∂μ, ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (X Y : ℕ → Ω → Path d) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (T : ℝ≥0)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ n,
      μ {ω | ∃ t : ℝ≥0, t ≤ T ∧
        (R < euclideanNorm (X n ω t)/ρ n ∨ R < euclideanNorm (Y n ω t)/ρ n)} ≤
          ENNReal.ofReal δ) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      μ {ω | ∃ t : ℝ≥0, t ≤ T ∧
        ε < euclideanNorm (χ ω (Y n ω t+X n ω t)-χ ω (Y n ω t))/ρ n} ≤
          ENNReal.ofReal δ := by
  classical
  clear hX hY
  intro ε δ hε hδ
  obtain ⟨R, hR, htail⟩ := htight (δ/2) (half_pos hδ)
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq (Vec d × Vec d)
  -- The strict, enlarged spatial ball makes the bad spatial event open.
  let U : ℕ → Ω → Set (Vec d × Vec d) := fun n ω =>
    {z | ε < euclideanNorm (χ ω (z.2+z.1)-χ ω z.2)/ρ n ∧
      euclideanNorm z.1 < ρ n*(2*R) ∧ euclideanNorm z.2 < ρ n*(2*R)}
  let E : ℕ → Set Ω := fun n => {ω | ∃ k : ℕ, q k ∈ U n ω}
  have hnorm : Continuous (euclideanNorm (d := d)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hE (n : ℕ) : MeasurableSet (E n) := by
    change MeasurableSet {ω | ∃ k : ℕ, q k ∈ U n ω}
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro k
    have hdiff : Measurable (fun ω => χ ω ((q k).2+(q k).1)-χ ω (q k).2) :=
      (hχ.comp (measurable_id.prodMk measurable_const)).sub
        (hχ.comp (measurable_id.prodMk measurable_const))
    exact (measurableSet_lt measurable_const
      ((hnorm.measurable.comp hdiff).div_const _)).inter
        (MeasurableSet.const _)
  have hshift : Tendsto (fun n => ρ n-1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hρ
  have hvanish : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ω ∈ E n ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hsub] with ω hω
    filter_upwards [hshift.eventually (uniform_two_point_sublinearity
      (χ ω) hω (2*R) ε (by positivity) hε)] with n hn
    simp only [sub_add_cancel] at hn
    have hnot : ω ∉ E n := by
      rintro ⟨k, hbad, hx, hy⟩
      exact (not_lt_of_ge (hn (q k).1 (q k).2 hx.le hy.le)) hbad
    simpa only [Set.mem_empty_iff_false, iff_false] using hnot
  have hmeasure : Tendsto (fun n => μ (E n)) atTop (𝓝 0) := by
    simpa only [measure_empty] using
      tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        MeasurableSet.empty hE hvanish
  filter_upwards [hmeasure.eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hδ)))] with n hn
  let A : Set Ω := {ω | ∃ t : ℝ≥0, t ≤ T ∧
    (R < euclideanNorm (X n ω t)/ρ n ∨ R < euclideanNorm (Y n ω t)/ρ n)}
  have hcover : {ω | ∃ t : ℝ≥0, t ≤ T ∧
      ε < euclideanNorm (χ ω (Y n ω t+X n ω t)-χ ω (Y n ω t))/ρ n} ≤ᵐ[μ]
        A ∪ E n := by
    filter_upwards [hcont] with ω hω
    rintro ⟨t, ht, hbad⟩
    by_cases hout : ω ∈ A
    · exact Or.inl hout
    right
    have htight' : ¬ (R < euclideanNorm (X n ω t)/ρ n ∨
        R < euclideanNorm (Y n ω t)/ρ n) := fun h => hout ⟨t, ht, h⟩
    have hx : euclideanNorm (X n ω t) ≤ ρ n*R := by
      simpa only [mul_comm] using
        (div_le_iff₀ (hρpos n)).mp (le_of_not_gt (not_or.mp htight').1)
    have hy : euclideanNorm (Y n ω t) ≤ ρ n*R := by
      simpa only [mul_comm] using
        (div_le_iff₀ (hρpos n)).mp (le_of_not_gt (not_or.mp htight').2)
    have hball : ρ n*R < ρ n*(2*R) :=
      mul_lt_mul_of_pos_left (by linarith only [hR]) (hρpos n)
    have hopen : IsOpen (U n ω) := by
      have hd : Continuous (fun z : Vec d × Vec d => χ ω (z.2+z.1)-χ ω z.2) :=
        (hω.comp (continuous_snd.add continuous_fst)).sub (hω.comp continuous_snd)
      exact (isOpen_lt continuous_const ((hnorm.comp hd).div_const _)).inter
        ((isOpen_lt (hnorm.comp continuous_fst) continuous_const).inter
          (isOpen_lt (hnorm.comp continuous_snd) continuous_const))
    exact hq.exists_mem_open hopen ⟨(X n ω t, Y n ω t), hbad,
      hx.trans_lt hball, hy.trans_lt hball⟩
  calc
    μ _ ≤ μ (A ∪ E n) := measure_mono_ae hcover
    _ ≤ μ A + μ (E n) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ/2) + ENNReal.ofReal (δ/2) := add_le_add (htail n) hn.le
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le]
      congr 1
      ring

open scoped NNReal in
/-- Uniform-time corrector control also holds at almost surely bounded random times. -/
@[nolint unusedArguments]
theorem random_two_point_corrector_remainder_at_random_times
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (χ : Ω → Vec d → Vec d)
    (hχ : Measurable (fun z : Ω × Vec d => χ z.1 z.2))
    (hcont : ∀ᵐ ω ∂μ, Continuous (χ ω))
    (hsub : ∀ᵐ ω ∂μ, ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (X Y : ℕ → Ω → Path d) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (T : ℝ≥0)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ n,
      μ {ω | ∃ t : ℝ≥0, t ≤ T ∧
        (R < euclideanNorm (X n ω t)/ρ n ∨ R < euclideanNorm (Y n ω t)/ρ n)} ≤ ENNReal.ofReal δ)
    (τ : ℕ → Ω → ℝ≥0) (hτ : ∀ n, Measurable (τ n))
    (hτT : ∀ n, ∀ᵐ ω ∂μ, τ n ω ≤ T) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      μ {ω | ε < euclideanNorm
        (χ ω (Y n ω (τ n ω)+X n ω (τ n ω))-χ ω (Y n ω (τ n ω)))/ρ n}
      ≤ ENNReal.ofReal δ := by
  clear hτ
  intro ε δ hε hδ
  filter_upwards [random_two_point_corrector_remainder_uniform_time μ χ hχ hcont hsub
    ρ hρpos hρ X Y hX hY T htight ε δ hε hδ] with n hn
  refine (measure_mono_ae ?_).trans hn
  filter_upwards [hτT n] with ω hω
  intro hbad
  exact ⟨τ n ω, hω, hbad⟩

open scoped NNReal in
/-- Uniform-time corrector control extends to tight random times. -/
@[nolint unusedArguments]
theorem random_two_point_corrector_remainder_at_tight_random_times
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (χ : Ω → Vec d → Vec d)
    (hχ : Measurable (fun z : Ω × Vec d => χ z.1 z.2))
    (hcont : ∀ᵐ ω ∂μ, Continuous (χ ω))
    (hsub : ∀ᵐ ω ∂μ, ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (X Y : ℕ → Ω → Path d) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (htight : ∀ (T : ℝ≥0) (δ : ℝ), 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ n,
      μ {ω | ∃ t : ℝ≥0, t ≤ T ∧
        (R < euclideanNorm (X n ω t)/ρ n ∨ R < euclideanNorm (Y n ω t)/ρ n)} ≤ ENNReal.ofReal δ)
    (τ : ℕ → Ω → ℝ≥0) (hτ : ∀ n, Measurable (τ n))
    (hτtight : ∀ δ : ℝ, 0 < δ → ∃ T : ℝ≥0, ∀ n,
      μ {ω | T < τ n ω} ≤ ENNReal.ofReal δ) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      μ {ω | ε < euclideanNorm
        (χ ω (Y n ω (τ n ω)+X n ω (τ n ω))-χ ω (Y n ω (τ n ω)))/ρ n}
      ≤ ENNReal.ofReal δ := by
  clear hτ
  intro ε δ hε hδ
  obtain ⟨T, hT⟩ := hτtight (δ/2) (half_pos hδ)
  filter_upwards [random_two_point_corrector_remainder_uniform_time μ χ hχ hcont hsub
    ρ hρpos hρ X Y hX hY T (htight T) ε (δ/2) hε (half_pos hδ)] with n hn
  calc
    μ _ ≤ μ ({ω | ∃ t : ℝ≥0, t ≤ T ∧
        ε < euclideanNorm (χ ω (Y n ω t+X n ω t)-χ ω (Y n ω t))/ρ n} ∪
        {ω | T < τ n ω}) := by
      apply measure_mono
      intro ω hbad
      by_cases h : τ n ω ≤ T
      · exact Or.inl ⟨τ n ω, h, hbad⟩
      · exact Or.inr (lt_of_not_ge h)
    _ ≤ μ {ω | ∃ t : ℝ≥0, t ≤ T ∧
        ε < euclideanNorm (χ ω (Y n ω t+X n ω t)-χ ω (Y n ω t))/ρ n} +
        μ {ω | T < τ n ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ/2) + ENNReal.ofReal (δ/2) := add_le_add hn (hT n)
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le]
      congr 1
      ring

open scoped NNReal in
/-- Uniform corrector control is preserved by tight time changes on compact intervals. -/
theorem random_two_point_corrector_remainder_under_tight_time_changes
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (χ : Ω → Vec d → Vec d)
    (hχ : Measurable (fun z : Ω × Vec d => χ z.1 z.2))
    (hcont : ∀ᵐ ω ∂μ, Continuous (χ ω))
    (hsub : ∀ᵐ ω ∂μ, ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (X Y : ℕ → Ω → Path d) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (htight : ∀ (S : ℝ≥0) (δ : ℝ), 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ n,
      μ {ω | ∃ u : ℝ≥0, u ≤ S ∧
        (R < euclideanNorm (X n ω u)/ρ n ∨ R < euclideanNorm (Y n ω u)/ρ n)} ≤ ENNReal.ofReal δ)
    (θ : ℕ → Ω → ℝ≥0 → ℝ≥0)
    (hθtight : ∀ (T : ℝ≥0) (δ : ℝ), 0 < δ → ∃ S : ℝ≥0, ∀ n,
      μ {ω | ∃ t : ℝ≥0, t ≤ T ∧ S < θ n ω t} ≤ ENNReal.ofReal δ) :
    ∀ (T : ℝ≥0) (ε δ : ℝ), 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      μ {ω | ∃ t : ℝ≥0, t ≤ T ∧ ε < euclideanNorm
        (χ ω (Y n ω (θ n ω t)+X n ω (θ n ω t))-χ ω (Y n ω (θ n ω t)))/ρ n}
      ≤ ENNReal.ofReal δ := by
  intro T ε δ hε hδ
  obtain ⟨S, hS⟩ := hθtight T (δ/2) (half_pos hδ)
  filter_upwards [random_two_point_corrector_remainder_uniform_time μ χ hχ hcont hsub
    ρ hρpos hρ X Y hX hY S (htight S) ε (δ/2) hε (half_pos hδ)] with n hn
  calc
    μ _ ≤ μ ({ω | ∃ u : ℝ≥0, u ≤ S ∧
        ε < euclideanNorm (χ ω (Y n ω u+X n ω u)-χ ω (Y n ω u))/ρ n} ∪
        {ω | ∃ t : ℝ≥0, t ≤ T ∧ S < θ n ω t}) := by
      apply measure_mono
      intro ω ⟨t, ht, hbad⟩
      by_cases h : θ n ω t ≤ S
      · exact Or.inl ⟨θ n ω t, h, hbad⟩
      · exact Or.inr ⟨t, ht, lt_of_not_ge h⟩
    _ ≤ μ {ω | ∃ u : ℝ≥0, u ≤ S ∧
        ε < euclideanNorm (χ ω (Y n ω u+X n ω u)-χ ω (Y n ω u))/ρ n} +
        μ {ω | ∃ t : ℝ≥0, t ≤ T ∧ S < θ n ω t} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ/2) + ENNReal.ofReal (δ/2) := add_le_add hn (hS n)
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le]
      congr 1
      ring

open scoped NNReal in
/-- Uniform spatial sublinearity and eventual compact-time joint tightness make the
random centered corrector increment vanish uniformly on each time interval. -/
@[nolint unusedArguments]
theorem random_two_point_corrector_remainder_uniform_time_of_eventual_tightness
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (χ : Ω → Vec d → Vec d)
    (hχ : Measurable (fun z : Ω × Vec d => χ z.1 z.2))
    (hcont : ∀ᵐ ω ∂μ, Continuous (χ ω))
    (hsub : ∀ᵐ ω ∂μ, ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (X Y : ℕ → Ω → Path d) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (T : ℝ≥0)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ᶠ n : ℕ in atTop,
      μ {ω | ∃ t : ℝ≥0, t ≤ T ∧
        (R < euclideanNorm (X n ω t)/ρ n ∨ R < euclideanNorm (Y n ω t)/ρ n)} ≤
          ENNReal.ofReal δ) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      μ {ω | ∃ t : ℝ≥0, t ≤ T ∧
        ε < euclideanNorm (χ ω (Y n ω t+X n ω t)-χ ω (Y n ω t))/ρ n} ≤
          ENNReal.ofReal δ := by
  classical
  clear hX hY
  intro ε δ hε hδ
  obtain ⟨R, hR, htail⟩ := htight (δ/2) (half_pos hδ)
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq (Vec d × Vec d)
  -- The strict, enlarged spatial ball makes the bad spatial event open.
  let U : ℕ → Ω → Set (Vec d × Vec d) := fun n ω =>
    {z | ε < euclideanNorm (χ ω (z.2+z.1)-χ ω z.2)/ρ n ∧
      euclideanNorm z.1 < ρ n*(2*R) ∧ euclideanNorm z.2 < ρ n*(2*R)}
  let E : ℕ → Set Ω := fun n => {ω | ∃ k : ℕ, q k ∈ U n ω}
  have hnorm : Continuous (euclideanNorm (d := d)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hE (n : ℕ) : MeasurableSet (E n) := by
    change MeasurableSet {ω | ∃ k : ℕ, q k ∈ U n ω}
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro k
    have hdiff : Measurable (fun ω => χ ω ((q k).2+(q k).1)-χ ω (q k).2) :=
      (hχ.comp (measurable_id.prodMk measurable_const)).sub
        (hχ.comp (measurable_id.prodMk measurable_const))
    exact (measurableSet_lt measurable_const
      ((hnorm.measurable.comp hdiff).div_const _)).inter
        (MeasurableSet.const _)
  have hshift : Tendsto (fun n => ρ n-1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hρ
  have hvanish : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ω ∈ E n ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hsub] with ω hω
    filter_upwards [hshift.eventually (uniform_two_point_sublinearity
      (χ ω) hω (2*R) ε (by positivity) hε)] with n hn
    simp only [sub_add_cancel] at hn
    have hnot : ω ∉ E n := by
      rintro ⟨k, hbad, hx, hy⟩
      exact (not_lt_of_ge (hn (q k).1 (q k).2 hx.le hy.le)) hbad
    simpa only [Set.mem_empty_iff_false, iff_false] using hnot
  have hmeasure : Tendsto (fun n => μ (E n)) atTop (𝓝 0) := by
    simpa only [measure_empty] using
      tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        MeasurableSet.empty hE hvanish
  filter_upwards [hmeasure.eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hδ))), htail] with n hn htailn
  let A : Set Ω := {ω | ∃ t : ℝ≥0, t ≤ T ∧
    (R < euclideanNorm (X n ω t)/ρ n ∨ R < euclideanNorm (Y n ω t)/ρ n)}
  have hcover : {ω | ∃ t : ℝ≥0, t ≤ T ∧
      ε < euclideanNorm (χ ω (Y n ω t+X n ω t)-χ ω (Y n ω t))/ρ n} ≤ᵐ[μ]
        A ∪ E n := by
    filter_upwards [hcont] with ω hω
    rintro ⟨t, ht, hbad⟩
    by_cases hout : ω ∈ A
    · exact Or.inl hout
    right
    have htight' : ¬ (R < euclideanNorm (X n ω t)/ρ n ∨
        R < euclideanNorm (Y n ω t)/ρ n) := fun h => hout ⟨t, ht, h⟩
    have hx : euclideanNorm (X n ω t) ≤ ρ n*R := by
      simpa only [mul_comm] using
        (div_le_iff₀ (hρpos n)).mp (le_of_not_gt (not_or.mp htight').1)
    have hy : euclideanNorm (Y n ω t) ≤ ρ n*R := by
      simpa only [mul_comm] using
        (div_le_iff₀ (hρpos n)).mp (le_of_not_gt (not_or.mp htight').2)
    have hball : ρ n*R < ρ n*(2*R) :=
      mul_lt_mul_of_pos_left (by linarith only [hR]) (hρpos n)
    have hopen : IsOpen (U n ω) := by
      have hd : Continuous (fun z : Vec d × Vec d => χ ω (z.2+z.1)-χ ω z.2) :=
        (hω.comp (continuous_snd.add continuous_fst)).sub (hω.comp continuous_snd)
      exact (isOpen_lt continuous_const ((hnorm.comp hd).div_const _)).inter
        ((isOpen_lt (hnorm.comp continuous_fst) continuous_const).inter
          (isOpen_lt (hnorm.comp continuous_snd) continuous_const))
    exact hq.exists_mem_open hopen ⟨(X n ω t, Y n ω t), hbad,
      hx.trans_lt hball, hy.trans_lt hball⟩
  calc
    μ _ ≤ μ (A ∪ E n) := measure_mono_ae hcover
    _ ≤ μ A + μ (E n) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ/2) + ENNReal.ofReal (δ/2) := add_le_add htailn hn.le
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le]
      congr 1
      ring


open scoped NNReal in
/-- Uniform corrector control is preserved by eventually tight time changes on compact intervals. -/
theorem random_two_point_corrector_remainder_under_eventually_tight_time_changes
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (χ : Ω → Vec d → Vec d)
    (hχ : Measurable (fun z : Ω × Vec d => χ z.1 z.2))
    (hcont : ∀ᵐ ω ∂μ, Continuous (χ ω))
    (hsub : ∀ᵐ ω ∂μ, ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (X Y : ℕ → Ω → Path d) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (htight : ∀ (S : ℝ≥0) (δ : ℝ), 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ᶠ n : ℕ in atTop,
      μ {ω | ∃ u : ℝ≥0, u ≤ S ∧
        (R < euclideanNorm (X n ω u)/ρ n ∨ R < euclideanNorm (Y n ω u)/ρ n)} ≤ ENNReal.ofReal δ)
    (θ : ℕ → Ω → ℝ≥0 → ℝ≥0)
    (hθtight : ∀ (T : ℝ≥0) (δ : ℝ), 0 < δ → ∃ S : ℝ≥0, ∀ᶠ n : ℕ in atTop,
      μ {ω | ∃ t : ℝ≥0, t ≤ T ∧ S < θ n ω t} ≤ ENNReal.ofReal δ) :
    ∀ (T : ℝ≥0) (ε δ : ℝ), 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      μ {ω | ∃ t : ℝ≥0, t ≤ T ∧ ε < euclideanNorm
        (χ ω (Y n ω (θ n ω t)+X n ω (θ n ω t))-χ ω (Y n ω (θ n ω t)))/ρ n}
      ≤ ENNReal.ofReal δ := by
  intro T ε δ hε hδ
  obtain ⟨S, hS⟩ := hθtight T (δ/2) (half_pos hδ)
  filter_upwards [random_two_point_corrector_remainder_uniform_time_of_eventual_tightness μ χ hχ hcont hsub
    ρ hρpos hρ X Y hX hY S (htight S) ε (δ/2) hε (half_pos hδ), hS] with n hn hSn
  calc
    μ _ ≤ μ ({ω | ∃ u : ℝ≥0, u ≤ S ∧
        ε < euclideanNorm (χ ω (Y n ω u+X n ω u)-χ ω (Y n ω u))/ρ n} ∪
        {ω | ∃ t : ℝ≥0, t ≤ T ∧ S < θ n ω t}) := by
      apply measure_mono
      intro ω ⟨t, ht, hbad⟩
      by_cases h : θ n ω t ≤ S
      · exact Or.inl ⟨θ n ω t, h, hbad⟩
      · exact Or.inr ⟨t, ht, lt_of_not_ge h⟩
    _ ≤ μ {ω | ∃ u : ℝ≥0, u ≤ S ∧
        ε < euclideanNorm (χ ω (Y n ω u+X n ω u)-χ ω (Y n ω u))/ρ n} +
        μ {ω | ∃ t : ℝ≥0, t ≤ T ∧ S < θ n ω t} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ/2) + ENNReal.ofReal (δ/2) := add_le_add hn hSn
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le]
      congr 1
      ring

end EinsteinFull

#print axioms EinsteinFull.ae_canonical_ball_weakSolution
#print axioms EinsteinFull.random_two_point_corrector_remainder_of_second_moments
#print axioms EinsteinFull.random_two_point_corrector_remainder_uniform_time
#print axioms EinsteinFull.random_two_point_corrector_remainder_at_random_times
#print axioms EinsteinFull.random_two_point_corrector_remainder_at_tight_random_times
#print axioms EinsteinFull.random_two_point_corrector_remainder_under_tight_time_changes
#print axioms EinsteinFull.random_two_point_corrector_remainder_uniform_time_of_eventual_tightness
#print axioms EinsteinFull.random_two_point_corrector_remainder_under_eventually_tight_time_changes
#print axioms EinsteinFull.exists_holder_harmonic_gradient_halfBall
#print axioms EinsteinFull.ae_canonical_rescaled_harmonic_holder
#print axioms EinsteinFull.ae_canonical_rescaled_corrector_holder

#print axioms EinsteinFull.canonical_spatial_harmonic_holder

#print axioms EinsteinFull.normalized_weak_potential_translate

#print axioms EinsteinFull.canonical_spatial_harmonic_holder_normalized

#print axioms EinsteinFull.ae_reduced_uniform_rescaled_harmonic_holder

#print axioms EinsteinFull.ae_physical_canonical_sublinear_weak_potential

#print axioms EinsteinFull.ae_physical_canonical_centered_corrector_holder

#print axioms EinsteinFull.centered_rescaled_energy_tendsto_zero

#print axioms EinsteinFull.coordinate_add_energy_le

#print axioms EinsteinFull.ae_physical_canonical_eventual_uniform_holder

#print axioms EinsteinFull.exists_continuous_representative_of_rescaled_holder

#print axioms EinsteinFull.continuous_origin_gauge_of_ae

#print axioms EinsteinFull.ae_physical_continuous_canonical_sublinear_weak_potential

#print axioms EinsteinFull.exists_measurable_reduced_akm_coefficient
#print axioms EinsteinFull.exists_continuous_affine_weak_potential

#print axioms EinsteinFull.ae_reconstructed_canonical_flux_divergence

#print axioms EinsteinFull.exists_continuous_akm_sublinear_weakPotential

#print axioms EinsteinFull.uniform_sublinearity_of_rescaled_holder

#print axioms EinsteinFull.exists_eventual_rescaled_corrector_holder

#print axioms EinsteinFull.uniform_sublinearity_of_affine_harmonic

#print axioms EinsteinFull.exists_uniformly_sublinear_canonical_corrector

#print axioms EinsteinFull.ae_physical_uniformly_sublinear_canonical_corrector

#print axioms EinsteinFull.ae_physical_uniform_canonical_harmonic_coordinate

#print axioms EinsteinFull.continuous_normalized_weak_potential_unique

#print axioms EinsteinFull.normalized_weak_potential_cocycle

#print axioms EinsteinFull.uniform_two_point_sublinearity

#print axioms EinsteinFull.two_point_corrector_remainder_of_tightness

#print axioms EinsteinFull.random_two_point_corrector_remainder_of_tightness

#print axioms EinsteinFull.random_two_point_corrector_remainder_at_scales
