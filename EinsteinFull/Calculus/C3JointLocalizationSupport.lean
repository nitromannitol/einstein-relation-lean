import EinsteinFull.Blueprint.G3.LocalizedCovarianceObjects
import EinsteinFull.Calculus.C2CoarseIdentificationSupport
import EinsteinFull.Calculus.AKMStretchedExponentialMoments
import EinsteinFull.Work.W2.CorrectorReuseSupport
import EinsteinRelation.Correctors.AKMTestConvolution
import EinsteinRelation.Environment.AKMCoefficientObservationUniqueness
import EinsteinRelation.Correctors.WeakPartialAddition
import EinsteinRelation.Calculus.WeakRepresentativeOperations
import EinsteinRelation.Correctors.WeakGradientMeasurability
import EinsteinRelation.TimeChange.Pairing
import EinsteinRelation.Correctors.HeatKernelConvolution
import EinsteinRelation.Correctors.EllipticOperatorBound
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import EinsteinRelation.Probability.ReductionInverseLocality
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! Properties of the actual selected variational family used by joint localization.
The source approximation constant is chosen before the environment law. -/

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM

/-- The full coefficient action is jointly measurable for the source's
test-integral sigma algebra. Raw coefficient evaluation is not used. -/
theorem measurable_translateCoefficient_joint {d : ℕ} {K : ℝ} :
    Measurable (fun p : Vec d × Coefficient d K => translateCoefficient p.1 p.2) := by
  have hobs (u : SmoothCompactTest d) (i j : Fin d) :
      Measurable (fun p : Vec d × Coefficient d K =>
        testIntegral (translateCoefficient p.1 p.2) u i j) := by
    let κ : SmoothCompactTest d :=
      ⟨fun x => u (-x), u.smooth.comp contDiff_neg,
        u.compact.comp_homeomorph (Homeomorph.neg (Vec d))⟩
    have hm := (Correctors.measurable_coefficientTestConvolution (K := K) κ i j).comp
      (measurable_swap : Measurable (Prod.swap : Vec d × Coefficient d K → _))
    convert hm using 1
    funext p
    rw [testIntegral_translate]
    change (∫ x, u (-p.1 + x) * p.2.field x i j) =
      ∫ x, u (-(p.1 - x)) * p.2.field x i j
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [show -p.1 + x = -(p.1 - x) by abel])
  rw [measurable_iff_comap_le]
  change (Environment.AKMTestIntegralSupport.coefficientSigma (d := d) (K := K)).comap
    (fun p : Vec d × Coefficient d K => translateCoefficient p.1 p.2) ≤ _
  unfold Environment.AKMTestIntegralSupport.coefficientSigma
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun u => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun i => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun j => ?_
  rw [MeasurableSpace.comap_comp]
  exact (hobs u i j).comap_le

/-- Strictness of the squared L² norm at a midpoint, without any
representative choice. This is the tie-break step in variational uniqueness. -/
theorem ae_eq_of_midpoint_square_min {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfg : (∫ x, f x ^ 2 ∂μ) = ∫ x, g x ^ 2 ∂μ)
    (hmid : (∫ x, f x ^ 2 ∂μ) ≤ ∫ x, ((f x + g x) / 2) ^ 2 ∂μ) :
    f =ᵐ[μ] g := by
  have hsum := (hf.add hg).integrable_sq
  have hdiff := (hf.sub hg).integrable_sq
  have hmidsq : Integrable (fun x => ((f x + g x) / 2) ^ 2) μ := by
    convert hsum.div_const 4 using 1
    funext x
    dsimp only [Pi.add_apply]
    ring
  have hidentity :
      (∫ x, (f x - g x) ^ 2 ∂μ) =
        2 * (∫ x, f x ^ 2 ∂μ) + 2 * (∫ x, g x ^ 2 ∂μ) -
          4 * (∫ x, ((f x + g x) / 2) ^ 2 ∂μ) := by
    calc
      _ = ∫ x, 2 * f x ^ 2 + 2 * g x ^ 2 -
          4 * ((f x + g x) / 2) ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ = _ := by
        rw [integral_sub (f := fun x => 2 * f x ^ 2 + 2 * g x ^ 2)
            (g := fun x => 4 * ((f x + g x) / 2) ^ 2)
            ((hf.integrable_sq.const_mul 2).add
            (hg.integrable_sq.const_mul 2))
            (hmidsq.const_mul 4),
          integral_add (f := fun x => 2 * f x ^ 2) (g := fun x => 2 * g x ^ 2)
            (hf.integrable_sq.const_mul 2) (hg.integrable_sq.const_mul 2)]
        simp only [integral_const_mul]
  have hzero : (∫ x, (f x - g x) ^ 2 ∂μ) = 0 := by
    have hnonneg : 0 ≤ ∫ x, (f x - g x) ^ 2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg (f x - g x))
    linarith only [hidentity, hfg, hmid, hnonneg]
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => sq_nonneg (f x - g x))) hdiff).mp hzero
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- Recover the centerwise source conclusions for the exact chosen family.
This only asserts measurability at a fixed center; joint measurability needs
an additional internal translation argument. -/
theorem covarianceSourceLocalizedEnergy_source_bound
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (z : Vec d) (r : ℝ), 2 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < 1 → euclideanNorm q < 1 →
        @Measurable (Coefficient d (AKMUpperEllipticity D.ellipticity)) ℝ
          (localSigma (ball z (localizationOuterRadius δ r))) inferInstance
          (fun a => covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q) ∧
        OsBound (actualCoefficientLaw Q) (fun a =>
          |gaussianEnergyJ1 a z r p q -
            covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q|)
          s (C * r ^ (-γ)) := by
  classical
  let hex := EinsteinFull.External.akm_localized_energy d hd
    (AKMUpperEllipticity D.ellipticity) s δ γ
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
  let hα := Classical.choose_spec hex
  let hσ := Classical.choose_spec hα
  let hθ := Classical.choose_spec hσ
  let hC₀ := Classical.choose_spec hθ
  let C := Classical.choose hC₀
  let hC := Classical.choose_spec hC₀
  refine ⟨C, hC.2.2.2.2.2.2.2.2.1, ?_⟩
  intro Q z r hr p q hp hq
  have hW := Classical.choose_spec
    (hC.2.2.2.2.2.2.2.2.2 (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q))
  simpa only [covarianceSourceLocalizedEnergy, dite_eq_left hr,
    covarianceBasis, covarianceSourceSelection] using hW z r hr p q hp hq

/-- Every local source observable is an observable of the full coefficient
sigma algebra; this comparison does not use coefficient point evaluation. -/
theorem coefficientLocalSigma_le {d : ℕ} {K : ℝ} (U : Set (Vec d)) :
    Environment.AKMTestIntegralSupport.localSigma (K := K) U ≤
      Environment.AKMTestIntegralSupport.coefficientSigma (d := d) (K := K) := by
  unfold Environment.AKMTestIntegralSupport.localSigma
  refine iSup_le fun u => iSup_le fun i => iSup_le fun j => ?_
  exact (measurable_testIntegral u.1 i j).comap_le

/-- Translating the chosen energy at the origin gives an actual jointly
measurable family for unit loads. The variational translation identity below
identifies this family with the actual selected energy at each center. -/
theorem covarianceSourceLocalizedEnergy_translated_origin_measurable
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (p q : Vec d) (hp : euclideanNorm p < 1) (hq : euclideanNorm q < 1) :
    Measurable (fun v : Vec d × Coefficient d (AKMUpperEllipticity D.ellipticity) =>
      covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q
        (translateCoefficient v.1 v.2) 0 r p q) := by
  classical
  by_cases hr : 2 ≤ r
  · obtain ⟨C, _, hC⟩ := covarianceSourceLocalizedEnergy_source_bound d hd D s δ γ η β h
    have hm := (hC Q 0 r hr p q hp hq).1
    exact (hm.mono (coefficientLocalSigma_le _) le_rfl).comp
      measurable_translateCoefficient_joint
  · simpa only [covarianceSourceLocalizedEnergy, dite_eq_right hr] using
      (measurable_const : Measurable (fun _ : Vec d ×
        Coefficient d (AKMUpperEllipticity D.ellipticity) => (0 : ℝ)))

/-- The source's Euclidean ball is open in the coordinate topology. -/
theorem isOpen_covarianceSourceBall {d : ℕ} (z : Vec d) (T : ℝ) :
    IsOpen (ball z T) := by
  have hsq : Continuous (fun x : Vec d => ∑ i, (x i - z i) * (x i - z i)) :=
    continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).sub continuous_const).mul
        ((continuous_apply i).sub continuous_const)
  exact isOpen_lt (Real.continuous_sqrt.comp hsq) continuous_const

/-- Distributional gradients are unique on the actual open domain, including
when the two potentials agree only almost everywhere inside that domain. -/
theorem weakGradients_ae_eq_on_open_of_potential_ae_eq {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpen U) {f f' : Vec d → ℝ}
    {G H : Vec d → Vec d} (hff' : f =ᵐ[volume.restrict U] f')
    (hG : HasWeakGradient U f G) (hH : HasWeakGradient U f' H) :
    G =ᵐ[volume.restrict U] H := by
  have hi : ∀ i, ∀ᵐ x ∂volume, x ∈ U → G x i - H x i = 0 := by
    intro i
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hG i).2.1.sub (hH i).2.1)
    intro φ hφ hφc hφU
    have htest : IsSpatialTest U φ := ⟨hφ, hφc, hφU⟩
    have hgi := (hG i).2.2 φ htest
    have hhi := (hH i).2.2 φ htest
    have hval : (∫ x in U, f x * coordinateDerivative i φ x) =
        ∫ x in U, f' x * coordinateDerivative i φ x := by
      apply integral_congr_ae
      filter_upwards [hff'] with x hx
      rw [hx]
    have hz : (∫ x in U, G x i * φ x) = ∫ x in U, H x i * φ x := by
      linarith only [hgi, hhi, hval]
    have hgint := Correctors.integrableOn_mul_spatialTest (hG i).2.1 htest
    have hhint := Correctors.integrableOn_mul_spatialTest (hH i).2.1 htest
    have hsupport : ∀ x, x ∉ U → φ x • (G x i - H x i) = 0 := by
      intro x hx
      have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h))
      simp only [hφx, zero_smul]
    change (∫ x, φ x • (G x i - H x i)) = 0
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupport]
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub (by simpa only [IntegrableOn, mul_comm] using hgint)
      (by simpa only [IntegrableOn, mul_comm] using hhint)]
    simpa only [mul_comm, sub_eq_zero] using hz
  apply (ae_restrict_iff' hU.measurableSet).2
  filter_upwards [ae_all_iff.mpr hi] with x hx hxU
  exact funext (fun i => sub_eq_zero.mp (hx i hxU))

/-- The genuine supremum energy is independent of coordinate representatives
whose actual potentials agree almost everywhere in the source domain. -/
theorem localizedEnergyJ1_eq_of_coordinate_potential_ae_eq {d : ℕ} {K : ℝ}
    {a : Coefficient d K} {z : Vec d} {T S σ θ C : ℝ}
    (W V : LocalizedBasis a z T S σ θ C)
    (hWV : ∀ i, (W.coordinate i).potential =ᵐ[volume.restrict (ball z T)]
      (V.coordinate i).potential) (r : ℝ) (p q : Vec d) :
    localizedEnergyJ1 W r p q = localizedEnergyJ1 V r p q := by
  have hgrad : ∀ i, (W.coordinate i).grad =ᵐ[volume.restrict (ball z T)]
      (V.coordinate i).grad := fun i =>
    weakGradients_ae_eq_on_open_of_potential_ae_eq (isOpen_covarianceSourceBall z T) (hWV i)
      (W.coordinate i).weak_gradient (V.coordinate i).weak_gradient
  have hlinear (c : Vec d) : localizedGradient W c =ᵐ[volume.restrict (ball z T)]
      localizedGradient V c := by
    filter_upwards [ae_all_iff.mpr hgrad] with x hx
    simp only [localizedGradient, hx]
  unfold localizedEnergyJ1
  congr 1
  ext e
  have heq (c : Vec d) :
      (∫ x in ball z T, heatKernel z r x *
        (-(1 / 2 : ℝ) * dot (localizedGradient W c x)
          ((a x).mulVec (localizedGradient W c x)) -
          dot p ((a x).mulVec (localizedGradient W c x)) +
          dot q (localizedGradient W c x))) =
      ∫ x in ball z T, heatKernel z r x *
        (-(1 / 2 : ℝ) * dot (localizedGradient V c x)
          ((a x).mulVec (localizedGradient V c x)) -
          dot p ((a x).mulVec (localizedGradient V c x)) +
          dot q (localizedGradient V c x)) := by
    apply integral_congr_ae
    filter_upwards [hlinear c] with x hx
    rw [hx]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.trans (heq c)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.trans (heq c).symm⟩

/-- Scaling preserves a spatial weak gradient on its actual domain. -/
theorem covariance_hasWeakGradient_const_smul {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → ℝ} {G : Vec d → Vec d} (h : HasWeakGradient U f G) (c : ℝ) :
    HasWeakGradient U (fun x => c * f x) (fun x => c • G x) := by
  intro i
  refine ⟨fun x hx => ((h i).1 x hx).smul c,
    fun x hx => ((h i).2.1 x hx).smul c, ?_⟩
  intro φ hφ
  have he := (h i).2.2 φ hφ
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_const_mul, he]
  ring

/-- A spatial test's coordinate derivative remains supported inside the domain. -/
theorem covariance_isSpatialTest_coordinateDerivative {d : ℕ} {U : Set (Vec d)}
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) (i : Fin d) :
    IsSpatialTest U (coordinateDerivative i φ) := by
  refine ⟨(contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const,
    hφ.2.1.fderiv_apply ℝ (unitVector i), ?_⟩
  apply Set.Subset.trans ?_ hφ.2.2
  apply closure_minimal ?_ isClosed_closure
  intro x hx
  by_contra hxs
  exact hx (by simp [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs])

/-- Actual divergence-free fields on an arbitrary spatial domain are additive. -/
theorem covariance_hasWeakDivergence_add_zero {d : ℕ} {U : Set (Vec d)}
    {F G : Vec d → Vec d}
    (hF : HasWeakDivergence U F (fun _ => 0))
    (hG : HasWeakDivergence U G (fun _ => 0)) :
    HasWeakDivergence U (fun x => F x + G x) (fun _ => 0) := by
  refine ⟨fun i => (hF.1 i).add (hG.1 i), hF.2.1, ?_⟩
  intro φ hφ
  have hFi : IntegrableOn (fun x => dot (F x) (gradient φ x)) U volume := by
    unfold dot gradient
    exact integrable_finset_sum _ fun i _ => Correctors.integrableOn_mul_spatialTest
      (hF.1 i) (covariance_isSpatialTest_coordinateDerivative hφ i)
  have hGi : IntegrableOn (fun x => dot (G x) (gradient φ x)) U volume := by
    unfold dot gradient
    exact integrable_finset_sum _ fun i _ => Correctors.integrableOn_mul_spatialTest
      (hG.1 i) (covariance_isSpatialTest_coordinateDerivative hφ i)
  have hdot : ∀ x, dot (F x + G x) (gradient φ x) =
      dot (F x) (gradient φ x) + dot (G x) (gradient φ x) := by
    intro x
    simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  simp_rw [hdot]
  rw [integral_add hFi hGi, hF.2.2 φ hφ, hG.2.2 φ hφ]
  simp only [zero_mul, integral_zero, neg_zero, add_zero]

/-- Scaling an actual divergence-free field preserves its weak equation. -/
theorem covariance_hasWeakDivergence_const_smul_zero {d : ℕ} {U : Set (Vec d)}
    {F : Vec d → Vec d} (hF : HasWeakDivergence U F (fun _ => 0)) (c : ℝ) :
    HasWeakDivergence U (fun x => c • F x) (fun _ => 0) := by
  refine ⟨fun i x hx => (hF.1 i x hx).smul c, hF.2.1, ?_⟩
  intro φ hφ
  have hdot : ∀ x, dot (c • F x) (gradient φ x) = c * dot (F x) (gradient φ x) := by
    intro x
    simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
  simp_rw [hdot]
  rw [integral_const_mul, hF.2.2 φ hφ]
  simp only [zero_mul, integral_zero, neg_zero, mul_zero]

/-- The actual midpoint of two finite-domain harmonic functions retains its
potential, weak Euclidean gradient and divergence equation. -/
noncomputable def covarianceLocalHarmonicMidpoint {d : ℕ} {K : ℝ} {a : Coefficient d K}
    {z : Vec d} {T : ℝ} (w v : LocalHarmonic a z T) : LocalHarmonic a z T := by
  have hgrad : HasWeakGradient (ball z T)
      (fun x => (1 / 2 : ℝ) * (w.potential x + v.potential x))
      (fun x => (1 / 2 : ℝ) • (w.grad x + v.grad x)) :=
    covariance_hasWeakGradient_const_smul
      (fun i => Correctors.hasWeakPartialDerivative_add (w.weak_gradient i)
        (v.weak_gradient i)) (1 / 2)
  refine { potential := fun x => (1 / 2 : ℝ) * (w.potential x + v.potential x)
           grad := fun x => (1 / 2 : ℝ) • (w.grad x + v.grad x)
           square_integrable := (w.square_integrable.add v.square_integrable).const_mul _
           weak_gradient := hgrad
           gradient_square_integrable := ?_
           harmonic := ?_ }
  · have hm := Correctors.aestronglyMeasurable_euclideanNorm_of_weakGradient
      (isOpen_covarianceSourceBall z T) hgrad
    apply ((w.gradient_square_integrable.add v.gradient_square_integrable).const_mul
      (1 / 2 : ℝ)).mono' hm
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (show 0 ≤ euclideanNorm ((1 / 2 : ℝ) • (w.grad x + v.grad x)) from
        Real.sqrt_nonneg _),
      TimeChange.euclideanNorm_smul, abs_of_pos (by norm_num : 0 < (1 / 2 : ℝ))]
    exact mul_le_mul_of_nonneg_left (TimeChange.euclideanNorm_add_le _ _) (by norm_num)
  · have hdiv := covariance_hasWeakDivergence_const_smul_zero
      (covariance_hasWeakDivergence_add_zero w.harmonic v.harmonic) (1 / 2 : ℝ)
    simpa only [Matrix.mulVec_smul, Matrix.mulVec_add] using hdiv

/-- The gradient-bound part of AKM's actual admissible class is preserved by
midpoints, with the Euclidean squared norm and the same constant. -/
theorem covarianceLocalHarmonicMidpoint_admissible {d : ℕ} {K : ℝ}
    {a : Coefficient d K} {z : Vec d} {T C : ℝ} (w v : LocalHarmonic a z T)
    (hw : IsLocalizationAdmissible C w) (hv : IsLocalizationAdmissible C v) :
    IsLocalizationAdmissible C (covarianceLocalHarmonicMidpoint w v) := by
  let m := covarianceLocalHarmonicMidpoint w v
  have hwi : Integrable (fun x => euclideanSq (w.grad x))
      (volume.restrict (ball z T)) := by
    simpa only [TimeChange.euclideanSq_eq_sq_euclideanNorm] using
      w.gradient_square_integrable.integrable_sq
  have hvi : Integrable (fun x => euclideanSq (v.grad x))
      (volume.restrict (ball z T)) := by
    simpa only [TimeChange.euclideanSq_eq_sq_euclideanNorm] using
      v.gradient_square_integrable.integrable_sq
  have hmi : Integrable (fun x => euclideanSq (m.grad x))
      (volume.restrict (ball z T)) := by
    simpa only [TimeChange.euclideanSq_eq_sq_euclideanNorm] using
      m.gradient_square_integrable.integrable_sq
  have hp (x : Vec d) : euclideanSq (m.grad x) ≤
      (euclideanSq (w.grad x) + euclideanSq (v.grad x)) / 2 := by
    change (∑ i, ((1 / 2 : ℝ) * (w.grad x i + v.grad x i)) *
      ((1 / 2 : ℝ) * (w.grad x i + v.grad x i))) ≤
        ((∑ i, w.grad x i * w.grad x i) + (∑ i, v.grad x i * v.grad x i)) / 2
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (w.grad x i - v.grad x i)]
  have hle := integral_mono hmi ((hwi.add hvi).div_const 2) hp
  simp only [Pi.add_apply] at hle
  rw [integral_div, integral_add hwi hvi] at hle
  have havg : (⨍ x in ball z T, euclideanSq (m.grad x)) ≤
      ((⨍ x in ball z T, euclideanSq (w.grad x)) +
        (⨍ x in ball z T, euclideanSq (v.grad x))) / 2 := by
    simp only [average_eq, smul_eq_mul]
    have hm := mul_le_mul_of_nonneg_left hle
      (show 0 ≤ ((volume.restrict (ball z T)).real Set.univ)⁻¹ from
        inv_nonneg.mpr ENNReal.toReal_nonneg)
    nlinarith only [hm]
  have hw' := (Real.sqrt_le_iff.mp hw).2
  have hv' := (Real.sqrt_le_iff.mp hv).2
  apply Real.sqrt_le_iff.mpr
  exact ⟨(Real.sqrt_le_iff.mp hw).1, by linarith only [havg, hw', hv']⟩

/-- The literal source ball has finite coordinate Lebesgue volume. -/
theorem volume_covarianceSourceBall_lt_top {d : ℕ} (z : Vec d) (T : ℝ) :
    volume (ball z T) < ⊤ := by
  have hsub : ball z T ⊆ Metric.ball z T := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm]
    apply lt_of_le_of_lt ?_ hx
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    change (x i - z i) ^ 2 ≤ ∑ j, (x j - z j) * (x j - z j)
    rw [pow_two]
    exact Finset.single_le_sum (fun j _ => mul_self_nonneg ((x - z) j)) (Finset.mem_univ i)
  exact lt_of_le_of_lt (measure_mono hsub) Metric.isBounded_ball.measure_lt_top

/-- A uniform bound for the literal isotropic source kernel, also valid for
its algebraic value at zero scale. -/
theorem covarianceSourceHeatKernel_bound {d : ℕ} (y x : Vec d) (s : ℝ) :
    |heatKernel y s x| ≤ (4 * Real.pi * s ^ 2) ^ (-(d : ℝ) / 2) := by
  have hc : 0 ≤ (4 * Real.pi * s ^ 2) ^ (-(d : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  have he : Real.exp (-euclideanSq (x - y) / (4 * s ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · rw [TimeChange.euclideanSq_eq_sq_euclideanNorm]
      exact neg_nonpos.mpr (sq_nonneg _)
    · positivity
  unfold heatKernel Correctors.euclideanHeatKernel
  rw [abs_mul, abs_of_nonneg hc, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left he hc).trans_eq (mul_one _)

/-- Actual L2 source potentials have integrable truncated heat pairings;
subsequent linearity arguments may therefore split these integrals. -/
theorem covarianceSourceHeatPairing_integrable {d : ℕ} {z : Vec d} {T : ℝ}
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict (ball z T)))
    (y : Vec d) (s : ℝ) :
    IntegrableOn (fun x => heatKernel y s x * f x) (ball z T) volume := by
  have : IsFiniteMeasure (volume.restrict (ball z T)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      volume_covarianceSourceBall_lt_top z T⟩
  apply (hf.integrable (by norm_num)).bdd_mul
    (((Correctors.continuous_euclideanHeatKernel (s ^ 2)).comp
      (continuous_id.sub continuous_const)).aestronglyMeasurable.restrict)
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.sub_apply, id_eq, heatKernel] using
      covarianceSourceHeatKernel_bound y x s)

/-- The truncated source pairing is continuous in its center for every L2
potential, using a uniform Gaussian majorant on the actual finite ball. -/
theorem continuous_covarianceSourceHeatPairing {d : ℕ} {z : Vec d} {T : ℝ}
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict (ball z T))) (s : ℝ) :
    Continuous (fun y => ∫ x in ball z T, heatKernel y s x * f x) := by
  have : IsFiniteMeasure (volume.restrict (ball z T)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      volume_covarianceSourceBall_lt_top z T⟩
  apply continuous_of_dominated
    (bound := fun x => (4 * Real.pi * s ^ 2) ^ (-(d : ℝ) / 2) * |f x|)
  · intro y
    exact (covarianceSourceHeatPairing_integrable hf y s).aestronglyMeasurable
  · intro y
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (covarianceSourceHeatKernel_bound y x s)
        (abs_nonneg _))
  · exact (hf.integrable (by norm_num)).abs.const_mul _
  · exact Filter.Eventually.of_forall (fun x =>
      ((Correctors.continuous_euclideanHeatKernel (s ^ 2)).comp
        (continuous_const.sub continuous_id)).mul continuous_const)

/-- The source objective's outer square is integrable; both truncated
integrals can therefore be split in convexity arguments. -/
theorem covarianceSourceHeatPairing_square_integrable {d : ℕ}
    {z : Vec d} {T : ℝ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball z T))) (s R : ℝ) :
    IntegrableOn (fun y => (∫ x in ball z T, heatKernel y s x * f x) ^ 2)
      (ball z R) volume := by
  have : IsFiniteMeasure (volume.restrict (ball z T)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      volume_covarianceSourceBall_lt_top z T⟩
  have : IsFiniteMeasure (volume.restrict (ball z R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      volume_covarianceSourceBall_lt_top z R⟩
  let B := (4 * Real.pi * s ^ 2) ^ (-(d : ℝ) / 2) *
    ∫ x in ball z T, |f x|
  have hB (y : Vec d) : |∫ x in ball z T, heatKernel y s x * f x| ≤ B := by
    have hi := norm_integral_le_of_norm_le
      ((hf.integrable (by norm_num)).abs.const_mul
        ((4 * Real.pi * s ^ 2) ^ (-(d : ℝ) / 2)))
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (covarianceSourceHeatKernel_bound y x s)
          (abs_nonneg _)))
    simpa only [Real.norm_eq_abs, integral_const_mul] using hi
  apply Integrable.mono' (integrable_const (B ^ 2))
    (((continuous_covarianceSourceHeatPairing hf s).pow 2).aestronglyMeasurable.restrict)
  exact Filter.Eventually.of_forall (fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      _ = |∫ x in ball z T, heatKernel y s x * f x| ^ 2 := (sq_abs _).symm
      _ ≤ B ^ 2 := (sq_le_sq₀ (abs_nonneg _)
        ((abs_nonneg _).trans (hB y))).2 (hB y))

/-- Convexity of the literal truncated Gaussian objective on L2 potentials. -/
theorem covarianceLocalizationObjective_midpoint_le {d : ℕ} {z : Vec d}
    {T : ℝ} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball z T)))
    (hg : MemLp g 2 (volume.restrict (ball z T))) (S σ θ : ℝ) :
    localizationObjective z T S σ θ (fun x => (f x + g x) / 2) ≤
      (localizationObjective z T S σ θ f +
        localizationObjective z T S σ θ g) / 2 := by
  have hm : MemLp (fun x => (f x + g x) / 2) 2
      (volume.restrict (ball z T)) := by
    simpa only [div_eq_mul_inv, mul_comm, Pi.add_apply] using (hf.add hg).const_mul (2 : ℝ)⁻¹
  have hlin (y : Vec d) :
      (∫ x in ball z T, heatKernel y (σ * S) x * ((f x + g x) / 2)) =
        ((∫ x in ball z T, heatKernel y (σ * S) x * f x) +
          (∫ x in ball z T, heatKernel y (σ * S) x * g x)) / 2 := by
    simp_rw [← mul_div_assoc, mul_add]
    rw [integral_div, integral_add
      (covarianceSourceHeatPairing_integrable hf y (σ * S))
      (covarianceSourceHeatPairing_integrable hg y (σ * S))]
  have hpoint (y : Vec d) :
      (∫ x in ball z T, heatKernel y (σ * S) x * ((f x + g x) / 2)) ^ 2 ≤
        ((∫ x in ball z T, heatKernel y (σ * S) x * f x) ^ 2 +
          (∫ x in ball z T, heatKernel y (σ * S) x * g x) ^ 2) / 2 := by
    rw [hlin]
    nlinarith [sq_nonneg ((∫ x in ball z T, heatKernel y (σ * S) x * f x) -
      (∫ x in ball z T, heatKernel y (σ * S) x * g x))]
  have hfi := covarianceSourceHeatPairing_square_integrable hf (σ * S) (S / θ)
  have hgi := covarianceSourceHeatPairing_square_integrable hg (σ * S) (S / θ)
  have hle := integral_mono
    (covarianceSourceHeatPairing_square_integrable hm (σ * S) (S / θ))
    ((hfi.add hgi).div_const 2) hpoint
  simp only [Pi.add_apply] at hle
  rw [integral_div, integral_add hfi hgi] at hle
  unfold localizationObjective
  simp only [average_eq, smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left hle
    (show 0 ≤ ((volume.restrict (ball z (S / θ))).real Set.univ)⁻¹ from
      inv_nonneg.mpr ENNReal.toReal_nonneg)
  nlinarith only [h]

/-- Centered affine coordinates belong to L2 on the literal finite ball. -/
theorem covarianceSourceCoordinate_memLp {d : ℕ} (z : Vec d) (T : ℝ) (i : Fin d) :
    MemLp (fun x => (x - z) i) 2 (volume.restrict (ball z T)) := by
  have : IsFiniteMeasure (volume.restrict (ball z T)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      volume_covarianceSourceBall_lt_top z T⟩
  apply MemLp.of_bound
    (((continuous_apply i).comp (continuous_id.sub continuous_const)).aestronglyMeasurable.restrict)
    T
  filter_upwards [ae_restrict_mem (isOpen_covarianceSourceBall z T).measurableSet] with x hx
  rw [Real.norm_eq_abs]
  apply lt_of_le_of_lt ?_ hx |>.le
  apply Real.abs_le_sqrt
  change (x i - z i) ^ 2 ≤ ∑ j, (x j - z j) * (x j - z j)
  rw [pow_two]
  exact Finset.single_le_sum (fun j _ => mul_self_nonneg ((x - z) j)) (Finset.mem_univ i)

/-- The midpoint of actual coordinate minimizers is again a minimizer of
the same source objective with the same RMS constraint. -/
theorem covarianceLocalHarmonicMidpoint_minimizer {d : ℕ} {K : ℝ}
    {a : Coefficient d K} {z : Vec d} {T S σ θ C : ℝ} {i : Fin d}
    {w v : LocalHarmonic a z T}
    (hw : IsCoordinateMinimizer S σ θ C i w)
    (hv : IsCoordinateMinimizer S σ θ C i v) :
    IsCoordinateMinimizer S σ θ C i (covarianceLocalHarmonicMidpoint w v) := by
  refine ⟨covarianceLocalHarmonicMidpoint_admissible w v hw.1 hv.1, ?_⟩
  intro u hu
  have hc := covarianceLocalizationObjective_midpoint_le
    (w.square_integrable.sub (covarianceSourceCoordinate_memLp z T i))
    (v.square_integrable.sub (covarianceSourceCoordinate_memLp z T i)) S σ θ
  have heq : (fun x => ((w.potential x - (x - z) i) +
      (v.potential x - (x - z) i)) / 2) =
      (fun x => (covarianceLocalHarmonicMidpoint w v).potential x - (x - z) i) := by
    funext x
    change ((w.potential x - (x - z) i) + (v.potential x - (x - z) i)) / 2 =
      (1 / 2 : ℝ) * (w.potential x + v.potential x) - (x - z) i
    ring
  change localizationObjective z T S σ θ
    (fun x => ((w.potential x - (x - z) i) + (v.potential x - (x - z) i)) / 2) ≤
      (localizationObjective z T S σ θ (fun x => w.potential x - (x - z) i) +
        localizationObjective z T S σ θ (fun x => v.potential x - (x - z) i)) / 2 at hc
  rw [heq] at hc
  linarith [hw.2 u hu, hv.2 u hu]

/-- The source's least-L2 tie-break determines every coordinate potential
up to spatial AE equality, without any measurability premise on the choice. -/
theorem covarianceLeastNormCoordinateMinimizer_ae_eq {d : ℕ} {K : ℝ}
    {a : Coefficient d K} {z : Vec d} {T S σ θ C : ℝ} {i : Fin d}
    {w v : LocalHarmonic a z T}
    (hw : IsLeastNormCoordinateMinimizer S σ θ C i w)
    (hv : IsLeastNormCoordinateMinimizer S σ θ C i v) :
    w.potential =ᵐ[volume.restrict (ball z T)] v.potential := by
  apply ae_eq_of_midpoint_square_min w.square_integrable v.square_integrable
  · exact le_antisymm (hw.2 v hv.1) (hv.2 w hw.1)
  · have h := hw.2 (covarianceLocalHarmonicMidpoint w v)
      (covarianceLocalHarmonicMidpoint_minimizer hw.1 hv.1)
    convert h using 1 <;> congr 1
    funext x
    change ((w.potential x + v.potential x) / 2) ^ 2 =
      ((1 / 2 : ℝ) * (w.potential x + v.potential x)) ^ 2
    ring

/-- The actual localized energy is independent of every permissible
least-norm coordinate selection, for arbitrary real loads and scale. -/
theorem covarianceLocalizedBasis_energy_eq {d : ℕ} {K : ℝ}
    {a : Coefficient d K} {z : Vec d} {T S σ θ C : ℝ}
    (W V : LocalizedBasis a z T S σ θ C) (r : ℝ) (p q : Vec d) :
    localizedEnergyJ1 W r p q = localizedEnergyJ1 V r p q :=
  localizedEnergyJ1_eq_of_coordinate_potential_ae_eq W V
    (fun i => covarianceLeastNormCoordinateMinimizer_ae_eq (W.selected i) (V.selected i)) r p q

/-- Translation takes the literal Euclidean source ball to the ball with
translated center, without changing its radius. -/
theorem covarianceSourceBall_preimage_sub {d : ℕ} (z y : Vec d) (T : ℝ) :
    (fun x : Vec d => x - y) ⁻¹' ball z T = ball (z + y) T := by
  ext x
  change euclideanNorm (x - y - z) < T ↔ euclideanNorm (x - (z + y)) < T
  rw [show x - y - z = x - (z + y) by abel]

/-- Translation preserves the restricted volume on the actual source balls. -/
theorem covarianceSourceBall_measurePreserving_sub {d : ℕ} (z y : Vec d) (T : ℝ) :
    MeasurePreserving (fun x : Vec d => x - y)
      (volume.restrict (ball (z + y) T)) (volume.restrict (ball z T)) := by
  have hm : MeasurePreserving (fun x : Vec d => x - y) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-y)
  simpa only [covarianceSourceBall_preimage_sub] using
    hm.restrict_preimage (isOpen_covarianceSourceBall z T).measurableSet

/-- A change of variables on a source ball, valid even for totalized
integrals before an integrability statement is available. -/
theorem covarianceSourceBall_integral_sub {d : ℕ} (z y : Vec d) (T : ℝ)
    (f : Vec d → ℝ) :
    (∫ x in ball (z + y) T, f (x - y)) = ∫ x in ball z T, f x := by
  apply (covarianceSourceBall_measurePreserving_sub z y T).integral_comp
  simpa only [sub_eq_add_neg, Homeomorph.coe_addRight] using
    (Homeomorph.addRight (-y)).measurableEmbedding

/-- The truncated source pairing commutes with translation of both centers
and the potential, at exactly the same kernel scale and truncation radius. -/
theorem covarianceSourceHeatPairing_translate {d : ℕ} (z y v : Vec d)
    (T s : ℝ) (f : Vec d → ℝ) :
    (∫ x in ball (z + y) T, heatKernel (v + y) s x * f (x - y)) =
      ∫ x in ball z T, heatKernel v s x * f x := by
  have heq (x : Vec d) : heatKernel (v + y) s x = heatKernel v s (x - y) := by
    unfold heatKernel
    rw [show x - (v + y) = x - y - v by abel]
  simp_rw [heq]
  exact covarianceSourceBall_integral_sub z y T (fun x => heatKernel v s x * f x)

/-- The actual objective is translation invariant, with every parameter
and the outer volume normalization unchanged. -/
theorem covarianceLocalizationObjective_translate {d : ℕ} (z y : Vec d)
    (T S σ θ : ℝ) (f : Vec d → ℝ) :
    localizationObjective (z + y) T S σ θ (fun x => f (x - y)) =
      localizationObjective z T S σ θ f := by
  have hm : (volume.restrict (ball (z + y) (S / θ))).real Set.univ =
      (volume.restrict (ball z (S / θ))).real Set.univ := by
    exact (covarianceSourceBall_measurePreserving_sub z y (S / θ)).measureReal_preimage
      (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  unfold localizationObjective
  simp only [average_eq, smul_eq_mul, hm]
  congr 1
  have hpair (v : Vec d) :
      (∫ x in ball (z + y) T, heatKernel v (σ * S) x * f (x - y)) =
        ∫ x in ball z T, heatKernel (v - y) (σ * S) x * f x := by
    simpa only [sub_add_cancel] using
      covarianceSourceHeatPairing_translate z y (v - y) T (σ * S) f
  simp_rw [hpair]
  exact covarianceSourceBall_integral_sub z y (S / θ)
    (fun v => (∫ x in ball z T, heatKernel v (σ * S) x * f x) ^ 2)

/-- Local integrability on an open set commutes with spatial translation. -/
theorem covariance_locallyIntegrableOn_translate {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {f : Vec d → ℝ} (hf : LocallyIntegrableOn f U volume)
    (y : Vec d) :
    LocallyIntegrableOn (fun x => f (x - y)) ((fun x : Vec d => x - y) ⁻¹' U) volume := by
  intro x hx
  obtain ⟨V, hV, hi⟩ := hf (x - y) hx
  obtain ⟨W, hW, hxW, hWV⟩ := mem_nhdsWithin.mp hV
  have hmp : MeasurePreserving (fun x : Vec d => x - y) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-y)
  refine ⟨(fun x : Vec d => x - y) ⁻¹' (W ∩ U), ?_, ?_⟩
  · apply mem_nhdsWithin.mpr
    exact ⟨(fun x : Vec d => x - y) ⁻¹' W,
      hW.preimage (continuous_id.sub continuous_const), hxW, fun _ h => h⟩
  · exact (hmp.restrict_preimage (hW.measurableSet.inter hU.measurableSet)).integrable_comp_of_integrable
      (hi.mono_set hWV)

/-- A source-ball test translates to the corresponding test on the old ball. -/
theorem covariance_isSpatialTest_translate {d : ℕ} {z y : Vec d} {T : ℝ}
    {φ : Vec d → ℝ} (hφ : IsSpatialTest (ball (z + y) T) φ) :
    IsSpatialTest (ball z T) (fun x => φ (x + y)) := by
  refine ⟨hφ.1.comp (contDiff_id.add contDiff_const),
    hφ.2.1.comp_homeomorph (Homeomorph.addRight y), ?_⟩
  intro x hx
  have hx' := hφ.2.2 (tsupport_comp_subset_preimage φ
    (continuous_id.add continuous_const) hx)
  change euclideanNorm ((x + y) - (z + y)) < T at hx'
  change euclideanNorm (x - z) < T
  simpa only [add_sub_add_right_eq_sub] using hx'

/-- Coordinate derivatives of translated smooth tests are translated derivatives. -/
theorem covariance_coordinateDerivative_translate {d : ℕ} (i : Fin d)
    (φ : Vec d → ℝ) (y x : Vec d) :
    coordinateDerivative i (fun z => φ (z + y)) x = coordinateDerivative i φ (x + y) := by
  simp only [coordinateDerivative, fderiv_comp_add_right]

/-- Actual weak partial derivatives translate on the literal source balls. -/
theorem covariance_hasWeakPartialDerivative_translate {d : ℕ} {z : Vec d} {T : ℝ}
    {f g : Vec d → ℝ} {i : Fin d} (h : HasWeakPartialDerivative (ball z T) i f g)
    (y : Vec d) : HasWeakPartialDerivative (ball (z + y) T) i
      (fun x => f (x - y)) (fun x => g (x - y)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [covarianceSourceBall_preimage_sub] using
      covariance_locallyIntegrableOn_translate (isOpen_covarianceSourceBall z T) h.1 y
  · simpa only [covarianceSourceBall_preimage_sub] using
      covariance_locallyIntegrableOn_translate (isOpen_covarianceSourceBall z T) h.2.1 y
  · intro φ hφ
    have he := h.2.2 (fun x => φ (x + y)) (covariance_isSpatialTest_translate hφ)
    have hd := covarianceSourceBall_integral_sub z y T
      (fun x => f x * coordinateDerivative i (fun u => φ (u + y)) x)
    have hg := covarianceSourceBall_integral_sub z y T (fun x => g x * φ (x + y))
    simp only [covariance_coordinateDerivative_translate, sub_add_cancel] at hd hg
    rw [hd, hg]
    simpa only [covariance_coordinateDerivative_translate] using he

/-- Actual weak divergence translates on the literal source balls. -/
theorem covariance_hasWeakDivergence_translate {d : ℕ} {z : Vec d} {T : ℝ}
    {F : Vec d → Vec d} {f : Vec d → ℝ} (h : HasWeakDivergence (ball z T) F f)
    (y : Vec d) : HasWeakDivergence (ball (z + y) T)
      (fun x => F (x - y)) (fun x => f (x - y)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa only [covarianceSourceBall_preimage_sub] using
      covariance_locallyIntegrableOn_translate (isOpen_covarianceSourceBall z T) (h.1 i) y
  · simpa only [covarianceSourceBall_preimage_sub] using
      covariance_locallyIntegrableOn_translate (isOpen_covarianceSourceBall z T) h.2.1 y
  · intro φ hφ
    have he := h.2.2 (fun x => φ (x + y)) (covariance_isSpatialTest_translate hφ)
    have hgrad (x : Vec d) : gradient (fun u => φ (u + y)) x = gradient φ (x + y) := by
      funext i
      exact covariance_coordinateDerivative_translate i φ y x
    have hd := covarianceSourceBall_integral_sub z y T
      (fun x => dot (F x) (gradient (fun u => φ (u + y)) x))
    have hg := covarianceSourceBall_integral_sub z y T (fun x => f x * φ (x + y))
    simp only [hgrad, sub_add_cancel] at hd hg
    rw [hd, hg]
    simpa only [hgrad] using he

/-- Change the center and coefficient of an actual harmonic function by an
exact spatial translation. Field matching is pointwise, not probabilistic. -/
noncomputable def covarianceLocalHarmonicTransport {d : ℕ} {K : ℝ}
    {a b : Coefficient d K} {z z' : Vec d} {T : ℝ}
    (w : LocalHarmonic a z T) (y : Vec d) (hz : z' = z + y)
    (hab : ∀ x, b x = a (x - y)) : LocalHarmonic b z' T := by
  have hmp : MeasurePreserving (fun x : Vec d => x - y)
      (volume.restrict (ball z' T)) (volume.restrict (ball z T)) := by
    rw [hz]
    exact covarianceSourceBall_measurePreserving_sub z y T
  refine { potential := fun x => w.potential (x - y)
           grad := fun x => w.grad (x - y)
           square_integrable := w.square_integrable.comp_measurePreserving hmp
           gradient_square_integrable := w.gradient_square_integrable.comp_measurePreserving hmp
           weak_gradient := ?_
           harmonic := ?_ }
  · intro i
    rw [hz]
    exact covariance_hasWeakPartialDerivative_translate (w.weak_gradient i) y
  · rw [hz]
    have h := covariance_hasWeakDivergence_translate w.harmonic y
    simpa only [hab] using h

/-- Actual harmonic functions translate with their coefficient field; the
potential and weak gradient are transported together. -/
noncomputable def covarianceLocalHarmonicTranslate {d : ℕ} {K : ℝ}
    {a : Coefficient d K} {z : Vec d} {T : ℝ}
    (w : LocalHarmonic a z T) (y : Vec d) :
    LocalHarmonic (translateCoefficient (-y) a) (z + y) T :=
  covarianceLocalHarmonicTransport w y rfl (fun x => by
    change a (-y + x) = a (x - y)
    rw [neg_add_eq_sub])

/-- The Euclidean RMS constraint is unchanged by translation of the actual
harmonic function and its source ball. -/
theorem covarianceLocalHarmonicTranslate_admissible {d : ℕ} {K : ℝ}
    {a : Coefficient d K} {z : Vec d} {T C : ℝ}
    (w : LocalHarmonic a z T) (y : Vec d) :
    IsLocalizationAdmissible C (covarianceLocalHarmonicTranslate w y) ↔
      IsLocalizationAdmissible C w := by
  have hm : (volume.restrict (ball (z + y) T)).real Set.univ =
      (volume.restrict (ball z T)).real Set.univ := by
    exact (covarianceSourceBall_measurePreserving_sub z y T).measureReal_preimage
      (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  change Real.sqrt (⨍ x in ball (z + y) T, euclideanSq (w.grad (x - y))) ≤ C ↔
    Real.sqrt (⨍ x in ball z T, euclideanSq (w.grad x)) ≤ C
  simp only [average_eq, smul_eq_mul, hm,
    covarianceSourceBall_integral_sub z y T (fun x => euclideanSq (w.grad x))]

/-- Move an origin harmonic function for the translated coefficient back
to the actual coefficient and prescribed source center. -/
noncomputable def covarianceLocalHarmonicFromOrigin {d : ℕ} {K : ℝ}
    {a : Coefficient d K} {z : Vec d} {T : ℝ}
    (w : LocalHarmonic (translateCoefficient z a) 0 T) : LocalHarmonic a z T :=
  covarianceLocalHarmonicTransport w z (zero_add z).symm (fun x => by
    change a x = a (z + (x - z))
    rw [show z + (x - z) = x by abel])

/-- Move an actual centered harmonic function to the origin with the
translated coefficient, keeping the actual potential and weak gradient. -/
noncomputable def covarianceLocalHarmonicToOrigin {d : ℕ} {K : ℝ}
    {a : Coefficient d K} {z : Vec d} {T : ℝ}
    (w : LocalHarmonic a z T) : LocalHarmonic (translateCoefficient z a) 0 T :=
  covarianceLocalHarmonicTransport w (-z) (add_neg_cancel z).symm (fun x => by
    change a (z + x) = a (x - -z)
    rw [sub_neg_eq_add, add_comm])

/-- The exact transport preserves admissibility for the same RMS constant. -/
theorem covarianceLocalHarmonicTransport_admissible {d : ℕ} {K : ℝ}
    {a b : Coefficient d K} {z z' : Vec d} {T C : ℝ}
    (w : LocalHarmonic a z T) (y : Vec d) (hz : z' = z + y)
    (hab : ∀ x, b x = a (x - y)) :
    IsLocalizationAdmissible C (covarianceLocalHarmonicTransport w y hz hab) ↔
      IsLocalizationAdmissible C w := by
  change Real.sqrt (⨍ x in ball z' T, euclideanSq (w.grad (x - y))) ≤ C ↔
    Real.sqrt (⨍ x in ball z T, euclideanSq (w.grad x)) ≤ C
  rw [hz]
  exact covarianceLocalHarmonicTranslate_admissible w y

/-- The coordinate objective is preserved by the actual harmonic transport. -/
theorem covarianceLocalHarmonicTransport_objective {d : ℕ} {K : ℝ}
    {a b : Coefficient d K} {z z' : Vec d} {T : ℝ}
    (w : LocalHarmonic a z T) (y : Vec d) (hz : z' = z + y)
    (hab : ∀ x, b x = a (x - y)) (S σ θ : ℝ) (i : Fin d) :
    localizationObjective z' T S σ θ
      (fun x => (covarianceLocalHarmonicTransport w y hz hab).potential x - (x - z') i) =
    localizationObjective z T S σ θ (fun x => w.potential x - (x - z) i) := by
  change localizationObjective z' T S σ θ
    (fun x => w.potential (x - y) - (x - z') i) = _
  rw [hz]
  have heq : (fun x => w.potential (x - y) - (x - (z + y)) i) =
      (fun x => w.potential (x - y) - ((x - y) - z) i) := by
    funext x
    rw [show x - (z + y) = (x - y) - z by abel]
  rw [heq]
  exact covarianceLocalizationObjective_translate z y T S σ θ
    (fun x => w.potential x - (x - z) i)

/-- The least-norm functional is preserved by the actual harmonic transport. -/
theorem covarianceLocalHarmonicTransport_squareIntegral {d : ℕ} {K : ℝ}
    {a b : Coefficient d K} {z z' : Vec d} {T : ℝ}
    (w : LocalHarmonic a z T) (y : Vec d) (hz : z' = z + y)
    (hab : ∀ x, b x = a (x - y)) :
    (∫ x in ball z' T, (covarianceLocalHarmonicTransport w y hz hab).potential x ^ 2) =
      ∫ x in ball z T, w.potential x ^ 2 := by
  change (∫ x in ball z' T, w.potential (x - y) ^ 2) = _
  rw [hz]
  exact covarianceSourceBall_integral_sub z y T (fun x => w.potential x ^ 2)

/-- Transport preserves the actual coordinate minimization problem with
exactly the same scale parameters and admissibility constant. -/
theorem covarianceLocalHarmonicTransport_minimizer {d : ℕ} {K : ℝ}
    {a b : Coefficient d K} {z z' : Vec d} {T S σ θ C : ℝ} {i : Fin d}
    (w : LocalHarmonic a z T) (y : Vec d) (hz : z' = z + y)
    (hab : ∀ x, b x = a (x - y)) (hw : IsCoordinateMinimizer S σ θ C i w) :
    IsCoordinateMinimizer S σ θ C i (covarianceLocalHarmonicTransport w y hz hab) := by
  refine ⟨(covarianceLocalHarmonicTransport_admissible w y hz hab).2 hw.1, ?_⟩
  intro v hv
  have hz' : z = z' + -y := by rw [hz]; abel
  have hba : ∀ x, a x = b (x - -y) := by
    intro x
    rw [hab, sub_neg_eq_add, add_sub_cancel_right]
  let u := covarianceLocalHarmonicTransport v (-y) hz' hba
  have hu : IsLocalizationAdmissible C u :=
    (covarianceLocalHarmonicTransport_admissible v (-y) hz' hba).2 hv
  rw [covarianceLocalHarmonicTransport_objective]
  have h := hw.2 u hu
  rw [covarianceLocalHarmonicTransport_objective v (-y) hz' hba] at h
  exact h

/-- Translation preserves the actual least-L2 tie-break, without choosing
new structural parameters or assuming uniqueness of representatives. -/
theorem covarianceLocalHarmonicTransport_leastMinimizer {d : ℕ} {K : ℝ}
    {a b : Coefficient d K} {z z' : Vec d} {T S σ θ C : ℝ} {i : Fin d}
    (w : LocalHarmonic a z T) (y : Vec d) (hz : z' = z + y)
    (hab : ∀ x, b x = a (x - y)) (hw : IsLeastNormCoordinateMinimizer S σ θ C i w) :
    IsLeastNormCoordinateMinimizer S σ θ C i
      (covarianceLocalHarmonicTransport w y hz hab) := by
  refine ⟨covarianceLocalHarmonicTransport_minimizer w y hz hab hw.1, ?_⟩
  intro v hv
  have hz' : z = z' + -y := by rw [hz]; abel
  have hba : ∀ x, a x = b (x - -y) := by
    intro x
    rw [hab, sub_neg_eq_add, add_sub_cancel_right]
  let u := covarianceLocalHarmonicTransport v (-y) hz' hba
  have hu : IsCoordinateMinimizer S σ θ C i u :=
    covarianceLocalHarmonicTransport_minimizer v (-y) hz' hba hv
  rw [covarianceLocalHarmonicTransport_squareIntegral]
  have h := hw.2 u hu
  rw [covarianceLocalHarmonicTransport_squareIntegral v (-y) hz' hba] at h
  exact h

/-- Transport the actual coordinate minimizers with their fixed source tuple. -/
noncomputable def covarianceLocalizedBasisTransport {d : ℕ} {K : ℝ}
    {a b : Coefficient d K} {z z' : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (y : Vec d) (hz : z' = z + y)
    (hab : ∀ x, b x = a (x - y)) : LocalizedBasis b z' T S σ θ C where
  coordinate i := covarianceLocalHarmonicTransport (W.coordinate i) y hz hab
  selected i := covarianceLocalHarmonicTransport_leastMinimizer
    (W.coordinate i) y hz hab (W.selected i)

/-- The genuine real-coefficient supremum energy commutes with transport.
This is a pointwise identity for every coefficient field and both real loads. -/
theorem covarianceLocalizedBasisTransport_energy {d : ℕ} {K : ℝ}
    {a b : Coefficient d K} {z z' : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (y : Vec d) (hz : z' = z + y)
    (hab : ∀ x, b x = a (x - y)) (r : ℝ) (p q : Vec d) :
    localizedEnergyJ1 (covarianceLocalizedBasisTransport W y hz hab) r p q =
      localizedEnergyJ1 W r p q := by
  have hk (x : Vec d) : heatKernel z' r x = heatKernel z r (x - y) := by
    unfold heatKernel
    rw [hz, show x - (z + y) = x - y - z by abel]
  have heq (c : Vec d) :
      (∫ x in ball z' T, heatKernel z' r x *
        (-(1 / 2 : ℝ) * dot
            (localizedGradient (covarianceLocalizedBasisTransport W y hz hab) c x)
            ((b x).mulVec
              (localizedGradient (covarianceLocalizedBasisTransport W y hz hab) c x)) -
          dot p ((b x).mulVec
            (localizedGradient (covarianceLocalizedBasisTransport W y hz hab) c x)) +
          dot q (localizedGradient (covarianceLocalizedBasisTransport W y hz hab) c x))) =
      ∫ x in ball z T, heatKernel z r x *
        (-(1 / 2 : ℝ) * dot (localizedGradient W c x)
            ((a x).mulVec (localizedGradient W c x)) -
          dot p ((a x).mulVec (localizedGradient W c x)) +
          dot q (localizedGradient W c x)) := by
    have hg (x : Vec d) :
        localizedGradient (covarianceLocalizedBasisTransport W y hz hab) c x =
          localizedGradient W c (x - y) := rfl
    simp_rw [hg, hk, hab]
    rw [hz]
    exact covarianceSourceBall_integral_sub z y T (fun x => heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (localizedGradient W c x)
          ((a x).mulVec (localizedGradient W c x)) -
        dot p ((a x).mulVec (localizedGradient W c x)) +
        dot q (localizedGradient W c x)))
  unfold localizedEnergyJ1
  congr 1
  ext e
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.trans (heq c)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.trans (heq c).symm⟩

/-- The actual centerwise chosen source family equals its translated-origin
value, pointwise in the coefficient and center, for all real loads. -/
theorem covarianceSourceLocalizedEnergy_eq_translated_origin
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (a : Coefficient d (AKMUpperEllipticity D.ellipticity))
    (z : Vec d) (r : ℝ) (p q : Vec d) :
    covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q =
      covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q
        (translateCoefficient z a) 0 r p q := by
  classical
  by_cases hr : 2 ≤ r
  · simp only [covarianceSourceLocalizedEnergy, dite_eq_left hr]
    let W := covarianceBasis d hd D s δ γ η β h Q (translateCoefficient z a) 0 r hr
    have hab : ∀ x, a x = (translateCoefficient z a) (x - z) := by
      intro x
      change a x = a (z + (x - z))
      rw [show z + (x - z) = x by abel]
    let V := covarianceLocalizedBasisTransport W z (zero_add z).symm hab
    exact (covarianceLocalizedBasis_energy_eq
      (covarianceBasis d hd D s δ γ η β h Q a z r hr) V r p q).trans
        (covarianceLocalizedBasisTransport_energy W z (zero_add z).symm hab r p q)
  · simp only [covarianceSourceLocalizedEnergy, dite_eq_right hr]

/-- Exact stationarity of the actual chosen energy, pointwise in the source
coefficient field and with no change of its structural selection tuple. -/
theorem covarianceSourceLocalizedEnergy_translate
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (a : Coefficient d (AKMUpperEllipticity D.ellipticity))
    (z y : Vec d) (r : ℝ) (p q : Vec d) :
    covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a (z + y) r p q =
      covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q
        (translateCoefficient y a) z r p q := by
  rw [covarianceSourceLocalizedEnergy_eq_translated_origin
        d hd D s δ γ η β h Q a (z + y),
      covarianceSourceLocalizedEnergy_eq_translated_origin
        d hd D s δ γ η β h Q (translateCoefficient y a) z]
  have he : translateCoefficient (z + y) a =
      translateCoefficient z (translateCoefficient y a) := by
    apply coefficient_ext
    funext x
    change a ((z + y) + x) = a (y + (z + x))
    rw [show (z + y) + x = y + (z + x) by abel]
  rw [he]

/-- Joint measurability of the actual chosen family follows from its proved
pointwise translation identity and the genuine source measurable origin. -/
theorem covarianceSourceLocalizedEnergy_joint_measurable
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (p q : Vec d) (hp : euclideanNorm p < 1) (hq : euclideanNorm q < 1) :
    Measurable (fun v : Vec d × Coefficient d (AKMUpperEllipticity D.ellipticity) =>
      covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q v.2 v.1 r p q) := by
  have heq : (fun v : Vec d × Coefficient d (AKMUpperEllipticity D.ellipticity) =>
      covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q v.2 v.1 r p q) =
      (fun v => covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q
        (translateCoefficient v.1 v.2) 0 r p q) := by
    funext v
    exact covarianceSourceLocalizedEnergy_eq_translated_origin
      d hd D s δ γ η β h Q v.2 v.1 r p q
  rw [heq]
  exact covarianceSourceLocalizedEnergy_translated_origin_measurable
    d hd D s δ γ η β h Q r p q hp hq

/-- Completion of the square for the actual symmetric elliptic coefficient,
using the dimension-free Euclidean operator bound. -/
theorem covarianceEnergyDensity_le {d : ℕ} {K : ℝ} (hK : 0 < K)
    (a : Coefficient d K) (x p q ξ : Vec d) :
    -(1 / 2 : ℝ) * dot ξ ((a x).mulVec ξ) -
        dot p ((a x).mulVec ξ) + dot q ξ ≤
      (K * euclideanNorm p + euclideanNorm q) ^ 2 / 2 := by
  have hm : euclideanNorm ((a x).mulVec ξ) ≤ K * euclideanNorm ξ :=
    Correctors.mulVec_euclideanNorm_le_of_quadratic (a x) hK (a.symmetric x)
      (fun v => (by
        have hn : 0 ≤ euclideanSq v := by
          unfold euclideanSq dot
          exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
        exact hn.trans (a.elliptic x v).1))
      (fun v => (a.elliptic x v).2) ξ
  have hp : -dot p ((a x).mulVec ξ) ≤
      euclideanNorm p * (K * euclideanNorm ξ) :=
    (neg_le_abs _).trans ((TimeChange.abs_dot_le_euclideanNorm _ _).trans
      (mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg _)))
  have hq : dot q ξ ≤ euclideanNorm q * euclideanNorm ξ :=
    (le_abs_self _).trans (TimeChange.abs_dot_le_euclideanNorm _ _)
  have he := (a.elliptic x ξ).1
  rw [TimeChange.euclideanSq_eq_sq_euclideanNorm] at he
  nlinarith [sq_nonneg (euclideanNorm ξ - (K * euclideanNorm p + euclideanNorm q))]

/-- A single real coefficient-vector value in the genuine source supremum. -/
noncomputable def covarianceLocalizedEnergyValue {d : ℕ} {K : ℝ}
    {a : Coefficient d K} {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (r : ℝ) (p q c : Vec d) : ℝ :=
  ∫ x in ball z T, heatKernel z r x *
    (-(1 / 2 : ℝ) * dot (localizedGradient W c x)
        ((a x).mulVec (localizedGradient W c x)) -
      dot p ((a x).mulVec (localizedGradient W c x)) +
        dot q (localizedGradient W c x))

/-- The source energy is exactly the supremum over all real coefficient vectors. -/
theorem localizedEnergyJ1_eq_sSup_range {d : ℕ} {K : ℝ}
    {a : Coefficient d K} {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (r : ℝ) (p q : Vec d) :
    localizedEnergyJ1 W r p q = sSup (Set.range (covarianceLocalizedEnergyValue W r p q)) := by
  unfold localizedEnergyJ1 covarianceLocalizedEnergyValue
  congr 1
  ext e
  simp only [Set.mem_setOf_eq, Set.mem_range, eq_comm]

/-- Every coefficient-vector value satisfies the deterministic load bound.
The totalized nonintegrable branch is handled explicitly; no integral is split. -/
theorem covarianceLocalizedEnergyValue_le {d : ℕ} {K : ℝ} (hK : 0 < K)
    {a : Coefficient d K} {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) {r : ℝ} (hr : 0 < r) (p q c : Vec d) :
    covarianceLocalizedEnergyValue W r p q c ≤
      (K * euclideanNorm p + euclideanNorm q) ^ 2 / 2 := by
  let B := (K * euclideanNorm p + euclideanNorm q) ^ 2 / 2
  have hB : 0 ≤ B := div_nonneg (sq_nonneg _) (by norm_num)
  have hk : Integrable (heatKernel z r) :=
    (Correctors.integrable_euclideanHeatKernel (sq_pos_of_pos hr)).comp_sub_right z
  have hk0 (x : Vec d) : 0 ≤ heatKernel z r x :=
    Correctors.euclideanHeatKernel_nonneg (sq_nonneg r) _
  have hk1 : ∫ x, heatKernel z r x = 1 := by
    unfold heatKernel
    rw [integral_sub_right_eq_self, Correctors.integral_euclideanHeatKernel (sq_pos_of_pos hr)]
  unfold covarianceLocalizedEnergyValue
  by_cases hi : IntegrableOn (fun x => heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (localizedGradient W c x)
          ((a x).mulVec (localizedGradient W c x)) -
        dot p ((a x).mulVec (localizedGradient W c x)) + dot q (localizedGradient W c x)))
      (ball z T)
  · calc
      _ ≤ ∫ x in ball z T, heatKernel z r x * B :=
        integral_mono hi ((hk.mul_const B).restrict) (fun x =>
          mul_le_mul_of_nonneg_left (covarianceEnergyDensity_le hK a x p q _) (hk0 x))
      _ ≤ ∫ x, heatKernel z r x * B :=
        setIntegral_le_integral (hk.mul_const B)
          (Filter.Eventually.of_forall (fun x => mul_nonneg (hk0 x) hB))
      _ = B := by rw [integral_mul_const, hk1, one_mul]
  · rw [integral_undef hi]
    exact hB

/-- The actual source supremum is nonnegative and has the exact deterministic
Euclidean load bound, for every real coefficient-vector subspace. -/
theorem localizedEnergyJ1_nonneg_le {d : ℕ} {K : ℝ} (hK : 0 < K)
    {a : Coefficient d K} {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) {r : ℝ} (hr : 0 < r) (p q : Vec d) :
    0 ≤ localizedEnergyJ1 W r p q ∧
      localizedEnergyJ1 W r p q ≤ (K * euclideanNorm p + euclideanNorm q) ^ 2 / 2 := by
  rw [localizedEnergyJ1_eq_sSup_range]
  have hb : BddAbove (Set.range (covarianceLocalizedEnergyValue W r p q)) :=
    ⟨_, by rintro _ ⟨c, rfl⟩; exact covarianceLocalizedEnergyValue_le hK W hr p q c⟩
  have hz : covarianceLocalizedEnergyValue W r p q 0 = 0 := by
    simp [covarianceLocalizedEnergyValue, localizedGradient, dot]
  constructor
  · rw [← hz]
    exact le_csSup hb (Set.mem_range_self _)
  · exact csSup_le (Set.range_nonempty _) (by
      rintro _ ⟨c, rfl⟩
      exact covarianceLocalizedEnergyValue_le hK W hr p q c)

/-- The full coefficient-vector parametrization is linear. -/
theorem localizedGradient_smul {d : ℕ} {K : ℝ}
    {a : Coefficient d K} {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (b : ℝ) (c x : Vec d) :
    localizedGradient W (b • c) x = b • localizedGradient W c x := by
  simp only [localizedGradient, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Simultaneously scaling both loads and the full coefficient vector scales
one source energy value quadratically; totalized integrals also obey this. -/
theorem covarianceLocalizedEnergyValue_smul {d : ℕ} {K : ℝ}
    {a : Coefficient d K} {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (r b : ℝ) (p q c : Vec d) :
    covarianceLocalizedEnergyValue W r (b • p) (b • q) (b • c) =
      b ^ 2 * covarianceLocalizedEnergyValue W r p q c := by
  unfold covarianceLocalizedEnergyValue
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [localizedGradient_smul, Matrix.mulVec_smul]
    change heatKernel z r x *
      (-(1 / 2 : ℝ) * dotProduct (b • localizedGradient W c x)
          (b • (a x).mulVec (localizedGradient W c x)) -
        dotProduct (b • p) (b • (a x).mulVec (localizedGradient W c x)) +
          dotProduct (b • q) (b • localizedGradient W c x)) = _
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    change heatKernel z r x *
      (-(1 / 2 : ℝ) * (b * (b * dot (localizedGradient W c x)
          ((a x).mulVec (localizedGradient W c x)))) -
        b * (b * dot p ((a x).mulVec (localizedGradient W c x))) +
          b * (b * dot q (localizedGradient W c x))) = _
    ring)

/-- Quadratic real-load homogeneity of the actual full source supremum.
The reverse inequality uses all real coefficient vectors, including inverse
rescaling, rather than restricting the optimizing class. -/
theorem localizedEnergyJ1_smul {d : ℕ} {K : ℝ} (hK : 0 < K)
    {a : Coefficient d K} {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) {r : ℝ} (hr : 0 < r)
    (b : ℝ) (p q : Vec d) :
    localizedEnergyJ1 W r (b • p) (b • q) = b ^ 2 * localizedEnergyJ1 W r p q := by
  by_cases hb : b = 0
  · subst b
    have h := localizedEnergyJ1_nonneg_le hK W hr (0 : Vec d) 0
    simpa only [zero_smul, zero_pow (by decide : 2 ≠ 0), zero_mul] using
      le_antisymm (by simpa [euclideanNorm, euclideanSq, dot] using h.2) h.1
  have hs : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hbd (p q : Vec d) : BddAbove (Set.range (covarianceLocalizedEnergyValue W r p q)) :=
    ⟨_, by rintro _ ⟨c, rfl⟩; exact covarianceLocalizedEnergyValue_le hK W hr p q c⟩
  rw [localizedEnergyJ1_eq_sSup_range, localizedEnergyJ1_eq_sSup_range]
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨c, rfl⟩
    have hc := covarianceLocalizedEnergyValue_smul W r b p q (b⁻¹ • c)
    rw [smul_smul, mul_inv_cancel₀ hb, one_smul] at hc
    rw [hc]
    exact mul_le_mul_of_nonneg_left
      (le_csSup (hbd p q) (Set.mem_range_self _)) hs.le
  · have hh : sSup (Set.range (covarianceLocalizedEnergyValue W r p q)) ≤
        sSup (Set.range (covarianceLocalizedEnergyValue W r (b • p) (b • q))) / b ^ 2 := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨c, rfl⟩
      apply (le_div_iff₀ hs).2
      rw [mul_comm, ← covarianceLocalizedEnergyValue_smul]
      exact le_csSup (hbd (b • p) (b • q)) (Set.mem_range_self _)
    simpa only [mul_comm] using (le_div_iff₀ hs).1 hh

/-- The actual chosen family obeys the deterministic load bound, including
its defined zero value below the source scale range. -/
theorem covarianceSourceLocalizedEnergy_nonneg_le
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (a : Coefficient d (AKMUpperEllipticity D.ellipticity))
    (z : Vec d) (r : ℝ) (p q : Vec d) :
    0 ≤ covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q ∧
      covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q ≤
        (AKMUpperEllipticity D.ellipticity * euclideanNorm p + euclideanNorm q) ^ 2 / 2 := by
  by_cases hr : 2 ≤ r
  · simp only [covarianceSourceLocalizedEnergy, dite_eq_left hr]
    exact localizedEnergyJ1_nonneg_le
      (mul_pos (ellipticityScale_pos D.one_le_ellipticity)
        (ellipticityScale_pos D.one_le_ellipticity))
      _ (by linarith) p q
  · simp only [covarianceSourceLocalizedEnergy, dite_eq_right hr]
    exact ⟨le_rfl, div_nonneg (sq_nonneg _) (by norm_num)⟩

/-- Quadratic real-load homogeneity for the actual chosen centerwise family. -/
theorem covarianceSourceLocalizedEnergy_smul
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (a : Coefficient d (AKMUpperEllipticity D.ellipticity))
    (z : Vec d) (r b : ℝ) (p q : Vec d) :
    covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r (b • p) (b • q) =
      b ^ 2 * covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q := by
  by_cases hr : 2 ≤ r
  · simp only [covarianceSourceLocalizedEnergy, dite_eq_left hr]
    exact localizedEnergyJ1_smul
      (mul_pos (ellipticityScale_pos D.one_le_ellipticity)
        (ellipticityScale_pos D.one_le_ellipticity))
      _ (by linarith) b p q
  · simp only [covarianceSourceLocalizedEnergy, dite_eq_right hr, mul_zero]

/-- The actual selected family is jointly measurable for arbitrary real loads.
Both loads are divided by the same deterministic positive scalar. -/
theorem covarianceSourceLocalizedEnergy_joint_measurable_real
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (p q : Vec d) :
    Measurable (fun v : Vec d × Coefficient d (AKMUpperEllipticity D.ellipticity) =>
      covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q v.2 v.1 r p q) := by
  let b := 1 + euclideanNorm p + euclideanNorm q
  have hb : 0 < b := by dsimp [b, euclideanNorm]; positivity
  have hp : euclideanNorm (b⁻¹ • p) < 1 := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hb), inv_mul_eq_div]
    apply (div_lt_one hb).2
    dsimp [b]
    have hn : 0 ≤ euclideanNorm q := Real.sqrt_nonneg _
    linarith
  have hq : euclideanNorm (b⁻¹ • q) < 1 := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hb), inv_mul_eq_div]
    apply (div_lt_one hb).2
    dsimp [b]
    have hn : 0 ≤ euclideanNorm p := Real.sqrt_nonneg _
    linarith
  have heq : (fun v : Vec d × Coefficient d (AKMUpperEllipticity D.ellipticity) =>
      covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q v.2 v.1 r p q) =
      (fun v => b ^ 2 * covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q
        v.2 v.1 r (b⁻¹ • p) (b⁻¹ • q)) := by
    funext v
    simpa only [smul_smul, mul_inv_cancel₀ hb.ne', one_smul] using
      covarianceSourceLocalizedEnergy_smul d hd D s δ γ η β h Q v.2 v.1 r b
        (b⁻¹ • p) (b⁻¹ • q)
  rw [heq]
  exact (covarianceSourceLocalizedEnergy_joint_measurable d hd D s δ γ η β h Q r
    (b⁻¹ • p) (b⁻¹ • q) hp hq).const_mul (b ^ 2)

/-- Every real-load source energy is spatially integrable against the actual
Gaussian after any measurable spatial rescaling. This precedes any Bochner
splitting of the physical polarization. -/
theorem covarianceSourceLocalizedEnergy_heat_integrable
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (a : Coefficient d (AKMUpperEllipticity D.ellipticity))
    (g : Vec d → Vec d) (hg : Measurable g) (y : Vec d)
    {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (p q : Vec d) :
    Integrable (fun z => heatKernel y ρ z *
      covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a (g z) r p q) := by
  let B := (AKMUpperEllipticity D.ellipticity * euclideanNorm p + euclideanNorm q) ^ 2 / 2
  have hm0 := covarianceSourceLocalizedEnergy_joint_measurable_real d hd D s δ γ η β h Q r p q
  have hmap : Measurable (fun z : Vec d => (g z, a)) := hg.prodMk measurable_const
  have hm := hm0.comp hmap
  have hk : Integrable (heatKernel y ρ) :=
    (Correctors.integrable_euclideanHeatKernel (sq_pos_of_pos hρ)).comp_sub_right y
  have hkc : Continuous (heatKernel y ρ) :=
    (Correctors.continuous_euclideanHeatKernel _).comp (continuous_id.sub continuous_const)
  apply (hk.mul_const B).mono' (hkc.measurable.mul hm).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    have hk0 : 0 ≤ heatKernel y ρ z :=
      Correctors.euclideanHeatKernel_nonneg (sq_nonneg ρ) _
    have he := covarianceSourceLocalizedEnergy_nonneg_le d hd D s δ γ η β h Q a (g z) r p q
    change ‖heatKernel y ρ z *
      covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a (g z) r p q‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg hk0 he.1)]
    exact mul_le_mul_of_nonneg_left he.2 hk0)

/-- Real-load energies have every finite-measure Lp bound, under their
actual coefficient sigma algebra. -/
theorem covarianceSourceLocalizedEnergy_memLp
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (P : Measure (Coefficient d (AKMUpperEllipticity D.ellipticity)))
    [IsFiniteMeasure P] (e : ENNReal) (z : Vec d) (r : ℝ) (p q : Vec d) :
    MemLp (fun a => covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q) e P := by
  have hm := (covarianceSourceLocalizedEnergy_joint_measurable_real
    d hd D s δ γ η β h Q r p q).comp
      (measurable_const.prodMk measurable_id : Measurable
        (fun a : Coefficient d (AKMUpperEllipticity D.ellipticity) => (z, a)))
  apply MemLp.of_bound hm.aestronglyMeasurable
    ((AKMUpperEllipticity D.ellipticity * euclideanNorm p + euclideanNorm q) ^ 2 / 2)
  exact Filter.Eventually.of_forall (fun a => by
    have he := covarianceSourceLocalizedEnergy_nonneg_le d hd D s δ γ η β h Q a z r p q
    change ‖covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q‖ ≤ _
    rw [Real.norm_of_nonneg he.1]
    exact he.2)

/-- Centering under a finite coefficient law preserves genuine joint
measurability of the actual selected energy. -/
theorem covarianceCenteredLocalizedEnergy_joint_measurable
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (P : Measure (Coefficient d (AKMUpperEllipticity D.ellipticity)))
    [IsFiniteMeasure P] (r : ℝ) (p q : Vec d) :
    Measurable (fun v : Vec d × Coefficient d (AKMUpperEllipticity D.ellipticity) =>
      centeredLocalizedEnergy P (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q)
        v.2 v.1 r p q) := by
  have hm := covarianceSourceLocalizedEnergy_joint_measurable_real d hd D s δ γ η β h Q r p q
  exact hm.sub (hm.stronglyMeasurable.integral_prod_right'.measurable.comp measurable_fst)

/-- Literal source centering has every finite-measure Lp bound. -/
theorem covarianceCenteredLocalizedEnergy_memLp
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (P : Measure (Coefficient d (AKMUpperEllipticity D.ellipticity)))
    [IsFiniteMeasure P] (e : ENNReal) (z : Vec d) (r : ℝ) (p q : Vec d) :
    MemLp (fun a => centeredLocalizedEnergy P
      (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z r p q) e P :=
  (covarianceSourceLocalizedEnergy_memLp d hd D s δ γ η β h Q P e z r p q).sub (memLp_const _)

/-- Literal source centering has mean zero under the actual probability law. -/
theorem covarianceCenteredLocalizedEnergy_integral_eq_zero
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (P : Measure (Coefficient d (AKMUpperEllipticity D.ellipticity)))
    [IsProbabilityMeasure P] (z : Vec d) (r : ℝ) (p q : Vec d) :
    (∫ a, centeredLocalizedEnergy P
      (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z r p q ∂P) = 0 := by
  have hi := memLp_one_iff_integrable.mp
    (covarianceSourceLocalizedEnergy_memLp d hd D s δ γ η β h Q P 1 z r p q)
  simp only [centeredLocalizedEnergy]
  rw [integral_sub hi (integrable_const _)]
  simp

/-- Both the source value and its probability mean lie in the deterministic
load interval, so literal centering preserves the same absolute bound. -/
theorem covarianceCenteredLocalizedEnergy_abs_le
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (P : Measure (Coefficient d (AKMUpperEllipticity D.ellipticity)))
    [IsProbabilityMeasure P]
    (a : Coefficient d (AKMUpperEllipticity D.ellipticity))
    (z : Vec d) (r : ℝ) (p q : Vec d) :
    |centeredLocalizedEnergy P (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q)
      a z r p q| ≤
      (AKMUpperEllipticity D.ellipticity * euclideanNorm p + euclideanNorm q) ^ 2 / 2 := by
  have hi := memLp_one_iff_integrable.mp
    (covarianceSourceLocalizedEnergy_memLp d hd D s δ γ η β h Q P 1 z r p q)
  have hl : 0 ≤ ∫ b, covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q b z r p q ∂P :=
    integral_nonneg (fun b =>
      (covarianceSourceLocalizedEnergy_nonneg_le d hd D s δ γ η β h Q b z r p q).1)
  have hu : (∫ b, covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q b z r p q ∂P) ≤
      (AKMUpperEllipticity D.ellipticity * euclideanNorm p + euclideanNorm q) ^ 2 / 2 := by
    calc
      _ ≤ ∫ _b, (AKMUpperEllipticity D.ellipticity * euclideanNorm p +
          euclideanNorm q) ^ 2 / 2 ∂P := integral_mono hi (integrable_const _) (fun b =>
        (covarianceSourceLocalizedEnergy_nonneg_le d hd D s δ γ η β h Q b z r p q).2)
      _ = _ := by simp
  have he := covarianceSourceLocalizedEnergy_nonneg_le d hd D s δ γ η β h Q a z r p q
  unfold centeredLocalizedEnergy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The actual centered real-load energies are Gaussian spatially integrable
before physical normalization and subtraction of polarized terms. -/
theorem covarianceCenteredLocalizedEnergy_heat_integrable
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (P : Measure (Coefficient d (AKMUpperEllipticity D.ellipticity)))
    [IsProbabilityMeasure P]
    (a : Coefficient d (AKMUpperEllipticity D.ellipticity))
    (g : Vec d → Vec d) (hg : Measurable g) (y : Vec d)
    {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (p q : Vec d) :
    Integrable (fun z => heatKernel y ρ z * centeredLocalizedEnergy P
      (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a (g z) r p q) := by
  let B := (AKMUpperEllipticity D.ellipticity * euclideanNorm p + euclideanNorm q) ^ 2 / 2
  have hm0 := covarianceCenteredLocalizedEnergy_joint_measurable d hd D s δ γ η β h Q P r p q
  have hmap : Measurable (fun z : Vec d => (g z, a)) := hg.prodMk measurable_const
  have hm := hm0.comp hmap
  have hk : Integrable (heatKernel y ρ) :=
    (Correctors.integrable_euclideanHeatKernel (sq_pos_of_pos hρ)).comp_sub_right y
  have hkc : Continuous (heatKernel y ρ) :=
    (Correctors.continuous_euclideanHeatKernel _).comp (continuous_id.sub continuous_const)
  apply (hk.mul_const B).mono' (hkc.measurable.mul hm).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    have hk0 : 0 ≤ heatKernel y ρ z :=
      Correctors.euclideanHeatKernel_nonneg (sq_nonneg ρ) _
    change ‖heatKernel y ρ z * centeredLocalizedEnergy P
      (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a (g z) r p q‖ ≤ _
    rw [norm_mul, Real.norm_of_nonneg hk0, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (covarianceCenteredLocalizedEnergy_abs_le d hd D s δ γ η β h Q P a (g z) r p q) hk0)

/-- The exact source local sigma algebra also supports arbitrary real loads.
The common positive rescaling preserves the actual selected family and radius. -/
theorem covarianceSourceLocalizedEnergy_local_measurable_real
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d) :
    @Measurable (Coefficient d (AKMUpperEllipticity D.ellipticity)) ℝ
      (localSigma (ball z (localizationOuterRadius δ r))) inferInstance
      (fun a => covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q) := by
  let b := 1 + euclideanNorm p + euclideanNorm q
  have hb : 0 < b := by dsimp [b, euclideanNorm]; positivity
  have hp : euclideanNorm (b⁻¹ • p) < 1 := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hb), inv_mul_eq_div]
    apply (div_lt_one hb).2
    dsimp [b]
    have hn : 0 ≤ euclideanNorm q := Real.sqrt_nonneg _
    linarith
  have hq : euclideanNorm (b⁻¹ • q) < 1 := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hb), inv_mul_eq_div]
    apply (div_lt_one hb).2
    dsimp [b]
    have hn : 0 ≤ euclideanNorm p := Real.sqrt_nonneg _
    linarith
  have heq : (fun a => covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q) =
      (fun a => b ^ 2 * covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q
        a z r (b⁻¹ • p) (b⁻¹ • q)) := by
    funext a
    simpa only [smul_smul, mul_inv_cancel₀ hb.ne', one_smul] using
      covarianceSourceLocalizedEnergy_smul d hd D s δ γ η β h Q a z r b
        (b⁻¹ • p) (b⁻¹ • q)
  rw [heq]
  obtain ⟨C, hC, hsource⟩ := covarianceSourceLocalizedEnergy_source_bound d hd D s δ γ η β h
  exact ((hsource Q z r hr (b⁻¹ • p) (b⁻¹ • q) hp hq).1).const_mul (b ^ 2)

/-- The literal physical polarized matrix coordinate is spatially integrable
against the isotropic source Gaussian, before any Bochner splitting. -/
theorem covarianceLocalizedEntry_heat_integrable
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (j k : Fin d) (ω : FieldPair d)
    (y : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun z => heatKernel y ρ z *
      covarianceLocalizedEntry d hd D s δ γ η β h Q r z j k ω) := by
  classical
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  by_cases hω : ω ∈ ReductionImageV3.physicalReducedRange D.ellipticity
  · let a := project (r₀ := D.dependenceRange) Q.ellipticity_parameter
      (ReductionImageV3.inverseReducePhysical ⟨ω, hω⟩)
    let A := ellipticityScale D.ellipticity • homogenizedCoefficient Q
    have hg : Measurable (fun z : Vec d => D.dependenceRange⁻¹ • z) :=
      (continuous_const_smul (D.dependenceRange⁻¹ : ℝ)).measurable
    have hip := covarianceCenteredLocalizedEnergy_heat_integrable
      d hd D s δ γ η β h Q (actualCoefficientLaw Q) a
      (fun z => D.dependenceRange⁻¹ • z) hg y hρ (r / D.dependenceRange)
      (unitVector j + unitVector k) (A.mulVec (unitVector j))
    have him := covarianceCenteredLocalizedEnergy_heat_integrable
      d hd D s δ γ η β h Q (actualCoefficientLaw Q) a
      (fun z => D.dependenceRange⁻¹ • z) hg y hρ (r / D.dependenceRange)
      (unitVector j - unitVector k) (A.mulVec (unitVector j))
    convert ((hip.sub him).const_mul (ellipticityScale D.ellipticity)⁻¹).div_const 2 using 1
    funext z
    simp only [covarianceLocalizedEntry, dite_eq_left hω]
    dsimp only [a, A, Pi.sub_apply]
    ring
  · simp only [covarianceLocalizedEntry, dite_eq_right hω, mul_zero]
    apply integrable_zero

open Classical in
/-- Zero extension of a genuine coefficient observable through the physical
reduced-image inverse and the actual normalization map. -/
noncomputable def covariancePhysicalLift {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (F : Coefficient d (AKMUpperEllipticity L) → ℝ)
    (ω : FieldPair d) : ℝ :=
  if hω : ω ∈ ReductionImageV3.physicalReducedRange L then
    F (project (r₀ := r₀) Q.ellipticity_parameter
      (ReductionImageV3.inverseReducePhysical ⟨ω, hω⟩))
  else 0

/-- Reconstruction agrees pointwise on every physical field. -/
theorem covariancePhysicalLift_reduce {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (F : Coefficient d (AKMUpperEllipticity L) → ℝ)
    (ω : ReductionImageV3.PhysicalField d L) :
    covariancePhysicalLift Q F (reduce ω.1) =
      F (project (r₀ := r₀) Q.ellipticity_parameter ω) := by
  have hω : reduce ω.1 ∈ ReductionImageV3.physicalReducedRange L := ⟨ω.1, ω.2, rfl⟩
  simp only [covariancePhysicalLift, dite_eq_left hω]
  exact congrArg (fun v => F (project (r₀ := r₀) Q.ellipticity_parameter v))
    (ReductionImageV3.inverseReduce_reducePhysical ω)

/-- Measurable observables remain measurable under the exact physical lift. -/
theorem covariancePhysicalLift_measurable {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (F : Coefficient d (AKMUpperEllipticity L) → ℝ)
    (hF : Measurable F) : Measurable (covariancePhysicalLift Q F) := by
  classical
  unfold covariancePhysicalLift
  exact Measurable.dite
    (hF.comp ((measurable_project (r₀ := r₀) Q.ellipticity_parameter).comp
      (ReductionImageV3.physicalReduceHomeomorph (d := d) (L := L)).symm.continuous.measurable))
    measurable_const (ReductionImageV3.measurableSet_physicalReducedRange L)

/-- The physical reference reduction preserves the literal ambient reduced law.
This small map identity uses only the existing reference-law construction. -/
theorem covariancePhysicalReduction_measurePreserving {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    MeasurePreserving (fun ω : ReductionImageV3.PhysicalField d L => reduce ω.1)
      (ReductionImageV3.physicalReferenceLaw Q) (reducedLaw Q) := by
  refine ⟨Probability.measurable_reduce.comp measurable_subtype_coe, ?_⟩
  change Measure.map (reduce ∘ Subtype.val) (ReductionImageV3.physicalReferenceLaw Q) =
    Measure.map reduce Q.measure
  rw [← Measure.map_map Probability.measurable_reduce measurable_subtype_coe,
    ReductionImageV3.physicalReferenceLaw_forget Q]

/-- The exact lift has the original coefficient-law integral. -/
theorem covariancePhysicalLift_integral {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (F : Coefficient d (AKMUpperEllipticity L) → ℝ)
    (hF : Measurable F) :
    (∫ ω, covariancePhysicalLift Q F ω ∂reducedLaw Q) =
      ∫ a, F a ∂actualCoefficientLaw Q := by
  have hemb : MeasurableEmbedding
      (fun ω : ReductionImageV3.PhysicalField d L => reduce ω.1) :=
    (Probability.measurableEmbedding_reduce d).comp
      (MeasurableEmbedding.subtype_coe (Sharpness.measurableSet_isRegular_fieldPair L))
  rw [← (covariancePhysicalReduction_measurePreserving Q).integral_comp hemb]
  simp only [covariancePhysicalLift_reduce]
  exact (integral_map (measurable_project (r₀ := r₀) Q.ellipticity_parameter).aemeasurable
    hF.aestronglyMeasurable).symm

/-- The literal physical lift preserves all coefficient-law Lp bounds. -/
theorem covariancePhysicalLift_memLp {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (F : Coefficient d (AKMUpperEllipticity L) → ℝ)
    (hF : Measurable F) (e : ENNReal) (hLp : MemLp F e (actualCoefficientLaw Q)) :
    MemLp (covariancePhysicalLift Q F) e (reducedLaw Q) := by
  have hlift := covariancePhysicalLift_measurable Q F hF
  have hr := covariancePhysicalReduction_measurePreserving Q
  rw [← hr.map_eq]
  apply (memLp_map_measure_iff hlift.aestronglyMeasurable hr.measurable.aemeasurable).2
  have hp := hLp.comp_of_map (measurable_project (r₀ := r₀) Q.ellipticity_parameter).aemeasurable
  simpa only [Function.comp_def, covariancePhysicalLift_reduce] using hp

/-- Joint source observables lift through the actual physical reconstruction. -/
theorem covariancePhysicalLift_joint_measurable {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (F : Vec d × Coefficient d (AKMUpperEllipticity L) → ℝ) (hF : Measurable F) :
    Measurable (fun p : Vec d × FieldPair d => covariancePhysicalLift Q
      (fun a => F (p.1, a)) p.2) := by
  classical
  let S : Set (Vec d × FieldPair d) :=
    {p | p.2 ∈ ReductionImageV3.physicalReducedRange L}
  have hS : MeasurableSet S :=
    (ReductionImageV3.measurableSet_physicalReducedRange L).preimage measurable_snd
  have hi : Measurable (fun p : S =>
      (⟨p.1.2, p.2⟩ : ReductionImageV3.ReducedPhysicalField d L)) :=
    (measurable_snd.comp measurable_subtype_coe).subtype_mk
  have hc := (measurable_project (r₀ := r₀) Q.ellipticity_parameter).comp
    ((ReductionImageV3.physicalReduceHomeomorph (d := d) (L := L)).symm.continuous.measurable.comp hi)
  exact Measurable.dite (hF.comp
    ((measurable_fst.comp measurable_subtype_coe).prodMk hc)) measurable_const hS

/-- The literal physical matrix entry is exactly a lifted coefficient
polarization, including its full anisotropic second load and normalization. -/
theorem covarianceLocalizedEntry_eq_physicalLift
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (x : Vec d) (j k : Fin d) :
    covarianceLocalizedEntry d hd D s δ γ η β h Q r x j k =
      covariancePhysicalLift Q (fun a =>
        let A := ellipticityScale D.ellipticity • homogenizedCoefficient Q
        let J := covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q
        (ellipticityScale D.ellipticity)⁻¹ *
          (centeredLocalizedEnergy (actualCoefficientLaw Q) J a
            (D.dependenceRange⁻¹ • x) (r / D.dependenceRange)
            (unitVector j + unitVector k) (A.mulVec (unitVector j)) -
          centeredLocalizedEnergy (actualCoefficientLaw Q) J a
            (D.dependenceRange⁻¹ • x) (r / D.dependenceRange)
            (unitVector j - unitVector k) (A.mulVec (unitVector j))) / 2) := rfl

/-- Each literal physical polarized matrix entry is genuinely jointly
measurable in position and reduced environment. -/
theorem covarianceLocalizedEntry_joint_measurable
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (j k : Fin d) :
    Measurable (fun p : Vec d × FieldPair d =>
      covarianceLocalizedEntry d hd D s δ γ η β h Q r p.1 j k p.2) := by
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  let A := ellipticityScale D.ellipticity • homogenizedCoefficient Q
  have hp := covarianceCenteredLocalizedEnergy_joint_measurable
    d hd D s δ γ η β h Q (actualCoefficientLaw Q) (r / D.dependenceRange)
    (unitVector j + unitVector k) (A.mulVec (unitVector j))
  have hm := covarianceCenteredLocalizedEnergy_joint_measurable
    d hd D s δ γ η β h Q (actualCoefficientLaw Q) (r / D.dependenceRange)
    (unitVector j - unitVector k) (A.mulVec (unitVector j))
  have hg : Measurable (fun p : Vec d × Coefficient d (AKMUpperEllipticity D.ellipticity) =>
      (D.dependenceRange⁻¹ • p.1, p.2)) :=
    ((measurable_const_smul _).comp measurable_fst).prodMk measurable_snd
  exact covariancePhysicalLift_joint_measurable Q _
    (((hp.comp hg).sub (hm.comp hg)).const_mul (ellipticityScale D.ellipticity)⁻¹ |>.div_const 2)

/-- Every literal physical polarized coordinate has all finite-law Lp bounds. -/
theorem covarianceLocalizedEntry_memLp
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (e : ENNReal) (r : ℝ) (x : Vec d) (j k : Fin d) :
    MemLp (covarianceLocalizedEntry d hd D s δ γ η β h Q r x j k) e (reducedLaw Q) := by
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  let A := ellipticityScale D.ellipticity • homogenizedCoefficient Q
  have hp := covarianceCenteredLocalizedEnergy_memLp
    d hd D s δ γ η β h Q (actualCoefficientLaw Q) e
    (D.dependenceRange⁻¹ • x) (r / D.dependenceRange)
    (unitVector j + unitVector k) (A.mulVec (unitVector j))
  have hm := covarianceCenteredLocalizedEnergy_memLp
    d hd D s δ γ η β h Q (actualCoefficientLaw Q) e
    (D.dependenceRange⁻¹ • x) (r / D.dependenceRange)
    (unitVector j - unitVector k) (A.mulVec (unitVector j))
  rw [covarianceLocalizedEntry_eq_physicalLift]
  refine covariancePhysicalLift_memLp Q _ ?_ e ?_
  · have hpj := covarianceCenteredLocalizedEnergy_joint_measurable
      d hd D s δ γ η β h Q (actualCoefficientLaw Q) (r / D.dependenceRange)
      (unitVector j + unitVector k) (A.mulVec (unitVector j))
    have hmj := covarianceCenteredLocalizedEnergy_joint_measurable
      d hd D s δ γ η β h Q (actualCoefficientLaw Q) (r / D.dependenceRange)
      (unitVector j - unitVector k) (A.mulVec (unitVector j))
    exact (((hpj.sub hmj).comp (measurable_const.prodMk measurable_id)).const_mul
      (ellipticityScale D.ellipticity)⁻¹).div_const 2
  · simpa only [div_eq_mul_inv, Pi.sub_apply, A] using
      (((hp.sub hm).const_mul (ellipticityScale D.ellipticity)⁻¹).mul_const (2 : ℝ)⁻¹)

/-- Integrate a physical polarization only after its two coefficient
terms have been proved integrable. -/
theorem covariancePhysicalLift_polarization_integral {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (F G : Coefficient d (AKMUpperEllipticity L) → ℝ)
    (c : ℝ) (hF : Measurable F) (hG : Measurable G)
    (hiF : Integrable F (actualCoefficientLaw Q))
    (hiG : Integrable G (actualCoefficientLaw Q)) :
    (∫ ω, covariancePhysicalLift Q (fun a => c * (F a - G a) / 2) ω ∂reducedLaw Q) =
      c * ((∫ a, F a ∂actualCoefficientLaw Q) -
        ∫ a, G a ∂actualCoefficientLaw Q) / 2 := by
  have hFG : Measurable (fun a => c * (F a - G a) / 2) := by
    simpa only [Pi.sub_apply] using ((hF.sub hG).const_mul c |>.div_const 2)
  rw [covariancePhysicalLift_integral Q (fun a => c * (F a - G a) / 2) hFG]
  rw [integral_div, integral_const_mul, integral_sub hiF hiG]

/-- Literal source centering transfers to exact physical matrix centering. -/
theorem covarianceLocalizedEntry_integral_eq_zero
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (x : Vec d) (j k : Fin d) :
    (∫ ω, covarianceLocalizedEntry d hd D s δ γ η β h Q r x j k ω ∂reducedLaw Q) = 0 := by
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  let A := ellipticityScale D.ellipticity • homogenizedCoefficient Q
  let z := D.dependenceRange⁻¹ • x
  let ρ := r / D.dependenceRange
  let J := covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q
  have hmeas (p : Vec d) : Measurable (fun a =>
      centeredLocalizedEnergy (actualCoefficientLaw Q) J a z ρ p (A.mulVec (unitVector j))) := by
    have hm := covarianceCenteredLocalizedEnergy_joint_measurable d hd D s δ γ η β h Q
      (actualCoefficientLaw Q) ρ p (A.mulVec (unitVector j))
    have hmap : Measurable (fun a : Coefficient d (AKMUpperEllipticity D.ellipticity) =>
      (z, a)) := measurable_const.prodMk measurable_id
    have hv := hm.comp hmap
    simpa only [Function.comp_def] using hv
  have hi (p : Vec d) : Integrable (fun a =>
      centeredLocalizedEnergy (actualCoefficientLaw Q) J a z ρ p (A.mulVec (unitVector j)))
      (actualCoefficientLaw Q) := memLp_one_iff_integrable.mp
    (covarianceCenteredLocalizedEnergy_memLp d hd D s δ γ η β h Q
      (actualCoefficientLaw Q) 1 z ρ p (A.mulVec (unitVector j)))
  have hzero (p : Vec d) : (∫ a, centeredLocalizedEnergy (actualCoefficientLaw Q) J
      a z ρ p (A.mulVec (unitVector j)) ∂actualCoefficientLaw Q) = 0 :=
    covarianceCenteredLocalizedEnergy_integral_eq_zero d hd D s δ γ η β h Q
      (actualCoefficientLaw Q) z ρ p (A.mulVec (unitVector j))
  rw [covarianceLocalizedEntry_eq_physicalLift]
  change (∫ ω, covariancePhysicalLift Q (fun a => (ellipticityScale D.ellipticity)⁻¹ *
    (centeredLocalizedEnergy (actualCoefficientLaw Q) J a z ρ
      (unitVector j + unitVector k) (A.mulVec (unitVector j)) -
    centeredLocalizedEnergy (actualCoefficientLaw Q) J a z ρ
      (unitVector j - unitVector k) (A.mulVec (unitVector j))) / 2) ω ∂reducedLaw Q) = 0
  rw [covariancePhysicalLift_polarization_integral Q _ _ _
    (hmeas (unitVector j + unitVector k)) (hmeas (unitVector j - unitVector k))
    (hi (unitVector j + unitVector k)) (hi (unitVector j - unitVector k)), hzero, hzero]
  ring

/-- The actual coefficient law is invariant under every real translation.
This uses physical stationarity and the exact unit-range project map. -/
theorem covarianceActualCoefficientLaw_translation_invariant
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (z : Vec d) :
    Measure.map (translateCoefficient z) (actualCoefficientLaw Q) = actualCoefficientLaw Q := by
  change Measure.map (translateCoefficient z)
      (Measure.map (project (r₀ := r₀) Q.ellipticity_parameter)
        (ReductionImageV3.physicalReferenceLaw Q)) = _
  rw [Measure.map_map (measurable_translateCoefficient _)
    (measurable_project (r₀ := r₀) Q.ellipticity_parameter)]
  rw [show (translateCoefficient z ∘ project (r₀ := r₀) Q.ellipticity_parameter) =
      (project (r₀ := r₀) Q.ellipticity_parameter ∘ physicalTranslate (r₀ • z)) from by
        funext ω
        exact project_translation_covariant (r₀ := r₀) Q.ellipticity_parameter z ω]
  rw [← Measure.map_map (measurable_project (r₀ := r₀) Q.ellipticity_parameter)
    (measurable_physicalTranslate (r₀ • z)), physicalReferenceLaw_translation_invariant Q]
  rfl

/-- Actual source means are translation invariant for all real loads. -/
theorem covarianceSourceLocalizedEnergy_integral_translate
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (z y : Vec d) (r : ℝ) (p q : Vec d) :
    (∫ a, covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a (z + y) r p q
      ∂actualCoefficientLaw Q) =
    ∫ a, covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q
      ∂actualCoefficientLaw Q := by
  have hm := (covarianceSourceLocalizedEnergy_joint_measurable_real
    d hd D s δ γ η β h Q r p q).comp
      (measurable_const.prodMk measurable_id : Measurable
        (fun a : Coefficient d (AKMUpperEllipticity D.ellipticity) => (z, a)))
  have hi := integral_map (μ := actualCoefficientLaw Q)
    (measurable_translateCoefficient y).aemeasurable hm.aestronglyMeasurable
  rw [covarianceActualCoefficientLaw_translation_invariant Q y] at hi
  change (∫ a, covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q
    ∂actualCoefficientLaw Q) =
      ∫ a, covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q
        (translateCoefficient y a) z r p q ∂actualCoefficientLaw Q at hi
  rw [hi]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun a =>
    covarianceSourceLocalizedEnergy_translate d hd D s δ γ η β h Q a z y r p q))

/-- Literal centering preserves exact pointwise source stationarity. -/
theorem covarianceCenteredLocalizedEnergy_translate
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (a : Coefficient d (AKMUpperEllipticity D.ellipticity))
    (z y : Vec d) (r : ℝ) (p q : Vec d) :
    centeredLocalizedEnergy (actualCoefficientLaw Q)
      (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a (z + y) r p q =
    centeredLocalizedEnergy (actualCoefficientLaw Q)
      (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q)
      (translateCoefficient y a) z r p q := by
  unfold centeredLocalizedEnergy
  rw [covarianceSourceLocalizedEnergy_translate,
    covarianceSourceLocalizedEnergy_integral_translate]

/-- Coefficient covariance transfers through physical reconstruction on its
actual image, with the original physical-to-unit-range spatial scale. -/
theorem covariancePhysicalLift_reduce_translate {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (F G : Coefficient d (AKMUpperEllipticity L) → ℝ)
    (x y : Vec d) (hxy : r₀ • y = x)
    (hFG : ∀ a, F a = G (translateCoefficient y a))
    (ω : ReductionImageV3.PhysicalField d L) :
    covariancePhysicalLift Q F (reduce ω.1) =
      covariancePhysicalLift Q G (translate x (reduce ω.1)) := by
  rw [← reduce_translate]
  change covariancePhysicalLift Q F (reduce ω.1) =
    covariancePhysicalLift Q G (reduce (physicalTranslate x ω).1)
  rw [covariancePhysicalLift_reduce, covariancePhysicalLift_reduce, hFG,
    project_translation_covariant, hxy]

/-- Each literal physical matrix entry has the required translation covariance
under the ambient reduced law, without selecting a new representative. -/
theorem covarianceLocalizedEntry_translate
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (x : Vec d) (j k : Fin d) :
    (fun ω => covarianceLocalizedEntry d hd D s δ γ η β h Q r x j k ω) =ᵐ[reducedLaw Q]
      (fun ω => covarianceLocalizedEntry d hd D s δ γ η β h Q r 0 j k
        (translate x ω)) := by
  have hm (z : Vec d) : Measurable
      (covarianceLocalizedEntry d hd D s δ γ η β h Q r z j k) := by
    have hv := (covarianceLocalizedEntry_joint_measurable d hd D s δ γ η β h Q r j k).comp
      (measurable_const.prodMk measurable_id : Measurable (fun ω : FieldPair d => (z, ω)))
    simpa only [Function.comp_def] using hv
  have hr := covariancePhysicalReduction_measurePreserving Q
  rw [← hr.map_eq]
  apply (ae_map_iff hr.measurable.aemeasurable
    (measurableSet_eq_fun (hm x) ((hm 0).comp (Probability.measurable_translate x)))).2
  apply Filter.Eventually.of_forall
  intro ω
  rw [covarianceLocalizedEntry_eq_physicalLift, covarianceLocalizedEntry_eq_physicalLift]
  apply covariancePhysicalLift_reduce_translate Q _ _ x (D.dependenceRange⁻¹ • x)
  · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one
      D.one_le_dependenceRange)), one_smul]
  · intro a
    dsimp only
    rw [show (D.dependenceRange⁻¹ : ℝ) • (0 : Vec d) = 0 from smul_zero _]
    rw [← zero_add (D.dependenceRange⁻¹ • x),
      covarianceCenteredLocalizedEnergy_translate,
      covarianceCenteredLocalizedEnergy_translate]
    simp only [zero_add]

/-- A coefficient observable whose physical pullback is local admits a local
ambient reduced representative. Factorization uses the real target only. -/
theorem covariancePhysicalLift_exists_local {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (F : Coefficient d (AKMUpperEllipticity L) → ℝ) (hF : Measurable F)
    (U : Set (Vec d))
    (hlocal : @Measurable (ReductionImageV3.PhysicalField d L) ℝ
      ((EinsteinRelation.localSigma U).comap Subtype.val) inferInstance
      (fun ω => F (project (r₀ := r₀) Q.ellipticity_parameter ω))) :
    ∃ G : FieldPair d → ℝ,
      @Measurable _ _ (EinsteinRelation.localSigma U) inferInstance G ∧
      G =ᵐ[reducedLaw Q] covariancePhysicalLift Q F := by
  have he : (EinsteinRelation.localSigma U).comap
      (fun ω : ReductionImageV3.PhysicalField d L => reduce ω.1) =
      (EinsteinRelation.localSigma U).comap
        (Subtype.val : ReductionImageV3.PhysicalField d L → FieldPair d) := by
    change (EinsteinRelation.localSigma U).comap (reduce ∘ Subtype.val) = _
    rw [← MeasurableSpace.comap_comp, Probability.localSigma_reduce_comap_eq]
  have hm := hlocal.mono he.symm.le le_rfl
  obtain ⟨G, hG, hFG⟩ := hm.exists_eq_measurable_comp (mY := EinsteinRelation.localSigma U)
  refine ⟨G, hG, ?_⟩
  have hr := covariancePhysicalReduction_measurePreserving Q
  rw [← hr.map_eq]
  apply (ae_map_iff hr.measurable.aemeasurable (measurableSet_eq_fun
    (hG.mono (Probability.localSigma_le_borel U) le_rfl)
    (covariancePhysicalLift_measurable Q F hF))).2
  apply Filter.Eventually.of_forall
  intro ω
  rw [covariancePhysicalLift_reduce]
  exact (congrFun hFG ω).symm

/-- The literal physical polarization admits a representative on exactly the
containing ball in the joint-localization statement. -/
theorem covarianceLocalizedEntry_exists_local
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (hr : 2 * D.dependenceRange ≤ r) (x : Vec d) (j k : Fin d) :
    ∃ G : FieldPair d → ℝ,
      @Measurable _ _ (EinsteinRelation.localSigma
        (ball x (covarianceLocalizationRadius D δ r))) inferInstance G ∧
      G =ᵐ[reducedLaw Q] covarianceLocalizedEntry d hd D s δ γ η β h Q r x j k := by
  have hr₀ : 0 < D.dependenceRange := lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange
  have hρ : 2 ≤ r / D.dependenceRange := (le_div_iff₀ hr₀).2 hr
  let z := D.dependenceRange⁻¹ • x
  let ρ := r / D.dependenceRange
  let A := ellipticityScale D.ellipticity • homogenizedCoefficient Q
  let J := covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q
  let F : Coefficient d (AKMUpperEllipticity D.ellipticity) → ℝ := fun a =>
    (ellipticityScale D.ellipticity)⁻¹ *
      (centeredLocalizedEnergy (actualCoefficientLaw Q) J a z ρ
        (unitVector j + unitVector k) (A.mulVec (unitVector j)) -
       centeredLocalizedEnergy (actualCoefficientLaw Q) J a z ρ
        (unitVector j - unitVector k) (A.mulVec (unitVector j))) / 2
  have hcenter (p : Vec d) : @Measurable _ ℝ
      (EinsteinRelation.Environment.AKMTestIntegralSupport.localSigma (ball z (localizationOuterRadius δ ρ))) inferInstance
      (fun a => centeredLocalizedEnergy (actualCoefficientLaw Q) J a z ρ p
        (A.mulVec (unitVector j))) := by
    exact (covarianceSourceLocalizedEnergy_local_measurable_real
      d hd D s δ γ η β h Q z ρ hρ p (A.mulVec (unitVector j))).sub measurable_const
  have hF : @Measurable _ ℝ (EinsteinRelation.Environment.AKMTestIntegralSupport.localSigma (ball z (localizationOuterRadius δ ρ)))
      inferInstance F := ((hcenter (unitVector j + unitVector k)).sub
        (hcenter (unitVector j - unitVector k))).const_mul _ |>.div_const 2
  have hsub : (fun u : Vec d => D.dependenceRange • u) ''
      ball z (localizationOuterRadius δ ρ) ⊆ ball x (covarianceLocalizationRadius D δ r) := by
    rintro _ ⟨u, hu, rfl⟩
    have hx : D.dependenceRange • z = x := by
      dsimp only [z]
      rw [smul_smul, mul_inv_cancel₀ hr₀.ne', one_smul]
    change euclideanNorm (D.dependenceRange • u - x) < _
    rw [← hx, ← smul_sub, TimeChange.euclideanNorm_smul, abs_of_pos hr₀]
    exact mul_lt_mul_of_pos_left hu hr₀
  have hp := project_localSigma_comap_le (r₀ := D.dependenceRange)
    Q.ellipticity_parameter (ball z (localizationOuterRadius δ ρ))
  change (EinsteinRelation.Environment.AKMTestIntegralSupport.localSigma (ball z (localizationOuterRadius δ ρ))).comap
      (project (r₀ := D.dependenceRange) Q.ellipticity_parameter) ≤
    (EinsteinRelation.localSigma ((fun u : Vec d => D.dependenceRange • u) ''
      ball z (localizationOuterRadius δ ρ))).comap Subtype.val at hp
  have hlocal := (hF.comp (comap_measurable _)).mono
    (hp.trans (MeasurableSpace.comap_mono (Probability.localSigma_mono hsub))) le_rfl
  obtain ⟨G, hG, he⟩ := covariancePhysicalLift_exists_local Q F
    (hF.mono (coefficientLocalSigma_le _) le_rfl)
    (ball x (covarianceLocalizationRadius D δ r)) hlocal
  refine ⟨G, hG, ?_⟩
  change G =ᵐ[reducedLaw Q] covariancePhysicalLift Q F
  exact he

/-- The exact Euclidean source ball is Borel in the coordinate carrier. -/
theorem covarianceSourceBall_measurable {d : ℕ} (x : Vec d) (R : ℝ) :
    MeasurableSet (ball x R) := by
  change MeasurableSet {z : Vec d | euclideanNorm (z - x) < R}
  apply measurableSet_lt _ measurable_const
  unfold euclideanNorm euclideanSq dot
  fun_prop

/-- The literal isotropic truncated clock integral, with no mass renormalization. -/
noncomputable def covarianceLocalizedClock {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (r R : ℝ) (x : Vec d) (ω : FieldPair d) : ℝ :=
  ∫ z in ball 0 R, heatKernel 0 r z * centeredClockField Q (x - z) ω

/-- The literal truncated clock is jointly measurable in position and environment. -/
theorem covarianceLocalizedClock_joint_measurable {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (r R : ℝ) :
    Measurable (fun p : Vec d × FieldPair d => covarianceLocalizedClock Q r R p.1 p.2) := by
  have hk : Measurable (heatKernel (0 : Vec d) r) :=
    ((Correctors.continuous_euclideanHeatKernel _).comp
      (continuous_id.sub continuous_const)).measurable
  have hm : Measurable (fun p : (Vec d × FieldPair d) × Vec d =>
      heatKernel 0 r p.2 * centeredClockField Q (p.1.1 - p.2) p.1.2) :=
    (hk.comp measurable_snd).mul ((continuous_centeredClockField Q).measurable.comp
      ((measurable_fst.fst.sub measurable_snd).prodMk measurable_fst.snd))
  exact hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (ball 0 R)) |>.measurable

/-- Clock stationarity is pointwise for the literal truncated integral. -/
theorem covarianceLocalizedClock_translate {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (r R : ℝ) (x : Vec d) (ω : FieldPair d) :
    covarianceLocalizedClock Q r R x ω =
      covarianceLocalizedClock Q r R 0 (translate x ω) := by
  unfold covarianceLocalizedClock
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change heatKernel 0 r z * (_ - _) = heatKernel 0 r z * (_ - _)
  congr 2
  change ω.2 (x - z) = ω.2 (x + (0 - z))
  rw [zero_sub, sub_eq_add_neg]

/-- The literal truncated clock is measurable from the exact containing ball. -/
theorem covarianceLocalizedClock_local_measurable {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (r R : ℝ) (x : Vec d) :
    @Measurable _ _ (EinsteinRelation.localSigma (ball x R)) inferInstance
      (covarianceLocalizedClock Q r R x) := by
  letI : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma (ball x R)
  letI : MeasureSpace (ball (0 : Vec d) R) := Measure.Subtype.measureSpace
  have hmap : SigmaFinite ((volume : Measure (ball (0 : Vec d) R)).map Subtype.val) := by
    rw [(covarianceSourceBall_measurable (0 : Vec d) R).map_coe_volume]
    infer_instance
  letI : SigmaFinite (volume : Measure (ball (0 : Vec d) R)) :=
    SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable hmap
  let f : ball (0 : Vec d) R → FieldPair d → ℝ := fun z ω =>
    heatKernel 0 r z.1 * centeredClockField Q (x - z.1) ω
  have hc (ω : FieldPair d) : Continuous (fun z => f z ω) :=
    (((Correctors.continuous_euclideanHeatKernel _).comp
      (continuous_subtype_val.sub continuous_const))).mul
        ((continuous_centeredClockField Q).comp
          ((continuous_const.sub continuous_subtype_val).prodMk continuous_const))
  have hm (z : ball (0 : Vec d) R) : Measurable (f z) := by
    apply measurable_const.mul
    apply measurable_centeredClockField_local Q
    change euclideanNorm ((x - z.1) - x) < R
    rw [show (x - z.1) - x = -z.1 by abel]
    have hn := TimeChange.euclideanNorm_smul (-1) z.1
    simp only [neg_one_smul, abs_neg, abs_one, one_mul] at hn
    rw [hn]
    simpa only [ball, Set.mem_setOf_eq, sub_zero] using z.2
  have hj := measurable_uncurry_of_continuous_of_measurable hc hm
  have hi := (hj.stronglyMeasurable.integral_prod_left' (μ := (volume : Measure (ball (0 : Vec d) R)))).measurable
  convert hi using 1
  funext ω
  exact (integral_subtype (covarianceSourceBall_measurable (0 : Vec d) R)
    (fun z => heatKernel 0 r z * centeredClockField Q (x - z) ω)).symm


/-- A simultaneous pointwise clock bound gives spatial Gaussian integrability. -/
theorem covarianceClock_heat_integrable {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {r : ℝ} (hr : 0 < r)
    (x : Vec d) (ω : FieldPair d) (B : ℝ)
    (hω : ∀ y, |centeredClockField Q y ω| ≤ B) :
    Integrable (fun z => heatKernel 0 r z * centeredClockField Q (x - z) ω) := by
  have hk : Integrable (heatKernel (0 : Vec d) r) := by
    exact (Correctors.integrable_euclideanHeatKernel (d := d)
      (sq_pos_of_pos hr)).comp_sub_right 0
  have hm : Continuous (fun z : Vec d =>
      heatKernel 0 r z * centeredClockField Q (x - z) ω) :=
    ((Correctors.continuous_euclideanHeatKernel _).comp
      (continuous_id.sub continuous_const)).mul
        ((continuous_centeredClockField Q).comp
          ((continuous_const.sub continuous_id).prodMk continuous_const))
  apply (hk.mul_const B).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    have hk0 : 0 ≤ heatKernel (0 : Vec d) r z :=
      Correctors.euclideanHeatKernel_nonneg (sq_nonneg r) _
    rw [norm_mul, Real.norm_of_nonneg hk0, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hω (x - z)) hk0)

/-- Truncation does not increase the simultaneous structural clock bound. -/
theorem covarianceLocalizedClock_abs_le {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {r : ℝ} (hr : 0 < r)
    (R : ℝ) (x : Vec d) (ω : FieldPair d) {B : ℝ} (hB : 0 ≤ B)
    (hω : ∀ y, |centeredClockField Q y ω| ≤ B) :
    |covarianceLocalizedClock Q r R x ω| ≤ B := by
  have hk : Integrable (heatKernel (0 : Vec d) r) := by
    exact (Correctors.integrable_euclideanHeatKernel (d := d)
      (sq_pos_of_pos hr)).comp_sub_right 0
  have hk0 (z : Vec d) : 0 ≤ heatKernel (0 : Vec d) r z :=
    Correctors.euclideanHeatKernel_nonneg (sq_nonneg r) _
  have hi : (∫ z : Vec d, heatKernel 0 r z) = 1 := by
    simpa only [heatKernel, sub_zero] using
      Correctors.integral_euclideanHeatKernel (d := d) (sq_pos_of_pos hr)
  calc
    |covarianceLocalizedClock Q r R x ω| ≤
        ∫ z in ball 0 R, heatKernel 0 r z * B := by
      change ‖∫ z in ball 0 R, heatKernel 0 r z * centeredClockField Q (x - z) ω‖ ≤ _
      apply norm_integral_le_of_norm_le (hk.mul_const B).integrableOn
      exact Filter.Eventually.of_forall (fun z => by
        rw [norm_mul, Real.norm_of_nonneg (hk0 z), Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hω (x - z)) (hk0 z))
    _ ≤ ∫ z : Vec d, heatKernel 0 r z * B :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall (fun z => mul_nonneg (hk0 z) hB)) (hk.mul_const B)
    _ = B := by rw [integral_mul_const, hi, one_mul]

/-- One full-measure set bounds every truncated-clock position. -/
theorem covarianceLocalizedClock_ae_forall_abs_le {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ x,
      |covarianceLocalizedClock Q r R x ω| ≤ 2 * sourceReducedBound L := by
  filter_upwards [ae_forall_abs_centeredClockField_le Q] with ω hω
  exact fun x => covarianceLocalizedClock_abs_le Q hr R x ω
    (mul_nonneg (by norm_num) (Clock.sourceReducedBound_pos Q.ellipticity_parameter).le) hω

/-- The literal truncated clock belongs to every finite-law Lp space. -/
theorem covarianceLocalizedClock_memLp {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (x : Vec d) (e : ENNReal) :
    MemLp (covarianceLocalizedClock Q r R x) e (reducedLaw Q) := by
  letI := reducedLaw_probability Q
  have hm := (covarianceLocalizedClock_joint_measurable Q r R).comp
    (measurable_const.prodMk measurable_id : Measurable (fun ω : FieldPair d => (x, ω)))
  apply MemLp.of_bound hm.aestronglyMeasurable (2 * sourceReducedBound L)
  filter_upwards [covarianceLocalizedClock_ae_forall_abs_le Q hr R] with ω hω
  simpa only [Real.norm_eq_abs, Function.comp_def] using hω x


/-- Gaussian-clock Fubini is justified by a product integrability witness. -/
theorem covarianceClock_heat_product_integrable {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {r : ℝ} (hr : 0 < r) (R : ℝ) (x : Vec d) :
    Integrable (fun p : Vec d × FieldPair d =>
      heatKernel 0 r p.1 * centeredClockField Q (x - p.1) p.2)
      ((volume.restrict (ball 0 R)).prod (reducedLaw Q)) := by
  letI := reducedLaw_probability Q
  have hk : Integrable (heatKernel (0 : Vec d) r) := by
    exact (Correctors.integrable_euclideanHeatKernel (d := d)
      (sq_pos_of_pos hr)).comp_sub_right 0
  have hm : Continuous (fun p : Vec d × FieldPair d =>
      heatKernel 0 r p.1 * centeredClockField Q (x - p.1) p.2) :=
    ((Correctors.continuous_euclideanHeatKernel _).comp
      (continuous_fst.sub continuous_const)).mul
        ((continuous_centeredClockField Q).comp
          ((continuous_const.sub continuous_fst).prodMk continuous_snd))
  have hdom := memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr
    ((hk.mul_const (2 * sourceReducedBound L)).integrableOn
      (s := ball (0 : Vec d) R))).comp_fst (reducedLaw Q))
  apply hdom.mono' hm.aestronglyMeasurable
  have hω := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict (ball (0 : Vec d) R)) (ν := reducedLaw Q)).ae
      (ae_forall_abs_centeredClockField_le Q)
  filter_upwards [hω] with p hp
  have hk0 : 0 ≤ heatKernel (0 : Vec d) r p.1 :=
    Correctors.euclideanHeatKernel_nonneg (sq_nonneg r) _
  change ‖heatKernel 0 r p.1 * centeredClockField Q (x - p.1) p.2‖ ≤
    heatKernel 0 r p.1 * (2 * sourceReducedBound L)
  rw [norm_mul, Real.norm_of_nonneg hk0, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hp (x - p.1)) hk0

/-- The literal, unnormalized truncated clock is centered. -/
theorem covarianceLocalizedClock_integral_eq_zero {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {r : ℝ} (hr : 0 < r) (R : ℝ) (x : Vec d) :
    (∫ ω, covarianceLocalizedClock Q r R x ω ∂reducedLaw Q) = 0 := by
  unfold covarianceLocalizedClock
  rw [← integral_integral_swap (covarianceClock_heat_product_integrable Q hr R x)]
  simp_rw [integral_const_mul, integral_centeredClockField, mul_zero]
  exact integral_zero _ _


/-- Joint measurability of the exact full matrix-clock vector. -/
theorem covarianceLocalizedField_joint_measurable
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (r : ℝ) :
    Measurable (fun p : Vec d × FieldPair d =>
      covarianceLocalizedField d hd D s δ γ η β h Q r p.1 p.2) := by
  apply Measurable.of_eval
  intro a
  rcases a with ⟨j, k⟩ | ⟨⟩
  · exact covarianceLocalizedEntry_joint_measurable d hd D s δ γ η β h Q r j k
  · exact covarianceLocalizedClock_joint_measurable Q r (covarianceLocalizationRadius D δ r)

/-- Every exact full-field coordinate is in L² and centered. -/
theorem covarianceLocalizedField_memLp_integral
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {r : ℝ} (hr : 0 < r) (x : Vec d) (a : JointObservationIndex d) :
    MemLp (fun ω => covarianceLocalizedField d hd D s δ γ η β h Q r x ω a)
      2 (reducedLaw Q) ∧
    (∫ ω, covarianceLocalizedField d hd D s δ γ η β h Q r x ω a ∂reducedLaw Q) = 0 := by
  rcases a with ⟨j, k⟩ | ⟨⟩
  · exact ⟨covarianceLocalizedEntry_memLp d hd D s δ γ η β h Q 2 r x j k,
      covarianceLocalizedEntry_integral_eq_zero d hd D s δ γ η β h Q r x j k⟩
  · exact ⟨covarianceLocalizedClock_memLp Q hr (covarianceLocalizationRadius D δ r) x 2,
      covarianceLocalizedClock_integral_eq_zero Q hr (covarianceLocalizationRadius D δ r) x⟩

/-- Finite-coordinate factorization gives the exact full-field local representative. -/
theorem covarianceLocalizedField_exists_local
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (hr : 2 * D.dependenceRange ≤ r) (x : Vec d) :
    ∃ localized : FieldPair d → JointObservationIndex d → ℝ,
      @Measurable _ _ (EinsteinRelation.localSigma
        (ball x (covarianceLocalizationRadius D δ r))) inferInstance localized ∧
      localized =ᵐ[reducedLaw Q] covarianceLocalizedField d hd D s δ γ η β h Q r x := by
  classical
  have he (i : Fin d × Fin d) :=
    covarianceLocalizedEntry_exists_local d hd D s δ γ η β h Q r hr x i.1 i.2
  choose G hG heG using he
  let localized : FieldPair d → JointObservationIndex d → ℝ := fun ω a =>
    match a with
    | .inl i => G i ω
    | .inr _ => covarianceLocalizedClock Q r (covarianceLocalizationRadius D δ r) x ω
  refine ⟨localized, ?_, ?_⟩
  · letI : MeasurableSpace (FieldPair d) :=
      EinsteinRelation.localSigma (ball x (covarianceLocalizationRadius D δ r))
    apply Measurable.of_eval
    intro a
    rcases a with i | ⟨⟩
    · exact hG i
    · exact covarianceLocalizedClock_local_measurable Q r (covarianceLocalizationRadius D δ r) x
  · filter_upwards [ae_all_iff.2 heG] with ω hω
    funext a
    rcases a with i | ⟨⟩
    · exact hω i
    · rfl

/-- Stationarity holds for the exact full vector on one full-measure set. -/
theorem covarianceLocalizedField_translate
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (x : Vec d) :
    (fun ω => covarianceLocalizedField d hd D s δ γ η β h Q r x ω) =ᵐ[reducedLaw Q]
      (fun ω => covarianceLocalizedField d hd D s δ γ η β h Q r 0 (translate x ω)) := by
  have he (i : Fin d × Fin d) :=
    covarianceLocalizedEntry_translate d hd D s δ γ η β h Q r x i.1 i.2
  filter_upwards [ae_all_iff.2 he] with ω hω
  funext a
  rcases a with i | ⟨⟩
  · exact hω i
  · exact covarianceLocalizedClock_translate Q r (covarianceLocalizationRadius D δ r) x ω


/-- The literal clock truncation error is bounded by the removed isotropic
Gaussian mass on a single full-measure set, uniformly in the spatial point. -/
theorem covarianceLocalizedClock_ae_truncation_error_le {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ x : Vec d,
      |(∫ z : Vec d, heatKernel 0 r z * centeredClockField Q (x - z) ω) -
        covarianceLocalizedClock Q r R x ω| ≤
          2 * sourceReducedBound L * ∫ z in (ball (0 : Vec d) R)ᶜ, heatKernel 0 r z := by
  have hk : Integrable (heatKernel (0 : Vec d) r) :=
    (Correctors.integrable_euclideanHeatKernel (sq_pos_of_pos hr)).comp_sub_right 0
  filter_upwards [ae_forall_abs_centeredClockField_le Q] with ω hω
  intro x
  have hi := covarianceClock_heat_integrable Q hr x ω (2 * sourceReducedBound L) hω
  have he : (∫ z : Vec d, heatKernel 0 r z * centeredClockField Q (x - z) ω) -
      covarianceLocalizedClock Q r R x ω =
      ∫ z in (ball (0 : Vec d) R)ᶜ, heatKernel 0 r z * centeredClockField Q (x - z) ω := by
    unfold covarianceLocalizedClock
    linarith [integral_add_compl (covarianceSourceBall_measurable (0 : Vec d) R) hi]
  rw [he]
  calc
    _ ≤ ∫ z in (ball (0 : Vec d) R)ᶜ, heatKernel 0 r z * (2 * sourceReducedBound L) := by
      change ‖∫ z in (ball (0 : Vec d) R)ᶜ,
        heatKernel 0 r z * centeredClockField Q (x - z) ω‖ ≤ _
      apply norm_integral_le_of_norm_le (hk.mul_const (2 * sourceReducedBound L)).integrableOn
      exact Filter.Eventually.of_forall (fun z => by
        have hk0 : 0 ≤ heatKernel (0 : Vec d) r z :=
          Correctors.euclideanHeatKernel_nonneg (sq_nonneg r) _
        rw [norm_mul, Real.norm_of_nonneg hk0, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hω (x - z)) hk0)
    _ = _ := by rw [integral_mul_const, mul_comm]


/-- Splitting the literal Euclidean kernel into a wider density and an
exponential factor preserves its isotropic covariance. -/
theorem covarianceEuclideanHeatKernel_split {d : ℕ} {t : ℝ} (ht : 0 < t) (z : Vec d) :
    Correctors.euclideanHeatKernel t z =
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-euclideanSq z / (8 * t)) *
        Correctors.euclideanHeatKernel (2 * t) z := by
  have hp : (4 * Real.pi * (2 * t)) ^ (-(d : ℝ) / 2) =
      (2 : ℝ) ^ (-(d : ℝ) / 2) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
    rw [show 4 * Real.pi * (2 * t) = 2 * (4 * Real.pi * t) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  have htwo : (2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-(d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num),
      show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  unfold Correctors.euclideanHeatKernel
  rw [hp, show -euclideanSq z / (4 * t) =
      -euclideanSq z / (8 * t) + -euclideanSq z / (4 * (2 * t)) by ring,
    Real.exp_add]
  calc
    _ = ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-(d : ℝ) / 2)) *
        ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
          (Real.exp (-euclideanSq z / (8 * t)) *
            Real.exp (-euclideanSq z / (4 * (2 * t))))) := by rw [htwo]; ring
    _ = _ := by ring

/-- The literal isotropic heat kernel has an exponential tail outside a
Euclidean ball. -/
theorem covarianceEuclideanHeatKernel_tail_le {d : ℕ} {t R : ℝ}
    (ht : 0 < t) (hR : 0 ≤ R) :
    (∫ z : Vec d in (ball (0 : Vec d) R)ᶜ, Correctors.euclideanHeatKernel t z) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(R ^ 2 / (8 * t))) := by
  let C := (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(R ^ 2 / (8 * t)))
  have hi := (Correctors.integrable_euclideanHeatKernel (d := d)
    (show 0 < 2 * t by positivity)).const_mul C
  calc
    _ ≤ ∫ z in (ball (0 : Vec d) R)ᶜ, C * Correctors.euclideanHeatKernel (2 * t) z := by
      apply setIntegral_mono_on (Correctors.integrable_euclideanHeatKernel ht).integrableOn
        hi.integrableOn (covarianceSourceBall_measurable (0 : Vec d) R).compl
      intro z hz
      have hzR : R ≤ euclideanNorm z := by
        simpa only [Set.mem_compl_iff, ball, Set.mem_setOf_eq, sub_zero, not_lt] using hz
      have hsq : 0 ≤ euclideanSq z := by
        unfold euclideanSq
        exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (z j))
      have hRz : R ^ 2 ≤ euclideanSq z := by
        simpa only [euclideanNorm, Real.sq_sqrt hsq] using pow_le_pow_left₀ hR hzR 2
      rw [covarianceEuclideanHeatKernel_split ht z]
      apply mul_le_mul_of_nonneg_right _
        (Correctors.euclideanHeatKernel_nonneg (by positivity) _)
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2))
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using
        (neg_le_neg (div_le_div_of_nonneg_right hRz (by positivity : 0 ≤ 8 * t)))
    _ ≤ ∫ z : Vec d, C * Correctors.euclideanHeatKernel (2 * t) z :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall (fun z =>
        mul_nonneg (by dsimp [C]; positivity)
          (Correctors.euclideanHeatKernel_nonneg (by positivity) z)))
    _ = _ := by
      rw [integral_const_mul, Correctors.integral_euclideanHeatKernel (by positivity), mul_one]

/-- Exponential decay at any positive power dominates each fixed inverse power. -/
theorem covarianceGaussian_exp_inversePower_le {K δ : ℝ} (hK : 0 < K)
    (hδ : 0 < δ) (p : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      Real.exp (-(r ^ (2 * δ) / (4 * K))) ≤ C * r ^ (-p) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (p / (2 * δ))
  have hnp : p ≤ 2 * δ * n := by
    have h := (div_le_iff₀ (show 0 < 2 * δ by positivity)).mp hn
    nlinarith
  refine ⟨(n.factorial : ℝ) * (4 * K) ^ n, by positivity, ?_⟩
  intro r hr
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hx : 0 < r ^ (2 * δ) / (4 * K) := by positivity
  have hfact : 0 < (n.factorial : ℝ) := by positivity
  have h := one_div_le_one_div_of_le (div_pos (pow_pos hx n) hfact)
    (Real.pow_div_factorial_le_exp _ hx.le n)
  have he : (1 : ℝ) / Real.exp (r ^ (2 * δ) / (4 * K)) =
      Real.exp (-(r ^ (2 * δ) / (4 * K))) := by rw [one_div, Real.exp_neg]
  rw [he] at h
  have hratio : (1 : ℝ) / ((r ^ (2 * δ) / (4 * K)) ^ n / n.factorial) =
      (n.factorial : ℝ) * (4 * K) ^ n * r ^ (-(2 * δ * n)) := by
    rw [one_div_div, div_pow, div_div_eq_mul_div,
      ← Real.rpow_natCast (r ^ (2 * δ)) n, ← Real.rpow_mul hr0.le,
      Real.rpow_neg hr0.le]
    ring
  rw [hratio] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hr (by linarith : -(2 * δ * n) ≤ -p)) (by positivity))

/-- The exact physical containing radius has the same Gaussian tail ratio as
the unit-range radius, with no change of kernel. -/
theorem covarianceLocalizationRadius_ratio {d : ℕ} (D : StructuralData d)
    (δ : ℝ) {r : ℝ} (hr : 0 < r) :
    (covarianceLocalizationRadius D δ r) ^ 2 / (8 * r ^ 2) =
      (r / D.dependenceRange) ^ (2 * δ) / 8 := by
  have hr₀ : 0 < D.dependenceRange := lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange
  have hρ : 0 < r / D.dependenceRange := div_pos hr hr₀
  have hpow : ((r / D.dependenceRange) ^ (1 + δ)) ^ 2 =
      (r / D.dependenceRange) ^ 2 * (r / D.dependenceRange) ^ (2 * δ) := by
    rw [← Real.rpow_natCast ((r / D.dependenceRange) ^ (1 + δ)) 2,
      ← Real.rpow_mul hρ.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (1 + δ) * (2 : ℝ) = 2 + 2 * δ by ring, Real.rpow_add hρ, Real.rpow_two]
  unfold covarianceLocalizationRadius
  rw [mul_pow, hpow, div_pow]
  field_simp

/-- Every fixed inverse-power bound for the removed literal isotropic mass
has a constant fixed before the environment law. -/
theorem covarianceHeatKernel_physical_tail_inversePower_le {d : ℕ}
    (D : StructuralData d) {δ : ℝ} (hδ : 0 < δ) (p : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 2 * D.dependenceRange ≤ r →
      (∫ z : Vec d in (ball 0 (covarianceLocalizationRadius D δ r))ᶜ,
        heatKernel 0 r z) ≤ C * r ^ (-p) := by
  have hr₀ : 0 < D.dependenceRange := lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange
  obtain ⟨C, hC, hb⟩ := covarianceGaussian_exp_inversePower_le (K := 2) (by norm_num) hδ p
  refine ⟨(2 : ℝ) ^ ((d : ℝ) / 2) * C * D.dependenceRange ^ p, by positivity, ?_⟩
  intro r hr
  have hrpos : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) hr₀) hr
  have hρ : 1 ≤ r / D.dependenceRange := by
    apply (le_div_iff₀ hr₀).2
    linarith
  have htail := covarianceEuclideanHeatKernel_tail_le (d := d) (sq_pos_of_pos hrpos)
    (show 0 ≤ covarianceLocalizationRadius D δ r by
      unfold covarianceLocalizationRadius
      positivity)
  have he : (fun z : Vec d => heatKernel 0 r z) = Correctors.euclideanHeatKernel (r ^ 2) := by
    funext z
    simp only [heatKernel, sub_zero]
  rw [← he, covarianceLocalizationRadius_ratio D δ hrpos] at htail
  have hp : (r / D.dependenceRange) ^ (-p) = D.dependenceRange ^ p * r ^ (-p) := by
    rw [Real.div_rpow hrpos.le hr₀.le, Real.rpow_neg hr₀.le]
    simp only [div_inv_eq_mul, mul_comm]
  apply htail.trans
  have hb' := hb (r / D.dependenceRange) hρ
  norm_num only [Nat.cast_ofNat, mul_one] at hb'
  rw [hp] at hb'
  convert mul_le_mul_of_nonneg_left hb'
    (show 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) by positivity) using 1 <;> ring

/-- The exact clock coordinate satisfies every fixed inverse-power truncation
bound, with constants before the law and scale. -/
theorem covarianceLocalizedClock_physical_tail_bound
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) (p : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ r : ℝ, 2 * D.dependenceRange ≤ r → ∀ x : Vec d,
      ∀ᵐ ω ∂reducedLaw Q,
        |(∫ z : Vec d, heatKernel 0 r z * centeredClockField Q (x - z) ω) -
          covarianceLocalizedField d hd D s δ γ η β h Q r x ω (.inr ())| ≤ C * r ^ (-p) := by
  obtain ⟨C, hC, hb⟩ := covarianceHeatKernel_physical_tail_inversePower_le D h.2.2.2.1 p
  have hK := Clock.sourceReducedBound_pos (le_trans (by norm_num) D.one_le_ellipticity)
  refine ⟨2 * sourceReducedBound D.ellipticity * C, by positivity, ?_⟩
  intro Q r hr x
  have hrpos : 0 < r := lt_of_lt_of_le
    (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange)) hr
  filter_upwards [covarianceLocalizedClock_ae_truncation_error_le Q hrpos
    (covarianceLocalizationRadius D δ r)] with ω hω
  exact (hω x).trans (by
    convert mul_le_mul_of_nonneg_left (hb r hr)
      (show 0 ≤ 2 * sourceReducedBound D.ellipticity by positivity) using 1 <;> ring)

/-- Each whole-space variational value has the deterministic Euclidean load
bound, including the totalized nonintegrable branch. -/
theorem covarianceGaussianEnergyValue_le {d : ℕ} {K : ℝ} (hK : 0 < K)
    {a : Coefficient d K} {z : Vec d} {r : ℝ} (hr : 0 < r)
    (p q : Vec d) (w : SubquadraticHarmonic a) :
    (∫ x, heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
        dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))) ≤
      (K * euclideanNorm p + euclideanNorm q) ^ 2 / 2 := by
  let B := (K * euclideanNorm p + euclideanNorm q) ^ 2 / 2
  have hB : 0 ≤ B := div_nonneg (sq_nonneg _) (by norm_num)
  have hk : Integrable (heatKernel z r) :=
    (Correctors.integrable_euclideanHeatKernel (sq_pos_of_pos hr)).comp_sub_right z
  have hk0 (x : Vec d) : 0 ≤ heatKernel z r x :=
    Correctors.euclideanHeatKernel_nonneg (sq_nonneg r) _
  have hk1 : ∫ x, heatKernel z r x = 1 := by
    unfold heatKernel
    rw [integral_sub_right_eq_self, Correctors.integral_euclideanHeatKernel (sq_pos_of_pos hr)]
  by_cases hi : Integrable (fun x => heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
        dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x)))
  · calc
      _ ≤ ∫ x, heatKernel z r x * B :=
        integral_mono hi (hk.mul_const B) (fun x =>
          mul_le_mul_of_nonneg_left (covarianceEnergyDensity_le hK a x p q _) (hk0 x))
      _ = B := by rw [integral_mul_const, hk1, one_mul]
  · rw [integral_undef hi]
    exact hB

/-- The actual Gaussian variational supremum is bounded for arbitrary real
loads; the conditional supremum is used only after boundedness is proved. -/
theorem covarianceGaussianEnergy_bddAbove_le {d : ℕ} {K : ℝ} (hK : 0 < K)
    (a : Coefficient d K) (z : Vec d) {r : ℝ} (hr : 0 < r) (p q : Vec d) :
    BddAbove {e : ℝ | ∃ w : SubquadraticHarmonic a,
      e = ∫ x, heatKernel z r x *
        (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
          dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))} ∧
    gaussianEnergyJ1 a z r p q ≤ (K * euclideanNorm p + euclideanNorm q) ^ 2 / 2 := by
  let S := {e : ℝ | ∃ w : SubquadraticHarmonic a,
    e = ∫ x, heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
        dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))}
  have hb : ∀ e ∈ S, e ≤ (K * euclideanNorm p + euclideanNorm q) ^ 2 / 2 := by
    rintro e ⟨w, rfl⟩
    exact covarianceGaussianEnergyValue_le hK hr p q w
  refine ⟨⟨_, hb⟩, ?_⟩
  change sSup S ≤ _
  by_cases hs : S.Nonempty
  · exact csSup_le hs hb
  · rw [Set.not_nonempty_iff_eq_empty.mp hs, Real.sSup_empty]
    positivity

/-- The zero function belongs to the genuine whole-space source harmonic class. -/
def covarianceZeroSubquadraticHarmonic {d : ℕ} {K : ℝ} (a : Coefficient d K) :
    SubquadraticHarmonic a where
  potential := fun _ => 0
  grad := fun _ => 0
  weak_gradient := by
    intro j
    exact ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, by intro φ hφ; simp⟩
  local_energy := by
    intro R hR
    exact ⟨MemLp.zero, by simpa [euclideanNorm, euclideanSq, dot] using
      (MemLp.zero : MemLp (fun _ : Vec d => (0 : ℝ)) 2 (volume.restrict (ball 0 R)))⟩
  harmonic := by simpa using hasWeakDivergence_zero (Set.univ : Set (Vec d))
  growth := by simp

/-- An actual whole-space Gaussian variational value. -/
noncomputable def covarianceGaussianEnergyValue {d : ℕ} {K : ℝ} {a : Coefficient d K}
    (z : Vec d) (r : ℝ) (p q : Vec d) (w : SubquadraticHarmonic a) : ℝ :=
  ∫ x, heatKernel z r x *
    (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
      dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))

/-- The full Gaussian energy is the supremum over the actual harmonic class. -/
theorem covarianceGaussianEnergy_eq_sSup_range {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (z : Vec d) (r : ℝ) (p q : Vec d) :
    gaussianEnergyJ1 a z r p q = sSup (Set.range (covarianceGaussianEnergyValue (a := a) z r p q)) := by
  unfold gaussianEnergyJ1 energyJ1 covarianceGaussianEnergyValue
  congr 1
  ext e
  simp only [Set.mem_setOf_eq, Set.mem_range, eq_comm]

/-- The zero competitor proves nonnegativity without presuming that a total
conditional supremum is attained. -/
theorem covarianceGaussianEnergy_nonneg_le {d : ℕ} {K : ℝ} (hK : 0 < K)
    (a : Coefficient d K) (z : Vec d) {r : ℝ} (hr : 0 < r) (p q : Vec d) :
    0 ≤ gaussianEnergyJ1 a z r p q ∧
      gaussianEnergyJ1 a z r p q ≤ (K * euclideanNorm p + euclideanNorm q) ^ 2 / 2 := by
  refine ⟨?_, (covarianceGaussianEnergy_bddAbove_le hK a z hr p q).2⟩
  apply le_csSup (covarianceGaussianEnergy_bddAbove_le hK a z hr p q).1
  refine ⟨covarianceZeroSubquadraticHarmonic a, ?_⟩
  simp [covarianceZeroSubquadraticHarmonic, dot]

/-- Scaling a genuine A₁ member and both loads scales its variational value
quadratically, with the same totalized integral. -/
theorem covarianceGaussianEnergyValue_smul {d : ℕ} {K : ℝ}
    {a : Coefficient d K} (z : Vec d) (r b : ℝ) (p q : Vec d)
    (w : SubquadraticHarmonic a) :
    covarianceGaussianEnergyValue z r (b • p) (b • q)
      (EinsteinFull.smulSubquadraticHarmonic b w) =
        b ^ 2 * covarianceGaussianEnergyValue z r p q w := by
  unfold covarianceGaussianEnergyValue
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only [EinsteinFull.smulSubquadraticHarmonic]
    rw [Matrix.mulVec_smul]
    change heatKernel z r x *
      (-(1 / 2 : ℝ) * dotProduct (b • w.grad x) (b • (a x).mulVec (w.grad x)) -
        dotProduct (b • p) (b • (a x).mulVec (w.grad x)) +
          dotProduct (b • q) (b • w.grad x)) = _
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    change heatKernel z r x *
      (-(1 / 2 : ℝ) * (b * (b * dot (w.grad x) ((a x).mulVec (w.grad x)))) -
        b * (b * dot p ((a x).mulVec (w.grad x))) + b * (b * dot q (w.grad x))) = _
    ring)

/-- Full real-load homogeneity uses inverse rescaling of the entire A₁ class,
retaining its weak gradient, harmonicity and growth conditions. -/
theorem covarianceGaussianEnergy_smul {d : ℕ} {K : ℝ} (hK : 0 < K)
    (a : Coefficient d K) (z : Vec d) {r : ℝ} (hr : 0 < r)
    (b : ℝ) (p q : Vec d) :
    gaussianEnergyJ1 a z r (b • p) (b • q) = b ^ 2 * gaussianEnergyJ1 a z r p q := by
  by_cases hb : b = 0
  · subst b
    have hh := covarianceGaussianEnergy_nonneg_le hK a z hr (0 : Vec d) 0
    simpa only [zero_smul, zero_pow (by decide : 2 ≠ 0), zero_mul] using
      le_antisymm (by simpa [euclideanNorm, euclideanSq, dot] using hh.2) hh.1
  have hs : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hn (p q : Vec d) : (Set.range (covarianceGaussianEnergyValue (a := a) z r p q)).Nonempty :=
    ⟨_, Set.mem_range_self (covarianceZeroSubquadraticHarmonic a)⟩
  have hbd (p q : Vec d) : BddAbove (Set.range (covarianceGaussianEnergyValue (a := a) z r p q)) :=
    ⟨_, by rintro _ ⟨w, rfl⟩; exact covarianceGaussianEnergyValue_le hK hr p q w⟩
  rw [covarianceGaussianEnergy_eq_sSup_range, covarianceGaussianEnergy_eq_sSup_range]
  apply le_antisymm
  · apply csSup_le (hn _ _)
    rintro _ ⟨w, rfl⟩
    have hc := covarianceGaussianEnergyValue_smul z r b p q
      (EinsteinFull.smulSubquadraticHarmonic b⁻¹ w)
    have he : covarianceGaussianEnergyValue z r (b • p) (b • q)
        (EinsteinFull.smulSubquadraticHarmonic b
          (EinsteinFull.smulSubquadraticHarmonic b⁻¹ w)) =
        covarianceGaussianEnergyValue z r (b • p) (b • q) w := by
      simp only [covarianceGaussianEnergyValue, EinsteinFull.smulSubquadraticHarmonic,
        smul_smul, mul_inv_cancel₀ hb, one_smul]
    rw [he] at hc
    rw [hc]
    exact mul_le_mul_of_nonneg_left
      (le_csSup (hbd p q) (Set.mem_range_self _)) hs.le
  · have hh : sSup (Set.range (covarianceGaussianEnergyValue (a := a) z r p q)) ≤
        sSup (Set.range (covarianceGaussianEnergyValue (a := a) z r (b • p) (b • q))) / b ^ 2 := by
      apply csSup_le (hn _ _)
      rintro _ ⟨w, rfl⟩
      apply (le_div_iff₀ hs).2
      rw [mul_comm, ← covarianceGaussianEnergyValue_smul]
      exact le_csSup (hbd (b • p) (b • q)) (Set.mem_range_self _)
    simpa only [mul_comm] using (le_div_iff₀ hs).1 hh

/-- Positive deterministic scaling preserves the exact source O_s convention. -/
theorem covarianceOsBound_const_mul {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {s θ c : ℝ} (hc : 0 < c)
    (h : OsBound P X s θ) : OsBound P (fun ω => c * X ω) s (c * θ) := by
  refine ⟨h.1.const_mul c, h.2.1, mul_pos hc h.2.2.1, ?_⟩
  convert h.2.2.2 using 1
  apply lintegral_congr
  intro ω
  have hm : max (c * X ω) 0 = c * max (X ω) 0 := by
    rw [mul_max_of_nonneg _ _ hc.le, mul_zero]
  have he : (c * θ)⁻¹ * max (c * X ω) 0 = θ⁻¹ * max (X ω) 0 := by
    rw [hm, mul_inv_rev]
    calc
      _ = (c⁻¹ * c) * (θ⁻¹ * max (X ω) 0) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hc.ne', one_mul]
  rw [he]

/-- The source error bound extends to each fixed Euclidean load ball, with
its constant chosen before the environment law, center, scale and loads. -/
theorem covarianceSourceLocalizedEnergy_error_osBound_real
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (z : Vec d) (r : ℝ), 2 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < b → euclideanNorm q < b →
        OsBound (actualCoefficientLaw Q) (fun a =>
          |gaussianEnergyJ1 a z r p q -
            covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q|)
          s (C * r ^ (-γ)) := by
  obtain ⟨C, hC, hbound⟩ := covarianceSourceLocalizedEnergy_source_bound d hd D s δ γ η β h
  refine ⟨b ^ 2 * C, by positivity, ?_⟩
  intro Q z r hr p q hp hq
  have hpn : euclideanNorm (b⁻¹ • p) < 1 := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hb), inv_mul_eq_div]
    exact (div_lt_one hb).2 hp
  have hqn : euclideanNorm (b⁻¹ • q) < 1 := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hb), inv_mul_eq_div]
    exact (div_lt_one hb).2 hq
  have hunit := (hbound Q z r hr (b⁻¹ • p) (b⁻¹ • q) hpn hqn).2
  have hs := covarianceOsBound_const_mul (sq_pos_of_pos hb) hunit
  have hK : 0 < AKMUpperEllipticity D.ellipticity :=
    mul_pos (ellipticityScale_pos D.one_le_ellipticity)
      (ellipticityScale_pos D.one_le_ellipticity)
  have he : (fun a : Coefficient d (AKMUpperEllipticity D.ellipticity) =>
      b ^ 2 * |gaussianEnergyJ1 a z r (b⁻¹ • p) (b⁻¹ • q) -
        covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r (b⁻¹ • p) (b⁻¹ • q)|) =
      (fun a => |gaussianEnergyJ1 a z r p q -
        covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q|) := by
    funext a
    have hg := covarianceGaussianEnergy_smul hK a z (by linarith : 0 < r) b
      (b⁻¹ • p) (b⁻¹ • q)
    have hl := covarianceSourceLocalizedEnergy_smul d hd D s δ γ η β h Q a z r b
      (b⁻¹ • p) (b⁻¹ • q)
    simp only [smul_smul, mul_inv_cancel₀ hb.ne', one_smul] at hg hl
    rw [← abs_of_pos (sq_pos_of_pos hb), ← abs_mul, mul_sub, ← hg, ← hl]
  rw [he] at hs
  simpa only [mul_assoc] using hs

/-- Absolute Gaussian localization errors have genuine L2 membership and the
source decay, without presuming measurability of their signed counterparts. -/
theorem covarianceSourceLocalizedEnergy_abs_error_l2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (z : Vec d) (r : ℝ), 2 ≤ r → ∀ p q : Vec d,
        euclideanNorm p < b → euclideanNorm q < b →
        MemLp (fun a => |gaussianEnergyJ1 a z r p q -
          covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q|)
          2 (actualCoefficientLaw Q) ∧
        Real.sqrt (∫ a, |gaussianEnergyJ1 a z r p q -
          covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q| ^ 2
          ∂actualCoefficientLaw Q) ≤ C * r ^ (-γ) := by
  obtain ⟨C, hC, hbound⟩ := covarianceSourceLocalizedEnergy_error_osBound_real
    d hd D s δ γ η β h b hb
  let M := Real.sqrt (2 * (2 / s) ^ (2 / s))
  have hs : 0 < s := lt_trans zero_lt_one h.2.1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M * C, mul_pos hM hC, ?_⟩
  intro Q z r hr p q hp hq
  have hOs := hbound Q z r hr p q hp hq
  constructor
  · have ha : OsBound (actualCoefficientLaw Q)
        (fun a => abs (abs (gaussianEnergyJ1 a z r p q -
          covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q)))
        s (C * r ^ (-γ)) := by simpa only [abs_abs] using hOs
    exact EinsteinFull.AKM.memLp_two_of_osBound ha hOs.1.aestronglyMeasurable
  · simpa only [mul_assoc] using EinsteinFull.AKM.sqrt_integral_sq_le_of_osBound hOs


/-- The actual anisotropic polarization loads lie in one structural load ball.
The same bound covers both signs, and the ball is fixed before the law. -/
theorem covariancePolarizedLoads_bound {d : ℕ} (D : StructuralData d) :
    ∃ b : ℝ, 0 < b ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (j k : Fin d) (ε : ℝ), |ε| ≤ 1 →
        euclideanNorm (unitVector j + ε • unitVector k) < b ∧
        euclideanNorm ((ellipticityScale D.ellipticity •
          homogenizedCoefficient Q).mulVec (unitVector j)) < b := by
  let κ := ellipticityScale D.ellipticity
  let B := sourceReducedBound D.ellipticity
  have hκ : 0 < κ := ellipticityScale_pos D.one_le_ellipticity
  have hB : 0 ≤ B := (Clock.sourceReducedBound_pos D.one_le_ellipticity).le
  refine ⟨3 + κ * B, by positivity, ?_⟩
  intro Q j k ε hε
  have hu (i : Fin d) : euclideanNorm (unitVector i) = 1 := by
    change Real.sqrt (dotProduct (Pi.single i (1 : ℝ)) (Pi.single i 1)) = 1
    rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]
  have hp : euclideanNorm (unitVector j + ε • unitVector k) ≤ 2 := by
    calc
      _ ≤ euclideanNorm (unitVector j) + euclideanNorm (ε • unitVector k) :=
        TimeChange.euclideanNorm_add_le _ _
      _ = 1 + |ε| := by rw [TimeChange.euclideanNorm_smul, hu, hu, mul_one]
      _ ≤ 2 := by linarith
  have hq : euclideanNorm ((κ • homogenizedCoefficient Q).mulVec (unitVector j)) ≤
      κ * B := by
    rw [Matrix.smul_mulVec, TimeChange.euclideanNorm_smul, abs_of_pos hκ]
    exact mul_le_mul_of_nonneg_left (homogenizedCoefficient_column_bound Q j) hκ.le
  exact ⟨lt_of_le_of_lt hp (by nlinarith [mul_nonneg hκ.le hB]),
    lt_of_le_of_lt hq (by linarith)⟩

/-- Actual anisotropic polarized source errors obey the source L2 decay,
uniformly for both signs and with the constant preceding the law. -/
theorem covarianceSourcePolarization_abs_error_l2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (z : Vec d) (r : ℝ), 2 ≤ r → ∀ (j k : Fin d) (ε : ℝ), |ε| ≤ 1 →
        let p := unitVector j + ε • unitVector k
        let q := (ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec
          (unitVector j)
        MemLp (fun a => |gaussianEnergyJ1 a z r p q -
          covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q|)
          2 (actualCoefficientLaw Q) ∧
        Real.sqrt (∫ a, |gaussianEnergyJ1 a z r p q -
          covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z r p q| ^ 2
          ∂actualCoefficientLaw Q) ≤ C * r ^ (-γ) := by
  obtain ⟨b, hb, hloads⟩ := covariancePolarizedLoads_bound D
  obtain ⟨C, hC, hbound⟩ := covarianceSourceLocalizedEnergy_abs_error_l2
    d hd D s δ γ η β h b hb
  refine ⟨C, hC, ?_⟩
  intro Q z r hr j k ε hε
  exact hbound Q z r hr _ _ (hloads Q j k ε hε).1 (hloads Q j k ε hε).2


/-- Squared integrals are preserved by the literal zero-extended physical lift. -/
theorem covariancePhysicalLift_integral_sq {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (F : Coefficient d (AKMUpperEllipticity L) → ℝ)
    (hF : Measurable F) :
    (∫ ω, (covariancePhysicalLift Q F ω) ^ 2 ∂reducedLaw Q) =
      ∫ a, (F a) ^ 2 ∂actualCoefficientLaw Q := by
  have he : (fun ω => (covariancePhysicalLift Q F ω) ^ 2) =
      covariancePhysicalLift Q (fun a => (F a) ^ 2) := by
    funext ω
    unfold covariancePhysicalLift
    split <;> simp
  rw [he]
  exact covariancePhysicalLift_integral Q _ (hF.pow_const 2)

/-- Absolute source errors at the true polarized loads retain their L2 bound
in physical units under the actual reduced law. This uses the exact physical
inverse, unit-range projection and radius r/r₀. -/
theorem covariancePhysicalPolarization_abs_error_l2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ r : ℝ, 2 * D.dependenceRange ≤ r →
      ∀ (x : Vec d) (j k : Fin d) (ε : ℝ), |ε| ≤ 1 →
        let p := unitVector j + ε • unitVector k
        let q := (ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec
          (unitVector j)
        let F := fun a => |gaussianEnergyJ1 a (D.dependenceRange⁻¹ • x)
          (r / D.dependenceRange) p q -
          covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a
            (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) p q|
        MemLp (covariancePhysicalLift Q F) 2 (reducedLaw Q) ∧
        Real.sqrt (∫ ω, (covariancePhysicalLift Q F ω) ^ 2 ∂reducedLaw Q) ≤
          C * r ^ (-γ) := by
  obtain ⟨b, hb, hloads⟩ := covariancePolarizedLoads_bound D
  obtain ⟨C₀, _, hOs⟩ := covarianceSourceLocalizedEnergy_error_osBound_real
    d hd D s δ γ η β h b hb
  obtain ⟨C, hC, hbound⟩ := covarianceSourcePolarization_abs_error_l2
    d hd D s δ γ η β h
  have hr₀ : 0 < D.dependenceRange := lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange
  refine ⟨C * D.dependenceRange ^ γ, mul_pos hC (Real.rpow_pos_of_pos hr₀ _), ?_⟩
  intro Q r hr x j k ε hε
  have hρ : 2 ≤ r / D.dependenceRange := (le_div_iff₀ hr₀).2 hr
  have hrpos : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) hr₀) hr
  have hp := (hloads Q j k ε hε).1
  have hq := (hloads Q j k ε hε).2
  have hm := (hOs Q (D.dependenceRange⁻¹ • x) (r / D.dependenceRange)
    hρ _ _ hp hq).1
  have hL := hbound Q (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) hρ j k ε hε
  constructor
  · exact covariancePhysicalLift_memLp Q _ hm 2 hL.1
  · rw [covariancePhysicalLift_integral_sq Q _ hm]
    have he : (r / D.dependenceRange) ^ (-γ) = D.dependenceRange ^ γ * r ^ (-γ) := by
      rw [Real.div_rpow hrpos.le hr₀.le, Real.rpow_neg hr₀.le]
      simp only [div_inv_eq_mul, mul_comm]
    simpa only [he, mul_assoc] using hL.2

/-- Spatially equivalent coefficient fields have the same genuine A₁ members:
only the flux equation changes, and that equation is insensitive to null sets. -/
def covarianceTransportSubquadraticHarmonic {d : ℕ} {K : ℝ}
    {a b : Coefficient d K} (hab : a.field =ᵐ[volume] b.field)
    (w : SubquadraticHarmonic a) : SubquadraticHarmonic b where
  potential := w.potential
  grad := w.grad
  weak_gradient := w.weak_gradient
  local_energy := w.local_energy
  harmonic := HasWeakDivergence.congr_ae w.harmonic
    (ae_restrict_of_ae (hab.mono fun x hx => congrArg (fun M => M.mulVec (w.grad x)) hx))
    (ae_eq_refl _)
  growth := w.growth

/-- Transporting a whole-space competitor through coefficient equality
preserves its actual Gaussian variational value, including totalized integrals. -/
theorem covarianceGaussianEnergyValue_congr_coefficient_ae {d : ℕ} {K : ℝ}
    {a b : Coefficient d K} (hab : a.field =ᵐ[volume] b.field)
    (z : Vec d) (r : ℝ) (p q : Vec d) (w : SubquadraticHarmonic a) :
    covarianceGaussianEnergyValue z r p q w =
      covarianceGaussianEnergyValue z r p q
        (covarianceTransportSubquadraticHarmonic hab w) := by
  apply integral_congr_ae
  filter_upwards [hab] with x hx
  change heatKernel z r x *
    (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
      dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x)) =
    heatKernel z r x *
    (-(1 / 2 : ℝ) * dot (w.grad x) ((b x).mulVec (w.grad x)) -
      dot p ((b x).mulVec (w.grad x)) + dot q (w.grad x))
  rw [show a x = b x from hx]

/-- The full, coefficient-dependent A₁ supremum respects spatial coefficient
null sets. Equality is pointwise in the loads, center and radius. -/
theorem covarianceGaussianEnergy_congr_coefficient_ae {d : ℕ} {K : ℝ}
    {a b : Coefficient d K} (hab : a.field =ᵐ[volume] b.field)
    (z : Vec d) (r : ℝ) (p q : Vec d) :
    gaussianEnergyJ1 a z r p q = gaussianEnergyJ1 b z r p q := by
  rw [covarianceGaussianEnergy_eq_sSup_range, covarianceGaussianEnergy_eq_sSup_range]
  congr 1
  ext e
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨covarianceTransportSubquadraticHarmonic hab w,
      (covarianceGaussianEnergyValue_congr_coefficient_ae hab z r p q w).symm⟩
  · rintro ⟨w, rfl⟩
    exact ⟨covarianceTransportSubquadraticHarmonic hab.symm w,
      (covarianceGaussianEnergyValue_congr_coefficient_ae hab.symm z r p q w).symm⟩

/-- Observationally identical source coefficients have equal signed Gaussian
energies. No pointwise coefficient evaluations enter this statement. -/
theorem covarianceGaussianEnergy_congr_testIntegral {d : ℕ} {K : ℝ}
    (a b : Coefficient d K)
    (hab : ∀ (u : SmoothCompactTest d) (i j : Fin d),
      testIntegral a u i j = testIntegral b u i j)
    (z : Vec d) (r : ℝ) (p q : Vec d) :
    gaussianEnergyJ1 a z r p q = gaussianEnergyJ1 b z r p q :=
  covarianceGaussianEnergy_congr_coefficient_ae
    (coefficient_field_ae_eq_of_testIntegral_eq a b hab) z r p q

/-- The literal signed polarization also factors through source observations;
this is an invariance assertion, not a measurability assumption. -/
theorem covarianceCoarsenedCoefficient_congr_testIntegral {d : ℕ} {K : ℝ}
    (a b : Coefficient d K)
    (hab : ∀ (u : SmoothCompactTest d) (i j : Fin d),
      testIntegral a u i j = testIntegral b u i j)
    (A : Mat d) (z : Vec d) (r : ℝ) :
    coarsenedCoefficient a A z r = coarsenedCoefficient b A z r := by
  ext j k
  simp only [coarsenedCoefficient,
    covarianceGaussianEnergy_congr_testIntegral a b hab]

end EinsteinFull.Blueprint
