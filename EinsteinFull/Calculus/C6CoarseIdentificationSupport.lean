import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.Moments.Variance
import EinsteinFull.Calculus.C2CoarseIdentificationSupport
import EinsteinFull.Calculus.AKMStretchedExponentialMoments
import EinsteinFull.External.AKMCoarsenedCoefficientEstimates
import EinsteinFull.External.AKMAveragedCorrector
import EinsteinFull.Calculus.S1SharpBoundSupport
import EinsteinRelation.Mobility.DriftBoundPointwise
import EinsteinRelation.Correctors.HeatKernelConvolution
import EinsteinRelation.Correctors.SpatialMomentAverage
import EinsteinFull.Calculus.C2CorrectorPointwiseMoments
import EinsteinRelation.Correctors.AffineWeakSolution
import EinsteinRelation.Correctors.AKMLocalCanonicalIdentificationSublinearity
import EinsteinRelation.Correctors.ScalarRmsTriangle
import EinsteinRelation.Correctors.BoundedTestRms
import EinsteinRelation.Correctors.WeakPartialAddition
import EinsteinRelation.Correctors.AKMSourceMeasurableEnergy
import EinsteinFull.Calculus.C3CanonicalCorrectorSupport
import EinsteinFull.Calculus.C4HalfDirectionCorrector
import EinsteinFull.Frozen.HomogenizedCoefficient
import EinsteinFull.Work.W2.CorrectorReuseSupport
import EinsteinRelation.Correctors.StationaryConvolutionFubini

/-! Boundedness and normalization for the actual A₁ flux supremum, and
isotropic Gaussian moments of the canonical affine gradient. Source-corrector
identification and the covariance reduction remain separate obligations. -/

open MeasureTheory
noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM EinsteinFull.External.Draft
open EinsteinRelation.ReductionImageV3

/-- Entry bounds control multiplication in the ambient coordinate norm. -/
theorem coarseMatrix_mulVec_norm_le {d : ℕ} (M : Mat d) {c : ℝ}
    (hc : 0 ≤ c) (hM : ∀ i j, |M i j| ≤ c) (v : Vec d) :
    ‖M.mulVec v‖ ≤ (d : ℝ) * c * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  calc
    |M.mulVec v i| ≤ ∑ j, |M i j * v j| := by
      simpa only [Matrix.mulVec, dotProduct] using
        Finset.abs_sum_le_sum_abs (fun j => M i j * v j) Finset.univ
    _ ≤ ∑ _j : Fin d, c * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hM i j) (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j)
        (abs_nonneg _) hc
    _ = (d : ℝ) * c * ‖v‖ := by simp [mul_assoc]

/-- A normalized nonnegative weighted energy bounds a weighted vector integral.
The total Bochner integral inequality suffices for this deterministic bound;
spatial integrability in the covariance statement remains a separate obligation. -/
theorem coarseWeightedIntegral_norm_le {d : ℕ} (mask : Vec d → ℝ)
    (grad v : Vec d → Vec d) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ x, 0 ≤ mask x) (hmi : Integrable mask)
    (hmu : ∫ x, mask x = 1)
    (hi : Integrable (fun x => mask x * euclideanNorm (grad x) ^ 2))
    (hn : Real.sqrt (∫ x, mask x * euclideanNorm (grad x) ^ 2) ≤ 1)
    (hv : ∀ x, ‖v x‖ ≤ B * euclideanNorm (grad x)) :
    ‖∫ x, mask x • v x‖ ≤ 2 * B := by
  have he : (∫ x, mask x * euclideanNorm (grad x) ^ 2) ≤ 1 := by
    exact (Real.sqrt_le_iff).mp hn |>.2 |>.trans (by norm_num)
  have hdom := (hmi.add hi).const_mul B
  calc
    ‖∫ x, mask x • v x‖ ≤ ∫ x, ‖mask x • v x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, B * (mask x + mask x * euclideanNorm (grad x) ^ 2) := by
      apply integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) hdom
      apply ae_of_all
      intro x
      change ‖mask x • v x‖ ≤ B * (mask x + mask x * euclideanNorm (grad x) ^ 2)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hm x)]
      have ht : euclideanNorm (grad x) ≤ 1 + euclideanNorm (grad x) ^ 2 := by
        nlinarith only [sq_nonneg (euclideanNorm (grad x) - 1)]
      calc
        mask x * ‖v x‖ ≤ mask x * (B * euclideanNorm (grad x)) :=
          mul_le_mul_of_nonneg_left (hv x) (hm x)
        _ ≤ mask x * (B * (1 + euclideanNorm (grad x) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht hB) (hm x)
        _ = _ := by ring
    _ = B * (1 + ∫ x, mask x * euclideanNorm (grad x) ^ 2) := by
      rw [integral_const_mul, integral_add hmi hi, hmu]
    _ ≤ 2 * B := by nlinarith only [mul_le_mul_of_nonneg_left he hB]

/-- The defining set of the literal normalized A₁ flux defect is bounded.
No stochastic estimate or choice of harmonic representative is needed. -/
theorem coarseFluxResidual_bddAbove {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (a : Coefficient d K) (A : Mat d) (z : Vec d) {r : ℝ} (hr : 0 < r) :
    BddAbove {e : ℝ | ∃ w : SubquadraticHarmonic a,
      Integrable (fun x => heatKernel z r x * euclideanNorm (w.grad x) ^ 2) ∧
      Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (w.grad x) ^ 2) ≤ 1 ∧
      e = euclideanNorm
        ((∫ x, heatKernel z r x • (a x).mulVec (w.grad x)) -
          (A + coarsenedCoefficient a A z r).mulVec
            (∫ x, heatKernel z r x • w.grad x))} := by
  classical
  let M := A + coarsenedCoefficient a A z r
  let c : ℝ := ∑ i : Fin d, ∑ j : Fin d, |M i j|
  have hc : 0 ≤ c := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM : ∀ i j, |M i j| ≤ c := fun i j =>
    (Finset.single_le_sum (fun j _ => abs_nonneg (M i j)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i _ =>
        Finset.sum_nonneg fun j _ => abs_nonneg (M i j)) (Finset.mem_univ i))
  have hm (x : Vec d) : 0 ≤ heatKernel z r x :=
    Correctors.euclideanHeatKernel_nonneg (sq_nonneg r) (x - z)
  have hmi : Integrable (heatKernel z r) :=
    (Correctors.integrable_euclideanHeatKernel (sq_pos_of_pos hr)).comp_sub_right z
  have hmu : ∫ x, heatKernel z r x = 1 := by
    change (∫ x, Correctors.euclideanHeatKernel (r ^ 2) (x - z)) = 1
    rw [integral_sub_right_eq_self]
    exact Correctors.integral_euclideanHeatKernel (sq_pos_of_pos hr)
  refine ⟨((d : ℝ) + 1) * (2 * (d * K) + d * c * 2), ?_⟩
  rintro e ⟨w, hi, hn, rfl⟩
  have hw : ‖∫ x, heatKernel z r x • w.grad x‖ ≤ 2 := by
    simpa only [one_mul, mul_one] using coarseWeightedIntegral_norm_le
      (heatKernel z r) w.grad w.grad zero_le_one hm hmi hmu hi hn
      (fun x => by simpa only [one_mul] using Calculus.S1.norm_le_euclideanNorm (w.grad x))
  have hf : ‖∫ x, heatKernel z r x • (a x).mulVec (w.grad x)‖ ≤ 2 * (d * K) := by
    apply coarseWeightedIntegral_norm_le (heatKernel z r) w.grad _ (by positivity)
      hm hmi hmu hi hn
    intro x
    have hs (v : Vec d) : 0 ≤ euclideanSq v := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    have ha : ∀ i j, |a x i j| ≤ K :=
      abs_entry_le_of_quadratic_bounds hK (a x) (a.symmetric x)
        (fun v => (hs v).trans (a.elliptic x v).1)
        (fun v => (a.elliptic x v).2)
    exact (coarseMatrix_mulVec_norm_le (a x) hK ha (w.grad x)).trans
      (mul_le_mul_of_nonneg_left (Calculus.S1.norm_le_euclideanNorm _) (by positivity))
  apply (euclideanNorm_le_dimension_mul_norm _).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_sub_le _ _).trans (add_le_add hf
    ((coarseMatrix_mulVec_norm_le M hc hM _).trans
      (mul_le_mul_of_nonneg_left hw (by positivity))))

/-- Apply the true normalized flux defect to any integrable source A₁ member.
Boundedness is discharged here, including the zero weighted-energy case. -/
theorem coarseFluxResidual_le_gradientSize_mul_of_integrable {d : ℕ} {K : ℝ}
    (hK : 0 ≤ K) {a : Coefficient d K} (A : Mat d) (z : Vec d) {r : ℝ}
    (hr : 0 < r) (w : SubquadraticHarmonic a)
    (hi : Integrable (fun x => heatKernel z r x * euclideanNorm (w.grad x) ^ 2)) :
    euclideanNorm
      ((∫ x, heatKernel z r x • (a x).mulVec (w.grad x)) -
        (A + coarsenedCoefficient a A z r).mulVec
          (∫ x, heatKernel z r x • w.grad x)) ≤
      Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (w.grad x) ^ 2) *
        normalizedCoarseFluxDefect a A z r := by
  have hb := coarseFluxResidual_bddAbove hK a A z hr
  let N := Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (w.grad x) ^ 2)
  by_cases hn : 0 < N
  · exact coarseFluxResidual_le_gradientSize_mul A z r w hi hn hb
  have hn0 : N = 0 := le_antisymm (le_of_not_gt hn) (Real.sqrt_nonneg _)
  let F := euclideanNorm
    ((∫ x, heatKernel z r x • (a x).mulVec (w.grad x)) -
      (A + coarsenedCoefficient a A z r).mulVec
        (∫ x, heatKernel z r x • w.grad x))
  have hF : F ≤ 0 := by
    by_contra h
    have hpos : 0 < F := lt_of_not_ge h
    obtain ⟨b, hb⟩ := hb
    let c := (|b| + 1) / F
    have hc : 0 < c := div_pos (by positivity) hpos
    let v := smulSubquadraticHarmonic c w
    have hvi : Integrable (fun x => heatKernel z r x * euclideanNorm (v.grad x) ^ 2) := by
      apply (hi.const_mul (c ^ 2)).congr
      apply ae_of_all
      intro x
      simp only [v, smulSubquadraticHarmonic, TimeChange.euclideanNorm_smul, mul_pow, sq_abs]
      ring
    have hvn : Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (v.grad x) ^ 2) ≤ 1 := by
      rw [coarseGradientSize_smul]
      change |c| * N ≤ 1
      rw [hn0, mul_zero]
      exact zero_le_one
    have hv := hb ⟨v, hvi, hvn, rfl⟩
    rw [coarseFluxResidual_smul, TimeChange.euclideanNorm_smul, abs_of_pos hc] at hv
    change c * F ≤ b at hv
    have hcf : c * F = |b| + 1 := div_mul_cancel₀ _ hpos.ne'
    rw [hcf] at hv
    have hab : b ≤ |b| := le_abs_self b
    linarith only [hv, hab]
  change F ≤ N * normalizedCoarseFluxDefect a A z r
  rw [hn0, zero_mul]
  exact hF

/-- Literal isotropic Gaussian averaging preserves uniform probabilistic moments
of a jointly measurable Euclidean field and gives spatial energy integrability. -/
theorem coarseHeatKernel_energy_moment_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] {p C : ℝ}
    (hp : 2 ≤ p) (hC : 0 ≤ C)
    (g : Ω × Vec d → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    (hm : ∀ x, MemLp (fun ω => g (ω, x)) (ENNReal.ofReal p) P ∧
      eLpNorm (fun ω => g (ω, x)) (ENNReal.ofReal p) P ≤ ENNReal.ofReal C)
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    (∀ᵐ ω ∂P, Integrable (fun x => heatKernel z r x * ‖g (ω, x)‖ ^ 2)) ∧
    MemLp (fun ω => Real.sqrt (∫ x, heatKernel z r x * ‖g (ω, x)‖ ^ 2))
      (ENNReal.ofReal p) P ∧
    eLpNorm (fun ω => Real.sqrt (∫ x, heatKernel z r x * ‖g (ω, x)‖ ^ 2))
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal C := by
  have hk : Measurable (heatKernel z r) :=
    ((Correctors.continuous_euclideanHeatKernel (r ^ 2)).comp
      (continuous_id.sub continuous_const)).measurable
  have hk0 (x : Vec d) : 0 ≤ heatKernel z r x :=
    Correctors.euclideanHeatKernel_nonneg (sq_nonneg r) (x - z)
  have hki : Integrable (heatKernel z r) :=
    (Correctors.integrable_euclideanHeatKernel (d := d) (sq_pos_of_pos hr)).comp_sub_right z
  have hmass : (∫ x, heatKernel z r x) = 1 := by
    change (∫ x, Correctors.euclideanHeatKernel (r ^ 2) (x - z)) = 1
    rw [integral_sub_right_eq_self,
      Correctors.integral_euclideanHeatKernel (sq_pos_of_pos hr)]
  let ν : Measure (Vec d) := volume.withDensity (fun x => ENNReal.ofReal (heatKernel z r x))
  have hν : IsProbabilityMeasure ν := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hki (ae_of_all _ hk0), hmass]
    exact ENNReal.ofReal_one⟩
  obtain ⟨hsp, hs, hsb⟩ := Correctors.spatialL2_average_moment_le P ν hp hC g hg hm
  have heq (ω : Ω) : (∫ x, ‖g (ω, x)‖ ^ 2 ∂ν) =
      ∫ x, heatKernel z r x * ‖g (ω, x)‖ ^ 2 := by
    rw [integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (hk0 x), smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hsp] with ω hω
    have hi := (memLp_two_iff_integrable_sq_norm hω.aestronglyMeasurable).mp hω
    have hi' := (integrable_withDensity_iff_integrable_smul' hk.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hi
    simpa only [ENNReal.toReal_ofReal (hk0 _), smul_eq_mul] using hi'
  · simpa only [heq] using hs
  · simpa only [heq] using hsb

/-- The actual canonical affine gradient has isotropic Gaussian energy moments
at every positive scale, from its explicit marginal moment bound. -/
theorem coarseCorrector_heatKernel_energy_moment_le
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    {p M : ℝ} (hp : 2 ≤ p) (hM : 0 ≤ M)
    (hm : MemLp (fun ω => correctorGradient Q i ω) (ENNReal.ofReal p) (reducedLaw Q))
    (hb : eLpNorm (fun ω => correctorGradient Q i ω) (ENNReal.ofReal p)
      (reducedLaw Q) ≤ ENNReal.ofReal M) (z : Vec d) {r : ℝ} (hr : 0 < r) :
    (∀ᵐ ω ∂reducedLaw Q, Integrable (fun x => heatKernel z r x *
      euclideanNorm (unitVector i + WithLp.ofLp (correctorGradient Q i (translate x ω))) ^ 2)) ∧
    MemLp (fun ω => Real.sqrt (∫ x, heatKernel z r x *
      euclideanNorm (unitVector i + WithLp.ofLp (correctorGradient Q i (translate x ω))) ^ 2))
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    eLpNorm (fun ω => Real.sqrt (∫ x, heatKernel z r x *
      euclideanNorm (unitVector i + WithLp.ofLp (correctorGradient Q i (translate x ω))) ^ 2))
      (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal (1 + M) := by
  have hprob : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let a : EuclideanSpace ℝ (Fin d) := Correctors.correctorUnitVector i
  have ha : ‖a‖ = 1 := by simp [a, Correctors.correctorUnitVector]
  let g : FieldPair d × Vec d → EuclideanSpace ℝ (Fin d) :=
    fun v => a + correctorGradient Q i (translate v.2 v.1)
  have hg : Measurable g := measurable_const.add (measurable_correctorGradient_orbit Q i)
  have hcol (x : Vec d) :
      MemLp (fun ω => g (ω, x)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (fun ω => g (ω, x)) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal (1 + M) := by
    have ht := measurePreserving_translate (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) x
    have hmx := hm.comp_measurePreserving ht
    have hx : eLpNorm (fun ω => correctorGradient Q i (translate x ω))
        (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M :=
      (eLpNorm_comp_measurePreserving hm.aestronglyMeasurable ht).trans_le hb
    refine ⟨(memLp_const a).add hmx, ?_⟩
    calc
      _ ≤ eLpNorm (fun _ : FieldPair d => a) (ENNReal.ofReal p) (reducedLaw Q) +
          eLpNorm (fun ω => correctorGradient Q i (translate x ω))
            (ENNReal.ofReal p) (reducedLaw Q) :=
        eLpNorm_add_le (by
          simpa only [ENNReal.ofReal_one] using
            ENNReal.ofReal_le_ofReal (show 1 ≤ p by linarith))
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal M := by
        gcongr
        rw [eLpNorm_const' a (ENNReal.ofReal_ne_zero_iff.mpr (by linarith : 0 < p))
          ENNReal.ofReal_ne_top]
        simp [← ofReal_norm, ha]
      _ = _ := (ENNReal.ofReal_add (by norm_num) hM).symm
  have heq (ω : FieldPair d) (x : Vec d) :
      euclideanNorm (unitVector i + WithLp.ofLp (correctorGradient Q i (translate x ω))) =
        ‖g (ω, x)‖ := by
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
    rfl
  simpa only [← heq] using
    coarseHeatKernel_energy_moment_le (reducedLaw Q) hp (by positivity : 0 ≤ 1 + M)
      g hg hcol z hr

/-- A coordinate is locally square integrable on every positive Euclidean ball. -/
theorem coarseCoordinate_memLp {d : ℕ} (i : Fin d) {R : ℝ} (hR : 0 < R) :
    MemLp (fun x : Vec d => x i) 2 (volume.restrict (ball 0 R)) := by
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2.ne
  apply (memLp_const R).of_le (continuous_apply i).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet)] with x hx
  change |x i| ≤ |R|
  rw [abs_of_pos hR]
  exact (Regeneration.coordinate_abs_le_euclideanNorm x i).trans
    (by
      change euclideanNorm (x - 0) < R at hx
      simpa only [sub_zero] using hx.le)

/-- The affine coordinate has the actual constant weak gradient on all space. -/
theorem coarseCoordinate_weakGradient {d : ℕ} (i : Fin d) :
    HasWeakGradient Set.univ (fun x : Vec d => x i) (fun _ => unitVector i) := by
  intro j
  have hc := hasWeakPartialDerivative_of_contDiff j (fun x : Vec d => x i)
    (contDiff_apply ℝ ℝ i)
  have heq : coordinateDerivative j (fun x : Vec d => x i) =
      fun _ : Vec d => unitVector i j := by
    funext x
    rw [coordinateDerivative, (hasFDerivAt_apply i x).fderiv]
    change unitVector j i = unitVector i j
    simp [unitVector, Pi.single_apply, eq_comm]
  simpa only [heq] using hc

/-- Adding the affine coordinate to a sublinear potential gives the precise
uncentered subquadratic growth required by the source A₁ class. -/
theorem coarseAffine_subquadratic_growth {d : ℕ} (i : Fin d) (u : Vec d → ℝ)
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hsub : Filter.Tendsto
      (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R, u x ^ 2))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun R : ℝ => R ^ (-2 : ℤ) *
      Real.sqrt (⨍ x in ball 0 R, |x i + u x| ^ 2)) Filter.atTop (nhds 0) := by
  have hlim := Filter.Tendsto.add tendsto_inv_atTop_zero
    (Filter.Tendsto.mul tendsto_inv_atTop_zero hsub)
  simp only [mul_zero, add_zero] at hlim
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    exact mul_nonneg (zpow_nonneg hR.le _) (Real.sqrt_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    have hfin : volume (ball (0 : Vec d) R) ≠ ⊤ :=
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2.ne
    letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr hfin
    have hb : scalarRms volume (ball 0 R) (fun x : Vec d => x i) ≤ R := by
      apply scalarRms_le_of_ae_abs_le volume _ hfin hR.le
        (continuous_apply i).aestronglyMeasurable
      filter_upwards [ae_restrict_mem (by
        unfold ball euclideanNorm euclideanSq dot
        exact (isOpen_lt (by fun_prop) continuous_const).measurableSet)] with x hx
      exact (Regeneration.coordinate_abs_le_euclideanNorm x i).trans
        (by
          change euclideanNorm (x - 0) < R at hx
          simpa only [sub_zero] using hx.le)
    have ht := scalarRms_sub_le volume (ball 0 R) (coarseCoordinate_memLp i hR)
      (hu R hR).neg
    have ht' : Real.sqrt (⨍ x in ball 0 R, |x i + u x| ^ 2) ≤
        R + Real.sqrt (⨍ x in ball 0 R, u x ^ 2) := by
      simpa only [scalarRms, Pi.neg_apply, sub_neg_eq_add, neg_sq, sq_abs] using
        ht.trans (add_le_add hb (le_refl _))
    calc
      _ ≤ R ^ (-2 : ℤ) * (R + Real.sqrt (⨍ x in ball 0 R, u x ^ 2)) :=
        mul_le_mul_of_nonneg_left ht' (zpow_nonneg hR.le _)
      _ = R⁻¹ + R⁻¹ * (R⁻¹ * Real.sqrt (⨍ x in ball 0 R, u x ^ 2)) := by
        rw [zpow_neg, zpow_ofNat]
        field_simp [hR.ne']
        <;> ring

/-- Every actual unit-direction corrector supplies the genuine affine member
of source A₁, with its literal potential and gradient, almost surely. -/
theorem coarseCorrector_affine_mem_A1 {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} (i : Fin d) (φ : Corrector P (unitVector i)) :
    ∀ᵐ a ∂P, ∃ w : SubquadraticHarmonic a,
      w.potential = (fun x => x i + φ.potential a x) ∧
      w.grad = (fun x => unitVector i + φ.grad a x) := by
  filter_upwards [φ.locally_square_integrable, φ.weak_gradient, φ.harmonic, φ.sublinear]
    with a hloc hweak hharm hsub
  have hg (R : ℝ) (hR : 0 < R) :
      MemLp (fun x => euclideanNorm (unitVector i + φ.grad a x)) 2
        (volume.restrict (ball 0 R)) := by
    letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr
        (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2.ne
    have hc : Continuous (euclideanNorm : Vec d → ℝ) := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    have hm := (memLp_const (unitVector i)).add (hloc R hR).2
    apply (hm.norm.const_mul ((d : ℝ) + 1)).of_le
      (hc.comp_aestronglyMeasurable hm.aestronglyMeasurable)
    exact ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (show 0 ≤ euclideanNorm _ from Real.sqrt_nonneg _),
        Real.norm_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
      exact euclideanNorm_le_dimension_mul_norm _
  refine ⟨⟨(fun x => x i + φ.potential a x),
    (fun x => unitVector i + φ.grad a x),
    (fun j => hasWeakPartialDerivative_add (coarseCoordinate_weakGradient i j) (hweak j)),
    (fun R hR => ⟨(coarseCoordinate_memLp i hR).add (hloc R hR).1, hg R hR⟩),
    hharm, ?_⟩, rfl, rfl⟩
  exact coarseAffine_subquadratic_growth i (φ.potential a)
    (fun R hR => (hloc R hR).1)
    (sublinear_uncentered_of_centered _ (fun R hR => (hloc R hR).1) hsub)

/-- The source flux supremum controls the literal affine corrector residual.
A₁ membership and boundedness are proved internally; only the weighted energy
integrability is supplied at this deterministic interface. -/
theorem coarseCorrector_affine_fluxResidual_le {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    {P : Measure (Coefficient d K)} (i : Fin d) (φ : Corrector P (unitVector i))
    (A : Mat d) (z : Vec d) {r : ℝ} (hr : 0 < r)
    (hi : ∀ᵐ a ∂P, Integrable (fun x => heatKernel z r x *
      euclideanNorm (unitVector i + φ.grad a x) ^ 2)) :
    ∀ᵐ a ∂P, euclideanNorm
      ((∫ x, heatKernel z r x • (a x).mulVec (unitVector i + φ.grad a x)) -
        (A + coarsenedCoefficient a A z r).mulVec
          (∫ x, heatKernel z r x • (unitVector i + φ.grad a x))) ≤
      Real.sqrt (∫ x, heatKernel z r x *
        euclideanNorm (unitVector i + φ.grad a x) ^ 2) *
          normalizedCoarseFluxDefect a A z r := by
  filter_upwards [coarseCorrector_affine_mem_A1 i φ, hi] with a ha hi
  obtain ⟨w, _, hw⟩ := ha
  have hwi : Integrable (fun x => heatKernel z r x * euclideanNorm (w.grad x) ^ 2) := by
    simpa only [hw] using hi
  simpa only [hw] using
    coarseFluxResidual_le_gradientSize_mul_of_integrable hK A z hr w hwi

/-- Finite weighted energy gives ordinary spatial integrability of a dominated
vector field. The measurability assumption belongs to this generic interface. -/
theorem coarseWeightedVector_integrable {d : ℕ} (mask : Vec d → ℝ)
    (grad v : Vec d → Vec d) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ x, 0 ≤ mask x) (hmi : Integrable mask)
    (hi : Integrable (fun x => mask x * euclideanNorm (grad x) ^ 2))
    (hvmeas : AEStronglyMeasurable v volume)
    (hv : ∀ x, ‖v x‖ ≤ B * euclideanNorm (grad x)) :
    Integrable (fun x => mask x • v x) := by
  apply ((hmi.add hi).const_mul B).mono'
    (hmi.aestronglyMeasurable.smul hvmeas)
  apply ae_of_all
  intro x
  change ‖mask x • v x‖ ≤ B * (mask x + mask x * euclideanNorm (grad x) ^ 2)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hm x)]
  have ht : euclideanNorm (grad x) ≤ 1 + euclideanNorm (grad x) ^ 2 := by
    nlinarith only [sq_nonneg (euclideanNorm (grad x) - 1)]
  calc
    mask x * ‖v x‖ ≤ mask x * (B * euclideanNorm (grad x)) :=
      mul_le_mul_of_nonneg_left (hv x) (hm x)
    _ ≤ mask x * (B * (1 + euclideanNorm (grad x) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht hB) (hm x)
    _ = B * (mask x + mask x * euclideanNorm (grad x) ^ 2) := by ring

/-- The actual affine corrector gradient and flux have ordinary Gaussian
integrals whenever their weighted energy is finite. Raw coefficient sections
are handled through their spatially almost-everywhere measurable representative. -/
theorem coarseCorrector_affine_integrable {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    {P : Measure (Coefficient d K)} (i : Fin d) (φ : Corrector P (unitVector i))
    (a : Coefficient d K) (z : Vec d) {r : ℝ} (hr : 0 < r)
    (hi : Integrable (fun x => heatKernel z r x *
      euclideanNorm (unitVector i + φ.grad a x) ^ 2)) :
    Integrable (fun x => heatKernel z r x • (unitVector i + φ.grad a x)) ∧
    Integrable (fun x => heatKernel z r x •
      (a x).mulVec (unitVector i + φ.grad a x)) := by
  have hm (x : Vec d) : 0 ≤ heatKernel z r x :=
    Correctors.euclideanHeatKernel_nonneg (sq_nonneg r) (x - z)
  have hmi : Integrable (heatKernel z r) :=
    (Correctors.integrable_euclideanHeatKernel (sq_pos_of_pos hr)).comp_sub_right z
  have hg : Measurable (fun x => unitVector i + φ.grad a x) :=
    measurable_const.add (φ.measurable_grad.comp (measurable_const.prodMk measurable_id))
  have hf : AEStronglyMeasurable
      (fun x => (a x).mulVec (unitVector i + φ.grad a x)) volume := by
    apply ((measurable_sourceFluxRepresentative φ.grad φ.measurable_grad (unitVector i)).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable.congr
    exact sourceFluxRepresentative_ae_eq φ.grad (unitVector i) a
  constructor
  · apply coarseWeightedVector_integrable (heatKernel z r) _ _ zero_le_one
      hm hmi hi hg.aestronglyMeasurable
    intro x
    simpa only [one_mul] using Calculus.S1.norm_le_euclideanNorm (unitVector i + φ.grad a x)
  · apply coarseWeightedVector_integrable (B := (d : ℝ) * K)
      (heatKernel z r) _ _ (by positivity) hm hmi hi hf
    intro x
    have hs (v : Vec d) : 0 ≤ euclideanSq v := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)
    have ha : ∀ j k, |a x j k| ≤ K :=
      abs_entry_le_of_quadratic_bounds hK (a x) (a.symmetric x)
        (fun v => (hs v).trans (a.elliptic x v).1)
        (fun v => (a.elliptic x v).2)
    exact (coarseMatrix_mulVec_norm_le (a x) hK ha _).trans
      (mul_le_mul_of_nonneg_left (Calculus.S1.norm_le_euclideanNorm _) (by positivity))

/-- Select the actual full-coordinate producer together with its physical
canonical gradient and its exact expected flux. The same witness supplies both
identities; no identification of arbitrary source witnesses is assumed. -/
theorem exists_coarseCorrector_global_identification_meanFlux
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ φ : Corrector (actualCoefficientLaw Q) (unitVector i),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
          (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate (r₀ • y) (reduce ω.1))).ofLp) ∧
      meanFlux φ = ellipticityScale L • (homogenizedCoefficient Q).mulVec (unitVector i) := by
  obtain ⟨φ, hid⟩ := exists_akmCorrector_global_gradient_identification_from_pde Q i
  let ψ : Corrector (actualCoefficientLaw Q) (unitVector i) :=
    Calculus.C4HalfDirectionCorrector.doubledCorrector Q i φ
  refine ⟨ψ, ?_, ?_⟩
  · filter_upwards [hid] with ω hω
    filter_upwards [hω] with y hy
    simpa only [ψ, smul_add, Calculus.C4HalfDirectionCorrector.two_smul_halfDirection,
      Calculus.C4HalfDirectionCorrector.doubledCorrector_grad,
      correctorUnitVector, WithLp.ofLp_toLp, unitVector] using hy
  · have hm : meanFlux ψ = (2 : ℝ) • meanFlux φ := by
      simpa only [ψ, meanFlux, Calculus.C4HalfDirectionCorrector.doubledCorrector,
        scaledAKMCorrector, Calculus.C4HalfDirectionCorrector.two_smul_halfDirection,
        correctorUnitVector, WithLp.ofLp_toLp, unitVector] using
        meanFlux_scaledAKMCorrector φ 2
    rw [hm, akm_meanFlux_of_global_gradient_identification Q i φ hid, smul_smul,
      show (2 : ℝ) * (ellipticityScale L / 2) = ellipticityScale L by ring]
    congr 1
    ext j
    simp [homogenizedCoefficient, Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, mul_ite]

/-- The literal frozen commutator is measurable, including the selected
strongly measurable canonical gradient representative. -/
theorem coarseCommutator_measurable {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (j i : Fin d) :
    Measurable (commutatorObservation Q j i) := by
  apply Finset.measurable_fun_sum
  intro k _
  have ha : Continuous (fun ω : FieldPair d => ω.1 (0 : Vec d)) :=
    (continuous_eval_const (0 : Vec d)).comp continuous_fst
  have hg : Measurable (fun ω : FieldPair d => correctorGradient Q i ω k) :=
    (PiLp.continuous_apply 2 _ k).measurable.comp
      (Lp.stronglyMeasurable (correctorGradient Q i)).measurable
  exact ((ha.matrix_elem j k).measurable.sub measurable_const).mul
    (measurable_const.add hg)

/-- The target's literal isotropic commutator convolution has ordinary spatial
and probability integrals and mean zero. These facts require no smoothness. -/
theorem coarseCommutator_heatKernel_integrable_mean_zero
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (j i : Fin d)
    (x : Vec d) {r : ℝ} (hr : 0 < r) :
    (∀ᵐ ω ∂reducedLaw Q, Integrable (fun z => heatKernel 0 r z *
      commutatorObservation Q j i (translate (x - z) ω))) ∧
    Integrable (fun ω => ∫ z, heatKernel 0 r z *
      commutatorObservation Q j i (translate (x - z) ω)) (reducedLaw Q) ∧
    (∫ ω, ∫ z, heatKernel 0 r z *
      commutatorObservation Q j i (translate (x - z) ω) ∂volume ∂reducedLaw Q) = 0 := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hk : Measurable (heatKernel (0 : Vec d) r) := by
    unfold heatKernel euclideanHeatKernel euclideanSq dot
    fun_prop
  have hki : Integrable (heatKernel (0 : Vec d) r) := by
    change Integrable (fun z : Vec d => Correctors.euclideanHeatKernel (r ^ 2) (z - 0))
    simpa only [sub_zero] using
      Correctors.integrable_euclideanHeatKernel (d := d) (sq_pos_of_pos hr)
  have hf := coarseCommutator_measurable Q j i
  have hshift : Measurable (fun z : Vec d => x - z) := measurable_const.sub measurable_id
  have hi := integrable_stationary_weight volume (reducedLaw Q)
    (reducedEnvironmentLaw_stationary Q) hk hki hshift hf
    (integrable_commutatorObservation Q j i)
  refine ⟨hi.prod_left_ae, hi.integral_prod_right, ?_⟩
  have hswap : Integrable (Function.uncurry (fun ω : FieldPair d => fun z : Vec d =>
      heatKernel 0 r z * commutatorObservation Q j i (translate (x - z) ω)))
      ((reducedLaw Q).prod volume) := hi.swap
  rw [integral_integral_swap hswap]
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro z
  change (∫ ω : FieldPair d, heatKernel 0 r z *
    commutatorObservation Q j i (translate (x - z) ω) ∂reducedLaw Q) = 0
  rw [integral_const_mul, Probability.integral_translate (reducedLaw Q)
    (reducedEnvironmentLaw_stationary Q) (x - z) (commutatorObservation Q j i) hf,
    integral_commutatorObservation, mul_zero]

/-- Ordinary weighted raw-flux integrals are measurable despite the raw
coefficient field being only spatially almost everywhere represented. -/
theorem coarseWeightedFlux_measurable {d : ℕ} {K : ℝ}
    (g : Coefficient d K → Vec d → Vec d)
    (hg : Measurable (fun p : Coefficient d K × Vec d => g p.1 p.2))
    (e : Vec d) {w : Vec d → ℝ} (hw : Measurable w) :
    Measurable (fun a : Coefficient d K =>
      ∫ y, w y • (a y).mulVec (e + g a y)) := by
  have heq : (fun a : Coefficient d K => ∫ y, w y • sourceFluxRepresentative g e a y) =
      (fun a => ∫ y, w y • (a y).mulVec (e + g a y)) := by
    funext a
    apply integral_congr_ae
    filter_upwards [sourceFluxRepresentative_ae_eq g e a] with y hy
    rw [hy]
  rw [← heq]
  exact ((hw.comp measurable_snd).smul
    (measurable_sourceFluxRepresentative g hg e)).stronglyMeasurable.integral_prod_right'.measurable

/-- Continuous stationarity of the identified canonical flux, rather than
lattice stationarity of an arbitrary source witness, determines the expectation
of every integrable weighted actual flux. -/
theorem coarseCorrector_weightedFlux_expectation
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    {w : Vec d → ℝ} (hw : Measurable w) (hwi : Integrable w) :
    Integrable (fun a => ∫ y, w y • (a y).mulVec (unitVector i + φ.grad a y))
      (actualCoefficientLaw Q) ∧
    (∫ a, ∫ y, w y • (a y).mulVec (unitVector i + φ.grad a y)
      ∂volume ∂actualCoefficientLaw Q) =
      (∫ y, w y) • (ellipticityScale L •
        (homogenizedCoefficient Q).mulVec (unitVector i)) := by
  let q := fun a : Coefficient d (AKMUpperEllipticity L) =>
    ∫ y, w y • (a y).mulVec (unitVector i + φ.grad a y)
  have hq : Measurable q := coarseWeightedFlux_measurable φ.grad φ.measurable_grad _ hw
  let f : FieldPair d → Vec d := fun ω => (canonicalCorrectorFlux Q i ω).ofLp
  let C := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  have hf : Measurable f := C.continuous.measurable.comp
    (Lp.stronglyMeasurable (canonicalCorrectorFlux Q i)).measurable
  have hfi : Integrable f (reducedEnvironmentLaw Q) :=
    C.integrable_comp (canonicalCorrectorFlux_integrable Q i)
  have hσ : Measurable (fun y : Vec d => r₀ • y) :=
    (continuous_id.const_smul r₀).measurable
  have hsp := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_spatial_canonicalCorrectorFlux Q i (σ := fun y => r₀ • y) hσ)
  have hflux : ∀ᵐ ω ∂physicalReferenceLaw Q,
      q (project (r₀ := r₀) Q.ellipticity_parameter ω) =
      ellipticityScale L • ∫ y, w y • f (translate (r₀ • y) (reduce ω.1)) := by
    filter_upwards [hid, hsp] with ω hω hs
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [hω, hs] with y hy hsy
    change w y • ((ellipticityScale L • (reduce ω.1).1 (r₀ • y)).mulVec
      (unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y)) = _
    change _ = ellipticityScale L • (w y • (canonicalCorrectorFlux Q i
      (translate (r₀ • y) (reduce ω.1))).ofLp)
    rw [hsy, hy, Matrix.smul_mulVec, smul_comm]
  have hcell : Integrable (fun ω => ∫ y, w y • f (translate (r₀ • y) ω))
      (reducedEnvironmentLaw Q) :=
    (integrable_weighted_stationary_prod (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) volume hf hfi hw hwi hσ).integral_prod_right
  constructor
  · apply ((measurePreserving_akmProject Q).integrable_comp hq.aestronglyMeasurable).mp
    apply (((measurePreserving_physicalReduction Q).integrable_comp_of_integrable hcell).smul
      (ellipticityScale L)).congr
    filter_upwards [hflux] with ω hω
    exact hω.symm
  · have hm := integral_map (μ := physicalReferenceLaw Q)
      (measurable_project (r₀ := r₀) Q.ellipticity_parameter).aemeasurable
      (hq.aestronglyMeasurable (μ := actualCoefficientLaw Q))
    change (∫ a, q a ∂actualCoefficientLaw Q) = _ at hm ⊢
    rw [hm, integral_congr_ae hflux, integral_smul]
    have hEmb : MeasurableEmbedding (fun ω : PhysicalField d L => reduce ω.1) :=
      (Probability.measurableEmbedding_reduce d).comp
        (MeasurableEmbedding.subtype_coe (Sharpness.measurableSet_isRegular_fieldPair L))
    rw [(measurePreserving_physicalReduction Q).integral_comp hEmb
      (fun ω => ∫ y, w y • f (translate (r₀ • y) ω)),
      integral_weighted_stationary (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) volume hf hfi hw hwi hσ]
    have he : (∫ ω, f ω ∂reducedEnvironmentLaw Q) =
        (homogenizedCoefficient Q).mulVec (unitVector i) := by
      rw [show (∫ ω, f ω ∂reducedEnvironmentLaw Q) = (expectedCorrectorFlux Q i).ofLp from
        C.integral_comp_comm (canonicalCorrectorFlux_integrable Q i)]
      ext j
      simp [homogenizedCoefficient, Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, mul_ite]
    rw [he, smul_comm]

/-- One actual coordinate corrector has the canonical physical gradient and
an ordinary, integrable Gaussian flux average with the exact homogenized mean
at every positive scale. The witness is fixed before center and scale. -/
theorem exists_coarseCorrector_gaussianFlux_expectation
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ φ : Corrector (actualCoefficientLaw Q) (unitVector i),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
          (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate (r₀ • y) (reduce ω.1))).ofLp) ∧
      meanFlux φ = ellipticityScale L • (homogenizedCoefficient Q).mulVec (unitVector i) ∧
      ∀ (z : Vec d) (r : ℝ), 0 < r →
        Integrable (fun a => ∫ y, heatKernel z r y •
          (a y).mulVec (unitVector i + φ.grad a y)) (actualCoefficientLaw Q) ∧
        (∫ a, ∫ y, heatKernel z r y • (a y).mulVec (unitVector i + φ.grad a y)
          ∂volume ∂actualCoefficientLaw Q) = meanFlux φ := by
  obtain ⟨φ, hid, hmean⟩ := exists_coarseCorrector_global_identification_meanFlux Q i
  refine ⟨φ, hid, hmean, ?_⟩
  intro z r hr
  have hk : Measurable (heatKernel z r) :=
    ((Correctors.continuous_euclideanHeatKernel (r ^ 2)).comp
      (continuous_id.sub continuous_const)).measurable
  have hki : Integrable (heatKernel z r) :=
    (Correctors.integrable_euclideanHeatKernel (d := d) (sq_pos_of_pos hr)).comp_sub_right z
  have hmass : (∫ y, heatKernel z r y) = 1 := by
    change (∫ y, Correctors.euclideanHeatKernel (r ^ 2) (y - z)) = 1
    rw [integral_sub_right_eq_self,
      Correctors.integral_euclideanHeatKernel (sq_pos_of_pos hr)]
  obtain ⟨hi, he⟩ := coarseCorrector_weightedFlux_expectation Q i φ hid hk hki
  exact ⟨hi, by simpa only [hmass, one_smul, hmean] using he⟩

/-- The commutator comparison splits into the genuine normalized A₁ flux
defect and the coarsened coefficient acting on the averaged corrector gradient.
No stochastic estimate or source-matrix identification is assumed here. -/
theorem coarseCorrector_affine_commutatorResidual_le {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    {P : Measure (Coefficient d K)} (i : Fin d) (φ : Corrector P (unitVector i))
    (A : Mat d) (z : Vec d) {r : ℝ} (hr : 0 < r)
    (hi : ∀ᵐ a ∂P, Integrable (fun x => heatKernel z r x *
      euclideanNorm (unitVector i + φ.grad a x) ^ 2)) :
    ∀ᵐ a ∂P,
      let B := coarsenedCoefficient a A z r
      let U := ∫ x, heatKernel z r x • (unitVector i + φ.grad a x)
      let F := ∫ x, heatKernel z r x • (a x).mulVec (unitVector i + φ.grad a x)
      euclideanNorm (F - A.mulVec U - B.mulVec (unitVector i)) ≤
        Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (unitVector i + φ.grad a x) ^ 2) *
          normalizedCoarseFluxDefect a A z r +
        euclideanNorm (B.mulVec (U - unitVector i)) := by
  filter_upwards [coarseCorrector_affine_fluxResidual_le hK i φ A z hr hi] with a ha
  let B := coarsenedCoefficient a A z r
  let U := ∫ x, heatKernel z r x • (unitVector i + φ.grad a x)
  let F := ∫ x, heatKernel z r x • (a x).mulVec (unitVector i + φ.grad a x)
  change euclideanNorm (F - A.mulVec U - B.mulVec (unitVector i)) ≤ _
  have heq : F - A.mulVec U - B.mulVec (unitVector i) =
      (F - (A + B).mulVec U) + B.mulVec (U - unitVector i) := by
    rw [Matrix.add_mulVec, Matrix.mulVec_sub]
    abel
  rw [heq]
  exact (TimeChange.euclideanNorm_add_le _ _).trans (add_le_add ha le_rfl)

/-- Canonical L² and stationarity give ordinary weighted affine-energy
integrability for every integrable weight and deterministic spatial rescaling. -/
theorem coarseCanonical_weightedAffineEnergy_integrable
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) (c : ℝ)
    {w : Vec d → ℝ} (hw : Measurable w) (hwi : Integrable w) :
    (∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun y => w y *
      euclideanNorm (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (c • y) ω)).ofLp ^ 2)) ∧
    Integrable (fun ω => ∫ y, w y *
      euclideanNorm (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (c • y) ω)).ofLp ^ 2) (reducedEnvironmentLaw Q) := by
  let G := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  let F : FieldPair d → ℝ := fun ω => ‖correctorUnitVector i + G ω‖ ^ 2
  have hXm : Measurable (fun ω : FieldPair d => correctorUnitVector i + G ω) :=
    measurable_const.add (Lp.stronglyMeasurable G).measurable
  have hF : Measurable F := hXm.norm.pow_const 2
  have hX : MemLp (fun ω => correctorUnitVector i + G ω) 2 (reducedEnvironmentLaw Q) :=
    (memLp_const (correctorUnitVector i)).add (Lp.memLp G)
  have hFi : Integrable F (reducedEnvironmentLaw Q) :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX
  have hσ : Measurable (fun y : Vec d => c • y) :=
    (continuous_id.const_smul c).measurable
  have h := integrable_weighted_stationary_prod (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) volume hF hFi hw hwi hσ
  have hn (v : EuclideanSpace ℝ (Fin d)) : euclideanNorm v.ofLp = ‖v‖ := by
    simpa only [WithLp.toLp_ofLp] using TimeChange.euclideanNorm_eq_norm_toLp v.ofLp
  constructor
  · simpa only [smul_eq_mul, F, G, hn] using h.prod_left_ae
  · simpa only [smul_eq_mul, F, G, hn] using h.integral_prod_right

/-- An identified actual corrector has ordinary weighted affine-energy
integrability both in space and after spatial integration in probability. -/
theorem coarseCorrector_weightedAffineEnergy_integrable
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    {w : Vec d → ℝ} (hw : Measurable w) (hwi : Integrable w) :
    (∀ᵐ a ∂actualCoefficientLaw Q, Integrable (fun y => w y *
      euclideanNorm (unitVector i + φ.grad a y) ^ 2)) ∧
    Integrable (fun a => ∫ y, w y * euclideanNorm (unitVector i + φ.grad a y) ^ 2)
      (actualCoefficientLaw Q) := by
  let f := fun (a : Coefficient d (AKMUpperEllipticity L)) (y : Vec d) =>
    w y * euclideanNorm (unitVector i + φ.grad a y) ^ 2
  have hm : Measurable (Function.uncurry f) := by
    have hg : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
        unitVector i + φ.grad p.1 p.2) := measurable_const.add φ.measurable_grad
    have hn : Continuous (fun v : Vec d => euclideanNorm v) := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    exact (hw.comp measurable_snd).mul ((hn.measurable.comp hg).pow_const 2)
  have hset : MeasurableSet {a | Integrable (f a) volume} :=
    measurableSet_integrable hm.stronglyMeasurable
  obtain ⟨hsp, hpi⟩ := coarseCanonical_weightedAffineEnergy_integrable Q i r₀ hw hwi
  have hnorm := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae hsp
  have hphys : ∀ᵐ ω ∂physicalReferenceLaw Q,
      Integrable (f (project (r₀ := r₀) Q.ellipticity_parameter ω)) volume := by
    filter_upwards [hid, hnorm] with ω hω hn
    apply hn.congr
    filter_upwards [hω] with y hy
    exact congrArg (fun v : Vec d => w y * euclideanNorm v ^ 2) hy.symm
  constructor
  · exact (ae_map_iff (measurable_project (r₀ := r₀)
      Q.ellipticity_parameter).aemeasurable hset).2 hphys
  · have hq : Measurable (fun a => ∫ y, f a y) :=
      hm.stronglyMeasurable.integral_prod_right'.measurable
    apply ((measurePreserving_akmProject Q).integrable_comp hq.aestronglyMeasurable).mp
    apply ((measurePreserving_physicalReduction Q).integrable_comp_of_integrable hpi).congr
    filter_upwards [hid] with ω hω
    apply integral_congr_ae
    filter_upwards [hω] with y hy
    exact congrArg (fun v : Vec d => w y * euclideanNorm v ^ 2) hy.symm

/-- At every positive Gaussian scale the identified actual affine gradient
and raw flux are spatially integrable, as is the squared affine gradient. -/
theorem coarseCorrector_gaussianAffine_integrable
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ a ∂actualCoefficientLaw Q,
      Integrable (fun y => heatKernel z r y * euclideanNorm (unitVector i + φ.grad a y) ^ 2) ∧
      Integrable (fun y => heatKernel z r y • (unitVector i + φ.grad a y)) ∧
      Integrable (fun y => heatKernel z r y • (a y).mulVec (unitVector i + φ.grad a y)) := by
  have hw : Measurable (heatKernel z r) :=
    ((Correctors.continuous_euclideanHeatKernel (r ^ 2)).comp
      (continuous_id.sub continuous_const)).measurable
  have hwi : Integrable (heatKernel z r) :=
    (Correctors.integrable_euclideanHeatKernel (sq_pos_of_pos hr)).comp_sub_right z
  have hsp := (coarseCorrector_weightedAffineEnergy_integrable Q i φ hid hw hwi).1
  filter_upwards [hsp] with a ha
  exact ⟨ha, coarseCorrector_affine_integrable
    (by unfold AKMUpperEllipticity; exact mul_self_nonneg _) i φ a z hr ha⟩

/-- Canonical identification discharges the spatial integrability premise in
the deterministic Gaussian commutator/coarse-column comparison. -/
theorem coarseCorrector_gaussian_commutatorResidual_le
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    (A : Mat d) (z : Vec d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ a ∂actualCoefficientLaw Q,
      let B := coarsenedCoefficient a A z r
      let U := ∫ y, heatKernel z r y • (unitVector i + φ.grad a y)
      let F := ∫ y, heatKernel z r y • (a y).mulVec (unitVector i + φ.grad a y)
      euclideanNorm (F - A.mulVec U - B.mulVec (unitVector i)) ≤
        Real.sqrt (∫ y, heatKernel z r y * euclideanNorm (unitVector i + φ.grad a y) ^ 2) *
          normalizedCoarseFluxDefect a A z r +
        euclideanNorm (B.mulVec (U - unitVector i)) := by
  apply coarseCorrector_affine_commutatorResidual_le
    (by unfold AKMUpperEllipticity; exact mul_self_nonneg _) i φ A z hr
  filter_upwards [coarseCorrector_gaussianAffine_integrable Q i φ hid z hr] with a ha
  exact ha.1

/-- The coordinate mean-zero characterization gives the full ordinary vector
expectation of the canonical stationary gradient. -/
theorem coarseCanonical_gradient_integral_zero
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    (∫ ω, (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω
      ∂reducedEnvironmentLaw Q) = 0 := by
  let G := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  have hi : Integrable G (reducedEnvironmentLaw Q) :=
    (Lp.memLp G).integrable (by norm_num)
  ext j
  let π := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j
  have hj := canonicalCorrectorGradient_mean_zero Q i j
  rw [euclideanCoordinateMean, ContinuousLinearMap.comp_apply,
    EinsteinRelation.l2Expectation_apply] at hj
  calc
    (∫ ω, G ω ∂reducedEnvironmentLaw Q) j =
        ∫ ω, (G ω) j ∂reducedEnvironmentLaw Q := (π.integral_comp_comm hi).symm
    _ = ∫ ω, ((π.compLpL 2 (reducedEnvironmentLaw Q)) G) ω
        ∂reducedEnvironmentLaw Q :=
      integral_congr_ae (ContinuousLinearMap.coeFn_compLpL π G
        (p := 2) (μ := reducedEnvironmentLaw Q)).symm
    _ = 0 := hj

/-- Every ordinary weighted actual-gradient average is probability integrable
and centered, for a corrector identified with the canonical physical gradient. -/
theorem coarseCorrector_weightedGradient_expectation
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    {w : Vec d → ℝ} (hw : Measurable w) (hwi : Integrable w) :
    Integrable (fun a => ∫ y, w y • φ.grad a y) (actualCoefficientLaw Q) ∧
    (∫ a, ∫ y, w y • φ.grad a y ∂volume ∂actualCoefficientLaw Q) = 0 := by
  let q := fun a : Coefficient d (AKMUpperEllipticity L) => ∫ y, w y • φ.grad a y
  have hq : Measurable q :=
    ((hw.comp measurable_snd).smul φ.measurable_grad).stronglyMeasurable.integral_prod_right'.measurable
  let G := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  let f : FieldPair d → Vec d := fun ω => (G ω).ofLp
  let C := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  have hf : Measurable f := C.continuous.measurable.comp (Lp.stronglyMeasurable G).measurable
  have hGi : Integrable G (reducedEnvironmentLaw Q) :=
    (Lp.memLp G).integrable (by norm_num)
  have hfi : Integrable f (reducedEnvironmentLaw Q) := C.integrable_comp hGi
  have hσ : Measurable (fun y : Vec d => r₀ • y) :=
    (continuous_id.const_smul r₀).measurable
  have hu : (correctorUnitVector i).ofLp = unitVector i := by
    ext j
    simp [correctorUnitVector, unitVector, Pi.single_apply, eq_comm]
  have heq : ∀ᵐ ω ∂physicalReferenceLaw Q,
      q (project (r₀ := r₀) Q.ellipticity_parameter ω) =
      ∫ y, w y • f (translate (r₀ • y) (reduce ω.1)) := by
    filter_upwards [hid] with ω hω
    apply integral_congr_ae
    filter_upwards [hω] with y hy
    have hy' : unitVector i + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        unitVector i + f (translate (r₀ • y) (reduce ω.1)) := by
      simpa only [WithLp.ofLp_add, hu] using hy
    exact congrArg (fun v : Vec d => w y • v) (add_left_cancel hy')
  have hcell : Integrable (fun ω => ∫ y, w y • f (translate (r₀ • y) ω))
      (reducedEnvironmentLaw Q) :=
    (integrable_weighted_stationary_prod (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) volume hf hfi hw hwi hσ).integral_prod_right
  constructor
  · apply ((measurePreserving_akmProject Q).integrable_comp hq.aestronglyMeasurable).mp
    apply ((measurePreserving_physicalReduction Q).integrable_comp_of_integrable hcell).congr
    filter_upwards [heq] with ω hω
    exact hω.symm
  · have hm := integral_map (μ := physicalReferenceLaw Q)
      (measurable_project (r₀ := r₀) Q.ellipticity_parameter).aemeasurable
      (hq.aestronglyMeasurable (μ := actualCoefficientLaw Q))
    change (∫ a, q a ∂actualCoefficientLaw Q) = _ at hm ⊢
    rw [hm, integral_congr_ae heq]
    have hEmb : MeasurableEmbedding (fun ω : PhysicalField d L => reduce ω.1) :=
      (Probability.measurableEmbedding_reduce d).comp
        (MeasurableEmbedding.subtype_coe (Sharpness.measurableSet_isRegular_fieldPair L))
    rw [(measurePreserving_physicalReduction Q).integral_comp hEmb
      (fun ω => ∫ y, w y • f (translate (r₀ • y) ω)),
      integral_weighted_stationary (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) volume hf hfi hw hwi hσ]
    have hz : (∫ ω, f ω ∂reducedEnvironmentLaw Q) = 0 := by
      rw [show (∫ ω, f ω ∂reducedEnvironmentLaw Q) =
          C (∫ ω, G ω ∂reducedEnvironmentLaw Q) from C.integral_comp_comm hGi,
        coarseCanonical_gradient_integral_zero Q i, map_zero]
    rw [hz, smul_zero]

/-- The same actual corrector has an integrable Gaussian affine-gradient
average with expectation equal to its unit load. -/
theorem coarseCorrector_gaussianAffineGradient_expectation
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    Integrable (fun a => ∫ y, heatKernel z r y • (unitVector i + φ.grad a y))
      (actualCoefficientLaw Q) ∧
    (∫ a, ∫ y, heatKernel z r y • (unitVector i + φ.grad a y)
      ∂volume ∂actualCoefficientLaw Q) = unitVector i := by
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  have hw : Measurable (heatKernel z r) :=
    ((Correctors.continuous_euclideanHeatKernel (r ^ 2)).comp
      (continuous_id.sub continuous_const)).measurable
  have hwi : Integrable (heatKernel z r) :=
    (Correctors.integrable_euclideanHeatKernel (sq_pos_of_pos hr)).comp_sub_right z
  have hmass : (∫ y, heatKernel z r y) = 1 := by
    change (∫ y, Correctors.euclideanHeatKernel (r ^ 2) (y - z)) = 1
    rw [integral_sub_right_eq_self,
      Correctors.integral_euclideanHeatKernel (sq_pos_of_pos hr)]
  obtain ⟨hgi, hgmean⟩ := coarseCorrector_weightedGradient_expectation Q i φ hid hw hwi
  have hc : Integrable (fun y => heatKernel z r y • unitVector i) := hwi.smul_const _
  have heq : (fun a => ∫ y, heatKernel z r y • (unitVector i + φ.grad a y)) =ᵐ[
      actualCoefficientLaw Q] (fun a => unitVector i + ∫ y, heatKernel z r y • φ.grad a y) := by
    filter_upwards [coarseCorrector_gaussianAffine_integrable Q i φ hid z hr] with a ha
    have hg : Integrable (fun y => heatKernel z r y • φ.grad a y) := by
      apply (ha.2.1.sub hc).congr
      exact Filter.Eventually.of_forall (fun y => by simp [smul_add])
    simp_rw [smul_add]
    rw [integral_add hc hg, integral_smul_const, hmass, one_smul]
  constructor
  · exact ((integrable_const _).add hgi).congr heq.symm
  · rw [integral_congr_ae heq, integral_add (integrable_const _) hgi,
      integral_const, hgmean]
    simp

/-- The Gaussian raw-flux residual against any deterministic matrix has the
exact expected mismatch between that matrix and the canonical physical flux. -/
theorem coarseCorrector_gaussianFluxResidual_expectation
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    (A : Mat d) (z : Vec d) {r : ℝ} (hr : 0 < r) :
    let R := fun a =>
      (∫ y, heatKernel z r y • (a y).mulVec (unitVector i + φ.grad a y)) -
      A.mulVec (∫ y, heatKernel z r y • (unitVector i + φ.grad a y))
    Integrable R (actualCoefficientLaw Q) ∧
    (∫ a, R a ∂actualCoefficientLaw Q) =
      ellipticityScale L • (homogenizedCoefficient Q).mulVec (unitVector i) -
        A.mulVec (unitVector i) := by
  have hw : Measurable (heatKernel z r) :=
    ((Correctors.continuous_euclideanHeatKernel (r ^ 2)).comp
      (continuous_id.sub continuous_const)).measurable
  have hwi : Integrable (heatKernel z r) :=
    (Correctors.integrable_euclideanHeatKernel (sq_pos_of_pos hr)).comp_sub_right z
  have hmass : (∫ y, heatKernel z r y) = 1 := by
    change (∫ y, Correctors.euclideanHeatKernel (r ^ 2) (y - z)) = 1
    rw [integral_sub_right_eq_self,
      Correctors.integral_euclideanHeatKernel (sq_pos_of_pos hr)]
  obtain ⟨hFi, hFmean⟩ := coarseCorrector_weightedFlux_expectation Q i φ hid hw hwi
  obtain ⟨hUi, hUmean⟩ := coarseCorrector_gaussianAffineGradient_expectation Q i φ hid z hr
  let T : Vec d →L[ℝ] Vec d := (Matrix.toLin' A).toContinuousLinearMap
  have hAi := T.integrable_comp hUi
  constructor
  · exact hFi.sub hAi
  · change (∫ a, _ - T (_) ∂actualCoefficientLaw Q) = _
    rw [integral_sub hFi hAi, T.integral_comp_comm hUi, hUmean, hFmean, hmass, one_smul]
    rfl


/-- The source's Frobenius matrix size controls every signed entry. -/
theorem coarseMatrix_entry_le_size {d : ℕ} (M : Mat d) (i j : Fin d) :
    |M i j| ≤ coarsenedMatrixSize M := by
  unfold coarsenedMatrixSize
  apply Real.abs_le_sqrt
  calc
    (M i j) ^ 2 ≤ ∑ k : Fin d, (M i k) ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (M i k)) (Finset.mem_univ j)
    _ ≤ ∑ l : Fin d, ∑ k : Fin d, (M l k) ^ 2 :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun k _ => sq_nonneg (M l k))
        (Finset.mem_univ i)

/-- The source's matrix size controls its action in the coordinate norm. -/
theorem coarseMatrix_mulVec_norm_le_size {d : ℕ} (M : Mat d) (v : Vec d) :
    ‖M.mulVec v‖ ≤ (d : ℝ) * coarsenedMatrixSize M * ‖v‖ :=
  coarseMatrix_mulVec_norm_le M (Real.sqrt_nonneg _) (coarseMatrix_entry_le_size M) v

/-- Taking expectations in the actual affine A₁ residual bounds the deterministic
homogenized-column mismatch by two ordinary Cauchy–Schwarz products. The four
scalar L² assumptions are explicit support interfaces for stochastic estimates. -/
theorem coarseCorrector_gaussian_matrixMismatch_le
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    (A : Mat d) (z : Vec d) {r : ℝ} (hr : 0 < r)
    (hN : MemLp (fun a => Real.sqrt (∫ y, heatKernel z r y *
      euclideanNorm (unitVector i + φ.grad a y) ^ 2)) 2 (actualCoefficientLaw Q))
    (hD : MemLp (fun a => normalizedCoarseFluxDefect a A z r) 2 (actualCoefficientLaw Q))
    (hB : MemLp (fun a => coarsenedMatrixSize (coarsenedCoefficient a A z r))
      2 (actualCoefficientLaw Q))
    (hU : MemLp (fun a => ‖∫ y, heatKernel z r y • (unitVector i + φ.grad a y)‖)
      2 (actualCoefficientLaw Q)) :
    ‖ellipticityScale L • (homogenizedCoefficient Q).mulVec (unitVector i) -
      A.mulVec (unitVector i)‖ ≤
      Real.sqrt (∫ a, (Real.sqrt (∫ y, heatKernel z r y *
        euclideanNorm (unitVector i + φ.grad a y) ^ 2)) ^ 2 ∂actualCoefficientLaw Q) *
      Real.sqrt (∫ a, (normalizedCoarseFluxDefect a A z r) ^ 2 ∂actualCoefficientLaw Q) +
      (d : ℝ) * (Real.sqrt (∫ a, (coarsenedMatrixSize (coarsenedCoefficient a A z r)) ^ 2
        ∂actualCoefficientLaw Q) *
        Real.sqrt (∫ a, ‖∫ y, heatKernel z r y • (unitVector i + φ.grad a y)‖ ^ 2
          ∂actualCoefficientLaw Q)) := by
  let P := actualCoefficientLaw Q
  let N := fun a => Real.sqrt (∫ y, heatKernel z r y *
    euclideanNorm (unitVector i + φ.grad a y) ^ 2)
  let D := fun a : Coefficient d (AKMUpperEllipticity L) => normalizedCoarseFluxDefect a A z r
  let B := fun a : Coefficient d (AKMUpperEllipticity L) =>
    coarsenedMatrixSize (coarsenedCoefficient a A z r)
  let U := fun a => ∫ y, heatKernel z r y • (unitVector i + φ.grad a y)
  let R := fun a => (∫ y, heatKernel z r y • (a y).mulVec (unitVector i + φ.grad a y)) -
    A.mulVec (U a)
  obtain ⟨_, hmean⟩ := coarseCorrector_gaussianFluxResidual_expectation Q i φ hid A z hr
  have hi : ∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y *
      euclideanNorm (unitVector i + φ.grad a y) ^ 2) := by
    filter_upwards [coarseCorrector_gaussianAffine_integrable Q i φ hid z hr] with a ha
    exact ha.1
  have hres := coarseCorrector_affine_fluxResidual_le
    (by unfold AKMUpperEllipticity; exact mul_self_nonneg _) i φ A z hr hi
  have hpoint : ∀ᵐ a ∂P, ‖R a‖ ≤ ‖N a‖ * ‖D a‖ +
      (d : ℝ) * (‖B a‖ * ‖‖U a‖‖) := by
    filter_upwards [hres] with a ha
    let M := coarsenedCoefficient a A z r
    let F := ∫ y, heatKernel z r y • (a y).mulVec (unitVector i + φ.grad a y)
    have heq : R a = (F - (A + M).mulVec (U a)) + M.mulVec (U a) := by
      dsimp only [R]
      rw [Matrix.add_mulVec]
      abel
    have hna : 0 ≤ N a := Real.sqrt_nonneg _
    have hba : 0 ≤ B a := Real.sqrt_nonneg _
    calc
      ‖R a‖ ≤ ‖F - (A + M).mulVec (U a)‖ + ‖M.mulVec (U a)‖ := by
        rw [heq]
        exact norm_add_le _ _
      _ ≤ N a * D a + (d : ℝ) * B a * ‖U a‖ :=
        add_le_add ((Calculus.S1.norm_le_euclideanNorm _).trans ha) (coarseMatrix_mulVec_norm_le_size M (U a))
      _ ≤ ‖N a‖ * ‖D a‖ + (d : ℝ) * (‖B a‖ * ‖‖U a‖‖) := by
        simp only [Real.norm_of_nonneg hna, Real.norm_of_nonneg hba, norm_norm]
        exact add_le_add (mul_le_mul_of_nonneg_left (le_abs_self _) hna) (le_of_eq (by ring))
  have hcs (f g : Coefficient d (AKMUpperEllipticity L) → ℝ)
      (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
      (∫ a, ‖f a‖ * ‖g a‖ ∂P) ≤
        Real.sqrt (∫ a, (f a) ^ 2 ∂P) * Real.sqrt (∫ a, (g a) ^ 2 ∂P) := by
    have hh := integral_mul_norm_le_Lp_mul_Lq (p := (2 : ℝ)) (q := (2 : ℝ))
      Real.HolderConjugate.two_two (by simpa using hf) (by simpa using hg)
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs] using hh
  have hdom := (hN.norm.integrable_mul hD.norm).add
    ((hB.norm.integrable_mul hU.norm).const_mul (d : ℝ))
  rw [← hmean]
  calc
    ‖∫ a, R a ∂P‖ ≤ ∫ a, ‖R a‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ a, ‖N a‖ * ‖D a‖ + (d : ℝ) * (‖B a‖ * ‖‖U a‖‖) ∂P :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hdom hpoint
    _ = (∫ a, ‖N a‖ * ‖D a‖ ∂P) +
        (d : ℝ) * (∫ a, ‖B a‖ * ‖‖U a‖‖ ∂P) := by
      calc
        _ = (∫ a, ‖N a‖ * ‖D a‖ ∂P) +
            (∫ a, (d : ℝ) * (‖B a‖ * ‖‖U a‖‖) ∂P) :=
          integral_add (hN.norm.integrable_mul hD.norm)
            ((hB.norm.integrable_mul hU.norm).const_mul _)
        _ = _ := by rw [integral_const_mul]
    _ ≤ _ := add_le_add (hcs N D hN hD)
      (mul_le_mul_of_nonneg_left (hcs B (fun a => ‖U a‖) hB hU) (Nat.cast_nonneg d))


/-- The normalized supremum is nonnegative, including a possibly empty
normalizing class, since every member is a Euclidean norm. -/
theorem coarseFluxDefect_nonneg {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (A : Mat d) (z : Vec d) (r : ℝ) : 0 ≤ normalizedCoarseFluxDefect a A z r := by
  apply Real.sSup_nonneg
  rintro e ⟨w, _, _, rfl⟩
  exact Real.sqrt_nonneg _

/-- A nonnegative source O_s variable has genuine L² membership and the
explicit root-second-moment bound; measurability comes from the source bound. -/
theorem coarseNonnegative_osBound_L2 {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {s θ : ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (h : OsBound P X s θ) :
    MemLp X 2 P ∧ Real.sqrt (∫ ω, (X ω) ^ 2 ∂P) ≤
      Real.sqrt (2 * (2 / s) ^ (2 / s)) * θ := by
  have ha : OsBound P (fun ω => |X ω|) s θ := by
    simpa only [abs_of_nonneg (hX _)] using h
  exact ⟨AKM.memLp_two_of_osBound ha h.1.aestronglyMeasurable,
    by simpa only [sq_abs] using AKM.sqrt_integral_sq_le_of_osBound ha⟩

/-- The approved source coarsening input gives ordinary L² membership and
root-second-moment rates for the literal matrix size and normalized defect.
One constant precedes the coefficient law, source objects, center, and scale. -/
theorem coarseSource_L2_estimates (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (hK : 1 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient d K), LawHypotheses P →
      ∀ S : SourceObjects P, ∀ (z : Vec d) (r : ℝ), 1 ≤ r →
      MemLp (fun a => coarsenedMatrixSize (coarsenedCoefficient a S.homogenized z r)) 2 P ∧
      MemLp (fun a => normalizedCoarseFluxDefect a S.homogenized z r) 2 P ∧
      Real.sqrt (∫ a, (coarsenedMatrixSize (coarsenedCoefficient a S.homogenized z r)) ^ 2 ∂P) ≤
        C * r ^ (-(d : ℝ) / 2) ∧
      Real.sqrt (∫ a, (normalizedCoarseFluxDefect a S.homogenized z r) ^ 2 ∂P) ≤
        C * r ^ (-(d : ℝ)) := by
  obtain ⟨C₀, hC₀, hs⟩ := External.akm_coarsened_coefficient_estimates
    d hd K 1 hK (by norm_num) (by norm_num)
  let b := Real.sqrt (2 * (2 / (1 : ℝ)) ^ (2 / (1 : ℝ)))
  let t := Real.sqrt (2 * (2 / ((1 : ℝ) / 2)) ^ (2 / ((1 : ℝ) / 2)))
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  refine ⟨(b + t + 1) * C₀, mul_pos (by positivity) hC₀, ?_⟩
  intro P hP S z r hr
  obtain ⟨hBs, hDs⟩ := hs P hP S z r hr
  obtain ⟨hBm, hBn⟩ := coarseNonnegative_osBound_L2
    (fun _ => Real.sqrt_nonneg _) hBs
  obtain ⟨hDm, hDn⟩ := coarseNonnegative_osBound_L2
    (fun a => coarseFluxDefect_nonneg a S.homogenized z r) hDs
  refine ⟨hBm, hDm, hBn.trans ?_, hDn.trans ?_⟩
  · change b * (C₀ * r ^ (-(d : ℝ) / 2)) ≤ _
    have hp : 0 ≤ C₀ * r ^ (-(d : ℝ) / 2) :=
      mul_nonneg hC₀.le (Real.rpow_nonneg (by linarith) _)
    have hh := mul_le_mul_of_nonneg_right (show b ≤ b + t + 1 by linarith) hp
    simpa only [mul_assoc] using hh
  · change t * (C₀ * r ^ (-(d : ℝ))) ≤ _
    have hp : 0 ≤ C₀ * r ^ (-(d : ℝ)) :=
      mul_nonneg hC₀.le (Real.rpow_nonneg (by linarith) _)
    have hh := mul_le_mul_of_nonneg_right (show t ≤ b + t + 1 by linarith) hp
    simpa only [mul_assoc] using hh

/-- Removing the unit-energy normalization gives a uniform weighted-average
bound, including when the weighted energy vanishes. -/
theorem coarseWeightedIntegral_norm_le_sqrt_energy {d : ℕ}
    (w : Vec d → ℝ) (v : Vec d → Vec d)
    (hw : ∀ x, 0 ≤ w x) (hwi : Integrable w) (hmu : ∫ x, w x = 1)
    (hi : Integrable (fun x => w x * euclideanNorm (v x) ^ 2)) :
    ‖∫ x, w x • v x‖ ≤
      2 * Real.sqrt (∫ x, w x * euclideanNorm (v x) ^ 2) := by
  let N := Real.sqrt (∫ x, w x * euclideanNorm (v x) ^ 2)
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have heps (ε : ℝ) (hε : 0 < ε) : ‖∫ x, w x • v x‖ ≤ 2 * (N + ε) := by
    let c := (N + ε)⁻¹
    have hp : 0 < N + ε := add_pos_of_nonneg_of_pos hN hε
    have hc : 0 < c := inv_pos.mpr hp
    have hci : Integrable (fun x => w x * euclideanNorm (c • v x) ^ 2) := by
      apply (hi.const_mul (c ^ 2)).congr
      apply ae_of_all
      intro x
      simp only [TimeChange.euclideanNorm_smul, mul_pow, sq_abs]
      ring
    have hsize : Real.sqrt (∫ x, w x * euclideanNorm (c • v x) ^ 2) = c * N := by
      have hf : (fun x => w x * euclideanNorm (c • v x) ^ 2) =
          (fun x => c ^ 2 * (w x * euclideanNorm (v x) ^ 2)) := by
        funext x
        simp only [TimeChange.euclideanNorm_smul, mul_pow, sq_abs]
        ring
      rw [hf, integral_const_mul, Real.sqrt_mul (sq_nonneg c),
        Real.sqrt_sq_eq_abs, abs_of_pos hc]
    apply coarseWeightedIntegral_norm_le w (fun x => c • v x) v hp.le hw hwi hmu hci
    · rw [hsize]
      exact (inv_mul_le_one₀ hp).2 (by linarith)
    · intro x
      rw [TimeChange.euclideanNorm_smul, abs_of_pos hc]
      have hcancel : (N + ε) * c = 1 := mul_inv_cancel₀ hp.ne'
      calc
        ‖v x‖ ≤ euclideanNorm (v x) := Calculus.S1.norm_le_euclideanNorm _
        _ = (N + ε) * (c * euclideanNorm (v x)) := by rw [← mul_assoc, hcancel, one_mul]
  by_contra h
  have hgap : 0 < ‖∫ x, w x • v x‖ - 2 * N := sub_pos.mpr (lt_of_not_ge h)
  have hh := heps ((‖∫ x, w x • v x‖ - 2 * N) / 4) (div_pos hgap (by norm_num))
  linarith only [hh, hgap]

/-- An integrable averaged energy controls both the energy square root and
weighted vector average in probability L². -/
theorem coarseWeightedEnergy_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {μ : Measure Ω} {w : Vec d → ℝ}
    (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y) (hwi : Integrable w)
    (hmu : ∫ y, w y = 1) (v : Ω → Vec d → Vec d)
    (hv : Measurable (Function.uncurry v))
    (hsp : ∀ᵐ ω ∂μ, Integrable (fun y => w y * euclideanNorm (v ω y) ^ 2))
    (hE : Integrable (fun ω => ∫ y, w y * euclideanNorm (v ω y) ^ 2) μ) :
    MemLp (fun ω => Real.sqrt (∫ y, w y * euclideanNorm (v ω y) ^ 2)) 2 μ ∧
    MemLp (fun ω => ‖∫ y, w y • v ω y‖) 2 μ := by
  have hn : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hm : Measurable (fun ω => ∫ y, w y * euclideanNorm (v ω y) ^ 2) :=
    ((hw.comp measurable_snd).mul ((hn.measurable.comp hv).pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  have hnonneg (ω : Ω) : 0 ≤ ∫ y, w y * euclideanNorm (v ω y) ^ 2 :=
    integral_nonneg (fun y => mul_nonneg (hw0 y) (sq_nonneg _))
  have hN : MemLp (fun ω => Real.sqrt (∫ y, w y * euclideanNorm (v ω y) ^ 2)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (hm.sqrt.aestronglyMeasurable)).2
    simpa only [Real.sq_sqrt (hnonneg _)] using hE
  refine ⟨hN, ?_⟩
  have hUm : Measurable (fun ω => ‖∫ y, w y • v ω y‖) :=
    ((hw.comp measurable_snd).smul hv).stronglyMeasurable.integral_prod_right'.measurable.norm
  apply (hN.const_mul 2).mono' hUm.aestronglyMeasurable
  filter_upwards [hsp] with ω hω
  simpa only [Real.norm_eq_abs, abs_norm] using
    coarseWeightedIntegral_norm_le_sqrt_energy w (v ω) hw0 hwi hmu hω

/-- Canonical identification supplies both L² inputs for the actual affine
corrector's weighted average without a new stochastic premise. -/
theorem coarseCorrector_weightedAffine_memLp_two
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    {w : Vec d → ℝ} (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hwi : Integrable w) (hmu : ∫ y, w y = 1) :
    MemLp (fun a => Real.sqrt (∫ y, w y *
      euclideanNorm (unitVector i + φ.grad a y) ^ 2)) 2 (actualCoefficientLaw Q) ∧
    MemLp (fun a => ‖∫ y, w y • (unitVector i + φ.grad a y)‖)
      2 (actualCoefficientLaw Q) := by
  obtain ⟨hsp, hE⟩ := coarseCorrector_weightedAffineEnergy_integrable Q i φ hid hw hwi
  exact coarseWeightedEnergy_memLp_two hw hw0 hwi hmu
    (fun a y => unitVector i + φ.grad a y)
    (measurable_const.add φ.measurable_grad) hsp hE

/-- Stationarity identifies the actual weighted affine energy with the
canonical one-point energy, independently of the shape of the weight. -/
theorem coarseCorrector_weightedAffineEnergy_expectation
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    {w : Vec d → ℝ} (hw : Measurable w) (hwi : Integrable w) :
    (∫ a, ∫ y, w y * euclideanNorm (unitVector i + φ.grad a y) ^ 2
      ∂volume ∂actualCoefficientLaw Q) =
      (∫ y, w y) * ∫ ω, ‖correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω‖ ^ 2
          ∂reducedEnvironmentLaw Q := by
  let G := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  let F : FieldPair d → ℝ := fun ω => ‖correctorUnitVector i + G ω‖ ^ 2
  have hXm : Measurable (fun ω : FieldPair d => correctorUnitVector i + G ω) :=
    measurable_const.add (Lp.stronglyMeasurable G).measurable
  have hF : Measurable F := hXm.norm.pow_const 2
  have hX : MemLp (fun ω => correctorUnitVector i + G ω) 2 (reducedEnvironmentLaw Q) :=
    (memLp_const (correctorUnitVector i)).add (Lp.memLp G)
  have hFi : Integrable F (reducedEnvironmentLaw Q) :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX
  have hn (v : EuclideanSpace ℝ (Fin d)) : euclideanNorm v.ofLp = ‖v‖ := by
    simpa only [WithLp.toLp_ofLp] using TimeChange.euclideanNorm_eq_norm_toLp v.ofLp
  let q := fun a : Coefficient d (AKMUpperEllipticity L) =>
    ∫ y, w y * euclideanNorm (unitVector i + φ.grad a y) ^ 2
  have hnorm : Continuous (fun v : Vec d => euclideanNorm v) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hq : Measurable q :=
    ((hw.comp measurable_snd).mul ((hnorm.measurable.comp
      (measurable_const.add φ.measurable_grad)).pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  have heq : ∀ᵐ ω ∂physicalReferenceLaw Q,
      q (project (r₀ := r₀) Q.ellipticity_parameter ω) =
      ∫ y, w y * F (translate (r₀ • y) (reduce ω.1)) := by
    filter_upwards [hid] with ω hω
    apply integral_congr_ae
    filter_upwards [hω] with y hy
    dsimp only [F, G]
    rw [hy, hn]
  have hm := integral_map (μ := physicalReferenceLaw Q)
    (measurable_project (r₀ := r₀) Q.ellipticity_parameter).aemeasurable
    (hq.aestronglyMeasurable (μ := actualCoefficientLaw Q))
  change (∫ a, q a ∂actualCoefficientLaw Q) = _ at hm ⊢
  rw [hm, integral_congr_ae heq]
  have hEmb : MeasurableEmbedding (fun ω : PhysicalField d L => reduce ω.1) :=
    (Probability.measurableEmbedding_reduce d).comp
      (MeasurableEmbedding.subtype_coe (Sharpness.measurableSet_isRegular_fieldPair L))
  have hσ : Measurable (fun y : Vec d => r₀ • y) :=
    (continuous_id.const_smul r₀).measurable
  rw [(measurePreserving_physicalReduction Q).integral_comp hEmb
    (fun ω => ∫ y, w y * F (translate (r₀ • y) ω))]
  simpa only [smul_eq_mul, F, G] using
    integral_weighted_stationary (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) volume hF hFi hw hwi hσ

/-- The second moment of a weighted vector average is controlled by four times
the averaged energy; the constant is independent of the weight and scale. -/
theorem coarseWeightedIntegral_secondMoment_le {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {μ : Measure Ω} {w : Vec d → ℝ}
    (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y) (hwi : Integrable w)
    (hmu : ∫ y, w y = 1) (v : Ω → Vec d → Vec d)
    (hv : Measurable (Function.uncurry v))
    (hsp : ∀ᵐ ω ∂μ, Integrable (fun y => w y * euclideanNorm (v ω y) ^ 2))
    (hE : Integrable (fun ω => ∫ y, w y * euclideanNorm (v ω y) ^ 2) μ) :
    (∫ ω, ‖∫ y, w y • v ω y‖ ^ 2 ∂μ) ≤
      4 * ∫ ω, ∫ y, w y * euclideanNorm (v ω y) ^ 2 ∂volume ∂μ := by
  have hU := (coarseWeightedEnergy_memLp_two hw hw0 hwi hmu v hv hsp hE).2
  have hUi := (memLp_two_iff_integrable_sq hU.aestronglyMeasurable).mp hU
  rw [← integral_const_mul]
  apply integral_mono_ae hUi (hE.const_mul 4)
  filter_upwards [hsp] with ω hω
  have hnonneg : 0 ≤ ∫ y, w y * euclideanNorm (v ω y) ^ 2 :=
    integral_nonneg (fun y => mul_nonneg (hw0 y) (sq_nonneg _))
  have hh := (sq_le_sq₀ (norm_nonneg (∫ y, w y • v ω y))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _))).2
      (coarseWeightedIntegral_norm_le_sqrt_energy w (v ω) hw0 hwi hmu hω)
  simpa only [mul_pow, Real.sq_sqrt hnonneg, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh

/-- Both second moments needed for identifying the homogenized matrix have
bounds independent of the center and scale of any probability weight. -/
theorem coarseCorrector_weightedAffine_secondMoments
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    {w : Vec d → ℝ} (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hwi : Integrable w) (hmu : ∫ y, w y = 1) :
    let E := ∫ ω, ‖correctorUnitVector i + (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω‖ ^ 2
        ∂reducedEnvironmentLaw Q
    Real.sqrt (∫ a, (Real.sqrt (∫ y, w y *
      euclideanNorm (unitVector i + φ.grad a y) ^ 2)) ^ 2 ∂actualCoefficientLaw Q) =
      Real.sqrt E ∧
    Real.sqrt (∫ a, ‖∫ y, w y • (unitVector i + φ.grad a y)‖ ^ 2
      ∂actualCoefficientLaw Q) ≤ 2 * Real.sqrt E := by
  dsimp only
  have he := coarseCorrector_weightedAffineEnergy_expectation Q i φ hid hw hwi
  rw [hmu, one_mul] at he
  constructor
  · congr 1
    calc
      _ = ∫ a, ∫ y, w y * euclideanNorm (unitVector i + φ.grad a y) ^ 2
          ∂volume ∂actualCoefficientLaw Q := by
        apply integral_congr_ae
        apply ae_of_all
        intro a
        exact Real.sq_sqrt (integral_nonneg
          (fun y => mul_nonneg (hw0 y) (sq_nonneg _)))
      _ = _ := he
  · obtain ⟨hsp, hE⟩ := coarseCorrector_weightedAffineEnergy_integrable Q i φ hid hw hwi
    have hh := coarseWeightedIntegral_secondMoment_le hw hw0 hwi hmu
      (fun a y => unitVector i + φ.grad a y)
      (measurable_const.add φ.measurable_grad) hsp hE
    rw [he] at hh
    have hs := Real.sqrt_le_sqrt hh
    simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by norm_num] using hs

/-- Vanishing source coarse errors identify each source homogenized column
with the actual canonical mean-flux column. No source-corrector identification
or large-scale oscillation premise is needed. -/
theorem coarseCorrector_sourceHomogenized_column
    {d : ℕ} (hd : 2 ≤ d) {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    (S : SourceObjects (actualCoefficientLaw Q)) :
    ellipticityScale L • (homogenizedCoefficient Q).mulVec (unitVector i) =
      S.homogenized.mulVec (unitVector i) := by
  let e := Real.sqrt (∫ ω, ‖correctorUnitVector i + (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω‖ ^ 2
      ∂reducedEnvironmentLaw Q)
  have he : 0 ≤ e := Real.sqrt_nonneg _
  obtain ⟨C, hC, hs⟩ := coarseSource_L2_estimates d hd (AKMUpperEllipticity L)
    (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  have hb (r : ℝ) (hr : 1 ≤ r) :
      ‖ellipticityScale L • (homogenizedCoefficient Q).mulVec (unitVector i) -
        S.homogenized.mulVec (unitVector i)‖ ≤
      e * (C * r ^ (-(d : ℝ))) + (d : ℝ) * (C * r ^ (-(d : ℝ) / 2) * (2 * e)) := by
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hw : Measurable (heatKernel (0 : Vec d) r) :=
      ((Correctors.continuous_euclideanHeatKernel (r ^ 2)).comp
        (continuous_id.sub continuous_const)).measurable
    have hw0 (y : Vec d) : 0 ≤ heatKernel (0 : Vec d) r y :=
      Correctors.euclideanHeatKernel_nonneg (sq_nonneg r) (y - 0)
    have hwi : Integrable (heatKernel (0 : Vec d) r) :=
      (Correctors.integrable_euclideanHeatKernel (sq_pos_of_pos hr0)).comp_sub_right 0
    have hmass : (∫ y, heatKernel (0 : Vec d) r y) = 1 := by
      change (∫ y, Correctors.euclideanHeatKernel (r ^ 2) (y - 0)) = 1
      rw [integral_sub_right_eq_self,
        Correctors.integral_euclideanHeatKernel (sq_pos_of_pos hr0)]
    obtain ⟨hN, hU⟩ := coarseCorrector_weightedAffine_memLp_two Q i φ hid hw hw0 hwi hmass
    obtain ⟨hNs, hUs⟩ := coarseCorrector_weightedAffine_secondMoments Q i φ hid hw hw0 hwi hmass
    obtain ⟨hB, hD, hBs, hDs⟩ := hs (actualCoefficientLaw Q)
      (lawHypotheses_actualCoefficientLaw Q) S 0 r hr
    have hm := coarseCorrector_gaussian_matrixMismatch_le Q i φ hid S.homogenized 0 hr0
      hN hD hB hU
    rw [hNs] at hm
    apply hm.trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left hDs he
    · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      exact mul_le_mul hBs hUs (Real.sqrt_nonneg _)
        (mul_nonneg hC.le (Real.rpow_nonneg hr0.le _))
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have ht₁ := tendsto_rpow_neg_atTop hd0
  have ht₂ : Filter.Tendsto (fun r : ℝ => r ^ (-(d : ℝ) / 2))
      Filter.atTop (nhds 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (half_pos hd0)
  have ht := ((ht₁.const_mul C).const_mul e).add
    ((((ht₂.const_mul C).mul_const (2 * e))).const_mul (d : ℝ))
  simp only [mul_zero, zero_mul, add_zero] at ht
  have hz := le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Filter.eventually_atTop.2 ⟨1, hb⟩)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

/-- Every genuine source basis has the same homogenized matrix as the
canonical construction, with the literal coefficient normalization. -/
theorem coarseSource_homogenized_eq {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (S : SourceObjects (actualCoefficientLaw Q)) :
    S.homogenized = ellipticityScale L • homogenizedCoefficient Q := by
  ext j i
  obtain ⟨φ, hid, _⟩ := exists_coarseCorrector_global_identification_meanFlux Q i
  have h := congrFun (coarseCorrector_sourceHomogenized_column Fact.out Q i φ hid S) j
  simpa [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, mul_ite, smul_eq_mul]
    using h.symm

/-- A nonnegative source stretched-exponential variable has an explicit
fourth-moment norm bound and genuine L⁴ membership. -/
theorem coarseNonnegative_osBound_L4 {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {s θ : ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (h : OsBound P X s θ) :
    MemLp X 4 P ∧ Real.sqrt (Real.sqrt (∫ ω, (X ω) ^ 4 ∂P)) ≤
      Real.sqrt (Real.sqrt (2 * (4 / s) ^ (4 / s))) * θ := by
  have hs : 0 < s := h.2.1
  have hθ : 0 < θ := h.2.2.1
  have ha : OsBound P (fun ω => |X ω|) s θ := by
    simpa only [abs_of_nonneg (hX _)] using h
  have hm := AKM.abs_moment_le_of_osBound ha (show (0 : ℝ) < 4 by norm_num)
  simp only [Real.rpow_ofNat, abs_of_nonneg (hX _)] at hm
  have hi : Integrable (fun ω => X ω ^ 4) P := by
    refine ⟨h.1.aestronglyMeasurable.pow 4, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => pow_nonneg (hX ω) 4)]
    exact lt_of_le_of_lt hm ENNReal.ofReal_lt_top
  constructor
  · apply (integrable_norm_rpow_iff h.1.aestronglyMeasurable
      (by norm_num : (4 : ENNReal) ≠ 0) (by norm_num : (4 : ENNReal) ≠ ⊤)).mp
    simpa only [show (4 : ENNReal).toReal = (4 : ℝ) by norm_num,
      Real.rpow_ofNat, Real.norm_eq_abs,
      abs_of_nonneg (hX _)] using hi
  · have hC : 0 ≤ 2 * (4 / s) ^ (4 / s) := by positivity
    have hbound : (∫ ω, X ω ^ 4 ∂P) ≤ 2 * θ ^ 4 * (4 / s) ^ (4 / s) := by
      rw [integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun ω => pow_nonneg (hX ω) 4) hi.aestronglyMeasurable]
      have hc : 0 ≤ 2 * θ ^ 4 * (4 / s) ^ (4 / s) := by positivity
      simpa only [ENNReal.toReal_ofReal hc] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    calc
      Real.sqrt (Real.sqrt (∫ ω, X ω ^ 4 ∂P)) ≤
          Real.sqrt (Real.sqrt (2 * θ ^ 4 * (4 / s) ^ (4 / s))) :=
        Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hbound)
      _ = _ := by
        rw [show 2 * θ ^ 4 * (4 / s) ^ (4 / s) =
          (2 * (4 / s) ^ (4 / s)) * (θ ^ 2) ^ 2 by ring,
          Real.sqrt_mul hC, Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg θ),
          Real.sqrt_mul (Real.sqrt_nonneg _), Real.sqrt_sq_eq_abs,
          abs_of_pos h.2.2.1]

/-- The literal source matrix and flux defect have L⁴ rates with one constant
preceding all laws, source objects, centers, and scales. -/
theorem coarseSource_L4_estimates (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (hK : 1 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient d K), LawHypotheses P →
      ∀ S : SourceObjects P, ∀ (z : Vec d) (r : ℝ), 1 ≤ r →
      MemLp (fun a => coarsenedMatrixSize (coarsenedCoefficient a S.homogenized z r)) 4 P ∧
      MemLp (fun a => normalizedCoarseFluxDefect a S.homogenized z r) 4 P ∧
      Real.sqrt (Real.sqrt (∫ a,
        (coarsenedMatrixSize (coarsenedCoefficient a S.homogenized z r)) ^ 4 ∂P)) ≤
          C * r ^ (-(d : ℝ) / 2) ∧
      Real.sqrt (Real.sqrt (∫ a,
        (normalizedCoarseFluxDefect a S.homogenized z r) ^ 4 ∂P)) ≤
          C * r ^ (-(d : ℝ)) := by
  obtain ⟨C₀, hC₀, hs⟩ := External.akm_coarsened_coefficient_estimates
    d hd K 1 hK (by norm_num) (by norm_num)
  let b := Real.sqrt (Real.sqrt (2 * (4 / (1 : ℝ)) ^ (4 / (1 : ℝ))))
  let t := Real.sqrt (Real.sqrt (2 * (4 / ((1 : ℝ) / 2)) ^ (4 / ((1 : ℝ) / 2))))
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  refine ⟨(b + t + 1) * C₀, mul_pos (by positivity) hC₀, ?_⟩
  intro P hP S z r hr
  obtain ⟨hBs, hDs⟩ := hs P hP S z r hr
  obtain ⟨hBm, hBn⟩ := coarseNonnegative_osBound_L4
    (fun _ => Real.sqrt_nonneg _) hBs
  obtain ⟨hDm, hDn⟩ := coarseNonnegative_osBound_L4
    (fun a => coarseFluxDefect_nonneg a S.homogenized z r) hDs
  refine ⟨hBm, hDm, hBn.trans ?_, hDn.trans ?_⟩
  · change b * (C₀ * r ^ (-(d : ℝ) / 2)) ≤ _
    have hp : 0 ≤ C₀ * r ^ (-(d : ℝ) / 2) :=
      mul_nonneg hC₀.le (Real.rpow_nonneg (by linarith) _)
    have hh := mul_le_mul_of_nonneg_right (show b ≤ b + t + 1 by linarith) hp
    simpa only [mul_assoc] using hh
  · change t * (C₀ * r ^ (-(d : ℝ))) ≤ _
    have hp : 0 ≤ C₀ * r ^ (-(d : ℝ)) :=
      mul_nonneg hC₀.le (Real.rpow_nonneg (by linarith) _)
    have hh := mul_le_mul_of_nonneg_right (show t ≤ b + t + 1 by linarith) hp
    simpa only [mul_assoc] using hh

/-- Source rates transfer to the canonical homogenized load with no source
identification hypothesis. The constant precedes the actual law. -/
theorem coarseActual_L4_estimates (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d L r₀),
      ∀ (z : Vec d) (r : ℝ), 1 ≤ r →
      MemLp (fun a => coarsenedMatrixSize (coarsenedCoefficient a
        (ellipticityScale L • homogenizedCoefficient Q) z r)) 4 (actualCoefficientLaw Q) ∧
      MemLp (fun a => normalizedCoarseFluxDefect a
        (ellipticityScale L • homogenizedCoefficient Q) z r) 4 (actualCoefficientLaw Q) ∧
      Real.sqrt (Real.sqrt (∫ a, (coarsenedMatrixSize (coarsenedCoefficient a
        (ellipticityScale L • homogenizedCoefficient Q) z r)) ^ 4
          ∂actualCoefficientLaw Q)) ≤ C * r ^ (-(d : ℝ) / 2) ∧
      Real.sqrt (Real.sqrt (∫ a, (normalizedCoarseFluxDefect a
        (ellipticityScale L • homogenizedCoefficient Q) z r) ^ 4
          ∂actualCoefficientLaw Q)) ≤ C * r ^ (-(d : ℝ)) := by
  have hK := one_lt_AKMUpperEllipticity hL
  obtain ⟨C, hC, hs⟩ := coarseSource_L4_estimates d hd (AKMUpperEllipticity L) hK
  refine ⟨C, hC, ?_⟩
  intro r₀ Q z r hr
  obtain ⟨_, _, hex⟩ := External.akm_averaged_corrector.1 d hd
    (AKMUpperEllipticity L) 1 hK (by norm_num) (by norm_num)
  obtain ⟨S, _⟩ := hex (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q)
  let : Fact (2 ≤ d) := ⟨hd⟩
  simpa only [coarseSource_homogenized_eq Q S] using
    hs (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q) S z r hr

/-- Deterministic spatial rescaling preserves the canonical Gaussian energy
moment bound, because every translated marginal has the original law. -/
theorem coarseCorrector_rescaledHeatKernel_energy_moment_le
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    {p M : ℝ} (hp : 2 ≤ p) (hM : 0 ≤ M)
    (hm : MemLp (fun ω => correctorGradient Q i ω) (ENNReal.ofReal p) (reducedLaw Q))
    (hb : eLpNorm (fun ω => correctorGradient Q i ω) (ENNReal.ofReal p)
      (reducedLaw Q) ≤ ENNReal.ofReal M) (c : ℝ) (z : Vec d) {r : ℝ} (hr : 0 < r) :
    (∀ᵐ ω ∂reducedLaw Q, Integrable (fun x => heatKernel z r x *
      euclideanNorm (unitVector i + WithLp.ofLp (correctorGradient Q i (translate (c • x) ω))) ^ 2)) ∧
    MemLp (fun ω => Real.sqrt (∫ x, heatKernel z r x *
      euclideanNorm (unitVector i + WithLp.ofLp (correctorGradient Q i (translate (c • x) ω))) ^ 2))
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    eLpNorm (fun ω => Real.sqrt (∫ x, heatKernel z r x *
      euclideanNorm (unitVector i + WithLp.ofLp (correctorGradient Q i (translate (c • x) ω))) ^ 2))
      (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal (1 + M) := by
  have hprob : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let a : EuclideanSpace ℝ (Fin d) := Correctors.correctorUnitVector i
  have ha : ‖a‖ = 1 := by simp [a, Correctors.correctorUnitVector]
  let g : FieldPair d × Vec d → EuclideanSpace ℝ (Fin d) :=
    fun v => a + correctorGradient Q i (translate (c • v.2) v.1)
  have hg : Measurable g := measurable_const.add ((measurable_correctorGradient_orbit Q i).comp
    (measurable_fst.prodMk (show Measurable
      (fun v : FieldPair d × Vec d => c • v.2) by fun_prop)))
  have hcol (x : Vec d) :
      MemLp (fun ω => g (ω, x)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (fun ω => g (ω, x)) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal (1 + M) := by
    have ht := measurePreserving_translate (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) (c • x)
    have hmx := hm.comp_measurePreserving ht
    have hx : eLpNorm (fun ω => correctorGradient Q i (translate (c • x) ω))
        (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M :=
      (eLpNorm_comp_measurePreserving hm.aestronglyMeasurable ht).trans_le hb
    refine ⟨(memLp_const a).add hmx, ?_⟩
    calc
      _ ≤ eLpNorm (fun _ : FieldPair d => a) (ENNReal.ofReal p) (reducedLaw Q) +
          eLpNorm (fun ω => correctorGradient Q i (translate (c • x) ω))
            (ENNReal.ofReal p) (reducedLaw Q) :=
        eLpNorm_add_le (by
          simpa only [ENNReal.ofReal_one] using
            ENNReal.ofReal_le_ofReal (show 1 ≤ p by linarith))
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal M := by
        gcongr
        rw [eLpNorm_const' a (ENNReal.ofReal_ne_zero_iff.mpr (by linarith : 0 < p))
          ENNReal.ofReal_ne_top]
        simp [← ofReal_norm, ha]
      _ = _ := (ENNReal.ofReal_add (by norm_num) hM).symm
  have heq (ω : FieldPair d) (x : Vec d) :
      euclideanNorm (unitVector i + WithLp.ofLp (correctorGradient Q i (translate (c • x) ω))) =
        ‖g (ω, x)‖ := by
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
    rfl
  simpa only [← heq] using
    coarseHeatKernel_energy_moment_le (reducedLaw Q) hp (by positivity : 0 ≤ 1 + M)
      g hg hcol z hr

/-- Global identification transports the canonical Gaussian energy moments
to the actual source corrector and its normalized coefficient law. -/
theorem coarseCorrector_actualGaussian_energy_moment_le
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      unitVector i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    {p M : ℝ} (hp : 2 ≤ p) (hM : 0 ≤ M)
    (hm : MemLp (fun ω => correctorGradient Q i ω) (ENNReal.ofReal p) (reducedLaw Q))
    (hb : eLpNorm (fun ω => correctorGradient Q i ω) (ENNReal.ofReal p)
      (reducedLaw Q) ≤ ENNReal.ofReal M) (z : Vec d) {r : ℝ} (hr : 0 < r) :
    (∀ᵐ a ∂actualCoefficientLaw Q, Integrable (fun y => heatKernel z r y *
      euclideanNorm (unitVector i + φ.grad a y) ^ 2)) ∧
    MemLp (fun a => Real.sqrt (∫ y, heatKernel z r y *
      euclideanNorm (unitVector i + φ.grad a y) ^ 2))
        (ENNReal.ofReal p) (actualCoefficientLaw Q) ∧
    eLpNorm (fun a => Real.sqrt (∫ y, heatKernel z r y *
      euclideanNorm (unitVector i + φ.grad a y) ^ 2))
        (ENNReal.ofReal p) (actualCoefficientLaw Q) ≤ ENNReal.ofReal (1 + M) := by
  let N := fun a : Coefficient d (AKMUpperEllipticity L) => Real.sqrt (∫ y,
    heatKernel z r y * euclideanNorm (unitVector i + φ.grad a y) ^ 2)
  let G := fun ω : FieldPair d => Real.sqrt (∫ y, heatKernel z r y *
    euclideanNorm (unitVector i + WithLp.ofLp
      (correctorGradient Q i (translate (r₀ • y) ω))) ^ 2)
  obtain ⟨_, hG, hGn⟩ := coarseCorrector_rescaledHeatKernel_energy_moment_le
    Q i hp hM hm hb r₀ z hr
  have hw : Measurable (heatKernel z r) :=
    ((Correctors.continuous_euclideanHeatKernel (r ^ 2)).comp
      (continuous_id.sub continuous_const)).measurable
  have hn : Continuous (fun v : Vec d => euclideanNorm v) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hNm : Measurable N :=
    ((hw.comp measurable_snd).mul
      ((hn.measurable.comp (measurable_const.add φ.measurable_grad)).pow_const 2)
        ).stronglyMeasurable.integral_prod_right'.measurable.sqrt
  have heq : (fun ω => N (project (r₀ := r₀) Q.ellipticity_parameter ω)) =ᵐ[
      physicalReferenceLaw Q] (fun ω => G (reduce ω.1)) := by
    filter_upwards [hid] with ω hω
    apply congrArg Real.sqrt
    apply integral_congr_ae
    filter_upwards [hω] with y hy
    exact congrArg (fun v : Vec d => heatKernel z r y * euclideanNorm v ^ 2) hy
  have hNn : eLpNorm N (ENNReal.ofReal p) (actualCoefficientLaw Q) ≤
      ENNReal.ofReal (1 + M) := by
    calc
      _ = eLpNorm (N ∘ project (r₀ := r₀) Q.ellipticity_parameter)
          (ENNReal.ofReal p) (physicalReferenceLaw Q) :=
        (eLpNorm_comp_measurePreserving hNm.aestronglyMeasurable
          (measurePreserving_akmProject Q)).symm
      _ = eLpNorm (fun ω => G (reduce ω.1)) (ENNReal.ofReal p)
          (physicalReferenceLaw Q) := eLpNorm_congr_ae heq
      _ = eLpNorm G (ENNReal.ofReal p) (reducedLaw Q) :=
        eLpNorm_comp_measurePreserving hG.aestronglyMeasurable
          (measurePreserving_physicalReduction Q)
      _ ≤ _ := hGn
  refine ⟨?_, lt_of_le_of_lt hNn ENNReal.ofReal_lt_top, hNn⟩
  filter_upwards [coarseCorrector_gaussianAffine_integrable Q i φ hid z hr] with a ha
  exact ha.1

/-- The literal Frobenius size respects nonnegative scalar normalization. -/
theorem coarseMatrix_size_smul {d : ℕ} (M : Mat d) {c : ℝ} (hc : 0 ≤ c) :
    coarsenedMatrixSize (c • M) = c * coarsenedMatrixSize M := by
  unfold coarsenedMatrixSize
  simp only [Matrix.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

/-- The fourth-moment expression retains the exact physical scalar factor,
including for total integrals before integrability has been established. -/
theorem coarseFourthMoment_const_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Ω → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Real.sqrt (Real.sqrt (∫ ω, (c * F ω) ^ 4 ∂P)) =
      c * Real.sqrt (Real.sqrt (∫ ω, F ω ^ 4 ∂P)) := by
  have heq : (fun ω => (c * F ω) ^ 4) =
      (fun ω => (c ^ 2) ^ 2 * F ω ^ 4) := by funext ω; ring
  rw [heq, integral_const_mul, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg c),
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

/-- For a nonnegative L⁴ observable, the fourth-root moment is its L⁴ norm. -/
theorem coarseNonnegative_eLpNorm_four {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : Ω → ℝ} (hF : ∀ ω, 0 ≤ F ω) (hm : MemLp F 4 P) :
    eLpNorm F 4 P = ENNReal.ofReal (Real.sqrt (Real.sqrt (∫ ω, F ω ^ 4 ∂P))) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (4 : ENNReal) ≠ 0)
    (by norm_num : (4 : ENNReal) ≠ ⊤) hm]
  simp only [show (4 : ENNReal).toReal = (4 : ℝ) by norm_num,
    Real.norm_eq_abs, abs_of_nonneg (hF _), Real.rpow_ofNat]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul
    (integral_nonneg fun ω => pow_nonneg (hF ω) 4)]
  norm_num

/-- Literal centering contracts the scalar second moment under a probability law. -/
theorem coarseCentered_secondMoment_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : MemLp f 2 P) :
    MemLp (fun ω => f ω - ∫ a, f a ∂P) 2 P ∧
      (∫ ω, (f ω - ∫ a, f a ∂P) ^ 2 ∂P) ≤ ∫ ω, f ω ^ 2 ∂P := by
  refine ⟨hf.sub (memLp_const _), ?_⟩
  rw [← ProbabilityTheory.variance_eq_integral hf.aemeasurable,
    ProbabilityTheory.variance_eq_sub hf]
  exact sub_le_self _ (sq_nonneg _)

/-- Coordinate L² membership gives the literal finite Euclidean size in L².
The second moment is exactly the sum of the coordinate second moments. -/
theorem coarseFiniteVector_secondMoment {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {P : Measure Ω} {v : Ω → ι → ℝ}
    (hv : ∀ i, MemLp (fun ω => v ω i) 2 P) :
    MemLp (fun ω => Real.sqrt (∑ i, (v ω i) ^ 2)) 2 P ∧
      (∫ ω, (Real.sqrt (∑ i, (v ω i) ^ 2)) ^ 2 ∂P) =
        ∑ i, ∫ ω, (v ω i) ^ 2 ∂P := by
  have hsq : ∀ ω, 0 ≤ ∑ i, (v ω i) ^ 2 :=
    fun ω => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm : AEStronglyMeasurable (fun ω => Real.sqrt (∑ i, (v ω i) ^ 2)) P := by
    have hi := fun i => (hv i).aestronglyMeasurable
    fun_prop
  have hint : Integrable (fun ω => ∑ i, (v ω i) ^ 2) P :=
    integrable_finset_sum _ fun i _ => (hv i).integrable_sq
  have heq : (fun ω => (Real.sqrt (∑ i, (v ω i) ^ 2)) ^ 2) =
      (fun ω => ∑ i, (v ω i) ^ 2) := by
    funext ω
    exact Real.sq_sqrt (hsq ω)
  refine ⟨(memLp_two_iff_integrable_sq hm).2 (heq.symm ▸ hint), ?_⟩
  rw [heq, integral_finset_sum _ fun i _ => (hv i).integrable_sq]

/-- Centering every coordinate contracts the full finite Euclidean L² size.
No entry is omitted and no dimension-dependent loss is introduced. -/
theorem coarseFiniteVector_centering_le {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {P : Measure Ω} [IsProbabilityMeasure P] {v : Ω → ι → ℝ}
    (hv : ∀ i, MemLp (fun ω => v ω i) 2 P) :
    MemLp (fun ω => Real.sqrt (∑ i, (v ω i - ∫ a, v a i ∂P) ^ 2)) 2 P ∧
      Real.sqrt (∫ ω, (Real.sqrt (∑ i, (v ω i - ∫ a, v a i ∂P) ^ 2)) ^ 2 ∂P) ≤
        Real.sqrt (∫ ω, (Real.sqrt (∑ i, (v ω i) ^ 2)) ^ 2 ∂P) := by
  have hc := fun i => coarseCentered_secondMoment_le (hv i)
  obtain ⟨hm, heq⟩ := coarseFiniteVector_secondMoment (fun i => (hc i).1)
  refine ⟨hm, ?_⟩
  rw [heq, (coarseFiniteVector_secondMoment hv).2]
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => (hc i).2)

/-- One coordinatewise L² bound controls the full finite Euclidean vector with
its exact square-root cardinality factor. -/
theorem coarseFiniteVector_L2_le {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {P : Measure Ω} {v : Ω → ι → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ i, MemLp (fun ω => v ω i) 2 P)
    (hbound : ∀ i, Real.sqrt (∫ ω, (v ω i) ^ 2 ∂P) ≤ C) :
    Real.sqrt (∫ ω, (Real.sqrt (∑ i, (v ω i) ^ 2)) ^ 2 ∂P) ≤
      Real.sqrt (Fintype.card ι : ℝ) * C := by
  rw [(coarseFiniteVector_secondMoment hv).2]
  have hi : ∀ i, (∫ ω, (v ω i) ^ 2 ∂P) ≤ C ^ 2 := by
    intro i
    have hnonneg : 0 ≤ ∫ ω, (v ω i) ^ 2 ∂P :=
      integral_nonneg fun ω => sq_nonneg _
    have hs := Real.sq_sqrt hnonneg
    have hb := hbound i
    have hp := Real.sqrt_nonneg (∫ ω, (v ω i) ^ 2 ∂P)
    nlinarith
  calc
    _ ≤ Real.sqrt (∑ _ : ι, C ^ 2) :=
      Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => hi i)
    _ = Real.sqrt (Fintype.card ι : ℝ) * C := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hC]

/-- The approved averaged-corrector input gives genuine Gaussian gradient
L⁴ decay for its selected source witness, with one constant before the law. -/
theorem coarseSource_gradientAverage_L4 (d : ℕ) (hd : 2 ≤ d)
    (K : ℝ) (hK : 1 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient d K), LawHypotheses P →
      ∃ S : SourceObjects P, ∀ e : Vec d, euclideanNorm e < 1 →
      ∀ (z : Vec d) (r : ℝ), 1 ≤ r →
        (∀ᵐ a ∂P, Integrable
          (fun y => heatKernel z r y • (S.corrector e).grad a y)) ∧
        MemLp (fun a => euclideanNorm
          (∫ y, heatKernel z r y • (S.corrector e).grad a y)) 4 P ∧
        Real.sqrt (Real.sqrt (∫ a, (euclideanNorm
          (∫ y, heatKernel z r y • (S.corrector e).grad a y)) ^ 4 ∂P)) ≤
            C * r ^ (-(d : ℝ) / 2) := by
  obtain ⟨C₀, hC₀, hs⟩ := External.akm_averaged_corrector.1 d hd K 1 hK
    (by norm_num) (by norm_num)
  let b := Real.sqrt (Real.sqrt (2 * (4 / (1 : ℝ)) ^ (4 / (1 : ℝ))))
  refine ⟨(b + 1) * C₀, mul_pos (by positivity) hC₀, ?_⟩
  intro P hP
  obtain ⟨S, hS⟩ := hs P hP
  refine ⟨S, ?_⟩
  intro e he z r hr
  obtain ⟨hI, hg, _⟩ := hS e he z r hr
  obtain ⟨hm, hn⟩ := coarseNonnegative_osBound_L4
    (fun a => Real.sqrt_nonneg _) hg
  refine ⟨hI.mono fun a ha => ha.1, hm, ?_⟩
  calc
    _ ≤ b * (C₀ * r ^ (-(d : ℝ) / 2)) := hn
    _ ≤ ((b + 1) * C₀) * r ^ (-(d : ℝ) / 2) := by
      have hrp : 0 ≤ r ^ (-(d : ℝ) / 2) := Real.rpow_nonneg
        (le_trans zero_le_one hr) _
      nlinarith


/-- Scalar Cauchy--Schwarz in squared integral form. Source:
`paper/main.tex:777–782,840`; integration of the kernel energy. -/
theorem coarseIntegral_mul_sq_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, f x^2 ∂μ)*(∫ x, g x^2 ∂μ) := by
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all μ fun x => abs_nonneg (f x))
    (ae_of_all μ fun x => abs_nonneg (g x))
    (show MemLp (fun x => |f x|) (ENNReal.ofReal 2) μ by
      simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using hf.norm)
    (show MemLp (fun x => |g x|) (ENNReal.ofReal 2) μ by
      simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using hg.norm)
  have he (v : Ω → ℝ) : (∫ x, |v x|^(2 : ℝ) ∂μ)^(1/(2 : ℝ)) =
      Real.sqrt (∫ x, v x^2 ∂μ) := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    exact integral_congr_ae (ae_of_all μ fun x => by simp only [Real.rpow_two,sq_abs])
  rw [he f,he g] at hh
  have hb : |∫ x, f x*g x ∂μ| ≤
      Real.sqrt (∫ x, f x^2 ∂μ)*Real.sqrt (∫ x, g x^2 ∂μ) := by
    calc
      _ ≤ ∫ x, |f x*g x| ∂μ := abs_integral_le_integral_abs
      _ = ∫ x, |f x| * |g x| ∂μ := integral_congr_ae (ae_of_all μ fun x => abs_mul _ _)
      _ ≤ _ := hh
  have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
  simpa only [sq_abs,mul_pow,Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (f x)),
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (g x))] using hs


/-- Uniform spatial L² bounds give a weighted space-time L² bound for every
integrable positive parameter weight. Source: `paper/main.tex:777–782,840`. -/
theorem coarseMemLp_weighted_product_of_uniform_energy
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (ν : Measure X) [SFinite ν]
    {w : Ω → ℝ} (hwm : Measurable w) (hw : Integrable w μ)
    (hwp : ∀ ω, 0 < w ω) {f : Ω × X → ℝ} (hfm : Measurable f)
    (hf : ∀ᵐ ω ∂μ, MemLp (fun x => f (ω,x)) 2 ν)
    {M : ℝ} (hbound : ∀ᵐ ω ∂μ, (∫ x, f (ω,x)^2 ∂ν) ≤ M) :
    MemLp (fun z => (w z.1 * f z) / Real.sqrt (w z.1)) 2 (μ.prod ν) := by
  let g : Ω × X → ℝ := fun z => (w z.1 * f z) / Real.sqrt (w z.1)
  have hgm : Measurable g :=
    ((hwm.comp measurable_fst).mul hfm).div (hwm.sqrt.comp measurable_fst)
  have heq (z : Ω × X) : g z^2 = w z.1 * f z^2 := by
    dsimp only [g]
    rw [div_pow,mul_pow,Real.sq_sqrt (hwp _).le]
    field_simp
  apply (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hgm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨?_,?_⟩
  · filter_upwards [hf] with ω hω
    simpa only [heq] using hω.integrable_sq.const_mul (w ω)
  · have hm : AEStronglyMeasurable (fun ω => ∫ x, g (ω,x)^2 ∂ν) μ :=
      (hgm.pow_const 2).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    have hn : (fun ω => ∫ x, ‖g (ω,x)^2‖ ∂ν) = fun ω => ∫ x, g (ω,x)^2 ∂ν := by
      funext ω
      exact integral_congr_ae (ae_of_all _ (fun x => Real.norm_of_nonneg (sq_nonneg _)))
    rw [hn]
    apply (hw.mul_const M).mono' hm
    filter_upwards [hbound] with ω hω
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => sq_nonneg _))]
    simp_rw [heq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hω (hwp ω).le

/-- A finite positive parameter weight and a weighted product L² bound give
an actual L² parameter integral, even on infinite spatial measure.
Source: `paper/main.tex:777–782,840`. -/
theorem coarseMemLp_two_integral_of_weighted_product
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [SFinite μ] (ν : Measure X) [SFinite ν]
    {w : Ω → ℝ} (hwm : Measurable w) (hw : Integrable w μ)
    (hwp : ∀ ω, 0 < w ω) {f : Ω × X → ℝ}
    (hfm : Measurable f)
    (hf : MemLp (fun z => f z / Real.sqrt (w z.1)) 2 (μ.prod ν)) :
    MemLp (fun x => ∫ ω, f (ω,x) ∂μ) 2 ν ∧
      ∀ᵐ x ∂ν, Integrable (fun ω => f (ω,x)) μ := by
  let g : Ω × X → ℝ := fun z => f z / Real.sqrt (w z.1)
  have hs : MemLp (fun ω => Real.sqrt (w ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq hwm.sqrt.aestronglyMeasurable).mpr
    simpa only [Real.sq_sqrt (hwp _).le] using hw
  have hsq := hf.integrable_sq
  have hgx : ∀ᵐ x ∂ν, MemLp (fun ω => g (ω,x)) 2 μ := by
    filter_upwards [hsq.prod_left_ae] with x hx
    apply (memLp_two_iff_integrable_sq ?_).mpr hx
    exact ((hfm.comp measurable_prodMk_right).div hwm.sqrt).aestronglyMeasurable
  have hcancel (z : Ω × X) : g z * Real.sqrt (w z.1) = f z :=
    div_mul_cancel₀ _ (Real.sqrt_pos.mpr (hwp z.1)).ne'
  refine ⟨?_, ?_⟩
  · have havm : AEStronglyMeasurable (fun x => ∫ ω, f (ω,x) ∂μ) ν :=
      hfm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq havm).mpr
    have hb : Integrable (fun x => (∫ ω, w ω ∂μ) * (∫ ω, g (ω,x)^2 ∂μ)) ν :=
      hsq.integral_prod_right.const_mul _
    apply hb.mono' (havm.pow 2)
    filter_upwards [hgx] with x hx
    have hc := coarseIntegral_mul_sq_le μ hx hs
    have heq : (fun ω => g (ω,x)*Real.sqrt (w ω)) = fun ω => f (ω,x) :=
      funext fun ω => hcancel (ω,x)
    rw [heq] at hc
    simp only [Real.sq_sqrt (hwp _).le] at hc
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_sq,mul_comm] using hc
  · filter_upwards [hgx] with x hx
    exact (hx.integrable_mul hs).congr (ae_of_all _ (fun ω => hcancel (ω,x)))


/-- The actual commutator has L² membership from the canonical flux and
canonical gradient, without a smooth-moment assumption. -/
theorem coarseCommutator_memLp_two {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (j i : Fin d) :
    MemLp (commutatorObservation Q j i) 2 (reducedLaw Q) := by
  have hF0 : MemLp (fun ω : FieldPair d =>
      correctorFluxOfGradient Q i (correctorGradient Q i) ω j) 2 (reducedLaw Q) :=
    (Lp.memLp (correctorFluxOfGradient Q i (correctorGradient Q i))).eval_piLp j
  have heq : (fun ω : FieldPair d =>
      correctorFluxOfGradient Q i (correctorGradient Q i) ω j) =ᵐ[reducedLaw Q]
      (fun ω => ∑ k : Fin d, ω.1 0 j k *
        (unitVector i k + correctorGradient Q i ω k)) := by
    filter_upwards [correctorFluxOfGradient_ae Q i] with ω hω
    exact hω j
  have hF := hF0.ae_eq heq
  have hg (k : Fin d) : MemLp (fun ω : FieldPair d => correctorGradient Q i ω k)
      2 (reducedLaw Q) := (Lp.memLp (correctorGradient Q i)).eval_piLp k
  have hc (k : Fin d) : MemLp (fun _ω : FieldPair d => unitVector i k)
      2 (reducedLaw Q) := memLp_const _
  have hA : MemLp (fun ω : FieldPair d => ∑ k : Fin d, homogenizedCoefficient Q j k *
      (unitVector i k + correctorGradient Q i ω k)) 2 (reducedLaw Q) := by
    apply memLp_finsetSum
    intro k _
    exact ((hc k).add (hg k)).const_mul (homogenizedCoefficient Q j k)
  exact (hF.sub hA).ae_eq (ae_of_all _ fun ω =>
    (commutatorObservation_eq_flux_sub Q j i ω).symm)

/-- Positive Gaussian averaging preserves L² for a measurable stationary
observable. The convolution has the literal translated physical argument. -/
theorem coarseStationary_heatKernel_memLp_two {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (f : FieldPair d → ℝ)
    (hf : Measurable f) (hm : MemLp f 2 (reducedLaw Q))
    (x : Vec d) {r : ℝ} (hr : 0 < r) :
    MemLp (fun ω => ∫ z, heatKernel 0 r z * f (translate (x-z) ω))
      2 (reducedLaw Q) := by
  have hk : Measurable (heatKernel (0 : Vec d) r) := by
    unfold heatKernel euclideanHeatKernel euclideanSq dot
    fun_prop
  have hki : Integrable (heatKernel (0 : Vec d) r) := by
    change Integrable (fun z : Vec d => euclideanHeatKernel (r ^ 2) (z - 0))
    simpa only [sub_zero] using
      integrable_euclideanHeatKernel (d := d) (sq_pos_of_pos hr)
  have hkp : ∀ z : Vec d, 0 < heatKernel 0 r z := by
    intro z
    unfold heatKernel euclideanHeatKernel
    positivity
  let F := fun p : Vec d × FieldPair d => f (translate (x-p.1) p.2)
  have hFm : Measurable F := hf.comp
    (Probability.continuous_translate.measurable.comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd))
  have hFs : ∀ z : Vec d, MemLp (fun ω => F (z,ω)) 2 (reducedLaw Q) :=
    fun z => hm.comp_measurePreserving
      (measurePreserving_translate (reducedLaw Q) (reducedEnvironmentLaw_stationary Q) (x-z))
  have hFb : ∀ z : Vec d,
      (∫ ω, F (z,ω)^2 ∂reducedLaw Q) ≤ ∫ ω, f ω^2 ∂reducedLaw Q := by
    intro z
    exact le_of_eq (Probability.integral_translate (reducedLaw Q)
      (reducedEnvironmentLaw_stationary Q) (x-z) (fun ω => f ω^2) (hf.pow_const 2))
  have hw := coarseMemLp_weighted_product_of_uniform_energy volume (reducedLaw Q)
    hk hki hkp hFm (ae_of_all _ hFs) (ae_of_all _ hFb)
  exact (coarseMemLp_two_integral_of_weighted_product volume (reducedLaw Q)
    hk hki hkp ((hk.comp measurable_fst).mul hFm) hw).1

/-- Every actual isotropic Gaussian commutator entry belongs to L². -/
theorem coarseCommutator_heatKernel_memLp_two {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (j i : Fin d) (x : Vec d) {r : ℝ} (hr : 0 < r) :
    MemLp (fun ω => ∫ z, heatKernel 0 r z *
      commutatorObservation Q j i (translate (x-z) ω)) 2 (reducedLaw Q) :=
  coarseStationary_heatKernel_memLp_two Q _ (coarseCommutator_measurable Q j i)
    (coarseCommutator_memLp_two Q j i) x hr

/-- A mean-zero observable minus a centered comparison has no larger L²
error than the uncentered difference. -/
theorem coarseCenteredDifference_secondMoment_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f g : Ω → ℝ}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) (hmean : (∫ ω, f ω ∂P) = 0) :
    MemLp (fun ω => f ω - (g ω - ∫ a, g a ∂P)) 2 P ∧
      (∫ ω, (f ω - (g ω - ∫ a, g a ∂P)) ^ 2 ∂P) ≤
        ∫ ω, (f ω - g ω) ^ 2 ∂P := by
  have heq : (fun ω => f ω - (g ω - ∫ a, g a ∂P)) =
      (fun ω => (f ω - g ω) - ∫ a, (f a - g a) ∂P) := by
    rw [integral_sub (hf.integrable (by norm_num)) (hg.integrable (by norm_num)), hmean]
    funext ω
    ring
  have hc := coarseCentered_secondMoment_le (hf.sub hg)
  refine ⟨hc.1.ae_eq (ae_of_all _ fun ω => (congrFun heq ω).symm), ?_⟩
  calc
    _ = ∫ ω, ((f ω - g ω) - ∫ a, (f a - g a) ∂P)^2 ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => congrArg (fun t : ℝ => t^2) (congrFun heq ω))
    _ ≤ _ := hc.2

end EinsteinFull
