import EinsteinFull.Homogenization.HighContrastCorrectors
import EinsteinFull.Homogenization.HighContrastSlopeSupport

/-!
# The slope of a sublinear corrected affine function

Let `ψ` be a sublinear function whose gradient, shifted by `e`, coincides almost everywhere with
a corrected gradient `e' + ∇Φ_{e'}` of the high-contrast corrector family of Armstrong, Kuusi and
Loher, *Homogenization at a polynomial scale in high contrast*. Pairing with smooth cutoffs at
scale `r`, the corrector estimate makes the averages of `∇Φ_{e'}` vanish as `r → ∞`, and
sublinearity makes the averages of `∇ψ` vanish; therefore `e = e'`.
-/

open MeasureTheory Filter Topology
open scoped Pointwise

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport
  EinsteinRelation.External.AKM
open _root_.Homogenization hiding euclideanBall Vec Mat
open _root_.Homogenization.HighContrast

variable {d : ℕ}

/-- The integral of a cutoff-weighted pairing with the corrector gradient is controlled by the
corrector estimate, for scales above the homogenization scale. -/
theorem abs_integral_cutoff_gradPhi_le {K : ℝ} {hK : 1 ≤ K} {P : Measure (Coefficient d K)}
    {κ C : ℝ} (hC : 0 ≤ C) (pk : HighContrastCorrectorPackage hK P κ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend) (e w : Vec d) {r : ℝ} (hr : 0 < r) (hrX : pk.X b ≤ r)
    (hloc : ∀ i, LocallyIntegrable (fun x => pk.gradPhi e b x i) volume)
    (η : QuantitativeBallCutoff (0 : Vec d) (r / 2) r) :
    |∫ x, η.toFun x * vecDot (pk.gradPhi e b x)
        (matVecMul (matTranspose (matSqrt (symmPart pk.abar))) w)| ≤
      (volume (ellipsoid pk.abar r)).toReal *
        (Real.sqrt (vecNormSq w * ((volume (euclideanBall d r)).toReal ^ (-(2 : ℝ) / d) +
          d * (2 * quantitativeBallCutoffGradientConst d / r) ^ 2)) *
        (r * (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) *
          (r / pk.X b) ^ (-κ)))) := by
  set M := matSqrt (symmPart pk.abar)
  set V := ellipsoid pk.abar r
  set F : Vec d → Vec d := fun x => matVecMul M (pk.gradPhi e b x)
  set ψ : Vec d → Vec d := fun x => η.toFun x • w
  set Kr : ℝ := vecNormSq w * ((volume (euclideanBall d r)).toReal ^ (-(2 : ℝ) / d) +
    d * (2 * quantitativeBallCutoffGradientConst d / r) ^ 2)
  set B : ℝ := C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) * (r / pk.X b) ^ (-κ)
  have hS : (symmPart pk.abar).PosDef := posDef_symmPart_of_vecDot_pos pk.posDef
  have hBV : euclideanBall d r ⊆ V := euclideanBallAt_zero_subset_ellipsoid pk.abar r
  have hVtop : volume V ≠ ⊤ := (volume_ellipsoid_lt_top hS r).ne
  have hVpos : 0 < volume V := volume_ellipsoid_pos pk.abar hr
  have hVm : MeasurableSet V := measurableSet_ellipsoid pk.abar r
  have htest : IsLocalVecTest V ψ := isLocalVecTest_ballCutoff_smul hBV η w
  have hpt (x : Vec d) : vecDot (F x) (ψ x) =
      η.toFun x * vecDot (pk.gradPhi e b x) (matVecMul (matTranspose M) w) := by
    simp only [F, ψ]
    rw [vecDot_matVecMul_transpose]
    simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hcont : Continuous η.toFun := η.smooth.continuous
  have hint : Integrable (fun x => η.toFun x * vecDot (pk.gradPhi e b x)
      (matVecMul (matTranspose M) w)) := by
    simp only [vecDot, Finset.mul_sum]
    refine integrable_finsetSum _ fun i _ => ?_
    have := ((hloc i).integrable_smul_left_of_hasCompactSupport hcont η.hasCompactSupport)
    have h2 := this.mul_const ((matVecMul (matTranspose M) w) i)
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul]
    ring
  have hintV : IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume := by
    simp_rw [hpt]
    exact hint.integrableOn
  have hnormV := h1NormSq_ballCutoff_smul_le hr hBV hVtop η w
  have hneg : negOneNorm V F ≤ ENNReal.ofReal (r * B) := by
    have h := pk.corrector b hb e r hrX
    have h1 : ENNReal.ofReal r⁻¹ * negOneNorm V F ≤ ENNReal.ofReal B :=
      le_trans le_self_add h
    calc negOneNorm V F = ENNReal.ofReal r * (ENNReal.ofReal r⁻¹ * negOneNorm V F) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal r * ENNReal.ofReal B := by gcongr
      _ = ENNReal.ofReal (r * B) := (ENNReal.ofReal_mul hr.le).symm
  have hB0 : 0 ≤ B := by
    have hX : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
    exact mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _))
      (Real.rpow_nonneg (div_nonneg hr.le hX.le) _)
  have hvolume : (∫ x, η.toFun x * vecDot (pk.gradPhi e b x)
      (matVecMul (matTranspose M) w)) =
      (volume V).toReal * volumeAverage V (fun x => vecDot (F x) (ψ x)) := by
    unfold volumeAverage
    have hVreal : 0 < (volume V).toReal := ENNReal.toReal_pos hVpos.ne' hVtop
    rw [← mul_assoc, mul_inv_cancel₀ hVreal.ne', one_mul]
    simp_rw [hpt]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    have hxη : x ∉ tsupport η.toFun := fun h => hx (hBV (η.support_subset h))
    simp [image_eq_zero_of_notMem_tsupport hxη]
  rw [hvolume, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  by_cases hw : w = 0
  · have hzero : volumeAverage V (fun x => vecDot (F x) (ψ x)) = 0 := by
      simp [volumeAverage, ψ, hw, vecDot]
    rw [hzero, abs_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hr.le hB0)
  · have hBpos := volume_euclideanBall_pos' (d := d) hr
    have hBreal : 0 < (volume (euclideanBall d r)).toReal :=
      ENNReal.toReal_pos hBpos.ne' (volume_euclideanBall_ne_top' r)
    have hwpos : 0 < vecNormSq w :=
      lt_of_le_of_ne (vecNormSq_nonneg w) fun h => hw (vecNormSq_eq_zero h.symm)
    have hK0 : 0 < Kr := mul_pos hwpos (add_pos_of_pos_of_nonneg
      (Real.rpow_pos_of_pos hBreal _) (by positivity))
    exact abs_volumeAverage_le_of_negOneNorm_le hK0 (mul_nonneg hr.le hB0) htest hintV
      hnormV hneg

theorem volume_euclideanBall_toReal_le_integral_cutoff {r : ℝ}
    (η : QuantitativeBallCutoff (0 : Vec d) (r / 2) r) :
    (volume (euclideanBall d (r / 2))).toReal ≤ ∫ x, η.toFun x := by
  have hint : Integrable η.toFun :=
    η.smooth.continuous.integrable_of_hasCompactSupport η.hasCompactSupport
  have h1 : ∫ x in euclideanBall d (r / 2), η.toFun x = (volume (euclideanBall d (r / 2))).toReal := by
    rw [setIntegral_congr_fun (HighContrast.isOpen_euclideanBall d (r / 2)).measurableSet
      (fun x hx => η.eq_one_on_inner x hx)]
    simp [measureReal_def]
  rw [← h1]
  exact setIntegral_le_integral hint (Filter.Eventually.of_forall η.nonneg)

/-- The cutoff-weighted pairing with the gradient of a function in `L²_loc` is bounded by the
cutoff gradient and the normalized `L²` norm on the ball. -/
theorem abs_integral_cutoff_grad_le {ψ : Vec d → ℝ} {Dψ : Vec d → Vec d}
    (hψ : HasWeakGradientOn Set.univ ψ Dψ) {r : ℝ} (hr : 0 < r)
    (hψL2 : MemLp ψ 2 (volume.restrict (euclideanBall d r)))
    (η : QuantitativeBallCutoff (0 : Vec d) (r / 2) r) (u : Vec d)
    (hDψ : ∀ i, Integrable (fun x => η.toFun x * Dψ x i)) :
    |∫ x, η.toFun x * vecDot (Dψ x) u| ≤
      (∑ i, |u i|) * (2 * quantitativeBallCutoffGradientConst d / r) *
        ((volume (euclideanBall d r)).toReal *
          (normalizedL2Norm (euclideanBall d r) ψ).toReal) := by
  have hdiff : Differentiable ℝ η.toFun := η.smooth.differentiable (by simp)
  have hgrad (x : Vec d) : ‖fderiv ℝ η.toFun x‖ ≤ 2 * quantitativeBallCutoffGradientConst d / r := by
    have h := η.gradient_bound x
    have hrr : r - r / 2 = r / 2 := by ring
    rw [hrr] at h
    calc ‖fderiv ℝ η.toFun x‖ ≤ quantitativeBallCutoffGradientConst d / (r / 2) := h
      _ = 2 * quantitativeBallCutoffGradientConst d / r := by field_simp
  set G := 2 * quantitativeBallCutoffGradientConst d / r
  have hG : 0 ≤ G := le_trans (norm_nonneg _) (hgrad 0)
  have hL1 := integral_abs_le_volume_mul_normalizedL2Norm hr hψL2
  have : IsFiniteMeasure (volume.restrict (euclideanBall d r)) :=
    isFiniteMeasure_restrict.mpr (volume_euclideanBall_ne_top' r)
  -- each coordinate
  have hcoord (i : Fin d) : |∫ x, η.toFun x * Dψ x i| ≤
      G * ((volume (euclideanBall d r)).toReal *
        (normalizedL2Norm (euclideanBall d r) ψ).toReal) := by
    have hw := hψ i η.toFun η.smooth η.hasCompactSupport (Set.subset_univ _)
    simp only [Measure.restrict_univ] at hw
    have heq : ∫ x, η.toFun x * Dψ x i = -∫ x, ψ x * fderiv ℝ η.toFun x (basisVec i) := by
      rw [hw, neg_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [heq, abs_neg]
    have hsupp (x : Vec d) (hx : x ∉ euclideanBall d r) :
        ψ x * fderiv ℝ η.toFun x (basisVec i) = 0 := by
      have hxη : x ∉ tsupport η.toFun := fun h => hx (η.support_subset h)
      have : fderiv ℝ η.toFun x = 0 := by
        by_contra hne
        exact hxη (support_fderiv_subset ℝ hne)
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    calc |∫ x in euclideanBall d r, ψ x * fderiv ℝ η.toFun x (basisVec i)|
        ≤ ∫ x in euclideanBall d r, |ψ x * fderiv ℝ η.toFun x (basisVec i)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x in euclideanBall d r, G * |ψ x| := by
          refine setIntegral_mono_on ?_ ?_ (HighContrast.isOpen_euclideanBall d r).measurableSet
            fun x _ => ?_
          · refine Integrable.abs ?_
            have hbd : ∀ x, ‖fderiv ℝ η.toFun x (basisVec i)‖ ≤ G := fun x =>
              (by rw [Real.norm_eq_abs]; exact (abs_fderiv_apply_basisVec_le η.toFun x i).trans (hgrad x))
            have hmeas : AEStronglyMeasurable (fun x => fderiv ℝ η.toFun x (basisVec i))
                (volume.restrict (euclideanBall d r)) :=
              ((η.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
            exact (hψL2.integrable one_le_two).mul_bdd hmeas
              (Filter.Eventually.of_forall hbd) |>.congr
              (Filter.Eventually.of_forall fun x => by ring)
          · exact ((hψL2.integrable one_le_two).abs.const_mul G)
          · rw [abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right ((abs_fderiv_apply_basisVec_le η.toFun x i).trans
              (hgrad x)) (abs_nonneg _)
      _ = G * ∫ x in euclideanBall d r, |ψ x| := integral_const_mul _ _
      _ ≤ G * ((volume (euclideanBall d r)).toReal *
            (normalizedL2Norm (euclideanBall d r) ψ).toReal) :=
          mul_le_mul_of_nonneg_left hL1 hG
  have hsplit : ∫ x, η.toFun x * vecDot (Dψ x) u = ∑ i, u i * ∫ x, η.toFun x * Dψ x i := by
    have hfun : (fun x => η.toFun x * vecDot (Dψ x) u) =
        fun x => ∑ i, u i * (η.toFun x * Dψ x i) := by
      funext x
      simp only [vecDot, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hfun, integral_finsetSum _ fun i _ => (hDψ i).const_mul (u i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_const_mul _ _
  rw [hsplit]
  calc |∑ i, u i * ∫ x, η.toFun x * Dψ x i|
      ≤ ∑ i, |u i * ∫ x, η.toFun x * Dψ x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |u i| * (G * ((volume (euclideanBall d r)).toReal *
          (normalizedL2Norm (euclideanBall d r) ψ).toReal)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
    _ = (∑ i, |u i|) * G * ((volume (euclideanBall d r)).toReal *
          (normalizedL2Norm (euclideanBall d r) ψ).toReal) := by
        rw [← Finset.sum_mul, mul_assoc]

theorem volume_euclideanBall_toReal {r : ℝ} (hr : 0 < r) :
    (volume (euclideanBall d r)).toReal = r ^ d * (volume (euclideanBall d 1)).toReal := by
  rw [volume_euclideanBall_eq hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem volume_ellipsoid_toReal (abar : Mat d) {r : ℝ} (hr : 0 < r) :
    (volume (ellipsoid abar r)).toReal = r ^ d * (volume (ellipsoid abar 1)).toReal := by
  rw [volume_ellipsoid_eq abar hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem volume_euclideanBall_toReal_rpow {r : ℝ} (hr : 0 < r) (hd : 0 < d) :
    (volume (euclideanBall d r)).toReal ^ (-(2 : ℝ) / d) =
      (volume (euclideanBall d 1)).toReal ^ (-(2 : ℝ) / d) / r ^ 2 := by
  have hb : 0 ≤ (volume (euclideanBall d 1)).toReal := ENNReal.toReal_nonneg
  rw [volume_euclideanBall_toReal hr, Real.mul_rpow (by positivity) hb, ← Real.rpow_natCast,
    ← Real.rpow_mul hr.le]
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hexp : (d : ℝ) * (-(2 : ℝ) / d) = -2 := by field_simp
  rw [hexp, Real.rpow_neg hr.le, Real.rpow_two]
  field_simp

/-- **Slope identification.** A sublinear function whose shifted gradient agrees almost
everywhere with a corrected gradient of the high-contrast corrector family has the same
slope. -/
theorem eq_slope_of_ae_eq_corrected {K : ℝ} {hK : 1 ≤ K} {P : Measure (Coefficient d K)}
    {κ C : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hC : 0 ≤ C) (pk : HighContrastCorrectorPackage hK P κ C)
    {b : CoeffSpace d} (hb : b ∈ pk.Ωend) {e e' : Vec d} {ψ : Vec d → ℝ}
    {Dψ : Vec d → Vec d} (hψ : HasWeakGradientOn Set.univ ψ Dψ)
    (hψL2 : ∀ r : ℝ, 0 < r → MemLp ψ 2 (volume.restrict (euclideanBall d r)))
    (hDψ : ∀ i, LocallyIntegrable (fun x => Dψ x i) volume)
    (hloc : ∀ i, LocallyIntegrable (fun x => pk.gradPhi e' b x i) volume)
    (hsub : Tendsto (fun r : ℝ => r⁻¹ * (normalizedL2Norm (euclideanBall d r) ψ).toReal)
      atTop (𝓝 0))
    (heq : (fun x => e + Dψ x) =ᵐ[volume] fun x => e' + pk.gradPhi e' b x) :
    e = e' := by
  set S := symmPart pk.abar
  set M := matSqrt S
  set Mt := matTranspose M
  have hS : S.PosDef := posDef_symmPart_of_vecDot_pos pk.posDef
  set G := quantitativeBallCutoffGradientConst d
  set b₁ := (volume (euclideanBall d 1)).toReal
  set e₁ := (volume (ellipsoid pk.abar 1)).toReal
  have hb₁ : 0 < b₁ := ENNReal.toReal_pos (volume_euclideanBall_pos' one_pos).ne'
    (volume_euclideanBall_ne_top' 1)
  have hX : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
  have key : ∀ w : Vec d, vecDot (e - e') (matVecMul Mt w) = 0 := by
    intro w
    set u := matVecMul Mt w
    set D := e - e'
    set c₀ := b₁ ^ (-(2 : ℝ) / d) + d * (2 * G) ^ 2
    set A := C * Real.sqrt (vecDot e' (matVecMul S e'))
    set f : ℝ → ℝ := fun r => 2 ^ d * (e₁ / b₁ * Real.sqrt (vecNormSq w * c₀) *
      (A * (r / pk.X b) ^ (-κ)) + (∑ i, |u i|) * (2 * G) *
        (r⁻¹ * (normalizedL2Norm (euclideanBall d r) ψ).toReal))
    have hbound : ∀ᶠ r in atTop, |vecDot D u| ≤ f r := by
      filter_upwards [eventually_ge_atTop (pk.X b)] with r hrX
      have hr : 0 < r := lt_of_lt_of_le hX hrX
      let η := QuantitativeBallCutoff.canonical (0 : Vec d) (r / 2) r (by positivity)
        (by linarith)
      have hηint : Integrable η.toFun :=
        η.smooth.continuous.integrable_of_hasCompactSupport η.hasCompactSupport
      have hI := volume_euclideanBall_toReal_le_integral_cutoff η
      have hIpos : 0 < (volume (euclideanBall d (r / 2))).toReal := by
        rw [volume_euclideanBall_toReal (by positivity)]
        positivity
      have hgradint : ∀ i, Integrable (fun x => η.toFun x * pk.gradPhi e' b x i) := fun i => by
        simpa [smul_eq_mul] using (hloc i).integrable_smul_left_of_hasCompactSupport
          η.smooth.continuous η.hasCompactSupport
      have hDψint : ∀ i, Integrable (fun x => η.toFun x * Dψ x i) := fun i => by
        simpa [smul_eq_mul] using (hDψ i).integrable_smul_left_of_hasCompactSupport
          η.smooth.continuous η.hasCompactSupport
      have hvecint (F : Vec d → Vec d)
          (hF : ∀ i, Integrable (fun x => η.toFun x * F x i)) :
          Integrable (fun x => η.toFun x * vecDot (F x) u) := by
        have hfun : (fun x => η.toFun x * vecDot (F x) u) =
            fun x => ∑ i, u i * (η.toFun x * F x i) := by
          funext x
          simp only [vecDot, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        rw [hfun]
        exact integrable_finsetSum _ fun i _ => (hF i).const_mul (u i)
      have hid : (∫ x, η.toFun x) * vecDot D u =
          (∫ x, η.toFun x * vecDot (pk.gradPhi e' b x) u) -
            ∫ x, η.toFun x * vecDot (Dψ x) u := by
        rw [← integral_sub (hvecint _ hgradint) (hvecint _ hDψint), ← integral_mul_const]
        refine integral_congr_ae ?_
        filter_upwards [heq] with x hx
        have hD : D = pk.gradPhi e' b x - Dψ x := by
          have h := congrArg (fun v => v - Dψ x - e') hx
          simp only [D]
          rw [show e - e' = e + Dψ x - Dψ x - e' by abel, h]
          abel
        rw [hD]
        simp only [vecDot, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      have hA := abs_integral_cutoff_gradPhi_le hC pk hb e' w hr hrX hloc η
      have hT := abs_integral_cutoff_grad_le hψ hr (hψL2 r hr) η u hDψint
      have hmain : (volume (euclideanBall d (r / 2))).toReal * |vecDot D u| ≤
          (volume (ellipsoid pk.abar r)).toReal *
            (Real.sqrt (vecNormSq w * ((volume (euclideanBall d r)).toReal ^ (-(2 : ℝ) / d) +
              d * (2 * G / r) ^ 2)) * (r * (A * (r / pk.X b) ^ (-κ)))) +
          (∑ i, |u i|) * (2 * G / r) * ((volume (euclideanBall d r)).toReal *
            (normalizedL2Norm (euclideanBall d r) ψ).toReal) := by
        calc (volume (euclideanBall d (r / 2))).toReal * |vecDot D u|
            ≤ (∫ x, η.toFun x) * |vecDot D u| :=
              mul_le_mul_of_nonneg_right hI (abs_nonneg _)
          _ = |(∫ x, η.toFun x) * vecDot D u| := by
              rw [abs_mul, abs_of_nonneg (le_trans hIpos.le hI)]
          _ ≤ |∫ x, η.toFun x * vecDot (pk.gradPhi e' b x) u| +
                |∫ x, η.toFun x * vecDot (Dψ x) u| := by
              rw [hid]
              exact abs_sub _ _
          _ ≤ _ := add_le_add hA hT
      -- rescale
      rw [volume_euclideanBall_toReal (by positivity : (0 : ℝ) < r / 2),
        volume_ellipsoid_toReal pk.abar hr, volume_euclideanBall_toReal_rpow hr hd,
        volume_euclideanBall_toReal hr] at hmain
      have hK : vecNormSq w * (b₁ ^ (-(2 : ℝ) / d) / r ^ 2 + d * (2 * G / r) ^ 2) =
          vecNormSq w * c₀ / r ^ 2 := by
        simp only [c₀]
        field_simp
      rw [hK, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hr.le] at hmain
      have hpos : 0 < (r / 2) ^ d * b₁ := by positivity
      refine le_of_mul_le_mul_left (hmain.trans (le_of_eq ?_)) hpos
      simp only [f]
      rw [div_pow]
      field_simp
      ring
    have hlim : Tendsto f atTop (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => (r / pk.X b) ^ (-κ)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop hκ).comp (tendsto_id.atTop_div_const hX)
      have h := ((h1.const_mul A).const_mul (e₁ / b₁ * Real.sqrt (vecNormSq w * c₀))).add
        (hsub.const_mul ((∑ i, |u i|) * (2 * G)))
      have h2 := h.const_mul ((2 : ℝ) ^ d)
      simpa [f] using h2
    have hle : |vecDot D u| ≤ 0 := ge_of_tendsto hlim hbound
    exact abs_nonpos_iff.mp hle
  have hMD : matVecMul M (e - e') = 0 := by
    have h0 := key (matVecMul M (e - e'))
    rw [vecDot_matVecMul_transpose] at h0
    exact vecNormSq_eq_zero h0
  have hu : IsUnit M.det := isUnit_det_matSqrt hS
  have hD : e - e' = matVecMul M⁻¹ (matVecMul M (e - e')) := by
    rw [matVecMul_mul, Matrix.nonsing_inv_mul _ hu]
    funext i
    simp [matVecMul, Matrix.one_apply]
  rw [hMD] at hD
  have hzero : matVecMul M⁻¹ (0 : Vec d) = 0 := by
    funext i
    simp [matVecMul]
  rw [hzero] at hD
  exact sub_eq_zero.mp hD

end EinsteinFull.Homogenization
