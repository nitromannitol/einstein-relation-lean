import EinsteinFull.Homogenization.NegOnePairing
import EinsteinFull.Homogenization.NormalizedBallNorms
import HCPoly.Analytic.EllipsoidGeometry
import EinsteinRelation.Correctors.BallMeanSquareComparison
import Homogenization.Sobolev.Foundations.QuantitativeCutoff

/-!
# Scaling of balls and ellipsoids and smooth ball cutoffs

Centered Euclidean balls and the ellipsoids of a homogenized matrix scale linearly with the
radius, so their volumes scale with the `d`-th power. A smooth cutoff between the balls of
radii `r/2` and `r` has a test-function norm of order `1/r` on any domain containing the
larger ball, and the `L¹` mass of a function on a ball is controlled by its normalized `L²`
norm. These are the computations used to pair the corrector estimate of Armstrong, Kuusi and
Loher, *Homogenization at a polynomial scale in high contrast*, with cutoffs at large scales.
-/

open MeasureTheory
open scoped Pointwise

namespace EinsteinFull.Homogenization

open _root_.Homogenization hiding euclideanBall
open _root_.Homogenization.HighContrast

variable {d : ℕ}

theorem volume_smul_of_pos {r : ℝ} (hr : 0 < r) (s : Set (Vec d)) :
    volume (r • s) = ENNReal.ofReal (r ^ d) * volume s := by
  rw [Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_pos (pow_pos hr d)]

theorem euclideanBall_eq_smul {r : ℝ} (hr : 0 < r) :
    euclideanBall d r = r • euclideanBall d 1 := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  simp only [euclideanBall, euclideanBallAt, Set.mem_ofPred_eq, sub_zero]
  have hscale : vecNormSq (r⁻¹ • x) = r⁻¹ ^ 2 * vecNormSq x := by
    simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hscale, one_pow]
  constructor
  · intro h
    have hr2 : 0 < r ^ 2 := by positivity
    rw [inv_pow]
    rw [inv_mul_lt_iff₀ hr2, mul_one]
    exact h
  · intro h
    have hr2 : 0 < r ^ 2 := by positivity
    rw [inv_pow, inv_mul_lt_iff₀ hr2, mul_one] at h
    exact h

theorem ellipsoid_eq_smul (abar : Mat d) {r : ℝ} (hr : 0 < r) :
    ellipsoid abar r = r • ellipsoid abar 1 := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  simp only [ellipsoid, Set.mem_ofPred_eq, one_pow, mul_one]
  have hscale : vecDot (r⁻¹ • x) (matVecMul (symmPart abar)⁻¹ (r⁻¹ • x)) =
      r⁻¹ ^ 2 * vecDot x (matVecMul (symmPart abar)⁻¹ x) := by
    simp only [vecDot, matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hscale]
  have hr2 : 0 < r ^ 2 := by positivity
  rw [inv_pow, inv_mul_le_iff₀ hr2, mul_comm]

theorem volume_euclideanBall_eq {r : ℝ} (hr : 0 < r) :
    volume (euclideanBall d r) = ENNReal.ofReal (r ^ d) * volume (euclideanBall d 1) := by
  rw [euclideanBall_eq_smul hr, volume_smul_of_pos hr]

theorem volume_ellipsoid_eq (abar : Mat d) {r : ℝ} (hr : 0 < r) :
    volume (ellipsoid abar r) = ENNReal.ofReal (r ^ d) * volume (ellipsoid abar 1) := by
  rw [ellipsoid_eq_smul abar hr, volume_smul_of_pos hr]

theorem cg_euclideanBall_zero (r : ℝ) :
    _root_.Homogenization.euclideanBall (0 : Vec d) r = euclideanBall d r := rfl

/-- The `L¹` mass of a locally square-integrable function on a ball is bounded by the volume
times the normalized `L²` norm. -/
theorem integral_abs_le_volume_mul_normalizedL2Norm {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (euclideanBall d r))) :
    ∫ x in euclideanBall d r, |f x| ≤
      (volume (euclideanBall d r)).toReal * (normalizedL2Norm (euclideanBall d r) f).toReal := by
  have hpos := volume_euclideanBall_pos' (d := d) hr
  have hfin := volume_euclideanBall_ne_top' (d := d) r
  have hball : euclideanBall d r = EinsteinRelation.External.AKM.ball (0 : Vec d) r :=
    (ball_zero_eq_euclideanBall hr).symm
  have hf' : MemLp f 2 (volume.restrict (EinsteinRelation.External.AKM.ball 0 r)) := by rwa [← hball]
  rw [normalizedL2Norm_euclideanBall_eq_ofReal hr hf', ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hvol : 0 < (volume (euclideanBall d r)).toReal := ENNReal.toReal_pos hpos.ne' hfin
  have : IsFiniteMeasure (volume.restrict (euclideanBall d r)) :=
    isFiniteMeasure_restrict.mpr hfin
  have hint := hf.integrable one_le_two
  have hsq := hf.integrable_sq
  have hmean : (⨍ x in euclideanBall d r, |f x|) ^ 2 ≤ ⨍ x in euclideanBall d r, |f x| ^ 2 := by
    have hμ : (volume.restrict (euclideanBall d r)).real Set.univ ≠ 0 := by
      rw [measureReal_restrict_apply_univ, measureReal_def]
      exact hvol.ne'
    exact EinsteinRelation.Correctors.sq_average_le_average_sq _ hμ hf.abs
  have habs_sq : (fun x => |f x| ^ 2) = fun x => f x ^ 2 := by
    funext x
    rw [sq_abs]
  rw [habs_sq] at hmean
  have hmean' : ⨍ x in euclideanBall d r, |f x| ≤
      Real.sqrt (⨍ x in EinsteinRelation.External.AKM.ball (0 : Vec d) r, f x ^ 2) := by
    rw [← hball]
    exact Real.le_sqrt_of_sq_le hmean
  have hav : ∫ x in euclideanBall d r, |f x| =
      (volume (euclideanBall d r)).toReal * ⨍ x in euclideanBall d r, |f x| := by
    rw [setAverage_eq, smul_eq_mul, measureReal_def, ← mul_assoc, mul_inv_cancel₀ hvol.ne',
      one_mul]
  rw [hav]
  exact mul_le_mul_of_nonneg_left hmean' hvol.le

/-- A ball cutoff times a fixed vector is a local test on any domain containing the ball. -/
theorem isLocalVecTest_ballCutoff_smul {V : Set (Vec d)} {r : ℝ} (hBV : euclideanBall d r ⊆ V)
    (η : QuantitativeBallCutoff (0 : Vec d) (r / 2) r) (w : Vec d) :
    IsLocalVecTest V (fun x => η.toFun x • w) where
  contDiff := η.smooth.smul contDiff_const
  hasCompactSupport := by
    have h : HasCompactSupport (η.toFun • fun _ : Vec d => w) := η.hasCompactSupport.smul_right
    exact h
  tsupport_subset := (tsupport_smul_subset_left η.toFun (fun _ => w)).trans
    (η.support_subset.trans hBV)

theorem abs_fderiv_apply_basisVec_le (η : Vec d → ℝ) (x : Vec d) (i : Fin d) :
    |fderiv ℝ η x (basisVec i)| ≤ ‖fderiv ℝ η x‖ := by
  have h := (fderiv ℝ η x).le_opNorm (basisVec i)
  have hb : ‖(basisVec i : Vec d)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases hji : j = i <;> simp [basisVec, hji]
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ η x (basisVec i)‖ ≤ ‖fderiv ℝ η x‖ * ‖(basisVec i : Vec d)‖ := h
    _ ≤ ‖fderiv ℝ η x‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ‖fderiv ℝ η x‖ := mul_one _

theorem vecNormSq_smoothGrad_le (η : Vec d → ℝ) (x : Vec d) :
    vecNormSq (smoothGrad η x) ≤ d * ‖fderiv ℝ η x‖ ^ 2 := by
  change ∑ i, smoothGrad η x i * smoothGrad η x i ≤ _
  calc ∑ i, smoothGrad η x i * smoothGrad η x i ≤ ∑ _i : Fin d, ‖fderiv ℝ η x‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := abs_fderiv_apply_basisVec_le η x i
        have h2 : |smoothGrad η x i| ≤ ‖fderiv ℝ η x‖ := h
        nlinarith [abs_nonneg (smoothGrad η x i), sq_abs (smoothGrad η x i)]
    _ = d * ‖fderiv ℝ η x‖ ^ 2 := by simp

theorem eVolumeAverage_le_of_le {V : Set (Vec d)} (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ⊤)
    {f : Vec d → ENNReal} {c : ENNReal} (hf : ∀ x, f x ≤ c) : eVolumeAverage V f ≤ c := by
  unfold eVolumeAverage
  rw [ENNReal.div_le_iff hV0 hVtop]
  calc ∫⁻ x in V, f x ≤ ∫⁻ _x in V, c := lintegral_mono hf
    _ = c * volume V := by rw [setLIntegral_const]

/-- The normalized test norm of a ball cutoff times a vector. -/
theorem h1NormSq_ballCutoff_smul_le {V : Set (Vec d)} {r : ℝ} (hr : 0 < r)
    (hBV : euclideanBall d r ⊆ V) (hVtop : volume V ≠ ⊤)
    (η : QuantitativeBallCutoff (0 : Vec d) (r / 2) r) (w : Vec d) :
    h1NormSq V (fun x => η.toFun x • w) ≤
      ENNReal.ofReal (vecNormSq w * ((volume (euclideanBall d r)).toReal ^ (-(2 : ℝ) / d) +
        d * (2 * quantitativeBallCutoffGradientConst d / r) ^ 2)) := by
  have hBpos := volume_euclideanBall_pos' (d := d) hr
  have hBfin := volume_euclideanBall_ne_top' (d := d) r
  have hVpos : 0 < volume V := lt_of_lt_of_le hBpos (measure_mono hBV)
  have hBreal : 0 < (volume (euclideanBall d r)).toReal := ENNReal.toReal_pos hBpos.ne' hBfin
  have hVreal : (volume (euclideanBall d r)).toReal ≤ (volume V).toReal :=
    ENNReal.toReal_mono hVtop (measure_mono hBV)
  have hdiffη : Differentiable ℝ η.toFun := η.smooth.differentiable (by simp)
  have hgrad (x : Vec d) : ‖fderiv ℝ η.toFun x‖ ≤ 2 * quantitativeBallCutoffGradientConst d / r := by
    have h := η.gradient_bound x
    have hrr : r - r / 2 = r / 2 := by ring
    rw [hrr] at h
    calc ‖fderiv ℝ η.toFun x‖ ≤ quantitativeBallCutoffGradientConst d / (r / 2) := h
      _ = 2 * quantitativeBallCutoffGradientConst d / r := by field_simp
  have hG : 0 ≤ 2 * quantitativeBallCutoffGradientConst d / r :=
    le_trans (norm_nonneg _) (hgrad 0)
  -- the value part
  have hval (x : Vec d) : ENNReal.ofReal (vecNormSq (η.toFun x • w)) ≤
      ENNReal.ofReal (vecNormSq w) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 := η.nonneg x
    have h1 := η.le_one x
    have : vecNormSq (η.toFun x • w) = η.toFun x ^ 2 * vecNormSq w := by
      simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this]
    have hsq : η.toFun x ^ 2 ≤ 1 := by nlinarith
    nlinarith [vecNormSq_nonneg w]
  -- the gradient part
  have hgradpt (x : Vec d) : ENNReal.ofReal (∑ j, vecNormSq (smoothGrad (fun y => (η.toFun y • w) j) x)) ≤
      ENNReal.ofReal (vecNormSq w * (d * (2 * quantitativeBallCutoffGradientConst d / r) ^ 2)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hcomp (j : Fin d) : smoothGrad (fun y => (η.toFun y • w) j) x =
        w j • smoothGrad η.toFun x := by
      have : (fun y => (η.toFun y • w) j) = fun y => w j * η.toFun y := by
        funext y
        simp [smul_eq_mul, mul_comm]
      rw [this, smoothGrad_const_mul hdiffη]
    have hsum : ∑ j, vecNormSq (smoothGrad (fun y => (η.toFun y • w) j) x) =
        vecNormSq w * vecNormSq (smoothGrad η.toFun x) := by
      simp only [hcomp]
      simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsum]
    have h1 := vecNormSq_smoothGrad_le η.toFun x
    have h2 : ‖fderiv ℝ η.toFun x‖ ^ 2 ≤ (2 * quantitativeBallCutoffGradientConst d / r) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hgrad x) 2
    have h3 : vecNormSq (smoothGrad η.toFun x) ≤ d * (2 * quantitativeBallCutoffGradientConst d / r) ^ 2 :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d))
    exact mul_le_mul_of_nonneg_left h3 (vecNormSq_nonneg w)
  have hpow : volume V ^ (-(2 : ℝ) / d) ≤
      ENNReal.ofReal ((volume (euclideanBall d r)).toReal ^ (-(2 : ℝ) / d)) := by
    have hVpos' : 0 < (volume V).toReal := ENNReal.toReal_pos hVpos.ne' hVtop
    rw [← ENNReal.ofReal_toReal hVtop, ENNReal.ofReal_rpow_of_pos hVpos']
    refine ENNReal.ofReal_le_ofReal ?_
    exact Real.rpow_le_rpow_of_nonpos hBreal hVreal
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg d))
  unfold h1NormSq
  have hA := eVolumeAverage_le_of_le hVpos.ne' hVtop hval
  have hB := eVolumeAverage_le_of_le hVpos.ne' hVtop hgradpt
  calc volume V ^ (-(2 : ℝ) / d) *
        eVolumeAverage V (fun x => ENNReal.ofReal (vecNormSq (η.toFun x • w))) +
      eVolumeAverage V (fun x => ENNReal.ofReal
        (∑ j, vecNormSq (smoothGrad (fun y => (η.toFun y • w) j) x)))
      ≤ ENNReal.ofReal ((volume (euclideanBall d r)).toReal ^ (-(2 : ℝ) / d)) *
          ENNReal.ofReal (vecNormSq w) +
        ENNReal.ofReal (vecNormSq w * (d * (2 * quantitativeBallCutoffGradientConst d / r) ^ 2)) := by
        gcongr
    _ = ENNReal.ofReal (vecNormSq w * ((volume (euclideanBall d r)).toReal ^ (-(2 : ℝ) / d) +
        d * (2 * quantitativeBallCutoffGradientConst d / r) ^ 2)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hBreal.le _),
          ← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg hBreal.le _) (vecNormSq_nonneg w))
            (mul_nonneg (vecNormSq_nonneg w) (by positivity))]
        congr 1
        ring

end EinsteinFull.Homogenization
