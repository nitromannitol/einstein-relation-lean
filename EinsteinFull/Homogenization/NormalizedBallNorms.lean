import HCPoly.Provider.Regularity.CorrectorNormalizedL2Bridge
import HCPoly.Provider.PolynomialHomogenization.Root.Corrector.AffineLiouvilleGrowth
import EinsteinRelation.External.AKMEnergyDensity

/-!
# Normalized `L²` norms on Euclidean balls

Elementary facts about the volume-normalized `L²` norm of Armstrong, Kuusi and Loher,
*Homogenization at a polynomial scale in high contrast*, on centered Euclidean balls: its
identification with the normalized square average used by Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, the triangle inequality,
homogeneity, the bound for linear functions, and the behaviour under dilation.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.External.AKM
open _root_.Homogenization hiding euclideanBall Vec Mat euclideanNorm isOpen_euclideanBall
open _root_.Homogenization.HighContrast

variable {d : ℕ}

theorem ball_zero_eq_euclideanBall {R : ℝ} (hR : 0 < R) :
    ball (0 : Vec d) R = euclideanBall d R := by
  ext x
  simp only [ball, euclideanBall, euclideanBallAt, sub_zero]
  have hsq : euclideanSq x = vecNormSq x := rfl
  show Real.sqrt (euclideanSq x) < R ↔ _
  rw [Real.sqrt_lt' hR, hsq]
  exact Iff.rfl

theorem volume_euclideanBall_pos' {R : ℝ} (hR : 0 < R) :
    0 < volume (euclideanBall d R) :=
  (isOpen_euclideanBall d R).measure_pos volume ⟨0, by
    simp [euclideanBall, euclideanBallAt, vecNormSq, vecDot]; positivity⟩

theorem volume_euclideanBall_ne_top' (R : ℝ) : volume (euclideanBall d R) ≠ ⊤ :=
  Book.Ch01.volume_euclideanBall_ne_top (0 : Vec d) R

/-- On a ball, the normalized `L²` norm is the square root of the square average. -/
theorem normalizedL2Norm_euclideanBall_eq_ofReal {R : ℝ} (hR : 0 < R) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (ball 0 R))) :
    normalizedL2Norm (euclideanBall d R) u =
      ENNReal.ofReal (Real.sqrt (⨍ x in ball 0 R, u x ^ 2)) := by
  rw [ball_zero_eq_euclideanBall hR] at hu ⊢
  have hpos := volume_euclideanBall_pos' (d := d) hR
  have hfin := volume_euclideanBall_ne_top' (d := d) R
  have hint : Integrable (fun x => u x ^ 2) (volume.restrict (euclideanBall d R)) :=
    hu.integrable_sq
  unfold normalizedL2Norm eVolumeAverage
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => sq_nonneg (u x))]
  rw [setAverage_eq, smul_eq_mul, Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  congr 1
  rw [measureReal_def, ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_div_of_pos
    (ENNReal.toReal_pos hpos.ne' hfin), div_eq_inv_mul, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

theorem normalizedL2Norm_add_le {V : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict V))
    (hg : AEStronglyMeasurable g (volume.restrict V)) :
    normalizedL2Norm V (fun x => f x + g x) ≤ normalizedL2Norm V f + normalizedL2Norm V g := by
  have hf' : AEStronglyMeasurable f (volumeNormalizedMeasure V) := hf.smul_measure _
  have hg' : AEStronglyMeasurable g (volumeNormalizedMeasure V) := hg.smul_measure _
  rw [normalizedL2Norm_eq_eLpNorm_volumeNormalizedMeasure V (fun x => f x + g x) (hf'.add hg'),
    normalizedL2Norm_eq_eLpNorm_volumeNormalizedMeasure V _ hf',
    normalizedL2Norm_eq_eLpNorm_volumeNormalizedMeasure V _ hg']
  exact eLpNorm_add_le (by norm_num)

theorem normalizedL2Norm_const_mul (V : Set (Vec d)) (c : ℝ) (f : Vec d → ℝ) :
    normalizedL2Norm V (fun x => c * f x) = ENNReal.ofReal |c| * normalizedL2Norm V f := by
  unfold normalizedL2Norm eVolumeAverage
  have hpt (x : Vec d) : ENNReal.ofReal ((c * f x) ^ 2) =
      ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (f x ^ 2) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg c), mul_pow]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_div_assoc,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg c) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq_eq_abs]

/-- A pointwise bound on a ball bounds the normalized norm. -/
theorem normalizedL2Norm_le_of_forall_le {R : ℝ} (hR : 0 < R) {f : Vec d → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ x ∈ euclideanBall d R, |f x| ≤ M) :
    normalizedL2Norm (euclideanBall d R) f ≤ ENNReal.ofReal M := by
  have hpos := volume_euclideanBall_pos' (d := d) hR
  have hfin := volume_euclideanBall_ne_top' (d := d) R
  unfold normalizedL2Norm eVolumeAverage
  have hle : (∫⁻ x in euclideanBall d R, ENNReal.ofReal (f x ^ 2)) ≤
      ∫⁻ _x in euclideanBall d R, ENNReal.ofReal (M ^ 2) := by
    refine setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal ?_
    have := hf x hx
    nlinarith [abs_nonneg (f x), sq_abs (f x)]
  rw [setLIntegral_const] at hle
  have hdiv : (∫⁻ x in euclideanBall d R, ENNReal.ofReal (f x ^ 2)) /
      volume (euclideanBall d R) ≤ ENNReal.ofReal (M ^ 2) := by
    rw [ENNReal.div_le_iff hpos.ne' hfin]
    exact hle
  calc ((∫⁻ x in euclideanBall d R, ENNReal.ofReal (f x ^ 2)) /
        volume (euclideanBall d R)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (M ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hdiv (by norm_num)
    _ = ENNReal.ofReal M := by
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg M) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hM]

theorem abs_vecDot_le_of_mem_euclideanBall {R : ℝ} (hR : 0 ≤ R) (e : Vec d) {x : Vec d}
    (hx : x ∈ euclideanBall d R) :
    |vecDot e x| ≤ Real.sqrt (vecNormSq e) * R := by
  have hx' : vecNormSq x < R ^ 2 := by simpa [euclideanBall, euclideanBallAt] using hx
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq e x
  have h1 : vecDot e x ^ 2 ≤ (Real.sqrt (vecNormSq e) * R) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (vecNormSq_nonneg e)]
    calc vecDot e x ^ 2 ≤ vecNormSq e * vecNormSq x := hcs
      _ ≤ vecNormSq e * R ^ 2 :=
        mul_le_mul_of_nonneg_left hx'.le (vecNormSq_nonneg e)
  exact abs_le_of_sq_le_sq' h1 (by positivity) |>.elim (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)

theorem normalizedL2Norm_vecDot_le {R : ℝ} (hR : 0 < R) (e : Vec d) :
    normalizedL2Norm (euclideanBall d R) (fun x => vecDot e x) ≤
      ENNReal.ofReal (Real.sqrt (vecNormSq e) * R) :=
  normalizedL2Norm_le_of_forall_le hR (by positivity)
    fun x hx => abs_vecDot_le_of_mem_euclideanBall hR.le e hx

/-- Dilation by two on a ball is controlled by the normalized norm on an enlarged ball. -/
theorem exists_normalizedL2Norm_dilate_le :
    ∃ q A : ℝ, 0 < q ∧ 0 ≤ A ∧ ∀ (R : ℝ), 0 < R → ∀ u : Vec d → ℝ,
      normalizedL2Norm (euclideanBall d R) (fun x => u ((2 : ℝ) • x)) ≤
        ENNReal.ofReal A * normalizedL2Norm (euclideanBall d (q * R)) u := by
  let L : Mat d := (2 : ℝ) • (1 : Mat d)
  have hL : IsUnit L.det := by
    rw [isUnit_iff_ne_zero]
    simp [L]
  have hmul (y : Vec d) : matVecMul L y = (2 : ℝ) • y := by
    funext i
    simp [L, matVecMul, Matrix.one_apply, smul_eq_mul]
  have hq : 0 < Root.affineBallFactor L := zero_lt_one.trans_le (Root.one_le_affineBallFactor L)
  have hbase : 0 ≤ |L.det|⁻¹ * Root.affineBallFactor L ^ d :=
    mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (pow_nonneg hq.le _)
  refine ⟨Root.affineBallFactor L, (|L.det|⁻¹ * Root.affineBallFactor L ^ d) ^ (1 / 2 : ℝ),
    hq, Real.rpow_nonneg hbase _, fun R hR u => ?_⟩
  have h := Root.normalizedL2Norm_affinePullback_ball_le hL hR u
  simp only [hmul] at h
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg hbase (by norm_num)]

end EinsteinFull.Homogenization
