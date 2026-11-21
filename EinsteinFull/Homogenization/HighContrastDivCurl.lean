import EinsteinFull.Homogenization.HighContrastCorrectorBounds
import EinsteinFull.Homogenization.DivCurlEstimates

/-!
# The div-curl argument for high-contrast correctors

On the event of the homogenization theorem of Armstrong, Kuusi and Loher, *Homogenization at a
polynomial scale in high contrast*, the symmetric part `s̄` of the homogenized matrix of a
`(1, K)`-elliptic law satisfies `|e|² ≤ e · s̄ e ≤ K² |e|²`.

The proof is the classical div-curl argument (Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Section 1). On the origin cube of side
`3ᴺ`, weighted by the square of the inner cutoff of relative width `1/4`, the mean gradient of
the corrected affine function of slope `e` tends to `e` times the mean weight, by the corrector
clause of the homogenization theorem; its mean flux paired with `e` tends to `e · s̄ e` times
the mean weight, by the flux clause; and its weighted energy has the same limit, since the cross
term is controlled by the sublinearity of the corrector. Cauchy–Schwarz then gives the two
bounds.
-/

open MeasureTheory Filter Topology

namespace EinsteinFull.Homogenization

open _root_.Homogenization hiding euclideanBall
open _root_.Homogenization.HighContrast

variable {d : ℕ}

theorem norm_fderiv_sq_le {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ x, 0 ≤ η x)
    (hη1 : ∀ x, η x ≤ 1) {M : ℝ} (hM : ∀ x, ‖fderiv ℝ η x‖ ≤ M) (x : Vec d) :
    ‖fderiv ℝ (fun y => η y ^ 2) x‖ ≤ 2 * M := by
  have hd : DifferentiableAt ℝ η x := (hη.differentiable (by simp)).differentiableAt
  have heq : (fun y => η y ^ 2) = fun y => η y * η y := by
    funext y
    ring
  have hle : ‖η x • fderiv ℝ η x‖ ≤ M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη0 x)]
    calc η x * ‖fderiv ℝ η x‖ ≤ 1 * M := mul_le_mul (hη1 x) (hM x) (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  have hfd : fderiv ℝ (fun y => η y * η y) x = η x • fderiv ℝ η x + η x • fderiv ℝ η x :=
    (hd.hasFDerivAt.mul hd.hasFDerivAt).fderiv
  rw [heq, hfd]
  calc ‖η x • fderiv ℝ η x + η x • fderiv ℝ η x‖
      ≤ ‖η x • fderiv ℝ η x‖ + ‖η x • fderiv ℝ η x‖ := norm_add_le _ _
    _ ≤ M + M := add_le_add hle hle
    _ = 2 * M := by ring

theorem tsupport_sq_subset (η : Vec d → ℝ) : tsupport (fun y => η y ^ 2) ⊆ tsupport η :=
  closure_mono fun x hx => by
    simp only [Function.mem_support] at hx ⊢
    intro h
    exact hx (by rw [h]; ring)

theorem sqrt_vecNormSq_add_le (x y : Vec d) :
    Real.sqrt (vecNormSq (x + y)) ≤ Real.sqrt (vecNormSq x) + Real.sqrt (vecNormSq y) := by
  have hexp : vecNormSq (x + y) = vecNormSq x + 2 * vecDot x y + vecNormSq y := by
    simp only [vecNormSq, vecDot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Real.sqrt_le_left (by positivity), hexp, add_sq, Real.sq_sqrt (vecNormSq_nonneg x),
    Real.sq_sqrt (vecNormSq_nonneg y)]
  have h := abs_vecDot_le_sqrt_mul_sqrt x y
  have h2 := le_abs_self (vecDot x y)
  nlinarith

/-- The reverse triangle inequality for the Euclidean norm, in coordinates. -/
theorem mul_sqrt_sub_sqrt_le (t : ℝ) (ht : 0 ≤ t) (e y : Vec d) :
    t * Real.sqrt (vecNormSq e) - Real.sqrt (∑ i, y i ^ 2) ≤
      Real.sqrt (∑ i, (e i * t + y i) ^ 2) := by
  have h1 : ∑ i, (e i * t + y i) ^ 2 = vecNormSq (fun i => e i * t + y i) := by
    simp [vecNormSq, vecDot, sq]
  have h2 : ∑ i, y i ^ 2 = vecNormSq (-y) := by
    simp [vecNormSq, vecDot, sq]
  have h3 : vecNormSq ((fun i => e i * t + y i) + -y) = t ^ 2 * vecNormSq e := by
    simp only [vecNormSq, vecDot, Pi.add_apply, Pi.neg_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h := sqrt_vecNormSq_add_le (fun i => e i * t + y i) (-y)
  rw [h3, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht] at h
  rw [h1, h2]
  linarith

/-- The algebraic decomposition of the flux defect paired with `e`. -/
theorem vecDot_fluxDefect_eq (A B : Mat d) (e v : Vec d) :
    vecDot (matVecMul (A - skewPart B) v - matVecMul (symmPart B) e) e =
      vecDot e (matVecMul A v) - vecDot e (matVecMul (symmPart B) e) -
        vecDot (matVecMul (matTranspose (skewPart B)) e) (v - e) := by
  have h0 := vecDot_matVecMul_skewPart_self_eq_zero B e
  have h1 : vecDot e (matVecMul (skewPart B) (v - e)) =
      vecDot (matVecMul (matTranspose (skewPart B)) e) (v - e) := by
    rw [← vecDot_matVecMul_transpose]
    simp only [matTranspose, Matrix.transpose_transpose]
  have h2 : matVecMul (skewPart B) v =
      matVecMul (skewPart B) e + matVecMul (skewPart B) (v - e) := by
    rw [← matVecMul_add]
    congr 1
    abel
  rw [vecDot_comm _ e, vecDot_sub_right, sub_matVecMul, vecDot_sub_right, h2,
    vecDot_add_right e (matVecMul (skewPart B) e), h0, h1]
  ring

theorem eventually_abs_le_of_tendsto_zero {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, |f N| ≤ ε := by
  filter_upwards [hf.eventually (Metric.ball_mem_nhds 0 hε)] with N hN
  have h : dist (f N) 0 < ε := hN
  rw [Real.dist_eq, sub_zero] at h
  exact h.le

theorem tendsto_scale_rpow_neg [NeZero d] {κ : ℝ} (hκ : 0 < κ) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun N : ℕ => ((Real.sqrt d * (3 : ℝ) ^ N) / X) ^ (-κ)) atTop (𝓝 0) := by
  have hd : 0 < Real.sqrt d :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d)))
  have h1 : Tendsto (fun N : ℕ => (Real.sqrt d * (3 : ℝ) ^ N) / X) atTop atTop :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).const_mul_atTop
      hd).atTop_div_const hX
  exact (tendsto_rpow_neg_atTop hκ).comp h1

/-- A function integrable for the normalized cube measure and vanishing outside the cube is
integrable on the whole space. -/
theorem integrable_of_integrable_normalizedCubeMeasure (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : Integrable f (normalizedCubeMeasure Q)) (h0 : ∀ x, x ∉ cubeSet Q → f x = 0) :
    Integrable f volume := by
  have hv : 0 < cubeVolume Q := cubeVolume_pos Q
  have hc : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hv)).ne'
  have h1 : IntegrableOn f (cubeSet Q) volume := by
    rw [normalizedCubeMeasure, integrable_smul_measure hc ENNReal.ofReal_ne_top] at hf
    exact hf
  exact h1.integrable_of_forall_notMem_eq_zero h0

theorem cubeAverage_sq_le_one (Q : TriadicCube d) {η : Vec d → ℝ} (hηc : Continuous η)
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) :
    cubeAverage Q (fun x => η x ^ 2) ≤ 1 := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) := ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hη : MemLp η 2 (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_bound Q hηc.aestronglyMeasurable (c := 1)
      fun x => abs_le.mpr ⟨by linarith [hη0 x], hη1 x⟩
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  calc ∫ x, η x ^ 2 ∂normalizedCubeMeasure Q ≤ ∫ _x, (1 : ℝ) ∂normalizedCubeMeasure Q :=
        integral_mono hη.integrable_sq (integrable_const 1)
          fun x => pow_le_one₀ (hη0 x) (hη1 x)
    _ = 1 := by simp

/-- **Cutoff pairing on origin cubes.** If `L G` has normalized `H⁻¹` norm at most `r B` on the
ellipsoid `E_r`, `r = √d 3ᴺ`, the integral of a cutoff supported in the origin cube of side `3ᴺ`
against `G · (Lᵀ w)` is bounded by `|w| B 3ᴺ (M + |B₁|^(-1/d) 3⁻ᴺ)` times the cube volume, up to a
factor depending on `d` and the ellipsoid. -/
theorem abs_integral_le_of_negOneNorm_originCube [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) (N : ℕ) {G : Vec d → Vec d} {L : Mat d} {B : ℝ} (hB : 0 ≤ B)
    (hneg : negOneNorm (ellipsoid abar (Real.sqrt d * (3 : ℝ) ^ N))
        (fun x => matVecMul L (G x)) ≤ ENNReal.ofReal (Real.sqrt d * (3 : ℝ) ^ N * B))
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηcs : HasCompactSupport η)
    (hηQ : tsupport η ⊆ openCubeSet (originCube d (N : ℤ))) (hη0 : ∀ x, 0 ≤ η x)
    (hη1 : ∀ x, η x ≤ 1) {M : ℝ} (hM : ∀ x, ‖fderiv ℝ η x‖ ≤ M) (w : Vec d)
    (hint : Integrable (fun x => η x * vecDot (G x) (matVecMul (matTranspose L) w))) :
    |∫ x, η x * vecDot (G x) (matVecMul (matTranspose L) w)| ≤
      Real.sqrt (volume (ellipsoid abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
        Real.sqrt (vecNormSq w) * B * (3 : ℝ) ^ N *
        (M + ballVolumeConstant d * ((3 : ℝ) ^ N)⁻¹) * cubeVolume (originCube d (N : ℤ)) := by
  set r := Real.sqrt d * (3 : ℝ) ^ N with hr_def
  have hr : 0 < r := EllipticWholeSpaceSolution.sqrt_mul_three_pow_pos N
  have hVtop : volume (ellipsoid abar r) ≠ ⊤ := (volume_ellipsoid_lt_top hS r).ne
  have hVpos : 0 < volume (ellipsoid abar r) := volume_ellipsoid_pos abar hr
  have hAV : openCubeSet (originCube d (N : ℤ)) ⊆ ellipsoid abar r :=
    (openCubeSet_subset_cubeSet _).trans ((cubeSet_originCube_subset_euclideanBall N).trans
      (euclideanBallAt_zero_subset_ellipsoid abar r))
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hmain := abs_integral_mul_vecDot_le_of_negOneNorm hVpos.ne' hVtop
    (isOpen_openCubeSet _).measurableSet hAV (mul_nonneg hr.le hB) hneg hη hηcs hηQ hη0 hη1 hM
    w hint
  refine hmain.trans ?_
  set v := (volume (ellipsoid abar r)).toReal with hv
  have hv0 : 0 < v := ENNReal.toReal_pos hVpos.ne' hVtop
  set a := (volume (openCubeSet (originCube d (N : ℤ)))).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have haR : a = cubeVolume (originCube d (N : ℤ)) := volume_openCubeSet_toReal _
  set T := v ^ (-(2 : ℝ) / d) + d * M ^ 2 with hT
  have hsplit : v * (Real.sqrt (vecNormSq w * (a / v) * T) * (r * B)) =
      Real.sqrt v * Real.sqrt (vecNormSq w) * Real.sqrt a * Real.sqrt T * (r * B) := by
    rw [Real.sqrt_mul (mul_nonneg (vecNormSq_nonneg w) (div_nonneg ha0 hv0.le)),
      Real.sqrt_mul (vecNormSq_nonneg w), Real.sqrt_div' a hv0.le]
    have hsv : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv0.le
    have hsv0 : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
    have hvv : v * (Real.sqrt v)⁻¹ = Real.sqrt v := by
      rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hsv0.ne', hsv]
    calc v * (Real.sqrt (vecNormSq w) * (Real.sqrt a / Real.sqrt v) * Real.sqrt T * (r * B))
        = (v * (Real.sqrt v)⁻¹) * Real.sqrt (vecNormSq w) * Real.sqrt a * Real.sqrt T *
            (r * B) := by ring
      _ = _ := by rw [hvv]
  have hTle := sqrt_testFactor_le abar hS N hM0
  rw [← hv, ← hT] at hTle
  have hvsq := sqrt_volume_ellipsoid_sqrt_mul abar N
  rw [← hr_def, ← hv] at hvsq
  have hdd : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hQ : Real.sqrt ((3 : ℝ) ^ (N * d)) * Real.sqrt a = a := by
    rw [haR, cubeVolume_originCube, ← pow_mul]
    exact Real.mul_self_sqrt (by positivity)
  rw [hsplit, hvsq, ← haR]
  have hrB : r * B = Real.sqrt d * (3 : ℝ) ^ N * B := by rw [hr_def]
  rw [hrB]
  calc Real.sqrt (volume (ellipsoid abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) *
        Real.sqrt ((3 : ℝ) ^ (N * d)) * Real.sqrt (vecNormSq w) * Real.sqrt a * Real.sqrt T *
        (Real.sqrt d * (3 : ℝ) ^ N * B)
      ≤ Real.sqrt (volume (ellipsoid abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) *
        Real.sqrt ((3 : ℝ) ^ (N * d)) * Real.sqrt (vecNormSq w) * Real.sqrt a *
        (Real.sqrt d * (M + ballVolumeConstant d * ((3 : ℝ) ^ N)⁻¹)) *
        (Real.sqrt d * (3 : ℝ) ^ N * B) := by
        gcongr
    _ = Real.sqrt (volume (ellipsoid abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) *
        (Real.sqrt d * Real.sqrt d) * Real.sqrt (vecNormSq w) * B * (3 : ℝ) ^ N *
        (M + ballVolumeConstant d * ((3 : ℝ) ^ N)⁻¹) *
        (Real.sqrt ((3 : ℝ) ^ (N * d)) * Real.sqrt a) := by ring
    _ = _ := by rw [hdd, hQ]

/-- The gradient bound of the inner cutoff of relative width `1/4` of an origin cube, at the
unit scale. -/
noncomputable def originCutoffConst (d : ℕ) : ℝ :=
  16 * d * smoothTransitionProfile.derivBound

theorem originCutoffConst_nonneg (d : ℕ) : 0 ≤ originCutoffConst d := by
  unfold originCutoffConst
  have := smoothTransitionProfile.derivBound_nonneg
  positivity

theorem originCutoff_smooth (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (innerCubeCutoff (originCube d (N : ℤ)) (1 / 4)) :=
  innerCubeCutoff_smooth _ (by norm_num) le_rfl

theorem norm_fderiv_originCutoff_le (N : ℕ) (x : Vec d) :
    ‖fderiv ℝ (innerCubeCutoff (originCube d (N : ℤ)) (1 / 4)) x‖ ≤
      originCutoffConst d * ((3 : ℝ) ^ N)⁻¹ := by
  have h := norm_fderiv_innerCubeCutoff_le (originCube d (N : ℤ))
    (by norm_num : (0 : ℝ) < 1 / 4) le_rfl x
  rw [cubeScaleFactor_originCube] at h
  refine h.trans (le_of_eq ?_)
  unfold originCutoffConst
  field_simp
  ring

theorem originCutoff_sq_smooth (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2) :=
  (originCutoff_smooth N).pow 2

theorem tsupport_originCutoff_sq_subset (N : ℕ) :
    tsupport (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2) ⊆
      openCubeSet (originCube d (N : ℤ)) :=
  (tsupport_sq_subset _).trans (tsupport_innerCubeCutoff_subset _ (by norm_num) le_rfl)

theorem originCutoff_sq_hasCompactSupport (N : ℕ) :
    HasCompactSupport (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2) :=
  IsCompact.of_isClosed_subset (innerCubeCutoff_hasCompactSupport _ (by norm_num) le_rfl)
    (isClosed_tsupport _) (tsupport_sq_subset _)

theorem originCutoff_sq_le_one (N : ℕ) (x : Vec d) :
    innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 ≤ 1 :=
  pow_le_one₀ (innerCubeCutoff_nonneg _ _ x) (innerCubeCutoff_le_one _ _ x)

theorem norm_fderiv_originCutoff_sq_le (N : ℕ) (x : Vec d) :
    ‖fderiv ℝ (fun y => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) y ^ 2) x‖ ≤
      2 * (originCutoffConst d * ((3 : ℝ) ^ N)⁻¹) :=
  norm_fderiv_sq_le (originCutoff_smooth N) (innerCubeCutoff_nonneg _ _)
    (innerCubeCutoff_le_one _ _) (norm_fderiv_originCutoff_le N) x

theorem originCutoff_sq_eq_zero (N : ℕ) {x : Vec d} (hx : x ∉ cubeSet (originCube d (N : ℤ))) :
    innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 = 0 := by
  rw [innerCubeCutoff_eq_zero_of_not_mem _ (by norm_num) le_rfl hx]
  ring

namespace EllipticWholeSpaceSolution

variable {K : ℝ} (s : EllipticWholeSpaceSolution d K)

/-- The solution energy is at most twice `|e|²` plus twice the corrector energy. -/
theorem cubeAverage_vecNormSq_Dv_le [NeZero d] (e : Vec d) (N : ℕ) :
    cubeAverage (originCube d (N : ℤ)) (fun x => vecNormSq (s.Dv x)) ≤
      2 * vecNormSq e + 2 * cubeAverage (originCube d (N : ℤ))
        (fun x => vecNormSq (s.correctorGrad e x)) := by
  have hDv := s.integrableOn_vecNormSq_Dv N
  have hcg : IntegrableOn (fun x => vecNormSq (s.correctorGrad e x))
      (cubeSet (originCube d (N : ℤ))) volume := by
    have h := integrable_finsetSum (μ := volume.restrict (cubeSet (originCube d (N : ℤ))))
      Finset.univ fun i _ => ((s.memLp_cubeSet_Dv N i).sub (memLp_const (e i))).integrable_sq
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [vecNormSq, vecDot, sq, correctorGrad]
  have hint2 : IntegrableOn (fun x => 2 * vecNormSq e + 2 * vecNormSq (s.correctorGrad e x))
      (cubeSet (originCube d (N : ℤ))) volume :=
    (integrableOn_const (C := 2 * vecNormSq e) (volume_cubeSet_lt_top _).ne).add
      (hcg.const_mul 2)
  calc cubeAverage (originCube d (N : ℤ)) (fun x => vecNormSq (s.Dv x))
      ≤ cubeAverage (originCube d (N : ℤ))
          (fun x => 2 * vecNormSq e + 2 * vecNormSq (s.correctorGrad e x)) :=
        mul_le_mul_of_nonneg_left
          (setIntegral_mono_on hDv hint2 (measurableSet_cubeSet _) fun x _ => by
            have h := vecNormSq_sub_le_two_mul (s.correctorGrad e x) (-e)
            have h1 : s.correctorGrad e x - -e = s.Dv x := by simp [correctorGrad]
            have h2 : vecNormSq (-e) = vecNormSq e := by simp [vecNormSq, vecDot]
            rw [h1, h2] at h
            linarith)
          (inv_nonneg.mpr (cubeVolume_nonneg _))
    _ = _ := cubeAverage_const_add_two_mul _ _ hcg

section Weighted

variable [NeZero d] (N : ℕ) {η : Vec d → ℝ} (hηc : Continuous η) (hη0 : ∀ x, 0 ≤ η x)
  (hη1 : ∀ x, η x ≤ 1)
include hηc hη0 hη1

omit [NeZero d] in
theorem integrable_normalized_cutoff_sq :
    Integrable (fun x => η x ^ 2) (normalizedCubeMeasure (originCube d (N : ℤ))) :=
  (memLp_normalized_cutoff N hηc hη0 hη1).integrable_sq

theorem integrable_normalized_cutoff_sq_mul_Dv (i : Fin d) :
    Integrable (fun x => η x ^ 2 * s.Dv x i) (normalizedCubeMeasure (originCube d (N : ℤ))) := by
  have h : Integrable (fun x => η x * (η x * s.Dv x i))
      (normalizedCubeMeasure (originCube d (N : ℤ))) :=
    (memLp_normalized_cutoff N hηc hη0 hη1).integrable_mul
      (s.memLp_normalized_cutoff_mul_Dv N hηc hη0 hη1 i)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  ring

theorem integrable_normalized_cutoff_sq_mul_correctorGrad (e : Vec d) (i : Fin d) :
    Integrable (fun x => η x ^ 2 * s.correctorGrad e x i)
      (normalizedCubeMeasure (originCube d (N : ℤ))) := by
  refine ((s.integrable_normalized_cutoff_sq_mul_Dv N hηc hη0 hη1 i).sub
    ((integrable_normalized_cutoff_sq N hηc hη0 hη1).const_mul (e i))).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply, correctorGrad]
  ring

theorem integrable_normalized_cutoff_sq_mul_vecDot_correctorGrad (e c : Vec d) :
    Integrable (fun x => η x ^ 2 * vecDot c (s.correctorGrad e x))
      (normalizedCubeMeasure (originCube d (N : ℤ))) := by
  have h := integrable_finsetSum (μ := normalizedCubeMeasure (originCube d (N : ℤ)))
    Finset.univ fun i _ =>
      (s.integrable_normalized_cutoff_sq_mul_correctorGrad N hηc hη0 hη1 e i).const_mul (c i)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [vecDot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cubeAverage_cutoff_sq_mul_vecDot_correctorGrad (e c : Vec d) :
    cubeAverage (originCube d (N : ℤ)) (fun x => η x ^ 2 * vecDot c (s.correctorGrad e x)) =
      ∑ i, c i * cubeAverage (originCube d (N : ℤ))
        (fun x => η x ^ 2 * s.correctorGrad e x i) := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure, ← integral_const_mul]
  rw [← integral_finsetSum _ fun i _ =>
    (s.integrable_normalized_cutoff_sq_mul_correctorGrad N hηc hη0 hη1 e i).const_mul (c i)]
  congr 1
  funext x
  simp only [vecDot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cubeAverage_cutoff_sq_mul_Dv_eq (e : Vec d) (i : Fin d) :
    cubeAverage (originCube d (N : ℤ)) (fun x => η x ^ 2 * s.Dv x i) =
      e i * cubeAverage (originCube d (N : ℤ)) (fun x => η x ^ 2) +
        cubeAverage (originCube d (N : ℤ)) (fun x => η x ^ 2 * s.correctorGrad e x i) := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [← integral_const_mul, ← integral_add
    ((integrable_normalized_cutoff_sq N hηc hη0 hη1).const_mul (e i))
    (s.integrable_normalized_cutoff_sq_mul_correctorGrad N hηc hη0 hη1 e i)]
  congr 1
  funext x
  simp only [correctorGrad, Pi.sub_apply]
  ring

theorem integrable_normalized_weightedFlux (hK : 1 ≤ K) (p : Vec d) :
    Integrable (fun x => η x ^ 2 * vecDot p (matVecMul (s.coeff x) (s.Dv x)))
      (normalizedCubeMeasure (originCube d (N : ℤ))) := by
  have hfg := s.memLp_normalized_cutoff_mul_normDv N hηc hη0 hη1
  have hf := memLp_normalized_cutoff N hηc hη0 hη1
  have hprod : Integrable (fun x => η x * (η x * Real.sqrt (vecNormSq (s.Dv x))))
      (normalizedCubeMeasure (originCube d (N : ℤ))) := hf.integrable_mul hfg
  have hmeasflux : AEStronglyMeasurable (fun x => vecDot p (matVecMul (s.coeff x) (s.Dv x)))
      (normalizedCubeMeasure (originCube d (N : ℤ))) := by
    have hmeasf (i j : Fin d) : Measurable (fun x => s.coeff x i j) :=
      (measurable_pi_iff.mp (measurable_pi_iff.mp s.measurable_coeff i)) j
    have hDv (i : Fin d) := (s.memLp_normalized_Dv N i).aestronglyMeasurable
    simp only [vecDot, matVecMul]
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => aestronglyMeasurable_const.mul ?_
    exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      ((hmeasf i j).aestronglyMeasurable).mul (hDv j)
  refine Integrable.mono' (hprod.const_mul (K * Real.sqrt (vecNormSq p)))
    ((hηc.pow 2).aestronglyMeasurable.mul hmeasflux) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have h := s.abs_vecDot_flux_le hK p x
  calc η x ^ 2 * |vecDot p (matVecMul (s.coeff x) (s.Dv x))|
      ≤ η x ^ 2 * (K * Real.sqrt (vecNormSq p) * Real.sqrt (vecNormSq (s.Dv x))) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by ring

theorem cubeAverage_weightedEnergy_sub_weightedFlux (hK : 1 ≤ K) (e : Vec d) :
    cubeAverage (originCube d (N : ℤ))
        (fun x => η x ^ 2 * vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x))) -
      cubeAverage (originCube d (N : ℤ))
        (fun x => η x ^ 2 * vecDot e (matVecMul (s.coeff x) (s.Dv x))) =
    cubeAverage (originCube d (N : ℤ))
      (fun x => η x ^ 2 * vecDot (s.correctorGrad e x) (matVecMul (s.coeff x) (s.Dv x))) := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [← integral_sub (s.integrable_normalized_weightedEnergy N hηc hη0 hη1 hK)
    (s.integrable_normalized_weightedFlux N hηc hη0 hη1 hK e)]
  congr 1
  funext x
  simp only [correctorGrad]
  rw [vecDot_sub_left]
  ring

theorem integrable_normalized_fluxDefect (hK : 1 ≤ K) (B : Mat d) (e : Vec d) :
    Integrable (fun x => η x ^ 2 * vecDot (matVecMul (s.coeff x - skewPart B) (s.Dv x) -
      matVecMul (symmPart B) e) e) (normalizedCubeMeasure (originCube d (N : ℤ))) := by
  have h1 := s.integrable_normalized_weightedFlux N hηc hη0 hη1 hK e
  have h2 := (integrable_normalized_cutoff_sq N hηc hη0 hη1).const_mul
    (vecDot e (matVecMul (symmPart B) e))
  have h3 := s.integrable_normalized_cutoff_sq_mul_vecDot_correctorGrad N hηc hη0 hη1 e
    (matVecMul (matTranspose (skewPart B)) e)
  refine ((h1.sub h2).sub h3).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  rw [vecDot_fluxDefect_eq]
  simp only [correctorGrad]
  ring

theorem cubeAverage_fluxDefect_eq (hK : 1 ≤ K) (B : Mat d) (e : Vec d) :
    cubeAverage (originCube d (N : ℤ)) (fun x => η x ^ 2 *
        vecDot (matVecMul (s.coeff x - skewPart B) (s.Dv x) - matVecMul (symmPart B) e) e) =
      cubeAverage (originCube d (N : ℤ))
          (fun x => η x ^ 2 * vecDot e (matVecMul (s.coeff x) (s.Dv x))) -
        vecDot e (matVecMul (symmPart B) e) * cubeAverage (originCube d (N : ℤ))
          (fun x => η x ^ 2) -
        cubeAverage (originCube d (N : ℤ)) (fun x => η x ^ 2 *
          vecDot (matVecMul (matTranspose (skewPart B)) e) (s.correctorGrad e x)) := by
  have h1 := s.integrable_normalized_weightedFlux N hηc hη0 hη1 hK e
  have h2 := (integrable_normalized_cutoff_sq N hηc hη0 hη1).const_mul
    (vecDot e (matVecMul (symmPart B) e))
  have h3 := s.integrable_normalized_cutoff_sq_mul_vecDot_correctorGrad N hηc hη0 hη1 e
    (matVecMul (matTranspose (skewPart B)) e)
  have h12 : Integrable (fun x => η x ^ 2 * vecDot e (matVecMul (s.coeff x) (s.Dv x)) -
      vecDot e (matVecMul (symmPart B) e) * η x ^ 2)
      (normalizedCubeMeasure (originCube d (N : ℤ))) := h1.sub h2
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [← integral_const_mul, ← integral_sub h1 h2, ← integral_sub h12 h3]
  congr 1
  funext x
  rw [vecDot_fluxDefect_eq]
  simp only [correctorGrad]
  ring

end Weighted

end EllipticWholeSpaceSolution

section Package

variable {K : ℝ} {hK : 1 ≤ K}
  {P : Measure (EinsteinRelation.Environment.AKMTestIntegralSupport.Coefficient d K)} {κ C : ℝ}

/-- **The weighted mean of the corrector gradient tends to zero.** -/
theorem HighContrastCorrectorPackage.tendsto_cubeAverage_cutoff_sq_correctorGrad [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) (hκ : 0 < κ) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d)
    (i : Fin d) :
    Tendsto (fun N : ℕ => cubeAverage (originCube d (N : ℤ)) (fun x =>
      innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        (pk.wholeSpaceSolution hb hbell e).correctorGrad e x i)) atTop (𝓝 0) := by
  obtain ⟨N₀, hN₀⟩ := exists_sqrt_mul_three_pow_ge (d := d) (pk.X b)
  have hX : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
  refine squeeze_zero_norm' (a := fun N : ℕ =>
    (2 * originCutoffConst d + ballVolumeConstant d) * (pk.pairingConstant e *
      ((Real.sqrt d * (3 : ℝ) ^ N) / pk.X b) ^ (-κ))) ?_ ?_
  · filter_upwards [eventually_ge_atTop N₀] with N hN
    have hpb := pk.pairingBound hC hb hbell e (hN₀ N hN) 0 0 le_rfl (originCube d (N : ℤ))
      (by simp [descendantsAtDepth_zero]) _ (originCutoff_sq_smooth N)
      (originCutoff_sq_hasCompactSupport N) (tsupport_originCutoff_sq_subset N)
      (fun x => sq_nonneg _) (originCutoff_sq_le_one N) _ (norm_fderiv_originCutoff_sq_le N) i
    beta_reduce at hpb
    rw [pk.pairingAmplitude_eq] at hpb
    have hv := cubeVolume_pos (originCube d (N : ℤ))
    have hout : ∫ x in cubeSet (originCube d (N : ℤ)),
        innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
          (pk.wholeSpaceSolution hb hbell e).correctorGrad e x i =
        ∫ x, innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
          (pk.wholeSpaceSolution hb hbell e).correctorGrad e x i := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      rw [originCutoff_sq_eq_zero N hx, zero_mul]
    rw [Real.norm_eq_abs]
    unfold cubeAverage
    rw [hout, abs_mul, abs_of_pos (inv_pos.mpr hv), inv_mul_le_iff₀ hv]
    refine hpb.trans (le_of_eq ?_)
    have hQ : Real.sqrt ((3 : ℝ) ^ (N * d)) * Real.sqrt (cubeVolume (originCube d (N : ℤ))) =
        cubeVolume (originCube d (N : ℤ)) := by
      rw [cubeVolume_originCube, ← pow_mul]
      exact Real.mul_self_sqrt (by positivity)
    have h3 : (3 : ℝ) ^ N * ((3 : ℝ) ^ N)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    calc pk.pairingConstant e * ((Real.sqrt d * (3 : ℝ) ^ N) / pk.X b) ^ (-κ) * (3 : ℝ) ^ N *
          Real.sqrt ((3 : ℝ) ^ (N * d)) * (2 * (originCutoffConst d * ((3 : ℝ) ^ N)⁻¹) +
            ballVolumeConstant d * ((3 : ℝ) ^ N)⁻¹) *
          Real.sqrt (cubeVolume (originCube d (N : ℤ)))
        = pk.pairingConstant e * ((Real.sqrt d * (3 : ℝ) ^ N) / pk.X b) ^ (-κ) *
          ((3 : ℝ) ^ N * ((3 : ℝ) ^ N)⁻¹) * (2 * originCutoffConst d + ballVolumeConstant d) *
          (Real.sqrt ((3 : ℝ) ^ (N * d)) * Real.sqrt (cubeVolume (originCube d (N : ℤ)))) := by
          ring
      _ = _ := by rw [h3, hQ]; ring
  · have h := ((tendsto_scale_rpow_neg (d := d) hκ hX).const_mul (pk.pairingConstant e)).const_mul
      (2 * originCutoffConst d + ballVolumeConstant d)
    rw [mul_zero, mul_zero] at h
    exact h

/-- **The weighted cross term tends to zero.** The pairing of the corrector gradient with the
flux, weighted by the squared inner cutoff, is controlled by the sublinearity of the corrector. -/
theorem HighContrastCorrectorPackage.tendsto_cubeAverage_cutoff_sq_crossTerm [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) (hκ : 0 < κ) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d) :
    Tendsto (fun N : ℕ => cubeAverage (originCube d (N : ℤ)) (fun x =>
      innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        vecDot ((pk.wholeSpaceSolution hb hbell e).correctorGrad e x)
          (matVecMul ((pk.wholeSpaceSolution hb hbell e).coeff x)
            ((pk.wholeSpaceSolution hb hbell e).Dv x)))) atTop (𝓝 0) := by
  obtain ⟨Ē, n₂, hĒ, hE⟩ := pk.exists_energy_bound_of_mem hκ hC hb hbell e
  have hosc := pk.tendsto_oscillation_div hκ hC hb hbell e
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hc0 : 0 ≤ 2 * (Real.sqrt d * originCutoffConst d * K) :=
    mul_nonneg zero_le_two
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (originCutoffConst_nonneg d)) hK0)
  refine squeeze_zero_norm' (a := fun N : ℕ =>
    2 * (Real.sqrt d * originCutoffConst d * K) * Real.sqrt (2 * vecNormSq e + 2 * Ē) *
      (cubeBesovOscillation (originCube d (N : ℤ)) 2
        ((pk.wholeSpaceSolution hb hbell e).corrector e) / (3 : ℝ) ^ N)) ?_ ?_
  · filter_upwards [eventually_ge_atTop n₂] with N hN
    have h := (pk.wholeSpaceSolution hb hbell e).abs_cubeAverage_weighted_correctorGrad_le hK e N
      (originCutoff_smooth N) (innerCubeCutoff_hasCompactSupport _ (by norm_num) le_rfl)
      (tsupport_innerCubeCutoff_subset _ (by norm_num) le_rfl)
      (innerCubeCutoff_nonneg _ _) (innerCubeCutoff_le_one _ _) (norm_fderiv_originCutoff_le N)
    rw [Real.norm_eq_abs]
    refine h.trans ?_
    have hDv : cubeAverage (originCube d (N : ℤ))
        (fun x => vecNormSq ((pk.wholeSpaceSolution hb hbell e).Dv x)) ≤
          2 * vecNormSq e + 2 * Ē := by
      have h1 := (pk.wholeSpaceSolution hb hbell e).cubeAverage_vecNormSq_Dv_le e N
      have h2 := hE N hN
      linarith
    have hsq := Real.sqrt_le_sqrt hDv
    have hosc0 : 0 ≤ cubeBesovOscillation (originCube d (N : ℤ)) 2
        ((pk.wholeSpaceSolution hb hbell e).corrector e) / (3 : ℝ) ^ N :=
      div_nonneg (cubeLpNorm_nonneg _ _ _) (by positivity)
    calc 2 * (Real.sqrt d * (originCutoffConst d * ((3 : ℝ) ^ N)⁻¹) * K) *
          cubeBesovOscillation (originCube d (N : ℤ)) 2
            ((pk.wholeSpaceSolution hb hbell e).corrector e) *
          Real.sqrt (cubeAverage (originCube d (N : ℤ))
            (fun x => vecNormSq ((pk.wholeSpaceSolution hb hbell e).Dv x)))
        = 2 * (Real.sqrt d * originCutoffConst d * K) *
          (cubeBesovOscillation (originCube d (N : ℤ)) 2
            ((pk.wholeSpaceSolution hb hbell e).corrector e) / (3 : ℝ) ^ N) *
          Real.sqrt (cubeAverage (originCube d (N : ℤ))
            (fun x => vecNormSq ((pk.wholeSpaceSolution hb hbell e).Dv x))) := by
          rw [div_eq_mul_inv]
          ring
      _ ≤ 2 * (Real.sqrt d * originCutoffConst d * K) *
          (cubeBesovOscillation (originCube d (N : ℤ)) 2
            ((pk.wholeSpaceSolution hb hbell e).corrector e) / (3 : ℝ) ^ N) *
          Real.sqrt (2 * vecNormSq e + 2 * Ē) :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hc0 hosc0)
      _ = _ := by ring
  · have h := hosc.const_mul (2 * (Real.sqrt d * originCutoffConst d * K) *
      Real.sqrt (2 * vecNormSq e + 2 * Ē))
    rw [mul_zero] at h
    exact h

/-- **The weighted flux defect tends to zero.** The flux of the corrected affine function of
slope `e`, minus the skew part of the homogenized matrix applied to its gradient and minus
`s̄ e`, paired with `e` and weighted by the squared inner cutoff, has mean tending to zero, by
the flux clause of the corrector estimate. -/
theorem HighContrastCorrectorPackage.tendsto_cubeAverage_cutoff_sq_fluxDefect [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) (hκ : 0 < κ) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d) :
    Tendsto (fun N : ℕ => cubeAverage (originCube d (N : ℤ)) (fun x =>
      innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        vecDot (matVecMul ((pk.wholeSpaceSolution hb hbell e).coeff x - skewPart pk.abar)
          ((pk.wholeSpaceSolution hb hbell e).Dv x) - matVecMul (symmPart pk.abar) e) e))
      atTop (𝓝 0) := by
  have hSpd : (symmPart pk.abar).PosDef := posDef_symmPart_of_vecDot_pos pk.posDef
  have hX : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
  have hLw : matVecMul (matTranspose (matSqrt (symmPart pk.abar))⁻¹)
      (matVecMul (matSqrt (symmPart pk.abar)) e) = e := by
    have hT : matTranspose (matSqrt (symmPart pk.abar))⁻¹ = (matSqrt (symmPart pk.abar))⁻¹ := by
      unfold matTranspose
      rw [Matrix.transpose_nonsing_inv, (isSymm_matSqrt _).eq]
    rw [hT, matVecMul_mul, Matrix.nonsing_inv_mul _ (isUnit_det_matSqrt hSpd),
      _root_.Homogenization.matVecMul_one]
  have hs (x : Vec d) : (pk.wholeSpaceSolution hb hbell e).coeff x =
      ellipticRepresentative K b x := rfl
  have hsD (x : Vec d) : (pk.wholeSpaceSolution hb hbell e).Dv x = e + pk.gradPhi e b x := rfl
  obtain ⟨N₀, hN₀⟩ := exists_sqrt_mul_three_pow_ge (d := d) (pk.X b)
  set w := matVecMul (matSqrt (symmPart pk.abar)) e
  refine squeeze_zero_norm' (a := fun N : ℕ =>
    Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
      Real.sqrt (vecNormSq w) * (2 * originCutoffConst d + ballVolumeConstant d) *
      (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) *
        ((Real.sqrt d * (3 : ℝ) ^ N) / pk.X b) ^ (-κ))) ?_ ?_
  · filter_upwards [eventually_ge_atTop N₀] with N hN
    have hr : 0 < Real.sqrt d * (3 : ℝ) ^ N := EllipticWholeSpaceSolution.sqrt_mul_three_pow_pos N
    have hneg := pk.negOneNorm_flux_le hb e hr (hN₀ N hN)
    have hB0 : 0 ≤ C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) *
        ((Real.sqrt d * (3 : ℝ) ^ N) / pk.X b) ^ (-κ) :=
      mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (div_nonneg hr.le hX.le) _)
    have hae : (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        vecDot (matVecMul (b.1 x - skewPart pk.abar) (e + pk.gradPhi e b x) -
          matVecMul (symmPart pk.abar) e) e) =ᵐ[volume]
        fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
          vecDot (matVecMul ((pk.wholeSpaceSolution hb hbell e).coeff x - skewPart pk.abar)
            ((pk.wholeSpaceSolution hb hbell e).Dv x) - matVecMul (symmPart pk.abar) e) e := by
      filter_upwards [ellipticRepresentative_ae_eq b hbell] with x hx
      have hx' : b.1 x = ellipticRepresentative K b x := hx
      rw [hx', hs x, hsD x]
    have hintS : Integrable (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        vecDot (matVecMul ((pk.wholeSpaceSolution hb hbell e).coeff x - skewPart pk.abar)
          ((pk.wholeSpaceSolution hb hbell e).Dv x) - matVecMul (symmPart pk.abar) e) e) :=
      integrable_of_integrable_normalizedCubeMeasure _
        ((pk.wholeSpaceSolution hb hbell e).integrable_normalized_fluxDefect N
          (originCutoff_smooth N).continuous (innerCubeCutoff_nonneg _ _)
          (innerCubeCutoff_le_one _ _) hK pk.abar e)
        fun x hx => by rw [originCutoff_sq_eq_zero N hx, zero_mul]
    have hintB : Integrable (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        vecDot (matVecMul (b.1 x - skewPart pk.abar) (e + pk.gradPhi e b x) -
          matVecMul (symmPart pk.abar) e)
          (matVecMul (matTranspose (matSqrt (symmPart pk.abar))⁻¹) w)) := by
      rw [hLw]
      exact hintS.congr hae.symm
    have hmain := abs_integral_le_of_negOneNorm_originCube pk.abar hSpd N
      (G := fun x => matVecMul (b.1 x - skewPart pk.abar) (e + pk.gradPhi e b x) -
        matVecMul (symmPart pk.abar) e) (L := (matSqrt (symmPart pk.abar))⁻¹) hB0 hneg
      (originCutoff_sq_smooth N) (originCutoff_sq_hasCompactSupport N)
      (tsupport_originCutoff_sq_subset N) (fun x => sq_nonneg _) (originCutoff_sq_le_one N)
      (norm_fderiv_originCutoff_sq_le N) w hintB
    beta_reduce at hmain
    rw [hLw, integral_congr_ae hae] at hmain
    have hv := cubeVolume_pos (originCube d (N : ℤ))
    have hout : ∫ x in cubeSet (originCube d (N : ℤ)),
        innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
          vecDot (matVecMul ((pk.wholeSpaceSolution hb hbell e).coeff x - skewPart pk.abar)
            ((pk.wholeSpaceSolution hb hbell e).Dv x) - matVecMul (symmPart pk.abar) e) e =
        ∫ x, innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
          vecDot (matVecMul ((pk.wholeSpaceSolution hb hbell e).coeff x - skewPart pk.abar)
            ((pk.wholeSpaceSolution hb hbell e).Dv x) - matVecMul (symmPart pk.abar) e) e := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      rw [originCutoff_sq_eq_zero N hx, zero_mul]
    rw [Real.norm_eq_abs]
    unfold cubeAverage
    rw [hout, abs_mul, abs_of_pos (inv_pos.mpr hv), inv_mul_le_iff₀ hv]
    refine hmain.trans (le_of_eq ?_)
    have h3 : (3 : ℝ) ^ N * ((3 : ℝ) ^ N)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    calc Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
          Real.sqrt (vecNormSq w) * (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) *
            ((Real.sqrt d * (3 : ℝ) ^ N) / pk.X b) ^ (-κ)) * (3 : ℝ) ^ N *
          (2 * (originCutoffConst d * ((3 : ℝ) ^ N)⁻¹) + ballVolumeConstant d * ((3 : ℝ) ^ N)⁻¹) *
          cubeVolume (originCube d (N : ℤ))
        = Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
          Real.sqrt (vecNormSq w) * (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) *
            ((Real.sqrt d * (3 : ℝ) ^ N) / pk.X b) ^ (-κ)) * ((3 : ℝ) ^ N * ((3 : ℝ) ^ N)⁻¹) *
          (2 * originCutoffConst d + ballVolumeConstant d) *
          cubeVolume (originCube d (N : ℤ)) := by ring
      _ = _ := by rw [h3]; ring
  · have h := ((tendsto_scale_rpow_neg (d := d) hκ hX).const_mul
      (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)))).const_mul
      (Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
        Real.sqrt (vecNormSq w) * (2 * originCutoffConst d + ballVolumeConstant d))
    rw [mul_zero, mul_zero] at h
    exact h

/-- **Bounds on the homogenized matrix.** On the event of the homogenization theorem of
Armstrong, Kuusi and Loher, the symmetric part `s̄` of the homogenized matrix of the dilated law
satisfies `|e|² ≤ e · s̄ e ≤ K² |e|²`. -/
theorem HighContrastCorrectorPackage.vecNormSq_le_vecDot_symmPart_and_le [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) (hκ : 0 < κ) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d) :
    vecNormSq e ≤ vecDot e (matVecMul (symmPart pk.abar) e) ∧
      vecDot e (matVecMul (symmPart pk.abar) e) ≤ K ^ 2 * vecNormSq e := by
  have hA := pk.tendsto_cubeAverage_cutoff_sq_fluxDefect hκ hC hb hbell e
  have hB := pk.tendsto_cubeAverage_cutoff_sq_crossTerm hκ hC hb hbell e
  have hy := pk.tendsto_cubeAverage_cutoff_sq_correctorGrad hκ hC hb hbell e
  generalize pk.wholeSpaceSolution hb hbell e = s at hA hB hy
  have hq0 : 0 ≤ vecDot e (matVecMul (symmPart pk.abar) e) := by
    by_cases he : e = 0
    · rw [he]
      simp [vecDot]
    · exact (pk.posDef e he).le
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hp0 : 0 ≤ Real.sqrt (vecNormSq e) := Real.sqrt_nonneg _
  have hp2 : Real.sqrt (vecNormSq e) ^ 2 = vecNormSq e := Real.sq_sqrt (vecNormSq_nonneg e)
  have hc : (0 : ℝ) < (1 / 2) ^ d := by positivity
  have hηc (N : ℕ) : Continuous (innerCubeCutoff (originCube d (N : ℤ)) (1 / 4)) :=
    (originCutoff_smooth N).continuous
  have hη0 (N : ℕ) : ∀ x, 0 ≤ innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x :=
    innerCubeCutoff_nonneg _ _
  have hη1 (N : ℕ) : ∀ x, innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ≤ 1 :=
    innerCubeCutoff_le_one _ _
  have hCc : Tendsto (fun N : ℕ => cubeAverage (originCube d (N : ℤ)) (fun x =>
      innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        vecDot (matVecMul (matTranspose (skewPart pk.abar)) e) (s.correctorGrad e x)))
      atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
      (hy i).const_mul (matVecMul (matTranspose (skewPart pk.abar)) e i)
    have h0 : ∑ i : Fin d, matVecMul (matTranspose (skewPart pk.abar)) e i * (0 : ℝ) = 0 := by
      simp
    rw [h0] at h
    refine h.congr fun N => ?_
    rw [s.cubeAverage_cutoff_sq_mul_vecDot_correctorGrad N (hηc N) (hη0 N) (hη1 N)]
  have hY : Tendsto (fun N : ℕ => Real.sqrt (∑ i, cubeAverage (originCube d (N : ℤ)) (fun x =>
      innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 * s.correctorGrad e x i) ^ 2))
      atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => (hy i).pow 2
    have h0 : ∑ i : Fin d, (0 : ℝ) ^ 2 = 0 := by simp
    rw [h0] at h
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h
    rw [Real.sqrt_zero] at h2
    exact h2
  have hfacts (N : ℕ) :
      (1 / 2 : ℝ) ^ d ≤ cubeAverage (originCube d (N : ℤ))
          (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2) ∧
        cubeAverage (originCube d (N : ℤ))
          (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2) ≤ 1 ∧
        0 ≤ cubeAverage (originCube d (N : ℤ))
          (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
            vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x))) := by
    have hs1 := pow_le_cubeAverage_sq_innerCubeCutoff (originCube d (N : ℤ))
      (by norm_num : (0 : ℝ) < 1 / 4) le_rfl
    have hhalf : (1 - 2 * (1 / 4 : ℝ)) = 1 / 2 := by norm_num
    rw [hhalf] at hs1
    refine ⟨hs1, cubeAverage_sq_le_one _ (hηc N) (hη0 N) (hη1 N),
      cubeAverage_nonneg_of_nonneg _ fun x => mul_nonneg (sq_nonneg _)
        ((vecNormSq_nonneg _).trans (s.vecNormSq_le_energyDensity x))⟩
  constructor
  · rw [← hp2]
    refine sq_le_of_approx hq0 hp0 hc fun ε hε => ?_
    obtain ⟨N, h1, h2, h3, h4⟩ := ((eventually_abs_le_of_tendsto_zero hA (half_pos hε)).and
      ((eventually_abs_le_of_tendsto_zero hCc (half_pos hε)).and
        ((eventually_abs_le_of_tendsto_zero hB hε).and
          (eventually_abs_le_of_tendsto_zero hY hε)))).exists
    obtain ⟨hs1, hs2, ha0⟩ := hfacts N
    have hdef := s.cubeAverage_fluxDefect_eq N (hηc N) (hη0 N) (hη1 N) hK pk.abar e
    have hcross := s.cubeAverage_weightedEnergy_sub_weightedFlux N (hηc N) (hη0 N) (hη1 N) hK e
    have hgs := s.sum_sq_cubeAverage_le_weightedEnergy N (hηc N) (hη0 N) (hη1 N) hK
    have hsum : ∑ i, cubeAverage (originCube d (N : ℤ))
        (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 * s.Dv x i) ^ 2 =
        ∑ i, (e i * cubeAverage (originCube d (N : ℤ))
            (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2) +
          cubeAverage (originCube d (N : ℤ))
            (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
              s.correctorGrad e x i)) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by
        rw [s.cubeAverage_cutoff_sq_mul_Dv_eq N (hηc N) (hη0 N) (hη1 N) e i]
    have htri := mul_sqrt_sub_sqrt_le (cubeAverage (originCube d (N : ℤ))
      (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2))
      (le_trans hc.le hs1) e (fun i => cubeAverage (originCube d (N : ℤ))
        (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 * s.correctorGrad e x i))
    beta_reduce at htri
    rw [← hsum] at htri
    have h4' := (le_abs_self _).trans h4
    have hsq0 : 0 ≤ ∑ i, cubeAverage (originCube d (N : ℤ))
        (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 * s.Dv x i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    refine ⟨_, _, cubeAverage (originCube d (N : ℤ))
      (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        vecDot e (matVecMul (s.coeff x) (s.Dv x))), _, hs1, hs2, Real.sqrt_nonneg _, ?_, ?_, ?_,
      (Real.sq_sqrt hsq0).trans_le hgs⟩
    · rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
    · rw [hcross]
      exact h3
    · linarith
  · rw [← hp2]
    refine le_sq_mul_of_approx hq0 hp0 hK0 hc fun ε hε => ?_
    obtain ⟨N, h1, h2, h3⟩ := ((eventually_abs_le_of_tendsto_zero hA (half_pos hε)).and
      ((eventually_abs_le_of_tendsto_zero hCc (half_pos hε)).and
        (eventually_abs_le_of_tendsto_zero hB hε))).exists
    obtain ⟨hs1, hs2, ha0⟩ := hfacts N
    have hdef := s.cubeAverage_fluxDefect_eq N (hηc N) (hη0 N) (hη1 N) hK pk.abar e
    have hcross := s.cubeAverage_weightedEnergy_sub_weightedFlux N (hηc N) (hη0 N) (hη1 N) hK e
    have hflux := s.cubeAverage_flux_le N (hηc N) (hη0 N) (hη1 N) hK e
    refine ⟨_, _, _, hs1, hs2, ha0, ?_, ?_, hflux⟩
    · rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
    · rw [hcross]
      exact h3

end Package

end EinsteinFull.Homogenization
