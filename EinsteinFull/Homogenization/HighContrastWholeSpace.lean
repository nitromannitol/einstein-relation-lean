import EinsteinFull.Homogenization.CorrectorEnergyIteration
import EinsteinFull.Homogenization.HighContrastCorrectors
import EinsteinFull.Homogenization.NormalizedBallNorms
import HCPoly.Provider.Regularity.LiouvilleCubeRestriction
import HCPoly.Provider.Regularity.CorrectorGlobalEquation

/-!
# High-contrast correctors as whole-space solutions

A coefficient field of the high-contrast coefficient space of Armstrong, Kuusi and Loher,
*Homogenization at a polynomial scale in high contrast*, that is `(1, K)`-elliptic almost
everywhere has a measurable representative that is `(1, K)`-elliptic at every point. On the
event of the homogenization theorem, the affine function of slope `e` plus the corrector of
direction `e` is a whole-space solution for that representative, and its square averages on
origin cubes grow at most polynomially.
-/

open MeasureTheory Filter Topology

namespace EinsteinFull.Homogenization

open _root_.Homogenization hiding euclideanBall
open _root_.Homogenization.HighContrast

variable {d : ℕ}

/-- The pointwise `(1, K)`-elliptic representative of a coefficient field: the jointly
measurable representative where it is `(1, K)`-elliptic, and the identity elsewhere. -/
noncomputable def ellipticRepresentative (K : ℝ) (b : CoeffSpace d) : CoeffField d :=
  open Classical in
  fun x => if IsEllipticMatrix 1 K (coeffSpaceRepresentative b x) then
    coeffSpaceRepresentative b x else 1

theorem measurableSet_isEllipticMatrix_coeffSpaceRepresentative (K : ℝ) (b : CoeffSpace d) :
    MeasurableSet {x | IsEllipticMatrix 1 K (coeffSpaceRepresentative b x)} := by
  have hpair : MeasurableSet {p : CoeffSpace d × Vec d |
      IsEllipticMatrix 1 K (coeffSpaceRepresentative p.1 p.2)} :=
    measurable_coeffSpaceRepresentative
      (_root_.Homogenization.measurableSet_isEllipticMatrix (d := d) (lam := 1) (Lam := K))
  exact measurable_prodMk_left hpair

theorem measurable_coeffSpaceRepresentative_apply (b : CoeffSpace d) (i j : Fin d) :
    Measurable (fun x => coeffSpaceRepresentative b x i j) := by
  unfold coeffSpaceRepresentative
  exact Measurable.limsup (fun n => (continuous_coeffSpaceObservation n i j b).measurable)

theorem measurable_ellipticRepresentative (K : ℝ) (b : CoeffSpace d) :
    Measurable (fun x i j => ellipticRepresentative K b x i j) := by
  classical
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  have heq : (fun x => ellipticRepresentative K b x i j) = fun x =>
      if IsEllipticMatrix 1 K (coeffSpaceRepresentative b x) then
        coeffSpaceRepresentative b x i j else (1 : Mat d) i j := by
    funext x
    unfold ellipticRepresentative
    split_ifs <;> rfl
  rw [heq]
  exact Measurable.ite (measurableSet_isEllipticMatrix_coeffSpaceRepresentative K b)
    (measurable_coeffSpaceRepresentative_apply b i j) measurable_const

theorem isEllipticMatrix_ellipticRepresentative {K : ℝ} (hK : 1 ≤ K) (b : CoeffSpace d)
    (x : Vec d) : IsEllipticMatrix 1 K (ellipticRepresentative K b x) := by
  unfold ellipticRepresentative
  split_ifs with h
  · exact h
  · exact isEllipticMatrix_one_le hK

theorem ellipticRepresentative_ae_eq {K : ℝ} (b : CoeffSpace d)
    (hb : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) :
    (fun x => b.1 x) =ᵐ[volume] ellipticRepresentative K b := by
  filter_upwards [hb, coeffSpaceRepresentative_ae_eq b] with x hx hrep
  unfold ellipticRepresentative
  rw [hrep, ite_eq_left hx]

/-- Adding a linear function adds its slope to a weak gradient on the whole space. -/
theorem hasWeakGradientOn_vecDot_add [NeZero d] (e : Vec d) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : LocallyIntegrable u volume)
    (hg : ∀ i, LocallyIntegrable (fun x => g x i) volume)
    (h : HasWeakGradientOn Set.univ u g) :
    HasWeakGradientOn Set.univ (fun x => vecDot e x + u x) (fun x => e + g x) := by
  intro i χ hχ hcs hsub
  have haff := HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := i)
    (contDiff_vecDot_left e) χ hχ hcs hsub
  have hu' := h i χ hχ hcs hsub
  simp only [fderiv_vecDot_left_apply] at haff
  simp only [Measure.restrict_univ] at haff hu' ⊢
  have hχc : Continuous χ := hχ.continuous
  have hdχc : Continuous (fun x => fderiv ℝ χ x (basisVec i)) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdχs : HasCompactSupport (fun x => fderiv ℝ χ x (basisVec i)) :=
    hcs.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hi1 : Integrable (fun x => vecDot e x * fderiv ℝ χ x (basisVec i)) :=
    ((contDiff_vecDot_left e).continuous.mul hdχc).integrable_of_hasCompactSupport
      hdχs.mul_left
  have hi2 : Integrable (fun x => u x * fderiv ℝ χ x (basisVec i)) := by
    have := hu.integrable_smul_right_of_hasCompactSupport hdχc hdχs
    simpa [smul_eq_mul, mul_comm] using this
  have hi3 : Integrable (fun x => e i * χ x) :=
    (continuous_const.mul hχc).integrable_of_hasCompactSupport hcs.mul_left
  have hi4 : Integrable (fun x => g x i * χ x) := by
    have := (hg i).integrable_smul_right_of_hasCompactSupport hχc hcs
    simpa [smul_eq_mul, mul_comm] using this
  calc ∫ x, (vecDot e x + u x) * fderiv ℝ χ x (basisVec i)
      = ∫ x, (vecDot e x * fderiv ℝ χ x (basisVec i) +
          u x * fderiv ℝ χ x (basisVec i)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring
    _ = -∫ x, (e i * χ x + g x i * χ x) := by
        rw [integral_add hi1 hi2, haff, hu', integral_add hi3 hi4]
        ring
    _ = -∫ x, (e + g x) i * χ x := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Pi.add_apply]
        ring

theorem exists_euclideanBall_superset_of_isCompact {k : Set (Vec d)} (hk : IsCompact k) :
    ∃ R : ℝ, 0 < R ∧ k ⊆ euclideanBall d R := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp hk.isBounded
  refine ⟨Real.sqrt d * (|r| + 1) + 1, by positivity, fun x hx => ?_⟩
  have hx' : ‖x‖ ≤ r := by simpa using hr hx
  have hcoord (i : Fin d) : |x i| ≤ |r| := ((norm_le_pi_norm x i).trans hx').trans (le_abs_self r)
  have hsum : vecNormSq x ≤ d * |r| ^ 2 := by
    change ∑ i, x i * x i ≤ _
    calc ∑ i, x i * x i ≤ ∑ _i : Fin d, |r| ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hcoord i
          nlinarith [abs_nonneg (x i), sq_abs (x i), abs_mul_abs_self (x i)]
      _ = d * |r| ^ 2 := by simp
  show vecNormSq (x - 0) < (Real.sqrt d * (|r| + 1) + 1) ^ 2
  rw [sub_zero]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs := Real.sq_sqrt hd
  have h0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  nlinarith [abs_nonneg r]

/-- A weak gradient on every centered Euclidean ball is a weak gradient on the whole space. -/
theorem hasWeakGradientOn_univ_of_forall_euclideanBall {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : ∀ R : ℝ, 0 < R → HasWeakGradientOn (euclideanBall d R) u g) :
    HasWeakGradientOn Set.univ u g := by
  intro i χ hχ hcs hsub
  obtain ⟨R, hR, hkR⟩ := exists_euclideanBall_superset_of_isCompact hcs.isCompact
  have hball := h R hR i χ hχ hcs hkR
  have h1 : ∫ x in euclideanBall d R, u x * fderiv ℝ χ x (basisVec i) =
      ∫ x in Set.univ, u x * fderiv ℝ χ x (basisVec i) := by
    rw [Measure.restrict_univ]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hxs : x ∉ tsupport χ := fun h' => hx (hkR h')
    have hfd : fderiv ℝ χ x = 0 := by
      by_contra hne
      exact hxs (support_fderiv_subset ℝ hne)
    simp [hfd]
  have h2 : ∫ x in euclideanBall d R, g x i * χ x = ∫ x in Set.univ, g x i * χ x := by
    rw [Measure.restrict_univ]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hxs : x ∉ tsupport χ := fun h' => hx (hkR h')
    simp [image_eq_zero_of_notMem_tsupport hxs]
  rw [← h1, ← h2]
  exact hball

theorem lintegral_sq_le_of_normalizedL2Norm_le {V : Set (Vec d)} {v : Vec d → ℝ} {c : ℝ}
    (hc0 : 0 ≤ c) (hVtop : volume V ≠ ⊤) (h : normalizedL2Norm V v ≤ ENNReal.ofReal c) :
    ∫⁻ x in V, ENNReal.ofReal (v x ^ 2) ≤ ENNReal.ofReal (c ^ 2) * volume V := by
  by_cases hV0 : volume V = 0
  · rw [Measure.restrict_eq_zero.mpr hV0, lintegral_zero_measure]
    exact zero_le
  have hY : eVolumeAverage V (fun x => ENNReal.ofReal (v x ^ 2)) ≤ ENNReal.ofReal c ^ (2 : ℝ) := by
    have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
    unfold normalizedL2Norm at h2
    rwa [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h2
  unfold eVolumeAverage at hY
  rw [ENNReal.div_le_iff hV0 hVtop] at hY
  have hc : ENNReal.ofReal c ^ (2 : ℝ) = ENNReal.ofReal (c ^ 2) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      ENNReal.ofReal_pow hc0]
  rwa [hc] at hY

theorem euclideanBall_sqrt_mul_subset_cubeSet (N : ℕ) :
    euclideanBall d (Real.sqrt d * (3 : ℝ) ^ N) ⊆ cubeSet (originCube d ((N + d + 1 : ℕ) : ℤ)) := by
  refine euclideanBall_subset_cubeSet_originCube (by positivity) ?_
  have h := four_mul_sqrt_le_three_pow d
  rw [show N + d + 1 = N + (d + 1) by ring, pow_add]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  have h' : Real.sqrt d ≤ (3 : ℝ) ^ (d + 1) / 2 := by
    have : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    linarith
  have := mul_le_mul_of_nonneg_left h' h3.le
  linarith

theorem rpow_two_add_two_mul_eq (N : ℕ) {ϑ : ℝ} :
    ((3 : ℝ) ^ N) ^ (2 + 2 * ϑ) = 9 ^ N * ((3 : ℝ) ^ (2 * ϑ)) ^ N := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  rw [Real.rpow_add h3, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← pow_mul, mul_comm N 2, pow_mul, ← Real.rpow_natCast_mul (by norm_num),
    ← Real.rpow_mul_natCast (by norm_num)]
  norm_num
  ring_nf

/-- **Polynomial growth on origin cubes.** The growth condition of the Liouville class with
exponent `1 + ϑ` bounds the square averages on the origin cube of side `3ᴺ` by a constant
times `9ᴺ (3^(2ϑ))ᴺ` for all large `N`. -/
theorem exists_cube_growth_of_liouvilleGrowth [NeZero d] {v : Vec d → ℝ}
    (hvmeas : AEStronglyMeasurable v volume) {ϑ : ℝ}
    (hgrowth : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + ϑ))) *
      normalizedL2Norm (euclideanBall d r) v) atTop (𝓝 0)) :
    ∃ (Cg : ℝ) (Ng : ℕ), 0 ≤ Cg ∧ ∀ N, Ng ≤ N →
      cubeAverage (originCube d (N : ℤ)) (fun x => v x ^ 2) ≤
        Cg * 9 ^ N * ((3 : ℝ) ^ (2 * ϑ)) ^ N := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hev := hgrowth.eventually (Iio_mem_nhds (zero_lt_one : (0 : ENNReal) < 1))
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨Ng, hNg⟩ := pow_unbounded_of_one_lt (max r₀ 1) (by norm_num : (1 : ℝ) < 3)
  set Cg := (3 : ℝ) ^ ((d + 1) * d) * Real.sqrt d ^ (2 + 2 * ϑ) with hCg
  refine ⟨Cg, Ng, by rw [hCg]; positivity, ?_⟩
  intro N hN
  set r := Real.sqrt d * (3 : ℝ) ^ N with hr
  have hsd : 1 ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have h3N : (3 : ℝ) ^ Ng ≤ (3 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hr0 : 0 < r := by positivity
  have hrr₀ : r₀ ≤ r := by
    have : (3 : ℝ) ^ N ≤ r := by
      rw [hr]
      nlinarith [pow_pos (show (0 : ℝ) < 3 by norm_num) N]
    have := le_max_left r₀ 1
    linarith
  have hlt := hr₀ r hrr₀
  have hnorm : normalizedL2Norm (euclideanBall d r) v ≤ ENNReal.ofReal (r ^ (1 + ϑ)) := by
    have hpos : 0 < r ^ (-(1 + ϑ)) := Real.rpow_pos_of_pos hr0 _
    have hinv : (r ^ (-(1 + ϑ)))⁻¹ = r ^ (1 + ϑ) := by
      rw [Real.rpow_neg hr0.le, inv_inv]
    calc normalizedL2Norm (euclideanBall d r) v
        = ENNReal.ofReal (r ^ (-(1 + ϑ)))⁻¹ * (ENNReal.ofReal (r ^ (-(1 + ϑ))) *
            normalizedL2Norm (euclideanBall d r) v) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le),
            inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (r ^ (-(1 + ϑ)))⁻¹ * 1 := by gcongr
      _ = ENNReal.ofReal (r ^ (1 + ϑ)) := by rw [mul_one, hinv]
  have hBtop : volume (euclideanBall d r) ≠ ⊤ := (measure_mono
    (euclideanBall_sqrt_mul_subset_cubeSet (d := d) N)).trans_lt (volume_cubeSet_lt_top _) |>.ne
  have hlint := lintegral_sq_le_of_normalizedL2Norm_le (by positivity) hBtop hnorm
  have hQB : cubeSet (originCube d (N : ℤ)) ⊆ euclideanBall d r :=
    cubeSet_originCube_subset_euclideanBall N
  have hfinB : ∫⁻ x in euclideanBall d r, ENNReal.ofReal (v x ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop) hlint
  have hint : ∫ x in cubeSet (originCube d (N : ℤ)), v x ^ 2 ≤
      (r ^ (1 + ϑ)) ^ 2 * (volume (euclideanBall d r)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (hvmeas.pow 2).restrict]
    calc (∫⁻ x in cubeSet (originCube d (N : ℤ)), ENNReal.ofReal (v x ^ 2)).toReal
        ≤ (∫⁻ x in euclideanBall d r, ENNReal.ofReal (v x ^ 2)).toReal :=
          ENNReal.toReal_mono hfinB (lintegral_mono_set hQB)
      _ ≤ (ENNReal.ofReal ((r ^ (1 + ϑ)) ^ 2) * volume (euclideanBall d r)).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop) hlint
      _ = (r ^ (1 + ϑ)) ^ 2 * (volume (euclideanBall d r)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hvolB : (volume (euclideanBall d r)).toReal ≤
      cubeVolume (originCube d ((N + d + 1 : ℕ) : ℤ)) := by
    rw [← volume_cubeSet_toReal]
    exact ENNReal.toReal_mono (volume_cubeSet_lt_top _).ne
      (measure_mono (euclideanBall_sqrt_mul_subset_cubeSet N))
  have hrpow : (r ^ (1 + ϑ)) ^ 2 = Real.sqrt d ^ (2 + 2 * ϑ) * (9 ^ N * ((3 : ℝ) ^ (2 * ϑ)) ^ N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le, hr,
      Real.mul_rpow (Real.sqrt_nonneg _) (by positivity), ← rpow_two_add_two_mul_eq N]
    norm_num
    ring_nf
  unfold cubeAverage
  rw [cubeVolume_originCube]
  have hvolQ : cubeVolume (originCube d ((N + d + 1 : ℕ) : ℤ)) =
      ((3 : ℝ) ^ N) ^ d * (3 : ℝ) ^ ((d + 1) * d) := by
    rw [cubeVolume_originCube, show N + d + 1 = N + (d + 1) by ring, pow_add, mul_pow,
      ← pow_mul (3 : ℝ) (d + 1) d]
  have h3d : (0 : ℝ) < ((3 : ℝ) ^ N) ^ d := by positivity
  calc (((3 : ℝ) ^ N) ^ d)⁻¹ * ∫ x in cubeSet (originCube d (N : ℤ)), v x ^ 2
      ≤ (((3 : ℝ) ^ N) ^ d)⁻¹ * ((r ^ (1 + ϑ)) ^ 2 *
          cubeVolume (originCube d ((N + d + 1 : ℕ) : ℤ))) := by
        refine mul_le_mul_of_nonneg_left (hint.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hvolB (by positivity)
    _ = Cg * 9 ^ N * ((3 : ℝ) ^ (2 * ϑ)) ^ N := by
        rw [hvolQ, hrpow, hCg]
        field_simp

theorem memLp_euclideanBall_of_memLiouvilleClass {b : CoeffField d} {ϑ : ℝ} {v : Vec d → ℝ}
    {Dv : Vec d → Vec d} (h : MemLiouvilleClass b ϑ v Dv) {R : ℝ} (hR : 0 < R) :
    MemLp v 2 (volume.restrict (euclideanBall d R)) := by
  obtain ⟨r, hrR, hr, hnorm⟩ :=
    exists_large_radius_normalizedL2Norm_ne_top_of_liouvilleGrowth (R := R) h.2.2
  have hmem := memLp_volumeRestrict_of_normalizedL2Norm_ne_top h.1.1.1
    (volume_euclideanBall_pos' hr).ne' (volume_euclideanBall_ne_top' r) hnorm
  refine hmem.mono_measure (Measure.restrict_mono ?_ le_rfl)
  intro x hx
  have hx' : vecNormSq (x - 0) < R ^ 2 := hx
  show vecNormSq (x - 0) < r ^ 2
  nlinarith

theorem memLp_grad_euclideanBall_of_memLiouvilleClass {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b) {ϑ : ℝ} {v : Vec d → ℝ}
    {Dv : Vec d → Vec d} (h : MemLiouvilleClass b ϑ v Dv) {R : ℝ} (hR : 0 < R) (i : Fin d) :
    MemLp (fun x => Dv x i) 2 (volume.restrict (euclideanBall d R)) := by
  have hsq := integrableOn_vecNormSq_grad_of_memH1sLoc_class hb h.1 hR
  have hmeas := aestronglyMeasurable_grad_of_memH1sLoc h.1 (euclideanBall d R) i
  refine (memLp_two_iff_integrable_sq hmeas).2 (hsq.mono' (hmeas.pow 2) ?_)
  filter_upwards with x
  have hi : 0 ≤ Dv x i ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hi]
  exact sq_apply_le_vecNormSq (Dv x) i

section Package

variable {K : ℝ} {hK : 1 ≤ K}
  {P : Measure (EinsteinRelation.Environment.AKMTestIntegralSupport.Coefficient d K)} {κ C : ℝ}

theorem HighContrastCorrectorPackage.memLiouvilleClass_affine
    (pk : HighContrastCorrectorPackage hK P κ C) {b : CoeffSpace d} (hb : b ∈ pk.Ωend)
    (e : Vec d) {ϑ : ℝ} (hϑ : ϑ ∈ Set.Ioo (0 : ℝ) 1) :
    MemLiouvilleClass (fun x => b.1 x) ϑ (fun x => vecDot e x + pk.Phi e b x)
      (fun x => e + pk.gradPhi e b x) := by
  simpa using pk.liouville_mem b hb ϑ hϑ e 0

/-- The affine function of slope `e` plus the corrector of direction `e`, as a whole-space
solution for the pointwise elliptic representative. -/
noncomputable def HighContrastCorrectorPackage.wholeSpaceSolution [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) {b : CoeffSpace d} (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d) :
    EllipticWholeSpaceSolution d K where
  coeff := ellipticRepresentative K b
  measurable_coeff := measurable_ellipticRepresentative K b
  elliptic := isEllipticMatrix_ellipticRepresentative hK b
  v := fun x => vecDot e x + pk.Phi e b x
  Dv := fun x => e + pk.gradPhi e b x
  weak := hasWeakGradientOn_univ_of_forall_euclideanBall fun R hR =>
    ((pk.memLiouvilleClass_affine hb e (ϑ := 1 / 2) ⟨by norm_num, by norm_num⟩).1.2 R hR).1
  locL2 := fun R hR =>
    ⟨memLp_euclideanBall_of_memLiouvilleClass
        (pk.memLiouvilleClass_affine hb e (ϑ := 1 / 2) ⟨by norm_num, by norm_num⟩) hR,
      fun i => memLp_grad_euclideanBall_of_memLiouvilleClass b.2
        (pk.memLiouvilleClass_affine hb e (ϑ := 1 / 2) ⟨by norm_num, by norm_num⟩) hR i⟩
  solution := by
    have h := (pk.equation b hb e).2
    refine IsWeakSolutionOn.congr_ae ?_ (Filter.EventuallyEq.refl _ _) h
    rw [Measure.restrict_univ]
    exact ellipticRepresentative_ae_eq b hbell

theorem HighContrastCorrectorPackage.wholeSpaceSolution_correctorGrad [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) {b : CoeffSpace d} (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d)
    (x : Vec d) : (pk.wholeSpaceSolution hb hbell e).correctorGrad e x = pk.gradPhi e b x := by
  simp [HighContrastCorrectorPackage.wholeSpaceSolution, EllipticWholeSpaceSolution.correctorGrad]

theorem HighContrastCorrectorPackage.wholeSpaceSolution_corrector [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) {b : CoeffSpace d} (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d)
    (x : Vec d) : (pk.wholeSpaceSolution hb hbell e).corrector e x = pk.Phi e b x := by
  simp [HighContrastCorrectorPackage.wholeSpaceSolution, EllipticWholeSpaceSolution.corrector]

/-- The square averages of the affine function plus the corrector grow at most like
`9ᴺ ρᴺ` on origin cubes, with `ρ^(d+1) ≤ 2`. -/
theorem HighContrastCorrectorPackage.exists_cube_growth [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) {b : CoeffSpace d} (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d) :
    ∃ (ρ Cg : ℝ) (Ng : ℕ), 1 ≤ ρ ∧ ρ ^ (d + 1) ≤ 2 ∧ 0 ≤ Cg ∧ ∀ N, Ng ≤ N →
      cubeAverage (originCube d (N : ℤ)) (fun x => (pk.wholeSpaceSolution hb hbell e).v x ^ 2) ≤
        Cg * 9 ^ N * ρ ^ N := by
  set ϑ : ℝ := 1 / (4 * (d + 1)) with hϑ
  have hϑ0 : 0 < ϑ := by positivity
  have hϑ1 : ϑ < 1 := by
    rw [hϑ, div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hL := pk.memLiouvilleClass_affine hb e ⟨hϑ0, hϑ1⟩
  obtain ⟨Cg, Ng, hCg, hgrowth⟩ := exists_cube_growth_of_liouvilleGrowth hL.1.1.1 hL.2.2
  refine ⟨(3 : ℝ) ^ (2 * ϑ), Cg, Ng, Real.one_le_rpow (by norm_num) (by positivity), ?_, hCg,
    hgrowth⟩
  rw [← Real.rpow_mul_natCast (by norm_num)]
  have h : 2 * ϑ * ((d + 1 : ℕ) : ℝ) = 1 / 2 := by
    rw [hϑ]
    push_cast
    field_simp
    ring
  rw [show ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 by push_cast; ring] at h
  rw [show (((d + 1 : ℕ)) : ℝ) = (d : ℝ) + 1 by push_cast; ring, h]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
  norm_num

end Package

end EinsteinFull.Homogenization
