import EinsteinFull.Homogenization.HighContrastQuantitative
import EinsteinFull.Homogenization.SourceCorrectorIdentification
import EinsteinFull.Homogenization.StretchedExponentialTail
import EinsteinRelation.Correctors.BallMeanSquareComparison

/-!
# Oscillation and energy bounds for source correctors

Let `φ` be a source corrector of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Definitions 3.14–3.15, of a unit slope `e`. Its
dilation is the high-contrast corrector of Armstrong, Kuusi and Loher, *Homogenization at a
polynomial scale in high contrast*, of the dilated coefficient, up to an additive constant. The
quantitative bounds on origin cubes above the homogenization scale `X` of that theorem transfer
to Euclidean balls: for `r ≥ 3^(n₁+1) X` the normalized `L²` oscillation of `φ` on `B_r` is at
most `C r^(1-θ) X^θ` and its energy on `B_r` is at most `C`. Trading part of the exponent for
integrability of the random scale gives the oscillation and gradient conclusions of Lemma 3.17,
(3.85)–(3.86): with `β = θ/(2d)`, for every `s ∈ (0, d)` the random radius
`(3^(n₁+1) X)^(2d/(d+s))` is `O_s(C_s)` and above it the oscillation is at most
`C r^(1 - β(d-s))`.
-/

open MeasureTheory Filter Topology
open scoped Pointwise

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport
  EinsteinRelation.External.AKM
open _root_.Homogenization hiding euclideanBall Vec Mat euclideanNorm
open _root_.Homogenization.HighContrast

variable {d : ℕ}

section Balls

theorem ball_zero_two_mul {ρ : ℝ} (hρ : 0 < ρ) :
    ball (0 : Vec d) (2 * ρ) = (2 : ℝ) • ball (0 : Vec d) ρ := by
  rw [ball_zero_eq_euclideanBall (by positivity), ball_zero_eq_euclideanBall hρ,
    euclideanBall_eq_smul (by positivity), euclideanBall_eq_smul hρ, smul_smul]

theorem volume_real_ball {ρ : ℝ} (hρ : 0 < ρ) :
    volume.real (ball (0 : Vec d) ρ) = ρ ^ d * (volume (euclideanBall d 1)).toReal := by
  rw [measureReal_def, ball_zero_eq_euclideanBall hρ, volume_euclideanBall_toReal hρ]

theorem volume_ball_ne_zero {ρ : ℝ} (hρ : 0 < ρ) : volume (ball (0 : Vec d) ρ) ≠ 0 := by
  rw [ball_zero_eq_euclideanBall hρ]
  exact (volume_euclideanBall_pos' hρ).ne'

theorem volume_ball_ne_top {ρ : ℝ} (hρ : 0 < ρ) : volume (ball (0 : Vec d) ρ) ≠ ⊤ := by
  rw [ball_zero_eq_euclideanBall hρ]
  exact volume_euclideanBall_ne_top' ρ

/-- Averages over centered balls under the dilation by two. -/
theorem setAverage_ball_two_mul (f : Vec d → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ⨍ x in ball 0 (2 * ρ), f x = ⨍ y in ball 0 ρ, f ((2 : ℝ) • y) := by
  rw [setAverage_eq, setAverage_eq, ball_zero_two_mul hρ,
    Measure.setIntegral_comp_smul_of_pos volume f (ball 0 ρ) two_pos, Module.finrank_fin_fun]
  have hv : volume.real ((2 : ℝ) • ball (0 : Vec d) ρ) =
      2 ^ d * volume.real (ball (0 : Vec d) ρ) := by
    rw [measureReal_def, measureReal_def, volume_smul_of_pos two_pos, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hv, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_inv]
  ring

/-- The centered square average is the least square average about a constant. -/
theorem setAverage_sq_sub_setAverage_le {S : Set (Vec d)} (hS0 : volume S ≠ 0)
    (hS : volume S ≠ ⊤) {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict S)) (m : ℝ) :
    ⨍ x in S, (u x - ⨍ y in S, u y) ^ 2 ≤ ⨍ x in S, (u x - m) ^ 2 := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS
  have hμ : (volume.restrict S).real Set.univ ≠ 0 := by
    rw [measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_ne_zero.mpr ⟨hS0, hS⟩
  rw [EinsteinRelation.Correctors.average_sq_sub_const _ hμ hu,
    EinsteinRelation.Correctors.average_sq_sub_const _ hμ hu]
  nlinarith [sq_nonneg (m - ⨍ y in S, u y)]

/-- The ratio of the volume of a cube of side `6ρ` to that of the ball of radius `ρ`. -/
noncomputable def ballCubeRatio (d : ℕ) : ℝ :=
  (6 : ℝ) ^ d / (volume (euclideanBall d 1)).toReal

theorem ballCubeRatio_nonneg (d : ℕ) : 0 ≤ ballCubeRatio d :=
  div_nonneg (by positivity) ENNReal.toReal_nonneg

theorem cube_div_ball_le {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : (3 : ℝ) ^ N ≤ 6 * ρ) :
    ((3 : ℝ) ^ N) ^ d / volume.real (ball (0 : Vec d) ρ) ≤ ballCubeRatio d := by
  have hB : 0 < (volume (euclideanBall d 1)).toReal :=
    ENNReal.toReal_pos (volume_euclideanBall_pos' one_pos).ne' (volume_euclideanBall_ne_top' 1)
  rw [volume_real_ball hρ, ballCubeRatio, div_le_div_iff₀ (by positivity) hB]
  calc ((3 : ℝ) ^ N) ^ d * (volume (euclideanBall d 1)).toReal
      ≤ (6 * ρ) ^ d * (volume (euclideanBall d 1)).toReal := by gcongr
    _ = 6 ^ d * (ρ ^ d * (volume (euclideanBall d 1)).toReal) := by ring

theorem cubeVolume_originCube_natCast (N : ℕ) :
    cubeVolume (originCube d (N : ℤ)) = ((3 : ℝ) ^ N) ^ d := by
  simp [cubeVolume, cubeScaleFactor, originCube]

/-- A ball average of a nonnegative function is controlled by the average on a cube
containing the ball. -/
theorem setAverage_ball_le_mul_cubeAverage {f : Vec d → ℝ} (hf0 : ∀ x, 0 ≤ f x) {ρ : ℝ}
    (hρ : 0 < ρ) {N : ℕ} (hρN : ρ ≤ (3 : ℝ) ^ N / 2)
    (hfi : IntegrableOn f (cubeSet (originCube d (N : ℤ))) volume) :
    ⨍ x in ball 0 ρ, f x ≤
      ((3 : ℝ) ^ N) ^ d / volume.real (ball (0 : Vec d) ρ) *
        cubeAverage (originCube d (N : ℤ)) f := by
  have hsub : ball (0 : Vec d) ρ ⊆ cubeSet (originCube d (N : ℤ)) := by
    rw [ball_zero_eq_euclideanBall hρ]
    exact euclideanBall_subset_cubeSet_originCube hρ.le hρN
  have hvpos : 0 < volume.real (ball (0 : Vec d) ρ) :=
    ENNReal.toReal_pos (volume_ball_ne_zero hρ) (volume_ball_ne_top hρ)
  have hint : ∫ x in ball 0 ρ, f x ≤ ∫ x in cubeSet (originCube d (N : ℤ)), f x :=
    setIntegral_mono_set hfi (Filter.Eventually.of_forall fun x => hf0 x) hsub.eventuallyLE
  have h3 : 0 < ((3 : ℝ) ^ N) ^ d := by positivity
  rw [setAverage_eq, smul_eq_mul, cubeAverage, cubeVolume_originCube_natCast]
  have heq : ((3 : ℝ) ^ N) ^ d / volume.real (ball (0 : Vec d) ρ) *
      ((((3 : ℝ) ^ N) ^ d)⁻¹ * ∫ x in cubeSet (originCube d (N : ℤ)), f x) =
      (volume.real (ball (0 : Vec d) ρ))⁻¹ * ∫ x in cubeSet (originCube d (N : ℤ)), f x := by
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hvpos.le)

end Balls

section Transfer

/-- The oscillation of a function on `B_{2ρ}` is controlled by the square deviation of a
function on `B_ρ` whose dilation it is, up to an additive constant. -/
theorem setAverage_ball_two_mul_sq_le {u Φ : Vec d → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (e : Vec d)
    (hu : MemLp u 2 (volume.restrict (ball 0 (2 * ρ)))) {c : ℝ}
    (hc : dilatedCorrectedAffine e u =ᵐ[volume] fun x => vecDot e x + Φ x + c) (m : ℝ) :
    ⨍ x in ball 0 (2 * ρ), |u x - ⨍ y in ball 0 (2 * ρ), u y| ^ 2 ≤
      4 * ⨍ y in ball 0 ρ, (Φ y - m) ^ 2 := by
  have h2ρ : 0 < 2 * ρ := by positivity
  simp_rw [sq_abs]
  refine (setAverage_sq_sub_setAverage_le (volume_ball_ne_zero h2ρ) (volume_ball_ne_top h2ρ) hu
    (2 * m + 2 * c)).trans (le_of_eq ?_)
  rw [setAverage_ball_two_mul _ hρ]
  have hae : (fun y => (u ((2 : ℝ) • y) - (2 * m + 2 * c)) ^ 2) =ᵐ[volume.restrict (ball 0 ρ)]
      fun y => 4 * (Φ y - m) ^ 2 := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hc] with y hy
    simp only [dilatedCorrectedAffine, dilatedPotential] at hy
    have h : u ((2 : ℝ) • y) = 2 * Φ y + 2 * c := by linarith
    rw [h]
    ring
  rw [average_congr hae, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul,
    integral_const_mul]
  ring

/-- The energy of a function on `B_{2ρ}` is the energy on `B_ρ` of its dilated gradient. -/
theorem setAverage_ball_two_mul_euclideanSq_eq {g G : Vec d → Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : dilatedGradient g =ᵐ[volume] G) :
    ⨍ x in ball 0 (2 * ρ), euclideanSq (g x) = ⨍ y in ball 0 ρ, vecNormSq (G y) := by
  rw [setAverage_ball_two_mul _ hρ]
  refine average_congr (ae_restrict_of_ae ?_)
  filter_upwards [hg] with y hy
  simp only [dilatedGradient] at hy
  rw [hy]
  rfl

end Transfer

section WholeSpace

variable {K : ℝ}

theorem EllipticWholeSpaceSolution.integrableOn_vecNormSq_correctorGrad [NeZero d]
    (s : EllipticWholeSpaceSolution d K) (e : Vec d) (N : ℕ) :
    IntegrableOn (fun x => vecNormSq (s.correctorGrad e x)) (cubeSet (originCube d (N : ℤ)))
      volume := by
  have h := integrable_finsetSum (μ := volume.restrict (cubeSet (originCube d (N : ℤ))))
    Finset.univ fun i _ => ((s.memLp_cubeSet_Dv N i).sub (memLp_const (e i))).integrable_sq
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [vecNormSq, vecDot, sq, EllipticWholeSpaceSolution.correctorGrad]

theorem EllipticWholeSpaceSolution.setAverage_ball_sq_le [NeZero d]
    (s : EllipticWholeSpaceSolution d K) (e : Vec d) {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ}
    (hρN : ρ ≤ (3 : ℝ) ^ N / 2) :
    ⨍ x in ball 0 ρ, (s.corrector e x - cubeAverage (originCube d (N : ℤ)) (s.corrector e)) ^ 2 ≤
      ((3 : ℝ) ^ N) ^ d / volume.real (ball (0 : Vec d) ρ) *
        cubeBesovOscillation (originCube d (N : ℤ)) 2 (s.corrector e) ^ 2 := by
  have hΦ := s.memLp_cubeSet_corrector e N
  have : IsFiniteMeasure (volume.restrict (cubeSet (originCube d (N : ℤ)))) :=
    isFiniteMeasure_restrict.mpr (volume_cubeSet_lt_top _).ne
  set k := cubeAverage (originCube d (N : ℤ)) (s.corrector e) with hk
  have hfl : MemLp (fun x => s.corrector e x - k) 2
      (volume.restrict (cubeSet (originCube d (N : ℤ)))) := hΦ.sub (memLp_const k)
  have hnorm : MemLp (cubeFluctuation (originCube d (N : ℤ)) (s.corrector e)) 2
      (normalizedCubeMeasure (originCube d (N : ℤ))) :=
    hfl.smul_measure ENNReal.ofReal_ne_top
  have hosc : cubeBesovOscillation (originCube d (N : ℤ)) 2 (s.corrector e) ^ 2 =
      cubeAverage (originCube d (N : ℤ)) (fun x => (s.corrector e x - k) ^ 2) :=
    (integrable_and_cubeLpNorm_sq_eq_cubeAverage_sq _ _ hnorm).2
  rw [hosc]
  exact setAverage_ball_le_mul_cubeAverage (fun x => sq_nonneg _) hρ hρN hfl.integrable_sq

theorem EllipticWholeSpaceSolution.setAverage_ball_vecNormSq_le [NeZero d]
    (s : EllipticWholeSpaceSolution d K) (e : Vec d) {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ}
    (hρN : ρ ≤ (3 : ℝ) ^ N / 2) :
    ⨍ x in ball 0 ρ, vecNormSq (s.correctorGrad e x) ≤
      ((3 : ℝ) ^ N) ^ d / volume.real (ball (0 : Vec d) ρ) *
        cubeAverage (originCube d (N : ℤ)) (fun x => vecNormSq (s.correctorGrad e x)) :=
  setAverage_ball_le_mul_cubeAverage (fun _ => vecNormSq_nonneg _) hρ hρN
    (s.integrableOn_vecNormSq_correctorGrad e N)

end WholeSpace

section Scales

theorem exists_three_pow_near {r : ℝ} (hr : 1 ≤ r) :
    ∃ N : ℕ, r < (3 : ℝ) ^ N ∧ (3 : ℝ) ^ N ≤ 3 * r := by
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hr (by norm_num : (1 : ℝ) < 3)
  exact ⟨k + 1, hk2, by rw [pow_succ]; linarith⟩

theorem three_pow_add_mul_rpow_neg (n L : ℕ) (θ : ℝ) :
    (3 : ℝ) ^ (n + L) * ((3 : ℝ) ^ L) ^ (-θ) =
      ((3 : ℝ) ^ (n + L)) ^ (1 - θ) * ((3 : ℝ) ^ n) ^ θ := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [← Real.rpow_natCast (3 : ℝ) (n + L), ← Real.rpow_natCast (3 : ℝ) L,
    ← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_mul h3.le, ← Real.rpow_mul h3.le,
    ← Real.rpow_mul h3.le, ← Real.rpow_add h3, ← Real.rpow_add h3]
  congr 1
  push_cast
  ring

/-- **Choice of scales.** Bounds at every origin cube of side `3^(n₀+L)` with `X ≤ √d 3^n₀` and
`n₁ ≤ n₀`, with decay `(3^L)^(-θ)` of the second, give at a cube of side between `r` and `3r`,
for `r ≥ 3^(n₁+1) X`, the second bound `3 A w r^(1-θ') (3^(n₁+1) X)^θ'` with `θ' = min θ 1`. -/
theorem exists_cube_le_of_scale_bounds [NeZero d] {A θ X r v w : ℝ} {n₁ : ℕ} (hA : 0 ≤ A)
    (hθ : 0 < θ) (hw : 0 ≤ w) (hX : 1 ≤ X) {E O : ℕ → ℝ}
    (hq : ∀ n₀ L : ℕ, X ≤ Real.sqrt d * (3 : ℝ) ^ n₀ → n₁ ≤ n₀ →
      E (n₀ + L) ≤ A * v ∧ O (n₀ + L) ≤ A * w * (3 : ℝ) ^ (n₀ + L) * ((3 : ℝ) ^ L) ^ (-θ))
    (hr : (3 : ℝ) ^ (n₁ + 1) * X ≤ r) :
    ∃ N : ℕ, r < (3 : ℝ) ^ N ∧ (3 : ℝ) ^ N ≤ 3 * r ∧ E N ≤ A * v ∧
      O N ≤ 3 * A * w * r ^ (1 - min θ 1) * ((3 : ℝ) ^ (n₁ + 1) * X) ^ min θ 1 := by
  have h3n : (1 : ℝ) ≤ (3 : ℝ) ^ (n₁ + 1) := one_le_pow₀ (by norm_num)
  have hr1 : 1 ≤ r := le_trans (by nlinarith) hr
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near hX (by norm_num : (1 : ℝ) < 3)
  obtain ⟨N, hN1, hN2⟩ := exists_three_pow_near hr1
  set n₀ := n₁ + (m + 1) with hn₀
  have h0 : (3 : ℝ) ^ n₀ ≤ (3 : ℝ) ^ (n₁ + 1) * X := by
    rw [hn₀, pow_add, pow_succ, pow_succ]
    have : (0 : ℝ) < 3 ^ n₁ := by positivity
    nlinarith
  have hn₀N : n₀ ≤ N := by
    have : (3 : ℝ) ^ n₀ < (3 : ℝ) ^ N := lt_of_le_of_lt (h0.trans hr) hN1
    exact ((pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp this).le
  have hsd : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hXn₀ : X ≤ Real.sqrt d * (3 : ℝ) ^ n₀ := by
    have h1 : X ≤ (3 : ℝ) ^ n₀ :=
      hm2.le.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    have h2 : (0 : ℝ) < (3 : ℝ) ^ n₀ := by positivity
    nlinarith
  obtain ⟨L, rfl⟩ : ∃ L, N = n₀ + L := ⟨N - n₀, by omega⟩
  obtain ⟨hE, hO⟩ := hq n₀ L hXn₀ (by omega)
  refine ⟨n₀ + L, hN1, hN2, hE, hO.trans ?_⟩
  have hθ' : 0 < min θ 1 := lt_min hθ one_pos
  have hθ'1 : min θ 1 ≤ 1 := min_le_right _ _
  have hL1 : (1 : ℝ) ≤ 3 ^ L := one_le_pow₀ (by norm_num)
  have hstep1 : ((3 : ℝ) ^ L) ^ (-θ) ≤ ((3 : ℝ) ^ L) ^ (-min θ 1) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg (min_le_left _ _))
  have hstep2 : ((3 : ℝ) ^ (n₀ + L)) ^ (1 - min θ 1) ≤ 3 * r ^ (1 - min θ 1) := by
    calc ((3 : ℝ) ^ (n₀ + L)) ^ (1 - min θ 1) ≤ (3 * r) ^ (1 - min θ 1) :=
          Real.rpow_le_rpow (by positivity) hN2 (by linarith)
      _ = 3 ^ (1 - min θ 1) * r ^ (1 - min θ 1) := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 3 * r ^ (1 - min θ 1) := by
          have h31 : (3 : ℝ) ^ (1 - min θ 1) ≤ 3 := by
            calc (3 : ℝ) ^ (1 - min θ 1) ≤ 3 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 3 := Real.rpow_one 3
          have : 0 ≤ r ^ (1 - min θ 1) := Real.rpow_nonneg (by linarith) _
          nlinarith
  have hstep3 : ((3 : ℝ) ^ n₀) ^ (min θ 1) ≤ ((3 : ℝ) ^ (n₁ + 1) * X) ^ (min θ 1) :=
    Real.rpow_le_rpow (by positivity) h0 hθ'.le
  have hAw : 0 ≤ A * w := mul_nonneg hA hw
  calc A * w * (3 : ℝ) ^ (n₀ + L) * ((3 : ℝ) ^ L) ^ (-θ)
      ≤ A * w * (3 : ℝ) ^ (n₀ + L) * ((3 : ℝ) ^ L) ^ (-min θ 1) := by gcongr
    _ = A * w * (((3 : ℝ) ^ (n₀ + L)) ^ (1 - min θ 1) * ((3 : ℝ) ^ n₀) ^ (min θ 1)) := by
        rw [mul_assoc (A * w), three_pow_add_mul_rpow_neg]
    _ ≤ A * w * ((3 * r ^ (1 - min θ 1)) * ((3 : ℝ) ^ (n₁ + 1) * X) ^ (min θ 1)) := by
        gcongr
    _ = 3 * A * w * r ^ (1 - min θ 1) * ((3 : ℝ) ^ (n₁ + 1) * X) ^ min θ 1 := by ring

end Scales

section Package

variable {K : ℝ} {hK : 1 ≤ K} {P : Measure (Coefficient d K)} {κ C : ℝ}

/-- The tail of a power of a multiple of the homogenization scale. -/
theorem HighContrastCorrectorPackage.measure_scaledX_le
    (pk : HighContrastCorrectorPackage hK P κ C) (hP : LawHypotheses P) {B p : ℝ} (hB : 0 < B)
    (hp : 0 < p) (hC : 0 ≤ C) {t : ℝ} (ht : 1 ≤ t) :
    P {a | t * (B * (C * (2 + K / 1) ^ C)) ^ p ≤ (B * pk.X (toHighContrast hK a)) ^ p} ≤
      ENNReal.ofReal (Real.exp (-(t ^ ((d : ℝ) / p)))) := by
  set C₁ := C * (2 + K / 1) ^ C with hC₁def
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hC₁ : 0 ≤ C₁ := mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  have : IsProbabilityMeasure (P.map (toHighContrast hK)) :=
    isProbabilityMeasure_map_toHighContrast hK hP
  set t' := t ^ p⁻¹ with ht'def
  have ht' : 1 ≤ t' := Real.one_le_rpow ht (inv_nonneg.mpr hp.le)
  have hset : {a | t * (B * C₁) ^ p ≤ (B * pk.X (toHighContrast hK a)) ^ p} ⊆
      toHighContrast hK ⁻¹' {b | C₁ * t' ≤ pk.X b} := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at ha ⊢
    have hX0 : 0 ≤ pk.X (toHighContrast hK a) := le_trans zero_le_one (pk.one_le_X _)
    have h := Real.rpow_le_rpow (by positivity) ha (inv_nonneg.mpr hp.le)
    rw [Real.mul_rpow (by linarith) (by positivity), Real.rpow_rpow_inv (by positivity) hp.ne',
      Real.rpow_rpow_inv (by positivity) hp.ne'] at h
    have h2 : B * (C₁ * t') ≤ B * pk.X (toHighContrast hK a) := by
      rw [ht'def]
      linarith
    exact le_of_mul_le_mul_left h2 hB
  calc P {a | t * (B * C₁) ^ p ≤ (B * pk.X (toHighContrast hK a)) ^ p}
      ≤ P (toHighContrast hK ⁻¹' {b | C₁ * t' ≤ pk.X b}) := measure_mono hset
    _ = (P.map (toHighContrast hK)) {b | C₁ * t' ≤ pk.X b} :=
        (Measure.map_apply (measurable_toHighContrast hK)
          (measurableSet_le measurable_const pk.measurable_X)).symm
    _ = ENNReal.ofReal ((P.map (toHighContrast hK)).real {b | C₁ * t' ≤ pk.X b}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-(t' ^ (d : ℝ)))) := ENNReal.ofReal_le_ofReal (pk.tail t' ht')
    _ = ENNReal.ofReal (Real.exp (-(t ^ ((d : ℝ) / p)))) := by
        rw [ht'def, ← Real.rpow_mul (by linarith), inv_mul_eq_div]

end Package

section Main

/-- **Oscillation and energy bounds for source correctors.** There are `β > 0` and `C`
depending only on `d` and `K` such that for every `s ∈ (0, d)` there is `C_s` with the
following property. For every law and every unit slope `e`, a random radius `X ≥ 1` with
`X ≤ O_s(C_s)`, the same for all source correctors, bounds from below the scales `r` at which
every source corrector `φ` of slope `e` satisfies
`‖φ - (φ)_{B_r}‖_{L²(B_r)} ≤ C r^(1 - β(d-s))` and `‖∇φ‖_{L²(B_r)} ≤ C`, almost surely
(normalized norms). This is the scalar part of Armstrong, Kuusi and Mourrat, Lemma 3.17,
(3.85)–(3.86). -/
theorem exists_sourceCorrector_bounds (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (hK : 1 < K) :
    ∃ β C : ℝ, 0 < β ∧ 0 < C ∧ ∀ s : ℝ, 0 < s → s < d → ∃ Cs : ℝ, 0 < Cs ∧
      ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
        ∃ X : Coefficient d K → ℝ, Measurable X ∧ OsBound P X s Cs ∧ (∀ a, 1 ≤ X a) ∧
          ∀ e : Vec d, euclideanNorm e = 1 → ∀ φ : SourceCorrector P e,
            ∀ᵐ a ∂P, ∀ r : ℝ, X a ≤ r →
              Real.sqrt (⨍ x in ball 0 r,
                |φ.potential a x - (⨍ y in ball 0 r, φ.potential a y)| ^ 2) ≤
                  C * r ^ (1 - β * ((d : ℝ) - s)) ∧
              Real.sqrt (⨍ x in ball 0 r, euclideanSq (φ.grad a x)) ≤ C := by
  have hd0 : NeZero d := ⟨by omega⟩
  have hK1 : 1 ≤ K := hK.le
  obtain ⟨κ, C₀, hκ, hC₀, hpk⟩ := exists_highContrastCorrectorPackage d hd
  obtain ⟨A, θ, n₁, hA, hθ, hq⟩ := exists_highContrast_quantitative_bounds d K hK1 hκ hC₀.le
  have hθ'0 : 0 < min θ 1 := lt_min hθ one_pos
  have hV := ballCubeRatio_nonneg d
  set V := ballCubeRatio d with hVdef
  set Cφ := max 1 (max (2 * Real.sqrt V * (3 * A)) (Real.sqrt (V * A))) with hCφ
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdne : (d : ℝ) ≠ 0 := hdpos.ne'
  refine ⟨min θ 1 / (2 * d), Cφ, by positivity, lt_of_lt_of_le one_pos (le_max_left _ _),
    fun s hs hsd => ?_⟩
  have hds : 0 < (d : ℝ) + s := by positivity
  have hdsne : (d : ℝ) + s ≠ 0 := hds.ne'
  set p : ℝ := 2 * d / (d + s) with hp
  have hp0 : 0 < p := by positivity
  have hp1 : 1 ≤ p := by
    rw [hp, le_div_iff₀ hds]
    linarith
  have h3n : (1 : ℝ) ≤ (3 : ℝ) ^ (n₁ + 1) := one_le_pow₀ (by norm_num)
  have hK2 : (0 : ℝ) < 2 + K / 1 := by linarith
  have hC₁ : 0 < C₀ * (2 + K / 1) ^ C₀ := mul_pos hC₀ (Real.rpow_pos_of_pos hK2 _)
  have hA₁ : 0 < ((3 : ℝ) ^ (n₁ + 1) * (C₀ * (2 + K / 1) ^ C₀)) ^ p :=
    Real.rpow_pos_of_pos (mul_pos (by positivity) hC₁) _
  refine ⟨(8 : ℝ) ^ s⁻¹ * ((3 : ℝ) ^ (n₁ + 1) * (C₀ * (2 + K / 1) ^ C₀)) ^ p,
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hA₁, fun P hP => ?_⟩
  obtain ⟨pk⟩ := hpk K hK1 P hP
  have hprob : IsProbabilityMeasure P := hP.1
  have hXm : Measurable fun a => ((3 : ℝ) ^ (n₁ + 1) * pk.X (toHighContrast hK1 a)) ^ p :=
    ((pk.measurable_X.comp (measurable_toHighContrast hK1)).const_mul _).pow_const p
  have hX1 : ∀ a, 1 ≤ ((3 : ℝ) ^ (n₁ + 1) * pk.X (toHighContrast hK1 a)) ^ p := fun a =>
    Real.one_le_rpow (one_le_mul_of_one_le_of_one_le h3n (pk.one_le_X _)) hp0.le
  refine ⟨fun a => ((3 : ℝ) ^ (n₁ + 1) * pk.X (toHighContrast hK1 a)) ^ p, hXm, ?_, hX1,
    fun e he φ => ?_⟩
  · have hq' : s ≤ (d : ℝ) / p := by
      have h : (d : ℝ) / p = (d + s) / 2 := by
        rw [hp, div_div_eq_mul_div, eq_div_iff two_ne_zero, div_mul_eq_mul_div,
          div_eq_iff (by positivity)]
        ring
      rw [h]
      linarith
    exact osBound_of_tail hXm hs hq' hA₁ fun t ht =>
      pk.measure_scaledX_le hP (by positivity) hp0 hC₀.le ht
  · have he1 : vecNormSq e = 1 := by
      have h : Real.sqrt (euclideanSq e) = 1 := he
      rwa [Real.sqrt_eq_one] at h
    filter_upwards [ae_dilated_eq_highContrast hP hd hκ hC₀.le pk φ,
      φ.locally_square_integrable] with a ha hloc
    obtain ⟨hb, ⟨c, hc⟩, hgrad⟩ := ha
    have hbell := ae_isEllipticMatrix_toHighContrast hK1 a
    intro r hr
    have hr' : ((3 : ℝ) ^ (n₁ + 1) * pk.X (toHighContrast hK1 a)) ^ p ≤ r := hr
    generalize hbdef : toHighContrast hK1 a = b at hb hc hgrad hbell hr'
    have hXb1 : 1 ≤ pk.X b := pk.one_le_X b
    have hXb0 : 0 ≤ pk.X b := zero_le_one.trans hXb1
    have hBX1 : 1 ≤ (3 : ℝ) ^ (n₁ + 1) * pk.X b := one_le_mul_of_one_le_of_one_le h3n hXb1
    have hBXr : (3 : ℝ) ^ (n₁ + 1) * pk.X b ≤ r := by
      calc (3 : ℝ) ^ (n₁ + 1) * pk.X b = ((3 : ℝ) ^ (n₁ + 1) * pk.X b) ^ (1 : ℝ) :=
            (Real.rpow_one _).symm
        _ ≤ ((3 : ℝ) ^ (n₁ + 1) * pk.X b) ^ p := Real.rpow_le_rpow_of_exponent_le hBX1 hp1
        _ ≤ r := hr'
    have hr0 : 0 < r := by linarith
    have hBXp : (3 : ℝ) ^ (n₁ + 1) * pk.X b ≤ r ^ p⁻¹ := by
      have h := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hr' (inv_nonneg.mpr hp0.le)
      rwa [Real.rpow_rpow_inv (by linarith) hp0.ne'] at h
    obtain ⟨N, hN1, hN2, hE, hO⟩ := exists_cube_le_of_scale_bounds (d := d) hA hθ
      (Real.sqrt_nonneg (vecNormSq e)) hXb1
      (E := fun N => cubeAverage (originCube d (N : ℤ))
        (fun x => vecNormSq ((pk.wholeSpaceSolution hb hbell e).correctorGrad e x)))
      (O := fun N => cubeBesovOscillation (originCube d (N : ℤ)) 2
        ((pk.wholeSpaceSolution hb hbell e).corrector e))
      (fun n₀ L hX hn => hq P pk hb hbell e n₀ L hX hn) hBXr
    set ρ := r / 2 with hρ
    have hρ0 : 0 < ρ := by positivity
    have hr2 : 2 * ρ = r := by
      rw [hρ]
      ring
    have hρN : ρ ≤ (3 : ℝ) ^ N / 2 := by
      rw [hρ]
      linarith
    have hratio : ((3 : ℝ) ^ N) ^ d / volume.real (ball (0 : Vec d) ρ) ≤ V :=
      cube_div_ball_le hρ0 (by rw [hρ]; linarith)
    have hgrad' : dilatedGradient (φ.grad a) =ᵐ[volume]
        fun y => (pk.wholeSpaceSolution hb hbell e).correctorGrad e y := by
      filter_upwards [hgrad] with y hy
      exact hy.trans (pk.wholeSpaceSolution_correctorGrad hb hbell e y).symm
    have hc' : dilatedCorrectedAffine e (φ.potential a) =ᵐ[volume]
        fun y => vecDot e y + (pk.wholeSpaceSolution hb hbell e).corrector e y + c := by
      filter_upwards [hc] with y hy
      rw [hy, pk.wholeSpaceSolution_corrector hb hbell e y]
    have hEball : ⨍ x in ball 0 r, euclideanSq (φ.grad a x) ≤ V * A := by
      rw [← hr2, setAverage_ball_two_mul_euclideanSq_eq hρ0 hgrad']
      calc ⨍ y in ball 0 ρ, vecNormSq ((pk.wholeSpaceSolution hb hbell e).correctorGrad e y)
          ≤ ((3 : ℝ) ^ N) ^ d / volume.real (ball (0 : Vec d) ρ) *
              cubeAverage (originCube d (N : ℤ))
                (fun x => vecNormSq ((pk.wholeSpaceSolution hb hbell e).correctorGrad e x)) :=
            (pk.wholeSpaceSolution hb hbell e).setAverage_ball_vecNormSq_le e hρ0 hρN
        _ ≤ V * (A * vecNormSq e) :=
            mul_le_mul hratio hE
              ((pk.wholeSpaceSolution hb hbell e).cubeAverage_correctorGrad_nonneg e N) hV
        _ = V * A := by rw [he1, mul_one]
    set γ := 1 - min θ 1 / (2 * d) * ((d : ℝ) - s) with hγ
    have hOr : cubeBesovOscillation (originCube d (N : ℤ)) 2
        ((pk.wholeSpaceSolution hb hbell e).corrector e) ≤ 3 * A * r ^ γ := by
      refine hO.trans ?_
      rw [he1, Real.sqrt_one, mul_one]
      have h1 : ((3 : ℝ) ^ (n₁ + 1) * pk.X b) ^ min θ 1 ≤ r ^ (p⁻¹ * min θ 1) := by
        rw [Real.rpow_mul hr0.le]
        exact Real.rpow_le_rpow (by positivity) hBXp hθ'0.le
      have h2 : r ^ (1 - min θ 1) * r ^ (p⁻¹ * min θ 1) = r ^ γ := by
        rw [← Real.rpow_add hr0, hγ, hp, inv_div]
        congr 1
        field_simp
        ring
      calc 3 * A * r ^ (1 - min θ 1) * ((3 : ℝ) ^ (n₁ + 1) * pk.X b) ^ min θ 1
          ≤ 3 * A * r ^ (1 - min θ 1) * r ^ (p⁻¹ * min θ 1) := by gcongr
        _ = 3 * A * r ^ γ := by rw [mul_assoc, h2]
    have hO0 : 0 ≤ cubeBesovOscillation (originCube d (N : ℤ)) 2
        ((pk.wholeSpaceSolution hb hbell e).corrector e) := ENNReal.toReal_nonneg
    have hOball : ⨍ x in ball 0 r,
        |φ.potential a x - (⨍ y in ball 0 r, φ.potential a y)| ^ 2 ≤
          (2 * Real.sqrt V * (3 * A * r ^ γ)) ^ 2 := by
      have hu : MemLp (φ.potential a) 2 (volume.restrict (ball 0 (2 * ρ))) :=
        (hloc _ (by positivity)).1
      have h := setAverage_ball_two_mul_sq_le hρ0 e hu hc'
        (cubeAverage (originCube d (N : ℤ)) ((pk.wholeSpaceSolution hb hbell e).corrector e))
      rw [hr2] at h
      refine h.trans ?_
      calc 4 * ⨍ y in ball 0 ρ, ((pk.wholeSpaceSolution hb hbell e).corrector e y -
            cubeAverage (originCube d (N : ℤ)) ((pk.wholeSpaceSolution hb hbell e).corrector e)) ^ 2
          ≤ 4 * (((3 : ℝ) ^ N) ^ d / volume.real (ball (0 : Vec d) ρ) *
              cubeBesovOscillation (originCube d (N : ℤ)) 2
                ((pk.wholeSpaceSolution hb hbell e).corrector e) ^ 2) := by
            gcongr
            exact (pk.wholeSpaceSolution hb hbell e).setAverage_ball_sq_le e hρ0 hρN
        _ ≤ 4 * (V * (3 * A * r ^ γ) ^ 2) := by gcongr
        _ = (2 * Real.sqrt V * (3 * A * r ^ γ)) ^ 2 := by
            rw [show (2 * Real.sqrt V * (3 * A * r ^ γ)) ^ 2 =
              4 * (Real.sqrt V ^ 2 * (3 * A * r ^ γ) ^ 2) by ring, Real.sq_sqrt hV]
    have hrγ : 0 ≤ r ^ γ := Real.rpow_nonneg hr0.le _
    refine ⟨?_, ?_⟩
    · calc Real.sqrt (⨍ x in ball 0 r,
            |φ.potential a x - (⨍ y in ball 0 r, φ.potential a y)| ^ 2)
          ≤ Real.sqrt ((2 * Real.sqrt V * (3 * A * r ^ γ)) ^ 2) := Real.sqrt_le_sqrt hOball
        _ = 2 * Real.sqrt V * (3 * A) * r ^ γ := by
            rw [Real.sqrt_sq (by positivity)]
            ring
        _ ≤ Cφ * r ^ γ :=
            mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hrγ
    · calc Real.sqrt (⨍ x in ball 0 r, euclideanSq (φ.grad a x)) ≤ Real.sqrt (V * A) :=
            Real.sqrt_le_sqrt hEball
        _ ≤ Cφ := (le_max_right _ _).trans (le_max_right _ _)

end Main

end EinsteinFull.Homogenization
