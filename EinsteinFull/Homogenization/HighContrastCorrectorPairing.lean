import EinsteinFull.Homogenization.HighContrastWholeSpace
import EinsteinFull.Homogenization.HighContrastSlope

/-!
# Pairings of high-contrast correctors with cube cutoffs

The corrector estimate of Armstrong, Kuusi and Loher, *Homogenization at a polynomial scale in
high contrast*, bounds the normalized `H⁻¹` norm of the adapted corrector gradient on the
ellipsoids `E_r`. Paired with a smooth cutoff supported in a set `A ⊂ E_r`, it bounds the
integral of the cutoff against a partial derivative of the corrector by the square root of the
volume of `A`, the gradient bound of the cutoff, and the decay factor `(r / X)^(-κ)`. On the
triadic subcubes of an origin cube this is the pairing bound consumed by the energy iteration.
-/

open MeasureTheory Filter Topology

namespace EinsteinFull.Homogenization

open _root_.Homogenization hiding euclideanBall
open _root_.Homogenization.HighContrast

variable {d : ℕ}

theorem eVolumeAverage_le_of_le_indicator {V A : Set (Vec d)} (hA : MeasurableSet A)
    {f : Vec d → ENNReal} {c : ENNReal}
    (hf : ∀ x, f x ≤ A.indicator (fun _ => c) x) :
    eVolumeAverage V f ≤ c * volume A / volume V := by
  unfold eVolumeAverage
  refine ENNReal.div_le_div_right ?_ _
  calc ∫⁻ x in V, f x ≤ ∫⁻ x in V, A.indicator (fun _ => c) x := lintegral_mono hf
    _ = c * (volume.restrict V) A := lintegral_indicator_const hA c
    _ ≤ c * volume A := by
        gcongr
        exact Measure.restrict_le_self

/-- The normalized test norm of a cutoff supported in `A`, times a fixed vector. -/
theorem h1NormSq_smul_le_of_tsupport {V A : Set (Vec d)} (hA : MeasurableSet A)
    (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ⊤) (hAtop : volume A ≠ ⊤) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηA : tsupport η ⊆ A) (hη0 : ∀ x, 0 ≤ η x)
    (hη1 : ∀ x, η x ≤ 1) {M : ℝ} (hM : ∀ x, ‖fderiv ℝ η x‖ ≤ M) (w : Vec d) :
    h1NormSq V (fun x => η x • w) ≤
      ENNReal.ofReal (vecNormSq w * ((volume A).toReal / (volume V).toReal) *
        ((volume V).toReal ^ (-(2 : ℝ) / d) + d * M ^ 2)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hdiff : Differentiable ℝ η := hη.differentiable (by simp)
  have hval (x : Vec d) : ENNReal.ofReal (vecNormSq (η x • w)) ≤
      A.indicator (fun _ => ENNReal.ofReal (vecNormSq w)) x := by
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      refine ENNReal.ofReal_le_ofReal ?_
      have : vecNormSq (η x • w) = η x ^ 2 * vecNormSq w := by
        simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [this]
      have h0 := hη0 x
      have h1 := hη1 x
      have hsq : η x ^ 2 ≤ 1 := by nlinarith
      nlinarith [vecNormSq_nonneg w]
    · rw [Set.indicator_of_notMem hx]
      have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hηA h)
      simp [hηx, vecNormSq, vecDot]
  have hgrad (x : Vec d) : ENNReal.ofReal (∑ j, vecNormSq (smoothGrad (fun y => (η y • w) j) x)) ≤
      A.indicator (fun _ => ENNReal.ofReal (vecNormSq w * (d * M ^ 2))) x := by
    have hcomp (j : Fin d) : smoothGrad (fun y => (η y • w) j) x = w j • smoothGrad η x := by
      have : (fun y => (η y • w) j) = fun y => w j * η y := by
        funext y
        simp [smul_eq_mul, mul_comm]
      rw [this, smoothGrad_const_mul hdiff]
    have hsum : ∑ j, vecNormSq (smoothGrad (fun y => (η y • w) j) x) =
        vecNormSq w * vecNormSq (smoothGrad η x) := by
      simp only [hcomp]
      simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, hsum]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := vecNormSq_smoothGrad_le η x
      have h2 : ‖fderiv ℝ η x‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM x) 2
      have h3 : vecNormSq (smoothGrad η x) ≤ d * M ^ 2 :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d))
      exact mul_le_mul_of_nonneg_left h3 (vecNormSq_nonneg w)
    · rw [Set.indicator_of_notMem hx, hsum]
      have hfd : fderiv ℝ η x = 0 := by
        by_contra hne
        exact hx (hηA (support_fderiv_subset ℝ hne))
      have hg : smoothGrad η x = 0 := by
        funext i
        simp [smoothGrad, hfd]
      simp [hg, vecNormSq, vecDot]
  have hA1 := eVolumeAverage_le_of_le_indicator (V := V) hA hval
  have hB1 := eVolumeAverage_le_of_le_indicator (V := V) hA hgrad
  have hVreal : 0 < (volume V).toReal := ENNReal.toReal_pos hV0 hVtop
  have hpow : volume V ^ (-(2 : ℝ) / d) = ENNReal.ofReal ((volume V).toReal ^ (-(2 : ℝ) / d)) := by
    rw [← ENNReal.ofReal_toReal hVtop, ENNReal.ofReal_rpow_of_pos hVreal, ENNReal.toReal_ofReal
      ENNReal.toReal_nonneg]
  have hratio (c : ℝ) (hc : 0 ≤ c) : ENNReal.ofReal c * volume A / volume V =
      ENNReal.ofReal (c * ((volume A).toReal / (volume V).toReal)) := by
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_div_of_pos hVreal, ENNReal.ofReal_toReal hAtop,
      ENNReal.ofReal_toReal hVtop, mul_div_assoc]
  unfold h1NormSq
  rw [hpow]
  calc ENNReal.ofReal ((volume V).toReal ^ (-(2 : ℝ) / d)) *
        eVolumeAverage V (fun x => ENNReal.ofReal (vecNormSq (η x • w))) +
      eVolumeAverage V (fun x => ENNReal.ofReal
        (∑ j, vecNormSq (smoothGrad (fun y => (η y • w) j) x)))
      ≤ ENNReal.ofReal ((volume V).toReal ^ (-(2 : ℝ) / d)) *
          (ENNReal.ofReal (vecNormSq w) * volume A / volume V) +
        ENNReal.ofReal (vecNormSq w * (d * M ^ 2)) * volume A / volume V := by
        gcongr
    _ = ENNReal.ofReal (vecNormSq w * ((volume A).toReal / (volume V).toReal) *
        ((volume V).toReal ^ (-(2 : ℝ) / d) + d * M ^ 2)) := by
        have hw0 := vecNormSq_nonneg w
        have hdM : 0 ≤ vecNormSq w * (d * M ^ 2) := mul_nonneg hw0 (by positivity)
        have hrat : 0 ≤ (volume A).toReal / (volume V).toReal := by positivity
        rw [hratio _ hw0, hratio _ hdM,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hVreal.le _),
          ← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg hVreal.le _) (mul_nonneg hw0 hrat))
            (mul_nonneg hdM hrat)]
        congr 1
        ring

/-- An integral against a local test is bounded by the volume, the test norm and the
negative-one norm. -/
theorem abs_setIntegral_le_of_negOneNorm_le {V : Set (Vec d)} (hV0 : volume V ≠ 0)
    (hVtop : volume V ≠ ⊤) {F ψ : Vec d → Vec d} (htest : IsLocalVecTest V ψ)
    (hint : IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume) {Kψ N : ℝ} (hK : 0 < Kψ)
    (hN : 0 ≤ N) (hnorm : h1NormSq V ψ ≤ ENNReal.ofReal Kψ)
    (hneg : negOneNorm V F ≤ ENNReal.ofReal N) :
    |∫ x in V, vecDot (F x) (ψ x)| ≤ (volume V).toReal * (Real.sqrt Kψ * N) := by
  have h := abs_volumeAverage_le_of_negOneNorm_le hK hN htest hint hnorm hneg
  have hVreal : 0 < (volume V).toReal := ENNReal.toReal_pos hV0 hVtop
  unfold volumeAverage at h
  rw [abs_mul, abs_of_pos (inv_pos.mpr hVreal), inv_mul_le_iff₀ hVreal] at h
  exact h

/-- The integral bound of `abs_setIntegral_le_of_negOneNorm_le`, for a nonnegative test norm
bound. -/
theorem abs_setIntegral_le_of_negOneNorm_le' {V : Set (Vec d)} (hV0 : volume V ≠ 0)
    (hVtop : volume V ≠ ⊤) {F ψ : Vec d → Vec d} (htest : IsLocalVecTest V ψ)
    (hint : IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume) {Kψ N : ℝ} (hK : 0 ≤ Kψ)
    (hN : 0 ≤ N) (hnorm : h1NormSq V ψ ≤ ENNReal.ofReal Kψ)
    (hneg : negOneNorm V F ≤ ENNReal.ofReal N) :
    |∫ x in V, vecDot (F x) (ψ x)| ≤ (volume V).toReal * (Real.sqrt Kψ * N) := by
  have hbound : ∀ t : ℝ, 0 < t →
      |∫ x in V, vecDot (F x) (ψ x)| ≤ (volume V).toReal * (Real.sqrt (Kψ + t) * N) := by
    intro t ht
    exact abs_setIntegral_le_of_negOneNorm_le hV0 hVtop htest hint (by linarith) hN
      (hnorm.trans (ENNReal.ofReal_le_ofReal (by linarith))) hneg
  have hlim : Tendsto (fun t : ℝ => (volume V).toReal * (Real.sqrt (Kψ + t) * N))
      (𝓝[>] 0) (𝓝 ((volume V).toReal * (Real.sqrt Kψ * N))) := by
    have hc : Continuous (fun t : ℝ => (volume V).toReal * (Real.sqrt (Kψ + t) * N)) := by
      fun_prop
    have h := hc.tendsto 0
    rw [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht => hbound t ht)

theorem sqrt_sq_add_mul_sq_le {a M : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M) {n : ℝ} (hn : 1 ≤ n) :
    Real.sqrt (a ^ 2 + n * M ^ 2) ≤ Real.sqrt n * (M + a) := by
  rw [Real.sqrt_le_left (by positivity)]
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  nlinarith [mul_nonneg ha hM, sq_nonneg a]

/-- The volume factor of the test norm on `E_r` is at most the one of the ball `B_r`. -/
theorem volume_ellipsoid_rpow_le (abar : Mat d) (hd : 0 < d) {r : ℝ} (hr : 0 < r)
    (hS : (symmPart abar).PosDef) :
    (volume (ellipsoid abar r)).toReal ^ (-(1 : ℝ) / d) ≤
      (volume (euclideanBall d 1)).toReal ^ (-(1 : ℝ) / d) / r := by
  have hB0 : 0 < (volume (euclideanBall d 1)).toReal :=
    ENNReal.toReal_pos (volume_euclideanBall_pos' one_pos).ne' (volume_euclideanBall_ne_top' 1)
  have hBr : (volume (euclideanBall d r)).toReal ≤ (volume (ellipsoid abar r)).toReal :=
    ENNReal.toReal_mono (volume_ellipsoid_lt_top hS r).ne
      (measure_mono (euclideanBallAt_zero_subset_ellipsoid abar r))
  have hBr0 : 0 < (volume (euclideanBall d r)).toReal :=
    ENNReal.toReal_pos (volume_euclideanBall_pos' hr).ne' (volume_euclideanBall_ne_top' r)
  have hexp : -(1 : ℝ) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg d)
  calc (volume (ellipsoid abar r)).toReal ^ (-(1 : ℝ) / d)
      ≤ (volume (euclideanBall d r)).toReal ^ (-(1 : ℝ) / d) :=
        Real.rpow_le_rpow_of_nonpos hBr0 hBr hexp
    _ = (volume (euclideanBall d 1)).toReal ^ (-(1 : ℝ) / d) / r := by
        rw [volume_euclideanBall_toReal hr, Real.mul_rpow (by positivity) hB0.le,
          ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
        have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
        rw [show (d : ℝ) * (-(1 : ℝ) / d) = -1 by field_simp, Real.rpow_neg_one]
        field_simp

section Package

variable {K : ℝ} {hK : 1 ≤ K}
  {P : Measure (EinsteinRelation.Environment.AKMTestIntegralSupport.Coefficient d K)} {κ C : ℝ}

/-- **Cutoff pairing with the corrector gradient.** For a smooth cutoff supported in a
measurable subset `A` of `E_r` with `r ≥ X`, the integral of the cutoff against the corrector
gradient in the direction `sᵀ w` is bounded by the corrector estimate. -/
theorem HighContrastCorrectorPackage.abs_integral_mul_gradPhi_le
    (pk : HighContrastCorrectorPackage hK P κ C) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend) (e : Vec d) {r : ℝ} (hr : 0 < r) (hrX : pk.X b ≤ r)
    (hloc : ∀ i, LocallyIntegrable (fun x => pk.gradPhi e b x i) volume)
    {A : Set (Vec d)} (hA : MeasurableSet A) (hAV : A ⊆ ellipsoid pk.abar r)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηcs : HasCompactSupport η)
    (hηA : tsupport η ⊆ A) (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ η x‖ ≤ M) (w : Vec d) :
    |∫ x, η x * vecDot (pk.gradPhi e b x)
        (matVecMul (matTranspose (matSqrt (symmPart pk.abar))) w)| ≤
      (volume (ellipsoid pk.abar r)).toReal *
        (Real.sqrt (vecNormSq w * ((volume A).toReal / (volume (ellipsoid pk.abar r)).toReal) *
          ((volume (ellipsoid pk.abar r)).toReal ^ (-(2 : ℝ) / d) + d * M ^ 2)) *
        (r * (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) *
          (r / pk.X b) ^ (-κ)))) := by
  set S := matSqrt (symmPart pk.abar)
  set V := ellipsoid pk.abar r
  set F : Vec d → Vec d := fun x => matVecMul S (pk.gradPhi e b x)
  set ψ : Vec d → Vec d := fun x => η x • w
  set B : ℝ := C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) * (r / pk.X b) ^ (-κ)
  have hSpd : (symmPart pk.abar).PosDef := posDef_symmPart_of_vecDot_pos pk.posDef
  have hVtop : volume V ≠ ⊤ := (volume_ellipsoid_lt_top hSpd r).ne
  have hVpos : 0 < volume V := volume_ellipsoid_pos pk.abar hr
  have hAtop : volume A ≠ ⊤ := ((measure_mono hAV).trans_lt (volume_ellipsoid_lt_top hSpd r)).ne
  have htest : IsLocalVecTest V ψ :=
    ⟨hη.smul contDiff_const, hηcs.smul_right,
      (tsupport_smul_subset_left η (fun _ => w)).trans (hηA.trans hAV)⟩
  have hpt (x : Vec d) : vecDot (F x) (ψ x) =
      η x * vecDot (pk.gradPhi e b x) (matVecMul (matTranspose S) w) := by
    simp only [F, ψ]
    rw [vecDot_matVecMul_transpose]
    simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hcont : Continuous η := hη.continuous
  have hint : Integrable (fun x => η x * vecDot (pk.gradPhi e b x)
      (matVecMul (matTranspose S) w)) := by
    simp only [vecDot, Finset.mul_sum]
    refine integrable_finsetSum _ fun i _ => ?_
    have := ((hloc i).integrable_smul_left_of_hasCompactSupport hcont hηcs)
    have h2 := this.mul_const ((matVecMul (matTranspose S) w) i)
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul]
    ring
  have hintV : IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume := by
    simp_rw [hpt]
    exact hint.integrableOn
  have hnormV := h1NormSq_smul_le_of_tsupport hA hVpos.ne' hVtop hAtop hη hηA hη0 hη1 hM w
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
  have hVreal : 0 < (volume V).toReal := ENNReal.toReal_pos hVpos.ne' hVtop
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hK0 : 0 ≤ vecNormSq w * ((volume A).toReal / (volume V).toReal) *
      ((volume V).toReal ^ (-(2 : ℝ) / d) + d * M ^ 2) :=
    mul_nonneg (mul_nonneg (vecNormSq_nonneg w) (by positivity))
      (add_nonneg (Real.rpow_nonneg hVreal.le _) (by positivity))
  have hmain := abs_setIntegral_le_of_negOneNorm_le' hVpos.ne' hVtop htest hintV hK0
    (mul_nonneg hr.le hB0) hnormV hneg
  have hzero : ∫ x, η x * vecDot (pk.gradPhi e b x) (matVecMul (matTranspose S) w) =
      ∫ x in V, vecDot (F x) (ψ x) := by
    simp_rw [hpt]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    have hxη : x ∉ tsupport η := fun h => hx (hAV (hηA h))
    simp [image_eq_zero_of_notMem_tsupport hxη]
  rw [hzero]
  exact hmain

/-- The dimensional constant `|B₁|^(-1/d)` of the lower-order term of the pairing bound. -/
noncomputable def ballVolumeConstant (d : ℕ) : ℝ :=
  (volume (euclideanBall d 1)).toReal ^ (-(1 : ℝ) / d)

theorem ballVolumeConstant_nonneg (d : ℕ) : 0 ≤ ballVolumeConstant d :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

/-- The amplitude of the pairing bound of the corrector of direction `e` at the scale `3ᴺ`. -/
noncomputable def HighContrastCorrectorPackage.pairingAmplitude
    (pk : HighContrastCorrectorPackage hK P κ C) (b : CoeffSpace d) (e : Vec d) (N : ℕ) : ℝ :=
  Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
    Real.sqrt (∑ i, vecNormSq (matVecMul (matSqrt (symmPart pk.abar))⁻¹ (basisVec i))) *
    (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) *
      ((Real.sqrt d * (3 : ℝ) ^ N) / pk.X b) ^ (-κ))

theorem HighContrastCorrectorPackage.pairingAmplitude_nonneg
    (pk : HighContrastCorrectorPackage hK P κ C) (hC : 0 ≤ C) (b : CoeffSpace d) (e : Vec d)
    (N : ℕ) : 0 ≤ pk.pairingAmplitude b e N := by
  have hX : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
  unfold HighContrastCorrectorPackage.pairingAmplitude
  exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _))
    (Real.rpow_nonneg (by positivity) _))

theorem sqrt_volume_ellipsoid_sqrt_mul (abar : Mat d) [NeZero d] (N : ℕ) :
    Real.sqrt (volume (ellipsoid abar (Real.sqrt d * (3 : ℝ) ^ N))).toReal =
      Real.sqrt (volume (ellipsoid abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) *
        Real.sqrt ((3 : ℝ) ^ (N * d)) := by
  have hr : 0 < Real.sqrt d * (3 : ℝ) ^ N :=
    EllipticWholeSpaceSolution.sqrt_mul_three_pow_pos N
  rw [volume_ellipsoid_toReal abar hr, mul_pow, ← pow_mul, mul_comm N d,
    Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  ring

theorem sqrt_testFactor_le (abar : Mat d) [NeZero d] (hS : (symmPart abar).PosDef) (N : ℕ)
    {M : ℝ} (hM : 0 ≤ M) :
    Real.sqrt ((volume (ellipsoid abar (Real.sqrt d * (3 : ℝ) ^ N))).toReal ^ (-(2 : ℝ) / d) +
        d * M ^ 2) ≤
      Real.sqrt d * (M + ballVolumeConstant d * ((3 : ℝ) ^ N)⁻¹) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hr : 0 < Real.sqrt d * (3 : ℝ) ^ N :=
    EllipticWholeSpaceSolution.sqrt_mul_three_pow_pos N
  set v := (volume (ellipsoid abar (Real.sqrt d * (3 : ℝ) ^ N))).toReal with hv
  have hv0 : 0 < v := ENNReal.toReal_pos (volume_ellipsoid_pos abar hr).ne'
    (volume_ellipsoid_lt_top hS _).ne
  set a := v ^ (-(1 : ℝ) / d) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg hv0.le _
  have hsq : a ^ 2 = v ^ (-(2 : ℝ) / d) := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hv0.le]
    congr 1
    push_cast
    ring
  have hn : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 := sqrt_sq_add_mul_sq_le ha0 hM hn
  rw [hsq] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  have h2 := volume_ellipsoid_rpow_le abar hd hr hS
  rw [← hv, ← ha] at h2
  have hsd : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hn
  have h3 : ballVolumeConstant d / (Real.sqrt d * (3 : ℝ) ^ N) ≤
      ballVolumeConstant d * ((3 : ℝ) ^ N)⁻¹ := by
    rw [div_eq_mul_inv, mul_inv]
    have hc := ballVolumeConstant_nonneg d
    have h3N : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
    have hinv : (Real.sqrt d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsd
    calc ballVolumeConstant d * ((Real.sqrt d)⁻¹ * ((3 : ℝ) ^ N)⁻¹)
        ≤ ballVolumeConstant d * (1 * ((3 : ℝ) ^ N)⁻¹) := by gcongr
      _ = ballVolumeConstant d * ((3 : ℝ) ^ N)⁻¹ := by rw [one_mul]
  unfold ballVolumeConstant at h3 ⊢
  linarith

/-- **The pairing bound on origin cubes.** At every scale `3ᴺ` with `X ≤ √d 3ᴺ`, the
corrector gradient of direction `e` satisfies the pairing bound with the amplitude
`pairingAmplitude` and the dimensional constant `|B₁|^(-1/d)`. -/
theorem HighContrastCorrectorPackage.pairingBound [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d)
    {N : ℕ} (hNX : pk.X b ≤ Real.sqrt d * (3 : ℝ) ^ N) (m : ℕ) :
    (pk.wholeSpaceSolution hb hbell e).PairingBound e (pk.pairingAmplitude b e N)
      (ballVolumeConstant d) N m := by
  intro j hj R hR η hη hcs hts hη0 hη1 M hM i
  set s := pk.wholeSpaceSolution hb hbell e
  set S := matSqrt (symmPart pk.abar)
  have hSpd : (symmPart pk.abar).PosDef := posDef_symmPart_of_vecDot_pos pk.posDef
  set r := Real.sqrt d * (3 : ℝ) ^ N with hr_def
  have hr : 0 < r := EllipticWholeSpaceSolution.sqrt_mul_three_pow_pos N
  set w := matVecMul S⁻¹ (basisVec i) with hw
  have hST : matTranspose S = S := isSymm_matSqrt _
  have hSw : matVecMul (matTranspose S) w = basisVec i := by
    rw [hST, hw, matVecMul_mul, Matrix.mul_nonsing_inv _ (isUnit_det_matSqrt hSpd),
      _root_.Homogenization.matVecMul_one]
  have hloc : ∀ k, LocallyIntegrable (fun x => pk.gradPhi e b x k) volume := by
    intro k
    have h := (s.locallyIntegrable_Dv k).sub (locallyIntegrable_const (e k))
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [s, HighContrastCorrectorPackage.wholeSpaceSolution]
  have hRQ : openCubeSet R ⊆ cubeSet (originCube d (N : ℤ)) :=
    (openCubeSet_subset_cubeSet R).trans (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have hAV : openCubeSet R ⊆ ellipsoid pk.abar r :=
    hRQ.trans ((cubeSet_originCube_subset_euclideanBall N).trans
      (euclideanBallAt_zero_subset_ellipsoid pk.abar r))
  have hmain := pk.abs_integral_mul_gradPhi_le hC hb e hr hNX hloc (isOpen_openCubeSet R).measurableSet
    hAV hη hcs hts hη0 hη1 hM w
  have hint_eq : ∫ x, η x * s.correctorGrad e x i =
      ∫ x, η x * vecDot (pk.gradPhi e b x) (matVecMul (matTranspose S) w) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hc : s.correctorGrad e x = pk.gradPhi e b x := pk.wholeSpaceSolution_correctorGrad hb hbell e x
    show η x * s.correctorGrad e x i = η x * vecDot (pk.gradPhi e b x) (matVecMul (matTranspose S) w)
    rw [hSw, hc]
    simp [vecDot, basisVec, Pi.single_apply]
  rw [hint_eq]
  refine hmain.trans ?_
  set v := (volume (ellipsoid pk.abar r)).toReal with hv
  have hv0 : 0 < v := ENNReal.toReal_pos (volume_ellipsoid_pos pk.abar hr).ne'
    (volume_ellipsoid_lt_top hSpd r).ne
  set a := (volume (openCubeSet R)).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have haR : a = cubeVolume R := volume_openCubeSet_toReal R
  set T := v ^ (-(2 : ℝ) / d) + d * M ^ 2 with hT
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hT0 : 0 ≤ T := add_nonneg (Real.rpow_nonneg hv0.le _) (by positivity)
  set B := C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) * (r / pk.X b) ^ (-κ)
    with hB
  have hB0 : 0 ≤ B := by
    have hX : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
    exact mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _))
      (Real.rpow_nonneg (div_nonneg hr.le hX.le) _)
  set W := Real.sqrt (∑ k, vecNormSq (matVecMul S⁻¹ (basisVec k))) with hW
  have hwW : Real.sqrt (vecNormSq w) ≤ W := by
    refine Real.sqrt_le_sqrt ?_
    exact Finset.single_le_sum (f := fun k => vecNormSq (matVecMul S⁻¹ (basisVec k)))
      (fun k _ => vecNormSq_nonneg _) (Finset.mem_univ i)
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
  have hTle := sqrt_testFactor_le pk.abar hSpd N hM0
  rw [← hv, ← hT] at hTle
  have hvsq := sqrt_volume_ellipsoid_sqrt_mul pk.abar N
  rw [← hr_def, ← hv] at hvsq
  have hdd : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  rw [hsplit, hvsq, ← haR]
  have hrB : r * B = Real.sqrt d * (3 : ℝ) ^ N * B := by rw [hr_def]
  rw [hrB]
  have hamp : pk.pairingAmplitude b e N = Real.sqrt (volume (ellipsoid pk.abar 1)).toReal *
      Real.sqrt (Real.sqrt d ^ d) * d * W * B := by
    rw [HighContrastCorrectorPackage.pairingAmplitude, hB, hr_def]
  rw [hamp]
  have hc0 : 0 ≤ Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) *
      Real.sqrt ((3 : ℝ) ^ (N * d)) := by positivity
  calc Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) *
        Real.sqrt ((3 : ℝ) ^ (N * d)) * Real.sqrt (vecNormSq w) * Real.sqrt a * Real.sqrt T *
        (Real.sqrt d * (3 : ℝ) ^ N * B)
      ≤ Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) *
        Real.sqrt ((3 : ℝ) ^ (N * d)) * W * Real.sqrt a *
        (Real.sqrt d * (M + ballVolumeConstant d * ((3 : ℝ) ^ N)⁻¹)) *
        (Real.sqrt d * (3 : ℝ) ^ N * B) := by
        gcongr
    _ = Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) *
        (Real.sqrt d * Real.sqrt d) * W * B * (3 : ℝ) ^ N * Real.sqrt ((3 : ℝ) ^ (N * d)) *
        (M + ballVolumeConstant d * ((3 : ℝ) ^ N)⁻¹) * Real.sqrt a := by ring
    _ = _ := by rw [hdd]

end Package

end EinsteinFull.Homogenization
