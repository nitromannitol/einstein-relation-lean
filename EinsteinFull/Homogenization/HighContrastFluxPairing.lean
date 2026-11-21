import EinsteinFull.Homogenization.GaussianTestPairing
import EinsteinFull.Homogenization.HighContrastSourceBounds
import EinsteinFull.Homogenization.HeatSelectedFluxPotential

/-!
# Pairing bounds for the fluxes of source correctors

On the event of the homogenization theorem of Armstrong, Kuusi and Loher, *Homogenization at a
polynomial scale in high contrast*, the corrector estimate bounds the normalized `H⁻¹(E_r)` norms
of `s̄^{1/2} ∇φ` and of `s̄^{-1/2}((a - k̄)(e + ∇φ) - s̄ e)` by `r (r/X)^(-κ)`. Since
`a(e + ∇φ) - ā e = ((a - k̄)(e + ∇φ) - s̄ e) + k̄ ∇φ`, every component of the flux defect
`a(e + ∇φ) - ā e` has a pairing bound at the scales above `X` in the sense of
`HasScalePairingBound`. A pairing bound is preserved by the dilation `x ↦ 2x`, which relates the
dilated law to a source law of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*; hence the components of the source flux
`a(e + ∇φ)` of a source corrector, centered at `ā e`, have pairing bounds at the scales above
`2X`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM

variable {d : ℕ}

section Dilation

theorem gradient_comp_two_smul {η : Vec d → ℝ} (hη : Differentiable ℝ η) (x : Vec d) :
    gradient (fun y => η ((2 : ℝ) • y)) x = (2 : ℝ) • gradient η ((2 : ℝ) • x) := by
  have hd := ((hη ((2 : ℝ) • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul (2 : ℝ))).congr_of_eventuallyEq
      (f₁ := fun y => η ((2 : ℝ) • y)) (Filter.Eventually.of_forall fun _ => rfl)
  funext l
  change fderiv ℝ (fun y => η ((2 : ℝ) • y)) x (unitVector l) = _
  rw [hd.fderiv]
  simp [gradient, coordinateDerivative]

theorem tsupport_comp_two_smul_subset {η : Vec d → ℝ} {ρ : ℝ} (hη : tsupport η ⊆ ball 0 ρ) :
    tsupport (fun x => η ((2 : ℝ) • x)) ⊆ ball 0 (ρ / 2) := by
  have hclosed : IsClosed ((fun x : Vec d => (2 : ℝ) • x) ⁻¹' tsupport η) :=
    (isClosed_tsupport η).preimage (continuous_const_smul (2 : ℝ))
  have hsub : tsupport (fun x => η ((2 : ℝ) • x)) ⊆
      (fun x : Vec d => (2 : ℝ) • x) ⁻¹' tsupport η :=
    closure_minimal (fun x hx => subset_tsupport η hx) hclosed
  intro x hx
  have h := hη (hsub hx)
  simp only [ball, sub_zero, Set.mem_ofPred_eq] at h ⊢
  rw [TimeChange.euclideanNorm_smul, abs_two] at h
  linarith

/-- **Pairing bounds are preserved by the dilation `x ↦ 2x`.** -/
theorem HasScalePairingBound.of_dilation {F G : Vec d → ℝ} {R₀ A κ : ℝ}
    (hG : HasScalePairingBound G R₀ A κ) (hR₀ : 0 < R₀)
    (hFG : ∀ᵐ x ∂(volume : Measure (Vec d)), F ((2 : ℝ) • x) = G x) :
    HasScalePairingBound F (2 * R₀) A κ := by
  intro ρ hρ η hη hηc hηρ
  have hρ0 : 0 < ρ := by linarith
  have hηd : Differentiable ℝ η := hη.differentiable (by simp)
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => (2 : ℝ) • x) := contDiff_id.const_smul 2
  have hη₂ : ContDiff ℝ (⊤ : ℕ∞) (fun x => η ((2 : ℝ) • x)) := hη.comp hlin
  have hη₂c : HasCompactSupport (fun x => η ((2 : ℝ) • x)) := hηc.comp_smul two_ne_zero
  have hpair := hG (ρ / 2) (by linarith) _ hη₂ hη₂c (tsupport_comp_two_smul_subset hηρ)
  have hfin : Module.finrank ℝ (Vec d) = d := Module.finrank_fin_fun ℝ
  have hcomp (f : Vec d → ℝ) : ∫ x, f ((2 : ℝ) • x) = ((2 : ℝ) ^ d)⁻¹ * ∫ y, f y := by
    rw [Measure.integral_comp_smul_of_nonneg volume f (2 : ℝ) (hR := by norm_num), hfin,
      smul_eq_mul]
  have hcv : ∫ y, η y * F y = (2 : ℝ) ^ d * ∫ x, η ((2 : ℝ) • x) * G x := by
    have h2 : ∫ x, η ((2 : ℝ) • x) * F ((2 : ℝ) • x) = ∫ x, η ((2 : ℝ) • x) * G x :=
      integral_congr_ae (hFG.mono fun x hx => by simp only [hx])
    rw [← h2, hcomp (fun y => η y * F y)]
    field_simp
  have hsq : ∫ x, η ((2 : ℝ) • x) ^ 2 = ((2 : ℝ) ^ d)⁻¹ * ∫ y, η y ^ 2 :=
    hcomp (fun y => η y ^ 2)
  have hgr : ∫ x, euclideanSq (gradient (fun y => η ((2 : ℝ) • y)) x) =
      4 * (((2 : ℝ) ^ d)⁻¹ * ∫ y, euclideanSq (gradient η y)) := by
    have hg : ∀ x, euclideanSq (gradient (fun y => η ((2 : ℝ) • y)) x) =
        4 * euclideanSq (gradient η ((2 : ℝ) • x)) := fun x => by
      rw [gradient_comp_two_smul hηd, Environment.AKMTestIntegralSupport.euclideanSq_smul]
      norm_num
    simp_rw [hg]
    rw [integral_const_mul, hcomp (fun y => euclideanSq (gradient η y))]
  set q := Real.sqrt ((2 : ℝ) ^ d) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hqq : q * q = (2 : ℝ) ^ d := Real.mul_self_sqrt (by positivity)
  have hq2 : (2 : ℝ) ^ ((d : ℝ) / 2) = q := by
    rw [hq, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hpow : (ρ / 2) ^ ((d : ℝ) / 2 + 1) = ρ ^ ((d : ℝ) / 2 + 1) / (q * 2) := by
    rw [Real.div_rpow hρ0.le (by norm_num), Real.rpow_add (by norm_num : (0 : ℝ) < 2) ((d : ℝ) / 2) 1,
      hq2, Real.rpow_one]
  have hsqrt : Real.sqrt ((ρ / 2)⁻¹ ^ 2 * (((2 : ℝ) ^ d)⁻¹ * ∫ y, η y ^ 2) +
      4 * (((2 : ℝ) ^ d)⁻¹ * ∫ y, euclideanSq (gradient η y))) =
      2 / q * Real.sqrt (ρ⁻¹ ^ 2 * (∫ y, η y ^ 2) + ∫ y, euclideanSq (gradient η y)) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 / q), ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [← hqq]
    field_simp
    ring
  have hbase : ρ / 2 / R₀ = ρ / (2 * R₀) := by ring
  rw [hcv, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ d)]
  calc (2 : ℝ) ^ d * |∫ x, η ((2 : ℝ) • x) * G x|
      ≤ (2 : ℝ) ^ d * (A * (ρ / 2) ^ ((d : ℝ) / 2 + 1) * (ρ / 2 / R₀) ^ (-κ) *
          Real.sqrt ((ρ / 2)⁻¹ ^ 2 * (∫ x, η ((2 : ℝ) • x) ^ 2) +
            ∫ x, euclideanSq (gradient (fun y => η ((2 : ℝ) • y)) x))) := by
        gcongr
    _ = A * ρ ^ ((d : ℝ) / 2 + 1) * (ρ / (2 * R₀)) ^ (-κ) *
          Real.sqrt (ρ⁻¹ ^ 2 * (∫ y, η y ^ 2) + ∫ y, euclideanSq (gradient η y)) := by
        rw [hsq, hgr, hsqrt, hpow, hbase, ← hqq]
        field_simp

end Dilation


section HighContrast

open _root_.Homogenization hiding euclideanBall Vec Mat euclideanNorm
open _root_.Homogenization.HighContrast

theorem eVolumeAverage_ofReal_le {V : Set (Vec d)} (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ⊤)
    {g : Vec d → ℝ} (hg : Integrable g volume) (hg0 : ∀ x, 0 ≤ g x) :
    eVolumeAverage V (fun x => ENNReal.ofReal (g x)) ≤
      ENNReal.ofReal ((∫ x, g x) / (volume V).toReal) := by
  unfold eVolumeAverage
  have hVreal : 0 < (volume V).toReal := ENNReal.toReal_pos hV0 hVtop
  rw [ENNReal.ofReal_div_of_pos hVreal, ENNReal.ofReal_toReal hVtop,
    ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall hg0)]
  exact ENNReal.div_le_div_right (setLIntegral_le_lintegral _ _) _

/-- The normalized test norm of `η w` for a smooth compactly supported `η`. -/
theorem h1NormSq_smul_le {V : Set (Vec d)} (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ⊤)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) (w : Vec d) :
    h1NormSq V (fun x => η x • w) ≤
      ENNReal.ofReal (vecNormSq w * ((volume V).toReal ^ (-(2 : ℝ) / d) * (∫ x, η x ^ 2) +
        ∫ x, euclideanSq (gradient η x)) / (volume V).toReal) := by
  have hdiff : Differentiable ℝ η := hη.differentiable (by simp)
  have hval (x : Vec d) : vecNormSq (η x • w) = vecNormSq w * η x ^ 2 := by
    simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hgrad (x : Vec d) : ∑ j, vecNormSq (smoothGrad (fun y => (η y • w) j) x) =
      vecNormSq w * euclideanSq (gradient η x) := by
    have hcomp (j : Fin d) : smoothGrad (fun y => (η y • w) j) x = w j • smoothGrad η x := by
      have : (fun y => (η y • w) j) = fun y => w j * η y := by
        funext y
        simp [smul_eq_mul, mul_comm]
      rw [this, smoothGrad_const_mul hdiff]
    simp only [hcomp]
    have hsg : smoothGrad η x = gradient η x := rfl
    simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, hsg, euclideanSq,
      dot]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hVreal : 0 < (volume V).toReal := ENNReal.toReal_pos hV0 hVtop
  have hA := eVolumeAverage_ofReal_le hV0 hVtop
    ((integrable_sq_of_hasCompactSupport hη.continuous hηc).const_mul (vecNormSq w))
    (fun x => mul_nonneg (vecNormSq_nonneg w) (sq_nonneg _))
  have hB := eVolumeAverage_ofReal_le hV0 hVtop
    ((integrable_euclideanSq_gradient hη hηc).const_mul (vecNormSq w))
    (fun x => mul_nonneg (vecNormSq_nonneg w) (vecNormSq_nonneg (gradient η x)))
  have hpow : volume V ^ (-(2 : ℝ) / d) =
      ENNReal.ofReal ((volume V).toReal ^ (-(2 : ℝ) / d)) := by
    rw [← ENNReal.ofReal_toReal hVtop, ENNReal.ofReal_rpow_of_pos hVreal,
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  have hI1 : 0 ≤ ∫ x, η x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hI2 : 0 ≤ ∫ x, euclideanSq (gradient η x) :=
    integral_nonneg fun x => vecNormSq_nonneg (gradient η x)
  unfold h1NormSq
  simp_rw [hval, hgrad]
  rw [hpow]
  calc ENNReal.ofReal ((volume V).toReal ^ (-(2 : ℝ) / d)) *
        eVolumeAverage V (fun x => ENNReal.ofReal (vecNormSq w * η x ^ 2)) +
      eVolumeAverage V (fun x => ENNReal.ofReal (vecNormSq w * euclideanSq (gradient η x)))
      ≤ ENNReal.ofReal ((volume V).toReal ^ (-(2 : ℝ) / d)) *
          ENNReal.ofReal ((∫ x, vecNormSq w * η x ^ 2) / (volume V).toReal) +
        ENNReal.ofReal ((∫ x, vecNormSq w * euclideanSq (gradient η x)) / (volume V).toReal) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hVreal.le _), ← ENNReal.ofReal_add
          (mul_nonneg (Real.rpow_nonneg hVreal.le _)
            (div_nonneg (by rw [integral_const_mul]; exact mul_nonneg (vecNormSq_nonneg w) hI1)
              hVreal.le))
          (div_nonneg (by rw [integral_const_mul]; exact mul_nonneg (vecNormSq_nonneg w) hI2)
            hVreal.le)]
        congr 1
        rw [integral_const_mul, integral_const_mul]
        ring

/-- **Pairing of a smooth test with a field of small negative-one norm.** -/
theorem abs_integral_mul_vecDot_le_of_negOneNorm_smooth {V : Set (Vec d)} (hV0 : volume V ≠ 0)
    (hVtop : volume V ≠ ⊤) {G : Vec d → Vec d} {L : Mat d} {N : ℝ} (hN : 0 ≤ N)
    (hneg : negOneNorm V (fun x => matVecMul L (G x)) ≤ ENNReal.ofReal N)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηV : tsupport η ⊆ V) (w : Vec d)
    (hint : Integrable (fun x => η x * vecDot (G x) (matVecMul (matTranspose L) w)) volume) :
    |∫ x, η x * vecDot (G x) (matVecMul (matTranspose L) w)| ≤
      Real.sqrt (vecNormSq w) * Real.sqrt ((volume V).toReal) *
        Real.sqrt ((volume V).toReal ^ (-(2 : ℝ) / d) * (∫ x, η x ^ 2) +
          ∫ x, euclideanSq (gradient η x)) * N := by
  set F : Vec d → Vec d := fun x => matVecMul L (G x)
  set ψ : Vec d → Vec d := fun x => η x • w
  have htest : IsLocalVecTest V ψ :=
    ⟨hη.smul contDiff_const, hηc.smul_right,
      (tsupport_smul_subset_left η (fun _ => w)).trans hηV⟩
  have hpt (x : Vec d) : vecDot (F x) (ψ x) =
      η x * vecDot (G x) (matVecMul (matTranspose L) w) := by
    simp only [F, ψ]
    rw [vecDot_matVecMul_transpose]
    simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hintV : IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume := by
    simp_rw [hpt]
    exact hint.integrableOn
  set Q := (volume V).toReal ^ (-(2 : ℝ) / d) * (∫ x, η x ^ 2) +
    ∫ x, euclideanSq (gradient η x) with hQ
  have hVreal : 0 < (volume V).toReal := ENNReal.toReal_pos hV0 hVtop
  have hQ0 : 0 ≤ Q := add_nonneg (mul_nonneg (Real.rpow_nonneg hVreal.le _)
    (integral_nonneg fun x => sq_nonneg _)) (integral_nonneg fun x => vecNormSq_nonneg _)
  have hnorm := h1NormSq_smul_le hV0 hVtop hη hηc w
  have hK0 : 0 ≤ vecNormSq w * Q / (volume V).toReal :=
    div_nonneg (mul_nonneg (vecNormSq_nonneg w) hQ0) hVreal.le
  have hmain := abs_setIntegral_le_of_negOneNorm_le' hV0 hVtop htest hintV hK0 hN hnorm hneg
  have hzero : ∫ x, η x * vecDot (G x) (matVecMul (matTranspose L) w) =
      ∫ x in V, vecDot (F x) (ψ x) := by
    simp_rw [hpt]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    have hxη : x ∉ tsupport η := fun h => hx (hηV h)
    simp [image_eq_zero_of_notMem_tsupport hxη]
  rw [hzero]
  refine hmain.trans (le_of_eq ?_)
  rw [Real.sqrt_div (mul_nonneg (vecNormSq_nonneg w) hQ0), Real.sqrt_mul (vecNormSq_nonneg w)]
  have hdiv : (volume V).toReal / Real.sqrt (volume V).toReal = Real.sqrt (volume V).toReal :=
    Real.div_sqrt
  calc (volume V).toReal * (Real.sqrt (vecNormSq w) * Real.sqrt Q /
        Real.sqrt (volume V).toReal * N)
      = (volume V).toReal / Real.sqrt (volume V).toReal *
          (Real.sqrt (vecNormSq w) * Real.sqrt Q * N) := by ring
    _ = _ := by rw [hdiv]; ring

theorem symmPart_add_skewPart (A : Mat d) : symmPart A + skewPart A = A := by
  ext i j
  simp only [symmPart, skewPart, Matrix.add_apply]
  ring

/-- The flux defect splits into the defect controlled by the corrector estimate and the skew
part of the homogenized matrix applied to the corrector gradient. -/
theorem flux_decomposition (B abar : Mat d) (e v : Vec d) :
    matVecMul B (e + v) - matVecMul abar e =
      (matVecMul (B - skewPart abar) (e + v) - matVecMul (symmPart abar) e) +
        matVecMul (skewPart abar) v := by
  funext i
  have hij : ∀ j, abar i j = symmPart abar i j + skewPart abar i j := fun j => by
    simp only [symmPart, skewPart]
    ring
  simp only [matVecMul, Pi.sub_apply, Pi.add_apply, Matrix.sub_apply, hij]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end HighContrast


section Package

open _root_.Homogenization hiding euclideanBall Vec Mat euclideanNorm
open _root_.Homogenization.HighContrast

variable {K : ℝ} {hK : 1 ≤ K}
  {P : Measure (EinsteinRelation.Environment.AKMTestIntegralSupport.Coefficient d K)} {κ C : ℝ}

/-- The amplitude of the pairing bound of the flux defect tested in the direction `w`. -/
noncomputable def HighContrastCorrectorPackage.fluxAmplitude
    (pk : HighContrastCorrectorPackage hK P κ C) (w : Vec d) : ℝ :=
  Real.sqrt (vecNormSq (matVecMul (matSqrt (symmPart pk.abar)) w)) +
    Real.sqrt (vecNormSq (matVecMul (matSqrt (symmPart pk.abar))⁻¹
      (matVecMul (matTranspose (skewPart pk.abar)) w)))

theorem HighContrastCorrectorPackage.fluxAmplitude_nonneg
    (pk : HighContrastCorrectorPackage hK P κ C) (w : Vec d) : 0 ≤ pk.fluxAmplitude w :=
  add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- **Pairing of a smooth test with the flux defect.** -/
theorem HighContrastCorrectorPackage.abs_integral_mul_flux_le
    (pk : HighContrastCorrectorPackage hK P κ C) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend) (e w : Vec d) {r : ℝ} (hr : 0 < r) (hrX : pk.X b ≤ r)
    (hloc : ∀ i, LocallyIntegrable (fun x => pk.gradPhi e b x i) volume)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηr : tsupport η ⊆ ellipsoid pk.abar r)
    (hint : Integrable (fun x => η x * vecDot (matVecMul (b.1 x) (e + pk.gradPhi e b x) -
      matVecMul pk.abar e) w) volume) :
    |∫ x, η x * vecDot (matVecMul (b.1 x) (e + pk.gradPhi e b x) - matVecMul pk.abar e) w| ≤
      pk.fluxAmplitude w * Real.sqrt ((volume (ellipsoid pk.abar r)).toReal) *
        Real.sqrt ((volume (ellipsoid pk.abar r)).toReal ^ (-(2 : ℝ) / d) * (∫ x, η x ^ 2) +
          ∫ x, euclideanSq (gradient η x)) *
        (r * (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) *
          (r / pk.X b) ^ (-κ))) := by
  set S := symmPart pk.abar with hSdef
  set T := matSqrt S with hT
  set k := skewPart pk.abar with hk
  have hSpd : S.PosDef := posDef_symmPart_of_vecDot_pos pk.posDef
  set V := ellipsoid pk.abar r with hV
  have hVtop : volume V ≠ ⊤ := (volume_ellipsoid_lt_top hSpd r).ne
  have hV0 : volume V ≠ 0 := (volume_ellipsoid_pos pk.abar hr).ne'
  have hX : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
  set N := r * (C * Real.sqrt (vecDot e (matVecMul S e)) * (r / pk.X b) ^ (-κ)) with hN
  have hN0 : 0 ≤ N := mul_nonneg hr.le (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _))
    (Real.rpow_nonneg (div_nonneg hr.le hX.le) _))
  have hTt : matTranspose T = T := isSymm_matSqrt _
  have hTinvt : matTranspose T⁻¹ = T⁻¹ := by
    unfold matTranspose
    rw [Matrix.transpose_nonsing_inv]
    exact congrArg _ hTt
  set w₁ := matVecMul T w with hw₁
  set w₂ := matVecMul T⁻¹ (matVecMul (matTranspose k) w) with hw₂
  have hw₁' : matVecMul (matTranspose T⁻¹) w₁ = w := by
    rw [hTinvt, hw₁, matVecMul_mul, Matrix.nonsing_inv_mul _ (isUnit_det_matSqrt hSpd),
      _root_.Homogenization.matVecMul_one]
  have hw₂' : matVecMul (matTranspose T) w₂ = matVecMul (matTranspose k) w := by
    rw [hTt, hw₂, matVecMul_mul, Matrix.mul_nonsing_inv _ (isUnit_det_matSqrt hSpd),
      _root_.Homogenization.matVecMul_one]
  set G₁ : Vec d → Vec d := fun x => matVecMul (b.1 x - k) (e + pk.gradPhi e b x) -
    matVecMul S e with hG₁
  have hsplit (x : Vec d) : η x * vecDot (matVecMul (b.1 x) (e + pk.gradPhi e b x) -
      matVecMul pk.abar e) w =
      η x * vecDot (G₁ x) (matVecMul (matTranspose T⁻¹) w₁) +
        η x * vecDot (pk.gradPhi e b x) (matVecMul (matTranspose T) w₂) := by
    rw [hw₁', hw₂', vecDot_matVecMul_transpose, flux_decomposition, vecDot_add_left]
    ring
  have hint2 : Integrable (fun x => η x * vecDot (pk.gradPhi e b x)
      (matVecMul (matTranspose T) w₂)) volume := by
    simp only [vecDot, Finset.mul_sum]
    refine integrable_finsetSum _ fun i _ => ?_
    have := ((hloc i).integrable_smul_left_of_hasCompactSupport hη.continuous hηc)
    have h2 := this.mul_const ((matVecMul (matTranspose T) w₂) i)
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul]
    ring
  have hint1 : Integrable (fun x => η x * vecDot (G₁ x) (matVecMul (matTranspose T⁻¹) w₁))
      volume := by
    refine (hint.sub hint2).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [hsplit x]
    ring
  have h1 := abs_integral_mul_vecDot_le_of_negOneNorm_smooth hV0 hVtop hN0
    (pk.negOneNorm_flux_le hb e hr hrX) hη hηc hηr w₁ hint1
  have h2 := abs_integral_mul_vecDot_le_of_negOneNorm_smooth hV0 hVtop hN0
    (pk.negOneNorm_gradPhi_le hb e hr hrX) hη hηc hηr w₂ hint2
  have heq : ∫ x, η x * vecDot (matVecMul (b.1 x) (e + pk.gradPhi e b x) -
      matVecMul pk.abar e) w =
      (∫ x, η x * vecDot (G₁ x) (matVecMul (matTranspose T⁻¹) w₁)) +
        ∫ x, η x * vecDot (pk.gradPhi e b x) (matVecMul (matTranspose T) w₂) := by
    rw [← integral_add hint1 hint2]
    exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
  rw [heq]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  unfold HighContrastCorrectorPackage.fluxAmplitude
  rw [← hT, ← hk, ← hw₁, ← hw₂]
  ring

/-- **The flux defect has a pairing bound at the scales above the homogenization scale.** -/
theorem HighContrastCorrectorPackage.hasScalePairingBound_flux [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) (hκ : 0 < κ) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e w : Vec d)
    (hloc : ∀ i, LocallyIntegrable (fun x => pk.gradPhi e b x i) volume)
    (hint : ∀ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      Integrable (fun x => η x * vecDot (matVecMul (b.1 x) (e + pk.gradPhi e b x) -
        matVecMul pk.abar e) w) volume) :
    HasScalePairingBound (fun x => vecDot (matVecMul (b.1 x) (e + pk.gradPhi e b x) -
        matVecMul pk.abar e) w) (pk.X b)
      (pk.fluxAmplitude w * Real.sqrt ((2 * K) ^ d * (volume (euclideanBall d 1)).toReal) *
        max ((volume (euclideanBall d 1)).toReal ^ (-(1 : ℝ) / d)) 1 *
        (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)))) κ := by
  intro ρ hρ η hη hηc hηρ
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hX : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
  have hρ0 : 0 < ρ := lt_of_lt_of_le hX hρ
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hSpd : (symmPart pk.abar).PosDef := posDef_symmPart_of_vecDot_pos pk.posDef
  have hlow (v : Vec d) := (pk.vecNormSq_le_vecDot_symmPart_and_le hκ hC hb hbell v).1
  have hup (v : Vec d) := (pk.vecNormSq_le_vecDot_symmPart_and_le hκ hC hb hbell v).2
  have hηE : tsupport η ⊆ ellipsoid pk.abar ρ := by
    refine hηρ.trans ?_
    rw [ball_zero_eq_euclideanBall hρ0]
    exact euclideanBallAt_zero_subset_ellipsoid _ _
  have h := pk.abs_integral_mul_flux_le hC hb e w hρ0 hρ hloc hη hηc hηE (hint η hη hηc)
  set ω := (volume (euclideanBall d 1)).toReal with hω
  have hω0 : 0 < ω :=
    ENNReal.toReal_pos (volume_euclideanBall_pos' one_pos).ne' (volume_euclideanBall_ne_top' 1)
  set VE := (volume (ellipsoid pk.abar ρ)).toReal with hVE
  have hBρ : (volume (euclideanBall d ρ)).toReal ≤ VE :=
    ENNReal.toReal_mono (volume_ellipsoid_lt_top hSpd ρ).ne
      (measure_mono (euclideanBallAt_zero_subset_ellipsoid pk.abar ρ))
  have hBρ0 : 0 < (volume (euclideanBall d ρ)).toReal :=
    ENNReal.toReal_pos (volume_euclideanBall_pos' hρ0).ne' (volume_euclideanBall_ne_top' ρ)
  have hVE0 : 0 < VE := lt_of_lt_of_le hBρ0 hBρ
  have hVEle : VE ≤ (2 * K) ^ d * ω * ρ ^ d := by
    have hE1 : (volume (ellipsoid pk.abar 1)).toReal ≤ (2 * K) ^ d * ω := by
      have h1 : (volume (ellipsoid pk.abar 1)).toReal ≤
          (volume (euclideanBall d (2 * K))).toReal :=
        ENNReal.toReal_mono (volume_euclideanBall_ne_top' _)
          (measure_mono (ellipsoid_one_subset_euclideanBall hK hlow hup hSpd))
      rwa [volume_euclideanBall_toReal (by positivity)] at h1
    rw [hVE, volume_ellipsoid_toReal pk.abar hρ0]
    calc ρ ^ d * (volume (ellipsoid pk.abar 1)).toReal ≤ ρ ^ d * ((2 * K) ^ d * ω) := by
          gcongr
      _ = (2 * K) ^ d * ω * ρ ^ d := by ring
  have hrpow : VE ^ (-(2 : ℝ) / d) ≤ ω ^ (-(2 : ℝ) / d) / ρ ^ 2 := by
    rw [← volume_euclideanBall_toReal_rpow hρ0 hd]
    exact Real.rpow_le_rpow_of_nonpos hBρ0 hBρ
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg d))
  set M := max (ω ^ (-(1 : ℝ) / d)) 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hωM : ω ^ (-(2 : ℝ) / d) ≤ M ^ 2 := by
    have h1 : ω ^ (-(2 : ℝ) / d) = (ω ^ (-(1 : ℝ) / d)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hω0.le]
      congr 1
      push_cast
      ring
    rw [h1]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hω0.le _) (le_max_left _ _) 2
  set X := ∫ x, η x ^ 2 with hXdef
  set Y := ∫ x, euclideanSq (gradient η x) with hYdef
  have hX0 : 0 ≤ X := integral_nonneg fun x => sq_nonneg _
  have hY0 : 0 ≤ Y := integral_nonneg fun x => vecNormSq_nonneg (gradient η x)
  have hsq1 : Real.sqrt (VE ^ (-(2 : ℝ) / d) * X + Y) ≤ M * Real.sqrt (ρ⁻¹ ^ 2 * X + Y) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ M), ← Real.sqrt_mul (sq_nonneg M)]
    refine Real.sqrt_le_sqrt ?_
    have hρ2 : ρ⁻¹ ^ 2 = 1 / ρ ^ 2 := by rw [inv_pow, one_div]
    have e1 : VE ^ (-(2 : ℝ) / d) * X ≤ M ^ 2 * (ρ⁻¹ ^ 2 * X) := by
      calc VE ^ (-(2 : ℝ) / d) * X ≤ ω ^ (-(2 : ℝ) / d) / ρ ^ 2 * X := by gcongr
        _ ≤ M ^ 2 / ρ ^ 2 * X := by gcongr
        _ = M ^ 2 * (ρ⁻¹ ^ 2 * X) := by rw [hρ2]; ring
    have e2 : Y ≤ M ^ 2 * Y := le_mul_of_one_le_left hY0 (one_le_pow₀ hM1)
    nlinarith
  have hsq2 : Real.sqrt VE ≤ Real.sqrt ((2 * K) ^ d * ω) * ρ ^ ((d : ℝ) / 2) := by
    have hρd : Real.sqrt (ρ ^ d) = ρ ^ ((d : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]
      congr 1
      ring
    rw [← hρd, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hVEle
  have hρpow : ρ ^ ((d : ℝ) / 2) * ρ = ρ ^ ((d : ℝ) / 2 + 1) := by
    rw [Real.rpow_add hρ0, Real.rpow_one]
  have hamp := pk.fluxAmplitude_nonneg w
  have hcs : 0 ≤ C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) :=
    mul_nonneg hC (Real.sqrt_nonneg _)
  have hrX : 0 ≤ (ρ / pk.X b) ^ (-κ) := Real.rpow_nonneg (div_nonneg hρ0.le hX.le) _
  refine h.trans ?_
  calc pk.fluxAmplitude w * Real.sqrt VE * Real.sqrt (VE ^ (-(2 : ℝ) / d) * X + Y) *
        (ρ * (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) * (ρ / pk.X b) ^ (-κ)))
      ≤ pk.fluxAmplitude w * (Real.sqrt ((2 * K) ^ d * ω) * ρ ^ ((d : ℝ) / 2)) *
        (M * Real.sqrt (ρ⁻¹ ^ 2 * X + Y)) *
        (ρ * (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) *
          (ρ / pk.X b) ^ (-κ))) := by
        gcongr
    _ = pk.fluxAmplitude w * Real.sqrt ((2 * K) ^ d * ω) * M *
          (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e))) *
          (ρ ^ ((d : ℝ) / 2) * ρ) * (ρ / pk.X b) ^ (-κ) * Real.sqrt (ρ⁻¹ ^ 2 * X + Y) := by
        ring
    _ = _ := by rw [hρpow]

end Package


section Source

open EinsteinRelation.Environment.AKMTestIntegralSupport
open _root_.Homogenization hiding euclideanBall Vec Mat euclideanNorm
open _root_.Homogenization.HighContrast

variable {K : ℝ}

theorem mulVec_eq_matVecMul (M : Mat d) (v : Vec d) : M.mulVec v = matVecMul M v := rfl

theorem euclideanNorm_le_sqrt_mul_norm (v : Vec d) : euclideanNorm v ≤ Real.sqrt d * ‖v‖ :=
  euclideanNorm_le_sqrt_mul_of_abs_le fun l => by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm v l

theorem abs_mulVec_apply_le (hK : 1 ≤ K) (a : Coefficient d K) (y v : Vec d) (k : Fin d) :
    |((a.field y).mulVec v) k| ≤ K * euclideanNorm v := by
  have h := vecNormSq_matVecMul_le_of_isEllipticMatrix (source_isEllipticMatrix a hK le_rfl y) v
  refine (abs_apply_le_euclideanNorm ((a.field y).mulVec v) k).trans ?_
  have hK0 : 0 ≤ K := by linarith
  have h2 : Real.sqrt (euclideanSq ((a.field y).mulVec v)) ≤ Real.sqrt (K ^ 2 * euclideanSq v) :=
    Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK0] at h2
  exact h2

theorem measurable_coefficientRepresentative_apply (i j : Fin d) :
    Measurable (fun p : Coefficient d K × Vec d => coefficientRepresentative p.1 p.2 i j) := by
  have hm := measurable_coefficientRepresentative (d := d) (K := K)
  change @Measurable _ (Fin d → Fin d → ℝ) _ (borel _) _ at hm
  rw [← (Pi.borelSpace (X := fun _ : Fin d => Fin d → ℝ)).measurable_eq] at hm
  exact (measurable_pi_iff.mp (measurable_pi_iff.mp hm i)) j

theorem measurable_sourceFlux (a : Coefficient d K) {g : Vec d → Vec d} (hgm : Measurable g)
    (e c : Vec d) (k : Fin d) :
    Measurable (fun y => ((coefficientRepresentative a y).mulVec (e + g y)) k - c k) := by
  have hrep (i j : Fin d) : Measurable (fun y => coefficientRepresentative a y i j) :=
    Measurable.of_uncurry_left (f := fun a y => coefficientRepresentative a y i j)
      (measurable_coefficientRepresentative_apply i j)
  have hfun : (fun y => ((coefficientRepresentative a y).mulVec (e + g y)) k - c k) =
      fun y => (∑ j, coefficientRepresentative a y k j * (e + g y) j) - c k := rfl
  rw [hfun]
  refine (Finset.measurable_sum _ fun j _ => ?_).sub_const _
  exact (hrep k j).mul ((measurable_pi_apply j).comp (measurable_const.add hgm))

theorem abs_sourceFlux_le (hK : 1 ≤ K) (a : Coefficient d K) (y : Vec d) (e v c : Vec d)
    (k : Fin d) :
    |((a.field y).mulVec (e + v)) k - c k| ≤
      K * (euclideanNorm e + Real.sqrt d * ‖v‖) + |c k| := by
  have h1 := abs_mulVec_apply_le hK a y (e + v) k
  have h2 : euclideanNorm (e + v) ≤ euclideanNorm e + Real.sqrt d * ‖v‖ :=
    (TimeChange.euclideanNorm_add_le _ _).trans
      (add_le_add le_rfl (euclideanNorm_le_sqrt_mul_norm v))
  have hK0 : 0 ≤ K := by linarith
  have h3 : K * euclideanNorm (e + v) ≤ K * (euclideanNorm e + Real.sqrt d * ‖v‖) :=
    mul_le_mul_of_nonneg_left h2 hK0
  linarith [abs_sub ((a.field y).mulVec (e + v) k) (c k)]

/-- The components of the source flux with a locally square-integrable gradient are locally
square integrable. -/
theorem memLp_sourceFlux (hK : 1 ≤ K) (a : Coefficient d K) {g : Vec d → Vec d}
    (hgm : Measurable g) (hg : ∀ R : ℝ, 0 < R → MemLp g 2 (volume.restrict (ball 0 R)))
    (e c : Vec d) (k : Fin d) (R : ℝ) :
    MemLp (fun y => ((coefficientRepresentative a y).mulVec (e + g y)) k - c k) 2
      (volume.restrict (ball 0 R)) := by
  have hR1 : ball (0 : Vec d) R ⊆ ball 0 (max R 1) := ball_subset_ball_of_le (le_max_left _ _)
  refine MemLp.mono_measure (Measure.restrict_mono hR1 le_rfl) ?_
  have hR' : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfin := isFiniteMeasure_restrict_ball (d := d) (max R 1)
  have h1 : MemLp (fun y => ‖g y‖) 2 (volume.restrict (ball 0 (max R 1))) := (hg _ hR').norm
  have h2 : MemLp (fun y => euclideanNorm e + Real.sqrt d * ‖g y‖) 2
      (volume.restrict (ball 0 (max R 1))) :=
    (memLp_const (euclideanNorm e)).add (h1.const_mul (Real.sqrt d))
  have h3 : MemLp (fun y => K * (euclideanNorm e + Real.sqrt d * ‖g y‖) + |c k|) 2
      (volume.restrict (ball 0 (max R 1))) := (h2.const_mul K).add (memLp_const |c k|)
  refine h3.of_le (measurable_sourceFlux a hgm e c k).aestronglyMeasurable ?_
  have hae := ae_restrict_of_ae (μ := volume) (s := ball 0 (max R 1))
    (coefficientRepresentative_ae_eq a)
  filter_upwards [hae] with y hy
  have hK0 : 0 ≤ K := by linarith
  have hpos : 0 ≤ K * (euclideanNorm e + Real.sqrt d * ‖g y‖) + |c k| :=
    add_nonneg (mul_nonneg hK0 (add_nonneg (euclideanNorm_nonneg e)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))) (abs_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  have hy' : coefficientRepresentative a y = a.field y := hy
  simp only [hy']
  exact abs_sourceFlux_le hK a y e (g y) c k

/-- **Pairing bounds for the fluxes of source correctors.** There is `κ > 0` depending only on
the dimension such that for every law, slope `e` and source corrector `φ`, almost surely there
are a scale `R₀ > 0` and a vector `c` for which every component of `a(e + ∇φ) - c` has a
pairing bound at the scales above `R₀` with decay exponent `κ`. -/
theorem exists_hasScalePairingBound_sourceFlux (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (hK : 1 < K) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
      ∀ (e : Vec d) (φ : SourceCorrector P e), ∀ᵐ a ∂P, ∃ (R₀ : ℝ) (c : Vec d), 0 < R₀ ∧
        ∀ k : Fin d, ∃ A : ℝ, 0 ≤ A ∧ HasScalePairingBound
          (fun y => ((coefficientRepresentative a y).mulVec (e + φ.grad a y)) k - c k) R₀ A κ := by
  have hd0 : NeZero d := ⟨by omega⟩
  have hK1 : 1 ≤ K := hK.le
  obtain ⟨κ, C₀, hκ, hC₀, hpk⟩ := exists_highContrastCorrectorPackage d hd
  refine ⟨κ, hκ, fun P hP e φ => ?_⟩
  obtain ⟨pk⟩ := hpk K hK1 P hP
  filter_upwards [ae_dilated_eq_highContrast hP hd hκ hC₀.le pk φ, φ.weak_gradient,
    φ.locally_square_integrable] with a ha hw hloc2
  obtain ⟨hb, -, hgrad⟩ := ha
  have hbell := ae_isEllipticMatrix_toHighContrast hK1 a
  generalize hbdef : toHighContrast hK1 a = b at hb hgrad hbell
  have hX : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
  have hgm : Measurable (φ.grad a) :=
    φ.measurable_grad.comp (measurable_const.prodMk measurable_id)
  have hlocPhi : ∀ i, LocallyIntegrable (fun x => pk.gradPhi e b x i) volume := fun i =>
    (locallyIntegrable_dilatedGradient hw i).congr (hgrad.mono fun x hx => congrFun hx i)
  refine ⟨2 * pk.X b, matVecMul pk.abar e, by positivity, fun k => ?_⟩
  set F : Vec d → ℝ := fun y => ((coefficientRepresentative a y).mulVec (e + φ.grad a y)) k -
    (matVecMul pk.abar e) k with hF
  have hFmem : ∀ R : ℝ, MemLp F 2 (volume.restrict (ball 0 R)) :=
    memLp_sourceFlux hK1 a hgm (fun R hR => (hloc2 R hR).2) e _ k
  have hFloc : LocallyIntegrable F volume := locallyIntegrable_of_memLp_ball hFmem
  have hFG : ∀ᵐ x ∂(volume : Measure (Vec d)), F ((2 : ℝ) • x) =
      vecDot (matVecMul (b.1 x) (e + pk.gradPhi e b x) - matVecMul pk.abar e) (unitVector k) := by
    have h1 : ∀ᵐ x ∂(volume : Measure (Vec d)),
        coefficientRepresentative a ((2 : ℝ) • x) = a.field ((2 : ℝ) • x) :=
      (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) two_ne_zero).ae_eq_comp
        (coefficientRepresentative_ae_eq a)
    have h2 := toHighContrast_ae_eq hK1 a
    rw [hbdef] at h2
    filter_upwards [h1, h2, hgrad] with x hx1 hx2 hx3
    have hx2' : b.1 x = a.field ((2 : ℝ) • x) := hx2
    simp only [hF]
    rw [hx1, hx2', ← hx3]
    simp [vecDot, unitVector, Pi.single_apply, dilatedGradient, mulVec_eq_matVecMul]
  have hint : ∀ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      Integrable (fun x => η x * vecDot (matVecMul (b.1 x) (e + pk.gradPhi e b x) -
        matVecMul pk.abar e) (unitVector k)) volume := by
    intro η hη hηc
    have hη2 : Continuous (fun y => η ((2 : ℝ)⁻¹ • y)) :=
      hη.continuous.comp (continuous_const_smul _)
    have hη2c : HasCompactSupport (fun y => η ((2 : ℝ)⁻¹ • y)) :=
      hηc.comp_smul (inv_ne_zero two_ne_zero)
    have h1 : Integrable (fun y => η ((2 : ℝ)⁻¹ • y) * F y) volume := by
      have := hFloc.integrable_smul_left_of_hasCompactSupport hη2 hη2c
      simpa [smul_eq_mul] using this
    have h2 := h1.comp_smul (two_ne_zero : (2 : ℝ) ≠ 0)
    refine h2.congr (hFG.mono fun x hx => ?_)
    simp only [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_smul]
    rw [hx]
  have hmain := (pk.hasScalePairingBound_flux hκ hC₀.le hb hbell e (unitVector k) hlocPhi
    hint).of_dilation hX hFG
  exact ⟨_, mul_nonneg (mul_nonneg (mul_nonneg (pk.fluxAmplitude_nonneg _) (Real.sqrt_nonneg _))
    (le_max_of_le_right zero_le_one)) (mul_nonneg hC₀.le (Real.sqrt_nonneg _)), hmain⟩

end Source

end EinsteinFull.Homogenization
