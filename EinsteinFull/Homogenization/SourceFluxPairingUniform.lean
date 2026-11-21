import EinsteinFull.Homogenization.HighContrastHomogenizedBound
import EinsteinFull.Homogenization.SourceFluxCorrectorExistence

/-!
# Uniform pairing bounds for the fluxes of source correctors

Fix a package of the homogenization theorem of Armstrong, Kuusi and Loher for a law of Armstrong,
Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*. Almost
surely, every component of the source flux `a(e + ∇φ)` of a source corrector of a unit slope,
centered at the homogenized flux `ā e`, has a pairing bound at the scales above twice the
homogenization scale. Since the homogenized matrix is bounded, the amplitude of this bound and
the centering vector are bounded by constants depending only on `d`, `K` and the constants of the
theorem. A pairing bound persists when the scale and the amplitude increase.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open _root_.Homogenization hiding euclideanBall Vec Mat euclideanNorm
open _root_.Homogenization.HighContrast

variable {d : ℕ}

/-- A pairing bound persists when the scale and the amplitude increase. -/
theorem HasScalePairingBound.mono {F : Vec d → ℝ} {R₀ R₁ A A' κ : ℝ}
    (hF : HasScalePairingBound F R₀ A κ) (hR₀ : 0 < R₀) (hR : R₀ ≤ R₁) (hA : 0 ≤ A)
    (hAA : A ≤ A') (hκ : 0 ≤ κ) : HasScalePairingBound F R₁ A' κ := by
  intro ρ hρ η h1 h2 h3
  have hρ0 : 0 < ρ := lt_of_lt_of_le hR₀ (hR.trans hρ)
  have hR₁ : 0 < R₁ := lt_of_lt_of_le hR₀ hR
  have hA' : 0 ≤ A' := hA.trans hAA
  have hq : (ρ / R₀) ^ (-κ) ≤ (ρ / R₁) ^ (-κ) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hρ0 hR₁) (div_le_div_of_nonneg_left hρ0.le hR₀ hR)
      (by linarith)
  refine (hF ρ (hR.trans hρ) η h1 h2 h3).trans ?_
  gcongr

section Package

variable [NeZero d] {K : ℝ} {hK : 1 ≤ K} {P : Measure (Coefficient d K)} {κ C : ℝ}

/-- The amplitude of the flux pairing bound is controlled by a bound on the homogenized matrix. -/
theorem HighContrastCorrectorPackage.fluxAmplitude_le
    (pk : HighContrastCorrectorPackage hK P κ C) (hκ : 0 < κ) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) {Cab : ℝ}
    (hCab : 0 ≤ Cab)
    (habar : ∀ u w : Vec d, |vecDot (matVecMul pk.abar u) w| ≤
      Cab * Real.sqrt (vecNormSq u) * Real.sqrt (vecNormSq w)) (w : Vec d) :
    pk.fluxAmplitude w ≤ (K + Cab) * Real.sqrt (vecNormSq w) := by
  have hlow (v : Vec d) := (pk.vecNormSq_le_vecDot_symmPart_and_le hκ hC hb hbell v).1
  have hup (v : Vec d) := (pk.vecNormSq_le_vecDot_symmPart_and_le hκ hC hb hbell v).2
  have hS : (symmPart pk.abar).PosDef := posDef_symmPart_of_vecDot_pos pk.posDef
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  unfold HighContrastCorrectorPackage.fluxAmplitude
  have h1 : Real.sqrt (vecNormSq (matVecMul (matSqrt (symmPart pk.abar)) w)) ≤
      K * Real.sqrt (vecNormSq w) := by
    rw [vecNormSq_matVecMul_matSqrt_eq hS]
    calc Real.sqrt (vecDot w (matVecMul (symmPart pk.abar) w))
        ≤ Real.sqrt (K ^ 2 * vecNormSq w) := Real.sqrt_le_sqrt (hup w)
      _ = K * Real.sqrt (vecNormSq w) := by rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK0]
  have h2 : Real.sqrt (vecNormSq (matVecMul (matSqrt (symmPart pk.abar))⁻¹
      (matVecMul (matTranspose (skewPart pk.abar)) w))) ≤ Cab * Real.sqrt (vecNormSq w) := by
    refine (Real.sqrt_le_sqrt (vecNormSq_matVecMul_inv_matSqrt_le hlow hS _)).trans ?_
    rw [matTranspose_skewPart, neg_matVecMul]
    have hn : vecNormSq (-matVecMul (skewPart pk.abar) w) =
        vecNormSq (matVecMul (skewPart pk.abar) w) := by simp [vecNormSq, vecDot]
    rw [hn]
    exact sqrt_vecNormSq_skewPart_le hCab habar w
  linarith

end Package

/-- **Pairing bounds for the fluxes of source correctors at the homogenization scale.** -/
theorem HighContrastCorrectorPackage.ae_hasScalePairingBound_sourceFlux {K : ℝ} {hK : 1 ≤ K}
    {P : Measure (Coefficient d K)} {κ C : ℝ} (pk : HighContrastCorrectorPackage hK P κ C)
    (hP : LawHypotheses P) (hd : 2 ≤ d) (hκ : 0 < κ) (hC : 0 ≤ C) (e : Vec d)
    (φ : SourceCorrector P e) :
    ∀ᵐ a ∂P, toHighContrast hK a ∈ pk.Ωend ∧ ∀ k : Fin d, HasScalePairingBound
      (fun y => ((coefficientRepresentative a y).mulVec (e + φ.grad a y)) k -
        (matVecMul pk.abar e) k) (2 * pk.X (toHighContrast hK a))
      (pk.fluxAmplitude (unitVector k) *
        Real.sqrt ((2 * K) ^ d * (volume (euclideanBall d 1)).toReal) *
        max ((volume (euclideanBall d 1)).toReal ^ (-(1 : ℝ) / d)) 1 *
        (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)))) κ := by
  have hd0 : NeZero d := ⟨by omega⟩
  filter_upwards [ae_dilated_eq_highContrast hP hd hκ hC pk φ, φ.weak_gradient,
    φ.locally_square_integrable] with a ha hw hloc2
  obtain ⟨hb, -, hgrad⟩ := ha
  refine ⟨hb, fun k => ?_⟩
  have hbell := ae_isEllipticMatrix_toHighContrast hK a
  generalize hbdef : toHighContrast hK a = b at hb hgrad hbell ⊢
  have hX : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
  have hgm : Measurable (φ.grad a) :=
    φ.measurable_grad.comp (measurable_const.prodMk measurable_id)
  have hlocPhi : ∀ i, LocallyIntegrable (fun x => pk.gradPhi e b x i) volume := fun i =>
    (locallyIntegrable_dilatedGradient hw i).congr (hgrad.mono fun x hx => congrFun hx i)
  set F : Vec d → ℝ := fun y => ((coefficientRepresentative a y).mulVec (e + φ.grad a y)) k -
    (matVecMul pk.abar e) k with hF
  have hFmem : ∀ R : ℝ, MemLp F 2 (volume.restrict (ball 0 R)) :=
    memLp_sourceFlux hK a hgm (fun R hR => (hloc2 R hR).2) e _ k
  have hFloc : LocallyIntegrable F volume := locallyIntegrable_of_memLp_ball hFmem
  have hFG : ∀ᵐ x ∂(volume : Measure (Vec d)), F ((2 : ℝ) • x) =
      vecDot (matVecMul (b.1 x) (e + pk.gradPhi e b x) - matVecMul pk.abar e) (unitVector k) := by
    have h1 : ∀ᵐ x ∂(volume : Measure (Vec d)),
        coefficientRepresentative a ((2 : ℝ) • x) = a.field ((2 : ℝ) • x) :=
      (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) two_ne_zero).ae_eq_comp
        (coefficientRepresentative_ae_eq a)
    have h2 := toHighContrast_ae_eq hK a
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
  exact (pk.hasScalePairingBound_flux hκ hC hb hbell e (unitVector k) hlocPhi hint).of_dilation
    hX hFG

/-- **Uniform pairing bounds for the fluxes of source correctors.** The amplitude `A` and the
bound `C_ā` on the centering vector depend only on `d`, `K` and the constants of the
homogenization theorem. -/
theorem exists_uniform_sourceFlux_pairing (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (hK : 1 ≤ K) {κ C : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C) :
    ∃ A Cab : ℝ, 0 ≤ A ∧ 0 ≤ Cab ∧ ∀ (P : Measure (Coefficient d K))
      (pk : HighContrastCorrectorPackage hK P κ C), LawHypotheses P →
      ∀ e : Vec d, euclideanNorm e = 1 → ∀ φ : SourceCorrector P e,
        ∀ᵐ a ∂P, toHighContrast hK a ∈ pk.Ωend ∧ (∀ k : Fin d, |(matVecMul pk.abar e) k| ≤ Cab) ∧
          ∀ k : Fin d, HasScalePairingBound
            (fun y => ((coefficientRepresentative a y).mulVec (e + φ.grad a y)) k -
              (matVecMul pk.abar e) k) (2 * pk.X (toHighContrast hK a)) A κ := by
  have hd0 : NeZero d := ⟨by omega⟩
  obtain ⟨Cab, hCab, habar⟩ := exists_abs_vecDot_abar_le d K hK hκ hC
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  refine ⟨(K + Cab) * Real.sqrt ((2 * K) ^ d * (volume (euclideanBall d 1)).toReal) *
      max ((volume (euclideanBall d 1)).toReal ^ (-(1 : ℝ) / d)) 1 * (C * K), Cab,
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (le_max_of_le_right zero_le_one)) (mul_nonneg hC hK0), hCab, ?_⟩
  intro P pk hP e he φ
  have he1 : vecNormSq e = 1 := by
    have h : Real.sqrt (euclideanSq e) = 1 := he
    rwa [Real.sqrt_eq_one] at h
  have hunit : ∀ k : Fin d, vecNormSq (unitVector k : Vec d) = 1 := by
    intro k
    simp [vecNormSq, vecDot, unitVector, Pi.single_apply]
  filter_upwards [pk.ae_hasScalePairingBound_sourceFlux hP hd hκ hC e φ] with a ha
  obtain ⟨hb, hpair⟩ := ha
  have hbell := ae_isEllipticMatrix_toHighContrast hK a
  have hab := habar P pk hb hbell
  refine ⟨hb, fun k => ?_, fun k => ?_⟩
  · have h := hab e (unitVector k)
    rw [he1, hunit k, Real.sqrt_one, mul_one, mul_one] at h
    have hk : vecDot (matVecMul pk.abar e) (unitVector k) = (matVecMul pk.abar e) k := by
      simp [vecDot, unitVector, Pi.single_apply]
    rwa [hk] at h
  · have hX : 0 < 2 * pk.X (toHighContrast hK a) :=
      mul_pos two_pos (lt_of_lt_of_le one_pos (pk.one_le_X _))
    refine (hpair k).mono hX le_rfl (mul_nonneg (mul_nonneg (mul_nonneg
      (pk.fluxAmplitude_nonneg _) (Real.sqrt_nonneg _)) (le_max_of_le_right zero_le_one))
      (mul_nonneg hC (Real.sqrt_nonneg _))) ?_ hκ.le
    have hamp := pk.fluxAmplitude_le hκ hC hb hbell hCab hab (unitVector k)
    rw [hunit k, Real.sqrt_one, mul_one] at hamp
    have hq : Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) ≤ K := by
      have h := (pk.vecNormSq_le_vecDot_symmPart_and_le hκ hC hb hbell e).2
      rw [he1, mul_one] at h
      calc Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) ≤ Real.sqrt (K ^ 2) :=
            Real.sqrt_le_sqrt h
        _ = K := Real.sqrt_sq hK0
    have hs0 := Real.sqrt_nonneg ((2 * K) ^ d * (volume (euclideanBall d 1)).toReal)
    have hm0 : 0 ≤ max ((volume (euclideanBall d 1)).toReal ^ (-(1 : ℝ) / d)) 1 :=
      le_max_of_le_right zero_le_one
    have hf0 := pk.fluxAmplitude_nonneg (unitVector k)
    gcongr
