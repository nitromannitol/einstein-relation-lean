import EinsteinFull.Homogenization.SourceFluxPotentialIdentification
import EinsteinFull.Homogenization.SourceFluxPairingUniform
import EinsteinFull.External.Draft.AKMSublinearCorrectorsV2

/-!
# Sublinearity of the scalar and flux correctors of source correctors

This module proves the statement `akmSublinearCorrectorsStmtV2`: the oscillation and local
gradient bounds of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Lemma 3.17, (3.85)–(3.86), for source correctors, together with the
existence of the flux corrector (Lemma 6.1) and the oscillation bound (6.13) of Proposition 6.2
for every flux corrector, above one random radius with stretched-exponential moments.

The radius is `X = (B X_HC)^p` with `p = 2d/(d+s)`, where `X_HC` is the homogenization scale of
the theorem of Armstrong, Kuusi and Loher, *Homogenization at a polynomial scale in high
contrast*, and `B` is a constant. Above `B X_HC` the corrector has bounded energy and
oscillation `r^(1-θ) (B X_HC)^θ`, and the flux potential has oscillation
`r (r/(B X_HC))^(-ϑ)`, from the energy and uniform pairing bounds of the flux. For `r ≥ X` the
factor `X_HC ≤ r^(1/p)` turns both into powers `r^(1 - β(d-s))`, and the tail of `X_HC` gives the
stretched-exponential moment of order `s`.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport
  EinsteinRelation.External.AKM
open EinsteinFull.External.Source.AKM
open _root_.Homogenization hiding euclideanBall Vec Mat euclideanNorm
open _root_.Homogenization.HighContrast

variable {d : ℕ}

/-- **Energy and oscillation of source correctors above a multiple of the homogenization
scale.** -/
theorem exists_sourceCorrector_scale_bounds (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (hK : 1 ≤ K)
    {κ C₀ : ℝ} (hκ : 0 < κ) (hC₀ : 0 ≤ C₀) :
    ∃ (Cφ θ : ℝ) (n₁ : ℕ), 0 ≤ Cφ ∧ 0 < θ ∧ θ ≤ 1 ∧ ∀ (P : Measure (Coefficient d K))
      (pk : HighContrastCorrectorPackage hK P κ C₀), LawHypotheses P →
      ∀ e : Vec d, euclideanNorm e = 1 → ∀ φ : SourceCorrector P e, ∀ᵐ a ∂P, ∀ r : ℝ,
        (3 : ℝ) ^ (n₁ + 1) * pk.X (toHighContrast hK a) ≤ r →
        Real.sqrt (⨍ x in ball 0 r,
            |φ.potential a x - (⨍ y in ball 0 r, φ.potential a y)| ^ 2) ≤
          Cφ * r ^ (1 - θ) * ((3 : ℝ) ^ (n₁ + 1) * pk.X (toHighContrast hK a)) ^ θ ∧
        Real.sqrt (⨍ x in ball 0 r, euclideanSq (φ.grad a x)) ≤ Cφ := by
  have hd0 : NeZero d := ⟨by omega⟩
  obtain ⟨A, θ, n₁, hA, hθ, hq⟩ := exists_highContrast_quantitative_bounds d K hK hκ hC₀
  have hθ'0 : 0 < min θ 1 := lt_min hθ one_pos
  have hV := ballCubeRatio_nonneg d
  set V := ballCubeRatio d with hVdef
  refine ⟨max (2 * Real.sqrt V * (3 * A)) (Real.sqrt (V * A)), min θ 1, n₁,
    le_max_of_le_right (Real.sqrt_nonneg _), hθ'0, min_le_right _ _, ?_⟩
  intro P pk hP e he φ
  have he1 : vecNormSq e = 1 := by
    have h : Real.sqrt (euclideanSq e) = 1 := he
    rwa [Real.sqrt_eq_one] at h
  filter_upwards [ae_dilated_eq_highContrast hP hd hκ hC₀ pk φ,
    φ.locally_square_integrable] with a ha hloc
  obtain ⟨hb, ⟨c, hc⟩, hgrad⟩ := ha
  have hbell := ae_isEllipticMatrix_toHighContrast hK a
  intro r hBXr
  generalize hbdef : toHighContrast hK a = b at hb hc hgrad hbell hBXr ⊢
  have hXb1 : 1 ≤ pk.X b := pk.one_le_X b
  have hXb0 : 0 < pk.X b := lt_of_lt_of_le one_pos hXb1
  have h3n : (1 : ℝ) ≤ (3 : ℝ) ^ (n₁ + 1) := one_le_pow₀ (by norm_num)
  have hBX1 : 1 ≤ (3 : ℝ) ^ (n₁ + 1) * pk.X b := one_le_mul_of_one_le_of_one_le h3n hXb1
  have hr0 : 0 < r := by linarith
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
  set Ob := 3 * A * r ^ (1 - min θ 1) * ((3 : ℝ) ^ (n₁ + 1) * pk.X b) ^ min θ 1 with hOb
  have hOb0 : 0 ≤ Ob := by positivity
  have hOr : cubeBesovOscillation (originCube d (N : ℤ)) 2
      ((pk.wholeSpaceSolution hb hbell e).corrector e) ≤ Ob := by
    refine hO.trans (le_of_eq ?_)
    rw [he1, Real.sqrt_one, mul_one]
  have hO0 : 0 ≤ cubeBesovOscillation (originCube d (N : ℤ)) 2
      ((pk.wholeSpaceSolution hb hbell e).corrector e) := ENNReal.toReal_nonneg
  have hOball : ⨍ x in ball 0 r,
      |φ.potential a x - (⨍ y in ball 0 r, φ.potential a y)| ^ 2 ≤
        (2 * Real.sqrt V * Ob) ^ 2 := by
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
      _ ≤ 4 * (V * Ob ^ 2) := by gcongr
      _ = (2 * Real.sqrt V * Ob) ^ 2 := by
          rw [show (2 * Real.sqrt V * Ob) ^ 2 = 4 * (Real.sqrt V ^ 2 * Ob ^ 2) by ring,
            Real.sq_sqrt hV]
  refine ⟨?_, ?_⟩
  · calc Real.sqrt (⨍ x in ball 0 r,
          |φ.potential a x - (⨍ y in ball 0 r, φ.potential a y)| ^ 2)
        ≤ Real.sqrt ((2 * Real.sqrt V * Ob) ^ 2) := Real.sqrt_le_sqrt hOball
      _ = 2 * Real.sqrt V * (3 * A) * r ^ (1 - min θ 1) *
            ((3 : ℝ) ^ (n₁ + 1) * pk.X b) ^ min θ 1 := by
          rw [Real.sqrt_sq (by positivity), hOb]
          ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · calc Real.sqrt (⨍ x in ball 0 r, euclideanSq (φ.grad a x)) ≤ Real.sqrt (V * A) :=
          Real.sqrt_le_sqrt hEball
      _ ≤ _ := le_max_right _ _

theorem rpow_one_sub_mul_rpow_inv_le {r p x m s : ℝ} (hr : 1 ≤ r) (hd : 0 < (d : ℝ))
    (hs : s < d) (hp : p = 2 * d / (d + s)) (hx : m ≤ x) :
    r ^ (1 - x) * (r ^ p⁻¹) ^ x ≤ r ^ (1 - m / (2 * d) * ((d : ℝ) - s)) := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  rw [← Real.rpow_mul hr0.le, ← Real.rpow_add hr0]
  refine Real.rpow_le_rpow_of_exponent_le hr ?_
  have hpinv : p⁻¹ = (d + s) / (2 * d) := by rw [hp, inv_div]
  rw [hpinv]
  have h2d : (2 * (d : ℝ)) ≠ 0 := by positivity
  have hq : ((d : ℝ) + s) / (2 * d) = 1 - ((d : ℝ) - s) / (2 * d) := by
    rw [eq_sub_iff_add_eq, ← add_div, show (d : ℝ) + s + (d - s) = 2 * d by ring, div_self h2d]
  have key : 1 - x + (d + s) / (2 * d) * x = 1 - x * ((d : ℝ) - s) / (2 * d) := by
    rw [hq]
    ring
  rw [key]
  have h1 : m / (2 * d) * ((d : ℝ) - s) ≤ x * ((d : ℝ) - s) / (2 * d) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hx (by linarith))
      (by positivity)
  linarith

end EinsteinFull.Homogenization

namespace EinsteinFull.External

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport
  EinsteinRelation.External.AKM
open EinsteinFull.External.Source.AKM EinsteinFull.Homogenization
open _root_.Homogenization hiding euclideanBall Vec Mat euclideanNorm
open _root_.Homogenization.HighContrast

/-- **Armstrong, Kuusi and Mourrat, Lemma 3.17 and Proposition 6.2, for source correctors.** -/
theorem akmSublinearCorrectorsStmtV2_holds : Draft.akmSublinearCorrectorsStmtV2 := by
  intro d hd K hK
  have hd0 : NeZero d := ⟨by omega⟩
  have hK1 : 1 ≤ K := hK.le
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨κ, C₀, hκ, hC₀, hpk⟩ := exists_highContrastCorrectorPackage d hd
  obtain ⟨Cφ, θ, n₁, hCφ, hθ, hθ1, hφb⟩ :=
    exists_sourceCorrector_scale_bounds d hd K hK1 hκ hC₀.le
  obtain ⟨Ap, Cab, hAp, hCab, hpair⟩ := exists_uniform_sourceFlux_pairing d hd K hK1 hκ hC₀.le
  obtain ⟨CS, hCS, hSosc⟩ := exists_osc_heatSelectedPotential_le d hd
  have hV₁ : 0 ≤ (volume (euclideanBall d 1)).toReal := ENNReal.toReal_nonneg
  set M := 3 * (K ^ 2 * 1 + K ^ 2 * Cφ ^ 2 + Cab ^ 2) * (volume (euclideanBall d 1)).toReal
    with hM
  have hM0 : 0 ≤ M := by positivity
  have hϑ0 : 0 < fluxDecayExponent d κ := fluxDecayExponent_pos hκ
  set CF := CS * (Real.sqrt M + Ap + Ap / κ) with hCF
  have hCF0 : 0 ≤ CF := by positivity
  set B : ℝ := 2 * (3 : ℝ) ^ (n₁ + 1) with hB
  have h3n : (1 : ℝ) ≤ (3 : ℝ) ^ (n₁ + 1) := one_le_pow₀ (by norm_num)
  have hB1 : 1 ≤ B := by rw [hB]; linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hm0 : 0 < min θ (fluxDecayExponent d κ) := lt_min hθ hϑ0
  refine ⟨min θ (fluxDecayExponent d κ) / (2 * d), 1 + Cφ + d * CF,
    div_pos hm0 (by positivity), by positivity, fun s hs hsd => ?_⟩
  have hds : 0 < (d : ℝ) + s := by positivity
  set p : ℝ := 2 * d / (d + s) with hp
  have hp0 : 0 < p := by positivity
  have hp1 : 1 ≤ p := by
    rw [hp, le_div_iff₀ hds]
    linarith
  have hK2 : (0 : ℝ) < 2 + K / 1 := by linarith
  have hC₁ : 0 < C₀ * (2 + K / 1) ^ C₀ := mul_pos hC₀ (Real.rpow_pos_of_pos hK2 _)
  have hA₁ : 0 < (B * (C₀ * (2 + K / 1) ^ C₀)) ^ p :=
    Real.rpow_pos_of_pos (mul_pos (by positivity) hC₁) _
  refine ⟨(8 : ℝ) ^ s⁻¹ * (B * (C₀ * (2 + K / 1) ^ C₀)) ^ p,
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hA₁,
    fun P hP e he φ => ⟨nonempty_sourceFluxCorrector hd hK hP he φ, fun S => ?_⟩⟩
  obtain ⟨pk⟩ := hpk K hK1 P hP
  have hprob : IsProbabilityMeasure P := hP.1
  have hXm : Measurable fun a => (B * pk.X (toHighContrast hK1 a)) ^ p :=
    ((pk.measurable_X.comp (measurable_toHighContrast hK1)).const_mul _).pow_const p
  have hX1 : ∀ a, 1 ≤ (B * pk.X (toHighContrast hK1 a)) ^ p := fun a =>
    Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hB1 (pk.one_le_X _)) hp0.le
  refine ⟨fun a => (B * pk.X (toHighContrast hK1 a)) ^ p, hXm, ?_, ?_⟩
  · have hq' : s ≤ (d : ℝ) / p := by
      have h : (d : ℝ) / p = (d + s) / 2 := by
        rw [hp, div_div_eq_mul_div, eq_div_iff two_ne_zero, div_mul_eq_mul_div,
          div_eq_iff (by positivity)]
        ring
      rw [h]
      linarith
    exact osBound_of_tail hXm hs hq' hA₁ fun t ht =>
      pk.measure_scaledX_le hP (by positivity) hp0 hC₀.le ht
  have he1 : euclideanSq e = 1 := by
    have h : Real.sqrt (euclideanSq e) = 1 := he
    rwa [Real.sqrt_eq_one] at h
  filter_upwards [hφb P pk hP e he φ, hpair P pk hP e he φ,
    ae_heatFormulaHypotheses_representativeFlux hd hK hP he φ,
    EinsteinFull.Homogenization.SourceFluxCorrector.ae_potential_eq_add_const hd S,
    S.locally_square_integrable,
    φ.locally_square_integrable] with a hφa hpa hg hSc hSloc hφloc
  refine ⟨hX1 a, fun r hr => ?_⟩
  obtain ⟨-, hcab, hpk'⟩ := hpa
  have hXb1 : 1 ≤ pk.X (toHighContrast hK1 a) := pk.one_le_X _
  have hX0 : 0 < pk.X (toHighContrast hK1 a) := lt_of_lt_of_le one_pos hXb1
  have h3Xpos : 0 < (3 : ℝ) ^ (n₁ + 1) * pk.X (toHighContrast hK1 a) := by positivity
  have hBX1 : 1 ≤ B * pk.X (toHighContrast hK1 a) := one_le_mul_of_one_le_of_one_le hB1 hXb1
  have hr' : (B * pk.X (toHighContrast hK1 a)) ^ p ≤ r := hr
  have hBXr : B * pk.X (toHighContrast hK1 a) ≤ r := by
    calc B * pk.X (toHighContrast hK1 a) = (B * pk.X (toHighContrast hK1 a)) ^ (1 : ℝ) :=
          (Real.rpow_one _).symm
      _ ≤ (B * pk.X (toHighContrast hK1 a)) ^ p := Real.rpow_le_rpow_of_exponent_le hBX1 hp1
      _ ≤ r := hr'
  have hr1 : 1 ≤ r := hBX1.trans hBXr
  have hr0 : 0 < r := by linarith
  have hBXp : B * pk.X (toHighContrast hK1 a) ≤ r ^ p⁻¹ := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hr' (inv_nonneg.mpr hp0.le)
    rwa [Real.rpow_rpow_inv (by linarith) hp0.ne'] at h
  have h3X : (3 : ℝ) ^ (n₁ + 1) * pk.X (toHighContrast hK1 a) ≤
      B * pk.X (toHighContrast hK1 a) := by
    rw [hB]
    nlinarith
  have h2X : 2 * pk.X (toHighContrast hK1 a) ≤ B * pk.X (toHighContrast hK1 a) := by
    rw [hB]
    nlinarith
  have hRpos : 0 < B * pk.X (toHighContrast hK1 a) := by linarith
  have hφab := hφa r (h3X.trans hBXr)
  set γ := 1 - min θ (fluxDecayExponent d κ) / (2 * d) * ((d : ℝ) - s) with hγ
  have hrγ : 0 ≤ r ^ γ := Real.rpow_nonneg hr0.le _
  -- the scalar corrector
  have hφ' : Real.sqrt (⨍ x in ball 0 r,
      |φ.potential a x - (⨍ y in ball 0 r, φ.potential a y)| ^ 2) ≤ Cφ * r ^ γ := by
    refine hφab.1.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hCφ
    calc r ^ (1 - θ) * ((3 : ℝ) ^ (n₁ + 1) * pk.X (toHighContrast hK1 a)) ^ θ
        ≤ r ^ (1 - θ) * (r ^ p⁻¹) ^ θ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h3Xpos.le (h3X.trans hBXp) hθ.le)
            (Real.rpow_nonneg hr0.le _)
      _ ≤ r ^ γ := rpow_one_sub_mul_rpow_inv_le hr1 hdpos hsd hp (min_le_left _ _)
  -- the flux corrector
  set g := representativeFlux φ a with hgdef
  have hfun : ∀ (k : Fin d) (y : Vec d),
      g y k - ((matVecMul pk.abar e) k - sourceMeanFlux φ k) =
        ((coefficientRepresentative a y).mulVec (e + φ.grad a y)) k - (matVecMul pk.abar e) k := by
    intro k y
    simp only [hgdef, representativeFlux, Pi.sub_apply]
    ring
  have hgm : Measurable (φ.grad a) :=
    Measurable.of_uncurry_left (f := fun a y => φ.grad a y) φ.measurable_grad
  have hmem : ∀ R : ℝ, 0 < R → MemLp (φ.grad a) 2 (volume.restrict (ball 0 R)) :=
    fun R hR => (hφloc R hR).2
  have hgrowth : ∀ (k : Fin d) (R : ℝ), B * pk.X (toHighContrast hK1 a) ≤ R →
      ∫⁻ y in ball 0 R, ‖g y k - ((matVecMul pk.abar e) k - sourceMeanFlux φ k)‖ₑ ^ 2 ≤
        ENNReal.ofReal (M * R ^ d) := by
    intro k R hR
    simp_rw [hfun k]
    refine (lintegral_sourceFlux_sq_le hK1 a hgm hmem h3Xpos (fun r' hr' => (hφa r' hr').2) e
      (matVecMul pk.abar e) k R (h3X.trans hR)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc2 : (matVecMul pk.abar e) k ^ 2 ≤ Cab ^ 2 := by
      have h := hcab k
      exact sq_le_sq' (by linarith [neg_abs_le ((matVecMul pk.abar e) k)])
        (le_trans (le_abs_self _) h)
    have hR0 : 0 ≤ R := le_trans hRpos.le hR
    rw [he1, hM]
    gcongr
  have hmom : ∀ k : Fin d, HasGaussianMoments
      (fun y => g y k - ((matVecMul pk.abar e) k - sourceMeanFlux φ k)) := fun k =>
    hasGaussianMoments_of_growth ((hg.measurable k).sub_const _) hM0 hRpos (hgrowth k)
  have hpairR : ∀ k : Fin d, HasScalePairingBound
      (fun y => g y k - ((matVecMul pk.abar e) k - sourceMeanFlux φ k))
      (B * pk.X (toHighContrast hK1 a)) Ap κ := by
    intro k
    have h : (fun y => g y k - ((matVecMul pk.abar e) k - sourceMeanFlux φ k)) =
        fun y => ((coefficientRepresentative a y).mulVec (e + φ.grad a y)) k -
          (matVecMul pk.abar e) k := funext (hfun k)
    rw [h]
    exact (hpk' k).mono (by linarith) h2X hAp le_rfl hκ.le
  have hVr : 0 < volume.real (ball (0 : Vec d) r) :=
    ENNReal.toReal_pos (volume_ball_ne_zero hr0) (volume_ball_ne_top hr0)
  have hfin := isFiniteMeasure_restrict_ball (d := d) r
  have hS' : ∀ j k, Real.sqrt (⨍ x in ball 0 r,
      |S.potential a x j k - ⨍ y in ball 0 r, S.potential a y j k| ^ 2) ≤ CF * r ^ γ := by
    intro j k
    obtain ⟨c', hc'⟩ := hSc hg j k
    rw [sqrt_setAverage_sq_eq_oscBall_div,
      oscBall_eq_of_ae_eq_add_const hr0 hc'
        ((hg.memLp_heatSelectedPotential hd j k r).integrable one_le_two),
      div_le_iff₀ (Real.sqrt_pos.mpr hVr)]
    refine (hSosc hg (fun k => (matVecMul pk.abar e) k - sourceMeanFlux φ k) hRpos hAp hκ hM0
      hmom hpairR hgrowth j k hBXr).trans ?_
    have hR : r * (r / (B * pk.X (toHighContrast hK1 a))) ^ (-fluxDecayExponent d κ) ≤ r ^ γ := by
      have e1 : r * (r / (B * pk.X (toHighContrast hK1 a))) ^ (-fluxDecayExponent d κ) =
          r ^ (1 - fluxDecayExponent d κ) *
            (B * pk.X (toHighContrast hK1 a)) ^ fluxDecayExponent d κ := by
        rw [Real.rpow_neg (div_pos hr0 hRpos).le, Real.div_rpow hr0.le hRpos.le, inv_div,
          Real.rpow_sub hr0, Real.rpow_one]
        ring
      rw [e1]
      calc r ^ (1 - fluxDecayExponent d κ) *
            (B * pk.X (toHighContrast hK1 a)) ^ fluxDecayExponent d κ
          ≤ r ^ (1 - fluxDecayExponent d κ) * (r ^ p⁻¹) ^ fluxDecayExponent d κ :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hRpos.le hBXp hϑ0.le)
              (Real.rpow_nonneg hr0.le _)
        _ ≤ r ^ γ := rpow_one_sub_mul_rpow_inv_le hr1 hdpos hsd hp (min_le_right _ _)
    have hsV := Real.sqrt_nonneg (volume.real (ball (0 : Vec d) r))
    calc CS * (Real.sqrt M + Ap + Ap / κ) * r *
          (r / (B * pk.X (toHighContrast hK1 a))) ^ (-fluxDecayExponent d κ) *
          Real.sqrt (volume.real (ball (0 : Vec d) r))
        = CF * (r * (r / (B * pk.X (toHighContrast hK1 a))) ^ (-fluxDecayExponent d κ)) *
          Real.sqrt (volume.real (ball (0 : Vec d) r)) := by rw [hCF]; ring
      _ ≤ CF * r ^ γ * Real.sqrt (volume.real (ball (0 : Vec d) r)) := by gcongr
  have hfrob := sqrt_setAverage_frobeniusNorm_sq_le (by positivity) (U := S.potential a)
    (fun j k => (hSloc r hr0 j k).1) hS'
  refine ⟨?_, ?_⟩
  · calc Real.sqrt (⨍ x in ball 0 r,
          |φ.potential a x - (⨍ y in ball 0 r, φ.potential a y)| ^ 2) +
        Real.sqrt (⨍ x in ball 0 r, frobeniusNorm (S.potential a x -
          (Matrix.of fun i j => ⨍ y in ball 0 r, S.potential a y i j)) ^ 2)
        ≤ Cφ * r ^ γ + d * (CF * r ^ γ) := add_le_add hφ' hfrob
      _ ≤ (1 + Cφ + d * CF) * r ^ γ := by
          linarith [show (1 + Cφ + d * CF) * r ^ γ = r ^ γ + (Cφ * r ^ γ + d * (CF * r ^ γ)) by
            ring]
  · have hdC := mul_nonneg hdpos.le hCF0
    exact hφab.2.trans (by linarith)

end EinsteinFull.External

/-! The high-contrast homogenization theorem raises the CoarseGraining instances
`Homogenization.instMeasurableSpaceMat` (the product σ-algebra on `Mat d`) and
`Homogenization.instBorelSpaceMat` to priority `10000`, and CoarseGraining declares further copies
of `MeasurableSpace (Mat d)`. The modules that use `akm_sublinear_correctors` were elaborated with
the Borel instance `EinsteinRelation.instMeasurableSpaceMat`; these priorities keep that instance
for them. -/

attribute [instance 100] Homogenization.instMeasurableSpaceMat
attribute [instance 100] Homogenization.instBorelSpaceMat
attribute [instance 20000] EinsteinRelation.instMeasurableSpaceMat
