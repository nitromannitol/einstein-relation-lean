import EinsteinFull.Homogenization.HighContrastFluxPairing
import EinsteinFull.Homogenization.HighContrastQuantitative

/-!
# A bound on the homogenized matrix of a uniformly elliptic law

On the event of the homogenization theorem of Armstrong, Kuusi and Loher, *Homogenization at a
polynomial scale in high contrast*, the homogenized matrix `ā = s̄ + k̄` of a `(1, K)`-elliptic law
satisfies `|ā u · w| ≤ C |u| |w|` with `C` depending only on `d`, `K` and the constants of the
theorem. Indeed, tested against the squared inner cutoff of a large origin cube, the flux
`a(u + ∇φ_u) · w` has mean `ā u · w` up to an error that vanishes with the size of the cube: the
flux clause of the corrector estimate controls `((a - k̄)(u + ∇φ_u) - s̄ u) · w` and the corrector
clause controls `k̄ ∇φ_u`. The flux itself is bounded by `K |w|` times the root mean square of
`u + ∇φ_u`, which is of order `|u|` by the energy bound. This is the classical identification of
the homogenized coefficients as mean fluxes (Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Section 1).
-/

open MeasureTheory Filter Topology

namespace EinsteinFull.Homogenization

open _root_.Homogenization hiding euclideanBall
open _root_.Homogenization.HighContrast

variable {d : ℕ}

section Algebra

theorem vecDot_sub_matVecMul_eq (A B : Mat d) (v w : Vec d) :
    vecDot (matVecMul (A - B) v) w =
      vecDot w (matVecMul A v) - vecDot (matVecMul (matTranspose B) w) v := by
  rw [sub_matVecMul, vecDot_sub_left, vecDot_comm (matVecMul A v) w,
    ← vecDot_matVecMul_transpose v w B, vecDot_comm v]

theorem vecDot_skewPart_eq (A : Mat d) (u w : Vec d) :
    vecDot (matVecMul (skewPart A) u) w =
      (vecDot (matVecMul A u) w - vecDot u (matVecMul A w)) / 2 := by
  rw [skewPart_eq_smul_sub_transpose, smul_matVecMul, vecDot_smul_left, sub_matVecMul,
    vecDot_sub_left, vecDot_comm (matVecMul (matTranspose A) u) w,
    vecDot_matVecMul_transpose w u A, vecDot_comm (matVecMul A w) u]
  ring

theorem abs_vecDot_skewPart_le {A : Mat d} {C : ℝ}
    (hA : ∀ u w : Vec d, |vecDot (matVecMul A u) w| ≤
      C * Real.sqrt (vecNormSq u) * Real.sqrt (vecNormSq w)) (u w : Vec d) :
    |vecDot (matVecMul (skewPart A) u) w| ≤
      C * Real.sqrt (vecNormSq u) * Real.sqrt (vecNormSq w) := by
  rw [vecDot_skewPart_eq]
  have h1 := hA u w
  have h2 := hA w u
  rw [vecDot_comm (matVecMul A w) u] at h2
  rw [abs_div, abs_two, div_le_iff₀ two_pos]
  have h3 := abs_sub (vecDot (matVecMul A u) w) (vecDot u (matVecMul A w))
  linarith

theorem sqrt_vecNormSq_skewPart_le {A : Mat d} {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ u w : Vec d, |vecDot (matVecMul A u) w| ≤
      C * Real.sqrt (vecNormSq u) * Real.sqrt (vecNormSq w)) (u : Vec d) :
    Real.sqrt (vecNormSq (matVecMul (skewPart A) u)) ≤ C * Real.sqrt (vecNormSq u) := by
  have h := abs_vecDot_skewPart_le hA u (matVecMul (skewPart A) u)
  have hv : vecDot (matVecMul (skewPart A) u) (matVecMul (skewPart A) u) =
      Real.sqrt (vecNormSq (matVecMul (skewPart A) u)) ^ 2 := by
    rw [Real.sq_sqrt (vecNormSq_nonneg _)]
    rfl
  have ha := Real.sqrt_nonneg (vecNormSq (matVecMul (skewPart A) u))
  have hb : 0 ≤ C * Real.sqrt (vecNormSq u) := mul_nonneg hC (Real.sqrt_nonneg _)
  rw [hv, abs_of_nonneg (sq_nonneg _)] at h
  by_contra hlt
  rw [not_le] at hlt
  have hapos : 0 < Real.sqrt (vecNormSq (matVecMul (skewPart A) u)) := lt_of_le_of_lt hb hlt
  nlinarith [mul_pos hapos (sub_pos.mpr hlt)]

theorem vecNormSq_matVecMul_matSqrt_eq {S : Mat d} (hS : S.PosDef) (w : Vec d) :
    vecNormSq (matVecMul (matSqrt S) w) = vecDot w (matVecMul S w) := by
  have hTT : matSqrt S * matSqrt S = S := (matSqrt_spec hS.posSemidef).2
  have hTt : matTranspose (matSqrt S) = matSqrt S := isSymm_matSqrt _
  calc vecNormSq (matVecMul (matSqrt S) w)
      = vecDot (matVecMul (matSqrt S) w) (matVecMul (matSqrt S) w) := rfl
    _ = vecDot w (matVecMul (matTranspose (matSqrt S)) (matVecMul (matSqrt S) w)) :=
        (vecDot_matVecMul_transpose w _ (matSqrt S)).symm
    _ = vecDot w (matVecMul S w) := by rw [hTt, matVecMul_mul, hTT]

end Algebra

namespace EllipticWholeSpaceSolution

variable {K : ℝ} (s : EllipticWholeSpaceSolution d K)

section Weighted

variable [NeZero d] (N : ℕ) {η : Vec d → ℝ} (hηc : Continuous η) (hη0 : ∀ x, 0 ≤ η x)
  (hη1 : ∀ x, η x ≤ 1)
include hηc hη0 hη1

theorem integrable_normalized_cutoff_sq_mul_vecDot_Dv (c : Vec d) :
    Integrable (fun x => η x ^ 2 * vecDot c (s.Dv x))
      (normalizedCubeMeasure (originCube d (N : ℤ))) := by
  have h := integrable_finsetSum (μ := normalizedCubeMeasure (originCube d (N : ℤ)))
    Finset.univ fun i _ =>
      (s.integrable_normalized_cutoff_sq_mul_Dv N hηc hη0 hη1 i).const_mul (c i)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [vecDot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem integrable_normalized_fluxDefect_test (hK : 1 ≤ K) (B : Mat d) (e w : Vec d) :
    Integrable (fun x => η x ^ 2 * vecDot (matVecMul (s.coeff x - skewPart B) (s.Dv x) -
      matVecMul (symmPart B) e) w) (normalizedCubeMeasure (originCube d (N : ℤ))) := by
  have h1 := s.integrable_normalized_weightedFlux N hηc hη0 hη1 hK w
  have h2 := (integrable_normalized_cutoff_sq N hηc hη0 hη1).const_mul
    (vecDot (matVecMul (symmPart B) e) w)
  have h3 := s.integrable_normalized_cutoff_sq_mul_vecDot_Dv N hηc hη0 hη1
    (matVecMul (matTranspose (skewPart B)) w)
  refine ((h1.sub h3).sub h2).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  rw [vecDot_sub_left, vecDot_sub_matVecMul_eq]
  ring

/-- The weighted mean flux tested against `w`, minus `B e · w` times the mean weight, is the
weighted mean flux defect plus the weighted mean of `k̄ᵀ w · ∇φ`. -/
theorem cubeAverage_flux_test_eq (hK : 1 ≤ K) (B : Mat d) (e w : Vec d) :
    cubeAverage (originCube d (N : ℤ))
        (fun x => η x ^ 2 * vecDot w (matVecMul (s.coeff x) (s.Dv x))) -
      vecDot (matVecMul B e) w * cubeAverage (originCube d (N : ℤ)) (fun x => η x ^ 2) =
    cubeAverage (originCube d (N : ℤ)) (fun x => η x ^ 2 *
        vecDot (matVecMul (s.coeff x - skewPart B) (s.Dv x) - matVecMul (symmPart B) e) w) +
      cubeAverage (originCube d (N : ℤ)) (fun x => η x ^ 2 *
        vecDot (matVecMul (matTranspose (skewPart B)) w) (s.correctorGrad e x)) := by
  have h1 := s.integrable_normalized_weightedFlux N hηc hη0 hη1 hK w
  have h2 := (integrable_normalized_cutoff_sq N hηc hη0 hη1).const_mul
    (vecDot (matVecMul B e) w)
  have hD := s.integrable_normalized_fluxDefect_test N hηc hη0 hη1 hK B e w
  have hC := s.integrable_normalized_cutoff_sq_mul_vecDot_correctorGrad N hηc hη0 hη1 e
    (matVecMul (matTranspose (skewPart B)) w)
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [← integral_const_mul, ← integral_sub h1 h2, ← integral_add hD hC]
  congr 1
  funext x
  have hce : vecDot (matVecMul (matTranspose (skewPart B)) w) e =
      vecDot (matVecMul (skewPart B) e) w := by
    rw [vecDot_comm, vecDot_matVecMul_transpose]
  have hB : vecDot (matVecMul B e) w =
      vecDot (matVecMul (symmPart B) e) w + vecDot (matVecMul (skewPart B) e) w := by
    conv_lhs => rw [← symmPart_add_skewPart B]
    rw [add_matVecMul, vecDot_add_left]
  simp only [correctorGrad]
  rw [vecDot_sub_left (matVecMul (s.coeff x - skewPart B) (s.Dv x)), vecDot_sub_matVecMul_eq,
    vecDot_sub_right _ (s.Dv x) e, hce, hB]
  ring

end Weighted

end EllipticWholeSpaceSolution

section Package

variable {K : ℝ} {hK : 1 ≤ K}
  {P : Measure (EinsteinRelation.Environment.AKMTestIntegralSupport.Coefficient d K)} {κ C : ℝ}

/-- **The weighted flux defect tested against `w` tends to zero.** -/
theorem HighContrastCorrectorPackage.tendsto_cubeAverage_cutoff_sq_fluxDefect_test [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) (hκ : 0 < κ) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e w : Vec d) :
    Tendsto (fun N : ℕ => cubeAverage (originCube d (N : ℤ)) (fun x =>
      innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        vecDot (matVecMul ((pk.wholeSpaceSolution hb hbell e).coeff x - skewPart pk.abar)
          ((pk.wholeSpaceSolution hb hbell e).Dv x) - matVecMul (symmPart pk.abar) e) w))
      atTop (𝓝 0) := by
  have hSpd : (symmPart pk.abar).PosDef := posDef_symmPart_of_vecDot_pos pk.posDef
  have hX : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
  have hLw : matVecMul (matTranspose (matSqrt (symmPart pk.abar))⁻¹)
      (matVecMul (matSqrt (symmPart pk.abar)) w) = w := by
    have hT : matTranspose (matSqrt (symmPart pk.abar))⁻¹ = (matSqrt (symmPart pk.abar))⁻¹ := by
      unfold matTranspose
      rw [Matrix.transpose_nonsing_inv, (isSymm_matSqrt _).eq]
    rw [hT, matVecMul_mul, Matrix.nonsing_inv_mul _ (isUnit_det_matSqrt hSpd),
      _root_.Homogenization.matVecMul_one]
  have hs (x : Vec d) : (pk.wholeSpaceSolution hb hbell e).coeff x =
      ellipticRepresentative K b x := rfl
  have hsD (x : Vec d) : (pk.wholeSpaceSolution hb hbell e).Dv x = e + pk.gradPhi e b x := rfl
  obtain ⟨N₀, hN₀⟩ := exists_sqrt_mul_three_pow_ge (d := d) (pk.X b)
  set w' := matVecMul (matSqrt (symmPart pk.abar)) w
  refine squeeze_zero_norm' (a := fun N : ℕ =>
    Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
      Real.sqrt (vecNormSq w') * (2 * originCutoffConst d + ballVolumeConstant d) *
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
          matVecMul (symmPart pk.abar) e) w) =ᵐ[volume]
        fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
          vecDot (matVecMul ((pk.wholeSpaceSolution hb hbell e).coeff x - skewPart pk.abar)
            ((pk.wholeSpaceSolution hb hbell e).Dv x) - matVecMul (symmPart pk.abar) e) w := by
      filter_upwards [ellipticRepresentative_ae_eq b hbell] with x hx
      have hx' : b.1 x = ellipticRepresentative K b x := hx
      rw [hx', hs x, hsD x]
    have hintS : Integrable (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        vecDot (matVecMul ((pk.wholeSpaceSolution hb hbell e).coeff x - skewPart pk.abar)
          ((pk.wholeSpaceSolution hb hbell e).Dv x) - matVecMul (symmPart pk.abar) e) w) :=
      integrable_of_integrable_normalizedCubeMeasure _
        ((pk.wholeSpaceSolution hb hbell e).integrable_normalized_fluxDefect_test N
          (originCutoff_smooth N).continuous (innerCubeCutoff_nonneg _ _)
          (innerCubeCutoff_le_one _ _) hK pk.abar e w)
        fun x hx => by rw [originCutoff_sq_eq_zero N hx, zero_mul]
    have hintB : Integrable (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        vecDot (matVecMul (b.1 x - skewPart pk.abar) (e + pk.gradPhi e b x) -
          matVecMul (symmPart pk.abar) e)
          (matVecMul (matTranspose (matSqrt (symmPart pk.abar))⁻¹) w')) := by
      rw [hLw]
      exact hintS.congr hae.symm
    have hmain := abs_integral_le_of_negOneNorm_originCube pk.abar hSpd N
      (G := fun x => matVecMul (b.1 x - skewPart pk.abar) (e + pk.gradPhi e b x) -
        matVecMul (symmPart pk.abar) e) (L := (matSqrt (symmPart pk.abar))⁻¹) hB0 hneg
      (originCutoff_sq_smooth N) (originCutoff_sq_hasCompactSupport N)
      (tsupport_originCutoff_sq_subset N) (fun x => sq_nonneg _) (originCutoff_sq_le_one N)
      (norm_fderiv_originCutoff_sq_le N) w' hintB
    beta_reduce at hmain
    rw [hLw, integral_congr_ae hae] at hmain
    have hv := cubeVolume_pos (originCube d (N : ℤ))
    have hout : ∫ x in cubeSet (originCube d (N : ℤ)),
        innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
          vecDot (matVecMul ((pk.wholeSpaceSolution hb hbell e).coeff x - skewPart pk.abar)
            ((pk.wholeSpaceSolution hb hbell e).Dv x) - matVecMul (symmPart pk.abar) e) w =
        ∫ x, innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
          vecDot (matVecMul ((pk.wholeSpaceSolution hb hbell e).coeff x - skewPart pk.abar)
            ((pk.wholeSpaceSolution hb hbell e).Dv x) - matVecMul (symmPart pk.abar) e) w := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      rw [originCutoff_sq_eq_zero N hx, zero_mul]
    rw [Real.norm_eq_abs]
    unfold cubeAverage
    rw [hout, abs_mul, abs_of_pos (inv_pos.mpr hv), inv_mul_le_iff₀ hv]
    refine hmain.trans (le_of_eq ?_)
    have h3 : (3 : ℝ) ^ N * ((3 : ℝ) ^ N)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    calc Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
          Real.sqrt (vecNormSq w') * (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) *
            ((Real.sqrt d * (3 : ℝ) ^ N) / pk.X b) ^ (-κ)) * (3 : ℝ) ^ N *
          (2 * (originCutoffConst d * ((3 : ℝ) ^ N)⁻¹) + ballVolumeConstant d * ((3 : ℝ) ^ N)⁻¹) *
          cubeVolume (originCube d (N : ℤ))
        = Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
          Real.sqrt (vecNormSq w') * (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) *
            ((Real.sqrt d * (3 : ℝ) ^ N) / pk.X b) ^ (-κ)) * ((3 : ℝ) ^ N * ((3 : ℝ) ^ N)⁻¹) *
          (2 * originCutoffConst d + ballVolumeConstant d) *
          cubeVolume (originCube d (N : ℤ)) := by ring
      _ = _ := by rw [h3]; ring
  · have h := ((tendsto_scale_rpow_neg (d := d) hκ hX).const_mul
      (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)))).const_mul
      (Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
        Real.sqrt (vecNormSq w') * (2 * originCutoffConst d + ballVolumeConstant d))
    rw [mul_zero, mul_zero] at h
    exact h

/-- **The weighted mean flux tends to the homogenized flux.** -/
theorem HighContrastCorrectorPackage.tendsto_cubeAverage_cutoff_sq_flux_sub [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) (hκ : 0 < κ) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e w : Vec d) :
    Tendsto (fun N : ℕ => cubeAverage (originCube d (N : ℤ)) (fun x =>
        innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
          vecDot w (matVecMul ((pk.wholeSpaceSolution hb hbell e).coeff x)
            ((pk.wholeSpaceSolution hb hbell e).Dv x))) -
      vecDot (matVecMul pk.abar e) w * cubeAverage (originCube d (N : ℤ))
        (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2)) atTop (𝓝 0) := by
  have hA := pk.tendsto_cubeAverage_cutoff_sq_fluxDefect_test hκ hC hb hbell e w
  have hy := pk.tendsto_cubeAverage_cutoff_sq_correctorGrad hκ hC hb hbell e
  generalize pk.wholeSpaceSolution hb hbell e = s at hA hy ⊢
  have hCc : Tendsto (fun N : ℕ => cubeAverage (originCube d (N : ℤ)) (fun x =>
      innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        vecDot (matVecMul (matTranspose (skewPart pk.abar)) w) (s.correctorGrad e x)))
      atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
      (hy i).const_mul (matVecMul (matTranspose (skewPart pk.abar)) w i)
    have h0 : ∑ i : Fin d, matVecMul (matTranspose (skewPart pk.abar)) w i * (0 : ℝ) = 0 := by
      simp
    rw [h0] at h
    refine h.congr fun N => ?_
    rw [s.cubeAverage_cutoff_sq_mul_vecDot_correctorGrad N (originCutoff_smooth N).continuous
      (innerCubeCutoff_nonneg _ _) (innerCubeCutoff_le_one _ _) e]
  have h := hA.add hCc
  rw [add_zero] at h
  refine h.congr fun N => ?_
  rw [s.cubeAverage_flux_test_eq N (originCutoff_smooth N).continuous (innerCubeCutoff_nonneg _ _)
    (innerCubeCutoff_le_one _ _) hK pk.abar e w]

end Package

/-- **The homogenized matrix is bounded.** There is `C_ā` depending only on `d`, `K` and the
constants of the homogenization theorem such that on its event `|ā u · w| ≤ C_ā |u| |w|`. -/
theorem exists_abs_vecDot_abar_le (d : ℕ) [NeZero d] (K : ℝ) (hK : 1 ≤ K) {κ C : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C) :
    ∃ Cab : ℝ, 0 ≤ Cab ∧
      ∀ (P : Measure (EinsteinRelation.Environment.AKMTestIntegralSupport.Coefficient d K))
        (pk : HighContrastCorrectorPackage hK P κ C) {b : CoeffSpace d}, b ∈ pk.Ωend →
        (∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) →
        ∀ u w : Vec d, |vecDot (matVecMul pk.abar u) w| ≤
          Cab * Real.sqrt (vecNormSq u) * Real.sqrt (vecNormSq w) := by
  obtain ⟨A, θ, n₁, hA, hθ, hq⟩ := exists_highContrast_quantitative_bounds d K hK hκ hC
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  refine ⟨2 ^ d * (K * Real.sqrt (K * (2 + 2 * A))), by positivity, ?_⟩
  intro P pk b hb hbell u w
  have hlim := pk.tendsto_cubeAverage_cutoff_sq_flux_sub hκ hC hb hbell u w
  obtain ⟨N₀, hN₀⟩ := exists_sqrt_mul_three_pow_ge (d := d) (pk.X b)
  have hqN : ∀ N, max N₀ n₁ ≤ N → cubeAverage (originCube d (N : ℤ))
      (fun x => vecNormSq ((pk.wholeSpaceSolution hb hbell u).correctorGrad u x)) ≤
        A * vecNormSq u := by
    intro N hN
    have h := (hq P pk hb hbell u N 0 (hN₀ N ((le_max_left _ _).trans hN))
      ((le_max_right _ _).trans hN)).1
    simpa using h
  generalize pk.wholeSpaceSolution hb hbell u = s at hlim hqN
  set Cb := K * Real.sqrt (K * (2 + 2 * A)) * Real.sqrt (vecNormSq u) *
    Real.sqrt (vecNormSq w) with hCb
  have hu0 := Real.sqrt_nonneg (vecNormSq u)
  have hw0 := Real.sqrt_nonneg (vecNormSq w)
  have key : ∀ ε : ℝ, 0 < ε → (1 / 2 : ℝ) ^ d * |vecDot (matVecMul pk.abar u) w| ≤ Cb + ε := by
    intro ε hε
    obtain ⟨N, hN1, hN2⟩ := ((eventually_abs_le_of_tendsto_zero hlim hε).and
      (eventually_ge_atTop (max N₀ n₁))).exists
    have hηc : Continuous (innerCubeCutoff (originCube d (N : ℤ)) (1 / 4)) :=
      (originCutoff_smooth N).continuous
    have hη0 : ∀ x, 0 ≤ innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x :=
      innerCubeCutoff_nonneg _ _
    have hη1 : ∀ x, innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ≤ 1 :=
      innerCubeCutoff_le_one _ _
    have hs1 := pow_le_cubeAverage_sq_innerCubeCutoff (originCube d (N : ℤ))
      (by norm_num : (0 : ℝ) < 1 / 4) le_rfl
    have hhalf : (1 - 2 * (1 / 4 : ℝ)) = 1 / 2 := by norm_num
    rw [hhalf] at hs1
    have hs2 := cubeAverage_sq_le_one (originCube d (N : ℤ)) hηc hη0 hη1
    set a := cubeAverage (originCube d (N : ℤ))
      (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2) with ha
    have ha0 : 0 ≤ a := le_trans (by positivity) hs1
    -- the weighted energy is at most `K (2 + 2A) |u|²`
    set W := cubeAverage (originCube d (N : ℤ)) (fun x =>
      innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x))) with hWdef
    have hW : W ≤ K * (2 + 2 * A) * vecNormSq u := by
      have h1 : W ≤ K * cubeAverage (originCube d (N : ℤ)) (fun x => vecNormSq (s.Dv x)) := by
        rw [hWdef]
        simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
        rw [← integral_const_mul]
        refine integral_mono (s.integrable_normalized_weightedEnergy N hηc hη0 hη1 hK)
          ((s.integrable_normalized_vecNormSq_Dv N).const_mul K) fun x => ?_
        have he := s.abs_energyDensity_le hK x
        have he0 := (vecNormSq_nonneg (s.Dv x)).trans (s.vecNormSq_le_energyDensity x)
        have hη2 : innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 ≤ 1 :=
          pow_le_one₀ (hη0 x) (hη1 x)
        have hη20 := sq_nonneg (innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x)
        rw [abs_of_nonneg he0] at he
        calc innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
              vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x))
            ≤ 1 * vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x)) :=
              mul_le_mul_of_nonneg_right hη2 he0
          _ ≤ K * vecNormSq (s.Dv x) := by linarith
      have h2 := s.cubeAverage_vecNormSq_Dv_le u N
      have h3 := hqN N hN2
      have hun := vecNormSq_nonneg u
      calc W ≤ K * cubeAverage (originCube d (N : ℤ)) (fun x => vecNormSq (s.Dv x)) := h1
        _ ≤ K * (2 * vecNormSq u + 2 * (A * vecNormSq u)) := by gcongr; linarith
        _ = K * (2 + 2 * A) * vecNormSq u := by ring
    have hW0 : 0 ≤ W := by
      rw [hWdef]
      exact cubeAverage_nonneg_of_nonneg _ fun x => mul_nonneg (sq_nonneg _)
        ((vecNormSq_nonneg _).trans (s.vecNormSq_le_energyDensity x))
    have hsW : Real.sqrt W ≤ Real.sqrt (K * (2 + 2 * A)) * Real.sqrt (vecNormSq u) := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt hW
    have hsa : Real.sqrt a ≤ 1 := Real.sqrt_le_one.mpr hs2
    have hflux : ∀ p : Vec d, cubeAverage (originCube d (N : ℤ))
        (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
          vecDot p (matVecMul (s.coeff x) (s.Dv x))) ≤
        K * Real.sqrt (vecNormSq p) *
          (Real.sqrt (K * (2 + 2 * A)) * Real.sqrt (vecNormSq u)) := by
      intro p
      refine (s.cubeAverage_flux_le N hηc hη0 hη1 hK p).trans ?_
      have hp := Real.sqrt_nonneg (vecNormSq p)
      calc K * Real.sqrt (vecNormSq p) * Real.sqrt a * Real.sqrt W
          ≤ K * Real.sqrt (vecNormSq p) * 1 *
              (Real.sqrt (K * (2 + 2 * A)) * Real.sqrt (vecNormSq u)) := by gcongr
        _ = _ := by ring
    have hneg : cubeAverage (originCube d (N : ℤ))
        (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
          vecDot (-w) (matVecMul (s.coeff x) (s.Dv x))) =
        -cubeAverage (originCube d (N : ℤ))
          (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
            vecDot w (matVecMul (s.coeff x) (s.Dv x))) := by
      simp only [cubeAverage_eq_integral_normalizedCubeMeasure, vecDot_neg_left, mul_neg,
        integral_neg]
    have hnw : vecNormSq (-w) = vecNormSq w := by simp [vecNormSq, vecDot]
    have hp1 := hflux w
    have hp2 := hflux (-w)
    rw [hneg, hnw] at hp2
    set D := cubeAverage (originCube d (N : ℤ))
      (fun x => innerCubeCutoff (originCube d (N : ℤ)) (1 / 4) x ^ 2 *
        vecDot w (matVecMul (s.coeff x) (s.Dv x))) with hD
    have hDabs : |D| ≤ Cb := by
      rw [abs_le]
      constructor <;> nlinarith
    have hN1' : |D - vecDot (matVecMul pk.abar u) w * a| ≤ ε := hN1
    have htri : |vecDot (matVecMul pk.abar u) w * a| ≤ |D| +
        |D - vecDot (matVecMul pk.abar u) w * a| := by
      have := abs_sub D (D - vecDot (matVecMul pk.abar u) w * a)
      rwa [sub_sub_cancel] at this
    rw [abs_mul, abs_of_nonneg ha0] at htri
    calc (1 / 2 : ℝ) ^ d * |vecDot (matVecMul pk.abar u) w|
        ≤ a * |vecDot (matVecMul pk.abar u) w| :=
          mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)
      _ = |vecDot (matVecMul pk.abar u) w| * a := mul_comm _ _
      _ ≤ Cb + ε := by linarith
  have h2 : (1 / 2 : ℝ) ^ d * |vecDot (matVecMul pk.abar u) w| ≤ Cb :=
    le_of_forall_pos_le_add key
  have h22 : (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d = 1 := by
    rw [← mul_pow]
    norm_num
  calc |vecDot (matVecMul pk.abar u) w|
      = (2 : ℝ) ^ d * ((1 / 2 : ℝ) ^ d * |vecDot (matVecMul pk.abar u) w|) := by
        rw [← mul_assoc, h22, one_mul]
    _ ≤ (2 : ℝ) ^ d * Cb := by gcongr
    _ = _ := by rw [hCb]; ring

end EinsteinFull.Homogenization
