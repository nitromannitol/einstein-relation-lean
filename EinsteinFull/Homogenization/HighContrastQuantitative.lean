import EinsteinFull.Homogenization.HighContrastDivCurl

/-!
# Quantitative bounds for high-contrast correctors

On the event of the homogenization theorem of Armstrong, Kuusi and Loher, *Homogenization at a
polynomial scale in high contrast*, the bounds `|e|² ≤ e · s̄ e ≤ K² |e|²` on the homogenized
matrix bound the pairing amplitude of the corrector estimate by a constant depending only on `d`,
`K` and the constants of the theorem. The energy iteration and the oscillation decay then give,
at every origin cube of side `3^(n₀ + L)` with `X ≤ √d 3^n₀` and `n₀` beyond a fixed depth,
`⨍ |∇φ_e|² ≤ A |e|²` and `‖φ_e - (φ_e)‖ ≤ A |e| 3^(n₀ + L) 3^(-θ L)`, with deterministic
constants `A`, `θ`.
-/

open MeasureTheory Filter Topology

namespace EinsteinFull.Homogenization

open _root_.Homogenization hiding euclideanBall
open _root_.Homogenization.HighContrast

variable {d : ℕ}

section MatrixBounds

variable {abar : Mat d} {K : ℝ}

theorem specBound_symmPart_le
    (hup : ∀ v : Vec d, vecDot v (matVecMul (symmPart abar) v) ≤ K ^ 2 * vecNormSq v) :
    specBound (symmPart abar) ≤ K ^ 2 := by
  refine specBound_le (sq_nonneg K) fun x => ?_
  rw [matVecMul_smul_one', vecDot_smul_right]
  have h := hup x
  have hn : vecDot x x = vecNormSq x := rfl
  rw [hn]
  linarith

theorem vecDot_matVecMul_inv_symmPart_le
    (hlow : ∀ v : Vec d, vecNormSq v ≤ vecDot v (matVecMul (symmPart abar) v))
    (hS : (symmPart abar).PosDef) (x : Vec d) :
    vecDot x (matVecMul (symmPart abar)⁻¹ x) ≤ vecNormSq x := by
  have hu : IsUnit (symmPart abar).det := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  set y := matVecMul (symmPart abar)⁻¹ x with hy
  have hSy : matVecMul (symmPart abar) y = x := by
    rw [hy, matVecMul_mul, Matrix.mul_nonsing_inv _ hu, _root_.Homogenization.matVecMul_one]
  have h1 : vecDot x y = vecDot y (matVecMul (symmPart abar) y) := by
    rw [hSy, vecDot_comm]
  have h2 := hlow y
  have h3 := abs_vecDot_le_sqrt_mul_sqrt y x
  have h4 := le_abs_self (vecDot y x)
  have hy0 := Real.sqrt_nonneg (vecNormSq y)
  have hx0 := Real.sqrt_nonneg (vecNormSq x)
  have hyy := Real.sq_sqrt (vecNormSq_nonneg y)
  have hxx := Real.sq_sqrt (vecNormSq_nonneg x)
  have hSyx : vecDot y (matVecMul (symmPart abar) y) = vecDot y x := by rw [hSy]
  rw [h1, hSyx]
  rw [hSyx] at h2
  have h5 : Real.sqrt (vecNormSq y) ≤ Real.sqrt (vecNormSq x) := by nlinarith
  nlinarith

theorem specBound_inv_symmPart_le_one
    (hlow : ∀ v : Vec d, vecNormSq v ≤ vecDot v (matVecMul (symmPart abar) v))
    (hS : (symmPart abar).PosDef) : specBound (symmPart abar)⁻¹ ≤ 1 := by
  refine specBound_le zero_le_one fun x => ?_
  rw [matVecMul_smul_one', vecDot_smul_right, one_mul]
  have h := vecDot_matVecMul_inv_symmPart_le hlow hS x
  have hn : vecDot x x = vecNormSq x := rfl
  rw [hn]
  linarith

theorem ellipsoid_one_subset_euclideanBall (hK : 1 ≤ K)
    (hlow : ∀ v : Vec d, vecNormSq v ≤ vecDot v (matVecMul (symmPart abar) v))
    (hup : ∀ v : Vec d, vecDot v (matVecMul (symmPart abar) v) ≤ K ^ 2 * vecNormSq v)
    (hS : (symmPart abar).PosDef) : ellipsoid abar 1 ⊆ euclideanBall d (2 * K) := by
  intro x hx
  have hx' : vecDot x (matVecMul (symmPart abar)⁻¹ x) ≤ specBound (symmPart abar)⁻¹ * 1 ^ 2 :=
    hx
  have h1 := specBound_inv_symmPart_le_one hlow hS
  have h2 := specBound_symmPart_le hup
  have h3 := vecNormSq_le_vecDot_matVecMul_inv_mul_specBound hS x
  have h4 := specBound_nonneg (symmPart abar)
  have hxS : vecDot x (matVecMul (symmPart abar)⁻¹ x) ≤ 1 := by nlinarith
  show vecNormSq (x - 0) < (2 * K) ^ 2
  rw [sub_zero]
  nlinarith [mul_nonneg (sub_nonneg.2 hxS) h4]

theorem vecNormSq_matVecMul_inv_matSqrt_le
    (hlow : ∀ v : Vec d, vecNormSq v ≤ vecDot v (matVecMul (symmPart abar) v))
    (hS : (symmPart abar).PosDef) (w : Vec d) :
    vecNormSq (matVecMul (matSqrt (symmPart abar))⁻¹ w) ≤ vecNormSq w := by
  set T := matSqrt (symmPart abar)
  have hTT : T * T = symmPart abar := (matSqrt_spec hS.posSemidef).2
  have hTt : matTranspose T = T := isSymm_matSqrt _
  set v := matVecMul T⁻¹ w with hv
  have hTv : matVecMul T v = w := by
    rw [hv, matVecMul_mul, Matrix.mul_nonsing_inv _ (isUnit_det_matSqrt hS),
      _root_.Homogenization.matVecMul_one]
  have hvSv : vecDot v (matVecMul (symmPart abar) v) = vecNormSq w := by
    rw [← hTT, ← matVecMul_mul, hTv]
    calc vecDot v (matVecMul T w) = vecDot v (matVecMul (matTranspose T) w) := by rw [hTt]
      _ = vecDot (matVecMul T v) w := vecDot_matVecMul_transpose v w T
      _ = vecNormSq w := by rw [hTv]; rfl
  have h := hlow v
  rw [hvSv] at h
  exact h

end MatrixBounds

section Package

variable {K : ℝ} {hK : 1 ≤ K}
  {P : Measure (EinsteinRelation.Environment.AKMTestIntegralSupport.Coefficient d K)} {κ C : ℝ}

/-- The deterministic bound of the pairing constant. -/
noncomputable def pairingConstantBound (d : ℕ) (K C : ℝ) : ℝ :=
  Real.sqrt (volume (euclideanBall d (2 * K))).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
    Real.sqrt d * (C * K)

theorem pairingConstantBound_nonneg (d : ℕ) {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    0 ≤ pairingConstantBound d K C := by
  unfold pairingConstantBound
  have := mul_nonneg hC hK
  positivity

/-- **The pairing constant is bounded deterministically.** -/
theorem HighContrastCorrectorPackage.pairingConstant_le [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) (hκ : 0 < κ) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d) :
    pk.pairingConstant e ≤ pairingConstantBound d K C * Real.sqrt (vecNormSq e) := by
  have hlow (v : Vec d) := (pk.vecNormSq_le_vecDot_symmPart_and_le hκ hC hb hbell v).1
  have hup (v : Vec d) := (pk.vecNormSq_le_vecDot_symmPart_and_le hκ hC hb hbell v).2
  have hS : (symmPart pk.abar).PosDef := posDef_symmPart_of_vecDot_pos pk.posDef
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hvol : (volume (ellipsoid pk.abar 1)).toReal ≤
      (volume (euclideanBall d (2 * K))).toReal :=
    ENNReal.toReal_mono (volume_euclideanBall_lt_top _).ne
      (measure_mono (ellipsoid_one_subset_euclideanBall hK hlow hup hS))
  have hsum : ∑ i, vecNormSq (matVecMul (matSqrt (symmPart pk.abar))⁻¹ (basisVec i)) ≤ d := by
    calc ∑ i, vecNormSq (matVecMul (matSqrt (symmPart pk.abar))⁻¹ (basisVec i))
        ≤ ∑ i : Fin d, vecNormSq (basisVec i : Vec d) :=
          Finset.sum_le_sum fun i _ => vecNormSq_matVecMul_inv_matSqrt_le hlow hS _
      _ = d := by simp [vecNormSq, vecDot, basisVec, Pi.single_apply]
  have hq : Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)) ≤
      K * Real.sqrt (vecNormSq e) := by
    calc Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e))
        ≤ Real.sqrt (K ^ 2 * vecNormSq e) := Real.sqrt_le_sqrt (hup e)
      _ = K * Real.sqrt (vecNormSq e) := by
          rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK0]
  unfold HighContrastCorrectorPackage.pairingConstant pairingConstantBound
  calc Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
        Real.sqrt (∑ i, vecNormSq (matVecMul (matSqrt (symmPart pk.abar))⁻¹ (basisVec i))) *
        (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)))
      ≤ Real.sqrt (volume (euclideanBall d (2 * K))).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
        Real.sqrt d * (C * (K * Real.sqrt (vecNormSq e))) := by
        gcongr
    _ = _ := by ring

theorem inv_three_pow_le_rpow {N L : ℕ} (hLN : L ≤ N) {θ : ℝ} (hθ1 : θ ≤ 1) :
    ((3 : ℝ) ^ N)⁻¹ ≤ ((3 : ℝ) ^ L) ^ (-θ) := by
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ L := one_le_pow₀ (by norm_num)
  calc ((3 : ℝ) ^ N)⁻¹ ≤ ((3 : ℝ) ^ L)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hLN)
    _ = ((3 : ℝ) ^ L) ^ (-(1 : ℝ)) := (Real.rpow_neg_one _).symm
    _ ≤ ((3 : ℝ) ^ L) ^ (-θ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

theorem inv_three_pow_div_le_rpow {L q : ℕ} (hq : 1 ≤ q) {θ : ℝ} (hθ : θ ≤ 1 / q) :
    ((3 : ℝ) ^ (L / q))⁻¹ ≤ 3 * ((3 : ℝ) ^ L) ^ (-θ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlt : (L : ℝ) < q * ((L / q : ℕ) + 1) := by
    have := Nat.lt_mul_div_succ L (show 0 < q by omega)
    exact_mod_cast this
  have h1 : (L : ℝ) / q - 1 ≤ (L / q : ℕ) := by
    rw [div_sub_one hq0.ne', div_le_iff₀ hq0]
    linarith
  have h1' : (1 : ℝ) ≤ (3 : ℝ) ^ L := one_le_pow₀ (by norm_num)
  have h2 : ((3 : ℝ) ^ L) ^ (-(1 / (q : ℝ))) ≤ ((3 : ℝ) ^ L) ^ (-θ) :=
    Real.rpow_le_rpow_of_exponent_le h1' (by linarith)
  have h3 : ((3 : ℝ) ^ (L / q))⁻¹ = (3 : ℝ) ^ (-((L / q : ℕ) : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  have h4 : ((3 : ℝ) ^ L) ^ (-(1 / (q : ℝ))) = (3 : ℝ) ^ (-((L : ℝ) / q)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have h5 : (3 : ℝ) ^ (-((L / q : ℕ) : ℝ)) ≤ (3 : ℝ) ^ (1 - (L : ℝ) / q) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h6 : (3 : ℝ) ^ (1 - (L : ℝ) / q) = 3 * (3 : ℝ) ^ (-((L : ℝ) / q)) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
  rw [h3]
  calc (3 : ℝ) ^ (-((L / q : ℕ) : ℝ)) ≤ 3 * (3 : ℝ) ^ (-((L : ℝ) / q)) := h5.trans h6.le
    _ = 3 * ((3 : ℝ) ^ L) ^ (-(1 / (q : ℝ))) := by rw [h4]
    _ ≤ 3 * ((3 : ℝ) ^ L) ^ (-θ) := by gcongr

theorem inv_rpow_pow_le_rpow {κ θ : ℝ} (hθ : θ ≤ κ / 2) (L : ℕ) :
    (((3 : ℝ) ^ (κ / 2)) ^ L)⁻¹ ≤ ((3 : ℝ) ^ L) ^ (-θ) := by
  have h1' : (1 : ℝ) ≤ (3 : ℝ) ^ L := one_le_pow₀ (by norm_num)
  have h : (((3 : ℝ) ^ (κ / 2)) ^ L)⁻¹ = ((3 : ℝ) ^ L) ^ (-(κ / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_neg (by positivity),
      ← Real.rpow_natCast ((3 : ℝ)) L, ← Real.rpow_mul (by norm_num)]
    congr 2
    ring
  rw [h]
  exact Real.rpow_le_rpow_of_exponent_le h1' (by linarith)

/-- **Quantitative bounds for high-contrast correctors.** There are constants `A`, `θ > 0` and
a depth `n₁`, depending only on `d`, `K`, `κ` and `C`, such that on the event of the
homogenization theorem, at every origin cube of side `3^(n₀ + L)` with `X ≤ √d 3^n₀` and
`n₁ ≤ n₀`, the corrector of every direction `e` satisfies `⨍ |∇φ_e|² ≤ A |e|²` and has
oscillation at most `A |e| 3^(n₀ + L) (3^L)^(-θ)`. -/
theorem exists_highContrast_quantitative_bounds (d : ℕ) [NeZero d] (K : ℝ) (hK : 1 ≤ K)
    {κ C : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C) :
    ∃ (A θ : ℝ) (n₁ : ℕ), 0 ≤ A ∧ 0 < θ ∧
      ∀ (P : Measure (EinsteinRelation.Environment.AKMTestIntegralSupport.Coefficient d K))
        (pk : HighContrastCorrectorPackage hK P κ C) {b : CoeffSpace d} (hb : b ∈ pk.Ωend)
        (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d)
        (n₀ L : ℕ), pk.X b ≤ Real.sqrt d * (3 : ℝ) ^ n₀ → n₁ ≤ n₀ →
        cubeAverage (originCube d ((n₀ + L : ℕ) : ℤ))
            (fun x => vecNormSq ((pk.wholeSpaceSolution hb hbell e).correctorGrad e x)) ≤
          A * vecNormSq e ∧
        cubeBesovOscillation (originCube d ((n₀ + L : ℕ) : ℤ)) 2
            ((pk.wholeSpaceSolution hb hbell e).corrector e) ≤
          A * Real.sqrt (vecNormSq e) * (3 : ℝ) ^ (n₀ + L) * ((3 : ℝ) ^ L) ^ (-θ) := by
  obtain ⟨CE, hCE, n₁, hE⟩ := exists_energy_bound d K hK
  obtain ⟨C₀, hC₀, hdecay⟩ := exists_oscillation_decay d
  obtain ⟨q, hq1, hq⟩ := exists_three_pow_le_rpow_pow hκ d
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  set γ := (3 : ℝ) ^ (κ / 2) with hγ
  have hγ1 : 1 < γ := Real.one_lt_rpow (by norm_num) (by positivity)
  set cμ := ballVolumeConstant d
  have hcμ : 0 ≤ cμ := ballVolumeConstant_nonneg d
  set Cp := pairingConstantBound d K C
  have hCp : 0 ≤ Cp := pairingConstantBound_nonneg d hK0 hC
  set A₁ := CE * (1 + (1 + cμ) ^ 2 * Cp ^ 2)
  have hA₁ : 0 ≤ A₁ := by positivity
  set A₂ := C₀ * (19 / 4 * Real.sqrt A₁ + 16 * (1 + cμ) * Cp)
  have hA₂ : 0 ≤ A₂ := by positivity
  set θ := min (1 / (q : ℝ)) (κ / 2)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hθ0 : 0 < θ := lt_min (by positivity) (by positivity)
  have hθq : θ ≤ 1 / q := min_le_left _ _
  have hθκ : θ ≤ κ / 2 := min_le_right _ _
  have hθ1 : θ ≤ 1 := hθq.trans (by rw [div_le_one hq0]; exact_mod_cast hq1)
  refine ⟨max A₁ A₂, θ, n₁, le_max_of_le_left hA₁, hθ0, ?_⟩
  intro P pk b hb hbell e n₀ L hX hn₁
  set s := pk.wholeSpaceSolution hb hbell e
  set p := Real.sqrt (vecNormSq e)
  have hp0 : 0 ≤ p := Real.sqrt_nonneg _
  have hpc := pk.pairingConstant_le hκ hC hb hbell e
  have hpc0 := pk.pairingConstant_nonneg hC e
  have hXN : ∀ N, n₀ ≤ N → pk.X b ≤ Real.sqrt d * (3 : ℝ) ^ N := fun N hN =>
    hX.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hN)
      (Real.sqrt_nonneg _))
  have henergy : cubeAverage (originCube d ((n₀ + L : ℕ) : ℤ))
      (fun x => vecNormSq (s.correctorGrad e x)) ≤ A₁ * vecNormSq e := by
    obtain ⟨ρ, Cg, Ng, hρ, hρ2, hCg, hgrowth⟩ := pk.exists_cube_growth hb hbell e
    have h := hE s e (Cp * p) cμ (mul_nonneg hCp hp0) hcμ n₀ (fun N hN m _ =>
      EllipticWholeSpaceSolution.PairingBound.mono _ hcμ
        ((pk.pairingAmplitude_le hκ hC b e (hXN N hN)).trans hpc)
        (pk.pairingBound hC hb hbell e (hXN N hN) m)) ρ Cg Ng hρ hρ2 hCg hgrowth (n₀ + L)
      (max_le (Nat.le_add_right _ _) (hn₁.trans (Nat.le_add_right _ _)))
    have hpp : p ^ 2 = vecNormSq e := Real.sq_sqrt (vecNormSq_nonneg e)
    calc _ ≤ CE * (vecNormSq e + (1 + cμ) ^ 2 * (Cp * p) ^ 2) := h
      _ = A₁ * vecNormSq e := by rw [mul_pow, hpp]; ring
  refine ⟨henergy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (vecNormSq_nonneg e)), ?_⟩
  have hpair : ∀ m ≤ n₀ + L, s.PairingBound e (Cp * p * (γ ^ L)⁻¹ ^ 2) cμ (n₀ + L) m := by
    intro m _
    refine EllipticWholeSpaceSolution.PairingBound.mono _ hcμ ?_
      (pk.pairingBound hC hb hbell e (hXN _ (Nat.le_add_right _ _)) m)
    rw [pk.pairingAmplitude_eq, hγ, inv_pow_rpow_half_sq]
    have hXpos : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
    have hsplit : (Real.sqrt d * (3 : ℝ) ^ (n₀ + L)) / pk.X b =
        ((Real.sqrt d * (3 : ℝ) ^ n₀) / pk.X b) * (3 : ℝ) ^ L := by
      rw [pow_add]
      ring
    have hbase : 1 ≤ (Real.sqrt d * (3 : ℝ) ^ n₀) / pk.X b := by
      rw [le_div_iff₀ hXpos, one_mul]
      exact hX
    rw [hsplit, Real.mul_rpow (by positivity) (by positivity)]
    have h1 : ((Real.sqrt d * (3 : ℝ) ^ n₀) / pk.X b) ^ (-κ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
    have h2 : 0 ≤ ((3 : ℝ) ^ L) ^ (-κ) := Real.rpow_nonneg (by positivity) _
    calc pk.pairingConstant e * (((Real.sqrt d * (3 : ℝ) ^ n₀) / pk.X b) ^ (-κ) *
          ((3 : ℝ) ^ L) ^ (-κ))
        ≤ (Cp * p) * (1 * ((3 : ℝ) ^ L) ^ (-κ)) :=
          mul_le_mul hpc (mul_le_mul_of_nonneg_right h1 h2) (by positivity) (by positivity)
      _ = Cp * p * ((3 : ℝ) ^ L) ^ (-κ) := by ring
  have hEb : cubeAverage (originCube d ((n₀ + L : ℕ) : ℤ))
      (fun x => vecNormSq (s.correctorGrad e x)) ≤ A₁ * vecNormSq e := henergy
  have h := hdecay s e cμ (A₁ * vecNormSq e) (Cp * p) γ q n₀ L hcμ
    (mul_nonneg hA₁ (vecNormSq_nonneg e)) (mul_nonneg hCp hp0) hγ1.le hq1 hq hpair hEb
  set t := ((3 : ℝ) ^ L) ^ (-θ)
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have hr1 : ((3 : ℝ) ^ (n₀ + L))⁻¹ ≤ t := inv_three_pow_le_rpow (Nat.le_add_left _ _) hθ1
  have hr2 : ((3 : ℝ) ^ (L / q))⁻¹ ≤ 3 * t := inv_three_pow_div_le_rpow hq1 hθq
  have hr3 : (γ ^ L)⁻¹ ≤ t := inv_rpow_pow_le_rpow hθκ L
  have hsq : Real.sqrt (A₁ * vecNormSq e) = Real.sqrt A₁ * p := Real.sqrt_mul hA₁ _
  rw [hsq] at h
  have h3N : (0 : ℝ) ≤ (3 : ℝ) ^ (n₀ + L) := by positivity
  have hsA : 0 ≤ Real.sqrt A₁ * p := mul_nonneg (Real.sqrt_nonneg _) hp0
  calc cubeBesovOscillation (originCube d ((n₀ + L : ℕ) : ℤ)) 2 (s.corrector e)
      ≤ C₀ * (3 : ℝ) ^ (n₀ + L) * (Real.sqrt A₁ * p * (((3 : ℝ) ^ (n₀ + L))⁻¹ +
          5 / 4 * ((3 : ℝ) ^ (L / q))⁻¹) + 16 * (1 + cμ) * (Cp * p) * (γ ^ L)⁻¹) := h
    _ ≤ C₀ * (3 : ℝ) ^ (n₀ + L) * (Real.sqrt A₁ * p * (t + 5 / 4 * (3 * t)) +
          16 * (1 + cμ) * (Cp * p) * t) := by
        gcongr
    _ = A₂ * p * (3 : ℝ) ^ (n₀ + L) * t := by ring
    _ ≤ max A₁ A₂ * p * (3 : ℝ) ^ (n₀ + L) * t := by
        gcongr
        exact le_max_right _ _

end Package

end EinsteinFull.Homogenization
