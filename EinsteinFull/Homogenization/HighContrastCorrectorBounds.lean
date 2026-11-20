import EinsteinFull.Homogenization.HighContrastCorrectorPairing

/-!
# Energy bounds and sublinearity of high-contrast correctors

On the event of the homogenization theorem of Armstrong, Kuusi and Loher, *Homogenization at a
polynomial scale in high contrast*, the corrector of every direction has bounded energy on all
large origin cubes, and its oscillation on the origin cube of side `3ᴺ` is `o(3ᴺ)`. Both follow
from the energy iteration and the oscillation decay, with the pairing bound supplied by the
corrector estimate on the ellipsoids above the homogenization scale.
-/

open MeasureTheory Filter Topology

namespace EinsteinFull.Homogenization

open _root_.Homogenization hiding euclideanBall
open _root_.Homogenization.HighContrast

variable {d : ℕ}

section Package

variable {K : ℝ} {hK : 1 ≤ K}
  {P : Measure (EinsteinRelation.Environment.AKMTestIntegralSupport.Coefficient d K)} {κ C : ℝ}

/-- The pairing amplitude without its decay factor. -/
noncomputable def HighContrastCorrectorPackage.pairingConstant
    (pk : HighContrastCorrectorPackage hK P κ C) (e : Vec d) : ℝ :=
  Real.sqrt (volume (ellipsoid pk.abar 1)).toReal * Real.sqrt (Real.sqrt d ^ d) * d *
    Real.sqrt (∑ i, vecNormSq (matVecMul (matSqrt (symmPart pk.abar))⁻¹ (basisVec i))) *
    (C * Real.sqrt (vecDot e (matVecMul (symmPart pk.abar) e)))

theorem HighContrastCorrectorPackage.pairingConstant_nonneg
    (pk : HighContrastCorrectorPackage hK P κ C) (hC : 0 ≤ C) (e : Vec d) :
    0 ≤ pk.pairingConstant e := by
  unfold HighContrastCorrectorPackage.pairingConstant
  exact mul_nonneg (by positivity) (mul_nonneg hC (Real.sqrt_nonneg _))

theorem HighContrastCorrectorPackage.pairingAmplitude_eq
    (pk : HighContrastCorrectorPackage hK P κ C) (b : CoeffSpace d) (e : Vec d) (N : ℕ) :
    pk.pairingAmplitude b e N =
      pk.pairingConstant e * ((Real.sqrt d * (3 : ℝ) ^ N) / pk.X b) ^ (-κ) := by
  unfold HighContrastCorrectorPackage.pairingAmplitude HighContrastCorrectorPackage.pairingConstant
  ring

theorem HighContrastCorrectorPackage.pairingAmplitude_le [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) (hκ : 0 < κ) (hC : 0 ≤ C) (b : CoeffSpace d)
    (e : Vec d) {N : ℕ} (hNX : pk.X b ≤ Real.sqrt d * (3 : ℝ) ^ N) :
    pk.pairingAmplitude b e N ≤ pk.pairingConstant e := by
  rw [pk.pairingAmplitude_eq]
  have hX : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
  have h1 : 1 ≤ (Real.sqrt d * (3 : ℝ) ^ N) / pk.X b := by rw [le_div_iff₀ hX]; linarith
  have h2 : ((Real.sqrt d * (3 : ℝ) ^ N) / pk.X b) ^ (-κ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
  have h3 := pk.pairingConstant_nonneg hC e
  calc pk.pairingConstant e * ((Real.sqrt d * (3 : ℝ) ^ N) / pk.X b) ^ (-κ)
      ≤ pk.pairingConstant e * 1 := mul_le_mul_of_nonneg_left h2 h3
    _ = pk.pairingConstant e := mul_one _

theorem exists_sqrt_mul_three_pow_ge [NeZero d] (X : ℝ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → X ≤ Real.sqrt d * (3 : ℝ) ^ N := by
  obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt X (by norm_num : (1 : ℝ) < 3)
  refine ⟨N₀, fun N hN => ?_⟩
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hsd : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1
  have h3 : (3 : ℝ) ^ N₀ ≤ (3 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
  have h3N : (0 : ℝ) ≤ (3 : ℝ) ^ N := by positivity
  nlinarith

/-- **Energy bound for high-contrast correctors.** On the event of the homogenization theorem,
the corrector of every direction has bounded energy on all large origin cubes. -/
theorem HighContrastCorrectorPackage.exists_energy_bound_of_mem [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) (hκ : 0 < κ) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d) :
    ∃ (Ē : ℝ) (n₂ : ℕ), 0 ≤ Ē ∧ ∀ n, n₂ ≤ n →
      cubeAverage (originCube d (n : ℤ))
        (fun x => vecNormSq ((pk.wholeSpaceSolution hb hbell e).correctorGrad e x)) ≤ Ē := by
  obtain ⟨CE, hCE, n₁, hE⟩ := exists_energy_bound d K hK
  obtain ⟨N₀, hN₀⟩ := exists_sqrt_mul_three_pow_ge (d := d) (pk.X b)
  obtain ⟨ρ, Cg, Ng, hρ, hρ2, hCg, hgrowth⟩ := pk.exists_cube_growth hb hbell e
  have hcμ := ballVolumeConstant_nonneg d
  have hδ := pk.pairingConstant_nonneg hC e
  refine ⟨CE * (vecNormSq e + (1 + ballVolumeConstant d) ^ 2 * pk.pairingConstant e ^ 2),
    max N₀ n₁, by have := vecNormSq_nonneg e; positivity, ?_⟩
  intro n hn
  refine hE (pk.wholeSpaceSolution hb hbell e) e (pk.pairingConstant e) (ballVolumeConstant d)
    hδ hcμ N₀ (fun N hN m _ => ?_) ρ Cg Ng hρ hρ2 hCg hgrowth n hn
  exact EllipticWholeSpaceSolution.PairingBound.mono _ hcμ
    (pk.pairingAmplitude_le hκ hC b e (hN₀ N hN)) (pk.pairingBound hC hb hbell e (hN₀ N hN) m)

theorem inv_pow_rpow_half_sq (κ : ℝ) (L : ℕ) :
    (((3 : ℝ) ^ (κ / 2)) ^ L)⁻¹ ^ 2 = ((3 : ℝ) ^ L) ^ (-κ) := by
  rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast ((3 : ℝ)) L,
    ← Real.rpow_mul (by norm_num), inv_pow, ← Real.rpow_natCast (_ ^ _) 2,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by positivity)]
  congr 1
  push_cast
  ring

theorem exists_three_pow_le_rpow_pow {κ : ℝ} (hκ : 0 < κ) (d : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ (3 : ℝ) ^ (6 + d) ≤ ((3 : ℝ) ^ (κ / 2)) ^ (2 * q) := by
  refine ⟨⌈((6 + d : ℕ) : ℝ) / κ⌉₊ + 1, by omega, ?_⟩
  set q := ⌈((6 + d : ℕ) : ℝ) / κ⌉₊ + 1
  have hq : ((6 + d : ℕ) : ℝ) ≤ κ * q := by
    have h1 : ((6 + d : ℕ) : ℝ) / κ ≤ ⌈((6 + d : ℕ) : ℝ) / κ⌉₊ := Nat.le_ceil _
    have h2 : (⌈((6 + d : ℕ) : ℝ) / κ⌉₊ : ℝ) ≤ q := by
      simp only [q]
      push_cast
      linarith
    rw [div_le_iff₀ hκ] at h1
    nlinarith
  rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  push_cast at hq ⊢
  linarith

/-- **Sublinearity of high-contrast correctors.** On the event of the homogenization theorem,
the oscillation of the corrector of every direction on the origin cube of side `3ᴺ` is
`o(3ᴺ)`. -/
theorem HighContrastCorrectorPackage.tendsto_oscillation_div [NeZero d]
    (pk : HighContrastCorrectorPackage hK P κ C) (hκ : 0 < κ) (hC : 0 ≤ C) {b : CoeffSpace d}
    (hb : b ∈ pk.Ωend)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 K (b.1 x)) (e : Vec d) :
    Tendsto (fun N : ℕ => cubeBesovOscillation (originCube d (N : ℤ)) 2
      ((pk.wholeSpaceSolution hb hbell e).corrector e) / (3 : ℝ) ^ N) atTop (𝓝 0) := by
  obtain ⟨C₀, hC₀, hdecay⟩ := exists_oscillation_decay d
  obtain ⟨Ē, n₂, hĒ, hE⟩ := pk.exists_energy_bound_of_mem hκ hC hb hbell e
  obtain ⟨N₀, hN₀⟩ := exists_sqrt_mul_three_pow_ge (d := d) (pk.X b)
  obtain ⟨q, hq1, hq⟩ := exists_three_pow_le_rpow_pow hκ d
  set γ := (3 : ℝ) ^ (κ / 2) with hγ
  have hγ1 : 1 < γ := Real.one_lt_rpow (by norm_num) (by positivity)
  set n₀ := max N₀ n₂
  set D := pk.pairingConstant e
  have hD := pk.pairingConstant_nonneg hC e
  have hcμ := ballVolumeConstant_nonneg d
  set g : ℕ → ℝ := fun L => C₀ * (Real.sqrt Ē * (((3 : ℝ) ^ (n₀ + L))⁻¹ +
    5 / 4 * ((3 : ℝ) ^ (L / q))⁻¹) + 16 * (1 + ballVolumeConstant d) * D * (γ ^ L)⁻¹)
  have hbound : ∀ L : ℕ, cubeBesovOscillation (originCube d ((n₀ + L : ℕ) : ℤ)) 2
      ((pk.wholeSpaceSolution hb hbell e).corrector e) / (3 : ℝ) ^ (n₀ + L) ≤ g L := by
    intro L
    have hX : pk.X b ≤ Real.sqrt d * (3 : ℝ) ^ (n₀ + L) := hN₀ _ (by omega)
    have hpair : ∀ m ≤ n₀ + L, (pk.wholeSpaceSolution hb hbell e).PairingBound e
        (D * (γ ^ L)⁻¹ ^ 2) (ballVolumeConstant d) (n₀ + L) m := by
      intro m _
      refine EllipticWholeSpaceSolution.PairingBound.mono _ hcμ ?_
        (pk.pairingBound hC hb hbell e hX m)
      rw [pk.pairingAmplitude_eq, hγ, inv_pow_rpow_half_sq]
      refine mul_le_mul_of_nonneg_left ?_ hD
      have hXpos : 0 < pk.X b := lt_of_lt_of_le one_pos (pk.one_le_X b)
      have hsplit : (Real.sqrt d * (3 : ℝ) ^ (n₀ + L)) / pk.X b =
          ((Real.sqrt d * (3 : ℝ) ^ n₀) / pk.X b) * (3 : ℝ) ^ L := by
        rw [pow_add]
        ring
      have hbase : 1 ≤ (Real.sqrt d * (3 : ℝ) ^ n₀) / pk.X b := by
        rw [le_div_iff₀ hXpos, one_mul]
        exact hN₀ _ (le_max_left _ _)
      rw [hsplit, Real.mul_rpow (by positivity) (by positivity)]
      have h1 : ((Real.sqrt d * (3 : ℝ) ^ n₀) / pk.X b) ^ (-κ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
      have h2 : 0 ≤ ((3 : ℝ) ^ L) ^ (-κ) := Real.rpow_nonneg (by positivity) _
      calc ((Real.sqrt d * (3 : ℝ) ^ n₀) / pk.X b) ^ (-κ) * ((3 : ℝ) ^ L) ^ (-κ)
          ≤ 1 * ((3 : ℝ) ^ L) ^ (-κ) := mul_le_mul_of_nonneg_right h1 h2
        _ = ((3 : ℝ) ^ L) ^ (-κ) := one_mul _
    have h := hdecay (pk.wholeSpaceSolution hb hbell e) e (ballVolumeConstant d) Ē D γ q n₀ L
      hcμ hĒ hD hγ1.le hq1 hq hpair (hE _ (by omega))
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (n₀ + L) := by positivity
    rw [div_le_iff₀ h3]
    calc _ ≤ _ := h
      _ = g L * (3 : ℝ) ^ (n₀ + L) := by simp only [g]; ring
  have hg : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℕ => ((3 : ℝ) ^ (n₀ + L))⁻¹) atTop (𝓝 0) := by
      refine tendsto_inv_atTop_zero.comp ?_
      refine (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).comp ?_
      exact tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
    have h2 : Tendsto (fun L : ℕ => ((3 : ℝ) ^ (L / q))⁻¹) atTop (𝓝 0) := by
      refine tendsto_inv_atTop_zero.comp ?_
      refine (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).comp ?_
      exact Nat.tendsto_div_const_atTop (by omega)
    have h3 : Tendsto (fun L : ℕ => (γ ^ L)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hγ1)
    have := ((h1.add (h2.const_mul (5 / 4))).const_mul (Real.sqrt Ē)).add
      (h3.const_mul (16 * (1 + ballVolumeConstant d) * D))
    have := this.const_mul C₀
    simpa [g] using this
  have hosc0 : ∀ L : ℕ, 0 ≤ cubeBesovOscillation (originCube d ((n₀ + L : ℕ) : ℤ)) 2
      ((pk.wholeSpaceSolution hb hbell e).corrector e) / (3 : ℝ) ^ (n₀ + L) :=
    fun L => div_nonneg (cubeLpNorm_nonneg _ _ _) (by positivity)
  have hshift := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg hosc0 hbound
  rw [← Filter.tendsto_add_atTop_iff_nat n₀]
  refine hshift.congr fun L => ?_
  rw [add_comm L n₀]

end Package

end EinsteinFull.Homogenization
