import EinsteinFull.Calculus.C6FluxActualRecoveryBudget
import EinsteinFull.Calculus.C3FluxActualSiteLpTransfer
import EinsteinFull.Calculus.C1FluxActualSiteCETransfer
import EinsteinFull.Calculus.C3FluxGeneralTestTransfer

open MeasureTheory EinsteinRelation EinsteinFull

namespace EinsteinFull.Blueprint

/-- The single-block estimate at the Gaussian recovery scale `r ^ 2`, for every
admissible cutoff, both for the block and for its residual after conditioning
on `m`: the input of the cutoff-Schwartz site assembly. -/
def FluxSiteOracle {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (J : Lp ℂ 2 (reducedLaw Q)) (q : ENNReal) (r : ℝ) (hr : 0 < r) (zc : Vec d)
    (i j : Fin d) (m : MeasurableSpace (FieldPair d)) (Qm Qr : ℝ) : Prop :=
  ∀ θ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ →
    Function.support θ ⊆ {w : Vec d | euclideanNorm w ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} →
    (∀ w, |θ w| ≤ 1) →
    (∀ w, Real.sqrt (∑ l : Fin d, (fderiv ℝ θ w (unitVector l)) ^ 2) ≤
      (2 * Real.sqrt (d : ℝ) + 2) / r) →
    (∀ y, HasSum (fun z : Fin d → ℤ => θ (y - fun l => r * (z l : ℝ))) 1) →
    ∀ b : Bool,
      let B₀ := fun ξ : Vec d → ℝ => centeredComplexLp Q (∫ y : Vec d,
        ((ξ (y - zc) : ℂ) * homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0
          (zc - y)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
      let B₁ := fun ξ : Vec d → ℝ => centeredComplexLp Q (∫ y : Vec d,
        ((ξ (y - zc) : ℂ) * fderiv ℝ
          (homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0)
          (zc - y) (unitVector j)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
      let E0 : Bool → ℝ := fun b => if b then r ^ (-(d : ℝ)) else r ^ (-(d : ℝ) - 1)
      let U : FieldPair d → ℂ := if b then B₀ θ else B₁ θ
      MemLp U q (reducedLaw Q) ∧
        (eLpNorm U q (reducedLaw Q)).toReal ≤ Qm * E0 b ∧
        MemLp (U - (reducedLaw Q)[U | m]) q (reducedLaw Q) ∧
        (eLpNorm (U - (reducedLaw Q)[U | m]) q (reducedLaw Q)).toReal ≤ Qr * E0 b

/-- One cutoff-Schwartz site is controlled by the eight admissible Gaussian
blocks, with the recovery normalizations absorbed into a single constant. -/
theorem c1_schwartz_site_assembly (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (ctest : ℝ) (hctest : 0 < ctest) (Btest : ℕ → ℝ) (hBtest : ∀ q, 0 < Btest q) :
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (J : Lp ℂ 2 (reducedLaw Q)) (q : ENNReal), 1 ≤ q →
      ∀ (s r : ℝ), 0 < s → ∀ (hr : 0 < r) (k : ℕ) (ψ : SchwartzMap (Vec d) ℂ),
        HasGaussianTestControl s k ctest Btest ψ →
      ∀ (zc : Vec d) (i j : Fin d) (m : MeasurableSpace (FieldPair d))
        (Qm Qr : ℝ), 0 ≤ Qm → 0 ≤ Qr → FluxSiteOracle Q J q r hr zc i j m Qm Qr →
      let W := s ^ (-(k : ℝ) / 2) * sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
          {y : Vec d | euclideanNorm (y - zc) ≤ (2 * Real.sqrt (d : ℝ) + 2) * r})
      let F := centeredComplexLp Q (∫ y : Vec d,
        ((fluxPartitionCutoff r (y - zc) : ℂ) * ψ (-y)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
      MemLp (F : FieldPair d → ℂ) q (reducedLaw Q) ∧
      (eLpNorm (F : FieldPair d → ℂ) q (reducedLaw Q)).toReal ≤
        Cb * (1 + r / Real.sqrt s) * Qm * W ∧
      MemLp ((F : FieldPair d → ℂ) - (reducedLaw Q)[(F : FieldPair d → ℂ) | m]) q
        (reducedLaw Q) ∧
      (eLpNorm ((F : FieldPair d → ℂ) - (reducedLaw Q)[(F : FieldPair d → ℂ) | m]) q
        (reducedLaw Q)).toReal ≤ Cb * (1 + r / Real.sqrt s) * Qr * W := by
  obtain ⟨Crec, Csite, hCrec, hCsite, hpart⟩ :=
    c6_actual_schwartz_recovery_admissible_partitions d hd D ctest hctest Btest hBtest
  obtain ⟨Cb, hCb, hbud⟩ :=
    c6_actual_schwartz_recovery_coefficient_budget d Crec Csite hCrec hCsite
  refine ⟨Cb, hCb, ?_⟩
  intro Q J q hq s r hs hr k ψ hψ zc i j m Qm Qr hQm hQr hblk W F
  let B₀ := fun ξ : Vec d → ℝ => centeredComplexLp Q (∫ y : Vec d,
    ((ξ (y - zc) : ℂ) * homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0
      (zc - y)) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
  let B₁ := fun ξ : Vec d → ℝ => centeredComplexLp Q (∫ y : Vec d,
    ((ξ (y - zc) : ℂ) * fderiv ℝ
      (homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0)
      (zc - y) (unitVector j)) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
  let E0 : Bool → ℝ := fun b => if b then r ^ (-(d : ℝ)) else r ^ (-(d : ℝ) - 1)
  have hθ := hpart Q i j s r hs hr k ψ hψ zc
  have hbase := c3_flux_averaged_baseline_partition_admissible r hr j
  dsimp only at hθ hbase
  have hR0 : 0 ≤ (2 * Real.sqrt (d : ℝ) + 2) * r := by positivity
  have hsup := c1_gaussian_ball_sup s ctest ((2 * Real.sqrt (d : ℝ) + 2) * r) hs hctest hR0 zc
  have hz : zc ∈ {y : Vec d | euclideanNorm (y - zc) ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} := by
    simpa [euclideanNorm, euclideanSq, dot] using hR0
  have hE : 0 < sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
        {y : Vec d | euclideanNorm (y - zc) ≤ (2 * Real.sqrt (d : ℝ) + 2) * r}) :=
    lt_of_lt_of_le (by positivity) (hsup.2 zc hz)
  have hWpos : 0 < W := mul_pos (Real.rpow_pos_of_pos hs _) hE
  let baseline : Vec d → ℝ := fun x =>
    (fluxPartitionCutoff r x + fluxPartitionCutoff r (x - r • unitVector j)) / 2
  let M : Bool → ℝ := fun b => 2 * Crec *
    (1 + Csite + Csite * ((2 * Real.sqrt (d : ℝ) + 2) + r * (Real.sqrt s)⁻¹)) *
      (if b then r ^ d else r ^ (d + 1))
  have hMpos (b : Bool) : 0 < M b := by
    have hc : 0 < Crec := lt_of_lt_of_le zero_lt_one hCrec
    dsimp only [M]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity
  let f := fun u : Vec d => (fluxPartitionCutoff r u : ℂ) * ψ (-(u + zc))
  let kernel := homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0
  let slope := fun w : Vec d =>
    ((((homogenizedCoefficient Q)⁻¹).mulVec w j / (r ^ 2) : ℝ) : ℂ)
  let v := r • unitVector j
  let g := fun w : Vec d => f w / (W : ℂ)
  let h := fun w : Vec d => g (w + v) / (slope v * kernel (-(w + v)))
  let δ : Bool → Vec d → ℂ := fun b w => if b then
    slope w * h w - slope (w - v) * h (w - v) else h w - h (w - v)
  let θ : Bool → Bool → Vec d → ℝ := fun b q w => baseline w +
    (if q then (δ b w).im else (δ b w).re) / M b
  have hθ' : ∀ b a, ContDiff ℝ (⊤ : ℕ∞) (θ b a) ∧ HasCompactSupport (θ b a) :=
    fun b a => ⟨(hθ b a).1, (hθ b a).2.1⟩
  have hrec : ∀ y : Vec d, (fluxPartitionCutoff r (y - zc) : ℂ) * ψ (-y) =
      ((W * M true : ℝ) : ℂ) * kernel (-(y - zc)) *
        (((θ true false (y - zc) - baseline (y - zc) : ℝ) : ℂ) +
          Complex.I * ((θ true true (y - zc) - baseline (y - zc) : ℝ) : ℂ)) -
      ((W * M false : ℝ) : ℂ) * fderiv ℝ kernel (-(y - zc)) (unitVector j) *
        (((θ false false (y - zc) - baseline (y - zc) : ℝ) : ℂ) +
          Complex.I * ((θ false true (y - zc) - baseline (y - zc) : ℝ) : ℂ)) :=
    fun y => c3_cutoff_schwartz_site_recovery_split Q i j r W M hr hWpos
      (fun b => (hMpos b).ne') (fluxPartitionCutoff r) ψ zc y baseline
  have hsiteLp := c3_actual_schwartz_site_lp_bound Q i j (r ^ 2) (sq_pos_of_pos hr) zc J
    ((W * M true : ℝ) : ℂ) ((W * M false : ℝ) : ℂ) (fluxPartitionCutoff r) ψ θ baseline
    hθ' hbase.1 hbase.2.1 hrec
  have hsiteCE := c1_actual_schwartz_site_condExp_bound Q i j (r ^ 2) (sq_pos_of_pos hr) zc J
    ((W * M true : ℝ) : ℂ) ((W * M false : ℝ) : ℂ) (fluxPartitionCutoff r) ψ θ baseline
    hθ' hbase.1 hbase.2.1 hrec
  have hU (b a : Bool) := hblk (θ b a) (hθ b a).1 (hθ b a).2.1 (hθ b a).2.2.1
    (hθ b a).2.2.2.1 (hθ b a).2.2.2.2.1 (hθ b a).2.2.2.2.2
  have hB := hblk baseline hbase.1 hbase.2.1 hbase.2.2.1 hbase.2.2.2.1
    hbase.2.2.2.2.1 hbase.2.2.2.2.2
  have key (Q' : ℝ) (hQ' : 0 ≤ Q') :
      (4 * ‖((W * M true : ℝ) : ℂ)‖ * (Q' * E0 true) +
        4 * ‖((W * M false : ℝ) : ℂ)‖ * (Q' * E0 false)) * 1 ≤
        Cb * (1 + r / Real.sqrt s) * Q' * W := by
    have hb := hbud s r ctest hs hr hctest k zc
    dsimp only at hb
    rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (mul_pos hWpos (hMpos true)).le,
      Real.norm_of_nonneg (mul_pos hWpos (hMpos false)).le]
    have := mul_le_mul_of_nonneg_left hb hQ'
    dsimp only [E0, M, W]
    simp only [Bool.false_eq_true, ↓reduceIte] at this ⊢
    linarith [this]
  obtain ⟨hF1, hF2⟩ := hsiteLp q hq (fun b => Qm * E0 b) 1
    (fun b a => (hU b a b).1) (fun b => (hB b).1)
    (fun b a => by simpa only [mul_one] using (hU b a b).2.1)
    (fun b => by simpa only [mul_one] using (hB b).2.1)
  obtain ⟨hG1, hG2⟩ := hsiteCE q hq m (fun b => Qr * E0 b) 1
    (fun b a => (hU b a b).1) (fun b => (hB b).1) (fun b a => (hU b a b).2.2.1)
    (fun b => (hB b).2.2.1)
    (fun b a => by simpa only [mul_one] using (hU b a b).2.2.2)
    (fun b => by simpa only [mul_one] using (hB b).2.2.2)
  exact ⟨hF1, hF2.trans (key Qm hQm), hG1, hG2.trans (key Qr hQr)⟩

/-- The first iterated derivative of a kernel in a coordinate direction. -/
theorem c1_iterated_one_apply {d : ℕ} (f : Vec d → ℂ) (y : Vec d) (j : Fin d) :
    iteratedFDeriv ℝ 1 f y (fun _ => unitVector j) = fderiv ℝ f y (unitVector j) := by
  simp [iteratedFDeriv_one_apply]

/-- The zeroth iterated derivative of a kernel is the kernel. -/
theorem c1_iterated_zero_apply {d : ℕ} (f : Vec d → ℂ) (y : Vec d) (m : Fin 0 → Vec d) :
    iteratedFDeriv ℝ 0 f y m = f y := by
  simp [iteratedFDeriv_zero_apply]

/-- Scalar comparison of a single-block bound with the common site oracle. -/
theorem c1_oracle_scalar (Cd Cm Pl Pm Kb S V E : ℝ) (hCd : 0 ≤ Cd) (hCm : Cd ≤ Cm)
    (hPl : 0 ≤ Pl) (hP : Pl ≤ Pm) (hKb : 0 ≤ Kb) (hS : 0 ≤ S) (hV : 0 ≤ V)
    (hE : V ≤ E) :
    Cd * Pl * Kb * V + Cd * S * V ≤ (Cm * Kb * Pm + Cm * S) * E := by
  have h1 : Cd * Pl ≤ Cm * Pm := mul_le_mul hCm hP hPl (hCd.trans hCm)
  have h2 : Cd * Pl * Kb + Cd * S ≤ Cm * Pm * Kb + Cm * S := by
    have := mul_le_mul_of_nonneg_right h1 hKb
    have := mul_le_mul_of_nonneg_right hCm hS
    linarith
  calc _ = (Cd * Pl * Kb + Cd * S) * V := by ring
    _ ≤ (Cm * Pm * Kb + Cm * S) * E :=
      mul_le_mul h2 hE hV (by
        have hCm0 := hCd.trans hCm
        have hPm0 := hPl.trans hP
        positivity)
    _ = _ := by ring

/-- Scalar comparison of the residual bound with the common site oracle. -/
theorem c1_oracle_scalar_res (Cd Cm S V E : ℝ) (hCm : Cd ≤ Cm) (hS : 0 ≤ S)
    (hV : 0 ≤ V) (hE : V ≤ E) (hCd : 0 ≤ Cd) : Cd * S * V ≤ Cm * S * E :=
  mul_le_mul (mul_le_mul_of_nonneg_right hCm hS) hE hV (mul_nonneg (hCd.trans hCm) hS)

end EinsteinFull.Blueprint
