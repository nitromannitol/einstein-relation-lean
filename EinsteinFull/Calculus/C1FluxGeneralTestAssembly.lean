import EinsteinFull.Calculus.CarverSFluxGeneralTestGain

open scoped BigOperators
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The zeroth and coordinate first derivative estimates, factored into their
Gaussian and derivative-order scales. -/
theorem c1_gaussian_test_value_coordinate (d : ℕ) (ctest : ℝ) (Btest : ℕ → ℝ)
    (s : ℝ) (hs : 0 < s) (k : ℕ) (ψ : SchwartzMap (Vec d) ℂ)
    (hψ : HasGaussianTestControl s k ctest Btest ψ) (x : Vec d) :
    let E := s ^ (-(d : ℝ) / 2) * Real.exp (-ctest * euclideanNorm x ^ 2 / s)
    ‖ψ x‖ ≤ Btest 0 * s ^ (-(k : ℝ) / 2) * E ∧
    ∀ j : Fin d, ‖fderiv ℝ (fun y => ψ y) x (unitVector j)‖ ≤
      Btest 1 * s ^ (-((k + 1 : ℕ) : ℝ) / 2) * E := by
  dsimp only
  have hpow (q : ℕ) :
      s ^ (-(d : ℝ) / 2 - ((q + k : ℕ) : ℝ) / 2) =
        s ^ (-((q + k : ℕ) : ℝ) / 2) * s ^ (-(d : ℝ) / 2) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  constructor
  · have h := hψ 0 (fun i => Fin.elim0 i) x
    rw [hpow 0] at h
    simp only [iteratedFDeriv_zero_apply, Nat.zero_add] at h
    convert h using 1 <;> ring
  · intro j
    have h := hψ 1 (fun _ => j) x
    rw [hpow 1] at h
    simp only [iteratedFDeriv_one_apply, Nat.add_comm 1 k] at h
    convert h using 1 <;> ring

/-- The Gaussian supremum is finite and controls every point of the ball. -/
theorem c1_gaussian_ball_sup {d : ℕ} (s c ρ : ℝ) (hs : 0 < s)
    (hc : 0 < c) (hρ : 0 ≤ ρ) (z : Vec d) :
    let G := fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-c * euclideanNorm y ^ 2 / s)
    let B := {y : Vec d | euclideanNorm (y - z) ≤ ρ}
    0 ≤ sSup (G '' B) ∧ ∀ y ∈ B, G y ≤ sSup (G '' B) := by
  intro G B
  have hG (y : Vec d) : 0 ≤ G y := by dsimp [G]; positivity
  have hb : BddAbove (G '' B) := by
    refine ⟨s ^ (-(d : ℝ) / 2), ?_⟩
    rintro a ⟨y, _, rfl⟩
    dsimp only [G]
    have hexp : Real.exp (-c * euclideanNorm y ^ 2 / s) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _)) hs.le
    exact mul_le_of_le_one_right (Real.rpow_nonneg hs.le _) hexp
  have hz : z ∈ B := by
    simpa [B, euclideanNorm, euclideanSq, dot] using hρ
  exact ⟨(hG z).trans (le_csSup hb ⟨z, hz, rfl⟩),
    fun y hy => le_csSup hb ⟨y, hy, rfl⟩⟩

/-- On the cutoff ball, the translated test has the same Gaussian envelope
as the supremum centered at the translation point. -/
theorem c1_gaussian_test_shifted_ball {d : ℕ} (s c ρ : ℝ) (hs : 0 < s)
    (hc : 0 < c) (hρ : 0 ≤ ρ) (B : ℕ → ℝ) (hB : ∀ q, 0 < B q)
    (k : ℕ) (ψ : SchwartzMap (Vec d) ℂ)
    (hψ : HasGaussianTestControl s k c B ψ) (z w : Vec d)
    (hw : euclideanNorm w ≤ ρ) :
    let W := sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-c * euclideanNorm y ^ 2 / s)) ''
        {y : Vec d | euclideanNorm (y - z) ≤ ρ})
    ‖ψ (-(w + z))‖ ≤ B 0 * s ^ (-(k : ℝ) / 2) * W ∧
    ∀ j : Fin d, ‖fderiv ℝ (fun y => ψ y) (-(w + z)) (unitVector j)‖ ≤
      B 1 * s ^ (-((k + 1 : ℕ) : ℝ) / 2) * W := by
  dsimp only
  have hsup := c1_gaussian_ball_sup s c ρ hs hc hρ z
  have hmem : w + z ∈ {y : Vec d | euclideanNorm (y - z) ≤ ρ} := by
    change euclideanNorm ((w + z) - z) ≤ ρ
    simpa only [add_sub_cancel_right] using hw
  have hle := hsup.2 (w + z) hmem
  have hv := c1_gaussian_test_value_coordinate d c B s hs k ψ hψ (-(w + z))
  simp only [Entropy.euclideanNorm_neg'] at hv
  constructor
  · exact hv.1.trans (mul_le_mul_of_nonneg_left hle
      (mul_nonneg (hB 0).le (Real.rpow_nonneg hs.le _)))
  · intro j
    exact (hv.2 j).trans (mul_le_mul_of_nonneg_left hle
      (mul_nonneg (hB 1).le (Real.rpow_nonneg hs.le _)))

/-- A translated reflection changes the sign of a coordinate derivative. -/
theorem c1_schwartz_reflected_shift_deriv {d : ℕ} (ψ : SchwartzMap (Vec d) ℂ)
    (z w : Vec d) (j : Fin d) :
    fderiv ℝ (fun u : Vec d => ψ (-(u + z))) w (unitVector j) =
      -fderiv ℝ (fun u => ψ u) (-(w + z)) (unitVector j) := by
  have hshift : DifferentiableAt ℝ (fun u : Vec d => -(u + z)) w :=
    differentiableAt_id.add_const z |>.neg
  rw [fderiv_fun_comp w ((ψ.smooth (⊤ : ℕ∞)).differentiable (by simp)).differentiableAt
    hshift]
  have hd : fderiv ℝ (fun u : Vec d => -(u + z)) w =
      -ContinuousLinearMap.id ℝ (Vec d) :=
    ((hasFDerivAt_id w).add_const z).neg.fderiv
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply, map_neg]

/-- Pointwise product bounds for the canonical cutoff and a reflected test. -/
theorem c1_cutoff_reflected_local {d : ℕ} (r : ℝ) (hr : 0 < r)
    (ψ : SchwartzMap (Vec d) ℂ) (z w : Vec d) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hv : ‖ψ (-(w + z))‖ ≤ A)
    (hd : ∀ j : Fin d, ‖fderiv ℝ (fun x => ψ x) (-(w + z)) (unitVector j)‖ ≤ B) :
    let f : Vec d → ℂ := fun x => (fluxPartitionCutoff r x : ℂ) * ψ (-(x + z))
    ‖f w‖ ≤ A ∧
      Real.sqrt (∑ j : Fin d, ‖fderiv ℝ f w (unitVector j)‖ ^ 2) ≤
        Real.sqrt (d : ℝ) * (B + A / r) := by
  let χ : Vec d → ℂ := fun x => (fluxPartitionCutoff r x : ℂ)
  let g : Vec d → ℂ := fun x => ψ (-(x + z))
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ :=
    Complex.ofRealCLM.contDiff.comp (flux_partition_cutoff_contDiff r)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    (ψ.smooth (⊤ : ℕ∞)).comp ((contDiff_id.add contDiff_const).neg)
  have hχval : ‖χ w‖ ≤ 1 := by
    dsimp only [χ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (flux_partition_cutoff_nonneg r w)]
    exact flux_partition_cutoff_le_one r w
  have hχder (j : Fin d) : ‖fderiv ℝ χ w (unitVector j)‖ ≤ 1 / r := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp w
      (((flux_partition_cutoff_contDiff r).differentiable (by norm_num) w).hasFDerivAt)
    change ‖fderiv ℝ (Complex.ofRealCLM ∘ fluxPartitionCutoff r) w (unitVector j)‖ ≤ _
    rw [h.fderiv]
    change ‖((fderiv ℝ (fluxPartitionCutoff r) w (unitVector j) : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact flux_partition_cutoff_coord_deriv_le hr w j
  change ‖χ w * g w‖ ≤ A ∧
    Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun x => χ x * g x) w (unitVector j)‖ ^ 2) ≤ _
  constructor
  · rw [norm_mul]
    exact (mul_le_mul hχval hv (norm_nonneg _) zero_le_one).trans (by simp)
  · have hcoord (j : Fin d) :
        ‖fderiv ℝ (fun x => χ x * g x) w (unitVector j)‖ ≤ B + A / r := by
      rw [fderiv_fun_mul ((hχ.differentiable (by norm_num)) w)
        ((hg.differentiable (by norm_num)) w)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      calc
        _ ≤ ‖χ w * fderiv ℝ g w (unitVector j)‖ +
            ‖g w * fderiv ℝ χ w (unitVector j)‖ := norm_add_le _ _
        _ = ‖χ w‖ * ‖fderiv ℝ g w (unitVector j)‖ +
            ‖g w‖ * ‖fderiv ℝ χ w (unitVector j)‖ := by rw [norm_mul, norm_mul]
        _ ≤ 1 * B + A * (1 / r) := by
          apply add_le_add
          · apply mul_le_mul hχval _ (norm_nonneg _) zero_le_one
            simpa only [g, c1_schwartz_reflected_shift_deriv, norm_neg] using hd j
          · exact mul_le_mul hv (hχder j) (norm_nonneg _) hA
        _ = B + A / r := by ring
    exact c3_complex_coordinate_length_le _ _ (add_nonneg hB (div_nonneg hA hr.le)) hcoord

/-- Uniform value and gradient bounds for the actual compact Schwartz block. -/
theorem c1_flux_compact_schwartz_block_value_gradient (d : ℕ) (ctest : ℝ)
    (hc : 0 < ctest) (Btest : ℕ → ℝ) (hB : ∀ q, 0 < Btest q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s r : ℝ), 0 < s → 0 < r →
    ∀ (k : ℕ) (ψ : SchwartzMap (Vec d) ℂ), HasGaussianTestControl s k ctest Btest ψ →
    ∀ z : Vec d,
    let R := 2 * Real.sqrt (d : ℝ) + 2
    let f : Vec d → ℂ := fun w => (fluxPartitionCutoff r w : ℂ) * ψ (-(w+z))
    let W := sSup ((fun y : Vec d => s ^ (-(d : ℝ)/2) *
      Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
        {y : Vec d | euclideanNorm (y-z) ≤ R*r})
    (∀ w, ‖f w‖ ≤ C * s ^ (-(k : ℝ)/2) * W) ∧
      (∀ w, Real.sqrt (∑ j : Fin d, ‖fderiv ℝ f w (unitVector j)‖ ^ 2) ≤
        C * ((R/r) * s ^ (-(k : ℝ)/2) + s ^ (-((k+1 : ℕ) : ℝ)/2)) * W) := by
  let C : ℝ := (1 + Btest 0 + Btest 1) * (1 + Real.sqrt (d : ℝ))
  have hB0 := hB 0
  have hB1 := hB 1
  have hd : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hC : 0 < C := by dsimp [C]; positivity
  have hc0 : Btest 0 ≤ C := by dsimp [C]; nlinarith [mul_nonneg hB0.le hd, mul_nonneg hB1.le hd]
  have hc1 : Real.sqrt (d : ℝ) * Btest 0 ≤ C := by
    dsimp [C]; nlinarith [mul_nonneg hB1.le hd]
  have hc2 : Real.sqrt (d : ℝ) * Btest 1 ≤ C := by
    dsimp [C]; nlinarith [mul_nonneg hB0.le hd]
  refine ⟨C, hC, ?_⟩
  intro s r hs hr k ψ hψ z
  dsimp only
  let R : ℝ := 2 * Real.sqrt (d : ℝ) + 2
  let f : Vec d → ℂ := fun w => (fluxPartitionCutoff r w : ℂ) * ψ (-(w + z))
  let W : ℝ := sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
    Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
      {y : Vec d | euclideanNorm (y - z) ≤ R * r})
  let S : ℝ := s ^ (-(k : ℝ) / 2)
  let T : ℝ := s ^ (-((k + 1 : ℕ) : ℝ) / 2)
  change (∀ w, ‖f w‖ ≤ C * S * W) ∧
    (∀ w, Real.sqrt (∑ j : Fin d, ‖fderiv ℝ f w (unitVector j)‖ ^ 2) ≤
      C * ((R / r) * S + T) * W)
  have hR : 1 ≤ R := by dsimp [R]; linarith
  have hρ : 0 ≤ R * r := mul_nonneg (le_trans zero_le_one hR) hr.le
  have hW : 0 ≤ W := (c1_gaussian_ball_sup s ctest (R * r) hs hc hρ z).1
  have hS : 0 ≤ S := (Real.rpow_pos_of_pos hs _).le
  have hT : 0 ≤ T := (Real.rpow_pos_of_pos hs _).le
  have hcoef : Real.sqrt (d : ℝ) * Btest 0 ≤ C * R :=
    hc1.trans (le_mul_of_one_le_right hC.le hR)
  have hfs : Function.support f ⊆ {w : Vec d | euclideanNorm w ≤ R * r} := by
    intro w hw
    apply flux_partition_cutoff_support hr
    intro hzero
    apply hw
    simp [f, hzero]
  have hout (w : Vec d) (hw : ¬ euclideanNorm w ≤ R * r) :
      f w = 0 ∧ ∀ j : Fin d, fderiv ℝ f w (unitVector j) = 0 := by
    constructor
    · apply Function.notMem_support.mp
      intro h
      exact hw (hfs h)
    · intro j
      apply Function.notMem_support.mp
      intro h
      exact hw (c3_fderiv_support_euclidean_ball f (R * r) hfs (unitVector j) h)
  have hlocal (w : Vec d) (hw : euclideanNorm w ≤ R * r) :
      ‖f w‖ ≤ Btest 0 * S * W ∧
      Real.sqrt (∑ j : Fin d, ‖fderiv ℝ f w (unitVector j)‖ ^ 2) ≤
        Real.sqrt (d : ℝ) * (Btest 1 * T * W + (Btest 0 * S * W) / r) := by
    have h := c1_gaussian_test_shifted_ball s ctest (R * r) hs hc hρ Btest hB k ψ hψ z w hw
    exact c1_cutoff_reflected_local r hr ψ z w (Btest 0 * S * W) (Btest 1 * T * W)
      (by positivity) (by positivity) h.1 h.2
  constructor
  · intro w
    by_cases hw : euclideanNorm w ≤ R * r
    · exact (hlocal w hw).1.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc0 hS) hW)
    · rw [(hout w hw).1, norm_zero]
      positivity
  · intro w
    by_cases hw : euclideanNorm w ≤ R * r
    · apply (hlocal w hw).2.trans
      have ha := mul_le_mul_of_nonneg_right hcoef (div_nonneg hS hr.le)
      have hb := mul_le_mul_of_nonneg_right hc2 hT
      have hh := mul_le_mul_of_nonneg_right (add_le_add hb ha) hW
      convert hh using 1 <;> field_simp [ne_of_gt hr] <;> ring
    · have hz := (hout w hw).2
      have hz' (j : Fin d) : ‖fderiv ℝ f w (unitVector j)‖ ^ 2 = 0 := by
        rw [hz j, norm_zero]
        norm_num
      simp only [hz', Finset.sum_const_zero, Real.sqrt_zero]
      positivity

/-- Lowering the decay exponents enlarges the radius-time envelope. -/
theorem c1_flux_gain_envelope_mono (r t κ κ' η η' : ℝ)
    (hr : 1 ≤ r) (ht : 1 ≤ t) (hrt : r ≤ Real.sqrt t)
    (hκ : κ' ≤ κ) (hη : η' ≤ η) :
    r ^ κ * t ^ (-κ / 2) * t ^ (-η) ≤
      r ^ κ' * t ^ (-κ' / 2) * t ^ (-η') := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hratio : r / Real.sqrt t ≤ 1 := (div_le_one hs).2 hrt
  have hid (a : ℝ) : r ^ a * t ^ (-a / 2) = (r / Real.sqrt t) ^ a := by
    have hp : t ^ (-a / 2) = (Real.sqrt t ^ a)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le, ← Real.rpow_neg ht0.le]
      congr 1 <;> ring
    rw [hp, Real.div_rpow hr0.le hs.le, div_eq_mul_inv]
  rw [hid κ, hid κ']
  exact mul_le_mul
    (Real.rpow_le_rpow_of_exponent_ge (div_pos hr0 hs) hratio hκ)
    (Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg hη))
    (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg (div_pos hr0 hs).le _)

/-- Two positive exponent pairs admit a common positive envelope. -/
theorem c1_flux_gain_envelope_common (κ₁ κ₂ η₁ η₂ : ℝ)
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) :
    ∃ κ η : ℝ, 0 < κ ∧ 0 < η ∧
      ∀ r t : ℝ, 1 ≤ r → 1 ≤ t → r ≤ Real.sqrt t →
        (r ^ κ₁ * t ^ (-κ₁ / 2) * t ^ (-η₁) ≤
          r ^ κ * t ^ (-κ / 2) * t ^ (-η)) ∧
        (r ^ κ₂ * t ^ (-κ₂ / 2) * t ^ (-η₂) ≤
          r ^ κ * t ^ (-κ / 2) * t ^ (-η)) := by
  refine ⟨min κ₁ κ₂, min η₁ η₂, lt_min hκ₁ hκ₂, lt_min hη₁ hη₂, ?_⟩
  intro r t hr ht hrt
  exact ⟨c1_flux_gain_envelope_mono r t κ₁ _ η₁ _ hr ht hrt (min_le_left _ _) (min_le_left _ _),
    c1_flux_gain_envelope_mono r t κ₂ _ η₂ _ hr ht hrt (min_le_right _ _) (min_le_right _ _)⟩

/-- The minima of two positive exponent pairs give a common envelope. -/
theorem c1_flux_gain_common_positive_exponents (κ₁ κ₂ η₁ η₂ : ℝ)
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) :
    let κ := min κ₁ κ₂
    let η := min η₁ η₂
    0 < κ ∧ 0 < η ∧ ∀ r t : ℝ, 1 ≤ r → 1 ≤ t → r ≤ Real.sqrt t →
    (r ^ κ₁ * t ^ (-κ₁ / 2) * t ^ (-η₁) ≤ r ^ κ * t ^ (-κ / 2) * t ^ (-η)) ∧
    (r ^ κ₂ * t ^ (-κ₂ / 2) * t ^ (-η₂) ≤ r ^ κ * t ^ (-κ / 2) * t ^ (-η)) := by
  refine ⟨lt_min hκ₁ hκ₂, lt_min hη₁ hη₂, ?_⟩
  intro r t hr ht hrt
  exact ⟨c1_flux_gain_envelope_mono r t κ₁ _ η₁ _ hr ht hrt (min_le_left _ _) (min_le_left _ _),
    c1_flux_gain_envelope_mono r t κ₂ _ η₂ _ hr ht hrt (min_le_right _ _) (min_le_right _ _)⟩


/-- At the actual block radius, the envelope is ordered by its joint exponent. -/
theorem c1_flux_actual_radius_envelope_mono
    (t κ₁ κ₂ η σ₁ σ₂ : ℝ) (ht : 1 ≤ t)
    (hbudget : η * κ₁ - σ₁ ≤ η * κ₂ - σ₂) :
    (t ^ (1/2 + η)) ^ κ₁ * t ^ (-κ₁/2) * t ^ (-σ₁) ≤
      (t ^ (1/2 + η)) ^ κ₂ * t ^ (-κ₂/2) * t ^ (-σ₂) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hid (κ σ : ℝ) :
      (t ^ (1/2 + η)) ^ κ * t ^ (-κ/2) * t ^ (-σ) =
        t ^ (η * κ - σ) := by
    rw [← Real.rpow_mul ht0.le, ← Real.rpow_add ht0,
      ← Real.rpow_add ht0]
    congr 1 <;> ring
  rw [hid κ₁ σ₁, hid κ₂ σ₂]
  exact Real.rpow_le_rpow_of_exponent_le ht hbudget

/-- A common structural exponent satisfies the frozen gain budgets. -/
theorem c1_flux_gain_common_structural_budget
    (d : ℕ) (κb κp : ℝ) (hκb : 0 < κb) (hκbhalf : κb < 1 / 2)
    (hκp : 0 < κp) :
    let κ := min κb κp
    let η := κ / (16 * ((d : ℝ) + 2))
    let η₀ := η / 4
    let ε := κ / 8
    0 < κ ∧ κ < 1 / 2 ∧ 0 < η₀ ∧ 0 < ε ∧
      κ ≤ κb ∧ κ ≤ κp ∧
      -1 - κ / 2 + η * ((d : ℝ) + 1 - κ) ≤ -1 - κ / 4 ∧
      ∀ t : ℝ, 1 ≤ t →
        t ^ (-1 - κb / 2 + η * ((d : ℝ) + 1 - κb)) ≤ t ^ (-1 - ε) := by
  dsimp only
  let κ := min κb κp
  let η := κ / (16 * ((d : ℝ) + 2))
  have hk : 0 < κ := lt_min hκb hκp
  have hkb : κ ≤ κb := min_le_left _ _
  have hkp : κ ≤ κp := min_le_right _ _
  have hkh : κ < 1 / 2 := lt_of_le_of_lt hkb hκbhalf
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hden : 0 < 16 * ((d : ℝ) + 2) := by positivity
  have he : 0 < η := div_pos hk hden
  have heb : η * ((d : ℝ) + 1) ≤ κ / 16 := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 16)).2
    nlinarith
  change 0 < κ ∧ κ < 1 / 2 ∧ 0 < η / 4 ∧ 0 < κ / 8 ∧
    κ ≤ κb ∧ κ ≤ κp ∧
    -1 - κ / 2 + η * ((d : ℝ) + 1 - κ) ≤ -1 - κ / 4 ∧
    ∀ t : ℝ, 1 ≤ t →
      t ^ (-1 - κb / 2 + η * ((d : ℝ) + 1 - κb)) ≤ t ^ (-1 - κ / 8)
  refine ⟨hk, hkh, by positivity, by positivity, hkb, hkp, ?_, ?_⟩
  · nlinarith [mul_nonneg he.le hk.le]
  · intro t ht
    apply Real.rpow_le_rpow_of_exponent_le ht
    nlinarith [mul_nonneg he.le hκb.le]

end EinsteinFull.Blueprint
