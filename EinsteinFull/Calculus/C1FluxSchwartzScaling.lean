import EinsteinFull.Calculus.C6IndependentBlocksAssembly
import EinsteinFull.Calculus.C1FluxGeneralTestAssembly
import EinsteinFull.Calculus.CarverSFluxLattice
import EinsteinFull.Calculus.C19FluxActualAnnularBudget

noncomputable section
open MeasureTheory EinsteinRelation
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

/-- A Gaussian envelope over a nonempty ball is at most its prefactor. -/
theorem c1_gaussian_envelope_le_prefactor {d : ℕ} (s C ρ : ℝ)
    (hs : 0 < s) (hC : 0 < C) (hρ : 0 ≤ ρ) (x z : Vec d) :
    sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-euclideanNorm (x - y) ^ 2 / (C * s))) ''
        {y : Vec d | euclideanNorm (y - z) ≤ ρ}) ≤ s ^ (-(d : ℝ) / 2) := by
  apply csSup_le
  · refine ⟨_, ⟨z, ?_, rfl⟩⟩
    simpa [euclideanNorm, euclideanSq, dot] using hρ
  · rintro a ⟨y, hy, rfl⟩
    have hexp : Real.exp (-euclideanNorm (x - y) ^ 2 / (C * s)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (mul_nonneg hC.le hs.le)
    exact mul_le_of_le_one_right (Real.rpow_nonneg hs.le _) hexp


/-- The zeroth and first Gaussian derivative prefactors at the recovery scale. -/
theorem c1_recovery_gaussian_prefactors (d : ℕ) (r : ℝ) (hr : 0 < r) :
    (r ^ 2) ^ (-(d : ℝ) / 2) = r ^ (-(d : ℝ)) ∧
      (r ^ 2) ^ (-(1 : ℝ) / 2) * (r ^ 2) ^ (-(d : ℝ) / 2) =
        r ^ (-(d : ℝ) - 1) := by
  have hpow (a : ℝ) : (r ^ 2) ^ a = r ^ (2 * a) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hr.le]
  constructor
  · convert hpow (-(d : ℝ) / 2) using 1
    congr 1
    ring
  · rw [hpow, hpow, ← Real.rpow_add hr]
    congr 1
    ring


/-- The recovery coefficient's extra length factor has one half-power of
scale inflation and one mesoscopic time power. -/
theorem c1_recovery_length_inflation (η t s : ℝ)
    (hη : 0 ≤ η) (ht : 1 ≤ t) (hs : 1 ≤ s) :
    1 + t ^ (1 / 2 + η) / Real.sqrt s ≤
      2 * t ^ η * Real.sqrt (1 + t / s) := by
  have h := flux_lattice_inflation_le 2 η t s hη ht hs
  norm_num [Real.sqrt_eq_rpow] at h ⊢
  convert h using 1


/-- At the mesoscopic recovery scale, the block time-to-scale ratio is bounded. -/
theorem c1_recovery_scale_ratio_le_two (η t : ℝ) (hη : 0 ≤ η) (ht : 1 ≤ t) :
    1 + t / (t ^ (1 / 2 + η)) ^ 2 ≤ 2 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hscale : t ≤ (t ^ (1 / 2 + η)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    calc
      t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
      _ ≤ t ^ ((1 / 2 + η) * 2) := by
        apply Real.rpow_le_rpow_of_exponent_le ht
        linarith
  have hden : 0 < (t ^ (1 / 2 + η)) ^ 2 := by positivity
  have hratio : t / (t ^ (1 / 2 + η)) ^ 2 ≤ 1 := (div_le_one hden).2 hscale
  linarith


/-- Recovery-scale envelopes have the zeroth- and first-order prefactors
needed for the two normalized Gaussian components. -/
theorem c1_recovery_envelope_prefactors {d : ℕ} (r C ρ : ℝ)
    (hr : 0 < r) (hC : 0 < C) (hρ : 0 ≤ ρ) (x z : Vec d) :
    let E := sSup ((fun y : Vec d => (r ^ 2) ^ (-(d : ℝ) / 2) *
      Real.exp (-euclideanNorm (x - y) ^ 2 / (C * (r ^ 2)))) ''
        {y : Vec d | euclideanNorm (y - z) ≤ ρ})
    E ≤ r ^ (-(d : ℝ)) ∧
      (r ^ 2) ^ (-(1 : ℝ) / 2) * E ≤ r ^ (-(d : ℝ) - 1) := by
  dsimp only
  have h := c1_gaussian_envelope_le_prefactor (r ^ 2) C ρ (sq_pos_of_pos hr) hC hρ x z
  obtain ⟨h₀, h₁⟩ := c1_recovery_gaussian_prefactors d r hr
  constructor
  · simpa only [h₀] using h
  · calc
      _ ≤ (r ^ 2) ^ (-(1 : ℝ) / 2) * (r ^ 2) ^ (-(d : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (sq_nonneg r) _)
      _ = _ := h₁


/-- Increasing the Gaussian decay rate decreases its ball envelope. -/
theorem c1_gaussian_ball_sup_antitone {d : ℕ} (s c₁ c₂ ρ : ℝ)
    (hs : 0 < s) (hc₁ : 0 < c₁) (hc : c₁ ≤ c₂) (hρ : 0 ≤ ρ) (z : Vec d) :
    sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-c₂ * euclideanNorm y ^ 2 / s)) ''
        {y : Vec d | euclideanNorm (y - z) ≤ ρ}) ≤
    sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-c₁ * euclideanNorm y ^ 2 / s)) ''
        {y : Vec d | euclideanNorm (y - z) ≤ ρ}) := by
  have hsup := c1_gaussian_ball_sup s c₁ ρ hs hc₁ hρ z
  apply csSup_le
  · refine ⟨_, ⟨z, ?_, rfl⟩⟩
    simpa [euclideanNorm, euclideanSq, dot] using hρ
  · rintro a ⟨y, hy, rfl⟩
    calc
      _ ≤ s ^ (-(d : ℝ) / 2) * Real.exp (-c₁ * euclideanNorm y ^ 2 / s) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hs.le _)
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ hs.le
        nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg (euclideanNorm y))]
      _ ≤ _ := hsup.2 y hy


/-- The recovery length factor consumes at most half of the available gain. -/
theorem c1_recovery_exponent_margin (d : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    let η := κ / (16 * ((d : ℝ) + 2));
    -1 - κ / 2 + η * ((d : ℝ) + 1 - κ) + η ≤ -1 - κ / 8 := by
  dsimp only
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hden : 0 < 16 * ((d : ℝ) + 2) := by positivity
  have hη : κ / (16 * ((d : ℝ) + 2)) ≤ κ / 8 := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hκ.le hd]
  have hmargin := flux_lattice_exponent_margin d κ hκ
  linarith


/-- The time and scale powers of the recovered finite-family bound combine to
the required gain `t ^ (-1 - κ / 8)`. -/
theorem c1_schwartz_power_budget (d : ℕ) (κ t s Clat : ℝ) (hκ : 0 < κ)
    (ht : 1 ≤ t) (hs : 1 ≤ s) (hClat : 0 ≤ Clat) :
    let η := κ / (16 * ((d : ℝ) + 2))
    let r := t ^ (1 / 2 + η)
    (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) ≤
        Clat * t ^ (η * (d : ℝ) / 2) * (1 + t / s) ^ ((d : ℝ) / 4) →
    t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ) * r ^ (-(d : ℝ) / 2) *
        (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) * (1 + r / Real.sqrt s) ≤
      2 * Clat * t ^ (-1 - κ / 8) * (1 + t / s) ^ ⌈(d : ℝ) / 4 + 1 / 2⌉₊ := by
  intro η r hinfl
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hη : 0 ≤ η := div_nonneg hκ.le (by positivity)
  have hl : 1 ≤ 1 + t / s := by
    have : 0 ≤ t / s := by positivity
    linarith
  have hlen := c1_recovery_length_inflation η t s hη ht hs
  have hmargin := c1_recovery_exponent_margin d κ hκ
  dsimp only at hmargin
  have hexp : t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ) *
      r ^ (-(d : ℝ) / 2) * t ^ (η * (d : ℝ) / 2) * t ^ η =
      t ^ (-1 - κ / 2 + η * ((d : ℝ) + 1 - κ) + η) := by
    simp only [r]
    rw [← Real.rpow_mul ht0.le, ← Real.rpow_mul ht0.le, ← Real.rpow_add ht0,
      ← Real.rpow_add ht0, ← Real.rpow_add ht0, ← Real.rpow_add ht0]
    congr 1
    have hη' : η = κ / (16 * ((d : ℝ) + 2)) := rfl
    ring
  have hpow : t ^ (-1 - κ / 2 + η * ((d : ℝ) + 1 - κ) + η) ≤ t ^ (-1 - κ / 8) :=
    Real.rpow_le_rpow_of_exponent_le ht hmargin
  have hℓ : (1 + t / s) ^ ((d : ℝ) / 4) * Real.sqrt (1 + t / s) ≤
      (1 + t / s) ^ ⌈(d : ℝ) / 4 + 1 / 2⌉₊ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (lt_of_lt_of_le zero_lt_one hl),
      ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hl (by
      have := Nat.le_ceil ((d : ℝ) / 4 + 1 / 2)
      linarith)
  have hpos1 : 0 ≤ t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ) *
      r ^ (-(d : ℝ) / 2) := by positivity
  calc t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ) * r ^ (-(d : ℝ) / 2) *
        (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) * (1 + r / Real.sqrt s)
      ≤ t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ) * r ^ (-(d : ℝ) / 2) *
        (Clat * t ^ (η * (d : ℝ) / 2) * (1 + t / s) ^ ((d : ℝ) / 4)) *
          (2 * t ^ η * Real.sqrt (1 + t / s)) := by
        have h1 := mul_le_mul_of_nonneg_left hinfl hpos1
        have hY : 0 ≤ 1 + r / Real.sqrt s := by positivity
        have hX : 0 ≤ t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ) *
            r ^ (-(d : ℝ) / 2) * (Clat * t ^ (η * (d : ℝ) / 2) * (1 + t / s) ^ ((d : ℝ) / 4)) := by
          positivity
        have hlen' : 1 + r / Real.sqrt s ≤ 2 * t ^ η * Real.sqrt (1 + t / s) := by
          simpa only [r] using hlen
        exact mul_le_mul h1 hlen' hY hX
    _ = 2 * Clat * (t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ) *
        r ^ (-(d : ℝ) / 2) * t ^ (η * (d : ℝ) / 2) * t ^ η) *
          ((1 + t / s) ^ ((d : ℝ) / 4) * Real.sqrt (1 + t / s)) := by ring
    _ ≤ 2 * Clat * t ^ (-1 - κ / 8) * (1 + t / s) ^ ⌈(d : ℝ) / 4 + 1 / 2⌉₊ := by
        rw [hexp]
        have h2 : 0 ≤ 2 * Clat := by positivity
        calc _ ≤ 2 * Clat * t ^ (-1 - κ / 8) *
              ((1 + t / s) ^ ((d : ℝ) / 4) * Real.sqrt (1 + t / s)) := by
              gcongr
          _ ≤ _ := by gcongr

/-- The lattice square sum of the Gaussian test envelope of any positive width
is controlled by the fixed-width lattice estimate. -/
theorem c1_test_lattice_square_sum (d : ℕ) (hd : 2 ≤ d) (κ ctest : ℝ)
    (hκ : 0 < κ) (hctest : 0 < ctest) :
    ∃ Clat : ℝ, 0 < Clat ∧ ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      let η := κ / (16 * ((d : ℝ) + 2))
      let r := t ^ (1 / 2 + η)
      let R := 2 * Real.sqrt (d : ℝ) + 2
      let E := fun z : Fin d → ℤ => sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
          {y : Vec d | euclideanNorm (y - fun j => r * (z j : ℝ)) ≤ R * r})
      Summable (fun z : Fin d → ℤ => (E z) ^ 2) ∧
      Real.sqrt (∑' z : Fin d → ℤ, (E z) ^ 2) ≤
        Clat * r ^ (-(d : ℝ) / 2) * s ^ (-(d : ℝ) / 4) *
          (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) ∧
      (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) ≤
        Clat * t ^ (η * (d : ℝ) / 2) * (1 + t / s) ^ ((d : ℝ) / 4) := by
  have hC1 : 1 ≤ max 1 (1 / ctest) := le_max_left _ _
  have hC0 : 0 < max 1 (1 / ctest) := lt_of_lt_of_le zero_lt_one hC1
  obtain ⟨Clat, hClat, hlat⟩ := carverS_flux_lattice_square_sum_fixed_parameters d hd κ
    (max 1 (1 / ctest)) hκ hC1
  refine ⟨Clat, hClat, ?_⟩
  intro t s ht hs η r R E
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  obtain ⟨hsum, hbound, hinfl⟩ := hlat t s ht hs 0
  dsimp only at hsum hbound hinfl
  have hr0 : 0 < r := Real.rpow_pos_of_pos ht0 _
  have hρ : 0 ≤ R * r := by positivity
  have hE0 (z : Fin d → ℤ) : 0 ≤ E z :=
    (c1_gaussian_ball_sup s ctest (R * r) hs0 hctest hρ _).1
  have hEle (z : Fin d → ℤ) : E z ≤ sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-euclideanNorm ((0 : Vec d) - y) ^ 2 / (max 1 (1 / ctest) * s))) ''
        {y : Vec d | euclideanNorm (y - fun j => r * (z j : ℝ)) ≤ R * r}) := by
    have hanti := c1_gaussian_ball_sup_antitone (d := d) s (1 / max 1 (1 / ctest)) ctest
      (R * r) hs0 (by positivity) (by
        rw [div_le_iff₀ hC0]
        calc 1 = ctest * (1 / ctest) := by field_simp
          _ ≤ ctest * max 1 (1 / ctest) := by
            gcongr
            exact le_max_right _ _) hρ (fun j => r * (z j : ℝ))
    refine hanti.trans (le_of_eq ?_)
    congr 2
    funext y
    have hn : euclideanNorm ((0 : Vec d) - y) = euclideanNorm y := by
      simp [euclideanNorm, euclideanSq, dot]
    rw [hn]
    congr 2
    field_simp
  have hsum' : Summable (fun z : Fin d → ℤ => (E z) ^ 2) :=
    hsum.of_nonneg_of_le (fun z => sq_nonneg _) fun z =>
      pow_le_pow_left₀ (hE0 z) (hEle z) 2
  refine ⟨hsum', le_trans ?_ hbound, hinfl⟩
  apply Real.sqrt_le_sqrt
  exact hsum'.tsum_le_tsum (fun z => pow_le_pow_left₀ (hE0 z) (hEle z) 2) hsum

/-- The Gaussian envelope over a ball around the origin equals its peak value. -/
theorem c1_gaussian_ball_sup_origin {d : ℕ} (s c ρ : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hρ : 0 ≤ ρ) :
    sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-c * euclideanNorm y ^ 2 / s)) ''
        {y : Vec d | euclideanNorm (y - 0) ≤ ρ}) = s ^ (-(d : ℝ) / 2) := by
  have hsup := c1_gaussian_ball_sup s c ρ hs hc hρ (0 : Vec d)
  have hz : (0 : Vec d) ∈ {y : Vec d | euclideanNorm (y - 0) ≤ ρ} := by
    simpa [euclideanNorm, euclideanSq, dot] using hρ
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨0, hz, rfl⟩⟩
    · rintro a ⟨y, hy, rfl⟩
      have hexp : Real.exp (-c * euclideanNorm y ^ 2 / s) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _)) hs.le
      exact mul_le_of_le_one_right (Real.rpow_nonneg hs.le _) hexp
  · have h0 := hsup.2 0 hz
    have hn : euclideanNorm (0 : Vec d) = 0 := by simp [euclideanNorm, euclideanSq, dot]
    simpa [hn] using h0

/-- The annular residual series, evaluated at the origin site and the Gaussian
recovery scale `r ^ 2`, is absorbed into the main gain. -/
theorem c1_annular_absorbed_form (d : ℕ) {η κ Cloc : ℝ} (hη : 0 < η) (hκ : κ < 1)
    (hCloc : 1 ≤ Cloc) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ ζ : ℂ,
      ‖ζ‖ * Real.sqrt t ≤ t ^ (η / 4) → ∀ (Lb : ℕ) (K growth Cm : ℝ),
      1 ≤ K → 0 ≤ growth → 0 ≤ Cm →
    Cm * (2 + t) ^ Cloc * Real.exp (Cloc * ‖ζ‖ ^ 2 * t) * (t ^ (1 / 2 + η)) ^ d *
      (∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
        Real.exp (-4 ^ n * (t ^ (2 * η) / Cloc))) ≤
    Cm * (∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
        Real.exp (-4 ^ n * ((1 / Cloc) / 2))) *
      (K * Real.exp (growth * ‖ζ‖ ^ 2 * t / 2) * t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        (t ^ (1 / 2 + η)) ^ ((d : ℝ) + 1 - κ) * (1 + t / (t ^ (1 / 2 + η)) ^ 2) ^ Lb) := by
  obtain ⟨T, hT1, hT⟩ := c19_actual_schwartz_annular_residual_absorbed d hη hκ hCloc
  refine ⟨T, hT1, fun t ht ζ hζ Lb K growth Cm hK hg hCm => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (hT1.trans ht)
  have hr : 0 < t ^ (1 / 2 + η) := Real.rpow_pos_of_pos ht0 _
  have h := hT t ht ζ hζ ((t ^ (1 / 2 + η)) ^ 2) (sq_pos_of_pos hr) 0 Lb K growth 1 hK hg
    one_pos 0
  dsimp only at h
  rw [c1_gaussian_ball_sup_origin _ _ _ (sq_pos_of_pos hr) one_pos (by positivity)] at h
  obtain ⟨h₀, -⟩ := c1_recovery_gaussian_prefactors d (t ^ (1 / 2 + η)) hr
  rw [h₀] at h
  have hpd : (t ^ (1 / 2 + η)) ^ d * (t ^ (1 / 2 + η)) ^ (-(d : ℝ)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    simp
  simp only [Nat.cast_zero, neg_zero, zero_div, Real.rpow_zero, mul_one] at h
  have hmul := mul_le_mul_of_nonneg_left h (mul_nonneg hCm (by positivity :
    0 ≤ (t ^ (1 / 2 + η)) ^ d))
  refine le_trans (le_of_eq ?_) (hmul.trans (le_of_eq ?_))
  · linear_combination (-(Cm * (2 + t) ^ Cloc * Real.exp (Cloc * ‖ζ‖ ^ 2 * t) *
      (t ^ (1 / 2 + η)) ^ d * ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
        Real.exp (-4 ^ n * (t ^ (2 * η) / Cloc)))) * hpd
  · linear_combination (Cm * (∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
        Real.exp (-4 ^ n * ((1 / Cloc) / 2))) * (K * Real.exp (growth * ‖ζ‖ ^ 2 * t / 2) *
        t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * (t ^ (1 / 2 + η)) ^ ((d : ℝ) + 1 - κ) *
        (1 + t / (t ^ (1 / 2 + η)) ^ 2) ^ Lb)) * hpd

/-- The series term of the recovery residual and the annular absorption combine
into a single multiple of the main block bound. -/
theorem c1_schwartz_series_scalar (Cb ℓ Cm Kb P Pm A N Ssum e0 Qm : ℝ) (hCb : 0 ≤ Cb)
    (hℓ : 0 ≤ ℓ) (hCm : 0 ≤ Cm) (hKb : 0 ≤ Kb) (hP : P ≤ Pm)
    (hA : 0 ≤ A) (hN : 0 ≤ N) (hQ : Qm = Cm * Kb * P + N * e0) (he : e0 ≤ Ssum)
    (hann : N * Ssum ≤ Cm * A * (Kb * P)) :
    Cb * ℓ * Qm + 2 * (Cb * ℓ * N) * Ssum ≤ Cb * ℓ * ((1 + 3 * A) * Cm * Kb * Pm) := by
  have h1 : N * e0 ≤ N * Ssum := mul_le_mul_of_nonneg_left he hN
  have h3 : Cm * Kb * P * (1 + 3 * A) ≤ Cm * Kb * Pm * (1 + 3 * A) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (mul_nonneg hCm hKb))
      (by positivity)
  have h4 : Qm + 2 * N * Ssum ≤ (1 + 3 * A) * Cm * Kb * Pm := by
    subst hQ
    nlinarith [h1, h3, hann]
  calc _ = Cb * ℓ * (Qm + 2 * N * Ssum) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (mul_nonneg hCb hℓ)

/-- A finite square sum of weights bounded by an infinite square sum. -/
theorem c1_finite_sqrt_weight {ι : Type*} (c : ℝ) (hc : 0 ≤ c) (E w : ι → ℝ)
    (hw : ∀ z, w z = c * E z) (hs : Summable fun z => E z ^ 2) (Λ : Finset ι) :
    Real.sqrt (∑ z ∈ Λ, w z ^ 2) ≤ c * Real.sqrt (∑' z, E z ^ 2) := by
  have hT0 : 0 ≤ ∑' z, E z ^ 2 := tsum_nonneg fun z => sq_nonneg _
  calc Real.sqrt (∑ z ∈ Λ, w z ^ 2) ≤ Real.sqrt ((c * Real.sqrt (∑' z, E z ^ 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [mul_pow, Real.sq_sqrt hT0]
        calc ∑ z ∈ Λ, w z ^ 2 = c ^ 2 * ∑ z ∈ Λ, E z ^ 2 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z _
              rw [hw z, mul_pow]
          _ ≤ _ := mul_le_mul_of_nonneg_left (hs.sum_le_tsum Λ (fun z _ => sq_nonneg _))
              (sq_nonneg _)
    _ = c * Real.sqrt (∑' z, E z ^ 2) := Real.sqrt_sq (mul_nonneg hc (Real.sqrt_nonneg _))

/-- The final real-variable chain of the cutoff-Schwartz finite-family bound. -/
theorem c1_schwartz_final_chain (colorC Ccol Cb ℓ A Cm Pm K e τt rp rmd ℓd sk sd Clat lt tg
    S1 sw : ℝ) (hcol : colorC ≤ Ccol) (hcolnn : 0 ≤ colorC) (hCb : 0 ≤ Cb) (hℓ : 0 ≤ ℓ)
    (hA : 0 ≤ A) (hCm : 0 ≤ Cm) (hPm : 0 ≤ Pm) (hK : 0 ≤ K) (he : 0 ≤ e) (hτt : 0 ≤ τt)
    (hrp : 0 ≤ rp) (hsk : 0 ≤ sk) (hsd : 0 ≤ sd)
    (hClat : 0 ≤ Clat) (hS1 : S1 ≤ Cb * ℓ * ((1 + 3 * A) * Cm * (K * e * τt * rp) * Pm))
    (hS10 : 0 ≤ S1) (hsw : sw ≤ sk * (Clat * rmd * sd * ℓd)) (hsw0 : 0 ≤ sw)
    (hpb : τt * rp * rmd * ℓd * ℓ ≤ 2 * Clat * tg * lt) :
    colorC * S1 * sw ≤ (Ccol * Cb * (1 + 3 * A) * Cm * Pm * Clat * (2 * Clat)) * K * e *
      tg * (sk * sd) * lt := by
  have hB : 0 ≤ Cb * ℓ * ((1 + 3 * A) * Cm * (K * e * τt * rp) * Pm) := by positivity
  have hCc : 0 ≤ Ccol := hcolnn.trans hcol
  calc colorC * S1 * sw
      ≤ Ccol * (Cb * ℓ * ((1 + 3 * A) * Cm * (K * e * τt * rp) * Pm)) *
        (sk * (Clat * rmd * sd * ℓd)) :=
        mul_le_mul (mul_le_mul hcol hS1 hS10 hCc) hsw hsw0 (mul_nonneg hCc hB)
    _ = (Ccol * Cb * (1 + 3 * A) * Cm * Pm * Clat) * K * e * (sk * sd) *
        (τt * rp * rmd * ℓd * ℓ) := by ring
    _ ≤ (Ccol * Cb * (1 + 3 * A) * Cm * Pm * Clat) * K * e * (sk * sd) *
        (2 * Clat * tg * lt) :=
        mul_le_mul_of_nonneg_left hpb (by positivity)
    _ = _ := by ring

/-- The recovery-scale prefactor of the time-`t` flux estimate for the residual
beyond the local annuli. -/
def c1OracleN (d : ℕ) (Cm Cloc ζn t r : ℝ) : ℝ :=
  Cm * (2 + t) ^ Cloc * Real.exp (Cloc * ζn ^ 2 * t) * r ^ d

/-- The recovery-scale prefactor of the main time-`t` flux estimate. -/
noncomputable def c1OracleKb (d : ℕ) (κ growth K ζn t r : ℝ) : ℝ :=
  K * Real.exp (growth * ζn ^ 2 * t / 2) * t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
    r ^ ((d : ℝ) + 1 - κ)

/-- The recovery-scale bound for one admissible block at time `t`. -/
noncomputable def c1OracleQm (d : ℕ) (κ η Cm Cloc growth K ζn t r : ℝ) (Lmax : ℕ) : ℝ :=
  Cm * c1OracleKb d κ growth K ζn t r * (1 + t / r ^ 2) ^ Lmax +
    c1OracleN d Cm Cloc ζn t r * Real.exp (-(t ^ (2 * η) / Cloc))

end EinsteinFull.Blueprint
