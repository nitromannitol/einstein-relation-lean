import EinsteinFull.Calculus.C9TubeSignedDyadicGainTransport

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- A uniform local integral bound extends to each inner dyadic cylinder with
only the geometric cardinality cost of the parabolic cover. -/
theorem c11_dyadic_inner_lintegral_le_geometric_local_bound (d : ℕ) :
    ∃ C B : ℕ, ∀ n : ℕ, ∀ (f : (ℝ × Vec d) → ℝ≥0∞) (M : ℝ≥0∞),
      (∀ y ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
          (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
          sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)),
        (∫⁻ x in Set.Ioo (y.1 - (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4)
          (y.1 + (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4) ×ˢ
          sourceBall y.2 ((1 / (8 * (2 : ℝ) ^ n)) / 2), f x ∂volume) ≤ M) →
      (∫⁻ x in Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)), f x ∂volume) ≤
        (C * B ^ n : ℕ) * M := by
  obtain ⟨C, B, hcover⟩ := c9_dyadic_inner_lintegral_parabolic_cover d
  refine ⟨C, B, ?_⟩
  intro n f M hlocal
  obtain ⟨U, hcard, hcenter, hsum⟩ := hcover n
  refine (hsum f).trans ?_
  calc
    _ ≤ ∑ _y ∈ U, M := Finset.sum_le_sum fun y hy => hlocal y (hcenter y hy)
    _ = (U.card : ℝ≥0∞) * M := by simp
    _ ≤ (C * B ^ n : ℕ) * M := by
      exact mul_le_mul_left (Nat.cast_le.mpr hcard) M

/-- A finite-exponent norm gain gives the corresponding moment gain. -/
theorem c11_moment_gain_of_norm_gain
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (v : X → ℝ)
    (hvμ : AEStronglyMeasurable v μ) (hvν : AEStronglyMeasurable v ν)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (T : ℝ≥0∞)
    (hgain : eLpNorm v (ENNReal.ofReal q) ν ≤ T * eLpNorm v (ENNReal.ofReal p) μ) :
    (∫⁻ x, ‖v x‖ₑ ^ q ∂ν) ≤ T ^ q * (∫⁻ x, ‖v x‖ₑ ^ p ∂μ) ^ (q / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top hvν,
    eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top hvμ,
    ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal hp.le] at hgain
  have h := ENNReal.rpow_le_rpow hgain hq.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at h
  have hq' : (1 / q) * q = 1 := by field_simp [ne_of_gt hq]
  have hp' : (1 / p) * q = q / p := by ring
  simpa only [hq', hp', ENNReal.rpow_one] using h

/-- Cancel a finite positive Jacobian factor from a transported gain. -/
theorem c11_cancel_finite_jacobian_gain (a b x y : ℝ≥0∞)
    (ha0 : a ≠ 0) (hatop : a ≠ ⊤) (h : a * x ≤ b * y) :
    x ≤ (a⁻¹ * b) * y := by
  have h' := mul_le_mul_right h a⁻¹
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel ha0 hatop, one_mul] using h'

/-- The Jacobian used in parabolic rescaling is finite and nonzero. -/
theorem c11_parabolic_jacobian_finite_ne_zero (d : ℕ) (r : ℝ) (hr : 0 < r) :
    let J : ℝ≥0∞ := ENNReal.ofReal |(r ^ 2)⁻¹| *
      ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹)
    J ≠ 0 ∧ J ≠ ⊤ := by
  dsimp only
  constructor
  · exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- Every real power of a finite nonzero Jacobian can be cancelled. -/
theorem c11_cancel_jacobian_rpow_gain (J b x y : ℝ≥0∞) (a : ℝ)
    (hJ0 : J ≠ 0) (hJtop : J ≠ ⊤) (h : J ^ a * x ≤ b * y) :
    x ≤ ((J ^ a)⁻¹ * b) * y := by
  have ha0 : J ^ a ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hJ0, hJtop]
  have hatop : J ^ a ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hJ0 hJtop
  exact c11_cancel_finite_jacobian_gain _ _ _ _ ha0 hatop h

/-- A transported norm gain has a single Jacobian factor after cancellation. -/
theorem c11_cancel_jacobian_two_powers (J T x y : ℝ≥0∞) (a b : ℝ)
    (hJ0 : J ≠ 0) (hJtop : J ≠ ⊤)
    (h : J ^ a * x ≤ T * (J ^ b * y)) :
    x ≤ (J ^ (b - a) * T) * y := by
  have h' : J ^ a * x ≤ (T * J ^ b) * y := by simpa [mul_assoc] using h
  have hc := c11_cancel_jacobian_rpow_gain J (T * J ^ b) x y a hJ0 hJtop h'
  rw [ENNReal.rpow_sub b a hJ0 hJtop]
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hc

/-- The power of the parabolic Jacobian in a transported gain has
an exponent proportional to the reciprocal iteration exponent. -/
theorem c11_jacobian_iteration_exponent (d : ℕ) (hd : 2 ≤ d) (p : ℝ)
    (hp : 0 < p) :
    1 / p - 1 / (p * (((d : ℝ) + 2) / d)) =
      (2 / ((d : ℝ) + 2)) / p := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hd2 : (d : ℝ) + 2 ≠ 0 := by positivity
  field_simp [ne_of_gt hp, hd0, hd2]
  <;> ring

/-- Convert an explicit norm gain to the signed iteration's moment form. -/
theorem c11_signed_moment_gain_of_norm_gain
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (v : X → ℝ)
    (hvμ : AEStronglyMeasurable v μ) (hvν : AEStronglyMeasurable v ν)
    (p s : ℝ) (hp : 0 < p) (hs : 0 ≤ s) (T : ℝ≥0∞)
    (hgain : eLpNorm v (ENNReal.ofReal (p * (1 + s))) ν ≤
      T * eLpNorm v (ENNReal.ofReal p) μ) :
    (∫⁻ x, ‖v x‖ₑ ^ (p * (1 + s)) ∂ν) ≤
      T ^ (p * (1 + s)) * (1 * (∫⁻ x, ‖v x‖ₑ ^ p ∂μ)) ^ s *
        (1 * (∫⁻ x, ‖v x‖ₑ ^ p ∂μ)) := by
  have hq : 0 < p * (1 + s) := by positivity
  have h := c11_moment_gain_of_norm_gain μ ν v hvμ hvν p (p * (1 + s)) hp hq T hgain
  have hdiv : (p * (1 + s)) / p = s + 1 := by
    field_simp [ne_of_gt hp]; ring
  rw [hdiv, ENNReal.rpow_add_of_nonneg _ _ hs (by norm_num), ENNReal.rpow_one] at h
  simpa only [one_mul, mul_assoc] using h

/-- A Jacobian-weighted norm estimate gives the signed moment estimate
with the Jacobian cancelled explicitly. -/
theorem c11_signed_moment_gain_of_jacobian_norm_gain
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (v : X → ℝ)
    (hvμ : AEStronglyMeasurable v μ) (hvν : AEStronglyMeasurable v ν)
    (p s : ℝ) (hp : 0 < p) (hs : 0 ≤ s) (a b : ℝ≥0∞)
    (ha0 : a ≠ 0) (hatop : a ≠ ⊤)
    (hgain : a * eLpNorm v (ENNReal.ofReal (p * (1 + s))) ν ≤
      b * eLpNorm v (ENNReal.ofReal p) μ) :
    (∫⁻ x, ‖v x‖ₑ ^ (p * (1 + s)) ∂ν) ≤
      (a⁻¹ * b) ^ (p * (1 + s)) *
        (1 * (∫⁻ x, ‖v x‖ₑ ^ p ∂μ)) ^ s *
        (1 * (∫⁻ x, ‖v x‖ₑ ^ p ∂μ)) := by
  exact c11_signed_moment_gain_of_norm_gain μ ν v hvμ hvν p s hp hs (a⁻¹ * b)
    (c11_cancel_finite_jacobian_gain a b _ _ ha0 hatop hgain)

/-- A uniform gain on each member of the parabolic cover gives a global
moment gain, with the cover cardinality kept explicit. -/
theorem c11_dyadic_moment_gain_of_uniform_local_norm_gain (d : ℕ) :
    ∃ C B : ℕ, ∀ (n : ℕ) (u : ℝ × Vec d → ℝ) (p s : ℝ),
      0 < p → 0 ≤ s → ∀ T : ℝ≥0∞,
      let ν := volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))
      AEStronglyMeasurable u ν →
      (∀ y ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
          (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
          sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)),
        let μ := volume.restrict (Set.Ioo (y.1 - (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4)
          (y.1 + (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4) ×ˢ
          sourceBall y.2 ((1 / (8 * (2 : ℝ) ^ n)) / 2))
        AEStronglyMeasurable u μ ∧
        eLpNorm u (ENNReal.ofReal (p * (1 + s))) μ ≤
          T * eLpNorm u (ENNReal.ofReal p) ν) →
      (∫⁻ x in Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)),
        ‖u x‖ₑ ^ (p * (1 + s))) ≤
      (C * B ^ n : ℕ) * (T ^ (p * (1 + s)) *
        (∫⁻ x, ‖u x‖ₑ ^ p ∂ν) ^ s * (∫⁻ x, ‖u x‖ₑ ^ p ∂ν)) := by
  obtain ⟨C, B, hcover⟩ := c11_dyadic_inner_lintegral_le_geometric_local_bound d
  refine ⟨C, B, ?_⟩
  intro n u p s hp hs T ν hν hlocal
  apply hcover n (fun x => ‖u x‖ₑ ^ (p * (1 + s)))
  intro y hy
  obtain ⟨hμ, hgain⟩ := hlocal y hy
  simpa only [one_mul] using
    c11_signed_moment_gain_of_norm_gain ν _ u hν hμ p s hp hs T hgain

/-- The cover cardinality, iteration exponent and radius loss have a
single geometric upper bound. -/
theorem c11_dyadic_coefficient_geometric_bound (N B C c : ℝ)
    (hN : 1 ≤ N) (hB : 1 ≤ B) (hC : 1 ≤ C) (hc : 1 ≤ c) :
    ∃ A b : ℝ, 1 ≤ A ∧ 1 < b ∧ ∀ n : ℕ,
      (N * B ^ n) * (C * (2 * c ^ n) ^ 2) * (8 * (2 : ℝ) ^ n) ^ 2 ≤
        A * b ^ n := by
  let A : ℝ := 256 * N * C
  let b : ℝ := 4 * B * c ^ 2 + 1
  have hA : 1 ≤ A := by
    dsimp [A]
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hC)]
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hbpos : 0 < 4 * B * c ^ 2 := by positivity
  have hb : 1 < b := by dsimp [b]; linarith
  refine ⟨A, b, hA, hb, ?_⟩
  intro n
  have heq : (N * B ^ n) * (C * (2 * c ^ n) ^ 2) * (8 * (2 : ℝ) ^ n) ^ 2 =
      A * (4 * B * c ^ 2) ^ n := by
    dsimp [A]
    simp only [mul_pow, ← pow_mul]
    ring_nf
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm 2 n]
  rw [heq]
  gcongr
  dsimp [b]
  linarith

/-- The same geometric bound also controls the cover factor at the
reciprocal Sobolev exponent. -/
theorem c11_dyadic_coefficient_geometric_rpow_bound (N B C c : ℝ)
    (hN : 1 ≤ N) (hB : 1 ≤ B) (hC : 1 ≤ C) (hc : 1 ≤ c) :
    ∃ A b : ℝ, 1 ≤ A ∧ 1 < b ∧ ∀ n : ℕ,
      Real.rpow (N * B ^ n) (1 / c) * (C * (2 * c ^ n) ^ 2) *
        (8 * (2 : ℝ) ^ n) ^ 2 ≤ A * b ^ n := by
  obtain ⟨A, b, hA, hb, hbound⟩ := c11_dyadic_coefficient_geometric_bound N B C c hN hB hC hc
  refine ⟨A, b, hA, hb, ?_⟩
  intro n
  have hnb : 1 ≤ N * B ^ n := by
    have hpow : 1 ≤ B ^ n := one_le_pow₀ hB
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hpow)]
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hrec : 1 / c ≤ 1 := (div_le_one hcpos).2 hc
  have hpow : Real.rpow (N * B ^ n) (1 / c) ≤ N * B ^ n := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnb hrec
  calc
    _ ≤ (N * B ^ n) * (C * (2 * c ^ n) ^ 2) * (8 * (2 : ℝ) ^ n) ^ 2 := by
      gcongr
    _ ≤ A * b ^ n := hbound n

/-- The root of the cover-weighted gain separates the cover loss from the
local norm coefficient. -/
theorem c11_cover_gain_root (N T : ℝ≥0∞) (p c : ℝ)
    (hp : 0 < p) (hc : 0 < c) :
    (N * T ^ (p * c)) ^ (1 / (p * c)) = N ^ (1 / (p * c)) * T := by
  have hpc : p * c ≠ 0 := ne_of_gt (mul_pos hp hc)
  have he : (p * c) * (1 / (p * c)) = 1 := by field_simp [hpc]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    he, ENNReal.rpow_one]

/-- The cover loss can be combined with the local coefficient before taking
the input-exponent root. -/
theorem c11_cover_gain_root_input_exponent (N T : ℝ≥0∞) (p c : ℝ)
    (hp : 0 < p) (hc : 0 < c) :
    (N * T ^ (p * c)) ^ (1 / (p * c)) =
      (N ^ (1 / c) * T ^ p) ^ (1 / p) := by
  rw [c11_cover_gain_root N T p c hp hc,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  have h₁ : (1 / c) * (1 / p) = 1 / (p * c) := by
    field_simp [ne_of_gt hp, ne_of_gt hc]
    <;> ring
  have h₂ : p * (1 / p) = 1 := by field_simp [ne_of_gt hp]
  rw [h₁, h₂, ENNReal.rpow_one]

/-- Raising the radius and signed-gain losses to the input exponent leaves
the inverse-square radius and the quadratic exponent factor. -/
theorem c11_signed_gain_coefficient_power (C p r : ℝ)
    (hC : 0 ≤ C) (hp : 0 < p) (hr : 0 < r) :
    Real.rpow (Real.rpow r (-(2 / p)) * Real.rpow (C * p ^ 2) (1 / p)) p =
      (r ^ 2)⁻¹ * (C * p ^ 2) := by
  have hCp : 0 ≤ C * p ^ 2 := mul_nonneg hC (sq_nonneg p)
  have h₁ : (-(2 / p)) * p = -2 := by field_simp [ne_of_gt hp]
  have h₂ : (1 / p) * p = 1 := by field_simp [ne_of_gt hp]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hCp _),
    ← Real.rpow_mul hr.le, ← Real.rpow_mul hCp, h₁, h₂,
    Real.rpow_neg hr.le, Real.rpow_two, Real.rpow_one]

/-- The same coefficient identity in the extended nonnegative reals used by
the moment recurrence. -/
theorem c11_signed_gain_ennreal_coefficient_power (C p r : ℝ)
    (hC : 0 ≤ C) (hp : 0 < p) (hr : 0 < r) :
    (ENNReal.ofReal (Real.rpow r (-(2 / p))) *
      ENNReal.ofReal (Real.rpow (C * p ^ 2) (1 / p))) ^ p =
      ENNReal.ofReal ((r ^ 2)⁻¹ * (C * p ^ 2)) := by
  have h₁ : 0 ≤ Real.rpow r (-(2 / p)) := Real.rpow_nonneg hr.le _
  have h₂ : 0 ≤ Real.rpow (C * p ^ 2) (1 / p) :=
    Real.rpow_nonneg (mul_nonneg hC (sq_nonneg p)) _
  simp only [Real.rpow_eq_pow] at *
  rw [← ENNReal.ofReal_mul h₁,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg h₁ h₂) hp.le]
  simpa only [Real.rpow_eq_pow] using congrArg ENNReal.ofReal
    (c11_signed_gain_coefficient_power C p r hC hp hr)

/-- A real coefficient bound controls the root of the actual cover-weighted
signed gain. -/
theorem c11_cover_signed_gain_root_bound (N C p c r D : ℝ)
    (hN : 0 ≤ N) (hC : 0 ≤ C) (hp : 0 < p) (hc : 0 < c) (hr : 0 < r)
    (hbound : Real.rpow N (1 / c) * ((r ^ 2)⁻¹ * (C * p ^ 2)) ≤ D) :
    (ENNReal.ofReal N *
      (ENNReal.ofReal (Real.rpow r (-(2 / p))) *
        ENNReal.ofReal (Real.rpow (C * p ^ 2) (1 / p))) ^ (p * c)) ^
      (1 / (p * c)) ≤ ENNReal.ofReal (Real.rpow D (1 / p)) := by
  have hleft : 0 ≤ Real.rpow N (1 / c) * ((r ^ 2)⁻¹ * (C * p ^ 2)) := by
    exact mul_nonneg (Real.rpow_nonneg hN _) (by positivity)
  simp only [Real.rpow_eq_pow] at *
  have hcoef := c11_signed_gain_ennreal_coefficient_power C p r hC hp hr
  simp only [Real.rpow_eq_pow] at hcoef
  rw [c11_cover_gain_root_input_exponent _ _ p c hp hc,
    hcoef,
    ENNReal.ofReal_rpow_of_nonneg hN (by positivity : 0 ≤ 1 / c),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hN _),
    ENNReal.ofReal_rpow_of_nonneg hleft (by positivity : 0 ≤ 1 / p)]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hleft hbound (by positivity))

/-- The dyadic cover and the actual radius loss admit a uniform geometric
coefficient at the input exponent. -/
theorem c11_dyadic_signed_gain_coefficient_bound (N B C c : ℝ)
    (hN : 1 ≤ N) (hB : 1 ≤ B) (hC : 1 ≤ C) (hc : 1 ≤ c) :
    ∃ A b : ℝ, 1 ≤ A ∧ 1 < b ∧ ∀ n : ℕ,
      let p : ℝ := 2 * c ^ n
      let r : ℝ := 1 / (8 * (2 : ℝ) ^ n)
      (ENNReal.ofReal (N * B ^ n) *
        (ENNReal.ofReal (Real.rpow r (-(2 / p))) *
          ENNReal.ofReal (Real.rpow (C * p ^ 2) (1 / p))) ^ (p * c)) ^
        (1 / (p * c)) ≤ ENNReal.ofReal (Real.rpow (A * b ^ n) (1 / p)) := by
  obtain ⟨A, b, hA, hb, hbound⟩ :=
    c11_dyadic_coefficient_geometric_rpow_bound N B C c hN hB hC hc
  refine ⟨A, b, hA, hb, ?_⟩
  intro n p r
  have hp : 0 < p := by dsimp [p]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hN0 : 0 ≤ N * B ^ n := by positivity
  have hC0 : 0 ≤ C := by linarith
  have hr2 : (r ^ 2)⁻¹ = (8 * (2 : ℝ) ^ n) ^ 2 := by
    dsimp [r]
    simp only [one_div, inv_pow, inv_inv]
  apply c11_cover_signed_gain_root_bound (N * B ^ n) C p c r (A * b ^ n)
    hN0 hC0 hp hc0 hr
  simpa only [p, hr2, mul_assoc, mul_comm, mul_left_comm] using hbound n

/-- A fixed bounded-overlap constant and any positive signed-gain constant
give the geometric coefficient needed by the dyadic iteration. -/
theorem c11_overlap_signed_gain_coefficient_bound (N C c : ℝ)
    (hN : 1 ≤ N) (hC : 0 < C) (hc : 1 ≤ c) :
    ∃ A b : ℝ, 1 ≤ A ∧ 1 < b ∧ ∀ n : ℕ,
      let p : ℝ := 2 * c ^ n
      let r : ℝ := 1 / (8 * (2 : ℝ) ^ n)
      (ENNReal.ofReal N *
        (ENNReal.ofReal (Real.rpow r (-(2 / p))) *
          ENNReal.ofReal (Real.rpow (C * p ^ 2) (1 / p))) ^ (p * c)) ^
        (1 / (p * c)) ≤ ENNReal.ofReal (Real.rpow (A * b ^ n) (1 / p)) := by
  obtain ⟨A, b, hA, hb, hbound⟩ :=
    c11_dyadic_coefficient_geometric_rpow_bound N 1 (max C 1) c hN
      (le_refl 1) (le_max_right C 1) hc
  refine ⟨A, b, hA, hb, ?_⟩
  intro n p r
  have hp : 0 < p := by dsimp [p]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hN0 : 0 ≤ N := by linarith
  have hr2 : (r ^ 2)⁻¹ = (8 * (2 : ℝ) ^ n) ^ 2 := by
    dsimp [r]
    simp only [one_div, inv_pow, inv_inv]
  apply c11_cover_signed_gain_root_bound N C p c r (A * b ^ n)
    hN0 hC.le hp hc0 hr
  calc
    _ ≤ Real.rpow N (1 / c) * ((8 * (2 : ℝ) ^ n) ^ 2 *
        (max C 1 * (2 * c ^ n) ^ 2)) := by
      rw [hr2]
      dsimp [p]
      gcongr
      exact le_max_left C 1
    _ ≤ A * b ^ n := by
      simpa only [one_pow, mul_one, mul_assoc, mul_comm, mul_left_comm] using hbound n

/-- The signed-gain Jacobian coefficient is the physical radius loss. -/
theorem c11_signed_jacobian_scale (d : ℕ) (hd : 0 < (d : ℝ))
    (p r : ℝ) (hp : 0 < p) (hr : 0 < r) :
    let J : ℝ≥0∞ := ENNReal.ofReal |(r ^ 2)⁻¹| *
      ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹)
    J ^ ((1 / ENNReal.ofReal p).toReal -
      (1 / ENNReal.ofReal (p*((d:ℝ)+2)/d)).toReal) =
      ENNReal.ofReal (Real.rpow r (-(2/p))) := by
  dsimp only
  have hj := c11_parabolic_jacobian_finite_ne_zero d r hr
  dsimp only at hj
  rw [ENNReal.rpow_sub _ _ hj.1 hj.2,
    c17_parabolic_jacobian_combine d r hr]
  have h := c17_parabolic_gain_ennreal_ratio d p r hd hp hr
  have hq : p * ((d : ℝ) + 2) / d = p * (((d : ℝ) + 2) / d) := by ring
  rw [hq]
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- Every inner local cylinder in the cover lies in the preceding dyadic cylinder. -/
theorem c11_dyadic_inner_local_containment (d n : ℕ) (t : ℝ) (y : Vec d)
    (hinner : (t, y) ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall 0 (1 / 2 + 1 / (4 * (2 : ℝ) ^ n))) :
    let r : ℝ := 1 / (8 * (2 : ℝ) ^ n)
    Set.Ioo (t - r ^ 2 / 4) (t + r ^ 2 / 4) ×ˢ sourceBall y (r / 2) ⊆
      Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall 0 (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)) := by
  dsimp only
  apply Set.Subset.trans ?_ (c9_dyadic_local_cylinder_containment d n t y hinner)
  intro x hx
  have hr : 0 < 1 / (8 * (2 : ℝ) ^ n) := by positivity
  have hs : 0 ≤ (1 / (8 * (2 : ℝ) ^ n)) ^ 2 := sq_nonneg _
  rcases hx with ⟨⟨ht₁, ht₂⟩, hy⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · linarith
  · linarith
  · change euclideanNorm (x.2 - y) < _ at hy ⊢
    linarith

/-- The actual dyadic signed gain with its Jacobian cancelled. -/
theorem c11_dyadic_local_signed_gain_cancelled
    (d : ℕ) (κ : ℝ)
    (hSignedUnitGain :
      ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ p : ℝ, 2 ≤ p →
      eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ (n : ℕ) (t : ℝ) (y : Vec d),
      (t, y) ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall 0 (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)) →
      ∀ p : ℝ, 2 ≤ p →
      let r : ℝ := 1 / (8 * (2 : ℝ) ^ n)
      let J : ℝ≥0∞ := ENNReal.ofReal |(r^2)⁻¹| *
        ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹)
      eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
          (volume.restrict (Set.Ioo (t-(r^2)/4) (t+r^2/4) ×ˢ sourceBall y (r/2))) ≤
      (J ^ ((1 / ENNReal.ofReal p).toReal -
          (1 / ENNReal.ofReal (p*((d:ℝ)+2)/d)).toReal) *
        ENNReal.ofReal (Real.rpow (C*p^2) (1/p))) *
          eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
              (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
              sourceBall 0 (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))) := by
  obtain ⟨C, hC, hlocal⟩ := c9_dyadic_local_signed_gain_global_rhs d κ hSignedUnitGain
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal n t y hinner p hp
  have h := hlocal ρ α hell u G hcal n t y hinner p hp
  have hr : 0 < (1 / (8 * (2 : ℝ) ^ n)) := by positivity
  have hj := c11_parabolic_jacobian_finite_ne_zero d _ hr
  dsimp only at h ⊢ hj
  exact c11_cancel_jacobian_two_powers _ _ _ _ _ _ hj.1 hj.2 h

/-- Jacobian cancellation with the enlarged local cylinder used by the overlap cover. -/
theorem c11_dyadic_local_signed_gain_cancelled_enlarged
    (d : ℕ) (κ : ℝ)
    (hSignedUnitGain :
      ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ p : ℝ, 2 ≤ p →
      eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ (n : ℕ) (t : ℝ) (y : Vec d),
      (t, y) ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall 0 (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)) →
      ∀ p : ℝ, 2 ≤ p →
      let r : ℝ := 1 / (8 * (2 : ℝ) ^ n)
      let J : ℝ≥0∞ := ENNReal.ofReal |(r^2)⁻¹| *
        ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹)
      eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
          (volume.restrict (Set.Ioo (t-(r^2)/4) (t+r^2/4) ×ˢ sourceBall y (r/2))) ≤
      (J ^ ((1 / ENNReal.ofReal p).toReal -
          (1 / ENNReal.ofReal (p*((d:ℝ)+2)/d)).toReal) *
        ENNReal.ofReal (Real.rpow (C*p^2) (1/p))) *
          eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r))) := by
  obtain ⟨C, hC, hlocal⟩ := c9_dyadic_local_signed_gain_with_jacobian d κ hSignedUnitGain
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal n t y hinner p hp
  have h := hlocal ρ α hell u G hcal n t y hinner p hp
  have hr : 0 < (1 / (8 * (2 : ℝ) ^ n)) := by positivity
  have hj := c11_parabolic_jacobian_finite_ne_zero d _ hr
  dsimp only at h ⊢ hj
  have hcancel := c11_cancel_jacobian_two_powers _ _ _ _ _ _ hj.1 hj.2 h
  have hsub : Set.Ioo (t - (1 / (8 * (2 : ℝ) ^ n)) ^ 2)
      (t + (1 / (8 * (2 : ℝ) ^ n)) ^ 2) ×ˢ sourceBall y (1 / (8 * (2 : ℝ) ^ n)) ⊆
      Set.Ioo (t - (1 / (8 * (2 : ℝ) ^ n)) ^ 2)
      (t + (1 / (8 * (2 : ℝ) ^ n)) ^ 2) ×ˢ sourceBall y (2 * (1 / (8 * (2 : ℝ) ^ n))) := by
    intro x hx
    rcases hx with ⟨ht, hy⟩
    refine ⟨ht, ?_⟩
    change euclideanNorm (x.2 - y) < _ at hy ⊢
    linarith
  have hmono := eLpNorm_mono_measure u (p := ENNReal.ofReal p)
    (Measure.restrict_mono_set volume hsub)
  exact hcancel.trans (mul_le_mul (le_refl _) hmono zero_le zero_le)

/-- The zero extension of a locally measurable moment is measurable for the
global measure used by the overlap estimate. -/
theorem c11_moment_indicator_aemeasurable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : Set X) (hA : MeasurableSet A) (u : X → ℝ) (p : ℝ)
    (hu : AEStronglyMeasurable u (μ.restrict A)) :
    AEMeasurable (A.indicator (fun x => ‖u x‖ₑ ^ p)) μ := by
  exact (aemeasurable_indicator_iff hA).2 (hu.aemeasurable.enorm.pow_const p)

/-- Extending a local moment by zero does not change its integral on a
subset of the extension cylinder. -/
theorem c11_lintegral_indicator_of_subset {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A W : Set X) (hW : MeasurableSet W) (hsub : W ⊆ A)
    (f : X → ℝ≥0∞) :
    (∫⁻ x in W, A.indicator f x ∂μ) = ∫⁻ x in W, f x ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hW] with x hx
  exact Set.indicator_of_mem (hsub hx) _

open Classical in
/-- The actual caloric local norm gains combine through a bounded-overlap
cover into the signed dyadic moment recurrence. -/
theorem c11_dyadic_overlap_signed_moment
    (d n : ℕ) (u : ℝ × Vec d → ℝ) (F : Finset (ℝ × Vec d)) (N : ℕ)
    (p s : ℝ) (hp : 0 < p) (hs : 0 ≤ s) (T : ℝ≥0∞)
    (hu : AEStronglyMeasurable u (volume.restrict
      (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)))
    (hcenter : ∀ z ∈ F, z ∈ Set.Ioo (-(1/4) - 3/(8*(2:ℝ)^n))
      (1/4 + 3/(8*(2:ℝ)^n)) ×ˢ sourceBall 0 (1/2 + 1/(4*(2:ℝ)^n)))
    (hcover : ∀ x ∈ Set.Ioo (-(1/4) - 3/(8*(2:ℝ)^n))
      (1/4 + 3/(8*(2:ℝ)^n)) ×ˢ sourceBall (0 : Vec d) (1/2 + 1/(4*(2:ℝ)^n)),
      ∃ z ∈ F, x ∈ Set.Ioo (z.1-(1/(8*(2:ℝ)^n))^2/4)
        (z.1+(1/(8*(2:ℝ)^n))^2/4) ×ˢ sourceBall z.2 ((1/(8*(2:ℝ)^n))/2))
    (hcontain : ∀ z ∈ F, Set.Ioo (z.1-(1/(8*(2:ℝ)^n))^2)
      (z.1+(1/(8*(2:ℝ)^n))^2) ×ˢ sourceBall z.2 (2*(1/(8*(2:ℝ)^n))) ⊆
      Set.Ioo (-(1/4) - 3/(4*(2:ℝ)^n)) (1/4 + 3/(4*(2:ℝ)^n)) ×ˢ
        sourceBall 0 (1/2 + 1/(2*(2:ℝ)^n)))
    (hoverlap : ∀ x : ℝ × Vec d, (F.filter (fun z => x ∈
      Set.Ioo (z.1-(1/(8*(2:ℝ)^n))^2) (z.1+(1/(8*(2:ℝ)^n))^2) ×ˢ
        sourceBall z.2 (2*(1/(8*(2:ℝ)^n))))).card ≤ N)
    (hlocal : ∀ z ∈ F,
      eLpNorm u (ENNReal.ofReal (p*(1+s))) (volume.restrict
        (Set.Ioo (z.1-(1/(8*(2:ℝ)^n))^2/4) (z.1+(1/(8*(2:ℝ)^n))^2/4) ×ˢ
          sourceBall z.2 ((1/(8*(2:ℝ)^n))/2))) ≤
      T * eLpNorm u (ENNReal.ofReal p) (volume.restrict
        (Set.Ioo (z.1-(1/(8*(2:ℝ)^n))^2) (z.1+(1/(8*(2:ℝ)^n))^2) ×ˢ
          sourceBall z.2 (2*(1/(8*(2:ℝ)^n)))))) :
    (∫⁻ x in Set.Ioo (-(1/4) - 3/(8*(2:ℝ)^n)) (1/4 + 3/(8*(2:ℝ)^n)) ×ˢ
      sourceBall (0 : Vec d) (1/2 + 1/(4*(2:ℝ)^n)), ‖u x‖ₑ ^ (p*(1+s))) ≤
    (N : ℝ≥0∞) * T ^ (p*(1+s)) *
      (∫⁻ x in Set.Ioo (-(1/4) - 3/(4*(2:ℝ)^n)) (1/4 + 3/(4*(2:ℝ)^n)) ×ˢ
        sourceBall (0 : Vec d) (1/2 + 1/(2*(2:ℝ)^n)), ‖u x‖ₑ ^ p) ^ s *
      (∫⁻ x in Set.Ioo (-(1/4) - 3/(4*(2:ℝ)^n)) (1/4 + 3/(4*(2:ℝ)^n)) ×ˢ
        sourceBall (0 : Vec d) (1/2 + 1/(2*(2:ℝ)^n)), ‖u x‖ₑ ^ p) := by
  classical
  let r : ℝ := 1/(8*(2:ℝ)^n)
  let D : Set (ℝ × Vec d) := Set.Ioo (-(1/4) - 3/(8*(2:ℝ)^n))
    (1/4 + 3/(8*(2:ℝ)^n)) ×ˢ sourceBall 0 (1/2 + 1/(4*(2:ℝ)^n))
  let A : Set (ℝ × Vec d) := Set.Ioo (-(1/4) - 3/(4*(2:ℝ)^n))
    (1/4 + 3/(4*(2:ℝ)^n)) ×ˢ sourceBall 0 (1/2 + 1/(2*(2:ℝ)^n))
  have hA : MeasurableSet A := measurableSet_Ioo.prod (c17_isOpen_sourceBall _ _).measurableSet
  have huA : AEStronglyMeasurable u (volume.restrict A) := hu.mono_measure
    (Measure.restrict_mono_set volume (c11_moser_dyadic_cylinder_containment d n).2)
  let f : (ℝ × Vec d) → ℝ≥0∞ := A.indicator (fun x => ‖u x‖ₑ ^ p)
  have hf : AEMeasurable f volume := c11_moment_indicator_aemeasurable volume A hA u p huA
  have hlocal' : ∀ z ∈ F,
      (∫⁻ x in Set.Ioo (z.1-r^2/4) (z.1+r^2/4) ×ˢ sourceBall z.2 (r/2),
        ‖u x‖ₑ ^ (p*(1+s))) ≤ T ^ (p*(1+s)) *
      (∫⁻ x in Set.Ioo (z.1-r^2) (z.1+r^2) ×ˢ sourceBall z.2 (2*r), f x) ^ s *
      (∫⁻ x in Set.Ioo (z.1-r^2) (z.1+r^2) ×ˢ sourceBall z.2 (2*r), f x) := by
    intro z hz
    let W := Set.Ioo (z.1-r^2) (z.1+r^2) ×ˢ sourceBall z.2 (2*r)
    let V := Set.Ioo (z.1-r^2/4) (z.1+r^2/4) ×ˢ sourceBall z.2 (r/2)
    have hW : MeasurableSet W := measurableSet_Ioo.prod (c17_isOpen_sourceBall _ _).measurableSet
    have hWA : W ⊆ A := hcontain z hz
    have huW := huA.mono_measure (Measure.restrict_mono_set volume hWA)
    have huV := huA.mono_measure (Measure.restrict_mono_set volume
      (c11_dyadic_inner_local_containment d n z.1 z.2 (hcenter z hz)))
    have hg := c11_signed_moment_gain_of_norm_gain (volume.restrict W) (volume.restrict V)
      u huW huV p s hp hs T (hlocal z hz)
    have heq : (∫⁻ x in W, f x) = ∫⁻ x in W, ‖u x‖ₑ ^ p :=
      c11_lintegral_indicator_of_subset volume A W hW hWA _
    change (∫⁻ x in V, ‖u x‖ₑ ^ (p*(1+s))) ≤ T ^ (p*(1+s)) *
      (∫⁻ x in W, f x) ^ s * (∫⁻ x in W, f x)
    rw [heq]
    simpa only [one_mul] using hg
  have h := c9_bounded_overlap_moment_transport d F r A D N hA hcontain hcover hoverlap
    f (fun x => ‖u x‖ₑ ^ (p*(1+s))) hf s hs (T ^ (p*(1+s))) hlocal'
  have heq : (∫⁻ x in A, f x) = ∫⁻ x in A, ‖u x‖ₑ ^ p :=
    c11_lintegral_indicator_of_subset volume A A hA (Set.Subset.rfl) _
  change (∫⁻ x in D, ‖u x‖ₑ ^ (p*(1+s))) ≤ (N : ℝ≥0∞) * T ^ (p*(1+s)) *
    (∫⁻ x in A, ‖u x‖ₑ ^ p) ^ s * (∫⁻ x in A, ‖u x‖ₑ ^ p)
  simpa only [heq, mul_assoc, mul_left_comm, mul_comm] using h

/-- The inner cylinder at one dyadic step is the next iteration cylinder. -/
theorem c11_dyadic_inner_cylinder_eq_next (d n : ℕ) :
    (Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
      (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
      sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n))) =
    (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ (n + 1)))
      (1 / 4 + 3 / (4 * (2 : ℝ) ^ (n + 1))) ×ˢ
      sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ (n + 1)))) := by
  have hn : (2 : ℝ) ^ n ≠ 0 := by positivity
  have ht : 3 / (8 * (2 : ℝ) ^ n) = 3 / (4 * (2 : ℝ) ^ (n + 1)) := by
    rw [pow_succ]
    field_simp [hn]
    <;> ring
  have hx : 1 / (4 * (2 : ℝ) ^ n) = 1 / (2 * (2 : ℝ) ^ (n + 1)) := by
    rw [pow_succ]
    field_simp [hn]
    <;> ring
  rw [ht, hx]

/-- Conditional native local maximum estimate. The first input is the full
unit signed gain; the second supplies its dyadic transport and uniform bounds. -/
theorem c11_native_unit_L2_local_max_downstream
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (_hκ : 0 < κ)
    (hSignedGain : ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
        IsUniformlyElliptic κ ρ α →
        ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
        ∀ p : ℝ, 2 ≤ p →
          eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
            (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
          ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
            eLpNorm u (ENNReal.ofReal p)
              (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)))
    (hDyadicTransport : (∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
        IsUniformlyElliptic κ ρ α →
        ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
        ∀ p : ℝ, 2 ≤ p →
          eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
            (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
          ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
            eLpNorm u (ENNReal.ofReal p)
              (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) →
      (let c : ℝ := ((d : ℝ) + 2) / d
      let s : ℝ := 2 / d
      let ν : ℕ → Measure (ℝ × Vec d) := fun n =>
        volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
          (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
          sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))
      ∃ A b : ℝ, 1 ≤ A ∧ 1 < b ∧
        ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
          IsUniformlyElliptic κ ρ α →
          ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
          IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
          ∃ K B E : ℕ → ℝ≥0∞,
            (∀ n, (K n * B n ^ s * E n) ^ (1 / ((2 * c ^ n) * (1 + s))) ≤
              ENNReal.ofReal (Real.rpow (A * Real.rpow b (n : ℝ))
                (1 / (2 * Real.rpow c (n : ℝ))))) ∧
            (∀ n, (∫⁻ x, ‖u x‖ₑ ^ ((2 * c ^ n) * (1 + s)) ∂(ν (n + 1))) ≤
              K n * (B n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))) ^ s *
                (E n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n)))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      eLpNorm u ⊤ (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
        ENNReal.ofReal C * eLpNorm u 2
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) := by
  exact c11_native_unit_L2_local_max_of_signed_moment_gain d hd κ
    (hDyadicTransport hSignedGain)

end EinsteinFull.Calculus
