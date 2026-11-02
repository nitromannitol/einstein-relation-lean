import EinsteinFull.Calculus.C6FluxBlockGlobalGradientMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped NNReal

noncomputable section
namespace EinsteinFull.Blueprint

/-- The polynomial in the scaled force is absorbed into any positive Gaussian rate. -/
theorem c6_flux_force_polynomial_absorption (C κ : ℝ) (hC : 0 ≤ C) (hκ : 0 < κ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (ζ : ℂ) (t : ℝ≥0),
      (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C ≤
        K * Real.exp (κ * ‖ζ‖ ^ 2 * (t : ℝ)) := by
  refine ⟨Real.exp (C ^ 2 / (4 * κ)), ?_, ?_⟩
  · exact Real.one_le_exp (div_nonneg (sq_nonneg C) (by positivity))
  · intro ζ t
    let x : ℝ := ‖ζ‖ * Real.sqrt (t : ℝ)
    have hx : 0 ≤ x := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    have hlog : Real.log (1 + x) ≤ x := by
      linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith)]
    have hquad : C * x ≤ C ^ 2 / (4 * κ) + κ * x ^ 2 := by
      have h : C * x - κ * x ^ 2 ≤ C ^ 2 / (4 * κ) := by
        apply (le_div_iff₀ (by positivity : 0 < 4 * κ)).2
        nlinarith [sq_nonneg (2 * κ * x - C)]
      linarith
    have hx2 : x ^ 2 = ‖ζ‖ ^ 2 * (t : ℝ) := by
      dsimp [x]
      rw [mul_pow, Real.sq_sqrt t.coe_nonneg]
    have hforce : κ * ‖ζ‖ ^ 2 * (t : ℝ) = κ * x ^ 2 := by
      rw [hx2]
      ring
    rw [Real.rpow_def_of_pos (show 0 < 1 + x by linarith)]
    rw [hforce, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      Real.log (1 + x) * C ≤ x * C := mul_le_mul_of_nonneg_right hlog hC
      _ ≤ C ^ 2 / (4 * κ) + κ * x ^ 2 := by nlinarith [hquad]

/-- A sufficiently large growth rate absorbs both the polynomial and a fixed exponential. -/
theorem c6_flux_force_growth_budget (C Cp κ : ℝ) (hC : 0 ≤ C) (hCp : 0 ≤ Cp)
    (hκ : 0 < κ) :
    ∃ K growth₀ : ℝ, 1 ≤ K ∧ 0 < growth₀ ∧ ∀ growth : ℝ, growth₀ ≤ growth →
    ∀ (ζ : ℂ) (t : ℝ≥0),
      (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) ≤
      K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) := by
  obtain ⟨K, hK, hpoly⟩ := c6_flux_force_polynomial_absorption C κ hC hκ
  refine ⟨K, 8 * (Cp + κ + 1), hK, by positivity, ?_⟩
  intro growth hgrowth ζ t
  have hrate : κ + Cp + growth / 8 ≤ growth / 2 := by linarith
  have hq : 0 ≤ ‖ζ‖ ^ 2 * (t : ℝ) := mul_nonneg (sq_nonneg _) t.coe_nonneg
  have hexp : κ * ‖ζ‖ ^ 2 * (t : ℝ) + Cp * ‖ζ‖ ^ 2 * (t : ℝ) +
      growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8 ≤ growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrate) hq]
  calc
    _ ≤ (K * Real.exp (κ * ‖ζ‖ ^ 2 * (t : ℝ))) *
        Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) := by
          gcongr
          exact hpoly ζ t
    _ = K * Real.exp (κ * ‖ζ‖ ^ 2 * (t : ℝ) + Cp * ‖ζ‖ ^ 2 * (t : ℝ) +
        growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) := by rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by linarith)

/-- The force constraint and physical radius give the corresponding power bounds. -/
theorem c6_flux_bad_event_power_bounds (d : ℕ) (t r η : ℝ) (ζ : ℂ)
    (ht : 0 ≤ t) (hr : Real.sqrt t ≤ r)
    (hforce : ‖ζ‖ * Real.sqrt t ≤ t ^ η) :
    ‖ζ‖ ^ 2 * t ≤ t ^ (2 * η) ∧
      t ^ ((d : ℝ) / 4) ≤ r ^ ((d : ℝ) / 2) := by
  constructor
  · have hs : (‖ζ‖ * Real.sqrt t) ^ 2 ≤ (t ^ η) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hforce 2
    rw [mul_pow, Real.sq_sqrt ht] at hs
    have ht2 : (t ^ η) ^ 2 = t ^ (2 * η) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
      congr 1
      ring
    rwa [ht2] at hs
  · have h := Real.rpow_le_rpow (Real.sqrt_nonneg t) hr (show 0 ≤ (d : ℝ) / 2 by positivity)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht] at h
    convert h using 1 <;> congr 1 <;> ring

/-- A lower power is eventually dominated by any positive multiple of a higher power. -/
theorem c6_flux_lower_power_absorption (a b C ε : ℝ) (hab : a < b)
    (hε : 0 < ε) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t → C * t ^ a ≤ ε * t ^ b := by
  obtain ⟨T, hT⟩ := Filter.tendsto_atTop_atTop.mp
    (_root_.tendsto_rpow_atTop (show 0 < b - a by linarith)) (C / ε)
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have htpos : 0 < t := by linarith
  have hpow : C / ε ≤ t ^ (b - a) := hT t (le_trans (le_max_right _ _) ht)
  have hcoef : C ≤ ε * t ^ (b - a) := (div_le_iff₀' hε).mp hpow
  have hmul := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg htpos.le a)
  have heq : t ^ b = t ^ a * t ^ (b - a) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  rw [heq]
  nlinarith [hmul]

/-- A stretched exponential eventually dominates any real power. -/
theorem c6_flux_stretched_exp_absorption (q a b δ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 < δ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      t ^ q * Real.exp (-a * t ^ b) ≤ δ := by
  have hlim : Filter.Tendsto (fun t : ℝ => (t ^ b) ^ (q / b) *
      Real.exp (-a * t ^ b)) Filter.atTop (nhds 0) :=
    (_root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (q / b) a ha).comp
      (_root_.tendsto_rpow_atTop hb)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (eventually_lt_nhds hδ))
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have h := (hT t (le_trans (le_max_right _ _) ht)).le
  rw [← Real.rpow_mul (show 0 ≤ t by linarith)] at h
  have heq : b * (q / b) = q := by field_simp [ne_of_gt hb]
  simpa only [heq] using h

/-- The force growth leaves separate radius and time portions of the stretched tail. -/
theorem c6_flux_bad_event_exponent_budget
    (d : ℕ) (C c p η : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hp : 0 < p)
    (hsmall : 2 * η < (d : ℝ) / 4) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ (t r : ℝ) (ζ : ℂ), T ≤ t →
      Real.sqrt t ≤ r → ‖ζ‖ * Real.sqrt t ≤ t ^ η →
      C * ‖ζ‖ ^ 2 * t - c * r ^ ((d : ℝ) / 2) / (2 * p) ≤
        -(c / (8 * p)) * r ^ ((d : ℝ) / 2) -
          2 * (c / (8 * p)) * t ^ ((d : ℝ) / 4) := by
  have hk : 0 < c / (8 * p) := by positivity
  obtain ⟨T, hT, hpower⟩ := c6_flux_lower_power_absorption
    (2 * η) ((d : ℝ) / 4) C (c / (8 * p)) hsmall hk
  refine ⟨T, hT, ?_⟩
  intro t r ζ ht hr hf
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨hforce, hradius⟩ := c6_flux_bad_event_power_bounds d t r η ζ ht0 hr hf
  have hforce' := mul_le_mul_of_nonneg_left hforce hC
  have hradius' := mul_le_mul_of_nonneg_left hradius (le_of_lt hk)
  have hbudget := hpower t ht
  have hcoef : c / (2 * p) = 4 * (c / (8 * p)) := by
    field_simp [ne_of_gt hp] <;> ring
  have htail : c * r ^ ((d : ℝ) / 2) / (2 * p) =
      4 * (c / (8 * p)) * r ^ ((d : ℝ) / 2) := by
    rw [← hcoef]
    ring
  rw [htail]
  nlinarith [hforce', hradius', hbudget]

/-- A stretched exponential beats a polynomial with any prescribed power remainder. -/
theorem c6_flux_stretched_exp_power_remainder (q m a b δ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      t ^ q * Real.exp (-a * t ^ b) ≤ δ * t ^ (-m) := by
  obtain ⟨T, hT, h⟩ := c6_flux_stretched_exp_absorption (q + m) a b δ ha hb hδ
  refine ⟨T, hT, ?_⟩
  intro t ht
  have htpos : 0 < t := by linarith
  have hrem : 0 ≤ t ^ (-m) := Real.rpow_nonneg htpos.le _
  have hbound := mul_le_mul_of_nonneg_right (h t ht) hrem
  have heq : (t ^ (q + m) * Real.exp (-a * t ^ b)) * t ^ (-m) =
      t ^ q * Real.exp (-a * t ^ b) := by
    rw [Real.rpow_add htpos, Real.rpow_neg htpos.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos htpos m)] <;> ring
  rw [heq] at hbound
  exact hbound

/-- Uniform absorption of the actual-radius bad-event tail. -/
theorem c6_flux_bad_event_tail_absorption
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ) (C c p m η₀ : ℝ)
    (hC : 1 ≤ C) (hc : 0 < c) (hp : 2 ≤ p)
    (hsmall : 2 * η₀ < (d : ℝ) / 4) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ (t r : ℝ) (ζ : ℂ), t₀ ≤ t →
      Real.sqrt t ≤ r → ‖ζ‖ * Real.sqrt t ≤ t ^ η₀ →
      (1 + r) ^ d * (2 + t) ^ N *
        Real.exp (C * ‖ζ‖ ^ 2 * t - c * r ^ ((d : ℝ) / 2) / (2*p)) ≤ t ^ (-m) := by
  let k : ℝ := c / (8 * p)
  have hp0 : 0 < p := by linarith
  have hk : 0 < k := by dsimp [k]; positivity
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hδ : 0 < ((2 : ℝ) ^ d)⁻¹ / (3 : ℝ) ^ N := by positivity
  obtain ⟨T₁, hT₁, hexponent⟩ := c6_flux_bad_event_exponent_budget d C c p η₀
    (by linarith) hc hp0 hsmall
  obtain ⟨T₂, hT₂, hradius⟩ := c6_flux_stretched_exp_absorption (d : ℝ) k
    ((d : ℝ) / 2) 1 hk (by positivity) (by norm_num)
  obtain ⟨T₃, hT₃, htime⟩ := c6_flux_stretched_exp_power_remainder (N : ℝ) m
    (2 * k) ((d : ℝ) / 4) (((2 : ℝ) ^ d)⁻¹ / (3 : ℝ) ^ N)
    (by positivity) (by positivity) hδ
  refine ⟨max T₁ (max (T₂ ^ 2) T₃), le_trans hT₁ (le_max_left _ _), ?_⟩
  intro t r ζ ht hr hf
  have ht₁ : T₁ ≤ t := le_trans (le_max_left _ _) ht
  have ht₂ : T₂ ^ 2 ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have ht₃ : T₃ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht1 : 1 ≤ t := le_trans hT₁ ht₁
  have hr₂ : T₂ ≤ r := le_trans (Real.le_sqrt_of_sq_le ht₂) hr
  have hr1 : 1 ≤ r := le_trans hT₂ hr₂
  have hrad0 : r ^ d * Real.exp (-k * r ^ ((d : ℝ) / 2)) ≤ 1 := by
    simpa only [Real.rpow_natCast] using hradius r hr₂
  have hrpoly : (1 + r) ^ d ≤ (2 * r) ^ d :=
    pow_le_pow_left₀ (by linarith) (by linarith) d
  have hrad : (1 + r) ^ d * Real.exp (-k * r ^ ((d : ℝ) / 2)) ≤ (2 : ℝ) ^ d := by
    calc
      _ ≤ (2 * r) ^ d * Real.exp (-k * r ^ ((d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hrpoly (le_of_lt (Real.exp_pos _))
      _ = (2 : ℝ) ^ d * (r ^ d * Real.exp (-k * r ^ ((d : ℝ) / 2))) := by
        rw [mul_pow]; ring
      _ ≤ (2 : ℝ) ^ d * 1 :=
        mul_le_mul_of_nonneg_left hrad0 (by positivity)
      _ = _ := mul_one _
  have htpoly : (2 + t) ^ N ≤ (3 * t) ^ N :=
    pow_le_pow_left₀ (by linarith) (by linarith) N
  have htim : (2 + t) ^ N * Real.exp (-(2 * k) * t ^ ((d : ℝ) / 4)) ≤
      ((2 : ℝ) ^ d)⁻¹ * t ^ (-m) := by
    have hconst : (3 : ℝ) ^ N * (((2 : ℝ) ^ d)⁻¹ / (3 : ℝ) ^ N) =
        ((2 : ℝ) ^ d)⁻¹ := by
      have h3 : (3 : ℝ) ^ N ≠ 0 := by positivity
      field_simp [h3]
    calc
      _ ≤ (3 * t) ^ N * Real.exp (-(2 * k) * t ^ ((d : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_right htpoly (le_of_lt (Real.exp_pos _))
      _ = (3 : ℝ) ^ N * (t ^ N * Real.exp (-(2 * k) * t ^ ((d : ℝ) / 4))) := by
        rw [mul_pow]; ring
      _ ≤ (3 : ℝ) ^ N * ((((2 : ℝ) ^ d)⁻¹ / (3 : ℝ) ^ N) * t ^ (-m)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Real.rpow_natCast] using htime t ht₃
      _ = _ := by rw [← mul_assoc, hconst]
  have hexp := Real.exp_le_exp.mpr (hexponent t r ζ ht₁ hr hf)
  change Real.exp (C * ‖ζ‖ ^ 2 * t - c * r ^ ((d : ℝ) / 2) / (2*p)) ≤
    Real.exp (-k * r ^ ((d : ℝ) / 2) - 2 * k * t ^ ((d : ℝ) / 4)) at hexp
  have hexp' : Real.exp (C * ‖ζ‖ ^ 2 * t - c * r ^ ((d : ℝ) / 2) / (2*p)) ≤
      Real.exp (-k * r ^ ((d : ℝ) / 2)) *
        Real.exp (-(2 * k) * t ^ ((d : ℝ) / 4)) := by
    calc
      _ ≤ Real.exp (-k * r ^ ((d : ℝ) / 2) - 2 * k * t ^ ((d : ℝ) / 4)) := hexp
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hprod := mul_le_mul hrad htim (by positivity) (by positivity : 0 ≤ (2 : ℝ) ^ d)
  have hpow : (2 : ℝ) ^ d ≠ 0 := by positivity
  calc
    _ ≤ ((1 + r) ^ d * Real.exp (-k * r ^ ((d : ℝ) / 2))) *
        ((2 + t) ^ N * Real.exp (-(2 * k) * t ^ ((d : ℝ) / 4))) := by
          have h := mul_le_mul_of_nonneg_left hexp'
            (show 0 ≤ (1 + r) ^ d * (2 + t) ^ N by positivity)
          calc
            _ ≤ ((1 + r) ^ d * (2 + t) ^ N) *
                (Real.exp (-k * r ^ ((d : ℝ) / 2)) *
                  Real.exp (-(2 * k) * t ^ ((d : ℝ) / 4))) := h
            _ = _ := by ring
    _ ≤ (2 : ℝ) ^ d * (((2 : ℝ) ^ d)⁻¹ * t ^ (-m)) := hprod
    _ = t ^ (-m) := by field_simp [hpow]

/-- Absorption of the literal probability-tail prefactor at the physical radius. -/
theorem c6_flux_actual_radius_probability_tail_absorption
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ) (C Ctail c p m η η₀ : ℝ)
    (hC : 1 ≤ C) (hCt : 1 ≤ Ctail) (hc : 0 < c) (hp : 2 ≤ p)
    (hη : 0 ≤ η)
    (hsmall : 2 * η₀ < (d : ℝ) / 4) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ (t : ℝ) (ζ : ℂ), t₀ ≤ t →
      ‖ζ‖ * Real.sqrt t ≤ t ^ η₀ →
      let r := t ^ (1/2 + η)
      (1 + r) ^ d * (2 + t) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * t) *
        (Ctail * Real.exp (-c * r ^ ((d : ℝ)/2))) ^ (1/(2*p)) ≤ t ^ (-m) := by
  obtain ⟨T, hT, hbound⟩ := c6_flux_bad_event_tail_absorption d hd N C c p (m + 1) η₀
    hC hc hp hsmall
  refine ⟨max T (Ctail ^ (1 / (2 * p))), le_trans hT (le_max_left _ _), ?_⟩
  intro t ζ ht hf
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have ht1 : 1 ≤ t := le_trans hT htT
  have htpos : 0 < t := by linarith
  have hct : Ctail ^ (1 / (2 * p)) ≤ t := le_trans (le_max_right _ _) ht
  have hr : Real.sqrt t ≤ t ^ (1 / 2 + η) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have hb := hbound t (t ^ (1 / 2 + η)) ζ htT hr hf
  have hconst : 0 ≤ Ctail ^ (1 / (2 * p)) := Real.rpow_nonneg (by linarith) _
  have hmul := mul_le_mul_of_nonneg_left hb hconst
  have hpowers : t * t ^ (-(m + 1)) = t ^ (-m) := by
    calc
      _ = t ^ (1 : ℝ) * t ^ (-(m + 1)) := by rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) + (-(m + 1))) := (Real.rpow_add htpos _ _).symm
      _ = t ^ (-m) := by congr 1; ring
  have hfinal : Ctail ^ (1 / (2 * p)) * t ^ (-(m + 1)) ≤ t ^ (-m) := by
    calc
      _ ≤ t * t ^ (-(m + 1)) := mul_le_mul_of_nonneg_right hct (Real.rpow_nonneg htpos.le _)
      _ = _ := hpowers
  have heq : (Ctail * Real.exp (-c * (t ^ (1 / 2 + η)) ^ ((d : ℝ) / 2))) ^ (1 / (2 * p)) =
      Ctail ^ (1 / (2 * p)) * Real.exp (-c * (t ^ (1 / 2 + η)) ^ ((d : ℝ) / 2) / (2 * p)) := by
    rw [Real.mul_rpow (by linarith : 0 ≤ Ctail) (le_of_lt (Real.exp_pos _)), ← Real.exp_mul]
    congr 2
    ring
  dsimp only
  rw [heq]
  calc
    _ = Ctail ^ (1 / (2 * p)) * ((1 + t ^ (1 / 2 + η)) ^ d * (2 + t) ^ N *
        Real.exp (C * ‖ζ‖ ^ 2 * t - c * (t ^ (1 / 2 + η)) ^ ((d : ℝ) / 2) / (2 * p))) := by
          rw [show C * ‖ζ‖ ^ 2 * t - c * (t ^ (1 / 2 + η)) ^ ((d : ℝ) / 2) / (2 * p) =
            C * ‖ζ‖ ^ 2 * t + (-c * (t ^ (1 / 2 + η)) ^ ((d : ℝ) / 2) / (2 * p)) by ring, Real.exp_add]
          ring
    _ ≤ Ctail ^ (1 / (2 * p)) * t ^ (-(m + 1)) := hmul
    _ ≤ t ^ (-m) := hfinal

/-- Uniform bad-event budget for every radius above the diffusive scale. -/
theorem c6_flux_physical_event_bad_budget
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ) (A C Ctail c p m η₀ : ℝ)
    (hA : 0 ≤ A) (hC : 1 ≤ C) (hCt : 1 ≤ Ctail)
    (hc : 0 < c) (hp : 2 ≤ p)
    (hsmall : 2 * η₀ < (d : ℝ) / 4) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ (t r : ℝ) (ζ : ℂ), t₀ ≤ t →
      Real.sqrt t ≤ r → ‖ζ‖ * Real.sqrt t ≤ t ^ η₀ →
      A * (1 + r) ^ d * (2 + t) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * t) *
        (Ctail * Real.exp (-c * r ^ ((d : ℝ)/2))) ^ (1/(2*p)) ≤ t ^ (-m) := by
  obtain ⟨T, hT, hbound⟩ := c6_flux_bad_event_tail_absorption d hd N C c p (m + 1) η₀
    hC hc hp hsmall
  refine ⟨max T (A * Ctail ^ (1 / (2 * p))), le_trans hT (le_max_left _ _), ?_⟩
  intro t r ζ ht hr hf
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have htpos : 0 < t := by have := le_trans hT htT; linarith
  have hct : A * Ctail ^ (1 / (2 * p)) ≤ t := le_trans (le_max_right _ _) ht
  have hb := hbound t r ζ htT hr hf
  have hconst : 0 ≤ A * Ctail ^ (1 / (2 * p)) :=
    mul_nonneg hA (Real.rpow_nonneg (by linarith) _)
  have hmul := mul_le_mul_of_nonneg_left hb hconst
  have hpowers : t * t ^ (-(m + 1)) = t ^ (-m) := by
    calc
      _ = t ^ (1 : ℝ) * t ^ (-(m + 1)) := by rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) + (-(m + 1))) := (Real.rpow_add htpos _ _).symm
      _ = t ^ (-m) := by congr 1; ring
  have hfinal : (A * Ctail ^ (1 / (2 * p))) * t ^ (-(m + 1)) ≤ t ^ (-m) := by
    calc
      _ ≤ t * t ^ (-(m + 1)) := mul_le_mul_of_nonneg_right hct (Real.rpow_nonneg htpos.le _)
      _ = _ := hpowers
  have heq : (Ctail * Real.exp (-c * r ^ ((d : ℝ) / 2))) ^ (1 / (2 * p)) =
      Ctail ^ (1 / (2 * p)) * Real.exp (-c * r ^ ((d : ℝ) / 2) / (2 * p)) := by
    rw [Real.mul_rpow (by linarith : 0 ≤ Ctail) (le_of_lt (Real.exp_pos _)), ← Real.exp_mul]
    congr 2
    ring
  rw [heq]
  calc
    _ = (A * Ctail ^ (1 / (2 * p))) * ((1 + r) ^ d * (2 + t) ^ N *
        Real.exp (C * ‖ζ‖ ^ 2 * t - c * r ^ ((d : ℝ) / 2) / (2 * p))) := by
          rw [show C * ‖ζ‖ ^ 2 * t - c * r ^ ((d : ℝ) / 2) / (2 * p) =
            C * ‖ζ‖ ^ 2 * t + (-c * r ^ ((d : ℝ) / 2) / (2 * p)) by ring, Real.exp_add]
          ring
    _ ≤ (A * Ctail ^ (1 / (2 * p))) * t ^ (-(m + 1)) := hmul
    _ ≤ t ^ (-m) := hfinal

/-- The good and bad contributions share a single growth envelope. -/
theorem c6_flux_good_bad_final_budget
    (d : ℕ) (κ C Cp : ℝ) (hκ : 0 < κ) (hκhalf : κ < 1 / 2)
    (hC : 0 ≤ C) (hCp : 0 ≤ Cp) :
    ∃ A growth₀ : ℝ, 1 ≤ A ∧ 0 < growth₀ ∧
    ∀ growth : ℝ, growth₀ ≤ growth → ∀ (t : ℝ≥0) (ζ : ℂ), 1 ≤ (t : ℝ) →
    ∀ H K : ℝ, 0 ≤ H → 1 ≤ K →
    let η := κ / (16 * ((d : ℝ) + 2))
    let r := (t : ℝ) ^ (1 / 2 + η)
    H * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) +
      H * K * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        r ^ ((d : ℝ) + 1 - κ) *
        (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
        Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) ≤
      A * H * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
        (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        r ^ ((d : ℝ) + 1 - κ) := by
  obtain ⟨B, g₀, hB, hg₀, hbudget⟩ := c6_flux_force_growth_budget C Cp κ hC hCp hκ
  refine ⟨1 + B, g₀, by linarith, hg₀, ?_⟩
  intro growth hg t ζ ht H K hH hK
  dsimp only
  let η : ℝ := κ / (16 * ((d : ℝ) + 2))
  let r : ℝ := (t : ℝ) ^ (1 / 2 + η)
  let P : ℝ := (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4))
  let R : ℝ := r ^ ((d : ℝ) + 1 - κ)
  let E : ℝ := Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hr : 1 ≤ r := Real.one_le_rpow ht (by linarith : 0 ≤ 1 / 2 + η)
  have hR : 1 ≤ R := Real.one_le_rpow hr (by
    have hd : (0 : ℝ) ≤ d := by positivity
    linarith)
  have hE : 1 ≤ E := Real.one_le_exp (by
    have hgpos : 0 ≤ growth := by linarith
    positivity)
  have hP : 0 ≤ P := Real.rpow_nonneg t.coe_nonneg _
  have hKR : 1 ≤ K * E * R := by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hE), mul_nonneg (sub_nonneg.mpr (show 1 ≤ K * E by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hE)])) (sub_nonneg.mpr hR)]
  have hbad : H * P ≤ H * K * E * P * R := by
    nlinarith [mul_nonneg (mul_nonneg hH hP) (sub_nonneg.mpr hKR)]
  have hgood := mul_le_mul_of_nonneg_left (hbudget growth hg ζ t)
    (show 0 ≤ H * K * P * R by positivity)
  change H * P + H * K * P * R *
    (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
    Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
    Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) ≤
    (1 + B) * H * K * E * P * R
  nlinarith [hgood]


/-- The selected radius contributes a fixed dimension-dependent factor. -/
theorem c6_flux_selected_radius_final_budget
    (d : ℕ) (κ C Cp : ℝ) (hκ : 0 < κ) (hκhalf : κ < 1 / 2)
    (hC : 0 ≤ C) (hCp : 0 ≤ Cp) :
    ∃ A growth₀ : ℝ, 1 ≤ A ∧ 0 < growth₀ ∧
    ∀ growth : ℝ, growth₀ ≤ growth → ∀ (t : ℝ≥0) (ζ : ℂ), 1 ≤ (t : ℝ) →
    ∀ H K : ℝ, 0 ≤ H → 1 ≤ K →
    let η := κ / (16 * ((d : ℝ) + 2))
    let r := (t : ℝ) ^ (1 / 2 + η)
    let R := 2 * Real.sqrt (d : ℝ) + 3
    H * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) +
      H * K * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        (R * r) ^ ((d : ℝ) + 1 - κ) *
        (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
        Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) ≤
      A * H * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
        (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        r ^ ((d : ℝ) + 1 - κ) := by
  obtain ⟨A, g₀, hA, hg₀, hbudget⟩ :=
    c6_flux_good_bad_final_budget d κ C Cp hκ hκhalf hC hCp
  let R : ℝ := 2 * Real.sqrt (d : ℝ) + 3
  let B : ℝ := R ^ ((d : ℝ) + 1 - κ)
  have hR : 1 ≤ R := by dsimp [R]; have := Real.sqrt_nonneg (d : ℝ); linarith
  have hexp : 0 ≤ (d : ℝ) + 1 - κ := by
    have hd : (0 : ℝ) ≤ d := by positivity
    linarith
  have hB : 1 ≤ B := Real.one_le_rpow hR hexp
  refine ⟨B * A, g₀, by nlinarith, hg₀, ?_⟩
  intro growth hg t ζ ht H K hH hK
  dsimp only
  let r : ℝ := (t : ℝ) ^ (1 / 2 + κ / (16 * ((d : ℝ) + 2)))
  have hr : 0 ≤ r := Real.rpow_nonneg t.coe_nonneg _
  have hscaled := hbudget growth hg t ζ ht (B * H) K (by positivity) hK
  dsimp only at hscaled
  have hpow : (R * r) ^ ((d : ℝ) + 1 - κ) = B * r ^ ((d : ℝ) + 1 - κ) := by
    dsimp [B]
    exact Real.mul_rpow (by linarith : 0 ≤ R) hr
  have hbad : H * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) ≤
      (B * H) * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) := by
    exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg t.coe_nonneg _)
  change H * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) +
    H * K * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
      (R * r) ^ ((d : ℝ) + 1 - κ) *
      (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
      Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
      Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) ≤
    (B * A) * H * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
      (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ)
  rw [hpow]
  nlinarith [hscaled]

end EinsteinFull.Blueprint
