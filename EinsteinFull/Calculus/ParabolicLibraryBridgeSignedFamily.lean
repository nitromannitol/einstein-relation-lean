import EllipticRegularity.Parabolic.LocalMax.PowerFamilyStruct
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A sign-symmetric truncated power family

The library's power family `F, G` is built on `s ≥ 0`.  Composing with the smoothed absolute
value `sh σ s = √(s² + σ²) - σ` gives even functions on all of `ℝ` with the same structural
inequalities, `F ∈ C²`, `F''` bounded, `G ∈ C¹`, `G'` bounded, `F ≤ (|s| + ε)^p`, and
`G = (sh σ + ε)^{p/2}` while `sh σ ≤ N`.  This removes the sign hypothesis of the Moser power
step for solutions.
-/

open Filter Topology

noncomputable section
namespace EinsteinFull.SignedLocalMax

open PDE.Parabolic.LocalMax

/-- Smoothed absolute value. -/
def sh (σ s : ℝ) : ℝ := Real.sqrt (s ^ 2 + σ ^ 2) - σ

section Smoothing

variable {σ : ℝ}

theorem sqrt_ge (hσ : 0 < σ) (s : ℝ) : σ ≤ Real.sqrt (s ^ 2 + σ ^ 2) := by
  calc σ = Real.sqrt (σ ^ 2) := (Real.sqrt_sq hσ.le).symm
    _ ≤ Real.sqrt (s ^ 2 + σ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg s])

theorem abs_le_sqrt' (s : ℝ) : |s| ≤ Real.sqrt (s ^ 2 + σ ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg σ])

theorem sqrt_le_abs_add (hσ : 0 < σ) (s : ℝ) : Real.sqrt (s ^ 2 + σ ^ 2) ≤ |s| + σ := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_abs s, mul_nonneg (abs_nonneg s) hσ.le]

theorem sh_nonneg (hσ : 0 < σ) (s : ℝ) : 0 ≤ sh σ s := by
  unfold sh
  linarith [sqrt_ge hσ s]

theorem sh_le_abs (hσ : 0 < σ) (s : ℝ) : sh σ s ≤ |s| := by
  unfold sh
  linarith [sqrt_le_abs_add hσ s]

theorem abs_sub_le_sh (s : ℝ) : |s| - σ ≤ sh σ s := by
  unfold sh
  linarith [abs_le_sqrt' (σ := σ) s]

theorem sh_contDiff (hσ : 0 < σ) : ContDiff ℝ (⊤ : ℕ∞) (sh σ) := by
  unfold sh
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => s ^ 2 + σ ^ 2) :=
    (contDiff_id.pow 2).add contDiff_const
  exact (h1.sqrt fun s => by positivity).sub contDiff_const

theorem sqrt_pos' (hσ : 0 < σ) (s : ℝ) : 0 < Real.sqrt (s ^ 2 + σ ^ 2) :=
  Real.sqrt_pos.2 (by positivity)

theorem sqrt_sq' (s : ℝ) : Real.sqrt (s ^ 2 + σ ^ 2) ^ 2 = s ^ 2 + σ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem sh_hasDerivAt (hσ : 0 < σ) (s : ℝ) :
    HasDerivAt (sh σ) (s / Real.sqrt (s ^ 2 + σ ^ 2)) s := by
  have hpos : 0 < s ^ 2 + σ ^ 2 := by positivity
  have hr := sqrt_pos' hσ s
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + σ ^ 2) (2 * s) s := by
    have := ((hasDerivAt_id s).pow 2).add_const (σ ^ 2)
    simpa using this
  have h2 := (h1.sqrt hpos.ne').sub_const σ
  exact h2.congr_deriv (by field_simp)

theorem sh'_hasDerivAt (hσ : 0 < σ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => s / Real.sqrt (s ^ 2 + σ ^ 2))
      (σ ^ 2 / Real.sqrt (s ^ 2 + σ ^ 2) ^ 3) s := by
  have hpos : 0 < s ^ 2 + σ ^ 2 := by positivity
  have hr := sqrt_pos' hσ s
  have e := sqrt_sq' (σ := σ) s
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + σ ^ 2) (2 * s) s := by
    have := ((hasDerivAt_id s).pow 2).add_const (σ ^ 2)
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + σ ^ 2))
      (s / Real.sqrt (s ^ 2 + σ ^ 2)) s :=
    (h1.sqrt hpos.ne').congr_deriv (by field_simp)
  have h3 := (hasDerivAt_id s).div h2 hr.ne'
  refine h3.congr_deriv ?_
  simp only [id]
  field_simp
  nlinarith [e]

theorem abs_sh'_le (hσ : 0 < σ) (s : ℝ) : |s / Real.sqrt (s ^ 2 + σ ^ 2)| ≤ 1 := by
  have hr := sqrt_pos' hσ s
  rw [abs_div, abs_of_pos hr, div_le_one hr]
  exact abs_le_sqrt' s

theorem sh''_nonneg (hσ : 0 < σ) (s : ℝ) : 0 ≤ σ ^ 2 / Real.sqrt (s ^ 2 + σ ^ 2) ^ 3 := by
  have := sqrt_pos' hσ s
  positivity

theorem sh''_le (hσ : 0 < σ) (s : ℝ) : σ ^ 2 / Real.sqrt (s ^ 2 + σ ^ 2) ^ 3 ≤ 1 / σ := by
  have hr := sqrt_pos' hσ s
  have h1 := sqrt_ge hσ s
  rw [div_le_div_iff₀ (by positivity) hσ]
  have : σ ^ 3 ≤ Real.sqrt (s ^ 2 + σ ^ 2) ^ 3 := pow_le_pow_left₀ hσ.le h1 3
  nlinarith

theorem sh''_mul_abs_le (hσ : 0 < σ) (s : ℝ) :
    σ ^ 2 / Real.sqrt (s ^ 2 + σ ^ 2) ^ 3 * |s| ≤ 1 := by
  have hr := sqrt_pos' hσ s
  have h1 := sqrt_ge hσ s
  have h2 := abs_le_sqrt' (σ := σ) s
  rw [div_mul_eq_mul_div, div_le_one (by positivity)]
  have h3 : σ ^ 2 ≤ Real.sqrt (s ^ 2 + σ ^ 2) ^ 2 := pow_le_pow_left₀ hσ.le h1 2
  calc σ ^ 2 * |s| ≤ Real.sqrt (s ^ 2 + σ ^ 2) ^ 2 * Real.sqrt (s ^ 2 + σ ^ 2) :=
        mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
    _ = Real.sqrt (s ^ 2 + σ ^ 2) ^ 3 := by ring

end Smoothing

section Structure

/-- The structural inequalities of the library family at a nonnegative argument. -/
theorem struct_key {p ε N s : ℝ} (hp : 1 < p) (hε : 0 < ε) (hN : 0 ≤ N) (hs : 0 ≤ s) :
    powF1 p ε N s ^ 2 ≤ (2 + p / (p - 1)) * powF2 p ε N s * powF p ε N s ∧
      powG p ε N s ^ 2 ≤ (2 + p / (p - 1)) * powF p ε N s ∧
      powG1 p ε N s ^ 2 ≤ (2 + p / (p - 1)) * powF2 p ε N s := by
  have hp1 : 0 < p - 1 := by linarith
  have hK : (2 + p / (p - 1)) * (p - 1) = 3 * p - 2 := by field_simp; ring
  have hK2 : 2 ≤ 2 + p / (p - 1) := by
    have : 0 ≤ p / (p - 1) := div_nonneg (by linarith) hp1.le
    linarith
  generalize 2 + p / (p - 1) = K at hK hK2 ⊢
  by_cases hc : p ≤ 2 ∨ s ≤ N
  · have hw : 0 < s + ε := by linarith
    obtain ⟨h1, h2, h3, h4⟩ := rpow_split hw p
    have ha : 0 < (s + ε) ^ (p - 2) := Real.rpow_pos_of_pos hw _
    have := struct_ineqs_uncapped hp hK hK2 ha h4 hw
    rw [powF1_eq_of_le hε hs hc, powF2, powCap_eq_of_le hs hc, powF_eq_of_le hε hs hc,
      powG_eq_of_le hε hs hc, powG1, powCap_eq_of_le hs hc, h1, h2, h3]
    exact this
  · push Not at hc
    obtain ⟨hp2, hsN⟩ := hc
    have hL : 0 < N + ε := by linarith
    obtain ⟨h1, h2, h3, h4⟩ := rpow_split hL p
    have ha : 0 < (N + ε) ^ (p - 2) := Real.rpow_pos_of_pos hL _
    have := struct_ineqs_capped hp2 hK hK2 ha h4 hL (sub_nonneg.2 hsN.le)
    have hcap' : powCap p ε N s = N + ε := powCap_eq_cap hp2 hsN.le hN
    rw [powF1_eq_of_ge hp2 hε hN hsN.le, powF2, hcap', powF_eq_of_ge hp2 hε hN hsN.le,
      powG_eq_of_ge hp2 hε hN hsN.le, powG1, hcap', h1, h2, h3]
    convert this using 3 <;> ring

/-- Linear growth of `F'`. -/
theorem powF1_le_linear {p ε N : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) {C : ℝ}
    (hC : ∀ s, powF2 p ε N s ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    powF1 p ε N t ≤ p * ε ^ (p - 1) + C * t := by
  unfold powF1
  have h : ∫ r in (0 : ℝ)..t, powF2 p ε N r ≤ ∫ _r in (0 : ℝ)..t, C :=
    intervalIntegral.integral_mono_on ht
      ((powF2_continuous hε hN).intervalIntegrable _ _) intervalIntegrable_const
      fun r _ => hC r
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

end Structure

section Family

/-- The sign-symmetric truncated power family. -/
theorem exists_signedFamily {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) {N σ : ℝ} (hN : 0 ≤ N)
    (hσ : 0 < σ) :
    ∃ F G : ℝ → ℝ, ContDiff ℝ 2 F ∧ (∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C) ∧
      ContDiff ℝ 1 G ∧ (∃ M : ℝ, 0 ≤ M ∧ ∀ s, |deriv G s| ≤ M) ∧
      ∀ s, 0 ≤ F s ∧ 0 ≤ deriv (deriv F) s ∧
        deriv F s ^ 2 ≤ (2 + p / (p - 1)) * deriv (deriv F) s * F s ∧
        G s ^ 2 ≤ (2 + p / (p - 1)) * F s ∧
        deriv G s ^ 2 ≤ (2 + p / (p - 1)) * deriv (deriv F) s ∧
        F s ≤ (|s| + ε) ^ p ∧ 0 ≤ G s ∧ (sh σ s ≤ N → G s = (sh σ s + ε) ^ (p / 2)) := by
  have hp0 : 0 < p := by linarith
  let F : ℝ → ℝ := fun s => powF p ε N (sh σ s)
  let G : ℝ → ℝ := fun s => powG p ε N (sh σ s)
  let h1 : ℝ → ℝ := fun s => s / Real.sqrt (s ^ 2 + σ ^ 2)
  let h2 : ℝ → ℝ := fun s => σ ^ 2 / Real.sqrt (s ^ 2 + σ ^ 2) ^ 3
  have hshc : ContDiff ℝ 2 (sh σ) := by
    have hf := sh_contDiff hσ
    first
      | exact hf.of_le (by exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
      | exact hf.of_le (by simp)
      | exact hf.of_le (by norm_cast; exact le_top)
      | exact hf.of_le (WithTop.coe_le_coe.2 le_top)
  have hshc1 : ContDiff ℝ 1 (sh σ) := by
    have hf := sh_contDiff hσ
    first
      | exact hf.of_le (by exact_mod_cast (le_top : ((1 : ℕ) : ℕ∞) ≤ ⊤))
      | exact hf.of_le (by simp)
      | exact hf.of_le (by norm_cast; exact le_top)
      | exact hf.of_le (WithTop.coe_le_coe.2 le_top)
  have hF1 : ∀ s, HasDerivAt F (powF1 p ε N (sh σ s) * h1 s) s := fun s =>
    (powF_hasDerivAt hε hN (sh σ s)).comp s (sh_hasDerivAt hσ s)
  have hdF : deriv F = fun s => powF1 p ε N (sh σ s) * h1 s := funext fun s => (hF1 s).deriv
  have hF2 : ∀ s, HasDerivAt (deriv F)
      (powF2 p ε N (sh σ s) * h1 s * h1 s + powF1 p ε N (sh σ s) * h2 s) s := by
    intro s
    rw [hdF]
    exact ((powF1_hasDerivAt hε hN (sh σ s)).comp s (sh_hasDerivAt hσ s)).mul
      (sh'_hasDerivAt hσ s)
  have hddF : ∀ s, deriv (deriv F) s =
      powF2 p ε N (sh σ s) * h1 s * h1 s + powF1 p ε N (sh σ s) * h2 s :=
    fun s => (hF2 s).deriv
  have hG1 : ∀ s, HasDerivAt G (powG1 p ε N (sh σ s) * h1 s) s := fun s =>
    (powG_hasDerivAt hε hN (sh σ s)).comp s (sh_hasDerivAt hσ s)
  have hdG : ∀ s, deriv G s = powG1 p ε N (sh σ s) * h1 s := fun s => (hG1 s).deriv
  obtain ⟨C₀, hC₀⟩ := exists_powF2_bound hp hε hN
  obtain ⟨M₀, hM₀, hM₀b⟩ := exists_powG1_bound hp hε hN
  have hC₀' : ∀ s, powF2 p ε N s ≤ (C₀ : ℝ) := fun s => by
    have := hC₀ s
    rw [deriv_deriv_powF hε hN, abs_of_nonneg (powF2_nonneg hp hε hN s)] at this
    exact this
  have hM₀' : ∀ s, powG1 p ε N s ≤ M₀ := fun s => by
    have := hM₀b s
    rw [deriv_powG hε hN, abs_of_nonneg (powG1_nonneg hp hε hN s)] at this
    exact this
  have hA0 : 0 ≤ p * ε ^ (p - 1) := mul_nonneg hp0.le (Real.rpow_nonneg hε.le _)
  have hC0 : (0 : ℝ) ≤ C₀ := by
    have := hC₀' 0
    have := powF2_nonneg hp hε hN 0
    linarith
  refine ⟨F, G, (powF_contDiff hε hN).comp hshc, ?_, (powG_contDiff hε hN).comp hshc1, ?_, ?_⟩
  · refine ⟨(C₀ + (p * ε ^ (p - 1) / σ + C₀)).toNNReal, fun s => ?_⟩
    refine le_trans ?_ (Real.le_coe_toNNReal _)
    rw [hddF s]
    have ht := sh_nonneg hσ s
    have hh1 := abs_sh'_le hσ s
    have hh2 := sh''_nonneg hσ s
    have hh2a := sh''_le hσ s
    have hh2b := sh''_mul_abs_le hσ s
    have hF2n := powF2_nonneg hp hε hN (sh σ s)
    have hF1n := powF1_nonneg hp hε hN ht
    have hF1l := powF1_le_linear hε hN hC₀' ht
    have hshle := sh_le_abs hσ s
    have hhsq : h1 s * h1 s ≤ 1 := by
      have : |h1 s| * |h1 s| ≤ 1 * 1 := mul_le_mul hh1 hh1 (abs_nonneg _) zero_le_one
      rw [← abs_mul, abs_mul_self] at this
      linarith
    have hhsq0 : 0 ≤ h1 s * h1 s := mul_self_nonneg _
    have t1 : powF2 p ε N (sh σ s) * h1 s * h1 s ≤ C₀ := by
      calc powF2 p ε N (sh σ s) * h1 s * h1 s = powF2 p ε N (sh σ s) * (h1 s * h1 s) := by ring
        _ ≤ powF2 p ε N (sh σ s) * 1 := mul_le_mul_of_nonneg_left hhsq hF2n
        _ ≤ C₀ := by rw [mul_one]; exact hC₀' _
    have t2 : powF1 p ε N (sh σ s) * h2 s ≤ p * ε ^ (p - 1) / σ + C₀ := by
      calc powF1 p ε N (sh σ s) * h2 s
          ≤ (p * ε ^ (p - 1) + C₀ * sh σ s) * h2 s := mul_le_mul_of_nonneg_right hF1l hh2
        _ = p * ε ^ (p - 1) * h2 s + C₀ * (sh σ s * h2 s) := by ring
        _ ≤ p * ε ^ (p - 1) * (1 / σ) + C₀ * 1 := by
            refine add_le_add (mul_le_mul_of_nonneg_left hh2a hA0) (mul_le_mul_of_nonneg_left ?_ hC0)
            calc sh σ s * h2 s ≤ |s| * h2 s := mul_le_mul_of_nonneg_right hshle hh2
              _ = h2 s * |s| := mul_comm _ _
              _ ≤ 1 := hh2b
        _ = p * ε ^ (p - 1) / σ + C₀ := by ring
    have t3 : 0 ≤ powF2 p ε N (sh σ s) * h1 s * h1 s + powF1 p ε N (sh σ s) * h2 s := by
      have : 0 ≤ powF2 p ε N (sh σ s) * (h1 s * h1 s) := mul_nonneg hF2n hhsq0
      have : 0 ≤ powF1 p ε N (sh σ s) * h2 s := mul_nonneg hF1n hh2
      nlinarith
    rw [abs_of_nonneg t3]
    linarith
  · refine ⟨M₀, hM₀, fun s => ?_⟩
    rw [hdG s]
    have hh1 := abs_sh'_le hσ s
    rw [abs_mul, abs_of_nonneg (powG1_nonneg hp hε hN _)]
    calc powG1 p ε N (sh σ s) * |h1 s| ≤ M₀ * 1 :=
          mul_le_mul (hM₀' _) hh1 (abs_nonneg _) hM₀
      _ = M₀ := mul_one _
  · intro s
    have ht := sh_nonneg hσ s
    obtain ⟨k1, k2, k3⟩ := struct_key hp hε hN ht
    have hh2 := sh''_nonneg hσ s
    have hF2n := powF2_nonneg hp hε hN (sh σ s)
    have hF1n := powF1_nonneg hp hε hN ht
    have hF0 := powF_nonneg hp hε hN ht
    have hhsq0 : 0 ≤ h1 s * h1 s := mul_self_nonneg _
    have hK : 0 ≤ 2 + p / (p - 1) := by
      have : 0 ≤ p / (p - 1) := div_nonneg hp0.le (by linarith)
      linarith
    have hterm : 0 ≤ powF1 p ε N (sh σ s) * h2 s := mul_nonneg hF1n hh2
    have hmain : 0 ≤ powF2 p ε N (sh σ s) * h1 s * h1 s + powF1 p ε N (sh σ s) * h2 s := by
      have : 0 ≤ powF2 p ε N (sh σ s) * (h1 s * h1 s) := mul_nonneg hF2n hhsq0
      nlinarith
    refine ⟨hF0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hddF s]; exact hmain
    · rw [hddF s, hdF]
      show (powF1 p ε N (sh σ s) * h1 s) ^ 2 ≤ _
      have e1 : (powF1 p ε N (sh σ s) * h1 s) ^ 2 = powF1 p ε N (sh σ s) ^ 2 * (h1 s * h1 s) := by
        ring
      rw [e1]
      calc powF1 p ε N (sh σ s) ^ 2 * (h1 s * h1 s)
          ≤ ((2 + p / (p - 1)) * powF2 p ε N (sh σ s) * powF p ε N (sh σ s)) * (h1 s * h1 s) :=
            mul_le_mul_of_nonneg_right k1 hhsq0
        _ ≤ (2 + p / (p - 1)) * (powF2 p ε N (sh σ s) * h1 s * h1 s +
              powF1 p ε N (sh σ s) * h2 s) * powF p ε N (sh σ s) := by
            have : 0 ≤ (2 + p / (p - 1)) * (powF1 p ε N (sh σ s) * h2 s) * powF p ε N (sh σ s) :=
              mul_nonneg (mul_nonneg hK hterm) hF0
            nlinarith
    · exact k2
    · rw [hdG s, hddF s]
      have e1 : (powG1 p ε N (sh σ s) * h1 s) ^ 2 = powG1 p ε N (sh σ s) ^ 2 * (h1 s * h1 s) := by
        ring
      rw [e1]
      calc powG1 p ε N (sh σ s) ^ 2 * (h1 s * h1 s)
          ≤ ((2 + p / (p - 1)) * powF2 p ε N (sh σ s)) * (h1 s * h1 s) :=
            mul_le_mul_of_nonneg_right k3 hhsq0
        _ ≤ (2 + p / (p - 1)) * (powF2 p ε N (sh σ s) * h1 s * h1 s +
              powF1 p ε N (sh σ s) * h2 s) := by
            have : 0 ≤ (2 + p / (p - 1)) * (powF1 p ε N (sh σ s) * h2 s) := mul_nonneg hK hterm
            nlinarith
    · refine (powF_le hp hε hN ht).trans ?_
      exact Real.rpow_le_rpow (by linarith) (by linarith [sh_le_abs hσ s]) hp0.le
    · exact powG_nonneg hp hε hN ht
    · intro hsN
      exact powG_eq_of_le hε ht (Or.inr hsN)

end Family

end EinsteinFull.SignedLocalMax
