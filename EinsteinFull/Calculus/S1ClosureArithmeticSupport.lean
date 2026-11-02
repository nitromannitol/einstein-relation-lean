import EinsteinFull.Calculus.S1CovarianceL2Support
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt

/-! Dyadic-scale and exponent bookkeeping, and the Euclidean bounds for a
Frobenius-bounded matrix, used to close the covariance argument from its
intermediate estimates. -/

open MeasureTheory

namespace EinsteinFull.Calculus.S1

/-! ### The dyadic scale `L = 2 ^ ⌊log (R ^ θ) / log 2⌋` -/

theorem dyadic_scale_bounds {R θ L : ℝ} (hR : 1 ≤ R) (hθ : 0 < θ)
    (hL : L = (2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2)) :
    0 < L ∧ L ≤ R ^ θ ∧ R ^ θ ≤ 2 * L := by
  have hx1 : 1 ≤ R ^ θ := Real.one_le_rpow hR hθ.le
  generalize R ^ θ = x at hx1 hL ⊢
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2t : (2 : ℝ) ^ (Real.log x / Real.log 2) = x :=
    Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  generalize Real.log x / Real.log 2 = t at h2t hL
  have hLeq : L = (2 : ℝ) ^ ((⌊t⌋ : ℤ) : ℝ) := by rw [hL, Real.rpow_intCast]
  have hle : ((⌊t⌋ : ℤ) : ℝ) ≤ t := Int.floor_le t
  have hlt : t < ((⌊t⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one t
  refine ⟨?_, ?_, ?_⟩
  · rw [hLeq]
    positivity
  · calc L = (2 : ℝ) ^ ((⌊t⌋ : ℤ) : ℝ) := hLeq
      _ ≤ (2 : ℝ) ^ t := Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = x := h2t
  · calc x = (2 : ℝ) ^ t := h2t.symm
      _ ≤ (2 : ℝ) ^ (((⌊t⌋ : ℤ) : ℝ) + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hlt.le
      _ = (2 : ℝ) ^ ((⌊t⌋ : ℤ) : ℝ) * 2 := Real.rpow_add_one (by norm_num) _
      _ = 2 * L := by rw [hLeq]; ring

theorem rpow_neg_le_rpow_neg {R a b : ℝ} (hR : 1 ≤ R) (hab : a ≤ b) :
    R ^ (-b) ≤ R ^ (-a) :=
  Real.rpow_le_rpow_of_exponent_le hR (by linarith)

theorem scale_bound_sq {R θ η L : ℝ} (hR : 1 ≤ R) (hL0 : 0 < L) (hLR : L ≤ R ^ θ)
    (hη : 0 ≤ η) : (L ^ η / R) ^ 2 ≤ R ^ (-(2 * (1 - θ * η))) := by
  have hR0 : 0 < R := by linarith
  have h1 : L ^ η ≤ R ^ (θ * η) := by
    calc L ^ η ≤ (R ^ θ) ^ η := Real.rpow_le_rpow hL0.le hLR hη
      _ = R ^ (θ * η) := (Real.rpow_mul hR0.le _ _).symm
  have h2 : L ^ η / R ≤ R ^ (θ * η - 1) := by
    rw [Real.rpow_sub_one hR0.ne']
    gcongr
  calc (L ^ η / R) ^ 2 ≤ (R ^ (θ * η - 1)) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg (Real.rpow_nonneg hL0.le _) hR0.le) h2 2
    _ = R ^ (-(2 * (1 - θ * η))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
        congr 1
        push_cast
        ring

theorem rpow_neg_scale_le {R θ L q : ℝ} (hR : 1 ≤ R) (hL0 : 0 < L) (hL2 : R ^ θ ≤ 2 * L)
    (hq : 0 ≤ q) : L ^ (-q) ≤ 2 ^ q * R ^ (-(θ * q)) := by
  have hR0 : 0 < R := by linarith
  have hRθ : 0 < R ^ θ := Real.rpow_pos_of_pos hR0 _
  have h1 : (R ^ θ / 2) ^ q ≤ L ^ q :=
    Real.rpow_le_rpow (by positivity) (by linarith) hq
  have h2 : (R ^ θ / 2) ^ q = R ^ (θ * q) / 2 ^ q := by
    rw [Real.div_rpow hRθ.le (by norm_num), ← Real.rpow_mul hR0.le]
  have h3 : 0 < (R ^ θ / 2) ^ q := by positivity
  rw [Real.rpow_neg hL0.le]
  calc (L ^ q)⁻¹ ≤ ((R ^ θ / 2) ^ q)⁻¹ := inv_anti₀ h3 h1
    _ = 2 ^ q * R ^ (-(θ * q)) := by
        rw [h2, inv_div, Real.rpow_neg hR0.le]
        ring

theorem scale_ratio_le {R θ L : ℝ} (hR : 1 ≤ R) (hLR : L ≤ R ^ θ) :
    L / R ≤ R ^ (-(1 - θ)) := by
  have hR0 : 0 < R := by linarith
  calc L / R ≤ R ^ θ / R := by gcongr
    _ = R ^ (-(1 - θ)) := by
        rw [← Real.rpow_sub_one hR0.ne']
        congr 1
        ring

theorem scale_bound_B {R θ η L p d : ℝ} (hR : 1 ≤ R) (hL0 : 0 < L) (hL2 : R ^ θ ≤ 2 * L)
    (hη : 0 ≤ η) (hp : 0 ≤ p) :
    R ^ d * (L ^ η) ^ (-p) ≤ 2 ^ (η * p) * R ^ (d - θ * (η * p)) := by
  have hR0 : 0 < R := by linarith
  have h := rpow_neg_scale_le (θ := θ) hR hL0 hL2 (mul_nonneg hη hp)
  have e : (L ^ η) ^ (-p) = L ^ (-(η * p)) := by
    rw [← Real.rpow_mul hL0.le]
    congr 1
    ring
  rw [e]
  calc R ^ d * L ^ (-(η * p)) ≤ R ^ d * (2 ^ (η * p) * R ^ (-(θ * (η * p)))) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hR0.le _)
    _ = 2 ^ (η * p) * R ^ (d - θ * (η * p)) := by
        rw [sub_eq_add_neg, Real.rpow_add hR0]
        ring

theorem scale_estimates {R θ η β κ γ d L ε : ℝ} (hR : 1 ≤ R) (hL0 : 0 < L)
    (hLR : L ≤ R ^ θ) (hL2 : R ^ θ ≤ 2 * L) (hη : 0 ≤ η) (hd : 0 ≤ d) (hγ : 0 ≤ γ)
    (hβ : β ≤ 1) (hκ : 0 ≤ κ)
    (hε1 : ε ≤ 2 * (1 - θ * η)) (hε2 : ε ≤ θ * η * d - d / 2)
    (hε3 : ε ≤ θ * η * γ - d / 2) (hε4 : ε ≤ 1 - θ)
    (hε5 : ε ≤ θ * ((1 - β) / 2)) (hε6 : ε ≤ θ * κ) :
    (L ^ η / R) ^ 2 ≤ R ^ (-ε) ∧
    R ^ (d / 2) * ((L ^ η) ^ (-d) + (L ^ η) ^ (-γ)) ≤
      (2 ^ (η * d) + 2 ^ (η * γ)) * R ^ (-ε) ∧
    L / R + L ^ (-(1 - β) / 2) ≤ (1 + 2 ^ ((1 - β) / 2)) * R ^ (-ε) ∧
    L ^ (-κ) + L / R ≤ (2 ^ κ + 1) * R ^ (-ε) := by
  have hR0 : 0 < R := by linarith
  have hEmono : ∀ e : ℝ, ε ≤ e → R ^ (-e) ≤ R ^ (-ε) := fun e he =>
    rpow_neg_le_rpow_neg hR he
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (scale_bound_sq hR hL0 hLR hη).trans (hEmono _ hε1)
  · have hB1 := scale_bound_B (θ := θ) (η := η) (d := d / 2) (p := d) hR hL0 hL2 hη hd
    have hB2 := scale_bound_B (θ := θ) (η := η) (d := d / 2) (p := γ) hR hL0 hL2 hη hγ
    have m1 : R ^ (d / 2 - θ * (η * d)) ≤ R ^ (-ε) :=
      Real.rpow_le_rpow_of_exponent_le hR (by linarith)
    have m2 : R ^ (d / 2 - θ * (η * γ)) ≤ R ^ (-ε) :=
      Real.rpow_le_rpow_of_exponent_le hR (by linarith)
    calc R ^ (d / 2) * ((L ^ η) ^ (-d) + (L ^ η) ^ (-γ))
        = R ^ (d / 2) * (L ^ η) ^ (-d) + R ^ (d / 2) * (L ^ η) ^ (-γ) := mul_add _ _ _
      _ ≤ 2 ^ (η * d) * R ^ (d / 2 - θ * (η * d)) +
          2 ^ (η * γ) * R ^ (d / 2 - θ * (η * γ)) := add_le_add hB1 hB2
      _ ≤ 2 ^ (η * d) * R ^ (-ε) + 2 ^ (η * γ) * R ^ (-ε) :=
          add_le_add (mul_le_mul_of_nonneg_left m1 (by positivity))
            (mul_le_mul_of_nonneg_left m2 (by positivity))
      _ = (2 ^ (η * d) + 2 ^ (η * γ)) * R ^ (-ε) := by ring
  · have h1 := scale_ratio_le (θ := θ) hR hLR
    have h2 := rpow_neg_scale_le (θ := θ) hR hL0 hL2 (q := (1 - β) / 2) (by linarith)
    have e : -(1 - β) / 2 = -((1 - β) / 2) := by ring
    rw [e]
    have m1 : R ^ (-(1 - θ)) ≤ R ^ (-ε) := hEmono _ hε4
    have m2 : R ^ (-(θ * ((1 - β) / 2))) ≤ R ^ (-ε) := hEmono _ hε5
    calc L / R + L ^ (-((1 - β) / 2))
        ≤ R ^ (-ε) + 2 ^ ((1 - β) / 2) * R ^ (-ε) :=
          add_le_add (h1.trans m1)
            (h2.trans (mul_le_mul_of_nonneg_left m2 (by positivity)))
      _ = (1 + 2 ^ ((1 - β) / 2)) * R ^ (-ε) := by ring
  · have h1 := scale_ratio_le (θ := θ) hR hLR
    have h2 := rpow_neg_scale_le (θ := θ) hR hL0 hL2 hκ
    calc L ^ (-κ) + L / R ≤ 2 ^ κ * R ^ (-ε) + R ^ (-ε) :=
          add_le_add (h2.trans (mul_le_mul_of_nonneg_left (hEmono _ hε6) (by positivity)))
            (h1.trans (hEmono _ hε4))
      _ = (2 ^ κ + 1) * R ^ (-ε) := by ring

theorem exists_common_eps (a b c e f g : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : 0 < e) (hf : 0 < f) (hg : 0 < g) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ a ∧ ε ≤ b ∧ ε ≤ c ∧ ε ≤ e ∧ ε ≤ f ∧ ε ≤ g :=
  ⟨min a (min b (min c (min e (min f g)))),
    lt_min ha (lt_min hb (lt_min hc (lt_min he (lt_min hf hg)))),
    min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))),
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))),
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))⟩

/-- Three-term triangle inequality for mean-square sizes. -/
theorem l2Size_sub_le_three {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U S L Y : Ω → ℂ} (hU : MemLp U 2 μ) (hS : MemLp S 2 μ) (hL : MemLp L 2 μ)
    (hY : MemLp Y 2 μ) :
    l2Size μ (U - Y) ≤ l2Size μ (U - S) + l2Size μ (S - L) + l2Size μ (L - Y) := by
  have e : U - Y = ((U - S) + (S - L)) + (L - Y) := by
    funext ω
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [e]
  calc l2Size μ (((U - S) + (S - L)) + (L - Y))
      ≤ l2Size μ ((U - S) + (S - L)) + l2Size μ (L - Y) :=
        l2Size_add_le ((hU.sub hS).add (hS.sub hL)) (hL.sub hY)
    _ ≤ (l2Size μ (U - S) + l2Size μ (S - L)) + l2Size μ (L - Y) := by
        gcongr
        exact l2Size_add_le (hU.sub hS) (hS.sub hL)

/-- The assembled large-scale estimate: the intermediate approximations
(smoothing, localization, trimmed blocks), the test bound for the actual pairing and
the covariance limit of the trimmed blocks give the all-scale covariance bound. -/
theorem closure_large_scale_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {UF UG SF SG LF LG YF YG : Ω → ℂ} {T : ℂ}
    (hUF : MemLp UF 2 μ) (hUG : MemLp UG 2 μ) (hSF : MemLp SF 2 μ) (hSG : MemLp SG 2 μ)
    (hLF : MemLp LF 2 μ) (hLG : MemLp LG 2 μ) (hYF : MemLp YF 2 μ) (hYG : MemLp YG 2 μ)
    {R θ η β κ γ d L ε C₁ C₂ C₄ nF nG : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hnF : 0 ≤ nF) (hnG : 0 ≤ nG)
    (hR : 1 ≤ R) (hL0 : 0 < L) (hLR : L ≤ R ^ θ) (hL2 : R ^ θ ≤ 2 * L)
    (hη : 0 ≤ η) (hd : 0 ≤ d) (hγ : 0 ≤ γ) (hβ : β ≤ 1) (hκ : 0 ≤ κ)
    (hε1 : ε ≤ 2 * (1 - θ * η)) (hε2 : ε ≤ θ * η * d - d / 2)
    (hε3 : ε ≤ θ * η * γ - d / 2) (hε4 : ε ≤ 1 - θ)
    (hε5 : ε ≤ θ * ((1 - β) / 2)) (hε6 : ε ≤ θ * κ)
    (e1F : Real.sqrt (∫ ω, ‖UF ω - SF ω‖ ^ 2 ∂μ) ≤ C₁ * nF * (L ^ η / R) ^ 2)
    (e2F : Real.sqrt (∫ ω, ‖SF ω - LF ω‖ ^ 2 ∂μ) ≤
      C₁ * nF * R ^ (d / 2) * ((L ^ η) ^ (-d) + (L ^ η) ^ (-γ)))
    (e3F : Real.sqrt (∫ ω, ‖LF ω - YF ω‖ ^ 2 ∂μ) ≤
      C₂ * nF * (L / R + L ^ (-(1 - β) / 2)))
    (e1G : Real.sqrt (∫ ω, ‖UG ω - SG ω‖ ^ 2 ∂μ) ≤ C₁ * nG * (L ^ η / R) ^ 2)
    (e2G : Real.sqrt (∫ ω, ‖SG ω - LG ω‖ ^ 2 ∂μ) ≤
      C₁ * nG * R ^ (d / 2) * ((L ^ η) ^ (-d) + (L ^ η) ^ (-γ)))
    (e3G : Real.sqrt (∫ ω, ‖LG ω - YG ω‖ ^ 2 ∂μ) ≤
      C₂ * nG * (L / R + L ^ (-(1 - β) / 2)))
    (hUGn : l2Size μ UG ≤ C₄ * nG) (hYFn : l2Size μ YF ≤ C₂ * nF)
    (hcov : ‖(∫ ω, YF ω * YG ω ∂μ) - T‖ ≤ C₂ * nF * nG * (L ^ (-κ) + L / R)) :
    ‖(∫ ω, UF ω * UG ω ∂μ) - T‖ ≤
      (C₄ * (C₁ * (1 + (2 ^ (η * d) + 2 ^ (η * γ))) + C₂ * (1 + 2 ^ ((1 - β) / 2))) +
        C₂ * (C₁ * (1 + (2 ^ (η * d) + 2 ^ (η * γ))) + C₂ * (1 + 2 ^ ((1 - β) / 2))) +
        C₂ * (2 ^ κ + 1)) * nF * nG * R ^ (-ε) := by
  obtain ⟨hA, hB, hC, hD⟩ := scale_estimates (θ := θ) (η := η) (β := β) (κ := κ) (γ := γ)
    (d := d) (ε := ε) hR hL0 hLR hL2 hη hd hγ hβ hκ hε1 hε2 hε3 hε4 hε5 hε6
  have hE : 0 ≤ R ^ (-ε) := Real.rpow_nonneg (by linarith) _
  -- the common bound for the F-chain and the G-chain
  have chain : ∀ {n : ℝ}, 0 ≤ n → ∀ {a b c : ℝ},
      a ≤ C₁ * n * (L ^ η / R) ^ 2 →
      b ≤ C₁ * n * R ^ (d / 2) * ((L ^ η) ^ (-d) + (L ^ η) ^ (-γ)) →
      c ≤ C₂ * n * (L / R + L ^ (-(1 - β) / 2)) →
      a + b + c ≤ n * (C₁ * (1 + (2 ^ (η * d) + 2 ^ (η * γ))) +
        C₂ * (1 + 2 ^ ((1 - β) / 2))) * R ^ (-ε) := by
    intro n hn a b c ha hb hc
    have t1 : C₁ * n * (L ^ η / R) ^ 2 ≤ C₁ * n * R ^ (-ε) :=
      mul_le_mul_of_nonneg_left hA (mul_nonneg hC₁ hn)
    have t2 : C₁ * n * R ^ (d / 2) * ((L ^ η) ^ (-d) + (L ^ η) ^ (-γ)) ≤
        C₁ * n * ((2 ^ (η * d) + 2 ^ (η * γ)) * R ^ (-ε)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hB (mul_nonneg hC₁ hn)
    have t3 : C₂ * n * (L / R + L ^ (-(1 - β) / 2)) ≤
        C₂ * n * ((1 + 2 ^ ((1 - β) / 2)) * R ^ (-ε)) :=
      mul_le_mul_of_nonneg_left hC (mul_nonneg hC₂ hn)
    calc a + b + c ≤ C₁ * n * R ^ (-ε) +
          C₁ * n * ((2 ^ (η * d) + 2 ^ (η * γ)) * R ^ (-ε)) +
          C₂ * n * ((1 + 2 ^ ((1 - β) / 2)) * R ^ (-ε)) :=
          add_le_add (add_le_add (ha.trans t1) (hb.trans t2)) (hc.trans t3)
      _ = n * (C₁ * (1 + (2 ^ (η * d) + 2 ^ (η * γ))) +
          C₂ * (1 + 2 ^ ((1 - β) / 2))) * R ^ (-ε) := by ring
  set Mc : ℝ := C₁ * (1 + (2 ^ (η * d) + 2 ^ (η * γ))) + C₂ * (1 + 2 ^ ((1 - β) / 2))
    with hMc
  have hMc0 : 0 ≤ Mc := by rw [hMc]; positivity
  have a1F : l2Size μ (UF - YF) ≤ nF * Mc * R ^ (-ε) :=
    (l2Size_sub_le_three hUF hSF hLF hYF).trans (chain hnF e1F e2F e3F)
  have a1G : l2Size μ (UG - YG) ≤ nG * Mc * R ^ (-ε) :=
    (l2Size_sub_le_three hUG hSG hLG hYG).trans (chain hnG e1G e2G e3G)
  have key := norm_integral_mul_sub_le hUF hUG hYF hYG
  have k1 : l2Size μ (UF - YF) * l2Size μ UG ≤ (nF * Mc * R ^ (-ε)) * (C₄ * nG) :=
    mul_le_mul a1F hUGn (l2Size_nonneg _) (mul_nonneg (mul_nonneg hnF hMc0) hE)
  have k2 : l2Size μ YF * l2Size μ (UG - YG) ≤ (C₂ * nF) * (nG * Mc * R ^ (-ε)) :=
    mul_le_mul hYFn a1G (l2Size_nonneg _) (mul_nonneg hC₂ hnF)
  have k3 : C₂ * nF * nG * (L ^ (-κ) + L / R) ≤ C₂ * nF * nG * ((2 ^ κ + 1) * R ^ (-ε)) :=
    mul_le_mul_of_nonneg_left hD (mul_nonneg (mul_nonneg hC₂ hnF) hnG)
  have tri : ‖(∫ ω, UF ω * UG ω ∂μ) - T‖ ≤
      ‖(∫ ω, UF ω * UG ω ∂μ) - ∫ ω, YF ω * YG ω ∂μ‖ +
        ‖(∫ ω, YF ω * YG ω ∂μ) - T‖ := by
    have e : (∫ ω, UF ω * UG ω ∂μ) - T =
        ((∫ ω, UF ω * UG ω ∂μ) - ∫ ω, YF ω * YG ω ∂μ) +
          ((∫ ω, YF ω * YG ω ∂μ) - T) := by ring
    rw [e]
    exact norm_add_le _ _
  calc ‖(∫ ω, UF ω * UG ω ∂μ) - T‖
      ≤ ‖(∫ ω, UF ω * UG ω ∂μ) - ∫ ω, YF ω * YG ω ∂μ‖ +
        ‖(∫ ω, YF ω * YG ω ∂μ) - T‖ := tri
    _ ≤ (l2Size μ (UF - YF) * l2Size μ UG + l2Size μ YF * l2Size μ (UG - YG)) +
        C₂ * nF * nG * ((2 ^ κ + 1) * R ^ (-ε)) :=
        add_le_add key (hcov.trans k3)
    _ ≤ ((nF * Mc * R ^ (-ε)) * (C₄ * nG) + (C₂ * nF) * (nG * Mc * R ^ (-ε))) +
        C₂ * nF * nG * ((2 ^ κ + 1) * R ^ (-ε)) :=
        add_le_add (add_le_add k1 k2) le_rfl
    _ = (C₄ * Mc + C₂ * Mc + C₂ * (2 ^ κ + 1)) * nF * nG * R ^ (-ε) := by ring

/-! ### Matrices with bounded Frobenius size -/

theorem sum_sq_mulVec_le {ι : Type*} [Fintype ι] (A : ι → ι → ℝ) (ξ : ι → ℝ) :
    ∑ a, (∑ b, A a b * ξ b) ^ 2 ≤ (∑ a, ∑ b, A a b ^ 2) * ∑ b, ξ b ^ 2 := by
  calc ∑ a, (∑ b, A a b * ξ b) ^ 2
      ≤ ∑ a, ((∑ b, A a b ^ 2) * ∑ b, ξ b ^ 2) :=
        Finset.sum_le_sum fun a _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ a, ∑ b, A a b ^ 2) * ∑ b, ξ b ^ 2 := by rw [Finset.sum_mul]

theorem norm_toLp_mulVec_le {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (ξ : EuclideanSpace ℝ ι) :
    ‖WithLp.toLp 2 (A.mulVec (WithLp.ofLp ξ))‖ ≤
      Real.sqrt (∑ a, ∑ b, A a b ^ 2) * ‖ξ‖ := by
  have hF : 0 ≤ ∑ a, ∑ b, A a b ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have h1 : ‖WithLp.toLp 2 (A.mulVec (WithLp.ofLp ξ))‖ =
      Real.sqrt (∑ a, (∑ b, A a b * ξ b) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rfl
  have h2 : ‖ξ‖ = Real.sqrt (∑ b, ξ b ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [h1, h2, ← Real.sqrt_mul hF]
  exact Real.sqrt_le_sqrt (sum_sq_mulVec_le (fun a b => A a b) _)

theorem norm_double_sum_le {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (u v : ι → ℂ) :
    ‖∑ a, ∑ b, u a * (A a b : ℂ) * v b‖ ≤
      Real.sqrt (∑ a, ∑ b, A a b ^ 2) *
        (Real.sqrt (∑ a, ‖u a‖ ^ 2) * Real.sqrt (∑ b, ‖v b‖ ^ 2)) := by
  have hF : 0 ≤ ∑ a, ∑ b, A a b ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hs := sum_sq_mulVec_le (fun a b => |A a b|) (fun b => ‖v b‖)
  simp only [sq_abs] at hs
  calc ‖∑ a, ∑ b, u a * (A a b : ℂ) * v b‖
      ≤ ∑ a, ‖∑ b, u a * (A a b : ℂ) * v b‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖u a‖ * ∑ b, |A a b| * ‖v b‖ := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine (norm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact le_of_eq (mul_assoc _ _ _)
    _ ≤ Real.sqrt (∑ a, ‖u a‖ ^ 2) * Real.sqrt (∑ a, (∑ b, |A a b| * ‖v b‖) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ a, ‖u a‖ ^ 2) *
          Real.sqrt ((∑ a, ∑ b, A a b ^ 2) * ∑ b, ‖v b‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs) (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑ a, ∑ b, A a b ^ 2) *
        (Real.sqrt (∑ a, ‖u a‖ ^ 2) * Real.sqrt (∑ b, ‖v b‖ ^ 2)) := by
        rw [Real.sqrt_mul hF]
        ring

theorem norm_double_sum_le_norm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (u v : EuclideanSpace ℂ ι) :
    ‖∑ a, ∑ b, u a * (A a b : ℂ) * v b‖ ≤
      Real.sqrt (∑ a, ∑ b, A a b ^ 2) * (‖u‖ * ‖v‖) := by
  have h := norm_double_sum_le A (fun a => u a) (fun b => v b)
  rw [EuclideanSpace.norm_eq u, EuclideanSpace.norm_eq v]
  exact h

end EinsteinFull.Calculus.S1
