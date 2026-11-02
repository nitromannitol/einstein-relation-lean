import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.OrderClosed

/-!
# Dyadic scale and the resolvent rate limit

Real-analysis steps behind the clock estimate `|η(λ) - 𝔼μ| ≤ C λ` in `paper/main.tex`,
lines 1165–1180. Proposition 6.1 bounds `|𝔼[ρ_s μ] - 𝔼μ|` by `C (s R + λ + λ² R + R⁻¹)`
for `0 < s ≤ λ²` and dyadic `R`. The steps below are:

1. `exists_dyadic_scale`: a dyadic scale `R = 2^n` with `C₀ R ≤ l / (2 λ)` and
   `R ≥ l / (4 C₀ λ)`, so that `R ≍ λ⁻¹`.
2. `abs_sub_le_of_tendsto_resolvent`: letting `s ↓ 0` in the resolvent bound.
3. `clock_rate_of_resolvent`: the two steps combined into a bound linear in `λ`.

The smallness hypothesis `λ ≤ l / (4 C₀)` is exactly what makes the largest admissible
scale `l / (2 λ C₀)` at least `2`.
-/

open Filter Topology

namespace EinsteinRelation.Clock

/-- Dyadic scale selection. For `λ ≤ l / (4 C₀)` there is a power of two `R = 2^n`, at least `2`,
with `C₀ R ≤ l / (2 λ)` and `l / (4 C₀ λ) ≤ R`. -/
theorem exists_dyadic_scale (C₀ l : ℝ) (hC₀ : 0 < C₀) (_hl : 0 < l) (lam : ℝ) (hlam : 0 < lam)
    (hsmall : lam ≤ l / (4 * C₀)) :
    ∃ R : ℝ, 2 ≤ R ∧ (∃ k : ℕ, R = 2 ^ k) ∧ C₀ * R ≤ l / (2 * lam) ∧
      l / (4 * C₀ * lam) ≤ R := by
  have hk : 0 < 2 * lam * C₀ := by positivity
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = l / (2 * lam * C₀) := ⟨_, rfl⟩
  have hxk : l = x * (2 * lam * C₀) := (div_eq_iff hk.ne').mp hx.symm
  have hx2 : 2 ≤ x := by
    have h4 : lam * (4 * C₀) ≤ l := (le_div_iff₀ (by positivity : (0:ℝ) < 4 * C₀)).mp hsmall
    have h2 : 2 * (2 * lam * C₀) = lam * (4 * C₀) := by ring
    refine le_of_mul_le_mul_right ?_ hk
    linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (by linarith : (1:ℝ) ≤ x) (by norm_num : (1:ℝ) < 2)
  have hpow : (2:ℝ) ^ (n + 1) = 2 ^ n * 2 := pow_succ (2:ℝ) n
  rw [hpow] at hn2
  have hn_two : (2:ℝ) ≤ 2 ^ n := by
    cases n with
    | zero =>
      norm_num at hn2
      linarith
    | succ m =>
      have h1 : (1:ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      linarith
  refine ⟨2 ^ n, hn_two, ⟨n, rfl⟩, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * lam)]
    have hc : 0 ≤ C₀ * (2 * lam) := by positivity
    have := mul_le_mul_of_nonneg_left hn1 hc
    linarith
  · rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * C₀ * lam)]
    have := mul_lt_mul_of_pos_right hn2 hk
    linarith

/-- Letting `s ↓ 0` in the resolvent bound. If `|F s - m| ≤ C (s R + λ + λ² R + R⁻¹)` for
`0 < s ≤ λ²` and `F s → η` as `s ↓ 0`, then `|η - m| ≤ C (λ + λ² R + R⁻¹)`. The sign of `C`
plays no role. -/
theorem abs_sub_le_of_tendsto_resolvent (F : ℝ → ℝ) (m η C R lam : ℝ) (hlam : 0 < lam)
    (hF : ∀ s, 0 < s → s ≤ lam ^ 2 → |F s - m| ≤ C * (s * R + lam + lam ^ 2 * R + R⁻¹))
    (hlim : Tendsto F (𝓝[>] 0) (𝓝 η)) : |η - m| ≤ C * (lam + lam ^ 2 * R + R⁻¹) := by
  have hcont : Continuous (fun s : ℝ => C * (s * R + lam + lam ^ 2 * R + R⁻¹)) := by
    fun_prop
  have hval : C * (0 * R + lam + lam ^ 2 * R + R⁻¹) = C * (lam + lam ^ 2 * R + R⁻¹) := by
    ring
  have hB : Tendsto (fun s : ℝ => C * (s * R + lam + lam ^ 2 * R + R⁻¹)) (𝓝[>] 0)
      (𝓝 (C * (lam + lam ^ 2 * R + R⁻¹))) := by
    rw [← hval]
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun s : ℝ => |F s - m|) (𝓝[>] 0) (𝓝 |η - m|) :=
    (hlim.sub (tendsto_const_nhds (x := m))).abs
  have hE : ∀ᶠ s in 𝓝[>] 0, |F s - m| ≤ C * (s * R + lam + lam ^ 2 * R + R⁻¹) := by
    filter_upwards [Ioo_mem_nhdsGT (pow_pos hlam 2)] with s hs
    exact hF s hs.1 hs.2.le
  exact le_of_tendsto_of_tendsto hA hB hE

/-- Clock rate from the resolvent limit. Under `λ ≤ l / (4 C₀)`, if the resolvent bound holds
for every dyadic scale `R` with `C₀ R ≤ l / (2 λ)` and `l / (4 C₀ λ) ≤ R`, and `F s → η` as
`s ↓ 0`, then `|η - m| ≤ C (1 + l / (2 C₀) + 4 C₀ / l) λ`. -/
theorem clock_rate_of_resolvent (C₀ l : ℝ) (hC₀ : 0 < C₀) (hl : 0 < l) (lam : ℝ) (hlam : 0 < lam)
    (hsmall : lam ≤ l / (4 * C₀)) (F : ℝ → ℝ) (m η C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ R : ℝ, 2 ≤ R → (∃ k : ℕ, R = 2 ^ k) → C₀ * R ≤ l / (2 * lam) →
      l / (4 * C₀ * lam) ≤ R →
      ∀ s, 0 < s → s ≤ lam ^ 2 → |F s - m| ≤ C * (s * R + lam + lam ^ 2 * R + R⁻¹))
    (hlim : Tendsto F (𝓝[>] 0) (𝓝 η)) :
    |η - m| ≤ C * (1 + l / (2 * C₀) + 4 * C₀ / l) * lam := by
  obtain ⟨R, hR2, hRk, hup, hlow⟩ := exists_dyadic_scale C₀ l hC₀ hl lam hlam hsmall
  have hup' : C₀ * R * (2 * lam) ≤ l :=
    (le_div_iff₀ (by positivity : (0:ℝ) < 2 * lam)).mp hup
  have hlamR : lam * R ≤ l / (2 * C₀) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * C₀)]
    linarith
  have h1 : lam ^ 2 * R ≤ lam * (l / (2 * C₀)) := by
    have := mul_le_mul_of_nonneg_left hlamR hlam.le
    calc lam ^ 2 * R = lam * (lam * R) := by ring
      _ ≤ lam * (l / (2 * C₀)) := this
  have h2 : R⁻¹ ≤ 4 * C₀ / l * lam := by
    have hinv : R⁻¹ ≤ (l / (4 * C₀ * lam))⁻¹ := inv_anti₀ (by positivity) hlow
    rw [inv_div] at hinv
    calc R⁻¹ ≤ 4 * C₀ * lam / l := hinv
      _ = 4 * C₀ / l * lam := by ring
  have hsum : lam + lam ^ 2 * R + R⁻¹ ≤ (1 + l / (2 * C₀) + 4 * C₀ / l) * lam := by
    have e : (1 + l / (2 * C₀) + 4 * C₀ / l) * lam =
        lam + lam * (l / (2 * C₀)) + 4 * C₀ / l * lam := by
      ring
    rw [e]
    linarith
  have hbound := abs_sub_le_of_tendsto_resolvent F m η C R lam hlam (hF R hR2 hRk hup hlow) hlim
  calc |η - m| ≤ C * (lam + lam ^ 2 * R + R⁻¹) := hbound
    _ ≤ C * ((1 + l / (2 * C₀) + 4 * C₀ / l) * lam) := mul_le_mul_of_nonneg_left hsum hC
    _ = C * (1 + l / (2 * C₀) + 4 * C₀ / l) * lam := by ring

end EinsteinRelation.Clock
