import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.Monotone

/-! Minkowski's inequality for sample integrals of a jointly measurable field.

Source anchors: paper/main.tex, lines 834–838 and 845–876. The Minkowski step is the
`L^m`-norm bound for `∫_0^T ∇v(t) dt` on lines 834–838, which integrates the weighted spatial
gradient norms under the probability law. Let `Q` be a probability measure on `Ω`, `ν` a
σ-finite measure on `X`, and
`f : X × Ω → ℝ` jointly measurable. Suppose each section `f (x, ·)` has `L^p(Q)`-norm at most
`H x`, where `H ≥ 0` is integrable. Then for `Q`-a.e. `ω` the section `x ↦ f (x, ω)` is
`ν`-integrable, and `ω ↦ ∫ f (x, ω) dν(x)` lies in `L^p(Q)` with norm at most `∫ H dν`.

Proof. Tonelli and `L¹ ≤ L^p` on the probability space make the spatial absolute integral
`G(ω) = ∫ |f (x, ω)| dν(x)` finite for `Q`-a.e. `ω`, which gives section integrability. For
`1 < p`, the Minkowski bound `∫ G^p dQ ≤ (∫ H dν)^p` is proved in `ℝ≥0∞` by testing the truncations
`min G n` against Hölder's inequality and Tonelli. This avoids dividing by `H` and needs no
independence, sign, or continuity hypothesis. The case `p = 1` is Tonelli. The sample integral is
bounded by `G` pointwise, so its `L^p` norm is bounded by that of `G`.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- A value in `ℝ≥0∞` is the supremum of its truncations at the natural numbers. -/
private theorem integralMoment_eq_iSup_min (a : ℝ≥0∞) :
    a = ⨆ n : ℕ, min a (n : ℝ≥0∞) := by
  refine le_antisymm ?_ (iSup_le fun n => min_le_left _ _)
  rcases eq_or_ne a ⊤ with ha | ha
  · rw [ha]
    calc (⊤ : ℝ≥0∞) = ⨆ n : ℕ, (n : ℝ≥0∞) := ENNReal.iSup_natCast.symm
      _ ≤ ⨆ n : ℕ, min ⊤ (n : ℝ≥0∞) :=
        iSup_mono fun n => le_of_eq (min_eq_right (le_top : (n : ℝ≥0∞) ≤ ⊤)).symm
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
    exact le_iSup_of_le n (le_min le_rfl hn.le)

/-- Taking `p`-th powers commutes with the truncation supremum for `0 < p`. -/
private theorem integralMoment_rpow_eq_iSup_min {p : ℝ} (hp : 0 < p) (a : ℝ≥0∞) :
    a ^ p = ⨆ n : ℕ, (min a (n : ℝ≥0∞)) ^ p := by
  calc a ^ p = (⨆ n : ℕ, min a (n : ℝ≥0∞)) ^ p := by rw [← integralMoment_eq_iSup_min a]
    _ = ⨆ n : ℕ, (min a (n : ℝ≥0∞)) ^ p :=
      Monotone.map_iSup_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ p)
        ENNReal.continuous_rpow_const.continuousAt
        (fun _ _ hxy => ENNReal.rpow_le_rpow hxy hp.le) (ENNReal.zero_rpow_of_pos hp)

/-- From `A ≤ M A^{1/q}` with `A` finite and `1/p + 1/q = 1`, get `A ≤ M^p`. -/
private theorem integralMoment_le_of_le_mul_rpow {A M : ℝ≥0∞} {p q : ℝ} (hp : 1 < p)
    (hpq : p.HolderConjugate q) (hA : A ≠ ⊤) (h : A ≤ M * A ^ (1 / q)) :
    A ≤ M ^ p := by
  have hp0 : 0 < p := by linarith
  rcases eq_or_ne A 0 with hA0 | hA0
  · rw [hA0]
    exact zero_le
  have hq : 0 < q - 1 := hpq.symm.sub_one_pos
  have hq0 : 0 ≤ 1 / q := one_div_nonneg.2 (by linarith)
  have hBpos : 0 < A ^ (1 / q) := ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hA
  have hBtop : A ^ (1 / q) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hq0 hA
  have hexp : 1 / p + 1 / q = 1 := by
    rw [one_div, one_div]
    exact hpq.inv_add_inv_eq_one
  have hsplit : A = A ^ (1 / p) * A ^ (1 / q) := by
    rw [← ENNReal.rpow_add _ _ hA0 hA, hexp, ENNReal.rpow_one]
  have hmul : A ^ (1 / q) * A ^ (1 / p) ≤ A ^ (1 / q) * M := by
    calc A ^ (1 / q) * A ^ (1 / p) = A ^ (1 / p) * A ^ (1 / q) := mul_comm _ _
      _ = A := hsplit.symm
      _ ≤ M * A ^ (1 / q) := h
      _ = A ^ (1 / q) * M := mul_comm _ _
  have hA1 : A ^ (1 / p) ≤ M := (ENNReal.mul_le_mul_iff_right hBpos.ne' hBtop).1 hmul
  calc A = (A ^ (1 / p)) ^ p := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
    _ ≤ M ^ p := ENNReal.rpow_le_rpow hA1 hp0.le

/-- `(x ^ p) ^ (1/p) = x` for `0 < p`. -/
private theorem integralMoment_rpow_rpow_inv {p : ℝ} (hp : 0 < p) (x : ℝ≥0∞) :
    (x ^ p) ^ (1 / p) = x := by
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- Each truncated moment `∫ (min G n)^p dQ` is finite, where `G ω = ∫ g (x, ω) dν`. -/
private theorem integralMoment_truncated_ne_top {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (Q : Measure Ω) [IsProbabilityMeasure Q] (ν : Measure X)
    [SigmaFinite ν] {p : ℝ} (hp : 0 ≤ p) (g : X × Ω → ℝ≥0∞) (n : ℕ) :
    ∫⁻ ω, (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q ≠ ⊤ := by
  have hle : ∫⁻ ω, (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q ≤
      ∫⁻ _ω, (n : ℝ≥0∞) ^ p ∂Q :=
    lintegral_mono fun ω => ENNReal.rpow_le_rpow (min_le_right _ _) hp
  rw [lintegral_const, measure_univ, mul_one] at hle
  exact ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg hp (ENNReal.natCast_ne_top n)) hle

/-- Truncated Minkowski estimate: `A_n ≤ M A_n^{1/q}` for `A_n = ∫ (min G n)^p dQ`, where
`G ω = ∫ g (x, ω) dν`, `M = ∫ H dν`, and `(∫ g (x, ·)^p dQ)^{1/p} ≤ H x`. -/
private theorem integralMoment_truncated_le {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (Q : Measure Ω) [IsProbabilityMeasure Q] (ν : Measure X)
    [SigmaFinite ν] {p q : ℝ} (hp : 1 < p) (hpq : p.HolderConjugate q)
    (g : X × Ω → ℝ≥0∞) (hg : Measurable g) (H : X → ℝ≥0∞)
    (hH : ∀ x, (∫⁻ ω, g (x, ω) ^ p ∂Q) ^ (1 / p) ≤ H x) (n : ℕ) :
    ∫⁻ ω, (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q ≤
      (∫⁻ x, H x ∂ν) * (∫⁻ ω, (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q) ^ (1 / q) := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < q - 1 := hpq.symm.sub_one_pos
  have hGm : Measurable fun ω => ∫⁻ x, g (x, ω) ∂ν := hg.lintegral_prod_left'
  have hTm : Measurable fun ω => min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞) :=
    hGm.min measurable_const
  have hTpm : Measurable fun ω => (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1) :=
    hTm.pow_const _
  have hgx : ∀ ω, Measurable fun x => g (x, ω) := fun ω =>
    hg.comp (measurable_prodMk_right (y := ω))
  have hA_top := integralMoment_truncated_ne_top Q ν hp0.le g n
  have hAq_top : (∫⁻ ω, (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q) ^ (1 / q) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 (by linarith)) hA_top
  -- `t ^ p = t ^ (p - 1) * t`
  have hsplit : ∀ t : ℝ≥0∞, t ^ p = t ^ (p - 1) * t := by
    intro t
    calc t ^ p = t ^ ((p - 1) + 1) := by rw [sub_add_cancel]
      _ = t ^ (p - 1) * t ^ (1 : ℝ) :=
        ENNReal.rpow_add_of_nonneg (p - 1) 1 (by linarith) zero_le_one
      _ = t ^ (p - 1) * t := by rw [ENNReal.rpow_one]
  -- pointwise: `T^p ≤ G · T^{p-1}` with `T = min G n ≤ G`
  have hstep1 : ∫⁻ ω, (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q ≤
      ∫⁻ ω, ∫⁻ x, g (x, ω) * (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1) ∂ν ∂Q := by
    refine lintegral_mono fun ω => ?_
    calc (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ p
        = (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1) *
            min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞) := hsplit _
      _ ≤ (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1) * ∫⁻ x, g (x, ω) ∂ν :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) zero_le
      _ = ∫⁻ x, g (x, ω) * (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1) ∂ν := by
          rw [lintegral_mul_const'' _ (hgx ω).aemeasurable]
          exact mul_comm _ _
  -- Tonelli
  have hstep2 : ∫⁻ ω, ∫⁻ x, g (x, ω) * (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1) ∂ν ∂Q =
      ∫⁻ x, ∫⁻ ω, g (x, ω) * (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1) ∂Q ∂ν := by
    refine lintegral_lintegral_swap
      (f := fun ω x => g (x, ω) * (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1)) ?_
    exact ((hg.comp measurable_swap).mul (hTpm.comp measurable_fst)).aemeasurable
  -- Hölder in `ω` for each fixed `x`, using `(T^{p-1})^q = T^p`
  have hstep3 : ∀ x : X, ∫⁻ ω, g (x, ω) * (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1) ∂Q ≤
      H x * (∫⁻ ω, (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q) ^ (1 / q) := by
    intro x
    have hgy : Measurable fun ω => g (x, ω) := hg.comp (measurable_prodMk_left (x := x))
    have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq Q hpq hgy.aemeasurable hTpm.aemeasurable
    have hTq : ∫⁻ ω, ((min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1)) ^ q ∂Q =
        ∫⁻ ω, (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q := by
      refine lintegral_congr fun ω => ?_
      rw [← ENNReal.rpow_mul, hpq.sub_one_mul_conj]
    calc ∫⁻ ω, g (x, ω) * (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1) ∂Q
        ≤ (∫⁻ ω, g (x, ω) ^ p ∂Q) ^ (1 / p) *
            (∫⁻ ω, ((min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1)) ^ q ∂Q) ^ (1 / q) :=
          hHold
      _ = (∫⁻ ω, g (x, ω) ^ p ∂Q) ^ (1 / p) *
            (∫⁻ ω, (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q) ^ (1 / q) := by
          rw [hTq]
      _ ≤ H x * (∫⁻ ω, (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q) ^ (1 / q) :=
          mul_le_mul_of_nonneg_right (hH x) zero_le
  -- integrate in `x`
  have hstep4 : ∫⁻ x, ∫⁻ ω, g (x, ω) * (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1) ∂Q ∂ν ≤
      (∫⁻ x, H x ∂ν) * (∫⁻ ω, (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q) ^ (1 / q) := by
    calc ∫⁻ x, ∫⁻ ω, g (x, ω) * (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ (p - 1) ∂Q ∂ν
        ≤ ∫⁻ x, H x * (∫⁻ ω, (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q) ^ (1 / q) ∂ν :=
          lintegral_mono fun x => hstep3 x
      _ = (∫⁻ x, H x ∂ν) * (∫⁻ ω, (min (∫⁻ x', g (x', ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q) ^ (1 / q) :=
          lintegral_mul_const' _ _ hAq_top
  exact hstep1.trans (hstep2.le.trans hstep4)

/-- Minkowski's inequality in `ℝ≥0∞` for `1 < p`:
`∫ (∫ g (x, ·) dν)^p dQ ≤ (∫ H dν)^p` when `‖g (x, ·)‖_{L^p(Q)} ≤ H x`. -/
private theorem integralMoment_lintegral_pow_le_of_one_lt {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (Q : Measure Ω) [IsProbabilityMeasure Q] (ν : Measure X)
    [SigmaFinite ν] {p q : ℝ} (hp : 1 < p) (hpq : p.HolderConjugate q)
    (g : X × Ω → ℝ≥0∞) (hg : Measurable g) (H : X → ℝ≥0∞)
    (hH : ∀ x, (∫⁻ ω, g (x, ω) ^ p ∂Q) ^ (1 / p) ≤ H x) :
    ∫⁻ ω, (∫⁻ x, g (x, ω) ∂ν) ^ p ∂Q ≤ (∫⁻ x, H x ∂ν) ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hGm : Measurable fun ω => ∫⁻ x, g (x, ω) ∂ν := hg.lintegral_prod_left'
  have hTm : ∀ n : ℕ, Measurable fun ω => (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ p :=
    fun n => (hGm.min measurable_const).pow_const p
  have hmono : Monotone fun (n : ℕ) (ω : Ω) => (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ p := by
    intro m n hmn ω
    exact ENNReal.rpow_le_rpow (min_le_min le_rfl (by exact_mod_cast hmn)) hp0
  calc ∫⁻ ω, (∫⁻ x, g (x, ω) ∂ν) ^ p ∂Q
      = ∫⁻ ω, ⨆ n : ℕ, (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q :=
        lintegral_congr fun ω => integralMoment_rpow_eq_iSup_min (by linarith) _
    _ = ⨆ n : ℕ, ∫⁻ ω, (min (∫⁻ x, g (x, ω) ∂ν) (n : ℝ≥0∞)) ^ p ∂Q :=
        lintegral_iSup hTm hmono
    _ ≤ (∫⁻ x, H x ∂ν) ^ p :=
        iSup_le fun n => integralMoment_le_of_le_mul_rpow hp hpq
          (integralMoment_truncated_ne_top (p := p) Q ν hp0 g n)
          (integralMoment_truncated_le Q ν hp hpq g hg H hH n)

/-- Minkowski's inequality in `ℝ≥0∞` for `1 ≤ p`, covering `p = 1` by Tonelli. -/
private theorem integralMoment_lintegral_pow_le {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (Q : Measure Ω) [IsProbabilityMeasure Q] (ν : Measure X)
    [SigmaFinite ν] {p : ℝ} (hp : 1 ≤ p) (g : X × Ω → ℝ≥0∞) (hg : Measurable g)
    (H : X → ℝ≥0∞) (hH : ∀ x, (∫⁻ ω, g (x, ω) ^ p ∂Q) ^ (1 / p) ≤ H x) :
    ∫⁻ ω, (∫⁻ x, g (x, ω) ∂ν) ^ p ∂Q ≤ (∫⁻ x, H x ∂ν) ^ p := by
  rcases hp.eq_or_lt with rfl | hp1
  · have hH1 : ∀ x, ∫⁻ ω, g (x, ω) ∂Q ≤ H x := fun x => by
      simpa only [ENNReal.rpow_one, div_one] using hH x
    simp only [ENNReal.rpow_one]
    calc ∫⁻ ω, ∫⁻ x, g (x, ω) ∂ν ∂Q = ∫⁻ x, ∫⁻ ω, g (x, ω) ∂Q ∂ν :=
          lintegral_lintegral_swap (f := fun ω x => g (x, ω))
            (hg.comp measurable_swap).aemeasurable
      _ ≤ ∫⁻ x, H x ∂ν := lintegral_mono fun x => hH1 x
  · exact integralMoment_lintegral_pow_le_of_one_lt Q ν hp1
      (Real.HolderConjugate.conjExponent hp1) g hg H hH

/-- Sample integrals of a jointly measurable field with uniform `L^p` section bounds.

For `Q`-a.e. `ω`, the section `x ↦ f (x, ω)` is `ν`-integrable; the sample integral
`ω ↦ ∫ f (x, ω) dν` lies in `L^p(Q)`, with `L^p(Q)`-norm at most `∫ H dν`. -/
theorem integral_moment_le : ∀ {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (ν : Measure X) [SigmaFinite ν]
    {p : ℝ}, 1 ≤ p → ∀ (H : X → ℝ), Measurable H → (∀ x, 0 ≤ H x) → Integrable H ν →
    ∀ f : X × Ω → ℝ, Measurable f →
    (∀ x, MemLp (fun ω => f (x,ω)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => f (x,ω)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (H x)) →
    (∀ᵐ ω ∂Q, Integrable (fun x => f (x,ω)) ν) ∧
    MemLp (fun ω => ∫ x, f (x,ω) ∂ν) (ENNReal.ofReal p) Q ∧
    eLpNorm (fun ω => ∫ x, f (x,ω) ∂ν) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (∫ x, H x ∂ν) := by
  intro Ω X _ _ Q _ ν _ p hp H _ hH0 hHi f hf hmem
  have hp0 : 0 ≤ p := by linarith
  have hnonneg : (0 : X → ℝ) ≤ᵐ[ν] H := Filter.Eventually.of_forall hH0
  have hE_toReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0
  have hE_ne_zero : ENNReal.ofReal p ≠ 0 :=
    (ENNReal.ofReal_pos.2 (show (0 : ℝ) < p by linarith)).ne'
  have hE_ne_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfe : Measurable fun z : X × Ω => ‖f z‖ₑ := hf.enorm
  have hmx : ∀ x, AEStronglyMeasurable (fun ω => f (x, ω)) Q := fun x =>
    (hf.comp (measurable_prodMk_left (x := x))).aestronglyMeasurable
  -- the `L^p` bound of each section, in lintegral form
  have hlp : ∀ x, (∫⁻ ω, ‖f (x, ω)‖ₑ ^ p ∂Q) ^ (1 / p) ≤ ENNReal.ofReal (H x) := by
    intro x
    have h := (hmem x).2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hE_ne_zero hE_ne_top (hmx x), hE_toReal] at h
    exact h
  -- `L¹ ≤ L^p` on the probability space
  have hL1 : ∀ x, ∫⁻ ω, ‖f (x, ω)‖ₑ ∂Q ≤ ENNReal.ofReal (H x) := by
    intro x
    have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hp
    have h1 := eLpNorm_le_eLpNorm_of_exponent_le (f := fun ω => f (x, ω)) (μ := Q) hle
    rw [eLpNorm_one_eq_lintegral_enorm (hmx x)] at h1
    exact h1.trans (hmem x).2
  -- Tonelli: the total spatial absolute mass has finite `Q`-integral
  have hGm : Measurable fun ω => ∫⁻ x, ‖f (x, ω)‖ₑ ∂ν := hfe.lintegral_prod_left'
  have hfin : ∫⁻ ω, ∫⁻ x, ‖f (x, ω)‖ₑ ∂ν ∂Q ≠ ⊤ := by
    have hswap : ∫⁻ ω, ∫⁻ x, ‖f (x, ω)‖ₑ ∂ν ∂Q = ∫⁻ x, ∫⁻ ω, ‖f (x, ω)‖ₑ ∂Q ∂ν :=
      lintegral_lintegral_swap (f := fun ω x => ‖f (x, ω)‖ₑ)
        (hfe.comp measurable_swap).aemeasurable
    have hle : ∫⁻ x, ∫⁻ ω, ‖f (x, ω)‖ₑ ∂Q ∂ν ≤ ∫⁻ x, ENNReal.ofReal (H x) ∂ν :=
      lintegral_mono fun x => hL1 x
    rw [hswap]
    refine ne_top_of_le_ne_top ?_ hle
    rw [← ofReal_integral_eq_lintegral_ofReal hHi hnonneg]
    exact ENNReal.ofReal_ne_top
  -- so the spatial absolute integral is finite for `Q`-a.e. `ω`
  have hae : ∀ᵐ ω ∂Q, ∫⁻ x, ‖f (x, ω)‖ₑ ∂ν < ⊤ := ae_lt_top hGm hfin
  -- hence every such section is `ν`-integrable
  have hsec : ∀ᵐ ω ∂Q, Integrable (fun x => f (x, ω)) ν := by
    filter_upwards [hae] with ω hω
    exact ⟨(hf.comp (measurable_prodMk_right (y := ω))).aestronglyMeasurable, hω⟩
  -- Minkowski bound for the spatial absolute integral
  have hpow : ∫⁻ ω, (∫⁻ x, ‖f (x, ω)‖ₑ ∂ν) ^ p ∂Q ≤ (∫⁻ x, ENNReal.ofReal (H x) ∂ν) ^ p :=
    integralMoment_lintegral_pow_le Q ν hp (fun z => ‖f z‖ₑ) hfe
      (fun x => ENNReal.ofReal (H x)) hlp
  -- the sample integral is dominated pointwise by the spatial absolute integral
  have hF_le : ∀ ω, ‖∫ x, f (x, ω) ∂ν‖ₑ ^ p ≤ (∫⁻ x, ‖f (x, ω)‖ₑ ∂ν) ^ p := fun ω =>
    ENNReal.rpow_le_rpow (enorm_integral_le_lintegral_enorm _) hp0
  have hM : ∫⁻ x, ENNReal.ofReal (H x) ∂ν = ENNReal.ofReal (∫ x, H x ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hHi hnonneg).symm
  have hF_lint : ∫⁻ ω, ‖∫ x, f (x, ω) ∂ν‖ₑ ^ p ∂Q ≤
      ∫⁻ ω, (∫⁻ x, ‖f (x, ω)‖ₑ ∂ν) ^ p ∂Q :=
    lintegral_mono fun ω => hF_le ω
  have hnorm : ∫⁻ ω, ‖∫ x, f (x, ω) ∂ν‖ₑ ^ p ∂Q ≤ (ENNReal.ofReal (∫ x, H x ∂ν)) ^ p := by
    rw [← hM]
    exact hF_lint.trans hpow
  -- strong measurability of the sample integral, via the swapped product
  have hFsm : StronglyMeasurable fun ω => ∫ x, f (x, ω) ∂ν := by
    have hfs : StronglyMeasurable fun z : Ω × X => f (z.2, z.1) :=
      (hf.comp measurable_swap).stronglyMeasurable
    exact hfs.integral_prod_right'
  have hbound : eLpNorm (fun ω => ∫ x, f (x, ω) ∂ν) (ENNReal.ofReal p) Q ≤
      ENNReal.ofReal (∫ x, H x ∂ν) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hE_ne_zero hE_ne_top hFsm.aestronglyMeasurable,
      hE_toReal]
    calc (∫⁻ ω, ‖∫ x, f (x, ω) ∂ν‖ₑ ^ p ∂Q) ^ (1 / p)
        ≤ ((ENNReal.ofReal (∫ x, H x ∂ν)) ^ p) ^ (1 / p) :=
          ENNReal.rpow_le_rpow hnorm (one_div_nonneg.2 hp0)
      _ = ENNReal.ofReal (∫ x, H x ∂ν) := integralMoment_rpow_rpow_inv (by linarith) _
  have hmemF : MemLp (fun ω => ∫ x, f (x, ω) ∂ν) (ENNReal.ofReal p) Q :=
    lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  exact ⟨hsec, hmemF, hbound⟩

end EinsteinRelation.Correctors
