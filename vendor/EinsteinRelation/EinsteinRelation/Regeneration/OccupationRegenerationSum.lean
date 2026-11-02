import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.CompleteLattice.Finset

/-!
# Occupation bound summed over regeneration intervals (Proposition 3.2, Step 3)

Step 3 of the proof of Proposition 3.2 (`paper/main.tex` lines 491–496, `regen.occupation-time`).
Since the regeneration times satisfy `τ_k ≥ 2kΔ`, every `t ∈ [0, T]` lies in one of the
intervals `[τ_k, τ_{k+1})` with `k ≤ ⌊T/(2Δ)⌋₊`. Hence the integral of `g` over `[0, T]` is at
most the sum of its integrals over these intervals. Taking expectations, with each interval
term bounded by the same constant `M`, gives `(⌊T/(2Δ)⌋₊ + 1) M`, which is at most
`(T/(2Δ) + 1) M`.

The deterministic inequality uses real times. The expectation forms are stated for real-valued
times and for `ℝ≥0∞`-valued times, the type of `regenerationTime`. For the latter, the times
are finite almost surely and the interval integrals run over their real values.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinRelation

/-- Union bound over a finite family of time sets, by induction on the family. -/
theorem lintegral_biUnion_range_le (g : ℝ → ℝ≥0∞) (A : ℕ → Set ℝ) (s : Finset ℕ) :
    ∫⁻ t in ⋃ k ∈ s, A k, g t ≤ ∑ k ∈ s, ∫⁻ t in A k, g t := by
  induction s using Finset.induction_on with
  | empty =>
    have hU : (⋃ k ∈ (∅ : Finset ℕ), A k) = ∅ := by
      ext t
      simp
    simp only [hU, Finset.sum_empty, Measure.restrict_empty, lintegral_zero_measure, le_refl]
  | insert a s has ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert has]
    exact (lintegral_union_le g _ _).trans (add_le_add le_rfl ih)

/-- Covering of `[0, T]` by the intervals `[τ k, τ (k+1))` with `k ≤ N`, once `T < τ (N+1)`.
For `t ∈ [0, T]`, the index is the largest `k ≤ N` with `τ k ≤ t`. -/
theorem Icc_subset_biUnion_regeneration (τ : ℕ → ℝ) (hτ0 : τ 0 = 0) (N : ℕ) (T : ℝ)
    (hT : T < τ (N + 1)) :
    Icc 0 T ⊆ ⋃ k ∈ Finset.range (N + 1), Ico (τ k) (τ (k + 1)) := by
  intro t ht
  obtain ⟨ht0, htT⟩ := Set.mem_Icc.1 ht
  have h0 : τ 0 ≤ t := by
    rw [hτ0]
    exact ht0
  obtain ⟨m, hm⟩ : ∃ m, Nat.findGreatest (fun k => τ k ≤ t) N = m := ⟨_, rfl⟩
  have hmN : m ≤ N := by
    rw [← hm]
    exact Nat.findGreatest_le N
  have hτm : τ m ≤ t := by
    have h := Nat.findGreatest_spec (P := fun k => τ k ≤ t) (Nat.zero_le N) h0
    rw [hm] at h
    exact h
  have hlt : t < τ (m + 1) := by
    by_contra hcon
    have hle : τ (m + 1) ≤ t := not_lt.mp hcon
    rcases Nat.lt_or_ge m N with hmlt | hmge
    · have hnot := Nat.findGreatest_is_greatest (P := fun k => τ k ≤ t) (n := N) (k := m + 1)
        (by omega) (by omega)
      exact hnot hle
    · have hmN' : m = N := le_antisymm hmN hmge
      rw [hmN'] at hle
      linarith
  exact Set.mem_iUnion₂.2 ⟨m, Finset.mem_range.2 (by omega), Set.mem_Ico.2 ⟨hτm, hlt⟩⟩

/-- Since `τ k ≥ 2kΔ`, the time `τ (⌊T/(2Δ)⌋₊ + 1)` lies beyond `T`. -/
theorem lt_regeneration_succ_floor (Δ : ℝ) (hΔ : 0 < Δ) (τ : ℕ → ℝ)
    (hlow : ∀ k : ℕ, 2 * (k : ℝ) * Δ ≤ τ k) (T : ℝ) :
    T < τ (⌊T / (2 * Δ)⌋₊ + 1) := by
  have h2 : 0 < 2 * Δ := by linarith
  have h1 : T / (2 * Δ) < (⌊T / (2 * Δ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hkey : T / (2 * Δ) * (2 * Δ) = T := div_mul_cancel₀ T h2.ne'
  have h3 : T < ((⌊T / (2 * Δ)⌋₊ : ℝ) + 1) * (2 * Δ) := by
    have h5 := mul_lt_mul_of_pos_right h1 h2
    rw [hkey] at h5
    exact h5
  have h4 : 2 * ((⌊T / (2 * Δ)⌋₊ : ℝ) + 1) * Δ ≤ τ (⌊T / (2 * Δ)⌋₊ + 1) := by
    have h := hlow (⌊T / (2 * Δ)⌋₊ + 1)
    push_cast at h
    exact h
  calc T < ((⌊T / (2 * Δ)⌋₊ : ℝ) + 1) * (2 * Δ) := h3
    _ = 2 * ((⌊T / (2 * Δ)⌋₊ : ℝ) + 1) * Δ := by ring
    _ ≤ τ (⌊T / (2 * Δ)⌋₊ + 1) := h4

/-- Deterministic form of Step 3: the integral of `g` over `[0, T]` is at most the sum of its
integrals over the regeneration intervals `[τ k, τ (k+1))` with `k ≤ ⌊T/(2Δ)⌋₊`. -/
theorem lintegral_Icc_le_sum_regeneration (g : ℝ → ℝ≥0∞) (Δ : ℝ) (hΔ : 0 < Δ) (τ : ℕ → ℝ)
    (hτ0 : τ 0 = 0) (hlow : ∀ k : ℕ, 2 * (k : ℝ) * Δ ≤ τ k) (T : ℝ) :
    ∫⁻ t in Icc 0 T, g t ≤
      ∑ k ∈ Finset.range (⌊T / (2 * Δ)⌋₊ + 1), ∫⁻ t in Ico (τ k) (τ (k + 1)), g t :=
  le_trans
    (lintegral_mono_set (Icc_subset_biUnion_regeneration τ hτ0 ⌊T / (2 * Δ)⌋₊ T
      (lt_regeneration_succ_floor Δ hΔ τ hlow T)))
    (lintegral_biUnion_range_le g (fun k => Ico (τ k) (τ (k + 1)))
      (Finset.range (⌊T / (2 * Δ)⌋₊ + 1)))

/-- Measurability in `ω` of the integral of `g ω` over the random interval `[a ω, b ω)`, given
joint measurability of `(ω, t) ↦ g ω t`. The interval integral is written as an integral over
`t` of an indicator of a measurable subset of `Ω × ℝ`. -/
theorem measurable_lintegral_regeneration_interval {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω → ℝ → ℝ≥0∞) (hg : Measurable fun p : Ω × ℝ => g p.1 p.2) (a b : Ω → ℝ)
    (ha : Measurable a) (hb : Measurable b) :
    Measurable fun ω => ∫⁻ t in Ico (a ω) (b ω), g ω t := by
  have h1 : MeasurableSet {p : Ω × ℝ | a p.1 ≤ p.2} :=
    measurableSet_le (ha.comp measurable_fst) measurable_snd
  have h2 : MeasurableSet {p : Ω × ℝ | p.2 < b p.1} :=
    measurableSet_lt measurable_snd (hb.comp measurable_fst)
  have hS : MeasurableSet ({p : Ω × ℝ | a p.1 ≤ p.2} ∩ {p : Ω × ℝ | p.2 < b p.1}) :=
    h1.inter h2
  have hind : Measurable (({p : Ω × ℝ | a p.1 ≤ p.2} ∩ {p : Ω × ℝ | p.2 < b p.1}).indicator
      fun p : Ω × ℝ => g p.1 p.2) :=
    hg.indicator hS
  have hmem : ∀ (ω : Ω) (t : ℝ), t ∈ Ico (a ω) (b ω) ↔
      (ω, t) ∈ {p : Ω × ℝ | a p.1 ≤ p.2} ∩ {p : Ω × ℝ | p.2 < b p.1} :=
    fun ω t => Iff.rfl
  have hEq : ∀ ω : Ω, (∫⁻ t in Ico (a ω) (b ω), g ω t) =
      ∫⁻ t, ({p : Ω × ℝ | a p.1 ≤ p.2} ∩ {p : Ω × ℝ | p.2 < b p.1}).indicator
        (fun p : Ω × ℝ => g p.1 p.2) (ω, t) := by
    intro ω
    have hint : (∫⁻ t in Ico (a ω) (b ω), g ω t) =
        ∫⁻ t, (Ico (a ω) (b ω)).indicator (g ω) t :=
      (lintegral_indicator measurableSet_Ico (g ω)).symm
    rw [hint]
    refine lintegral_congr fun t => ?_
    by_cases h : t ∈ Ico (a ω) (b ω)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem ω t).1 h)]
    · have hnot : (ω, t) ∉ {p : Ω × ℝ | a p.1 ≤ p.2} ∩ {p : Ω × ℝ | p.2 < b p.1} :=
        fun h' => h ((hmem ω t).2 h')
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hnot]
  have hfun : Measurable fun ω => ∫⁻ t,
      ({p : Ω × ℝ | a p.1 ≤ p.2} ∩ {p : Ω × ℝ | p.2 < b p.1}).indicator
        (fun p : Ω × ℝ => g p.1 p.2) (ω, t) :=
    hind.lintegral_prod_right'
  have hfeq : (fun ω => ∫⁻ t in Ico (a ω) (b ω), g ω t) = fun ω =>
      ∫⁻ t, ({p : Ω × ℝ | a p.1 ≤ p.2} ∩ {p : Ω × ℝ | p.2 < b p.1}).indicator
        (fun p : Ω × ℝ => g p.1 p.2) (ω, t) :=
    funext hEq
  rw [hfeq]
  exact hfun

/-- Step 3 of Proposition 3.2 in expectation, for real-valued regeneration times. The pathwise
covering holds almost surely, and each interval term has expectation at most `M`. -/
theorem lintegral_occupation_sum_expectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (g : Ω → ℝ → ℝ≥0∞) (hg : Measurable fun p : Ω × ℝ => g p.1 p.2)
    (Δ : ℝ) (hΔ : 0 < Δ) (τ : ℕ → Ω → ℝ) (hτ : ∀ k : ℕ, Measurable (τ k))
    (hpath : ∀ᵐ ω ∂P, τ 0 ω = 0 ∧ ∀ k : ℕ, 2 * (k : ℝ) * Δ ≤ τ k ω)
    (M : ℝ≥0∞)
    (hM : ∀ k : ℕ, ∫⁻ ω, (∫⁻ t in Ico (τ k ω) (τ (k + 1) ω), g ω t) ∂P ≤ M) (T : ℝ) :
    ∫⁻ ω, (∫⁻ t in Icc 0 T, g ω t) ∂P ≤ ((⌊T / (2 * Δ)⌋₊ + 1 : ℕ) : ℝ≥0∞) * M := by
  have hmeas : ∀ k : ℕ, Measurable fun ω => ∫⁻ t in Ico (τ k ω) (τ (k + 1) ω), g ω t :=
    fun k => measurable_lintegral_regeneration_interval g hg (τ k) (τ (k + 1)) (hτ k) (hτ (k + 1))
  calc ∫⁻ ω, (∫⁻ t in Icc 0 T, g ω t) ∂P
      ≤ ∫⁻ ω, (∑ k ∈ Finset.range (⌊T / (2 * Δ)⌋₊ + 1),
          ∫⁻ t in Ico (τ k ω) (τ (k + 1) ω), g ω t) ∂P :=
        lintegral_mono_ae (hpath.mono fun ω hω =>
          lintegral_Icc_le_sum_regeneration (g ω) Δ hΔ (fun k => τ k ω) hω.1 hω.2 T)
    _ = ∑ k ∈ Finset.range (⌊T / (2 * Δ)⌋₊ + 1),
          ∫⁻ ω, (∫⁻ t in Ico (τ k ω) (τ (k + 1) ω), g ω t) ∂P :=
        lintegral_finset_sum _ fun k _ => hmeas k
    _ ≤ ∑ k ∈ Finset.range (⌊T / (2 * Δ)⌋₊ + 1), M := Finset.sum_le_sum fun k _ => hM k
    _ = ((⌊T / (2 * Δ)⌋₊ + 1 : ℕ) : ℝ≥0∞) * M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The number of regeneration intervals is at most `T/(2Δ) + 1` for `T ≥ 0`. -/
theorem card_floor_succ_le_ofReal (Δ : ℝ) (hΔ : 0 < Δ) (T : ℝ) (hT : 0 ≤ T) :
    ((⌊T / (2 * Δ)⌋₊ + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (T / (2 * Δ) + 1) := by
  have hx : 0 ≤ T / (2 * Δ) := div_nonneg hT (by linarith)
  have hfloor : (⌊T / (2 * Δ)⌋₊ : ℝ) ≤ T / (2 * Δ) := Nat.floor_le hx
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  linarith

/-- Real-number form of Step 3 for real-valued regeneration times:
the expectation is at most `ENNReal.ofReal (T/(2Δ) + 1) * M`. -/
theorem lintegral_occupation_expectation_ofReal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (g : Ω → ℝ → ℝ≥0∞) (hg : Measurable fun p : Ω × ℝ => g p.1 p.2)
    (Δ : ℝ) (hΔ : 0 < Δ) (τ : ℕ → Ω → ℝ) (hτ : ∀ k : ℕ, Measurable (τ k))
    (hpath : ∀ᵐ ω ∂P, τ 0 ω = 0 ∧ ∀ k : ℕ, 2 * (k : ℝ) * Δ ≤ τ k ω)
    (M : ℝ≥0∞)
    (hM : ∀ k : ℕ, ∫⁻ ω, (∫⁻ t in Ico (τ k ω) (τ (k + 1) ω), g ω t) ∂P ≤ M) (T : ℝ)
    (hT : 0 ≤ T) :
    ∫⁻ ω, (∫⁻ t in Icc 0 T, g ω t) ∂P ≤ ENNReal.ofReal (T / (2 * Δ) + 1) * M :=
  (lintegral_occupation_sum_expectation P g hg Δ hΔ τ hτ hpath M hM T).trans
    (mul_le_mul_of_nonneg_right (card_floor_succ_le_ofReal Δ hΔ T hT) zero_le)

/-- Step 3 of Proposition 3.2 in expectation, for `ℝ≥0∞`-valued regeneration times as returned
by `regenerationTime`. Almost surely each time is finite, satisfies `ENNReal.ofReal (2kΔ) ≤ τ k`,
and `τ 0 = 0`. The interval integrals run over the real values of the times. -/
theorem lintegral_occupation_sum_expectation_ennreal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Ω → ℝ → ℝ≥0∞) (hg : Measurable fun p : Ω × ℝ => g p.1 p.2)
    (Δ : ℝ) (hΔ : 0 < Δ) (τ : ℕ → Ω → ℝ≥0∞) (hτ : ∀ k : ℕ, Measurable (τ k))
    (hpath : ∀ᵐ ω ∂P, τ 0 ω = 0 ∧
      ∀ k : ℕ, τ k ω ≠ ⊤ ∧ ENNReal.ofReal (2 * (k : ℝ) * Δ) ≤ τ k ω)
    (M : ℝ≥0∞)
    (hM : ∀ k : ℕ,
      ∫⁻ ω, (∫⁻ t in Ico (τ k ω).toReal (τ (k + 1) ω).toReal, g ω t) ∂P ≤ M)
    (T : ℝ) :
    ∫⁻ ω, (∫⁻ t in Icc 0 T, g ω t) ∂P ≤ ((⌊T / (2 * Δ)⌋₊ + 1 : ℕ) : ℝ≥0∞) * M := by
  have hpathR : ∀ᵐ ω ∂P, (τ 0 ω).toReal = 0 ∧
      ∀ k : ℕ, 2 * (k : ℝ) * Δ ≤ (τ k ω).toReal := by
    filter_upwards [hpath] with ω hω
    refine ⟨?_, fun k => ?_⟩
    · rw [hω.1, ENNReal.toReal_zero]
    · exact (ENNReal.ofReal_le_iff_le_toReal (hω.2 k).1).1 (hω.2 k).2
  exact lintegral_occupation_sum_expectation P g hg Δ hΔ (fun k ω => (τ k ω).toReal)
    (fun k => (hτ k).ennreal_toReal) hpathR M hM T

/-- Real-number form of Step 3 for `ℝ≥0∞`-valued regeneration times:
the expectation is at most `ENNReal.ofReal (T/(2Δ) + 1) * M`. -/
theorem lintegral_occupation_expectation_ennreal_ofReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Ω → ℝ → ℝ≥0∞) (hg : Measurable fun p : Ω × ℝ => g p.1 p.2)
    (Δ : ℝ) (hΔ : 0 < Δ) (τ : ℕ → Ω → ℝ≥0∞) (hτ : ∀ k : ℕ, Measurable (τ k))
    (hpath : ∀ᵐ ω ∂P, τ 0 ω = 0 ∧
      ∀ k : ℕ, τ k ω ≠ ⊤ ∧ ENNReal.ofReal (2 * (k : ℝ) * Δ) ≤ τ k ω)
    (M : ℝ≥0∞)
    (hM : ∀ k : ℕ,
      ∫⁻ ω, (∫⁻ t in Ico (τ k ω).toReal (τ (k + 1) ω).toReal, g ω t) ∂P ≤ M)
    (T : ℝ) (hT : 0 ≤ T) :
    ∫⁻ ω, (∫⁻ t in Icc 0 T, g ω t) ∂P ≤ ENNReal.ofReal (T / (2 * Δ) + 1) * M :=
  (lintegral_occupation_sum_expectation_ennreal P g hg Δ hΔ τ hτ hpath M hM T).trans
    (mul_le_mul_of_nonneg_right (card_floor_succ_le_ofReal Δ hΔ T hT) zero_le)

end EinsteinRelation
