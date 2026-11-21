import EinsteinFull.External.DFGW.IntegralCauchy
import Mathlib.MeasureTheory.Order.Lattice

/-! # Second moments of finite maxima

The mean maximal square of equally distributed square-integrable variables, normalized by the
number of terms, is bounded uniformly by their common second moment.
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The normalized maximum of finitely many square-integrable variables is integrable and has
mean bounded by their common second moment. -/
theorem integrable_max_sq_and_integral_le (g : ℕ → Ω → ℝ)
    (hg : ∀ k, StronglyMeasurable (g k)) (hg2 : ∀ k, MemLp (g k) 2 P)
    (C : ℝ) (hmean : ∀ k, (∫ ω, (g k ω) ^ 2 ∂P) = C) (n : ℕ) :
    Integrable (fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ((n + 1 : ℝ)⁻¹) * (g k ω) ^ 2)) P ∧
    (∫ ω, (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ((n + 1 : ℝ)⁻¹) * (g k ω) ^ 2) ∂P) ≤ C := by
  let Y : ℕ → Ω → ℝ := fun k ω => ((n + 1 : ℝ)⁻¹) * (g k ω) ^ 2
  let H : Ω → ℝ := fun ω => ∑ k ∈ Finset.range (n + 1), Y k ω
  let Z : Ω → ℝ := fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => Y k ω)
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hY (k : ℕ) : Integrable (Y k) P := (hg2 k).integrable_sq.const_mul _
  have hY0 (k : ℕ) (ω : Ω) : 0 ≤ Y k ω := mul_nonneg (inv_nonneg.2 hn.le) (sq_nonneg _)
  have hH : Integrable H P := integrable_finsetSum _ (fun k _ => hY k)
  have hZmeas : StronglyMeasurable Z := by
    apply Measurable.stronglyMeasurable
    apply Finset.measurable_range_sup''
    intro k hk
    exact measurable_const.mul ((hg k).measurable.pow_const 2)
  have hZ0 (ω : Ω) : 0 ≤ Z ω := by
    have h := Finset.le_sup' (fun k : ℕ => Y k ω)
      (Finset.mem_range.2 (Nat.zero_lt_succ n))
    exact (hY0 0 ω).trans h
  have hZH (ω : Ω) : Z ω ≤ H ω := by
    apply Finset.sup'_le
    intro k hk
    exact Finset.single_le_sum (fun j _ => hY0 j ω) hk
  have hZ : Integrable Z P := hH.mono' hZmeas.aestronglyMeasurable
    (ae_of_all P fun ω => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hZ0 ω)] using hZH ω)
  refine ⟨hZ, ?_⟩
  calc
    (∫ ω, Z ω ∂P) ≤ ∫ ω, H ω ∂P := integral_mono hZ hH hZH
    _ = ∑ k ∈ Finset.range (n + 1), ((n + 1 : ℝ)⁻¹) * C := by
      rw [integral_finsetSum _ (fun k _ => hY k)]
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul, hmean k]
    _ = C := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      field_simp

end EinsteinFull.External.DFGW
