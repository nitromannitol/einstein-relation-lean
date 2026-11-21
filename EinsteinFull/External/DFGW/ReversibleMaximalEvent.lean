import EinsteinFull.External.DFGW.DynkinTimeReversal
import EinsteinFull.External.DFGW.MartingaleMaximal

/-! # Maximal events under time reversal

A forward and reversed increment representation controls excursions of an observable by its
initial value and two martingale maximal events.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- A forward-reversed representation controls a finite maximal event by the initial value
and the corresponding forward and reversed maximal events. -/
theorem measureReal_max_of_forward_sub_reversed
    (Z M : ℕ → Ω → ℝ) (R : Ω → Ω) (n : ℕ) (a : ℝ) (ha : 0 < a)
    (hrep : ∀ᵐ ω ∂P, ∀ k ≤ n, 2 * (Z k ω - Z 0 ω) =
      M k ω - (M n (R ω) - M (n - k) (R ω))) :
    P.real {ω | ∃ k ≤ n, a ≤ |Z k ω|} ≤
      P.real {ω | a / 4 ≤ |Z 0 ω|} +
      P.real {ω | ∃ k ≤ n, a / 4 ≤ |M k ω|} +
      P.real {ω | ∃ k ≤ n, a / 4 ≤ |M k (R ω)|} := by
  let A : Set Ω := {ω | ∃ k ≤ n, a ≤ |Z k ω|}
  let B : Set Ω := {ω | a / 4 ≤ |Z 0 ω|}
  let C : Set Ω := {ω | ∃ k ≤ n, a / 4 ≤ |M k ω|}
  let D : Set Ω := {ω | ∃ k ≤ n, a / 4 ≤ |M k (R ω)|}
  have hsub : A ≤ᵐ[P] (B ∪ C) ∪ D := by
    filter_upwards [hrep] with ω hω hA
    by_contra hnot
    have hB : |Z 0 ω| < a / 4 := by
      have : ω ∉ B := fun hb => hnot (Or.inl (Or.inl hb))
      exact lt_of_not_ge this
    have hC (k : ℕ) (hk : k ≤ n) : |M k ω| < a / 4 := by
      have : ω ∉ C := fun hc => hnot (Or.inl (Or.inr hc))
      exact lt_of_not_ge (fun hc => this ⟨k, hk, hc⟩)
    have hD (k : ℕ) (hk : k ≤ n) : |M k (R ω)| < a / 4 := by
      have : ω ∉ D := fun hd => hnot (Or.inr hd)
      exact lt_of_not_ge (fun hd => this ⟨k, hk, hd⟩)
    obtain ⟨k, hk, hZ⟩ := hA
    have htriangle : |Z k ω| ≤ |Z k ω - Z 0 ω| + |Z 0 ω| := by
      calc
        |Z k ω| = |(Z k ω - Z 0 ω) + Z 0 ω| := by rw [sub_add_cancel]
        _ ≤ _ := abs_add_le _ _
    have hmart : |2 * (Z k ω - Z 0 ω)| ≤
        |M k ω| + |M n (R ω)| + |M (n - k) (R ω)| := by
      rw [hω k hk]
      calc
        |M k ω - (M n (R ω) - M (n - k) (R ω))| ≤
            |M k ω| + |M n (R ω) - M (n - k) (R ω)| := abs_sub _ _
        _ ≤ _ := by linarith [abs_sub (M n (R ω)) (M (n - k) (R ω))]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hmart
    have hn : n - k ≤ n := Nat.sub_le n k
    have hMn := hD n le_rfl
    have hMnk := hD (n - k) hn
    have hMk := hC k hk
    linarith
  have hle : P.real A ≤ P.real ((B ∪ C) ∪ D) := by
    exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  calc
    P.real A ≤ P.real ((B ∪ C) ∪ D) := hle
    _ ≤ P.real (B ∪ C) + P.real D := measureReal_union_le _ _
    _ ≤ P.real B + P.real C + P.real D := by
      linarith [measureReal_union_le (μ := P) B C]

end EinsteinFull.External.DFGW
