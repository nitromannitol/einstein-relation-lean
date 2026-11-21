import EinsteinFull.External.DFGW.ReversibleMaximalEvent

/-! # A maximal inequality from time reversal

The forward and reversed martingale representation gives a finite-grid maximal inequality
under a measure-preserving time reflection.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
variable {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}

/-- Under a measure-preserving reflection, a finite reversible excursion is controlled by the
initial absolute moment and twice the terminal martingale absolute moment. -/
theorem measureReal_max_le_of_forward_sub_reversed
    (Z M : ℕ → Ω → ℝ) (R : Ω → Ω) (hR : MeasurePreserving R P P)
    (hZ0 : Martingale (fun _ : ℕ => Z 0) ℱ P) (hM : Martingale M ℱ P)
    (n : ℕ) (a : ℝ) (ha : 0 < a)
    (hrep : ∀ᵐ ω ∂P, ∀ k ≤ n, 2 * (Z k ω - Z 0 ω) =
      M k ω - (M n (R ω) - M (n - k) (R ω))) :
    (a / 4) * P.real {ω | ∃ k ≤ n, a ≤ |Z k ω|} ≤
      (∫ ω, |Z 0 ω| ∂P) + 2 * ∫ ω, |M n ω| ∂P := by
  let C : Set Ω := {ω | ∃ k ≤ n, a / 4 ≤ |M k ω|}
  have hC : MeasurableSet C := by
    have heq : C = ⋃ k : ℕ, ⋃ (_ : k ≤ n), {ω | a / 4 ≤ |M k ω|} := by
      ext ω
      simp [C]
    rw [heq]
    exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
      measurableSet_le measurable_const (continuous_abs.measurable.comp ((hM.stronglyMeasurable k).mono (ℱ.le k)).measurable)
  have hpres : P.real {ω | ∃ k ≤ n, a / 4 ≤ |M k (R ω)|} = P.real C := by
    change P.real (R ⁻¹' C) = P.real C
    simp only [Measure.real, hR.measure_preimage hC.nullMeasurableSet]
  have hbound := measureReal_max_of_forward_sub_reversed Z M R n a ha hrep
  rw [hpres] at hbound
  have hinit := measureReal_martingale_max_le (fun _ : ℕ => Z 0) hZ0 0 (show 0 ≤ a / 4 by positivity)
  have hinit' : (a / 4) * P.real {ω | a / 4 ≤ |Z 0 ω|} ≤ ∫ ω, |Z 0 ω| ∂P := by
    have hevent : {ω | ∃ k ≤ 0, a / 4 ≤ |Z 0 ω|} = {ω | a / 4 ≤ |Z 0 ω|} := by
      ext ω
      simp
    simpa only [hevent] using hinit
  have hmax : (a / 4) * P.real C ≤ ∫ ω, |M n ω| ∂P :=
    measureReal_martingale_max_le M hM n (show 0 ≤ a / 4 by positivity)
  have hmul := mul_le_mul_of_nonneg_left hbound (show 0 ≤ a / 4 by positivity)
  nlinarith

end EinsteinFull.External.DFGW
