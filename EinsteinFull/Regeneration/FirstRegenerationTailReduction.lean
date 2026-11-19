import EinsteinFull.Regeneration.FirstRegenerationMaximum

/-!
# Reduction of the first-regeneration tail

The final step of Gantert–Mathieu–Piatnitski, Lemma 5.8, combines the forward-hitting
estimate with the exponential estimate on the regeneration endpoint. The two estimates
and almost-sure finiteness remain explicit hypotheses.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The first-regeneration tail follows from the forward-hitting and endpoint estimates,
with constants independent of time. -/
theorem first_regeneration_tail_of_hitting_and_endpoint {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam l : ℝ) (hlam : 0 < lam) (hl : 0 < l)
    (i : Fin d) (hsupport : HasSuccessfulBridgeSupport Q Δ i (l / lam) K)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      firstRegenerationTime Δ lam (l / lam) ωz.2 i ≠ ⊤)
    (κ s C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hhit : ∀ (T : ℝ≥0) (a : ℝ),
      annealedCoupledLaw Q K {ωz | (T : ℝ≥0∞) ≤ firstHittingAbove ωz.2.1 i a} ≤
        ENNReal.ofReal (C * Real.exp (-κ * lam ^ 2 * T + lam * a)))
    (hend : ∀ b : ℝ,
      annealedCoupledLaw Q K {ωz | b ≤ lam *
        (ωz.2.1 (firstRegenerationTime Δ lam (l / lam) ωz.2 i).toNNReal i -
          ωz.2.1 0 i)} ≤ ENNReal.ofReal (D * Real.exp (-s * b))) :
    ∀ T : ℝ≥0,
      annealedCoupledLaw Q K {ωz |
        (T : ℝ≥0∞) < firstRegenerationTime Δ lam (l / lam) ωz.2 i} ≤
          ENNReal.ofReal ((C + D * Real.exp (12 * s * l)) *
            Real.exp (-(min (κ / 2) (s * κ / 2)) * lam ^ 2 * T)) := by
  let c : ℝ := min (κ / 2) (s * κ / 2)
  let C' : ℝ := C + D * Real.exp (12 * s * l)
  intro T
  let a : ℝ := κ * lam * (T : ℝ) / 2
  have hR : 0 < l / lam := div_pos hl hlam
  have htail := first_regeneration_tail_le_hitting_add_endpoint
    Q K hK Δ hΔ lam (l / lam) hlam hR i hsupport hfinite T a
  have hleft := hhit T a
  have hright : annealedCoupledLaw Q K {ωz | a - 12 * (l / lam) ≤
      ωz.2.1 (firstRegenerationTime Δ lam (l / lam) ωz.2 i).toNNReal i - ωz.2.1 0 i} ≤
      ENNReal.ofReal (D * Real.exp (-s * (lam * (a - 12 * (l / lam))))) := by
    apply (measure_mono ?_).trans (hend _)
    intro ωz hωz
    exact mul_le_mul_of_nonneg_left hωz hlam.le
  have ht : 0 ≤ lam ^ 2 * (T : ℝ) := by positivity
  have hc1 : c ≤ κ / 2 := min_le_left _ _
  have hc2 : c ≤ s * κ / 2 := min_le_right _ _
  have he1 : -κ * lam ^ 2 * (T : ℝ) + lam * a ≤ -c * lam ^ 2 * (T : ℝ) := by
    dsimp [a]
    nlinarith
  have hb : lam * (a - 12 * (l / lam)) = κ * lam ^ 2 * (T : ℝ) / 2 - 12 * l := by
    dsimp [a]
    field_simp
  have he2 : -s * (lam * (a - 12 * (l / lam))) ≤
      12 * s * l + -c * lam ^ 2 * (T : ℝ) := by
    rw [hb]
    nlinarith
  have hr : C * Real.exp (-κ * lam ^ 2 * (T : ℝ) + lam * a) +
      D * Real.exp (-s * (lam * (a - 12 * (l / lam)))) ≤
        C' * Real.exp (-c * lam ^ 2 * (T : ℝ)) := by
    calc
      _ ≤ C * Real.exp (-c * lam ^ 2 * (T : ℝ)) +
          D * Real.exp (12 * s * l + -c * lam ^ 2 * (T : ℝ)) := by
            gcongr
      _ = C' * Real.exp (-c * lam ^ 2 * (T : ℝ)) := by
        rw [Real.exp_add]
        dsimp [C']
        ring
  calc
    _ ≤ _ + _ := htail
    _ ≤ ENNReal.ofReal (C * Real.exp (-κ * lam ^ 2 * (T : ℝ) + lam * a)) +
        ENNReal.ofReal (D * Real.exp (-s * (lam * (a - 12 * (l / lam))))) :=
      add_le_add hleft hright
    _ = ENNReal.ofReal (C * Real.exp (-κ * lam ^ 2 * (T : ℝ) + lam * a) +
        D * Real.exp (-s * (lam * (a - 12 * (l / lam))))) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hr

end EinsteinFull.Regeneration
