import EinsteinFull.Regeneration.FirstRegenerationMaximum
import Mathlib.Probability.Moments.Basic

/-!
# Reduction of the first-regeneration tail

The final step of Gantert–Mathieu–Piatnitski, Lemma 5.8, combines the forward-hitting
estimate with the exponential estimate on the regeneration endpoint. The two estimates
and almost-sure finiteness remain explicit hypotheses.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- An integrable exponential moment of the first-regeneration displacement bounds its
upper tail by Markov's inequality. -/
theorem first_regeneration_endpoint_tail_of_exp_moment {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (s D : ℝ) (hs : 0 ≤ s)
    (hint : Integrable (fun ωz : FieldPair d × CoupledSample d =>
      Real.exp (s * (lam * (ωz.2.1 (firstRegenerationTime Δ lam R ωz.2 i).toNNReal i -
        ωz.2.1 0 i)))) (annealedCoupledLaw Q K))
    (hmoment : (∫ ωz : FieldPair d × CoupledSample d,
      Real.exp (s * (lam * (ωz.2.1 (firstRegenerationTime Δ lam R ωz.2 i).toNNReal i -
        ωz.2.1 0 i))) ∂annealedCoupledLaw Q K) ≤ D) (b : ℝ) :
    annealedCoupledLaw Q K {ωz | b ≤ lam *
      (ωz.2.1 (firstRegenerationTime Δ lam R ωz.2 i).toNNReal i - ωz.2.1 0 i)} ≤
        ENNReal.ofReal (D * Real.exp (-s * b)) := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q K) :=
    annealedCoupledLaw_isProbabilityMeasure Q K hK
  let X : FieldPair d × CoupledSample d → ℝ := fun ωz => lam *
    (ωz.2.1 (firstRegenerationTime Δ lam R ωz.2 i).toNNReal i - ωz.2.1 0 i)
  have h := measure_ge_le_exp_mul_mgf (X := X) (μ := annealedCoupledLaw Q K) b hs hint
  have hm : mgf X (annealedCoupledLaw Q K) s ≤ D := hmoment
  rw [← ENNReal.ofReal_toReal (measure_ne_top (annealedCoupledLaw Q K) _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.exp (-s * b) * mgf X (annealedCoupledLaw Q K) s := h
    _ ≤ Real.exp (-s * b) * D := mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = D * Real.exp (-s * b) := mul_comm _ _

/-- The first-regeneration tail follows from the forward-hitting and endpoint estimates,
with constants independent of time. -/
theorem first_regeneration_tail_of_hitting_and_endpoint {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam l : ℝ) (hlam : 0 < lam) (hl : 0 < l)
    (i : Fin d) (hsupport : HasSuccessfulBridgeSupport Q Δ i (l / lam) K)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      firstRegenerationTime Δ lam (l / lam) ωz.2 i ≠ ⊤)
    (κ s C D : ℝ) (hκ : 0 ≤ κ) (hC : 0 < C) (hD : 0 < D)
    (hhit : ∀ (T : ℝ≥0) (a : ℝ), 0 ≤ a →
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
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hleft := hhit T a ha
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
