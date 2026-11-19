import EinsteinFull.Frozen.RegenerationCoupling
import EinsteinFull.Regeneration.NoReturnFromHitting

/-!
# Uniform no-backtracking from a crossing estimate

Complementing the lower-barrier crossing event turns the quenched crossing
bound into the no-backtracking estimate used at regeneration trials.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A half bound for backward crossing gives a half no-backtracking bound for
every starting point of the supplied reduced diffusion. -/
theorem uniform_no_backtracking_of_crossing_bound {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hback : ∀ᵐ ω ∂Q.measure, ∀ x, P (x, ω) {γ |
      firstHittingBelow γ (Renewal.forceCoord hd) (-(l / lam)) ≠ ⊤} ≤
        ENNReal.ofReal (1 / 2 : ℝ)) :
    ∀ᵐ ω ∂Q.measure, ∀ x, ENNReal.ofReal (1 / 2 : ℝ) ≤
      P (x, ω) {γ | NoBacktracking (l / lam) γ (Renewal.forceCoord hd)} := by
  filter_upwards [hK.2.2.1, hback] with ω hP hb x
  obtain ⟨hω, G, hpath⟩ := hP
  let : IsProbabilityMeasure (P (x, ω)) := by
    rw [hpath x]
    exact G.pathLaw_isMarkovKernel.isProbabilityMeasure x
  let E : Set (Path d) := {γ | NoBacktracking (l / lam) γ (Renewal.forceCoord hd)}
  have hE : MeasurableSet E := measurableSet_NoBacktracking (l / lam) _
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 : ℝ≥0∞) / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  have hb' : P (x, ω) Eᶜ ≤ (1 : ℝ≥0∞) / 2 := by
    simpa only [E, NoBacktracking, Set.compl_ofPred, not_not, ← hhalf] using hb x
  have hsum : P (x, ω) E + P (x, ω) Eᶜ = 1 := by
    simpa using measure_add_measure_compl (μ := P (x, ω)) hE
  have hle : (1 : ℝ≥0∞) ≤ P (x, ω) E + (1 : ℝ≥0∞) / 2 := by
    calc
      1 = P (x, ω) E + P (x, ω) Eᶜ := hsum.symm
      _ ≤ P (x, ω) E + (1 : ℝ≥0∞) / 2 := add_le_add_right hb' _
  rw [hhalf]
  apply ENNReal.le_of_add_le_add_right (by simp : (1 : ℝ≥0∞) / 2 ≠ ⊤)
  exact (ENNReal.add_halves 1).le.trans hle

end EinsteinFull.Regeneration
