import EinsteinRelation.Correctors.ScalarDecompositionGlue
import EinsteinRelation.Correctors.ScalarDecompositionLocality
import EinsteinRelation.Correctors.ScalarGlobalMomentBounds

/-! # Joint assembly of the decomposition data

Source: `paper/main.tex:1044–1090`. The same literal finite sums satisfy
the two equations, all localizations, and all four moment bounds.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- Assemble every construction conclusion from the checked bands and
small-scale flux (`paper/main.tex:1044–1090`). -/
theorem scalarDecompositionData_of_bands {d : ℕ} (hd : 2 ≤ d)
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {p A B D F C₀ R : ℝ} (hp : 1 ≤ p)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (K : ℕ) (hR : R = (2 : ℝ) ^ K)
    (hcoef : ∃ L : ℝ, ∀ᵐ ω ∂Q, ∀ i j : Fin d, |ω.1 0 i j| ≤ L)
    (X H b : ℕ → FieldPair d → ℝ) (V W P : ℕ → FieldPair d → Vec d)
    (f e : FieldPair d → ℝ) (E₀ : FieldPair d → Vec d)
    (hX : ∀ k ∈ Finset.range K, Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] (X k))
    (hH : ∀ k ∈ Finset.range K, Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] (H k))
    (hV : ∀ k ∈ Finset.range K, Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] (V k))
    (hW : ∀ k ∈ Finset.range K, Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] (W k))
    (hP : ∀ k ∈ Finset.range K, Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] (P k))
    (hf : Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] f)
    (he : Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] e)
    (hE₀ : Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] E₀)
    (hband : ∀ k ∈ Finset.range K, SatisfiesReducedGeneratorEquation Q hQ 0
      (X k) (V k) (b k) (W k) (⟨0, by omega⟩ : Fin d))
    (hdrift : ∀ k ∈ Finset.range K, HasWeakHorizontalDivergence Q hQ (P k)
      (fun ω => dot ((ω.1 0).mulVec (unitVector (⟨0, by omega⟩ : Fin d))) (V k ω) - H k ω))
    (hsmall : HasWeakHorizontalDivergence Q hQ E₀
      (fun ω => f ω - e ω - ∑ k ∈ Finset.range K, b k ω))
    (hXb : ∀ k ∈ Finset.range K, eLpNorm (X k) (ENNReal.ofReal (2 * p)) Q ≤
      ENNReal.ofReal (A * ((2 : ℝ) ^ k + Real.sqrt (Real.log (2 + (2 : ℝ) ^ k)))))
    (hPb : ∀ k ∈ Finset.range K, eLpNorm (fun ω => euclideanNorm (P k ω)) (ENNReal.ofReal (2 * p)) Q ≤
      ENNReal.ofReal (A * ((2 : ℝ) ^ k + Real.sqrt (Real.log (2 + (2 : ℝ) ^ k)))))
    (hVb : ∀ k ∈ Finset.range K, eLpNorm (fun ω => euclideanNorm (V k ω)) (ENNReal.ofReal (2 * p)) Q ≤ ENNReal.ofReal A)
    (hWb : ∀ k ∈ Finset.range K, eLpNorm (fun ω => euclideanNorm (W k ω)) (ENNReal.ofReal (2 * p)) Q ≤
      ENNReal.ofReal (B * (Real.sqrt (Real.log (2 + (2 : ℝ) ^ k)) / (2 : ℝ) ^ k)))
    (hHb : ∀ k ∈ Finset.range K, eLpNorm (H k) (ENNReal.ofReal (2 * p)) Q ≤
      ENNReal.ofReal (B * (Real.sqrt (Real.log (2 + (2 : ℝ) ^ k)) / (2 : ℝ) ^ k)))
    (hE₀b : eLpNorm (fun ω => euclideanNorm (E₀ ω)) (ENNReal.ofReal (2 * p)) Q ≤ ENNReal.ofReal D)
    (heb : eLpNorm e (ENNReal.ofReal (2 * p)) Q ≤ ENNReal.ofReal (F * R⁻¹)) :
    let C := 8 * A + 24 * B + D + F
    ∃ (ψ h e' : FieldPair d → ℝ) (Dψ E P' : FieldPair d → Vec d),
      Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] ψ ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] h ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] e' ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] E ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] P' ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] Dψ ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < C₀ * R}] (fun ω => f ω - e' ω) ∧
      SatisfiesReducedGeneratorEquation Q hQ 0 ψ Dψ (fun ω => f ω - e' ω)
        (fun ω => -(E ω)) (⟨0, by omega⟩ : Fin d) ∧
      HasWeakHorizontalDivergence Q hQ P'
        (fun ω => dot ((ω.1 0).mulVec (unitVector (⟨0, by omega⟩ : Fin d))) (Dψ ω) - h ω) ∧
      eLpNorm ψ (ENNReal.ofReal (2 * p)) Q +
        eLpNorm (fun ω => euclideanNorm (P' ω)) (ENNReal.ofReal (2 * p)) Q ≤ ENNReal.ofReal (C * R) ∧
      eLpNorm (fun ω => euclideanNorm (Dψ ω)) (ENNReal.ofReal (2 * p)) Q ≤ ENNReal.ofReal (C * Real.log (2 + R)) ∧
      eLpNorm (fun ω => euclideanNorm (E ω)) (ENNReal.ofReal (2 * p)) Q +
        eLpNorm h (ENNReal.ofReal (2 * p)) Q ≤ ENNReal.ofReal C ∧
      eLpNorm e' (ENNReal.ofReal (2 * p)) Q ≤ ENNReal.ofReal (C * R⁻¹) := by
  dsimp only
  have hBorel := Probability.localSigma_le_borel {y : Vec d | euclideanNorm (y - 0) < C₀ * R}
  have hXm k hk : Measurable (X k) := (hX k hk).mono hBorel le_rfl
  have hHm k hk : Measurable (H k) := (hH k hk).mono hBorel le_rfl
  have hVm k hk : Measurable (V k) := (hV k hk).mono hBorel le_rfl
  have hWm k hk : Measurable (W k) := (hW k hk).mono hBorel le_rfl
  have hPm k hk : Measurable (P k) := (hP k hk).mono hBorel le_rfl
  have hm := measurable_localSigma_globalBands (Finset.range K) hX hH hV hW hP hf he hE₀
  have hb := scalarGlobal_moment_bounds (μ := Q) (ENNReal.one_le_ofReal.mpr (by linarith))
    hA hB hD hF K X H V W P E₀ e hXm hHm hVm hWm hPm
    (hE₀.mono hBorel le_rfl) hXb hPb hVb hWb hHb hE₀b (by simpa only [← hR] using heb)
  refine ⟨_, _, e, _, _, _, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1,
    hm.2.2.2.2.1, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2,
    satisfiesReducedGeneratorEquation_globalBands (Finset.range K) _ hcoef hband hsmall,
    hasWeakHorizontalDivergence_globalDrift (Finset.range K) _ hdrift, ?_⟩
  simpa only [← hR] using hb.2

end EinsteinRelation.Correctors
