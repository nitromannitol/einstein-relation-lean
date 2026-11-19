import EinsteinFull.Regeneration.DowncrossingExponentialMoment
import EinsteinFull.Regeneration.ExponentialMomentContraction

/-!
# Contracting exponential moment on a failed downcrossing

The exponential overshoot estimate and a one-half crossing bound give the
strict moment contraction in Shen (2003), Proposition 4.7.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

attribute [local irreducible] firstHittingBelow coordinateMaximum

/-- Uniform crossing bounds yield a common exponential tilt whose expectation on the
finite-downcrossing event is at most three quarters. -/
theorem downcrossing_overshoot_moment_contraction (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) :
    ∃ a : ℝ, 0 < a ∧ ∀ {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
      (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hlam : 0 < lam) (h1 : lam ≤ 1)
      (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd Λ hΛ ω hω lam hlam.le h1) (x : Vec d) (i : Fin d) (R : ℝ), 0 ≤ R →
      (∀ y u, 0 ≤ u → G.pathLaw y {γ | firstHittingBelow γ i (-u) ≠ ⊤} ≤
        ENNReal.ofReal (C * Real.exp (-κ * lam * u))) →
      G.pathLaw x {γ | firstHittingBelow γ i (-R) ≠ ⊤} ≤ ENNReal.ofReal (1 / 2 : ℝ) →
      let E := {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤}
      let F := fun γ : Path d => Real.exp (a * lam *
        coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal)
      Integrable (E.indicator F) (G.pathLaw x) ∧
        (∫ γ, E.indicator F γ ∂G.pathLaw x) ≤ (3 / 4 : ℝ) := by
  let b : ℝ := κ / 4
  let M : ℝ := max C 1 * Real.exp b / (1 - Real.exp (b - κ / 2))
  have hb : 0 < b := by dsimp [b]; positivity
  have hbk : b < κ / 2 := by dsimp [b]; linarith
  have hexp : Real.exp (b - κ / 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hM : 0 < M := by
    dsimp [M]
    exact div_pos (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right C 1)) (Real.exp_pos _))
      (sub_pos.mpr hexp)
  let θ : ℝ := min (1 / 2) (1 / (4 * M))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hθM : θ * M ≤ 1 / 4 := by
    have hm := mul_le_mul_of_nonneg_right (min_le_right (1 / 2 : ℝ) (1 / (4 * M))) hM.le
    have he : (1 / (4 * M)) * M = (1 / 4 : ℝ) := by field_simp
    dsimp [θ]
    linarith
  refine ⟨θ * b, mul_pos hθ hb, ?_⟩
  intro d hd ω lam Λ hΛ hω hlam h1 G x i R hR hback hfail
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  let P := G.pathLaw x
  let E : Set (Path d) := {γ | firstHittingBelow γ i (-R) ≠ ⊤}
  let X : Path d → ℝ := downcrossingMaximum lam R i
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun (measurable_first_downcrossing R i) measurable_const).compl
  have hX : Measurable X := measurable_downcrossingMaximum lam R i
  have hmass : P.real E ≤ (1 / 2 : ℝ) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfail
    simpa only [P, E, measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] using h
  obtain ⟨hi, hiM⟩ := downcrossing_maximum_exponential_moment hd ω lam Λ hΛ hω
    hlam h1 G x i R κ C b hR hκ hC hb hbk hback
  change Integrable (fun γ => Real.exp (b * X γ)) P at hi
  have hiM' : (∫ γ, Real.exp (b * X γ) ∂P) ≤ M := hiM
  obtain ⟨htilt, htiltM⟩ := exponential_moment_indicator_le P E hE X hX b θ M hθ.le hθ1 hi hiM'
  let F : Path d → ℝ := fun γ => Real.exp ((θ * b) * lam *
    coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal)
  have heq : E.indicator F = E.indicator (fun γ => Real.exp ((θ * b) * X γ)) := by
    funext γ
    by_cases hγ : γ ∈ E
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hγ]
      dsimp only [F, X, downcrossingMaximum]
      rw [Set.indicator_of_mem hγ]
      congr 1
      ring
    · simp only [Set.indicator_of_notMem hγ]
  change Integrable (E.indicator F) P ∧ (∫ γ, E.indicator F γ ∂P) ≤ (3 / 4 : ℝ)
  rw [heq]
  exact ⟨htilt, htiltM.trans (by linarith)⟩

end EinsteinFull.Regeneration
