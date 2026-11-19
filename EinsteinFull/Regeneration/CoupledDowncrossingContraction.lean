import EinsteinFull.Regeneration.DowncrossingMomentContraction

/-!
# Overshoot contraction for a coupled path

The path marginal carries the finite-downcrossing moment contraction to the
split path-and-coin law.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

attribute [local irreducible] firstHittingBelow coordinateMaximum

/-- The uniform failed-downcrossing contraction holds for every coupled law
with the supplied diffusion as path marginal. -/
theorem coupled_downcrossing_overshoot_moment_contraction (κ C : ℝ)
    (hκ : 0 < κ) (hC : 0 ≤ C) :
    ∃ a : ℝ, 0 < a ∧ ∀ {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
      (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hlam : 0 < lam) (h1 : lam ≤ 1)
      (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd Λ hΛ ω hω lam hlam.le h1) (x : Vec d) (ν : Measure (CoupledSample d)),
      ν.map Prod.fst = G.pathLaw x → ∀ (i : Fin d) (R : ℝ), 0 ≤ R →
      (∀ y u, 0 ≤ u → G.pathLaw y {γ | firstHittingBelow γ i (-u) ≠ ⊤} ≤
        ENNReal.ofReal (C * Real.exp (-κ * lam * u))) →
      G.pathLaw x {γ | firstHittingBelow γ i (-R) ≠ ⊤} ≤ ENNReal.ofReal (1 / 2 : ℝ) →
      let E := {z : CoupledSample d | firstHittingBelow z.1 i (-R) ≠ ⊤}
      let F := fun z : CoupledSample d => Real.exp (a * lam *
        coordinateMaximum z.1 i (firstHittingBelow z.1 i (-R)).toNNReal)
      Integrable (E.indicator F) ν ∧ (∫ z, E.indicator F z ∂ν) ≤ (3 / 4 : ℝ) := by
  obtain ⟨a, ha, h⟩ := downcrossing_overshoot_moment_contraction κ C hκ hC
  refine ⟨a, ha, ?_⟩
  intro d hd ω lam Λ hΛ hω hlam h1 G x ν hpath i R hR hback hfail
  let E : Set (Path d) := {γ | firstHittingBelow γ i (-R) ≠ ⊤}
  let F : Path d → ℝ := fun γ => Real.exp (a * lam *
    coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal)
  obtain ⟨hi, hbound⟩ := h hd ω lam Λ hΛ hω hlam h1 G x i R hR hback hfail
  change Integrable (E.indicator F) (G.pathLaw x) at hi
  change (∫ γ, E.indicator F γ ∂G.pathLaw x) ≤ (3 / 4 : ℝ) at hbound
  have hm : AEStronglyMeasurable (E.indicator F) (ν.map Prod.fst) := by
    rw [hpath]
    exact hi.aestronglyMeasurable
  have hi' : Integrable ((E.indicator F) ∘ Prod.fst) ν := by
    apply (integrable_map_measure hm measurable_fst.aemeasurable).mp
    rw [hpath]
    exact hi
  have heq : (fun z : CoupledSample d =>
      {z : CoupledSample d | firstHittingBelow z.1 i (-R) ≠ ⊤}.indicator
        (fun z => Real.exp (a * lam * coordinateMaximum z.1 i
          (firstHittingBelow z.1 i (-R)).toNNReal)) z) = (E.indicator F) ∘ Prod.fst := by
    funext z
    by_cases hz : firstHittingBelow z.1 i (-R) = ⊤ <;> simp [E, F, hz]
  dsimp only
  rw [heq]
  refine ⟨hi', ?_⟩
  change (∫ z, (E.indicator F) z.1 ∂ν) ≤ _
  rw [← integral_map measurable_fst.aemeasurable hm, hpath]
  exact hbound

end EinsteinFull.Regeneration
