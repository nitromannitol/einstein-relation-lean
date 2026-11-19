import EinsteinFull.Regeneration.DowncrossingExponentialMoment

/-!
# Overshoot moments for a coupled path

The path marginal transfers the finite-downcrossing exponential moment to the
actual path-and-coin law without any independence assumption on the coins.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The exponential overshoot moment holds under any coupled law with the given path marginal. -/
theorem coupled_downcrossing_overshoot_exponential_moment {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hlam : 0 < lam) (h1 : lam ≤ 1)
    (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam hlam.le h1) (x : Vec d) (ν : Measure (CoupledSample d))
    (hpath : ν.map Prod.fst = G.pathLaw x) (i : Fin d) (R κ C a : ℝ)
    (hR : 0 ≤ R) (hκ : 0 < κ) (hC : 0 ≤ C) (ha : 0 < a) (haκ : a < κ / 2)
    (hback : ∀ y u, 0 ≤ u → G.pathLaw y {γ | firstHittingBelow γ i (-u) ≠ ⊤} ≤
      ENNReal.ofReal (C * Real.exp (-κ * lam * u))) :
    let E := {z : CoupledSample d | firstHittingBelow z.1 i (-R) ≠ ⊤}
    let F := fun z : CoupledSample d => Real.exp (a * lam *
      coordinateMaximum z.1 i (firstHittingBelow z.1 i (-R)).toNNReal)
    Integrable (E.indicator F) ν ∧
      (∫ z, E.indicator F z ∂ν) ≤
        max C 1 * Real.exp a / (1 - Real.exp (a - κ / 2)) := by
  dsimp only
  let E : Set (Path d) := {γ | firstHittingBelow γ i (-R) ≠ ⊤}
  let F : Path d → ℝ := fun γ => Real.exp (a * lam *
    coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal)
  obtain ⟨hi, hbound⟩ := downcrossing_overshoot_exponential_moment hd ω lam Λ hΛ hω
    hlam h1 G x i R κ C a hR hκ hC ha haκ hback
  change Integrable (E.indicator F) (G.pathLaw x) at hi
  change (∫ γ, E.indicator F γ ∂G.pathLaw x) ≤ _ at hbound
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
  rw [heq]
  refine ⟨hi', ?_⟩
  change (∫ z, (E.indicator F) z.1 ∂ν) ≤ _
  rw [← integral_map measurable_fst.aemeasurable hm, hpath]
  exact hbound

end EinsteinFull.Regeneration
