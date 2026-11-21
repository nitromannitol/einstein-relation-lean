import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_condition_u2D_iterate
import EinsteinRelation.Regeneration.RenewalFromSliceFactor
import EinsteinRelation.Regeneration.CycleRecordMeasurability

/-!
# The laws of the physical regeneration records

From the regeneration factorization of the physical coupling: a measurable shift carries each
record to the next, and every record after the first has the law of the first record under the
conditioned law.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The record shift and the record laws for the split coupling of the physical kernel, from the
conditioned factorization and its iteration. -/
theorem physical_record_laws
    (hiter : Blueprint.node_app_u3A_factorization_u23_condition_u2D_iterateStmt_phys)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) :
    ∃ Θ : FutureState d (Renewal.forceCoord hd) (l / lam) →
        FutureState d (Renewal.forceCoord hd) (l / lam),
      Measurable Θ ∧
      (∀ k, ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
        Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      (∀ k, ∀ᵐ q ∂regenerationConditionedLaw hd Q lam l K hK.1 hD,
        Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      (∀ k, 1 ≤ k → (annealedCoupledLaw Q.measure K).map (regenerationRecord hd lam l k) =
        (regenerationConditionedLaw hd Q lam l K hK.1 hD).map (regenerationRecord hd lam l 0)) ∧
      (∀ k, 1 ≤ k → (regenerationConditionedLaw hd Q lam l K hK.1 hD).map
          (regenerationRecord hd lam l k) =
        (regenerationConditionedLaw hd Q lam l K hK.1 hD).map (regenerationRecord hd lam l 0)) := by
  have hit := hiter d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD
  obtain ⟨-, ⟨Θ, hΘ, hΘae, -⟩, hΦ⟩ := hit
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure (regenerationConditionedLaw hd Q lam l K hK.1 hD) :=
    ProbabilityTheory.cond_isProbabilityMeasure hD
  have hY : ∀ k, Measurable (regenerationRecord hd lam l k) := fun k =>
    measurable_cycleRecord hd lam l k
  have hmarg : ∀ ρ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × CoupledSample d))), IsProbabilityMeasure ρ →
      ∀ k, 1 ≤ k → ρ.map (regenerationRecord hd lam l k) =
        (regenerationConditionedLaw hd Q lam l K hK.1 hD).map (regenerationRecord hd lam l 0) := by
    intro ρ hρ _ k hk
    apply measure_eq_of_bounded_real_tests
    intro f hf hbf
    rw [integral_map (hY k).aemeasurable hf.aestronglyMeasurable,
      integral_map (hY 0).aemeasurable hf.aestronglyMeasurable]
    exact (hΦ f hf hbf ρ hρ).1 k hk
  refine ⟨Θ, hΘ, hΘae _ (Set.mem_insert _ _), hΘae _ (Set.mem_insert_of_mem _ rfl), ?_, ?_⟩
  · exact hmarg _ (Set.mem_insert _ _) inferInstance
  · exact hmarg _ (Set.mem_insert_of_mem _ rfl) inferInstance

end EinsteinFull.Regeneration
