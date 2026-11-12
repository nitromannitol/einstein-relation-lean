import EinsteinRelation.Environment.FieldMeasurability
import EinsteinRelation.Localization.ReducedJointObservation

namespace EinsteinRelation.Localization

/-- All joint point observations generate the canonical compact-open Borel
sigma algebra. Source main.tex234–241; this identifies sigma algebras, not topologies. -/
theorem localSigma_univ_eq_borel {d : ℕ} :
    localSigma (Set.univ : Set (Vec d)) = (inferInstance : MeasurableSpace (FieldPair d)) := by
  apply le_antisymm (Probability.localSigma_le_borel _) 
  have hid : @Measurable (FieldPair d) (FieldPair d) (localSigma Set.univ)
      inferInstance id := by
    apply @measurable_fieldPair_of_evaluations (FieldPair d) (localSigma Set.univ) d id
    intro x
    apply Measurable.of_comap_le
    exact le_iSup_of_le (⟨x, Set.mem_univ x⟩ : (Set.univ : Set (Vec d))) le_rfl
  simpa only [MeasurableSpace.comap_id] using hid.comap_le

/-- The full reduced joint pair determines every physical Borel observation.
The local inverse identities discharge this globally, without an AE premise. -/
theorem comap_reduce_borel_eq {d : ℕ} :
    (inferInstance : MeasurableSpace (FieldPair d)).comap (reduce (d := d)) =
      (inferInstance : MeasurableSpace (FieldPair d)) := by
  simpa only [localSigma_univ_eq_borel] using
    (localSigma_comap_reduce (Set.univ : Set (Vec d)))
end EinsteinRelation.Localization
