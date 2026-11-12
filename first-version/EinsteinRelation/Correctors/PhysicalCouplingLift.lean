import EinsteinRelation.Correctors.AKMCarrierIdentificationTransport
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Lifting actual reduced couplings to physical environments

Source: `paper/main.tex:699–708,817–875,886–894`. The physical reduction
is a measurable embedding. Pullback of an actual reduced coupling therefore
lifts both samples to physical fields without extending the inverse beyond
its image. Both physical marginals are proved from the given reduced ones.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open ReductionImageV3 Environment.AKMTestIntegralSupport

/-- Literal reduction of two physical samples. Source: `paper/main.tex:699–708`. -/
noncomputable def physicalPairReduction {d : ℕ} {L : ℝ}
    (z : PhysicalField d L × PhysicalField d L) : FieldPair d × FieldPair d :=
  (reduce z.1.1, reduce z.2.1)

/-- Joint reduction is a measurable embedding on the physical subtype.
Source: `paper/main.tex:699–708`. -/
theorem measurableEmbedding_physicalPairReduction (d : ℕ) (L : ℝ) :
    MeasurableEmbedding (physicalPairReduction (d := d) (L := L)) := by
  have hr : MeasurableEmbedding (fun ω : PhysicalField d L => reduce ω.1) :=
    (Probability.measurableEmbedding_reduce d).comp
      (MeasurableEmbedding.subtype_coe (Sharpness.measurableSet_isRegular_fieldPair L))
  exact hr.prodMap hr

/-- Pullback along the literal physical reduction; no off-image sample is
chosen. Source: `paper/main.tex:699–708,886–894`. -/
noncomputable def physicalCouplingLift {d : ℕ} {L : ℝ}
    (ν : Measure (FieldPair d × FieldPair d)) :
    Measure (PhysicalField d L × PhysicalField d L) :=
  ν.comap physicalPairReduction

/-- A coupling with actual reduced marginals has an exact physical lift
with actual physical marginals. Source: `paper/main.tex:699–708,886–894`. -/
theorem physicalCouplingLift_properties {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (ν : Measure (FieldPair d × FieldPair d))
    [IsProbabilityMeasure ν]
    (hfst : MeasurePreserving Prod.fst ν (reducedEnvironmentLaw Q))
    (hsnd : MeasurePreserving Prod.snd ν (reducedEnvironmentLaw Q)) :
    IsProbabilityMeasure (physicalCouplingLift (L := L) ν) ∧
      MeasurePreserving physicalPairReduction (physicalCouplingLift (L := L) ν) ν ∧
      MeasurePreserving Prod.fst (physicalCouplingLift (L := L) ν) (physicalReferenceLaw Q) ∧
      MeasurePreserving Prod.snd (physicalCouplingLift (L := L) ν) (physicalReferenceLaw Q) := by
  let r : PhysicalField d L → FieldPair d := fun ω => reduce ω.1
  have hr : MeasurableEmbedding r :=
    (Probability.measurableEmbedding_reduce d).comp
      (MeasurableEmbedding.subtype_coe (Sharpness.measurableSet_isRegular_fieldPair L))
  have hj := measurableEmbedding_physicalPairReduction d L
  have hsupport : ∀ᵐ z ∂ν, z ∈ Set.range (physicalPairReduction (d := d) (L := L)) := by
    have hμ := ae_map_reduce_mem_physicalImage Q
    filter_upwards [hfst.quasiMeasurePreserving.ae hμ,
      hsnd.quasiMeasurePreserving.ae hμ] with z h₁ h₂
    rcases h₁ with ⟨ω, hω, hredω⟩
    rcases h₂ with ⟨η, hη, hredη⟩
    exact ⟨(⟨ω,hω⟩, ⟨η,hη⟩), Prod.ext hredω hredη⟩
  have hjmap : (physicalCouplingLift (L := L) ν).map physicalPairReduction = ν := by
    rw [physicalCouplingLift, hj.map_comap, Measure.restrict_eq_self_of_ae_mem hsupport]
  have hfirst : (physicalCouplingLift (L := L) ν).map Prod.fst = physicalReferenceLaw Q := by
    have he : ((physicalCouplingLift (L := L) ν).map Prod.fst).map r =
        (physicalReferenceLaw Q).map r := by
      rw [Measure.map_map hr.measurable measurable_fst]
      change (physicalCouplingLift (L := L) ν).map (Prod.fst ∘ physicalPairReduction) = _
      rw [← Measure.map_map measurable_fst hj.measurable, hjmap, hfst.map_eq]
      exact (measurePreserving_physicalReduction Q).map_eq.symm
    have hc := congrArg (fun μ => μ.comap r) he
    simpa only [hr.comap_map] using hc
  have hsecond : (physicalCouplingLift (L := L) ν).map Prod.snd = physicalReferenceLaw Q := by
    have he : ((physicalCouplingLift (L := L) ν).map Prod.snd).map r =
        (physicalReferenceLaw Q).map r := by
      rw [Measure.map_map hr.measurable measurable_snd]
      change (physicalCouplingLift (L := L) ν).map (Prod.snd ∘ physicalPairReduction) = _
      rw [← Measure.map_map measurable_snd hj.measurable, hjmap, hsnd.map_eq]
      exact (measurePreserving_physicalReduction Q).map_eq.symm
    have hc := congrArg (fun μ => μ.comap r) he
    simpa only [hr.comap_map] using hc
  exact ⟨hj.isProbabilityMeasure_comap hsupport, ⟨hj.measurable, hjmap⟩,
    ⟨measurable_fst, hfirst⟩, ⟨measurable_snd, hsecond⟩⟩

end EinsteinRelation.Correctors
