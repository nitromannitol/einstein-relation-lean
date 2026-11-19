import EinsteinFull.Frozen.RegenerationNoReturn
import EinsteinRelation.Regeneration.Measurability

/-!
# No-return mass from quenched path estimates

The no-return event depends only on the path. The path marginal of the actual regeneration
coupling transfers any uniform quenched lower bound to the corresponding annealed mass.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The annealed coupling assigns to a path event the environment average of its quenched
origin probability. -/
theorem annealed_path_event_eq {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (hpath : HasPathMarginals Q K P)
    (E : Set (Path d)) (hE : MeasurableSet E) :
    annealedCoupledLaw Q K {ωz | ωz.2.1 ∈ E} = ∫⁻ ω, P (0, ω) E ∂Q := by
  have hevent : {ωz : FieldPair d × CoupledSample d | ωz.2.1 ∈ E} =
      Set.univ ×ˢ (Prod.fst ⁻¹' E) := by ext ωz; simp
  rw [hevent, annealedCoupledLaw, Measure.compProd_apply_prod MeasurableSet.univ
    (hE.preimage measurable_fst)]
  simp only [setLIntegral_univ]
  apply lintegral_congr_ae
  filter_upwards [hK.1, hpath.1] with ω hprob hmap
  have : IsProbabilityMeasure (originCoupledLaw K ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
  rw [← hmap, Measure.map_apply measurable_fst hE]
  rfl

/-- A quenched no-backtracking lower bound gives the same annealed lower bound for the
literal no-return event. -/
theorem no_return_mass_of_quenched {d : ℕ} (hd : 2 ≤ d)
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (hpath : HasPathMarginals Q K P) (R : ℝ) (c : ℝ≥0∞)
    (hlower : ∀ᵐ ω ∂Q, c ≤ P (0, ω) {γ | NoBacktracking R γ (Regeneration.Renewal.forceCoord hd)}) :
    c ≤ annealedCoupledLaw Q K (EinsteinFull.regenerationNoReturn hd R) := by
  let E : Set (Path d) := {γ | NoBacktracking R γ (Regeneration.Renewal.forceCoord hd)}
  have hE : MeasurableSet E := measurableSet_NoBacktracking R _
  change c ≤ annealedCoupledLaw Q K {ωz | ωz.2.1 ∈ E}
  rw [annealed_path_event_eq Q P K hK hpath E hE]
  calc
    c = ∫⁻ _ω, c ∂Q := by simp
    _ ≤ ∫⁻ ω, P (0, ω) E ∂Q := lintegral_mono_ae hlower

end EinsteinFull.Regeneration
