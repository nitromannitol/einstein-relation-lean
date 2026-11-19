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

/-- A quenched probability at most one half of ever crossing the negative barrier gives
the one-half annealed no-return bound. -/
theorem no_return_mass_of_backtracking_bound {d : ℕ} (hd : 2 ≤ d)
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (hpath : HasPathMarginals Q K P) (R : ℝ)
    (hback : ∀ᵐ ω ∂Q, P (0, ω) {γ |
      firstHittingBelow γ (Regeneration.Renewal.forceCoord hd) (-R) ≠ ⊤} ≤
        ENNReal.ofReal (1 / 2 : ℝ)) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤ annealedCoupledLaw Q K (EinsteinFull.regenerationNoReturn hd R) := by
  apply no_return_mass_of_quenched hd Q P K hK hpath R
  filter_upwards [hK.1, hpath.1, hback] with ω hprob hmap hb
  have : IsProbabilityMeasure (P (0, ω)) := by
    rw [← hmap]
    exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).2 hprob
  let E : Set (Path d) := {γ | NoBacktracking R γ (Regeneration.Renewal.forceCoord hd)}
  have hE : MeasurableSet E := measurableSet_NoBacktracking R _
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 : ℝ≥0∞) / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  have hb' : P (0, ω) Eᶜ ≤ (1 : ℝ≥0∞) / 2 := by
    simpa only [E, NoBacktracking, Set.compl_ofPred, not_not, ← hhalf] using hb
  have hsum : P (0, ω) E + P (0, ω) Eᶜ = 1 := by
    simpa using measure_add_measure_compl (μ := P (0, ω)) hE
  have hle : (1 : ℝ≥0∞) ≤ P (0, ω) E + (1 : ℝ≥0∞) / 2 := by
    calc
      1 = P (0, ω) E + P (0, ω) Eᶜ := hsum.symm
      _ ≤ P (0, ω) E + (1 : ℝ≥0∞) / 2 := add_le_add_right hb' _
  rw [hhalf]
  apply ENNReal.le_of_add_le_add_right (by simp : (1 : ℝ≥0∞) / 2 ≠ ⊤)
  exact (ENNReal.add_halves 1).le.trans hle

end EinsteinFull.Regeneration
