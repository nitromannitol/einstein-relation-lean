import EinsteinRelation.Environment.SquareRootLawTransportSupport
import EinsteinRelation.Correctors.StationaryGradientDomainSupport

/-! Source: `paper/main.tex:198-207`, Assumption 1.1. Translation ergodicity of the
time-changed environment law and a.e. constancy of translation-invariant observables. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

/-- The reduced environment law is translation ergodic: `reduce` commutes with the
translations (`reduce_translate`), so `isErgodic_map_of_equivariant` transfers
`Localization.environmentLaw_translation_ergodic`. -/
theorem reducedEnvironmentLaw_ergodic {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hd : 2 ≤ d) : IsErgodicUnder translate (reducedEnvironmentLaw Q) := by
  rw [reducedEnvironmentLaw]
  apply EinsteinRelation.isErgodic_map_of_equivariant translate Q.measure reduce
    Probability.measurable_reduce
  · intro A hA hInv
    exact Localization.environmentLaw_translation_ergodic Q hd A hA hInv
  · intro z x
    exact reduce_translate x z

/-- A measurable observable that is almost surely invariant under every translation is
almost surely constant under an ergodic law. (Use
`exists_eventuallyEq_const_of_forall_separating MeasurableSet` with preimages of
measurable sets, which are invariant up to null sets.) -/
theorem ae_eq_const_of_translate_invariant {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hErg : IsErgodicUnder translate Q)
    {H : FieldPair d → ℝ} (hH : Measurable H)
    (hinv : ∀ z : Vec d, (fun ρ => H (translate z ρ)) =ᵐ[Q] H) :
    ∃ c : ℝ, H =ᵐ[Q] fun _ => c := by
  have h_preimage_inv (z : Vec d) (U : Set ℝ) :
      ∀ᵐ x ∂Q, (translate z x ∈ H ⁻¹' U ↔ x ∈ H ⁻¹' U) := by
    have hz := hinv z
    filter_upwards [hz] with x hx
    simpa [Set.mem_preimage] using congrArg (fun t => t ∈ U) hx
  have h_meas (U : Set ℝ) (hU : MeasurableSet U) :
      Q (H ⁻¹' U) = 0 ∨ Q (H ⁻¹' U) = 1 := by
    apply hErg (H ⁻¹' U) (hH hU)
    intro z
    exact h_preimage_inv z U
  have h_ae_cond (U : Set ℝ) (hU : MeasurableSet U) :
      (∀ᶠ x in ae Q, H x ∈ U) ∨ (∀ᶠ x in ae Q, H x ∉ U) := by
    have hpre : MeasurableSet (H ⁻¹' U) := hH hU
    rcases h_meas U hU with h | h
    · right
      rw [ae_iff]
      simpa [Set.mem_setOf_eq] using h
    · left
      rw [ae_iff]
      have hcompl : Q ((H ⁻¹' U)ᶜ) = 0 := by
        have htotal := measure_add_measure_compl (μ := Q) hpre
        have huniv : Q Set.univ = 1 := by simp
        rw [h, huniv] at htotal
        have h_one_ne_top := ENNReal.one_ne_top
        have htotal' : (1 : ENNReal) + Q ((H ⁻¹' U)ᶜ) = (1 : ENNReal) + 0 := by
          simpa [add_zero] using htotal
        exact (ENNReal.add_right_inj h_one_ne_top).mp htotal'
      simpa using hcompl
  apply Filter.exists_eventuallyEq_const_of_forall_separating (l := ae Q)
    MeasurableSet
  exact h_ae_cond

end EinsteinRelation.Correctors
