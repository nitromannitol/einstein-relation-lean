import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Measurable spatial equality events

Source: `paper/main.tex:693-702`. An almost-everywhere spatial equality
between jointly measurable fields is a measurable event in the parameter.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Joint measurability permits pushing an almost-everywhere spatial
equality through a measurable parameter map. -/
theorem ae_spatial_eq_of_map_pullback {A B X E : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [T2Space E] [SecondCountableTopology E]
    (μ : Measure B) (ν : Measure X) [SFinite ν]
    (π : B → A) (hπ : Measurable π) (f g : A → X → E)
    (hf : Measurable (fun p : A × X => f p.1 p.2))
    (hg : Measurable (fun p : A × X => g p.1 p.2))
    (heq : ∀ᵐ b ∂μ, ∀ᵐ x ∂ν, f (π b) x = g (π b) x) :
    ∀ᵐ a ∂Measure.map π μ, ∀ᵐ x ∂ν, f a x = g a x := by
  have hs : MeasurableSet {a | ∀ᵐ x ∂ν, f a x = g a x} := by
    simp only [ae_iff]
    exact measurableSet_eq_fun
      (measurable_measure_prodMk_left (measurableSet_eq_fun hf hg).compl) measurable_const
  exact (ae_map_iff hπ.aemeasurable hs).mpr heq

end EinsteinRelation.Correctors
