import EinsteinRelation.Localization.CoefficientObservations
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Measurable actual continuous random fields

The canonical compact-open Borel carriers in `paper/main.tex:236–241,1212–1231`
can be observed through point evaluations. Countable dense evaluation gives a
measurable embedding; no identification of pointwise and compact-open topologies
is needed. This is also the measurability bridge for the actual sharpness law.
-/

open MeasureTheory
namespace EinsteinRelation

/-- Point evaluations characterize measurability on this Polish compact-open carrier. -/
theorem measurable_continuousMap_of_evaluations {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {E : Type*} [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] [PolishSpace C(Vec d, E)]
    (F : Ω → C(Vec d, E))
    (hF : ∀ x : Vec d, Measurable (fun ω => F ω x)) :
    @Measurable Ω C(Vec d, E) inferInstance (borel C(Vec d, E)) F := by
  letI : MeasurableSpace C(Vec d, E) := borel C(Vec d, E)
  letI : BorelSpace C(Vec d, E) := ⟨rfl⟩
  obtain ⟨D : Set (Vec d), hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  letI : Countable D := hDcount.to_subtype
  let E : C(Vec d, E) → (D → E) := fun f x => f x.1
  have hEcont : Continuous E := continuous_pi fun x => continuous_eval_const x.1
  have hEinj : Function.Injective E := by
    intro f g hfg
    apply ContinuousMap.injective_restrict hDdense
    exact ContinuousMap.ext fun x => congrFun hfg x
  have hEmb : MeasurableEmbedding E := hEcont.measurableEmbedding hEinj
  apply hEmb.measurable_comp_iff.mp
  exact measurable_pi_iff.mpr fun x => hF x.1

/-- Joint coefficient/scalar evaluations suffice for the literal field-pair Borel carrier. -/
theorem measurable_fieldPair_of_evaluations {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (F : Ω → FieldPair d)
    (hF : ∀ x : Vec d, Measurable (fun ω => ((F ω).1 x, (F ω).2 x))) :
    Measurable F := by
  letI : PolishSpace (Mat d) :=
    inferInstanceAs (PolishSpace (Fin d → Fin d → ℝ))
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : MeasurableSpace (CoefficientField d) := borel (CoefficientField d)
  letI : BorelSpace (CoefficientField d) := ⟨rfl⟩
  letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
  letI : BorelSpace C(Vec d, ℝ) := ⟨rfl⟩
  have h₁ := measurable_continuousMap_of_evaluations (fun ω => (F ω).1)
    (fun x => (hF x).fst)
  have h₂ := measurable_continuousMap_of_evaluations (fun ω => (F ω).2)
    (fun x => (hF x).snd)
  change @Measurable Ω (CoefficientField d × C(Vec d, ℝ)) inferInstance
    (borel (CoefficientField d × C(Vec d, ℝ))) F
  rw [← (Prod.borelSpace (α := CoefficientField d) (β := C(Vec d, ℝ))).measurable_eq]
  exact h₁.prodMk h₂

end EinsteinRelation
