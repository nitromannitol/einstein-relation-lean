import EinsteinRelation.Environment.LocalIntegralMeasurability
import EinsteinRelation.Correctors.LocalConditioningBounds

/-! # Translation of coefficient-only local observations

Source: `paper/main.tex:913–938`. Only the reduced coefficient is observed
when conditioning the correctors. Joint translation measurability is proved
for that sigma algebra itself, rather than for the larger joint environment
sigma algebra.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- The translated reduced coefficient at a moving point is jointly
measurable using only coefficients in the containing observation window.
Source: `paper/main.tex:913–938`. -/
theorem measurable_translate_reducedObservation_joint {d : ℕ} {S U W : Set (Vec d)}
    (hSW : ∀ x ∈ S, ∀ y ∈ U, x + y ∈ W) :
    @Measurable (↥S × FieldPair d) (FieldPair d)
      (@Prod.instMeasurableSpace ↥S (FieldPair d) _ (reducedCoefficientObservationSigma W))
      (reducedCoefficientObservationSigma U) (fun p => translate (p.1 : Vec d) p.2) := by
  apply Measurable.of_comap_le
  unfold reducedCoefficientObservationSigma
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun y => ?_
  rw [MeasurableSpace.comap_comp]
  haveI : TopologicalSpace.PseudoMetrizableSpace (Mat d) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  have hcont : ∀ ω : FieldPair d, Continuous fun x : ↥S => ω.1 ((x : Vec d) + y.1) :=
    fun ω => ω.1.continuous.comp (continuous_subtype_val.add continuous_const)
  have hcoord : ∀ x : ↥S, @Measurable (FieldPair d) (Mat d)
      (reducedCoefficientObservationSigma W) inferInstance
      (fun ω => ω.1 ((x : Vec d) + y.1)) := by
    intro x
    apply Measurable.of_comap_le
    exact le_iSup_of_le (⟨x.1 + y.1, hSW x.1 x.2 y.1 y.2⟩ : W) le_rfl
  exact (MeasureTheory.measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : ↥S) (ω : FieldPair d) => ω.1 ((x : Vec d) + y.1)) hcont hcoord).comap_le

/-- A jointly measurable local field remains jointly measurable after
centering and translating its environment. Source: `paper/main.tex:931–938`. -/
theorem measurable_centered_local_observable {d : ℕ} {E : Type*} [MeasurableSpace E]
    {S U W : Set (Vec d)} (hSW : ∀ x ∈ S, ∀ y ∈ U, x + y ∈ W)
    (F : Vec d → FieldPair d → E)
    (hF : @Measurable (Vec d × FieldPair d) E
      (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (reducedCoefficientObservationSigma U))
      inferInstance (Function.uncurry F)) (z : Vec d) :
    @Measurable (↥S × FieldPair d) E
      (@Prod.instMeasurableSpace ↥S (FieldPair d) _ (reducedCoefficientObservationSigma W))
      inferInstance (fun p => F (z - (p.1 : Vec d)) (translate (p.1 : Vec d) p.2)) := by
  exact hF.comp ((measurable_const.sub (measurable_subtype_coe.comp measurable_fst)).prodMk
    (measurable_translate_reducedObservation_joint hSW))


/-- A fixed translated coefficient window is measurable from any containing
window. Source: `paper/main.tex:913–938`. -/
theorem measurable_translate_reducedObservation {d : ℕ} {U W : Set (Vec d)}
    (x : Vec d) (hx : ∀ y ∈ U, x + y ∈ W) :
    @Measurable (FieldPair d) (FieldPair d)
      (reducedCoefficientObservationSigma W) (reducedCoefficientObservationSigma U)
      (translate x) := by
  have hSW : ∀ z ∈ ({x} : Set (Vec d)), ∀ y ∈ U, z + y ∈ W := by
    intro z hz y hy
    simpa only [Set.mem_singleton_iff.mp hz] using hx y hy
  exact (measurable_translate_reducedObservation_joint hSW).comp
    ((measurable_const (a := (⟨x, Set.mem_singleton x⟩ : ({x} : Set (Vec d))))).prodMk
      measurable_id)

end EinsteinRelation.Correctors
