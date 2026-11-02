import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
open MeasureTheory
namespace EinsteinRelation.Probability

/-- A continuous field `X → E` can be decoded measurably from its raw values. Evaluation on a
countable dense set `A ⊆ X` is a continuous injection `C(X, E) → (A → E)`, hence a measurable
embedding for the Borel σ-algebra of `C(X, E)` (`Continuous.measurableEmbedding`). Its measurable
left inverse reconstructs every continuous field exactly from these countable observations, which
is the measurability input of the future record (`paper/main.tex:331–340, 377–403`). -/
theorem exists_measurable_continuousMap_decoder {X E : Type*}
    [TopologicalSpace X] [SecondCountableTopology X]
    [TopologicalSpace E] [PolishSpace E] [Nonempty E]
    [MeasurableSpace E] [BorelSpace E] [PolishSpace C(X, E)] :
    ∃ D : (X → E) → C(X, E),
      @Measurable (X → E) C(X, E) inferInstance (borel C(X, E)) D ∧
      ∀ f : C(X, E), D (fun x => f x) = f := by
  obtain ⟨A, hA_count, hA_dense⟩ := TopologicalSpace.exists_countable_dense X
  haveI hA : Countable A := hA_count.to_subtype
  -- Evaluation on the countable set `A` is continuous and injective on `C(X, E)`.
  have hEcont : Continuous fun f : C(X, E) => fun a : A => f (a : X) :=
    continuous_pi fun a =>
      (continuous_eval_const (a : X) : Continuous fun f : C(X, E) => f (a : X))
  have hEinj : Function.Injective fun f : C(X, E) => fun a : A => f (a : X) := by
    intro f g hfg
    have hfun : (f : X → E) = (g : X → E) := by
      refine Continuous.ext_on hA_dense f.continuous g.continuous ?_
      intro x hx
      have hx_eval := congrFun hfg ⟨x, hx⟩
      exact hx_eval
    exact ContinuousMap.ext (congrFun hfun)
  -- The Borel σ-algebra on `C(X, E)`, as used in the statement.
  letI : MeasurableSpace C(X, E) := borel C(X, E)
  haveI : BorelSpace C(X, E) := ⟨rfl⟩
  haveI : Nonempty C(X, E) :=
    ⟨ContinuousMap.const X (Nonempty.some (inferInstance : Nonempty E))⟩
  have hemb := hEcont.measurableEmbedding hEinj
  have hrestrict : Measurable fun g : X → E => fun a : A => g (a : X) :=
    Measurable.of_eval fun a => measurable_pi_apply (a : X)
  refine ⟨fun g => hemb.invFun (fun a : A => g (a : X)), ?_, ?_⟩
  · exact hemb.measurable_invFun.comp hrestrict
  · intro f
    exact hemb.leftInverse_invFun f

end EinsteinRelation.Probability
