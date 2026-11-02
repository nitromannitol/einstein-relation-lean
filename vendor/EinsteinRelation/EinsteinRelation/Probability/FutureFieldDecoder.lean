import EinsteinRelation.Environment.Basic
import EinsteinRelation.Probability.ContinuousFieldDecoder
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.UniformSpace.CompactConvergence
open MeasureTheory

namespace EinsteinRelation.Probability

/-- Measurable decoder for the joint matrix/scalar field on the actual closed future halfspace
`{x | -2R ≤ x i}`, with the coordinate `i` in the role of `e₁` (`paper/main.tex:331–340,
377–403, 479–483`). The halfspace is closed in `Vec d`, hence locally compact and σ-compact, so
its continuous maps into `Mat d × ℝ` (compact-open topology) form a Polish space. The countable
evaluation decoder `exists_measurable_continuousMap_decoder` then applies. No hypothesis beyond
the statement is used, and `R` is arbitrary. -/
theorem exists_future_halfSpace_decoder {d : ℕ} (i : Fin d) (R : ℝ) :
    ∃ D : ({x : Vec d // -2 * R ≤ x i} → Mat d × ℝ) →
        C({x : Vec d // -2 * R ≤ x i}, Mat d × ℝ),
      @Measurable ({x : Vec d // -2 * R ≤ x i} → Mat d × ℝ)
        C({x : Vec d // -2 * R ≤ x i}, Mat d × ℝ) inferInstance
        (borel C({x : Vec d // -2 * R ≤ x i}, Mat d × ℝ)) D ∧
      ∀ f : C({x : Vec d // -2 * R ≤ x i}, Mat d × ℝ), D (fun x => f x) = f := by
  -- The actual halfspace is closed, by continuity of the coordinate `x ↦ x i`.
  have hclosed : IsClosed {x : Vec d | -2 * R ≤ x i} :=
    isClosed_le continuous_const (continuous_apply i)
  -- Instances on the subtype are stated in the predicate form used by the statement.
  haveI : LocallyCompactSpace {x : Vec d // -2 * R ≤ x i} :=
    hclosed.locallyCompactSpace
  haveI : SigmaCompactSpace {x : Vec d // -2 * R ≤ x i} :=
    hclosed.sigmaCompactSpace
  haveI : SecondCountableTopology {x : Vec d // -2 * R ≤ x i} :=
    inferInstanceAs (SecondCountableTopology (Set.Elem {x : Vec d | -2 * R ≤ x i}))
  -- The codomain `Mat d × ℝ` is Polish through its finite coordinate product.
  haveI : SecondCountableTopology (Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  haveI : PolishSpace (Mat d × ℝ) :=
    inferInstanceAs (PolishSpace ((Fin d → Fin d → ℝ) × ℝ))
  haveI : BorelSpace (Mat d × ℝ) := inferInstance
  haveI : Nonempty (Mat d × ℝ) := ⟨(0, 0)⟩
  -- Continuous maps on the locally compact, σ-compact halfspace are Polish. The uniform
  -- structure of `Mat d × ℝ` is local to this proof, as in `restrictionFunctionSpace_polish`.
  haveI : PolishSpace C({x : Vec d // -2 * R ≤ x i}, Mat d × ℝ) := by
    letI : UniformSpace (Mat d × ℝ) :=
      inferInstanceAs (UniformSpace ((Fin d → Fin d → ℝ) × ℝ))
    letI : CompleteSpace (Mat d × ℝ) :=
      inferInstanceAs (CompleteSpace ((Fin d → Fin d → ℝ) × ℝ))
    letI : Filter.IsCountablyGenerated (uniformity (Mat d × ℝ)) :=
      inferInstanceAs (Filter.IsCountablyGenerated (uniformity ((Fin d → Fin d → ℝ) × ℝ)))
    haveI : CompleteSpace C({x : Vec d // -2 * R ≤ x i}, Mat d × ℝ) := inferInstance
    haveI : Filter.IsCountablyGenerated
        (uniformity C({x : Vec d // -2 * R ≤ x i}, Mat d × ℝ)) := inferInstance
    haveI : SecondCountableTopology C({x : Vec d // -2 * R ≤ x i}, Mat d × ℝ) := inferInstance
    infer_instance
  exact exists_measurable_continuousMap_decoder

end EinsteinRelation.Probability
