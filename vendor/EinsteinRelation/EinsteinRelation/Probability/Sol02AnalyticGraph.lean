import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Measurable functions with analytic graphs

Source: `paper/main.tex:777–782,840`. This supplies the descriptive-set
step for choosing a unique continuous heat kernel. Analyticity of the
graph remains a separate hypothesis; uniqueness alone is insufficient.
-/

open MeasureTheory Set

namespace EinsteinRelation.Probability

/-- A measurable target set has analytic preimage under a function with
analytic graph. Source: `paper/main.tex:777–782,840`. -/
theorem sol02_analytic_preimage_of_analytic_graph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hgraph : AnalyticSet {p : X × Y | f p.1 = p.2})
    {s : Set Y} (hs : MeasurableSet s) : AnalyticSet (f ⁻¹' s) := by
  obtain ⟨W, tW, hW, g, hg, hgrange⟩ :=
    analyticSet_iff_exists_polishSpace_range.mp hgraph
  letI : MeasurableSpace W := borel W
  letI : BorelSpace W := ⟨rfl⟩
  have ht : MeasurableSet ((fun w => (g w).2) ⁻¹' s) := by
    exact hg.snd.measurable hs
  have ha : AnalyticSet ((fun w => (g w).1) ''
      ((fun w => (g w).2) ⁻¹' s)) := by
    exact ht.analyticSet.image_of_continuous hg.fst
  convert ha using 1
  ext x
  constructor
  · intro hx
    have hm : (x, f x) ∈ Set.range g := by rw [hgrange]; rfl
    obtain ⟨w, hw⟩ := hm
    change f x ∈ s at hx
    exact ⟨w, by change (g w).2 ∈ s; rw [hw]; exact hx, congrArg Prod.fst hw⟩
  · rintro ⟨w, hw, hx⟩
    have hm : f (g w).1 = (g w).2 := by
      have : g w ∈ Set.range g := ⟨w, rfl⟩
      rwa [hgrange] at this
    change f x ∈ s
    rw [← hx, hm]
    exact hw

/-- A total function between Polish spaces is measurable if its graph is
analytic. Suslin separation is already proved in Mathlib.
Source: `paper/main.tex:777–782,840`. -/
theorem sol02_measurable_of_analytic_graph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X] [PolishSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hgraph : AnalyticSet {p : X × Y | f p.1 = p.2}) :
    Measurable f := by
  intro s hs
  apply AnalyticSet.measurableSet_of_compl
  · exact sol02_analytic_preimage_of_analytic_graph hgraph hs
  · exact sol02_analytic_preimage_of_analytic_graph hgraph hs.compl

/-- An analytic relation with exactly one point in every section has a
measurable selector satisfying that relation everywhere.
Source: `paper/main.tex:777–782,840`. -/
theorem sol02_exists_measurable_of_analytic_unique
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X] [PolishSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (R : X → Y → Prop) (hR : AnalyticSet {p : X × Y | R p.1 p.2})
    (hunique : ∀ x, ∃! y, R x y) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, R x (f x) := by
  classical
  choose f hf using fun x => (hunique x).exists
  refine ⟨f, sol02_measurable_of_analytic_graph ?_, hf⟩
  convert hR using 1
  ext p
  change (f p.1 = p.2) ↔ R p.1 p.2
  exact ⟨fun h => h ▸ hf p.1,
    fun h => ExistsUnique.unique (hunique p.1) (hf p.1) h⟩

end EinsteinRelation.Probability
