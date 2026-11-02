import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.UnitInterval
import EinsteinRelation.Probability.Sol02AnalyticGraph

/-!
# Measurable selection of measure-valued maps with a Borel relation

If `R θ P` is a (Giry-)measurable relation between a Polish parameter space and probability
measures on a standard Borel space, and every `θ` has exactly one `P` with `R θ P`, then
`θ ↦ P_θ` is Giry-measurable.

The proof codes measures on `Ω` through a measurable embedding `Ω → [0,1]` into the Polish
space `ProbabilityMeasure [0,1]` (compact metrizable) and applies the analytic-graph theorem.
Only the inclusion `Giry ≤ Borel(weak)` on `ProbabilityMeasure [0,1]` is needed
(`measurable_toProb`).
-/

open MeasureTheory Topology Filter

namespace EinsteinFull

/-- `ProbabilityMeasure [0,1]` with the Borel σ-algebra of the weak topology. -/
def UIProbT : Type := ProbabilityMeasure unitInterval

namespace UIProbT

noncomputable instance : TopologicalSpace UIProbT :=
  inferInstanceAs (TopologicalSpace (ProbabilityMeasure unitInterval))

noncomputable instance : MeasurableSpace UIProbT := borel UIProbT

instance : BorelSpace UIProbT := ⟨rfl⟩

instance : CompactSpace UIProbT :=
  inferInstanceAs (CompactSpace (ProbabilityMeasure unitInterval))

instance : TopologicalSpace.MetrizableSpace UIProbT :=
  inferInstanceAs (TopologicalSpace.MetrizableSpace (ProbabilityMeasure unitInterval))

instance : PolishSpace UIProbT := by
  letI : MetricSpace UIProbT := TopologicalSpace.metrizableSpaceMetric UIProbT
  infer_instance

/-- The underlying probability measure. -/
def toProb (Q : UIProbT) : ProbabilityMeasure unitInterval := Q

theorem ext {Q Q' : UIProbT} (h : (Q.toProb : Measure unitInterval) = Q'.toProb) : Q = Q' :=
  Subtype.ext h

theorem lowerSemicontinuous_measure_open {G : Set unitInterval} (hG : IsOpen G) :
    LowerSemicontinuous fun Q : UIProbT => (Q.toProb : Measure unitInterval) G := by
  intro Q y hy
  have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto (L := 𝓝 Q)
    (μ := Q.toProb) (μs := fun Q' : UIProbT => Q'.toProb) tendsto_id hG
  exact Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le hy h)

/-- The Borel σ-algebra of the weak topology is finer than the Giry σ-algebra. -/
theorem measurable_toProb : Measurable UIProbT.toProb := by
  have h : Measurable fun Q : UIProbT => (Q.toProb : Measure unitInterval) := by
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (S := {s : Set unitInterval | IsOpen s}) ?_ isPiSystem_isOpen ?_
    · exact BorelSpace.measurable_eq
    · intro s hs
      exact (lowerSemicontinuous_measure_open hs).measurable
  exact Measurable.subtype_mk (h := fun Q => Q.toProb.2) h

end UIProbT

theorem exists_measurableEmbedding_unitInterval (Ω : Type*) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] : ∃ e : Ω → unitInterval, MeasurableEmbedding e := by
  obtain ⟨f, hf⟩ := exists_measurableEmbedding_real Ω
  have hmem : ∀ x : ℝ, (Real.arctan x + Real.pi / 2) / Real.pi ∈ unitInterval := by
    intro x
    have h1 := Real.neg_pi_div_two_lt_arctan x
    have h2 := Real.arctan_lt_pi_div_two x
    refine ⟨div_nonneg (by linarith) Real.pi_pos.le, ?_⟩
    rw [div_le_one Real.pi_pos]
    linarith
  let g : ℝ → unitInterval := fun x => ⟨(Real.arctan x + Real.pi / 2) / Real.pi, hmem x⟩
  have hgc : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    exact (Real.continuous_arctan.add continuous_const).div_const _
  have hgi : Function.Injective g := by
    intro x y hxy
    have h : (Real.arctan x + Real.pi / 2) / Real.pi = (Real.arctan y + Real.pi / 2) / Real.pi :=
      congrArg Subtype.val hxy
    have h' : Real.arctan x = Real.arctan y := by
      have := (div_left_inj' Real.pi_pos.ne').1 h
      linarith
    exact Real.arctan_injective h'
  exact ⟨g ∘ f, (hgc.measurableEmbedding hgi).comp hf⟩

theorem measurable_comap_measure {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {e : Ω → Ω'} (he : MeasurableEmbedding e) :
    Measurable fun μ : Measure Ω' => Measure.comap e μ := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have : (fun μ : Measure Ω' => Measure.comap e μ s) = fun μ => μ (e '' s) :=
    funext fun μ => he.comap_apply μ s
  rw [this]
  exact Measure.measurable_coe (he.measurableSet_image.2 hs)

theorem exists_measurable_selector_measure {Θ Ω : Type*} [TopologicalSpace Θ] [PolishSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (R : Θ → Measure Ω → Prop) (hprob : ∀ θ P, R θ P → IsProbabilityMeasure P)
    (huniq : ∀ θ, ∃! P, R θ P) (hR : MeasurableSet {p : Θ × Measure Ω | R p.1 p.2}) :
    ∃ g : Θ → Measure Ω, Measurable g ∧ ∀ θ, R θ (g θ) := by
  obtain ⟨e, he⟩ := exists_measurableEmbedding_unitInterval Ω
  let Rc : Θ → UIProbT → Prop := fun θ Q =>
    (Q.toProb : Measure unitInterval) (Set.range e) = 1 ∧
      R θ (Measure.comap e (Q.toProb : Measure unitInterval))
  have hcoe : Measurable fun Q : UIProbT => (Q.toProb : Measure unitInterval) :=
    measurable_subtype_coe.comp UIProbT.measurable_toProb
  have hcomap : Measurable fun p : Θ × UIProbT =>
      Measure.comap e (p.2.toProb : Measure unitInterval) :=
    (measurable_comap_measure he).comp (hcoe.comp measurable_snd)
  have hc : Measurable fun p : Θ × UIProbT =>
      (p.1, Measure.comap e (p.2.toProb : Measure unitInterval)) :=
    measurable_fst.prodMk hcomap
  have hRc : MeasurableSet {p : Θ × UIProbT | Rc p.1 p.2} := by
    have h1 : MeasurableSet {p : Θ × UIProbT |
        R p.1 (Measure.comap e (p.2.toProb : Measure unitInterval))} := hR.preimage hc
    have h2 : MeasurableSet {p : Θ × UIProbT |
        (p.2.toProb : Measure unitInterval) (Set.range e) = 1} :=
      ((Measure.measurable_coe he.measurableSet_range).comp (hcoe.comp measurable_snd))
        (measurableSet_singleton 1)
    exact h2.inter h1
  have hu : ∀ θ, ∃! Q, Rc θ Q := by
    intro θ
    obtain ⟨P, hP, hPu⟩ := huniq θ
    haveI := hprob θ P hP
    let Q0 : UIProbT := (⟨Measure.map e P, inferInstance⟩ : ProbabilityMeasure unitInterval)
    have hQ0 : (Q0.toProb : Measure unitInterval) = Measure.map e P := rfl
    have hcm : Measure.comap e (Measure.map e P) = P := he.comap_map P
    refine ⟨Q0, ⟨?_, ?_⟩, fun Q hQ => ?_⟩
    · rw [hQ0, Measure.map_apply he.measurable he.measurableSet_range, Set.preimage_range]
      exact measure_univ
    · rw [hQ0, hcm]
      exact hP
    · obtain ⟨hQ1, hQR⟩ := hQ
      have hPQ := hPu _ hQR
      apply UIProbT.ext
      rw [hQ0, ← hPQ, he.map_comap]
      refine (Measure.restrict_eq_self_of_ae_mem ?_).symm
      have hcompl : (Q.toProb : Measure unitInterval) (Set.range e)ᶜ = 0 := by
        rw [prob_compl_eq_zero_iff he.measurableSet_range]
        exact hQ1
      exact mem_ae_iff.2 hcompl
  obtain ⟨f, hf, hfR⟩ := EinsteinRelation.Probability.sol02_exists_measurable_of_analytic_unique
    Rc hRc.analyticSet hu
  refine ⟨fun θ => Measure.comap e ((f θ).toProb : Measure unitInterval), ?_, fun θ => (hfR θ).2⟩
  exact (measurable_comap_measure he).comp (hcoe.comp hf)

end EinsteinFull
