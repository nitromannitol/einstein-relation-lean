import EinsteinFull.Calculus.CLPeriodDichotomy

/-!
# Recovering the displacement from the environment

On an aperiodic environment the translation action is free, so the pair `(ω, translate x ω)`
determines `x`. By the Lusin–Souslin theorem the inverse is Borel; it is extended by `0` off
the pairs of this form.
-/

open MeasureTheory

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ}

/-- Environments without a nonzero period. -/
def aperiodicSet (d : ℕ) : Set (FieldPair d) := {ω | ∀ x, translate x ω = ω → x = 0}

theorem translate_mem_aperiodicSet_iff (y : Vec d) (ω : FieldPair d) :
    translate y ω ∈ aperiodicSet d ↔ ω ∈ aperiodicSet d := by
  simp only [aperiodicSet, Set.mem_ofPred_eq, translate_translate_eq_self_iff]

theorem measurableSet_aperiodicSet (d : ℕ) : MeasurableSet (aperiodicSet d) := by
  let ball : (Fin d → ℚ) × ℚ → Set (Vec d) := fun b =>
    Metric.closedBall (fun j => (b.1 j : ℝ)) (b.2 : ℝ)
  have hcompl : (aperiodicSet d)ᶜ =
      ⋃ b : {b : (Fin d → ℚ) × ℚ // (0 : Vec d) ∉ ball b}, periodHit (ball b.1) := by
    ext ω
    simp only [Set.mem_compl_iff, aperiodicSet, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      push Not at h
      obtain ⟨x, hx, hx0⟩ := h
      obtain ⟨b, -, hxb, hsub⟩ := exists_ratClosedBall x (norm_pos_iff.2 hx0)
      refine ⟨⟨b, fun h0 => ?_⟩, x, hxb, hx⟩
      have := hsub h0
      rw [Metric.mem_ball, dist_comm, dist_zero_right] at this
      exact lt_irrefl _ this
    · rintro ⟨⟨b, hb⟩, x, hxb, hx⟩ h
      exact hb (h x hx ▸ hxb)
  rw [← compl_compl (aperiodicSet d), hcompl]
  exact (MeasurableSet.iUnion fun b =>
    (isClosed_periodHit (isCompact_closedBall _ _)).measurableSet).compl

/-- The pair formed by an aperiodic environment and its translate. -/
def displacementPair (q : Vec d × aperiodicSet d) : FieldPair d × FieldPair d :=
  ((q.2 : FieldPair d), translate q.1 q.2)

theorem displacementPair_injective : Function.Injective (displacementPair (d := d)) := by
  rintro ⟨x, ω, hω⟩ ⟨x', ω', hω'⟩ h
  simp only [displacementPair, Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  have hper : translate (x - x') ω = ω := by
    have := congrArg (translate (-x')) h2
    rw [translate_add, translate_add, neg_add_cancel, translate_zero,
      show -x' + x = x - x' by abel] at this
    exact this
  have hx := sub_eq_zero.1 (hω (x - x') hper)
  subst hx
  rfl

theorem measurable_displacementPair : Measurable (displacementPair (d := d)) :=
  (measurable_subtype_coe.comp measurable_snd).prodMk
    (Localization.physicalTranslation_jointlyMeasurable.comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)))

theorem measurableEmbedding_displacementPair :
    MeasurableEmbedding (displacementPair (d := d)) := by
  let : PolishSpace (FieldPair d) := fieldPair_polish d
  have : StandardBorelSpace (FieldPair d) := inferInstance
  have : StandardBorelSpace (aperiodicSet d) := (measurableSet_aperiodicSet d).standardBorel
  have : MeasurableSpace.CountablySeparated (FieldPair d × FieldPair d) := inferInstance
  exact measurable_displacementPair.measurableEmbedding displacementPair_injective

/-- The displacement between two environments: the unique `x` with `translate x ω = ω'` when `ω`
is aperiodic and `ω'` is a translate of it, and `0` otherwise. -/
def displacementInv (p : FieldPair d × FieldPair d) : Vec d :=
  Function.extend displacementPair (fun q : Vec d × aperiodicSet d => q.1) (fun _ => 0) p

theorem measurable_displacementInv : Measurable (displacementInv (d := d)) :=
  measurableEmbedding_displacementPair.measurable_extend measurable_fst measurable_const

theorem displacementInv_translate {ω : FieldPair d} (hω : ω ∈ aperiodicSet d) (x : Vec d) :
    displacementInv (ω, translate x ω) = x :=
  displacementPair_injective.extend_apply (fun q : Vec d × aperiodicSet d => q.1)
    (fun _ => (0 : Vec d)) (x, ⟨ω, hω⟩)

/-- The displacement between two translates of an aperiodic environment. -/
theorem displacementInv_translate_translate {ω : FieldPair d} (hω : ω ∈ aperiodicSet d)
    (a b : Vec d) : displacementInv (translate a ω, translate b ω) = b - a := by
  have ha : translate a ω ∈ aperiodicSet d := (translate_mem_aperiodicSet_iff a ω).2 hω
  have hb : translate b ω = translate (b - a) (translate a ω) := by
    rw [translate_add, sub_add_cancel]
  rw [hb, displacementInv_translate ha]

end EinsteinFull
