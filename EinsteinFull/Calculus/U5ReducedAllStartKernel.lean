import EinsteinFull.Calculus.C16FoundationInstantiation

open MeasureTheory ProbabilityTheory Topology Filter
open scoped NNReal Classical

namespace EinsteinFull
open EinsteinRelation

theorem u5_measurableSet_solutionRelation_start {Θ : Type*} [MeasurableSpace Θ] {d : ℕ}
    (A : Θ → Vec d → Mat d) (B : Θ → Vec d → Vec d) {M : ℝ}
    (hAm : ∀ i j, Measurable fun p : Θ × Vec d => A p.1 p.2 i j)
    (hBm : ∀ k, Measurable fun p : Θ × Vec d => B p.1 p.2 k)
    (hAb : ∀ θ y i j, |A θ y i j| ≤ M) (hBb : ∀ θ y k, |B θ y k| ≤ M) (x : Θ → Vec d) (hx : Measurable x) :
    MeasurableSet {p : Θ × Measure (Path d) |
      SolvesMartingaleProblem (External.Draft.svGenerator (A p.1) (B p.1)) (x p.1) p.2} := by
  have hbdd : ∀ θ, BddCoef (A θ) (B θ) M := fun θ =>
    ⟨fun i j => (hAm i j).comp (measurable_const.prodMk measurable_id),
      fun k => (hBm k).comp (measurable_const.prodMk measurable_id), hAb θ, hBb θ⟩
  have hset : {p : Θ × Measure (Path d) |
      SolvesMartingaleProblem (External.Draft.svGenerator (A p.1) (B p.1)) (x p.1) p.2} =
      {p : Θ × Measure (Path d) |
        CountableCond (External.Draft.svGenerator (A p.1) (B p.1)) (x p.1) p.2} :=
    Set.ext fun p => ⟨countableCond_of_solves, solves_of_countableCond (hbdd p.1)⟩
  rw [hset]
  let ι : Θ × ProbabilityMeasure (Path d) → Θ × Measure (Path d) :=
    Prod.map id Subtype.val
  have hι : MeasurableEmbedding ι :=
    MeasurableEmbedding.id.prodMap
      (MeasurableEmbedding.subtype_coe ProbabilityMeasure.measurableSet_isProbabilityMeasure)
  let RelP : Set (Θ × ProbabilityMeasure (Path d)) := {q |
    (∀ᵐ γ ∂(q.2 : Measure (Path d)), γ 0 = x q.1) ∧
      ∀ u ∈ tfam d, ∀ S T : MarkovProcess.DenseTime, S ≤ T → ∀ E ∈ cylSys d S,
        ∫ γ in E, (compensatedTest (External.Draft.svGenerator (A q.1) (B q.1)) u
          (MarkovProcess.DenseTime.castOrderEmbedding T) γ -
          compensatedTest (External.Draft.svGenerator (A q.1) (B q.1)) u
            (MarkovProcess.DenseTime.castOrderEmbedding S) γ) ∂(q.2 : Measure (Path d)) = 0}
  have himg : {p : Θ × Measure (Path d) |
      CountableCond (External.Draft.svGenerator (A p.1) (B p.1)) (x p.1) p.2} = ι '' RelP := by
    ext p
    constructor
    · rintro ⟨hprob, hst, hcond⟩
      exact ⟨(p.1, ⟨p.2, hprob⟩), ⟨hst, hcond⟩, rfl⟩
    · rintro ⟨q, ⟨hst, hcond⟩, rfl⟩
      exact ⟨q.2.2, hst, hcond⟩
  rw [himg, hι.measurableSet_image]
  have hstartm : MeasurableSet {q : Θ × ProbabilityMeasure (Path d) |
      ∀ᵐ γ ∂(q.2 : Measure (Path d)), γ 0 = x q.1} := by
    have hs : MeasurableSet {z : (Θ × ProbabilityMeasure (Path d)) × Path d |
        z.2 0 = x z.1.1} := measurableSet_eq_fun
          ((measurable_pathPosition 0).comp measurable_snd)
          (hx.comp (measurable_fst.comp measurable_fst))
    have e : {q : Θ × ProbabilityMeasure (Path d) |
        ∀ᵐ γ ∂(q.2 : Measure (Path d)), γ 0 = x q.1} =
        {q | probKernel Θ (Path d) q {γ | ¬ γ 0 = x q.1} = 0} := by
      ext q
      exact ae_iff
    rw [e]
    exact measurableSet_eq_fun
      (Kernel.measurable_kernel_prodMk_left (κ := probKernel Θ (Path d)) hs.compl)
      measurable_const
  have e : {q : Θ × ProbabilityMeasure (Path d) | ∀ u ∈ tfam d, ∀ S T : MarkovProcess.DenseTime,
      S ≤ T → ∀ E ∈ cylSys d S,
        ∫ γ in E, (compensatedTest (External.Draft.svGenerator (A q.1) (B q.1)) u
          (MarkovProcess.DenseTime.castOrderEmbedding T) γ -
          compensatedTest (External.Draft.svGenerator (A q.1) (B q.1)) u
            (MarkovProcess.DenseTime.castOrderEmbedding S) γ) ∂(q.2 : Measure (Path d)) = 0} =
      ⋂ u ∈ tfam d, ⋂ S : MarkovProcess.DenseTime, ⋂ T : MarkovProcess.DenseTime,
        ⋂ (_ : S ≤ T), ⋂ E ∈ cylSys d S,
          {q : Θ × ProbabilityMeasure (Path d) |
            ∫ γ in E, (compensatedTest (External.Draft.svGenerator (A q.1) (B q.1)) u
              (MarkovProcess.DenseTime.castOrderEmbedding T) γ -
              compensatedTest (External.Draft.svGenerator (A q.1) (B q.1)) u
                (MarkovProcess.DenseTime.castOrderEmbedding S) γ)
              ∂(q.2 : Measure (Path d)) = 0} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  have hQ : MeasurableSet {q : Θ × ProbabilityMeasure (Path d) |
      ∀ u ∈ tfam d, ∀ S T : MarkovProcess.DenseTime, S ≤ T → ∀ E ∈ cylSys d S,
        ∫ γ in E, (compensatedTest (External.Draft.svGenerator (A q.1) (B q.1)) u
          (MarkovProcess.DenseTime.castOrderEmbedding T) γ -
          compensatedTest (External.Draft.svGenerator (A q.1) (B q.1)) u
            (MarkovProcess.DenseTime.castOrderEmbedding S) γ) ∂(q.2 : Measure (Path d)) = 0} := by
    rw [e]
    refine MeasurableSet.biInter (tfam_countable d) fun u hu => ?_
    refine MeasurableSet.iInter fun S => MeasurableSet.iInter fun T => MeasurableSet.iInter
      fun _ => MeasurableSet.biInter (cylSys_countable d S) fun E hE => ?_
    have hEm : MeasurableSet E := by
      have : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)
          (MarkovProcess.DenseTime.castOrderEmbedding S)] E := by
        rw [← cylSys_gen d S]
        exact MeasurableSpace.measurableSet_generateFrom hE
      exact (canonF d).le _ E this
    exact (measurable_Ival A B hAm hBm (tfam_test d u hu).1.continuous _ _ hEm)
      (measurableSet_singleton 0)
  exact hstartm.inter hQ


/-- A jointly measurable family of textbook reduced solutions at every start. -/
theorem u5_reduced_textbook_kernel_all_starts
    {d : ℕ} (hd : 1 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    (i : Fin d) (lam : ℝ) :
    ∃ K : ProbabilityTheory.Kernel (FieldPair d × Vec d) (Path d),
      ProbabilityTheory.IsMarkovKernel K ∧
      ∀ ω : FieldPair d, IsRegular Λ ω → ∀ x : Vec d,
        SolvesMartingaleProblem
          (External.Draft.svGenerator (reducedCoefficient ω)
            (forcedDrift (reducedCoefficient ω) i lam)) x (K (ω, x)) := by
  let : PolishSpace (FieldPair d) := fieldPair_polish d
  let A : (FieldPair d × Vec d) → Vec d → Mat d := fun p => famA Λ p.1
  let B : (FieldPair d × Vec d) → Vec d → Vec d := fun p => famB Λ i lam p.1
  obtain ⟨M, hAb, hBb⟩ := family_bounds hΛ i lam
  have hAm : ∀ a b, Measurable fun p : (FieldPair d × Vec d) × Vec d =>
      A p.1 p.2 a b := fun a b => (measurable_famA Λ a b).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hBm : ∀ k, Measurable fun p : (FieldPair d × Vec d) × Vec d =>
      B p.1 p.2 k := fun k => (measurable_famB Λ i lam k).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hR := u5_measurableSet_solutionRelation_start A B hAm hBm
    (fun θ y a b => hAb θ.1 y a b) (fun θ y k => hBb θ.1 y k)
    Prod.snd measurable_snd
  have huniq : ∀ p : FieldPair d × Vec d, ∃! P : Measure (Path d),
      SolvesMartingaleProblem (External.Draft.svGenerator (A p) (B p)) p.2 P := by
    intro ⟨ω, x⟩
    by_cases hreg : IsRegular Λ ω
    · change ∃! P : Measure (Path d), SolvesMartingaleProblem
        (External.Draft.svGenerator (famA Λ ω) (famB Λ i lam ω)) x P
      rw [famA_eq_of_regular hreg, famB_eq_of_regular i lam hreg]
      exact foundation_reduced_textbook_well_posed hd hΛ hreg i lam x
    · have e1 : famA Λ ω = fun _ => 1 := funext fun y => by
        unfold famA
        rw [ite_eq_right hreg]
      have e2 : famB Λ i lam ω = fun _ => 0 := funext fun y => by
        unfold famB
        rw [ite_eq_right hreg]
      change ∃! P : Measure (Path d), SolvesMartingaleProblem
        (External.Draft.svGenerator (famA Λ ω) (famB Λ i lam ω)) x P
      rw [e1, e2]
      refine foundation_textbook_well_posed d hd (fun _ => 1) (fun _ => 0)
        continuous_const (fun _ => Matrix.transpose_one) ⟨1, fun _ a b => ?_⟩
        ⟨1, one_pos, fun y ξ => ?_⟩ measurable_const ⟨0, fun _ k => by simp⟩ x
      · rcases eq_or_ne a b with rfl | hab
        · simp
        · simp [hab]
      · simp [euclideanSq, Matrix.one_mulVec]
  obtain ⟨g, hg, hgs⟩ := exists_measurable_selector_measure
    (fun p P => SolvesMartingaleProblem (External.Draft.svGenerator (A p) (B p)) p.2 P)
    (fun _ _ h => h.1) huniq hR
  let K : Kernel (FieldPair d × Vec d) (Path d) := ⟨g, hg⟩
  refine ⟨K, ⟨fun p => (hgs p).1⟩, ?_⟩
  intro ω hω x
  have h := hgs (ω, x)
  change SolvesMartingaleProblem
    (External.Draft.svGenerator (famA Λ ω) (famB Λ i lam ω)) x (K (ω, x)) at h
  rw [famA_eq_of_regular hω, famB_eq_of_regular i lam hω] at h
  exact h

end EinsteinFull
