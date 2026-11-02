import EinsteinFull.Calculus.S4CountableSolvesSupport
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# The martingale-problem relation is a measurable set of (parameter, measure) pairs

For a parameter space `Θ` and coefficients `A θ`, `B θ` that are bounded and jointly measurable
in `(θ, y)`, the set of pairs `(θ, P)` with `P` a solution of the martingale problem of
`svGenerator (A θ) (B θ)` from `x` is a measurable subset of `Θ × Measure (Path d)` (Giry).
-/

open MeasureTheory ProbabilityTheory Topology Filter
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

theorem measurable_compensated_joint {Θ : Type*} [MeasurableSpace Θ] {d : ℕ}
    (A : Θ → Vec d → Mat d) (B : Θ → Vec d → Vec d)
    (hAm : ∀ i j, Measurable fun p : Θ × Vec d => A p.1 p.2 i j)
    (hBm : ∀ k, Measurable fun p : Θ × Vec d => B p.1 p.2 k) {u : Vec d → ℝ}
    (hu : Continuous u) (t : ℝ≥0) :
    Measurable fun p : Θ × Path d =>
      compensatedTest (External.Draft.svGenerator (A p.1) (B p.1)) u t p.2 := by
  have heval : Measurable fun w : Path d × ℝ≥0 => w.1 w.2 :=
    (ContinuousEval.continuous_eval (F := Path d) (X := ℝ≥0) (Y := Vec d)).measurable
  have hy : Measurable fun z : (Θ × Path d) × ℝ => z.1.2 z.2.toNNReal :=
    heval.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_real_toNNReal.comp measurable_snd))
  have hG : Measurable fun z : (Θ × Path d) × ℝ =>
      External.Draft.svGenerator (A z.1.1) (B z.1.1) u (z.1.2 z.2.toNNReal) := by
    unfold External.Draft.svGenerator
    refine Measurable.add ?_ ?_
    · refine measurable_const.mul ?_
      refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
      exact ((hAm i j).comp ((measurable_fst.comp measurable_fst).prodMk hy)).mul
        ((measurable_fderiv_apply_const ℝ (fun y => fderiv ℝ u y (unitVector j))
          (unitVector i)).comp hy)
    · refine Finset.measurable_sum _ fun i _ => ?_
      exact ((hBm i).comp ((measurable_fst.comp measurable_fst).prodMk hy)).mul
        ((measurable_fderiv_apply_const ℝ u (unitVector i)).comp hy)
  have hint : Measurable fun p : Θ × Path d =>
      ∫ s in (0 : ℝ)..t, External.Draft.svGenerator (A p.1) (B p.1) u (p.2 s.toNNReal) := by
    have e : (fun p : Θ × Path d =>
        ∫ s in (0 : ℝ)..t, External.Draft.svGenerator (A p.1) (B p.1) u (p.2 s.toNNReal)) =
        fun p : Θ × Path d => ∫ s, External.Draft.svGenerator (A p.1) (B p.1) u
          (p.2 s.toNNReal) ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
      funext p
      rw [intervalIntegral.integral_of_le t.coe_nonneg]
    rw [e]
    exact (hG.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Ioc (0 : ℝ) t))).measurable
  unfold compensatedTest
  have h1 : Measurable fun p : Θ × Path d => u (p.2 t) :=
    hu.measurable.comp ((measurable_pathPosition t).comp measurable_snd)
  have h0 : Measurable fun p : Θ × Path d => u (p.2 0) :=
    hu.measurable.comp ((measurable_pathPosition 0).comp measurable_snd)
  exact (h1.sub h0).sub hint

/-- The Markov kernel `(θ, P) ↦ P` on probability measures. -/
noncomputable def probKernel (Θ : Type*) (Ω : Type*) [MeasurableSpace Θ] [MeasurableSpace Ω] :
    Kernel (Θ × ProbabilityMeasure Ω) Ω where
  toFun q := (q.2 : Measure Ω)
  measurable' := measurable_subtype_coe.comp measurable_snd

instance (Θ Ω : Type*) [MeasurableSpace Θ] [MeasurableSpace Ω] :
    IsMarkovKernel (probKernel Θ Ω) := ⟨fun q => q.2.2⟩

theorem measurable_setIntegral_param {Θ : Type*} [MeasurableSpace Θ] {Ω : Type*}
    [MeasurableSpace Ω] (H : Θ × Ω → ℝ) (hH : Measurable H) {B : Set Ω} (hB : MeasurableSet B) :
    Measurable fun q : Θ × ProbabilityMeasure Ω => ∫ ω in B, H (q.1, ω) ∂(q.2 : Measure Ω) := by
  have e : (fun q : Θ × ProbabilityMeasure Ω => ∫ ω in B, H (q.1, ω) ∂(q.2 : Measure Ω)) =
      fun q => ∫ ω, B.indicator (fun ω => H (q.1, ω)) ω ∂(probKernel Θ Ω q) := by
    funext q
    rw [integral_indicator hB]
    rfl
  rw [e]
  have hf : Measurable fun r : (Θ × ProbabilityMeasure Ω) × Ω =>
      B.indicator (fun ω => H (r.1.1, ω)) r.2 := by
    have h2 : Measurable fun r : (Θ × ProbabilityMeasure Ω) × Ω => H (r.1.1, r.2) :=
      hH.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h3 := h2.indicator (measurable_snd hB)
    exact h3
  exact (hf.stronglyMeasurable.integral_kernel_prod_right' (κ := probKernel Θ Ω)).measurable

theorem measurable_Ival {Θ : Type*} [MeasurableSpace Θ] {d : ℕ}
    (A : Θ → Vec d → Mat d) (B : Θ → Vec d → Vec d)
    (hAm : ∀ i j, Measurable fun p : Θ × Vec d => A p.1 p.2 i j)
    (hBm : ∀ k, Measurable fun p : Θ × Vec d => B p.1 p.2 k) {u : Vec d → ℝ}
    (hu : Continuous u) (S T : ℝ≥0) {E : Set (Path d)} (hE : MeasurableSet E) :
    Measurable fun q : Θ × ProbabilityMeasure (Path d) =>
      ∫ γ in E, (compensatedTest (External.Draft.svGenerator (A q.1) (B q.1)) u T γ -
        compensatedTest (External.Draft.svGenerator (A q.1) (B q.1)) u S γ)
        ∂(q.2 : Measure (Path d)) :=
  measurable_setIntegral_param
    (fun r : Θ × Path d =>
      compensatedTest (External.Draft.svGenerator (A r.1) (B r.1)) u T r.2 -
        compensatedTest (External.Draft.svGenerator (A r.1) (B r.1)) u S r.2)
    ((measurable_compensated_joint A B hAm hBm hu T).sub
      (measurable_compensated_joint A B hAm hBm hu S)) hE

theorem measurableSet_solutionRelation {Θ : Type*} [MeasurableSpace Θ] {d : ℕ}
    (A : Θ → Vec d → Mat d) (B : Θ → Vec d → Vec d) {M : ℝ}
    (hAm : ∀ i j, Measurable fun p : Θ × Vec d => A p.1 p.2 i j)
    (hBm : ∀ k, Measurable fun p : Θ × Vec d => B p.1 p.2 k)
    (hAb : ∀ θ y i j, |A θ y i j| ≤ M) (hBb : ∀ θ y k, |B θ y k| ≤ M) (x : Vec d) :
    MeasurableSet {p : Θ × Measure (Path d) |
      SolvesMartingaleProblem (External.Draft.svGenerator (A p.1) (B p.1)) x p.2} := by
  have hbdd : ∀ θ, BddCoef (A θ) (B θ) M := fun θ =>
    ⟨fun i j => (hAm i j).comp (measurable_const.prodMk measurable_id),
      fun k => (hBm k).comp (measurable_const.prodMk measurable_id), hAb θ, hBb θ⟩
  have hset : {p : Θ × Measure (Path d) |
      SolvesMartingaleProblem (External.Draft.svGenerator (A p.1) (B p.1)) x p.2} =
      {p : Θ × Measure (Path d) |
        CountableCond (External.Draft.svGenerator (A p.1) (B p.1)) x p.2} :=
    Set.ext fun p => ⟨countableCond_of_solves, solves_of_countableCond (hbdd p.1)⟩
  rw [hset]
  let ι : Θ × ProbabilityMeasure (Path d) → Θ × Measure (Path d) :=
    Prod.map id Subtype.val
  have hι : MeasurableEmbedding ι :=
    MeasurableEmbedding.id.prodMap
      (MeasurableEmbedding.subtype_coe ProbabilityMeasure.measurableSet_isProbabilityMeasure)
  let RelP : Set (Θ × ProbabilityMeasure (Path d)) := {q |
    (∀ᵐ γ ∂(q.2 : Measure (Path d)), γ 0 = x) ∧
      ∀ u ∈ tfam d, ∀ S T : MarkovProcess.DenseTime, S ≤ T → ∀ E ∈ cylSys d S,
        ∫ γ in E, (compensatedTest (External.Draft.svGenerator (A q.1) (B q.1)) u
          (MarkovProcess.DenseTime.castOrderEmbedding T) γ -
          compensatedTest (External.Draft.svGenerator (A q.1) (B q.1)) u
            (MarkovProcess.DenseTime.castOrderEmbedding S) γ) ∂(q.2 : Measure (Path d)) = 0}
  have himg : {p : Θ × Measure (Path d) |
      CountableCond (External.Draft.svGenerator (A p.1) (B p.1)) x p.2} = ι '' RelP := by
    ext p
    constructor
    · rintro ⟨hprob, hst, hcond⟩
      exact ⟨(p.1, ⟨p.2, hprob⟩), ⟨hst, hcond⟩, rfl⟩
    · rintro ⟨q, ⟨hst, hcond⟩, rfl⟩
      exact ⟨q.2.2, hst, hcond⟩
  rw [himg, hι.measurableSet_image]
  have hstartm : MeasurableSet {q : Θ × ProbabilityMeasure (Path d) |
      ∀ᵐ γ ∂(q.2 : Measure (Path d)), γ 0 = x} := by
    have hs : MeasurableSet {γ : Path d | ¬ γ 0 = x} :=
      (measurable_pathPosition 0 (measurableSet_singleton x)).compl
    have e : {q : Θ × ProbabilityMeasure (Path d) | ∀ᵐ γ ∂(q.2 : Measure (Path d)), γ 0 = x} =
        {q | (q.2 : Measure (Path d)) {γ | ¬ γ 0 = x} = 0} := by
      ext q
      exact ae_iff
    rw [e]
    exact ((Measure.measurable_coe hs).comp (measurable_subtype_coe.comp measurable_snd))
      (measurableSet_singleton 0)
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
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
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

end EinsteinFull
