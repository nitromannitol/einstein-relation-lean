import EinsteinFull.Calculus.SbxS2RegularRealizationUniquenessR01
import EinsteinFull.Calculus.U2RegularKernelCovariance
import EinsteinRelation.Probability.ConjugateCylinderIntegrals
import EinsteinRelation.Regeneration.SpatialRecenterEquiv

open EinsteinRelation EinsteinRelation.SpatialDirichlet MeasureTheory ProbabilityTheory Filter Topology
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull

-- Cylinder identification adapted from U6BoundedPhysicalResolvent.
private theorem continuous_list_getD {α : Type*} [TopologicalSpace α]
    (a₀ : α) (n : ℕ) : Continuous (fun l : List α => l[n]?.getD a₀) := by
  apply continuous_iff_continuousAt.mpr
  intro l
  induction l generalizing n with
  | nil =>
      rw [ContinuousAt, nhds_nil]
      exact tendsto_pure_nhds _ _
  | cons a l ih =>
      rw [ContinuousAt, List.tendsto_cons_iff]
      cases n with
      | zero => simpa only [List.getElem?_cons_zero, Option.getD_some] using tendsto_fst
      | succ n =>
          simpa only [List.getElem?_cons_succ, Function.comp_def] using Filter.Tendsto.comp (ih n) tendsto_snd

private theorem mem_pathEvalCylinder_iff {d : ℕ}
    (c : List (ℝ≥0 × Set (Vec d))) (γ : Path d) :
    γ ∈ pathEvalCylinder c ↔ ∀ p ∈ c, γ p.1 ∈ p.2 := by
  induction c with
  | nil => simp only [pathEvalCylinder, Set.mem_univ, List.not_mem_nil, false_implies,
      implies_true]
  | cons p c ih => simp only [pathEvalCylinder, Set.mem_inter_iff, Set.mem_ofPred_eq,
      List.forall_mem_cons, ih]

private def positionCylinder {d : ℕ} (c : List (ℝ≥0 × Set (Vec d))) :
    Set (List (Vec d)) :=
  {ys | ∀ i : Fin c.length, ys[i.val]?.getD 0 ∈ (c[i.val]).2}

private theorem measurableSet_positionCylinder {d : ℕ}
    (c : List (ℝ≥0 × Set (Vec d))) (hc : ∀ p ∈ c, MeasurableSet p.2) :
    MeasurableSet (positionCylinder c) := by
  unfold positionCylinder
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (hc c[i.val] (List.getElem_mem i.isLt)).preimage
    (continuous_list_getD (0 : Vec d) i.val).measurable

private theorem positionCylinder_preimage {d : ℕ}
    (c : List (ℝ≥0 × Set (Vec d))) :
    (fun γ : Path d => pathPositionsAtTimes (c.map Prod.fst) γ) ⁻¹'
      positionCylinder c = pathEvalCylinder c := by
  ext γ
  rw [mem_pathEvalCylinder_iff]
  simp only [Set.mem_preimage, positionCylinder, Set.mem_ofPred_eq,
    pathPositionsAtTimes, List.map_map, Function.comp_def, pathPosition]
  change (∀ i : Fin c.length,
    (c.map (fun p => γ p.1))[i.val]?.getD 0 ∈ (c[i.val]).2) ↔ _
  have hget (i : Fin c.length) :
      (c.map (fun p => γ p.1))[i.val]?.getD 0 = γ (c[i.val]).1 := by
    rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using i.isLt),
      Option.getD_some, List.getElem_map]
  simp only [hget]
  simpa only [List.get_eq_getElem] using
    (List.forall_mem_iff_get (l := c) (p := fun p => γ p.1 ∈ p.2)).symm

private theorem exists_cumulativeTimesFrom {d : ℕ}
    (c : List (ℝ≥0 × Set (Vec d))) (s : ℝ≥0)
    (hs : ∀ p ∈ c, s ≤ p.1)
    (hc : c.Pairwise (fun p q => p.1 ≤ q.1)) :
    ∃ increments, cumulativeTimesFrom s increments = c.map Prod.fst := by
  induction c generalizing s with
  | nil => exact ⟨[], rfl⟩
  | cons p c ih =>
      obtain ⟨increments, hi⟩ := ih p.1
        (List.pairwise_cons.mp hc).1 (List.pairwise_cons.mp hc).2
      refine ⟨(p.1 - s) :: increments, ?_⟩
      simp only [cumulativeTimesFrom, add_tsub_cancel_of_le (hs p (by simp)),
        List.map_cons, hi]

private theorem cylinder_eq_of_ordered_integral_eq {d : ℕ}
    {P Q : Measure (Path d)} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ (increments : List ℝ≥0) (F : List (Vec d) → ℝ),
      Measurable F → (∃ B : ℝ, ∀ z, |F z| ≤ B) →
        (∫ γ, F (pathPositionsAtTimes (cumulativeTimes increments) γ) ∂P) =
        ∫ γ, F (pathPositionsAtTimes (cumulativeTimes increments) γ) ∂Q)
    (c : List (ℝ≥0 × Set (Vec d))) (hc : ∀ p ∈ c, MeasurableSet p.2) :
    P (pathEvalCylinder c) = Q (pathEvalCylinder c) := by
  classical
  let c' := c.insertionSort (fun p q => p.1 ≤ q.1)
  have hperm : c'.Perm c := List.perm_insertionSort _ _
  have hc' : ∀ p ∈ c', MeasurableSet p.2 := fun p hp => hc p (hperm.mem_iff.mp hp)
  have hsorted : c'.Pairwise (fun p q => p.1 ≤ q.1) := by
    let : @Std.Total (ℝ≥0 × Set (Vec d)) (fun p q => p.1 ≤ q.1) :=
      ⟨fun p q => le_total p.1 q.1⟩
    let : IsTrans (ℝ≥0 × Set (Vec d)) (fun p q => p.1 ≤ q.1) :=
      ⟨fun _ _ _ hp hq => hp.trans hq⟩
    exact List.pairwise_insertionSort _ _
  obtain ⟨increments, hi⟩ := exists_cumulativeTimesFrom c' 0
    (fun p _ => bot_le) hsorted
  have hset : pathEvalCylinder c' = pathEvalCylinder c := by
    ext γ
    rw [mem_pathEvalCylinder_iff, mem_pathEvalCylinder_iff]
    constructor
    · intro h p hp
      exact h p (hperm.mem_iff.mpr hp)
    · intro h p hp
      exact h p (hperm.mem_iff.mp hp)
  let F : List (Vec d) → ℝ := (positionCylinder c').indicator 1
  have hFm : Measurable F := measurable_const.indicator (measurableSet_positionCylinder c' hc')
  have hFb : ∃ B : ℝ, ∀ z, |F z| ≤ B := by
    refine ⟨1, fun z => ?_⟩
    by_cases hz : z ∈ positionCylinder c' <;> simp [F, hz]
  have hpoint (γ : Path d) :
      F (pathPositionsAtTimes (cumulativeTimes increments) γ) =
        (pathEvalCylinder c).indicator (1 : Path d → ℝ) γ := by
    have hp : (fun γ : Path d => pathPositionsAtTimes (cumulativeTimes increments) γ) ⁻¹'
        positionCylinder c' = pathEvalCylinder c := by
      rw [cumulativeTimes, hi, positionCylinder_preimage, hset]
    change (positionCylinder c').indicator (fun _ => (1 : ℝ)) _ = _
    rw [← hp]
    rfl
  have heq := h increments F hFm hFb
  simp only [hpoint, integral_indicator_one (measurable_pathEvalCylinder c hc)] at heq
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top P _) (measure_ne_top Q _)).mp heq


/-- Fixed-environment covariance of the actual regular GMP path laws, simultaneously
for every starting point. -/
theorem s2_regular_realization_path_translation {d : ℕ} (hd : 2 ≤ d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (z : Vec d)
    (hωz : IsRegular Λ (translate z ω))
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (S : GantertFixedEnvironmentRealization hd Λ hΛ (translate z ω) hωz lam h0 h1)
    (hR : R.transitionKernel = fun t => u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t)
    (hS : S.transitionKernel = fun t =>
      u2RegularC0KernelSemigroup hd (translate z ω) lam Λ hΛ hωz t) :
    ∀ x, S.pathLaw x = Measure.map (Regeneration.recenterPathEquiv z) (R.pathLaw (x + z)) := by
  intro x
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft z
  let p := Regeneration.recenterPathEquiv z
  let : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  let : IsMarkovKernel S.pathLaw := S.pathLaw_isMarkovKernel
  let : IsProbabilityMeasure ((R.pathLaw (x + z)).map p) := (Measure.isProbabilityMeasure_map_iff p.measurable.aemeasurable).2 inferInstance
  obtain ⟨hreg, hcov⟩ := u2_regular_signed_kernel_translation_covariance hd ω lam Λ hΛ hω z
  have hK : S.transitionKernel = fun t => ((R.transitionKernel t).comap e e.measurable).map e.symm := by
    funext t
    apply Kernel.ext
    intro y
    rw [hS, Kernel.map_apply _ e.symm.measurable, Kernel.comap_apply, hR]
    simpa [e, MeasurableEquiv.addLeft, sub_eq_add_neg, add_comm] using hcov t y
  apply measure_eq_of_eq_on_pathCylinders
  · apply cylinder_eq_of_ordered_integral_eq
    intro increments F hF hb
    rw [S.pathLaw_ordered_finite_dimensional increments x F hF hb, hK,
      iteratedMarkovCylinderIntegral_conjugate, integral_map_equiv]
    have he : Continuous (e.symm : Vec d → Vec d) := by
      change Continuous (fun x : Vec d => -z + x)
      fun_prop
    have hl : Continuous (fun ys : List (Vec d) => ys.map e.symm) := by
      apply continuous_iff_continuousAt.mpr
      apply List.tendsto_nhds
      · exact tendsto_pure_nhds _ _
      · intro ys y ih
        exact (Filter.Tendsto.comp (he.tendsto y) tendsto_fst).cons
          (Filter.Tendsto.comp ih tendsto_snd)
    have hFm : Measurable (fun ys : List (Vec d) => F (ys.map e.symm)) :=
      hF.comp hl.measurable
    have h := R.pathLaw_ordered_finite_dimensional increments (x + z)
      (fun ys => F (ys.map e.symm)) hFm (by
        obtain ⟨B, hB⟩ := hb
        exact ⟨B, fun ys => hB _⟩)
    have hex : e x = x + z := by simp [e, MeasurableEquiv.addLeft, add_comm]
    rw [hex, ← h]
    apply integral_congr_ae
    filter_upwards with γ
    congr 1
    simp [pathPositionsAtTimes, pathPosition, Regeneration.recenterPathEquiv, e,
      sub_eq_add_neg, add_comm, List.map_map, Function.comp_def]
  · simp only [measure_univ]

#print axioms s2_regular_realization_path_translation
end EinsteinFull
