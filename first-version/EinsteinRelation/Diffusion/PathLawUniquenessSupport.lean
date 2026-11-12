import EinsteinRelation.Diffusion.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Thickening

open Function MeasureTheory Topology

namespace EinsteinRelation

open scoped NNReal

/-- A finite evaluation cylinder on nonnegative-time continuous path space. -/
def pathEvalCylinder {d : ℕ} : List (ℝ≥0 × Set (Vec d)) → Set (Path d)
  | [] => Set.univ
  | (t, A) :: rest => {γ | γ t ∈ A} ∩ pathEvalCylinder rest

theorem pathEvalCylinder_append {d : ℕ} (c c' : List (ℝ≥0 × Set (Vec d))) :
    pathEvalCylinder (c ++ c') = pathEvalCylinder c ∩ pathEvalCylinder c' := by
  induction c with
  | nil => simp [pathEvalCylinder]
  | cons p c ih => cases p with
    | mk t A => simp [pathEvalCylinder, ih, Set.inter_assoc]

/-- Measurable finite evaluation cylinders on path space. -/
def measurablePathCylinders {d : ℕ} : Set (Set (Path d)) :=
  {s | ∃ c : List (ℝ≥0 × Set (Vec d)),
    (∀ p ∈ c, MeasurableSet p.2) ∧ pathEvalCylinder c = s}

theorem measurable_pathEvalCylinder {d : ℕ} (c : List (ℝ≥0 × Set (Vec d)))
    (hA : ∀ p ∈ c, MeasurableSet p.2) : MeasurableSet (pathEvalCylinder c) := by
  induction c with
  | nil => simp [pathEvalCylinder]
  | cons p c ih =>
      rcases p with ⟨t, A⟩
      simp only [pathEvalCylinder]
      have hfirst : MeasurableSet {γ : Path d | γ t ∈ A} :=
        (measurable_pathPosition t) (hA (t, A) (by simp))
      exact hfirst.inter (ih fun q hq => hA q (by simp [hq]))

theorem isPiSystem_measurablePathCylinders {d : ℕ} :
    IsPiSystem (measurablePathCylinders (d := d)) := by
  intro s hs t ht _
  rcases hs with ⟨c, hc, rfl⟩
  rcases ht with ⟨c', hc', rfl⟩
  refine ⟨c ++ c', ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hc p hp
    · exact hc' p hp
  · exact pathEvalCylinder_append c c'

private noncomputable def denseNonnegativeTimes : Set ℝ≥0 :=
  (TopologicalSpace.exists_countable_dense (ℝ≥0)).choose

private theorem countable_denseNonnegativeTimes : denseNonnegativeTimes.Countable :=
  (TopologicalSpace.exists_countable_dense (ℝ≥0)).choose_spec.1

private theorem dense_denseNonnegativeTimes : Dense denseNonnegativeTimes :=
  (TopologicalSpace.exists_countable_dense (ℝ≥0)).choose_spec.2

private noncomputable def pathEvalRadius (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private def ShrunkPathTargetBasis {d : ℕ} {U : Set (Vec d)} :=
  {b : TopologicalSpace.countableBasis (Vec d) // closure (b : Set (Vec d)) ⊆ U}

private def pathTargetOpenCover {d : ℕ} {U : Set (Vec d)}
    (F : Finset (ShrunkPathTargetBasis (d := d) (U := U))) : Set (Vec d) :=
  ⋃ b ∈ F, (b.1 : Set (Vec d))

private def pathTargetClosedCover {d : ℕ} {U : Set (Vec d)}
    (F : Finset (ShrunkPathTargetBasis (d := d) (U := U))) : Set (Vec d) :=
  ⋃ b ∈ F, closure (b.1 : Set (Vec d))

private theorem isOpen_pathTargetOpenCover {d : ℕ} {U : Set (Vec d)}
    (F : Finset (ShrunkPathTargetBasis (d := d) (U := U))) :
    IsOpen (pathTargetOpenCover F) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [pathTargetOpenCover]
  | @insert b F hb ih =>
      simp only [pathTargetOpenCover, Finset.set_biUnion_insert]
      exact (TopologicalSpace.isOpen_of_mem_countableBasis b.1.2).union ih

private theorem isClosed_pathTargetClosedCover {d : ℕ} {U : Set (Vec d)}
    (F : Finset (ShrunkPathTargetBasis (d := d) (U := U))) :
    IsClosed (pathTargetClosedCover F) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [pathTargetClosedCover]
  | @insert b F hb ih =>
      simp only [pathTargetClosedCover, Finset.set_biUnion_insert]
      exact isClosed_closure.union ih

private def pathEvalGenerated (d : ℕ) : MeasurableSpace (Path d) :=
  MeasurableSpace.generateFrom (measurablePathCylinders (d := d))

private theorem measurable_pathEvalSet {d : ℕ} (t : ℝ≥0) (A : Set (Vec d))
    (hA : MeasurableSet A) : @MeasurableSet (Path d) (pathEvalGenerated d)
      {γ | γ t ∈ A} := by
  apply MeasurableSpace.measurableSet_generateFrom
  exact ⟨[(t, A)], by intro p hp; simp at hp; rcases hp with rfl; exact hA, by
    ext γ
    simp [pathEvalCylinder]⟩

private def pathEvalNearCondition {d : ℕ} {U : Set (Vec d)}
    (K : Set (ℝ≥0)) (F : Finset (ShrunkPathTargetBasis (d := d) (U := U))) (n : ℕ) :
    Set (Path d) :=
  {γ | ∀ t : denseNonnegativeTimes,
    (t : ℝ≥0) ∈ Metric.thickening (pathEvalRadius n) K →
      γ t ∈ pathTargetClosedCover F}

private theorem measurable_pathEvalNearCondition {d : ℕ} {U : Set (Vec d)}
    (K : Set (ℝ≥0)) (F : Finset (ShrunkPathTargetBasis (d := d) (U := U))) (n : ℕ) :
    @MeasurableSet (Path d) (pathEvalGenerated d) (pathEvalNearCondition K F n) := by
  classical
  haveI : Countable denseNonnegativeTimes := countable_denseNonnegativeTimes.to_subtype
  have hclosed : MeasurableSet (pathTargetClosedCover F) :=
    (isClosed_pathTargetClosedCover F).measurableSet
  change @MeasurableSet (Path d) (pathEvalGenerated d)
    {γ | ∀ t : denseNonnegativeTimes,
      (t : ℝ≥0) ∈ Metric.thickening (pathEvalRadius n) K →
        γ t ∈ pathTargetClosedCover F}
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun t => by
    by_cases ht : (t : ℝ≥0) ∈ Metric.thickening (pathEvalRadius n) K
    · simpa [ht] using measurable_pathEvalSet t (pathTargetClosedCover F) hclosed
    · simp [ht]

private theorem measurable_pathTargetOpenMapsTo {d : ℕ} (K : Set (ℝ≥0))
    (hK : IsCompact K) (U : Set (Vec d)) (hU : IsOpen U) :
    @MeasurableSet (Path d) (pathEvalGenerated d)
      {γ | Set.MapsTo γ K U} := by
  classical
  let I := ShrunkPathTargetBasis (d := d) (U := U)
  letI : Countable (TopologicalSpace.countableBasis (Vec d)) :=
    (TopologicalSpace.countable_countableBasis (Vec d)).to_subtype
  letI : Countable I := Subtype.val_injective.countable
  letI : Countable (Finset I) := inferInstance
  letI : Countable (Finset I × ℕ) := inferInstance
  have hsub :
      {γ : Path d | Set.MapsTo γ K U} =
        ⋃ p : Finset I × ℕ, pathEvalNearCondition K p.1 p.2 := by
    ext γ
    constructor
    · intro hγ
      have hcover : K ⊆ ⋃ b : I, γ ⁻¹' (b.1 : Set (Vec d)) := by
        intro t ht
        obtain ⟨b, hb, htb, hclosure⟩ :=
          (TopologicalSpace.isBasis_countableBasis (Vec d)).exists_closure_subset
            (hU.mem_nhds (hγ ht))
        exact Set.mem_iUnion.mpr ⟨⟨⟨b, hb⟩, hclosure⟩, by simpa using htb⟩
      obtain ⟨F, hF⟩ := hK.elim_finite_subcover
        (fun b : I => γ ⁻¹' (b.1 : Set (Vec d)))
        (fun b => (TopologicalSpace.isOpen_of_mem_countableBasis b.1.2).preimage γ.continuous)
        hcover
      have hV : IsOpen (pathTargetOpenCover F) := isOpen_pathTargetOpenCover F
      have hKsub : K ⊆ γ ⁻¹' pathTargetOpenCover F := by
        intro t ht
        rcases Set.mem_iUnion₂.mp (hF ht) with ⟨b, hb, hbt⟩
        exact Set.mem_iUnion₂.mpr ⟨b, hb, by simpa using hbt⟩
      obtain ⟨δ, hδpos, hδ⟩ :=
        hK.exists_thickening_subset_open (hV.preimage γ.continuous) hKsub
      obtain ⟨n, hn⟩ : ∃ n : ℕ, pathEvalRadius n ≤ δ := by
        obtain ⟨n, hn⟩ := exists_nat_gt (δ⁻¹)
        refine ⟨n, ?_⟩
        have hnpos : (0 : ℝ) < n := lt_trans (inv_pos.mpr hδpos) hn
        have hrecip : 1 / (n : ℝ) < δ := by
          have := one_div_lt_one_div_of_lt (inv_pos.mpr hδpos) hn
          simpa using this
        have hncast : (n : ℝ) ≤ n + 1 := by norm_num
        have hmono : pathEvalRadius n ≤ 1 / (n : ℝ) := by
          simpa [pathEvalRadius, one_div] using one_div_le_one_div_of_le hnpos hncast
        exact hmono.trans hrecip.le
      apply Set.mem_iUnion.mpr
      refine ⟨(F, n), ?_⟩
      intro t ht
      have htδ : (t : ℝ≥0) ∈ Metric.thickening δ K :=
        Metric.thickening_mono hn K ht
      have htV := hδ htδ
      have hOpenSubClosed : pathTargetOpenCover F ⊆ pathTargetClosedCover F := by
        intro y hy
        rcases Set.mem_iUnion₂.mp hy with ⟨b, hb, hyb⟩
        exact Set.mem_iUnion₂.mpr ⟨b, hb, subset_closure hyb⟩
      exact hOpenSubClosed htV
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨p, hp⟩
      rcases p with ⟨F, n⟩
      let C := pathTargetClosedCover F
      have hCclosed : IsClosed C := isClosed_pathTargetClosedCover F
      have hCsub : C ⊆ U := by
        intro y hy
        rcases Set.mem_iUnion₂.mp hy with ⟨b, hb, hyb⟩
        exact b.2 hyb
      have hrpos : (0 : ℝ) < pathEvalRadius n := by
        rw [pathEvalRadius]
        positivity
      have hKthick : K ⊆ Metric.thickening (pathEvalRadius n) K :=
        Metric.self_subset_thickening hrpos K
      have hDenseClose :
          Metric.thickening (pathEvalRadius n) K ⊆
            closure (denseNonnegativeTimes ∩ Metric.thickening (pathEvalRadius n) K) :=
        by
          simpa [Set.inter_comm] using
            dense_denseNonnegativeTimes.open_subset_closure_inter Metric.isOpen_thickening
      have hEvalSubset :
          denseNonnegativeTimes ∩ Metric.thickening (pathEvalRadius n) K ⊆ γ ⁻¹' C := by
        intro t ht
        exact hp ⟨t, ht.1⟩ ht.2
      intro t ht
      have htclose : (t : ℝ≥0) ∈
          closure (denseNonnegativeTimes ∩ Metric.thickening (pathEvalRadius n) K) :=
        hDenseClose (hKthick ht)
      have hpreclosed : IsClosed (γ ⁻¹' C) := hCclosed.preimage γ.continuous
      have hC : γ t ∈ C :=
        hpreclosed.closure_subset (closure_mono hEvalSubset htclose)
      exact hCsub hC
  rw [hsub]
  apply MeasurableSet.iUnion
  intro p
  exact measurable_pathEvalNearCondition K p.1 p.2

/-- The Borel sigma algebra on continuous nonnegative-time paths is generated by
finite measurable evaluation cylinders. -/
theorem borel_eq_generateFrom_measurablePathCylinders (d : ℕ) :
    borel (Path d) =
      MeasurableSpace.generateFrom (measurablePathCylinders (d := d)) := by
  classical
  let S : Set (Set (Path d)) :=
    Set.image2 (fun K U => {γ : Path d | Set.MapsTo γ K U})
      {K : Set (ℝ≥0) | IsCompact K} {U : Set (Vec d) | IsOpen U}
  have htop : ContinuousMap.compactOpen = TopologicalSpace.generateFrom S := by
    change ContinuousMap.compactOpen = TopologicalSpace.generateFrom S
    rw [ContinuousMap.compactOpen_eq]
  have hborel : borel (Path d) = MeasurableSpace.generateFrom S :=
    borel_eq_generateFrom_of_subbasis htop
  apply le_antisymm
  · rw [hborel]
    apply MeasurableSpace.generateFrom_le
    rintro _ ⟨K, hK, U, hU, rfl⟩
    exact measurable_pathTargetOpenMapsTo K hK U hU
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨c, hc, rfl⟩
    exact measurable_pathEvalCylinder c hc

/-- Finite measures agreeing on measurable path evaluation cylinders agree on all Borel
sets of continuous nonnegative-time paths. -/
theorem measure_eq_of_eq_on_pathCylinders {d : ℕ} {P Q : Measure (Path d)}
    [IsFiniteMeasure P]
    (hC : ∀ c : List (ℝ≥0 × Set (Vec d)),
      (∀ p ∈ c, MeasurableSet p.2) →
        P (pathEvalCylinder c) = Q (pathEvalCylinder c))
    (huniv : P Set.univ = Q Set.univ) : P = Q := by
  have hgen := borel_eq_generateFrom_measurablePathCylinders d
  refine MeasureTheory.ext_of_generate_finite (measurablePathCylinders (d := d)) hgen
    isPiSystem_measurablePathCylinders ?_ huniv
  intro s hs
  rcases hs with ⟨c, hc, rfl⟩
  exact hC c hc

end EinsteinRelation
