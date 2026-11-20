import EinsteinFull.Regeneration.BoxCoordinateMeasure
import EinsteinFull.Regeneration.BoxTransverseCollar
import EinsteinFull.Regeneration.VanishingFaceCollar

/-!
# Force-coordinate collars of an open box

The open-box collar mass is bounded by closed product collar masses, so zero
force-face values imply the normalized mass tends to zero.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- Vanishing values on the two force faces imply vanishing normalized collar mass. -/
theorem tendsto_box_force_collar_normalized
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (a b : PDE.Vec (n + 1))
    (hclosed : closedCoordinateBox i a b (a i) (b i) ⊆ U)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ k, 0 < δ k)
    (hthin : ∀ k, a i + δ k < b i - δ k)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hleft : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (a i, z)) = 0)
    (hright : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (b i, z)) = 0) :
    Tendsto (fun k => (∫ x in boxFaceCollars a b i (δ k), u x ^ 2
      ∂(PDE.volumeOn (PDE.axisBox a b))) / (δ k) ^ 2) atTop (𝓝 0) := by
  let K := transverseClosedBox i a b
  have hK : MeasurableSet K := measurableSet_Icc
  have hKfinite : volume K ≠ ∞ := isCompact_Icc.measure_lt_top.ne
  have hfull : coordinateIntervalBox n i (a i) (b i) K ⊆ U :=
    (coordinateIntervalBox_subset_closedCoordinateBox i a b (a i) (b i)).trans hclosed
  have hδl : ∀ k, a i + δ k ≤ b i := fun k => by linarith [hthin k, hδpos k]
  have hδr : ∀ k, a i ≤ b i - δ k := fun k => by linarith [hthin k, hδpos k]
  have hl := tendsto_left_face_collar_normalized hU u i (a i) (b i) δ hδ hδpos hδl
    K hK hKfinite hfull hr hball hcont hleft
  have hr' := tendsto_right_face_collar_normalized hU u i (a i) (b i) δ hδ hδpos hδr
    K hK hKfinite hfull hr hball hcont hright
  have hsum := hl.add hr'
  have hQmeas : MeasurableSet (PDE.axisBox a b) := (PDE.isOpen_axisBox a b).measurableSet
  have hQsub : PDE.axisBox a b ⊆ U := (axisBox_subset_closedCoordinateBox i a b).trans hclosed
  have hval : Integrable (fun x => u x ^ 2) (PDE.volumeOn (PDE.axisBox a b)) :=
    u.memL2.integrable_sq.mono_measure (Measure.restrict_mono hQsub le_rfl)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hsum)
    (fun k => div_nonneg (integral_nonneg fun _ => sq_nonneg _) (sq_nonneg _)) ?_
  intro k
  change (∫ x in boxFaceCollars a b i (δ k), u x ^ 2
      ∂(PDE.volumeOn (PDE.axisBox a b))) / (δ k) ^ 2 ≤
    (∫ p, u (centralSlabPoint n i p) ^ 2
      ∂((volume.restrict (Icc (a i) (a i + δ k))).prod (volume.restrict K))) / (δ k) ^ 2 +
    (∫ p, u (centralSlabPoint n i p) ^ 2
      ∂((volume.restrict (Icc (b i - δ k) (b i))).prod (volume.restrict K))) / (δ k) ^ 2
  let L : Set (PDE.Vec (n + 1)) := {x | x i ≤ a i + δ k}
  let R : Set (PDE.Vec (n + 1)) := {x | b i - δ k ≤ x i}
  have hLm : MeasurableSet L := measurableSet_le (measurable_pi_apply i) measurable_const
  have hRm : MeasurableSet R := measurableSet_le measurable_const (measurable_pi_apply i)
  have hdis : Disjoint L R := by
    apply Set.disjoint_left.2
    intro x hxL hxR
    change x i ≤ a i + δ k at hxL
    change b i - δ k ≤ x i at hxR
    linarith [hthin k]
  have hunion : boxFaceCollars a b i (δ k) = L ∪ R := rfl
  have hsplit : (∫ x in boxFaceCollars a b i (δ k), u x ^ 2
      ∂(PDE.volumeOn (PDE.axisBox a b))) =
      (∫ x in L, u x ^ 2 ∂(PDE.volumeOn (PDE.axisBox a b))) +
      ∫ x in R, u x ^ 2 ∂(PDE.volumeOn (PDE.axisBox a b)) := by
    rw [hunion]
    exact setIntegral_union hdis hRm (hval.mono_measure Measure.restrict_le_self)
      (hval.mono_measure Measure.restrict_le_self)
  have hboxL : closedCoordinateBox i a b (a i) (a i + δ k) ⊆ U := by
    apply Set.Subset.trans _ hclosed
    intro x hx
    exact ⟨⟨hx.1.1, hx.1.2.trans (hδl k)⟩, hx.2⟩
  have hboxR : closedCoordinateBox i a b (b i - δ k) (b i) ⊆ U := by
    apply Set.Subset.trans _ hclosed
    intro x hx
    exact ⟨⟨(hδr k).trans hx.1.1, hx.1.2⟩, hx.2⟩
  have hsubL : L ∩ PDE.axisBox a b ⊆ closedCoordinateBox i a b (a i) (a i + δ k) := by
    intro x hx
    have hbox := axisBox_subset_closedCoordinateBox i a b hx.2
    change ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x).1 ∈
      Icc (a i) (b i)) ∧ _ at hbox
    change ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x).1 ∈
      Icc (a i) (a i + δ k)) ∧ _
    refine ⟨⟨hbox.1.1, ?_⟩, hbox.2⟩
    simpa [L, MeasurableEquiv.piFinSuccAbove_apply] using hx.1
  have hsubR : R ∩ PDE.axisBox a b ⊆ closedCoordinateBox i a b (b i - δ k) (b i) := by
    intro x hx
    have hbox := axisBox_subset_closedCoordinateBox i a b hx.2
    change ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x).1 ∈
      Icc (a i) (b i)) ∧ _ at hbox
    change ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x).1 ∈
      Icc (b i - δ k) (b i)) ∧ _
    refine ⟨⟨?_, hbox.1.2⟩, hbox.2⟩
    simpa [R, MeasurableEquiv.piFinSuccAbove_apply] using hx.1
  have hvU : IntegrableOn (fun x => u x ^ 2) U := u.memL2.integrable_sq
  have hleftbound : (∫ x in L, u x ^ 2 ∂(PDE.volumeOn (PDE.axisBox a b))) ≤
      ∫ p, u (centralSlabPoint n i p) ^ 2
        ∂((volume.restrict (Icc (a i) (a i + δ k))).prod (volume.restrict K)) := by
    rw [← integral_closedCoordinateBox i a b (a i) (a i + δ k) (fun x => u x ^ 2)]
    change (∫ x, u x ^ 2 ∂((volume.restrict (PDE.axisBox a b)).restrict L)) ≤ _
    rw [Measure.restrict_restrict hLm]
    exact setIntegral_mono_set (hvU.mono_set hboxL)
      (Filter.Eventually.of_forall fun x => sq_nonneg (u x))
      (Filter.Eventually.of_forall fun x hx => hsubL hx)
  have hrightbound : (∫ x in R, u x ^ 2 ∂(PDE.volumeOn (PDE.axisBox a b))) ≤
      ∫ p, u (centralSlabPoint n i p) ^ 2
        ∂((volume.restrict (Icc (b i - δ k) (b i))).prod (volume.restrict K)) := by
    rw [← integral_closedCoordinateBox i a b (b i - δ k) (b i) (fun x => u x ^ 2)]
    change (∫ x, u x ^ 2 ∂((volume.restrict (PDE.axisBox a b)).restrict R)) ≤ _
    rw [Measure.restrict_restrict hRm]
    exact setIntegral_mono_set (hvU.mono_set hboxR)
      (Filter.Eventually.of_forall fun x => sq_nonneg (u x))
      (Filter.Eventually.of_forall fun x hx => hsubR hx)
  rw [hsplit, ← add_div]
  exact div_le_div_of_nonneg_right (add_le_add hleftbound hrightbound) (sq_nonneg _)

end EinsteinFull.Regeneration
