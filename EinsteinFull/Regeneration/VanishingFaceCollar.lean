import EinsteinFull.Regeneration.CoordinateFaceCollar
import EinsteinFull.Regeneration.ShrinkingProductCollar

/-!
# Vanishing normalized face collars

The endpoint inequality and absolute continuity of the normal derivative
energy imply that the normalized mass of a zero-trace collar tends to zero.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- A zero left trace makes the normalized collar mass tend to zero. -/
theorem tendsto_left_face_collar_normalized
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (a b : ℝ) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ k, 0 < δ k) (hδb : ∀ k, a + δ k ≤ b)
    (K : Set (Fin n → ℝ)) (hK : MeasurableSet K) (hKfinite : volume K ≠ ∞)
    (hsub : coordinateIntervalBox n i a b K ⊆ U)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hface : ∀ᵐ z ∂(volume.restrict K), u (centralSlabPoint n i (a, z)) = 0) :
    Tendsto (fun k => (∫ p, u (centralSlabPoint n i p) ^ 2
      ∂((volume.restrict (Icc a (a + δ k))).prod (volume.restrict K))) / (δ k) ^ 2)
      atTop (𝓝 0) := by
  let ν : Measure (Fin n → ℝ) := volume.restrict K
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hKfinite
  have hab : a < b := by linarith [hδpos 0, hδb 0]
  have hg := (coordinate_left_face_collar_le hU u i a b hab K hK hKfinite hsub
    hr hball hcont hface).2.1
  have henergy := tendsto_integral_left_product_collar ν a b δ hδ hδb
    (fun p => u.grad (centralSlabPoint n i p) i ^ 2) hg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds henergy ?_ ?_
  · intro k
    exact div_nonneg (integral_nonneg fun p => sq_nonneg _) (sq_nonneg _)
  · intro k
    have hsubk : coordinateIntervalBox n i a (a + δ k) K ⊆ U := by
      apply Set.Subset.trans _ hsub
      intro x hx
      change (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x) ∈
        Ioc a (a + δ k) ×ˢ K at hx
      change (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x) ∈
        Ioc a b ×ˢ K
      exact ⟨⟨hx.1.1, hx.1.2.trans (hδb k)⟩, hx.2⟩
    have hbound := (coordinate_left_face_collar_le hU u i a (a + δ k)
      (by linarith [hδpos k]) K hK hKfinite hsubk hr hball hcont hface).2.2
    have hsq : 0 < (δ k) ^ 2 := sq_pos_of_pos (hδpos k)
    apply (div_le_iff₀ hsq).2
    simpa only [add_sub_cancel_left, mul_comm] using hbound

/-- A zero right trace makes the normalized collar mass tend to zero. -/
theorem tendsto_right_face_collar_normalized
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (a b : ℝ) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ k, 0 < δ k) (hδb : ∀ k, a ≤ b - δ k)
    (K : Set (Fin n → ℝ)) (hK : MeasurableSet K) (hKfinite : volume K ≠ ∞)
    (hsub : coordinateIntervalBox n i a b K ⊆ U)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hface : ∀ᵐ z ∂(volume.restrict K), u (centralSlabPoint n i (b, z)) = 0) :
    Tendsto (fun k => (∫ p, u (centralSlabPoint n i p) ^ 2
      ∂((volume.restrict (Icc (b - δ k) b)).prod (volume.restrict K))) / (δ k) ^ 2)
      atTop (𝓝 0) := by
  let ν : Measure (Fin n → ℝ) := volume.restrict K
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hKfinite
  have hab : a < b := by linarith [hδpos 0, hδb 0]
  have hg := (coordinate_right_face_collar_le hU u i a b hab K hK hKfinite hsub
    hr hball hcont hface).2.1
  have henergy := tendsto_integral_right_product_collar ν a b δ hδ hδb
    (fun p => u.grad (centralSlabPoint n i p) i ^ 2) hg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds henergy ?_ ?_
  · intro k
    exact div_nonneg (integral_nonneg fun p => sq_nonneg _) (sq_nonneg _)
  · intro k
    have hsubk : coordinateIntervalBox n i (b - δ k) b K ⊆ U := by
      apply Set.Subset.trans _ hsub
      intro x hx
      change (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x) ∈
        Ioc (b - δ k) b ×ˢ K at hx
      change (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x) ∈
        Ioc a b ×ˢ K
      exact ⟨⟨lt_of_le_of_lt (hδb k) hx.1.1, hx.1.2⟩, hx.2⟩
    have hbound := (coordinate_right_face_collar_le hU u i (b - δ k) b
      (by linarith [hδpos k]) K hK hKfinite hsubk hr hball hcont hface).2.2
    have hsq : 0 < (δ k) ^ 2 := sq_pos_of_pos (hδpos k)
    apply (div_le_iff₀ hsq).2
    simpa only [sub_sub_cancel, mul_comm] using hbound

end EinsteinFull.Regeneration
