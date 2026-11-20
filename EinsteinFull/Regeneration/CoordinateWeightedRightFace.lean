import EinsteinFull.Regeneration.CoordinateIntervalIncrement
import EinsteinFull.Regeneration.WeightedRightFaceProduct

/-!
# Weighted right-face estimate for Sobolev functions

The coordinate-slice increment theorem and Fubini yield the weighted distance
to the right face for a continuous Sobolev function on a coordinate box.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- A continuous H¹ function satisfies the weighted right-face estimate on a coordinate box. -/
theorem coordinate_weighted_right_face_sq_le
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (a b s : ℝ) (hab : a < b) (hs : 0 ≤ s)
    (K : Set (Fin n → ℝ)) (hK : MeasurableSet K) (hKfinite : volume K ≠ ∞)
    (hsub : coordinateIntervalBox n i a b K ⊆ U)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hvalue : Integrable (fun p => Real.exp (s * p.1) *
      (u (centralSlabPoint n i (b, p.2)) - u (centralSlabPoint n i p)) ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict K)))
    (henergy : Integrable (fun p => Real.exp (s * p.1) *
      (u.grad (centralSlabPoint n i p) i) ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict K))) :
    (∫ p, Real.exp (s * p.1) *
      (u (centralSlabPoint n i (b, p.2)) - u (centralSlabPoint n i p)) ^ 2
      ∂((volume.restrict (Icc a b)).prod (volume.restrict K))) ≤
      (b - a) ^ 2 * ∫ p, Real.exp (s * p.1) *
        (u.grad (centralSlabPoint n i p) i) ^ 2
        ∂((volume.restrict (Icc a b)).prod (volume.restrict K)) := by
  let ν : Measure (Fin n → ℝ) := volume.restrict K
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hKfinite
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  let V : Set (ℝ × (Fin n → ℝ)) := Ioc a b ×ˢ K
  let W := coordinateIntervalBox n i a b K
  have hpres : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have hpre : e ⁻¹' W = V := by
    ext p
    simp [W, coordinateIntervalBox, e, V]
  have hWmeas : MeasurableSet W := (measurableSet_Ioc.prod hK).preimage
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).measurable
  have hm : (volume : Measure (ℝ × (Fin n → ℝ))).restrict V =
      (volume.restrict (Icc a b)).prod ν := by
    dsimp only [V, ν]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hpresW := hpres.restrict_preimage hWmeas
  rw [hpre, hm] at hpresW
  have hg : MemLp (fun p => u.grad (centralSlabPoint n i p) i) 2
      ((volume.restrict (Icc a b)).prod ν) := by
    have h := (u.gradMemL2 i).mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa only [centralSlabPoint, e, Function.comp_def] using h.comp_measurePreserving hpresW
  apply weighted_product_right_face_sq_le ν hab hs
    (fun p => u (centralSlabPoint n i p))
    (fun p => u.grad (centralSlabPoint n i p) i) hg hvalue henergy
  filter_upwards [ae_coordinate_interval_subincrement_of_h1 hU u i a b hab K hK
    hKfinite hsub hr hball hcont] with z hz
  refine ⟨(hcont.comp (continuous_centralSlabPoint n i z)).continuousOn, ?_⟩
  intro x hx
  exact hz x hx b ⟨hab.le, le_rfl⟩

end EinsteinFull.Regeneration
