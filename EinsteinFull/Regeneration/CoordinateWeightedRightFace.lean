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


/-- Bounded solutions supply both integrability hypotheses in the right-face estimate. -/
theorem coordinate_weighted_right_face_sq_le_of_bounded
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (a b s : ℝ) (hab : a < b) (hs : 0 ≤ s)
    (K : Set (Fin n → ℝ)) (hK : MeasurableSet K) (hKfinite : volume K ≠ ∞)
    (hsub : coordinateIntervalBox n i a b K ⊆ U)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hzero : ∀ x, 0 ≤ u x) (hone : ∀ x, u x ≤ 1) :
    (∫ p, Real.exp (s * p.1) *
      (u (centralSlabPoint n i (b, p.2)) - u (centralSlabPoint n i p)) ^ 2
      ∂((volume.restrict (Icc a b)).prod (volume.restrict K))) ≤
      (b - a) ^ 2 * ∫ p, Real.exp (s * p.1) *
        (u.grad (centralSlabPoint n i p) i) ^ 2
        ∂((volume.restrict (Icc a b)).prod (volume.restrict K)) := by
  let ν : Measure (Fin n → ℝ) := volume.restrict K
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hKfinite
  let μ : Measure (ℝ × (Fin n → ℝ)) := (volume.restrict (Icc a b)).prod ν
  let : IsFiniteMeasure (volume.restrict (Icc a b) : Measure ℝ) := by infer_instance
  let : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
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
  have hm : (volume : Measure (ℝ × (Fin n → ℝ))).restrict V = μ := by
    dsimp only [V, μ, ν]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hpresW := hpres.restrict_preimage hWmeas
  rw [hpre, hm] at hpresW
  have hg : MemLp (fun p => u.grad (centralSlabPoint n i p) i) 2 μ := by
    have h := (u.gradMemL2 i).mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa only [centralSlabPoint, e, Function.comp_def] using h.comp_measurePreserving hpresW
  have hw : Measurable (fun p : ℝ × (Fin n → ℝ) => Real.exp (s * p.1)) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul measurable_fst)
  have hwbound : ∀ᵐ p ∂μ, ‖Real.exp (s * p.1)‖ ≤ Real.exp (s * b) := by
    have h := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Icc a b))
      (ν := ν)).ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [h] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp.2 hs)
  have henergy : Integrable (fun p => Real.exp (s * p.1) *
      (u.grad (centralSlabPoint n i p) i) ^ 2) μ :=
    hg.integrable_sq.bdd_mul hw.aestronglyMeasurable hwbound
  have he : Measurable (centralSlabPoint n i) := e.measurable
  have hface : Measurable (fun p : ℝ × (Fin n → ℝ) => centralSlabPoint n i (b, p.2)) :=
    he.comp (measurable_const.prodMk measurable_snd)
  have hvalmeas : Measurable (fun p : ℝ × (Fin n → ℝ) => Real.exp (s * p.1) *
      (u (centralSlabPoint n i (b, p.2)) - u (centralSlabPoint n i p)) ^ 2) :=
    hw.mul (((hcont.measurable.comp hface).sub (hcont.measurable.comp he)).pow_const _)
  have hvalue : Integrable (fun p => Real.exp (s * p.1) *
      (u (centralSlabPoint n i (b, p.2)) - u (centralSlabPoint n i p)) ^ 2) μ := by
    apply Integrable.of_bound hvalmeas.aestronglyMeasurable (Real.exp (s * b))
    filter_upwards [hwbound] with p hp
    have hx := hzero (centralSlabPoint n i p)
    have hy := hone (centralSlabPoint n i p)
    have hx' := hzero (centralSlabPoint n i (b, p.2))
    have hy' := hone (centralSlabPoint n i (b, p.2))
    have hsq : (u (centralSlabPoint n i (b, p.2)) - u (centralSlabPoint n i p)) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (1 - (u (centralSlabPoint n i (b, p.2)) - u (centralSlabPoint n i p))),
        sq_nonneg (1 + (u (centralSlabPoint n i (b, p.2)) - u (centralSlabPoint n i p)))]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    have hw' : Real.exp (s * p.1) ≤ Real.exp (s * b) := by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hp
    nlinarith [Real.exp_pos (s * p.1)]
  exact coordinate_weighted_right_face_sq_le hU u i a b s hab hs K hK hKfinite
    hsub hr hball hcont hvalue henergy

end EinsteinFull.Regeneration
