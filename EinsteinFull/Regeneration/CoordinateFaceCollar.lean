import EinsteinFull.Regeneration.CoordinateIntervalIncrement
import EinsteinFull.Regeneration.LeftFaceProduct

/-!
# Boundary collars on coordinate slabs

A continuous Sobolev function vanishing on an end face has squared mass in a
collar bounded by the collar width squared times its normal derivative energy.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- A vanishing left trace gives the scale-sharp normal collar estimate. -/
theorem coordinate_left_face_collar_le
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (a b : ℝ) (hab : a < b)
    (K : Set (Fin n → ℝ)) (hK : MeasurableSet K) (hKfinite : volume K ≠ ∞)
    (hsub : coordinateIntervalBox n i a b K ⊆ U)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hface : ∀ᵐ z ∂(volume.restrict K), u (centralSlabPoint n i (a, z)) = 0) :
    Integrable (fun p => u (centralSlabPoint n i p) ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict K)) ∧
    Integrable (fun p => u.grad (centralSlabPoint n i p) i ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict K)) ∧
    (∫ p, u (centralSlabPoint n i p) ^ 2
      ∂((volume.restrict (Icc a b)).prod (volume.restrict K))) ≤
      (b - a) ^ 2 * ∫ p, u.grad (centralSlabPoint n i p) i ^ 2
        ∂((volume.restrict (Icc a b)).prod (volume.restrict K)) := by
  let ν : Measure (Fin n → ℝ) := volume.restrict K
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hKfinite
  let μ : Measure (ℝ × (Fin n → ℝ)) := (volume.restrict (Icc a b)).prod ν
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
  have hu : MemLp (fun p => u (centralSlabPoint n i p)) 2 μ := by
    have h := u.memL2.mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa only [centralSlabPoint, e, Function.comp_def] using h.comp_measurePreserving hpresW
  have hg : MemLp (fun p => u.grad (centralSlabPoint n i p) i) 2 μ := by
    have h := (u.gradMemL2 i).mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa only [centralSlabPoint, e, Function.comp_def] using h.comp_measurePreserving hpresW
  have hfaceprod := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict (Icc a b)) (ν := ν)).ae hface
  have hvalue : Integrable (fun p =>
      (u (centralSlabPoint n i p) - u (centralSlabPoint n i (a, p.2))) ^ 2) μ := by
    apply hu.integrable_sq.congr
    filter_upwards [hfaceprod] with p hp
    rw [hp, sub_zero]
  have hslice : ∀ᵐ z ∂ν, ∀ x ∈ Icc a b,
      u (centralSlabPoint n i (x, z)) - u (centralSlabPoint n i (a, z)) =
        ∫ t in a..x, u.grad (centralSlabPoint n i (t, z)) i := by
    filter_upwards [ae_coordinate_interval_subincrement_of_h1 hU u i a b hab K hK
      hKfinite hsub hr hball hcont] with z hz
    intro x hx
    exact hz a ⟨le_rfl, hab.le⟩ x hx
  have hbound := (product_left_face_sq_le ν hab
    (fun p => u (centralSlabPoint n i p)) (fun p => u.grad (centralSlabPoint n i p) i)
    hg hvalue hslice).2
  have heq : (∫ p, (u (centralSlabPoint n i p) -
      u (centralSlabPoint n i (a, p.2))) ^ 2 ∂μ) =
      ∫ p, u (centralSlabPoint n i p) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hfaceprod] with p hp
    rw [hp, sub_zero]
  rw [heq] at hbound
  exact ⟨hu.integrable_sq, hg.integrable_sq, hbound⟩


/-- A vanishing right trace gives the scale-sharp normal collar estimate. -/
theorem coordinate_right_face_collar_le
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (a b : ℝ) (hab : a < b)
    (K : Set (Fin n → ℝ)) (hK : MeasurableSet K) (hKfinite : volume K ≠ ∞)
    (hsub : coordinateIntervalBox n i a b K ⊆ U)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hface : ∀ᵐ z ∂(volume.restrict K), u (centralSlabPoint n i (b, z)) = 0) :
    Integrable (fun p => u (centralSlabPoint n i p) ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict K)) ∧
    Integrable (fun p => u.grad (centralSlabPoint n i p) i ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict K)) ∧
    (∫ p, u (centralSlabPoint n i p) ^ 2
      ∂((volume.restrict (Icc a b)).prod (volume.restrict K))) ≤
      (b - a) ^ 2 * ∫ p, u.grad (centralSlabPoint n i p) i ^ 2
        ∂((volume.restrict (Icc a b)).prod (volume.restrict K)) := by
  let ν : Measure (Fin n → ℝ) := volume.restrict K
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hKfinite
  let μ : Measure (ℝ × (Fin n → ℝ)) := (volume.restrict (Icc a b)).prod ν
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
  have hu : MemLp (fun p => u (centralSlabPoint n i p)) 2 μ := by
    have h := u.memL2.mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa only [centralSlabPoint, e, Function.comp_def] using h.comp_measurePreserving hpresW
  have hg : MemLp (fun p => u.grad (centralSlabPoint n i p) i) 2 μ := by
    have h := (u.gradMemL2 i).mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa only [centralSlabPoint, e, Function.comp_def] using h.comp_measurePreserving hpresW
  have hfaceprod := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict (Icc a b)) (ν := ν)).ae hface
  have hvalue : Integrable (fun p => Real.exp ((0 : ℝ) * p.1) *
      (u (centralSlabPoint n i (b, p.2)) - u (centralSlabPoint n i p)) ^ 2) μ := by
    apply hu.integrable_sq.congr
    filter_upwards [hfaceprod] with p hp
    simp [hp, sq_abs]
  have henergy : Integrable (fun p => Real.exp ((0 : ℝ) * p.1) *
      (u.grad (centralSlabPoint n i p) i) ^ 2) μ := by
    simpa using hg.integrable_sq
  have hslice : ∀ᵐ z ∂ν, ContinuousOn (fun x => u (centralSlabPoint n i (x, z))) (Icc a b) ∧
      ∀ x ∈ Icc a b,
        u (centralSlabPoint n i (b, z)) - u (centralSlabPoint n i (x, z)) =
          ∫ t in x..b, u.grad (centralSlabPoint n i (t, z)) i := by
    filter_upwards [ae_coordinate_interval_subincrement_of_h1 hU u i a b hab K hK
      hKfinite hsub hr hball hcont] with z hz
    refine ⟨(hcont.comp (continuous_centralSlabPoint n i z)).continuousOn, ?_⟩
    intro x hx
    exact hz x hx b ⟨hab.le, le_rfl⟩
  have hbound := weighted_product_right_face_sq_le ν hab (s := 0) (by norm_num)
    (fun p => u (centralSlabPoint n i p)) (fun p => u.grad (centralSlabPoint n i p) i)
    hg hvalue henergy hslice
  have heq : (∫ p, Real.exp ((0 : ℝ) * p.1) * (u (centralSlabPoint n i (b, p.2)) -
      u (centralSlabPoint n i p)) ^ 2 ∂μ) =
      ∫ p, u (centralSlabPoint n i p) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hfaceprod] with p hp
    simp [hp]
  rw [heq] at hbound
  refine ⟨hu.integrable_sq, hg.integrable_sq, ?_⟩
  simpa using hbound

end EinsteinFull.Regeneration
