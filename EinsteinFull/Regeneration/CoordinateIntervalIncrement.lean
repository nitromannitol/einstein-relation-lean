import EinsteinFull.Regeneration.CoordinateIntervalApproximation
import EinsteinFull.Regeneration.IntervalSliceApproximation

/-!
# Sobolev increments on coordinate boxes

A continuous H¹ function on a bounded open convex domain has its exact
subinterval increments on almost every line in a finite transverse section.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- Continuous Sobolev functions have every increment on almost every interval line. -/
theorem ae_coordinate_interval_subincrement_of_h1
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (a b : ℝ) (hab : a < b)
    (K : Set (Fin n → ℝ)) (hK : MeasurableSet K) (hKfinite : volume K ≠ ∞)
    (hsub : coordinateIntervalBox n i a b K ⊆ U)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun) :
    ∀ᵐ z ∂(volume.restrict K),
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        u (centralSlabPoint n i (t, z)) - u (centralSlabPoint n i (s, z)) =
          ∫ x in s..t, u.grad (centralSlabPoint n i (x, z)) i := by
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
  have hWmeas : MeasurableSet W :=
    (measurableSet_Ioc.prod hK).preimage
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).measurable
  have hm : (volume : Measure (ℝ × (Fin n → ℝ))).restrict V = coordinateIntervalMeasure n a b K := by
    dsimp only [V, coordinateIntervalMeasure]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hpresW := hpres.restrict_preimage hWmeas
  rw [hpre, hm] at hpresW
  have hu : MemLp (fun p => u (centralSlabPoint n i p)) 2 (coordinateIntervalMeasure n a b K) := by
    have h := u.memL2.mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa only [centralSlabPoint, e, Function.comp_def] using h.comp_measurePreserving hpresW
  have hg : MemLp (fun p => u.grad (centralSlabPoint n i p) i) 2 (coordinateIntervalMeasure n a b K) := by
    have h := (u.gradMemL2 i).mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa only [centralSlabPoint, e, Function.comp_def] using h.comp_measurePreserving hpresW
  obtain ⟨F, hF, hv, he, hvs, hes⟩ :=
    exists_coordinate_interval_smooth_approximation hU u i a b K hK hsub hr hball
  apply ae_interval_subinterval_increment_of_smooth_approximations ν i a b hab
    (fun k p => F k (centralSlabPoint n i p))
    (fun p => u (centralSlabPoint n i p))
    (fun p => u.grad (centralSlabPoint n i p) i)
    (fun k p => PDE.classicalGradient (F k) (centralSlabPoint n i p) -
      u.grad (centralSlabPoint n i p))
  · intro z k
    have hline : ContDiff ℝ 1 (fun t => centralSlabPoint n i (t, z)) := by
      convert (contDiff_const.add (contDiff_id.smul contDiff_const) :
        ContDiff ℝ 1 (fun t : ℝ => centralSlabPoint n i (0, z) + t • PDE.basisVec i)) using 1
      funext t
      exact centralSlabPoint_eq_add n i t z
    exact (hF k).comp hline
  · exact Filter.Eventually.of_forall fun z =>
      (hcont.comp (continuous_centralSlabPoint n i z)).continuousOn
  · exact hu
  · exact hg
  · exact hv
  · exact he
  · exact hvs
  · exact hes
  · intro z k t
    simp only [deriv_central_slab_line i z (hF k), Pi.sub_apply]



end EinsteinFull.Regeneration
