import EinsteinFull.Regeneration.SlabConvexApproximation
import EinsteinFull.Regeneration.SlabSliceApproximation
import EinsteinFull.Regeneration.SlabHarnackEnergy

/-!
# Sobolev increments on central slab lines

Smooth convex approximation and Fubini identify the increment of a continuous
H¹ representative with the integral of its force-coordinate weak derivative on
almost every central slab line.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- A central slab line is an affine line in the force coordinate. -/
theorem centralSlabPoint_eq_add (n : ℕ) (i : Fin (n + 1)) (t : ℝ) (z : Fin n → ℝ) :
    centralSlabPoint n i (t, z) = centralSlabPoint n i (0, z) + t • PDE.basisVec i := by
  funext j
  refine i.succAboveCases ?_ (fun k => ?_) j
  · simp [centralSlabPoint_coord, PDE.basisVec_apply]
  · simp [centralSlabPoint_coord, PDE.basisVec_apply, Fin.succAbove_ne]

/-- Differentiating a smooth function on a central line selects its force derivative. -/
theorem deriv_central_slab_line {n : ℕ} (i : Fin (n + 1)) (z : Fin n → ℝ)
    {F : PDE.Vec (n + 1) → ℝ} (hF : ContDiff ℝ 1 F) (t : ℝ) :
    deriv (fun s => F (centralSlabPoint n i (s, z))) t =
      PDE.classicalGradient F (centralSlabPoint n i (t, z)) i := by
  have hpath : HasDerivAt (fun s => centralSlabPoint n i (s, z)) (PDE.basisVec i) t := by
    convert ((hasDerivAt_id t).smul_const (PDE.basisVec i)).const_add
      (centralSlabPoint n i (0, z)) using 1
    · funext s
      exact centralSlabPoint_eq_add n i s z
    · simp only [one_smul]
  have h := (hF.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t hpath
  simpa only [PDE.classicalGradient_apply] using! h.deriv

/-- Continuous H¹ functions have the expected increment on almost every central line. -/
theorem ae_central_slab_increment_of_h1
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L : ℝ) (hL : 0 < L)
    (hsub : coordinateCentralSlab n i L ⊆ U)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun) :
    ∀ᵐ z ∂(volume.restrict (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))),
      u (centralSlabPoint n i (L, z)) - u (centralSlabPoint n i (0, z)) =
        ∫ t in (0 : ℝ)..L, u.grad (centralSlabPoint n i (t, z)) i := by
  let ν : Measure (Fin n → ℝ) := volume.restrict (Icc (fun _ => -1) (fun _ => 1))
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  let V : Set (ℝ × (Fin n → ℝ)) := Ioc 0 L ×ˢ Icc (fun _ => -1) (fun _ => 1)
  let W := coordinateCentralSlab n i L
  have hpres : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have hpre : e ⁻¹' W = V := by
    ext p
    simp [W, coordinateCentralSlab, e, V]
  have hWmeas : MeasurableSet W :=
    (measurableSet_Ioc.prod measurableSet_Icc).preimage
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).measurable
  have hm : (volume : Measure (ℝ × (Fin n → ℝ))).restrict V = centralSlabMeasure n L := by
    dsimp only [V, centralSlabMeasure]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hpresW := hpres.restrict_preimage hWmeas
  rw [hpre, hm] at hpresW
  have hu : MemLp (fun p => u (centralSlabPoint n i p)) 2 (centralSlabMeasure n L) := by
    have h := u.memL2.mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa only [centralSlabPoint, e, Function.comp_def] using h.comp_measurePreserving hpresW
  have hg : MemLp (fun p => u.grad (centralSlabPoint n i p) i) 2 (centralSlabMeasure n L) := by
    have h := (u.gradMemL2 i).mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa only [centralSlabPoint, e, Function.comp_def] using h.comp_measurePreserving hpresW
  obtain ⟨F, hF, hv, he, hvs, hes⟩ :=
    exists_central_slab_smooth_approximation hU u i L hsub hr hball
  apply ae_slab_increment_of_smooth_approximations ν i L hL
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
