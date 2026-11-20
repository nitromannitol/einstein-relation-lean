import EinsteinFull.Regeneration.SlabCentralCubeTransfer
import PDEFoundation.Sobolev.W1p.ConvexApprox.Summable
import PDEFoundation.Sobolev.W1p.GraphEnergy

/-!
# Convex approximation on central slab coordinates

Smooth convex approximations of an H¹ function retain their summable value and
full-gradient errors under the measure-preserving central-slab coordinate split.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- A common smooth subsequence has summable value and gradient errors on the central slab. -/
theorem exists_central_slab_smooth_approximation
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L : ℝ) (hsub : coordinateCentralSlab n i L ⊆ U)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) :
    ∃ F : ℕ → PDE.Vec (n + 1) → ℝ,
      (∀ k, ContDiff ℝ 1 (F k)) ∧
      (∀ k, MemLp (fun p => F k (centralSlabPoint n i p) -
        u (centralSlabPoint n i p)) 2 (centralSlabMeasure n L)) ∧
      (∀ k, MemLp (fun p => PDE.vecEuclideanNorm
        (PDE.classicalGradient (F k) (centralSlabPoint n i p) -
          u.grad (centralSlabPoint n i p))) 2 (centralSlabMeasure n L)) ∧
      Summable (fun k => (2 : ℝ) ^ k * ∫ p,
        (F k (centralSlabPoint n i p) - u (centralSlabPoint n i p)) ^ 2
          ∂(centralSlabMeasure n L)) ∧
      Summable (fun k => (2 : ℝ) ^ k * ∫ p,
        (PDE.vecEuclideanNorm (PDE.classicalGradient (F k) (centralSlabPoint n i p) -
          u.grad (centralSlabPoint n i p))) ^ 2 ∂(centralSlabMeasure n L)) := by
  obtain ⟨σ, _, hsmooth, _, hgraph⟩ :=
    PDE.H1Function.exists_strictMono_convexApproxSmoothW1p_summable_h1Graph_error
      hU u hball hr
  let ψ : ℕ → PDE.W1pFunction U (2 : ℝ≥0∞) := fun k =>
    PDE.W1pFunction.convexApproxSmoothW1p hU (by norm_num) u.toW1pFunction x₀ hr (σ k)
  let F : ℕ → PDE.Vec (n + 1) → ℝ := fun k => (ψ k).toFun
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
  have hgraph' : Summable (fun k => (2 : ℝ) ^ k *
      dist (ψ k).toW1pGraph u.toW1pFunction.toW1pGraph ^ 2) := by
    simpa only [ψ] using hgraph
  have hv (k : ℕ) : MemLp (fun x => F k x - u x) 2 (volume.restrict W) := by
    have h := ((ψ k).memLp.sub u.toW1pFunction.memLp).mono_measure
      (Measure.restrict_mono hsub le_rfl)
    convert h using 1
    funext x
    rfl
  have hg (k : ℕ) : MemLp (fun x => PDE.vecEuclideanNorm
      (PDE.classicalGradient (F k) x - u.grad x)) 2 (volume.restrict W) := by
    have hmem : PDE.MemLpOn U (2 : ℝ≥0∞)
        (fun x => PDE.vecEuclideanNorm ((ψ k).grad x - u.grad x)) := by
      apply PDE.GradMemLpOn.memLp_vecEuclideanNorm
      intro j
      exact ((ψ k).gradMemLp j).sub (u.gradMemL2 j)
    have h := PDE.memLpOn_mono hsub hmem
    simpa only [F, ψ, PDE.W1pFunction.convexApproxSmoothW1p_toFun,
      PDE.W1pFunction.convexApproxSmoothW1p_grad] using h
  have hvs := PDE.H1Function.summable_dyadic_integralOn_sq_sub_toW1pFunction ψ u hsub hgraph'
  have hgs := PDE.H1Function.summable_dyadic_integralOn_sq_grad_sub_toW1pFunction ψ u hsub hgraph'
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (hsmooth k).of_le (by norm_num)
  · intro k
    simpa only [centralSlabPoint, e, Function.comp_def] using (hv k).comp_measurePreserving hpresW
  · intro k
    simpa only [centralSlabPoint, e, Function.comp_def] using (hg k).comp_measurePreserving hpresW
  · convert hvs using 1
    ext k
    congr 1
    change (∫ p, (F k (e p) - u (e p)) ^ 2 ∂centralSlabMeasure n L) = _
    rw [← hpresW.map_eq]
    exact (integral_map_equiv (μ := centralSlabMeasure n L) e
      (fun x => (F k x - u x) ^ 2)).symm
  · convert hgs using 1
    ext k
    congr 1
    change (∫ p, (PDE.vecEuclideanNorm (PDE.classicalGradient (F k) (e p) -
      u.grad (e p))) ^ 2 ∂centralSlabMeasure n L) = _
    rw [← hpresW.map_eq]
    simpa only [F, ψ, PDE.W1pFunction.convexApproxSmoothW1p_toFun,
      PDE.W1pFunction.convexApproxSmoothW1p_grad] using (integral_map_equiv (μ := centralSlabMeasure n L) e
        (fun x => (PDE.vecEuclideanNorm
          (PDE.classicalGradient (F k) x - u.grad x)) ^ 2)).symm

end EinsteinFull.Regeneration
