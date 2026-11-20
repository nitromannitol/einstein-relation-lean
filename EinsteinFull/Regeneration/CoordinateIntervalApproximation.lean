import EinsteinFull.Regeneration.SlabSobolevIncrement

/-!
# Smooth approximations on coordinate boxes

Convex approximation yields summable value and gradient errors on any
measurable transverse section of an interval box.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- A force-coordinate interval times a transverse section, in vector coordinates. -/
noncomputable def coordinateIntervalBox (n : ℕ) (i : Fin (n + 1))
    (a b : ℝ) (K : Set (Fin n → ℝ)) : Set (PDE.Vec (n + 1)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i) ⁻¹' (Ioc a b ×ˢ K)

/-- Product measure on an interval and a transverse section. -/
noncomputable def coordinateIntervalMeasure (n : ℕ) (a b : ℝ) (K : Set (Fin n → ℝ)) :
    Measure (ℝ × (Fin n → ℝ)) :=
  (volume.restrict (Ioc a b)).prod (volume.restrict K)

/-- Convex approximation gives summable value and gradient errors on a coordinate box. -/
theorem exists_coordinate_interval_smooth_approximation
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (a b : ℝ) (K : Set (Fin n → ℝ))
    (hK : MeasurableSet K) (hsub : coordinateIntervalBox n i a b K ⊆ U)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) :
    ∃ F : ℕ → PDE.Vec (n + 1) → ℝ,
      (∀ k, ContDiff ℝ 1 (F k)) ∧
      (∀ k, MemLp (fun p => F k (centralSlabPoint n i p) -
        u (centralSlabPoint n i p)) 2 (coordinateIntervalMeasure n a b K)) ∧
      (∀ k, MemLp (fun p => PDE.vecEuclideanNorm
        (PDE.classicalGradient (F k) (centralSlabPoint n i p) -
          u.grad (centralSlabPoint n i p))) 2 (coordinateIntervalMeasure n a b K)) ∧
      Summable (fun k => (2 : ℝ) ^ k * ∫ p,
        (F k (centralSlabPoint n i p) - u (centralSlabPoint n i p)) ^ 2
          ∂(coordinateIntervalMeasure n a b K)) ∧
      Summable (fun k => (2 : ℝ) ^ k * ∫ p,
        (PDE.vecEuclideanNorm (PDE.classicalGradient (F k) (centralSlabPoint n i p) -
          u.grad (centralSlabPoint n i p))) ^ 2 ∂(coordinateIntervalMeasure n a b K)) := by
  obtain ⟨σ, _, hsmooth, _, hgraph⟩ :=
    PDE.H1Function.exists_strictMono_convexApproxSmoothW1p_summable_h1Graph_error
      hU u hball hr
  let ψ : ℕ → PDE.W1pFunction U (2 : ℝ≥0∞) := fun k =>
    PDE.W1pFunction.convexApproxSmoothW1p hU (by norm_num) u.toW1pFunction x₀ hr (σ k)
  let F : ℕ → PDE.Vec (n + 1) → ℝ := fun k => (ψ k).toFun
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
    change (∫ p, (F k (e p) - u (e p)) ^ 2 ∂coordinateIntervalMeasure n a b K) = _
    rw [← hpresW.map_eq]
    exact (integral_map_equiv (μ := coordinateIntervalMeasure n a b K) e
      (fun x => (F k x - u x) ^ 2)).symm
  · convert hgs using 1
    ext k
    congr 1
    change (∫ p, (PDE.vecEuclideanNorm (PDE.classicalGradient (F k) (e p) -
      u.grad (e p))) ^ 2 ∂coordinateIntervalMeasure n a b K) = _
    rw [← hpresW.map_eq]
    simpa only [F, ψ, PDE.W1pFunction.convexApproxSmoothW1p_toFun,
      PDE.W1pFunction.convexApproxSmoothW1p_grad] using (integral_map_equiv (μ := coordinateIntervalMeasure n a b K) e
        (fun x => (PDE.vecEuclideanNorm
          (PDE.classicalGradient (F k) x - u.grad x)) ^ 2)).symm


end EinsteinFull.Regeneration
