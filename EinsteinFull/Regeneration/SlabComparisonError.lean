import EinsteinFull.Regeneration.CoordinateWeightedError
import EinsteinFull.Regeneration.CoordinateWeightedGradient
import EinsteinFull.Regeneration.SlabBoundaryProfile
import EinsteinFull.Regeneration.SlabProfileError

/-!
# Error of the slab comparison profile

The clamped profile and a bounded solution agree at the right face. Their
weighted difference is controlled by the solution's energy and the weight of
the left boundary layer.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

private theorem integrable_weighted_sq_of_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure (ℝ × α)) [IsFiniteMeasure μ] (s b : ℝ) (hs : 0 ≤ s)
    (ht : ∀ᵐ p ∂μ, p.1 ≤ b) (f : ℝ × α → ℝ) (hf : Measurable f)
    (hbound : ∀ p, -1 ≤ f p ∧ f p ≤ 1) :
    Integrable (fun p => Real.exp (s * p.1) * (f p) ^ 2) μ := by
  have hm : Measurable (fun p : ℝ × α => Real.exp (s * p.1) * (f p) ^ 2) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_fst)).mul
      (hf.pow_const _)
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (s * b))
  filter_upwards [ht] with p hp
  have hsq : (f p) ^ 2 ≤ 1 := by
    have h := hbound p
    nlinarith [sq_nonneg (1 - f p), sq_nonneg (1 + f p)]
  have hw : Real.exp (s * p.1) ≤ Real.exp (s * b) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp hs)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  nlinarith [Real.exp_pos (s * p.1)]

/-- The weighted error between a bounded solution and the clamped comparison
profile is controlled by its energy on the same transverse section. -/
theorem slab_comparison_error_le_energy
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s lam Λ : ℝ) (hL : 1 ≤ L) (hs : 0 ≤ s) (hlam : 0 < lam)
    (K : Set (Fin n → ℝ)) (hK : MeasurableSet K) (hKfinite : volume K ≠ ∞)
    (hKsub : K ⊆ Icc (fun _ => -Real.exp (s * L / (n + 1)))
      (fun _ => Real.exp (s * L / (n + 1))))
    (hsub : coordinateIntervalBox n i (-L) L K ⊆ U)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hzero : ∀ x, 0 ≤ u x) (hone : ∀ x, u x ≤ 1)
    (hface : ∀ᵐ z ∂(volume.restrict K), u (centralSlabPoint n i (L, z)) = 1)
    (A : PDE.CoeffField (n + 1))
    (hEll : ∃ lam' Λ', PDE.IsEllipticFieldOn lam' Λ' U
      (fun x => Real.exp (s * x i) • A x))
    (hA : ∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (A x)) :
    Integrable (fun p => Real.exp (s * p.1) *
      (u (centralSlabPoint n i p) - slabBoundaryProfile hU i L (centralSlabPoint n i p)) ^ 2)
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict K)) ∧
    Integrable (fun p => PDE.vecDot
      (PDE.matVecMul (Real.exp (s * p.1) • A (centralSlabPoint n i p))
        (u.grad (centralSlabPoint n i p))) (u.grad (centralSlabPoint n i p)))
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict K)) ∧
    lam * (∫ p, Real.exp (s * p.1) *
      (u (centralSlabPoint n i p) - slabBoundaryProfile hU i L (centralSlabPoint n i p)) ^ 2
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict K))) ≤
      lam * (Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1)))) +
      (2 * L) ^ 2 * ∫ p,
        PDE.vecDot (PDE.matVecMul (Real.exp (s * p.1) • A (centralSlabPoint n i p))
          (u.grad (centralSlabPoint n i p))) (u.grad (centralSlabPoint n i p))
        ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict K)) := by
  let ν : Measure (Fin n → ℝ) := volume.restrict K
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hKfinite
  let μ : Measure (ℝ × (Fin n → ℝ)) := (volume.restrict (Icc (-L) L)).prod ν
  let : IsFiniteMeasure (volume.restrict (Icc (-L) L) : Measure ℝ) := by infer_instance
  let : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have he : Measurable (centralSlabPoint n i) := e.measurable
  let v : ℝ × (Fin n → ℝ) → ℝ := fun p => u (centralSlabPoint n i p)
  let w : ℝ × (Fin n → ℝ) → ℝ := fun p => min (max (p.1 + L) 0) 1
  have hv : Measurable v := hcont.measurable.comp he
  have hw : Measurable w := ((measurable_fst.add measurable_const).max measurable_const).min
    measurable_const
  have hv0 : ∀ p, 0 ≤ v p := fun p => hzero _
  have hv1 : ∀ p, v p ≤ 1 := fun p => hone _
  have hw0 : ∀ p, 0 ≤ w p := fun _ => le_min (le_max_right _ _) zero_le_one
  have hw1 : ∀ p, w p ≤ 1 := fun _ => min_le_right _ _
  have ht : ∀ᵐ p ∂μ, p.1 ≤ L := by
    have h := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Icc (-L) L))
      (ν := ν)).ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [h] with p hp
    exact hp.2
  have hdiff := integrable_weighted_sq_of_bounded μ s L hs ht (fun p => v p - w p)
    (hv.sub hw) (fun p => by constructor <;> linarith [hv0 p, hv1 p, hw0 p, hw1 p])
  have hu := integrable_weighted_sq_of_bounded μ s L hs ht (fun p => 1 - v p)
    (measurable_const.sub hv) (fun p => by constructor <;> linarith [hv0 p, hv1 p])
  have hp := integrable_weighted_sq_of_bounded μ s L hs ht (fun p => 1 - w p)
    (measurable_const.sub hw) (fun p => by constructor <;> linarith [hw0 p, hw1 p])
  have hcomp : (∫ p, Real.exp (s * p.1) * (v p - w p) ^ 2 ∂μ) ≤
      (∫ p, Real.exp (s * p.1) * (1 - v p) ^ 2 ∂μ) +
      ∫ p, Real.exp (s * p.1) * (1 - w p) ^ 2 ∂μ := by
    rw [← integral_add hu hp]
    apply integral_mono_ae hdiff (hu.add hp)
    filter_upwards with p
    have hprod := mul_nonneg (sub_nonneg.mpr (hv1 p)) (sub_nonneg.mpr (hw1 p))
    have hsq : (v p - w p) ^ 2 ≤ (1 - v p) ^ 2 + (1 - w p) ^ 2 := by nlinarith
    simpa only [Pi.add_apply, ← mul_add] using
      mul_le_mul_of_nonneg_left hsq (Real.exp_pos (s * p.1)).le
  have hprofile := (slab_profile_error_product_le n s L hs hL K hKfinite hKsub).2
  have henergy := coordinate_weighted_error_le_energy hU u i (-L) L s lam Λ
    (by linarith) hs hlam K hK hKfinite hsub hr hball hcont hzero hone hface A hEll hA
  have hprofile_eq : ∀ p, slabBoundaryProfile hU i L (centralSlabPoint n i p) = w p := by
    intro p
    rw [slabBoundaryProfile_apply]
    simp [w, centralSlabPoint, MeasurableEquiv.piFinSuccAbove_symm_apply]
  have hactual : Integrable (fun p => Real.exp (s * p.1) *
      (u (centralSlabPoint n i p) - slabBoundaryProfile hU i L (centralSlabPoint n i p)) ^ 2) μ := by
    apply hdiff.congr
    filter_upwards with p
    rw [hprofile_eq]
  have henergyint := (coordinate_weighted_gradient_le_energy u i (-L) L s lam Λ
    hs K hK hKfinite hsub A hEll hA).2.1
  refine ⟨hactual, henergyint, ?_⟩
  have htarget : (∫ p, Real.exp (s * p.1) *
      (u (centralSlabPoint n i p) - slabBoundaryProfile hU i L (centralSlabPoint n i p)) ^ 2
      ∂μ) = ∫ p, Real.exp (s * p.1) * (v p - w p) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with p
    rw [hprofile_eq]
  change lam * (∫ p, Real.exp (s * p.1) *
      (u (centralSlabPoint n i p) - slabBoundaryProfile hU i L (centralSlabPoint n i p)) ^ 2
      ∂μ) ≤ _
  rw [htarget]
  dsimp only [μ, ν, v, w] at hcomp hprofile henergy ⊢
  nlinarith [mul_le_mul_of_nonneg_left hcomp hlam.le,
    mul_le_mul_of_nonneg_left hprofile hlam.le]

end EinsteinFull.Regeneration
