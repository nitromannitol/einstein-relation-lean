import EinsteinFull.Regeneration.CoordinateWeightedGradient
import EinsteinFull.Regeneration.SlabProfileGradient

/-!
# Gradient error in the slab comparison

The weighted gradient terms in the slab cutoff argument are controlled by the
solution's elliptic energy and the left boundary-layer weight.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The gradient terms in GMP (4.23) have the claimed energy bound on every
finite transverse section contained in the comparison cube. -/
theorem slab_comparison_gradient_le_energy
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s lam Λ : ℝ) (hL : 1 ≤ L) (hs : 0 ≤ s) (hlam : 0 < lam)
    (K : Set (Fin n → ℝ)) (hK : MeasurableSet K) (hKfinite : volume K ≠ ∞)
    (hKsub : K ⊆ Icc (fun _ => -Real.exp (s * L / (n + 1)))
      (fun _ => Real.exp (s * L / (n + 1))))
    (hsub : coordinateIntervalBox n i (-L) L K ⊆ U)
    (A : PDE.CoeffField (n + 1))
    (hEll : ∃ lam' Λ', PDE.IsEllipticFieldOn lam' Λ' U
      (fun x => Real.exp (s * x i) • A x))
    (hA : ∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (A x)) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => Real.exp (s * p.1) *
      (PDE.vecNormSq (u.grad (centralSlabPoint n i p)) +
        PDE.vecNormSq ((slabBoundaryProfile hU i L).grad (centralSlabPoint n i p))))
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict K)) ∧
    lam * (∫ p : ℝ × (Fin n → ℝ), Real.exp (s * p.1) *
      (PDE.vecNormSq (u.grad (centralSlabPoint n i p)) +
        PDE.vecNormSq ((slabBoundaryProfile hU i L).grad (centralSlabPoint n i p)))
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict K))) ≤
      lam * (Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1)))) +
      ∫ p, PDE.vecDot (PDE.matVecMul (Real.exp (s * p.1) • A (centralSlabPoint n i p))
        (u.grad (centralSlabPoint n i p))) (u.grad (centralSlabPoint n i p))
        ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict K)) := by
  obtain ⟨hu, _, henergy⟩ := coordinate_weighted_gradient_le_energy u i (-L) L s lam Λ
    hs K hK hKfinite hsub A hEll hA
  obtain ⟨hv, hprofile⟩ := slab_profile_gradient_product_le hU i s L hs hL K hKfinite hKsub
  have hsum : Integrable (fun p : ℝ × (Fin n → ℝ) => Real.exp (s * p.1) *
      (PDE.vecNormSq (u.grad (centralSlabPoint n i p)) +
        PDE.vecNormSq ((slabBoundaryProfile hU i L).grad (centralSlabPoint n i p))))
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict K)) := by
    convert hu.add hv using 1
    ext p
    simp only [Pi.add_apply, mul_add]
  refine ⟨hsum, ?_⟩
  have heq : (∫ p : ℝ × (Fin n → ℝ), Real.exp (s * p.1) *
      (PDE.vecNormSq (u.grad (centralSlabPoint n i p)) +
        PDE.vecNormSq ((slabBoundaryProfile hU i L).grad (centralSlabPoint n i p)))
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict K))) =
      (∫ p, Real.exp (s * p.1) * PDE.vecNormSq (u.grad (centralSlabPoint n i p))
        ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict K))) +
      ∫ p, Real.exp (s * p.1) *
        PDE.vecNormSq ((slabBoundaryProfile hU i L).grad (centralSlabPoint n i p))
        ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict K)) := by
    simpa only [Pi.add_apply, ← mul_add] using integral_add hu hv
  rw [heq, mul_add]
  linarith [mul_le_mul_of_nonneg_left hprofile hlam.le]

end EinsteinFull.Regeneration
