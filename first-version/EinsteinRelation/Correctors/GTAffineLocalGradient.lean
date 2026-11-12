import EinsteinRelation.Correctors.GTHarmonicLocalGradient
import EinsteinRelation.Correctors.AffineLocalL2Bound

/-!
# Local bounds on the affine corrector gradient

Source: `paper/main.tex:735-739`. The three frozen GT inputs control
`e_i + grad u` by the local L² oscillation of `u` in any scalar gauge.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- The affine harmonic gradient has a uniform local bound depending only
on the scalar L² oscillation and the deterministic coefficient bounds. -/
theorem scalar_corrector_affine_local_gradient_bound_of_GT
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    (d : ℕ) (hd : 2 ≤ d) (lam Λ K α : ℝ)
    (hlam : 0 < lam) (hΛ : 0 < Λ) (hK : 0 < K)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Vec d → Mat d),
      EllipticBound (ball 0 4) a lam Λ →
      (∀ i j, HolderBound (ball 0 4) α (fun x => a x i j) K) →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d) (i : Fin d) (c : ℝ),
        MemLp (fun x => u x - c) 2 (volume.restrict (ball 0 4)) →
        WeakSolution (ball 0 4) a
          (fun x => x i + u x - c) (fun x => unitVector i + g x) →
        ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1),
          euclideanNorm (unitVector i + g x) ≤ C * (1 +
            Real.sqrt (∫ z in ball 0 4, |u z - c| ^ 2 ∂volume)) := by
  obtain ⟨A, hA, hest⟩ := harmonic_local_gradient_bound_of_GT
    h817 h832 h836 d hd lam Λ K α hlam hΛ hK hα hα1
  obtain ⟨B, hB, hroot⟩ := sqrt_integral_affine_radius_four_le d
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro a ha hh u g i c hu hw
  filter_upwards [hest a ha hh _ _ hw] with x hx
  exact hx.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hroot u i c hu hw.1) hA.le)

end EinsteinRelation.Correctors
