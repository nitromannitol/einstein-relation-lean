import EinsteinFull.Regeneration.GMPForceHarnack
import EinsteinRelation.External.GantertSection7Support

/-!
# Central-cube Harnack for the physical force weight

The physical generator's unit-force reversible weight is `exp (2 x₁)`.
-/

open MeasureTheory Set EinsteinRelation
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The physical unit-force equation has a uniform central-cube complement bound. -/
theorem gmp_physical_central_cube_complement_lower (d : ℕ) (hd : 2 ≤ d)
    (lam Λ : ℝ) (hlam : 0 < lam) (hΛ : lam ≤ Λ) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : PDE.Vec d, z (firstCoordinateIndex hd) = 0 →
      (∀ j, |z j| ≤ 1) →
      let U := PDE.euclideanBall ((1 / 2 : ℝ) • ((0 : PDE.Vec d) + z))
        (Real.sqrt (8 * d))
      ∀ a : PDE.CoeffField d,
      (∀ j k, AEMeasurable (fun x => a x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) →
      ∀ u : PDE.H1Function U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => physicalForceWeight hd 1 x • a x)
        U u 0 0 →
      Continuous u.toFun → (∀ x, u x ≤ 1) → u 0 < 2 / 3 → c ≤ 1 - u z := by
  obtain ⟨c, hc, hbound⟩ :=
    gmp_central_cube_complement_lower_of_force d (by omega) lam Λ 2 hlam hΛ (by norm_num)
  refine ⟨c, hc, ?_⟩
  intro z hz hcube
  dsimp only
  intro a hmeas hell u hsol hcont hupper hsmall
  have h := hbound (firstCoordinateIndex hd) z hz hcube
  dsimp only at h
  apply h a hmeas hell u
  · simpa only [physicalForceWeight, mul_one] using hsol
  · exact hcont
  · exact hupper
  · exact hsmall

end EinsteinFull.Regeneration
