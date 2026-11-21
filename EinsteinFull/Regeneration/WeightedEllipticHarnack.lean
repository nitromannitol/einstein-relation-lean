import EinsteinFull.Regeneration.EllipticCoefficientScaling

/-!
# Harnack comparison for weighted elliptic equations

A bounded positive weight can be normalized before applying elliptic Harnack.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- Continuous weighted elliptic solutions satisfy uniform pointwise Harnack comparison. -/
theorem weighted_elliptic_pointwise_harnack (d : ℕ) (hd : 0 < d)
    (lam Λ m M : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (hΛ : lam ≤ Λ) (hM : m ≤ M) :
    ∃ H : ℝ, 2 ≤ H ∧ ∀ (θ : ℝ), 0 < θ →
      ∀ z z' : PDE.Vec d, PDE.euclideanSqDist z z' ≤ θ / 4 →
      let U := PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ))
      ∀ (a : PDE.CoeffField d) (w : PDE.Vec d → ℝ),
      (∀ i j, AEMeasurable (fun x => a x i j) (volume.restrict U)) →
      AEMeasurable w (volume.restrict U) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) →
      (∀ᵐ x ∂(volume.restrict U), m ≤ w x ∧ w x ≤ M) →
      ∀ u : PDE.H1Function U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => w x • a x) U u 0 0 →
      Continuous u.toFun → (∀ x, 0 ≤ u.toFun x) → u z ≤ H * u z' := by
  have hml : 0 < m * lam := mul_pos hm hlam
  have hbig : m * lam ≤ M * Λ := mul_le_mul hM hΛ hlam.le (hm.trans_le hM).le
  have hratio : 1 ≤ (m * lam)⁻¹ * (M * Λ) := by
    have h := mul_le_mul_of_nonneg_left hbig (inv_pos.mpr hml).le
    simpa only [inv_mul_cancel₀ hml.ne'] using h
  obtain ⟨H, hH, hcomp⟩ := elliptic_pointwise_harnack_of_spatial_coeff d hd
    ((m * lam)⁻¹ * (M * Λ)) hratio
  refine ⟨H, hH, ?_⟩
  intro θ hθ z z' hdist
  dsimp only
  intro a w hmeas hwmeas hell hw u hsol hcont hnonneg
  let U := PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ))
  let b : PDE.CoeffField d := fun x => ((m * lam)⁻¹ * w x) • a x
  obtain ⟨hbmeas, hbell⟩ := normalized_weighted_ellipticity U a w lam Λ m M hlam hm
    hmeas hwmeas hell hw
  have hbmeas' : ∀ i j, AEMeasurable (fun x => b x i j) (volume.restrict U) := by
    intro i j
    change AEMeasurable (fun x => ((m * lam)⁻¹ * w x) * a x i j) _
    exact hbmeas i j
  have hsol' : PDE.IsWeakDivergenceFormL2SolutionOn b U u 0 0 := by
    simpa only [b, smul_smul] using elliptic_l2_solution_smul_coefficient
      (fun x => w x • a x) u hsol (m * lam)⁻¹
  exact hcomp b θ hθ z z' hdist hbmeas' hbell u hsol' hcont hnonneg

end EinsteinFull.Regeneration
