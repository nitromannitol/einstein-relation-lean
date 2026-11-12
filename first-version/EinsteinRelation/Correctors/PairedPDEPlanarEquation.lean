import EinsteinRelation.Correctors.PairedPDEPlanarRotation
import EinsteinRelation.Correctors.PairedCorrectorEquation
import EinsteinRelation.Correctors.EllipticOperatorBound

/-! # The planar paired skew equation

Source: `paper/main.tex:874–883`. The gradient of the independent skew
entry is the rotated flux. Applying the rotated inverse coefficient gives
a rotated ordinary gradient, whose weak divergence vanishes.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- A rotated flux satisfies the dual homogeneous equation on an open
region. No smoothness of the original potential is needed.
Source: `paper/main.tex:877–880`. -/
theorem planar_dual_harmonic_of_weakGradient {U : Set (Vec 2)} (hU : IsOpen U)
    {L : ℝ} (hL : 0 < L) {a : Vec 2 → Mat 2} (ha : IsElliptic L a)
    {w : Vec 2 → ℝ} {G H : Vec 2 → Vec 2}
    (hw : HasWeakGradient U w G)
    (hH : Set.EqOn H (fun x => planarRotation.mulVec ((a x).mulVec (G x))) U) :
    HasWeakDivergence U
      (fun x => (planarRotation * (a x)⁻¹ * planarRotation.transpose).mulVec (H x))
      (fun _ => 0) := by
  apply hasWeakDivergence_congr_ae hU
    (hasWeakDivergence_planar_rotated_gradient w G hw) ?_ Filter.EventuallyEq.rfl
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  rw [hH hx, ← planar_dual_orientation, planar_dual_flux (a x) (isElliptic_isUnit_det hL ha x)]
  exact (planarRotation_mulVec (G x)).symm

/-- The independent difference of two planar skew correctors is a genuine
weak solution of the dual homogeneous equation on the coefficient-agreement
region. The ordinary gradients and skew row-divergences are the only PDE
premises. Source: `paper/main.tex:874–883`. -/
theorem paired_planar_fluxCorrector_harmonic {U : Set (Vec 2)} (hU : IsOpen U)
    {L : ℝ} (hL : 0 < L) {a₁ a₂ : Vec 2 → Mat 2}
    (hell : IsElliptic L a₁) (ha : Set.EqOn a₁ a₂ U) (e m : Vec 2)
    {φ₁ φ₂ : Vec 2 → ℝ} {G₁ G₂ : Vec 2 → Vec 2} {S₁ S₂ : Vec 2 → Mat 2}
    (hφ₁ : HasWeakGradient U φ₁ G₁) (hφ₂ : HasWeakGradient U φ₂ G₂)
    (hS₁ : ∀ x, (S₁ x).transpose = -(S₁ x))
    (hS₂ : ∀ x, (S₂ x).transpose = -(S₂ x))
    (h₁ : HasWeakRowDivergence U S₁ (fun x => (a₁ x).mulVec (e + G₁ x) - m))
    (h₂ : HasWeakRowDivergence U S₂ (fun x => (a₂ x).mulVec (e + G₂ x) - m)) :
    HasWeakGradient U (fun x => S₁ x 0 1 - S₂ x 0 1)
        (fun x => planarRotation.mulVec ((a₁ x).mulVec (G₁ x - G₂ x))) ∧
      HasWeakDivergence U
        (fun x => (planarRotation * (a₁ x)⁻¹ * planarRotation.transpose).mulVec
          (planarRotation.mulVec ((a₁ x).mulVec (G₁ x - G₂ x))))
        (fun _ => 0) := by
  constructor
  · simpa only [planarRotation_mulVec] using
      paired_planar_fluxCorrector_gradient hU ha e m hS₁ hS₂ h₁ h₂
  · exact planar_dual_harmonic_of_weakGradient hU hL hell
      (hasWeakGradient_sub hφ₁ hφ₂) (fun _ _ => rfl)

/-- The skew gradient is controlled in the Euclidean norm with the original
ellipticity constant. This is the deterministic comparison in the last
sentence of Step 3. Source: `paper/main.tex:880–883`. -/
theorem planar_rotated_flux_euclideanNorm_le {L : ℝ} (hL : 0 < L)
    {a : Vec 2 → Mat 2} (ha : IsElliptic L a) (x v : Vec 2) :
    euclideanNorm (planarRotation.mulVec ((a x).mulVec v)) ≤
      L * euclideanNorm v := by
  unfold euclideanNorm at *
  rw [euclideanSq_planarRotation]
  exact isElliptic_mulVec_euclideanNorm_le hL ha x v

end EinsteinRelation.Correctors
