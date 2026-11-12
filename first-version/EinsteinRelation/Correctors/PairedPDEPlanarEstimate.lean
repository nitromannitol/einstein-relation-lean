import EinsteinRelation.Correctors.PairedPDEPlanarEnergy
import EinsteinRelation.Correctors.PairedPDEPlanarEllipticity

/-! # Joint planar skew equation and energy comparison

Source: `paper/main.tex:874–883`. The paired skew entry, its dual
coefficient, its actual weak gradient, and its energy bound stay joint.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The planar paired skew entry solves the uniformly elliptic dual equation
and inherits the paired ordinary-gradient energy, for the manuscript's
coefficient and row-divergence conventions. Source: `paper/main.tex:874–883`. -/
theorem paired_planar_fluxCorrector_dual_energy {U : Set (Vec 2)} (hU : IsOpen U)
    {L : ℝ} (hL : 0 < L) {a₁ a₂ : Vec 2 → Mat 2}
    (hell : IsElliptic L a₁) (ha : Set.EqOn a₁ a₂ U) (e m : Vec 2)
    {φ₁ φ₂ : Vec 2 → ℝ} {G₁ G₂ : Vec 2 → Vec 2} {S₁ S₂ : Vec 2 → Mat 2}
    (hφ₁ : HasWeakGradient U φ₁ G₁) (hφ₂ : HasWeakGradient U φ₂ G₂)
    (hS₁ : ∀ x, (S₁ x).transpose = -(S₁ x))
    (hS₂ : ∀ x, (S₂ x).transpose = -(S₂ x))
    (h₁ : HasWeakRowDivergence U S₁ (fun x => (a₁ x).mulVec (e + G₁ x) - m))
    (h₂ : HasWeakRowDivergence U S₂ (fun x => (a₂ x).mulVec (e + G₂ x) - m))
    (hG : MemLp (fun x => euclideanNorm (G₁ x - G₂ x)) 2 (volume.restrict U)) :
    let G := fun x => G₁ x - G₂ x
    let H := fun x => planarRotation.mulVec ((a₁ x).mulVec (G x))
    let b := fun x => planarRotation * (a₁ x)⁻¹ * planarRotation.transpose
    IsElliptic L b ∧
      HasWeakGradient U (fun x => S₁ x 0 1 - S₂ x 0 1) H ∧
      HasWeakDivergence U (fun x => (b x).mulVec (H x)) (fun _ => 0) ∧
      MemLp (fun x => euclideanNorm (H x)) 2 (volume.restrict U) ∧
      (∫ x in U, euclideanSq (H x)) ≤ L^2 * ∫ x in U, euclideanSq (G x) := by
  have hpair := paired_planar_fluxCorrector_harmonic hU hL hell ha e m
    hφ₁ hφ₂ hS₁ hS₂ h₁ h₂
  refine ⟨isElliptic_planar_dual hL hell, hpair.1, hpair.2, ?_, ?_⟩
  · exact planar_rotated_flux_memLp hU hL hell hpair.1 (fun _ _ => rfl) hG
  · exact planar_rotated_flux_energy_le hU hL hell hpair.1 (fun _ _ => rfl) hG

end EinsteinRelation.Correctors
