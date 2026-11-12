import EinsteinRelation.Correctors.PairedPDEPlanarEquation
import EinsteinRelation.Correctors.PairedPDEGradientLp
import EinsteinRelation.TimeChange.Pairing

/-! # Euclidean energy transfer to the planar skew entry

Source: `paper/main.tex:880–883`. The actual weak skew gradient inherits
square integrability and the corresponding local energy comparison from
the ordinary paired gradient.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The planar skew gradient belongs to L² whenever the paired ordinary
gradient does. The weak equation supplies measurability rather than an
extra pointwise coefficient measurability assumption.
Source: `paper/main.tex:880–883`. -/
theorem planar_rotated_flux_memLp {U : Set (Vec 2)} (hU : IsOpen U)
    {L : ℝ} (hL : 0 < L) {a : Vec 2 → Mat 2} (ha : IsElliptic L a)
    {σ : Vec 2 → ℝ} {H G : Vec 2 → Vec 2}
    (hσ : HasWeakGradient U σ H)
    (hH : Set.EqOn H (fun x => planarRotation.mulVec ((a x).mulVec (G x))) U)
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U)) :
    MemLp (fun x => euclideanNorm (H x)) 2 (volume.restrict U) := by
  apply memLp_euclideanNorm_of_weakGradient_domination hU hσ hG hL.le
  intro x hx
  rw [hH hx]
  exact planar_rotated_flux_euclideanNorm_le hL ha x (G x)

/-- The local skew energy is at most `L²` times the ordinary paired
energy in the exact Euclidean quadratic form.
Source: `paper/main.tex:880–883`. -/
theorem planar_rotated_flux_energy_le {U : Set (Vec 2)} (hU : IsOpen U)
    {L : ℝ} (hL : 0 < L) {a : Vec 2 → Mat 2} (ha : IsElliptic L a)
    {σ : Vec 2 → ℝ} {H G : Vec 2 → Vec 2}
    (hσ : HasWeakGradient U σ H)
    (hH : Set.EqOn H (fun x => planarRotation.mulVec ((a x).mulVec (G x))) U)
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U)) :
    (∫ x in U, euclideanSq (H x)) ≤ L^2 * ∫ x in U, euclideanSq (G x) := by
  have hH2 := planar_rotated_flux_memLp hU hL ha hσ hH hG
  have hiH : Integrable (fun x => euclideanSq (H x)) (volume.restrict U) := by
    simpa only [TimeChange.euclideanSq_eq_sq_euclideanNorm] using hH2.integrable_sq
  have hiG : Integrable (fun x => euclideanSq (G x)) (volume.restrict U) := by
    simpa only [TimeChange.euclideanSq_eq_sq_euclideanNorm] using hG.integrable_sq
  calc
    (∫ x in U, euclideanSq (H x)) ≤ ∫ x in U, L^2 * euclideanSq (G x) := by
      apply integral_mono_ae hiH (hiG.const_mul (L^2))
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      have hn := planar_rotated_flux_euclideanNorm_le hL ha x (G x)
      have he := hH hx
      dsimp only at he
      rw [← he] at hn
      have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hL.le (Real.sqrt_nonneg _))).2 hn
      rw [TimeChange.euclideanSq_eq_sq_euclideanNorm (H x),
        TimeChange.euclideanSq_eq_sq_euclideanNorm (G x)]
      simpa only [mul_pow] using hs
    _ = L^2 * ∫ x in U, euclideanSq (G x) := integral_const_mul _ _

end EinsteinRelation.Correctors
