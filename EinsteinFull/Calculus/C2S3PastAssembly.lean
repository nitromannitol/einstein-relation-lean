import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS1PastFiniteHistory

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.Regeneration

/-- Conditional assembly of the past-kernel node from the supported scalar
comparison for the actual supplied GMP realizations. This is support only until
the comparison is established. -/
theorem c2_past_kernel_of_supported_scalar_comparison
    (hcompare : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
      (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
      (lam l δ : ℝ) (hl : 0 < l) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K)
      (v : ℝ),
      let R := l / lam
      let i := Renewal.forceCoord hd
      let Δ := Renewal.regenDelta lam
      ∀ (ω ω' : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
        (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
        (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω) hω lam h0.le h1)
        (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω') hω' lam h0.le h1),
        (∀ y : Vec d, P (y, ω) = r.pathLaw y) →
        (∀ y : Vec d, P (y, ω') = r'.pathLaw y) →
        (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
        ∀ F : Path d → ℝ, Measurable F → BoundedRealTest F →
        (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') →
        (∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) →
        ∀ y : Vec d, y i ≤ v →
        (∫ γ, F γ ∂P (y, ω)) = (∫ γ, F γ ∂P (y, ω')) ∧
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω) =
          ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω') :
    node_app_u3A_factorization_u23_past_u2D_kernelStmt := by
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ _hl _hr _hδ _hδ1 P K hK R i Δ m v H hH hHb hHs
  exact PastFiniteHistory.exists_local_past_integral_version_of_gmp_scalar_comparison
    hd Q.ellipticity_parameter Q lam l δ h0 h1 P K hK v
    (hcompare hd Q.ellipticity_parameter Q lam l δ _hl h0 h1 P K hK v)
    m H hH hHb hHs

/-- Conditional past-kernel assembly from locality of the supplied stopped laws. -/
theorem c2_s3_past_kernel_of_requested_locality (requested_s3_past_supplied_stopped_locality : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (hl : 0 < l) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K) (v : ℝ), let R := l / lam
      let i := Renewal.forceCoord hd
      let Δ := Renewal.regenDelta lam
      ∀ (ω ω' : FieldPair d) (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω)) (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω')) (r : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω lam h0.le h1) (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω') hω' lam h0.le h1), (∀ y : Vec d, P (y, ω) = r.pathLaw y) → (∀ y : Vec d, P (y, ω') = r'.pathLaw y) → (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) → ∀ y : Vec d, y i ≤ v → (r.pathLaw y).map (Diffusion.localityStoppedPath {x : Vec d | x i < v + 3 * R}) = (r'.pathLaw y).map (Diffusion.localityStoppedPath {x : Vec d | x i < v + 3 * R})) : node_app_u3A_factorization_u23_past_u2D_kernelStmt := by
  apply c2_past_kernel_of_supported_scalar_comparison
  intro d hd Λ₀ r₀ hΛ₀ Q lam l δ hl h0 h1 P K hK v
  dsimp only
  intro ω ω' hω hω' r r' hr hr' hagree F hF _ hsegment hsupport y hy
  have hstop := requested_s3_past_supplied_stopped_locality hd hΛ₀ Q lam l δ
    hl h0 h1 P K hK v ω ω' hω hω' r r' hr hr' hagree y hy
  rw [← hr y, ← hr' y] at hstop
  exact PastFiniteHistory.integral_pair_eq_of_locality_stopped_law_eq
    (Renewal.regenDelta lam) (l / lam) v (div_pos hl h0) (Renewal.forceCoord hd)
    P y ω ω' hstop F hF hsegment hsupport

end EinsteinFull.Blueprint
