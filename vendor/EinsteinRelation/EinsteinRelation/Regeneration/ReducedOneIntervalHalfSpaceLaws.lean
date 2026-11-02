import EinsteinRelation.Regeneration.OneIntervalHalfSpaceLaws

/-!
# One-interval locality for the actual reduced diffusion

Source `paper/main.tex:199–208,265,377–381`. The GMP reduced path law is
realized on the zero-potential pair `(exp(-2V) a₀, 0)`, while the coupled
kernel is indexed by the original physical pair. The transport below
retains these distinct objects and pulls locality back through the
pointwise coefficient reduction.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

/-- Keep the actual environment parameter fixed while changing the
auxiliary environment index used in the fixed-realization calculation. -/
private def fixedEnvironmentKernel {d : ℕ} (P : QuenchedPathLaws d)
    (ω : FieldPair d) : QuenchedPathLaws d :=
  P.comap (fun xψ => (xψ.1, ω)) (measurable_fst.prodMk measurable_const)

private theorem zeroPotentialReducedPair_eq_on {d : ℕ}
    (ω ω' : FieldPair d) (U : Set (Vec d))
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) :
    ∀ y ∈ U, (zeroPotentialReducedPair ω).1 y = (zeroPotentialReducedPair ω').1 y ∧
      (zeroPotentialReducedPair ω).2 y = (zeroPotentialReducedPair ω').2 y := by
  intro y hy
  obtain ⟨ha, hV⟩ := heq y hy
  refine ⟨?_, rfl⟩
  change Real.exp (-2 * ω.2 y) • ω.1 y = Real.exp (-2 * ω'.2 y) • ω'.1 y
  rw [ha, hV]

section

variable (hLoc : External.GMPKernelLocality)
  {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
  (ω ω' : FieldPair d)
  (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
  (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
  (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
  (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
    hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
    (zeroPotentialReducedPair ω) hω lam h0 h1)
  (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
    hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
    (zeroPotentialReducedPair ω') hω' lam h0 h1)
  (P P' : QuenchedPathLaws d) (z : Vec d)
  (hP : P (z, ω) = r.pathLaw z) (hP' : P' (z, ω') = r'.pathLaw z)
  (Δ : ℝ≥0) (R : ℝ) (hR : 0 < R) (i : Fin d)

include hLoc hP hP' hR

/-- Past one-interval locality on the physical environment parameter,
using the exact zero-potential reduced realizations in `IsGMPReducedKernel`. -/
theorem reduced_oneInterval_past_integrals_eq_of_locality (v : ℝ) (hz : z i ≤ v)
    (heq : ∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (F : Path d → ℝ) (hF : Measurable F)
    (hsegment : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ')
    (hsupport : ∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) :
    (∫ γ, F γ ∂P (z, ω)) = (∫ γ, F γ ∂P' (z, ω')) ∧
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω) =
        ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P' z ω' := by
  have heq' := zeroPotentialReducedPair_eq_on ω ω' {y | y i ≤ v + 3 * R} heq
  exact oneInterval_past_integrals_eq_of_locality hLoc hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) (zeroPotentialReducedPair ω')
    hω hω' lam h0 h1 r r' (fixedEnvironmentKernel P ω) (fixedEnvironmentKernel P' ω')
    z hP hP' Δ R hR i v hz heq' F hF hsegment hsupport

/-- Future one-interval locality on the physical environment parameter,
again transporting the reduced law rather than identifying physical and reduced coefficients. -/
theorem reduced_oneInterval_future_integrals_eq_of_locality (hz : -R ≤ z i)
    (heq : ∀ y : Vec d, -2 * R ≤ y i → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (F : Path d → ℝ) (hF : Measurable F)
    (hsegment : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ')
    (hsupport : ∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → -R ≤ γ t i) :
    (∫ γ, F γ ∂P (z, ω)) = (∫ γ, F γ ∂P' (z, ω')) ∧
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω) =
        ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P' z ω' := by
  have heq' := zeroPotentialReducedPair_eq_on ω ω' {y | -2 * R ≤ y i} heq
  exact oneInterval_future_integrals_eq_of_locality hLoc hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) (zeroPotentialReducedPair ω')
    hω hω' lam h0 h1 r r' (fixedEnvironmentKernel P ω) (fixedEnvironmentKernel P' ω')
    z hP hP' Δ R hR i hz heq' F hF hsegment hsupport

end


end EinsteinRelation.Regeneration
