import EinsteinRelation.Environment.Smooth
import EinsteinRelation.Sharpness.SmoothFields
import EinsteinRelation.Sharpness.PhysicalEnvironment

/-! The literal constructed physical pair satisfies the smoothness predicate
of `sharp.example` (`paper/main.tex:1202–1231`). This does not construct its law.
-/

namespace EinsteinRelation.Sharpness

/-- Smoothness of the actual physical pair, with its actual gradient and clock
density. Continuity witnesses only certify membership in the canonical carrier. -/
theorem isSmoothFieldPair_physicalEnvironment {d : ℕ} (i : Fin d) (δ : ℝ)
    (ψ : Vec d → ℝ) (ha : Continuous (physicalCoefficientField i δ ψ))
    (hV : Continuous (potentialField i δ ψ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hj : ∀ x, jacobianFactor i (gradient ψ x) ≠ 0)
    (hμ : ∀ x, 0 < densityField i δ ψ x) :
    IsSmoothFieldPair (physicalEnvironment i δ ψ ha hV) :=
  contDiff_physicalFields i δ ψ hψ hj hμ

end EinsteinRelation.Sharpness
