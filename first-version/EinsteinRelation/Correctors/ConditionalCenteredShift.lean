import EinsteinRelation.Correctors.ConditionalCenteredCoordinateTransport
import Mathlib.MeasureTheory.Group.Integral

/-! Literal source centering after translating coordinates, used in
`paper/main.tex:872–894`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport

/-- A single literal centered observable in coordinates translated by its
source center. Source: `paper/main.tex:872–894`. -/
theorem conditionalCentered_coordinates {d : ℕ}
    (ζ : SourceMollifier d) (R : ℝ) (y : Point d)
    (φ : FieldPair d → Point d → ℝ) (σ : FieldPair d → Vec d → Mat d)
    (ω : FieldPair d) :
    let w : Vec d → ℝ := fun x =>
      sourceScaledMollifierKernel ζ R y (WithLp.toLp 2 (x+y.ofLp))
    conditionalCenteredScalar ζ R y φ ω = φ ω y -
      ∫ x, w x * φ ω (WithLp.toLp 2 (x+y.ofLp)) ∧
    conditionalCenteredSkew ζ R y σ ω = Matrix.of (fun a b =>
      σ ω y.ofLp a b - ∫ x, w x * σ ω (x+y.ofLp) a b) := by
  constructor
  · unfold conditionalCenteredScalar
    rw [integral_sourceMollifier_coordinate]
    congr 1
    exact (integral_add_right_eq_self _ y.ofLp).symm
  · ext a b
    change σ ω y.ofLp a b - _ = _
    rw [integral_sourceMollifier_coordinate]
    congr 1
    exact (integral_add_right_eq_self _ y.ofLp).symm

/-- The actual scalar and matrix copy differences, with the same source
kernel and the evaluation point translated to zero. Source:
`paper/main.tex:872–894`. -/
theorem conditionalCentered_copy_shift {d : ℕ}
    (ζ : SourceMollifier d) {R : ℝ} (hR : 1 ≤ R) (y : Point d)
    (φ : FieldPair d → Point d → ℝ) (σ : FieldPair d → Vec d → Mat d)
    (ω₁ ω₂ : FieldPair d)
    (hφ₁ : LocallyIntegrable (φ ω₁) volume)
    (hφ₂ : LocallyIntegrable (φ ω₂) volume)
    (hσ₁ : ∀ a b, LocallyIntegrable (fun x => σ ω₁ x a b) volume)
    (hσ₂ : ∀ a b, LocallyIntegrable (fun x => σ ω₂ x a b) volume) :
    let w : Vec d → ℝ := fun x =>
      sourceScaledMollifierKernel ζ R y (WithLp.toLp 2 (x+y.ofLp))
    (conditionalCenteredScalar ζ R y φ ω₁ - conditionalCenteredScalar ζ R y φ ω₂ =
      (φ ω₁ y - φ ω₂ y) - ∫ x, w x *
        (φ ω₁ (WithLp.toLp 2 (x+y.ofLp)) - φ ω₂ (WithLp.toLp 2 (x+y.ofLp)))) ∧
    (conditionalCenteredSkew ζ R y σ ω₁ - conditionalCenteredSkew ζ R y σ ω₂ =
      Matrix.of (fun a b => (σ ω₁ y.ofLp a b - σ ω₂ y.ofLp a b) - ∫ x, w x *
        (σ ω₁ (x+y.ofLp) a b - σ ω₂ (x+y.ofLp) a b))) := by
  constructor
  · rw [conditionalCenteredScalar_copy_difference ζ R hR y φ ω₁ ω₂ hφ₁ hφ₂]
    congr 1
    exact (integral_add_right_eq_self _ y.ofLp).symm
  · have h := conditionalCenteredSkew_copy_difference ζ R hR y σ ω₁ ω₂ hσ₁ hσ₂
    change conditionalCenteredSkew ζ R y σ ω₁ - conditionalCenteredSkew ζ R y σ ω₂ = _ at h
    rw [h]
    ext a b
    change (σ ω₁ y.ofLp a b - σ ω₂ y.ofLp a b) - _ = _
    congr 1
    exact (integral_add_right_eq_self _ y.ofLp).symm
end EinsteinRelation.Correctors
