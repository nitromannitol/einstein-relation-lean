import EinsteinRelation.Correctors.CorrectorConditionalStatement
import EinsteinRelation.Correctors.PlanarCenteredSkewNorm

/-! # Literal mollifier centering in the weak-equation coordinates

Source: `paper/main.tex:864–886`. These identities retain the source
mollifier and its Euclidean volume. They let the paired planar estimate
consume the same centered scalar and tensor observables as Lemma 5.2.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport

/-- The exact source mollifier integral is unchanged by the coordinate
identification, for every scalar integrand. Source: `paper/main.tex:864–875`. -/
theorem integral_sourceMollifier_coordinate {d : ℕ} (ζ : SourceMollifier d)
    (R : ℝ) (y : Point d) (u : Point d → ℝ) :
    (∫ z : Point d, sourceScaledMollifierKernel ζ R y z * u z) =
      ∫ x : Vec d, sourceScaledMollifierKernel ζ R y (WithLp.toLp 2 x) *
        u (WithLp.toLp 2 x) := by
  exact ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).symm.measurableEmbedding
    (fun z => sourceScaledMollifierKernel ζ R y z * u z)).symm

/-- Actual scalar copy observables equal the centered difference estimated
by the planar weak PDE. Only local integrability of each scalar is needed.
Source: `paper/main.tex:864–886`. -/
theorem conditionalCenteredScalar_copy_difference {d : ℕ}
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
    (φ : FieldPair d → Point d → ℝ) (ω₁ ω₂ : FieldPair d)
    (hφ₁ : LocallyIntegrable (φ ω₁) volume)
    (hφ₂ : LocallyIntegrable (φ ω₂) volume) :
    conditionalCenteredScalar ζ R y φ ω₁ - conditionalCenteredScalar ζ R y φ ω₂ =
      (φ ω₁ y - φ ω₂ y) -
        ∫ x : Vec d, sourceScaledMollifierKernel ζ R y (WithLp.toLp 2 x) *
          (φ ω₁ (WithLp.toLp 2 x) - φ ω₂ (WithLp.toLp 2 x)) := by
  have hi₁ := hφ₁.integrable_smul_left_of_hasCompactSupport
    (continuous_sourceScaledMollifierKernel ζ R y)
    (hasCompactSupport_sourceScaledMollifierKernel ζ hR y)
  have hi₂ := hφ₂.integrable_smul_left_of_hasCompactSupport
    (continuous_sourceScaledMollifierKernel ζ R y)
    (hasCompactSupport_sourceScaledMollifierKernel ζ hR y)
  change (φ ω₁ y - ∫ z, sourceScaledMollifierKernel ζ R y z * φ ω₁ z) -
    (φ ω₂ y - ∫ z, sourceScaledMollifierKernel ζ R y z * φ ω₂ z) = _
  rw [centered_pair_subtraction volume (φ ω₁) (φ ω₂)
    (sourceScaledMollifierKernel ζ R y) y hi₁ hi₂,
    integral_sourceMollifier_coordinate]

/-- The tensor centering is entrywise the very same source mollifier;
coordinate transport and subtraction require no pointwise modification.
Source: `paper/main.tex:869–886`. -/
theorem conditionalCenteredSkew_copy_difference {d : ℕ}
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
    (σ : FieldPair d → Vec d → Mat d) (ω₁ ω₂ : FieldPair d)
    (hσ₁ : ∀ a b, LocallyIntegrable (fun x => σ ω₁ x a b) volume)
    (hσ₂ : ∀ a b, LocallyIntegrable (fun x => σ ω₂ x a b) volume) :
    Matrix.of (fun a b => conditionalCenteredSkew ζ R y σ ω₁ a b -
      conditionalCenteredSkew ζ R y σ ω₂ a b) =
      Matrix.of (fun a b => (σ ω₁ (WithLp.ofLp y) a b - σ ω₂ (WithLp.ofLp y) a b) -
        ∫ x : Vec d, sourceScaledMollifierKernel ζ R y (WithLp.toLp 2 x) *
          (σ ω₁ x a b - σ ω₂ x a b)) := by
  have hc := (continuous_sourceScaledMollifierKernel ζ R y).comp
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  have hs := (hasCompactSupport_sourceScaledMollifierKernel ζ hR y).comp_homeomorph
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).symm
  ext a b
  change (σ ω₁ (WithLp.ofLp y) a b -
    ∫ z, sourceScaledMollifierKernel ζ R y z * σ ω₁ (WithLp.ofLp z) a b) -
      (σ ω₂ (WithLp.ofLp y) a b -
        ∫ z, sourceScaledMollifierKernel ζ R y z * σ ω₂ (WithLp.ofLp z) a b) = _
  rw [integral_sourceMollifier_coordinate, integral_sourceMollifier_coordinate]
  exact centered_pair_subtraction volume (fun x => σ ω₁ x a b)
    (fun x => σ ω₂ x a b) (fun x => sourceScaledMollifierKernel ζ R y (WithLp.toLp 2 x))
    (WithLp.ofLp y)
    ((hσ₁ a b).integrable_smul_left_of_hasCompactSupport hc hs)
    ((hσ₂ a b).integrable_smul_left_of_hasCompactSupport hc hs)

end EinsteinRelation.Correctors
