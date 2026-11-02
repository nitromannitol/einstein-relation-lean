import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedLaw
import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `e:holder-average#unforced-interior`, `paper/main.tex:700–705`.
Boundary-free real interior specialization on the actual coefficient field.
Apply separately to the real and imaginary caloric comparisons. The local
energy and distributional equation are explicit; no boundary-data norm or
Holder bound is a premise. This statement does not construct the comparison
or assert its boundary trace. -/
def node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ D : StructuralData d,
    ∃ α₀ C : ℝ, 0 < α₀ ∧ α₀ < 1 ∧ 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (τ : ℝ) (x : Vec d) (r : ℝ), 0 < r →
      let cyl := fun ρ : ℝ =>
        Set.Ioo (τ - ρ ^ 2) τ ×ˢ {y : Vec d | euclideanNorm (y - x) < ρ}
      ∀ (v : ℝ × Vec d → ℝ) (g : Fin d → ℝ × Vec d → ℝ),
        MemLp v 2 (volume.restrict (cyl r)) →
        (∀ j, MemLp (g j) 2 (volume.restrict (cyl r))) →
        (∀ φ : ℝ × Vec d → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ cyl r →
          ∀ j : Fin d,
            (∫ z in cyl r, v z * fderiv ℝ φ z (0, Pi.single j 1)) =
              -(∫ z in cyl r, g j z * φ z)) →
        (∀ φ : ℝ × Vec d → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ cyl r →
          (∫ z in cyl r, v z * fderiv ℝ φ z (1, 0)) =
            (1 / 2 : ℝ) * (∫ z in cyl r,
              ∑ j : Fin d, (∑ k : Fin d, ω.1 z.2 j k * g k z) *
                fderiv ℝ φ z (0, Pi.single j 1))) →
        ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
          Real.sqrt (⨍ z in cyl (θ * r),
            |v z - (⨍ w in cyl (θ * r), v w)| ^ 2) ≤
          C * θ ^ α₀ * Real.sqrt (⨍ z in cyl r,
            |v z - (⨍ w in cyl r, v w)| ^ 2)

end EinsteinFull.Blueprint
