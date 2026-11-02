import EinsteinFull.Frozen.GaussianAveragingSeminorm
import EinsteinFull.Frozen.StructuralData

open MeasureTheory
open scoped BigOperators ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:local-av`, `paper/main.tex:1057–1071`.
This source step is universal in the centered stationary field, on the actual
reduced joint law. Locality means an actual localSigma-measurable representative,
not independence of matrix and clock. The vector L2 norm is Euclidean across
coordinates. The second clause states the summable annular bound and the
logarithmic conclusion, with the polynomial/tail constants fixed before the law,
time and field. Local approximants are data exactly as in this universal source
lemma; their construction for the time fluxes is a different graph node.
The tail prefactor is harmlessly enlarged to max(m,A) so the first annulus
is controlled even when the supplied approximation error prefactor is zero. -/
def node_e_u3A_local_u2D_avStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    (∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (r : ℝ), 1 ≤ r → ∀ F : Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ j, (∫ ω, F j ω ∂reducedLaw Q) = 0) →
        (∀ j, ∃ f : FieldPair d → ℂ,
          Measurable[localSigma {x : Vec d | euclideanNorm x < r}] f ∧
            f =ᵐ[reducedLaw Q] (F j : FieldPair d → ℂ)) →
        gaussianAveragingSeminorm hd Q F ≤
          ENNReal.ofReal (C * r ^ ((d : ℝ) / 2) *
            Real.sqrt (∑ j, ‖F j‖ ^ 2))) ∧
    ∀ (c A₀ a : ℝ), 0 < c → 0 < A₀ → 0 ≤ a →
      ∃ C : ℝ, ∃ M₀ : ℕ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (s m A : ℝ), 1 ≤ s → 0 ≤ m → 0 ≤ A →
        m ≤ A₀ * s ^ (-(d : ℝ) / 4) → A ≤ A₀ * (2 + s) ^ a →
        ∀ Y : Fin d → Lp ℂ 2 (reducedLaw Q),
          (∀ j, (∫ ω, Y j ω ∂reducedLaw Q) = 0) →
          Real.sqrt (∑ j, ‖Y j‖ ^ 2) ≤ m →
          (∀ n : ℕ, 1 ≤ n → ∃ Yloc : Fin d → Lp ℂ 2 (reducedLaw Q),
            (∀ j, ∃ f : FieldPair d → ℂ,
              Measurable[localSigma {x : Vec d |
                euclideanNorm x < (n : ℝ) * Real.sqrt s}] f ∧
              f =ᵐ[reducedLaw Q] (Yloc j : FieldPair d → ℂ)) ∧
            Real.sqrt (∑ j, ‖Y j - Yloc j‖ ^ 2) ≤
              A * Real.exp (-c * (n : ℝ) ^ 2)) →
          let annulus := fun n : ℕ =>
            (((n : ℝ) + 1) * Real.sqrt s) ^ ((d : ℝ) / 2) *
              min m (max m A * Real.exp (-c * (n : ℝ) ^ 2))
          Summable annulus ∧
          gaussianAveragingSeminorm hd Q Y ≤ ENNReal.ofReal (C * ∑' n, annulus n) ∧
          (∑' n, annulus n) ≤ C * Real.log (2 + s) ^ M₀ ∧
          gaussianAveragingSeminorm hd Q Y ≤
            ENNReal.ofReal (C ^ 2 * Real.log (2 + s) ^ M₀)

end EinsteinFull.Blueprint
