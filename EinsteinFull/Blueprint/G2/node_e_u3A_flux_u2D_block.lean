import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.EndpointWeakFlux
import EinsteinFull.Frozen.CenteredComplexLp
import EinsteinFull.Frozen.GaussianDerivativeAverage
import EinsteinFull.Frozen.StationarySchwartzAverage
import EinsteinFull.Frozen.GaussianTestControl

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `e:flux-block`, `paper/main.tex:832–838`.
The actual endpoint flux tested against one smooth cutoff times a Gaussian
derivative. The full Lp bound includes the bad-event error; no good event or
corrector approximation is assumed. The deterministic cutoff has exactly the
mesoscopic support and gradient scaling needed by a partition of unity. -/
def node_e_u3A_flux_u2D_blockStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ κ η η₀ Cenv : ℝ, ∃ Lblock : ℕ → ℕ,
      0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ Cenv ∧
      η = κ / (16 * ((d : ℝ) + 2)) ∧ η₀ = η / 4 ∧
    ∀ p : ℝ, 2 ≤ p → ∃ growth₀ t₀ : ℝ, ∃ Cder : ℕ → ℝ,
      0 < growth₀ ∧ 1 ≤ t₀ ∧ (∀ k, 1 ≤ Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
        IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ t : ℝ≥0, 0 < (t : ℝ) →
          IsEndpointWeakFlux hd Q ν ζ a (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
            (G t) (J t)) ∧
        ∀ (t : ℝ≥0), t₀ ≤ (t : ℝ) →
        ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ →
        ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K →
        MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) →
        (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) *
            (((t : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
              ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) →

        ∀ (s : ℝ), 1 ≤ s → ∀ hs : 0 < s,
        ∀ (k : ℕ) (dirs : Fin k → Fin d),
          let r := (t : ℝ) ^ (1 / 2 + η)
          let R := 2 * Real.sqrt (d : ℝ) + 2
          let kernel := fun y : Vec d =>
            iteratedFDeriv ℝ k (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0)
              y (fun j => unitVector (dirs j))
          let W := fun (x z : Vec d) => sSup
            ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
              Real.exp (-euclideanNorm (x - y) ^ 2 / (Cenv * s))) ''
                {y : Vec d | euclideanNorm (y - z) ≤ R * r})
          ∀ χ : Vec d → ℝ,
            ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
            Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R * r} →
            (∀ y, |χ y| ≤ 1) →
            (∀ y, Real.sqrt (∑ j : Fin d,
              (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ R / r) →
          let B := fun (x z : Vec d) (j : Fin d) =>
            ∫ y : Vec d, (χ (y - z) * kernel (x - y)) •
              complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)
          ∀ (x z : Vec d) (j : Fin d),
            MemLp (B x z j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
            (eLpNorm (B x z j : FieldPair d → ℂ)
              (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
              Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
                (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
                r ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2) *
                (1 + (t : ℝ) / s) ^ Lblock k * W x z

end EinsteinFull.Blueprint
