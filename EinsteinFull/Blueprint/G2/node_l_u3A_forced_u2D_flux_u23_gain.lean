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

/-- Node `l:forced-flux#gain`, `paper/main.tex:842–852`.
Consumer-facing weak-flux gain, including general Gaussian-controlled tests.
The structural epsilon is fixed as kappa/8 before p. The deterministic lattice
square sum and exponent computation accompany the actual flux conclusion;
annular summation remains a reduction obligation.
The actual endpoint fluxes are produced, never assumed. -/
def node_l_u3A_forced_u2D_flux_u23_gainStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ κ η η₀ ε Clat : ℝ, ∃ L : ℕ → ℕ,
      0 < κ ∧ κ < 1 / 2 ∧ η = κ / (16 * ((d : ℝ) + 2)) ∧
      η₀ = η / 4 ∧ ε = κ / 8 ∧ 0 < ε ∧ 0 < η₀ ∧
      0 < Clat ∧
      -1 - κ / 2 + η * ((d : ℝ) + 1 - κ) ≤ -1 - κ / 4 ∧
      (∀ t s : ℝ, 1 ≤ t → 1 ≤ s → ∀ x : Vec d,
        let r := t ^ (1 / 2 + η)
        let R := 2 * Real.sqrt (d : ℝ) + 2
        let W := fun z : Fin d → ℤ => sSup
          ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
            Real.exp (-euclideanNorm (x - y) ^ 2 / s)) ''
              {y : Vec d | euclideanNorm
                (y - fun j => r * (z j : ℝ)) ≤ R * r})
        Summable (fun z : Fin d → ℤ => (W z) ^ 2) ∧
        Real.sqrt (∑' z : Fin d → ℤ, (W z) ^ 2) ≤
          Clat * r ^ (-(d : ℝ) / 2) * s ^ (-(d : ℝ) / 4) *
            (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) ∧
        (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) ≤
          Clat * t ^ (η * (d : ℝ) / 2) * (1 + t / s) ^ ((d : ℝ) / 4)) ∧
    ∀ p : ℝ, 2 ≤ p → ∃ growth₀ t₀ : ℝ, ∃ Cder : ℕ → ℝ,
      0 < growth₀ ∧ 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧
    (      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
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
          (∀ j : Fin d, MemLp
            (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J t j)) :
              FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) ∧
          Real.sqrt (∑ j : Fin d, ((eLpNorm
            (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J t j)) :
              FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) ^ 2) ≤
            Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
              (t : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
                (1 + (t : ℝ) / s) ^ L k) ∧
    (∀ ctest : ℝ, 0 < ctest → ∀ Btest : ℕ → ℝ, (∀ q, 0 < Btest q) →
      ∃ ttest : ℝ, ∃ Ctest : ℕ → ℝ, t₀ ≤ ttest ∧ (∀ k, 0 < Ctest k) ∧
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
        ∀ (t : ℝ≥0), ttest ≤ (t : ℝ) →
        ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ →
        ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K →
        MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) →
        (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) *
            (((t : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
              ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) →
        ∀ (s : ℝ), 1 ≤ s → ∀ (k : ℕ) (ψ : SchwartzMap (Vec d) ℂ),
        HasGaussianTestControl s k ctest Btest ψ →
          (∀ j : Fin d, MemLp
            (stationarySchwartzAverage Q ψ (centeredComplexLp Q (J t j)) : FieldPair d → ℂ)
              (ENNReal.ofReal p) (reducedLaw Q)) ∧
          Real.sqrt (∑ j : Fin d, ((eLpNorm
            (stationarySchwartzAverage Q ψ (centeredComplexLp Q (J t j)) : FieldPair d → ℂ)
              (ENNReal.ofReal p) (reducedLaw Q)).toReal) ^ 2) ≤
            Ctest k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
              (t : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
                (1 + (t : ℝ) / s) ^ L k)

end EinsteinFull.Blueprint
