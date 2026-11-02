import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.CorrectorGradient
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.EndpointWeakFlux
import Mathlib.Analysis.Calculus.FDeriv.Basic

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `e:flux-identity`, `paper/main.tex:817–825`.
Spatial potentials are produced and characterized by the ACTUAL canonical
corrector gradient and flux. They are local L2 potentials, including in d=2;
no stationary potential value is asserted. The universal smooth identity and
the weak endpoint specialization use the column-divergence sign convention.
All scalar shifts and antisymmetric constant shifts are allowed. The latter
specialization has only u, its first gradient and its time derivative. -/
def node_e_u3A_flux_u2D_identityStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
    HasSmoothBounds D Q →
  ∃ (φ : Fin d → FieldPair d → Vec d → ℝ)
    (S : Fin d → Fin d → Fin d → FieldPair d → Vec d → ℝ),
    (∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
      (∀ R : ℝ, 0 < R →
        MemLp (φ i ω) 2 (volume.restrict {x : Vec d | euclideanNorm x < R}) ∧
        ∀ k j, MemLp (S i k j ω) 2
          (volume.restrict {x : Vec d | euclideanNorm x < R})) ∧
      (∀ k j x, S i k j ω x = -S i j k ω x) ∧
      (∀ θ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ →
        (∀ j : Fin d,
          (∫ x, φ i ω x * fderiv ℝ θ x (unitVector j)) =
            -(∫ x, correctorGradient Q i (translate x ω) j * θ x)) ∧
        (∀ j : Fin d,
          (∑ k : Fin d, ∫ x, S i k j ω x * fderiv ℝ θ x (unitVector k)) =
            -(∫ x, ((∑ l : Fin d, ω.1 x j l *
              (unitVector i l + correctorGradient Q i (translate x ω) l)) -
                homogenizedCoefficient Q j i) * θ x))) ∧
      ∀ (cφ : ℝ) (cS : Fin d → Fin d → ℝ),
        (∀ k j, cS k j = -cS j k) →
      ∀ (F : Vec d → Fin d → ℂ),
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j)) →
      ∀ ψ : Vec d → ℂ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        let aF := fun (x : Vec d) (j : Fin d) =>
          ∑ l : Fin d, (ω.1 x j l : ℂ) * F x l
        let divAF := fun x : Vec d =>
          ∑ j : Fin d, fderiv ℝ (fun y => aF y j) x (unitVector j)
        (∫ x, (∑ j : Fin d,
          ((ω.1 x i j - homogenizedCoefficient Q i j : ℝ) : ℂ) * F x j) * ψ x) =
          (∫ x, ((φ i ω x - cφ : ℝ) : ℂ) * divAF x * ψ x) +
          (∫ x, ((φ i ω x - cφ : ℝ) : ℂ) *
            (∑ k : Fin d, aF x k * fderiv ℝ ψ x (unitVector k))) -
          (∫ x, ∑ k : Fin d, ∑ j : Fin d,
            ((S i k j ω x - cS k j : ℝ) : ℂ) * F x j *
              fderiv ℝ ψ x (unitVector k)) -
          (∫ x, (∑ k : Fin d, ∑ j : Fin d,
            ((S i k j ω x - cS k j : ℝ) : ℂ) *
              fderiv ℝ (fun y => F y j) x (unitVector k)) * ψ x)) ∧
    ∀ (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      let U := fun t => indexedEndpoint hd Q ν ζ P Pdag β a μ t
      ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a (U t) (G t) (J t)) ∧
        ∀ t : ℝ≥0, 0 < (t : ℝ) →
          DifferentiableAt ℝ (fun r : ℝ => U r.toNNReal) (t : ℝ) ∧
          ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
          ∀ (cφ : ℝ) (cS : Fin d → Fin d → ℝ),
            (∀ k j, cS k j = -cS j k) →
          ∀ ψ : Vec d → ℂ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            let u := fun x : Vec d => U t (translate x ω)
            let g := fun (x : Vec d) (j : Fin d) => G t j (translate x ω)
            let ut := fun x : Vec d =>
              deriv (fun r : ℝ => U r.toNNReal) (t : ℝ) (translate x ω)
            let c := ζ * ∫ ω, ∑ k : Fin d,
              a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q
            let F := fun (x : Vec d) (j : Fin d) => g x j -
              match ν with
              | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * u x
              | _ => 0
            let divAF := fun x : Vec d => 2 * ut x +
              match ν with
              | .inr true => 0
              | _ => 2 * c - 2 * ζ * (∑ k : Fin d,
                  (ω.1 x k ⟨0, by omega⟩ : ℂ) * g x k)
            (∫ x, J t i (translate x ω) * ψ x) =
              (∫ x, ((φ i ω x - cφ : ℝ) : ℂ) * divAF x * ψ x) +
              (∫ x, ((φ i ω x - cφ : ℝ) : ℂ) *
                (∑ k : Fin d, (∑ j : Fin d, (ω.1 x k j : ℂ) * F x j) *
                  fderiv ℝ ψ x (unitVector k))) -
              (∫ x, ∑ k : Fin d, ∑ j : Fin d,
                ((S i k j ω x - cS k j : ℝ) : ℂ) * F x j *
                  fderiv ℝ ψ x (unitVector k)) +
              match ν with
              | .inr true => 2 * ζ * (∫ x, (∑ k : Fin d,
                  ((S i k ⟨0, by omega⟩ ω x - cS k ⟨0, by omega⟩ : ℝ) : ℂ) *
                    g x k) * ψ x)
              | _ => 0

end EinsteinFull.Blueprint
