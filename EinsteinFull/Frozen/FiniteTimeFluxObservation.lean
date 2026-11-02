import EinsteinFull.Frozen.FluxIndex
import EinsteinFull.Frozen.TransposeEndpoint
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The literal time-integrated flux in e:time-flux. G is supplied horizontal
gradient data, identified with the actual endpoints by IsFiniteTimeFlux.
All time integrals have continuous-orbit witnesses guaranteeing genuine integrability.
The additional transpose integral is exactly -2*zeta*a*e_1*U_*. -/
noncomputable def finiteTimeFluxObservation {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ν : FluxIndex d) (ζ : ℂ)
    (Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (G : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (τ : ℝ≥0)
    (_hG : ∀ (ν : FluxIndex d) (k : Fin d), Continuous (fun r : ℝ≥0 => G r ν k))
    (_hU : ∀ f : Lp ℂ 2 (reducedLaw Q), Continuous (fun r : ℝ≥0 => Pdag r f))
    (j : Fin d) (ω : FieldPair d) : ℂ :=
  let i : Fin d := ν.elim id (fun _ => ⟨0, by omega⟩)
  a j i ω + (∑ k : Fin d, a j k ω *
    (∫ r in Set.Icc (0 : ℝ) (τ : ℝ), G r.toNNReal ν k) ω) -
    ν.elim (fun _ => 0) (fun _ => 2 * ζ * a j ⟨0, by omega⟩ ω *
      (∫ r in Set.Icc (0 : ℝ) (τ : ℝ),
        transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal) ω)

end EinsteinFull
