import EinsteinFull.Frozen.FiniteTimeCorrector
import EinsteinFull.Frozen.FiniteTimeFluxObservation
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- Continuous nonnegative-time orbits have genuine finite-time Bochner integrals. -/
theorem integrableOn_comp_toNNReal_Icc {E : Type*} [NormedAddCommGroup E]
    (F : ℝ≥0 → E) (hF : Continuous F) (T : ℝ) :
    IntegrableOn (fun r : ℝ => F r.toNNReal) (Set.Icc 0 T) := by
  exact (hF.comp continuous_real_toNNReal).integrableOn_Icc

/-- The corrector time integral uses the actual continuous semigroup orbit. -/
theorem integrableOn_finiteTimeCorrector_integrand {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (τ : ℝ≥0) (j : Fin d) :
    IntegrableOn (fun r : ℝ => P r.toNNReal (β j)) (Set.Icc 0 (τ : ℝ)) := by
  exact integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 (β j)) _

/-- Continuous supplied flux gradients have genuine time integrals. -/
theorem integrableOn_finiteTimeFlux_gradient_integrand {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (G : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : ∀ (ν : FluxIndex d) (k : Fin d), Continuous (fun r : ℝ≥0 => G r ν k))
    (τ : ℝ≥0) (ν : FluxIndex d) (k : Fin d) :
    IntegrableOn (fun r : ℝ => G r.toNNReal ν k) (Set.Icc 0 (τ : ℝ)) := by
  exact integrableOn_comp_toNNReal_Icc _ (hG ν k) _

/-- The public continuous-orbit domain protects the transpose flux integral. -/
theorem integrableOn_finiteTimeFlux_transpose_integrand {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hPdag : ∀ f : Lp ℂ 2 (reducedLaw Q), Continuous (fun r : ℝ≥0 => Pdag r f))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (τ : ℝ≥0) :
    IntegrableOn (fun r : ℝ => transposeEndpoint Q i Pdag β r.toNNReal)
      (Set.Icc 0 (τ : ℝ)) := by
  exact integrableOn_comp_toNNReal_Icc _ (hPdag (β i)) _

end EinsteinFull
