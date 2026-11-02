import EinsteinFull.Frozen.CenteredComplexLp
import EinsteinFull.Frozen.VelocityCorrelation
import EinsteinFull.Frozen.ClockCorrelation

/-! Elementary integrability and centering for the actual reduced probability law.

The constant-class and mean arguments follow the real L² patterns in the pinned
blueprint's `Correctors/HomogenizedMatrixBounds.lean`, at revision
`7748a8e9000034825873768d309be8915ae53b07`. These facts apply to arbitrary complex
L² observations; they assert no diffusion estimate or paper-specific result.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinFull

open EinsteinRelation

theorem integrable_complexLp {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (f : FieldPair d → ℂ) (reducedLaw Q) := by
  letI := reducedLaw_probability Q
  exact (Lp.memLp f).integrable (by norm_num)

theorem integrable_complexLp_mul {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f g : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun ω => f ω * g ω) (reducedLaw Q) :=
  (Lp.memLp f).integrable_mul (Lp.memLp g)

theorem coeFn_centeredComplexLp {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℂ 2 (reducedLaw Q)) :
    centeredComplexLp Q f =ᵐ[reducedLaw Q]
      fun ω => f ω - ∫ ω', f ω' ∂reducedLaw Q := by
  letI := reducedLaw_probability Q
  unfold centeredComplexLp
  filter_upwards [Lp.coeFn_sub f (Lp.const 2 (reducedLaw Q)
      (∫ ω, f ω ∂reducedLaw Q)),
    Lp.coeFn_const 2 (reducedLaw Q) (∫ ω, f ω ∂reducedLaw Q)] with ω hs hc
  simpa only [Pi.sub_apply, hc, Function.const_apply] using hs

theorem integral_centeredComplexLp {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, centeredComplexLp Q f ω ∂reducedLaw Q) = 0 := by
  letI := reducedLaw_probability Q
  rw [integral_congr_ae (coeFn_centeredComplexLp Q f),
    integral_sub (integrable_complexLp Q f) (integrable_const _)]
  simp

theorem centeredComplexLp_idempotent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℂ 2 (reducedLaw Q)) :
    centeredComplexLp Q (centeredComplexLp Q f) = centeredComplexLp Q f := by
  apply Lp.ext
  filter_upwards [coeFn_centeredComplexLp Q (centeredComplexLp Q f)] with ω hω
  simpa only [integral_centeredComplexLp, sub_zero] using hω

theorem integrable_velocityCorrelation_integrand {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    Integrable (fun ω => β i ω * P t (β j + ζ • a i j) ω) (reducedLaw Q) :=
  integrable_complexLp_mul Q (β i) (P t (β j + ζ • a i j))

theorem integrable_clockCorrelation_integrand {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    Integrable (fun ω => β i ω * P t (ζ • μ) ω) (reducedLaw Q) :=
  integrable_complexLp_mul Q (β i) (P t (ζ • μ))

end EinsteinFull
