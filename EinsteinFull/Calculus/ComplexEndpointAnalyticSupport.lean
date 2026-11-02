import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport
import EinsteinFull.Frozen.IndexedEndpoint
import EinsteinFull.Frozen.VelocityCorrelation
import EinsteinFull.Frozen.ClockCorrelation

/-!
# Entire force dependence of the actual stationary endpoints and correlations

Bounded evaluation and the actual bilinear L2 pairing transfer semigroup force
analyticity to the frozen endpoint and correlation formulas. The observations
are arbitrary fixed L2 classes; no higher-Lp or spatial-locality bound is assumed.
-/

open MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
  {F G : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

/-- The actual evolution of a force-analytic L2 datum is force analytic. -/
theorem analyticAt_complexEnvironmentSemigroup_apply
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z))
    (t : ℝ≥0) {z₀ : ℂ} {f : ℂ → Lp ℂ 2 (reducedLaw Q)}
    (hf : AnalyticAt ℂ f z₀) : AnalyticAt ℂ (fun z => F z t (f z)) z₀ :=
  ((ContinuousLinearMap.apply ℂ _).analyticAt_bilinear _).comp₂ hf
    (analyticAt_complexEnvironmentSemigroup hF t z₀)

/-- Every actual centered velocity endpoint is entire in complex force as an L2 class. -/
theorem analyticAt_velocityEndpoint
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z))
    (j : Fin d) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z => velocityEndpoint Q i j z (F z) β a t) z₀ := by
  have hd : AnalyticAt ℂ (fun z : ℂ => β j + z • a i j) z₀ :=
    analyticAt_const.add (analyticAt_id.fun_smul analyticAt_const)
  have ha := ((centeredComplexLpCLM Q).analyticAt _).comp
    (analyticAt_complexEnvironmentSemigroup_apply hF t hd)
  change AnalyticAt ℂ (fun z => centeredComplexLpCLM Q (F z t (β j + z • a i j))) z₀ at ha
  simpa only [centeredComplexLpCLM_apply, velocityEndpoint] using ha

/-- Every actual clock endpoint is entire in complex force as an L2 class. -/
theorem analyticAt_clockEndpoint
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z))
    (μ : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z => clockEndpoint Q z (F z) μ t) z₀ := by
  have ha := ((centeredComplexLpCLM Q).analyticAt _).comp
    (analyticAt_complexEnvironmentSemigroup_apply hF t (z₀ := z₀) (analyticAt_const (v := μ)))
  have hs := (analyticAt_id (𝕜 := ℂ) (z := z₀)).fun_smul ha
  change AnalyticAt ℂ (fun z => z • centeredComplexLpCLM Q (F z t μ)) z₀ at hs
  simpa only [centeredComplexLpCLM_apply, clockEndpoint] using hs

/-- Every actual bilinear transpose endpoint is entire in force as an L2 class. -/
theorem analyticAt_transposeEndpoint
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z))
    (hG : ∀ z : ℂ, IsComplexTransposeSemigroup Q (F z) (G z))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z => transposeEndpoint Q i (G z) β t) z₀ := by
  change AnalyticAt ℂ (fun z => G z t (β i)) z₀
  exact ((ContinuousLinearMap.apply ℂ (Lp ℂ 2 (reducedLaw Q)) (β i)).analyticAt _).comp
    (analyticAt_complexTransposeSemigroup hF hG t z₀)

/-- Each frozen indexed endpoint is entire in complex force on the actual L2 space. -/
theorem analyticAt_indexedEndpoint (hd : 2 ≤ d)
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ z (F z))
    (hG : ∀ z : ℂ, IsComplexTransposeSemigroup Q (F z) (G z))
    (ν : EndpointIndex d) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z => indexedEndpoint hd Q ν z (F z) (G z) β a μ t) z₀ := by
  rcases ν with j | b
  · exact analyticAt_velocityEndpoint hF j β a t z₀
  · cases b
    · exact analyticAt_clockEndpoint hF μ t z₀
    · exact analyticAt_transposeEndpoint hF hG β t z₀

/-- The literal bilinear velocity correlation is entire in complex force. -/
theorem analyticAt_velocityCorrelation
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z))
    (j : Fin d) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z => velocityCorrelation Q i j z (F z) β a t) z₀ := by
  let L := (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 (β i)
  have hd : AnalyticAt ℂ (fun z : ℂ => β j + z • a i j) z₀ :=
    analyticAt_const.add (analyticAt_id.fun_smul analyticAt_const)
  have ha := (L.analyticAt _).comp (analyticAt_complexEnvironmentSemigroup_apply hF t hd)
  change AnalyticAt ℂ (fun z => L (F z t (β j + z • a i j))) z₀ at ha
  simpa only [L, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply', velocityCorrelation] using ha

/-- The literal bilinear clock correlation is entire in complex force. -/
theorem analyticAt_clockCorrelation
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z => clockCorrelation Q i z (F z) β μ t) z₀ := by
  let L := (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 (β i)
  have hd : AnalyticAt ℂ (fun z : ℂ => z • μ) z₀ :=
    analyticAt_id.fun_smul analyticAt_const
  have ha := (L.analyticAt _).comp (analyticAt_complexEnvironmentSemigroup_apply hF t hd)
  change AnalyticAt ℂ (fun z => L (F z t (z • μ))) z₀ at ha
  simpa only [L, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply', clockCorrelation] using ha

end EinsteinFull
