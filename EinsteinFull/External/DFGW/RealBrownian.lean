import MarkovProcess.Examples.BrownianMotion
import Mathlib.Probability.BrownianMotion.Basic

/-! # Finite-dimensional laws of real Brownian motion

The continuous process constructed from the heat semigroup has the Gaussian
finite-dimensional laws of standard Brownian motion.
-/

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped NNReal

namespace EinsteinFull.External.DFGW

/-- The canonical process under the heat-semigroup Brownian law has the standard Gaussian
finite-dimensional distributions. -/
theorem isPreBrownianReal_heatProcess :
    IsPreBrownianReal (fun t (γ : ContinuousPath ℝ) => γ t) (brownianMotion 0) := by
  have h := isBrownianReal_brownianMotion 0
  apply HasIndepIncrements.isPreBrownianReal_of_hasLaw
  · intro t
    simpa only [sub_zero] using h.hasLaw_eval t
  · change MarkovProcess.HasIndepIncrements (fun t (γ : ContinuousPath ℝ) => γ t)
      (brownianMotion 0)
    simpa only [sub_zero] using h.hasIndepIncrements

end EinsteinFull.External.DFGW
