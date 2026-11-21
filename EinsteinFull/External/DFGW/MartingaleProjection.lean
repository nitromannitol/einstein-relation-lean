import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Linear images of martingales

A continuous linear image of an integrable martingale is a martingale.
-/

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.External.DFGW

variable {Ω ι E F : Type*} [Preorder ι] {m : MeasurableSpace Ω}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {ℱ : Filtration ι m} {P : Measure Ω} {M : ι → Ω → E}

/-- Applying a continuous linear map to a martingale gives a martingale. -/
theorem martingale_continuousLinearMap (hM : Martingale M ℱ P) (L : E →L[ℝ] F) :
    Martingale (fun t ω => L (M t ω)) ℱ P := by
  constructor
  · intro t
    exact L.continuous.comp_stronglyMeasurable (hM.stronglyAdapted t)
  · intro s t hst
    have hc := L.comp_condExp_comm (m := ℱ s) (hM.integrable t)
    filter_upwards [hc, hM.2 s t hst] with ω hcω hω
    change L (P[M t | ℱ s] ω) = P[L ∘ M t | ℱ s] ω at hcω
    change P[L ∘ M t | ℱ s] ω = L (M s ω)
    rw [← hcω, hω]

end EinsteinFull.External.DFGW
