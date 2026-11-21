import EinsteinFull.External.DFGW.FutureStateRepresentative
import EinsteinFull.External.DFGW.PastBlockMixing

/-! # Mixing of past and future observables

A centered square-integrable future observable becomes asymptotically orthogonal to every
square-integrable past observable under positive time shifts.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A centered future observable becomes asymptotically orthogonal to any past observable. -/
theorem tendsto_inner_past_future_zero
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hμ : μ Set.univ ≠ ⊤)
    {t : ℝ≥0} (ht : 0 < t) (f Z : Lp ℝ 2 P)
    (hf : AEStronglyMeasurable[Draft.dfgwCoordSigma (Set.Iic 0)] f P)
    (hZ : AEStronglyMeasurable[Draft.dfgwCoordSigma (Set.Ici 0)] Z P)
    (hmean : ∫ η, Z η ∂P = 0) :
    let shiftMP (u : ℝ) : MeasurePreserving (Draft.dfgwShift (S := S) u) P P :=
      ⟨measurable_shift u, hP.stationary u⟩
    Tendsto (fun n : ℕ => inner ℝ f
      (Lp.compMeasurePreserving _ (shiftMP (n • t : ℝ≥0)) Z)) atTop (𝓝 0) := by
  obtain ⟨g, hcond, hgm⟩ := exists_state_condExp_future hP Z hZ
  exact tendsto_inner_past_shifted_block_zero hP hμ ht f Z hf g (hgm.trans hmean) hcond

end EinsteinFull.External.DFGW
