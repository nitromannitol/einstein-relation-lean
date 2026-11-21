import EinsteinFull.External.DFGW.KernelInvariant
import MarkovProcess.Kernel.Lp

/-! # Transition operators on `L²`

The transition kernels of the stationary process induce contractions on `L²` of its marginal.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The transition kernel as a continuous linear contraction on the invariant `L²` space. -/
noncomputable def transitionOperator (hP : Draft.IsDFGWTrajectoryProcess P μ T) (t : ℝ≥0) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := by
  let : IsMarkovKernel (T t) := hP.markov_kernel t
  let : Fact (1 ≤ (2 : ℝ≥0)) := ⟨by norm_num⟩
  exact MarkovProcess.kernelLpFinite μ (T t) (MarkovProcess.IsSubMarkovKernel.of_isMarkovKernel (T t)) (le_of_eq (kernel_comp_eq hP t)) 2

/-- The `L²` transition operator has norm at most one. -/
theorem norm_transitionOperator_le_one (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (t : ℝ≥0) : ‖transitionOperator hP t‖ ≤ 1 := by
  let : IsMarkovKernel (T t) := hP.markov_kernel t
  let : Fact (1 ≤ (2 : ℝ≥0)) := ⟨by norm_num⟩
  exact MarkovProcess.norm_kernelLpFinite_le μ (T t) (MarkovProcess.IsSubMarkovKernel.of_isMarkovKernel (T t))
    (le_of_eq (kernel_comp_eq hP t)) 2

/-- The `L²` transition operator is represented almost everywhere by kernel integration. -/
theorem transitionOperator_ae_eq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (t : ℝ≥0) (f : Lp ℝ 2 μ) :
    transitionOperator hP t f =ᵐ[μ] fun x => ∫ y, f y ∂T t x := by
  let : IsMarkovKernel (T t) := hP.markov_kernel t
  let : Fact (1 ≤ (2 : ℝ≥0)) := ⟨by norm_num⟩
  exact MarkovProcess.coeFn_kernelLpFinite μ (T t) (MarkovProcess.IsSubMarkovKernel.of_isMarkovKernel (T t))
    (le_of_eq (kernel_comp_eq hP t)) 2 f

end EinsteinFull.External.DFGW
