import EinsteinFull.External.DFGW.Correlation

/-! # Kernel correlations as `L²` pairings

The actual kernel formula for square-integrable observables is integrable and agrees with the
corresponding `L²` semigroup pairing.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A pointwise kernel correlation is almost everywhere an `L²` product. -/
theorem mul_kernel_ae_eq (hP : Draft.IsDFGWTrajectoryProcess P μ T) (t : ℝ≥0)
    (f g : S → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (fun x => f x * ∫ y, g y ∂T t x) =ᵐ[μ]
      fun x => (hf.toLp f) x * (transitionOperator hP t (hg.toLp g)) x := by
  have hgf : (hg.toLp g) =ᵐ[μ] g := MemLp.coeFn_toLp hg
  have hkernel := MarkovProcess.kernelIntegral_congr_ae (le_of_eq (kernel_comp_eq hP t)) hgf
  filter_upwards [MemLp.coeFn_toLp hf, transitionOperator_ae_eq hP t (hg.toLp g),
    hkernel] with x hfx htx hk
  change f x * MarkovProcess.kernelIntegral (T t) g x = (hf.toLp f) x *
    (transitionOperator hP t (hg.toLp g)) x
  rw [htx]
  change f x * MarkovProcess.kernelIntegral (T t) g x = (hf.toLp f) x *
    MarkovProcess.kernelIntegral (T t) (hg.toLp g) x
  rw [hfx, hk]

/-- A kernel correlation of two square-integrable observables is integrable. -/
theorem integrable_mul_kernel (hP : Draft.IsDFGWTrajectoryProcess P μ T) (t : ℝ≥0)
    (f g : S → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => f x * ∫ y, g y ∂T t x) μ := by
  have hi := (Lp.memLp (hf.toLp f)).integrable_mul
    (Lp.memLp (transitionOperator hP t (hg.toLp g)))
  exact hi.congr (mul_kernel_ae_eq hP t f g hf hg).symm

/-- The kernel correlation is the corresponding real `L²` pairing. -/
theorem integral_mul_kernel_eq_inner (hP : Draft.IsDFGWTrajectoryProcess P μ T) (t : ℝ≥0)
    (f g : S → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * ∫ y, g y ∂T t x ∂μ) =
      inner ℝ (hf.toLp f) (transitionOperator hP t (hg.toLp g)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mul_kernel_ae_eq hP t f g hf hg] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm]

end EinsteinFull.External.DFGW
