import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped ENNReal BigOperators
namespace EinsteinRelation.Correctors

private theorem dot_ofLp_eq_inner {d : ℕ} (v w : EuclideanSpace ℝ (Fin d)) :
    dot (WithLp.ofLp v) (WithLp.ofLp w) = inner ℝ v w := by
  simp [dot, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The actual variational pairing on Euclidean L2 classes is a genuine integral.
Source main.tex688–701; no arbitrary nonintegrable representatives enter. -/
theorem integrable_lp_dot {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (v F : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) :
    Integrable (fun ω => dot (WithLp.ofLp (v ω)) (WithLp.ofLp (F ω))) μ := by
  simp_rw [dot_ofLp_eq_inner]
  exact L2.integrable_inner v F

/-- The genuine pairing of L2 representatives agrees with the original functions. -/
theorem integral_lp_dot_toLp {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {v F : Ω → EuclideanSpace ℝ (Fin d)} (hv : MemLp v 2 μ) (hF : MemLp F 2 μ) :
    (∫ ω, dot (WithLp.ofLp ((hv.toLp v) ω)) (WithLp.ofLp ((hF.toLp F) ω)) ∂μ) =
      ∫ ω, dot (WithLp.ofLp (v ω)) (WithLp.ofLp (F ω)) ∂μ := by
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp, hF.coeFn_toLp] with ω hvω hFω
  rw [hvω, hFω]

/-- Continuity of the literal integrated flux pairing in the Euclidean L2 test.
This provides extension from the actual horizontal gradient core to its closure. -/
theorem continuous_lp_dot_pairing {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (F : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) :
    Continuous (fun v : Lp (EuclideanSpace ℝ (Fin d)) 2 μ =>
      ∫ ω, dot (WithLp.ofLp (v ω)) (WithLp.ofLp (F ω)) ∂μ) := by
  have heq : (fun v : Lp (EuclideanSpace ℝ (Fin d)) 2 μ =>
      ∫ ω, dot (WithLp.ofLp (v ω)) (WithLp.ofLp (F ω)) ∂μ) =
      (fun v => inner ℝ v F) := by
    funext v
    simp only [dot_ofLp_eq_inner, L2.inner_def]
  rw [heq]
  exact continuous_id.inner continuous_const

/-- Vanishing of the actual flux pairing on a core extends to its L2 closure;
there is no density or closed-space premise hidden in this internal proof step. -/
theorem lp_dot_eq_zero_on_closure {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (F : Lp (EuclideanSpace ℝ (Fin d)) 2 μ)
    (S : Set (Lp (EuclideanSpace ℝ (Fin d)) 2 μ))
    (hS : ∀ v ∈ S, (∫ ω, dot (WithLp.ofLp (v ω)) (WithLp.ofLp (F ω)) ∂μ) = 0) :
    ∀ v ∈ closure S, (∫ ω, dot (WithLp.ofLp (v ω)) (WithLp.ofLp (F ω)) ∂μ) = 0 := by
  exact closure_minimal hS (isClosed_eq (continuous_lp_dot_pairing F) continuous_const)

end EinsteinRelation.Correctors
