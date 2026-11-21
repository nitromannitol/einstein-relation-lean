import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff
import PDEFoundation.Sobolev.H1.ZeroBoundaryLimit
import PDEFoundation.Measure.LpDominatedConvergence

/-!
# Zero-boundary limits of cutoff products

Cutoffs converging to one give an `H¹₀` representative when their multiplier
errors in each gradient coordinate tend to zero.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

private theorem cutoff_mul_tendsto_L2 {d : ℕ} {U : Set (PDE.Vec d)}
    [IsFiniteMeasure (PDE.volumeOn U)] (f : PDE.Vec d → ℝ) (hf : MemLp f 2 (PDE.volumeOn U))
    (inner outer : ℕ → Set (PDE.Vec d)) (C : ℕ → ℝ)
    (η : ∀ k, PDE.QuantitativeSmoothCutoff (inner k) (outer k) (C k))
    (hη : ∀ᵐ x ∂(PDE.volumeOn U), Tendsto (fun k => η k x) atTop (𝓝 1)) :
    Tendsto (fun k => eLpNorm (fun x => η k x * f x - f x) 2 (PDE.volumeOn U))
      atTop (𝓝 0) := by
  have h := PDE.tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
    (μ := PDE.volumeOn U) (p := 2) (F := fun k x => η k x * f x)
    (f := f) (bound := f) (by norm_num) (by norm_num)
    (fun k => (η k).smooth.continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    hf hf ?_ ?_
  · convert h using 1
  · intro k
    filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ((η k).nonneg x)]
    exact mul_le_of_le_one_left (norm_nonneg _) ((η k).le_one x)
  · filter_upwards [hη] with x hx
    simpa only [one_mul] using hx.mul_const (f x)

/-- Compactly supported cutoff products converge in `H¹` if their derivative
costs vanish, and their limit therefore belongs to `H¹₀`. -/
theorem memH10_of_cutoff_gradient_tendsto_zero {d : ℕ} {U : Set (PDE.Vec d)}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (inner outer : ℕ → Set (PDE.Vec d)) (C : ℕ → ℝ)
    (η : ∀ k, PDE.QuantitativeSmoothCutoff (inner k) (outer k) (C k))
    (houter : ∀ k, outer k ⊆ U)
    (hη : ∀ᵐ x ∂(PDE.volumeOn U), Tendsto (fun k => η k x) atTop (𝓝 1))
    (hcost : ∀ i : Fin d, Tendsto (fun k => eLpNorm
      (fun x => u x * PDE.classicalGradient (η k).toFun x i) 2 (PDE.volumeOn U))
      atTop (𝓝 0)) : PDE.MemH10 U u.toFun := by
  let : IsFiniteMeasure (PDE.volumeOn U) := hU.isFiniteMeasure_volumeOn
  let V : ℕ → PDE.H10Function U := fun k => u.mulCutoffToH10 hU (η k) (houter k)
  refine PDE.memH10_of_tendsto_H1 hU.isOpen u (fun k => (V k).toH1Function)
    (fun k => ⟨V k, rfl⟩) ?_ ?_
  · have h := cutoff_mul_tendsto_L2 u.toFun u.memL2 inner outer C η hη
    have heq (k : ℕ) : eLpNorm (fun x => u x - (V k).toH1Function x) 2 (PDE.volumeOn U) =
        eLpNorm (fun x => η k x * u x - u x) 2 (PDE.volumeOn U) := by
      rw [PDE.H1Function.mulCutoffToH10_toFun]
      exact PDE.eLpNorm_sub_swap (u.toFun) (fun x => η k x * u x)
    simpa only [heq] using h
  · intro i
    have hfirst := cutoff_mul_tendsto_L2 (fun x => u.grad x i) (u.gradMemL2 i)
      inner outer C η hη
    have hsum : Tendsto (fun k => eLpNorm
        (fun x => η k x * u.grad x i - u.grad x i) 2 (PDE.volumeOn U) +
        eLpNorm (fun x => u x * PDE.classicalGradient (η k).toFun x i)
          2 (PDE.volumeOn U)) atTop (𝓝 0) := by
      simpa using hfirst.add (hcost i)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le) ?_
    intro k
    have heq : (fun x => u.grad x i - (V k).toH1Function.grad x i) =
        (fun x => u.grad x i - η k x * u.grad x i) +
          -(fun x => u x * PDE.classicalGradient (η k).toFun x i) := by
      funext x
      simp only [V, PDE.H1Function.mulCutoffToH10_grad, Pi.add_apply, Pi.neg_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    change eLpNorm (fun x => u.grad x i - (V k).toH1Function.grad x i)
      2 (PDE.volumeOn U) ≤ _
    rw [heq]
    calc
      _ ≤ eLpNorm (fun x => u.grad x i - η k x * u.grad x i) 2 (PDE.volumeOn U) +
          eLpNorm (-(fun x => u x * PDE.classicalGradient (η k).toFun x i))
            2 (PDE.volumeOn U) := eLpNorm_add_le (by norm_num)
      _ = _ := by
        rw [eLpNorm_neg]
        congr 1
        exact PDE.eLpNorm_sub_swap (fun x => u.grad x i)
          (fun x => η k x * u.grad x i)

end EinsteinFull.Regeneration
