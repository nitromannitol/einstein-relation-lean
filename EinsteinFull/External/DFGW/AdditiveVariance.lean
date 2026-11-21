import EinsteinFull.External.DFGW.ProjectedMartingaleVariance
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Instances.RealVectorSpace

/-! # Linear growth of nonnegative additive functions

A nonnegative additive function on nonnegative real times is linear.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

/-- A nonnegative additive function of nonnegative real time grows linearly. -/
theorem nonnegative_additive_eq_mul (f : ℝ≥0 → ℝ)
    (hadd : ∀ s t, f (s + t) = f s + f t) (hnonneg : ∀ t, 0 ≤ f t)
    (t : ℝ≥0) : f t = (t : ℝ) * f 1 := by
  have hf0 : f 0 = 0 := by have h := hadd 0 0; simp only [zero_add] at h; linarith
  let F : ℝ → ℝ := fun x => f x.toNNReal - f (-x).toNNReal
  have hparts (x y : ℝ) :
      (x + y).toNNReal + (-x).toNNReal + (-y).toNNReal =
        (-(x + y)).toNNReal + x.toNNReal + y.toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add, Real.coe_toNNReal']
    simp only [max_def]
    split_ifs <;> linarith
  have hFadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have h := congrArg f (hparts x y)
    simp only [hadd] at h
    dsimp only [F]
    linarith
  let A : ℝ →+ ℝ :=
    { toFun := F
      map_zero' := by simp only [F, neg_zero, sub_self]
      map_add' := hFadd }
  have hFnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ A x := by
    intro x hx
    change 0 ≤ f x.toNNReal - f (-x).toNNReal
    rw [Real.toNNReal_of_nonpos (neg_nonpos.mpr hx), hf0, sub_zero]
    exact hnonneg _
  have hmono : Monotone A := by
    intro x y hxy
    have hh := hFnonneg (y - x) (sub_nonneg.mpr hxy)
    rw [map_sub] at hh
    linarith
  have hcont : Continuous A := MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable A hmono.measurable
  have hlin := map_real_smul A hcont (t : ℝ) (1 : ℝ)
  have hval : A (t : ℝ) = f t := by
    change f (t : ℝ).toNNReal - f (-(t : ℝ)).toNNReal = f t
    rw [Real.toNNReal_coe, Real.toNNReal_of_nonpos (neg_nonpos.mpr t.coe_nonneg), hf0, sub_zero]
  have hone : A 1 = f 1 := by
    change f (1 : ℝ).toNNReal - f (-(1 : ℝ)).toNNReal = f 1
    have hn : (-(1 : ℝ)).toNNReal = 0 := Real.toNNReal_of_nonpos (by norm_num)
    rw [hn, hf0, sub_zero]
    congr 1
    change ((1 : ℝ≥0) : ℝ).toNNReal = (1 : ℝ≥0)
    exact Real.toNNReal_coe
  simpa only [smul_eq_mul, mul_one, hval, hone] using hlin

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The second moment of a projected compensated martingale grows linearly in time. -/
theorem integral_projected_compensated_sq_eq_mul
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : Integrable φ μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P)
    (L : Vec d →L[ℝ] ℝ) (t : ℝ≥0) :
    (∫ η, (L (compensated X φ t η)) ^ 2 ∂P) =
      (t : ℝ) * ∫ η, (L (compensated X φ 1 η)) ^ 2 ∂P := by
  refine nonnegative_additive_eq_mul (fun u => ∫ η, (L (compensated X φ u η)) ^ 2 ∂P) ?_ ?_ t
  · exact integral_projected_compensated_sq_add hP hX φ hφ hL2 hM L
  · intro s
    exact integral_nonneg fun _ => sq_nonneg _

end EinsteinFull.External.DFGW
