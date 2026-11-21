import EinsteinFull.External.DFGW.VectorMartingaleApproximation
import EinsteinFull.External.DFGW.IncrementL2

/-! # Scalar projections of vector remainders

Coordinatewise sublinear mean-square error implies the same estimate for every fixed scalar
projection of the vector remainder.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- Coordinatewise sublinear mean-square errors imply sublinear error for every fixed
projection. -/
theorem tendsto_projected_remainder_of_coordinates
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : ∀ t, MemLp (N t) 2 P)
    (hcoord : ∀ i : Fin d, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (X 0 t η i - N t η i) ^ 2 ∂P) atTop (𝓝 0)) (e : Vec d) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (dot e (X 0 t η) - dot e (N t η)) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hP.probability
  let K : ℝ := ∑ i : Fin d, e i ^ 2
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : Tendsto (fun t : ℝ≥0 => ∑ i : Fin d, (t : ℝ)⁻¹ *
      ∫ η, (X 0 t η i - N t η i) ^ 2 ∂P) atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun i _ => hcoord i)
    simpa only [Finset.sum_const_zero] using h
  have hupper : Tendsto (fun t : ℝ≥0 => K * ∑ i : Fin d, (t : ℝ)⁻¹ *
      ∫ η, (X 0 t η i - N t η i) ^ 2 ∂P) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsum.const_mul K
  apply squeeze_zero (g := fun t : ℝ≥0 => K * ∑ i : Fin d, (t : ℝ)⁻¹ *
    ∫ η, (X 0 t η i - N t η i) ^ 2 ∂P)
  · intro t
    exact mul_nonneg (inv_nonneg.mpr t.coe_nonneg) (integral_nonneg fun _ => sq_nonneg _)
  · intro t
    let E : Fin d → C(ℝ, S) → ℝ := fun i η => X 0 t η i - N t η i
    let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, e i • ContinuousLinearMap.proj i
    have hL (v : Vec d) : L v = dot e v := by
      simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
    have hX : MemLp (X 0 t) 2 P := (memLp_pi_iff).2 fun i =>
      increment_coordinate_memLp hP φ hφ t (hL2 t) i
    have hE (i : Fin d) : MemLp (E i) 2 P := (hX.eval i).sub ((hN t).eval i)
    have hdot : MemLp (fun η => dot e (X 0 t η) - dot e (N t η)) 2 P := by
      have h := (hX.sub (hN t)).continuousLinearMap_comp L
      simpa only [Function.comp_apply, hL, dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] using h
    have hsumint : Integrable (fun η => ∑ i : Fin d, (E i η) ^ 2) P := by
      apply integrable_finsetSum
      intro i hi
      exact (hE i).integrable_sq
    have hpoint (η : C(ℝ, S)) : (dot e (X 0 t η) - dot e (N t η)) ^ 2 ≤
        K * ∑ i : Fin d, (E i η) ^ 2 := by
      have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ e (fun i => E i η)
      simpa only [K, E, dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] using hc
    have hbound := integral_mono (hdot.integrable_sq) (hsumint.const_mul K) hpoint
    rw [integral_const_mul, integral_finsetSum] at hbound
    · have ht : 0 ≤ ((t : ℝ)⁻¹) := inv_nonneg.mpr t.coe_nonneg
      have hb := mul_le_mul_of_nonneg_left hbound ht
      simpa only [E, ← Finset.mul_sum, mul_left_comm] using hb
    · intro i hi
      exact (hE i).integrable_sq
  · exact hupper

end EinsteinFull.External.DFGW
