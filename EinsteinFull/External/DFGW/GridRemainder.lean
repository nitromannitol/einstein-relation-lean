import EinsteinFull.External.DFGW.ScaledRemainderInMeasure

/-! # Martingale remainders on the integer grid

A sublinear mean-square martingale remainder is negligible in probability under diffusive
normalization at integer times.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- A sublinear mean-square remainder vanishes in probability on the diffusively scaled
integer grid. -/
theorem tendstoInMeasure_projected_grid_remainder
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : ∀ t, MemLp (N t) 2 P) (e : Vec d)
    (hrem : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (dot e (X 0 t η) - dot e (N t η)) ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P (fun (n : ℕ) η => (Real.sqrt (n + 1))⁻¹ *
      (dot e (X 0 ((n + 1 : ℕ) : ℝ≥0) η) - dot e (N ((n + 1 : ℕ) : ℝ≥0) η)))
      atTop (fun _ => 0) := by
  let : IsProbabilityMeasure P := hP.probability
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  let F (n : ℕ) (η : C(ℝ, S)) : ℝ := (Real.sqrt (n + 1))⁻¹ *
    (dot e (X 0 ((n + 1 : ℕ) : ℝ≥0) η) - dot e (N ((n + 1 : ℕ) : ℝ≥0) η))
  have hF (n : ℕ) : MemLp (F n) 2 P := by
    have hX := increment_dot_memLp hP φ hφ ((n + 1 : ℕ) : ℝ≥0) (hL2 _) e
    have hN : MemLp (fun η => dot e (N ((n + 1 : ℕ) : ℝ≥0) η)) 2 P := by
      simpa only [hL] using (hN2 ((n + 1 : ℕ) : ℝ≥0)).continuousLinearMap_comp L
    exact (hX.sub hN).const_mul _
  have htime : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hmom := hrem.comp htime
  have heq (n : ℕ) : (∫ η, F n η ^ 2 ∂P) = ((n + 1 : ℝ)⁻¹) *
      ∫ η, (dot e (X 0 ((n + 1 : ℕ) : ℝ≥0) η) -
        dot e (N ((n + 1 : ℕ) : ℝ≥0) η)) ^ 2 ∂P := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with η
    simp only [F, mul_pow, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (n + 1 : ℝ))]
  have hlim : Tendsto (fun n : ℕ => ∫ η, F n η ^ 2 ∂P) atTop (𝓝 0) := by
    simpa only [heq, Function.comp_def, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one] using hmom
  exact tendstoInMeasure_zero_of_integral_sq F hF hlim

end EinsteinFull.External.DFGW
