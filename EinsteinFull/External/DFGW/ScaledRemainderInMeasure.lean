import EinsteinFull.External.DFGW.ScaledMartingaleRemainder
import EinsteinFull.External.DFGW.MeanSquareConvergence

/-! # Scaled remainder converges in measure

The fixed-time diffusively scaled difference between an increment and its martingale
approximation converges to zero in measure, in every scalar projection.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The scaled difference of the increment and a square-integrable approximation is
square-integrable at each fixed time and scale. -/
theorem scaled_martingale_remainder_memLp
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hX : Draft.IsDFGWTrajectoryFamily P X Y)
    (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : ∀ t, MemLp (N t) 2 P)
    (e : Vec d) (t : ℝ≥0) (ε : ℝ) :
    MemLp (fun η => dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t)) -
      ε * dot e (N ((ε⁻¹ ^ 2).toNNReal * t) η)) 2 P := by
  let u : ℝ≥0 := (ε⁻¹ ^ 2).toNNReal * t
  have hA : MemLp (fun η => dot e (X 0 u η)) 2 P :=
    increment_dot_memLp hP φ hφ u (hL2 u) e
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  have hB : MemLp (fun η => dot e (N u η)) 2 P := by
    simpa only [Function.comp_apply, hL] using (hN2 u).continuousLinearMap_comp L
  have hsum : MemLp (fun η => ε * dot e (X 0 u η) - ε * dot e (N u η)) 2 P :=
    (hA.const_mul ε).sub (hB.const_mul ε)
  apply (memLp_congr_ae ?_).2 hsum
  filter_upwards [hX.version] with η hη
  change dot e (ε • Y η u) - ε * dot e (N u η) = _
  rw [hη]
  have hdot (v : Vec d) : dot e (ε • v) = ε * dot e v := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hdot]

/-- Diffusively scaled projection errors converge to zero in measure at each fixed time. -/
theorem tendstoInMeasure_scaled_martingale_remainder
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hX : Draft.IsDFGWTrajectoryFamily P X Y)
    (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d)
    (hrem : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (dot e (X 0 t η) - dot e (N t η)) ^ 2 ∂P) atTop (𝓝 0)) (t : ℝ≥0) :
    TendstoInMeasure P (fun ε η => dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t)) -
      ε * dot e (N ((ε⁻¹ ^ 2).toNNReal * t) η)) (𝓝[>] 0) (fun _ => 0) := by
  let : IsProbabilityMeasure P := hP.probability
  exact tendstoInMeasure_zero_of_integral_sq _
    (fun ε => scaled_martingale_remainder_memLp hP hX φ hφ hL2 N hN2 e t ε)
    (tendsto_scaled_martingale_remainder_sq hX N hstat e hrem t)

end EinsteinFull.External.DFGW
