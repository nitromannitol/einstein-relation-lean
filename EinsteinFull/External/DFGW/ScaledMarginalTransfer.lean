import EinsteinFull.External.DFGW.ScaledRemainderInMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Transfer of scaled marginal convergence

At any fixed time, convergence in distribution of a scaled martingale projection transfers
to the corresponding increment projection.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} [IsProbabilityMeasure P] {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}
variable {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]

/-- Fixed-time weak convergence of the scaled martingale transfers to the increment projection. -/
theorem tendstoInDistribution_scaled_increment_of_martingale
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hX : Draft.IsDFGWTrajectoryFamily P X Y)
    (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d)
    (hrem : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (dot e (X 0 t η) - dot e (N t η)) ^ 2 ∂P) atTop (𝓝 0)) (t : ℝ≥0)
    (Z : Ω' → ℝ)
    (hlimit : TendstoInDistribution (fun (ε : ℝ) η => ε * dot e (N ((ε⁻¹ ^ 2).toNNReal * t) η))
      (𝓝[>] 0) Z (fun _ => P) ν) :
    TendstoInDistribution (fun (ε : ℝ) η => dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t)))
      (𝓝[>] 0) Z (fun _ => P) ν := by
  let : IsProbabilityMeasure P := hP.probability
  let A : ℝ → C(ℝ, S) → ℝ := fun ε η => dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t))
  let B : ℝ → C(ℝ, S) → ℝ := fun ε η => ε * dot e (N ((ε⁻¹ ^ 2).toNNReal * t) η)
  have hdiff : TendstoInMeasure P (A - B) (𝓝[>] 0) 0 :=
    tendstoInMeasure_scaled_martingale_remainder hP hX φ hφ hL2 N hN2 hstat e hrem t
  have hA (ε : ℝ) : AEMeasurable (A ε) P := by
    let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
    have hL (v : Vec d) : L v = dot e v := by
      simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
    have hv : Continuous (fun γ : Path d => ε • γ ((ε⁻¹ ^ 2).toNNReal * t)) :=
      (continuous_eval_const ((ε⁻¹ ^ 2).toNNReal * t)).const_smul ε
    have hc : Continuous (fun γ : Path d => L (ε • γ ((ε⁻¹ ^ 2).toNNReal * t))) :=
      L.continuous.comp hv
    change AEMeasurable ((fun γ : Path d => dot e (ε • γ ((ε⁻¹ ^ 2).toNNReal * t))) ∘ Y) P
    simpa only [hL] using (hc.measurable.comp hX.version_measurable).aemeasurable
  exact tendstoInDistribution_of_tendstoInMeasure_sub A Z hlimit hdiff hA

end EinsteinFull.External.DFGW
