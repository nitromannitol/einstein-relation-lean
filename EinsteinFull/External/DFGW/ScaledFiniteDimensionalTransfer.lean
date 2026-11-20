import EinsteinFull.External.DFGW.ScaledRemainderInMeasure
import EinsteinFull.External.DFGW.FiniteDimensionalMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Transfer of finite-dimensional limits

The diffusively scaled increment process and its martingale approximation have asymptotically
the same finite-dimensional laws.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} [IsProbabilityMeasure P] {μ : Measure S}
variable {T : ℝ≥0 → Kernel S S} {X : ℝ → ℝ → C(ℝ, S) → Vec d}
variable {Y : C(ℝ, S) → Path d}
variable {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]

/-- The scaled vector remainder at finitely many times converges to zero in measure. -/
theorem tendstoInMeasure_scaled_finite_dimensional_remainder
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hX : Draft.IsDFGWTrajectoryFamily P X Y)
    (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (hrem : ∀ e : Vec d, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (dot e (X 0 t η) - dot e (N t η)) ^ 2 ∂P) atTop (𝓝 0))
    {n : ℕ} (times : Fin n → ℝ≥0) :
    TendstoInMeasure P (fun (ε : ℝ) η k =>
      ε • Y η ((ε⁻¹ ^ 2).toNNReal * times k) -
        ε • N ((ε⁻¹ ^ 2).toNNReal * times k) η) (𝓝[>] 0) (fun _ => 0) := by
  apply tendstoInMeasure_pi_zero
  intro k
  apply tendstoInMeasure_pi_zero
  intro i
  have h := tendstoInMeasure_scaled_martingale_remainder hP hX φ hφ hL2 N hN2 hstat
    (unitVector i) (hrem (unitVector i)) (times k)
  simpa only [dot, unitVector, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h

/-- Joint weak convergence at finitely many times transfers from the scaled martingale to the
increment process. -/
theorem tendstoInDistribution_scaled_finite_dimensional_of_martingale
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hX : Draft.IsDFGWTrajectoryFamily P X Y)
    (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (hrem : ∀ e : Vec d, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (dot e (X 0 t η) - dot e (N t η)) ^ 2 ∂P) atTop (𝓝 0))
    {n : ℕ} (times : Fin n → ℝ≥0) (Z : Ω' → Fin n → Vec d)
    (hlimit : TendstoInDistribution (fun (ε : ℝ) η k =>
      ε • N ((ε⁻¹ ^ 2).toNNReal * times k) η) (𝓝[>] 0) Z (fun _ => P) ν) :
    TendstoInDistribution (fun (ε : ℝ) η k =>
      ε • Y η ((ε⁻¹ ^ 2).toNNReal * times k)) (𝓝[>] 0) Z (fun _ => P) ν := by
  let A : ℝ → C(ℝ, S) → Fin n → Vec d := fun ε η k =>
    ε • Y η ((ε⁻¹ ^ 2).toNNReal * times k)
  let B : ℝ → C(ℝ, S) → Fin n → Vec d := fun ε η k =>
    ε • N ((ε⁻¹ ^ 2).toNNReal * times k) η
  have hdiff : TendstoInMeasure P (A - B) (𝓝[>] 0) 0 :=
    tendstoInMeasure_scaled_finite_dimensional_remainder hP hX φ hφ hL2 N hN2 hstat hrem times
  have hA (ε : ℝ) : AEMeasurable (A ε) P := by
    have hm : Measurable (A ε) := by
      apply measurable_pi_iff.mpr
      intro k
      have hc : Continuous (fun γ : Path d => ε • γ ((ε⁻¹ ^ 2).toNNReal * times k)) :=
        (continuous_eval_const ((ε⁻¹ ^ 2).toNNReal * times k)).const_smul ε
      change Measurable ((fun γ : Path d => ε • γ ((ε⁻¹ ^ 2).toNNReal * times k)) ∘ Y)
      exact hc.measurable.comp hX.version_measurable
    exact hm.aemeasurable
  exact tendstoInDistribution_of_tendstoInMeasure_sub A Z hlimit hdiff hA

end EinsteinFull.External.DFGW
