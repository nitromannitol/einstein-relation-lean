import EinsteinFull.External.DFGW.CorrelationLinear
import EinsteinFull.External.DFGW.VelocityCorrelation
import EinsteinFull.External.DFGW.ProjectedLp

/-! # Correlation of projected velocities

Every scalar projection of the mean velocity has integrable semigroup autocorrelation.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The autocorrelation of a finite sum is integrable when the summands' autocorrelations are. -/
theorem integrableOn_autocorrelation_sum (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    {ι : Type*} (s : Finset ι) (v : ι → Lp ℝ 2 μ)
    (hv : ∀ i ∈ s, IntegrableOn
      (fun t : ℝ => inner ℝ (v i) (transitionOperator hP t.toNNReal (v i))) (Set.Ioi 0)) :
    IntegrableOn (fun t : ℝ => inner ℝ (∑ i ∈ s, v i)
      (transitionOperator hP t.toNNReal (∑ i ∈ s, v i))) (Set.Ioi 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, map_zero, inner_zero_left] using
      (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioi 0))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    apply integrableOn_autocorrelation_add hP
    · exact hv i (Finset.mem_insert_self i s)
    · exact ih (fun j hj => hv j (Finset.mem_insert_of_mem hj))

/-- The scalar projection of the mean forward velocity has integrable autocorrelation. -/
theorem integrableOn_projected_velocity_autocorrelation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (e : Vec d)
    (hg : MemLp (fun x => dot e (φ x)) 2 μ) :
    IntegrableOn (fun t : ℝ => inner ℝ (hg.toLp (fun x => dot e (φ x)))
      (transitionOperator hP t.toNNReal (hg.toLp (fun x => dot e (φ x))))) (Set.Ioi 0) := by
  let v : Fin d → Lp ℝ 2 μ := fun i => e i • ((hφ.eval i).toLp (fun x => φ x i))
  have hv : ∀ i : Fin d, IntegrableOn
      (fun t : ℝ => inner ℝ (v i) (transitionOperator hP t.toNNReal (v i))) (Set.Ioi 0) := by
    intro i
    apply integrableOn_autocorrelation_smul hP
    have h := integrableOn_velocity_kernel_correlation hP hX φ hφ hlim hL2 hM i i
    simpa only [integral_mul_kernel_eq_inner hP _ (fun x => φ x i) (fun x => φ x i)
      (hφ.eval i) (hφ.eval i)] using h
  have hsum : hg.toLp (fun x => dot e (φ x)) = ∑ i : Fin d, v i :=
    projected_toLp_eq_sum φ hφ e hg
  rw [hsum]
  exact integrableOn_autocorrelation_sum hP Finset.univ v (fun i _ => hv i)

end EinsteinFull.External.DFGW
