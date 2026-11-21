import EinsteinFull.External.DFGW.ProjectionOrthogonality
import EinsteinFull.External.DFGW.MartingaleCovariance

/-! # Variance of projected increments

The second moment of a projected increment is the compensated second moment minus the
second moment of its integrated drift.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The Pythagorean identity for every scalar projection of an increment. -/
theorem integral_dot_increment_sq_add_drift_sq
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (t : ℝ≥0) (hM : MemLp (compensated X φ t) 2 P) (e : Vec d) :
    (∫ η, dot e (X 0 t η) ^ 2 ∂P) +
      (∫ η, (∫ u in (0 : ℝ)..(t : ℝ), dot e (φ (η u))) ^ 2 ∂P) =
      ∫ η, dot e (compensated X φ t η) ^ 2 ∂P := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  have haetime := ae_intervalIntegrable_observable hP φ (hφ.integrable one_le_two) t.coe_nonneg
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  let A : C(ℝ, S) → ℝ := fun η => dot e (∫ u in (0 : ℝ)..(t : ℝ), φ (η u))
  let B : C(ℝ, S) → ℝ := fun η => ∫ u in (0 : ℝ)..(t : ℝ), dot e (φ (η u))
  let M : C(ℝ, S) → ℝ := fun η => dot e (compensated X φ t η)
  let Z : C(ℝ, S) → ℝ := fun η => dot e (X 0 t η)
  have hAB : B =ᵐ[P] A := by
    filter_upwards [haetime] with η hη
    have h := L.intervalIntegral_comp_comm hη
    simpa only [A, B, hL] using h
  have hφdot : MemLp (fun x => dot e (φ x)) 2 μ := by
    unfold dot
    apply memLp_finsetSum
    intro i hi
    exact (hφ.eval i).const_mul (e i)
  have hB : MemLp B 2 P := (time_integral_memLp_and_sq_le hP _ hφdot t.coe_nonneg).1
  have hA : MemLp A 2 P := (memLp_congr_ae hAB).mp hB
  have hZ : MemLp Z 2 P := increment_dot_memLp hP φ hφ t hM e
  have hZA : Integrable (fun η => Z η * A η) P := hZ.integrable_mul hA
  have hzero : (∫ η, Z η * A η ∂P) = 0 := by
    have h := integral_dot_increment_mul_time_integral_eq_zero hP hX φ hφ _ hφdot t hM e
    have he : (∫ η, Z η * B η ∂P) = ∫ η, Z η * A η ∂P :=
      integral_congr_ae (hAB.mono fun η hη => by simp only; rw [hη])
    exact he ▸ h
  have hsq : (∫ η, M η ^ 2 ∂P) =
      (∫ η, Z η ^ 2 ∂P) - 2 * (∫ η, Z η * A η ∂P) + ∫ η, A η ^ 2 ∂P := by
    have he : (fun η => M η ^ 2) =
        (fun η => (Z η ^ 2 - 2 * (Z η * A η)) + A η ^ 2) := by
      funext η
      simp only [M, Z, A, compensated, dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      ring
    have hintsub : Integrable (fun η => Z η ^ 2 - 2 * (Z η * A η)) P := by
      apply (hZ.integrable_sq.sub (hZA.const_mul 2)).congr
      exact ae_of_all P fun η => by simp only [Pi.sub_apply]
    rw [he, integral_add hintsub hA.integrable_sq,
      integral_sub hZ.integrable_sq (hZA.const_mul 2), integral_const_mul]
  have hsqAB : (∫ η, B η ^ 2 ∂P) = ∫ η, A η ^ 2 ∂P :=
    integral_congr_ae (hAB.fun_comp (fun x : ℝ => x ^ 2))
  change (∫ η, Z η ^ 2 ∂P) + (∫ η, B η ^ 2 ∂P) = ∫ η, M η ^ 2 ∂P
  rw [hsqAB, hsq, hzero]
  ring

end EinsteinFull.External.DFGW
