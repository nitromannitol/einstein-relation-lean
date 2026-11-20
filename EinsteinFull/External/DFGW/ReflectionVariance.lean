import EinsteinFull.External.DFGW.ReflectionDrift

/-! # Reflection identity for second moments

Orthogonality of the antisymmetric increment and the symmetric integrated drift gives a
Pythagorean identity for their second moments.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The squared increment and squared integrated drift add to the squared compensated
increment. -/
theorem integral_increment_sq_add_drift_sq
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (t : ℝ≥0) (hM : MemLp (compensated X φ t) 2 P) (i : Fin d) :
    (∫ η, (X 0 t η i) ^ 2 ∂P) +
      (∫ η, (∫ u in (0 : ℝ)..(t : ℝ), φ (η u) i) ^ 2 ∂P) =
      ∫ η, (compensated X φ t η i) ^ 2 ∂P := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  have hφint : Integrable φ μ := hφ.integrable one_le_two
  have haetime := ae_intervalIntegrable_observable hP φ hφint t.coe_nonneg
  let A : C(ℝ, S) → ℝ := fun η => (∫ u in (0 : ℝ)..(t : ℝ), φ (η u)) i
  let B : C(ℝ, S) → ℝ := fun η => ∫ u in (0 : ℝ)..(t : ℝ), φ (η u) i
  let M : C(ℝ, S) → ℝ := fun η => compensated X φ t η i
  let Z : C(ℝ, S) → ℝ := fun η => X 0 t η i
  have hAB : B =ᵐ[P] A := by
    filter_upwards [haetime] with η hη
    have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).intervalIntegral_comp_comm hη
    simpa only [A, B, ContinuousLinearMap.proj_apply] using h
  have hB : MemLp B 2 P := (time_integral_memLp_and_sq_le hP _ (hφ.eval i) t.coe_nonneg).1
  have hA : MemLp A 2 P := (memLp_congr_ae hAB).mp hB
  have hM' : MemLp M 2 P := hM.eval i
  have hZ : MemLp Z 2 P := by
    apply (memLp_congr_ae ?_).mp (hM'.add hA)
    exact ae_of_all P fun η => by simp only [M, A, Z, compensated, Pi.sub_apply, Pi.add_apply]; ring
  have hZA : Integrable (fun η => Z η * A η) P := hZ.integrable_mul hA
  have hzero : (∫ η, Z η * A η ∂P) = 0 := by
    have h := integral_increment_mul_time_integral_eq_zero hP hX _ (hφ.eval i) t i hZ
    have he : (∫ η, Z η * B η ∂P) = ∫ η, Z η * A η ∂P :=
      integral_congr_ae (hAB.mono fun η hη => by simp only; rw [hη])
    exact he ▸ h
  have hsq : (∫ η, M η ^ 2 ∂P) =
      (∫ η, Z η ^ 2 ∂P) - 2 * (∫ η, Z η * A η ∂P) + ∫ η, A η ^ 2 ∂P := by
    have he : (fun η => M η ^ 2) =
        (fun η => (Z η ^ 2 - 2 * (Z η * A η)) + A η ^ 2) := by
      funext η
      simp only [M, Z, A, compensated, Pi.sub_apply]
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
