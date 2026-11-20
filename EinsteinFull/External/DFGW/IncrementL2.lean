import EinsteinFull.External.DFGW.TimeIntegralBound
import EinsteinFull.External.DFGW.VarianceAdditivity

/-! # Square integrability of increments

The increment is square-integrable when its compensated martingale and mean forward velocity
are square-integrable.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d}

/-- Every coordinate of an increment is square-integrable. -/
theorem increment_coordinate_memLp (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (φ : S → Vec d) (hφ : MemLp φ 2 μ) (t : ℝ≥0)
    (hM : MemLp (compensated X φ t) 2 P) (i : Fin d) :
    MemLp (fun η => X 0 t η i) 2 P := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  have haetime := ae_intervalIntegrable_observable hP φ (hφ.integrable one_le_two) t.coe_nonneg
  let A : C(ℝ, S) → ℝ := fun η => (∫ u in (0 : ℝ)..(t : ℝ), φ (η u)) i
  let B : C(ℝ, S) → ℝ := fun η => ∫ u in (0 : ℝ)..(t : ℝ), φ (η u) i
  have hAB : B =ᵐ[P] A := by
    filter_upwards [haetime] with η hη
    have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).intervalIntegral_comp_comm hη
    simpa only [A, B, ContinuousLinearMap.proj_apply] using h
  have hB := (time_integral_memLp_and_sq_le hP (fun x => φ x i) (hφ.eval i) t.coe_nonneg).1
  have hA : MemLp A 2 P := (memLp_congr_ae hAB).mp hB
  apply (memLp_congr_ae ?_).mp ((hM.eval i).add hA)
  exact ae_of_all P fun η => by simp only [A, compensated, Pi.sub_apply, Pi.add_apply]; ring

/-- Every scalar projection of an increment is square-integrable. -/
theorem increment_dot_memLp (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (φ : S → Vec d) (hφ : MemLp φ 2 μ) (t : ℝ≥0)
    (hM : MemLp (compensated X φ t) 2 P) (e : Vec d) :
    MemLp (fun η => dot e (X 0 t η)) 2 P := by
  unfold dot
  apply memLp_finsetSum
  intro i hi
  exact (increment_coordinate_memLp hP φ hφ t hM i).const_mul (e i)

end EinsteinFull.External.DFGW
