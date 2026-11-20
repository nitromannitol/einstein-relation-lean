import EinsteinFull.External.DFGW.ReflectionDrift
import EinsteinFull.External.DFGW.IncrementL2

/-! # Orthogonality of increment projections

Every scalar projection of an antisymmetric increment is orthogonal to an integrated state
observable.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- A projected increment is orthogonal to an integrated state observable. -/
theorem integral_dot_increment_mul_time_integral_eq_zero
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (g : S → ℝ) (hg : MemLp g 2 μ) (t : ℝ≥0)
    (hM : MemLp (compensated X φ t) 2 P) (e : Vec d) :
    (∫ η, dot e (X 0 t η) * (∫ u in (0 : ℝ)..(t : ℝ), g (η u)) ∂P) = 0 := by
  let A : C(ℝ, S) → ℝ := fun η => ∫ u in (0 : ℝ)..(t : ℝ), g (η u)
  have hA : MemLp A 2 P := (time_integral_memLp_and_sq_le hP g hg t.coe_nonneg).1
  have hmem (i : Fin d) : MemLp (fun η => X 0 t η i) 2 P :=
    increment_coordinate_memLp hP φ hφ t hM i
  have hint (i : Fin d) : Integrable (fun η => (e i * X 0 t η i) * A η) P :=
    ((hmem i).const_mul (e i)).integrable_mul hA
  calc
    _ = ∫ η, ∑ i : Fin d, (e i * X 0 t η i) * A η ∂P := by
      apply integral_congr_ae
      filter_upwards with η
      simp only [dot, Finset.sum_mul, A]
    _ = ∑ i : Fin d, ∫ η, (e i * X 0 t η i) * A η ∂P := by
      rw [integral_finsetSum]
      intro i hi
      exact hint i
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hz := integral_increment_mul_time_integral_eq_zero hP hX g hg t i (hmem i)
      have he : (fun η => (e i * X 0 t η i) * A η) =
          (fun η => e i * (X 0 t η i * A η)) := by
        funext η
        ring
      rw [he, integral_const_mul, hz, mul_zero]

end EinsteinFull.External.DFGW
