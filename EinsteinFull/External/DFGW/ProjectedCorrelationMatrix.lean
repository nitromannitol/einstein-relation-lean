import EinsteinFull.External.DFGW.ProjectedVelocityCorrelation

/-! # Matrix form of projected velocity correlations

The integrated autocorrelation of a scalar projection is the quadratic form of the matrix
of integrated coordinate correlations.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The projected integrated autocorrelation is the quadratic form of coordinate
correlation integrals. -/
theorem integral_projected_velocity_autocorrelation_eq_sum
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (e : Vec d)
    (hg : MemLp (fun x => dot e (φ x)) 2 μ) :
    (∫ t in Set.Ioi (0 : ℝ), inner ℝ (hg.toLp (fun x => dot e (φ x)))
      (transitionOperator hP t.toNNReal (hg.toLp (fun x => dot e (φ x))))) =
      ∑ i : Fin d, ∑ j : Fin d, (e i * e j) *
        ∫ t in Set.Ioi (0 : ℝ), ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ := by
  let v : Fin d → Lp ℝ 2 μ := fun i => (hφ.eval i).toLp (fun x => φ x i)
  have hpair (i j : Fin d) : IntegrableOn
      (fun t : ℝ => (e i * e j) * (∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ))
      (Set.Ioi 0) :=
    (integrableOn_velocity_kernel_correlation hP hX φ hφ hlim hL2 hM i j).const_mul _
  have hpoint (t : ℝ) : inner ℝ (hg.toLp (fun x => dot e (φ x)))
      (transitionOperator hP t.toNNReal (hg.toLp (fun x => dot e (φ x)))) =
      ∑ i : Fin d, ∑ j : Fin d, (e i * e j) *
        (∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ) := by
    rw [projected_toLp_eq_sum φ hφ e hg]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_mul_kernel_eq_inner hP _ (fun x => φ x i) (fun x => φ x j)
      (hφ.eval i) (hφ.eval j)]
    have hc : inner ℝ (v j) (transitionOperator hP t.toNNReal (v i)) =
        inner ℝ (v i) (transitionOperator hP t.toNNReal (v j)) := by
      rw [← inner_transitionOperator hP t.toNNReal (v i) (v j), real_inner_comm]
    change e i * (e j * inner ℝ (v j) (transitionOperator hP t.toNNReal (v i))) =
      (e i * e j) * inner ℝ (v i) (transitionOperator hP t.toNNReal (v j))
    rw [hc]
    ring
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ), ∑ i : Fin d, ∑ j : Fin d, (e i * e j) *
        (∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∑ i : Fin d, ∑ j : Fin d, ∫ t in Set.Ioi (0 : ℝ), (e i * e j) *
        (∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        intro j hj
        exact hpair i j
      · intro i hi
        apply integrable_finsetSum
        intro j hj
        exact hpair i j
    _ = _ := by simp only [integral_const_mul]

end EinsteinFull.External.DFGW
