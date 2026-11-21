import EinsteinFull.External.DFGW.DiagonalCorrelation

/-! # Absolute convergence of the velocity covariance integral

The mean-velocity energy estimate implies absolute time integrability of every coordinate
correlation in the diffusion matrix formula.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- Every mixed coordinate correlation of the mean velocity is absolutely integrable in time. -/
theorem integrableOn_velocity_kernel_correlation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (i j : Fin d) :
    IntegrableOn (fun t : ℝ => ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ)
      (Set.Ioi 0) := by
  have hdiag : ∀ k : Fin d,
      IntegrableOn (fun t : ℝ => ∫ x, φ x k * ∫ y, φ y k ∂T t.toNNReal x ∂μ)
        (Set.Ioi 0) := by
    intro k
    simp_rw [integral_mul_kernel_eq_inner hP _ (fun x => φ x k) (fun x => φ x k)
      (hφ.eval k) (hφ.eval k)]
    apply integrableOn_autocorrelation_of_resolvent_bound hP _
      (∫ η, (compensated X φ 1 η k) ^ 2 ∂P)
    exact fun lam => inner_velocity_transitionResolvent_le hP hX φ hφ hlim hL2 hM k lam
  exact integrableOn_kernel_correlation_of_diagonal hP _ _ (hφ.eval i) (hφ.eval j)
    (hdiag i) (hdiag j)

end EinsteinFull.External.DFGW
