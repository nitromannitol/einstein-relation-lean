import EinsteinFull.External.DFGW.ScaledVarianceLimit

/-! # Diffusively scaled second moments

The diffusion matrix satisfies the covariance formula and governs all diffusively scaled
projected second moments.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The diffusion matrix satisfies the covariance and scaled second-moment conclusions. -/
theorem exists_diffusion_matrix_scaled_variance
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) :
    ∃ C D : Mat d,
      C.transpose = C ∧ D.transpose = D ∧
      (∀ e : Vec d, dot e (C.mulVec e) =
        ∫ η, dot e (X 0 1 η - ∫ τ in (0 : ℝ)..1, φ (η τ)) ^ 2 ∂P) ∧
      (∀ i j : Fin d,
        IntegrableOn (fun t : ℝ => ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ)
          (Set.Ioi 0) ∧
        D i j = C i j - 2 * ∫ t in Set.Ioi (0 : ℝ),
          ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ) ∧
      (∀ (e : Vec d) (t : ℝ≥0), Tendsto
        (fun ε : ℝ => ∫ η, dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t)) ^ 2 ∂P)
        (𝓝[>] 0) (𝓝 (dot e (D.mulVec e) * t))) ∧
      ∀ e : Vec d, 0 ≤ dot e (D.mulVec e) := by
  obtain ⟨C, D, hC, hD, hCquad, hentries, hlimit, hnonneg⟩ :=
    exists_diffusion_matrix_variance_limit hP hX φ hφ hlim hL2 hM
  refine ⟨C, D, hC, hD, ?_, hentries, ?_, hnonneg⟩
  · intro e
    exact hCquad e
  · intro e t
    exact tendsto_scaled_dot_increment_sq hX e t D (hlimit e)

end EinsteinFull.External.DFGW
