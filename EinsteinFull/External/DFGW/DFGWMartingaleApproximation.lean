import EinsteinFull.External.DFGW.ApproximationCovariance
import EinsteinFull.External.DFGW.ScaledVarianceLimit

/-! # Martingale approximation and diffusion matrix

The DFGW increment family admits a stationary-increment vector martingale approximation whose
covariance is the diffusion matrix and whose fixed-time mean-square remainder is sublinear.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- DFGW covariance formula and vector martingale approximation, with fixed-time sublinear
mean-square remainder. -/
theorem exists_diffusion_martingale_approximation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) :
    ∃ (C D : Mat d) (N : ℝ≥0 → C(ℝ, S) → Vec d),
      C.transpose = C ∧ D.transpose = D ∧
      (∀ e : Vec d, dot e (C.mulVec e) = ∫ η, dot e (compensated X φ 1 η) ^ 2 ∂P) ∧
      (∀ i j : Fin d,
        IntegrableOn (fun t : ℝ => ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ)
          (Set.Ioi 0) ∧
        D i j = C i j - 2 * ∫ t in Set.Ioi (0 : ℝ),
          ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ) ∧
      (∀ e : Vec d, 0 ≤ dot e (D.mulVec e)) ∧
      Martingale N Draft.dfgwPast P ∧
      (∀ t, MemLp (N t) 2 P) ∧
      (∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
        fun η => N t (Draft.dfgwShift s η)) ∧
      (∀ e : Vec d, dot e (D.mulVec e) = ∫ η, dot e (N 1 η) ^ 2 ∂P) ∧
      (∀ e : Vec d, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
        ∫ η, (dot e (X 0 t η) - dot e (N t η)) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ (e : Vec d) (t : ℝ≥0), Tendsto
        (fun ε : ℝ => ∫ η, dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t)) ^ 2 ∂P)
        (𝓝[>] 0) (𝓝 (dot e (D.mulVec e) * t))) := by
  obtain ⟨C, D, hC, hD, hCquad, hentries, hvariance, hDnonneg⟩ :=
    exists_diffusion_matrix_variance_limit hP hX φ hφ hlim hL2 hM
  obtain ⟨N, hN, hN2, hstat, hcoorderr⟩ :=
    exists_vector_increment_martingale_approximation hP hcoord hX φ hφ hlim hL2 hM
  refine ⟨C, D, N, hC, hD, hCquad, hentries, hDnonneg, hN, hN2, hstat, ?_, ?_, ?_⟩
  · intro e
    exact (projected_martingale_variance_eq_limit hP φ hφ hL2 N hN hN2 hstat hcoorderr e
      (dot e (D.mulVec e)) (hvariance e)).symm
  · intro e
    exact tendsto_projected_remainder_of_coordinates hP φ hφ hL2 N hN2 hcoorderr e
  · intro e t
    exact tendsto_scaled_dot_increment_sq hX e t D (hvariance e)

end EinsteinFull.External.DFGW
