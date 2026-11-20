import EinsteinFull.External.DFGW.FiniteHorizonFDD
import EinsteinFull.External.DFGW.DFGWScaledFDD
import EinsteinFull.External.DFGW.DFGWMartingaleApproximation

/-! # Finite-dimensional DFGW limits

The DFGW hypotheses imply the covariance formula and joint Brownian limits at finitely many
nonnegative times as the diffusive scale tends to zero.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- Under the DFGW hypotheses, the covariance formula and finite-dimensional
Brownian limits hold at arbitrary positive scales. -/
theorem exists_diffusion_matrix_fdd
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) :
    letI : IsProbabilityMeasure P := hP.probability
    ∃ C D : Mat d,
      C.transpose = C ∧ D.transpose = D ∧
      (∀ e : Vec d, dot e (C.mulVec e) = ∫ η, dot e (compensated X φ 1 η) ^ 2 ∂P) ∧
      (∀ i j : Fin d,
        IntegrableOn (fun t : ℝ => ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ)
          (Set.Ioi 0) ∧
        D i j = C i j - 2 * ∫ t in Set.Ioi (0 : ℝ),
          ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ) ∧
      (∀ e : Vec d, 0 ≤ dot e (D.mulVec e)) ∧
      (∀ (e : Vec d) (t : ℝ≥0), Tendsto
        (fun ε : ℝ => ∫ η, dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t)) ^ 2 ∂P)
        (𝓝[>] 0) (𝓝 (dot e (D.mulVec e) * t))) ∧
      ∃ (W : Measure (Path d)) (hW : IsBrownianLaw D W),
        letI : IsProbabilityMeasure W := hW.1
        ∀ (m : ℕ) (t : Fin m → ℝ≥0),
          TendstoInDistribution (fun (ε : ℝ) η j => ε •
            Y η ((ε⁻¹ ^ 2).toNNReal * t j)) (𝓝[>] 0)
            (fun γ : Path d => fun j => γ (t j)) (fun _ => P) W := by
  let : IsProbabilityMeasure P := hP.probability
  obtain ⟨C, D, hC, hD, hCquad, hentries, hDnonneg, hvariance, W, hW, hunit⟩ :=
    exists_diffusion_matrix_scaled_fdd hP hcoord hX φ hφ hlim hL2 hM
  exact ⟨C, D, hC, hD, hCquad, hentries, hDnonneg, hvariance, W, hW,
    tendstoInDistribution_fdd_of_unit_interval Y hW hunit⟩

end EinsteinFull.External.DFGW
