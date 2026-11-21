import EinsteinFull.External.DFGW.GridBrownianFDD
import EinsteinFull.External.DFGW.DFGWMartingaleApproximation

/-! # Finite-dimensional DFGW limits along the diffusive grid

The DFGW hypotheses imply the covariance formula and joint Brownian limits at finitely many
unit-interval times along inverse square-root grid scales.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- Under the DFGW hypotheses, the covariance formula and grid-scale finite-dimensional
Brownian limits hold. -/
theorem exists_diffusion_matrix_grid_fdd
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
      ∃ (W : Measure (Path d)) (hW : IsBrownianLaw D W),
        letI : IsProbabilityMeasure W := hW.1
        ∀ (m : ℕ) (t : Fin m → ℝ≥0), (∀ j, t j ≤ 1) →
          TendstoInDistribution (fun n η j => gridScale n •
            Y η (((gridScale n)⁻¹ ^ 2).toNNReal * t j)) atTop
            (fun γ : Path d => fun j => γ (t j)) (fun _ => P) W := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  obtain ⟨C, D, N, hC, hD, hCquad, hentries, hDnonneg, hN, hN2, hstat, hNcov, hrem, _⟩ :=
    exists_diffusion_martingale_approximation hP hcoord hX φ hφ hlim hL2 hM
  obtain ⟨W, hW⟩ := exists_brownianLaw d D hD hDnonneg
  refine ⟨C, D, hC, hD, hCquad, hentries, hDnonneg, W, hW, ?_⟩
  intro m t ht
  exact tendstoInDistribution_grid_process_fdd hP hcoord (measure_ne_top μ Set.univ)
    (measure_ne_top P Set.univ) hX φ hφ hL2 N hN hN2 hstat hrem D hD hNcov W hW m t ht

end EinsteinFull.External.DFGW
