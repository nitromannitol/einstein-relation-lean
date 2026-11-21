import EinsteinFull.External.DFGW.IncrementOneTimeCLT
import EinsteinFull.External.DFGW.DFGWMartingaleApproximation

/-! # Scalar one-time limits under the DFGW hypotheses

The covariance formula and martingale approximation imply scalar normal limits for increments
on the diffusively scaled integer grid.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The DFGW covariance formula and scalar normal limits hold on the diffusively scaled
integer grid. -/
theorem exists_diffusion_matrix_projected_grid_clt
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
      (∀ e : Vec d, ∃ hvar : 0 ≤ dot e (D.mulVec e),
        letI : IsProbabilityMeasure (gaussianReal 0 ⟨dot e (D.mulVec e), hvar⟩) :=
          instIsProbabilityMeasureGaussianReal 0 _
        TendstoInDistribution (fun (n : ℕ) η => (Real.sqrt (n + 1))⁻¹ *
          dot e (X 0 ((n + 1 : ℕ) : ℝ≥0) η)) atTop (id : ℝ → ℝ)
          (fun _ => P) (gaussianReal 0 ⟨dot e (D.mulVec e), hvar⟩)) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  obtain ⟨C, D, N, hC, hD, hCquad, hentries, hDnonneg, hN, hN2, hstat, hNcov, hrem, _⟩ :=
    exists_diffusion_martingale_approximation hP hcoord hX φ hφ hlim hL2 hM
  refine ⟨C, D, hC, hD, hCquad, hentries, ?_⟩
  intro e
  refine ⟨hDnonneg e, ?_⟩
  have h := tendstoInDistribution_projected_increment_grid hP hcoord (measure_ne_top μ Set.univ)
    (measure_ne_top P Set.univ) φ hφ hL2 N hN hN2 hstat e (hrem e)
  simpa only [hNcov e] using h

end EinsteinFull.External.DFGW
