import EinsteinFull.External.DFGW.MartingaleContinuousTimeCLT
import EinsteinFull.External.DFGW.ScaledMarginalTransfer
import EinsteinFull.External.DFGW.DFGWMartingaleApproximation

/-! # Scalar marginal limits under the DFGW hypotheses

The covariance formula and martingale approximation give scalar normal limits at every
positive diffusive scale.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The DFGW covariance formula and all scalar projected one-time normal limits hold under the
trajectory hypotheses. -/
theorem exists_diffusion_matrix_projected_clt
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
      (∀ (e : Vec d) (t : ℝ≥0), Tendsto
        (fun ε : ℝ => ∫ η, dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t)) ^ 2 ∂P)
        (𝓝[>] 0) (𝓝 (dot e (D.mulVec e) * t))) ∧
      (∀ e : Vec d, ∃ hvar : 0 ≤ dot e (D.mulVec e),
        letI : IsProbabilityMeasure (gaussianReal 0 ⟨dot e (D.mulVec e), hvar⟩) :=
          instIsProbabilityMeasureGaussianReal 0 _
        TendstoInDistribution (fun (ε : ℝ) η => dot e (ε • Y η (ε⁻¹ ^ 2).toNNReal))
          (𝓝[>] 0) (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 ⟨dot e (D.mulVec e), hvar⟩)) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  obtain ⟨C, D, N, hC, hD, hCquad, hentries, hDnonneg, hN, hN2, hstat, hNcov, hrem, hscaled⟩ :=
    exists_diffusion_martingale_approximation hP hcoord hX φ hφ hlim hL2 hM
  refine ⟨C, D, hC, hD, hCquad, hentries, hscaled, ?_⟩
  intro e
  refine ⟨hDnonneg e, ?_⟩
  let σsq : ℝ≥0 := ⟨∫ η, dot e (N 1 η) ^ 2 ∂P, integral_nonneg fun _ => sq_nonneg _⟩
  let : IsProbabilityMeasure (gaussianReal 0 σsq) := instIsProbabilityMeasureGaussianReal 0 σsq
  have hmart := tendstoInDistribution_projected_martingale hP hcoord (measure_ne_top μ Set.univ)
    (measure_ne_top P Set.univ) N hN hN2 hstat e
  have hmart' : TendstoInDistribution (fun (ε : ℝ) η =>
      ε * dot e (N ((ε⁻¹ ^ 2).toNNReal * 1) η)) (𝓝[>] 0) (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 σsq) := by
    simpa only [mul_one] using hmart
  have h := tendstoInDistribution_scaled_increment_of_martingale hP hX φ hφ hL2 N hN2 hstat e
    (hrem e) 1 id hmart'
  simpa only [mul_one, hNcov e] using h

end EinsteinFull.External.DFGW
