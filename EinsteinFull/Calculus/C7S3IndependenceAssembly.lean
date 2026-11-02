import EinsteinFull.Blueprint.G1.Proofs.SbxS5EndpointAverageTransport
import EinsteinFull.Calculus.C6S3SuppliedPathRecenter

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration EinsteinRelation.Regeneration.Renewal
open EinsteinRelation.External.GantertSection7Support

/-- Conditional support for the independence assembly, pending the supplied-path
covariance producer. This does not prove the six-dependency graph root. -/
theorem c7_s3_independence_assuming_supplied_path_recenter
    (h1 : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (h2 : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (h3 : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (h4 : node_app_u3A_regen_u2D_tailsStmt)
    (h5 : node_app_u3A_factorization_u23_slicesStmt)
    (h6 : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hcov : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
      ∀ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCoupling hd Q lam l δ h0.le h1 P K →
      ∀ᵐ a ∂(volume : Measure (Vec d)),
        (∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
        ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
          P p = sbxS9RecenteredPathLaws P a p) :
    node_app_u3A_factorization_u23_independenceStmtV2 :=
  EndpointAverageTransport.independence_assuming_original_path_covariance
    h1 h2 h3 h4 h5 h6 hcov

/-- Assemble independence from all-start covariance on the same good sets. -/
theorem c7_s3_independence_of_all_start_recenter
    (c6_s3_all_start_recenter_covariance : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
      ∀ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCoupling hd Q lam l δ h0.le h1 P K →
      ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ᵐ η ∂Q.measure,
        ∀ x : Vec d, P (x, η) = sbxS9RecenteredPathLaws P a (x, η))
    (h1 : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (h2 : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (h3 : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (h4 : node_app_u3A_regen_u2D_tailsStmt)
    (h5 : node_app_u3A_factorization_u23_slicesStmt)
    (h6 : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt) :
    node_app_u3A_factorization_u23_independenceStmtV2 := by
  apply c7_s3_independence_assuming_supplied_path_recenter h1 h2 h3 h4 h5 h6
  intro d hd Λ₀ r₀ Q lam h0 hlam l δ hl hr hδ hδ1 P K hK
  filter_upwards [c6_s3_all_start_recenter_covariance d hd Λ₀ r₀ Q lam h0 hlam l δ
    hl hr hδ hδ1 P K hK] with a hall
  constructor
  · filter_upwards [hall] with η hη
    exact hη 0
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hall] with p hp
    exact hp p.1

/-- The requested identification yields the original and recentered path
laws on the common spatial and environment good sets. -/
theorem c7_s3_independence_of_requested_identification
    (requested_s3_supplied_gantert_c0_fdd : ∀ {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ)
      (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
      (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd Λ hΛ ω hω lam h0 h1) (I : Finset ℝ≥0),
      r.pathLaw.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (h1 : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (h2 : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (h3 : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (h4 : node_app_u3A_regen_u2D_tailsStmt)
    (h5 : node_app_u3A_factorization_u23_slicesStmt)
    (h6 : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt) :
    node_app_u3A_factorization_u23_independenceStmtV2 := by
  exact c7_s3_independence_of_all_start_recenter
    (c6_s3_all_start_recenter_of_requested_identification
      requested_s3_supplied_gantert_c0_fdd) h1 h2 h3 h4 h5 h6
/-- Independence follows from the six source dependency statements. -/
theorem node_app_u3A_factorization_u23_independence_of_deps
    (h1 : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (h2 : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (h3 : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (h4 : node_app_u3A_regen_u2D_tailsStmt)
    (h5 : node_app_u3A_factorization_u23_slicesStmt)
    (h6 : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt) :
    node_app_u3A_factorization_u23_independenceStmtV2 := by
  apply c7_s3_independence_of_requested_identification _ h1 h2 h3 h4 h5 h6
  intro d hd Λ hΛ ω hω lam h0 h1 r I
  exact EinsteinFull.u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam Λ hΛ hω h0 h1 r I

end EinsteinFull.Blueprint
