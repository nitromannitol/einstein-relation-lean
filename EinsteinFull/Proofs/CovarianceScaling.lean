import EinsteinFull.Blueprint.Foundation.Proofs.CanonicalLaw
import EinsteinFull.Blueprint.Foundation.Proofs.CorrectorConstruction
import EinsteinFull.Blueprint.Foundation.Proofs.ReducedBounds
import EinsteinFull.Blueprint.Foundation.Proofs.ReducedDerivatives
import EinsteinFull.Blueprint.Foundation.Proofs.StationaryEnvironment
import EinsteinFull.Blueprint.G3.Proofs.C10BlockCovRate
import EinsteinFull.Blueprint.G3.Proofs.C10TestBlocksReduction
import EinsteinFull.Blueprint.G3.Proofs.C1TestCLTReduction
import EinsteinFull.Blueprint.G3.Proofs.C2BlockBoundary
import EinsteinFull.Blueprint.G3.Proofs.C2BlockCLT
import EinsteinFull.Blueprint.G3.Proofs.C2BlockChange
import EinsteinFull.Blueprint.G3.Proofs.C2SmoothMoments
import EinsteinFull.Blueprint.G3.Proofs.C2TestReplacement
import EinsteinFull.Blueprint.G3.Proofs.C6CoarseIdentificationClosure
import EinsteinFull.Blueprint.G3.Proofs.C9JointLocalizationClosure
import EinsteinFull.Blueprint.G3.Proofs.ClockBlocks
import EinsteinFull.Blueprint.G3.Proofs.S1BlockRecursion
import EinsteinFull.Blueprint.G3.Proofs.S1Closure
import EinsteinFull.Blueprint.G3.Proofs.W2Reduction1
import EinsteinFull.Blueprint.G3.Proofs.W2Reduction2
import EinsteinFull.Blueprint.Roots.Proofs.W4Queue0410

namespace EinsteinFull.Proofs

open EinsteinFull.Blueprint

/-- Proposition 5.1, composed from the exact reviewed graph reductions. -/
theorem covariance_scaling : node_p_u3A_covarianceStmt := by
  have h0 : node_eq_u2E_reduced_u2D_boundsStmt :=
    node_eq_u2E_reduced_u2D_bounds_of_deps
  have h1 : node_e_u3A_parametersStmt :=
    node_e_u3A_parameters_of_deps h0
  have h2 : node_e_u3A_clock_u2D_l2Stmt :=
    node_e_u3A_clock_u2D_l2_of_deps
  have h3 : node_e_u3A_test_u2D_cltStmt :=
    node_e_u3A_test_u2D_clt_of_deps h2
  have h4 : node_stationary_u2D_environment_u23_canonical_u2D_lawStmt :=
    node_stationary_u2D_environment_u23_canonical_u2D_law_of_deps h0
  have h5 : node_stationary_u2D_environmentStmt :=
    node_stationary_u2D_environment_of_deps h4
  have h6 : node_corrector_u2D_constructionStmt :=
    node_corrector_u2D_construction_of_deps h5 h0
  have h7 : node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt :=
    node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps h0
  have h8 : node_corrector_u2D_construction_u23_smooth_u2D_momentsStmt :=
    node_corrector_u2D_construction_u23_smooth_u2D_moments_of_deps h6 h7
  have h9 : node_p_u3A_covariance_u23_coarse_u2D_identificationStmt :=
    node_p_u3A_covariance_u23_coarse_u2D_identification_of_deps h8
  have h10 : node_p_u3A_covariance_u23_joint_u2D_localizationStmt :=
    node_p_u3A_covariance_u23_joint_u2D_localization_of_deps h1 h2
  have h11 : node_p_u3A_covariance_u23_test_u2D_replacementStmt :=
    node_p_u3A_covariance_u23_test_u2D_replacement_of_deps h1 h3 h9 h10
  have h12 : node_p_u3A_covariance_u23_clock_u2D_blocksStmt :=
    node_p_u3A_covariance_u23_clock_u2D_blocks_of_deps h2 h10 h1
  have h13 : node_e_u3A_block_u2D_cltStmt :=
    node_e_u3A_block_u2D_clt_of_deps h10 h12
  have h14 : node_e_u3A_block_u2D_boundaryStmt :=
    node_e_u3A_block_u2D_boundary_of_deps h10 h12
  have h15 : node_e_u3A_block_u2D_changeStmt :=
    node_e_u3A_block_u2D_change_of_deps h10 h12
  have h16 : node_e_u3A_block_u2D_recursionStmt :=
    node_e_u3A_block_u2D_recursion_of_deps h13 h14 h15 h10 h1
  have h17 : node_e_u3A_block_u2D_cov_u2D_rateStmt :=
    node_e_u3A_block_u2D_cov_u2D_rate_of_deps h16 h10
  have h18 : node_p_u3A_covariance_u23_test_u2D_blocksStmt :=
    node_p_u3A_covariance_u23_test_u2D_blocks_of_deps h13 h14 h17 h11 h10
  have h19 : node_p_u3A_covariance_u23_closureStmt :=
    node_p_u3A_covariance_u23_closure_of_deps h11 h18 h3 h17
  have h20 : node_p_u3A_covarianceStmt :=
    node_p_u3A_covariance_of_deps h19
  exact h20

end EinsteinFull.Proofs
