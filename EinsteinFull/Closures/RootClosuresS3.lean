import EinsteinFull.Blueprint.Foundation.Proofs.C4LocalTimeReduction
import EinsteinFull.Blueprint.Foundation.Proofs.CLCorrectorCovariance
import EinsteinFull.Blueprint.Foundation.Proofs.CanonicalLaw
import EinsteinFull.Blueprint.Foundation.Proofs.CorrectorConstruction
import EinsteinFull.Blueprint.Foundation.Proofs.D1PathwiseV2
import EinsteinFull.Blueprint.Foundation.Proofs.F2PastKernelReduction
import EinsteinFull.Blueprint.Foundation.Proofs.GaugeHolomorphic
import EinsteinFull.Blueprint.Foundation.Proofs.ReducedBounds
import EinsteinFull.Blueprint.Foundation.Proofs.ReducedDerivatives
import EinsteinFull.Blueprint.Foundation.Proofs.S2ForcedClockV2
import EinsteinFull.Blueprint.Foundation.Proofs.S2UnforcedClockV2
import EinsteinFull.Blueprint.Foundation.Proofs.S2UnforcedProcessV2
import EinsteinFull.Blueprint.Foundation.Proofs.S5OffDiagonal
import EinsteinFull.Blueprint.Foundation.Proofs.StationaryEnvironment
import EinsteinFull.Blueprint.Foundation.Proofs.W1CenteredSource
import EinsteinFull.Blueprint.Foundation.Proofs.W1Queue0204_2
import EinsteinFull.Blueprint.Foundation.Proofs.W1Queue0330_1
import EinsteinFull.Blueprint.Foundation.Proofs.W1Queue0500_2
import EinsteinFull.Blueprint.Foundation.Proofs.W2CenteredEquations
import EinsteinFull.Blueprint.Foundation.Proofs.W3Queue0330_1
import EinsteinFull.Blueprint.Foundation.Proofs.W4Queue0315
import EinsteinFull.Blueprint.Foundation.Proofs.W4Queue0440
import EinsteinFull.Blueprint.Foundation.node_p_u3A_gauge_u23_closed_u2D_form
import EinsteinFull.Blueprint.G1.Proofs.CLS3SwitchKM
import EinsteinFull.Blueprint.G1.Proofs.CLS3SwitchNodes
import EinsteinFull.Blueprint.G1.Proofs.CLSection3Reductions
import EinsteinFull.Blueprint.G1.Proofs.S3Annuli
import EinsteinFull.Blueprint.G1.Proofs.S3KFactor
import EinsteinFull.Blueprint.G1.Proofs.S3PrebridgeK
import EinsteinFull.Blueprint.G1.Proofs.S3TwoMasses
import EinsteinFull.Blueprint.G1.Proofs.SmallIndices
import EinsteinFull.Blueprint.G1.Proofs.W1Queue0240
import EinsteinFull.Blueprint.G1.Proofs.W1Queue0315
import EinsteinFull.Blueprint.G1.Proofs.W1Queue0330_2
import EinsteinFull.Blueprint.G1.Proofs.W1Reduction1
import EinsteinFull.Blueprint.G1.Proofs.W1Reduction2
import EinsteinFull.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.Blueprint.G2.Proofs.C3BootstrapAverage
import EinsteinFull.Blueprint.G2.Proofs.C3HolderAverageReduction
import EinsteinFull.Blueprint.G2.Proofs.C6IndependentBlocksReduction
import EinsteinFull.Blueprint.G2.Proofs.C6UnitInitializationReduction
import EinsteinFull.Blueprint.G2.Proofs.S1FluxIdentity
import EinsteinFull.Blueprint.G2.Proofs.S5HolderInterior
import EinsteinFull.Blueprint.G2.Proofs.W1Queue0158_2
import EinsteinFull.Blueprint.G2.Proofs.W2EnergyTarget
import EinsteinFull.Blueprint.G2.Proofs.W2FluxParameters
import EinsteinFull.Blueprint.G2.Proofs.W4BootstrapPoint
import EinsteinFull.Blueprint.G3.Proofs.C10BlockCovRate
import EinsteinFull.Blueprint.G3.Proofs.C10TestBlocksReduction
import EinsteinFull.Blueprint.G3.Proofs.C14ClockEarlyReduction
import EinsteinFull.Blueprint.G3.Proofs.C15ClockReduction
import EinsteinFull.Blueprint.G3.Proofs.C1TestCLTReduction
import EinsteinFull.Blueprint.G3.Proofs.C2BlockBoundary
import EinsteinFull.Blueprint.G3.Proofs.C2BlockCLT
import EinsteinFull.Blueprint.G3.Proofs.C2BlockChange
import EinsteinFull.Blueprint.G3.Proofs.C2SmoothMoments
import EinsteinFull.Blueprint.G3.Proofs.C2TestReplacement
import EinsteinFull.Blueprint.G3.Proofs.C3SmoothedDuhamel
import EinsteinFull.Blueprint.G3.Proofs.C6CoarseIdentificationClosure
import EinsteinFull.Blueprint.G3.Proofs.C6SublinearPairReduction
import EinsteinFull.Blueprint.G3.Proofs.C9JointLocalizationClosure
import EinsteinFull.Blueprint.G3.Proofs.ClockBlocks
import EinsteinFull.Blueprint.G3.Proofs.GaussianFourier
import EinsteinFull.Blueprint.G3.Proofs.S1BlockRecursion
import EinsteinFull.Blueprint.G3.Proofs.S1Closure
import EinsteinFull.Blueprint.G3.Proofs.S2ForceReplacement
import EinsteinFull.Blueprint.G3.Proofs.S3LocalAv
import EinsteinFull.Blueprint.G3.Proofs.W1Queue0420_2
import EinsteinFull.Blueprint.G3.Proofs.W1SplitTailClosure
import EinsteinFull.Blueprint.G3.Proofs.W2GradientLimitClosure
import EinsteinFull.Blueprint.G3.Proofs.W2Queue0420_1
import EinsteinFull.Blueprint.G3.Proofs.W2Queue0430
import EinsteinFull.Blueprint.G3.Proofs.W2Reduction1
import EinsteinFull.Blueprint.G3.Proofs.W2Reduction2
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0400_1
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0400_2
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0400_3
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0420_2
import EinsteinFull.Blueprint.G3.Proofs.W3Reduction2
import EinsteinFull.Blueprint.G3.Proofs.W3ScalarIntegral
import EinsteinFull.Blueprint.G3.Proofs.W4Queue0400_2
import EinsteinFull.Blueprint.G3.Proofs.W4Queue0420_1
import EinsteinFull.Blueprint.G4.Proofs.C11SharpHarmonic
import EinsteinFull.Blueprint.G4.Proofs.C12SharpClock
import EinsteinFull.Blueprint.G4.Proofs.CLTimeChangeV2
import EinsteinFull.Blueprint.G4.Proofs.ResponseCesaroAbel
import EinsteinFull.Blueprint.G4.Proofs.S1SharpFields
import EinsteinFull.Blueprint.G4.Proofs.S1SharpReplacement
import EinsteinFull.Blueprint.G4.Proofs.S1SharpSeed
import EinsteinFull.Blueprint.G4.Proofs.S2PositiveCoefficient
import EinsteinFull.Blueprint.G4.Proofs.S2SeedErgodicity
import EinsteinFull.Blueprint.G4.Proofs.S4Division
import EinsteinFull.Blueprint.G4.Proofs.W2ClockZero
import EinsteinFull.Blueprint.G4.Proofs.W2Queue0145_1
import EinsteinFull.Blueprint.G4.Proofs.W2Queue0145_2
import EinsteinFull.Blueprint.G4.Proofs.W2Queue0158_2
import EinsteinFull.Blueprint.G4.Proofs.W2Queue0240_1
import EinsteinFull.Blueprint.G4.Proofs.W2Queue0240_2
import EinsteinFull.Blueprint.G4.Proofs.W2Queue0258
import EinsteinFull.Blueprint.G4.Proofs.W2Queue0305_1
import EinsteinFull.Blueprint.G4.Proofs.W2Queue0305_2
import EinsteinFull.Blueprint.G4.Proofs.W3Queue0240_1
import EinsteinFull.Blueprint.G4.Proofs.W3Queue0240_2
import EinsteinFull.Blueprint.G4.Proofs.W3Queue0250_1
import EinsteinFull.Blueprint.G4.Proofs.W4Queue0240_1
import EinsteinFull.Blueprint.G4.Proofs.W4Queue0240_2
import EinsteinFull.Blueprint.Roots.Proofs.CLS3SwitchRoots
import EinsteinFull.Blueprint.Roots.Proofs.CLSharpExampleRoot
import EinsteinFull.Blueprint.Roots.Proofs.CLTExpansionRoot
import EinsteinFull.Blueprint.Roots.Proofs.W1Queue0400_3
import EinsteinFull.Blueprint.Roots.Proofs.W1Queue0410
import EinsteinFull.Blueprint.Roots.Proofs.W2MobilityRoot
import EinsteinFull.Blueprint.Roots.Proofs.W2Queue0400_2
import EinsteinFull.Blueprint.Roots.Proofs.W2Queue0400_3
import EinsteinFull.Blueprint.Roots.Proofs.W2Queue0410
import EinsteinFull.Blueprint.Roots.Proofs.W3Queue0410
import EinsteinFull.Blueprint.Roots.Proofs.W4Queue0330_1
import EinsteinFull.Blueprint.Roots.Proofs.W4Queue0330_2
import EinsteinFull.Blueprint.Roots.Proofs.W4Queue0345_1
import EinsteinFull.Blueprint.Roots.Proofs.W4Queue0400_3
import EinsteinFull.Blueprint.Roots.Proofs.W4Queue0410
import EinsteinFull.Calculus.C10CrudeEnergyAssembly
import EinsteinFull.Calculus.C14FluxBlockAssembly
import EinsteinFull.Calculus.C14S3ConditionIterateFinal
import EinsteinFull.Calculus.C31FluxGainRoot
import EinsteinFull.Calculus.C6DyadicFinalReduction
import EinsteinFull.Calculus.C7EndpointUniformProjection
import EinsteinFull.Calculus.C7S3IndependenceAssembly
import EinsteinFull.Calculus.C9SharpClockContinuityReduction
import EinsteinFull.Calculus.CLElementaryRate
import EinsteinFull.Calculus.CLForcedLLNV2
import EinsteinFull.Calculus.CLSmallTimeCrude
import EinsteinFull.Calculus.F2PointKernelExactAssembler
import EinsteinFull.Calculus.SbxAOriginalRemainderAssemblerR07
import EinsteinFull.Calculus.SbxTakeoverFutureKernelReductionR01

/-! Closed proofs of the numbered root mirrors `t.main`, `t:expansion`, `p:tail`, `sharp.example`, `rt:local-mixing`, `rt:renewal`, `app:factorization`, `rt:factorization`,
composed from the exact graph reductions in dependency order. Each `cls3_cl_*`
applies one node's `_of_deps` reduction to the closed proofs of its ordered
graph hypotheses. -/

namespace EinsteinFull.Blueprint

/-- Closed proof of `eq.reduced-generator#pathwise`. -/
theorem cls3_cl_node_eq_u2E_reduced_u2D_generator_u23_pathwise : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2 :=
  node_eq_u2E_reduced_u2D_generator_u23_pathwise_of_deps

/-- Closed proof of `eq.reduced-bounds`. -/
theorem cls3_cl_node_eq_u2E_reduced_u2D_bounds : node_eq_u2E_reduced_u2D_boundsStmt :=
  node_eq_u2E_reduced_u2D_bounds_of_deps

/-- Closed proof of `stationary-environment#canonical-law`. -/
theorem cls3_cl_node_stationary_u2D_environment_u23_canonical_u2D_law : node_stationary_u2D_environment_u23_canonical_u2D_lawStmt :=
  node_stationary_u2D_environment_u23_canonical_u2D_law_of_deps cls3_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `stationary-environment`. -/
theorem cls3_cl_node_stationary_u2D_environment : node_stationary_u2D_environmentStmt :=
  node_stationary_u2D_environment_of_deps cls3_cl_node_stationary_u2D_environment_u23_canonical_u2D_law

/-- Closed proof of `stationary-environment#unforced-process`. -/
theorem cls3_cl_node_stationary_u2D_environment_u23_unforced_u2D_process : node_stationary_u2D_environment_u23_unforced_u2D_processStmtV2 :=
  node_stationary_u2D_environment_u23_unforced_u2D_process_of_deps cls3_cl_node_eq_u2E_reduced_u2D_generator_u23_pathwise cls3_cl_node_stationary_u2D_environment cls3_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `e:generators#real-semigroup`. -/
theorem cls3_cl_node_e_u3A_generators_u23_real_u2D_semigroup : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2 :=
  node_e_u3A_generators_u23_real_u2D_semigroup_of_deps cls3_cl_node_stationary_u2D_environment_u23_unforced_u2D_process cls3_cl_node_eq_u2E_reduced_u2D_generator_u23_pathwise

/-- Closed proof of `eq.reduced-bounds#derivatives`. -/
theorem cls3_cl_node_eq_u2E_reduced_u2D_bounds_u23_derivatives : node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt :=
  node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps cls3_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `p:gauge#closed-form`. -/
theorem cls3_cl_node_p_u3A_gauge_u23_closed_u2D_form : node_p_u3A_gauge_u23_closed_u2D_formStmt :=
  node_p_u3A_gauge_u23_closed_u2D_form_of_deps

/-- Closed proof of `p:gauge#holomorphic`. -/
theorem cls3_cl_node_p_u3A_gauge_u23_holomorphic : node_p_u3A_gauge_u23_holomorphicStmt :=
  node_p_u3A_gauge_u23_holomorphic_of_deps cls3_cl_node_p_u3A_gauge_u23_closed_u2D_form

/-- Closed proof of `stationary-analytic-semigroup`. -/
theorem cls3_cl_node_stationary_u2D_analytic_u2D_semigroup : node_stationary_u2D_analytic_u2D_semigroupStmt :=
  node_stationary_u2D_analytic_u2D_semigroup_of_deps cls3_cl_node_e_u3A_generators_u23_real_u2D_semigroup cls3_cl_node_eq_u2E_reduced_u2D_bounds_u23_derivatives cls3_cl_node_p_u3A_gauge_u23_holomorphic

/-- Closed proof of `l:forced-local#cutoff-environment`. -/
theorem cls3_cl_node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environment : node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environmentStmt :=
  node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environment_of_deps cls3_cl_node_eq_u2E_reduced_u2D_bounds cls3_cl_node_eq_u2E_reduced_u2D_bounds_u23_derivatives

/-- Closed proof of `l:forced-local#off-diagonal`. -/
theorem cls3_cl_node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal : node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt :=
  node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal_of_deps cls3_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `e:lp-growth`. -/
theorem cls3_cl_node_e_u3A_lp_u2D_growth : node_e_u3A_lp_u2D_growthStmt :=
  node_e_u3A_lp_u2D_growth_of_deps cls3_cl_node_stationary_u2D_environment cls3_cl_node_stationary_u2D_analytic_u2D_semigroup

/-- Closed proof of `l:forced-local#centered-source`. -/
theorem cls3_cl_node_l_u3A_forced_u2D_local_u23_centered_u2D_source : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt :=
  node_l_u3A_forced_u2D_local_u23_centered_u2D_source_of_deps cls3_cl_node_e_u3A_lp_u2D_growth

/-- Closed proof of `e:local-time`. -/
theorem cls3_cl_node_e_u3A_local_u2D_time : node_e_u3A_local_u2D_timeStmt :=
  node_e_u3A_local_u2D_time_of_deps cls3_cl_node_l_u3A_forced_u2D_local_u23_centered_u2D_source cls3_cl_node_e_u3A_lp_u2D_growth

/-- Closed proof of `l:forced-local#point-kernel`. -/
theorem cls3_cl_node_l_u3A_forced_u2D_local_u23_point_u2D_kernel : node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt :=
  node_l_u3A_forced_u2D_local_u23_point_u2D_kernel_of_deps cls3_cl_node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal cls3_cl_node_e_u3A_local_u2D_time cls3_cl_node_eq_u2E_reduced_u2D_bounds_u23_derivatives

/-- Closed proof of `e:forced-locality`. -/
theorem cls3_cl_node_e_u3A_forced_u2D_locality : node_e_u3A_forced_u2D_localityStmt :=
  node_e_u3A_forced_u2D_locality_of_deps cls3_cl_node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environment cls3_cl_node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal cls3_cl_node_l_u3A_forced_u2D_local_u23_point_u2D_kernel cls3_cl_node_e_u3A_local_u2D_time

/-- Closed proof of `stationary-analytic-semigroup#endpoints`. -/
theorem cls3_cl_node_stationary_u2D_analytic_u2D_semigroup_u23_endpoints : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt :=
  node_stationary_u2D_analytic_u2D_semigroup_u23_endpoints_of_deps cls3_cl_node_stationary_u2D_analytic_u2D_semigroup cls3_cl_node_e_u3A_forced_u2D_locality

/-- Closed proof of `finite-time-analyticity`. -/
theorem cls3_cl_node_finite_u2D_time_u2D_analyticity : node_finite_u2D_time_u2D_analyticityStmt :=
  node_finite_u2D_time_u2D_analyticity_of_deps cls3_cl_node_stationary_u2D_analytic_u2D_semigroup_u23_endpoints

/-- Closed proof of `p:integration#kernel-measurability-reality`. -/
theorem cls3_cl_node_p_u3A_integration_u23_kernel_u2D_measurability_u2D_reality : node_p_u3A_integration_u23_kernel_u2D_measurability_u2D_realityStmt :=
  node_p_u3A_integration_u23_kernel_u2D_measurability_u2D_reality_of_deps cls3_cl_node_stationary_u2D_analytic_u2D_semigroup

/-- Closed proof of `e:parameters`. -/
theorem cls3_cl_node_e_u3A_parameters : node_e_u3A_parametersStmt :=
  node_e_u3A_parameters_of_deps cls3_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `e:clock-l2`. -/
theorem cls3_cl_node_e_u3A_clock_u2D_l2 : node_e_u3A_clock_u2D_l2Stmt :=
  node_e_u3A_clock_u2D_l2_of_deps

/-- Closed proof of `e:test-clt`. -/
theorem cls3_cl_node_e_u3A_test_u2D_clt : node_e_u3A_test_u2D_cltStmt :=
  node_e_u3A_test_u2D_clt_of_deps cls3_cl_node_e_u3A_clock_u2D_l2

/-- Closed proof of `corrector-construction`. -/
theorem cls3_cl_node_corrector_u2D_construction : node_corrector_u2D_constructionStmt :=
  node_corrector_u2D_construction_of_deps cls3_cl_node_stationary_u2D_environment cls3_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `corrector-construction#smooth-moments`. -/
theorem cls3_cl_node_corrector_u2D_construction_u23_smooth_u2D_moments : node_corrector_u2D_construction_u23_smooth_u2D_momentsStmt :=
  node_corrector_u2D_construction_u23_smooth_u2D_moments_of_deps cls3_cl_node_corrector_u2D_construction cls3_cl_node_eq_u2E_reduced_u2D_bounds_u23_derivatives

/-- Closed proof of `p:covariance#coarse-identification`. -/
theorem cls3_cl_node_p_u3A_covariance_u23_coarse_u2D_identification : node_p_u3A_covariance_u23_coarse_u2D_identificationStmt :=
  node_p_u3A_covariance_u23_coarse_u2D_identification_of_deps cls3_cl_node_corrector_u2D_construction_u23_smooth_u2D_moments

/-- Closed proof of `p:covariance#joint-localization`. -/
theorem cls3_cl_node_p_u3A_covariance_u23_joint_u2D_localization : node_p_u3A_covariance_u23_joint_u2D_localizationStmt :=
  node_p_u3A_covariance_u23_joint_u2D_localization_of_deps cls3_cl_node_e_u3A_parameters cls3_cl_node_e_u3A_clock_u2D_l2

/-- Closed proof of `p:covariance#test-replacement`. -/
theorem cls3_cl_node_p_u3A_covariance_u23_test_u2D_replacement : node_p_u3A_covariance_u23_test_u2D_replacementStmt :=
  node_p_u3A_covariance_u23_test_u2D_replacement_of_deps cls3_cl_node_e_u3A_parameters cls3_cl_node_e_u3A_test_u2D_clt cls3_cl_node_p_u3A_covariance_u23_coarse_u2D_identification cls3_cl_node_p_u3A_covariance_u23_joint_u2D_localization

/-- Closed proof of `p:covariance#clock-blocks`. -/
theorem cls3_cl_node_p_u3A_covariance_u23_clock_u2D_blocks : node_p_u3A_covariance_u23_clock_u2D_blocksStmt :=
  node_p_u3A_covariance_u23_clock_u2D_blocks_of_deps cls3_cl_node_e_u3A_clock_u2D_l2 cls3_cl_node_p_u3A_covariance_u23_joint_u2D_localization cls3_cl_node_e_u3A_parameters

/-- Closed proof of `e:block-clt`. -/
theorem cls3_cl_node_e_u3A_block_u2D_clt : node_e_u3A_block_u2D_cltStmt :=
  node_e_u3A_block_u2D_clt_of_deps cls3_cl_node_p_u3A_covariance_u23_joint_u2D_localization cls3_cl_node_p_u3A_covariance_u23_clock_u2D_blocks

/-- Closed proof of `e:block-boundary`. -/
theorem cls3_cl_node_e_u3A_block_u2D_boundary : node_e_u3A_block_u2D_boundaryStmt :=
  node_e_u3A_block_u2D_boundary_of_deps cls3_cl_node_p_u3A_covariance_u23_joint_u2D_localization cls3_cl_node_p_u3A_covariance_u23_clock_u2D_blocks

/-- Closed proof of `e:block-change`. -/
theorem cls3_cl_node_e_u3A_block_u2D_change : node_e_u3A_block_u2D_changeStmt :=
  node_e_u3A_block_u2D_change_of_deps cls3_cl_node_p_u3A_covariance_u23_joint_u2D_localization cls3_cl_node_p_u3A_covariance_u23_clock_u2D_blocks

/-- Closed proof of `e:block-recursion`. -/
theorem cls3_cl_node_e_u3A_block_u2D_recursion : node_e_u3A_block_u2D_recursionStmt :=
  node_e_u3A_block_u2D_recursion_of_deps cls3_cl_node_e_u3A_block_u2D_clt cls3_cl_node_e_u3A_block_u2D_boundary cls3_cl_node_e_u3A_block_u2D_change cls3_cl_node_p_u3A_covariance_u23_joint_u2D_localization cls3_cl_node_e_u3A_parameters

/-- Closed proof of `e:block-cov-rate`. -/
theorem cls3_cl_node_e_u3A_block_u2D_cov_u2D_rate : node_e_u3A_block_u2D_cov_u2D_rateStmt :=
  node_e_u3A_block_u2D_cov_u2D_rate_of_deps cls3_cl_node_e_u3A_block_u2D_recursion cls3_cl_node_p_u3A_covariance_u23_joint_u2D_localization

/-- Closed proof of `p:covariance#test-blocks`. -/
theorem cls3_cl_node_p_u3A_covariance_u23_test_u2D_blocks : node_p_u3A_covariance_u23_test_u2D_blocksStmt :=
  node_p_u3A_covariance_u23_test_u2D_blocks_of_deps cls3_cl_node_e_u3A_block_u2D_clt cls3_cl_node_e_u3A_block_u2D_boundary cls3_cl_node_e_u3A_block_u2D_cov_u2D_rate cls3_cl_node_p_u3A_covariance_u23_test_u2D_replacement cls3_cl_node_p_u3A_covariance_u23_joint_u2D_localization

/-- Closed proof of `p:covariance#closure`. -/
theorem cls3_cl_node_p_u3A_covariance_u23_closure : node_p_u3A_covariance_u23_closureStmt :=
  node_p_u3A_covariance_u23_closure_of_deps cls3_cl_node_p_u3A_covariance_u23_test_u2D_replacement cls3_cl_node_p_u3A_covariance_u23_test_u2D_blocks cls3_cl_node_e_u3A_test_u2D_clt cls3_cl_node_e_u3A_block_u2D_cov_u2D_rate

/-- Closed proof of `p:covariance`. -/
theorem cls3_cl_node_p_u3A_covariance : node_p_u3A_covarianceStmt :=
  node_p_u3A_covariance_of_deps cls3_cl_node_p_u3A_covariance_u23_closure

/-- Closed proof of `e:time-flux`. -/
theorem cls3_cl_node_e_u3A_time_u2D_flux : node_e_u3A_time_u2D_fluxStmt :=
  node_e_u3A_time_u2D_flux_of_deps cls3_cl_node_stationary_u2D_analytic_u2D_semigroup

/-- Closed proof of `e:centered-equations`. -/
theorem cls3_cl_node_e_u3A_centered_u2D_equations : node_e_u3A_centered_u2D_equationsStmt :=
  node_e_u3A_centered_u2D_equations_of_deps

/-- Closed proof of `e:sublinear-pair`. -/
theorem cls3_cl_node_e_u3A_sublinear_u2D_pair : node_e_u3A_sublinear_u2D_pairStmt :=
  node_e_u3A_sublinear_u2D_pair_of_deps

/-- Closed proof of `e:flux-identity`. -/
theorem cls3_cl_node_e_u3A_flux_u2D_identity : node_e_u3A_flux_u2D_identityStmt :=
  node_e_u3A_flux_u2D_identity_of_deps cls3_cl_node_e_u3A_sublinear_u2D_pair

/-- Closed proof of `l:forced-flux#parameters`. -/
theorem cls3_cl_node_l_u3A_forced_u2D_flux_u23_parameters : node_l_u3A_forced_u2D_flux_u23_parametersStmt :=
  node_l_u3A_forced_u2D_flux_u23_parameters_of_deps cls3_cl_node_e_u3A_sublinear_u2D_pair

/-- Closed proof of `l:forced-local#crude-energy`. -/
theorem cls3_cl_node_l_u3A_forced_u2D_local_u23_crude_u2D_energy : node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt :=
  node_l_u3A_forced_u2D_local_u23_crude_u2D_energy_of_deps cls3_cl_node_l_u3A_forced_u2D_local_u23_point_u2D_kernel

/-- Closed proof of `e:flux-block`. -/
theorem cls3_cl_node_e_u3A_flux_u2D_block : node_e_u3A_flux_u2D_blockStmt :=
  node_e_u3A_flux_u2D_block_of_deps cls3_cl_node_e_u3A_flux_u2D_identity cls3_cl_node_e_u3A_local_u2D_time cls3_cl_node_l_u3A_forced_u2D_flux_u23_parameters cls3_cl_node_e_u3A_sublinear_u2D_pair cls3_cl_node_l_u3A_forced_u2D_local_u23_crude_u2D_energy

/-- Closed proof of `l:forced-flux#independent-blocks`. -/
theorem cls3_cl_node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocks : node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocksStmtV2 :=
  node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocks_of_deps cls3_cl_node_e_u3A_flux_u2D_block cls3_cl_node_e_u3A_forced_u2D_locality cls3_cl_node_l_u3A_forced_u2D_flux_u23_parameters

/-- Closed proof of `l:forced-flux#gain`. -/
theorem cls3_cl_node_l_u3A_forced_u2D_flux_u23_gain : node_l_u3A_forced_u2D_flux_u23_gainStmt :=
  node_l_u3A_forced_u2D_flux_u23_gain_of_deps cls3_cl_node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocks cls3_cl_node_l_u3A_forced_u2D_flux_u23_parameters cls3_cl_node_e_u3A_flux_u2D_block

/-- Closed proof of `l:forced-flux`. -/
theorem cls3_cl_node_l_u3A_forced_u2D_flux : node_l_u3A_forced_u2D_fluxStmt :=
  node_l_u3A_forced_u2D_flux_of_deps cls3_cl_node_l_u3A_forced_u2D_flux_u23_gain

/-- Closed proof of `p:scalar#unit-initialization`. -/
theorem cls3_cl_node_p_u3A_scalar_u23_unit_u2D_initialization : node_p_u3A_scalar_u23_unit_u2D_initializationStmt :=
  node_p_u3A_scalar_u23_unit_u2D_initialization_of_deps cls3_cl_node_e_u3A_forced_u2D_locality cls3_cl_node_stationary_u2D_analytic_u2D_semigroup_u23_endpoints

/-- Closed proof of `p:scalar#bootstrap-average`. -/
theorem cls3_cl_node_p_u3A_scalar_u23_bootstrap_u2D_average : node_p_u3A_scalar_u23_bootstrap_u2D_averageStmt :=
  node_p_u3A_scalar_u23_bootstrap_u2D_average_of_deps cls3_cl_node_e_u3A_centered_u2D_equations cls3_cl_node_l_u3A_forced_u2D_flux cls3_cl_node_p_u3A_scalar_u23_unit_u2D_initialization

/-- Closed proof of `e:holder-average#unforced-interior`. -/
theorem cls3_cl_node_e_u3A_holder_u2D_average_u23_unforced_u2D_interior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt :=
  node_e_u3A_holder_u2D_average_u23_unforced_u2D_interior_of_deps cls3_cl_node_e_u3A_local_u2D_time

/-- Closed proof of `e:holder-average`. -/
theorem cls3_cl_node_e_u3A_holder_u2D_average : node_e_u3A_holder_u2D_averageStmt :=
  node_e_u3A_holder_u2D_average_of_deps cls3_cl_node_e_u3A_local_u2D_time cls3_cl_node_e_u3A_lp_u2D_growth cls3_cl_node_l_u3A_forced_u2D_local_u23_centered_u2D_source cls3_cl_node_e_u3A_holder_u2D_average_u23_unforced_u2D_interior

/-- Closed proof of `p:scalar#smoothing-selection`. -/
theorem cls3_cl_node_p_u3A_scalar_u23_smoothing_u2D_selection : node_p_u3A_scalar_u23_smoothing_u2D_selectionStmt :=
  node_p_u3A_scalar_u23_smoothing_u2D_selection_of_deps cls3_cl_node_e_u3A_holder_u2D_average cls3_cl_node_p_u3A_scalar_u23_bootstrap_u2D_average

/-- Closed proof of `p:scalar#bootstrap-point`. -/
theorem cls3_cl_node_p_u3A_scalar_u23_bootstrap_u2D_point : node_p_u3A_scalar_u23_bootstrap_u2D_pointStmt :=
  node_p_u3A_scalar_u23_bootstrap_u2D_point_of_deps cls3_cl_node_p_u3A_scalar_u23_bootstrap_u2D_average cls3_cl_node_e_u3A_holder_u2D_average cls3_cl_node_p_u3A_scalar_u23_unit_u2D_initialization cls3_cl_node_p_u3A_scalar_u23_smoothing_u2D_selection

/-- Closed proof of `p:scalar`. -/
theorem cls3_cl_node_p_u3A_scalar : node_p_u3A_scalarStmt :=
  node_p_u3A_scalar_of_deps cls3_cl_node_p_u3A_scalar_u23_bootstrap_u2D_point

/-- Closed proof of `e:energy-target`. -/
theorem cls3_cl_node_e_u3A_energy_u2D_target : node_e_u3A_energy_u2D_targetStmt :=
  node_e_u3A_energy_u2D_target_of_deps cls3_cl_node_p_u3A_scalar cls3_cl_node_e_u3A_centered_u2D_equations cls3_cl_node_stationary_u2D_environment

/-- Closed proof of `l:forced-local`. -/
theorem cls3_cl_node_l_u3A_forced_u2D_local : node_l_u3A_forced_u2D_localStmt :=
  node_l_u3A_forced_u2D_local_of_deps cls3_cl_node_e_u3A_local_u2D_time cls3_cl_node_e_u3A_holder_u2D_average cls3_cl_node_e_u3A_forced_u2D_locality cls3_cl_node_l_u3A_forced_u2D_local_u23_point_u2D_kernel

/-- Closed proof of `p:late#dyadic-increments`. -/
theorem cls3_cl_node_p_u3A_late_u23_dyadic_u2D_increments : node_p_u3A_late_u23_dyadic_u2D_incrementsStmt :=
  node_p_u3A_late_u23_dyadic_u2D_increments_of_deps cls3_cl_node_e_u3A_energy_u2D_target cls3_cl_node_l_u3A_forced_u2D_local cls3_cl_node_e_u3A_time_u2D_flux

/-- Closed proof of `e:local-av`. -/
theorem cls3_cl_node_e_u3A_local_u2D_av : node_e_u3A_local_u2D_avStmt :=
  node_e_u3A_local_u2D_av_of_deps cls3_cl_node_e_u3A_time_u2D_flux

/-- Closed proof of `stationary-analytic-semigroup#flux`. -/
theorem cls3_cl_node_stationary_u2D_analytic_u2D_semigroup_u23_flux : node_stationary_u2D_analytic_u2D_semigroup_u23_fluxStmt :=
  node_stationary_u2D_analytic_u2D_semigroup_u23_flux_of_deps cls3_cl_node_stationary_u2D_analytic_u2D_semigroup cls3_cl_node_e_u3A_time_u2D_flux

/-- Closed proof of `p:late#cauchy`. -/
theorem cls3_cl_node_p_u3A_late_u23_cauchy : node_p_u3A_late_u23_cauchyStmt :=
  node_p_u3A_late_u23_cauchy_of_deps cls3_cl_node_p_u3A_late_u23_dyadic_u2D_increments cls3_cl_node_e_u3A_local_u2D_av cls3_cl_node_stationary_u2D_analytic_u2D_semigroup_u23_flux

/-- Closed proof of `p:late`. -/
theorem cls3_cl_node_p_u3A_late : node_p_u3A_lateStmt :=
  node_p_u3A_late_of_deps cls3_cl_node_p_u3A_late_u23_cauchy

/-- Closed proof of `l:late-propagation#smoothed-duhamel`. -/
theorem cls3_cl_node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamel : node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamelStmt :=
  node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamel_of_deps cls3_cl_node_p_u3A_scalar cls3_cl_node_l_u3A_forced_u2D_flux cls3_cl_node_e_u3A_centered_u2D_equations

/-- Closed proof of `l:late-propagation#unsmoothing`. -/
theorem cls3_cl_node_l_u3A_late_u2D_propagation_u23_unsmoothing : node_l_u3A_late_u2D_propagation_u23_unsmoothingStmt :=
  node_l_u3A_late_u2D_propagation_u23_unsmoothing_of_deps cls3_cl_node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamel cls3_cl_node_e_u3A_holder_u2D_average cls3_cl_node_p_u3A_scalar

/-- Closed proof of `l:late-propagation`. -/
theorem cls3_cl_node_l_u3A_late_u2D_propagation : node_l_u3A_late_u2D_propagationStmt :=
  node_l_u3A_late_u2D_propagation_of_deps cls3_cl_node_l_u3A_late_u2D_propagation_u23_unsmoothing

/-- Closed proof of `p:endpoint-comparison#force-replacement`. -/
theorem cls3_cl_node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacement : node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacementStmt :=
  node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacement_of_deps cls3_cl_node_e_u3A_time_u2D_flux cls3_cl_node_p_u3A_late cls3_cl_node_l_u3A_late_u2D_propagation

/-- Closed proof of `l:finite-xi#gradient-limit`. -/
theorem cls3_cl_node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limit : node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limitStmt :=
  node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limit_of_deps cls3_cl_node_p_u3A_scalar cls3_cl_node_l_u3A_forced_u2D_local

/-- Closed proof of `l:finite-xi#potential-identification`. -/
theorem cls3_cl_node_l_u3A_finite_u2D_xi_u23_potential_u2D_identification : node_l_u3A_finite_u2D_xi_u23_potential_u2D_identificationStmt :=
  node_l_u3A_finite_u2D_xi_u23_potential_u2D_identification_of_deps cls3_cl_node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limit cls3_cl_node_corrector_u2D_construction cls3_cl_node_e_u3A_generators_u23_real_u2D_semigroup

/-- Closed proof of `l:finite-xi#commutator-tail`. -/
theorem cls3_cl_node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tail : node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tailStmt :=
  node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tail_of_deps cls3_cl_node_l_u3A_finite_u2D_xi_u23_potential_u2D_identification

/-- Closed proof of `l:finite-xi#split-tail`. -/
theorem cls3_cl_node_l_u3A_finite_u2D_xi_u23_split_u2D_tail : node_l_u3A_finite_u2D_xi_u23_split_u2D_tailStmt :=
  node_l_u3A_finite_u2D_xi_u23_split_u2D_tail_of_deps cls3_cl_node_l_u3A_forced_u2D_flux cls3_cl_node_p_u3A_scalar cls3_cl_node_l_u3A_forced_u2D_local cls3_cl_node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tail

/-- Closed proof of `l:finite-xi#scalar-integral`. -/
theorem cls3_cl_node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integral : node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integralStmt :=
  node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integral_of_deps cls3_cl_node_p_u3A_scalar cls3_cl_node_p_u3A_scalar_u23_unit_u2D_initialization

/-- Closed proof of `l:finite-xi`. -/
theorem cls3_cl_node_l_u3A_finite_u2D_xi : node_l_u3A_finite_u2D_xiStmt :=
  node_l_u3A_finite_u2D_xi_of_deps cls3_cl_node_l_u3A_finite_u2D_xi_u23_split_u2D_tail cls3_cl_node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integral

/-- Closed proof of `p:endpoint-comparison#unforced-identification`. -/
theorem cls3_cl_node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identification : node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identificationStmt :=
  node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identification_of_deps cls3_cl_node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacement cls3_cl_node_l_u3A_finite_u2D_xi cls3_cl_node_l_u3A_late_u2D_propagation cls3_cl_node_e_u3A_test_u2D_clt

/-- Closed proof of `stationary-analytic-semigroup#clock`. -/
theorem cls3_cl_node_stationary_u2D_analytic_u2D_semigroup_u23_clock : node_stationary_u2D_analytic_u2D_semigroup_u23_clockStmt :=
  node_stationary_u2D_analytic_u2D_semigroup_u23_clock_of_deps cls3_cl_node_stationary_u2D_analytic_u2D_semigroup cls3_cl_node_l_u3A_forced_u2D_flux cls3_cl_node_p_u3A_scalar

/-- Closed proof of `e:clock-average`. -/
theorem cls3_cl_node_e_u3A_clock_u2D_average : node_e_u3A_clock_u2D_averageStmt :=
  node_e_u3A_clock_u2D_average_of_deps cls3_cl_node_p_u3A_scalar cls3_cl_node_l_u3A_forced_u2D_flux cls3_cl_node_stationary_u2D_analytic_u2D_semigroup_u23_clock

/-- Closed proof of `e:clock-early`. -/
theorem cls3_cl_node_e_u3A_clock_u2D_early : node_e_u3A_clock_u2D_earlyStmt :=
  node_e_u3A_clock_u2D_early_of_deps cls3_cl_node_e_u3A_clock_u2D_average cls3_cl_node_e_u3A_clock_u2D_l2 cls3_cl_node_e_u3A_centered_u2D_equations cls3_cl_node_l_u3A_late_u2D_propagation

/-- Closed proof of `p:endpoint-comparison#pairing`. -/
theorem cls3_cl_node_p_u3A_endpoint_u2D_comparison_u23_pairing : node_p_u3A_endpoint_u2D_comparison_u23_pairingStmt :=
  node_p_u3A_endpoint_u2D_comparison_u23_pairing_of_deps cls3_cl_node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identification cls3_cl_node_e_u3A_clock_u2D_early cls3_cl_node_e_u3A_clock_u2D_average cls3_cl_node_p_u3A_scalar cls3_cl_node_e_u3A_test_u2D_clt

/-- Closed proof of `p:endpoint-comparison`. -/
theorem cls3_cl_node_p_u3A_endpoint_u2D_comparison : node_p_u3A_endpoint_u2D_comparisonStmt :=
  node_p_u3A_endpoint_u2D_comparison_of_deps cls3_cl_node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identification cls3_cl_node_e_u3A_clock_u2D_early cls3_cl_node_e_u3A_clock_u2D_average cls3_cl_node_p_u3A_endpoint_u2D_comparison_u23_pairing

/-- Closed proof of `h:forced`. -/
theorem cls3_cl_node_h_u3A_forced : node_h_u3A_forcedStmt :=
  node_h_u3A_forced_of_deps cls3_cl_node_p_u3A_endpoint_u2D_comparison cls3_cl_node_p_u3A_scalar

/-- Closed proof of `p:profile#static-comparison`. -/
theorem cls3_cl_node_p_u3A_profile_u23_static_u2D_comparison : node_p_u3A_profile_u23_static_u2D_comparisonStmt :=
  node_p_u3A_profile_u23_static_u2D_comparison_of_deps cls3_cl_node_p_u3A_covariance cls3_cl_node_h_u3A_forced

/-- Closed proof of `e:fourier`. -/
theorem cls3_cl_node_e_u3A_fourier : node_e_u3A_fourierStmt :=
  node_e_u3A_fourier_of_deps cls3_cl_node_p_u3A_covariance

/-- Closed proof of `p:profile`. -/
theorem cls3_cl_node_p_u3A_profile : node_p_u3A_profileStmt :=
  node_p_u3A_profile_of_deps cls3_cl_node_p_u3A_profile_u23_static_u2D_comparison cls3_cl_node_e_u3A_fourier

/-- Closed proof of `p:tail#small-endpoints`. -/
theorem cls3_cl_node_p_u3A_tail_u23_small_u2D_endpoints : node_p_u3A_tail_u23_small_u2D_endpointsStmt :=
  node_p_u3A_tail_u23_small_u2D_endpoints_of_deps cls3_cl_node_p_u3A_scalar

/-- Closed proof of `p:tail#annuli`. -/
theorem cls3_cl_node_p_u3A_tail_u23_annuli : node_p_u3A_tail_u23_annuliStmt :=
  node_p_u3A_tail_u23_annuli_of_deps cls3_cl_node_p_u3A_tail_u23_small_u2D_endpoints cls3_cl_node_l_u3A_forced_u2D_local

/-- Closed proof of `app:factorization#slices`. -/
theorem cls3_cl_node_app_u3A_factorization_u23_slices : node_app_u3A_factorization_u23_slicesStmt :=
  node_app_u3A_factorization_u23_slices_of_deps

/-- Closed proof of `rt:prebridge-k`. -/
theorem cls3_cl_node_rt_u3A_prebridge_u2D_k : node_rt_u3A_prebridge_u2D_kStmt :=
  node_rt_u3A_prebridge_u2D_k_of_deps cls3_cl_node_app_u3A_factorization_u23_slices

/-- Closed proof of `rt:global-geometry`. -/
theorem cls3_cl_node_rt_u3A_global_u2D_geometry : node_rt_u3A_global_u2D_geometryStmt :=
  node_rt_u3A_global_u2D_geometry_of_deps cls3_cl_node_rt_u3A_prebridge_u2D_k cls3_cl_node_app_u3A_factorization_u23_slices

/-- Closed proof of `app:factorization#past-kernel`. -/
theorem cls3_cl_node_app_u3A_factorization_u23_past_u2D_kernel : node_app_u3A_factorization_u23_past_u2D_kernelStmt :=
  node_app_u3A_factorization_u23_past_u2D_kernel_of_deps

/-- Closed proof of `app:factorization#endpoint-disintegration`. -/
theorem cls3_cl_node_app_u3A_factorization_u23_endpoint_u2D_disintegration : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt :=
  node_app_u3A_factorization_u23_endpoint_u2D_disintegration_of_deps cls3_cl_node_app_u3A_factorization_u23_slices

/-- Closed proof of `app:factorization#future-kernel`. -/
theorem cls3_cl_node_app_u3A_factorization_u23_future_u2D_kernel : node_app_u3A_factorization_u23_future_u2D_kernelStmt :=
  node_app_u3A_factorization_u23_future_u2D_kernel_of_deps

/-- Closed proof of `rt:renewal#tube-geometry`. -/
theorem cls3_cl_node_rt_u3A_renewal_u23_tube_u2D_geometry : node_rt_u3A_renewal_u23_tube_u2D_geometryStmt :=
  node_rt_u3A_renewal_u23_tube_u2D_geometry_of_deps

/-- Closed proof of `rt:renewal#tube-probability`. -/
theorem cls3_cl_node_rt_u3A_renewal_u23_tube_u2D_probability : node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt :=
  node_rt_u3A_renewal_u23_tube_u2D_probability_of_deps cls3_cl_node_rt_u3A_renewal_u23_tube_u2D_geometry cls3_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `rt:renewal#coupling-parameter-transfer`. -/
theorem cls3_cl_node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transfer : node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transferStmt :=
  node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transfer_of_deps cls3_cl_node_rt_u3A_renewal_u23_tube_u2D_probability

/-- Closed proof of `app:regen-tails`. -/
theorem cls3_cl_node_app_u3A_regen_u2D_tails : node_app_u3A_regen_u2D_tailsStmt :=
  node_app_u3A_regen_u2D_tails_of_deps cls3_cl_node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transfer

/-- Closed proof of `app:factorization#coupling-scope`. -/
theorem cls3_cl_node_app_u3A_factorization_u23_coupling_u2D_scope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt :=
  node_app_u3A_factorization_u23_coupling_u2D_scope_of_deps cls3_cl_node_app_u3A_regen_u2D_tails

/-- Closed proof of `app:factorization#independence`. -/
theorem cls3_cl_node_app_u3A_factorization_u23_independence : node_app_u3A_factorization_u23_independenceStmtV2 :=
  node_app_u3A_factorization_u23_independence_of_deps cls3_cl_node_app_u3A_factorization_u23_endpoint_u2D_disintegration cls3_cl_node_app_u3A_factorization_u23_past_u2D_kernel cls3_cl_node_app_u3A_factorization_u23_future_u2D_kernel cls3_cl_node_app_u3A_regen_u2D_tails cls3_cl_node_app_u3A_factorization_u23_slices cls3_cl_node_app_u3A_factorization_u23_coupling_u2D_scope

/-- Closed proof of `rt:k-factor`. -/
theorem cls3_cl_node_rt_u3A_k_u2D_factor : node_rt_u3A_k_u2D_factorStmt :=
  node_rt_u3A_k_u2D_factor_of_deps cls3_cl_node_rt_u3A_global_u2D_geometry cls3_cl_node_app_u3A_factorization_u23_past_u2D_kernel cls3_cl_node_app_u3A_factorization_u23_independence cls3_cl_node_rt_u3A_prebridge_u2D_k

/-- Closed proof of `app:factorization#condition-iterate`. -/
theorem cls3_cl_node_app_u3A_factorization_u23_condition_u2D_iterate : node_app_u3A_factorization_u23_condition_u2D_iterateStmt :=
  node_app_u3A_factorization_u23_condition_u2D_iterate_of_deps cls3_cl_node_app_u3A_factorization_u23_independence cls3_cl_node_app_u3A_factorization_u23_slices cls3_cl_node_app_u3A_regen_u2D_tails

/-- Closed proof of `app:factorization`. -/
theorem cls3_cl_node_app_u3A_factorization : node_app_u3A_factorizationStmtV2 :=
  node_app_u3A_factorization_of_depsV2 cls3_cl_node_app_u3A_factorization_u23_independence cls3_cl_node_app_u3A_factorization_u23_condition_u2D_iterate cls3_cl_node_app_u3A_factorization_u23_coupling_u2D_scope

/-- Closed proof of `rt:factorization#small-indices`. -/
theorem cls3_cl_node_rt_u3A_factorization_u23_small_u2D_indices : node_rt_u3A_factorization_u23_small_u2D_indicesStmt :=
  node_rt_u3A_factorization_u23_small_u2D_indices_of_deps

/-- Closed proof of `rt:factorization`. -/
theorem cls3_cl_node_rt_u3A_factorization : node_rt_u3A_factorizationStmtV2 :=
  node_rt_u3A_factorization_of_depsV2 cls3_cl_node_app_u3A_factorization cls3_cl_node_app_u3A_factorization_u23_past_u2D_kernel cls3_cl_node_app_u3A_factorization_u23_slices cls3_cl_node_rt_u3A_factorization_u23_small_u2D_indices cls3_cl_node_app_u3A_factorization_u23_coupling_u2D_scope

/-- Closed proof of `rt:m-renewal`. -/
theorem cls3_cl_node_rt_u3A_m_u2D_renewal : node_rt_u3A_m_u2D_renewalStmtV2 :=
  node_rt_u3A_m_u2D_renewal_v2_of_deps cls3_cl_node_rt_u3A_factorization cls3_cl_node_rt_u3A_global_u2D_geometry

/-- Closed proof of `rt:two-masses`. -/
theorem cls3_cl_node_rt_u3A_two_u2D_masses : node_rt_u3A_two_u2D_massesStmt :=
  node_rt_u3A_two_u2D_masses_of_deps cls3_cl_node_rt_u3A_renewal_u23_tube_u2D_probability cls3_cl_node_app_u3A_factorization_u23_endpoint_u2D_disintegration cls3_cl_node_app_u3A_factorization_u23_independence cls3_cl_node_rt_u3A_renewal_u23_tube_u2D_geometry cls3_cl_node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transfer

/-- Closed proof of `rt:renewal#zero-exclusion`. -/
theorem cls3_cl_node_rt_u3A_renewal_u23_zero_u2D_exclusion : node_rt_u3A_renewal_u23_zero_u2D_exclusionStmt :=
  node_rt_u3A_renewal_u23_zero_u2D_exclusion_of_deps cls3_cl_node_rt_u3A_two_u2D_masses cls3_cl_node_app_u3A_regen_u2D_tails

/-- Closed proof of `rt:renewal#cauchy`. -/
theorem cls3_cl_node_rt_u3A_renewal_u23_cauchy : node_rt_u3A_renewal_u23_cauchyStmt :=
  node_rt_u3A_renewal_u23_cauchy_of_deps cls3_cl_node_rt_u3A_renewal_u23_zero_u2D_exclusion

/-- Closed proof of `rt:many-cycle-moment`. -/
theorem cls3_cl_node_rt_u3A_many_u2D_cycle_u2D_moment : node_rt_u3A_many_u2D_cycle_u2D_momentStmtV2 :=
  node_rt_u3A_many_u2D_cycle_u2D_moment_v2_of_deps cls3_cl_node_rt_u3A_factorization cls3_cl_node_app_u3A_regen_u2D_tails cls3_cl_node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transfer

/-- Closed proof of `rt:renewal`. -/
theorem cls3_cl_node_rt_u3A_renewal : node_rt_u3A_renewalStmtV2 :=
  node_rt_u3A_renewal_of_depsV2 cls3_cl_node_rt_u3A_renewal_u23_cauchy cls3_cl_node_rt_u3A_many_u2D_cycle_u2D_moment cls3_cl_node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transfer

/-- Closed proof of `rt:remainder-moment`. -/
theorem cls3_cl_node_rt_u3A_remainder_u2D_moment : node_rt_u3A_remainder_u2D_momentStmt :=
  s6_remainder_moment_of_original_deps cls3_cl_node_app_u3A_regen_u2D_tails cls3_cl_node_e_u3A_generators_u23_real_u2D_semigroup

/-- Closed proof of `rt:local-mixing#fixed-radius`. -/
theorem cls3_cl_node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radius : node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radiusStmtV4 :=
  node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radius_v4_of_deps cls3_cl_node_rt_u3A_factorization cls3_cl_node_rt_u3A_renewal cls3_cl_node_rt_u3A_remainder_u2D_moment cls3_cl_node_app_u3A_regen_u2D_tails

/-- Closed proof of `rt:local-mixing#phase-error`. -/
theorem cls3_cl_node_rt_u3A_local_u2D_mixing_u23_phase_u2D_error : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmtV4 :=
  node_rt_u3A_local_u2D_mixing_u23_phase_u2D_error_v4_of_deps cls3_cl_node_rt_u3A_m_u2D_renewal cls3_cl_node_rt_u3A_renewal cls3_cl_node_rt_u3A_remainder_u2D_moment cls3_cl_node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radius

/-- Closed proof of `rt:km-decomp`. -/
theorem cls3_cl_node_rt_u3A_km_u2D_decomp : node_rt_u3A_km_u2D_decompStmtV4 :=
  node_rt_u3A_km_u2D_decomp_of_deps cls3_cl_node_rt_u3A_k_u2D_factor cls3_cl_node_rt_u3A_local_u2D_mixing_u23_phase_u2D_error cls3_cl_node_rt_u3A_many_u2D_cycle_u2D_moment cls3_cl_node_rt_u3A_remainder_u2D_moment

/-- Closed proof of `rt:local-mixing`. -/
theorem cls3_cl_node_rt_u3A_local_u2D_mixing : node_rt_u3A_local_u2D_mixingStmtV2 :=
  node_rt_u3A_local_u2D_mixing_of_depsV2 cls3_cl_node_rt_u3A_km_u2D_decomp

/-- Closed proof of `p:tail#sum`. -/
theorem cls3_cl_node_p_u3A_tail_u23_sum : node_p_u3A_tail_u23_sumStmtV2 :=
  node_p_u3A_tail_u23_sum_v2_of_deps cls3_cl_node_p_u3A_tail_u23_small_u2D_endpoints cls3_cl_node_p_u3A_tail_u23_annuli cls3_cl_node_rt_u3A_local_u2D_mixing

/-- Closed proof of `p:tail`. -/
theorem cls3_cl_node_p_u3A_tail : node_p_u3A_tailStmt :=
  node_p_u3A_tail_of_depsV2 cls3_cl_node_p_u3A_tail_u23_sum

/-- Closed proof of `p:integration#uniform-profile-bounds`. -/
theorem cls3_cl_node_p_u3A_integration_u23_uniform_u2D_profile_u2D_bounds : node_p_u3A_integration_u23_uniform_u2D_profile_u2D_boundsStmt :=
  node_p_u3A_integration_u23_uniform_u2D_profile_u2D_bounds_of_deps cls3_cl_node_p_u3A_covariance cls3_cl_node_corrector_u2D_construction

/-- Closed proof of `p:integration#compact-extension`. -/
theorem cls3_cl_node_p_u3A_integration_u23_compact_u2D_extension : node_p_u3A_integration_u23_compact_u2D_extensionStmt :=
  node_p_u3A_integration_u23_compact_u2D_extension_of_deps cls3_cl_node_p_u3A_profile cls3_cl_node_finite_u2D_time_u2D_analyticity cls3_cl_node_p_u3A_integration_u23_uniform_u2D_profile_u2D_bounds

/-- Closed proof of `p:integration#common-window-data`. -/
theorem cls3_cl_node_p_u3A_integration_u23_common_u2D_window_u2D_data : node_p_u3A_integration_u23_common_u2D_window_u2D_dataStmt :=
  node_p_u3A_integration_u23_common_u2D_window_u2D_data_of_deps cls3_cl_node_p_u3A_profile cls3_cl_node_p_u3A_tail cls3_cl_node_p_u3A_integration_u23_compact_u2D_extension cls3_cl_node_p_u3A_integration_u23_uniform_u2D_profile_u2D_bounds

/-- Closed proof of `p:integration#actual-kernel-application`. -/
theorem cls3_cl_node_p_u3A_integration_u23_actual_u2D_kernel_u2D_application : node_p_u3A_integration_u23_actual_u2D_kernel_u2D_applicationStmt :=
  node_p_u3A_integration_u23_actual_u2D_kernel_u2D_application_of_deps cls3_cl_node_finite_u2D_time_u2D_analyticity cls3_cl_node_p_u3A_integration_u23_kernel_u2D_measurability_u2D_reality cls3_cl_node_p_u3A_profile cls3_cl_node_p_u3A_integration_u23_common_u2D_window_u2D_data

/-- Closed proof of `p:response#core-extension`. -/
theorem cls3_cl_node_p_u3A_response_u23_core_u2D_extension : node_p_u3A_response_u23_core_u2D_extensionStmt :=
  node_p_u3A_response_u23_core_u2D_extension_of_deps cls3_cl_node_stationary_u2D_environment cls3_cl_node_e_u3A_generators_u23_real_u2D_semigroup

/-- Closed proof of `eq.time-change-identities#forced-lln`. -/
theorem cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_lln : node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_llnStmtV2 :=
  node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_lln_of_deps cls3_cl_node_eq_u2E_reduced_u2D_generator_u23_pathwise cls3_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `eq.time-change-identities#forced-clock`. -/
theorem cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clock : node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clockStmtV2 :=
  node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clock_of_deps cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_lln cls3_cl_node_eq_u2E_reduced_u2D_generator_u23_pathwise cls3_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `eq.time-change-identities#corrector-covariance`. -/
theorem cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_corrector_u2D_covariance : node_eq_u2E_time_u2D_change_u2D_identities_u23_corrector_u2D_covarianceStmtV2 :=
  node_eq_u2E_time_u2D_change_u2D_identities_u23_corrector_u2D_covariance_of_deps cls3_cl_node_stationary_u2D_environment_u23_unforced_u2D_process cls3_cl_node_corrector_u2D_construction

/-- Closed proof of `eq.time-change-identities#unforced-clock`. -/
theorem cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clock : node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clockStmtV2 :=
  node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clock_of_deps cls3_cl_node_stationary_u2D_environment_u23_unforced_u2D_process cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_corrector_u2D_covariance cls3_cl_node_eq_u2E_reduced_u2D_generator_u23_pathwise

/-- Closed proof of `eq.time-change-identities`. -/
theorem cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2 :=
  node_eq_u2E_time_u2D_change_u2D_identities_of_deps cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clock cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clock

/-- Closed proof of `p:response#cesaro-abel`. -/
theorem cls3_cl_node_p_u3A_response_u23_cesaro_u2D_abel : node_p_u3A_response_u23_cesaro_u2D_abelStmt :=
  node_p_u3A_response_u23_cesaro_u2D_abel_of_deps cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities cls3_cl_node_p_u3A_response_u23_core_u2D_extension cls3_cl_node_e_u3A_generators_u23_real_u2D_semigroup

/-- Closed proof of `p:response`. -/
theorem cls3_cl_node_p_u3A_response : node_p_u3A_responseStmt :=
  node_p_u3A_response_of_deps cls3_cl_node_p_u3A_response_u23_core_u2D_extension cls3_cl_node_p_u3A_response_u23_cesaro_u2D_abel

/-- Closed proof of `finite-time-analyticity#abel-removal`. -/
theorem cls3_cl_node_finite_u2D_time_u2D_analyticity_u23_abel_u2D_removal : node_finite_u2D_time_u2D_analyticity_u23_abel_u2D_removalStmt :=
  node_finite_u2D_time_u2D_analyticity_u23_abel_u2D_removal_of_deps cls3_cl_node_p_u3A_response cls3_cl_node_p_u3A_tail cls3_cl_node_p_u3A_integration_u23_actual_u2D_kernel_u2D_application

/-- Closed proof of `clock-zero-coefficient`. -/
theorem cls3_cl_node_clock_u2D_zero_u2D_coefficient : node_clock_u2D_zero_u2D_coefficientStmt :=
  node_clock_u2D_zero_u2D_coefficient_of_deps cls3_cl_node_p_u3A_response cls3_cl_node_p_u3A_profile

/-- Closed proof of `e:numerator-clock`. -/
theorem cls3_cl_node_e_u3A_numerator_u2D_clock : node_e_u3A_numerator_u2D_clockStmt :=
  node_e_u3A_numerator_u2D_clock_of_deps cls3_cl_node_p_u3A_integration_u23_actual_u2D_kernel_u2D_application cls3_cl_node_finite_u2D_time_u2D_analyticity_u23_abel_u2D_removal cls3_cl_node_p_u3A_response cls3_cl_node_clock_u2D_zero_u2D_coefficient

/-- Closed proof of `e:linear-velocity#massive-gradients`. -/
theorem cls3_cl_node_e_u3A_linear_u2D_velocity_u23_massive_u2D_gradients : node_e_u3A_linear_u2D_velocity_u23_massive_u2D_gradientsStmt :=
  node_e_u3A_linear_u2D_velocity_u23_massive_u2D_gradients_of_deps cls3_cl_node_e_u3A_generators_u23_real_u2D_semigroup cls3_cl_node_corrector_u2D_construction

/-- Closed proof of `e:linear-velocity#spectral-integral`. -/
theorem cls3_cl_node_e_u3A_linear_u2D_velocity_u23_spectral_u2D_integral : node_e_u3A_linear_u2D_velocity_u23_spectral_u2D_integralStmt :=
  node_e_u3A_linear_u2D_velocity_u23_spectral_u2D_integral_of_deps cls3_cl_node_e_u3A_linear_u2D_velocity_u23_massive_u2D_gradients cls3_cl_node_p_u3A_scalar

/-- Closed proof of `e:linear-velocity#energy`. -/
theorem cls3_cl_node_e_u3A_linear_u2D_velocity_u23_energy : node_e_u3A_linear_u2D_velocity_u23_energyStmt :=
  node_e_u3A_linear_u2D_velocity_u23_energy_of_deps cls3_cl_node_corrector_u2D_construction

/-- Closed proof of `e:linear-velocity`. -/
theorem cls3_cl_node_e_u3A_linear_u2D_velocity : node_e_u3A_linear_u2D_velocityStmt :=
  node_e_u3A_linear_u2D_velocity_of_deps cls3_cl_node_e_u3A_linear_u2D_velocity_u23_spectral_u2D_integral cls3_cl_node_e_u3A_linear_u2D_velocity_u23_energy cls3_cl_node_p_u3A_response cls3_cl_node_p_u3A_tail

/-- Closed proof of `e:division`. -/
theorem cls3_cl_node_e_u3A_division : node_e_u3A_divisionStmt :=
  node_e_u3A_division_of_deps cls3_cl_node_e_u3A_numerator_u2D_clock cls3_cl_node_e_u3A_linear_u2D_velocity cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities cls3_cl_node_clock_u2D_zero_u2D_coefficient

/-- Closed proof of `t:expansion`. -/
theorem cls3_cl_node_t_u3A_expansion : node_t_u3A_expansionStmt :=
  node_t_u3A_expansion_of_deps cls3_cl_node_e_u3A_division

/-- Closed proof of `t.main#elementary-rate`. -/
theorem cls3_cl_node_t_u2E_main_u23_elementary_u2D_rate : node_t_u2E_main_u23_elementary_u2D_rateStmt :=
  node_t_u2E_main_u23_elementary_u2D_rate_of_deps cls3_cl_node_t_u3A_expansion

/-- Closed proof of `t.main`. -/
theorem cls3_cl_node_t_u2E_main : node_t_u2E_mainStmt :=
  node_t_u2E_main_of_deps cls3_cl_node_t_u2E_main_u23_elementary_u2D_rate

/-- Closed proof of `sharp.example#smooth-seed`. -/
theorem cls3_cl_node_sharp_u2E_example_u23_smooth_u2D_seed : node_sharp_u2E_example_u23_smooth_u2D_seedStmt :=
  node_sharp_u2E_example_u23_smooth_u2D_seed_of_deps

/-- Closed proof of `app:sharp-fields`. -/
theorem cls3_cl_node_app_u3A_sharp_u2D_fields : node_app_u3A_sharp_u2D_fieldsStmt :=
  node_app_u3A_sharp_u2D_fields_of_deps cls3_cl_node_sharp_u2E_example_u23_smooth_u2D_seed

/-- Closed proof of `app:sharp-harmonic`. -/
theorem cls3_cl_node_app_u3A_sharp_u2D_harmonic : node_app_u3A_sharp_u2D_harmonicStmt :=
  node_app_u3A_sharp_u2D_harmonic_of_deps cls3_cl_node_app_u3A_sharp_u2D_fields cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities

/-- Closed proof of `app:sharp-clock`. -/
theorem cls3_cl_node_app_u3A_sharp_u2D_clock : node_app_u3A_sharp_u2D_clockStmt :=
  node_app_u3A_sharp_u2D_clock_of_deps cls3_cl_node_app_u3A_sharp_u2D_harmonic cls3_cl_node_app_u3A_sharp_u2D_fields cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities

/-- Closed proof of `sharp.example#seed-nonconstancy`. -/
theorem cls3_cl_node_sharp_u2E_example_u23_seed_u2D_nonconstancy : node_sharp_u2E_example_u23_seed_u2D_nonconstancyStmt :=
  node_sharp_u2E_example_u23_seed_u2D_nonconstancy_of_deps

/-- Closed proof of `sharp.example#seed-ergodicity`. -/
theorem cls3_cl_node_sharp_u2E_example_u23_seed_u2D_ergodicity : node_sharp_u2E_example_u23_seed_u2D_ergodicityStmt :=
  node_sharp_u2E_example_u23_seed_u2D_ergodicity_of_deps cls3_cl_node_sharp_u2E_example_u23_smooth_u2D_seed

/-- Closed proof of `sharp.example#replacement-pair`. -/
theorem cls3_cl_node_sharp_u2E_example_u23_replacement_u2D_pair : node_sharp_u2E_example_u23_replacement_u2D_pairStmt :=
  node_sharp_u2E_example_u23_replacement_u2D_pair_of_deps cls3_cl_node_app_u3A_sharp_u2D_fields

/-- Closed proof of `sharp.example#clock-continuity`. -/
theorem cls3_cl_node_sharp_u2E_example_u23_clock_u2D_continuity : node_sharp_u2E_example_u23_clock_u2D_continuityStmt :=
  node_sharp_u2E_example_u23_clock_u2D_continuity_of_deps cls3_cl_node_sharp_u2E_example_u23_replacement_u2D_pair cls3_cl_node_e_u3A_numerator_u2D_clock cls3_cl_node_app_u3A_sharp_u2D_clock

/-- Closed proof of `sharp.example#positive-coefficient`. -/
theorem cls3_cl_node_sharp_u2E_example_u23_positive_u2D_coefficient : node_sharp_u2E_example_u23_positive_u2D_coefficientStmt :=
  node_sharp_u2E_example_u23_positive_u2D_coefficient_of_deps cls3_cl_node_sharp_u2E_example_u23_smooth_u2D_seed cls3_cl_node_app_u3A_sharp_u2D_fields cls3_cl_node_app_u3A_sharp_u2D_harmonic cls3_cl_node_app_u3A_sharp_u2D_clock cls3_cl_node_eq_u2E_time_u2D_change_u2D_identities cls3_cl_node_sharp_u2E_example_u23_seed_u2D_nonconstancy cls3_cl_node_sharp_u2E_example_u23_seed_u2D_ergodicity cls3_cl_node_sharp_u2E_example_u23_clock_u2D_continuity

/-- Closed proof of `sharp.example`. -/
theorem cls3_cl_node_sharp_u2E_example : node_sharp_u2E_exampleStmt :=
  node_sharp_u2E_example_of_deps cls3_cl_node_sharp_u2E_example_u23_positive_u2D_coefficient

end EinsteinFull.Blueprint
