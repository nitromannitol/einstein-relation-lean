import EinsteinFull.Blueprint.Foundation.Proofs.C4LocalTimeReduction
import EinsteinFull.Blueprint.Foundation.Proofs.CLCorrectorCovariance
import EinsteinFull.Blueprint.Foundation.Proofs.CanonicalLaw
import EinsteinFull.Blueprint.Foundation.Proofs.CorrectorConstruction
import EinsteinFull.Blueprint.Foundation.Proofs.D1PathwiseV2
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
import EinsteinFull.Blueprint.Foundation.Proofs.W2CenteredEquations
import EinsteinFull.Blueprint.Foundation.Proofs.W3Queue0330_1
import EinsteinFull.Blueprint.Foundation.Proofs.W4Queue0315
import EinsteinFull.Blueprint.Foundation.node_p_u3A_gauge_u23_closed_u2D_form
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
import EinsteinFull.Blueprint.G4.Proofs.CLTimeChangeV2
import EinsteinFull.Blueprint.G4.Proofs.ResponseCesaroAbel
import EinsteinFull.Blueprint.G4.Proofs.W2Queue0158_2
import EinsteinFull.Blueprint.Roots.Proofs.W1Queue0400_3
import EinsteinFull.Blueprint.Roots.Proofs.W1Queue0410
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
import EinsteinFull.Calculus.C31FluxGainRoot
import EinsteinFull.Calculus.C6DyadicFinalReduction
import EinsteinFull.Calculus.C7EndpointUniformProjection
import EinsteinFull.Calculus.CLForcedLLNV2
import EinsteinFull.Calculus.CLSmallTimeCrude
import EinsteinFull.Calculus.F2PointKernelExactAssembler

/-! Closed proofs of the numbered root mirrors `h:forced`, `l:finite-xi`, `l:forced-flux`, `l:forced-local`, `l:late-propagation`, `p:endpoint-comparison`, `p:late`, `p:profile`, `p:scalar`, `p:response`,
composed from the exact graph reductions in dependency order. Each `clr_cl_*`
applies one node's `_of_deps` reduction to the closed proofs of its ordered
graph hypotheses. -/

namespace EinsteinFull.Blueprint

/-- Closed proof of `eq.reduced-generator#pathwise`. -/
theorem clr_cl_node_eq_u2E_reduced_u2D_generator_u23_pathwise : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2 :=
  node_eq_u2E_reduced_u2D_generator_u23_pathwise_of_deps

/-- Closed proof of `eq.reduced-bounds`. -/
theorem clr_cl_node_eq_u2E_reduced_u2D_bounds : node_eq_u2E_reduced_u2D_boundsStmt :=
  node_eq_u2E_reduced_u2D_bounds_of_deps

/-- Closed proof of `stationary-environment#canonical-law`. -/
theorem clr_cl_node_stationary_u2D_environment_u23_canonical_u2D_law : node_stationary_u2D_environment_u23_canonical_u2D_lawStmt :=
  node_stationary_u2D_environment_u23_canonical_u2D_law_of_deps clr_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `stationary-environment`. -/
theorem clr_cl_node_stationary_u2D_environment : node_stationary_u2D_environmentStmt :=
  node_stationary_u2D_environment_of_deps clr_cl_node_stationary_u2D_environment_u23_canonical_u2D_law

/-- Closed proof of `stationary-environment#unforced-process`. -/
theorem clr_cl_node_stationary_u2D_environment_u23_unforced_u2D_process : node_stationary_u2D_environment_u23_unforced_u2D_processStmtV2 :=
  node_stationary_u2D_environment_u23_unforced_u2D_process_of_deps clr_cl_node_eq_u2E_reduced_u2D_generator_u23_pathwise clr_cl_node_stationary_u2D_environment clr_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `e:generators#real-semigroup`. -/
theorem clr_cl_node_e_u3A_generators_u23_real_u2D_semigroup : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2 :=
  node_e_u3A_generators_u23_real_u2D_semigroup_of_deps clr_cl_node_stationary_u2D_environment_u23_unforced_u2D_process clr_cl_node_eq_u2E_reduced_u2D_generator_u23_pathwise

/-- Closed proof of `eq.reduced-bounds#derivatives`. -/
theorem clr_cl_node_eq_u2E_reduced_u2D_bounds_u23_derivatives : node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt :=
  node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps clr_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `p:gauge#closed-form`. -/
theorem clr_cl_node_p_u3A_gauge_u23_closed_u2D_form : node_p_u3A_gauge_u23_closed_u2D_formStmt :=
  node_p_u3A_gauge_u23_closed_u2D_form_of_deps

/-- Closed proof of `p:gauge#holomorphic`. -/
theorem clr_cl_node_p_u3A_gauge_u23_holomorphic : node_p_u3A_gauge_u23_holomorphicStmt :=
  node_p_u3A_gauge_u23_holomorphic_of_deps clr_cl_node_p_u3A_gauge_u23_closed_u2D_form

/-- Closed proof of `stationary-analytic-semigroup`. -/
theorem clr_cl_node_stationary_u2D_analytic_u2D_semigroup : node_stationary_u2D_analytic_u2D_semigroupStmt :=
  node_stationary_u2D_analytic_u2D_semigroup_of_deps clr_cl_node_e_u3A_generators_u23_real_u2D_semigroup clr_cl_node_eq_u2E_reduced_u2D_bounds_u23_derivatives clr_cl_node_p_u3A_gauge_u23_holomorphic

/-- Closed proof of `e:time-flux`. -/
theorem clr_cl_node_e_u3A_time_u2D_flux : node_e_u3A_time_u2D_fluxStmt :=
  node_e_u3A_time_u2D_flux_of_deps clr_cl_node_stationary_u2D_analytic_u2D_semigroup

/-- Closed proof of `e:centered-equations`. -/
theorem clr_cl_node_e_u3A_centered_u2D_equations : node_e_u3A_centered_u2D_equationsStmt :=
  node_e_u3A_centered_u2D_equations_of_deps

/-- Closed proof of `e:sublinear-pair`. -/
theorem clr_cl_node_e_u3A_sublinear_u2D_pair : node_e_u3A_sublinear_u2D_pairStmt :=
  node_e_u3A_sublinear_u2D_pair_of_deps

/-- Closed proof of `e:flux-identity`. -/
theorem clr_cl_node_e_u3A_flux_u2D_identity : node_e_u3A_flux_u2D_identityStmt :=
  node_e_u3A_flux_u2D_identity_of_deps clr_cl_node_e_u3A_sublinear_u2D_pair

/-- Closed proof of `e:lp-growth`. -/
theorem clr_cl_node_e_u3A_lp_u2D_growth : node_e_u3A_lp_u2D_growthStmt :=
  node_e_u3A_lp_u2D_growth_of_deps clr_cl_node_stationary_u2D_environment clr_cl_node_stationary_u2D_analytic_u2D_semigroup

/-- Closed proof of `l:forced-local#centered-source`. -/
theorem clr_cl_node_l_u3A_forced_u2D_local_u23_centered_u2D_source : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt :=
  node_l_u3A_forced_u2D_local_u23_centered_u2D_source_of_deps clr_cl_node_e_u3A_lp_u2D_growth

/-- Closed proof of `e:local-time`. -/
theorem clr_cl_node_e_u3A_local_u2D_time : node_e_u3A_local_u2D_timeStmt :=
  node_e_u3A_local_u2D_time_of_deps clr_cl_node_l_u3A_forced_u2D_local_u23_centered_u2D_source clr_cl_node_e_u3A_lp_u2D_growth

/-- Closed proof of `l:forced-flux#parameters`. -/
theorem clr_cl_node_l_u3A_forced_u2D_flux_u23_parameters : node_l_u3A_forced_u2D_flux_u23_parametersStmt :=
  node_l_u3A_forced_u2D_flux_u23_parameters_of_deps clr_cl_node_e_u3A_sublinear_u2D_pair

/-- Closed proof of `l:forced-local#off-diagonal`. -/
theorem clr_cl_node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal : node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt :=
  node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal_of_deps clr_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `l:forced-local#point-kernel`. -/
theorem clr_cl_node_l_u3A_forced_u2D_local_u23_point_u2D_kernel : node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt :=
  node_l_u3A_forced_u2D_local_u23_point_u2D_kernel_of_deps clr_cl_node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal clr_cl_node_e_u3A_local_u2D_time clr_cl_node_eq_u2E_reduced_u2D_bounds_u23_derivatives

/-- Closed proof of `l:forced-local#crude-energy`. -/
theorem clr_cl_node_l_u3A_forced_u2D_local_u23_crude_u2D_energy : node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt :=
  node_l_u3A_forced_u2D_local_u23_crude_u2D_energy_of_deps clr_cl_node_l_u3A_forced_u2D_local_u23_point_u2D_kernel

/-- Closed proof of `e:flux-block`. -/
theorem clr_cl_node_e_u3A_flux_u2D_block : node_e_u3A_flux_u2D_blockStmt :=
  node_e_u3A_flux_u2D_block_of_deps clr_cl_node_e_u3A_flux_u2D_identity clr_cl_node_e_u3A_local_u2D_time clr_cl_node_l_u3A_forced_u2D_flux_u23_parameters clr_cl_node_e_u3A_sublinear_u2D_pair clr_cl_node_l_u3A_forced_u2D_local_u23_crude_u2D_energy

/-- Closed proof of `l:forced-local#cutoff-environment`. -/
theorem clr_cl_node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environment : node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environmentStmt :=
  node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environment_of_deps clr_cl_node_eq_u2E_reduced_u2D_bounds clr_cl_node_eq_u2E_reduced_u2D_bounds_u23_derivatives

/-- Closed proof of `e:forced-locality`. -/
theorem clr_cl_node_e_u3A_forced_u2D_locality : node_e_u3A_forced_u2D_localityStmt :=
  node_e_u3A_forced_u2D_locality_of_deps clr_cl_node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environment clr_cl_node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal clr_cl_node_l_u3A_forced_u2D_local_u23_point_u2D_kernel clr_cl_node_e_u3A_local_u2D_time

/-- Closed proof of `l:forced-flux#independent-blocks`. -/
theorem clr_cl_node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocks : node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocksStmtV2 :=
  node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocks_of_deps clr_cl_node_e_u3A_flux_u2D_block clr_cl_node_e_u3A_forced_u2D_locality clr_cl_node_l_u3A_forced_u2D_flux_u23_parameters

/-- Closed proof of `l:forced-flux#gain`. -/
theorem clr_cl_node_l_u3A_forced_u2D_flux_u23_gain : node_l_u3A_forced_u2D_flux_u23_gainStmt :=
  node_l_u3A_forced_u2D_flux_u23_gain_of_deps clr_cl_node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocks clr_cl_node_l_u3A_forced_u2D_flux_u23_parameters clr_cl_node_e_u3A_flux_u2D_block

/-- Closed proof of `l:forced-flux`. -/
theorem clr_cl_node_l_u3A_forced_u2D_flux : node_l_u3A_forced_u2D_fluxStmt :=
  node_l_u3A_forced_u2D_flux_of_deps clr_cl_node_l_u3A_forced_u2D_flux_u23_gain

/-- Closed proof of `stationary-analytic-semigroup#endpoints`. -/
theorem clr_cl_node_stationary_u2D_analytic_u2D_semigroup_u23_endpoints : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt :=
  node_stationary_u2D_analytic_u2D_semigroup_u23_endpoints_of_deps clr_cl_node_stationary_u2D_analytic_u2D_semigroup clr_cl_node_e_u3A_forced_u2D_locality

/-- Closed proof of `p:scalar#unit-initialization`. -/
theorem clr_cl_node_p_u3A_scalar_u23_unit_u2D_initialization : node_p_u3A_scalar_u23_unit_u2D_initializationStmt :=
  node_p_u3A_scalar_u23_unit_u2D_initialization_of_deps clr_cl_node_e_u3A_forced_u2D_locality clr_cl_node_stationary_u2D_analytic_u2D_semigroup_u23_endpoints

/-- Closed proof of `p:scalar#bootstrap-average`. -/
theorem clr_cl_node_p_u3A_scalar_u23_bootstrap_u2D_average : node_p_u3A_scalar_u23_bootstrap_u2D_averageStmt :=
  node_p_u3A_scalar_u23_bootstrap_u2D_average_of_deps clr_cl_node_e_u3A_centered_u2D_equations clr_cl_node_l_u3A_forced_u2D_flux clr_cl_node_p_u3A_scalar_u23_unit_u2D_initialization

/-- Closed proof of `e:holder-average#unforced-interior`. -/
theorem clr_cl_node_e_u3A_holder_u2D_average_u23_unforced_u2D_interior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt :=
  node_e_u3A_holder_u2D_average_u23_unforced_u2D_interior_of_deps clr_cl_node_e_u3A_local_u2D_time

/-- Closed proof of `e:holder-average`. -/
theorem clr_cl_node_e_u3A_holder_u2D_average : node_e_u3A_holder_u2D_averageStmt :=
  node_e_u3A_holder_u2D_average_of_deps clr_cl_node_e_u3A_local_u2D_time clr_cl_node_e_u3A_lp_u2D_growth clr_cl_node_l_u3A_forced_u2D_local_u23_centered_u2D_source clr_cl_node_e_u3A_holder_u2D_average_u23_unforced_u2D_interior

/-- Closed proof of `p:scalar#smoothing-selection`. -/
theorem clr_cl_node_p_u3A_scalar_u23_smoothing_u2D_selection : node_p_u3A_scalar_u23_smoothing_u2D_selectionStmt :=
  node_p_u3A_scalar_u23_smoothing_u2D_selection_of_deps clr_cl_node_e_u3A_holder_u2D_average clr_cl_node_p_u3A_scalar_u23_bootstrap_u2D_average

/-- Closed proof of `p:scalar#bootstrap-point`. -/
theorem clr_cl_node_p_u3A_scalar_u23_bootstrap_u2D_point : node_p_u3A_scalar_u23_bootstrap_u2D_pointStmt :=
  node_p_u3A_scalar_u23_bootstrap_u2D_point_of_deps clr_cl_node_p_u3A_scalar_u23_bootstrap_u2D_average clr_cl_node_e_u3A_holder_u2D_average clr_cl_node_p_u3A_scalar_u23_unit_u2D_initialization clr_cl_node_p_u3A_scalar_u23_smoothing_u2D_selection

/-- Closed proof of `p:scalar`. -/
theorem clr_cl_node_p_u3A_scalar : node_p_u3A_scalarStmt :=
  node_p_u3A_scalar_of_deps clr_cl_node_p_u3A_scalar_u23_bootstrap_u2D_point

/-- Closed proof of `e:energy-target`. -/
theorem clr_cl_node_e_u3A_energy_u2D_target : node_e_u3A_energy_u2D_targetStmt :=
  node_e_u3A_energy_u2D_target_of_deps clr_cl_node_p_u3A_scalar clr_cl_node_e_u3A_centered_u2D_equations clr_cl_node_stationary_u2D_environment

/-- Closed proof of `l:forced-local`. -/
theorem clr_cl_node_l_u3A_forced_u2D_local : node_l_u3A_forced_u2D_localStmt :=
  node_l_u3A_forced_u2D_local_of_deps clr_cl_node_e_u3A_local_u2D_time clr_cl_node_e_u3A_holder_u2D_average clr_cl_node_e_u3A_forced_u2D_locality clr_cl_node_l_u3A_forced_u2D_local_u23_point_u2D_kernel

/-- Closed proof of `p:late#dyadic-increments`. -/
theorem clr_cl_node_p_u3A_late_u23_dyadic_u2D_increments : node_p_u3A_late_u23_dyadic_u2D_incrementsStmt :=
  node_p_u3A_late_u23_dyadic_u2D_increments_of_deps clr_cl_node_e_u3A_energy_u2D_target clr_cl_node_l_u3A_forced_u2D_local clr_cl_node_e_u3A_time_u2D_flux

/-- Closed proof of `e:local-av`. -/
theorem clr_cl_node_e_u3A_local_u2D_av : node_e_u3A_local_u2D_avStmt :=
  node_e_u3A_local_u2D_av_of_deps clr_cl_node_e_u3A_time_u2D_flux

/-- Closed proof of `stationary-analytic-semigroup#flux`. -/
theorem clr_cl_node_stationary_u2D_analytic_u2D_semigroup_u23_flux : node_stationary_u2D_analytic_u2D_semigroup_u23_fluxStmt :=
  node_stationary_u2D_analytic_u2D_semigroup_u23_flux_of_deps clr_cl_node_stationary_u2D_analytic_u2D_semigroup clr_cl_node_e_u3A_time_u2D_flux

/-- Closed proof of `p:late#cauchy`. -/
theorem clr_cl_node_p_u3A_late_u23_cauchy : node_p_u3A_late_u23_cauchyStmt :=
  node_p_u3A_late_u23_cauchy_of_deps clr_cl_node_p_u3A_late_u23_dyadic_u2D_increments clr_cl_node_e_u3A_local_u2D_av clr_cl_node_stationary_u2D_analytic_u2D_semigroup_u23_flux

/-- Closed proof of `p:late`. -/
theorem clr_cl_node_p_u3A_late : node_p_u3A_lateStmt :=
  node_p_u3A_late_of_deps clr_cl_node_p_u3A_late_u23_cauchy

/-- Closed proof of `l:late-propagation#smoothed-duhamel`. -/
theorem clr_cl_node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamel : node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamelStmt :=
  node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamel_of_deps clr_cl_node_p_u3A_scalar clr_cl_node_l_u3A_forced_u2D_flux clr_cl_node_e_u3A_centered_u2D_equations

/-- Closed proof of `l:late-propagation#unsmoothing`. -/
theorem clr_cl_node_l_u3A_late_u2D_propagation_u23_unsmoothing : node_l_u3A_late_u2D_propagation_u23_unsmoothingStmt :=
  node_l_u3A_late_u2D_propagation_u23_unsmoothing_of_deps clr_cl_node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamel clr_cl_node_e_u3A_holder_u2D_average clr_cl_node_p_u3A_scalar

/-- Closed proof of `l:late-propagation`. -/
theorem clr_cl_node_l_u3A_late_u2D_propagation : node_l_u3A_late_u2D_propagationStmt :=
  node_l_u3A_late_u2D_propagation_of_deps clr_cl_node_l_u3A_late_u2D_propagation_u23_unsmoothing

/-- Closed proof of `p:endpoint-comparison#force-replacement`. -/
theorem clr_cl_node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacement : node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacementStmt :=
  node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacement_of_deps clr_cl_node_e_u3A_time_u2D_flux clr_cl_node_p_u3A_late clr_cl_node_l_u3A_late_u2D_propagation

/-- Closed proof of `l:finite-xi#gradient-limit`. -/
theorem clr_cl_node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limit : node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limitStmt :=
  node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limit_of_deps clr_cl_node_p_u3A_scalar clr_cl_node_l_u3A_forced_u2D_local

/-- Closed proof of `corrector-construction`. -/
theorem clr_cl_node_corrector_u2D_construction : node_corrector_u2D_constructionStmt :=
  node_corrector_u2D_construction_of_deps clr_cl_node_stationary_u2D_environment clr_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `l:finite-xi#potential-identification`. -/
theorem clr_cl_node_l_u3A_finite_u2D_xi_u23_potential_u2D_identification : node_l_u3A_finite_u2D_xi_u23_potential_u2D_identificationStmt :=
  node_l_u3A_finite_u2D_xi_u23_potential_u2D_identification_of_deps clr_cl_node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limit clr_cl_node_corrector_u2D_construction clr_cl_node_e_u3A_generators_u23_real_u2D_semigroup

/-- Closed proof of `l:finite-xi#commutator-tail`. -/
theorem clr_cl_node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tail : node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tailStmt :=
  node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tail_of_deps clr_cl_node_l_u3A_finite_u2D_xi_u23_potential_u2D_identification

/-- Closed proof of `l:finite-xi#split-tail`. -/
theorem clr_cl_node_l_u3A_finite_u2D_xi_u23_split_u2D_tail : node_l_u3A_finite_u2D_xi_u23_split_u2D_tailStmt :=
  node_l_u3A_finite_u2D_xi_u23_split_u2D_tail_of_deps clr_cl_node_l_u3A_forced_u2D_flux clr_cl_node_p_u3A_scalar clr_cl_node_l_u3A_forced_u2D_local clr_cl_node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tail

/-- Closed proof of `l:finite-xi#scalar-integral`. -/
theorem clr_cl_node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integral : node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integralStmt :=
  node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integral_of_deps clr_cl_node_p_u3A_scalar clr_cl_node_p_u3A_scalar_u23_unit_u2D_initialization

/-- Closed proof of `l:finite-xi`. -/
theorem clr_cl_node_l_u3A_finite_u2D_xi : node_l_u3A_finite_u2D_xiStmt :=
  node_l_u3A_finite_u2D_xi_of_deps clr_cl_node_l_u3A_finite_u2D_xi_u23_split_u2D_tail clr_cl_node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integral

/-- Closed proof of `e:clock-l2`. -/
theorem clr_cl_node_e_u3A_clock_u2D_l2 : node_e_u3A_clock_u2D_l2Stmt :=
  node_e_u3A_clock_u2D_l2_of_deps

/-- Closed proof of `e:test-clt`. -/
theorem clr_cl_node_e_u3A_test_u2D_clt : node_e_u3A_test_u2D_cltStmt :=
  node_e_u3A_test_u2D_clt_of_deps clr_cl_node_e_u3A_clock_u2D_l2

/-- Closed proof of `p:endpoint-comparison#unforced-identification`. -/
theorem clr_cl_node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identification : node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identificationStmt :=
  node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identification_of_deps clr_cl_node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacement clr_cl_node_l_u3A_finite_u2D_xi clr_cl_node_l_u3A_late_u2D_propagation clr_cl_node_e_u3A_test_u2D_clt

/-- Closed proof of `stationary-analytic-semigroup#clock`. -/
theorem clr_cl_node_stationary_u2D_analytic_u2D_semigroup_u23_clock : node_stationary_u2D_analytic_u2D_semigroup_u23_clockStmt :=
  node_stationary_u2D_analytic_u2D_semigroup_u23_clock_of_deps clr_cl_node_stationary_u2D_analytic_u2D_semigroup clr_cl_node_l_u3A_forced_u2D_flux clr_cl_node_p_u3A_scalar

/-- Closed proof of `e:clock-average`. -/
theorem clr_cl_node_e_u3A_clock_u2D_average : node_e_u3A_clock_u2D_averageStmt :=
  node_e_u3A_clock_u2D_average_of_deps clr_cl_node_p_u3A_scalar clr_cl_node_l_u3A_forced_u2D_flux clr_cl_node_stationary_u2D_analytic_u2D_semigroup_u23_clock

/-- Closed proof of `e:clock-early`. -/
theorem clr_cl_node_e_u3A_clock_u2D_early : node_e_u3A_clock_u2D_earlyStmt :=
  node_e_u3A_clock_u2D_early_of_deps clr_cl_node_e_u3A_clock_u2D_average clr_cl_node_e_u3A_clock_u2D_l2 clr_cl_node_e_u3A_centered_u2D_equations clr_cl_node_l_u3A_late_u2D_propagation

/-- Closed proof of `p:endpoint-comparison#pairing`. -/
theorem clr_cl_node_p_u3A_endpoint_u2D_comparison_u23_pairing : node_p_u3A_endpoint_u2D_comparison_u23_pairingStmt :=
  node_p_u3A_endpoint_u2D_comparison_u23_pairing_of_deps clr_cl_node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identification clr_cl_node_e_u3A_clock_u2D_early clr_cl_node_e_u3A_clock_u2D_average clr_cl_node_p_u3A_scalar clr_cl_node_e_u3A_test_u2D_clt

/-- Closed proof of `p:endpoint-comparison`. -/
theorem clr_cl_node_p_u3A_endpoint_u2D_comparison : node_p_u3A_endpoint_u2D_comparisonStmt :=
  node_p_u3A_endpoint_u2D_comparison_of_deps clr_cl_node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identification clr_cl_node_e_u3A_clock_u2D_early clr_cl_node_e_u3A_clock_u2D_average clr_cl_node_p_u3A_endpoint_u2D_comparison_u23_pairing

/-- Closed proof of `h:forced`. -/
theorem clr_cl_node_h_u3A_forced : node_h_u3A_forcedStmt :=
  node_h_u3A_forced_of_deps clr_cl_node_p_u3A_endpoint_u2D_comparison clr_cl_node_p_u3A_scalar

/-- Closed proof of `e:parameters`. -/
theorem clr_cl_node_e_u3A_parameters : node_e_u3A_parametersStmt :=
  node_e_u3A_parameters_of_deps clr_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `corrector-construction#smooth-moments`. -/
theorem clr_cl_node_corrector_u2D_construction_u23_smooth_u2D_moments : node_corrector_u2D_construction_u23_smooth_u2D_momentsStmt :=
  node_corrector_u2D_construction_u23_smooth_u2D_moments_of_deps clr_cl_node_corrector_u2D_construction clr_cl_node_eq_u2E_reduced_u2D_bounds_u23_derivatives

/-- Closed proof of `p:covariance#coarse-identification`. -/
theorem clr_cl_node_p_u3A_covariance_u23_coarse_u2D_identification : node_p_u3A_covariance_u23_coarse_u2D_identificationStmt :=
  node_p_u3A_covariance_u23_coarse_u2D_identification_of_deps clr_cl_node_corrector_u2D_construction_u23_smooth_u2D_moments

/-- Closed proof of `p:covariance#joint-localization`. -/
theorem clr_cl_node_p_u3A_covariance_u23_joint_u2D_localization : node_p_u3A_covariance_u23_joint_u2D_localizationStmt :=
  node_p_u3A_covariance_u23_joint_u2D_localization_of_deps clr_cl_node_e_u3A_parameters clr_cl_node_e_u3A_clock_u2D_l2

/-- Closed proof of `p:covariance#test-replacement`. -/
theorem clr_cl_node_p_u3A_covariance_u23_test_u2D_replacement : node_p_u3A_covariance_u23_test_u2D_replacementStmt :=
  node_p_u3A_covariance_u23_test_u2D_replacement_of_deps clr_cl_node_e_u3A_parameters clr_cl_node_e_u3A_test_u2D_clt clr_cl_node_p_u3A_covariance_u23_coarse_u2D_identification clr_cl_node_p_u3A_covariance_u23_joint_u2D_localization

/-- Closed proof of `p:covariance#clock-blocks`. -/
theorem clr_cl_node_p_u3A_covariance_u23_clock_u2D_blocks : node_p_u3A_covariance_u23_clock_u2D_blocksStmt :=
  node_p_u3A_covariance_u23_clock_u2D_blocks_of_deps clr_cl_node_e_u3A_clock_u2D_l2 clr_cl_node_p_u3A_covariance_u23_joint_u2D_localization clr_cl_node_e_u3A_parameters

/-- Closed proof of `e:block-clt`. -/
theorem clr_cl_node_e_u3A_block_u2D_clt : node_e_u3A_block_u2D_cltStmt :=
  node_e_u3A_block_u2D_clt_of_deps clr_cl_node_p_u3A_covariance_u23_joint_u2D_localization clr_cl_node_p_u3A_covariance_u23_clock_u2D_blocks

/-- Closed proof of `e:block-boundary`. -/
theorem clr_cl_node_e_u3A_block_u2D_boundary : node_e_u3A_block_u2D_boundaryStmt :=
  node_e_u3A_block_u2D_boundary_of_deps clr_cl_node_p_u3A_covariance_u23_joint_u2D_localization clr_cl_node_p_u3A_covariance_u23_clock_u2D_blocks

/-- Closed proof of `e:block-change`. -/
theorem clr_cl_node_e_u3A_block_u2D_change : node_e_u3A_block_u2D_changeStmt :=
  node_e_u3A_block_u2D_change_of_deps clr_cl_node_p_u3A_covariance_u23_joint_u2D_localization clr_cl_node_p_u3A_covariance_u23_clock_u2D_blocks

/-- Closed proof of `e:block-recursion`. -/
theorem clr_cl_node_e_u3A_block_u2D_recursion : node_e_u3A_block_u2D_recursionStmt :=
  node_e_u3A_block_u2D_recursion_of_deps clr_cl_node_e_u3A_block_u2D_clt clr_cl_node_e_u3A_block_u2D_boundary clr_cl_node_e_u3A_block_u2D_change clr_cl_node_p_u3A_covariance_u23_joint_u2D_localization clr_cl_node_e_u3A_parameters

/-- Closed proof of `e:block-cov-rate`. -/
theorem clr_cl_node_e_u3A_block_u2D_cov_u2D_rate : node_e_u3A_block_u2D_cov_u2D_rateStmt :=
  node_e_u3A_block_u2D_cov_u2D_rate_of_deps clr_cl_node_e_u3A_block_u2D_recursion clr_cl_node_p_u3A_covariance_u23_joint_u2D_localization

/-- Closed proof of `p:covariance#test-blocks`. -/
theorem clr_cl_node_p_u3A_covariance_u23_test_u2D_blocks : node_p_u3A_covariance_u23_test_u2D_blocksStmt :=
  node_p_u3A_covariance_u23_test_u2D_blocks_of_deps clr_cl_node_e_u3A_block_u2D_clt clr_cl_node_e_u3A_block_u2D_boundary clr_cl_node_e_u3A_block_u2D_cov_u2D_rate clr_cl_node_p_u3A_covariance_u23_test_u2D_replacement clr_cl_node_p_u3A_covariance_u23_joint_u2D_localization

/-- Closed proof of `p:covariance#closure`. -/
theorem clr_cl_node_p_u3A_covariance_u23_closure : node_p_u3A_covariance_u23_closureStmt :=
  node_p_u3A_covariance_u23_closure_of_deps clr_cl_node_p_u3A_covariance_u23_test_u2D_replacement clr_cl_node_p_u3A_covariance_u23_test_u2D_blocks clr_cl_node_e_u3A_test_u2D_clt clr_cl_node_e_u3A_block_u2D_cov_u2D_rate

/-- Closed proof of `p:covariance`. -/
theorem clr_cl_node_p_u3A_covariance : node_p_u3A_covarianceStmt :=
  node_p_u3A_covariance_of_deps clr_cl_node_p_u3A_covariance_u23_closure

/-- Closed proof of `p:profile#static-comparison`. -/
theorem clr_cl_node_p_u3A_profile_u23_static_u2D_comparison : node_p_u3A_profile_u23_static_u2D_comparisonStmt :=
  node_p_u3A_profile_u23_static_u2D_comparison_of_deps clr_cl_node_p_u3A_covariance clr_cl_node_h_u3A_forced

/-- Closed proof of `e:fourier`. -/
theorem clr_cl_node_e_u3A_fourier : node_e_u3A_fourierStmt :=
  node_e_u3A_fourier_of_deps clr_cl_node_p_u3A_covariance

/-- Closed proof of `p:profile`. -/
theorem clr_cl_node_p_u3A_profile : node_p_u3A_profileStmt :=
  node_p_u3A_profile_of_deps clr_cl_node_p_u3A_profile_u23_static_u2D_comparison clr_cl_node_e_u3A_fourier

/-- Closed proof of `p:response#core-extension`. -/
theorem clr_cl_node_p_u3A_response_u23_core_u2D_extension : node_p_u3A_response_u23_core_u2D_extensionStmt :=
  node_p_u3A_response_u23_core_u2D_extension_of_deps clr_cl_node_stationary_u2D_environment clr_cl_node_e_u3A_generators_u23_real_u2D_semigroup

/-- Closed proof of `eq.time-change-identities#forced-lln`. -/
theorem clr_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_lln : node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_llnStmtV2 :=
  node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_lln_of_deps clr_cl_node_eq_u2E_reduced_u2D_generator_u23_pathwise clr_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `eq.time-change-identities#forced-clock`. -/
theorem clr_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clock : node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clockStmtV2 :=
  node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clock_of_deps clr_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_lln clr_cl_node_eq_u2E_reduced_u2D_generator_u23_pathwise clr_cl_node_eq_u2E_reduced_u2D_bounds

/-- Closed proof of `eq.time-change-identities#corrector-covariance`. -/
theorem clr_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_corrector_u2D_covariance : node_eq_u2E_time_u2D_change_u2D_identities_u23_corrector_u2D_covarianceStmtV2 :=
  node_eq_u2E_time_u2D_change_u2D_identities_u23_corrector_u2D_covariance_of_deps clr_cl_node_stationary_u2D_environment_u23_unforced_u2D_process clr_cl_node_corrector_u2D_construction

/-- Closed proof of `eq.time-change-identities#unforced-clock`. -/
theorem clr_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clock : node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clockStmtV2 :=
  node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clock_of_deps clr_cl_node_stationary_u2D_environment_u23_unforced_u2D_process clr_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_corrector_u2D_covariance clr_cl_node_eq_u2E_reduced_u2D_generator_u23_pathwise

/-- Closed proof of `eq.time-change-identities`. -/
theorem clr_cl_node_eq_u2E_time_u2D_change_u2D_identities : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2 :=
  node_eq_u2E_time_u2D_change_u2D_identities_of_deps clr_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clock clr_cl_node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clock

/-- Closed proof of `p:response#cesaro-abel`. -/
theorem clr_cl_node_p_u3A_response_u23_cesaro_u2D_abel : node_p_u3A_response_u23_cesaro_u2D_abelStmt :=
  node_p_u3A_response_u23_cesaro_u2D_abel_of_deps clr_cl_node_eq_u2E_time_u2D_change_u2D_identities clr_cl_node_p_u3A_response_u23_core_u2D_extension clr_cl_node_e_u3A_generators_u23_real_u2D_semigroup

/-- Closed proof of `p:response`. -/
theorem clr_cl_node_p_u3A_response : node_p_u3A_responseStmt :=
  node_p_u3A_response_of_deps clr_cl_node_p_u3A_response_u23_core_u2D_extension clr_cl_node_p_u3A_response_u23_cesaro_u2D_abel

end EinsteinFull.Blueprint
