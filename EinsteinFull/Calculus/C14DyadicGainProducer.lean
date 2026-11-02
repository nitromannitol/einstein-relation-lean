import EinsteinFull.Calculus.C19FirstUnitGradientProjection
import EinsteinFull.Calculus.C1DyadicLocalTimeProjection
import EinsteinFull.Calculus.C3DyadicCrudeEnergyProjection
import EinsteinFull.Calculus.C31FluxGainRoot
import EinsteinFull.Calculus.C14FluxBlockAssembly
import EinsteinFull.Calculus.C6IndependentBlocksAssembly
import EinsteinFull.Blueprint.G3.Proofs.C6SublinearPairReduction
import EinsteinFull.Blueprint.G2.Proofs.W2FluxParameters
import EinsteinFull.Blueprint.G2.Proofs.S1FluxIdentity

namespace EinsteinFull.Blueprint

/-- The original forced local estimate supplies the inputs for the dyadic flux gain. -/
theorem c14_dyadic_flux_gain (hlocal : node_l_u3A_forced_u2D_localStmt) :
    node_l_u3A_forced_u2D_flux_u23_gainStmt := by
  have hsp := node_e_u3A_sublinear_u2D_pair_of_deps
  have hparams := node_l_u3A_forced_u2D_flux_u23_parameters_of_deps hsp
  have hidentity := node_e_u3A_flux_u2D_identity_of_deps hsp
  have hlt := c1_dyadic_local_time_of_forced_local hlocal
  have hcr := c3_dyadic_crude_energy_of_forced_local hlocal
  have hloc := c19_dyadic_locality_input_of_forced_local hlocal
  have hblock := node_e_u3A_flux_u2D_block_of_deps hidentity hlt hparams hsp hcr
  have hindependent : node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocksStmtV2 :=
    c6_node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocks_of_deps hblock hloc hparams
  exact node_l_u3A_forced_u2D_flux_u23_gain_of_deps hindependent hparams hblock

end EinsteinFull.Blueprint
