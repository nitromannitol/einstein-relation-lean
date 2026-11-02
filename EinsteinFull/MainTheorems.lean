import EinsteinFull.Frozen.UniformSmallForceExpansion
import EinsteinFull.Frozen.MobilityRate
import EinsteinFull.Frozen.Response
import EinsteinFull.Frozen.EnvironmentalFactorization
import EinsteinFull.Frozen.UniformLatticeRenewal
import EinsteinFull.Frozen.LocalMixing
import EinsteinFull.Frozen.CorrelationTail
import EinsteinFull.Frozen.Gauge
import EinsteinFull.Frozen.ForcedScalarDecay
import EinsteinFull.Frozen.ForcedLocalEstimates
import EinsteinFull.Frozen.ForcedWeakFlux
import EinsteinFull.Frozen.CovarianceScaling
import EinsteinFull.Frozen.ForcedComparison
import EinsteinFull.Frozen.LateForceReplacement
import EinsteinFull.Frozen.FiniteTimeUnforcedCommutator
import EinsteinFull.Frozen.LateHomogeneousPropagation
import EinsteinFull.Frozen.EndpointComparison
import EinsteinFull.Frozen.CorrelationProfile
import EinsteinFull.Frozen.KernelIntegration
import EinsteinFull.Frozen.SharpExample
import EinsteinFull.Frozen.RegenerationFactorization

/-! # The numbered results of the paper

Each numbered result of the paper is stated in its own file under `EinsteinFull/Frozen/` and proved there
from the provider in `EinsteinFull/Proofs/`.

| Label | Declaration | File |
| --- | --- | --- |
| t:expansion | `EinsteinFull.Frozen.uniform_small_force_expansion` | `EinsteinFull/Frozen/UniformSmallForceExpansion.lean` |
| t.main | `EinsteinFull.Frozen.mobility_rate` | `EinsteinFull/Frozen/MobilityRate.lean` |
| p:response | `EinsteinFull.Frozen.response` | `EinsteinFull/Frozen/Response.lean` |
| rt:factorization | `EinsteinFull.Frozen.environmental_factorization` | `EinsteinFull/Frozen/EnvironmentalFactorization.lean` |
| rt:renewal | `EinsteinFull.Frozen.uniform_lattice_renewal` | `EinsteinFull/Frozen/UniformLatticeRenewal.lean` |
| rt:local-mixing | `EinsteinFull.Frozen.local_mixing` | `EinsteinFull/Frozen/LocalMixing.lean` |
| p:tail | `EinsteinFull.Frozen.correlation_tail` | `EinsteinFull/Frozen/CorrelationTail.lean` |
| p:gauge | `EinsteinFull.Frozen.gauge` | `EinsteinFull/Frozen/Gauge.lean` |
| p:scalar | `EinsteinFull.Frozen.forced_scalar_decay` | `EinsteinFull/Frozen/ForcedScalarDecay.lean` |
| l:forced-local | `EinsteinFull.Frozen.forced_local_estimates` | `EinsteinFull/Frozen/ForcedLocalEstimates.lean` |
| l:forced-flux | `EinsteinFull.Frozen.forced_weak_flux` | `EinsteinFull/Frozen/ForcedWeakFlux.lean` |
| p:covariance | `EinsteinFull.Frozen.covariance_scaling` | `EinsteinFull/Frozen/CovarianceScaling.lean` |
| h:forced | `EinsteinFull.Frozen.forced_comparison` | `EinsteinFull/Frozen/ForcedComparison.lean` |
| p:late | `EinsteinFull.Frozen.late_force_replacement` | `EinsteinFull/Frozen/LateForceReplacement.lean` |
| l:finite-xi | `EinsteinFull.Frozen.finite_time_unforced_commutator` | `EinsteinFull/Frozen/FiniteTimeUnforcedCommutator.lean` |
| l:late-propagation | `EinsteinFull.Frozen.late_homogeneous_propagation` | `EinsteinFull/Frozen/LateHomogeneousPropagation.lean` |
| p:endpoint-comparison | `EinsteinFull.Frozen.endpoint_comparison` | `EinsteinFull/Frozen/EndpointComparison.lean` |
| p:profile | `EinsteinFull.Frozen.correlation_profile` | `EinsteinFull/Frozen/CorrelationProfile.lean` |
| p:integration | `EinsteinFull.Frozen.kernel_integration` | `EinsteinFull/Frozen/KernelIntegration.lean` |
| sharp.example | `EinsteinFull.Frozen.sharp_example` | `EinsteinFull/Frozen/SharpExample.lean` |
| app:factorization | `EinsteinFull.Frozen.regeneration_factorization` | `EinsteinFull/Frozen/RegenerationFactorization.lean` |
-/
