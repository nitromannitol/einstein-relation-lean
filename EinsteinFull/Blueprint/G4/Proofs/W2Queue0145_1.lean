import EinsteinFull.Blueprint.G4.node_e_u3A_linear_u2D_velocity_u23_energy
import EinsteinFull.Blueprint.Foundation.node_corrector_u2D_construction
import EinsteinFull.Work.W2.CorrectorCorrelationSupport

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull.Blueprint

/-- The canonical variational corrector identifies the homogenized coefficient
with the mean coefficient minus its anisotropic cross energy. The prescribed
graph premise is retained; the adopted canonical proof already supplies it. -/
@[nolint unusedArguments]
theorem node_e_u3A_linear_u2D_velocity_u23_energy_of_deps
    (_hcorrector : node_corrector_u2D_constructionStmt) :
    node_e_u3A_linear_u2D_velocity_u23_energyStmt := by
  intro d hd Λ₀ r₀ Q first i
  rw [homogenizedCoefficient_eq_mean_sub_corrector_energy,
    ← corrector_energy_eq_inner]
  congr 1
  apply integral_congr_ae
  filter_upwards with ω
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end EinsteinFull.Blueprint
