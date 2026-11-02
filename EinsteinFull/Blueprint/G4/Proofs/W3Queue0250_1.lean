import EinsteinFull.Blueprint.G4.node_e_u3A_linear_u2D_velocity
import EinsteinFull.Blueprint.G4.node_e_u3A_linear_u2D_velocity_u23_spectral_u2D_integral
import EinsteinFull.Blueprint.G4.node_e_u3A_linear_u2D_velocity_u23_energy
import EinsteinFull.Blueprint.Roots.node_p_u3A_response
import EinsteinFull.Blueprint.Roots.node_p_u3A_tail

namespace EinsteinFull.Blueprint

/-- Combine the actual unforced spectral integral with the canonical corrector
energy identity to identify the linear velocity coefficient. -/
-- The prescribed graph also retains response and tail for its velocity interpretation.
@[nolint unusedArguments]
theorem node_e_u3A_linear_u2D_velocity_of_deps
    (hspectral : node_e_u3A_linear_u2D_velocity_u23_spectral_u2D_integralStmt)
    (henergy : node_e_u3A_linear_u2D_velocity_u23_energyStmt)
    (_hresponse : node_p_u3A_responseStmt)
    (_htail : node_p_u3A_tailStmt) :
    node_e_u3A_linear_u2D_velocityStmt := by
  intro d hd D Q hQ β a hβ ha
  dsimp only
  intro P hP i
  obtain ⟨hint, hs⟩ := hspectral d hd D Q hQ β a hβ ha P hP i
  refine ⟨⟨hint, hs⟩, ?_⟩
  rw [hs, henergy d hd D.ellipticity D.dependenceRange Q i]
  ring

end EinsteinFull.Blueprint
