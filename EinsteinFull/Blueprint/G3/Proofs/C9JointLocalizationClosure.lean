import EinsteinFull.Calculus.C9JointLocalizationProperties
import EinsteinFull.Calculus.C10JointLocalizationError
import EinsteinFull.Blueprint.G3.node_e_u3A_parameters
import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_l2

namespace EinsteinFull.Blueprint

/-- Assemble the selected joint field properties and its centered matrix error. -/
theorem node_p_u3A_covariance_u23_joint_u2D_localization_of_deps
    (_hparameters : node_e_u3A_parametersStmt)
    (_hclock : node_e_u3A_clock_u2D_l2Stmt) :
    node_p_u3A_covariance_u23_joint_u2D_localizationStmt := by
  intro d hd D s δ γ η β h
  obtain ⟨C, hC, herror⟩ :=
    covariance_joint_localization_centered_error d hd D s δ γ η β h
  obtain ⟨hclock, hfield⟩ := covariance_joint_localization_properties d hd D s δ γ η β h
  refine ⟨C, hC, hclock, ?_⟩
  intro Q hQ r hr
  obtain ⟨hmeas, hprops⟩ := hfield Q hQ r hr
  refine ⟨hmeas, fun x => ?_⟩
  obtain ⟨hcenter, hlocal, hstationary⟩ := hprops x
  exact ⟨hcenter, hlocal, hstationary, herror Q hQ r hr x⟩

end EinsteinFull.Blueprint
