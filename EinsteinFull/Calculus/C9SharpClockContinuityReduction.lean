import EinsteinFull.Calculus.C13SharpClockContinuity
import EinsteinFull.Calculus.U6RegularSignedPathRealization

namespace EinsteinFull.Blueprint

/-- Sharp clock continuity from its three original graph dependencies. -/
theorem node_sharp_u2E_example_u23_clock_u2D_continuity_of_deps
    (h0 : node_sharp_u2E_example_u23_replacement_u2D_pairStmt)
    (h1 : node_e_u3A_numerator_u2D_clockStmt)
    (h2 : node_app_u3A_sharp_u2D_clockStmt) :
    node_sharp_u2E_example_u23_clock_u2D_continuityStmt := by
  apply sharp_clock_continuity_of_announced_foundation ?_ h0 h1 h2
  intro d hd L R hL Q lam hnonneg hone
  obtain ⟨K, hK, hGMP, _⟩ :=
    u6_foundation_regular_signed_origin_law_and_mp hd hL Q lam hnonneg hone
  exact ⟨K, hK, hGMP⟩

end EinsteinFull.Blueprint
