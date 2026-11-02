import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_flux
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_flux_u23_gain

namespace EinsteinFull.Blueprint

/-- The gain contract at `paper/main.tex:842–852` supplies the full weak-flux
conclusion at `paper/main.tex:718–736`. Retain its structural witnesses before
choosing the moment order, and retain both Gaussian and general test bounds. -/
theorem node_l_u3A_forced_u2D_flux_of_deps
    (hgain : node_l_u3A_forced_u2D_flux_u23_gainStmt) :
    node_l_u3A_forced_u2D_fluxStmt := by
  intro d hd D
  obtain ⟨_, _, η₀, ε, _, L, _, _, _, _, _, hε, hη₀, _, _, _, hp⟩ := hgain d hd D
  exact ⟨ε, η₀, L, hε, hη₀, hp⟩

end EinsteinFull.Blueprint
