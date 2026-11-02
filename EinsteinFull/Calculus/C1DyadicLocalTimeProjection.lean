import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_local
import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time

open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- The original forced local estimate supplies the local energy and time input. -/
theorem c1_dyadic_local_time_of_forced_local
    (hlocal : node_l_u3A_forced_u2D_localStmt) : node_e_u3A_local_u2D_timeStmt := by
  intro d hd D p hp
  obtain ⟨α, Cdet, c, N, hα, hCdet, hc, h⟩ := hlocal d hd D
  obtain ⟨C, Cp, hC, hCp, h⟩ := h p hp
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν
  obtain ⟨G, V, hgrad, henergy, _, _⟩ := h Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν
  refine ⟨G, V, hgrad, ?_⟩
  intro t ht
  exact ⟨(henergy t ht).1, (henergy t ht).2.1⟩

end EinsteinFull.Blueprint
