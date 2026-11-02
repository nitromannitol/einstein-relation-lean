import EinsteinFull.Blueprint.Roots.node_h_u3A_forced
import EinsteinFull.Blueprint.Roots.node_p_u3A_endpoint_u2D_comparison
import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Calculus.ComplexTransposeSupport

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Project the forced comparison and moments from endpoint comparison, using
the actual bilinear transpose of each supplied forward family.
The graph's scalar dependency is retained; its moment consequence is already
included in the endpoint-comparison contract. -/
@[nolint unusedArguments]
theorem node_h_u3A_forced_of_deps
    (hendpoint : node_p_u3A_endpoint_u2D_comparisonStmt)
    (_hscalar : node_p_u3A_scalarStmt) : node_h_u3A_forcedStmt := by
  intro d hd D
  obtain ⟨gain, C, hgain, hC, hdisc, hwindow, hmoments⟩ := hendpoint d hd D
  refine ⟨2 * gain, C, mul_pos (by norm_num) hgain, hC, ?_, ?_, hmoments⟩
  · intro Q hQ β a μ Z hβ ha hμ hZ R hR hRtwo z hz P hP i
    exact (hdisc Q hQ β a μ Z hβ ha hμ hZ R hR hRtwo z hz P
      (fun t => complexL2Transpose (reducedLaw Q) (P t)) hP
      (isComplexTransposeSemigroup_complexL2Transpose Q P)).2 i
  · intro C₀ hC₀
    obtain ⟨Cw, R₀, hCw, hR₀, hw⟩ := hwindow C₀ hC₀
    refine ⟨Cw, R₀, hCw, hR₀, ?_⟩
    intro Q hQ β a μ Z hβ ha hμ hZ R hR hRlarge z hz P hP i
    exact (hw Q hQ β a μ Z hβ ha hμ hZ R hR hRlarge z hz P
      (fun t => complexL2Transpose (reducedLaw Q) (P t)) hP
      (isComplexTransposeSemigroup_complexL2Transpose Q P)).2 i

end EinsteinFull.Blueprint
