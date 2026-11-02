import EinsteinFull.Blueprint.Roots.node_p_u3A_endpoint_u2D_comparison
import EinsteinFull.Blueprint.G3.node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identification
import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_early
import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_average
import EinsteinFull.Blueprint.G3.node_p_u3A_endpoint_u2D_comparison_u23_pairing

namespace EinsteinFull.Blueprint

/-- Project endpoint comparison and moments from the pairing contract.
The other direct graph dependencies are retained in their prescribed order;
their endpoint consequences are already included in the pairing contract. -/
@[nolint unusedArguments]
theorem node_p_u3A_endpoint_u2D_comparison_of_deps
    (_hunforced : node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identificationStmt)
    (_hearly : node_e_u3A_clock_u2D_earlyStmt)
    (_haverage : node_e_u3A_clock_u2D_averageStmt)
    (hpairing : node_p_u3A_endpoint_u2D_comparison_u23_pairingStmt) :
    node_p_u3A_endpoint_u2D_comparisonStmt := by
  intro d hd D
  obtain ⟨gain, C, hgain, hC, hdisc, hwindow, hmoments⟩ := hpairing d hd D
  refine ⟨gain, C, hgain, hC, ?_, ?_, hmoments⟩
  · intro Q hQ β a μ Z hβ ha hμ hZ R hR hRtwo z hz P Pdag hP hPdag
    exact (hdisc Q hQ β a μ Z hβ ha hμ hZ R hR hRtwo z hz P Pdag hP hPdag
      ).2.2.2.2.2.2.2
  · intro C₀ hC₀
    obtain ⟨Cw, R₀, hCw, hR₀, hw⟩ := hwindow C₀ hC₀
    refine ⟨Cw, R₀, hCw, hR₀, ?_⟩
    intro Q hQ β a μ Z hβ ha hμ hZ R hR hRlarge z hz P Pdag hP hPdag
    exact (hw Q hQ β a μ Z hβ ha hμ hZ R hR hRlarge z hz P Pdag hP hPdag
      ).2.2.2.2.2.2.2

end EinsteinFull.Blueprint
