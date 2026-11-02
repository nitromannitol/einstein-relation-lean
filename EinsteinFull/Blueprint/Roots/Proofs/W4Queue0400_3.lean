import EinsteinFull.Blueprint.Roots.node_l_u3A_late_u2D_propagation
import EinsteinFull.Blueprint.G3.node_l_u3A_late_u2D_propagation_u23_unsmoothing

namespace EinsteinFull.Blueprint

/-- Choose a single positive gain before the force-window constant, then take
the final combined estimate from unsmoothing. This is the conditional root
reduction for `paper/main.tex:1129–1137`. -/
theorem node_l_u3A_late_u2D_propagation_of_deps
    (hunsmoothing : node_l_u3A_late_u2D_propagation_u23_unsmoothingStmt) :
    node_l_u3A_late_u2D_propagationStmt := by
  intro d hd D δ hδ hδ'
  obtain ⟨ε, α, hε, hα, hstep⟩ := hunsmoothing d hd D
  obtain ⟨b, hb, _, hgain⟩ := hstep δ hδ hδ'
  have hδone : 0 < 1 - δ := by linarith
  have hεgain : 0 < ε * (1 - δ) / 2 := by positivity
  have hαgain : 0 < b * α / 2 := by positivity
  obtain ⟨ρ, hρ, hρlt⟩ := exists_between
    (lt_min (lt_min hεgain hαgain) hb)
  have hρε : ρ < ε * (1 - δ) / 2 := (lt_min_iff.mp (lt_min_iff.mp hρlt).1).1
  have hρα : ρ < b * α / 2 := (lt_min_iff.mp (lt_min_iff.mp hρlt).1).2
  have hρb : ρ < b := (lt_min_iff.mp hρlt).2
  have hwindow := hgain ρ hρ hρε hρα hρb
  obtain ⟨C, T₀, hC, hT₀, hdisc⟩ := hwindow 1 zero_lt_one
  refine ⟨ρ, C, T₀, hρ, hC, hT₀, ?_, ?_⟩
  · intro Q hQ β a μ hβ ha hμ T hT hlarge ζ hζ P Pdag hP hPdag ν
    exact (hdisc Q hQ β a μ hβ ha hμ T hT hlarge ζ (Or.inl hζ)
      P Pdag hP hPdag ν).2.2.2
  · intro C₀ hC₀
    obtain ⟨Cw, Tw, hCw, hTw, hreal⟩ := hwindow C₀ hC₀
    refine ⟨Cw, Tw, hCw, hTw, ?_⟩
    intro Q hQ β a μ hβ ha hμ T hT hlarge lam hlam P Pdag hP hPdag ν
    have hbound := (hreal Q hQ β a μ hβ ha hμ T hT hlarge (lam : ℂ)
      (Or.inr ⟨lam, rfl, hlam⟩) P Pdag hP hPdag ν).2.2.2
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hbound

end EinsteinFull.Blueprint
