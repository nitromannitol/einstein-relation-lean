import EinsteinFull.Blueprint.G1.node_rt_u3A_km_u2D_decomp
import EinsteinFull.Blueprint.Roots.node_rt_u3A_local_u2D_mixing

namespace EinsteinFull.Blueprint

/-- The signed-force covariance conclusion of the cycle decomposition gives
`rt:local-mixing` (`paper/main.tex:415–422, 520–534`) at a fixed structural
coupling scale and coin parameter. -/
theorem node_rt_u3A_local_u2D_mixing_of_deps
    (hkm : node_rt_u3A_km_u2D_decompStmt) :
    node_rt_u3A_local_u2D_mixingStmt := by
  intro d hd Λ₀ r₀
  obtain ⟨l, hl, hr, hscale⟩ := hkm d hd Λ₀ r₀
  obtain ⟨p, c, C, lam₀, hp, hc, hC, hlam, hlam_one, hcov⟩ :=
    hscale l le_rfl (1 / 2) (by norm_num) (by norm_num)
  refine ⟨l, p, c, C, lam₀, hl, hr, hp, hc, hC, hlam, hlam_one, ?_⟩
  intro Q lam hpos hsmall P hP
  exact (hcov Q).2 lam hpos hsmall P hP

end EinsteinFull.Blueprint
