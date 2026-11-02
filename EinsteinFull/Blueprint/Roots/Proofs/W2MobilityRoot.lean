import EinsteinFull.Blueprint.Roots.node_t_u2E_main
import EinsteinFull.Blueprint.G4.node_t_u2E_main_u23_elementary_u2D_rate

namespace EinsteinFull.Blueprint

/-- The signed elementary rate implies the positive-force mobility rate of
`paper/main.tex:136–144`, with the same structural witnesses. -/
theorem node_t_u2E_main_of_deps
    (hrate : node_t_u2E_main_u23_elementary_u2D_rateStmt) :
    node_t_u2E_mainStmt := by
  intro d hd D
  obtain ⟨C, lamStar, hC, hlamStar, _, _, hrate⟩ := hrate d hd D
  refine ⟨C, lamStar, hC, hlamStar, ?_⟩
  intro Q hQ P hP covariance hcovariance lam hlam hlam_le velocity hvelocity
  have habs : |lam| = lam := abs_of_pos hlam
  simpa only [habs] using
    hrate Q hQ P hP covariance hcovariance lam
      (habs.symm ▸ hlam) (habs.symm ▸ hlam_le) velocity hvelocity

end EinsteinFull.Blueprint
