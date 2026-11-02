import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_l2

open MeasureTheory

namespace EinsteinFull.Blueprint

/-- The finite-range clock covariance estimate, graph node `e:clock-l2`,
`paper/main.tex:891–896`, on the actual mean-square extension to spatial L². -/
theorem node_e_u3A_clock_u2D_l2_of_deps : node_e_u3A_clock_u2D_l2Stmt := by
  intro d _ Λ₀ r₀ _ _
  refine ⟨max (clockVarianceConstant d Λ₀ r₀) 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro Q f
  refine ⟨integrable_clockCovariance_test_of_memLp Q
    (Lp.stronglyMeasurable f).measurable (Lp.memLp f),
    clockTestL2_norm_sq_eq_covariance Q f, ?_⟩
  exact (clockTestL2_norm_sq_le Q f).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ‖f‖))

end EinsteinFull.Blueprint
