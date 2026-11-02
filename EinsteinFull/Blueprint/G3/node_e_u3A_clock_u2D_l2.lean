import EinsteinFull.Work.W7.ClockFiniteRangeSupport

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:clock-l2`, `paper/main.tex:891–896`.
For arbitrary real spatial L2 tests the integral means the existing continuous
mean-square extension of the literal integral on L1 intersect L2. The actual
covariance integrand is absolutely integrable; no samplewise improper integral
is presumed. Constants depend only on dimension, ellipticity and range. -/
def node_e_u3A_clock_u2D_l2Stmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (Λ₀ r₀ : ℝ), 1 ≤ Λ₀ → 1 ≤ r₀ →
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d Λ₀ r₀)
      (f : Lp ℝ 2 (volume : Measure (Vec d))),
      Integrable (fun z : Vec d × Vec d =>
        f z.1 * f z.2 * clockCovariance Q z.1 z.2) ∧
      ‖clockTestL2 Q f‖ ^ 2 =
        ∫ z : Vec d × Vec d, f z.1 * f z.2 * clockCovariance Q z.1 z.2 ∧
      ‖clockTestL2 Q f‖ ^ 2 ≤ C * ‖f‖ ^ 2

end EinsteinFull.Blueprint
