import EinsteinRelation.Calculus.CoordinatePathMomentBounds
import EinsteinRelation.Correctors.TimeIntegralLpBound

/-! # Joint integrability of coordinate path fluxes

Source: `paper/main.tex:1021–1029`. An integrable coordinate length
controls the full joint path integral by stationarity.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation

/-- Integrable path lengths give jointly integrable literal path fluxes
(`paper/main.tex:1021–1029`). -/
theorem integrable_coordinatePathFlux_joint {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [SFinite ν]
    {f : FieldPair d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 Q)
    (i : Fin d) (hi : Integrable (fun z : Vec d => |z i|) ν) :
    Integrable (fun q : Vec d × FieldPair d => coordinatePathFlux f q.1 q.2 i) (ν.prod Q) := by
  have hm : Measurable (fun q : FieldPair d × Vec d => coordinatePathFlux f q.2 q.1 i) :=
    (measurable_pi_apply i).comp ((measurable_coordinatePathFlux hf).comp measurable_swap)
  have hnorm : eLpNorm f 2 Q = ENNReal.ofReal (eLpNorm f 2 Q).toReal :=
    (ENNReal.ofReal_toReal hf2.eLpNorm_ne_top).symm
  have hj := Correctors.integrable_prod_of_eLpNorm_bound ν (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hm (hi.mul_const (eLpNorm f 2 Q).toReal) (fun z => by positivity)
    (fun z => by
      calc
        _ ≤ ENNReal.ofReal |z i| * eLpNorm f 2 Q :=
          eLpNorm_coordinatePathFlux_bound hQ (by norm_num) (by norm_num) hf z i
        _ = _ := by
          rw [ENNReal.ofReal_mul (abs_nonneg _)]
          exact congrArg (fun t => ENNReal.ofReal |z i| * t) hnorm)
  exact hj.swap

end EinsteinRelation
