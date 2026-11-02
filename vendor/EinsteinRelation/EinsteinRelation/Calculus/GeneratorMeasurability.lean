import EinsteinRelation.Calculus.Generator
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Measurability of the literal generator representatives

Source `paper/main.tex:61–80,194–217,240–255`. The actual total Frechet derivative
and each coordinate contraction are Borel measurable. This checks the concrete
physical/reduced generator expressions, without identifying a weak derivative
or modifying their values on spatial exceptional sets.
-/

open MeasureTheory

namespace EinsteinRelation

@[fun_prop] theorem measurable_coordinateDerivative {d : ℕ} (i : Fin d) (f : Vec d → ℝ) :
    Measurable (coordinateDerivative i f) :=
  measurable_fderiv_apply_const ℝ f (unitVector i)

@[fun_prop] theorem measurable_gradient {d : ℕ} (f : Vec d → ℝ) :
    Measurable (gradient f) := by
  exact Measurable.of_eval (fun i => measurable_coordinateDerivative i f)

@[fun_prop] theorem measurable_divergence {d : ℕ} (F : Vec d → Vec d) :
    Measurable (divergence F) := by
  unfold divergence
  fun_prop

@[fun_prop] theorem measurable_reducedGenerator {d : ℕ} (i : Fin d) (ω : FieldPair d)
    (lam : ℝ) (f : Vec d → ℝ) : Measurable (reducedGenerator i ω lam f) := by
  have hb : Measurable (fun x => (reducedCoefficient ω x).mulVec (unitVector i)) :=
    ((reduce ω).1.continuous.matrix_mulVec continuous_const).measurable
  have hdot : Measurable (fun x =>
      dot ((reducedCoefficient ω x).mulVec (unitVector i)) (gradient f x)) := by
    unfold dot
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp hb).mul
        ((measurable_pi_apply j).comp (measurable_gradient f))
  exact (measurable_const.mul (measurable_divergence _)).add (measurable_const.mul hdot)

@[fun_prop] theorem measurable_physicalGenerator {d : ℕ} (i : Fin d) (ω : FieldPair d)
    (lam : ℝ) (f : Vec d → ℝ) : Measurable (physicalGenerator i ω lam f) := by
  have ha : Measurable (fun x => ω.1 x) := ω.1.continuous.measurable
  have hV : Measurable (fun x => ω.2 x) := ω.2.continuous.measurable
  unfold physicalGenerator dot Matrix.mulVec dotProduct
  fun_prop

end EinsteinRelation
