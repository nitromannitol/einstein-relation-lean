import EinsteinRelation.Correctors.OrbitPotentialDomain
import Mathlib.MeasureTheory.Integral.Prod

/-! Source: `paper/main.tex:694-704,735-737`. A continuous spatial
gradient determines a potential normalized at the origin. The ray formula
makes this choice jointly measurable without choosing samplewise gauges. -/

open MeasureTheory

noncomputable section
namespace EinsteinRelation.Correctors

/-- The line integral along the segment from zero to the evaluation point. -/
def spatialRayPrimitive {d : ℕ} {Ω : Type*}
    (G : Ω → Vec d → Vec d) (ω : Ω) (x : Vec d) : ℝ :=
  ∫ t in (0 : ℝ)..1, dot x (G ω (t • x))

/-- Jointly measurable gradients yield a jointly measurable ray formula. -/
theorem measurable_spatialRayPrimitive {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (G : Ω → Vec d → Vec d)
    (hG : Measurable (fun p : Vec d × Ω => G p.2 p.1)) :
    Measurable (fun p : Vec d × Ω => spatialRayPrimitive G p.2 p.1) := by
  have hm : Measurable (fun p : (Vec d × Ω) × ℝ =>
      dot p.1.1 (G p.1.2 (p.2 • p.1.1))) := by
    have ht : Measurable (fun p : (Vec d × Ω) × ℝ => p.2 • p.1.1) :=
      measurable_snd.smul measurable_fst.fst
    have h := hG.comp (ht.prodMk measurable_fst.snd)
    unfold dot
    exact Finset.measurable_sum _ (fun j _ =>
      ((measurable_pi_apply j).comp measurable_fst.fst).mul
        ((measurable_pi_apply j).comp h))
  simp only [spatialRayPrimitive, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The ray formula recovers any continuously differentiable potential
with the supplied gradient, fixing only its value at the origin. -/
theorem spatialRayPrimitive_eq_sub_of_hasFDerivAt {d : ℕ}
    (u : Vec d → ℝ) (G : Vec d → Vec d) (hG : Continuous G)
    (hu : ∀ x, HasFDerivAt u
      (∑ j : Fin d, (G x j) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)) x)
    (x : Vec d) :
    spatialRayPrimitive (fun _ : Unit => G) () x = u x - u 0 := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => u (t • x)) (dot x (G (t • x))) t := by
    have ht : HasDerivAt (fun t : ℝ => t • x) x t := by
      simpa using (hasDerivAt_id' t).smul_const x
    convert (hu (t • x)).comp_hasDerivAt t ht using 1
    simp [dot, ContinuousLinearMap.sum_apply, mul_comm]
  have hc : Continuous (fun t : ℝ => dot x (G (t • x))) := by
    unfold dot
    exact continuous_finset_sum _ (fun j _ => continuous_const.mul
      ((continuous_apply j).comp (hG.comp (continuous_id.smul continuous_const))))
  simpa only [spatialRayPrimitive, one_smul, zero_smul] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      (hc.intervalIntegrable 0 1)

end EinsteinRelation.Correctors
