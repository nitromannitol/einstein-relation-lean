import EinsteinRelation.Calculus.Weak
import EinsteinRelation.Environment.Bounds
import EinsteinRelation.Environment.Reduction
import EinsteinRelation.Correctors.EllipticOperatorBound
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Metrizable.Basic

open MeasureTheory
open scoped InnerProductSpace

namespace EinsteinRelation.SpatialDirichlet

noncomputable section

/-! # Integrability on the actual weighted weak-gradient graph

The graph stores function representatives and their distributional gradients. The results here
establish pairwise integrability of the literal Euclidean energy integrand under an operator bound;
they do not identify a quotient Sobolev domain or an associated semigroup.
-/

/-- A representative and its distributional weak gradient, both in weighted `L²`. -/
structure WeightedSobolevGraph {d : ℕ} (m : Measure (Vec d)) where
  value : Vec d → ℝ
  weakGradient : Vec d → EuclideanSpace ℝ (Fin d)
  value_memLp : MemLp value 2 m
  gradient_memLp : MemLp weakGradient 2 m
  distributionalGradient : HasWeakGradient Set.univ value
    (fun x => WithLp.ofLp (weakGradient x))

/-- The literal Euclidean bilinear energy integrand for a coefficient field. -/
def weightedFormIntegrand {d : ℕ} {m : Measure (Vec d)} (A : Vec d → Mat d)
    (u v : WeightedSobolevGraph m) : Vec d → ℝ := fun x => (1 / 2 : ℝ) *
      dot (WithLp.ofLp (u.weakGradient x))
        ((A x).mulVec (WithLp.ofLp (v.weakGradient x)))

private theorem dot_ofLp_eq_inner {d : ℕ} (v w : EuclideanSpace ℝ (Fin d)) :
    dot (WithLp.ofLp v) (WithLp.ofLp w) = inner ℝ v w := by
  simp [dot, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

private theorem continuous_dot_fields {X : Type*} [TopologicalSpace X] {d : ℕ}
    {u v : X → Vec d} (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x => dot (u x) (v x)) := by
  unfold dot
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp hu).mul ((continuous_apply i).comp hv)

/-- A measurable coefficient field with a pointwise Euclidean operator bound gives an integrable
energy integrand on every pair in the full weighted weak-gradient graph. -/
theorem weightedFormIntegrand_integrable_of_operatorBound {d : ℕ} {m : Measure (Vec d)}
    (A : Vec d → Mat d) (hA : Measurable A) (K : ℝ)
    (hoperator : ∀ x ξ, euclideanNorm ((A x).mulVec ξ) ≤ K * euclideanNorm ξ)
    (u v : WeightedSobolevGraph m) :
    Integrable (weightedFormIntegrand A u v) m := by
  have hproduct : Integrable
      (fun x => ‖u.weakGradient x‖ * ‖v.weakGradient x‖) m :=
    u.gradient_memLp.norm.integrable_mul v.gradient_memLp.norm
  have hmajor : Integrable
      (fun x => (K / 2) * (‖u.weakGradient x‖ * ‖v.weakGradient x‖)) m := by
    have h := hproduct.const_mul (K / 2)
    exact h.congr (ae_of_all _ fun x => by ring)
  have hmeas : AEStronglyMeasurable (weightedFormIntegrand A u v) m := by
    letI : TopologicalSpace.PseudoMetrizableSpace (Mat d) := by
      change TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ)
      infer_instance
    letI : SecondCountableTopology (Mat d) := by
      change SecondCountableTopology (Fin d → Fin d → ℝ)
      infer_instance
    have hfirst : Continuous (fun z : Mat d ×
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
        WithLp.ofLp z.2.1) := by fun_prop
    have hsecond : Continuous (fun z : Mat d ×
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
        z.1.mulVec (WithLp.ofLp z.2.2)) := by fun_prop
    have hcont : Continuous (fun z : Mat d ×
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
        (1 / 2 : ℝ) * dot (WithLp.ofLp z.2.1)
          (z.1.mulVec (WithLp.ofLp z.2.2))) :=
      continuous_const.mul (continuous_dot_fields hfirst hsecond)
    change AEStronglyMeasurable
      (fun x => (1 / 2 : ℝ) * dot (WithLp.ofLp (u.weakGradient x))
        ((A x).mulVec (WithLp.ofLp (v.weakGradient x)))) m
    exact hcont.comp_aestronglyMeasurable
      (hA.aestronglyMeasurable.prodMk
        (u.gradient_memLp.aestronglyMeasurable.prodMk v.gradient_memLp.aestronglyMeasurable))
  apply Integrable.mono' hmajor hmeas
  filter_upwards with x
  have hu_norm : euclideanNorm (WithLp.ofLp (u.weakGradient x)) =
      ‖u.weakGradient x‖ := by
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
  have hv_norm : euclideanNorm (WithLp.ofLp (v.weakGradient x)) =
      ‖v.weakGradient x‖ := by
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
  have hA_norm : ‖(WithLp.toLp 2
      ((A x).mulVec (WithLp.ofLp (v.weakGradient x))) : EuclideanSpace ℝ (Fin d))‖ ≤
      K * ‖v.weakGradient x‖ := by
    calc
      ‖(WithLp.toLp 2
          ((A x).mulVec (WithLp.ofLp (v.weakGradient x))) : EuclideanSpace ℝ (Fin d))‖ =
          euclideanNorm ((A x).mulVec (WithLp.ofLp (v.weakGradient x))) :=
        (TimeChange.euclideanNorm_eq_norm_toLp _).symm
      _ ≤ K * euclideanNorm (WithLp.ofLp (v.weakGradient x)) :=
        hoperator x (WithLp.ofLp (v.weakGradient x))
      _ = K * ‖v.weakGradient x‖ := by rw [hv_norm]
  have hdot : dot (WithLp.ofLp (u.weakGradient x))
      ((A x).mulVec (WithLp.ofLp (v.weakGradient x))) =
      inner ℝ (u.weakGradient x) (WithLp.toLp 2
        ((A x).mulVec (WithLp.ofLp (v.weakGradient x)))) := by
    rw [← dot_ofLp_eq_inner]
  have hdot_bound : |dot (WithLp.ofLp (u.weakGradient x))
      ((A x).mulVec (WithLp.ofLp (v.weakGradient x)))| ≤
      K * (‖u.weakGradient x‖ * ‖v.weakGradient x‖) := by
    rw [hdot]
    calc
      |inner ℝ (u.weakGradient x) (WithLp.toLp 2
          ((A x).mulVec (WithLp.ofLp (v.weakGradient x))))| ≤
          ‖u.weakGradient x‖ * ‖(WithLp.toLp 2
            ((A x).mulVec (WithLp.ofLp (v.weakGradient x))) : EuclideanSpace ℝ (Fin d))‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖u.weakGradient x‖ * (K * ‖v.weakGradient x‖) :=
        mul_le_mul_of_nonneg_left hA_norm (norm_nonneg _)
      _ = K * (‖u.weakGradient x‖ * ‖v.weakGradient x‖) := by ring
  calc
    ‖weightedFormIntegrand A u v x‖ =
        (1 / 2 : ℝ) * |dot (WithLp.ofLp (u.weakGradient x))
          ((A x).mulVec (WithLp.ofLp (v.weakGradient x)))| := by
      simp [weightedFormIntegrand, Real.norm_eq_abs]
    _ ≤ (1 / 2 : ℝ) *
        (K * (‖u.weakGradient x‖ * ‖v.weakGradient x‖)) :=
      mul_le_mul_of_nonneg_left hdot_bound (by norm_num)
    _ = (K / 2) * (‖u.weakGradient x‖ * ‖v.weakGradient x‖) := by ring

/-- The physical coefficient in a regular field has Euclidean operator norm at most `L`. -/
theorem physicalWeightedFormIntegrand_integrable_of_regular {d : ℕ} {m : Measure (Vec d)}
    (ω : FieldPair d) (L : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω)
    (u v : WeightedSobolevGraph m) :
    Integrable (weightedFormIntegrand ω.1 u v) m := by
  have hop : ∀ x ξ, euclideanNorm ((ω.1 x).mulVec ξ) ≤ L * euclideanNorm ξ := by
    intro x ξ
    exact Correctors.isElliptic_mulVec_euclideanNorm_le
      (lt_of_lt_of_le zero_lt_one hL) hω.1 x ξ
  exact weightedFormIntegrand_integrable_of_operatorBound ω.1
    ω.1.continuous.measurable L hop u v

/-- The reduced coefficient in a regular field has Euclidean operator norm at most
`exp (2*L) * L`. -/
theorem reducedWeightedFormIntegrand_integrable_of_regular {d : ℕ} {m : Measure (Vec d)}
    (ω : FieldPair d) (L : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω)
    (u v : WeightedSobolevGraph m) :
    Integrable (weightedFormIntegrand (reducedCoefficient ω) u v) m := by
  have hK : 0 < Real.exp (2 * L) * L := by positivity
  have hop : ∀ x ξ, euclideanNorm ((reducedCoefficient ω x).mulVec ξ) ≤
      (Real.exp (2 * L) * L) * euclideanNorm ξ := by
    intro x ξ
    apply Correctors.mulVec_euclideanNorm_le_of_quadratic (reducedCoefficient ω x) hK
      (reducedCoefficient_transpose ω x (hω.1 x).1)
    · intro η
      have hsq : 0 ≤ euclideanSq η := by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg (η i)
      have hlow := (reducedCoefficient_energy_bounds ω x η L hL hω).1
      have hfac : 0 ≤ Real.exp (-2 * L) * L⁻¹ :=
        mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr (le_trans zero_le_one hL))
      exact (mul_nonneg hfac hsq).trans hlow
    · exact fun η => (reducedCoefficient_energy_bounds ω x η L hL hω).2
  exact weightedFormIntegrand_integrable_of_operatorBound (reducedCoefficient ω)
    (reduce ω).1.continuous.measurable (Real.exp (2 * L) * L) hop u v

end

end EinsteinRelation.SpatialDirichlet
