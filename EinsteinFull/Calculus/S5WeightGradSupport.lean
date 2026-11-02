import EinsteinFull.Calculus.S5CoefficientSupport
import EinsteinFull.Calculus.PhysicalH1WeightedIntegrationSupport
import EinsteinRelation.Calculus.HorizontalIntegration

/-!
# Smooth bounded exponential-type weights

A weight `φ` is smooth, bounded by `B`, and has Euclidean gradient bounded by `q |φ|`.
For such a weight the square `φ²` is a smooth multiplier with bounded derivatives, and its
gradient is bounded by `2 q φ²`.  Conjugation preserves the physical `H¹` graph.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

section S5WeightGrad

variable {d : ℕ}

theorem s5Nrm_smul (c : ℝ) (v : Fin d → ℝ) : s5Nrm (fun j => c * v j) = |c| * s5Nrm v := by
  unfold s5Nrm
  have h : ∑ j, (c * v j) ^ 2 = c ^ 2 * ∑ j, v j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem s5_abs_le_nrm (v : Fin d → ℝ) (j : Fin d) : |v j| ≤ s5Nrm v := by
  unfold s5Nrm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ j)

/-- A smooth bounded weight with gradient controlled by the weight itself. -/
structure S5Weight (φ : Vec d → ℝ) (B q : ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) φ
  B_nonneg : 0 ≤ B
  q_nonneg : 0 ≤ q
  bound : ∀ x, |φ x| ≤ B
  grad : ∀ x, s5Nrm (fun j => coordinateDerivative j φ x) ≤ q * |φ x|

variable {φ : Vec d → ℝ} {B q : ℝ}

theorem S5Weight.measurable (h : S5Weight φ B q) : Measurable φ := h.smooth.continuous.measurable

theorem S5Weight.sq_smooth (h : S5Weight φ B q) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x * φ x) := by
  have := h.smooth
  fun_prop

theorem S5Weight.sq_deriv (h : S5Weight φ B q) (j : Fin d) (x : Vec d) :
    coordinateDerivative j (fun y => φ y * φ y) x =
      (2 * φ x) * coordinateDerivative j φ x := by
  have hd : DifferentiableAt ℝ φ x := (h.smooth.differentiable (by simp)).differentiableAt
  rw [coordinateDerivative_mul j φ φ x hd hd]
  ring

theorem S5Weight.sq_grad (h : S5Weight φ B q) (x : Vec d) :
    s5Nrm (fun j => coordinateDerivative j (fun y => φ y * φ y) x) ≤
      2 * q * (φ x * φ x) := by
  have e : (fun j => coordinateDerivative j (fun y => φ y * φ y) x) =
      fun j => (2 * φ x) * coordinateDerivative j φ x := by
    funext j
    exact h.sq_deriv j x
  rw [e, s5Nrm_smul]
  have h1 := h.grad x
  have h2 : |2 * φ x| = 2 * |φ x| := by
    rw [abs_mul, abs_two]
  rw [h2]
  have h3 : |φ x| * |φ x| = φ x * φ x := abs_mul_abs_self _
  calc 2 * |φ x| * s5Nrm (fun j => coordinateDerivative j φ x)
      ≤ 2 * |φ x| * (q * |φ x|) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * q * (|φ x| * |φ x|) := by ring
    _ = 2 * q * (φ x * φ x) := by rw [h3]

theorem S5Weight.sq_bound (h : S5Weight φ B q) (x : Vec d) : |φ x * φ x| ≤ B * B := by
  rw [abs_mul]
  exact mul_le_mul (h.bound x) (h.bound x) (abs_nonneg _) h.B_nonneg

theorem S5Weight.sq_deriv_bound (h : S5Weight φ B q) (j : Fin d) (x : Vec d) :
    |coordinateDerivative j (fun y => φ y * φ y) x| ≤ 2 * q * (B * B) := by
  refine (s5_abs_le_nrm _ j).trans ((h.sq_grad x).trans ?_)
  have h1 : φ x * φ x ≤ B * B := (le_abs_self _).trans (h.sq_bound x)
  exact mul_le_mul_of_nonneg_left h1 (by have := h.q_nonneg; positivity)

theorem S5Weight.memLp_sq (h : S5Weight φ B q) :
    MemLp (fun x => ((φ x * φ x : ℝ) : ℂ)) ∞ (volume : Measure (Vec d)) := by
  refine memLp_top_of_bound ?_ (B * B) (Filter.Eventually.of_forall fun x => ?_)
  · exact (Complex.continuous_ofReal.comp
      (h.smooth.continuous.mul h.smooth.continuous)).aestronglyMeasurable
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact h.sq_bound x

theorem S5Weight.memLp_sq_deriv (h : S5Weight φ B q) (j : Fin d) :
    MemLp (fun x => (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) ∞
      (volume : Measure (Vec d)) := by
  have hρ := h.sq_smooth
  refine memLp_top_of_bound ?_ (2 * q * (B * B)) (Filter.Eventually.of_forall fun x => ?_)
  · exact (Complex.continuous_ofReal.comp
      ((hρ.continuous_fderiv (by simp)).clm_apply continuous_const)).aestronglyMeasurable
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact h.sq_deriv_bound j x

/-- Conjugation preserves the physical `H¹` graph. -/
theorem s5_isPhysicalH1Graph_star (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (h : IsPhysicalH1Graph volume (Or.inl rfl) u G) :
    IsPhysicalH1Graph volume (Or.inl rfl) (star u) (fun j => star (G j)) := by
  rw [isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) (star u)
    (fun j => star (G j)) (fun x => star (u x)) (fun j x => star (G j x))
    (Lp.coeFn_star u) (fun j => Lp.coeFn_star (G j))]
  constructor
  · intro j
    simpa only [Complex.star_def, Complex.conj_re] using h.1 j
  · intro j
    have h2 := h.2 j
    unfold HasWeakPartialDerivative at h2 ⊢
    refine ⟨?_, ?_, ?_⟩
    · simp only [Complex.star_def, Complex.conj_im]
      exact h2.1.neg
    · simp only [Complex.star_def, Complex.conj_im]
      exact h2.2.1.neg
    · intro ψ hψ
      have := h2.2.2 ψ hψ
      simp only [Complex.star_def, Complex.conj_im, neg_mul, MeasureTheory.integral_neg, this]

end S5WeightGrad

end EinsteinFull
