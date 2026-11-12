import EinsteinRelation.Calculus.WeakCalculusAlgebra
import EinsteinRelation.Correctors.ScalarCorrectedFunction

/-! # Vanishing double divergence of a skew horizontal field

Source: `paper/main.tex:1050–1054`, Step 3 of Proposition 6.1.
The divergence of the row divergences of a skew-symmetric matrix field vanishes.
The proof works with the actual horizontal generators and only requires the
integrability already included in the weak row-divergence predicates.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- A skew horizontal matrix has zero double divergence
(`paper/main.tex:1050–1054`). The symmetry of the test Hessian follows from
commutation of the horizontal translation generators. -/
theorem hasWeakHorizontalDivergence_rowDiv_of_skew {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {S : FieldPair d → Mat d} {R : FieldPair d → Vec d}
    (hS : ∀ᵐ ω ∂Q, (S ω).transpose = -(S ω))
    (hrows : ∀ i, HasWeakHorizontalDivergence Q hQ (fun ω k => S ω i k) (fun ω => R ω i)) :
    HasWeakHorizontalDivergence Q hQ R (fun _ => 0) := by
  refine ⟨fun i => (hrows i).2.1, by simp, fun F hF DF hDF => ?_⟩
  have hex : ∀ i k, ∃ H : Lp ℝ 2 Q, HasHorizontalLpDerivative Q hQ k (DF i) H := by
    intro i k
    obtain ⟨H, hH, -⟩ := (hF.derivative (hDF i)) [k]
    obtain ⟨H₀, hH₀, hH₁⟩ := hH
    have heq : H₀ = DF i := hH₀
    exact ⟨H, heq ▸ hH₁⟩
  choose DDF hDDF using hex
  have hsym : ∀ i k, DDF i k = DDF k i := fun i k =>
    horizontal_derivative_comm (hDF i) (hDDF i k) (hDF k) (hDDF k i)
  have hH : ∀ ω, Matrix.transpose ((fun i k => DDF i k ω) : Mat d) = (fun i k => DDF i k ω) := by
    intro ω
    ext i k
    exact congrArg (fun Z : Lp ℝ 2 Q => Z ω) (hsym k i)
  have hsecond : ∀ i k, Integrable (fun ω => S ω i k * DDF i k ω) Q := by
    intro i k
    obtain ⟨C, hC⟩ := ae_bound_of_hasHorizontalLpDerivative (hF.derivative (hDF i)) (hDDF i k)
    exact integrable_mul_of_ae_bound ((hrows i).1 k) hC
  have hfirst : ∀ i, Integrable (fun ω => R ω i * DF i ω) Q := by
    intro i
    obtain ⟨C, hC⟩ := ae_bound_of_hasHorizontalLpDerivative hF (hDF i)
    exact integrable_mul_of_ae_bound ((hrows i).2.1) hC
  have hrow : ∀ i, (∫ ω, ∑ k, S ω i k * DDF i k ω ∂Q) = -(∫ ω, R ω i * DF i ω ∂Q) :=
    fun i => (hrows i).2.2 (DF i) (hF.derivative (hDF i)) (DDF i) (hDDF i)
  have hsum : (∑ i, ∫ ω, ∑ k, S ω i k * DDF i k ω ∂Q) =
      -(∑ i, ∫ ω, R ω i * DF i ω ∂Q) := by
    simp_rw [hrow]
    rw [Finset.sum_neg_distrib]
  have hzero : (∑ i, ∫ ω, ∑ k, S ω i k * DDF i k ω ∂Q) = 0 := by
    rw [← integral_finset_sum _ fun i _ => integrable_finset_sum _ fun k _ => hsecond i k]
    calc
      _ = ∫ _ω : FieldPair d, (0 : ℝ) ∂Q := by
        apply integral_congr_ae
        filter_upwards [hS] with ω hω
        exact scalarCorrected_skew_sum_eq_zero (S ω) (fun i k => DDF i k ω) hω (hH ω)
      _ = 0 := integral_zero _ _
  simp only [zero_mul, integral_zero, neg_zero]
  rw [integral_finset_sum _ fun i _ => hfirst i]
  linarith only [hsum, hzero]

end EinsteinRelation.Correctors
