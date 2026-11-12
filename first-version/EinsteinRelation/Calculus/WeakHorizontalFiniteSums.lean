import EinsteinRelation.Calculus.WeakCalculusAlgebra

/-! # Finite sums of weak horizontal identities

Source: `paper/main.tex:1044–1069`. The corrected function, its gradient, and
the two fluxes of Proposition 6.1 are finite sums over coordinates and scales.
-/

open MeasureTheory

namespace EinsteinRelation

variable {d : ℕ} {Q : Measure (FieldPair d)} {hQ : IsStationary Q}

/-- A finite sum of weak gradients is the weak gradient of the sum. -/
theorem HasWeakHorizontalGradient.finset_sum {ι : Type*} (s : Finset ι)
    {f : ι → FieldPair d → ℝ} {Df : ι → FieldPair d → Vec d}
    (h : ∀ j ∈ s, HasWeakHorizontalGradient Q hQ (f j) (Df j)) :
    HasWeakHorizontalGradient Q hQ (fun ω => ∑ j ∈ s, f j ω) (fun ω => ∑ j ∈ s, Df j ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using HasWeakHorizontalGradient.zero (Q := Q) (hQ := hQ)
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using
      (h j (Finset.mem_insert_self j s)).add
        (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- A finite sum of weak divergences is the weak divergence of the sum. -/
theorem HasWeakHorizontalDivergence.finset_sum {ι : Type*} (s : Finset ι)
    {V : ι → FieldPair d → Vec d} {f : ι → FieldPair d → ℝ}
    (h : ∀ j ∈ s, HasWeakHorizontalDivergence Q hQ (V j) (f j)) :
    HasWeakHorizontalDivergence Q hQ (fun ω => ∑ j ∈ s, V j ω) (fun ω => ∑ j ∈ s, f j ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using HasWeakHorizontalDivergence.zero (Q := Q) (hQ := hQ)
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using
      (h j (Finset.mem_insert_self j s)).add
        (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- The divergence of a scalar field times a constant vector is the constant
vector paired with its weak gradient. -/
theorem HasWeakHorizontalGradient.divergence_const_mul {u : FieldPair d → ℝ}
    {Du : FieldPair d → Vec d} (hu : HasWeakHorizontalGradient Q hQ u Du) (c : Vec d) :
    HasWeakHorizontalDivergence Q hQ (fun ω => u ω • c) (fun ω => dot c (Du ω)) := by
  refine ⟨fun i => hu.1.mul_const (c i),
    integrable_finset_sum _ fun i _ => (hu.2.1 i).const_mul (c i), fun F hF DF hDF => ?_⟩
  obtain ⟨B, hB⟩ := ae_bound_of_isHorizontallySmoothTest hF
  have hleft : ∀ i, Integrable (fun ω => u ω * DF i ω) Q := by
    intro i
    obtain ⟨C, hC⟩ := ae_bound_of_hasHorizontalLpDerivative hF (hDF i)
    exact integrable_mul_of_ae_bound hu.1 hC
  have hright : ∀ i, Integrable (fun ω => Du ω i * F ω) Q := fun i =>
    integrable_mul_of_ae_bound (hu.2.1 i) hB
  have heq : ∀ i, (∫ ω, (u ω • c) i * DF i ω ∂Q) = c i * ∫ ω, u ω * DF i ω ∂Q := by
    intro i
    calc
      _ = ∫ ω, c i * (u ω * DF i ω) ∂Q := by
        congr 1
        funext ω
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = _ := integral_const_mul _ _
  rw [integral_finset_sum _ fun i _ => by
    simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm] using
      (hleft i).const_mul (c i)]
  simp_rw [heq, hu.2.2 _ F _ hF (hDF _), mul_neg]
  rw [Finset.sum_neg_distrib]
  congr 1
  calc
    _ = ∫ ω, ∑ i, c i * (Du ω i * F ω) ∂Q := by
      simp_rw [← integral_const_mul]
      exact (integral_finset_sum _ fun i _ => (hright i).const_mul (c i)).symm
    _ = _ := by
      congr 1
      funext ω
      simp only [dot, Finset.sum_mul, mul_assoc]

end EinsteinRelation
