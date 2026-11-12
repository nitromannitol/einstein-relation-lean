import EinsteinRelation.Correctors.WeakSkewDivergence
import EinsteinRelation.Calculus.WeakHorizontalDivergenceProducts

/-! # The skew flux cancellation in the scalar expansion

Source: `paper/main.tex:1050–1054`. If `R = Div S` and `S` is skew,
then `D · (g R + S Dg) = 0`. Applying this with `g = D_j u_r` gives the
cancellation used in the corrected generator equation of Proposition 6.1.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- The flux `g Div S + S Dg` is divergence-free for a weakly differentiable
scalar `g` and a skew matrix `S` (`paper/main.tex:1050–1054`). -/
theorem hasWeakHorizontalDivergence_skewProduct {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {S : FieldPair d → Mat d} {R Dg : FieldPair d → Vec d} {g : FieldPair d → ℝ}
    (hS : ∀ᵐ ω ∂Q, (S ω).transpose = -(S ω))
    (hrows : ∀ i, HasWeakHorizontalDivergence Q hQ (fun ω k => S ω i k) (fun ω => R ω i))
    (hg : HasWeakHorizontalGradient Q hQ g Dg)
    (hgm : Measurable g) (hDgm : Measurable Dg)
    (hS2 : ∀ i k, MemLp (fun ω => S ω i k) 2 Q)
    (hR2 : ∀ i, MemLp (fun ω => R ω i) 2 Q)
    (hg2 : MemLp g 2 Q) (hDg2 : ∀ i, MemLp (fun ω => Dg ω i) 2 Q) :
    HasWeakHorizontalDivergence Q hQ
      (fun ω i => g ω * R ω i + ∑ k, S ω i k * Dg ω k) (fun _ => 0) := by
  apply hasWeakHorizontalDivergence_rowDiv_of_skew
    (S := fun ω i k => g ω * S ω i k)
  · filter_upwards [hS] with ω hω
    ext i k
    have heq : S ω k i = -S ω i k := congrFun (congrFun hω i) k
    change g ω * S ω k i = -(g ω * S ω i k)
    rw [heq, mul_neg]
  · intro i
    exact (hrows i).mul_of_memLp_two hg hgm hDgm (hS2 i) (hR2 i) hg2 hDg2

end EinsteinRelation.Correctors
