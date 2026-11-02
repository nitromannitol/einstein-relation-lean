import EinsteinRelation.Calculus.HorizontalSobolev

/-! # Weak horizontal calculus on the environment carriers

Source `paper/main.tex:235–260`. The horizontal derivative `D_j` is the L²(Q) generator of the
unitary translation group (`HasHorizontalLpDerivative`); its iterates along coordinate lists
define the horizontally smooth tests. The weak gradient, the weak divergence and the reduced
generator equation are stated against these actual L² generators. Identities involving `D`
hold in distributions, tested against horizontally smooth functions. No estimate, existence
result or identification with the paper's conclusions is assumed here.
-/

open MeasureTheory

namespace EinsteinRelation

/-- Source main.tex:241–244. Iterated horizontal derivative along a list of coordinates, with
the convention of `coordinateIterate`: the head coordinate is applied last, and the empty list
is the identity. -/
def HasIteratedHorizontalLpDerivative {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) : List (Fin d) → Lp ℝ 2 Q → Lp ℝ 2 Q → Prop
  | [], f, g => g = f
  | i :: rest, f, g => ∃ h : Lp ℝ 2 Q, HasIteratedHorizontalLpDerivative Q hQ rest f h ∧
      HasHorizontalLpDerivative Q hQ i h g

/-- Source main.tex:245. Horizontally smooth in the L²(Q) generator sense: for every list of
coordinates, the iterated horizontal derivative of `F` exists in `Lp ℝ 2 Q` and is
Q-essentially bounded. The empty list gives the essential boundedness of `F` itself. -/
def IsHorizontallySmoothTest {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (F : Lp ℝ 2 Q) : Prop :=
  ∀ coordinates : List (Fin d), ∃ G : Lp ℝ 2 Q,
    HasIteratedHorizontalLpDerivative Q hQ coordinates F G ∧ ∃ M : ℝ, ∀ᵐ ω ∂Q, |G ω| ≤ M

/-- Source main.tex:241–245. `Df` is the weak horizontal gradient of the scalar field `f`:
`f` and every coordinate of `Df` are integrable, and for every horizontally smooth test `F`
and every L²(Q) derivative `G = D_i F` one has `∫ f G = -∫ (Df)_i F`. The tested products are
integrable because tests and their first derivatives are Q-essentially bounded. -/
def HasWeakHorizontalGradient {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (f : FieldPair d → ℝ) (Df : FieldPair d → Vec d) : Prop :=
  Integrable f Q ∧ (∀ i : Fin d, Integrable (fun ω => Df ω i) Q) ∧
    ∀ (i : Fin d) (F G : Lp ℝ 2 Q), IsHorizontallySmoothTest Q hQ F →
      HasHorizontalLpDerivative Q hQ i F G →
        (∫ ω, f ω * G ω ∂Q) = -(∫ ω, Df ω i * F ω ∂Q)

/-- Source main.tex:245–249. `h` is the weak horizontal divergence of the vector field `V`:
`V` and `h` are integrable, and for every horizontally smooth test `F` and every family
`DF i = D_i F` in L²(Q), `∫ V·DF = -∫ h F`. The tested products are integrable because tests
and their first derivatives are Q-essentially bounded. -/
def HasWeakHorizontalDivergence {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (V : FieldPair d → Vec d) (h : FieldPair d → ℝ) : Prop :=
  (∀ i : Fin d, Integrable (fun ω => V ω i) Q) ∧ Integrable h Q ∧
    ∀ (F : Lp ℝ 2 Q), IsHorizontallySmoothTest Q hQ F →
      ∀ DF : Fin d → Lp ℝ 2 Q, (∀ i : Fin d, HasHorizontalLpDerivative Q hQ i F (DF i)) →
        (∫ ω, (∑ i : Fin d, V ω i * DF i ω) ∂Q) = -(∫ ω, h ω * F ω ∂Q)

/-- Source main.tex:209–213, 237 and 245. Weak form of the reduced generator equation
`L^λ f = h + D·G`, where `L^λ f = (1/2) D·(a Df) + λ (a e_{i₁})·Df` and `a = ω.1 0` is the
reduced coefficient at the origin of the canonical pair. `Df` is the weak horizontal gradient of
`f` (`HasWeakHorizontalGradient`). The function `h` and every coordinate of `G` must be
Q-integrable. Otherwise the Bochner integrals in the identity would be `0` by convention for a
non-integrable integrand, and the identity could hold spuriously. The identity is tested against
every horizontally smooth `F` and every family `DF i = D_i F` in L²(Q). -/
def SatisfiesReducedGeneratorEquation {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (lam : ℝ) (f : FieldPair d → ℝ) (Df : FieldPair d → Vec d) (h : FieldPair d → ℝ)
    (G : FieldPair d → Vec d) (i₁ : Fin d) : Prop :=
  HasWeakHorizontalGradient Q hQ f Df ∧ Integrable h Q ∧
    (∀ i : Fin d, Integrable (fun ω => G ω i) Q) ∧
    ∀ (F : Lp ℝ 2 Q), IsHorizontallySmoothTest Q hQ F →
      ∀ DF : Fin d → Lp ℝ 2 Q, (∀ i : Fin d, HasHorizontalLpDerivative Q hQ i F (DF i)) →
        -(1 / 2 : ℝ) * (∫ ω, (∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j * Df ω j) ∂Q) +
            lam * (∫ ω, F ω * (∑ j : Fin d, (ω.1 0) j i₁ * Df ω j) ∂Q) =
          (∫ ω, h ω * F ω ∂Q) - (∫ ω, (∑ i : Fin d, G ω i * DF i ω) ∂Q)

end EinsteinRelation
