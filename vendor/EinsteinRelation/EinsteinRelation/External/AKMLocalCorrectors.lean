import EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinRelation.Calculus.Weak
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # AKM inputs for local correctors

Source: Armstrong--Kuusi--Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity* (2019), `paper/References/AKM.pdf`, SHA-256
`fb5da48f60f1a23eb57b82088fd3ede9a45fe2baa1748c84b01cca2262643d65`.
The applications are `paper/main.tex:779–800,850–858,938–945`.

These propositions use the book's coefficient space, test-integral sigma
algebras, lower ellipticity one, lattice stationarity and unit dependence
range. They are statements of literature inputs, not axioms or proofs of
those inputs. In particular, none asserts an estimate for the project's
canonical corrector without identifying that corrector with the source object.
All spatial norms below use the Euclidean quadratic form, not the function
space's default supremum norm. Space and time averages are volume normalized.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.External.AKM

open Environment.AKMTestIntegralSupport

/-- Standing hypotheses (0.6)--(0.11), pp. xvii--xviii. Symmetry and
`|ξ|² ≤ ξ·aξ ≤ K|ξ|²` are in `Coefficient`; the sigma algebras observe test
integrals, not point evaluations. Dimension and `K > 1` are quantified in
the individual inputs. -/
def IsAdmissibleLaw {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K)) : Prop :=
  IsProbabilityMeasure P ∧
    (∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P) ∧
    AKMFiniteRange P

/-- The convention `X ≤ O_s(θ)` in (0.41)--(0.42), p. xxxvii: the positive
part is inside the exponential. Positivity of `s` and `θ` is imposed at uses. -/
def StretchedExponentialBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s θ : ℝ) (X : Ω → ℝ) : Prop :=
  (∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s)) ∂P) ≤ 2

/-- The Euclidean ball at the origin used in the cited estimates. -/
def originBall (d : ℕ) (R : ℝ) : Set (Vec d) := {x | euclideanNorm x < R}

/-- AKM's backward cylinder `Q_R = (-R²,0] × B_R`, p. 303. -/
def cylinder (d : ℕ) (R : ℝ) : Set (ℝ × Vec d) :=
  Set.Ioc (-(R ^ 2)) 0 ×ˢ originBall d R

/-- The volume-normalized scalar `L²` norm. -/
noncomputable def scalarRms {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (U : Set X) (f : X → ℝ) : ℝ :=
  Real.sqrt (⨍ x in U, (f x) ^ 2 ∂ν)

/-- The volume-normalized Euclidean `L²` norm of a vector field. -/
noncomputable def vectorRms {d : ℕ} {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (U : Set X) (G : X → Vec d) : ℝ :=
  Real.sqrt (⨍ x in U, euclideanSq (G x) ∂ν)

/-- A scalar `H¹(B_R)` solution of (3.16), p. 75, with its actual weak
gradient `G`. All local integrability in the weak equation is explicit. -/
def IsHarmonic {d : ℕ} {K : ℝ} (A : Coefficient d K) (R : ℝ)
    (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  MemLp u 2 (volume.restrict (originBall d R)) ∧
    MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict (originBall d R)) ∧
    HasWeakGradient (originBall d R) u G ∧
    HasWeakDivergence (originBall d R) (fun x => (A x).mulVec (G x)) (fun _ => 0)

/-- Energy-class weak solutions of (8.23), in the equivalent distributional
form of (8.2) and (8.6), pp. 302--303. The equation identifies the time
derivative as `div(aG) ∈ L²(I;H⁻¹(U))`; no time derivative of a merely
measurable representative is used. Tests avoid both temporal endpoints. -/
def IsParabolicSolution {d : ℕ} {K : ℝ} (A : Coefficient d K)
    (I : Set ℝ) (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) : Prop :=
  MemLp u 2 (volume.restrict (I ×ˢ U)) ∧
    AEStronglyMeasurable G (volume.restrict (I ×ˢ U)) ∧
    MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (I ×ˢ U)) ∧
    (∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => u (t, x)) (fun x => G (t, x))) ∧
    ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ interior I ×ˢ U →
      (∫ z in I ×ˢ U,
        -(u z) * fderiv ℝ ψ z (1, 0) +
          dot ((A z.2).mulVec (G z))
            (fun j => fderiv ℝ ψ z (0, unitVector j))) = 0

/-- Theorem 3.3, (3.15)--(3.19), p. 75. One random scale works for every
radius and every weak solution. The three conclusions are the oscillation,
value and gradient estimates. The source allows `X_s = ∞` on a null set;
the real-valued version here modifies that null set, since (3.15) forces
almost sure finiteness. The constant is chosen before the law. -/
def EllipticLargeScale : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (K s : ℝ), 1 < K → 0 < s → s < d →
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
      ∃ X : Coefficient d K → ℝ, Measurable X ∧
        (∀ A, 1 ≤ X A) ∧ StretchedExponentialBound P s C X ∧
        ∀ᵐ A ∂P, ∀ R : ℝ, X A ≤ R →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d), IsHarmonic A R u G →
            ∀ r : ℝ, X A ≤ r → r ≤ R →
              scalarRms volume (originBall d r) (fun x => u x - ⨍ y in originBall d r, u y) / r ≤
                C * scalarRms volume (originBall d R)
                  (fun x => u x - ⨍ y in originBall d R, u y) / R ∧
              scalarRms volume (originBall d r) u ≤ C * scalarRms volume (originBall d R) u ∧
              vectorRms volume (originBall d r) G ≤ C * vectorRms volume (originBall d R) G

/-- Remark 8.8, (8.25), p. 315: the time-slice gradient estimate.
The estimate is stated for almost every time, which is the
representative-independent consequence of the printed supremum. Applying it
at a specified time requires the actual flow's time regularity. -/
def ParabolicLargeScale : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (K s : ℝ), 1 < K → 0 < s → s < d →
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
      ∃ X : Coefficient d K → ℝ, Measurable X ∧
        (∀ A, 1 ≤ X A) ∧ StretchedExponentialBound P s C X ∧
        ∀ᵐ A ∂P, ∀ R : ℝ, X A ≤ R →
          ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
            IsParabolicSolution A (Set.Ioc (-(R ^ 2)) 0) (originBall d R) u G →
            ∀ r : ℝ, X A ≤ r → r ≤ R / 2 →
              ∀ᵐ t ∂volume.restrict (Set.Ioo (-(r ^ 2) / 4) 0),
                vectorRms volume (originBall d (r / 2)) (fun x => G (t, x)) ≤
                  C * vectorRms volume (cylinder d R) G

/-- Definition 3.14, pp. 98--99. Covariance is almost everywhere in space
and law for each lattice translation; the field is jointly measurable. -/
def IsStationaryField {d : ℕ} {K : ℝ} {E : Type*} [MeasurableSpace E]
    (P : Measure (Coefficient d K)) (F : Coefficient d K → Vec d → E) : Prop :=
  Measurable (fun z : Coefficient d K × Vec d => F z.1 z.2) ∧
    ∀ z : LatticeIndex d, ∀ᵐ A ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      F A (x + latticeShift z) = F (translateCoefficient (latticeShift z) A) x

/-- The local equation and initial datum of (9.1), pp. 347--349.
The equation holds in every positive-time bounded cylinder, the initial
condition is `u(0)=div g` in distributions, and positive-time values use a
continuous representative. This predicate alone does not select the source
flow (9.2). Its construction, growth bound and identification with an
independently constructed solution are internal obligations. -/
def IsSemigroupSolution {d : ℕ} {K : ℝ} (A : Coefficient d K)
    (g : Vec d → Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) : Prop :=
  ContinuousOn u (Set.Ioi 0 ×ˢ Set.univ) ∧
    (∀ (a b R : ℝ), 0 < a → a < b → 0 < R →
      IsParabolicSolution A (Set.Ioo a b) (originBall d R) u G) ∧
    ∀ ψ : Vec d → ℝ, IsSpatialTest Set.univ ψ →
      Tendsto (fun t => ∫ x, u (t, x) * ψ x ∂volume)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (-(∫ x, dot (g x) (gradient ψ x) ∂volume)))

/-- Theorem 9.1, (9.7), p. 349: decay for a general bounded local stationary
vector field, not only for coefficient columns. `g(x)` is measurable for the
test-integral sigma algebra of `B₁(x)`, as in the printed theorem. The bound
on `g` is the essential Euclidean supremum. The stochastic conclusion is the
book's stretched-exponential estimate, before taking any finite moments.
The PDE is scalar, as explicitly required on p. 349. The conclusion is
existential: (9.2) supplies this flow. It does not assert decay for every
solution of the initial-value problem or assume a derived growth bound.
Identifying a separately constructed flow remains an internal obligation. -/
def ParabolicSemigroupDecay : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (K s : ℝ), 1 < K → 0 < s → s < 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
      ∀ g : Coefficient d K → Vec d → Vec d, IsStationaryField P g →
        (∀ᵐ A ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)), euclideanNorm (g A x) ≤ 1) →
        (∀ x : Vec d, Measurable[Environment.AKMTestIntegralSupport.localSigma
            {y | euclideanNorm (y - x) < 1}]
          (fun A => g A x)) →
        ∃ (u : Coefficient d K → ℝ × Vec d → ℝ)
          (G : Coefficient d K → ℝ × Vec d → Vec d),
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) ∧
          (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) ∧
          ∀ (t : ℝ), 1 ≤ t → ∀ x : Vec d,
            StretchedExponentialBound P s (C * t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4))
              (fun A => |u A (t, x)|)

/-- A first-order corrector in the sense of Section 3.4, pp. 98--100:
`φ` is an almost surely sublinear `H¹_loc` potential, `G` is its stationary
gradient, and `e·x+φ` is a-harmonic. Zero expected unit-cell gradient
and finite expected unit-cell energy are derived properties (Lemma 3.17),
not premises in this source characterization. They must be proved internally
when identifying the canonical gradient. There is no additive normalization
or quantitative corrector estimate in the predicate. -/
def IsFirstOrderCorrector {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K))
    (e : Vec d) (φ : Coefficient d K → Vec d → ℝ)
    (G : Coefficient d K → Vec d → Vec d) : Prop :=
  IsStationaryField P G ∧
    (∀ᵐ A ∂P,
      (∀ R : ℝ, 0 < R →
        MemLp (φ A) 2 (volume.restrict (originBall d R)) ∧
        MemLp (fun x => euclideanNorm (G A x)) 2 (volume.restrict (originBall d R))) ∧
      HasWeakGradient Set.univ (φ A) (G A) ∧
      HasWeakDivergence Set.univ (fun x => (A x).mulVec (e + G A x)) (fun _ => 0) ∧
      Tendsto (fun R => scalarRms volume (originBall d R) (φ A) / R) atTop (nhds 0))

/-- `ā e = E[∫_[0,1]^d a(e+∇φ_e)]`, the unit-cell mean flux convention
for a lattice-stationary law. It does not replace this average by a value
at the origin. -/
noncomputable def firstOrderMeanFlux {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K))
    (e : Vec d) (G : Coefficient d K → Vec d → Vec d) : Vec d :=
  fun j => ∫ A, (∫ x in Set.Icc (0 : Vec d) 1,
    ((A x).mulVec (e + G A x)) j ∂volume) ∂P

/-- A component-sum version of the normalized `H²(U)` norm of a smooth scalar
test, using (0.26) and
Appendix B, (B.1), p. 465. The second derivatives are summed once for each
multi-index: `j ≤ k` avoids counting a mixed derivative twice. The `L²`
terms are normalized averages, with factors `|U|^((j-2)/d)`. Summing the
component norms instead of taking their Euclidean sum is equivalent up to a
dimension-dependent constant; the resulting negative norm is no larger than
the source norm. -/
noncomputable def h2TestNorm {d : ℕ} (U : Set (Vec d)) (ψ : Vec d → ℝ) : ℝ :=
  (volume U).toReal ^ (-(2 : ℝ) / d) * scalarRms volume U ψ +
    (volume U).toReal ^ (-(1 : ℝ) / d) *
      ∑ j : Fin d, scalarRms volume U (coordinateDerivative j ψ) +
    ∑ j : Fin d, ∑ k ∈ Finset.univ.filter (j ≤ ·),
      scalarRms volume U (coordinateDerivative k (coordinateDerivative j ψ))

/-- The normalized negative `H²` norm, defined by duality against actual
compactly supported smooth tests, (0.29), p. xxxiv, and (B.4), p. 467.
The supremum lives in `ℝ≥0∞`, so infinite dual norms cannot become zero.
Absolute values give the same supremum as the source's signed pairing by
the symmetry of the test unit ball. -/
noncomputable def negativeH2Norm {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ≥0∞ :=
  ⨆ ψ : {ψ : Vec d → ℝ // IsSpatialTest U ψ ∧ h2TestNorm U ψ ≤ 1},
    ENNReal.ofReal |⨍ x in U, f x * ψ.1 x ∂volume|

/-- Component-sum convention for the negative norm of a vector distribution.
It is equivalent, with constants depending only on dimension, to the
Euclidean vector dual norm in (4.126). Thus it only changes that estimate's
unspecified dimension-dependent constant. -/
noncomputable def vectorNegativeH2Norm {d : ℕ} (U : Set (Vec d))
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  ∑ j : Fin d, negativeH2Norm U (fun x => F x j)

/-- The case `d = 2`, `α = 2 > d/2` of (4.126), p. 173, the unsmoothed
consequence accompanying Theorem 4.24 (p. 172). This is the case used at
`paper/main.tex:938–945`. The source's other dimensions and Sobolev orders
are not included. Both the full gradient and centered flux occur, with one
shared stochastic bound. `Z` is a real measurable upper bound for their
sum of extended norms; this expresses the source's `O_s(Cε)` bound without
using the unsafe real conversion of a potentially infinite norm.
The slope is in the source's open unit ball. -/
def CorrectorWeakH2 : Prop :=
  ∀ (K s : ℝ), 1 < K → 0 < s → s < 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient 2 K), IsAdmissibleLaw P →
      ∀ (e : Vec 2), euclideanNorm e < 1 →
        ∀ (φ : Coefficient 2 K → Vec 2 → ℝ) (G : Coefficient 2 K → Vec 2 → Vec 2),
          IsFirstOrderCorrector P e φ G → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
            ∃ Z : Coefficient 2 K → ℝ, Measurable Z ∧
              StretchedExponentialBound P s (C * ε) Z ∧
              ∀ᵐ A ∂P,
                vectorNegativeH2Norm (originBall 2 1) (fun x => G A (ε⁻¹ • x)) +
                  vectorNegativeH2Norm (originBall 2 1) (fun x =>
                    (A (ε⁻¹ • x)).mulVec (e + G A (ε⁻¹ • x)) - firstOrderMeanFlux P e G) ≤
                  ENNReal.ofReal (Z A)

end EinsteinRelation.External.AKM
