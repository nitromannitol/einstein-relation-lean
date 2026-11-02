import EinsteinFull.External.Source.AKMSourceFluxCorrector

open MeasureTheory

namespace EinsteinFull.External.Draft
open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- V2 removes the derived annealed cell-flux integrability premise by using
`SourceCorrector` and its literal heat-selected flux-potential carrier.
DRAFT for `external:AKM#3.17-6.2`: the oscillation and local-gradient
conclusions of Lemma 3.17, (3.85)–(3.86), printed p.100, and the flux-potential
conclusion of Proposition 6.2, (6.13), pp.249–250. The source flux object is
selected by (6.7); its existence is stated in Lemma 6.1. Only the oscillation
part of (3.85) is retained, not its negative norms or energy defect.
The random radius has the (3.39) stretched-exponential bound, with its constant
allowed to depend on s. The deterministic exponent and bound precede s and the
law. Lattice stationarity, unit range, Euclidean norms, normalized spatial
averages and source spatial correctors are literal. No horizontal or smooth
pointwise transfer, clock field or complex force occurs in this proposition. -/
def akmSublinearCorrectorsStmtV2 : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ K : ℝ, 1 < K →
    ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
    ∀ s : ℝ, 0 < s → s < d → ∃ Cs : ℝ, 0 < Cs ∧
    ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
    ∀ e : Vec d, euclideanNorm e = 1 → ∀ φ : SourceCorrector P e,
      Nonempty (Source.AKM.SourceFluxCorrector φ) ∧
      ∀ S : Source.AKM.SourceFluxCorrector φ, ∃ X : Coefficient d K → ℝ,
        Measurable X ∧ OsBound P X s Cs ∧
        ∀ᵐ a ∂P, 1 ≤ X a ∧ ∀ r : ℝ, X a ≤ r →
          Real.sqrt (⨍ x in ball 0 r,
            |φ.potential a x - (⨍ y in ball 0 r, φ.potential a y)| ^ 2) +
          Real.sqrt (⨍ x in ball 0 r,
            frobeniusNorm (S.potential a x -
              (Matrix.of fun i j => ⨍ y in ball 0 r, S.potential a y i j)) ^ 2) ≤
                C * r ^ (1 - β * ((d : ℝ) - s)) ∧
          Real.sqrt (⨍ x in ball 0 r, euclideanSq (φ.grad a x)) ≤ C

end EinsteinFull.External.Draft
