import EinsteinFull.External.Source.AKMNegativeSobolev
import EinsteinRelation.External.AKMEnergyDensitySources

open MeasureTheory

namespace EinsteinFull.External.Draft
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- DRAFT for graph leaf `external:AKM#4.126`: the unmollified `p = 2`
estimate following Theorem 4.24, printed pp.172–173, specialized to integer
orders `m > d/2`. Only the gradient and homogenized-centered flux occur;
the energy-density estimate requires mollification and is not asserted.
The constant depends on `d,K,m,s` and precedes the law, direction and scale.
The direction lies in the open Euclidean unit ball and `0 < ε < 1/2`.
Source spatial correctors and the variationally characterized homogenized
matrix are selected on the source law. A measurable real majorant expresses
the stochastic estimate for the extended negative norms. No Schwartz-test,
horizontal, physical, clock, or complex-force application is admitted. -/
def akmNegativeSobolevStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (K : ℝ), 1 < K →
    ∀ (m : ℕ), (d : ℝ) / 2 < m → ∀ s : ℝ, 0 < s → s < 2 →
      ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
        ∃ S : SourceObjects P, ∀ e : Vec d, euclideanNorm e < 1 →
        ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
          ∃ Z : Coefficient d K → ℝ, Measurable Z ∧
            OsBound P Z s (C * ε ^ ((d : ℝ) / 2)) ∧
            ∀ᵐ a ∂P,
              Source.AKM.vectorNegativeIntegerSobolevNorm m (originBall d 1)
                (fun x => (S.corrector e).grad a (ε⁻¹ • x)) +
              Source.AKM.vectorNegativeIntegerSobolevNorm m (originBall d 1)
                (fun x => (a (ε⁻¹ • x)).mulVec
                  (e + (S.corrector e).grad a (ε⁻¹ • x)) - S.homogenized.mulVec e) ≤
              ENNReal.ofReal (Z a)

end EinsteinFull.External.Draft
