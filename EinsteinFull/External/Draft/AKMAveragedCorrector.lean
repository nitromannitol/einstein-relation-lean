import EinsteinRelation.External.AKMEnergyDensitySources
import EinsteinRelation.External.AKMCorrectorOscillation

open MeasureTheory

namespace EinsteinFull.External.Draft
open EinsteinRelation
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- DRAFT for graph leaf `external:AKM#4.1`: AKM Theorem 4.1,
printed pp. 124–125, (4.1)–(4.7). This retains the three real spatial Gaussian
averages used by the paper. The variance is `2 r²`, the energy has its factor
`1/2`, the direction lies in the open Euclidean unit ball, and `0 < s < 2`.
The homogenized matrix is characterized by the source Dirichlet-energy limit,
not by assuming a clock or horizontal flux identity. Source objects are
existentially selected on the source law. Identifying them with the frozen
horizontal corrector remains internal. The scalar-potential bounds distinguish dimensions strictly above two from
dimension two. Additive constants are canceled in the planar bounds; the
higher-dimensional stationary representative has mean zero in the unit cell.
This proposition is not an admitted literature axiom. -/
def akmAveragedCorrectorStmt : Prop :=
  (∀ (d : ℕ), 2 ≤ d → ∀ K s : ℝ, 1 < K → 0 < s → s < 2 →
    ∃ C : ℝ, 0 < C ∧
    ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
      ∃ S : SourceObjects P, ∀ e : Vec d, euclideanNorm e < 1 →
      ∀ (x : Vec d) (r : ℝ), 1 ≤ r →
        (∀ᵐ a ∂P,
          Integrable (fun y => heatKernel x r y • (S.corrector e).grad a y) volume ∧
          Integrable (fun y => heatKernel x r y •
            ((a y).mulVec (e + (S.corrector e).grad a y))) volume ∧
          Integrable (fun y => heatKernel x r y * ((1 / 2 : ℝ) *
            dot (e + (S.corrector e).grad a y)
              ((a y).mulVec (e + (S.corrector e).grad a y)))) volume) ∧
        OsBound P (fun a => euclideanNorm
          (∫ y, heatKernel x r y • (S.corrector e).grad a y))
          s (C * r ^ (-(d : ℝ) / 2)) ∧
        OsBound P (fun a => euclideanNorm
          ((∫ y, heatKernel x r y • ((a y).mulVec
            (e + (S.corrector e).grad a y))) - S.homogenized.mulVec e))
          s (C * r ^ (-(d : ℝ) / 2)) ∧
        OsBound P (fun a => |sourceEnergyAverage (S.corrector e) x r a -
          (1 / 2 : ℝ) * dot e (S.homogenized.mulVec e)|)
          s (C * r ^ (-(d : ℝ) / 2))) ∧
  (∀ (d : ℕ), 2 < d → ∀ K : ℝ, 1 < K →
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
    ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
    ∀ e : Vec d, euclideanNorm e < 1 → ∀ φ : SourceCorrector P e,
      ∃ ψ : SourceCorrector P e,
        Measurable (fun z : Coefficient d K × Vec d => ψ.potential z.1 z.2) ∧
        (∀ᵐ a ∂P, ψ.grad a =ᵐ[volume] φ.grad a) ∧
        ScalarStationary P ψ.potential ∧
        (∫ a, ⨍ x in unitCell d, ψ.potential a x ∂volume ∂P) = 0 ∧
        AEOsBound P (fun a => Real.sqrt
          (⨍ x in unitCell d, |ψ.potential a x| ^ 2 ∂volume)) (2 + δ) C) ∧
  (∀ K s : ℝ, 1 < K → 0 < s → s < 2 →
    ∃ C : ℝ, 0 < C ∧
    ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
    ∀ e : Vec 2, euclideanNorm e < 1 → ∀ φ : SourceCorrector P e,
    ∀ r R : ℝ, 2 ≤ r → r ≤ R → ∀ x y : Vec 2,
      AEOsBound P (fun a => Real.sqrt (⨍ z in ball 0 r,
        |φ.potential a z - scalarHeatAverage (φ.potential a) 0 r| ^ 2 ∂volume))
        s (C * Real.sqrt (Real.log r)) ∧
      AEOsBound P (fun a => |scalarHeatAverage (φ.potential a) x r -
        scalarHeatAverage (φ.potential a) y R|)
        s (C * Real.sqrt (Real.log (2 + (R + euclideanNorm (x - y)) / r))))

end EinsteinFull.External.Draft
