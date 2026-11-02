import EinsteinRelation.External.AKMLocalCorrectors

/-!
# Integer-order normalized negative Sobolev norms

The test norm is AKM (0.26) and Appendix B, Definition B.2: every spatial
multi-index occurs once. The negative norm is the normalized dual supremum
over actual smooth compactly supported tests, (0.29). It takes values in
`ℝ≥0∞`; an infinite supremum is never converted to a real number.

This extends the blueprint's two-dimensional `negativeH2Norm` carrier to
arbitrary integer orders and dimensions. It adds no analytic assumption.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section
namespace EinsteinFull.External.Source.AKM
open EinsteinRelation EinsteinRelation.External.AKM

/-- The actual iterated coordinate derivative of a smooth test, with each
coordinate repeated its multi-index multiplicity. The order is fixed by the
increasing coordinate list; mixed derivatives commute on the smooth tests
used in the dual norm. -/
def multiIndexDerivative {d m : ℕ} (β : Fin d → Fin (m + 1))
    (ψ : Vec d → ℝ) : Vec d → ℝ :=
  ((List.finRange d).flatMap fun j => List.replicate (β j).val j).foldr
    coordinateDerivative ψ

/-- AKM's normalized `H^m(U)` test norm, (0.26) and (B.1).
The finite type indexes every multi-index with entries at most `m`; the
filter retains precisely total orders at most `m`. Each normalized scalar
L² norm has the source factor `|U|^((|β|-m)/d)`. -/
def integerSobolevTestNorm {d : ℕ} (m : ℕ) (U : Set (Vec d))
    (ψ : Vec d → ℝ) : ℝ :=
  ∑ β : Fin d → Fin (m + 1),
    if (∑ j : Fin d, (β j).val) ≤ m then
      (volume U).toReal ^ ((((∑ j : Fin d, (β j).val : ℕ) : ℝ) - m) / d) *
        scalarRms volume U (multiIndexDerivative β ψ)
    else 0

/-- The normalized scalar negative `H^m(U)` norm, defined by (0.29).
Absolute values give the source supremum because the test ball is symmetric.
No measurability or finiteness of a supremum is built into this definition. -/
def negativeIntegerSobolevNorm {d : ℕ} (m : ℕ) (U : Set (Vec d))
    (f : Vec d → ℝ) : ℝ≥0∞ :=
  ⨆ ψ : {ψ : Vec d → ℝ //
      IsSpatialTest U ψ ∧ integerSobolevTestNorm m U ψ ≤ 1},
    ENNReal.ofReal |⨍ x in U, f x * ψ.1 x ∂volume|

/-- Component sum of the scalar negative norms. This is equivalent to the
source vector norm up to a factor depending only on the dimension, absorbed
in the unspecified structural constant of (4.126). -/
def vectorNegativeIntegerSobolevNorm {d : ℕ} (m : ℕ) (U : Set (Vec d))
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  ∑ j : Fin d, negativeIntegerSobolevNorm m U (fun x => F x j)

end EinsteinFull.External.Source.AKM
