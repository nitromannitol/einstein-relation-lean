import EinsteinFull.Work.W8.SharpnessConstructionSupport
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.HomogenizedCoefficient

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

/-- Graph node `sharp.example#replacement-pair`, `paper/main.tex:1565–1565`.
The physical replacement is the literal pair (a/a11,-log(a11)/2).
Its measurable representative, structural data and smooth joint environment
law are conclusions, as is equality of the actual signed reduced generators. -/
def node_sharp_u2E_example_u23_replacement_u2D_pairStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d)),
    External.IsWhiteNoiseLaw P →
    let first : Fin d := ⟨0, by omega⟩
    ∀ (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      Q.measure = P.map (EinsteinFull.Work.W8.physicalPair first) →
      ∃ (Dnew : StructuralData d) (F : FieldPair d → FieldPair d),
        Measurable F ∧
        (∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
          (F ω).1 x = (reducedCoefficient ω x first first)⁻¹ • reducedCoefficient ω x ∧
          (F ω).2 x = -(1 / 2 : ℝ) * Real.log (reducedCoefficient ω x first first) ∧
          0 < reducedCoefficient ω x first first ∧
          clockDensity (F ω) x = reducedCoefficient ω x first first ∧
          reducedCoefficient (F ω) x = reducedCoefficient ω x ∧
          ∀ (lam : ℝ) (f : Vec d → ℝ),
            reducedGenerator first (F ω) lam f x = reducedGenerator first ω lam f x) ∧
        ∃ Qnew : EnvironmentLaw d Dnew.ellipticity Dnew.dependenceRange,
          Qnew.measure = Q.measure.map F ∧ HasSmoothBounds Dnew Qnew

end EinsteinFull.Blueprint
