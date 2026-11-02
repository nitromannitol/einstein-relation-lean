import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.CenteredComplexLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `l:forced-local#centered-source`, `paper/main.tex:679–687`.
The literal centered forward evolution has the Euclidean L2 gradient bound
with quadratic-force exponential growth (including the unforced bound at zero
force). Its actual coefficient-column mean is the centering source. On the
specified time window this source is controlled by the input at t/8; adding
its time primitive restores the full homogeneous generator equation. The
corrected orbit has the normalized local space-time L2 bound used next in the
paper. Joint representatives are conclusions, never regularity premises.
The square-root Volterra iteration and its Gamma denominators are proof
obligations, not extra assumptions. -/
def node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 2 ≤ p → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (ζ : ℂ)
      (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
    ∀ f : Lp ℂ 2 (reducedLaw Q),
      MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
    letI := reducedLaw_probability Q
    let u := fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))
    ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      (∀ r : ℝ, 0 < r →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (u r) (G r) ∧
        ‖G r‖ ≤ C / Real.sqrt r * Real.exp (C * ‖ζ‖ ^ 2 * r) * ‖f‖) ∧
      (let c := fun r : ℝ => ζ * (∫ ω,
          ∑ j : Fin d, (ω.1 0 j ⟨0, by omega⟩ : ℂ) * G r j ω ∂reducedLaw Q)
       ∀ t : ℝ, 0 < t →
        MemLp (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        IntegrableOn c (Icc (t / 4) t) ∧
        (∀ r ∈ Icc (t / 4) t,
          ‖c r‖ ≤ C * ‖ζ‖ / Real.sqrt t * Real.exp (C * ‖ζ‖ ^ 2 * t) *
            ‖u (t / 8)‖) ∧
        (let w := fun r : ℝ => u r +
            Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, c v)
         (∀ r : ℝ, 0 < r → ∃ V : Lp ℂ 2 (reducedLaw Q),
            HasDerivAt w V r ∧
            IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ (w r) V) ∧
         ∃ U : ℝ × FieldPair d → ℂ,
           StronglyMeasurable U ∧
           (∀ r : ℝ, (fun ω => U (r, ω)) =ᵐ[reducedLaw Q] w r) ∧
           ∀ (x : Vec d) (ρ : ℝ), 0 < ρ →
             let N := fun ω : FieldPair d => Real.sqrt
               (⨍ r in Icc (t / 4) t,
                 ⨍ y in {y : Vec d | euclideanNorm (y - x) < ρ},
                   ‖U (r, translate y ω)‖ ^ 2)
             MemLp N (ENNReal.ofReal p) (reducedLaw Q) ∧
             eLpNorm N (ENNReal.ofReal p) (reducedLaw Q) ≤
               ENNReal.ofReal (Cp * (1 + ‖ζ‖ * Real.sqrt t) *
                 Real.exp (Cp * ‖ζ‖ ^ 2 * t)) *
               eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)))

end EinsteinFull.Blueprint
