import EinsteinRelationAudit.MobilityRate.Vocabulary.Diffusion.Basic
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.Basic
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.Reduction
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.SourceReducedBoundSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.GantertSection7Support

/-! Restated from the library module `EinsteinRelation.Diffusion.GMPFamily`:
the declarations of that module that the statement of
`EinsteinRelationAudit.MobilityRate.mobility_rate` depends on, in their module context. -/

open MeasureTheory
open EinsteinRelation.External.GantertSection7Support (GantertFixedEnvironmentRealization)
namespace EinsteinRelation
/-- The zero-potential reduced pair `(a, 0)` with `a = exp(-2V) a₀`, the coefficient pair
of the reduced operators in GMP 2012, equations (3.8)-(3.9), p. 10. The coefficient is the
continuous reduced coefficient carried by `reduce`. -/
noncomputable def zeroPotentialReducedPair {d : ℕ} (ω : FieldPair d) : FieldPair d :=
  ((reduce ω).1, ⟨fun _ => 0, continuous_const⟩)
theorem one_le_sourceReducedBound {Λ₀ : ℝ} (hΛ : 1 ≤ Λ₀) : 1 ≤ sourceReducedBound Λ₀ := by
  have he : 1 ≤ Real.exp (2 * Λ₀) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hp : 1 ≤ 3 * Λ₀ ^ 2 + Λ₀ + 1 := by
    nlinarith [sq_nonneg Λ₀, hΛ]
  show 1 ≤ Real.exp (2 * Λ₀) * (3 * Λ₀ ^ 2 + Λ₀ + 1)
  calc
    (1 : ℝ) = 1 * 1 := by ring
    _ ≤ Real.exp (2 * Λ₀) * (3 * Λ₀ ^ 2 + Λ₀ + 1) :=
      mul_le_mul he hp (by norm_num) (Real.exp_pos _).le
/-- The physical diffusion family `X^λ` is the GMP Section 7 family (GMP 2012, Section 7,
p. 32). For every force `λ ∈ [0, 1]` and almost every environment `ω`, the origin path
law of `P λ` is the origin path law of a fixed-environment realization of the physical
pair `ω = (a₀, V)`. -/
def IsGMPPhysicalFamily {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d) : Prop :=
  ∀ (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1), ∀ᵐ ω ∂Q.measure,
    ∃ hω : IsRegular Λ₀ ω,
      ∃ r : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam h0 h1,
        P lam (0, ω) = r.pathLaw 0
/-- The reduced diffusion family `Y^λ` is the GMP Section 7 family on the zero-potential pair
(GMP 2012, Section 7, p. 32; equations (3.8)-(3.9), p. 10). For every force `λ ∈ [0, 1]`
and almost every environment `ω`, the zero-potential pair is regular at the source reduced
bound (by `isRegular_zeroPotentialReducedPair`), and the origin path law of `P λ` is the
origin path law of a fixed-environment realization of that pair. -/
def IsGMPReducedFamily {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d) : Prop :=
  ∀ (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1), ∀ᵐ ω ∂Q.measure,
    ∃ hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω),
      ∃ r : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
          (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω' lam h0 h1,
        P lam (0, ω) = r.pathLaw 0
/-- The reduced quenched kernel of one force `λ ∈ [0, 1]` (GMP 2012, Section 7, p. 32;
equations (3.8)-(3.9), p. 10). For almost every environment `ω`, the zero-potential pair is
realized by a fixed-environment realization whose path law from every spatial starting point
`x` is `P (x, ω)`. The identification holds for all starting points at once. -/
def IsGMPReducedKernel {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) : Prop :=
  ∀ᵐ ω ∂Q.measure, ∃ hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω),
    ∃ r : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
        (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω' lam h0 h1,
      ∀ x : Vec d, P (x, ω) = r.pathLaw x
end EinsteinRelation
