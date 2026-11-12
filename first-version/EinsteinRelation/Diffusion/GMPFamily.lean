import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Environment.Basic
import EinsteinRelation.Environment.Reduction
import EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinRelation.External.GantertSection7Support

/-! # Diffusion families bound to the GMP Section 7 realization

The physical and reduced diffusion families are tied to fixed-environment realizations of
the heat-kernel construction of Gantert, Mathieu and Piatnitski (2012), Section 7 (p. 32).
Its Dirichlet form is equation (7.1) on p. 32, and Lemma 7.1 identifies that form on p. 33.
The reduced family runs on the zero-potential pair `(exp(-2V) a₀, 0)`. GMP state that the
reduced operators have the physical form with `V` replaced by `0` and `a₀` replaced by
`exp(-2V) a₀` (equations (3.8)-(3.9), p. 10).
-/

open MeasureTheory
open EinsteinRelation.External.GantertSection7Support (GantertFixedEnvironmentRealization)

namespace EinsteinRelation

/-- The zero-potential reduced pair `(a, 0)` with `a = exp(-2V) a₀`, the coefficient pair
of the reduced operators in GMP 2012, equations (3.8)-(3.9), p. 10. The coefficient is the
continuous reduced coefficient carried by `reduce`. -/
noncomputable def zeroPotentialReducedPair {d : ℕ} (ω : FieldPair d) : FieldPair d :=
  ((reduce ω).1, ⟨fun _ => 0, continuous_const⟩)

@[simp] theorem zeroPotentialReducedPair_coefficient {d : ℕ} (ω : FieldPair d) (x : Vec d) :
    (zeroPotentialReducedPair ω).1 x = reducedCoefficient ω x := rfl

@[simp] theorem zeroPotentialReducedPair_potential {d : ℕ} (ω : FieldPair d) (x : Vec d) :
    (zeroPotentialReducedPair ω).2 x = 0 := rfl

/-- The zero-potential pair keeps the reduced coefficient of `ω`, because its clock
density `exp(-2 · 0)` equals one. -/
theorem reducedCoefficient_zeroPotentialReducedPair {d : ℕ} (ω : FieldPair d) (x : Vec d) :
    reducedCoefficient (zeroPotentialReducedPair ω) x = reducedCoefficient ω x := by
  show Real.exp (-2 * (0 : ℝ)) • reducedCoefficient ω x = reducedCoefficient ω x
  rw [mul_zero, Real.exp_zero, one_smul]

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

private theorem euclideanNorm_nonneg' {d : ℕ} (x : Vec d) : 0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

/-- The zero-potential reduced pair is regular at the source reduced bound. Ellipticity and
the operator Lipschitz bound are inherited from `sourceReducedBound_support`, since the bound
dominates `exp(2Λ₀)(Λ₀ + 2Λ₀²)`; the zero potential satisfies the potential bounds trivially. -/
theorem isRegular_zeroPotentialReducedPair {d : ℕ} {Λ₀ : ℝ} (hΛ : 1 ≤ Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) :
    IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω) := by
  obtain ⟨hK, hell, _, hlip, _, hsum⟩ := sourceReducedBound_support hΛ hω
  have hK0 : 0 ≤ sourceReducedBound Λ₀ := by linarith
  have hexp : 0 ≤ Real.exp (2 * Λ₀) * (2 * Λ₀) :=
    mul_nonneg (Real.exp_pos _).le (by linarith)
  have hle : Real.exp (2 * Λ₀) * (Λ₀ + 2 * Λ₀ ^ 2) ≤ sourceReducedBound Λ₀ := by
    linarith
  unfold IsRegular
  refine ⟨hell, ?_, ?_, ?_⟩
  · intro x
    simp only [zeroPotentialReducedPair_potential, abs_zero]
    exact hK0
  · intro x y ξ
    show euclideanNorm ((reducedCoefficient ω x - reducedCoefficient ω y).mulVec ξ) ≤
      sourceReducedBound Λ₀ * euclideanNorm (x - y) * euclideanNorm ξ
    exact (hlip x y ξ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (euclideanNorm_nonneg' _))
        (euclideanNorm_nonneg' _))
  · intro x y
    simp only [zeroPotentialReducedPair_potential, sub_self, abs_zero]
    exact mul_nonneg hK0 (euclideanNorm_nonneg' _)

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

/-- The physical origin law of one force `λ ∈ [0, 1]`, the kernel-level form of the physical
family condition (GMP 2012, Section 7, p. 32). For almost every environment `ω`, the kernel
`K` at `ω` equals the origin path law of a fixed-environment realization of the physical pair
`ω = (a₀, V)`. -/
def IsGMPPhysicalOriginLaw {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (K : ProbabilityTheory.Kernel (FieldPair d) (Path d)) : Prop :=
  ∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular Λ₀ ω,
    ∃ r : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam h0 h1,
      K ω = r.pathLaw 0

/-- The reduced origin law of one force `λ ∈ [0, 1]` (GMP 2012, Section 7, p. 32;
equations (3.8)-(3.9), p. 10). For almost every environment `ω`, the kernel `K` at `ω` equals
the origin path law of a fixed-environment realization of the zero-potential pair
`(exp(-2V) a₀, 0)`, which is regular at the source reduced bound. -/
def IsGMPReducedOriginLaw {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (K : ProbabilityTheory.Kernel (FieldPair d) (Path d)) : Prop :=
  ∀ᵐ ω ∂Q.measure, ∃ hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω),
    ∃ r : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
        (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω' lam h0 h1,
      K ω = r.pathLaw 0

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

/-- The physical diffusion family is the family of physical origin laws of its members, one
force at a time. The identification `originLaw (P lam) ω = P lam (0, ω)` holds by definition. -/
theorem isGMPPhysicalFamily_iff {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d) :
    IsGMPPhysicalFamily hd hΛ₀ Q P ↔
      ∀ (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1),
        IsGMPPhysicalOriginLaw hd hΛ₀ Q lam h0 h1 (originLaw (P lam)) :=
  Iff.rfl

/-- The reduced diffusion family is the family of reduced origin laws of its members, one force
at a time (GMP 2012, Section 7, p. 32; equations (3.8)-(3.9), p. 10). The identification
`originLaw (P lam) ω = P lam (0, ω)` holds by definition. -/
theorem isGMPReducedFamily_iff {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d) :
    IsGMPReducedFamily hd hΛ₀ Q P ↔
      ∀ (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1),
        IsGMPReducedOriginLaw hd hΛ₀ Q lam h0 h1 (originLaw (P lam)) :=
  Iff.rfl

end EinsteinRelation
