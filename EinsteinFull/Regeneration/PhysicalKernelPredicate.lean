import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Environment.SourceReducedBoundSupport

/-!
# The physical quenched kernel predicate

The physical diffusion of Gantert–Mathieu–Piatnitski (2012), Section 7 (p. 32), runs on the
pair `ω = (a₀, V)` itself. A quenched path kernel is the physical kernel when, for almost every
environment, it is the path law of a Section 7 realization of `ω` from every starting point.
Regularity is monotone in the bound and a realization does not depend on the bound, so the
physical kernel is also the physical kernel at the larger bound `sourceReducedBound Λ₀` used for
the reduced kernel.
-/

open MeasureTheory EinsteinRelation
open EinsteinRelation.External.GantertSection7Support

namespace EinsteinFull.Regeneration

/-- The physical quenched kernel of one force `λ ∈ [0, 1]` (GMP 2012, Section 7, p. 32). For
almost every environment `ω`, the kernel equals the path law of a fixed-environment realization
of the physical pair `ω = (a₀, V)` from every spatial starting point. -/
def IsGMPPhysicalKernel {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) : Prop :=
  ∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular Λ₀ ω,
    ∃ r : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam h0 h1,
      ∀ x : Vec d, P (x, ω) = r.pathLaw x

/-- The bound of the reduced coefficients dominates the physical bound. -/
theorem le_sourceReducedBound {L : ℝ} (hL : 1 ≤ L) : L ≤ sourceReducedBound L := by
  have he : 1 ≤ Real.exp (2 * L) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hp : L ≤ 3 * L ^ 2 + L + 1 := by nlinarith
  calc L ≤ 3 * L ^ 2 + L + 1 := hp
    _ = 1 * (3 * L ^ 2 + L + 1) := (one_mul _).symm
    _ ≤ Real.exp (2 * L) * (3 * L ^ 2 + L + 1) :=
      mul_le_mul_of_nonneg_right he (by nlinarith)

/-- Regularity is monotone in the bound. -/
theorem isRegular_mono {d : ℕ} {L M : ℝ} {ω : FieldPair d} (hL : 0 < L) (hLM : L ≤ M)
    (hω : IsRegular L ω) : IsRegular M ω := by
  rcases hω with ⟨hell, hpot, hlip, hpotlip⟩
  refine ⟨?_, fun x => (hpot x).trans hLM, ?_, ?_⟩
  · intro x
    refine ⟨(hell x).1, fun v => ⟨?_, ?_⟩⟩
    · have hv : 0 ≤ euclideanSq v := by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)
      exact (mul_le_mul_of_nonneg_right (inv_anti₀ hL hLM) hv).trans ((hell x).2 v).1
    · have hv : 0 ≤ euclideanSq v := by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)
      exact ((hell x).2 v).2.trans (mul_le_mul_of_nonneg_right hLM hv)
  · intro x y v
    exact (hlip x y v).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hLM (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  · intro x y
    exact (hpotlip x y).trans (mul_le_mul_of_nonneg_right hLM (Real.sqrt_nonneg _))

/-- A regular physical pair is regular at the reduced bound. -/
theorem isRegular_sourceReducedBound_of_isRegular {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hL : 1 ≤ L) (hω : IsRegular L ω) : IsRegular (sourceReducedBound L) ω :=
  isRegular_mono (lt_of_lt_of_le zero_lt_one hL) (le_sourceReducedBound hL) hω

/-- A fixed-environment realization, read at another bound of the same pair. -/
def realizationRebound {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1) (M : ℝ) (hM : 1 ≤ M)
    (hωM : IsRegular M ω) : GantertFixedEnvironmentRealization hd M hM ω hωM lam h0 h1 :=
  { r with }

/-- The physical quenched kernel read at the reduced bound: for almost every environment `ω`,
the kernel equals the path law of a fixed-environment realization of the physical pair `ω`,
regular at the bound `sourceReducedBound Λ₀`, from every spatial starting point. -/
def IsGMPPhysicalKernelReducedBound {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) : Prop :=
  ∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular (sourceReducedBound Λ₀) ω,
    ∃ r : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
        (one_le_sourceReducedBound hΛ₀) ω hω lam h0 h1,
      ∀ x : Vec d, P (x, ω) = r.pathLaw x

/-- The physical kernel is the physical kernel at the reduced bound. -/
theorem IsGMPPhysicalKernel.reducedBound {d : ℕ} {hd : 2 ≤ d} {Λ₀ r₀ : ℝ} {hΛ₀ : 1 ≤ Λ₀}
    {Q : EnvironmentLaw d Λ₀ r₀} {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    {P : QuenchedPathLaws d} (hP : IsGMPPhysicalKernel hd hΛ₀ Q lam h0 h1 P) :
    IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P := by
  filter_upwards [hP] with ω hω
  obtain ⟨hreg, r, hr⟩ := hω
  have hreg' := isRegular_sourceReducedBound_of_isRegular hΛ₀ hreg
  exact ⟨hreg', realizationRebound r _ (one_le_sourceReducedBound hΛ₀) hreg', hr⟩

end EinsteinFull.Regeneration
