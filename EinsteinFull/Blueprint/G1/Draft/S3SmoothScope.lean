import EinsteinFull.Calculus.CLKMCouplingAction

/-!
Smooth-scope (V3) Section 3 contracts.

Each V3 contract is its V1 statement with the structural data `D` in place of `(Λ₀, r₀)` and the
law restricted by `HasSmoothBounds D Q` (Assumption 1.2), as in the D1 smooth-scope contracts.
The name V2 of `rt:remainder-moment` is taken by the SI-13 quantifier repair (`RemainderMomentV2`).
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- DRAFT smooth-scope `rt:remainder-moment`. -/
def node_rt_u3A_remainder_u2D_momentStmtV3 : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B b : ℝ), 0 < B → 0 < b →
    ∃ l₀ p c C : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ,
    Measurable F → Measurable G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (J : ℝ) (t : ℝ≥0) (A : Set (FieldPair d × Regeneration.CoupledSample d)),
    0 ≤ J → MeasurableSet A →
    Regeneration.annealedCoupledLaw Q.measure K A ≤
      ENNReal.ofReal (B * Real.exp (B * J - b * lam ^ 2 * (t : ℝ))) →
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      IntegrableOn (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) A μ ∧
      |∫ ωz in A, F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ| ≤
        C * Real.exp (C * J - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal

/-- V1 restricts to V3. -/
theorem node_rt_u3A_remainder_u2D_momentStmtV3_of_v1 (h : node_rt_u3A_remainder_u2D_momentStmt) :
    node_rt_u3A_remainder_u2D_momentStmtV3 := by
  intro d hd D B b hB hb
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, h⟩ :=
    h d hd D.ellipticity D.dependenceRange B b hB hb
  exact ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, fun Q _ => h Q⟩

/-- Smooth-scope `rt:remainder-moment` from regen-tails and real-semigroup V2: on smooth laws
the GMP reduced kernel acts as the forced environment evolution. -/
theorem node_rt_u3A_remainder_u2D_moment_of_depsV3
    (htail : node_app_u3A_regen_u2D_tailsStmt)
    (hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2) :
    node_rt_u3A_remainder_u2D_momentStmtV3 := by
  intro d hd D B b hB hb
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, h⟩ :=
    remainder_moment_of_actionAt htail d hd D.ellipticity D.dependenceRange B b hB hb
  exact ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, fun Q hQ =>
    h Q (gmpReducedKernelActionSmooth_of_real hreal d hd D Q hQ)⟩

end EinsteinFull.Blueprint
