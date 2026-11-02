import EinsteinFull.Calculus.S4ReducedCoefficientSupport
import EinsteinRelation.Environment.Smooth
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth environments: the generator identity holds everywhere

For a smooth environment (`IsSmoothFieldPair ω`) every entry of the reduced coefficient is
differentiable at every point, so `reducedGenerator i ω lam f = svGenerator ã b f` everywhere
for `f ∈ C²`, with the drift `b = forcedDrift ã i lam`.  Hence the vendor martingale problem
for `reducedGenerator` is literally the textbook martingale problem, and the draft
well-posedness input gives existence and uniqueness from every start.
-/

open MeasureTheory
open scoped BigOperators NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The martingale problem only sees the generator on `C_c^∞`. -/
theorem solvesMartingaleProblem_congr {d : ℕ} {L L' : (Vec d → ℝ) → Vec d → ℝ}
    (h : ∀ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → L f = L' f)
    (x : Vec d) (P : Measure (Path d)) :
    SolvesMartingaleProblem L x P ↔ SolvesMartingaleProblem L' x P := by
  unfold SolvesMartingaleProblem
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun f => ?_
  refine imp_congr_right fun hf => imp_congr_right fun hc => ?_
  have e : compensatedTest L f = compensatedTest L' f := by
    funext t γ
    unfold compensatedTest
    rw [h f hf hc]
  rw [e, h f hf hc]

theorem contDiff_reducedCoefficient_entry {d : ℕ} {ω : FieldPair d}
    (hs : IsSmoothFieldPair ω) (k j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => reducedCoefficient ω z k j) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun z => Real.exp (-2 * ω.2 z)) := by
    first
      | exact (contDiff_const.mul hs.2).exp
      | exact (contDiff_const.fun_mul hs.2).exp
      | fun_prop
  have e : (fun z => reducedCoefficient ω z k j) =
      fun z => Real.exp (-2 * ω.2 z) * ω.1 z k j :=
    funext fun z => reducedCoefficient_apply ω z k j
  rw [e]
  first
    | exact hc.mul (hs.1 k j)
    | exact hc.fun_mul (hs.1 k j)
    | fun_prop

theorem differentiableAt_reducedCoefficient_entry {d : ℕ} {ω : FieldPair d}
    (hs : IsSmoothFieldPair ω) (k j : Fin d) (x : Vec d) :
    DifferentiableAt ℝ (fun z => reducedCoefficient ω z k j) x :=
  ((contDiff_reducedCoefficient_entry hs k j).differentiable (by simp)) x

/-- For a smooth environment the vendor reduced generator is the textbook second-order operator
at every point and for every `C²` test function. -/
theorem reducedGenerator_eq_svGenerator {d : ℕ} {ω : FieldPair d}
    (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Vec d) :
    reducedGenerator i ω lam f x =
      External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam) f x := by
  unfold reducedGenerator
  exact generator_eq_svGenerator_of_differentiableAt (reducedCoefficient ω) i lam hf
    (fun k j => differentiableAt_reducedCoefficient_entry hs k j x)

theorem reducedGenerator_solves_iff {d : ℕ} {ω : FieldPair d} (hs : IsSmoothFieldPair ω)
    (i : Fin d) (lam : ℝ) (x : Vec d) (P : Measure (Path d)) :
    SolvesMartingaleProblem (reducedGenerator i ω lam) x P ↔
      SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x P := by
  refine solvesMartingaleProblem_congr (fun f hf _ => ?_) x P
  funext y
  have h2 : ContDiff ℝ 2 f := by
    first
      | exact hf.of_le (by exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
      | exact hf.of_le (by simp)
      | exact hf.of_le (by norm_cast; exact le_top)
      | exact hf.of_le (WithTop.coe_le_coe.2 le_top)
  exact reducedGenerator_eq_svGenerator hs i lam h2 y

/-- Existence and uniqueness of the reduced martingale problem for a smooth regular
environment, from the draft textbook input. -/
theorem exists_unique_reduced_solution {d : ℕ} (hwp : External.Draft.svWellPosedStmt)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ) (x : Vec d) :
    ∃! P : Measure (Path d), SolvesMartingaleProblem (reducedGenerator i ω lam) x P :=
  (existsUnique_congr fun P => (reducedGenerator_solves_iff hs i lam x P).symm).1
    (exists_unique_clean_reduced_solution hwp hΛ hω i lam x)

end EinsteinFull
