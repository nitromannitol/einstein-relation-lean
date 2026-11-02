import EinsteinFull.Calculus.S4SolutionRelationSupport
import EinsteinFull.Calculus.FellerRegularSet
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The coefficient family of the reduced martingale problems over all environments

For a regular environment the family is `(reducedCoefficient ω, forcedDrift ...)`; off the regular
set it is `(1, 0)`.  Every member is well posed (draft textbook input), the family is bounded and
jointly measurable in `(ω, y)`; in particular the solution relation is measurable.
-/

open MeasureTheory Topology Filter
open scoped NNReal Classical

namespace EinsteinFull
open EinsteinRelation

/-- Diffusion matrix of the family. -/
noncomputable def famA {d : ℕ} (Λ : ℝ) (ω : FieldPair d) (y : Vec d) : Mat d :=
  if IsRegular Λ ω then reducedCoefficient ω y else 1

/-- Drift of the family. -/
noncomputable def famB {d : ℕ} (Λ : ℝ) (i : Fin d) (lam : ℝ) (ω : FieldPair d)
    (y : Vec d) : Vec d :=
  if IsRegular Λ ω then forcedDrift (reducedCoefficient ω) i lam y else 0

theorem continuous_reducedCoefficient_joint (d : ℕ) :
    Continuous fun p : FieldPair d × Vec d => reducedCoefficient p.1 p.2 := by
  have hexp : Continuous fun p : FieldPair d × Vec d => Real.exp (-2 * p.1.2 p.2) := by
    have h1 : Continuous fun p : FieldPair d × Vec d => p.1.2 p.2 :=
      ContinuousEval.continuous_eval.comp
        (((continuous_snd.comp continuous_fst).prodMk continuous_snd))
    exact Real.continuous_exp.comp (continuous_const.mul h1)
  have h2 : Continuous fun p : FieldPair d × Vec d => p.1.1 p.2 :=
    ContinuousEval.continuous_eval.comp
      (((continuous_fst.comp continuous_fst).prodMk continuous_snd))
  have e : (fun p : FieldPair d × Vec d => reducedCoefficient p.1 p.2) =
      fun p => Real.exp (-2 * p.1.2 p.2) • p.1.1 p.2 := by
    funext p
    rfl
  rw [e]
  exact hexp.smul h2

theorem measurable_famA {d : ℕ} (Λ : ℝ) (i j : Fin d) :
    Measurable fun p : FieldPair d × Vec d => famA Λ p.1 p.2 i j := by
  have hS : MeasurableSet {p : FieldPair d × Vec d | IsRegular Λ p.1} :=
    (Calculus.Feller.measurableSet_setOf_isRegular d Λ).preimage measurable_fst
  have e : (fun p : FieldPair d × Vec d => famA Λ p.1 p.2 i j) = fun p =>
      if IsRegular Λ p.1 then reducedCoefficient p.1 p.2 i j else (1 : Mat d) i j := by
    funext p
    unfold famA
    split_ifs <;> rfl
  rw [e]
  refine Measurable.ite hS ?_ measurable_const
  exact ((continuous_reducedCoefficient_joint d).matrix_elem i j).measurable

theorem forcedDrift_reduced_eq {d : ℕ} (ω : FieldPair d) (i : Fin d) (lam : ℝ) (y : Vec d)
    (k : Fin d) :
    forcedDrift (reducedCoefficient ω) i lam y k =
      (1 / 2 : ℝ) * ∑ l, fderiv ℝ (fun z => reducedCoefficient ω z l k) y (unitVector l) +
        lam * reducedCoefficient ω y k i := by
  simp only [forcedDrift, matrixDivDrift, coordinateDerivative]
  congr 2
  simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]

theorem measurable_famB {d : ℕ} (Λ : ℝ) (i : Fin d) (lam : ℝ) (k : Fin d) :
    Measurable fun p : FieldPair d × Vec d => famB Λ i lam p.1 p.2 k := by
  have hS : MeasurableSet {p : FieldPair d × Vec d | IsRegular Λ p.1} :=
    (Calculus.Feller.measurableSet_setOf_isRegular d Λ).preimage measurable_fst
  have e : (fun p : FieldPair d × Vec d => famB Λ i lam p.1 p.2 k) = fun p =>
      if IsRegular Λ p.1 then forcedDrift (reducedCoefficient p.1) i lam p.2 k
        else (0 : Vec d) k := by
    funext p
    unfold famB
    split_ifs <;> rfl
  rw [e]
  refine Measurable.ite hS ?_ measurable_const
  have e2 : (fun p : FieldPair d × Vec d => forcedDrift (reducedCoefficient p.1) i lam p.2 k) =
      fun p => (1 / 2 : ℝ) * ∑ l, fderiv ℝ (fun z => reducedCoefficient p.1 z l k) p.2
        (unitVector l) + lam * reducedCoefficient p.1 p.2 k i := by
    funext p
    exact forcedDrift_reduced_eq p.1 i lam p.2 k
  rw [e2]
  refine Measurable.add (measurable_const.mul ?_) (measurable_const.mul ?_)
  · refine Finset.measurable_sum _ fun l _ => ?_
    refine measurable_fderiv_apply_const_with_param ℝ (f := fun (ω : FieldPair d) (z : Vec d) =>
      reducedCoefficient ω z l k) ?_ (unitVector l)
    exact ((continuous_reducedCoefficient_joint d).matrix_elem l k)
  · exact ((continuous_reducedCoefficient_joint d).matrix_elem k i).measurable

theorem family_bounds {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) (i : Fin d) (lam : ℝ) :
    ∃ M : ℝ, (∀ (ω : FieldPair d) (y : Vec d) (a b : Fin d), |famA Λ ω y a b| ≤ M) ∧
      ∀ (ω : FieldPair d) (y : Vec d) (k : Fin d), |famB Λ i lam ω y k| ≤ M := by
  set MA : ℝ := Real.exp (2 * Λ) * Λ with hMA
  set K : ℝ≥0 := Real.toNNReal (Real.exp (2 * Λ) * (2 * Λ ^ 2 + Λ) * Real.sqrt d) with hK
  refine ⟨max 1 (max MA ((1 / 2 : ℝ) * (d * K) + |lam| * MA)), ?_, ?_⟩
  · intro ω y a b
    by_cases hreg : IsRegular Λ ω
    · have h := abs_reducedCoefficient_le hΛ hreg y a b
      unfold famA
      rw [if_pos hreg]
      exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
    · unfold famA
      rw [if_neg hreg]
      refine le_trans ?_ (le_max_left _ _)
      rcases eq_or_ne a b with rfl | hab
      · simp
      · simp [Matrix.one_apply, hab]
  · intro ω y k
    by_cases hreg : IsRegular Λ ω
    · have h := abs_forcedDrift_le (reducedCoefficient ω) (reducedCoefficient_lipschitz hΛ hreg)
        (abs_reducedCoefficient_le hΛ hreg) i lam y k
      unfold famB
      rw [if_pos hreg]
      exact h.trans ((le_max_right _ _).trans (le_max_right _ _))
    · unfold famB
      rw [if_neg hreg]
      simp only [Pi.zero_apply, abs_zero]
      exact zero_le_one.trans (le_max_left _ _)

end EinsteinFull
