import EinsteinFull.Calculus.U6BoundedPhysicalResolvent
import EinsteinFull.Calculus.SunaS2Pathwise

/-!
Exact foundation interfaces for arbitrary supplied GMP path laws.
The finite-dimensional statement is kernel equality, hence holds at every start.
No proposed literature axiom or source uniqueness hypothesis is used.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal

namespace EinsteinFull

/-- Every supplied realization has the canonical finite-dimensional laws. -/
theorem foundation_arbitrary_supplied_gmp_canonical_FDD
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (I : Finset ℝ≥0) :
    r.pathLaw.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
      MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I := by
  exact u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam Λ hΛ hω h0 h1 r I

/-- The same supplied law solves the literal physical martingale problem. -/
theorem foundation_arbitrary_supplied_gmp_physical_MP
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (x : Vec d) :
    SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam)
      x (r.pathLaw x) := by
  exact u6_arbitrary_supplied_gmp_solves_martingale_problem hd ω lam Λ hΛ hω h0 h1 r x

/-- The same supplied law also solves the textbook physical martingale problem. -/
theorem foundation_arbitrary_supplied_gmp_textbook_MP
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (x : Vec d) :
    SolvesMartingaleProblem
      (External.Draft.svGenerator (⇑ω.1)
        (physicalDrift ω (firstCoordinateIndex hd) lam)) x (r.pathLaw x) := by
  letI : IsMarkovKernel r.pathLaw := r.pathLaw_isMarkovKernel
  exact s2_canonical_FDD_law_solves_physical_textbook_mp hd ω lam Λ hΛ hω r.pathLaw
    (foundation_arbitrary_supplied_gmp_canonical_FDD hd Λ hΛ ω hω lam h0 h1 r) x

#print axioms foundation_arbitrary_supplied_gmp_canonical_FDD
#print axioms foundation_arbitrary_supplied_gmp_physical_MP
#print axioms foundation_arbitrary_supplied_gmp_textbook_MP

end EinsteinFull
