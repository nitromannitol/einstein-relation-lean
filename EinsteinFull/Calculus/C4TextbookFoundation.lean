import EinsteinFull.External.BassContinuousElliptic

/-!
# Textbook martingale-problem well-posedness on the frozen path space

Transport the admitted Bass theorem through completion and the measurable path
equivalence, preserving existence and uniqueness for the same coefficients.
-/

open EinsteinRelation MeasureTheory

namespace EinsteinFull

/-- Continuous bounded symmetric uniformly elliptic diffusion coefficients and
bounded measurable drift give the frozen textbook martingale problem a unique
law from each starting point. -/
theorem foundation_textbook_well_posed : External.Draft.svWellPosedStmt := by
  intro d hd a b hcont hsym hab hell hb hbb x
  obtain ⟨Λ₁, Λ₂, hΛ₁, hΛ₂, hellSource, hbSource⟩ :=
    External.Bass.exists_source_parameters hab hell hbb
  obtain ⟨Ma, haBound⟩ := hab
  obtain ⟨Mb, hbBound⟩ := hbb
  obtain ⟨P, hP, huniq⟩ := External.bass_continuous_elliptic_well_posed
    d hd Λ₁ Λ₂ hΛ₁ hΛ₂ a b hcont.measurable hb hsym hellSource hbSource hcont x
  apply (External.Bass.unique_solution_iff_frozen
    hcont.measurable hb haBound hbBound x).mp
  refine ⟨P, (External.Bass.Completion.solvesMartingaleProblem_iff
    hcont.measurable hb haBound hbBound).mp hP, ?_⟩
  intro Q hQ
  exact huniq Q ((External.Bass.Completion.solvesMartingaleProblem_iff
    hcont.measurable hb haBound hbBound).mpr hQ)

end EinsteinFull
