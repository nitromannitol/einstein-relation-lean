import EinsteinRelation.Regeneration.Coupling

/-! # No-backtracking is invariant under spatial recentering

Source `paper/main.tex:331–340,377–403`. The future record `Y_k` in
`regen.future` uses the path increments `(Y_{τ_k+t}-Y_{τ_k})_{t≥0}`, and the
no-backtracking event `D` is a barrier on the displacement from the starting
point. Subtracting one fixed spatial point from every position leaves each
coordinate increment unchanged, so `recenterSample` preserves `NoBacktracking`.
This is a deterministic path fact; it makes no probabilistic or kernel claim.
-/

open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

/-- Recentering subtracts the same fixed point at every time, so each coordinate
displacement from time zero is unchanged. -/
private theorem recenterSample_increment {d : ℕ} (x : Vec d) (z : CoupledSample d)
    (i : Fin d) (t : ℝ≥0) :
    (recenterSample x z).1 t i - (recenterSample x z).1 0 i = z.1 t i - z.1 0 i := by
  show (z.1 t - x) i - (z.1 0 - x) i = z.1 t i - z.1 0 i
  simp only [Pi.sub_apply]
  ring

/-- The extended first downward hitting time depends only on coordinate increments. -/
private theorem firstHittingBelow_congr_of_increments {d : ℕ} (γ δ : Path d) (i : Fin d)
    (a : ℝ) (h : ∀ t : ℝ≥0, δ t i - δ 0 i = γ t i - γ 0 i) :
    firstHittingBelow δ i a = firstHittingBelow γ i a := by
  unfold firstHittingBelow
  refine iInf_congr fun t => ?_
  rw [h t]

/-- Source D is unchanged by spatial recentering of the coupled sample. -/
theorem noBacktracking_recenterSample_iff {d : ℕ} (x : Vec d) (z : CoupledSample d)
    (R : ℝ) (i : Fin d) : NoBacktracking R (recenterSample x z).1 i ↔ NoBacktracking R z.1 i := by
  unfold NoBacktracking
  rw [firstHittingBelow_congr_of_increments z.1 (recenterSample x z).1 i (-R)
    (recenterSample_increment x z i)]

end EinsteinRelation.Regeneration
