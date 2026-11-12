import EinsteinRelation.Calculus.CoordinatePathTelescoping
import EinsteinRelation.Calculus.CoordinateTranslationPath

/-! # Endpoint cancellation along coordinate paths

Source: `paper/main.tex:1021–1029`. The finite sum of the actual segment
endpoint sources equals the full translation difference.
-/

noncomputable section
namespace EinsteinRelation

/-- Telescoping sum: ∑_{k=0}^{d-1} (a(k+1) - a(k)) = a(d) - a(0) -/
lemma coordinatePath_telescope_aux (a : ℕ → ℝ) (d : ℕ) :
    (∑ k ∈ Finset.range d, (a (k + 1) - a k)) = a d - a 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      ring

end EinsteinRelation
