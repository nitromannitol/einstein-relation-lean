import EinsteinRelation.Correctors.CurlPoissonLocalBound

/-! Source: `paper/main.tex:733-745`. The scalar divergence source in
each tensor component is bounded by the Euclidean centered-flux norm. -/
namespace EinsteinRelation.Correctors
open External.AKM

/-- The two-coordinate curl source costs at most twice the vector norm. -/
theorem euclideanNorm_curlSource_le {d : ℕ} (G : Vec d) (j k : Fin d) :
    euclideanNorm (G j • unitVector k - G k • unitVector j) ≤
      2 * euclideanNorm G := by
  have hn (l : Fin d) : euclideanNorm (unitVector l) = 1 := by
    simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]
  have h := TimeChange.euclideanNorm_add_le (G j • unitVector k)
    ((-G k) • unitVector j)
  rw [TimeChange.euclideanNorm_smul, TimeChange.euclideanNorm_smul,
    hn, hn, abs_neg, mul_one, mul_one] at h
  rw [sub_eq_add_neg, ← neg_smul]
  exact h.trans (by linarith [Regeneration.coordinate_abs_le_euclideanNorm G j,
    Regeneration.coordinate_abs_le_euclideanNorm G k])
end EinsteinRelation.Correctors
