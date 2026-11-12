import EinsteinRelation.Correctors.SpatialWeakExhaustion
import EinsteinRelation.External.AKMLocalCorrectors
import EinsteinRelation.Environment.EuclideanLipschitz

/-! # A common whole-space weak gradient for the supplied flow

Source: `paper/main.tex:789–816`. Countable spatial exhaustion turns the
local energy equations of the actual source flow into one whole-space weak
gradient for almost every positive time. The exceptional set does not
depend on the spatial test or its support.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The actual supplied gradient is the spatial weak gradient on the whole
space, on one common event of times in each positive interval.
Source: `paper/main.tex:789–816`. -/
theorem semigroupSolution_weakGradient_univ_ae {d : ℕ} {K a b : ℝ}
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G) (ha : 0 < a) (hab : a < b) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient Set.univ (fun x => u (t, x)) (fun x => G (t, x)) := by
  have hd : 0 < (d : ℝ) + 1 := by positivity
  have hlocal (n : ℕ) : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient (originBall d (((d : ℝ) + 1) * ((n : ℝ) + 1)))
        (fun x => u (t, x)) (fun x => G (t, x)) :=
    (hsol.2.1 a b _ ha hab (mul_pos hd (by positivity))).2.2.2.1
  filter_upwards [ae_all_iff.mpr hlocal] with t ht
  apply hasWeakGradient_univ_of_ball
  intro n
  apply hasWeakGradient_mono (h := ht n)
  intro x hx
  have hx' : ‖x‖ < (n : ℝ) + 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  exact (EinsteinRelation.euclideanNorm_le_dimension_mul_norm x).trans_lt
    (mul_lt_mul_of_pos_left hx' hd)


/-- One common whole-space spatial weak-gradient event holds for almost
every positive time. Source: `paper/main.tex:789–816`. -/
theorem semigroupSolution_weakGradient_positive_ae {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi 0),
      HasWeakGradient Set.univ (fun x => u (t, x)) (fun x => G (t, x)) := by
  have hlocal (n m : ℕ) : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Set.Ioo (1 / ((n : ℝ) + 1)) ((m : ℝ) + 2) →
        HasWeakGradient Set.univ (fun x => u (t, x)) (fun x => G (t, x)) := by
    by_cases hab : 1 / ((n : ℝ) + 1) < (m : ℝ) + 2
    · exact (ae_restrict_iff' measurableSet_Ioo).mp
        (semigroupSolution_weakGradient_univ_ae hsol (by positivity) hab)
    · exact Filter.Eventually.of_forall fun t ht => False.elim (hab (ht.1.trans ht.2))
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards [ae_all_iff.mpr fun n => ae_all_iff.mpr (hlocal n)] with t ht
  intro ht0
  change 0 < t at ht0
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht0
  obtain ⟨m, hm⟩ := exists_nat_gt t
  exact ht n m ⟨hn, hm.trans (by linarith)⟩

end EinsteinRelation.Correctors
