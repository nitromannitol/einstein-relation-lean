import EinsteinRelation.Calculus.WeakRepresentativeOperations
import EinsteinRelation.Correctors.ScalarPotentialApproxEuclidean
import EinsteinRelation.Correctors.SublinearApproximationTransfer
import EinsteinRelation.Correctors.SpatialOscillationComparison
import EinsteinRelation.Calculus.WeakGradientSubtraction

/-!
# Sublinearity of a weak potential from rapid scalar approximations

Source: `paper/main.tex:693-698`. Poincaré controls the centered difference
from each scalar approximant. The maximal gradient error is uniform in the
radius, while the uncentered scalar approximation is sublinear.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Transfer full-radius L² sublinearity through uniform, geometrically
small gradient errors. All functions are actual spatial weak potentials. -/
theorem sublinear_weakPotential_of_rapid_approximation
    (hP : BallPoincareEstimate) {d : ℕ} (hd : 2 ≤ d)
    (u : Vec d → ℝ) (G : Vec d → EuclideanSpace ℝ (Fin d))
    (v : ℕ → Vec d → ℝ) (D : ℕ → Vec d → EuclideanSpace ℝ (Fin d))
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hG : ∀ R : ℝ, 0 < R → MemLp G 2 (volume.restrict (ball 0 R)))
    (hv : ∀ n R, 0 < R → MemLp (v n) 2 (volume.restrict (ball 0 R)))
    (hD : ∀ n R, 0 < R → MemLp (D n) 2 (volume.restrict (ball 0 R)))
    (hwu : HasWeakGradient Set.univ u (fun x => (G x).ofLp))
    (hwv : ∀ n, HasWeakGradient Set.univ (v n) (fun x => (D n x).ofLp))
    (hscalar : ∀ n, Tendsto (fun R : ℝ => (R^2)⁻¹ *
      (⨍ x in ball 0 R, |v n x|^2 ∂volume)) atTop (𝓝 0))
    (C : ℝ) (herror : ∀ᶠ n : ℕ in atTop, ∀ R : ℝ, 1 ≤ R →
      (⨍ x in ball 0 R, ‖D n x - G x‖^2 ∂volume) ≤ C * (1 / 2 : ℝ)^n) :
    Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
      (⨍ x in ball 0 R, (u x - ⨍ y in ball 0 R, u y ∂volume)^2 ∂volume))
      atTop (𝓝 0) := by
  obtain ⟨P, hPpos, hp⟩ := normalized_ball_poincare_square hP d hd
  apply sublinear_oscillation_of_squared_limit
  apply tendsto_zero_of_uniform_geometric_approximation _
    (fun n R => (R^2)⁻¹ * (⨍ x in ball 0 R, |v n x|^2 ∂volume)) (2 * P * C)
  · exact Eventually.of_forall fun R => mul_nonneg (by positivity)
      (by
        rw [average_eq, smul_eq_mul]
        exact mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _))
  · exact hscalar
  apply herror.mono
  intro n hn R hR
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let μ := volume.restrict (ball (0 : Vec d) R)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hRpos)).2.ne
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  have hdiff : HasWeakGradient (ball 0 R) (fun x => u x - v n x)
      (fun x => (G x).ofLp - (D n x).ofLp) := by
    apply hasWeakGradient_sub_of_memLp (ball 0 R) u (v n)
      (fun x => (G x).ofLp) (fun x => (D n x).ofLp)
      (hu R hRpos) (hv n R hRpos) (J.comp_memLp' (hG R hRpos))
      (J.comp_memLp' (hD n R hRpos))
    · exact fun j => HasWeakPartialDerivative.restrict_subset (Set.subset_univ _)
        MeasurableSet.univ (hwu j)
    · exact fun j => HasWeakPartialDerivative.restrict_subset (Set.subset_univ _)
        MeasurableSet.univ (hwv n j)
  have hpoincare := hp R hRpos (fun x => u x - v n x)
    (fun x => (G x).ofLp - (D n x).ofLp) ((hu R hRpos).sub (hv n R hRpos))
    ((J.comp_memLp' (hG R hRpos)).sub (J.comp_memLp' (hD n R hRpos))) hdiff
  have hnorm (x : Vec d) : euclideanSq ((G x).ofLp - (D n x).ofLp) =
      ‖D n x - G x‖^2 := by
    rw [ScalarPotentialApproximation.euclideanSq_ofLp_sub_eq_norm_sq, norm_sub_rev]
  simp only [hnorm] at hpoincare
  have hosc := mul_le_mul_of_nonneg_left
    (average_centered_sq_le_error_and_approximation μ u (v n) (hu R hRpos) (hv n R hRpos))
    (show 0 ≤ (R^2)⁻¹ by positivity)
  have hgrad := hpoincare.trans
    (mul_le_mul_of_nonneg_left (hn R hR) hPpos.le)
  have hvabs : (⨍ x in ball (0 : Vec d) R, (v n x)^2 ∂volume) =
      ⨍ x in ball 0 R, |v n x|^2 ∂volume := by simp only [sq_abs]
  dsimp only [μ] at hosc
  rw [hvabs] at hosc
  nlinarith only [hosc, hgrad]

end EinsteinRelation.Correctors
