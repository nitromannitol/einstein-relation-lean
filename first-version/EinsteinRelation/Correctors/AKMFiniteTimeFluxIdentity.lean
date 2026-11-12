import EinsteinRelation.Correctors.AKMLocalFlowPairingContinuity
import EinsteinRelation.Correctors.ParabolicIntegratedFlux
import EinsteinRelation.Correctors.ParabolicSeparatedTests
import EinsteinRelation.Correctors.ParabolicSpatialPairings
import EinsteinRelation.Correctors.SpatialBallVolume
import EinsteinRelation.Correctors.WeakTimeFundamentalTheorem

/-! # Endpoint flux identity for the actual parabolic flow

Source: `paper/main.tex:808–816`. The distributional parabolic equation
determines the flux of a finite-time integral at its actual positive-time
endpoints. Continuity is needed only for scalar test pairings; no time
continuity of the gradient is assumed.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The flux of the literal integrated gradient pairs to the difference
of the original scalar flow at the two endpoints.
Source: `paper/main.tex:808–816`. -/
theorem akmLocal_semigroup_time_integral_flux_identity {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hR : 0 < R)
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest (originBall d R) ψ) :
    (∫ x in originBall d R,
      dot ((A x).mulVec (fun j => ∫ t in Set.Ioo a b, G (t,x) j)) (gradient ψ x)) =
      (∫ x in originBall d R, u (a,x) * ψ x) -
        (∫ x in originBall d R, u (b,x) * ψ x) := by
  have hball : originBall d R = ball (0 : Vec d) R := by
    ext x
    simp only [originBall, ball, sub_zero]
  haveI : IsFiniteMeasure (volume.restrict (originBall d R)) := by
    rw [hball]
    exact isFiniteMeasure_restrict.mpr
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2.ne
  have hlocal := hsol.2.1 a b R ha hab hR
  let f : ℝ → ℝ := fun t => ∫ x in originBall d R, u (t,x) * ψ x
  let q : ℝ → ℝ := fun t => ∫ x in originBall d R,
    dot ((A x).mulVec (G (t,x))) (gradient ψ x)
  have hpair (t : ℝ) : f t = ∫ x, u (t,x) * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψ.2.2 h)), mul_zero]
  have hfc : ContinuousOn f (Set.Icc a b) := by
    change ContinuousOn (fun t => f t) (Set.Icc a b)
    simp_rw [hpair]
    exact (akmLocal_semigroup_pairing_continuousOn hsol hψ.1.continuous hψ.2.1).mono
      (fun t ht => ha.trans_le ht.1)
  have hqi : IntegrableOn q (Set.Ioo a b) :=
    (parabolicSolution_spatial_pairings_integrable hK A hlocal hψ.1 hψ.2.1).2
  have hnegqi : IntegrableOn (fun t => -q t) (Set.Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact hqi.neg
  have hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Set.Ioo a b →
      (∫ t in Set.Ioo a b, f t * deriv η t) =
        -(∫ t in Set.Ioo a b, (-q t) * η t) := by
    intro η hη hηc hηs
    have he := parabolicSolution_separated_time_test hK A hlocal hη hηc
      (by simpa only [interior_Ioo] using hηs) hψ
    simp_rw [neg_mul]
    rw [integral_neg, neg_neg]
    simpa only [f, q, mul_comm] using he
  have he := integral_eq_sub_of_weak_time_derivative hab f (fun t => -q t)
    hfc hnegqi hweak
  rw [integral_neg, integral_Icc_eq_integral_Ioo] at he
  rw [parabolicSolution_time_integral_flux_pairing hK A hlocal hψ]
  change (∫ t in Set.Ioo a b, q t) = f a - f b
  linarith

end EinsteinRelation.Correctors
