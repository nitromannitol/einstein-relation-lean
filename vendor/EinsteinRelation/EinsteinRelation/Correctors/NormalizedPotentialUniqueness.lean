import EinsteinRelation.Correctors.BallPoincareTransfer
import EinsteinRelation.Correctors.SpatialBallVolume
import EinsteinRelation.Regeneration.HalfSpaces

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- A weak potential with zero gradient is constant on each ball. -/
theorem ae_eq_average_of_weakGradient_zero (hP : BallPoincareEstimate)
    {d : ℕ} (hd : 2 ≤ d) (R : ℝ) (hR : 0 < R) (u : Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (ball 0 R)))
    (hweak : HasWeakGradient (ball 0 R) u (fun _ => 0)) :
    u =ᵐ[volume.restrict (ball (0 : Vec d) R)]
      fun _ => ⨍ x in ball (0 : Vec d) R, u x ∂volume := by
  let μ := volume.restrict (ball (0 : Vec d) R)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2.ne
  obtain ⟨C, _, hest⟩ := hP d hd
  have h := hest 0 R hR u (fun _ => 0) hu (memLp_const (0 : Vec d)) hweak
  simp only [euclideanSq, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    integral_zero, Real.sqrt_zero, mul_zero] at h
  let c := ⨍ x in ball (0 : Vec d) R, u x ∂volume
  have hm : MemLp (fun x => u x - c) 2 μ := hu.sub (memLp_const c)
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hn : 0 ≤ ∫ x, |u x - c| ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hz : (∫ x, |u x - c| ^ 2 ∂μ) = 0 := by
    have hs := Real.sq_sqrt hn
    change Real.sqrt (∫ x, |u x - c| ^ 2 ∂μ) ≤ 0 at h
    have ht := Real.sqrt_nonneg (∫ x, |u x - c| ^ 2 ∂μ)
    nlinarith
  have ha := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg |u x - c|)
    (by simpa only [Real.norm_eq_abs] using hi)).mp hz
  filter_upwards [ha] with x hx
  change u x = c
  have : |u x - c| = 0 := eq_zero_of_pow_eq_zero hx
  exact sub_eq_zero.mp (abs_eq_zero.mp this)

/-- A weak potential with zero gradient is constant, and normalization on
one smaller ball fixes that constant; source `paper/main.tex:693-698`. -/
theorem ae_eq_zero_of_weakGradient_zero_and_unitBall_mean
    (hP : BallPoincareEstimate) {d : ℕ} (hd : 2 ≤ d)
    (R : ℝ) (hR : 1 ≤ R) (u : Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (ball 0 R)))
    (hweak : HasWeakGradient (ball 0 R) u (fun _ => 0))
    (hmean : (∫ x in ball (0 : Vec d) 1, u x) = 0) :
    u =ᵐ[volume.restrict (ball 0 R)] fun _ => 0 := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let c := ⨍ x in ball (0 : Vec d) R, u x ∂volume
  have ha := ae_eq_average_of_weakGradient_zero hP hd R hRpos u hu hweak
  have hs : ball (0 : Vec d) 1 ⊆ ball 0 R := fun x hx => lt_of_lt_of_le hx hR
  have ha1 := ha.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))
  have hc : c = 0 := by
    have heq := integral_congr_ae ha1
    rw [hmean, integral_const, smul_eq_mul] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left
      (by simpa only [Measure.real, Measure.restrict_apply_univ] using
        (unitBall_volume_pos_finite d).ne')
  change u =ᵐ[volume.restrict (ball (0 : Vec d) R)] (fun _ => c) at ha
  simpa only [hc] using ha

end EinsteinRelation.Correctors
