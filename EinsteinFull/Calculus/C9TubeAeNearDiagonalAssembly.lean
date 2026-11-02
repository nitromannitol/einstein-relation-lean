import EinsteinFull.Calculus.C8TubeWeightedParabolicPoincare
import PDEFoundation.Measure.BallVolume

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open scoped Topology

namespace EinsteinFull.Calculus

/-- A uniform weighted row mass and a row comparison yield a near-diagonal lower bound. -/
theorem c9_half_time_row_mass_near_diagonal_of_ae
    (d : ℕ) (κ A H m : ℝ) (hκ : 0 < κ) (hA : 0 < A) (hH : 0 < H) (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ρ : Vec d → ℝ) (q : ℝ → Vec d → Vec d → ℝ)
    (hρ : ∀ z, 0 ≤ ρ z ∧ ρ z ≤ κ⁻¹) (t : ℝ) (ht : 0 < t) (x y : Vec d),
    IntegrableOn (fun z => q (t/2) x z * ρ z) (sourceBall x (A * Real.sqrt (t/2))) →
    m ≤ (∫ z in sourceBall x (A * Real.sqrt (t/2)), q (t/2) x z * ρ z) →
    (∀ᵐ z ∂volume.restrict (sourceBall x (A * Real.sqrt (t/2))),
      0 ≤ q (t/2) x z ∧ q (t/2) x z ≤ H * q t x y) →
    c * Real.rpow t (-(d : ℝ)/2) ≤ q t x y := by
  let V : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal
  have hV : 0 < V := volume_euclideanBall_toReal_pos 0 (by norm_num)
  let D : ℝ := H * κ⁻¹ * A ^ d * V
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨m / D, div_pos hm hD, ?_⟩
  intro ρ q hρ t ht x y hint hmass hrow
  have ht2 : 0 < t/2 := by positivity
  have hr : 0 < A * Real.sqrt (t/2) := mul_pos hA (Real.sqrt_pos.2 ht2)
  let B := sourceBall x (A * Real.sqrt (t/2))
  have hB : B = euclideanBall x (A * Real.sqrt (t/2)) := c8_sourceBall_eq_euclideanBall x hr
  have hfin : volume B ≠ ⊤ := by rw [hB]; exact volume_euclideanBall_ne_top x hr.le
  haveI := isFiniteMeasure_restrict.mpr hfin
  have hq : 0 ≤ q t x y := by
    by_contra hn
    have hqneg : q t x y < 0 := lt_of_not_ge hn
    have hcomp0 : ∀ᵐ z ∂volume.restrict B, q (t/2) x z * ρ z ≤ 0 := by
      filter_upwards [hrow] with z hz
      have hzneg : q (t/2) x z ≤ 0 := by nlinarith [hz.2]
      exact mul_nonpos_of_nonpos_of_nonneg hzneg (hρ z).1
    have hi0 := integral_mono_ae hint (integrable_const (0 : ℝ)) hcomp0
    simp only [integral_zero] at hi0
    linarith
  have hcomp : ∀ᵐ z ∂volume.restrict B, q (t/2) x z * ρ z ≤ H * q t x y * κ⁻¹ := by
    filter_upwards [hrow] with z hz
    exact mul_le_mul hz.2 (hρ z).2 (hρ z).1 (mul_nonneg hH.le hq)
  have hi := integral_mono_ae hint (integrable_const (H * q t x y * κ⁻¹)) hcomp
  have hvol : (volume B).toReal = (A * Real.sqrt (t/2))^d * V := by
    rw [hB, volume_euclideanBall_toReal_eq_unit_mul_of_pos x hr]
  have hbound : m ≤ D * (Real.sqrt t)^d * q t x y := by
    have hc : (∫ _ in B, H * q t x y * κ⁻¹) =
        (H * q t x y * κ⁻¹) * (volume B).toReal := by
      simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_comm]
    rw [hc, hvol, mul_pow] at hi
    dsimp [D]
    have hs : Real.sqrt (t/2) ≤ Real.sqrt t := Real.sqrt_le_sqrt (by linarith)
    have hp : (Real.sqrt (t/2))^d ≤ (Real.sqrt t)^d :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hs d
    have hcoef : 0 ≤ H * q t x y * κ⁻¹ * (A ^ d * V) := by positivity
    nlinarith [hmass.trans hi, mul_le_mul_of_nonneg_left hp hcoef]
  have hp : (Real.sqrt t)^d = Real.rpow t ((d : ℝ)/2) := by
    rw [Real.rpow_eq_pow]
    simpa only [Real.rpow_natCast] using
      (Real.rpow_div_two_eq_sqrt (d : ℝ) ht.le).symm
  have hpow : 0 < Real.rpow t ((d : ℝ)/2) := Real.rpow_pos_of_pos ht _
  rw [hp] at hbound
  have hresult : m / D / Real.rpow t ((d : ℝ)/2) ≤ q t x y := by
    apply (div_le_iff₀ hpow).2
    apply (div_le_iff₀ hD).2
    nlinarith [hbound]
  have hneg : Real.rpow t (-(d : ℝ)/2) =
      (Real.rpow t ((d : ℝ)/2))⁻¹ := by
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow, neg_div, Real.rpow_neg ht.le]
  rw [hneg]
  simpa only [div_eq_mul_inv] using hresult

end EinsteinFull.Calculus
