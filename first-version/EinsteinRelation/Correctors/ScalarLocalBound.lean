import EinsteinRelation.External.GilbargTrudinger
import EinsteinRelation.Correctors.SpatialBallVolume

/-!
# Unit-scale value bound for the scalar corrector

Source: `paper/main.tex:735-739`. Apply the homogeneous local boundedness
estimate to the affine harmonic coordinate, then remove its affine part.
The constant is uniform in the center, coefficients and scalar gauge.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

private theorem measurableSet_euclideanBall {d : ℕ} (z : Vec d) (R : ℝ) :
    MeasurableSet (ball z R) := by
  unfold ball euclideanNorm euclideanSq dot
  exact (isOpen_lt (by fun_prop) continuous_const).measurableSet

private theorem euclideanBall_subset_closedBall {d : ℕ} (z : Vec d) {R : ℝ}
    (hR : 0 ≤ R) : ball z R ⊆ Metric.closedBall z R := by
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro j
  rw [Real.dist_eq]
  exact (Regeneration.coordinate_abs_le_euclideanNorm (x - z) j).trans hx.le

/-- GT 8.17 controls the scalar corrector relative to any constant by its
local unnormalized L² norm, with a dimension-dependent additive term. -/
theorem scalar_corrector_local_bound_of_GT
    (h817 : LocalBoundednessEstimate) (d : ℕ) (hd : 2 ≤ d)
    (lam Λ : ℝ) (hlam : 0 < lam) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Vec d → Mat d) (z : Vec d),
      EllipticBound (ball z 2) a lam Λ →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d) (i : Fin d) (c : ℝ),
        MemLp (fun x => u x - c) 2 (volume.restrict (ball z 2)) →
        WeakSolution (ball z 2) a
          (fun x => x i - z i + u x - c) (fun x => unitVector i + g x) →
        ∀ᵐ x ∂volume.restrict (ball z 1),
          |u x - c| ≤ C * (1 + Real.sqrt
            (∫ t in ball z 2, |u t - c| ^ 2 ∂volume)) := by
  obtain ⟨C, hC, hest⟩ := h817 d hd lam Λ 2 hlam hΛ (by norm_num)
  let A : ℝ := 4 + 4 * (4 : ℝ) ^ d
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨1 + C * A, by positivity, ?_⟩
  intro a z ha u g i c hu hw
  have hfinite : volume (ball z 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall z 2).measure_ne_top
      (measure_mono (euclideanBall_subset_closedBall z (by norm_num)))
  letI : IsFiniteMeasure (volume.restrict (ball z 2)) :=
    isFiniteMeasure_restrict.mpr hfinite
  have hmass : volume.real (ball z 2) ≤ (4 : ℝ) ^ d := by
    have h := measureReal_mono (μ := (volume : Measure (Vec d)))
      (euclideanBall_subset_closedBall z (by norm_num : (0 : ℝ) ≤ 2))
      (isCompact_closedBall z 2).measure_ne_top
    simpa only [measureReal_def, Real.volume_pi_closedBall z (by norm_num : (0 : ℝ) ≤ 2),
      Fintype.card_fin, show (2 : ℝ) * 2 = 4 by norm_num,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 4 ^ d)] using h
  have hsq := hu.integrable_sq
  have hsquare : Integrable (fun x => |u x - c| ^ 2)
      (volume.restrict (ball z 2)) := by simpa only [sq_abs] using hsq
  have hwaff : Integrable (fun x => |x i - z i + u x - c| ^ 2)
      (volume.restrict (ball z 2)) := by simpa only [sq_abs] using hw.1.integrable_sq
  have hI : 0 ≤ ∫ x in ball z 2, |u x - c| ^ 2 ∂volume :=
    integral_nonneg fun _ => sq_nonneg _
  have hlarge : (∫ x in ball z 2, |x i - z i + u x - c| ^ 2 ∂volume) ≤
      2 * (∫ x in ball z 2, |u x - c| ^ 2 ∂volume) + 8 * (4 : ℝ) ^ d := by
    calc
      _ ≤ ∫ x in ball z 2, 2 * |u x - c| ^ 2 + 8 ∂volume := by
        apply integral_mono_ae hwaff ((hsquare.const_mul 2).add (integrable_const 8))
        filter_upwards [ae_restrict_mem (measurableSet_euclideanBall z 2)] with x hx
        have hc2 : |x i - z i| ≤ 2 :=
          (Regeneration.coordinate_abs_le_euclideanNorm (x - z) i).trans hx.le
        have hc2sq : (x i - z i) ^ 2 ≤ 4 := by
          nlinarith only [sq_nonneg (2 - |x i - z i|), hc2, abs_nonneg (x i - z i), sq_abs (x i - z i)]
        simp only [sq_abs, Pi.add_apply]
        nlinarith only [sq_nonneg ((x i - z i) - (u x - c)), hc2sq]
      _ = 2 * (∫ x in ball z 2, |u x - c| ^ 2 ∂volume) +
          8 * volume.real (ball z 2) := by
        rw [integral_add (hsquare.const_mul 2) (integrable_const 8), integral_const_mul]
        simp only [setIntegral_const, smul_eq_mul, mul_comm (volume.real _) 8]
      _ ≤ _ := by linarith only [hmass]
  have hroot : Real.sqrt (∫ x in ball z 2, |x i - z i + u x - c| ^ 2 ∂volume) ≤
      A * (1 + Real.sqrt (∫ x in ball z 2, |u x - c| ^ 2 ∂volume)) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hs := Real.sq_sqrt hI
    have hs0 := Real.sqrt_nonneg (∫ x in ball z 2, |u x - c| ^ 2 ∂volume)
    have hV : 0 ≤ (4 : ℝ) ^ d := by positivity
    have hAA : 2 ≤ A ∧ 8 * (4 : ℝ) ^ d ≤ A ^ 2 := by
      dsimp [A]
      constructor <;> nlinarith only [hV, sq_nonneg ((4 : ℝ) ^ d)]
    have hA2 : 2 ≤ A ^ 2 := by nlinarith only [hAA.1]
    nlinarith only [hlarge, hs, hs0, hAA.2,
      mul_nonneg (sub_nonneg.mpr hA2) hI,
      mul_nonneg (sq_nonneg A) hs0]
  have hopen : IsOpen (ball z (2 : ℝ)) := by
    unfold ball euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have h := hest (ball z 2) hopen a ha _ _ hw z 1 (by norm_num)
    (by norm_num) (by simpa only [ENNReal.ofReal_ofNat, mul_one] using hw.1)
  filter_upwards [h, ae_restrict_mem (measurableSet_euclideanBall z 1)] with x hx hxb
  have hc1 : |x i - z i| ≤ 1 :=
    (Regeneration.coordinate_abs_le_euclideanNorm (x - z) i).trans hxb.le
  have htri : |u x - c| ≤ |x i - z i + u x - c| + 1 := by
    calc
      _ = |(x i - z i + u x - c) - (x i - z i)| := by congr 1; ring
      _ ≤ |x i - z i + u x - c| + |x i - z i| := abs_sub _ _
      _ ≤ _ := add_le_add_right hc1 _
  simp only [Real.one_rpow, mul_one, one_div] at hx
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] at hx
  simp only [Real.rpow_two] at hx
  have hmult := mul_le_mul_of_nonneg_left hroot hC.le
  have hs0 := Real.sqrt_nonneg (∫ x in ball z 2, |u x - c| ^ 2 ∂volume)
  change |u x - c| ≤ (1 + C * A) *
    (1 + Real.sqrt (∫ t in ball z 2, |u t - c| ^ 2 ∂volume))
  calc
    _ ≤ C * Real.sqrt (∫ t in ball z 2, |t i - z i + u t - c| ^ 2 ∂volume) + 1 :=
      htri.trans (by simpa only [Pi.add_apply] using add_le_add hx (le_refl (1 : ℝ)))
    _ ≤ C * (A * (1 + Real.sqrt (∫ t in ball z 2, |u t - c| ^ 2 ∂volume))) + 1 :=
      add_le_add hmult (le_refl (1 : ℝ))
    _ ≤ _ := by nlinarith only [hs0]

/-- The scalar part of the spatial L²-to-Lᵖ passage, retaining the
unnormalized local L² norm and the volume of the smaller ball. -/
theorem scalar_corrector_local_spatial_moment_of_GT
    (h817 : LocalBoundednessEstimate) (d : ℕ) (hd : 2 ≤ d)
    (lam Λ p : ℝ) (hlam : 0 < lam) (hΛ : 0 < Λ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Vec d → Mat d) (z : Vec d),
      EllipticBound (ball z 2) a lam Λ →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d) (i : Fin d) (c : ℝ),
        MemLp (fun x => u x - c) 2 (volume.restrict (ball z 2)) →
        WeakSolution (ball z 2) a
          (fun x => x i - z i + u x - c) (fun x => unitVector i + g x) →
        (∫⁻ x in ball z 1, ENNReal.ofReal (|u x - c| ^ p) ∂volume) ≤
          volume (ball z 1) * ENNReal.ofReal
            ((C * (1 + Real.sqrt (∫ t in ball z 2, |u t - c| ^ 2 ∂volume))) ^ p) := by
  obtain ⟨C, hC, hest⟩ := scalar_corrector_local_bound_of_GT h817 d hd lam Λ hlam hΛ
  refine ⟨C, hC, ?_⟩
  intro a z ha u g i c hu hw
  calc
    _ ≤ ∫⁻ _ in ball z 1, ENNReal.ofReal
        ((C * (1 + Real.sqrt (∫ t in ball z 2, |u t - c| ^ 2 ∂volume))) ^ p)
        ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [hest a z ha u g i c hu hw] with x hx
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) hx hp.le)
    _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ, mul_comm]

end EinsteinRelation.Correctors
