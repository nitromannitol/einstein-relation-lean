import EinsteinRelation.Correctors.AKMHeatKernelMollifiedPairing
import EinsteinRelation.Correctors.SpatialWeakProduct
import EinsteinRelation.Correctors.AKMHeatKernelCutoffLimit
import EinsteinRelation.Correctors.AKMHeatKernelCutoffs

/-! # Weak identification of vector and scalar kernel data

Source: AKM (9.2), p. 347; `paper/main.tex:777–782,840`.
The bounded divergence field is paired with smooth regularizations of
an actual compact weak-gradient datum, then smoothing is removed internally.
-/

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- A compact integrable weak-gradient datum is a valid test of a bounded
weak divergence field when its gradient is integrable. -/
theorem akm_weak_divergence_compact_integrable_test {d : ℕ}
    {g Df : Vec d → Vec d} {a f : Vec d → ℝ}
    (hdiv : HasWeakDivergence Set.univ g a)
    (hweak : HasWeakGradient Set.univ f Df)
    (hf : Integrable f volume) (hfc : HasCompactSupport f)
    (hDf : ∀ j, Integrable (fun x => Df x j) volume)
    (hg : AEStronglyMeasurable g volume) (ha : AEStronglyMeasurable a volume)
    {B C : ℝ} (hgb : ∀ᵐ x ∂volume, ‖g x‖ ≤ B)
    (hab : ∀ᵐ x ∂volume, |a x| ≤ C) :
    (∫ x, dot (g x) (Df x) ∂volume) = -(∫ x, a x * f x ∂volume) := by
  let ρ : ℕ → Vec d → ℝ := fun n => (akmTraceBump d n).normed volume
  have hρ n : ContDiff ℝ (⊤ : ℕ∞) (ρ n) := (akmTraceBump d n).contDiff_normed
  have hρc n : HasCompactSupport (ρ n) := (akmTraceBump d n).hasCompactSupport_normed
  have hρi n : Integrable (ρ n) volume := (hρ n).continuous.integrable_of_hasCompactSupport (hρc n)
  have hgm j := (continuous_apply j).comp_aestronglyMeasurable hg
  have hgj j : ∀ᵐ x ∂volume, ‖g x j‖ ≤ B := by
    filter_upwards [hgb] with x hx
    exact (norm_le_pi_norm (g x) j).trans hx
  have haj : ∀ᵐ x ∂volume, ‖a x‖ ≤ C := by simpa only [Real.norm_eq_abs] using hab
  have hci n j : Integrable (fun x => ∫ y, Df y j * ρ n (x-y) ∂volume) volume :=
    (hDf j).integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) (hρi n)
  have hgi n j : Integrable (fun x => g x j *
      (∫ y, Df y j * ρ n (x-y) ∂volume)) volume := (hci n j).bdd_mul (hgm j) (hgj j)
  have hid n : (∑ j, ∫ x, g x j * (∫ y, Df y j * ρ n (x-y) ∂volume) ∂volume) =
      -(∫ x, a x * (∫ y, f y * ρ n (x-y) ∂volume) ∂volume) := by
    have hh := hdiv.2.2 _ (akm_convolution_isSpatialTest hf hfc (hρ n) (hρc n))
    simp only [Measure.restrict_univ] at hh
    rw [← integral_finset_sum _ (fun j _ => hgi n j)]
    convert hh using 1
    apply integral_congr_ae
    filter_upwards with x
    unfold dot gradient
    apply Finset.sum_congr rfl
    intro j _
    rw [akm_coordinateDerivative_convolution hf hweak (hρ n) (hρc n)]
  have hleft j : Tendsto (fun n => ∫ x, g x j *
      (∫ y, Df y j * ρ n (x-y) ∂volume) ∂volume) atTop
      (𝓝 (∫ x, Df x j * g x j ∂volume)) := by
    have hh := akm_bounded_mollification_pairing_tendsto (hDf j) (hgm j) (hgj j)
    convert hh using 1
    funext n
    exact akm_integral_mul_convolution_swap (hDf j) (hρi n) (hgm j) (hgj j)
      (akmTraceBump d n).normed_neg
  have hright : Tendsto (fun n => ∫ x, a x *
      (∫ y, f y * ρ n (x-y) ∂volume) ∂volume) atTop
      (𝓝 (∫ x, f x * a x ∂volume)) := by
    have hh := akm_bounded_mollification_pairing_tendsto hf ha haj
    convert hh using 1
    funext n
    exact akm_integral_mul_convolution_swap hf (hρi n) ha haj
      (akmTraceBump d n).normed_neg
  have hlim := tendsto_finset_sum Finset.univ (fun j _ => hleft j)
  have heq : (∑ j, ∫ x, Df x j * g x j ∂volume) = -(∫ x, f x * a x ∂volume) :=
    tendsto_nhds_unique hlim ((hright.neg).congr (fun n => (hid n).symm))
  have hgDf j : Integrable (fun x => Df x j * g x j) volume :=
    (hDf j).mul_bdd (hgm j) (hgj j)
  rw [← integral_finset_sum _ (fun j _ => hgDf j)] at heq
  convert heq using 1
  · apply integral_congr_ae
    filter_upwards with x
    unfold dot
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  · congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- Compact weak-gradient tests are valid in the bounded divergence pairing.
The local gradient needs only the local integrability already in its definition. -/
theorem akm_weak_kernel_compact_pairing {d : ℕ}
    {g Dp : Vec d → Vec d} {a p χ : Vec d → ℝ}
    (hdiv : HasWeakDivergence Set.univ g a)
    (hgrad : HasWeakGradient Set.univ p Dp) (hp : Continuous p)
    (hg : AEStronglyMeasurable g volume) (ha : AEStronglyMeasurable a volume)
    {B C : ℝ} (hgb : ∀ᵐ x ∂volume, ‖g x‖ ≤ B)
    (hab : ∀ᵐ x ∂volume, |a x| ≤ C)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    (∫ x, χ x * dot (g x) (Dp x) + p x * dot (g x) (gradient χ x) ∂volume) =
      -(∫ x, χ x * p x * a x ∂volume) := by
  let f : Vec d → ℝ := fun x => χ x * p x
  let Df : Vec d → Vec d := fun x j => χ x * Dp x j + p x * coordinateDerivative j χ x
  have hfi : Integrable f volume :=
    (hχ.continuous.mul hp).integrable_of_hasCompactSupport hχc.mul_right
  have hDfi j : Integrable (fun x => Df x j) volume := by
    have hi := integrableOn_mul_spatialTest (hgrad j).2.1
      (show IsSpatialTest Set.univ χ from ⟨hχ, hχc, Set.subset_univ _⟩)
    have hi' : Integrable (fun x => Dp x j * χ x) volume := by
      simpa only [IntegrableOn, Measure.restrict_univ] using hi
    have hc : Continuous (coordinateDerivative j χ) :=
      (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hci : Integrable (fun x => p x * coordinateDerivative j χ x) volume :=
      (hp.mul hc).integrable_of_hasCompactSupport
      (hχc.fderiv_apply ℝ (unitVector j)).mul_left
    exact (hi'.congr (Eventually.of_forall (fun x => mul_comm _ _))).add hci
  have hh := akm_weak_divergence_compact_integrable_test hdiv
    (hasWeakGradient_mul_smooth isOpen_univ hgrad hχ) hfi hχc.mul_right hDfi hg ha hgb hab
  convert hh using 1
  · apply integral_congr_ae
    filter_upwards with x
    unfold dot gradient
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  · congr 1
    apply integral_congr_ae
    filter_upwards with x
    ring

/-- Integration by parts for a continuous integrable kernel and an absolutely
integrable gradient pairing. Compact testing and both cutoff limits are
proved internally. Source: AKM (9.2), p. 347; `paper/main.tex:777–782,840`. -/
theorem akm_weak_kernel_integration_by_parts {d : ℕ}
    {g Dp : Vec d → Vec d} {a p : Vec d → ℝ}
    (hdiv : HasWeakDivergence Set.univ g a)
    (hgrad : HasWeakGradient Set.univ p Dp) (hpc : Continuous p)
    (hp : Integrable p volume)
    (hg : AEStronglyMeasurable g volume) (ha : AEStronglyMeasurable a volume)
    {B C : ℝ} (hgb : ∀ᵐ x ∂volume, ‖g x‖ ≤ B)
    (hab : ∀ᵐ x ∂volume, |a x| ≤ C)
    (hint : Integrable (fun x => dot (g x) (Dp x)) volume) :
    -(∫ x, dot (g x) (Dp x) ∂volume) = ∫ x, p x * a x ∂volume := by
  obtain ⟨χ, L, hL, hχ, hb, hlim, hd⟩ := akm_exists_scaled_cutoffs d
  exact akm_kernel_pairing_of_compact_cutoffs hp hint hg ha hL hgb hab
    (fun n => (hχ n).1) hb hlim hd
    (fun n => akm_weak_kernel_compact_pairing hdiv hgrad hpc hg ha hgb hab
      (hχ n).1 (hχ n).2)

end EinsteinRelation.Correctors
