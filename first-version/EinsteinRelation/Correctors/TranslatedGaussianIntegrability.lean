import EinsteinRelation.Correctors.TranslatedLocalIntegrability
import EinsteinRelation.Correctors.IntegralCauchySquare
import EinsteinRelation.Correctors.ScaledGaussianIntegrability
import EinsteinRelation.Correctors.ParabolicUnitScaleGradient
import EinsteinRelation.Regeneration.HalfSpaces

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Gaussian local gradient energies give whole-space absolute convergence.
Source: AKM E.1 (E.7); `paper/main.tex:787–806,850`. -/
theorem integrable_of_translated_gaussian_energy {d : ℕ}
    {F : Vec d → Vec d} (hF : Measurable F) {D κ : ℝ}
    (hD : 0 ≤ D) (hκ : 0 < κ) (y : Vec d)
    (hlocal : ∀ v : Vec d, MemLp (fun x => euclideanNorm (F (v+x))) 2
      (volume.restrict (originBall d 1)))
    (hbound : ∀ v : Vec d,
      (∫ x in originBall d 1, euclideanNorm (F (v+x))^2) ≤
        D * Real.exp (-(2*κ) * euclideanSq (y-v))) :
    Integrable F volume := by
  let B := originBall d 1
  have hopen : IsOpen B := by
    unfold B originBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hBne : B.Nonempty := by
    refine ⟨0,?_⟩
    norm_num [B,originBall,euclideanNorm,euclideanSq,dot]
  have hBp : volume B ≠ 0 := (hopen.measure_pos volume hBne).ne'
  have hc := isCompact_closure_originBall d 1
  letI : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
      (hc.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  have hsq (v : Vec d) : euclideanSq (y-v) = euclideanSq (v-y) := by
    unfold euclideanSq dot
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.sub_apply]
    ring
  let w : Vec d → ℝ := fun v => Real.sqrt (D*volume.real B) *
    Real.exp (-κ*euclideanSq (y-v))
  have hw : Integrable w volume := by
    have hh := (measurePreserving_add_right volume (-y)).integrable_comp_of_integrable
      (integrable_scaled_gaussian_origin (d := d) hκ)
    simpa only [Function.comp_def,← sub_eq_add_neg,← hsq] using
      hh.const_mul (Real.sqrt (D*volume.real B))
  have hnorm (v : Vec d) : ‖F v‖ ≤ euclideanNorm (F v) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    rw [Real.norm_eq_abs]
    exact Regeneration.coordinate_abs_le_euclideanNorm _ j
  have hloc (v : Vec d) : IntegrableOn (fun x => ‖F (v+x)‖) B volume :=
    ((hlocal v).integrable (by norm_num)).mono'
      ((hF.comp (measurable_const.add measurable_id)).norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by simpa only [norm_norm] using hnorm (v+x))
  apply integrable_of_translated_local_norm_envelope hF hBp hw hloc
  intro v
  have hcs := integral_mul_sq_le_integral_sq_mul_integral_sq (volume.restrict B)
    (hlocal v) (memLp_const (1 : ℝ))
  simp only [mul_one,one_pow,integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one] at hcs
  have hbs := mul_le_mul_of_nonneg_right (hbound v) (measureReal_nonneg (μ := volume) (s := B))
  have he : (Real.exp (-κ*euclideanSq (y-v)))^2 =
      Real.exp (-(2*κ)*euclideanSq (y-v)) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hwpos : 0 ≤ w v := by dsimp only [w]; positivity
  have hwsq : (w v)^2 = D*Real.exp (-(2*κ)*euclideanSq (y-v))*volume.real B := by
    dsimp only [w]
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hD measureReal_nonneg),he]
    ring
  have hnon : 0 ≤ ∫ x in B, euclideanNorm (F (v+x)) :=
    integral_nonneg fun _ => Real.sqrt_nonneg _
  have hh : (∫ x in B, euclideanNorm (F (v+x))) ≤ w v := by
    have hs := hcs.trans hbs
    rw [← hwsq] at hs
    nlinarith
  apply le_trans ?_ hh
  apply integral_mono_ae (hloc v) ((hlocal v).integrable (by norm_num))
  exact Filter.Eventually.of_forall fun x => hnorm (v+x)

end EinsteinRelation.Correctors
