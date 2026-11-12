import EinsteinRelation.Correctors.ScalarCorrectedGradientMoments
import EinsteinRelation.Correctors.ScalarCorrectedDriftMoments
import EinsteinRelation.Correctors.ScalarCorrectedErrorMoments
import EinsteinRelation.Correctors.CorrectorAmplitudeLogBounds

/-! # Joint moments of the actual corrected fields

Source: `paper/main.tex:1070–1082`. One pair of constants controls all
five corrected fields, with fourth moments only on the original factors.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- Uniform constants for all five one-scale corrected fields
(`paper/main.tex:1070–1082`). -/
theorem scalarCorrected_band_moments (d : ℕ) (L A B : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ]
    {p r : ℝ}, 1 ≤ p → 1 ≤ r → ∀
    (a : FieldPair d → Mat d) (abar : Mat d) (i : Fin d)
    (u : FieldPair d → ℝ) (Du : FieldPair d → Vec d) (phi : Fin d → FieldPair d → ℝ)
    (Dphi H F : Fin d → FieldPair d → Vec d) (Sig : Fin d → FieldPair d → Mat d),
    Measurable a → Measurable u → Measurable Du →
    (∀ j, Measurable (phi j)) → (∀ j, Measurable (Dphi j)) →
    (∀ j, Measurable (H j)) → (∀ j, Measurable (F j)) → (∀ j, Measurable (Sig j)) →
    (∀ᵐ ω ∂μ, ∀ i j, |a ω i j| ≤ L) → (∀ i j, |abar i j| ≤ L) →
    eLpNorm u (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (B * r) →
    (∀ j, eLpNorm (fun ω => Du ω j) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal B) →
    (∀ j k, eLpNorm (fun ω => H j ω k) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (B / r)) →
    (∀ j, eLpNorm (phi j) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (A * Real.sqrt (Real.log (2 + r)))) →
    (∀ j k, eLpNorm (fun ω => Dphi j ω k) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal A) →
    (∀ j k, eLpNorm (fun ω => F j ω k) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (A / r)) →
    (∀ j k m, eLpNorm (fun ω => Sig j ω k m) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (A * Real.sqrt (Real.log (2 + r)))) →
    let v := fun ω => u ω + ∑ j, phi j ω * Du ω j
    let Dv := fun ω => Du ω + ∑ j, (Du ω j • Dphi j ω + phi j ω • H j ω)
    let W := fun ω => (1 / 2 : ℝ) • ∑ j,
      (phi j ω • ((a ω).mulVec (H j ω)) - (Sig j ω).mulVec (H j ω) + Du ω j • F j ω)
    let P := fun ω => u ω • abar.mulVec (unitVector i) + ∑ j, Du ω j • (fun k => Sig j ω i k)
    let h := fun ω => ∑ j, (phi j ω * dot ((a ω).mulVec (unitVector i)) (H j ω) -
      (Sig j ω).mulVec (H j ω) i + Du ω j * F j ω i)
    Measurable Dv → Measurable W → Measurable P →
    eLpNorm v (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal (C₁ * (r + Real.sqrt (Real.log (2 + r)))) ∧
    eLpNorm (fun ω => euclideanNorm (P ω)) (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal (C₁ * (r + Real.sqrt (Real.log (2 + r)))) ∧
    eLpNorm (fun ω => euclideanNorm (Dv ω)) (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal C₁ ∧
    eLpNorm (fun ω => euclideanNorm (W ω)) (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal (C₂ * (Real.sqrt (Real.log (2 + r)) / r)) ∧
    eLpNorm h (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal (C₂ * (Real.sqrt (Real.log (2 + r)) / r)) := by
  obtain ⟨CP, hCP, hPb⟩ := scalarCorrected_drift_coordinate_bounds d L A B hL hA hB
  let CV := B + 4 * (d : ℝ) * A * B
  let CE := (((d : ℝ) ^ 2 * (L + 1) + d) * A * B)
  let C₁ := CV + Real.sqrt d * (CP + CV)
  let C₂ := (1 + Real.sqrt d) * CE
  have hCV : 0 ≤ CV := by dsimp [CV]; positivity
  have hCE : 0 ≤ CE := by dsimp [CE]; positivity
  refine ⟨C₁, C₂, by dsimp [C₁]; positivity, by dsimp [C₂]; positivity, ?_⟩
  intro μ _ p r hp hr a abar i u Du phi Dphi H F Sig ham hu hDu hphi hDphi hH hF hSig hab habar hub hDub hHb hphib hDphib hFb hSigb
  dsimp only
  intro hDvm hWm hPm
  let w := Real.sqrt (Real.log (2 + r))
  have hw := correctorAmplitude_log_weight (d := d) hr
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hpm (j k m : Fin d) : Measurable (fun ω => Sig j ω k m) :=
    ((continuous_id : Continuous (fun M : Mat d => M)).matrix_elem k m).measurable.comp (hSig j)
  have hhm (j k : Fin d) : Measurable (fun ω => H j ω k) := (measurable_pi_apply k).comp (hH j)
  have hfm (j k : Fin d) : Measurable (fun ω => F j ω k) := (measurable_pi_apply k).comp (hF j)
  have hdm (j : Fin d) : Measurable (fun ω => Du ω j) := (measurable_pi_apply j).comp hDu
  have ham' (k m : Fin d) : Measurable (fun ω => a ω k m) :=
    ((continuous_id : Continuous (fun M : Mat d => M)).matrix_elem k m).measurable.comp ham
  have hfun := scalarCorrected_function_moment μ hp hr hw0 hA hB u Du phi hu hDu hphi hub hDub hphib
  have hgrad := scalarCorrected_gradient_coordinate_moment μ hp hr hw0 hw.2.1 hA hB
    Du phi Dphi H hDu hphi hDphi hH hDub hphib hDphib hHb
  have hPcoord := hPb μ hp hr hw.1 abar habar u Du Sig hu hDu hSig hub hDub hSigb i
  have hgradnorm := eLpNorm_euclideanNorm_le_of_coordinate_bounds μ (by linarith : 2 ≤ 2*p)
    hCV hDvm hgrad
  have hPnorm := eLpNorm_euclideanNorm_le_of_coordinate_bounds μ (by linarith : 2 ≤ 2*p)
    (mul_nonneg hCP (add_nonneg (by linarith) hw0)) hPm hPcoord
  have herror (k : Fin d) := scalarCorrected_error_scalar_coordinate μ hp hr hw.1 hA hB hL
    (fun _ m ω => a ω k m) (fun j m ω => Sig j ω k m) phi (fun j ω => Du ω j)
    (fun j m ω => H j ω m) (fun j ω => F j ω k)
    (fun _ m => ham' k m) (fun j m => hpm j k m) hphi hdm hhm (fun j => hfm j k)
    (hab.mono fun ω hω j m => hω k m) (fun j m => hSigb j k m) hphib hDub hHb (fun j => hFb j k)
  have hWcoord (k : Fin d) : eLpNorm
      (fun ω => ((1/2 : ℝ) • ∑ j, (phi j ω • ((a ω).mulVec (H j ω)) -
        (Sig j ω).mulVec (H j ω) + Du ω j • F j ω)) k) (ENNReal.ofReal (2*p)) μ ≤ ENNReal.ofReal (CE * (w/r)) := by
    have he : (fun ω => ((1/2 : ℝ) • ∑ j, (phi j ω • ((a ω).mulVec (H j ω)) -
        (Sig j ω).mulVec (H j ω) + Du ω j • F j ω)) k) =
      fun ω => (1/2 : ℝ) * ∑ j, (phi j ω * ∑ m, a ω k m * H j ω m -
        (∑ m, Sig j ω k m * H j ω m) + Du ω j * F j ω k) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Matrix.mulVec, dotProduct]
    rw [he]
    have h := eLpNorm_bounded_mul_le (by norm_num : (0:ℝ) ≤ 1) (ae_of_all μ (fun _ => show |(1/2:ℝ)| ≤ 1 by norm_num)) (herror k)
    simpa only [one_mul] using h
  have hWnorm := eLpNorm_euclideanNorm_le_of_coordinate_bounds μ (by linarith : 2 ≤ 2*p)
    (mul_nonneg hCE (div_nonneg hw0 (by linarith))) hWm hWcoord
  have hscalar := scalarCorrected_error_scalar_coordinate μ hp hr hw.1 hA hB hL
    (fun _ m ω => a ω m i) (fun j m ω => Sig j ω i m) phi (fun j ω => Du ω j)
    (fun j m ω => H j ω m) (fun j ω => F j ω i)
    (fun _ m => ham' m i) (fun j m => hpm j i m) hphi hdm hhm (fun j => hfm j i)
    (hab.mono fun ω hω j m => hω m i) (fun j m => hSigb j i m) hphib hDub hHb (fun j => hFb j i)
  have hh : eLpNorm (fun ω => ∑ j, (phi j ω * dot ((a ω).mulVec (unitVector i)) (H j ω) -
      (Sig j ω).mulVec (H j ω) i + Du ω j * F j ω i)) (ENNReal.ofReal (2*p)) μ ≤ ENNReal.ofReal (CE * (w/r)) := by
    simpa [dot, Matrix.mulVec, dotProduct, unitVector, Pi.single_apply] using hscalar
  have hCV₁ : CV ≤ C₁ := by
    dsimp [C₁]
    nlinarith [mul_nonneg (Real.sqrt_nonneg (d:ℝ)) (add_nonneg hCP hCV)]
  have hCP₁ : Real.sqrt d * CP ≤ C₁ := by dsimp [C₁]; nlinarith [mul_nonneg (Real.sqrt_nonneg (d:ℝ)) hCV]
  have hCG₁ : Real.sqrt d * CV ≤ C₁ := by dsimp [C₁]; nlinarith [mul_nonneg (Real.sqrt_nonneg (d:ℝ)) hCP]
  have hCE₂ : CE ≤ C₂ := by dsimp [C₂]; nlinarith [mul_nonneg (Real.sqrt_nonneg (d:ℝ)) hCE]
  have hWE₂ : Real.sqrt d * CE ≤ C₂ := by dsimp [C₂]; nlinarith
  refine ⟨hfun.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCV₁ (by positivity))),
    hPnorm.trans (ENNReal.ofReal_le_ofReal ?_),
    hgradnorm.trans (ENNReal.ofReal_le_ofReal hCG₁),
    hWnorm.trans (ENNReal.ofReal_le_ofReal ?_),
    hh.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCE₂ (by positivity)))⟩
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCP₁ (show 0 ≤ r+w by positivity)
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hWE₂ (show 0 ≤ w/r by positivity)

end EinsteinRelation.Correctors
