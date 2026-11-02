import EinsteinFull.External.AKMSublinearCorrectors
import EinsteinRelation.Correctors.ParabolicUnitScaleGradient
import EinsteinRelation.Correctors.AKMStretchedExponentialMoments

/-! Higher local-energy moments from the actual source random-radius estimate.
This does not assert the canonical smooth-moments node. -/

open MeasureTheory
noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- Every positive real moment of the unit-ball gradient energy follows from
the admitted source estimate, with its law-independent constant. The source
corrector and its unit direction are retained literally. -/
theorem sourceCorrector_unit_gradient_moments
    (d : ℕ) (hd : 2 ≤ d) (K p : ℝ) (hK : 1 < K) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
      ∀ (e : Vec d), euclideanNorm e = 1 → ∀ φ : SourceCorrector P e,
        (∫⁻ a, ENNReal.ofReal ((Real.sqrt
          (⨍ x in ball 0 1, euclideanSq (φ.grad a x))) ^ p) ∂P) ≤
            ENNReal.ofReal C := by
  obtain ⟨β, B, _hβ, hB, hest⟩ := External.akm_sublinear_correctors d hd K hK
  obtain ⟨θ, hθ, hsource⟩ := hest 1 zero_lt_one (by exact_mod_cast hd)
  let m : ℝ := (d : ℝ) / 2 * p
  have hm : 0 < m := mul_pos (div_pos (by exact_mod_cast (by omega : 0 < d))
    (by norm_num)) hp
  refine ⟨B ^ p * (2 * m ^ m * θ ^ m), by positivity, ?_⟩
  intro P hP e he φ
  obtain ⟨hne, hflux⟩ := hsource P hP e he φ
  obtain ⟨S⟩ := hne
  obtain ⟨X, _hXm, htail, hbound⟩ := hflux S
  have hX : ∀ᵐ a ∂P, 0 ≤ X a := hbound.mono fun _ ha => zero_le_one.trans ha.1
  have htail' : StretchedExponentialBound P 1 θ X := by
    simpa only [StretchedExponentialBound, div_eq_mul_inv, mul_comm] using htail.2.2.2
  have hmoment := lintegral_rpow_le_of_stretchedExponential P zero_lt_one hθ hm hX htail'
  simp only [div_one] at hmoment
  have hlocal : ∀ᵐ a ∂P,
      Real.sqrt (⨍ x in ball 0 1, euclideanSq (φ.grad a x)) ≤
        B * X a ^ ((d : ℝ) / 2) := by
    filter_upwards [hbound, φ.locally_square_integrable] with a ha hl
    have hnorm : MemLp (fun x => euclideanNorm (φ.grad a x)) 2
        (volume.restrict (originBall d (X a))) := by
      let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
      have hg := T.toContinuousLinearMap.comp_memLp' (hl (X a)
        (zero_lt_one.trans_le ha.1)).2
      rw [originBall_eq_gt_ball]
      simpa only [TimeChange.euclideanNorm_eq_norm_toLp, Function.comp_def, T,
        ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply] using! hg.norm
    have hunit := vectorRms_unitBall_le ha.1 (φ.grad a) hnorm
    have hlarge := (ha.2 (X a) le_rfl).2
    simp only [vectorRms, originBall_eq_gt_ball] at hunit
    exact hunit.trans (by
      calc
        _ ≤ X a ^ ((d : ℝ) / 2) * B := mul_le_mul_of_nonneg_left hlarge
          (Real.rpow_nonneg (zero_le_one.trans ha.1) _)
        _ = _ := mul_comm _ _)
  calc
    _ ≤ ∫⁻ a, ENNReal.ofReal (B ^ p * X a ^ m) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hlocal, hX] with a ha hx
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (B * X a ^ ((d : ℝ) / 2)) ^ p :=
          Real.rpow_le_rpow (Real.sqrt_nonneg _) ha hp.le
        _ = _ := by rw [Real.mul_rpow hB.le (Real.rpow_nonneg hx _),
          ← Real.rpow_mul hx]
    _ = ENNReal.ofReal (B ^ p) * (∫⁻ a, ENNReal.ofReal (X a ^ m) ∂P) := by
      simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg hB.le _)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (B ^ p) * ENNReal.ofReal (2 * m ^ m * θ ^ m) :=
      mul_le_mul_right hmoment _
    _ = _ := (ENNReal.ofReal_mul (Real.rpow_nonneg hB.le _)).symm

end EinsteinFull
