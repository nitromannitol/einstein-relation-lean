import EinsteinFull.Homogenization.SourceCorrectorHighContrast
import EinsteinFull.Homogenization.LinearWeakGradient
import EinsteinFull.Homogenization.NormalizedBallNorms
import EinsteinRelation.Correctors.AKMLocalCanonicalIdentificationSublinearity
import HCPoly.Provider.Regularity.CorrectorNormalizedL2Bridge
import HCPoly.Provider.PolynomialHomogenization.Root.Corrector.AffineLiouvilleGrowth

/-!
# Dilated source correctors in the Liouville class

The corrected affine function `x ↦ e·x + φ(2x)/2` of a source corrector of Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*, Definitions
3.14–3.15, lies in the Liouville class `𝒜_{1,ϑ}` of the dilated coefficient in the sense of
Armstrong, Kuusi and Loher, *Homogenization at a polynomial scale in high contrast*: it is in
`H¹_{s,loc}`, solves the equation, and grows at most linearly because the source corrector is
sublinear.
-/

open MeasureTheory Filter Topology
open scoped Pointwise

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport
  EinsteinRelation.External.AKM
open _root_.Homogenization hiding euclideanBall Vec Mat
open _root_.Homogenization.HighContrast

variable {d : ℕ}

/-- The corrected affine function of a dilated potential, `x ↦ e·x + u(2x)/2`. -/
noncomputable def dilatedCorrectedAffine (e : Vec d) (u : Vec d → ℝ) (x : Vec d) : ℝ :=
  vecDot e x + dilatedPotential u x

theorem locallyIntegrable_of_hasWeakGradient {u : Vec d → ℝ} {g : Vec d → Vec d}
    [NeZero d] (h : HasWeakGradient Set.univ u g) : LocallyIntegrable u volume := by
  have := (h 0).1
  rwa [locallyIntegrableOn_univ] at this

theorem locallyIntegrable_dilatedPotential [NeZero d] {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : HasWeakGradient Set.univ u g) : LocallyIntegrable (dilatedPotential u) volume := by
  have hu := locallyIntegrable_of_hasWeakGradient h
  have hcomp : LocallyIntegrable (fun x : Vec d => u ((2 : ℝ) • x)) volume := by
    rw [locallyIntegrable_iff]
    intro k hk
    have hk2 : IsCompact ((2 : ℝ) • k) := hk.smul (2 : ℝ)
    have hint := (locallyIntegrable_iff.mp hu) _ hk2
    have hmem : MemLp u 1 (volume.restrict ((2 : ℝ) • k)) := memLp_one_iff_integrable.mpr hint
    exact memLp_one_iff_integrable.mp
      (MemLp.comp_smul_restrict two_ne_zero hk.measurableSet hmem)
  have h := hcomp.smul ((2 : ℝ)⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [dilatedPotential, smul_eq_mul]

/-- The corrected affine function of a dilated potential has the corrected weak gradient. -/
theorem hasWeakGradientOn_dilatedCorrectedAffine [NeZero d] (e : Vec d) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (h : HasWeakGradient Set.univ u g) :
    HasWeakGradientOn Set.univ (dilatedCorrectedAffine e u)
      (fun x => e + dilatedGradient g x) := by
  intro i χ hχ hcs hsub
  have haff := HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := i)
    (contDiff_vecDot_left e) χ hχ hcs hsub
  have hpot := hasWeakGradientOn_dilated h i χ hχ hcs hsub
  simp only [fderiv_vecDot_left_apply] at haff
  simp only [Measure.restrict_univ] at haff hpot ⊢
  have hχc : Continuous χ := hχ.continuous
  have hdχc : Continuous (fun x => fderiv ℝ χ x (basisVec i)) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdχs : HasCompactSupport (fun x => fderiv ℝ χ x (basisVec i)) :=
    hcs.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hi1 : Integrable (fun x => vecDot e x * fderiv ℝ χ x (basisVec i)) :=
    ((contDiff_vecDot_left e).continuous.mul hdχc).integrable_of_hasCompactSupport
      hdχs.mul_left
  have hi2 : Integrable (fun x => dilatedPotential u x * fderiv ℝ χ x (basisVec i)) := by
    have := (locallyIntegrable_dilatedPotential h).integrable_smul_right_of_hasCompactSupport
      hdχc hdχs
    simpa [smul_eq_mul, mul_comm] using this
  have hi3 : Integrable (fun x => e i * χ x) :=
    (continuous_const.mul hχc).integrable_of_hasCompactSupport hcs.mul_left
  have hi4 : Integrable (fun x => dilatedGradient g x i * χ x) := by
    have hg : LocallyIntegrable (fun x => g x i) volume := by
      have := (h i).2.1
      rwa [locallyIntegrableOn_univ] at this
    have hcomp : LocallyIntegrable (fun x : Vec d => g ((2 : ℝ) • x) i) volume := by
      rw [locallyIntegrable_iff]
      intro k hk
      have hk2 : IsCompact ((2 : ℝ) • k) := hk.smul (2 : ℝ)
      have hmem : MemLp (fun x => g x i) 1 (volume.restrict ((2 : ℝ) • k)) :=
        memLp_one_iff_integrable.mpr ((locallyIntegrable_iff.mp hg) _ hk2)
      exact memLp_one_iff_integrable.mp
        (MemLp.comp_smul_restrict two_ne_zero hk.measurableSet hmem)
    have := hcomp.integrable_smul_right_of_hasCompactSupport hχc hcs
    simpa [dilatedGradient, smul_eq_mul, mul_comm] using this
  calc ∫ x, dilatedCorrectedAffine e u x * fderiv ℝ χ x (basisVec i)
      = ∫ x, (vecDot e x * fderiv ℝ χ x (basisVec i) +
          dilatedPotential u x * fderiv ℝ χ x (basisVec i)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [dilatedCorrectedAffine]
        ring
    _ = -∫ x, (e i * χ x + dilatedGradient g x i * χ x) := by
        rw [integral_add hi1 hi2, haff, hpot, integral_add hi3 hi4]
        ring
    _ = -∫ x, (e + dilatedGradient g x) i * χ x := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Pi.add_apply]
        ring

/-- Linear growth of the corrected affine function of a dilated sublinear potential. -/
theorem tendsto_growth_dilatedCorrectedAffine (e : Vec d) {u : Vec d → ℝ}
    (hu2 : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (huae : AEStronglyMeasurable u volume)
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R, u x ^ 2)) atTop (𝓝 0))
    {ϑ : ℝ} (hϑ : 0 < ϑ) :
    Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + ϑ))) *
      normalizedL2Norm (euclideanBall d r) (dilatedCorrectedAffine e u)) atTop (𝓝 0) := by
  obtain ⟨q, A, hq, hA, hdil⟩ := exists_normalizedL2Norm_dilate_le (d := d)
  let ε : ℝ → ℝ := fun R => R⁻¹ * Real.sqrt (⨍ x in ball 0 R, u x ^ 2)
  let c₁ : ℝ := Real.sqrt (vecNormSq e)
  have hεq : Tendsto (fun r : ℝ => ε (q * r)) atTop (𝓝 0) :=
    hsub.comp (tendsto_id.const_mul_atTop hq)
  have hpow : Tendsto (fun r : ℝ => r ^ (-ϑ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hϑ
  have hreal : Tendsto (fun r : ℝ => r ^ (-ϑ) * (c₁ + 2⁻¹ * A * q * ε (q * r)))
      atTop (𝓝 0) := by
    have h := hpow.mul ((tendsto_const_nhds (x := c₁)).add
      ((tendsto_const_nhds (x := 2⁻¹ * A * q)).mul hεq))
    simpa only [zero_mul, mul_zero, add_zero] using h
  have hbound : ∀ᶠ r : ℝ in atTop, ENNReal.ofReal (r ^ (-(1 + ϑ))) *
      normalizedL2Norm (euclideanBall d r) (dilatedCorrectedAffine e u) ≤
      ENNReal.ofReal (r ^ (-ϑ) * (c₁ + 2⁻¹ * A * q * ε (q * r))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hqr : 0 < q * r := mul_pos hq hr
    have hmeasA : AEStronglyMeasurable (fun x : Vec d => vecDot e x)
        (volume.restrict (euclideanBall d r)) :=
      (contDiff_vecDot_left e).continuous.aestronglyMeasurable
    have hmeasP : AEStronglyMeasurable (dilatedPotential u)
        (volume.restrict (euclideanBall d r)) := by
      have h2 : AEStronglyMeasurable (fun x : Vec d => u ((2 : ℝ) • x)) volume :=
        huae.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_smul volume two_ne_zero)
      exact (h2.const_mul _).restrict
    have htri := normalizedL2Norm_add_le hmeasA hmeasP
    have hpotEq : normalizedL2Norm (euclideanBall d r) (dilatedPotential u) =
        ENNReal.ofReal |(2 : ℝ)⁻¹| *
          normalizedL2Norm (euclideanBall d r) (fun x => u ((2 : ℝ) • x)) :=
      normalizedL2Norm_const_mul _ _ _
    have hball := normalizedL2Norm_euclideanBall_eq_ofReal hqr (hu2 _ hqr)
    have hsqrt : Real.sqrt (⨍ x in ball 0 (q * r), u x ^ 2) = q * r * ε (q * r) := by
      simp only [ε]
      field_simp
    have hN : normalizedL2Norm (euclideanBall d r) (dilatedCorrectedAffine e u) ≤
        ENNReal.ofReal (c₁ * r + 2⁻¹ * A * (q * r * ε (q * r))) := by
      have hε0 : 0 ≤ ε (q * r) := by
        simp only [ε]
        exact mul_nonneg (inv_nonneg.mpr hqr.le) (Real.sqrt_nonneg _)
      calc normalizedL2Norm (euclideanBall d r) (dilatedCorrectedAffine e u)
          ≤ normalizedL2Norm (euclideanBall d r) (fun x => vecDot e x) +
              normalizedL2Norm (euclideanBall d r) (dilatedPotential u) := htri
        _ ≤ ENNReal.ofReal (c₁ * r) + ENNReal.ofReal |(2 : ℝ)⁻¹| *
              (ENNReal.ofReal A * ENNReal.ofReal (q * r * ε (q * r))) := by
            rw [hpotEq]
            gcongr
            · exact normalizedL2Norm_vecDot_le hr e
            · rw [← hsqrt, ← hball]
              exact hdil r hr u
        _ = ENNReal.ofReal (c₁ * r + 2⁻¹ * A * (q * r * ε (q * r))) := by
            rw [abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), ← ENNReal.ofReal_mul hA,
              ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
            congr 1
            ring
    calc ENNReal.ofReal (r ^ (-(1 + ϑ))) *
          normalizedL2Norm (euclideanBall d r) (dilatedCorrectedAffine e u)
        ≤ ENNReal.ofReal (r ^ (-(1 + ϑ))) *
            ENNReal.ofReal (c₁ * r + 2⁻¹ * A * (q * r * ε (q * r))) := by gcongr
      _ = ENNReal.ofReal (r ^ (-ϑ) * (c₁ + 2⁻¹ * A * q * ε (q * r))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hsplit : r ^ (-(1 + ϑ)) = r ^ (-ϑ) * r⁻¹ := by
            rw [neg_add, Real.rpow_add hr, Real.rpow_neg_one, mul_comm]
          rw [hsplit]
          field_simp
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-ϑ) * (c₁ + 2⁻¹ * A * q * ε (q * r))))
      atTop (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal hreal)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun _ => zero_le) hbound

end EinsteinFull.Homogenization
