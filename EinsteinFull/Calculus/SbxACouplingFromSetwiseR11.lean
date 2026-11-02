import EinsteinFull.Calculus.SbxASourceSetwiseDensityR05
import EinsteinFull.Calculus.SbxS3CleanKernelPatchingR02
import EinsteinFull.Regeneration.SbxS1JointSplitR01
import EinsteinFull.Frozen.GantertRegenerationTail

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Calculus.SbxACouplingFromSetwiseR11

/-- All-regular setwise domination yields actual couplings with uniform no-return mass. -/
theorem a_uniform_actual_coupling_half_mass_of_setwise
    (hsetwise : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ),
      ∀ l : ℝ, 1 ≤ l → ∃ c : ℝ, 0 < c ∧
      ∀ (Q : EnvironmentLaw d Λ r),
      ∀ (μ : ℝ) (h0 : 0 < μ) (h1 : μ ≤ 1),
        ∃ P : QuenchedPathLaws d,
          IsGMPReducedKernel hd Q.ellipticity_parameter Q μ h0.le h1 P ∧
          ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
            ENNReal.ofReal (c * μ ^ d) •
              (volume : Measure (Vec d)).restrict
                (endpointBall (Renewal.forceCoord hd) (l / μ) x) ≤
            ((P (x, ω)).restrict {γ | ∀ t : ℝ≥0, t ≤ Renewal.regenDelta μ →
              γ t ∈ couplingRegion (Renewal.forceCoord hd) (l / μ) x}).map
                (fun γ => γ (Renewal.regenDelta μ))) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ),
      ∃ L : ℝ, 0 < L ∧ r < 2 * L ∧
      ∀ l : ℝ, L ≤ l → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (D : StructuralData d), D.ellipticity = Λ → D.dependenceRange = r →
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
      ∀ (μ : ℝ) (h0 : 0 < μ) (h1 : μ ≤ 1),
        ∃ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
          IsRegenerationCoupling hd Q μ l δ h0.le h1 P K ∧
          ENNReal.ofReal (1 / 2 : ℝ) ≤ annealedCoupledLaw Q.measure K
            (regenerationNoReturn hd (l / μ)) := by
  classical
  intro d hd Λ r
  obtain ⟨L, hL, hsep, htail'⟩ := EinsteinFull.External.gantert_regeneration_tail d hd Λ r
  refine ⟨max L 1, lt_of_lt_of_le hL (le_max_left _ _), ?_, ?_⟩
  · exact lt_of_lt_of_le hsep (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
  intro l hl
  have hlL : L ≤ l := le_trans (le_max_left _ _) hl
  have hl1 : 1 ≤ l := le_trans (le_max_right _ _) hl
  obtain ⟨c, hc, hbound⟩ := hsetwise d hd Λ r l hl1
  obtain ⟨hδ0, hδ1, hminor⟩ :=
    SbxASourceSetwiseDensityR05.source_minorization_of_rescaled_setwise
      (Renewal.forceCoord hd) l c (lt_of_lt_of_le zero_lt_one hl1) hc
  refine ⟨SbxS14MinorizationVolumeR03.windowCoinCoefficient (Renewal.forceCoord hd) l c,
    hδ0, hδ1, ?_⟩
  obtain ⟨cG, CG, hcG, hCG, hGtail⟩ := htail' l hlL _ hδ0 hδ1
  intro D hΛ hr Q hQ μ h0 h1
  subst Λ
  subst r
  obtain ⟨P, hP, hPbound⟩ := hbound Q μ h0 h1
  have hminP : ∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P (x, ω))
      (Renewal.regenDelta μ)
      (SbxS14MinorizationVolumeR03.windowCoinCoefficient (Renewal.forceCoord hd) l c)
      (l / μ) (Renewal.forceCoord hd) := by
    filter_upwards [hPbound] with ω hω
    exact hminor μ h0 (Renewal.regenDelta μ) (fun x => P (x, ω)) hω
  obtain ⟨P', _, hP', hMarkov, hstart, hmin'⟩ :=
    SbxS3Section3R01.clean_patch_reduced_kernel hd Q μ h0.le h1
      (Renewal.regenDelta μ) _ (l / μ) (Renewal.forceCoord hd) P hP hminP
  letI : IsMarkovKernel P' := hMarkov
  have hΔ := EinsteinRelation.regenDelta_pos h0
  have hR : 0 < l / μ := div_pos (lt_of_lt_of_le zero_lt_one hl1) h0
  let δ := SbxS14MinorizationVolumeR03.windowCoinCoefficient (Renewal.forceCoord hd) l c
  let K := EinsteinFull.Regeneration.splitContinuousCouplingKernel
    (Renewal.regenDelta μ) hΔ δ (l / μ) (Renewal.forceCoord hd) hδ0 hδ1 hR P' hmin'
  have hK : IsRegenerationCoupling hd Q μ l δ h0.le h1 P' K := by
    exact EinsteinFull.Regeneration.s1_canonical_all_clauses
      (Renewal.regenDelta μ) hΔ δ (l / μ) (Renewal.forceCoord hd)
      hδ0 hδ1 hR P' hmin' hstart hd Q h0.le h1 hP'
  refine ⟨P', K, hK, ?_⟩
  exact (hGtail Q μ h0 h1 P' K hK).1

end EinsteinFull.Calculus.SbxACouplingFromSetwiseR11
