import EinsteinFull.Calculus.U2RegularKernelCovariance
import EinsteinFull.Blueprint.G1.Proofs.SbxS5CouplingAnalyticRecenter
import EinsteinFull.Calculus.C8FoundationGMPAssociation
import MarkovProcess.Main

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration EinsteinRelation.Regeneration.Renewal
open EinsteinRelation.External.GantertSection7Support

/-- Conditional all-start covariance for the supplied path laws. -/
theorem c6_s3_all_start_recenter_of_requested_identification
    (requested_s3_supplied_gantert_c0_fdd : ∀ {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ)
      (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
      (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
      (I : Finset ℝ≥0),
      r.pathLaw.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ),
      0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
      ∀ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCoupling hd Q lam l δ h0.le h1 P K →
      ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ᵐ η ∂Q.measure,
        ∀ x : Vec d, P (x, η) = sbxS9RecenteredPathLaws P a (x, η) := by
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl hr hδ hδ1 P K hK
  have hgmp : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0.le h1 P := hK.2.2.1
  filter_upwards with a
  have hshift : ∀ᵐ η ∂Q.measure,
      ∃ hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair (translate (-a) η)),
        ∃ r : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
          (one_le_sourceReducedBound Q.ellipticity_parameter)
          (zeroPotentialReducedPair (translate (-a) η)) hω lam h0.le h1,
          ∀ x, P (x, translate (-a) η) = r.pathLaw x := by
    exact (show MeasurePreserving (translate (-a)) Q.measure Q.measure from
      ⟨EinsteinRelation.Probability.measurable_translate (-a), Q.stationary (-a)⟩).quasiMeasurePreserving.ae hgmp
  filter_upwards [hgmp, hshift] with η hη hs
  obtain ⟨hηreg, rη, hrη⟩ := hη
  obtain ⟨hsreg, rs, hrs⟩ := hs
  have htrans (b : Vec d) (ω : FieldPair d) :
      zeroPotentialReducedPair (translate b ω) = translate b (zeroPotentialReducedPair ω) := by
    unfold zeroPotentialReducedPair
    rw [reduce_translate]
    rfl
  have hpair : translate a (zeroPotentialReducedPair (translate (-a) η)) =
      zeroPotentialReducedPair η := by
    rw [← htrans, translate_add, add_neg_cancel, translate_zero]
  obtain ⟨hreg, hcov⟩ := u2_regular_signed_kernel_translation_covariance hd
    (zeroPotentialReducedPair (translate (-a) η)) lam (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) hsreg a
  let A := u2RegularC0KernelSemigroup hd (zeroPotentialReducedPair (translate (-a) η))
    lam (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter) hsreg
  let B := u2RegularC0KernelSemigroup hd (zeroPotentialReducedPair η)
    lam (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter) hηreg
  let e : Vec d → Vec d := fun x => x - a
  have hrel : ∀ t x, B t (e x) = (A t x).map e := by
    intro t x
    simpa [A, B, e, hpair, sub_add_cancel] using hcov t (x - a)
  have hA : A.IsConservative := u2_regular_kernel_conservative hd _ lam _ _ hsreg
  have hB : B.IsConservative := u2_regular_kernel_conservative hd _ lam _ _ hηreg
  let L := (rs.pathLaw.comap (fun x : Vec d => a + x)
    (measurable_const.add measurable_id)).map (recenterPathEquiv a)
  haveI := rs.pathLaw_isMarkovKernel
  haveI : IsMarkovKernel L := by
    dsimp [L]
    exact Kernel.IsMarkovKernel.map _ (recenterPathEquiv a).measurable
  have heq : L = rη.pathLaw := by
    apply MarkovProcess.Kernel.eq_of_map_denseFiniteEvaluation_eq
    intro I
    ext x s hs
    let J := MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet I
    have hfdd := congrArg (fun F : Kernel (Vec d) (J → Vec d) => F (a + x))
      (requested_s3_supplied_gantert_c0_fdd hd _ _ _ _ lam h0.le h1 rs J)
    have htarget := congrArg (fun F : Kernel (Vec d) (J → Vec d) => F x)
      (requested_s3_supplied_gantert_c0_fdd hd _ _ _ _ lam h0.le h1 rη J)
    have he : Measurable e := (continuous_id.sub continuous_const).measurable
    have htransport := gmpFiniteSetKernel_apply_embed A B hA hB
      he hrel J (a + x)
    have hmap : (MarkovProcess.ContinuousPath.finsetEvaluation J ∘ recenterPathEquiv a) =
        gmpCoordMap e ∘ MarkovProcess.ContinuousPath.finsetEvaluation J := rfl
    rw [Kernel.map_apply _ (MarkovProcess.ContinuousPath.measurable_finsetEvaluation J),
      Kernel.map_apply _ (MarkovProcess.ContinuousPath.measurable_finsetEvaluation J)]
    change (L x).map (MarkovProcess.ContinuousPath.finsetEvaluation J) s = _
    rw [show L x = (rs.pathLaw (a + x)).map (recenterPathEquiv a) by
      simp only [L, Kernel.map_apply _ (recenterPathEquiv a).measurable, Kernel.comap_apply],
      Measure.map_map (MarkovProcess.ContinuousPath.measurable_finsetEvaluation J)
        (recenterPathEquiv a).measurable, hmap,
      ← Measure.map_map (measurable_gmpCoordMap he)
        (MarkovProcess.ContinuousPath.measurable_finsetEvaluation J),
      ← Kernel.map_apply _ (MarkovProcess.ContinuousPath.measurable_finsetEvaluation J),
      hfdd, ← htransport]
    rw [Kernel.map_apply _ (MarkovProcess.ContinuousPath.measurable_finsetEvaluation J)] at htarget
    simpa [B, e] using congrArg (fun μ => μ s) htarget.symm
  intro x
  rw [sbxS5_analyticRecenterPaths_apply, hrη x, hrs (a + x)]
  have heval := congrArg (fun M : Kernel (Vec d) (Path d) => M x) heq
  simpa [L, Kernel.map_apply _ (recenterPathEquiv a).measurable,
    Kernel.comap_apply] using heval.symm

/-- Conditional origin covariance for the supplied path laws. -/
theorem c6_s3_origin_recenter_of_requested_identification
    (requested_s3_supplied_gantert_c0_fdd : ∀ {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ)
      (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
      (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
      (I : Finset ℝ≥0),
      r.pathLaw.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ),
      0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
      ∀ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCoupling hd Q lam l δ h0.le h1 P K →
      ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ᵐ η ∂Q.measure,
        P (0, η) = sbxS9RecenteredPathLaws P a (0, η) := by
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl hr hδ hδ1 P K hK
  filter_upwards [c6_s3_all_start_recenter_of_requested_identification
    requested_s3_supplied_gantert_c0_fdd d hd Λ₀ r₀ Q lam h0 h1 l δ hl hr hδ hδ1 P K hK] with a ha
  filter_upwards [ha] with η hη
  exact hη 0

end EinsteinFull.Blueprint
