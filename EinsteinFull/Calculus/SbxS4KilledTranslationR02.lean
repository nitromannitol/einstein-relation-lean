import EinsteinFull.Work.W1.GMPKilledEndpointSupport
import EinsteinFull.Calculus.SbxS2RegularPathTranslationR01
import EinsteinFull.Calculus.U6BoundedPhysicalResolvent
import EinsteinFull.Calculus.C8FoundationGMPAssociation
import EinsteinFull.Calculus.U6RegularSignedPathRealization
import EinsteinFull.Calculus.CLMarkovRestart
import EinsteinFull.Calculus.U8RegularExitTails

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support

/-- Strict survival in a translated open set is transported by path translation. -/
theorem s4_survival_translate {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (z : Vec d) (t : ℝ≥0) (γ : Path d) :
    (t : ℝ≥0∞) < localityExitTime ((fun x : Vec d => x + z) ⁻¹' U) (translatePath (-z) γ) ↔
      (t : ℝ≥0∞) < localityExitTime U γ := by
  have hV : IsOpen ((fun x : Vec d => x + z) ⁻¹' U) := hU.preimage (continuous_id.add continuous_const)
  rw [lt_localityExitTime_iff _ hV, lt_localityExitTime_iff U hU]
  have hc (v : Vec d) : -z + v + z = v := by abel
  simp only [translatePath_apply, Set.mem_preimage, hc]

/-- Translating a path law transports its killed endpoint measure. This is
conditional on the full path-law identity, not merely one-time marginals. -/
theorem s4_killed_row_of_path_translation {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (z : Vec d) (t : ℝ≥0) (P : Measure (Path d)) :
    ((P.map (translatePath (-z))).restrict
      {γ | (t : ℝ≥0∞) < localityExitTime ((fun x : Vec d => x + z) ⁻¹' U) γ}).map
        (pathPosition t) =
    (P.restrict {γ | (t : ℝ≥0∞) < localityExitTime U γ}).map
      (fun x : Path d => x t - z) := by
  have hV : IsOpen ((fun x : Vec d => x + z) ⁻¹' U) :=
    hU.preimage (continuous_id.add continuous_const)
  have hpre : translatePath (-z) ⁻¹'
      {γ | (t : ℝ≥0∞) < localityExitTime ((fun x : Vec d => x + z) ⁻¹' U) γ} =
      {γ | (t : ℝ≥0∞) < localityExitTime U γ} := by
    ext γ
    exact s4_survival_translate U hU z t γ
  rw [Measure.restrict_map (measurable_translatePath _) (measurableSet_localitySurvival _ hV t),
    Measure.map_map (measurable_pathPosition t) (measurable_translatePath _), hpre]
  congr 1
  funext γ
  simp only [Function.comp_apply, translatePath_apply, pathPosition, sub_eq_add_neg, add_comm]

/-- Actual killed endpoint rows are covariant under spatial translation for
supplied regular GMP realizations. -/
theorem s4_supplied_killed_endpoint_translation {d : ℕ} (hd : 2 ≤ d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (z : Vec d)
    (hωz : IsRegular Λ (translate z ω))
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (S : GantertFixedEnvironmentRealization hd Λ hΛ (translate z ω) hωz lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (x : Vec d) :
    gmpKilledEndpointKernel S ((fun y : Vec d => y + z) ⁻¹' U)
        (hU.preimage (continuous_id.add continuous_const)) t x =
      (gmpKilledEndpointKernel R U hU t (x + z)).map (fun y => y - z) := by
  have hR := funext (u6_arbitrary_supplied_gmp_transition_eq hd ω lam Λ hΛ hω h0 h1 R)
  have hS := funext (u6_arbitrary_supplied_gmp_transition_eq hd (translate z ω) lam Λ hΛ hωz h0 h1 S)
  have hp := s2_regular_realization_path_translation hd Λ hΛ ω hω lam h0 h1 z hωz R S hR hS x
  have he : (Regeneration.recenterPathEquiv z : Path d → Path d) = translatePath (-z) := by
    funext γ
    ext t i
    simp [Regeneration.recenterPathEquiv, translatePath, sub_eq_add_neg, add_comm]
  rw [he] at hp
  rw [gmpKilledEndpointKernel_apply, gmpKilledEndpointKernel_apply, hp,
    s4_killed_row_of_path_translation U hU z t]
  have hm : Measurable (fun y : Vec d => y - z) := (continuous_id.sub continuous_const).measurable
  rw [Measure.map_map hm (measurable_pathPosition t)]
  rfl


/-- Signed regular continuous-path realizations with the physical finite-time
laws transform covariantly at every starting point. -/
@[nolint unusedArguments]
theorem s4_signed_path_translation {d : ℕ} (hd : 2 ≤ d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam : ℝ) (z : Vec d) (hωz : IsRegular Λ (translate z ω))
    (K L : Kernel (Vec d) (Path d)) [IsMarkovKernel K] [IsMarkovKernel L]
    (hK : ∀ I : Finset ℝ≥0, K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
      MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (hL : ∀ I : Finset ℝ≥0, L.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
      MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
        (u2RegularC0KernelSemigroup hd (translate z ω) lam Λ hΛ hωz) I) :
    ∀ x, L x = (K (x + z)).map (translatePath (-z)) := by
  obtain ⟨hreg, hcov⟩ := u2_regular_signed_kernel_translation_covariance hd ω lam Λ hΛ hω z
  let A := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let B := u2RegularC0KernelSemigroup hd (translate z ω) lam Λ hΛ hωz
  let e : Vec d → Vec d := fun x => x - z
  have hrel : ∀ t x, B t (e x) = (A t x).map e := by
    intro t x
    simpa [A, B, e, sub_add_cancel] using hcov t (x - z)
  have hA : A.IsConservative := u2_regular_kernel_conservative hd _ lam _ _ hω
  have hB : B.IsConservative := u2_regular_kernel_conservative hd _ lam _ _ hωz
  let p := Regeneration.recenterPathEquiv z
  let M := (K.comap (fun x : Vec d => z + x)
    (measurable_const.add measurable_id)).map p
  haveI : IsMarkovKernel M := by
    dsimp [M]
    exact Kernel.IsMarkovKernel.map _ p.measurable
  have heq : M = L := by
    apply MarkovProcess.Kernel.eq_of_map_denseFiniteEvaluation_eq
    intro I
    ext x s hs
    let J := MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet I
    have hfdd := congrArg (fun F : Kernel (Vec d) (J → Vec d) => F (z + x)) (hK J)
    have htarget := congrArg (fun F : Kernel (Vec d) (J → Vec d) => F x) (hL J)
    have he : Measurable e := (continuous_id.sub continuous_const).measurable
    have htransport := Blueprint.gmpFiniteSetKernel_apply_embed A B hA hB he hrel J (z + x)
    have hmap : (MarkovProcess.ContinuousPath.finsetEvaluation J ∘ p) =
        Blueprint.gmpCoordMap e ∘ MarkovProcess.ContinuousPath.finsetEvaluation J := rfl
    rw [Kernel.map_apply _ (MarkovProcess.ContinuousPath.measurable_finsetEvaluation J),
      Kernel.map_apply _ (MarkovProcess.ContinuousPath.measurable_finsetEvaluation J)]
    change (M x).map (MarkovProcess.ContinuousPath.finsetEvaluation J) s = _
    rw [show M x = (K (z + x)).map p by
      simp only [M, Kernel.map_apply _ p.measurable, Kernel.comap_apply],
      Measure.map_map (MarkovProcess.ContinuousPath.measurable_finsetEvaluation J) p.measurable, hmap,
      ← Measure.map_map (Blueprint.measurable_gmpCoordMap he)
        (MarkovProcess.ContinuousPath.measurable_finsetEvaluation J),
      ← Kernel.map_apply _ (MarkovProcess.ContinuousPath.measurable_finsetEvaluation J),
      hfdd, ← htransport]
    rw [Kernel.map_apply _ (MarkovProcess.ContinuousPath.measurable_finsetEvaluation J)] at htarget
    simpa [B, e] using congrArg (fun μ => μ s) htarget.symm
  intro x
  have hp : (p : Path d → Path d) = translatePath (-z) := by
    funext γ
    ext t i
    simp [p, Regeneration.recenterPathEquiv, translatePath, sub_eq_add_neg, add_comm]
  have hx := congrArg (fun N : Kernel (Vec d) (Path d) => N x) heq
  change (K.comap (fun x : Vec d => z + x) (measurable_const.add measurable_id)).map p x = L x at hx
  rw [Kernel.map_apply _ p.measurable, Kernel.comap_apply, hp] at hx
  simpa [add_comm] using hx.symm


/-- A continuous-path realization of the regular physical semigroup for any signed force. -/
noncomputable def s4SignedRegularPathLaw {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    Kernel (Vec d) (Path d) :=
  Classical.choose (u6_regular_signed_continuous_kernel_exists hd ω lam Λ hΛ hω)

theorem s4_signed_regular_pathLaw_markov {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    IsMarkovKernel (s4SignedRegularPathLaw hd ω lam Λ hΛ hω) :=
  (Classical.choose_spec (u6_regular_signed_continuous_kernel_exists hd ω lam Λ hΛ hω)).1

theorem s4_signed_regular_pathLaw_fdd {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (I : Finset ℝ≥0) :
    (s4SignedRegularPathLaw hd ω lam Λ hΛ hω).map
      (MarkovProcess.ContinuousPath.finsetEvaluation I) =
      MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I :=
  (Classical.choose_spec (u6_regular_signed_continuous_kernel_exists hd ω lam Λ hΛ hω)).2 I

/-- Killed endpoint measures for the signed regular physical path realization
are carried by translation, for every open domain. -/
theorem s4_signed_killed_endpoint_translation {d : ℕ} (hd : 2 ≤ d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam : ℝ) (z : Vec d) (hωz : IsRegular Λ (translate z ω))
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (x : Vec d) :
    (((s4SignedRegularPathLaw hd (translate z ω) lam Λ hΛ hωz) x).restrict
      {γ | (t : ℝ≥0∞) < localityExitTime ((fun y : Vec d => y + z) ⁻¹' U) γ}).map
        (pathPosition t) =
    (((s4SignedRegularPathLaw hd ω lam Λ hΛ hω) (x + z)).restrict
      {γ | (t : ℝ≥0∞) < localityExitTime U γ}).map (fun γ => γ t - z) := by
  let K := s4SignedRegularPathLaw hd ω lam Λ hΛ hω
  let L := s4SignedRegularPathLaw hd (translate z ω) lam Λ hΛ hωz
  letI : IsMarkovKernel K := s4_signed_regular_pathLaw_markov hd ω lam Λ hΛ hω
  letI : IsMarkovKernel L := s4_signed_regular_pathLaw_markov hd (translate z ω) lam Λ hΛ hωz
  have hp := s4_signed_path_translation hd Λ hΛ ω hω lam z hωz K L
    (s4_signed_regular_pathLaw_fdd hd ω lam Λ hΛ hω)
    (s4_signed_regular_pathLaw_fdd hd (translate z ω) lam Λ hΛ hωz) x
  change ((L x).restrict _).map _ = _
  rw [hp]
  exact s4_killed_row_of_path_translation U hU z t (K (x + z))


/-- Integral form of signed killed endpoint translation for nonnegative observables. -/
theorem s4_signed_killed_endpoint_lintegral_translation {d : ℕ} (hd : 2 ≤ d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam : ℝ) (z : Vec d) (hωz : IsRegular Λ (translate z ω))
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (x : Vec d)
    (f : Vec d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ γ, f (γ t) ∂(((s4SignedRegularPathLaw hd (translate z ω) lam Λ hΛ hωz) x).restrict
      {γ | (t : ℝ≥0∞) < localityExitTime ((fun y : Vec d => y + z) ⁻¹' U) γ})) =
    ∫⁻ γ, f (γ t - z) ∂(((s4SignedRegularPathLaw hd ω lam Λ hΛ hω) (x + z)).restrict
      {γ | (t : ℝ≥0∞) < localityExitTime U γ}) := by
  have hm : Measurable (fun γ : Path d => γ t - z) :=
    (measurable_pathPosition t).sub measurable_const
  change (∫⁻ γ, f (pathPosition t γ) ∂_) = _
  rw [← lintegral_map hf (measurable_pathPosition t),
    s4_signed_killed_endpoint_translation hd Λ hΛ ω hω lam z hωz U hU t x,
    lintegral_map hf hm]

end EinsteinFull
