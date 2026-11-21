import EinsteinFull.Blueprint.G1.Proofs.SbxS1SplitGridFreshBits
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS10BridgeIntegrability
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.G1.Proofs.SbxS1SplitGridFreshBits`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.SbxS1SplitGridFreshBits
open EinsteinRelation EinsteinRelation.Regeneration EinsteinFull.SbxS10BridgeIntegrability
/-- The physical-kernel version of
`EinsteinFull.SbxS1SplitGridFreshBits.extended_splitGrid_marginals_and_freshBits`. -/
theorem extended_splitGrid_marginals_and_freshBits_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (hGMP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P ∧ HasFreshBits Q.measure Δ δ K := by
  exact ⟨(extended_splitGridCoupledLawKernel_marginals_phys hd hΛ₀ Q lam h0 h1 Δ hΔ R δ i hR P hGMP G hG hGae hP hminor hδ₁ hstart).1,
    (extended_splitGridCoupledLawKernel_marginals_phys hd hΛ₀ Q lam h0 h1 Δ hΔ R δ i hR P hGMP G hG hGae hP hminor hδ₁ hstart).2,
    extended_splitGrid_freshBits Q Δ hΔ R δ i hR P G hG hGae hP hminor hδ₀ hδ₁ hstart⟩

/-- The physical-kernel version of
`EinsteinFull.SbxS1SplitGridFreshBits.extended_splitGrid_accumulated`. -/
theorem extended_splitGrid_accumulated_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (hGMP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P ∧
      HasFreshBits Q.measure Δ δ K ∧ HasSuccessfulBridgeSupport Q.measure Δ i R K ∧
      HasUniformSuccessfulEndpoint Q.measure Δ δ R i K := by
  exact ⟨(extended_splitGrid_marginals_and_freshBits_phys hd hΛ₀ Q lam h0 h1 Δ hΔ R δ i hR
      P hGMP G hG hGae hP hminor hδ₀ hδ₁ hstart).1,
    (extended_splitGrid_marginals_and_freshBits_phys hd hΛ₀ Q lam h0 h1 Δ hΔ R δ i hR
      P hGMP G hG hGae hP hminor hδ₀ hδ₁ hstart).2.1,
    (extended_splitGrid_marginals_and_freshBits_phys hd hΛ₀ Q lam h0 h1 Δ hΔ R δ i hR
      P hGMP G hG hGae hP hminor hδ₀ hδ₁ hstart).2.2,
    extended_splitGrid_success_support Q Δ hΔ R δ i hR P G hG hGae hP hminor hδ₁ hstart,
    extended_splitGrid_uniform_successful_endpoint Q Δ hΔ R δ i hR P G hG hGae hP hminor
      hδ₀ hδ₁ hstart⟩

/-- The physical-kernel version of
`EinsteinFull.SbxS1SplitGridFreshBits.extended_splitGrid_accumulated_with_restart`. -/
theorem extended_splitGrid_accumulated_with_restart_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (hGMP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    (HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P ∧
      HasFreshBits Q.measure Δ δ K ∧ HasSuccessfulBridgeSupport Q.measure Δ i R K ∧
      HasUniformSuccessfulEndpoint Q.measure Δ δ R i K) ∧
      HasDeterministicRestart Q.measure Δ K := by
  exact ⟨extended_splitGrid_accumulated_phys hd hΛ₀ Q lam h0 h1 Δ hΔ R δ i hR P hGMP
      G hG hGae hP hminor hδ₀ hδ₁ hstart,
    extended_splitGrid_restart Q Δ hΔ R δ i hR P G hG hGae hP hminor hδ₁ hstart⟩

/-- The physical-kernel version of
`EinsteinFull.SbxS1SplitGridFreshBits.extended_splitGrid_isGMPCouplingV2`. -/
theorem extended_splitGrid_isGMPCouplingV2_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hΔ : 0 < Renewal.regenDelta lam) (hR : 0 < l / lam)
    (P : QuenchedPathLaws d) (hGMP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d))
          (endpointBall (Renewal.forceCoord hd) (l / lam) x) ≤
        (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (l / lam) (Renewal.forceCoord hd) P x ω).map
          (fun γ : Path d => γ (Renewal.regenDelta lam)))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel (Renewal.regenDelta lam) hΔ (l / lam) δ (Renewal.forceCoord hd)
        hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    Renewal.IsGMPCouplingV2Phys hd hΛ₀ Q lam l δ h0 h1 P K := by
  have hf := extended_splitGrid_accumulated_with_restart_phys hd hΛ₀ Q lam h0 h1
    (Renewal.regenDelta lam) hΔ (l / lam) δ (Renewal.forceCoord hd) hR P hGMP
    G hG hGae hP hminor hδ₀ hδ₁ hstart
  have hi := extended_splitGrid_oneInterval Q (Renewal.regenDelta lam) hΔ (l / lam) δ
    (Renewal.forceCoord hd) hR P G hG hGae hP hminor hδ₀ hδ₁ hstart
  exact ⟨hf.1.1, hf.1.2.1, hGMP, hf.1.2.2.1, hf.2,
    hf.1.2.2.2.1, hf.1.2.2.2.2, hi⟩

/-- The physical-kernel version of
`EinsteinFull.SbxS1SplitGridFreshBits.exists_markov_splitGrid_isGMPCouplingV2`. -/
theorem exists_markov_splitGrid_isGMPCouplingV2_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (hlam : 0 < lam) (h1 : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (hGMP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam hlam.le h1 P)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d))
          (endpointBall (Renewal.forceCoord hd) (l / lam) x) ≤
        (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (l / lam) (Renewal.forceCoord hd) P x ω).map
          (fun γ : Path d => γ (Renewal.regenDelta lam)))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    ∃ K : Kernel (Vec d × FieldPair d) (CoupledSample d),
      IsMarkovKernel K ∧ Renewal.IsGMPCouplingV2Phys hd hΛ₀ Q lam l δ hlam.le h1 P K := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hlam))
  have hR : 0 < l / lam := div_pos hl hlam
  let S := splitGridCoupledLawKernel (Renewal.regenDelta lam) hΔ (l / lam) δ
    (Renewal.forceCoord hd) hR P G hP hminor hδ₁
  let ν : Measure (CoupledSample d) := Measure.dirac ((0 : Path d), fun _ => false)
  let K := extendEnvironmentKernel G hG S ν
  let : IsMarkovKernel S := isMarkovKernel_splitGridCoupledLawKernel
    (Renewal.regenDelta lam) hΔ (l / lam) δ (Renewal.forceCoord hd) hR P G hP hminor hδ₁
  refine ⟨K, isMarkovKernel_extendEnvironmentKernel G hG S ν, ?_⟩
  exact extended_splitGrid_isGMPCouplingV2_phys hd hΛ₀ Q lam l δ hlam.le h1 hΔ hR P hGMP
    G hG hGae hP hminor hδ₀ hδ₁ hstart

end EinsteinFull.SbxS1SplitGridFreshBits
