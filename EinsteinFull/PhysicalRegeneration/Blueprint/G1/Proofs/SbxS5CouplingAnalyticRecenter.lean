import EinsteinFull.Blueprint.G1.Proofs.SbxS5CouplingAnalyticRecenter
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS9CouplingAlgebraRecenter
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.CoupledEnvironmentRegularity
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.G1.Proofs.SbxS5CouplingAnalyticRecenter`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration EinsteinRelation.Regeneration.Renewal
/-- The physical-kernel version of `EinsteinFull.Blueprint.sbxS5_probability_all_starts_of_gmp`. -/
theorem sbxS5_probability_all_starts_of_gmp_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)) := by
  filter_upwards [hP] with ω hω
  obtain ⟨hreg, r, hr⟩ := hω
  intro x
  rw [hr x]
  have := r.pathLaw_isMarkovKernel
  infer_instance

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbxS5_hasOneIntervalKernel_recenter`. -/
theorem sbxS5_hasOneIntervalKernel_recenter_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P)
    (hK : HasOneIntervalKernel Q.measure Δ δ R i P K) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      HasOneIntervalKernel Q.measure Δ δ R i
        (sbxS9RecenteredPathLaws P y) (sbxS9RecenteredCoupledLaws K y) := by
  filter_upwards [sbxS5_recenter_input_ae Q hK.2] with y hy
  have hmp : MeasurePreserving (translate (-y)) Q.measure Q.measure :=
    ⟨EinsteinRelation.Probability.measurable_translate (-y), Q.stationary (-y)⟩
  have hprob := hmp.quasiMeasurePreserving.ae
    (sbxS5_probability_all_starts_of_gmp_phys hd hΛ₀ Q lam h0 h1 P hP)
  constructor
  · filter_upwards [hy.1, hprob] with η hη hpη
    apply sbxS5_oneIntervalKernelAt_recenter y 0 η Δ δ R i P K hpη
    simpa only [add_zero] using hη
  · have hprod := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Vec d))) (ν := Q.measure)).ae hprob
    filter_upwards [hy.2, hprod] with xη hxη hpη
    exact sbxS5_oneIntervalKernelAt_recenter y xη.1 xη.2 Δ δ R i P K hpη hxη

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxS5_seven_coupling_clauses_recenter`. -/
theorem sbxS5_seven_coupling_clauses_recenter_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsGMPCouplingV2Phys hd hΛ₀ Q lam l δ h0 h1 P K) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      HasProbabilityLaws Q.measure (sbxS9RecenteredCoupledLaws K y) ∧
      HasPathMarginals Q.measure (sbxS9RecenteredCoupledLaws K y)
        (sbxS9RecenteredPathLaws P y) ∧
      HasFreshBits Q.measure (regenDelta lam) δ (sbxS9RecenteredCoupledLaws K y) ∧
      HasDeterministicRestart Q.measure (regenDelta lam)
        (sbxS9RecenteredCoupledLaws K y) ∧
      HasSuccessfulBridgeSupport Q.measure (regenDelta lam) (forceCoord hd) (l / lam)
        (sbxS9RecenteredCoupledLaws K y) ∧
      HasUniformSuccessfulEndpoint Q.measure (regenDelta lam) δ (l / lam) (forceCoord hd)
        (sbxS9RecenteredCoupledLaws K y) ∧
      HasOneIntervalKernel Q.measure (regenDelta lam) δ (l / lam) (forceCoord hd)
        (sbxS9RecenteredPathLaws P y) (sbxS9RecenteredCoupledLaws K y) := by
  obtain ⟨hprob, hpath, hgmp, hfresh, hrestart, hsupport, hendpoint, hinterval⟩ := hK
  filter_upwards [sbxS9_five_coupling_clauses_recenter Q (regenDelta lam) δ (l / lam)
    (forceCoord hd) P K hprob hpath hfresh hrestart hsupport,
    sbxS5_hasUniformSuccessfulEndpoint_recenter Q (regenDelta lam) δ (l / lam)
      (forceCoord hd) K hendpoint,
    sbxS5_hasOneIntervalKernel_recenter_phys hd hΛ₀ Q lam h0 h1 (regenDelta lam) δ (l / lam)
      (forceCoord hd) P K hgmp hinterval] with y halg hend hint
  exact ⟨halg.1, halg.2.1, halg.2.2.1, halg.2.2.2.1, halg.2.2.2.2, hend, hint⟩

end EinsteinFull.Blueprint
