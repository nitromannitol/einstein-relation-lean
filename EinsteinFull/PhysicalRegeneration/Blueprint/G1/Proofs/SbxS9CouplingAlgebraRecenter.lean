import EinsteinFull.Blueprint.G1.Proofs.SbxS9CouplingAlgebraRecenter
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.CoupledEnvironmentRegularity
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.G1.Proofs.SbxS9CouplingAlgebraRecenter`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration
/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxS9_coupled_law_eq_of_one_regular_path_law`. -/
theorem sbxS9_coupled_law_eq_of_one_regular_path_law_phys {d : ℕ}
    (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (P P' : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (x : Vec d) (ω : FieldPair d)
    (hg : CoupledEnvironmentRegularPhys hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
    (hLsp : ∀ᵐ y ∂(volume : Measure (Vec d)),
      CoupledFibreRegular Δ δ R i P' L (y, ω))
    (hx : CoupledFibreRegular Δ δ R i P K (x, ω))
    (hx' : CoupledFibreRegular Δ δ R i P' L (x, ω))
    (hP : P (x, ω) = P' (x, ω))
    (hPsp : ∀ᵐ y ∂(volume : Measure (Vec d)), P (y, ω) = P' (y, ω)) :
    K (x, ω) = L (x, ω) := by
  have hs : ∀ y, ∀ᵐ γ ∂P (y, ω), γ 0 = y := by
    obtain ⟨_, r, hr⟩ := hg.1
    intro y
    rw [hr y]
    exact r.pathLaw_starts_at y
  have hsp : ∀ᵐ y ∂(volume : Measure (Vec d)),
      CoupledFibreRegular Δ δ R i P K (y, ω) ∧
      CoupledFibreRegular Δ δ R i P' L (y, ω) ∧ P (y, ω) = P' (y, ω) := by
    filter_upwards [hg.2.2.1, hLsp, hPsp] with y hy hy' hp
    exact ⟨hy, hy', hp⟩
  have := hx.1
  have := hx'.1
  exact measure_eq_of_finite_history_integrals _ _ Δ hΔ
    (sbxS9_finite_histories_eq_of_one_regular_path_law Δ hΔ δ R i P P' K L x ω
      hs hx hx' hP hsp (fun n hn => hg.2.2.2 n hn x))

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxS9_coupling_laws_eq_of_prescribed_split_clauses`. -/
theorem sbxS9_coupling_laws_eq_of_prescribed_split_clauses_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P P' : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (hprobL : HasProbabilityLaws Q.measure L)
    (hpathL : HasPathMarginals Q.measure L P')
    (hrestartL : HasDeterministicRestart Q.measure (Renewal.regenDelta lam) L)
    (honeL : Renewal.HasOneIntervalKernel Q.measure (Renewal.regenDelta lam)
      δ (l / lam) (Renewal.forceCoord hd) P' L)
    (hP : (∀ᵐ ω ∂Q.measure, P (0, ω) = P' (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, P p = P' p) :
    (∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2))
  have hg := ae_coupledEnvironmentRegular_phys hd Q lam h0.le h1 P K
    hK.1 hK.2.1 hK.2.2.1 (Renewal.regenDelta lam) hΔ δ (l / lam)
    (Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.2
  have hregularL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) P' L p := by
    filter_upwards [hprobL.2, hpathL.2, hrestartL.2, honeL.2] with p hp hm hr ho
    exact ⟨hp, hm, hr, ho⟩
  have hPsp : ∀ᵐ ω ∂Q.measure,
      ∀ᵐ y ∂(volume : Measure (Vec d)), P (y, ω) = P' (y, ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := Q.measure)
        (ν := (volume : Measure (Vec d)))).quasiMeasurePreserving.ae hP.2)
  have hLsp : ∀ᵐ ω ∂Q.measure, ∀ᵐ y ∂(volume : Measure (Vec d)),
      CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) P' L (y, ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := Q.measure)
        (ν := (volume : Measure (Vec d)))).quasiMeasurePreserving.ae hregularL)
  have hgood := (hg.and hLsp).and hPsp
  constructor
  · filter_upwards [hgood, hP.1, hprobL.1, hpathL.1, hrestartL.1, honeL.1]
      with ω hω hp hprob hpath hr ho
    exact sbxS9_coupled_law_eq_of_one_regular_path_law_phys hd Λ₀ Q.ellipticity_parameter
      lam h0.le h1 (Renewal.regenDelta lam) hΔ δ (l / lam) (Renewal.forceCoord hd)
      P P' K L 0 ω hω.1.1 hω.1.2 hω.1.1.2.1 ⟨hprob, hpath, hr, ho⟩ hp hω.2
  · have hregularK : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
          (Renewal.forceCoord hd) P K p := by
      filter_upwards [hK.1.2, hK.2.1.2, hK.2.2.2.2.1.2,
        hK.2.2.2.2.2.2.2.2] with p hp hm hr ho
      exact ⟨hp, hm, hr, ho⟩
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hgood,
      hregularK, hregularL, hP.2] with p hp hk hl heq
    exact sbxS9_coupled_law_eq_of_one_regular_path_law_phys hd Λ₀ Q.ellipticity_parameter
      lam h0.le h1 (Renewal.regenDelta lam) hΔ δ (l / lam) (Renewal.forceCoord hd)
      P P' K L p.1 p.2 hp.1.1 hp.1.2 hk hl heq hp.2

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbxS9_six_coupling_clauses_recenter`. -/
theorem sbxS9_six_coupling_clauses_recenter_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      HasProbabilityLaws Q.measure (sbxS9RecenteredCoupledLaws K a) ∧
      HasPathMarginals Q.measure (sbxS9RecenteredCoupledLaws K a)
        (sbxS9RecenteredPathLaws P a) ∧
      HasFreshBits Q.measure (Renewal.regenDelta lam) δ (sbxS9RecenteredCoupledLaws K a) ∧
      HasDeterministicRestart Q.measure (Renewal.regenDelta lam)
        (sbxS9RecenteredCoupledLaws K a) ∧
      HasSuccessfulBridgeSupport Q.measure (Renewal.regenDelta lam)
        (Renewal.forceCoord hd) (l / lam) (sbxS9RecenteredCoupledLaws K a) ∧
      Renewal.HasOneIntervalKernel Q.measure (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) (sbxS9RecenteredPathLaws P a)
        (sbxS9RecenteredCoupledLaws K a) := by
  have hprob := isProbabilityMeasure_of_isGMPReducedKernel_phys hd Q.ellipticity_parameter
    Q lam h0.le h1 P hK.2.2.1
  have hone := sbxS9_hasOneIntervalKernel_recenter Q.measure Q.stationary
    (Renewal.regenDelta lam) δ (l / lam) (div_pos hl h0) (Renewal.forceCoord hd)
    P K hprob hK.2.2.2.2.2.2.2
  filter_upwards [sbxS9_five_coupling_clauses_recenter Q (Renewal.regenDelta lam)
    δ (l / lam) (Renewal.forceCoord hd) P K hK.1 hK.2.1 hK.2.2.2.1
    hK.2.2.2.2.1 hK.2.2.2.2.2.1, hone] with a ha ho
  exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2, ho⟩

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxS9_recentered_coupling_laws_eq_of_path_laws_eq`. -/
theorem sbxS9_recentered_coupling_laws_eq_of_path_laws_eq_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      ((∀ᵐ ω ∂Q.measure, P (0, ω) = sbxS9RecenteredPathLaws P a (0, ω)) ∧
        ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
          P p = sbxS9RecenteredPathLaws P a p) →
      (∀ᵐ ω ∂Q.measure, K (0, ω) = sbxS9RecenteredCoupledLaws K a (0, ω)) ∧
        ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
          K p = sbxS9RecenteredCoupledLaws K a p := by
  filter_upwards [sbxS9_six_coupling_clauses_recenter_phys hd Q lam h0 h1 l δ hl P K hK]
    with a ha
  intro hP
  exact sbxS9_coupling_laws_eq_of_prescribed_split_clauses_phys hd Q lam h0 h1 l δ
    P (sbxS9RecenteredPathLaws P a) K (sbxS9RecenteredCoupledLaws K a)
    hK ha.1 ha.2.1 ha.2.2.2.1 ha.2.2.2.2.2 hP

end EinsteinFull.Blueprint
