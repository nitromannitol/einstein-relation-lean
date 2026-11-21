import EinsteinFull.Regeneration.ReducedWindowMaximum
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnClosureR15
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnR13
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedCenteredSurvival
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.ReducedWindowMaximum`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of
`EinsteinFull.Regeneration.uniform_reduced_window_maximum_moment`. -/
theorem uniform_reduced_window_maximum_moment_phys {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
        (P : QuenchedPathLaws d),
        EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0.le h1 P →
        ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (i : Fin d),
          Integrable (fun γ : Path d => Real.exp (b * (lam *
            coordinateMaximum γ i (Renewal.regenDelta lam)))) (P (x, ω)) ∧
          (∫ γ, Real.exp (b * (lam * coordinateMaximum γ i (Renewal.regenDelta lam)))
            ∂P (x, ω)) ≤ C := by
  obtain ⟨ε₀, hε₀, hε₀1, hsurv⟩ := reduced_centered_survival_phys hd Λ₀ r₀ 1 one_pos
  let ε : ℝ := min ε₀ (1 / 2)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεε : ε ≤ ε₀ := min_le_left _ _
  let C : ℝ := Real.exp ε * Real.exp (ε / 4) / (1 - Real.exp (ε / 4 - ε / 2))
  have hC : 0 < C := by
    have hlt : Real.exp (ε / 4 - ε / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact div_pos (by positivity) (sub_pos.mpr hlt)
  refine ⟨ε / 4, C, by positivity, hC, ?_⟩
  intro Q lam h0 h1 P hP
  have hlamabs : |lam| = lam := abs_of_pos h0
  have hP' : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q |lam|
      (abs_pos.mpr h0.ne').le (by rw [hlamabs]; exact h1) P := by
    simpa only [hlamabs] using hP
  filter_upwards [hP, hsurv Q lam (abs_pos.mpr h0.ne') (by rw [hlamabs]; exact h1) P hP']
    with ω hreal hloc
  obtain ⟨hω, G, hrow⟩ := hreal
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  intro x i
  have hr : 0 < 1 / lam := one_div_pos.mpr h0
  have hfdd := foundation_arbitrary_supplied_gmp_canonical_FDD hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) ω
    hω lam h0.le h1 G
  have hstep : ∀ y, ENNReal.ofReal ε ≤ G.pathLaw y {γ |
      Renewal.regenDelta lam ≤ cappedCoordinateSlabExit γ i (1 / lam) (Renewal.regenDelta lam)} := by
    intro y
    have hy := hloc y
    rw [hrow y] at hy
    simp only [hlamabs] at hy
    have hsub : {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta lam),
          euclideanNorm (γ s - y) ≤ (1 / lam) / 2} ∩ {γ | γ 0 = y} ⊆
        {γ | Renewal.regenDelta lam ≤
          cappedCoordinateSlabExit γ i (1 / lam) (Renewal.regenDelta lam)} := by
      rintro γ ⟨hγ, hγ0⟩
      apply le_cappedCoordinateSlabExit_of_forall_mem
      intro s hs
      have hn := hγ s ⟨zero_le, hs⟩
      have hc := coordinate_abs_le_euclideanNorm (γ s - y) i
      change |γ s i - γ 0 i| < 1 / lam
      rw [hγ0]
      have hc' : |γ s i - y i| ≤ (1 / lam) / 2 := by
        simpa only [Pi.sub_apply] using hc.trans hn
      linarith
    have hstart : G.pathLaw y {γ | γ 0 = y}ᶜ = 0 := by
      have h := G.pathLaw_starts_at y
      rw [MeasureTheory.ae_iff] at h
      exact h
    calc ENNReal.ofReal ε ≤ ENNReal.ofReal ε₀ := ENNReal.ofReal_le_ofReal hεε
      _ ≤ G.pathLaw y {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta lam),
          euclideanNorm (γ s - y) ≤ (1 / lam) / 2} := by simpa only [one_div] using hy
      _ = G.pathLaw y ({γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta lam),
          euclideanNorm (γ s - y) ≤ (1 / lam) / 2} ∩ {γ | γ 0 = y}) :=
          (measure_inter_conull hstart).symm
      _ ≤ _ := measure_mono hsub
  have hmom := window_maximum_exponential_moment hd ω lam
    (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter) hω
    G.pathLaw hfdd i (1 / lam) hr (Renewal.regenDelta lam) ε hε hε1 hstep x
  have hfun : (fun γ : Path d => Real.exp ((ε / 4) *
      (coordinateMaximum γ i (Renewal.regenDelta lam) / (1 / lam)))) =
      fun γ => Real.exp (ε / 4 * (lam * coordinateMaximum γ i (Renewal.regenDelta lam))) := by
    funext γ
    rw [one_div, div_inv_eq_mul, mul_comm (coordinateMaximum γ i _) lam]
  rw [hfun] at hmom
  rw [hrow x]
  exact hmom

end EinsteinFull.Regeneration
