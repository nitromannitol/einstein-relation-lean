import EinsteinFull.Regeneration.GMPPositiveSlabExit
import EinsteinFull.Regeneration.ExitPayoffRescaledPotential
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS10BridgeIntegrability
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCouplingSetwiseLowerR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS1CouplingAssemblyR02
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPExitExhaustion
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPExitSmoothPayoff
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPGeometricSlabExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPPayoffComparison
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPScaledSlabExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPSlabExitMoment
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPUniformExitMinorization
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPUniformSlabEscape
import EinsteinFull.PhysicalRegeneration.Regeneration.SbxS1JointSplitR01
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.GMPPositiveSlabExit`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory Filter Set EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of `EinsteinFull.Regeneration.gmp_positive_slab_exit`. -/
theorem gmp_positive_slab_exit_phys (n : ℕ) (hd : 2 ≤ n + 1) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ l₀ : ℝ, 1 ≤ l₀ ∧ ∀ l : ℝ, l₀ ≤ l → ∀ (r : ℝ)
      (Q : EnvironmentLaw (n + 1) Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
      (ω : FieldPair (n + 1))
      (hω : IsRegular (sourceReducedBound Λ) ω)
      (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
        (one_le_sourceReducedBound Q.ellipticity_parameter) ω
        hω μ hμ.le hμ1) (c : Vec (n + 1)),
      (2 / 3 : ℝ) ≤ (G.pathLaw c).real {γ |
        coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ) ≠ ⊤ ∧
        γ (coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)).toNNReal
          (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = l / μ} := by
  obtain ⟨l₀, hl₀, hmain⟩ := gmp_positive_slab_exit_of_eventual_weak_solutions_phys n hd Λ hΛ
  refine ⟨l₀, hl₀, ?_⟩
  intro l hl r Q μ hμ hμ1 ω hω G c
  apply hmain l hl r Q μ hμ hμ1 ω hω G c c
  have hl1 : 1 ≤ l := hl₀.trans hl
  have hl0 : 0 < l := lt_of_lt_of_le zero_lt_one hl1
  have hμi : 0 < μ⁻¹ := inv_pos.mpr hμ
  set i := Renewal.forceCoord hd with hi
  obtain ⟨δ, -, -, hmean⟩ := uniform_regular_gmp_slab_exit_mean_phys (n + 1) hd Λ r l hl1
  obtain ⟨δ', -, -, hexp⟩ :=
    uniform_regular_gmp_slab_exit_exponential_moment_phys (n + 1) hd Λ r l hl1
  let R : ℝ := l + Real.exp (2 * l / (n + 1)) + 1
  have hRl : l < R := by
    have := Real.exp_pos (2 * l / (n + 1))
    simp only [R]
    linarith
  have hRe : Real.exp (2 * l / (n + 1)) < R := by
    simp only [R]
    linarith
  have hR1 : 1 < R := lt_of_le_of_lt hl1 hRl
  filter_upwards [eventually_ge_atTop ⌈R / μ⌉₊] with N hN
  have hNR : R / μ ≤ (N : ℝ) := (Nat.le_ceil (R / μ)).trans (by exact_mod_cast hN)
  let D := coordinateSlab i c (l / μ) ∩ Metric.ball c (N : ℝ)
  have hDo : IsOpen D := (isOpen_coordinateSlab i c (l / μ)).inter Metric.isOpen_ball
  have hDs : D ⊆ coordinateSlab i c (l / μ) := inter_subset_left
  have hfin : ∀ x, ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime D γ ≠ ⊤ :=
    fun x => (hexp Q μ hμ hμ1 ω hω G c x D hDo hDs).1
  let Km : ℝ := (Real.exp δ * Real.exp (δ / 4) / (1 - Real.exp (δ / 4 - δ / 2))) / (δ / 4)
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hτ : ∀ x, Integrable (fun γ => (MarkovProcess.ContinuousPath.exitTime D γ).toReal)
      (G.pathLaw x) := by
    intro x
    have h := ((hmean Q μ hμ hμ1 ω hω G c x D hDo hDs).1).const_mul (μ ^ 2)⁻¹
    refine h.congr (Eventually.of_forall fun γ => ?_)
    change (μ ^ 2)⁻¹ * (μ ^ 2 * _) = _
    rw [← mul_assoc, inv_mul_cancel₀ hμ2.ne', one_mul]
  have hM : ∀ x, ∫ γ, (MarkovProcess.ContinuousPath.exitTime D γ).toReal ∂G.pathLaw x ≤
      (μ ^ 2)⁻¹ * Km := by
    intro x
    have h := (hmean Q μ hμ hμ1 ω hω G c x D hDo hDs).2
    have heq : ∫ γ, (MarkovProcess.ContinuousPath.exitTime D γ).toReal ∂G.pathLaw x =
        (μ ^ 2)⁻¹ * ∫ γ, μ ^ 2 * (MarkovProcess.ContinuousPath.exitTime D γ).toReal
          ∂G.pathLaw x := by
      rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hμ2.ne', one_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hμ2.le)
  have : IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd μ) :=
    EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd _ μ
  have hDm : physicalReversibleMeasure ω hd μ D ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt (measure_ball_lt_top (x := c))).ne
  obtain ⟨f, hf, hfc, -, hfeq⟩ := exists_compact_smooth_slabPayoff i c c (l / μ) (N : ℝ)
  let U : Set (PDE.Vec (n + 1)) := Metric.ball 0 R
  have hU : PDE.IsOpenBoundedConvexDomain U := PDE.Ch4Infra.isOpenBoundedConvexDomain_ball 0 R
  have hAz : ∀ z ∈ U, dist (c + μ⁻¹ • z) c < N := by
    intro z hz
    have hz' : ‖z‖ < R := by simpa only [U, Metric.mem_ball, dist_zero_right] using hz
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hμi]
    calc μ⁻¹ * ‖z‖ < μ⁻¹ * R := mul_lt_mul_of_pos_left hz' hμi
      _ = R / μ := by rw [div_eq_inv_mul]
      _ ≤ N := hNR
  let S := openForceSlab U i l
  have hS : IsOpen S := isOpen_openForceSlab hU.isOpen i l
  have hSD : ∀ z ∈ S, c + μ⁻¹ • z ∈ D := by
    intro z hz
    refine ⟨?_, Metric.mem_ball.mpr (hAz z hz.1)⟩
    have hzi : |z i| < l := abs_lt.mpr hz.2
    change |(c + μ⁻¹ • z) i - c i| < l / μ
    rw [show (c + μ⁻¹ • z) i - c i = μ⁻¹ * z i by simp, abs_mul, abs_of_pos hμi,
      div_eq_inv_mul]
    exact mul_lt_mul_of_pos_left hzi hμi
  have hF : ∀ z ∈ U, gmpScaledSlabPayoff G i c l μ c N z = exitPayoff G D f (c + μ⁻¹ • z) :=
    fun z hz => gmpBoundedSlabPayoff_eq_exitPayoff G i c (l / μ) c N f hfeq hfin
      (c + μ⁻¹ • z) (Metric.mem_closedBall.mpr (hAz z hz).le)
  obtain ⟨u, hu, hsol⟩ := exists_rescaled_exitPayoff_solution_of_potential G hμ D hDo hDm f
    hf hfc hfin hτ ((μ ^ 2)⁻¹ * Km) hM c U hU (gmpScaledSlabPayoff G i c l μ c N) hF S hS
    inter_subset_left hSD
  have hcont : Continuous (gmpScaledSlabPayoff G i c l μ c N) := by
    have hP := continuous_exitPayoff_of_separated G D hDo (slabSmoothPayoff i c (l / μ))
      (slabSmoothPayoff_smooth i c (l / μ)).continuous 1
      (fun x => abs_le.mpr ⟨by linarith [(slabSmoothPayoff_mem_Icc i c (l / μ) x).1],
        (slabSmoothPayoff_mem_Icc i c (l / μ) x).2⟩) hfin
      (slab_ball_separated i c c (l / μ) N)
    exact hP.comp (continuous_const.add (continuous_const_smul μ⁻¹))
  refine ⟨U, hU, u, ?_, ⟨0, 1, one_pos, Metric.closedBall_subset_ball hR1⟩, hu, hu ▸ hcont,
    hsol⟩
  exact (coordinateSlabBox_subset_closedBall n i 2 l).trans
    (Metric.closedBall_subset_ball (max_lt hRl hRe))

end EinsteinFull.Regeneration
