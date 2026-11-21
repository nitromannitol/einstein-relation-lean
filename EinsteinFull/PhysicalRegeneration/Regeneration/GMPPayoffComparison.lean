import EinsteinFull.Regeneration.GMPPayoffComparison
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
`EinsteinFull.Regeneration.GMPPayoffComparison`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory Set EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of
`EinsteinFull.Regeneration.gmp_bounded_slab_payoff_lower_of_weak_solution`. -/
theorem gmp_bounded_slab_payoff_lower_of_weak_solution_phys
    (n : ℕ) (hd : 2 ≤ n + 1) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l : ℝ, l₀ ≤ l → ∀ (r : ℝ)
      (Q : EnvironmentLaw (n + 1) Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
      (ω : FieldPair (n + 1))
      (hω : IsRegular (sourceReducedBound Λ) ω)
      (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
        (one_le_sourceReducedBound Q.ellipticity_parameter) ω
        hω μ hμ.le hμ1) (c y : Vec (n + 1)) (N : ℝ)
      (U : Set (PDE.Vec (n + 1))) (hU : PDE.IsOpenBoundedConvexDomain U)
      (u : PDE.H1Function U),
      coordinateSlabBox n (Renewal.forceCoord hd) 2 l ⊆ U →
      ∀ {x₀ : PDE.Vec (n + 1)} {r' : ℝ}, 0 < r' → Metric.closedBall x₀ r' ⊆ U →
      u.toFun = gmpScaledSlabPayoff G (Renewal.forceCoord hd) c l μ y N →
      Continuous u.toFun →
      PDE.IsWeakDivergenceFormL2SolutionOn
        (fun x => Real.exp (2 * x (Renewal.forceCoord hd)) •
          gmpRescaledCoefficient (zeroPotentialReducedPair ω) c μ x)
        (openForceSlab U (Renewal.forceCoord hd) l)
        (u.restrict (isOpen_openForceSlab hU.isOpen (Renewal.forceCoord hd) l) inter_subset_left) 0 0 →
      (2 / 3 : ℝ) ≤ gmpBoundedSlabPayoff G (Renewal.forceCoord hd) c (l / μ) y N c := by
  have hK : 1 ≤ sourceReducedBound (sourceReducedBound Λ) :=
    one_le_sourceReducedBound (one_le_sourceReducedBound hΛ)
  obtain ⟨L₀, hL₀⟩ := exists_gmp_rescaled_slab_width n (sourceReducedBound (sourceReducedBound Λ)) hK
  refine ⟨max 1 L₀, by positivity, ?_⟩
  intro l hl r Q μ hμ hμ1 ω hω G c y N U hU u hsource x₀ r' hr hball hrep hcont hsol
  have hl0 : L₀ ≤ l := (le_max_right _ _).trans hl
  have hlpos : 0 < l := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hl)
  let i := Renewal.forceCoord hd
  have hzero : ∀ x, 0 ≤ u x := by
    intro x
    rw [hrep]
    exact (gmpScaledSlabPayoff_mem_Icc G i c l μ y N x).1
  have hone : ∀ x, u x ≤ 1 := by
    intro x
    rw [hrep]
    exact (gmpScaledSlabPayoff_mem_Icc G i c l μ y N x).2
  have hleft : ∀ᵐ z ∂(volume.restrict
      (Icc (fun _ : Fin n => -Real.exp (2 * l / (n + 1)))
        (fun _ => Real.exp (2 * l / (n + 1))))),
      u (centralSlabPoint n i (-l, z)) = 0 := by
    filter_upwards with z
    rw [hrep]
    exact gmpScaledSlabPayoff_lower G i c l μ hlpos hμ y N _
      (centralSlabPoint_coord n i (-l) z).1
  have hright : ∀ᵐ z ∂(volume.restrict
      (Icc (fun _ : Fin n => -Real.exp (2 * l / (n + 1)))
        (fun _ => Real.exp (2 * l / (n + 1))))),
      u (centralSlabPoint n i (l, z)) = 1 := by
    filter_upwards with z
    rw [hrep]
    exact gmpScaledSlabPayoff_upper G i c l μ hlpos hμ y N _
      (centralSlabPoint_coord n i l z).1
  have hcenter := hL₀ l hl0 U hU u i hsource hr hball hcont hzero hone hleft hright
    (zeroPotentialReducedPair ω)
    (isRegular_zeroPotentialReducedPair (one_le_sourceReducedBound hΛ) hω) c μ hsol
  rw [hrep, gmpScaledSlabPayoff_zero] at hcenter
  exact hcenter

/-- The physical-kernel version of
`EinsteinFull.Regeneration.gmp_positive_slab_exit_of_eventual_weak_solutions`. -/
theorem gmp_positive_slab_exit_of_eventual_weak_solutions_phys
    (n : ℕ) (hd : 2 ≤ n + 1) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ l₀ : ℝ, 1 ≤ l₀ ∧ ∀ l : ℝ, l₀ ≤ l → ∀ (r : ℝ)
      (Q : EnvironmentLaw (n + 1) Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
      (ω : FieldPair (n + 1))
      (hω : IsRegular (sourceReducedBound Λ) ω)
      (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
        (one_le_sourceReducedBound Q.ellipticity_parameter) ω
        hω μ hμ.le hμ1) (c y : Vec (n + 1)),
      (∀ᶠ N : ℕ in Filter.atTop, ∃ (U : Set (PDE.Vec (n + 1)))
        (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U),
        coordinateSlabBox n (Renewal.forceCoord hd) 2 l ⊆ U ∧
        (∃ x₀ : PDE.Vec (n + 1), ∃ r' : ℝ, 0 < r' ∧ Metric.closedBall x₀ r' ⊆ U) ∧
        u.toFun = gmpScaledSlabPayoff G (Renewal.forceCoord hd) c l μ y N ∧
        Continuous u.toFun ∧
        PDE.IsWeakDivergenceFormL2SolutionOn
          (fun x => Real.exp (2 * x (Renewal.forceCoord hd)) •
            gmpRescaledCoefficient (zeroPotentialReducedPair ω) c μ x)
          (openForceSlab U (Renewal.forceCoord hd) l)
          (u.restrict (isOpen_openForceSlab hU.isOpen (Renewal.forceCoord hd) l) inter_subset_left) 0 0) →
      (2 / 3 : ℝ) ≤ (G.pathLaw c).real {γ |
        coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ) ≠ ⊤ ∧
        γ (coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)).toNNReal
          (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = l / μ} := by
  obtain ⟨L₀, _, hL₀⟩ := gmp_bounded_slab_payoff_lower_of_weak_solution_phys n hd Λ hΛ
  refine ⟨max 1 L₀, le_max_left _ _, ?_⟩
  intro l hl r Q μ hμ hμ1 ω hω G c y hrep
  have hL : L₀ ≤ l := (le_max_right _ _).trans hl
  have hl1 : 1 ≤ l := (le_max_left _ _).trans hl
  have hlim := gmp_positive_slab_exit_tendsto_smooth_payoff_phys (n + 1) hd Λ r l hl1
    Q μ hμ hμ1 ω hω G c y
  have hlim' : Filter.Tendsto (fun N : ℕ =>
      gmpBoundedSlabPayoff G (Renewal.forceCoord hd) c (l / μ) y N c) Filter.atTop
      (nhds ((G.pathLaw c).real {γ | coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ) ≠ ⊤ ∧
        γ (coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)).toNNReal
          (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = l / μ})) := by
    simpa only [gmpBoundedSlabPayoff] using hlim
  have hbound : ∀ᶠ N : ℕ in Filter.atTop, (2 / 3 : ℝ) ≤
      gmpBoundedSlabPayoff G (Renewal.forceCoord hd) c (l / μ) y N c := by
    filter_upwards [hrep] with N hN
    obtain ⟨U, hU, u, hsource, ⟨x₀, r', hr, hball⟩, hvalue, hcont, hsol⟩ := hN
    exact hL₀ l hL r Q μ hμ hμ1 ω hω G c y N U hU u hsource hr hball hvalue hcont hsol
  exact ge_of_tendsto hlim' hbound

end EinsteinFull.Regeneration
