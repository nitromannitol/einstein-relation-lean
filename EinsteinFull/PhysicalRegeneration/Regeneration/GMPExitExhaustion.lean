import EinsteinFull.Regeneration.GMPExitExhaustion
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
`EinsteinFull.Regeneration.GMPExitExhaustion`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open Filter MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of `EinsteinFull.Regeneration.gmp_ae_source_slab_exit_ne_top`. -/
theorem gmp_ae_source_slab_exit_ne_top_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) ω)
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) ω
      hω μ hμ.le hμ1) (c x : Vec d) :
    ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime
      (coordinateSlab (Renewal.forceCoord hd) c (l / μ)) γ ≠ ⊤ := by
  obtain ⟨δ, hδ, hδ1, hminor⟩ := uniform_regular_gmp_source_minorization_phys d hd Λ r l hl
  let i := Renewal.forceCoord hd
  let R := l / μ
  let Δ := Renewal.regenDelta μ
  let U := coordinateSlab i c R
  have hR : 0 < R := div_pos (lt_of_lt_of_le zero_lt_one hl) hμ
  have hstep : ∀ y, G.pathLaw y {γ : Path d |
      ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ U} ≤ ENNReal.ofReal (1 - δ) :=
    gmp_slab_survival_le_of_source_minorization G Δ δ R i hδ hδ1.le hR
      (hminor Q μ hμ hμ1 ω hω G) c
  exact gmp_ae_exitTime_ne_top_of_survival_bound G U (isOpen_coordinateSlab i c R) Δ δ hδ hδ1.le hstep x

/-- The physical-kernel version of `EinsteinFull.Regeneration.gmp_slab_exit_event_tendsto_ball`. -/
theorem gmp_slab_exit_event_tendsto_ball_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) ω)
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) ω
      hω μ hμ.le hμ1) (c x y : Vec d) (B : Set (Vec d)) (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ => G.pathLaw x (finiteExitEvent
      (coordinateSlab (Renewal.forceCoord hd) c (l / μ) ∩ Metric.ball y n) B)) atTop
      (𝓝 (G.pathLaw x (finiteExitEvent (coordinateSlab (Renewal.forceCoord hd) c (l / μ)) B))) := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  exact tendsto_finiteExitEvent_ball (Vec d) (G.pathLaw x)
    (coordinateSlab (Renewal.forceCoord hd) c (l / μ)) B
    (isOpen_coordinateSlab _ _ _) hB y
    (gmp_ae_source_slab_exit_ne_top_phys d hd Λ r l hl Q μ hμ hμ1 ω hω G c x)

/-- The physical-kernel version of
`EinsteinFull.Regeneration.gmp_positive_slab_exit_tendsto_ball`. -/
theorem gmp_positive_slab_exit_tendsto_ball_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) ω)
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) ω
      hω μ hμ.le hμ1) (x y : Vec d) :
    let i := Renewal.forceCoord hd
    let B : Set (Vec d) := {z | z i - x i = l / μ}
    Tendsto (fun n : ℕ => G.pathLaw x (finiteExitEvent
      (coordinateSlab i x (l / μ) ∩ Metric.ball y n) B)) atTop
      (𝓝 (G.pathLaw x {γ | coordinateSlabExit γ i (l / μ) ≠ ⊤ ∧
        γ (coordinateSlabExit γ i (l / μ)).toNNReal i - γ 0 i = l / μ})) := by
  dsimp only
  let i := Renewal.forceCoord hd
  let B : Set (Vec d) := {z | z i - x i = l / μ}
  have hB : MeasurableSet B :=
    (isClosed_eq ((continuous_apply i).sub continuous_const) continuous_const).measurableSet
  have hlim := gmp_slab_exit_event_tendsto_ball_phys d hd Λ r l hl Q μ hμ hμ1 ω hω G x x y B hB
  have hae : finiteExitEvent (coordinateSlab i x (l / μ)) B =ᵐ[G.pathLaw x]
      {γ | coordinateSlabExit γ i (l / μ) ≠ ⊤ ∧
        γ (coordinateSlabExit γ i (l / μ)).toNNReal i - γ 0 i = l / μ} := by
    filter_upwards [G.pathLaw_starts_at x] with γ hstart
    change γ 0 = x at hstart
    have heq : coordinateSlabExit γ i (l / μ) =
        MarkovProcess.ContinuousPath.exitTime (coordinateSlab i x (l / μ)) γ := by
      simp only [coordinateSlabExit, hstart]
    by_cases hfin : MarkovProcess.ContinuousPath.exitTime (coordinateSlab i x (l / μ)) γ = ⊤
    · simp [finiteExitEvent, heq, hfin]
    · have htime := MarkovProcess.ContinuousPath.untopD_exitTimeTop_eq_toNNReal
        (coordinateSlab i x (l / μ)) γ hfin
      simp only [finiteExitEvent, Set.mem_ofPred_eq, lt_top_iff_ne_top, htime,
        heq, B, hstart]
  have hevent := measure_congr hae
  rw [hevent] at hlim
  exact hlim

/-- The physical-kernel version of
`EinsteinFull.Regeneration.gmp_positive_slab_exit_tendsto_payoff`. -/
theorem gmp_positive_slab_exit_tendsto_payoff_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) ω)
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) ω
      hω μ hμ.le hμ1) (x y : Vec d) (f : Vec d → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ z, ‖f z‖ ≤ C)
    (hlower : ∀ z, z (Renewal.forceCoord hd) - x (Renewal.forceCoord hd) = -(l / μ) → f z = 0)
    (hupper : ∀ z, z (Renewal.forceCoord hd) - x (Renewal.forceCoord hd) = l / μ → f z = 1) :
    Tendsto (fun n : ℕ => ∫ γ, f (γ ((MarkovProcess.ContinuousPath.exitTimeTop
      (coordinateSlab (Renewal.forceCoord hd) x (l / μ) ∩ Metric.ball y n) γ).untopD 0))
      ∂G.pathLaw x) atTop
      (𝓝 ((G.pathLaw x).real {γ | coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ) ≠ ⊤ ∧
        γ (coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)).toNNReal
          (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = l / μ})) := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  let i := Renewal.forceCoord hd
  let R := l / μ
  let U := coordinateSlab i x R
  let B : Set (Vec d) := {z | z i - x i = R}
  let E := finiteExitEvent U B
  have hB : MeasurableSet B :=
    (isClosed_eq ((continuous_apply i).sub continuous_const) continuous_const).measurableSet
  have hE : MeasurableSet E := measurableSet_finiteExitEvent U B (isOpen_coordinateSlab i x R) hB
  have hfin := gmp_ae_source_slab_exit_ne_top_phys d hd Λ r l hl Q μ hμ hμ1 ω hω G x x
  have hlim := tendsto_integral_exitPayoff_ball (Vec d) (G.pathLaw x) U
    (isOpen_coordinateSlab i x R) y f hf C hC hfin
  have hface : ∀ᵐ γ ∂G.pathLaw x,
      f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)) = E.indicator 1 γ := by
    filter_upwards [hfin, G.pathLaw_starts_at x] with γ hγ hstart
    change γ 0 = x at hstart
    have ht := MarkovProcess.ContinuousPath.untopD_exitTimeTop_eq_toNNReal U γ hγ
    have hr : 0 < R := div_pos (lt_of_lt_of_le zero_lt_one hl) hμ
    have hγ' : MarkovProcess.ContinuousPath.exitTime (coordinateSlab i (γ 0) R) γ ≠ ⊤ := by
      simpa only [hstart] using hγ
    have hdisp := coordinate_slab_exit_displacement γ i R hr hγ'
    rw [hstart] at hdisp
    change |γ (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal i - x i| = R at hdisp
    by_cases hp : γ (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal i - x i = R
    · have he : γ ∈ E := by
        change MarkovProcess.ContinuousPath.exitTime U γ < ⊤ ∧
          γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0) i - x i = R
        exact ⟨lt_top_iff_ne_top.mpr hγ, by rw [ht]; exact hp⟩
      rw [Set.indicator_of_mem he, Pi.one_apply, ht]
      exact hupper _ hp
    · have hn : γ (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal i - x i = -R := by
        rcases le_total 0 (γ (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal i - x i) with hpos | hneg
        · rw [abs_of_nonneg hpos] at hdisp
          exact (hp hdisp).elim
        · rw [abs_of_nonpos hneg] at hdisp
          linarith
      have he : γ ∉ E := by
        intro he
        have hh := he.2
        change γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0) i - x i = R at hh
        rw [ht] at hh
        exact hp hh
      rw [Set.indicator_of_notMem he, ht]
      exact hlower _ hn
  have hintegral : (∫ γ, f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))
      ∂G.pathLaw x) = (G.pathLaw x).real E := by
    rw [integral_congr_ae hface, integral_indicator_one hE]
  have hmass := tendsto_nhds_unique
    (gmp_slab_exit_event_tendsto_ball_phys d hd Λ r l hl Q μ hμ hμ1 ω hω G x x y B hB)
    (gmp_positive_slab_exit_tendsto_ball_phys d hd Λ r l hl Q μ hμ hμ1 ω hω G x y)
  rw [hintegral, measureReal_def, hmass] at hlim
  exact hlim

end EinsteinFull.Regeneration
