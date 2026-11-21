import EinsteinFull.Regeneration.TrialFailureFactor
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
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnClosureR15
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnR13
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCouplingSetwiseLowerR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS1CouplingAssemblyR02
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPBackwardFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPDowncrossingFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPDowncrossingSmallTilt
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPForwardFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPUniformExitMinorization
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPUniformSlabEscape
import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedCenteredSurvival
import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedWindowMaximum
import EinsteinFull.PhysicalRegeneration.Regeneration.SbxS1JointSplitR01
import EinsteinFull.PhysicalRegeneration.Regeneration.UniformFirstCandidate
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.TrialFailureFactor`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of `EinsteinFull.Regeneration.uniform_trial_failure_factor`. -/
theorem uniform_trial_failure_factor_phys (d : ℕ) (hd : 2 ≤ d) (Λ r L : ℝ) (hL : 1 ≤ L) :
    ∃ c Cw l₀ : ℝ, 0 < c ∧ 0 ≤ Cw ∧ 0 < l₀ ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (P : QuenchedPathLaws d),
        EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q μ hμ.le hμ1 P →
        (∀ᵐ ω ∂Q.measure, ∀ y : Vec d, (2 / 3 : ℝ) ≤ (P (y, ω)).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ}) →
        ∀ l : ℝ, l₀ ≤ l → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        ∀ᵐ ω ∂Q.measure, ∀ y : Vec d,
          ∫⁻ γ, trialFailureWeight (Renewal.regenDelta μ) μ (l / μ) (θ * c)
            (Renewal.forceCoord hd) γ ∂P (y, ω) ≤
            ENNReal.ofReal (Real.exp (θ * c * (13 * l)) * ((1 + θ * Cw) * (1 / 2 + θ / 4))) := by
  obtain ⟨a₀, l₀, ha₀, hl₀, hsmall⟩ :=
    uniform_coupled_downcrossing_small_tilt_of_positive_exit_phys d hd Λ r L hL
  obtain ⟨b₁, C, hb₁, hC, hwin⟩ := uniform_reduced_window_maximum_moment_phys hd Λ r
  refine ⟨min a₀ b₁, C, l₀, lt_min ha₀ hb₁, hC.le, hl₀, ?_⟩
  intro Q μ hμ hμ1 P hP hpositive l hl θ hθ0 hθ1
  set c := min a₀ b₁ with hc
  have hca : c ≤ a₀ := min_le_left _ _
  have hcb : c ≤ b₁ := min_le_right _ _
  have hlpos : 0 < l := lt_of_lt_of_le hl₀ hl
  filter_upwards [hP, hpositive, hwin Q μ hμ hμ1 P hP] with ω hreal hp hW
  obtain ⟨hω, G, hrow⟩ := hreal
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have hpositiveG : ∀ y : Vec d, (2 / 3 : ℝ) ≤ (G.pathLaw y).real {γ |
      coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
      γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
        (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ} := by
    intro y
    rw [← hrow y]
    exact hp y
  intro y
  let i := Renewal.forceCoord hd
  let Δ := Renewal.regenDelta μ
  let R := l / μ
  have hR : 0 < R := div_pos hlpos hμ
  have hμR : μ * R = l := by simp only [R]; field_simp
  -- window moment
  have hwinG : ∀ x, ∫⁻ η, windowWeight Δ μ (θ * c) i η ∂G.pathLaw x ≤
      ENNReal.ofReal (1 + θ * C) := by
    intro x
    obtain ⟨hint, hle⟩ := hW x i
    rw [hrow x] at hint hle
    have hlint : ∫⁻ η, ENNReal.ofReal (Real.exp (b₁ * (μ * coordinateMaximum η i Δ)))
        ∂G.pathLaw x ≤ ENNReal.ofReal C := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun η => (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal hle
    calc ∫⁻ η, windowWeight Δ μ (θ * c) i η ∂G.pathLaw x
        ≤ ∫⁻ η, 1 + ENNReal.ofReal θ *
            ENNReal.ofReal (Real.exp (b₁ * (μ * coordinateMaximum η i Δ))) ∂G.pathLaw x := by
          apply lintegral_mono
          intro η
          simp only [windowWeight]
          rw [← ENNReal.ofReal_mul hθ0, ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add zero_le_one (mul_nonneg hθ0 (Real.exp_pos _).le)]
          apply ENNReal.ofReal_le_ofReal
          have hM := coordinateMaximum_nonneg η i Δ
          have hX : 0 ≤ μ * coordinateMaximum η i Δ := mul_nonneg hμ.le hM
          have h1 : θ * c * μ * coordinateMaximum η i Δ ≤ θ * (b₁ * (μ * coordinateMaximum η i Δ)) := by
            have := mul_le_mul_of_nonneg_right hcb hX
            nlinarith
          calc Real.exp (θ * c * μ * coordinateMaximum η i Δ)
              ≤ Real.exp (θ * (b₁ * (μ * coordinateMaximum η i Δ))) := Real.exp_le_exp.mpr h1
            _ ≤ 1 + θ * Real.exp (b₁ * (μ * coordinateMaximum η i Δ)) :=
              exp_mul_le_one_add_mul_exp θ _ hθ0 hθ1
      _ = 1 + ENNReal.ofReal θ * ∫⁻ η, ENNReal.ofReal
            (Real.exp (b₁ * (μ * coordinateMaximum η i Δ))) ∂G.pathLaw x := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ 1 + ENNReal.ofReal θ * ENNReal.ofReal C := by gcongr
      _ = ENNReal.ofReal (1 + θ * C) := by
          rw [← ENNReal.ofReal_mul hθ0, ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add zero_le_one (mul_nonneg hθ0 hC.le)]
  -- fall moment
  have hfall : ∫⁻ γ, fallWeight μ R (θ * c) i γ ∂G.pathLaw y ≤ ENNReal.ofReal (1 / 2 + θ / 4) := by
    let ν : Measure (CoupledSample d) :=
      (G.pathLaw y).map (fun γ : Path d => ((γ, fun _ => false) : CoupledSample d))
    have hνm : Measurable (fun γ : Path d => ((γ, fun _ => false) : CoupledSample d)) :=
      measurable_id.prodMk measurable_const
    have hν : ν.map Prod.fst = G.pathLaw y := by
      rw [Measure.map_map measurable_fst hνm]
      exact Measure.map_id
    obtain ⟨hint, hle⟩ := hsmall Q μ hμ hμ1 ω hω G hpositiveG y ν hν l hl θ hθ0 hθ1
    set E := {z : CoupledSample d | firstHittingBelow z.1 (Renewal.forceCoord hd) (-(l / μ)) ≠ ⊤}
    set F := fun z : CoupledSample d => Real.exp ((θ * a₀) * μ *
      coordinateMaximum z.1 (Renewal.forceCoord hd)
        (firstHittingBelow z.1 (Renewal.forceCoord hd) (-(l / μ))).toNNReal)
    have hmono : ∀ γ : Path d, fallWeight μ R (θ * c) i γ ≤
        ENNReal.ofReal (E.indicator F ((γ, fun _ => false) : CoupledSample d)) := by
      intro γ
      by_cases hH : firstHittingBelow γ i (-R) ≠ ⊤
      · simp only [fallWeight]
        rw [Set.indicator_of_mem (show γ ∈ {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤} from hH),
          Set.indicator_of_mem (show ((γ, fun _ => false) : CoupledSample d) ∈ E from hH)]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hM := coordinateMaximum_nonneg γ i (firstHittingBelow γ i (-R)).toNNReal
        have h1 : θ * c ≤ θ * a₀ := mul_le_mul_of_nonneg_left hca hθ0
        have h2 : 0 ≤ μ * coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal :=
          mul_nonneg hμ.le hM
        change θ * c * μ * coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal ≤
          θ * a₀ * μ * coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal
        nlinarith
      · simp only [fallWeight]
        rw [Set.indicator_of_notMem (show γ ∉ {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤}
          from hH)]
        exact zero_le
    have hEm : MeasurableSet E :=
      (measurableSet_eq_fun ((measurable_first_downcrossing (l / μ) (Renewal.forceCoord hd)).comp
        measurable_fst) measurable_const).compl
    calc ∫⁻ γ, fallWeight μ R (θ * c) i γ ∂G.pathLaw y
        ≤ ∫⁻ γ, ENNReal.ofReal (E.indicator F ((γ, fun _ => false) : CoupledSample d))
          ∂G.pathLaw y := lintegral_mono hmono
      _ = ∫⁻ z, ENNReal.ofReal (E.indicator F z) ∂ν := by
          rw [lintegral_map _ hνm]
          exact ENNReal.measurable_ofReal.comp (Measurable.indicator
            (Real.measurable_exp.comp (measurable_const.mul
              ((measurable_maximum_at_downcrossing (l / μ) (Renewal.forceCoord hd)).comp
                measurable_fst))) hEm)
      _ = ENNReal.ofReal (∫ z, E.indicator F z ∂ν) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun z => Set.indicator_nonneg
              (fun z _ => (Real.exp_pos _).le) z)]
      _ ≤ ENNReal.ofReal (1 / 2 + θ / 4) := ENNReal.ofReal_le_ofReal hle
  have hmain := lintegral_trialFailureWeight_le hd ω μ
    (sourceReducedBound Λ) (one_le_sourceReducedBound Q.ellipticity_parameter) hω hμ.le hμ1 G Δ
    (EinsteinRelation.regenDelta_pos hμ) μ R (θ * c) hμ hR (mul_nonneg hθ0 (lt_min ha₀ hb₁).le) i
    (1 + θ * C) hwinG y
  rw [hrow y]
  calc ∫⁻ γ, trialFailureWeight Δ μ R (θ * c) i γ ∂G.pathLaw y
      ≤ ENNReal.ofReal (Real.exp (θ * c * μ * (13 * R))) *
          (ENNReal.ofReal (1 + θ * C) * ∫⁻ γ, fallWeight μ R (θ * c) i γ ∂G.pathLaw y) := hmain
    _ ≤ ENNReal.ofReal (Real.exp (θ * c * μ * (13 * R))) *
          (ENNReal.ofReal (1 + θ * C) * ENNReal.ofReal (1 / 2 + θ / 4)) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 2
        congr 1
        rw [← hμR]
        ring

end EinsteinFull.Regeneration
