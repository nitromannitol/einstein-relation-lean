import EinsteinFull.Regeneration.GMPDowncrossingSmallTilt
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
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPBackwardFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPDowncrossingFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPForwardFromPositiveExit
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
`EinsteinFull.Regeneration.GMPDowncrossingSmallTilt`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of
`EinsteinFull.Regeneration.uniform_coupled_downcrossing_small_tilt_of_positive_exit`. -/
theorem uniform_coupled_downcrossing_small_tilt_of_positive_exit_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r L : ℝ) (hL : 1 ≤ L) :
    ∃ a l₀ : ℝ, 0 < a ∧ 0 < l₀ ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) ω)
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) ω
          hω μ hμ.le hμ1),
        (∀ y : Vec d, (2 / 3 : ℝ) ≤ (G.pathLaw y).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ}) →
        ∀ (x : Vec d) (ν : Measure (CoupledSample d)), ν.map Prod.fst = G.pathLaw x →
        ∀ l : ℝ, l₀ ≤ l → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        let E := {z : CoupledSample d |
          firstHittingBelow z.1 (Renewal.forceCoord hd) (-(l / μ)) ≠ ⊤}
        let F := fun z : CoupledSample d => Real.exp ((θ * a) * μ *
          coordinateMaximum z.1 (Renewal.forceCoord hd)
            (firstHittingBelow z.1 (Renewal.forceCoord hd) (-(l / μ))).toNNReal)
        Integrable (E.indicator F) ν ∧
          (∫ z, E.indicator F z ∂ν) ≤ (1 / 2 : ℝ) + θ / 4 := by
  obtain ⟨a, l₁, ha, hl₁, hcontract⟩ :=
    uniform_coupled_downcrossing_contraction_of_positive_exit_phys d hd Λ r L hL
  obtain ⟨κ, C, hκ, hC, hback⟩ :=
    uniform_regular_backward_hitting_of_positive_exit_phys d hd Λ r L hL
  let l₀ : ℝ := max l₁ (2 * C / κ)
  have hl₀ : 0 < l₀ := lt_of_lt_of_le hl₁ (le_max_left _ _)
  refine ⟨a, l₀, ha, hl₀, ?_⟩
  intro Q μ hμ hμ1 ω hω G hpositive x ν hpath l hl θ hθ hθ1
  have hl₁' : l₁ ≤ l := (le_max_left _ _).trans hl
  have hscale : 2 * C ≤ κ * l := by
    have h := (div_le_iff₀ hκ).mp ((le_max_right l₁ (2 * C / κ)).trans hl)
    nlinarith
  have hexp : C * Real.exp (-κ * l) ≤ (1 / 2 : ℝ) := by
    have he := Real.add_one_le_exp (κ * l)
    have hpos : 0 < Real.exp (κ * l) := Real.exp_pos _
    rw [show -κ * l = -(κ * l) by ring, Real.exp_neg]
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    nlinarith
  let i := Renewal.forceCoord hd
  let R := l / μ
  let E : Set (CoupledSample d) := {z | firstHittingBelow z.1 i (-R) ≠ ⊤}
  let X : CoupledSample d → ℝ := fun z => μ *
    coordinateMaximum z.1 i (firstHittingBelow z.1 i (-R)).toNNReal
  have hpathE : MeasurableSet {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤} :=
    (measurableSet_eq_fun (measurable_first_downcrossing R i) measurable_const).compl
  have hE : MeasurableSet E := hpathE.preimage measurable_fst
  have hX : Measurable X := measurable_const.mul ((measurable_maximum_at_downcrossing R i).comp measurable_fst)
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mp (by
    rw [hpath]
    infer_instance)
  have hfail : G.pathLaw x {γ | firstHittingBelow γ i (-R) ≠ ⊤} ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (C * Real.exp (-κ * μ * (l / μ))) :=
        hback Q μ hμ hμ1 ω hω G hpositive x _
      _ = ENNReal.ofReal (C * Real.exp (-κ * l)) := by congr 2; field_simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal hexp
  have hmass : ν.real E ≤ (1 / 2 : ℝ) := by
    have heq : ν E = G.pathLaw x {γ | firstHittingBelow γ i (-R) ≠ ⊤} := by
      rw [← hpath, Measure.map_apply measurable_fst hpathE]
      rfl
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfail
    simpa only [measureReal_def, heq, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] using h
  obtain ⟨hi, hmoment⟩ := hcontract Q μ hμ hμ1 ω hω G hpositive x ν hpath l hl₁'
  have hi' : Integrable (E.indicator (fun z => Real.exp (a * X z))) ν := by
    simpa only [E, X, i, R, ← mul_assoc] using hi
  have hmoment' : (∫ z, E.indicator (fun z => Real.exp (a * X z)) z ∂ν) ≤ (3 / 4 : ℝ) := by
    simpa only [E, X, i, R, ← mul_assoc] using hmoment
  obtain ⟨hsmall, hbound⟩ :=
    exponential_moment_indicator_interpolate ν E hE X hX a θ (3 / 4) hθ hθ1 hi' hmoment'
  refine ⟨?_, ?_⟩
  · simpa only [E, X, i, R, ← mul_assoc] using hsmall
  · have h := mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr hθ1)
    have hh : (∫ z, E.indicator (fun z => Real.exp ((θ * a) * X z)) z ∂ν) ≤
        (1 / 2 : ℝ) + θ / 4 := by linarith
    simpa only [E, X, i, R, ← mul_assoc] using hh

end EinsteinFull.Regeneration
