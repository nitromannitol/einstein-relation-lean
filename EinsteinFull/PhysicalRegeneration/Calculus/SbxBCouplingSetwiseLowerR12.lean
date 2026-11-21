import EinsteinFull.Calculus.SbxBCouplingSetwiseLowerR12
import EinsteinFull.Regeneration.PhysicalKernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.SbxBCouplingSetwiseLowerR12`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Regeneration EinsteinRelation.Diffusion EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP EinsteinFull.Blueprint.TubeProbability
noncomputable section
/-- The physical-kernel version of `EinsteinFull.bCouplingLocalStepInput`. -/
def bCouplingLocalStepInput_phys : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ), 1 ≤ l →
    ∃ a : ℝ, 0 < a ∧ ∀ (Q : EnvironmentLaw d Λ r)
      (μ : ℝ) (hμ : 0 < μ) (h₁ : μ ≤ 1)
      (ω : FieldPair d)
      (hω : IsRegular (sourceReducedBound Λ) ω)
      (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
        (one_le_sourceReducedBound Q.ellipticity_parameter) ω
        hω μ hμ.le h₁) (x : Vec d),
      let i := Renewal.forceCoord hd
      let R := l / μ
      let U := couplingRegion i R x
      let A := b_couplingChainWindow i R x
      ∀ k < 80, ∀ z ∈ A k,
        ENNReal.ofReal (a * μ ^ d) • (volume : Measure (Vec d)).restrict (A (k+1)) ≤
          gmpKilledEndpointKernel G U (by
            exact isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
              (continuous_id.sub continuous_const)) continuous_const)
            (Renewal.regenDelta μ / (80 : ℝ≥0)) z

/-- The physical-kernel version of `EinsteinFull.b_coupling_local_steps`. -/
theorem b_coupling_local_steps_phys : bCouplingLocalStepInput_phys := by
  intro d hd Λ r l hl
  by_cases hΛ : 1 ≤ Λ
  · have hl' : 0 < l := lt_of_lt_of_le zero_lt_one hl
    obtain ⟨a₁, ha₁, hstep₁⟩ := s14_actual_translated_uniform_one_step
      d hd (sourceReducedBound Λ) (l/2) (1/80) (one_le_sourceReducedBound hΛ)
      (by positivity) (by norm_num)
    obtain ⟨a₂, ha₂, hstep₂⟩ := s14_actual_translated_uniform_one_step
      d hd (sourceReducedBound Λ) (2*l) (1/80) (one_le_sourceReducedBound hΛ)
      (by positivity) (by norm_num)
    refine ⟨min a₁ a₂, lt_min ha₁ ha₂, ?_⟩
    intro Q μ hμ hμ1 ω hω G x
    dsimp only
    let i := Renewal.forceCoord hd
    let R := l / μ
    let U := couplingRegion i R x
    let A := b_couplingChainWindow i R x
    have hR : 0 < R := div_pos hl' hμ
    have hopen (z : Vec d) (s : ℝ) : IsOpen (sourceBall z s) :=
      isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
        (continuous_id.sub continuous_const)) continuous_const
    have hU : IsOpen U := hopen _ _
    have hA (k : ℕ) : MeasurableSet (A k) := by
      dsimp [A, b_couplingChainWindow]
      split
      · exact (hopen _ _).measurableSet
      · split
        · exact (hopen _ _).measurableSet
        · exact MeasurableSet.empty
    intro k hk y hy
    obtain ⟨z,s,hs,hsr,hsub,hprev,hnext⟩ :=
      b_coupling_chain_step_geometry i R x hR k hk
    have hsub' : (fun v : Vec d => v-z) ⁻¹' sourceBall 0 s ⊆ U := by
      intro v hv
      apply hsub
      simpa [sourceBall] using hv
    have hinside {v : Vec d} (hv : v ∈ sourceBall z (s/2)) :
        v-z ∈ sourceBall 0 s := by
      change euclideanNorm (v-z-0) < s
      change euclideanNorm (v-z) < s/2 at hv
      simp only [sub_zero]
      linarith
    have hscaled {v : Vec d} (hv : v ∈ sourceBall z (s/2)) :
        μ • (v-z) ∈ sourceBall 0 ((μ*s)/2) :=
      b_coupling_scaled_inner μ s hμ z v hv
    have htime := b_coupling_step_time μ hμ
    have hRscale : μ*R=l := by dsimp [R]; field_simp
    rcases hsr with hs₁|hs₂
    · have hscale : l/2=μ*s := by rw [hs₁]; nlinarith
      have h := hstep₁ μ s hμ hμ1 hs hscale _ hω z G U hU hsub'
        (A k) (A (k+1)) (hA (k+1))
        (fun v hv => hinside (hprev hv)) (fun v hv => hinside (hnext hv))
        (fun v hv => by simpa [←hscale] using hscaled (hprev hv))
        (fun v hv => by simpa [←hscale] using hscaled (hnext hv)) y hy
      rw [htime] at h
      apply le_trans ?_ h
      gcongr
      exact min_le_left _ _
    · have hscale : 2*l=μ*s := by rw [hs₂]; nlinarith
      have h := hstep₂ μ s hμ hμ1 hs hscale _ hω z G U hU hsub'
        (A k) (A (k+1)) (hA (k+1))
        (fun v hv => hinside (hprev hv)) (fun v hv => hinside (hnext hv))
        (fun v hv => by simpa [←hscale] using hscaled (hprev hv))
        (fun v hv => by simpa [←hscale] using hscaled (hnext hv)) y hy
      rw [htime] at h
      apply le_trans ?_ h
      gcongr
      exact min_le_right _ _
  · refine ⟨1, zero_lt_one, ?_⟩
    intro Q
    exact (hΛ Q.ellipticity_parameter).elim

/-- The physical-kernel version of `EinsteinFull.b_original_setwise_lower_of_local_steps`. -/
theorem b_original_setwise_lower_of_local_steps_phys (hlocal : bCouplingLocalStepInput_phys) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ), 1 ≤ l →
      ∃ c : ℝ, 0 < c ∧ ∀ (Q : EnvironmentLaw d Λ r)
        (μ : ℝ) (hμ : 0 < μ) (h₁ : μ ≤ 1),
        ∃ P : QuenchedPathLaws d,
          EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q μ hμ.le h₁ P ∧
          ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
            ENNReal.ofReal (c * μ ^ d) • (volume : Measure (Vec d)).restrict
              (endpointBall (Renewal.forceCoord hd) (l / μ) x) ≤
            ((P (x, ω)).restrict {γ | ∀ t : ℝ≥0, t ≤ Renewal.regenDelta μ →
              γ t ∈ couplingRegion (Renewal.forceCoord hd) (l / μ) x}).map
                (fun γ => γ (Renewal.regenDelta μ)) := by
  intro d hd Λ r l hl
  obtain ⟨a, ha, hstep⟩ := hlocal d hd Λ r l hl
  obtain ⟨c, hc, hchain⟩ := b_coupling_setwise_of_local_chain a l ha
    (lt_of_lt_of_le zero_lt_one hl)
  refine ⟨c, hc, ?_⟩
  intro Q μ hμ h₁
  obtain ⟨P, hP, _, _, _⟩ := EinsteinFull.Regeneration.global_physical_kernel_exists_reducedBound hd Q μ hμ.le h₁
  refine ⟨P, hP, ?_⟩
  filter_upwards [hP] with ω hω
  obtain ⟨hω, G, hG⟩ := hω
  intro x
  rw [hG x]
  exact hchain μ hμ G x (hstep Q μ hμ h₁ ω hω G x)

/-- The physical-kernel version of `EinsteinFull.b_original_setwise_lower`. -/
theorem b_original_setwise_lower_phys :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ), 1 ≤ l →
      ∃ c : ℝ, 0 < c ∧ ∀ (Q : EnvironmentLaw d Λ r)
        (μ : ℝ) (hμ : 0 < μ) (h₁ : μ ≤ 1),
        ∃ P : QuenchedPathLaws d,
          EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q μ hμ.le h₁ P ∧
          ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
            ENNReal.ofReal (c * μ ^ d) • (volume : Measure (Vec d)).restrict
              (endpointBall (Renewal.forceCoord hd) (l / μ) x) ≤
            ((P (x, ω)).restrict {γ | ∀ t : ℝ≥0, t ≤ Renewal.regenDelta μ →
              γ t ∈ couplingRegion (Renewal.forceCoord hd) (l / μ) x}).map
                (fun γ => γ (Renewal.regenDelta μ)) :=
  b_original_setwise_lower_of_local_steps_phys b_coupling_local_steps_phys

end
end EinsteinFull
