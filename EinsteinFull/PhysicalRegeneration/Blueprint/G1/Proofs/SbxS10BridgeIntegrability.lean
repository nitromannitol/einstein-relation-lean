import EinsteinFull.Blueprint.G1.Proofs.SbxS10BridgeIntegrability
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.G1.Proofs.SbxS10BridgeIntegrability`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.SbxS10BridgeIntegrability
open EinsteinRelation EinsteinRelation.Regeneration
section Residual
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
end Residual
section CarrierSplit
variable {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
  (P : QuenchedPathLaws d) (G : Set (FieldPair d))
  (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
  (hminor : ∀ ω ∈ G, ∀ x : Vec d,
    ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
include hR hP hminor
end CarrierSplit
section Extension
variable {X Ω β : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace β]
end Extension

section Grid
variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
end Grid
section SplitGrid
variable {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
  (P : QuenchedPathLaws d) (G : Set (FieldPair d))
  (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
  (hminor : ∀ ω ∈ G, ∀ x : Vec d,
    ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
  (hδ₁ : δ < 1)
end SplitGrid

section CoupledGrid
variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
end CoupledGrid
section SplitCoupledGrid
variable {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
  (P : QuenchedPathLaws d) (G : Set (FieldPair d))
  (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
  (hminor : ∀ ω ∈ G, ∀ x : Vec d,
    ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
  (hδ₁ : δ < 1)
end SplitCoupledGrid

section AssembledRestart
variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
end AssembledRestart

section IntervalMarginals
variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
end IntervalMarginals
/-- The physical-kernel version of
`EinsteinFull.SbxS10BridgeIntegrability.ae_originalLaw_deterministic_restart`. -/
theorem ae_originalLaw_deterministic_restart_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (s : ℝ≥0) (A : Set (Path d)), MeasurableSet A →
      ∀ (B : Set (Path d)), MeasurableSet B → ∀ x : Vec d,
      P (x, ω) ((stopPathAt s) ⁻¹' A ∩ (gmpShiftPath s) ⁻¹' B) =
        ∫⁻ γ in (stopPathAt s) ⁻¹' A, P (γ s, ω) B ∂P (x, ω) := by
  filter_upwards [hP] with ω hω
  obtain ⟨hω, r, hr⟩ := hω
  intro s A hA B hB x
  have he := congrArg (fun μ : Measure (Path d) => μ A)
    (gmpPathLaw_prefix_future r s B hB x)
  rw [Measure.map_apply (measurable_gmpPrefixPath s) hA,
    Measure.map_apply (measurable_gmpPrefixPath s) hA,
    Measure.restrict_apply (hA.preimage (measurable_gmpPrefixPath s)),
    withDensity_apply _ (hA.preimage (measurable_gmpPrefixPath s))] at he
  have hprefix : stopPathAt (d := d) s = gmpPrefixPath s := by
    funext γ
    apply ContinuousMap.ext
    intro t
    rfl
  simpa only [hr, hprefix] using he

/-- The physical-kernel version of
`EinsteinFull.SbxS10BridgeIntegrability.ae_originalLaw_joint_restart`. -/
theorem ae_originalLaw_joint_restart_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (s : ℝ≥0) (x : Vec d),
      (P (x, ω)).map (fun γ => (stopPathAt s γ, gmpShiftPath s γ)) =
        ((P (x, ω)).map (stopPathAt s)) ⊗ₘ
          (P.comap (fun γ : Path d => (γ s, ω))
            ((continuous_eval_const s).measurable.prodMk measurable_const)) := by
  filter_upwards [ae_originalLaw_deterministic_restart_phys hd hΛ₀ Q lam h0 h1 P hP,
    isProbabilityMeasure_of_isGMPReducedKernel_phys hd hΛ₀ Q lam h0 h1 P hP]
    with ω hr hprob
  intro s x
  let J : Kernel (Path d) (Path d) := P.comap (fun γ : Path d => (γ s, ω))
    ((continuous_eval_const s).measurable.prodMk measurable_const)
  have : IsProbabilityMeasure (P (x, ω)) := hprob x
  have : IsMarkovKernel J := ⟨fun γ => hprob (γ s)⟩
  change (P (x, ω)).map (fun γ => (stopPathAt s γ, gmpShiftPath s γ)) =
    ((P (x, ω)).map (stopPathAt s)) ⊗ₘ J
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply ((measurable_stopPathAt s).prodMk (measurable_gmpShiftPath s))
    (hA.prod hB), Measure.compProd_apply_prod hA hB,
    setLIntegral_map hA (J.measurable_coe hB) (measurable_stopPathAt s)]
  change P (x, ω) ((stopPathAt s) ⁻¹' A ∩ (gmpShiftPath s) ⁻¹' B) = _
  simpa only [J, Kernel.comap_apply, stopPathAt, ContinuousMap.coe_mk, min_self]
    using hr s A hA B hB x

/-- The physical-kernel version of
`EinsteinFull.SbxS10BridgeIntegrability.ae_originalLaw_stopped_append`. -/
theorem ae_originalLaw_stopped_append_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (T U : ℝ≥0) (x : Vec d),
      (P (x, ω)).map (stopPathAt (T + U)) =
        (((P (x, ω)).map (stopPathAt T)) ⊗ₘ
          (P.comap (fun γ : Path d => (γ T, ω))
            ((continuous_eval_const T).measurable.prodMk measurable_const))).map
          (fun q => stopPathAt (T + U) (appendPaths T q.1 (stopPathAt U q.2))) := by
  filter_upwards [ae_originalLaw_joint_restart_phys hd hΛ₀ Q lam h0 h1 P hP] with ω hr
  intro T U x
  have hm : Measurable (fun q : Path d × Path d =>
      stopPathAt (T + U) (appendPaths T q.1 (stopPathAt U q.2))) :=
    (measurable_stopPathAt (T + U)).comp ((continuous_appendPaths T).measurable.comp
      (measurable_fst.prodMk ((measurable_stopPathAt U).comp measurable_snd)))
  calc
    _ = ((P (x, ω)).map (fun γ => (stopPathAt T γ, gmpShiftPath T γ))).map
        (fun q => stopPathAt (T + U) (appendPaths T q.1 (stopPathAt U q.2))) := by
      rw [Measure.map_map hm
        ((measurable_stopPathAt T).prodMk (measurable_gmpShiftPath T))]
      congr 1
      funext γ
      simp only [Function.comp_def, stopPathAt_append_stop, appendPaths_stopped_shift]
    _ = _ := congrArg (fun μ : Measure (Path d × Path d) => μ.map
      (fun q => stopPathAt (T + U) (appendPaths T q.1 (stopPathAt U q.2)))) (hr T x)

/-- The physical-kernel version of
`EinsteinFull.SbxS10BridgeIntegrability.ae_splitGridCoupledLawKernel_stoppedPath_eq`. -/
theorem ae_splitGridCoupledLawKernel_stoppedPath_eq_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (hGMP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P)
    (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (hω : ω ∈ G) (n : ℕ),
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
        (x, ⟨ω, hω⟩)).map
        (fun z => stopPathAt (((n + 1 : ℕ) : ℝ≥0) * Δ) z.1) =
      (P (x, ω)).map (stopPathAt (((n + 1 : ℕ) : ℝ≥0) * Δ)) := by
  filter_upwards [ae_originalLaw_stopped_append_phys hd hΛ₀ Q lam h0 h1 P hGMP] with ω hr
  intro x hω n
  let a : Vec d × G := (x, ⟨ω, hω⟩)
  let := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  have hre (m : ℕ) := splitGridLawKernel_stopped_prefix_recurrence Δ hΔ R δ i hR P G
    hP hminor hδ₁ hstart a m
  have hc (m : ℕ) :
      (splitGridLawKernel Δ R δ i hR P G hP hminor hδ₁ a).map
        (fun z => stopPathAt ((((m + 1 : ℕ) : ℝ≥0) * Δ) + Δ)
          (coupledConcat Δ hΔ (gridPairs z)).1) =
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a).map
        (fun z => stopPathAt ((((m + 1 : ℕ) : ℝ≥0) * Δ) + Δ) z.1) := by
    change _ = (gridCoupledLawKernel Δ hΔ
      (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor) a).map _
    rw [gridCoupledLawKernel_apply]
    change _ = Measure.map (stopPathAt _ ∘ Prod.fst)
      (Measure.map (coupledConcat Δ hΔ ∘ gridPairs)
        (splitGridLawKernel Δ R δ i hR P G hP hminor hδ₁ a))
    rw [Measure.map_map ((measurable_stopPathAt _).comp measurable_fst)
      ((measurable_coupledConcat Δ hΔ).comp measurable_gridPairs)]
    rfl
  induction n with
  | zero =>
    simpa only [Nat.zero_add, Nat.cast_one, one_mul, a] using
      splitGridCoupledLawKernel_map_firstPath Δ hΔ R δ i hR P G hP hminor hδ₁ a
  | succ n ih =>
    have hstep := (hc n).symm.trans (hre n)
    rw [← gridCoupledLawKernel_map_stoppedPath Δ hΔ
      (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor) a n] at hstep
    change (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a).map _ =
      (((splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a).map
        (fun z => stopPathAt (((n + 1 : ℕ) : ℝ≥0) * Δ) z.1)) ⊗ₘ
        (P.comap (fun γ : Path d => (γ (((n + 1 : ℕ) : ℝ≥0) * Δ), ω))
          ((continuous_eval_const _).measurable.prodMk measurable_const))).map _ at hstep
    rw [ih] at hstep
    have ho := hr (((n + 1 : ℕ) : ℝ≥0) * Δ) Δ x
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_mul, one_mul, a]
      using hstep.trans ho.symm

/-- The physical-kernel version of
`EinsteinFull.SbxS10BridgeIntegrability.ae_splitGridCoupledLawKernel_path_eq`. -/
theorem ae_splitGridCoupledLawKernel_path_eq_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (hGMP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P)
    (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (hω : ω ∈ G),
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
        (x, ⟨ω, hω⟩)).map Prod.fst = P (x, ω) := by
  filter_upwards [ae_splitGridCoupledLawKernel_stoppedPath_eq_phys hd hΛ₀ Q lam h0 h1
    Δ hΔ R δ i hR P hGMP G hP hminor hδ₁ hstart] with ω hω'
  intro x hω
  let := isMarkovKernel_splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
  apply measure_eq_of_stoppedPath_marginals Δ hΔ
  intro n
  rw [Measure.map_map (measurable_stopPathAt _) measurable_fst]
  exact hω' x hω n

/-- The physical-kernel version of
`EinsteinFull.SbxS10BridgeIntegrability.extended_splitGridCoupledLawKernel_marginals`. -/
theorem extended_splitGridCoupledLawKernel_marginals_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (hGMP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P := by
  let S := splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
  let ν : Measure (CoupledSample d) := Measure.dirac ((0 : Path d), fun _ => false)
  let K := extendEnvironmentKernel G hG S ν
  have : IsMarkovKernel S :=
    isMarkovKernel_splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
  have : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  have : IsMarkovKernel K := isMarkovKernel_extendEnvironmentKernel G hG S ν
  change HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P
  have hm := ae_splitGridCoupledLawKernel_path_eq_phys hd hΛ₀ Q lam h0 h1
    Δ hΔ R δ i hR P hGMP G hP hminor hδ₁ hstart
  constructor
  · constructor <;> filter_upwards [] with a <;> infer_instance
  · constructor
    · filter_upwards [hGae, hm] with ω hω hmω
      change (K (0, ω)).map Prod.fst = P (0, ω)
      rw [show K (0, ω) = S (0, ⟨ω, hω⟩) from
        extendEnvironmentKernel_apply_of_mem G hG S ν 0 ω hω]
      exact hmω 0 hω
    · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hGae,
        Measure.quasiMeasurePreserving_snd.ae hm] with a ha hma
      change (K a).map Prod.fst = P a
      rw [show K a = S (a.1, ⟨a.2, ha⟩) from
        extendEnvironmentKernel_apply_of_mem G hG S ν a.1 a.2 ha]
      exact hma a.1 ha

end EinsteinFull.SbxS10BridgeIntegrability
