import EinsteinFull.Calculus.C10S3CleanQuenchedStoppedTube
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Calculus.C19S3CleanHistoryParameterIntegral
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.C10S3CleanQuenchedStoppedTube`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The physical-kernel version of `EinsteinFull.Blueprint.c10_clean_history_level_restart`. -/
theorem c10_clean_history_level_restart_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) (m : ℕ)
    (A : Regeneration.CoupledSample d → ℝ)
    (hA : Measurable[Regeneration.finiteHistorySigma
      (Regeneration.Renewal.regenDelta lam) m] A)
    (F : ℝ × Regeneration.CoupledSample d → ℝ) (hF : Measurable F)
    (hbF : Regeneration.BoundedRealTest F) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    (∫ q, F (A q.2, Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂μ) =
    ∫ q, ∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1) ∂μ := by
  have hr := c19_s3_actual_history_parameter_integral_phys hd Q lam h0 h1 l δ P K hK m A hA (fun _ => 1) measurable_const
    (show Regeneration.BoundedRealTest (fun _ => 1) from ⟨1, by intro z; simp⟩)
    F hF hbF
  simpa only [one_mul] using hr


/-- The physical-kernel version of `EinsteinFull.Blueprint.c10_clean_grid_endpoint_probability`. -/
theorem c10_clean_grid_endpoint_probability_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) (m : ℕ) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
      IsProbabilityMeasure (K (q.2.1 ((m : ℝ≥0) *
        Regeneration.Renewal.regenDelta lam), q.1)) := by
  by_cases hm : m = 0
  · subst m
    have hs := Regeneration.ae_origin_start_of_isGMPReducedKernel_phys hd Q lam h0.le h1
      P K hK.1 hK.2.1 hK.2.2.1
    have hp : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
        IsProbabilityMeasure (K (0, q.1)) := by
      unfold Regeneration.annealedCoupledLaw
      apply Measure.ae_compProd_of_ae_ae
        (show MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
          IsProbabilityMeasure (K (0, q.1))} from
          by
            rw [show {q : FieldPair d × Regeneration.CoupledSample d |
              IsProbabilityMeasure (K (0, q.1))} =
              {q | K (0, q.1) Set.univ = 1} from by
                ext q
                exact ⟨fun h => h.measure_univ, fun h => ⟨h⟩⟩]
            exact ((K.measurable_coe MeasurableSet.univ)
              (measurableSet_singleton 1)).preimage (measurable_const.prodMk measurable_fst))
      filter_upwards [hK.1.1] with ω hω
      exact Filter.Eventually.of_forall fun _ => hω
    filter_upwards [hs, hp] with q hq hprob
    simpa only [Nat.cast_zero, zero_mul, hq] using hprob
  · have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
      Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
    have ht : 0 < (m : ℝ≥0) * Regeneration.Renewal.regenDelta lam :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) hΔ
    exact Regeneration.ae_at_endpoint_of_product_ae_phys hd Q lam h0.le h1 P K
      hK.1 hK.2.1 hK.2.2.1 _ ht _ hK.1.2

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c10_clean_history_level_conditional_integrable`. -/
theorem c10_clean_history_level_conditional_integrable_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) (m : ℕ)
    (A : Regeneration.CoupledSample d → ℝ) (hA : Measurable A)
    (F : ℝ × Regeneration.CoupledSample d → ℝ) (hF : Measurable F)
    (hbF : Regeneration.BoundedRealTest F) :
    let Δ := Regeneration.Renewal.regenDelta lam
    Integrable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      ∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1))
      (Regeneration.annealedCoupledLaw Q.measure K) := by
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  have : IsProbabilityMeasure μ :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let E : FieldPair d × Regeneration.CoupledSample d → Vec d × FieldPair d :=
    fun q => (q.2.1 ((m : ℝ≥0) * Δ), q.1)
  have hE : Measurable E := ((continuous_eval_const _).measurable.comp
    measurable_snd.fst).prodMk measurable_fst
  let L : Kernel (FieldPair d × Regeneration.CoupledSample d) (Regeneration.CoupledSample d) :=
    (EinsteinRelation.Probability.probabilityPart K).comap E hE
  let J : (FieldPair d × Regeneration.CoupledSample d) × Regeneration.CoupledSample d → ℝ :=
    fun q => F (A q.1.2, q.2)
  have hJ : Measurable J := hF.comp (((hA.comp measurable_fst.snd)).prodMk measurable_snd)
  let G : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q => ∫ w, J (q, w) ∂L q
  have hG : Measurable G := (hJ.stronglyMeasurable.integral_kernel_prod_right' (κ := L)).measurable
  obtain ⟨C, hC⟩ := hbF
  have hC0 : 0 ≤ C := (abs_nonneg (F (0, (0, fun _ => false)))).trans (hC _)
  have hbG : ∀ q, ‖G q‖ ≤ C := by
    intro q
    dsimp only [G, L, E, Kernel.comap_apply]
    by_cases hp : K (q.2.1 ((m : ℝ≥0) * Δ), q.1) Set.univ = 1
    · have : IsProbabilityMeasure (K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) := ⟨hp⟩
      rw [EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure]
      simpa using norm_integral_le_of_norm_le_const
        (μ := K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) (f := fun w => J (q, w)) (C := C)
        (Filter.Eventually.of_forall fun w => by
          simpa only [Real.norm_eq_abs, J] using hC (A q.2, w))
    · simp only [EinsteinRelation.Probability.probabilityPart_apply, ite_eq_right hp,
        integral_zero_measure, norm_zero]
      exact hC0
  have hi : Integrable G μ := Integrable.of_bound hG.aestronglyMeasurable C
    (Filter.Eventually.of_forall hbG)
  apply hi.congr
  filter_upwards [c10_clean_grid_endpoint_probability_phys hd Q lam h0 h1 l δ P K hK m] with q hq
  have := hq
  simp only [G, J, L, E, Kernel.comap_apply, Δ,
    EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure]

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c10_clean_grid_endpoint_path_marginal`. -/
theorem c10_clean_grid_endpoint_path_marginal_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) (m : ℕ) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
      (K (q.2.1 ((m : ℝ≥0) * Regeneration.Renewal.regenDelta lam), q.1)).map Prod.fst =
        P (q.2.1 ((m : ℝ≥0) * Regeneration.Renewal.regenDelta lam), q.1) := by
  by_cases hm : m = 0
  · subst m
    have hs := Regeneration.ae_origin_start_of_isGMPReducedKernel_phys hd Q lam h0.le h1
      P K hK.1 hK.2.1 hK.2.2.1
    have hqmp : Measure.QuasiMeasurePreserving
        (Prod.fst : FieldPair d × Regeneration.CoupledSample d → FieldPair d)
        (Regeneration.annealedCoupledLaw Q.measure K) Q.measure := by
      refine ⟨measurable_fst, ?_⟩
      rw [c10_clean_annealed_environment_map Q K hK.1]
    have hpq := hqmp.ae hK.2.1.1
    filter_upwards [hs, hpq] with q hq hp
    simpa only [Nat.cast_zero, zero_mul, hq] using hp
  · have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
      Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
    have ht : 0 < (m : ℝ≥0) * Regeneration.Renewal.regenDelta lam :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) hΔ
    exact Regeneration.ae_at_endpoint_of_product_ae_phys hd Q lam h0.le h1 P K
      hK.1 hK.2.1 hK.2.2.1 _ ht _ hK.2.1.2

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c10_clean_grid_endpoint_guard_prefix_bound`. -/
theorem c10_clean_grid_endpoint_guard_prefix_bound_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (hrestart : ∀ (ω : FieldPair d)
      (hω : IsRegular (sourceReducedBound Λ₀) ω)
      (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        ω hω lam h0.le h1)
      (x : Vec d) (a : ℝ) (N : ℕ),
      let Δ := Regeneration.Renewal.regenDelta lam
      let R := l / lam
      let i := Regeneration.Renewal.forceCoord hd
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
      ((r.pathLaw x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
        Measure.bind ((r.pathLaw x).restrict A) (fun γ => r.pathLaw (γ ((T γ).untopD 0))))
    (ε : ℝ) (hTube : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      ENNReal.ofReal ε ≤ P (x, ω) {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0)
        (Regeneration.Renewal.regenDelta lam), euclideanNorm (γ s - x) ≤ (l / lam) / 2})
    (m : ℕ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, ∀ (a : ℝ) (N : ℕ),
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
      let B : Set (Path d) := {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
        euclideanNorm (γ ((T γ).toNNReal + s) - γ (T γ).toNNReal) ≤ R / 2}
      ENNReal.ofReal ε * K (q.2.1 ((m : ℝ≥0) * Δ), q.1) (Prod.fst ⁻¹' A) ≤
        K (q.2.1 ((m : ℝ≥0) * Δ), q.1) (Prod.fst ⁻¹' (A ∩ B)) := by
  dsimp only
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.fst : FieldPair d × Regeneration.CoupledSample d → FieldPair d)
      (Regeneration.annealedCoupledLaw Q.measure K) Q.measure := by
    refine ⟨measurable_fst, ?_⟩
    rw [c10_clean_annealed_environment_map Q K hK.1]
  have he := hqmp.ae (hK.2.2.1.and hTube)
  have hm := c10_clean_grid_endpoint_path_marginal_phys hd Q lam h0 h1 l δ P K hK m
  filter_upwards [he, hm] with q henv hpath
  obtain ⟨⟨hω, r, hr⟩, htube⟩ := henv
  have htube' : ∀ y, ENNReal.ofReal ε ≤ r.pathLaw y
      {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Regeneration.Renewal.regenDelta lam),
        euclideanNorm (γ s - y) ≤ (l / lam) / 2} := by
    intro y
    rw [← hr y]
    exact htube y
  intro a N
  exact c10_clean_coupled_guard_prefix_tube_bound hd q.1 lam
    (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter) hω h0.le h1 r
    (K (q.2.1 ((m : ℝ≥0) * Regeneration.Renewal.regenDelta lam), q.1)) _
    (hpath.trans (hr _)) _ _ a _ N _ (hrestart q.1 hω r _ a N) htube'

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c10_clean_grid_endpoint_guard_prefix_real_bound`. -/
theorem c10_clean_grid_endpoint_guard_prefix_real_bound_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (hrestart : ∀ (ω : FieldPair d)
      (hω : IsRegular (sourceReducedBound Λ₀) ω)
      (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        ω hω lam h0.le h1)
      (x : Vec d) (a : ℝ) (N : ℕ),
      let Δ := Regeneration.Renewal.regenDelta lam
      let R := l / lam
      let i := Regeneration.Renewal.forceCoord hd
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
      ((r.pathLaw x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
        Measure.bind ((r.pathLaw x).restrict A) (fun γ => r.pathLaw (γ ((T γ).untopD 0))))
    (ε : ℝ) (hε : 0 ≤ ε) (hTube : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      ENNReal.ofReal ε ≤ P (x, ω) {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0)
        (Regeneration.Renewal.regenDelta lam), euclideanNorm (γ s - x) ≤ (l / lam) / 2})
    (m : ℕ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, ∀ (a : ℝ) (N : ℕ),
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
      let B : Set (Path d) := {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
        euclideanNorm (γ ((T γ).toNNReal + s) - γ (T γ).toNNReal) ≤ R / 2}
      ε * (K (q.2.1 ((m : ℝ≥0) * Δ), q.1)).real (Prod.fst ⁻¹' A) ≤
        (K (q.2.1 ((m : ℝ≥0) * Δ), q.1)).real (Prod.fst ⁻¹' (A ∩ B)) := by
  dsimp only
  filter_upwards [c10_clean_grid_endpoint_probability_phys hd Q lam h0 h1 l δ P K hK m,
    c10_clean_grid_endpoint_guard_prefix_bound_phys hd Q lam h0 h1 l δ P K hK hrestart ε hTube m]
    with q hprob hbound
  have := hprob
  intro a N
  have h := ENNReal.toReal_mono (measure_ne_top _ _) (hbound a N)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε, Measure.real_def] using h

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c10_clean_stopped_tube_of_uniform_quenched_tube`. -/
theorem c10_clean_stopped_tube_of_uniform_quenched_tube_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (hrestart : ∀ (ω : FieldPair d)
      (hω : IsRegular (sourceReducedBound Λ₀) ω)
      (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        ω hω lam h0.le h1)
      (x : Vec d) (a : ℝ) (N : ℕ),
      let Δ := Regeneration.Renewal.regenDelta lam
      let R := l / lam
      let i := Regeneration.Renewal.forceCoord hd
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
      ((r.pathLaw x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
        Measure.bind ((r.pathLaw x).restrict A) (fun γ => r.pathLaw (γ ((T γ).untopD 0))))
    (ε : ℝ) (hε : 0 < ε)
    (hTube : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, ENNReal.ofReal ε ≤ P (x, ω)
      {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Regeneration.Renewal.regenDelta lam),
        euclideanNorm (γ s - x) ≤ (l / lam) / 2}) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let μ := Regeneration.annealedCoupledLaw Q.measure K; let E := c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; let Tube := {q : FieldPair d × Regeneration.CoupledSample d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ, euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 ((c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) - (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 (c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}; ε * μ.real E ≤ μ.real (E ∩ Tube) := by
  classical
  dsimp only
  intro m A hA N
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let V : Set (ℝ × Path d) := {p |
    Regeneration.passageSequence Δ lam R p.1 p.2 i (2 * N) < ⊤ ∧
    ∀ k < N, Regeneration.passageSequence Δ lam R p.1 p.2 i (2 * k) ≠ ⊤ ∧
      ¬Regeneration.IsGoodPassage Δ lam R p.1 p.2 i (2 * k)}
  let B : Set (ℝ × Path d) := {p | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
    euclideanNorm (p.2 ((Regeneration.passageSequence Δ lam R p.1 p.2 i
      (2 * N)).toNNReal + s) - p.2 (Regeneration.passageSequence Δ lam R
      p.1 p.2 i (2 * N)).toNNReal) ≤ R / 2}
  have hV : MeasurableSet V := c10_clean_joint_guard_prefix_measurable Δ lam R i N
  have hB : MeasurableSet B := c10_clean_joint_passage_tube_measurable Δ lam R i N
  let S : Set (ℝ × Regeneration.CoupledSample d) :=
    (fun p => (p.1, p.2.1)) ⁻¹' V
  let U : Set (ℝ × Regeneration.CoupledSample d) :=
    (fun p => (p.1, p.2.1)) ⁻¹' (V ∩ B)
  have hS : MeasurableSet S := hV.preimage (measurable_fst.prodMk measurable_snd.fst)
  have hU : MeasurableSet U := (hV.inter hB).preimage (measurable_fst.prodMk measurable_snd.fst)
  let F : ℝ × Regeneration.CoupledSample d → ℝ := S.indicator (fun _ => 1)
  let G : ℝ × Regeneration.CoupledSample d → ℝ := U.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hS
  have hG : Measurable G := measurable_const.indicator hU
  have hbF : Regeneration.BoundedRealTest F := by
    refine ⟨1, fun p => ?_⟩
    by_cases hp : p ∈ S <;> simp [F, hp]
  have hbG : Regeneration.BoundedRealTest G := by
    refine ⟨1, fun p => ?_⟩
    by_cases hp : p ∈ U <;> simp [G, hp]
  have hAg : Measurable A := hA.mono (EinsteinRelation.Probability.finiteHistorySigma_le Δ m) le_rfl
  have hiF := c10_clean_history_level_conditional_integrable_phys hd Q lam h0 h1 l δ P K hK m A hAg F hF hbF
  have hiG := c10_clean_history_level_conditional_integrable_phys hd Q lam h0 h1 l δ P K hK m A hAg G hG hbG
  have hrF := c10_clean_history_level_restart_phys hd Q lam h0 h1 l δ P K hK m A hA F hF hbF
  have hrG := c10_clean_history_level_restart_phys hd Q lam h0 h1 l δ P K hK m A hA G hG hbG
  let E : Set (FieldPair d × Regeneration.CoupledSample d) :=
    c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
      {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
  let Tube : Set (FieldPair d × Regeneration.CoupledSample d) := {q |
    ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
        ((c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) -
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
          (c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}
  let H : FieldPair d × Regeneration.CoupledSample d → ℝ × Path d := fun q =>
    (A q.2, (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1)
  have hH : Measurable H := (hAg.comp measurable_snd).prodMk
    (((Regeneration.measurable_sampleTimeShift Δ).comp
      (measurable_const.prodMk measurable_snd)).fst)
  have hE : E = H ⁻¹' V := c10_clean_guard_prefix_event_eq Δ lam R A m i N
  have hTube' : Tube = H ⁻¹' B := by
    ext q
    rfl
  have hEm : MeasurableSet E := by
    rw [hE]
    exact hV.preimage hH
  have hETm : MeasurableSet (E ∩ Tube) := by
    rw [hE, hTube']
    exact (hV.inter hB).preimage hH
  have houterF : (∫ q, F (A q.2, Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂μ) = μ.real E := by
    rw [← integral_indicator_one hEm]
    apply integral_congr_ae
    filter_upwards [] with q
    by_cases hq : H q ∈ V <;> simp [F, S, hE, H, hq] at *
  have houterG : (∫ q, G (A q.2, Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂μ) = μ.real (E ∩ Tube) := by
    rw [← integral_indicator_one hETm]
    apply integral_congr_ae
    filter_upwards [] with q
    simp only [G, U, hE, hTube', H, Set.indicator_apply,
      Set.mem_preimage, Set.mem_inter_iff, Pi.one_apply]
  have hbound : ∀ᵐ q ∂μ,
      ε * (∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) ≤
        ∫ w, G (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1) := by
    filter_upwards [c10_clean_grid_endpoint_guard_prefix_real_bound_phys hd Q lam h0 h1 l δ P K hK hrestart ε hε.le hTube m] with q hq
    let Vq : Set (Regeneration.CoupledSample d) := {w | (A q.2, w.1) ∈ V}
    let Uq : Set (Regeneration.CoupledSample d) := {w | (A q.2, w.1) ∈ V ∩ B}
    have hVq : MeasurableSet Vq := hV.preimage (measurable_const.prodMk measurable_fst)
    have hUq : MeasurableSet Uq := (hV.inter hB).preimage (measurable_const.prodMk measurable_fst)
    have hif : (∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) =
        (K (q.2.1 ((m : ℝ≥0) * Δ), q.1)).real Vq := by
      rw [← integral_indicator_one hVq]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [F, S, Vq, Set.indicator_apply, Set.mem_preimage, Set.mem_ofPred_eq, Pi.one_apply]
    have hig : (∫ w, G (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) =
        (K (q.2.1 ((m : ℝ≥0) * Δ), q.1)).real Uq := by
      rw [← integral_indicator_one hUq]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [G, U, Uq, Set.indicator_apply, Set.mem_preimage,
        Set.mem_ofPred_eq, Set.mem_inter_iff, Pi.one_apply]
    rw [hif, hig]
    simpa [Vq, Uq, V, B, Δ, R, i, Set.preimage_inter, Set.ofPred_and] using hq (A q.2) N
  have hm := integral_mono_ae (hiF.const_mul ε) hiG hbound
  rw [integral_const_mul, ← hrF, ← hrG, houterF, houterG] at hm
  exact hm

end EinsteinFull.Blueprint
