import EinsteinFull.Blueprint.G1.Proofs.SbxS10BridgeIntegrability
import EinsteinFull.Regeneration.TrajectoryShift

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

namespace EinsteinFull.SbxS1SplitGridFreshBits
open EinsteinRelation EinsteinRelation.Regeneration EinsteinFull.SbxS10BridgeIntegrability

/-- The split-grid construction has a fresh coin at every finite history. -/
theorem splitGrid_freshBit (d : ℕ) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R δ : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (a : Vec d × G) (n : ℕ) (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H)
    (hb : BoundedRealTest H) :
    (∫ z, H z * (if z.2 n = true then (1 : ℝ) else 0)
      ∂splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a) =
      δ * ∫ z, H z ∂splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a := by
  cases n with
  | zero => exact splitGridCoupledLawKernel_freshBit_zero Δ hΔ R δ i hR P G hP hminor hδ₀ hδ₁ hstart a H hH
  | succ n => exact splitGridCoupledLawKernel_freshBit_succ Δ hΔ R δ i hR P G hP hminor hδ₀ hδ₁ hstart a n H hH hb

/-- Both almost-everywhere clauses hold for the same extended split kernel. -/
theorem extended_splitGrid_freshBits {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R δ : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    HasFreshBits Q.measure Δ δ K := by
  let S := splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
  let ν : Measure (CoupledSample d) := Measure.dirac ((0 : Path d), fun _ => false)
  let K := extendEnvironmentKernel G hG S ν
  change HasFreshBits Q.measure Δ δ K
  have hf (x : Vec d) (ω : FieldPair d) (hω : ω ∈ G) : FreshBitsAt Δ δ K (x, ω) := by
    intro n H hH hb
    rw [show K (x, ω) = S (x, ⟨ω, hω⟩) from
      extendEnvironmentKernel_apply_of_mem G hG S ν x ω hω]
    exact splitGrid_freshBit d Δ hΔ R δ i hR P G hP hminor hδ₀ hδ₁ hstart _ n H hH hb
  constructor
  · filter_upwards [hGae] with ω hω
    exact hf 0 ω hω
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hGae] with a ha
    exact hf a.1 a.2 ha

/-- Probability, path marginals, and fresh bits belong to the same construction. -/
theorem extended_splitGrid_marginals_and_freshBits {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (hGMP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P ∧ HasFreshBits Q.measure Δ δ K := by
  exact ⟨(extended_splitGridCoupledLawKernel_marginals hd hΛ₀ Q lam h0 h1 Δ hΔ R δ i hR P hGMP G hG hGae hP hminor hδ₁ hstart).1,
    (extended_splitGridCoupledLawKernel_marginals hd hΛ₀ Q lam h0 h1 Δ hΔ R δ i hR P hGMP G hG hGae hP hminor hδ₁ hstart).2,
    extended_splitGrid_freshBits Q Δ hΔ R δ i hR P G hG hGae hP hminor hδ₀ hδ₁ hstart⟩

/-- The successful branch of the actual split step has the source endpoint average. -/
theorem splitStep_successful_endpoint {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ)
    (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (a : Vec d × G)
    (φ : Vec d → ℝ) (hφ : Measurable φ) (hb : BoundedRealTest φ) :
    (∫ q, (if q.2 = true then (1 : ℝ) else 0) * φ (q.1 Δ)
      ∂splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor a) =
      δ * endpointAverage i R a.1 φ := by
  have := hP a.2.1 a.2.2 a.1
  have hf : Measurable (fun γ : Path d => φ (γ Δ)) :=
    hφ.comp (continuous_eval_const Δ).measurable
  have hb' : BoundedRealTest (fun γ : Path d => φ (γ Δ)) := by
    obtain ⟨C, hC⟩ := hb
    exact ⟨C, fun γ => hC (γ Δ)⟩
  have h := (splitStepKernelOnEnvironments_integral_bit Δ R δ i hR P G hP hminor
    hδ₀ hδ₁ a true (fun γ => φ (γ Δ)) hf hb').2
  simpa only [↓reduceIte, Blueprint.sbxS4_integral_killedBridgeMixture_endpoint
    Δ R δ i P a.1 a.2.1 hR hδ₀ (hminor a.2.1 a.2.2 a.1) φ hφ] using h

/-- Every successful sampled segment stays in its actual restart region. -/
theorem splitGrid_sampled_success_support {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ)
    (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1) (a : Vec d × G) :
    let K := splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor
    letI := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
    ∀ᵐ z ∂gridLawKernel Δ K a, ∀ n : ℕ,
      (gridPairs z n).2 = true →
      (gridPairs z n).1 Δ ∈ endpointBall i R
        (gridHistoryStart Δ n (Preorder.frestrictLe n z)).1 ∧
      ∀ t : ℝ≥0, t ≤ Δ → (gridPairs z n).1 t ∈ couplingRegion i R
        (gridHistoryStart Δ n (Preorder.frestrictLe n z)).1 := by
  let K := splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor
  let := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  apply ae_all_iff.mpr
  intro n
  have hm : Measurable (fun z : (j : ℕ) → gridState d G j =>
      (Preorder.frestrictLe n z, z (n + 1))) :=
    (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  have hp := Blueprint.sbxS4_measurableSet_success_support Δ R i
    (fun h : gridHistory d G n => (gridHistoryStart Δ n h).1)
    (measurable_gridHistoryStart Δ n).fst
  apply (ae_map_iff hm.aemeasurable hp).mp
  rw [gridLawKernel_map_prefix_next]
  apply Measure.ae_compProd_of_ae_ae hp
  apply ae_of_all
  intro h
  change ∀ᵐ q ∂K (gridHistoryStart Δ n h), _
  rw [splitStepKernelOnEnvironments_apply]
  exact Blueprint.sbxS4_firstSegmentLaw_ae_success_support Δ R δ i P
    (gridHistoryStart Δ n h).1 (gridHistoryStart Δ n h).2.1

/-- Successful sampled segments retain their tube after literal concatenation. -/
theorem splitGrid_concat_success_support {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R δ : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (a : Vec d × G) :
    let K := splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor
    letI := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
    ∀ᵐ z ∂gridLawKernel Δ K a, ∀ n : ℕ, (gridPairs z n).2 = true →
      ∀ t : ℝ≥0, t ≤ Δ →
        (coupledConcat Δ hΔ (gridPairs z)).1 ((n : ℝ≥0) * Δ + t) ∈
          couplingRegion i R ((coupledConcat Δ hΔ (gridPairs z)).1 ((n : ℝ≥0) * Δ)) := by
  let K := splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor
  let := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  have hs := splitGrid_sampled_success_support Δ R δ i hR P G hP hminor hδ₁ a
  have hc := ae_gridLawKernel_concat_segments Δ hΔ K
    (ae_splitStepKernel_starts Δ R δ i hR P G hP hminor hδ₁ hstart) a
  have hq := ae_all_iff.mpr (fun n : ℕ => ae_gridLawKernel_step_starts Δ K
    (ae_splitStepKernel_starts Δ R δ i hR P G hP hminor hδ₁ hstart) a n)
  filter_upwards [hs, hc, hq] with z hs hc hq n hn t ht
  have hzero := hc n 0 (show (0 : ℝ≥0) ≤ Δ from bot_le)
  simp only [add_zero] at hzero
  have hbase : (gridPairs z n).1 0 =
      (gridHistoryStart Δ n (Preorder.frestrictLe n z)).1 := hq n
  rw [hc n t ht, hzero, hbase]
  exact (hs n hn).2 t ht

/-- The assembled split law retains successful tube support at each grid interval. -/
theorem splitGrid_local_success_support {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R δ : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (a : Vec d × G) :
    ∀ᵐ z ∂splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a,
      ∀ n : ℕ, z.2 n = true → ∀ t : ℝ≥0, t ≤ Δ →
        z.1 ((n : ℝ≥0) * Δ + t) ∈ couplingRegion i R (z.1 ((n : ℝ≥0) * Δ)) := by
  let K := splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor
  let := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  change ∀ᵐ z ∂gridCoupledLawKernel Δ hΔ K a, _
  rw [gridCoupledLawKernel_apply]
  apply ae_all_iff.mpr
  intro n
  have hb : Measurable (fun z : CoupledSample d => z.1 ((n : ℝ≥0) * Δ)) :=
    (continuous_eval_const _).measurable.comp measurable_fst
  have hp : MeasurableSet {z : CoupledSample d | z.2 n = true →
      ∀ t : ℝ≥0, t ≤ Δ → z.1 ((n : ℝ≥0) * Δ + t) ∈
        couplingRegion i R (z.1 ((n : ℝ≥0) * Δ))} := by
    have he := (Renewal.isOpen_killedSegment_event Δ R i).measurableSet.preimage
      (hb.prodMk ((measurable_gridIntervalSample Δ n).fst))
    have hc : MeasurableSet {z : CoupledSample d | z.2 n = true} :=
      measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const
    apply hc.imp
    convert he using 1
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, gridIntervalSample, ContinuousMap.coe_mk]
    exact forall_congr' fun t => imp_congr_right fun ht => by rw [min_eq_left ht]
  apply (ae_map_iff ((measurable_coupledConcat Δ hΔ).comp measurable_gridPairs).aemeasurable hp).mpr
  filter_upwards [splitGrid_concat_success_support Δ hΔ R δ i hR P G hP hminor hδ₁ hstart a] with z hz
  exact hz n

/-- Successful bridges satisfy the literal absolute-time support assertion. -/
theorem splitGrid_success_support {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R δ : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (a : Vec d × G) :
    ∀ᵐ z ∂splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a,
      ∀ n : ℕ, z.2 n = true → ∀ t : ℝ≥0,
        (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
        z.1 t ∈ couplingRegion i R (z.1 ((n : ℝ≥0) * Δ)) := by
  filter_upwards [splitGrid_local_success_support Δ hΔ R δ i hR P G hP hminor hδ₁ hstart a] with z hz
  intro n hn t hlow hhigh
  have hu : t - (n : ℝ≥0) * Δ ≤ Δ := by
    apply tsub_le_iff_right.mpr
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using hhigh
  have h := hz n hn (t - (n : ℝ≥0) * Δ) hu
  rwa [add_tsub_cancel_of_le hlow] at h

/-- The same extended split kernel has successful bridge support on both fibres. -/
theorem extended_splitGrid_success_support {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R δ : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
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
    HasSuccessfulBridgeSupport Q.measure Δ i R K := by
  let S := splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
  let ν : Measure (CoupledSample d) := Measure.dirac ((0 : Path d), fun _ => false)
  let K := extendEnvironmentKernel G hG S ν
  change HasSuccessfulBridgeSupport Q.measure Δ i R K
  have hf (x : Vec d) (ω : FieldPair d) (hω : ω ∈ G) :
      SuccessfulBridgeSupportAt Δ i R K (x, ω) := by
    unfold SuccessfulBridgeSupportAt
    rw [show K (x, ω) = S (x, ⟨ω, hω⟩) from
      extendEnvironmentKernel_apply_of_mem G hG S ν x ω hω]
    exact splitGrid_success_support Δ hΔ R δ i hR P G hP hminor hδ₁ hstart _
  constructor
  · filter_upwards [hGae] with ω hω
    exact hf 0 ω hω
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hGae] with a ha
    exact hf a.1 a.2 ha

/-- The successful endpoint identity on the initial grid interval. -/
theorem splitGrid_successful_endpoint_zero {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (a : Vec d × G) (H : CoupledSample d → ℝ) (φ : Vec d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 0) inferInstance H)
    (hφ : Measurable φ) (hbφ : BoundedRealTest φ) :
    (∫ z, H z * (if z.2 0 = true then (1 : ℝ) else 0) * φ (z.1 Δ)
      ∂splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a) =
      δ * ∫ z, H z * endpointAverage i R (z.1 0) φ
        ∂splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a := by
  let K := splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor
  have : IsMarkovKernel K :=
    isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  have hs : ∀ᵐ q ∂K a, q.1 0 = a.1 :=
    ae_splitStepKernel_starts Δ R δ i hR P G hP hminor hδ₁ hstart a
  let c : CoupledSample d := (⟨fun _ => a.1, continuous_const⟩, fun _ => false)
  let F : Path d × Bool → ℝ := fun q => H (⟨fun _ => q.1 0, continuous_const⟩, fun _ => false)
  have hpath : Measurable (fun q : Path d × Bool => (⟨fun _ => q.1 0, continuous_const⟩ : Path d)) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (continuous_eval_const 0).measurable.comp measurable_fst
  have hFm : Measurable F :=
    (hH.mono (Probability.finiteHistorySigma_le Δ 0) le_rfl).comp (hpath.prodMk measurable_const)
  have hbit : Measurable (fun q : Path d × Bool => if q.2 = true then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const measurable_const
  have hFz (z : CoupledSample d) : F (gridIntervalSample Δ 0 z) = H z := by
    have he : (⟨fun _ => (gridIntervalSample Δ 0 z).1 0, continuous_const⟩, fun _ => false) =
        Probability.stoppedHistorySample Δ 0 z := by
      apply Prod.ext
      · apply ContinuousMap.ext
        intro t
        simp [gridIntervalSample, Probability.stoppedHistorySample]
      · funext k
        simp [Probability.stoppedHistorySample]
    exact (congrArg H he).trans (Probability.finiteHistory_test_stopped Δ 0 H hH z)
  have hg : Measurable (fun q : Path d × Bool => (stopPathAt Δ q.1, q.2)) :=
    ((measurable_stopPathAt Δ).comp measurable_fst).prodMk measurable_snd
  have hϕ : Measurable (fun q : Path d × Bool => φ (q.1 Δ)) :=
    hφ.comp ((continuous_eval_const Δ).measurable.comp measurable_fst)
  have hϕ0 : Measurable (fun q : Path d × Bool => endpointAverage i R (q.1 0) φ) := by
    exact measurable_endpointAverage i R (fun q : Path d × Bool => q.1 0)
      ((continuous_eval_const 0).measurable.comp measurable_fst)
      (fun p : (Path d × Bool) × Vec d => φ p.2) (hφ.comp measurable_snd)
  have hfirst := gridCoupledLawKernel_map_firstInterval Δ hΔ K a
  have hI := integral_map_of_stronglyMeasurable (μ := gridCoupledLawKernel Δ hΔ K a)
    (measurable_gridIntervalSample Δ 0) ((hFm.mul hbit).mul hϕ).stronglyMeasurable
  have hJ := integral_map_of_stronglyMeasurable (μ := gridCoupledLawKernel Δ hΔ K a)
    (measurable_gridIntervalSample Δ 0) (hFm.mul hϕ0).stronglyMeasurable
  rw [hfirst, integral_map_of_stronglyMeasurable hg
    ((hFm.mul hbit).mul hϕ).stronglyMeasurable] at hI
  rw [hfirst, integral_map_of_stronglyMeasurable hg (hFm.mul hϕ0).stronglyMeasurable] at hJ
  have hc (q : Path d × Bool) (hq : q.1 0 = a.1) :
      F (stopPathAt Δ q.1, q.2) = H c := by
    simp [F, c, stopPathAt, hq]
  have he := splitStep_successful_endpoint Δ R δ i hR P G hP hminor hδ₀ hδ₁ a φ hφ hbφ
  change (∫ z, H z * (if z.2 0 = true then (1 : ℝ) else 0) * φ (z.1 Δ)
      ∂gridCoupledLawKernel Δ hΔ K a) =
      δ * ∫ z, H z * endpointAverage i R (z.1 0) φ ∂gridCoupledLawKernel Δ hΔ K a
  change (∫ q, F (stopPathAt Δ q.1, q.2) *
      (if q.2 = true then (1 : ℝ) else 0) * φ ((stopPathAt Δ q.1) Δ) ∂K a) =
    ∫ z, F (gridIntervalSample Δ 0 z) *
      (if (gridIntervalSample Δ 0 z).2 = true then (1 : ℝ) else 0) *
      φ ((gridIntervalSample Δ 0 z).1 Δ) ∂gridCoupledLawKernel Δ hΔ K a at hI
  change (∫ q, F (stopPathAt Δ q.1, q.2) *
      endpointAverage i R ((stopPathAt Δ q.1) 0) φ ∂K a) =
    ∫ z, F (gridIntervalSample Δ 0 z) *
      endpointAverage i R ((gridIntervalSample Δ 0 z).1 0) φ
      ∂gridCoupledLawKernel Δ hΔ K a at hJ
  simp_rw [hFz] at hI hJ
  simp only [gridIntervalSample, ContinuousMap.coe_mk, Nat.cast_zero, zero_mul, zero_add,
    min_self, zero_min] at hI hJ
  have hi : (∫ q, F (stopPathAt Δ q.1, q.2) *
      (if q.2 = true then (1 : ℝ) else 0) * φ ((stopPathAt Δ q.1) Δ) ∂K a) =
      H c * (δ * endpointAverage i R a.1 φ) := by
    calc
      _ = H c * ∫ q, (if q.2 = true then (1 : ℝ) else 0) * φ (q.1 Δ) ∂K a := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hs] with q hq
        rw [hc q hq]
        simp [stopPathAt]
      _ = _ := by rw [he]
  have hj : (∫ q, F (stopPathAt Δ q.1, q.2) *
      endpointAverage i R ((stopPathAt Δ q.1) 0) φ ∂K a) =
      H c * endpointAverage i R a.1 φ := by
    calc
      _ = ∫ _q, H c * endpointAverage i R a.1 φ ∂K a := by
        apply integral_congr_ae
        filter_upwards [hs] with q hq
        rw [hc q hq]
        simp [stopPathAt, hq]
      _ = _ := by simp
  rw [hi] at hI
  rw [hj] at hJ
  rw [← hI, ← hJ]
  ring

/-- Successful endpoint identity against an arbitrary bounded stopped history
at a positive grid index. -/
theorem splitGrid_successful_endpoint_succ {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (a : Vec d × G) (n : ℕ) (H : CoupledSample d → ℝ) (φ : Vec d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ (n + 1)) inferInstance H)
    (hbH : BoundedRealTest H) (hφ : Measurable φ) (hbφ : BoundedRealTest φ) :
    (∫ z, H z * (if z.2 (n + 1) = true then (1 : ℝ) else 0) *
      φ (z.1 (((n + 2 : ℕ) : ℝ≥0) * Δ))
      ∂splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a) =
      δ * ∫ z, H z * endpointAverage i R (z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) φ
        ∂splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a := by
  let K := splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor
  have : IsMarkovKernel K :=
    isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  have hs : ∀ a : Vec d × G, ∀ᵐ q ∂K a, q.1 0 = a.1 :=
    ae_splitStepKernel_starts Δ R δ i hR P G hP hminor hδ₁ hstart
  let T : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0) * Δ
  let A : CoupledSample d → ℝ := fun z => endpointAverage i R (z.1 T) φ
  have hHm : Measurable H := hH.mono (Probability.finiteHistorySigma_le Δ (n + 1)) le_rfl
  have hbit : Measurable (fun q : Path d × Bool => if q.2 = true then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      measurable_const measurable_const
  have hφm : Measurable (fun q : Path d × Bool => φ (q.1 Δ)) :=
    hφ.comp ((continuous_eval_const Δ).measurable.comp measurable_fst)
  have hAm : Measurable A :=
    measurable_endpointAverage i R (fun z : CoupledSample d => z.1 T)
      ((continuous_eval_const T).measurable.comp measurable_fst)
      (fun p : CoupledSample d × Vec d => φ p.2) (hφ.comp measurable_snd)
  have hbA : BoundedRealTest A :=
    boundedRealTest_endpointAverage i R hR (fun z : CoupledSample d => z.1 T)
      (fun p : CoupledSample d × Vec d => φ p.2) (by
        obtain ⟨C, hC⟩ := hbφ
        exact ⟨C, fun p => hC p.2⟩)
  obtain ⟨C, hC⟩ := hbH
  have ⟨D, hD⟩ := hbφ
  obtain ⟨E, hE⟩ := hbA
  have hC' : ∀ z, ‖H z‖ ≤ C := by simpa only [Real.norm_eq_abs] using hC
  have hD' : ∀ x, ‖φ x‖ ≤ D := by simpa only [Real.norm_eq_abs] using hD
  have hE' : ∀ z, ‖A z‖ ≤ E := by simpa only [Real.norm_eq_abs] using hE
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (H (0, fun _ => false))) (hC' _)
  have hD0 : 0 ≤ D := le_trans (norm_nonneg (φ 0)) (hD' _)
  have hE0 : 0 ≤ E := le_trans (norm_nonneg (A (0, fun _ => false))) (hE' _)
  have hF : Measurable (fun z : CoupledSample d × (Path d × Bool) =>
      H z.1 * (if z.2.2 = true then (1 : ℝ) else 0) * φ (z.2.1 Δ)) :=
    ((hHm.comp measurable_fst).mul (hbit.comp measurable_snd)).mul (hφm.comp measurable_snd)
  have hFb : ∃ B : ℝ, ∀ z : CoupledSample d × (Path d × Bool),
      ‖H z.1 * (if z.2.2 = true then (1 : ℝ) else 0) * φ (z.2.1 Δ)‖ ≤ B := by
    refine ⟨C * D, fun z => ?_⟩
    by_cases hz : z.2.2 = true
    · simpa only [hz, ↓reduceIte, mul_one, norm_mul] using
        mul_le_mul (hC' z.1) (hD' (z.2.1 Δ)) (norm_nonneg _) hC0
    · simp [hz, mul_nonneg hC0 hD0]
  have hG : Measurable (fun z : CoupledSample d × (Path d × Bool) => H z.1 * A z.1) :=
    (hHm.comp measurable_fst).mul (hAm.comp measurable_fst)
  have hGb : ∃ B : ℝ, ∀ z : CoupledSample d × (Path d × Bool), ‖H z.1 * A z.1‖ ≤ B := by
    refine ⟨C * E, fun z => ?_⟩
    simpa only [norm_mul] using mul_le_mul (hC' z.1) (hE' z.1) (norm_nonneg _) hC0
  have hI := gridCoupledLawKernel_integral_stopped_nextInterval Δ hΔ K hs a n _ hF hFb
  have hJ := gridCoupledLawKernel_integral_stopped_nextInterval Δ hΔ K hs a n _ hG hGb
  have ha : ∀ᵐ h ∂gridPrefixKernel Δ K (n + 1) a,
      (gridStoppedHistory Δ hΔ n h).1 T = (gridHistoryStart Δ (n + 1) h).1 :=
    ae_gridPrefixKernel_stopped_endpoint Δ hΔ K hs a n
  have hi : (∫ h, ∫ q, H (gridStoppedHistory Δ hΔ n h) *
        (if q.2 = true then (1 : ℝ) else 0) * φ ((stopPathAt Δ q.1) Δ)
        ∂K (gridHistoryStart Δ (n + 1) h) ∂gridPrefixKernel Δ K (n + 1) a) =
      ∫ h, H (gridStoppedHistory Δ hΔ n h) * (δ * A (gridStoppedHistory Δ hΔ n h))
        ∂gridPrefixKernel Δ K (n + 1) a := by
    apply integral_congr_ae
    filter_upwards [ha] with h hh
    rw [show (∫ q, H (gridStoppedHistory Δ hΔ n h) *
        (if q.2 = true then (1 : ℝ) else 0) * φ ((stopPathAt Δ q.1) Δ)
        ∂K (gridHistoryStart Δ (n + 1) h)) =
      H (gridStoppedHistory Δ hΔ n h) *
        ∫ q, (if q.2 = true then (1 : ℝ) else 0) * φ (q.1 Δ)
          ∂K (gridHistoryStart Δ (n + 1) h) from by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with q
        simp [stopPathAt]]
    rw [splitStep_successful_endpoint Δ R δ i hR P G hP hminor hδ₀ hδ₁ _ φ hφ hbφ]
    simp only [A, hh]
  have hj : (∫ h, ∫ _q, H (gridStoppedHistory Δ hΔ n h) * A (gridStoppedHistory Δ hΔ n h)
        ∂K (gridHistoryStart Δ (n + 1) h) ∂gridPrefixKernel Δ K (n + 1) a) =
      ∫ h, H (gridStoppedHistory Δ hΔ n h) * A (gridStoppedHistory Δ hΔ n h)
        ∂gridPrefixKernel Δ K (n + 1) a := by simp
  rw [hi] at hI
  rw [hj] at hJ
  simp_rw [Probability.finiteHistory_test_stopped Δ (n + 1) H hH] at hI hJ
  simp only [gridIntervalSample, ContinuousMap.coe_mk, min_self,
    Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hI
  simp only [A, T, Probability.stoppedHistorySample, ContinuousMap.coe_mk, min_self] at hJ
  change (∫ z, H z * (if z.2 (n + 1) = true then (1 : ℝ) else 0) *
      φ (z.1 (((n + 2 : ℕ) : ℝ≥0) * Δ)) ∂gridCoupledLawKernel Δ hΔ K a) =
      δ * ∫ z, H z * endpointAverage i R (z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) φ
        ∂gridCoupledLawKernel Δ hΔ K a
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_mul, one_mul,
    two_mul, ← add_assoc] at ⊢ hI hJ
  rw [hI, hJ]
  simp only [mul_left_comm, integral_const_mul, A, T, Nat.cast_add, Nat.cast_one,
    add_mul, one_mul]

/-- The same extended split kernel has the uniform successful endpoint law. -/
theorem extended_splitGrid_uniform_successful_endpoint {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R δ : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    HasUniformSuccessfulEndpoint Q.measure Δ δ R i K := by
  let S := splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
  let ν : Measure (CoupledSample d) := Measure.dirac ((0 : Path d), fun _ => false)
  let K := extendEnvironmentKernel G hG S ν
  change HasUniformSuccessfulEndpoint Q.measure Δ δ R i K
  have hf (x : Vec d) (ω : FieldPair d) (hω : ω ∈ G) :
      UniformSuccessfulEndpointAt Δ δ R i K (x, ω) := by
    intro n H φ hH hbH hφ hbφ
    rw [show K (x, ω) = S (x, ⟨ω, hω⟩) from
      extendEnvironmentKernel_apply_of_mem G hG S ν x ω hω]
    cases n with
    | zero =>
      simpa only [Nat.cast_zero, zero_mul, Nat.zero_add, Nat.cast_one, one_mul] using
        splitGrid_successful_endpoint_zero Δ hΔ R δ i hR P G hP hminor hδ₀ hδ₁ hstart
          (x, ⟨ω, hω⟩) H φ hH hφ hbφ
    | succ n =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] using
        splitGrid_successful_endpoint_succ Δ hΔ R δ i hR P G hP hminor hδ₀ hδ₁ hstart
          (x, ⟨ω, hω⟩) n H φ hH hbH hφ hbφ
  constructor
  · filter_upwards [hGae] with ω hω
    exact hf 0 ω hω
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hGae] with a ha
    exact hf a.1 a.2 ha

/-- Marginals, fresh bits, successful bridge support and the successful endpoint
identity all hold for the same extended split kernel. -/
theorem extended_splitGrid_accumulated {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (hGMP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P ∧
      HasFreshBits Q.measure Δ δ K ∧ HasSuccessfulBridgeSupport Q.measure Δ i R K ∧
      HasUniformSuccessfulEndpoint Q.measure Δ δ R i K := by
  exact ⟨(extended_splitGrid_marginals_and_freshBits hd hΛ₀ Q lam h0 h1 Δ hΔ R δ i hR
      P hGMP G hG hGae hP hminor hδ₀ hδ₁ hstart).1,
    (extended_splitGrid_marginals_and_freshBits hd hΛ₀ Q lam h0 h1 Δ hΔ R δ i hR
      P hGMP G hG hGae hP hminor hδ₀ hδ₁ hstart).2.1,
    (extended_splitGrid_marginals_and_freshBits hd hΛ₀ Q lam h0 h1 Δ hΔ R δ i hR
      P hGMP G hG hGae hP hminor hδ₀ hδ₁ hstart).2.2,
    extended_splitGrid_success_support Q Δ hΔ R δ i hR P G hG hGae hP hminor hδ₁ hstart,
    extended_splitGrid_uniform_successful_endpoint Q Δ hΔ R δ i hR P G hG hGae hP hminor
      hδ₀ hδ₁ hstart⟩

/-- At time zero, the literal finite history is constant on any law that
starts at its prescribed point. -/
theorem deterministic_restart_zero_of_start {d : ℕ} (Δ : ℝ≥0)
    (K : CoupledQuenchedLaws d) (a : Vec d × FieldPair d)
    [IsProbabilityMeasure (K a)] (hs : ∀ᵐ z ∂K a, z.1 0 = a.1)
    (H Φ : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 0) inferInstance H) :
    (∫ z, H z * Φ (sampleTimeShift Δ z 0) ∂K a) =
      ∫ z, H z * (∫ z', Φ z' ∂K (z.1 0, a.2)) ∂K a := by
  let z₀ : CoupledSample d := (⟨fun _ => a.1, continuous_const⟩, fun _ => false)
  have hconst : ∀ᵐ z ∂K a, H z = H z₀ := by
    filter_upwards [hs] with z hz
    rw [← Probability.finiteHistory_test_stopped Δ 0 H hH z,
      ← Probability.finiteHistory_test_stopped Δ 0 H hH z₀]
    congr 1
    apply Prod.ext
    · apply ContinuousMap.ext
      intro t
      simpa only [Probability.stoppedHistorySample, Nat.cast_zero, zero_mul,
        min_eq_right (zero_le (a := t)), z₀, ContinuousMap.coe_mk] using hz
    · funext k
      simp only [Probability.stoppedHistorySample, Nat.not_lt_zero, ite_false]
  have hshift (z : CoupledSample d) : sampleTimeShift Δ z 0 = z := by
    apply Prod.ext
    · apply ContinuousMap.ext
      intro t
      simp only [sampleTimeShift, pathTimeShift, ContinuousMap.coe_mk, zero_add]
    · funext k
      simp only [sampleTimeShift, gridIndex, NNReal.coe_zero, zero_div, Nat.floor_zero, zero_add]
  simp only [hshift]
  calc
    (∫ z, H z * Φ z ∂K a) = ∫ z, H z₀ * Φ z ∂K a := by
      apply integral_congr_ae
      filter_upwards [hconst] with z hz
      rw [hz]
    _ = H z₀ * ∫ z, Φ z ∂K a := integral_const_mul _ _
    _ = ∫ z, H z₀ * (∫ z', Φ z' ∂K a) ∂K a := by simp
    _ = ∫ z, H z * (∫ z', Φ z' ∂K (z.1 0, a.2)) ∂K a := by
      apply integral_congr_ae
      filter_upwards [hconst, hs] with z hz hp
      rw [hz, hp]

/-- The extended split-grid law satisfies the literal restart identity at time zero. -/
theorem extended_splitGrid_restart_zero {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R δ : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d)) (hG : MeasurableSet G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (x : Vec d) (ω : FieldPair d) (hω : ω ∈ G)
    (H Φ : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 0) inferInstance H) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    (∫ z, H z * Φ (sampleTimeShift Δ z 0) ∂K (x, ω)) =
      ∫ z, H z * (∫ z', Φ z' ∂K (z.1 0, ω)) ∂K (x, ω) := by
  let S := splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
  let ν : Measure (CoupledSample d) := Measure.dirac ((0 : Path d), fun _ => false)
  let K := extendEnvironmentKernel G hG S ν
  have he : K (x, ω) = S (x, ⟨ω, hω⟩) :=
    extendEnvironmentKernel_apply_of_mem G hG S ν x ω hω
  have : IsProbabilityMeasure (K (x, ω)) := by
    rw [he]
    let := isMarkovKernel_splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
    infer_instance
  have hm : Measurable (fun z : CoupledSample d => stopPathAt Δ z.1) :=
    (measurable_stopPathAt Δ).comp measurable_fst
  have ht : MeasurableSet {γ : Path d | γ 0 = x} :=
    measurableSet_eq_fun (continuous_eval_const 0).measurable measurable_const
  have hp : ∀ᵐ γ ∂(P (x, ω)).map (stopPathAt Δ), γ 0 = x := by
    apply (ae_map_iff (measurable_stopPathAt Δ).aemeasurable ht).mpr
    filter_upwards [hstart ω hω x] with γ hγ
    simpa [stopPathAt] using hγ
  rw [← splitGridCoupledLawKernel_map_firstPath Δ hΔ R δ i hR P G hP hminor hδ₁
    (x, ⟨ω, hω⟩), ← he] at hp
  have hs : ∀ᵐ z ∂K (x, ω), z.1 0 = x := by
    have hh := (ae_map_iff hm.aemeasurable ht).mp hp
    filter_upwards [hh] with z hz
    simpa [stopPathAt] using hz
  exact deterministic_restart_zero_of_start Δ K (x, ω) hs H Φ hH

/-- Shifting the actual concatenated path and coin sequence by a grid time
is concatenation of the correspondingly shifted matching segments. -/
theorem coupledConcat_shift {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (q : ℕ → Path d × Bool)
    (hmatch : ∀ j, (q (j + 1)).1 0 = (q j).1 Δ) (n : ℕ) :
    sampleTimeShift Δ (coupledConcat Δ hΔ q) ((n : ℝ≥0) * Δ) =
      coupledConcat Δ hΔ (fun j => q (n + j)) := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    let k : ℕ := ⌊t / Δ⌋₊
    have hlow : (k : ℝ≥0) * Δ ≤ t := (le_div_iff₀ hΔ).mp (Nat.floor_le zero_le)
    have hhigh : t ≤ ((k + 1 : ℕ) : ℝ≥0) * Δ := by
      have h := (div_lt_iff₀ hΔ).mp (Nat.lt_floor_add_one (t / Δ))
      exact le_of_lt (by simpa only [Nat.cast_add, Nat.cast_one] using h)
    have hu : t - (k : ℝ≥0) * Δ ≤ Δ := by
      apply tsub_le_iff_right.mpr
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using hhigh
    have ht : t = (k : ℝ≥0) * Δ + (t - (k : ℝ≥0) * Δ) :=
      (add_tsub_cancel_of_le hlow).symm
    have hmatch' : ∀ j, (q (n + (j + 1))).1 0 = (q (n + j)).1 Δ := by
      intro j
      simpa only [Nat.add_assoc] using hmatch (n + j)
    change infiniteConcat Δ hΔ q ((n : ℝ≥0) * Δ + t) =
      infiniteConcat Δ hΔ (fun j => q (n + j)) t
    calc
      infiniteConcat Δ hΔ q ((n : ℝ≥0) * Δ + t) =
          infiniteConcat Δ hΔ q (((n + k : ℕ) : ℝ≥0) * Δ +
            (t - (k : ℝ≥0) * Δ)) := by
        congr 1
        calc
          (n : ℝ≥0) * Δ + t = (n : ℝ≥0) * Δ +
              ((k : ℝ≥0) * Δ + (t - (k : ℝ≥0) * Δ)) := congrArg _ ht
          _ = _ := by push_cast; ring
      _ = (q (n + k)).1 (t - (k : ℝ≥0) * Δ) :=
        infiniteConcat_segment Δ hΔ q hmatch (n + k) _ hu
      _ = infiniteConcat Δ hΔ (fun j => q (n + j))
          ((k : ℝ≥0) * Δ + (t - (k : ℝ≥0) * Δ)) :=
        (infiniteConcat_segment Δ hΔ (fun j => q (n + j)) hmatch' k _ hu).symm
      _ = infiniteConcat Δ hΔ (fun j => q (n + j)) t := congrArg _ ht.symm
  · funext k
    change (q (gridIndex Δ ((n : ℝ≥0) * Δ) + k)).2 = (q (n + k)).2
    rw [gridIndex_mul Δ hΔ n]

/-- The pathwise shift identity holds simultaneously at every grid time under
the actual trajectory law whenever each sampled segment starts at its input. -/
theorem ae_gridLawKernel_coupledConcat_shift {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (K : Kernel (Vec d × Ω) (Path d × Bool))
    [IsMarkovKernel K] (hstart : ∀ a, ∀ᵐ q ∂K a, q.1 0 = a.1)
    (a : Vec d × Ω) :
    ∀ᵐ z ∂gridLawKernel Δ K a, ∀ n : ℕ,
      sampleTimeShift Δ (coupledConcat Δ hΔ (gridPairs z)) ((n : ℝ≥0) * Δ) =
        coupledConcat Δ hΔ (fun j => gridPairs z (n + j)) := by
  filter_upwards [ae_gridLawKernel_matching Δ K hstart a] with z hz n
  exact coupledConcat_shift Δ hΔ (gridPairs z) hz n

/-- The actual finite prefix and the entire shifted segment sequence disintegrate
over the canonical continuation from that prefix. -/
theorem gridLawKernel_map_prefix_shiftedPairs {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (Δ : ℝ≥0) (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ) :
    (gridLawKernel Δ K a).map (fun z =>
      (Preorder.frestrictLe n z, fun j => gridPairs z (n + j))) =
      ((gridPrefixKernel Δ K n a) ⊗ₘ Kernel.traj (gridStep Δ K) n).map
        (fun hz => (hz.1, fun j => gridPairs hz.2 (n + j))) := by
  have hm : Measurable (fun z : (j : ℕ) → gridState d Ω j =>
      fun j => gridPairs z (n + j)) := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply _
  have hp : Measurable (fun z : (j : ℕ) → gridState d Ω j =>
      (Preorder.frestrictLe n z, z)) :=
    (Preorder.measurable_frestrictLe n).prodMk measurable_id
  have hg : Measurable (fun hz : gridHistory d Ω n × ((j : ℕ) → gridState d Ω j) =>
      (hz.1, fun j => gridPairs hz.2 (n + j))) :=
    measurable_fst.prodMk (hm.comp measurable_snd)
  rw [← gridLawKernel_map_prefix_continuation Δ K a n,
    Measure.map_map hg hp]
  rfl

/-- The first pair after a deterministic prefix has exactly the original
transition law at that prefix's endpoint. -/
theorem gridContinuation_map_first {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (Δ : ℝ≥0) (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (n : ℕ) (h : gridHistory d Ω n) :
    (Kernel.traj (gridStep Δ K) n h).map (fun z => gridPairs z n) =
      K (gridHistoryStart Δ n h) := by
  have hm := congrArg (fun L => L h)
    (Kernel.map_traj_succ_self (κ := gridStep Δ K) (a := n))
  rw [Kernel.map_apply _ (measurable_pi_apply (n + 1))] at hm
  exact hm

/-- The first cylinder of a continuation agrees with the fresh same-kernel law. -/
theorem gridContinuation_map_first_eq_fresh {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (Δ : ℝ≥0) (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (n : ℕ) (h : gridHistory d Ω n) :
    (Kernel.traj (gridStep Δ K) n h).map (fun z => gridPairs z n) =
      (gridPairLawKernel Δ K (gridHistoryStart Δ n h)).map (fun q => q 0) := by
  rw [gridContinuation_map_first]
  unfold gridPairLawKernel
  rw [Kernel.map_apply _ measurable_gridPairs,
    Measure.map_map (measurable_pi_apply 0) measurable_gridPairs]
  exact (gridLawKernel_map_first Δ K (gridHistoryStart Δ n h)).symm

/-- A continuation retains its prescribed initial data jointly with all of
its shifted future pairs, without a measurability assumption on singletons. -/
theorem gridContinuation_initial_and_shiftedPairs {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (n : ℕ) (h : gridHistory d Ω n) :
    (Kernel.traj (gridStep Δ K) n h).map
        (fun z => (z 0, fun j => gridPairs z (n + j))) =
      (Kernel.traj (gridStep Δ K) n h).map
        (fun z => (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩,
          fun j => gridPairs z (n + j))) := by
  let μ := Kernel.traj (gridStep Δ K) n h
  let u : ((j : ℕ) → gridState d Ω j) → ((j : ℕ) → gridState d Ω j) :=
    fun z => Function.updateFinset z (Finset.Iic n) h
  let f : ((j : ℕ) → gridState d Ω j) → (Vec d × Ω) × (ℕ → Path d × Bool) :=
    fun z => (z 0, fun j => gridPairs z (n + j))
  have hu : Measurable u := measurable_updateFinset_left
  have hf : Measurable f := by
    apply (measurable_pi_apply 0).prodMk
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply _
  calc
    μ.map f = (μ.map u).map f := by rw [Kernel.traj_map_updateFinset]
    _ = μ.map (f ∘ u) := Measure.map_map hf hu
    _ = _ := by
      congr 1
      funext z
      apply Prod.ext
      · simp [f, u, Function.updateFinset, Finset.mem_Iic]
      · funext j
        simp [f, u, Function.updateFinset, gridPairs, Finset.mem_Iic]

/-- The entire input history is retained jointly with the shifted future. -/
theorem gridContinuation_prefix_and_shiftedPairs {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (n : ℕ) (h : gridHistory d Ω n) :
    (Kernel.traj (gridStep Δ K) n h).map
        (fun z => (Preorder.frestrictLe n z, fun j => gridPairs z (n + j))) =
      (Kernel.traj (gridStep Δ K) n h).map
        (fun z => (h, fun j => gridPairs z (n + j))) := by
  let μ := Kernel.traj (gridStep Δ K) n h
  let u : ((j : ℕ) → gridState d Ω j) → ((j : ℕ) → gridState d Ω j) :=
    fun z => Function.updateFinset z (Finset.Iic n) h
  let f : ((j : ℕ) → gridState d Ω j) → gridHistory d Ω n × (ℕ → Path d × Bool) :=
    fun z => (Preorder.frestrictLe n z, fun j => gridPairs z (n + j))
  have hu : Measurable u := measurable_updateFinset_left
  have hf : Measurable f := by
    apply (Preorder.measurable_frestrictLe n).prodMk
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply _
  calc
    μ.map f = (μ.map u).map f := by rw [Kernel.traj_map_updateFinset]
    _ = μ.map (f ∘ u) := Measure.map_map hf hu
    _ = _ := by
      congr 1
      funext z
      apply Prod.ext
      · funext j
        simp [f, u, Preorder.frestrictLe, Function.updateFinset, j.2]
      · funext j
        simp [f, u, Function.updateFinset, gridPairs, Finset.mem_Iic]

/-- Every future pair has the supplied transition conditional on the actual
extended prefix of the continuation. -/
theorem gridContinuation_map_prefix_next {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (n j : ℕ) (h : gridHistory d Ω n) :
    (Kernel.traj (gridStep Δ K) n h).map
        (fun z => (Preorder.frestrictLe (n + j) z, gridPairs z (n + j))) =
      (Kernel.partialTraj (gridStep Δ K) n (n + j) h) ⊗ₘ
        (gridStep Δ K (n + j)) := by
  simpa only [gridPairs] using
    (Kernel.partialTraj_compProd_eq_map_traj (κ := gridStep Δ K)
      (a := n) (b := n + j) (x₀ := h) (Nat.le_add_right n j)).symm

/-- At each future transition the environment is the prescribed environment,
jointly with the entire future sequence. -/
theorem gridContinuation_start_and_shiftedPairs {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (n j : ℕ) (h : gridHistory d Ω n) :
    (Kernel.traj (gridStep Δ K) n h).map
        (fun z => (gridHistoryStart Δ (n + j + 1) (Preorder.frestrictLe (n + j + 1) z),
          fun k => gridPairs z (n + k))) =
      (Kernel.traj (gridStep Δ K) n h).map
        (fun z => (((gridPairs z (n + j)).1 Δ, (gridHistoryStart Δ n h).2),
          fun k => gridPairs z (n + k))) := by
  have henv : (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).2 =
      (gridHistoryStart Δ n h).2 := by
    cases n <;> rfl
  rw [← henv]
  let μ := Kernel.traj (gridStep Δ K) n h
  let u : ((j : ℕ) → gridState d Ω j) → ((j : ℕ) → gridState d Ω j) :=
    fun z => Function.updateFinset z (Finset.Iic n) h
  let f : ((j : ℕ) → gridState d Ω j) → (Vec d × Ω) × (ℕ → Path d × Bool) :=
    fun z => (gridHistoryStart Δ (n + j + 1) (Preorder.frestrictLe (n + j + 1) z),
      fun k => gridPairs z (n + k))
  have hu : Measurable u := measurable_updateFinset_left
  have hf : Measurable f := by
    apply ((measurable_gridHistoryStart Δ (n + j + 1)).comp
      (Preorder.measurable_frestrictLe _)).prodMk
    apply measurable_pi_iff.mpr
    intro k
    exact measurable_pi_apply _
  calc
    μ.map f = (μ.map u).map f := by rw [Kernel.traj_map_updateFinset]
    _ = μ.map (f ∘ u) := Measure.map_map hf hu
    _ = _ := by
      congr 1
      funext z
      apply Prod.ext
      · simp [f, u, gridHistoryStart, Preorder.frestrictLe,
          Function.updateFinset, gridPairs, Finset.mem_Iic]
      · funext k
        simp [f, u, Function.updateFinset, gridPairs, Finset.mem_Iic]

/-- The first `j + 1` pairs after a prefix, read from an extended grid history. -/
def gridShiftedPrefix {d : ℕ} {Ω : Type} (n j : ℕ)
    (h : gridHistory d Ω (n + j + 1)) :
    (k : Finset.Iic j) → Path d × Bool :=
  fun k => h ⟨n + k.1 + 1, Finset.mem_Iic.mpr (by
    have hk := Finset.mem_Iic.mp k.2
    omega)⟩

theorem measurable_gridShiftedPrefix {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (n j : ℕ) : Measurable (gridShiftedPrefix (d := d) (Ω := Ω) n j) := by
  apply measurable_pi_iff.mpr
  intro k
  exact measurable_pi_apply _

theorem gridShiftedPrefix_restrict {d : ℕ} {Ω : Type} (n j : ℕ)
    (z : (k : ℕ) → gridState d Ω k) :
    gridShiftedPrefix n j (Preorder.frestrictLe (n + j + 1) z) =
      Preorder.frestrictLe j (fun k => gridPairs z (n + k)) := rfl

/-- A shifted finite pair prefix and its next pair disintegrate over the
actual extended grid history and its original transition kernel. -/
theorem gridContinuation_shiftedPrefix_next {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (n j : ℕ) (h : gridHistory d Ω n) :
    (Kernel.traj (gridStep Δ K) n h).map
        (fun z => (Preorder.frestrictLe j (fun k => gridPairs z (n + k)),
          gridPairs z (n + j + 1))) =
      ((Kernel.partialTraj (gridStep Δ K) n (n + j + 1) h) ⊗ₘ
        (gridStep Δ K (n + j + 1))).map
          (fun pq => (gridShiftedPrefix n j pq.1, pq.2)) := by
  have hf : Measurable (fun pq : gridHistory d Ω (n + j + 1) × (Path d × Bool) =>
      (gridShiftedPrefix n j pq.1, pq.2)) :=
    ((measurable_gridShiftedPrefix n j).comp measurable_fst).prodMk measurable_snd
  have hg : Measurable (fun z : (k : ℕ) → gridState d Ω k =>
      (Preorder.frestrictLe (n + j + 1) z, gridPairs z (n + j + 1))) :=
    (Preorder.measurable_frestrictLe _).prodMk (measurable_pi_apply _)
  have hnext : (Kernel.traj (gridStep Δ K) n h).map
      (fun z => (Preorder.frestrictLe (n + j + 1) z, gridPairs z (n + j + 1))) =
      (Kernel.partialTraj (gridStep Δ K) n (n + j + 1) h) ⊗ₘ
        (gridStep Δ K (n + j + 1)) := by
    simpa only [gridPairs] using
      (Kernel.partialTraj_compProd_eq_map_traj (κ := gridStep Δ K)
        (a := n) (b := n + j + 1) (x₀ := h) (by omega)).symm
  rw [← hnext, Measure.map_map hf hg]
  congr 1

/-- The next pair depends on the latest endpoint and the fixed environment. -/
def gridPairStep {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) (ω : Ω) (j : ℕ) :
    Kernel ((k : Finset.Iic j) → Path d × Bool) (Path d × Bool) :=
  K.comap (fun q => ((q ⟨j, Finset.mem_Iic.mpr le_rfl⟩).1 Δ, ω))
    (((continuous_eval_const Δ).measurable.comp
      (measurable_fst.comp (measurable_pi_apply _))).prodMk measurable_const)

instance {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K] (ω : Ω) (j : ℕ) :
    IsMarkovKernel (gridPairStep Δ K ω j) := by
  unfold gridPairStep
  infer_instance

/-- The projected next-pair transition uses the original kernel at the
latest pair endpoint and the original environment. -/
theorem gridContinuation_pair_prefix_next {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (n j : ℕ) (h : gridHistory d Ω n) :
    (Kernel.traj (gridStep Δ K) n h).map
        (fun z => (Preorder.frestrictLe j (fun k => gridPairs z (n + k)),
          gridPairs z (n + j + 1))) =
      ((Kernel.traj (gridStep Δ K) n h).map
        (fun z => Preorder.frestrictLe j (fun k => gridPairs z (n + k)))).compProd
          (gridPairStep Δ K (gridHistoryStart Δ n h).2 j) := by
  let μ := Kernel.traj (gridStep Δ K) n h
  let u : ((k : ℕ) → gridState d Ω k) → ((k : ℕ) → gridState d Ω k) :=
    fun z => Function.updateFinset z (Finset.Iic n) h
  let p := fun z => Preorder.frestrictLe (n + j + 1) (u z)
  let v := fun z => gridPairs (u z) (n + j + 1)
  have hu : Measurable u := measurable_updateFinset_left
  have hp : Measurable p := (Preorder.measurable_frestrictLe _).comp hu
  have hv : Measurable v := (measurable_pi_apply _).comp hu
  have henv : (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).2 =
      (gridHistoryStart Δ n h).2 := by cases n <;> rfl
  have hpoint (z : (k : ℕ) → gridState d Ω k) :
      gridStep Δ K (n + j + 1) (p z) =
        gridPairStep Δ K (gridHistoryStart Δ n h).2 j (gridShiftedPrefix n j (p z)) := by
    rw [gridStep_apply, ← henv]
    congr 1
  have hjoint : μ.map (fun z => (p z, v z)) = (μ.map p).compProd
      (gridStep Δ K (n + j + 1)) := by
    have hm : μ.map u = μ := Kernel.traj_map_updateFinset h
    have hmapped {α : Type} [MeasurableSpace α] (f : ((k : ℕ) → gridState d Ω k) → α) (hf : Measurable f) :
        μ.map (f ∘ u) = μ.map f := by rw [← Measure.map_map hf hu, hm]
    change μ.map ((fun z => (Preorder.frestrictLe (n + j + 1) z,
      gridPairs z (n + j + 1))) ∘ u) =
      (μ.map ((Preorder.frestrictLe (n + j + 1)) ∘ u)).compProd _
    have hbase : Measurable (fun z : (k : ℕ) → gridState d Ω k =>
        (Preorder.frestrictLe (n + j + 1) z, gridPairs z (n + j + 1))) :=
      (Preorder.measurable_frestrictLe _).prodMk (measurable_pi_apply _)
    rw [hmapped _ hbase, hmapped _ (Preorder.measurable_frestrictLe _)]
    rw [Kernel.traj_map_frestrictLe_apply]
    simpa only [gridPairs] using
      (Kernel.partialTraj_compProd_eq_map_traj (κ := gridStep Δ K)
        (a := n) (b := n + j + 1) (x₀ := h) (by omega)).symm
  have hresult := EinsteinFull.Regeneration.map_pair_of_prefix_transition μ p
    (gridShiftedPrefix n j) v hp (measurable_gridShiftedPrefix n j) hv
    (gridStep Δ K (n + j + 1)) (gridPairStep Δ K (gridHistoryStart Δ n h).2 j)
    hjoint (Filter.Eventually.of_forall hpoint)
  have hm : μ.map u = μ := Kernel.traj_map_updateFinset h
  have hmapped {α : Type} [MeasurableSpace α] (f : ((k : ℕ) → gridState d Ω k) → α) (hf : Measurable f) :
      μ.map (f ∘ u) = μ.map f := by rw [← Measure.map_map hf hu, hm]
  change μ.map ((fun z => (Preorder.frestrictLe j (fun k => gridPairs z (n + k)),
      gridPairs z (n + j + 1))) ∘ u) =
    (μ.map ((fun z => Preorder.frestrictLe j (fun k => gridPairs z (n + k))) ∘ u)).compProd _ at hresult
  have hshift : Measurable (fun z : (k : ℕ) → gridState d Ω k =>
      fun k => gridPairs z (n + k)) := by
    apply measurable_pi_iff.mpr
    intro k
    exact measurable_pi_apply _
  have hprefix : Measurable (fun z : (k : ℕ) → gridState d Ω k =>
      Preorder.frestrictLe j (fun k => gridPairs z (n + k))) :=
    (Preorder.measurable_frestrictLe j).comp hshift
  have hboth : Measurable (fun z : (k : ℕ) → gridState d Ω k =>
      (Preorder.frestrictLe j (fun k => gridPairs z (n + k)),
        gridPairs z (n + j + 1))) := hprefix.prodMk (measurable_pi_apply _)
  rw [hmapped _ hboth, hmapped _ hprefix] at hresult
  exact hresult

/-- The complete shifted pair sequence has the fresh same-kernel law at the
endpoint of the prescribed history. -/
theorem gridContinuation_shiftedPairs_eq_fresh {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (n : ℕ) (h : gridHistory d Ω n) :
    (Kernel.traj (gridStep Δ K) n h).map (fun z k => gridPairs z (n + k)) =
      gridPairLawKernel Δ K (gridHistoryStart Δ n h) := by
  let a := gridHistoryStart Δ n h
  let μ := (Kernel.traj (gridStep Δ K) n h).map (fun z k => gridPairs z (n + k))
  let ν := gridPairLawKernel Δ K a
  have hm (m : ℕ) : Measurable (fun z : (k : ℕ) → gridState d Ω k =>
      fun k => gridPairs z (m + k)) := by
    apply measurable_pi_iff.mpr
    intro k
    exact measurable_pi_apply _
  have hν : ν = (Kernel.traj (gridStep Δ K) 0 (gridInitialHistory a)).map
      (fun z k => gridPairs z (0 + k)) := by
    unfold ν gridPairLawKernel gridLawKernel
    rw [Kernel.map_apply _ measurable_gridPairs]
    simp only [Kernel.comap_apply, Nat.zero_add]
  have htransition (m : ℕ) (b : gridHistory d Ω m) (j : ℕ) :
      ((Kernel.traj (gridStep Δ K) m b).map (fun z k => gridPairs z (m + k))).map
          (fun q => (Preorder.frestrictLe j q, q (j + 1))) =
        (((Kernel.traj (gridStep Δ K) m b).map (fun z k => gridPairs z (m + k))).map
          (Preorder.frestrictLe j)).compProd
            (gridPairStep Δ K (gridHistoryStart Δ m b).2 j) := by
    rw [Measure.map_map ((Preorder.measurable_frestrictLe j).prodMk (measurable_pi_apply _)) (hm m),
      Measure.map_map (Preorder.measurable_frestrictLe j) (hm m)]
    exact gridContinuation_pair_prefix_next Δ K m j b
  apply EinsteinFull.Regeneration.sequenceMeasure_eq_of_prefix_next μ ν
    (fun j => gridPairStep Δ K a.2 j)
  · dsimp [μ]
    rw [Measure.map_map (measurable_pi_apply 0) (hm n)]
    simpa only [Function.comp_def, Nat.add_zero, ν, a] using
      gridContinuation_map_first_eq_fresh Δ K n h
  · intro j
    exact htransition n h j
  · intro j
    rw [hν]
    simpa only [gridHistoryStart_initial] using htransition 0 (gridInitialHistory a) j

/-- The actual past and the full shifted future disintegrate through the
fresh pair law at the endpoint and environment of that past. -/
theorem gridLawKernel_prefix_shiftedPairs_eq_fresh {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ) :
    (gridLawKernel Δ K a).map (fun z =>
      (Preorder.frestrictLe n z, fun j => gridPairs z (n + j))) =
      (gridPrefixKernel Δ K n a) ⊗ₘ
        ((gridPairLawKernel Δ K).comap (gridHistoryStart Δ n)
          (measurable_gridHistoryStart Δ n)) := by
  have hm : Measurable (fun z : (j : ℕ) → gridState d Ω j =>
      fun j => gridPairs z (n + j)) := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply _
  rw [gridLawKernel_map_prefix_shiftedPairs Δ K a n]
  change ((gridPrefixKernel Δ K n a) ⊗ₘ Kernel.traj (gridStep Δ K) n).map
    (Prod.map id (fun z j => gridPairs z (n + j))) = _
  rw [← Measure.compProd_map hm]
  congr 1
  apply Kernel.ext
  intro h
  rw [Kernel.map_apply _ hm, Kernel.comap_apply]
  exact gridContinuation_shiftedPairs_eq_fresh Δ K n h

/-- The finite grid past and the assembled fresh future have the same joint
law as disintegration by the original coupled kernel at the grid endpoint. -/
theorem gridLawKernel_prefix_shiftedConcat_eq_fresh {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ) :
    (gridLawKernel Δ K a).map (fun z =>
      (Preorder.frestrictLe n z, coupledConcat Δ hΔ (fun j => gridPairs z (n + j)))) =
      (gridPrefixKernel Δ K n a) ⊗ₘ
        ((gridCoupledLawKernel Δ hΔ K).comap (gridHistoryStart Δ n)
          (measurable_gridHistoryStart Δ n)) := by
  have hm : Measurable (fun z : (j : ℕ) → gridState d Ω j =>
      (Preorder.frestrictLe n z, fun j => gridPairs z (n + j))) := by
    apply (Preorder.measurable_frestrictLe n).prodMk
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply _
  change (gridLawKernel Δ K a).map
    (Prod.map id (coupledConcat Δ hΔ) ∘ fun z =>
      (Preorder.frestrictLe n z, fun j => gridPairs z (n + j))) = _
  rw [← Measure.map_map ((measurable_id).prodMap (measurable_coupledConcat Δ hΔ)) hm]
  rw [gridLawKernel_prefix_shiftedPairs_eq_fresh Δ K a n]
  rw [← Measure.compProd_map (measurable_coupledConcat Δ hΔ)]
  congr 1
  apply Kernel.ext
  intro h
  rw [Kernel.map_apply _ (measurable_coupledConcat Δ hΔ), Kernel.comap_apply,
    Kernel.comap_apply, gridCoupledLawKernel, Kernel.map_apply _ (measurable_coupledConcat Δ hΔ)]

/-- The same disintegration holds for the literal time-shifted path and coins. -/
theorem gridLawKernel_prefix_sampleTimeShift_eq_fresh {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (hstart : ∀ a, ∀ᵐ q ∂K a, q.1 0 = a.1) (a : Vec d × Ω) (n : ℕ) :
    (gridLawKernel Δ K a).map (fun z =>
      (Preorder.frestrictLe n z,
        sampleTimeShift Δ (coupledConcat Δ hΔ (gridPairs z)) ((n : ℝ≥0) * Δ))) =
      (gridPrefixKernel Δ K n a) ⊗ₘ
        ((gridCoupledLawKernel Δ hΔ K).comap (gridHistoryStart Δ n)
          (measurable_gridHistoryStart Δ n)) := by
  calc
    _ = (gridLawKernel Δ K a).map (fun z =>
        (Preorder.frestrictLe n z, coupledConcat Δ hΔ (fun j => gridPairs z (n + j)))) := by
      apply Measure.map_congr
      filter_upwards [ae_gridLawKernel_coupledConcat_shift Δ hΔ K hstart a] with z hz
      rw [hz n]
    _ = _ := gridLawKernel_prefix_shiftedConcat_eq_fresh Δ hΔ K a n

/-- The stopped physical past and the shifted future disintegrate through the
same coupled kernel at the stopped endpoint and original environment. -/
theorem gridLawKernel_stopped_sampleTimeShift_eq_fresh {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (hstart : ∀ a, ∀ᵐ q ∂K a, q.1 0 = a.1) (a : Vec d × Ω) (n : ℕ) :
    (gridLawKernel Δ K a).map (fun z =>
      (Probability.stoppedHistorySample Δ (n + 1) (coupledConcat Δ hΔ (gridPairs z)),
        sampleTimeShift Δ (coupledConcat Δ hΔ (gridPairs z)) (((n + 1 : ℕ) : ℝ≥0) * Δ))) =
      ((gridPrefixKernel Δ K (n + 1) a).map (gridStoppedHistory Δ hΔ n)) ⊗ₘ
        (gridCoupledLawKernel Δ hΔ K).comap
          (fun q : CoupledSample d => (q.1 (((n + 1 : ℕ) : ℝ≥0) * Δ), a.2))
          (((continuous_eval_const _).measurable.comp measurable_fst).prodMk measurable_const) := by
  have hm : Measurable (fun z : (j : ℕ) → gridState d Ω j =>
      (Preorder.frestrictLe (n + 1) z,
        sampleTimeShift Δ (coupledConcat Δ hΔ (gridPairs z)) (((n + 1 : ℕ) : ℝ≥0) * Δ))) :=
    (Preorder.measurable_frestrictLe (n + 1)).prodMk
      ((measurable_sampleTimeShift Δ).comp (measurable_const.prodMk
        ((measurable_coupledConcat Δ hΔ).comp measurable_gridPairs)))
  calc
    _ = ((gridLawKernel Δ K a).map (fun z =>
        (Preorder.frestrictLe (n + 1) z,
          sampleTimeShift Δ (coupledConcat Δ hΔ (gridPairs z)) (((n + 1 : ℕ) : ℝ≥0) * Δ)))).map
        (fun q => (gridStoppedHistory Δ hΔ n q.1, q.2)) := by
      rw [Measure.map_map
        (g := fun q => (gridStoppedHistory Δ hΔ n q.1, q.2))
        (((measurable_gridStoppedHistory Δ hΔ n).comp measurable_fst).prodMk measurable_snd) hm]
      congr 1
      funext z
      exact congrArg (fun h => (h, sampleTimeShift Δ (coupledConcat Δ hΔ (gridPairs z))
        (((n + 1 : ℕ) : ℝ≥0) * Δ))) (gridStoppedHistory_restrict Δ hΔ n z).symm
    _ = _ := by
      rw [gridLawKernel_prefix_sampleTimeShift_eq_fresh Δ hΔ K hstart a (n + 1)]
      exact map_compProd_comap_statistic_ae _ (gridCoupledLawKernel Δ hΔ K)
        (gridStoppedHistory Δ hΔ n) (measurable_gridStoppedHistory Δ hΔ n)
        (fun q => (q.1 (((n + 1 : ℕ) : ℝ≥0) * Δ), a.2))
        (((continuous_eval_const _).measurable.comp measurable_fst).prodMk measurable_const)
        (gridHistoryStart Δ (n + 1)) (measurable_gridHistoryStart Δ (n + 1))
        (ae_gridPrefixKernel_stopped_restart Δ hΔ K hstart a n)

/-- Under the assembled coupled law, the physical stopped past and the literal
shifted sample have the same-kernel endpoint restart joint law. -/
theorem gridCoupledLawKernel_stopped_sampleTimeShift_eq_fresh {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (hstart : ∀ a, ∀ᵐ q ∂K a, q.1 0 = a.1) (a : Vec d × Ω) (n : ℕ) :
    (gridCoupledLawKernel Δ hΔ K a).map (fun z =>
      (Probability.stoppedHistorySample Δ (n + 1) z,
        sampleTimeShift Δ z (((n + 1 : ℕ) : ℝ≥0) * Δ))) =
      ((gridCoupledLawKernel Δ hΔ K a).map (Probability.stoppedHistorySample Δ (n + 1))) ⊗ₘ
        (gridCoupledLawKernel Δ hΔ K).comap
          (fun q : CoupledSample d => (q.1 (((n + 1 : ℕ) : ℝ≥0) * Δ), a.2))
          (((continuous_eval_const _).measurable.comp measurable_fst).prodMk measurable_const) := by
  have hs := (Probability.measurable_stoppedHistorySample (d := d) Δ (n + 1)).mono
    (Probability.finiteHistorySigma_le Δ (n + 1)) le_rfl
  have hm : Measurable (fun z : CoupledSample d =>
      (Probability.stoppedHistorySample Δ (n + 1) z,
        sampleTimeShift Δ z (((n + 1 : ℕ) : ℝ≥0) * Δ))) :=
    hs.prodMk ((measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_id))
  rw [gridCoupledLawKernel_map_stoppedHistory Δ hΔ K a n,
    gridCoupledLawKernel_apply Δ hΔ K a,
    Measure.map_map (f := fun z => coupledConcat Δ hΔ (gridPairs z))
      hm ((measurable_coupledConcat Δ hΔ).comp measurable_gridPairs)]
  exact gridLawKernel_stopped_sampleTimeShift_eq_fresh Δ hΔ K hstart a n

/-- The same-grid coupled law restarts at the physical endpoint against bounded
finite-history and future tests. -/
theorem gridCoupledLawKernel_restart_succ {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (hstart : ∀ a, ∀ᵐ q ∂K a, q.1 0 = a.1) (a : Vec d × Ω) (n : ℕ)
    (H Φ : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ (n + 1)) inferInstance H)
    (hbH : BoundedRealTest H) (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ z, H z * Φ (sampleTimeShift Δ z (((n + 1 : ℕ) : ℝ≥0) * Δ))
      ∂gridCoupledLawKernel Δ hΔ K a) =
    ∫ z, H z * (∫ q, Φ q ∂gridCoupledLawKernel Δ hΔ K
      (z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ), a.2)) ∂gridCoupledLawKernel Δ hΔ K a := by
  let μ := gridCoupledLawKernel Δ hΔ K a
  let S := Probability.stoppedHistorySample (d := d) Δ (n + 1)
  let T := (((n + 1 : ℕ) : ℝ≥0) * Δ)
  let κ : Kernel (CoupledSample d) (CoupledSample d) := (gridCoupledLawKernel Δ hΔ K).comap
    (fun q : CoupledSample d => (q.1 T, a.2))
    (((continuous_eval_const _).measurable.comp measurable_fst).prodMk measurable_const)
  let F : CoupledSample d × CoupledSample d → ℝ := fun q => H q.1 * Φ q.2
  have hs : Measurable S := (Probability.measurable_stoppedHistorySample (d := d) Δ (n + 1)).mono
    (Probability.finiteHistorySigma_le Δ (n + 1)) le_rfl
  have hm : Measurable (fun z : CoupledSample d => (S z, sampleTimeShift Δ z T)) :=
    hs.prodMk ((measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_id))
  have hHm : Measurable H := hH.mono (Probability.finiteHistorySigma_le Δ (n + 1)) le_rfl
  have hF : Measurable F := (hHm.comp measurable_fst).mul (hΦ.comp measurable_snd)
  have hbF : BoundedRealTest F := boundedRealTest_mul _ _
    (by obtain ⟨C, hC⟩ := hbH; exact ⟨C, fun q => hC q.1⟩)
    (by obtain ⟨C, hC⟩ := hbΦ; exact ⟨C, fun q => hC q.2⟩)
  have hi : Integrable F (μ.map S ⊗ₘ κ) := integrable_boundedRealTest _ F hF hbF
  have hfi : StronglyMeasurable (fun s => ∫ q, F (s, q) ∂κ s) :=
    hF.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
  calc
    (∫ z, H z * Φ (sampleTimeShift Δ z T) ∂μ) =
        ∫ z, F (S z, sampleTimeShift Δ z T) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with z
          simp only [F, S, Probability.finiteHistory_test_stopped Δ (n + 1) H hH]
    _ = ∫ q, F q ∂μ.map (fun z => (S z, sampleTimeShift Δ z T)) :=
      (integral_map_of_stronglyMeasurable hm hF.stronglyMeasurable).symm
    _ = ∫ s, ∫ q, F (s, q) ∂κ s ∂μ.map S := by
      rw [gridCoupledLawKernel_stopped_sampleTimeShift_eq_fresh Δ hΔ K hstart a n]
      exact Measure.integral_compProd hi
    _ = ∫ z, H z * (∫ q, Φ q ∂gridCoupledLawKernel Δ hΔ K (z.1 T, a.2)) ∂μ := by
      rw [integral_map_of_stronglyMeasurable hs hfi]
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [F, κ, Kernel.comap_apply, integral_const_mul]
      rw [show H (S z) = H z from Probability.finiteHistory_test_stopped Δ (n + 1) H hH z]
      have he : (S z).1 T = z.1 T := by
        simp [S, Probability.stoppedHistorySample, T]
      rw [he]

/-- The extended split-grid construction satisfies deterministic restart at
every starting point in its original good environment set. -/
theorem extended_splitGrid_restart_at {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R δ : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d)) (hG : MeasurableSet G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (x : Vec d) (ω : FieldPair d) (hω : ω ∈ G) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    DeterministicRestartAt Δ K (x, ω) := by
  let S := splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
  let ν : Measure (CoupledSample d) := Measure.dirac ((0 : Path d), fun _ => false)
  let E := extendEnvironmentKernel G hG S ν
  change DeterministicRestartAt Δ E (x, ω)
  intro n H Φ hH hbH hΦ hbΦ
  cases n with
  | zero =>
    simpa only [Nat.cast_zero, zero_mul] using
      extended_splitGrid_restart_zero Δ hΔ R δ i hR P G hG hP hminor hδ₁ hstart x ω hω H Φ hH
  | succ n =>
    let K := splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor
    have : IsMarkovKernel K :=
      isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
    have hs : ∀ a : Vec d × G, ∀ᵐ q ∂K a, q.1 0 = a.1 :=
      ae_splitStepKernel_starts Δ R δ i hR P G hP hminor hδ₁ hstart
    have he (y : Vec d) : E (y, ω) = S (y, ⟨ω, hω⟩) :=
      extendEnvironmentKernel_apply_of_mem G hG S ν y ω hω
    simp_rw [he]
    simpa only [Nat.succ_eq_add_one, S, splitGridCoupledLawKernel, K] using
      gridCoupledLawKernel_restart_succ Δ hΔ K hs (x, ⟨ω, hω⟩) n H Φ hH hbH hΦ hbΦ

/-- Both restart clauses hold for the same extended kernel and good set. -/
theorem extended_splitGrid_restart {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R δ : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
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
    HasDeterministicRestart Q.measure Δ K := by
  constructor
  · filter_upwards [hGae] with ω hω
    exact extended_splitGrid_restart_at Δ hΔ R δ i hR P G hG hP hminor hδ₁ hstart 0 ω hω
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hGae] with a ha
    exact extended_splitGrid_restart_at Δ hΔ R δ i hR P G hG hP hminor hδ₁ hstart a.1 a.2 ha

/-- The checked marginal, fresh-bit, support, endpoint and restart fields
belong to one and the same extended split-grid law. -/
theorem extended_splitGrid_accumulated_with_restart {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (hGMP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    (HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P ∧
      HasFreshBits Q.measure Δ δ K ∧ HasSuccessfulBridgeSupport Q.measure Δ i R K ∧
      HasUniformSuccessfulEndpoint Q.measure Δ δ R i K) ∧
      HasDeterministicRestart Q.measure Δ K := by
  exact ⟨extended_splitGrid_accumulated hd hΛ₀ Q lam h0 h1 Δ hΔ R δ i hR P hGMP
      G hG hGae hP hminor hδ₀ hδ₁ hstart,
    extended_splitGrid_restart Q Δ hΔ R δ i hR P G hG hGae hP hminor hδ₁ hstart⟩

/-- The five integrability requirements appearing in the literal one-interval
kernel statement, for every bounded finite-history and path test. -/
def OneIntervalTestsIntegrableAt {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (xω : Vec d × FieldPair d) : Prop :=
  ∀ (n : ℕ) (H : CoupledSample d → ℝ) (F : Path d → ℝ),
    @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H →
    BoundedRealTest H → Measurable F → BoundedRealTest F →
    Integrable (fun z : CoupledSample d => H z * (if z.2 n = true then (1 : ℝ) else 0) *
      F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) (K xω) ∧
    Integrable (fun z : CoupledSample d => H z *
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
        (z.1 ((n : ℝ≥0) * Δ)) xω.2)) (K xω) ∧
    Integrable (fun z : CoupledSample d => H z * (if z.2 n = true then (0 : ℝ) else 1) *
      F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) (K xω) ∧
    Integrable (fun z : CoupledSample d => H z *
      ((∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), xω.2)) - δ *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
          (z.1 ((n : ℝ≥0) * Δ)) xω.2))) (K xω) ∧
    Integrable (fun z : CoupledSample d => H z *
      (∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), xω.2))) (K xω)

/-- The same split-grid law has all five one-interval integrabilities at
both source qualifiers, in addition to its previously checked fields. -/
theorem extended_splitGrid_accumulated_with_integrabilities {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (hGMP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    ((HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P ∧
      HasFreshBits Q.measure Δ δ K ∧ HasSuccessfulBridgeSupport Q.measure Δ i R K ∧
      HasUniformSuccessfulEndpoint Q.measure Δ δ R i K) ∧
      HasDeterministicRestart Q.measure Δ K) ∧
    (∀ᵐ ω ∂Q.measure, OneIntervalTestsIntegrableAt Δ δ R i P K (0, ω)) ∧
    ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q.measure),
      OneIntervalTestsIntegrableAt Δ δ R i P K xω := by
  let K := extendEnvironmentKernel G hG
    (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
    (Measure.dirac ((0 : Path d), fun _ => false))
  have hfields := extended_splitGrid_accumulated_with_restart hd hΛ₀ Q lam h0 h1
    Δ hΔ R δ i hR P hGMP G hG hGae hP hminor hδ₀ hδ₁ hstart
  have hprob : HasProbabilityLaws Q.measure K := hfields.1.1
  refine ⟨hfields, ?_, ?_⟩
  · exact ae_oneInterval_integrabilities_origin hd hΛ₀ Q lam h0 h1 P K hGMP hprob
      Δ δ R i hR
  · exact ae_oneInterval_integrabilities_product hd hΛ₀ Q lam h0 h1 P K hGMP hprob
      Δ δ R i hR

/-- Segment-local tests may be evaluated on the stopped sampled interval in
both branches of the actual split-step kernel. -/
theorem splitStep_integral_stopped_bit {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (a : Vec d × G) (b : Bool)
    (F : Path d → ℝ) (hF : Measurable F) (hb : BoundedRealTest F)
    (hloc : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') :
    (∫ q, (if q.2 = b then (1 : ℝ) else 0) * F (stopPathAt Δ q.1)
      ∂splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor a) =
      if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P a.1 a.2.1)
      else (∫ γ, F γ ∂P (a.1, a.2.1)) -
        δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P a.1 a.2.1) := by
  have hstop (γ : Path d) : F (stopPathAt Δ γ) = F γ := by
    apply hloc
    intro t ht
    simp [stopPathAt, min_eq_left ht]
  simpa only [hstop] using
    (splitStepKernelOnEnvironments_integral_bit Δ R δ i hR P G hP hminor
      hδ₀ hδ₁ a b F hF hb).2

/-- A local test of the assembled interval equals the test of the literal
shifted path. -/
theorem gridIntervalSample_local_test {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (F : Path d → ℝ)
    (hloc : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ')
    (z : CoupledSample d) :
    F (gridIntervalSample Δ n z).1 = F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) := by
  apply hloc
  intro t ht
  simp only [gridIntervalSample, pathTimeShift, ContinuousMap.coe_mk, min_eq_left ht]

/-- The first actual grid interval has the literal split-step branch law. -/
theorem splitGrid_firstInterval_integral_bit {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (a : Vec d × G) (b : Bool)
    (F : Path d → ℝ) (hF : Measurable F) (hb : BoundedRealTest F)
    (hloc : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') :
    (∫ z, (if z.2 0 = b then (1 : ℝ) else 0) *
      F (pathTimeShift z.1 0)
      ∂splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a) =
      if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P a.1 a.2.1)
      else (∫ γ, F γ ∂P (a.1, a.2.1)) -
        δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P a.1 a.2.1) := by
  let K := splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor
  have : IsMarkovKernel K :=
    isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  let f : Path d × Bool → ℝ := fun q => (if q.2 = b then (1 : ℝ) else 0) * F q.1
  have hf : Measurable f :=
    (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      measurable_const measurable_const).mul (hF.comp measurable_fst)
  have hg : Measurable (fun q : Path d × Bool => (stopPathAt Δ q.1, q.2)) :=
    ((measurable_stopPathAt Δ).comp measurable_fst).prodMk measurable_snd
  have he := integral_map_of_stronglyMeasurable
    (μ := gridCoupledLawKernel Δ hΔ K a) (measurable_gridIntervalSample Δ 0)
    hf.stronglyMeasurable
  rw [gridCoupledLawKernel_map_firstInterval Δ hΔ K a,
    integral_map_of_stronglyMeasurable hg hf.stronglyMeasurable] at he
  have hl : (∫ z, f (gridIntervalSample Δ 0 z) ∂gridCoupledLawKernel Δ hΔ K a) =
      ∫ z, (if z.2 0 = b then (1 : ℝ) else 0) * F (pathTimeShift z.1 0)
        ∂gridCoupledLawKernel Δ hΔ K a := by
    apply integral_congr_ae
    filter_upwards [] with z
    change (if z.2 0 = b then (1 : ℝ) else 0) * F (gridIntervalSample Δ 0 z).1 = _
    rw [gridIntervalSample_local_test Δ 0 F hloc z]
    simp only [Nat.cast_zero, zero_mul]
  change (∫ z, (if z.2 0 = b then (1 : ℝ) else 0) * F (pathTimeShift z.1 0)
      ∂gridCoupledLawKernel Δ hΔ K a) = _
  rw [← hl, ← he]
  exact splitStep_integral_stopped_bit Δ R δ i hR P G hP hminor hδ₀ hδ₁ a b F hF hb hloc

/-- Both one-interval branch identities against a finite history, for the
same extended split-grid law and every start in the good environment carrier. -/
theorem extended_splitGrid_interval_bit_at {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d)) (hG : MeasurableSet G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (x : Vec d) (ω : FieldPair d) (hω : ω ∈ G) (n : ℕ) (b : Bool)
    (H : CoupledSample d → ℝ) (F : Path d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H)
    (hbH : BoundedRealTest H) (hF : Measurable F) (hbF : BoundedRealTest F)
    (hloc : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') :
    let E := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    (∫ z, H z * (if z.2 n = b then (1 : ℝ) else 0) *
      F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂E (x, ω)) =
    ∫ z, H z * (if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
      (z.1 ((n : ℝ≥0) * Δ)) ω) else
      (∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), ω)) - δ *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (z.1 ((n : ℝ≥0) * Δ)) ω))
      ∂E (x, ω) := by
  let S := splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
  let ν : Measure (CoupledSample d) := Measure.dirac ((0 : Path d), fun _ => false)
  let E := extendEnvironmentKernel G hG S ν
  let Φ : CoupledSample d → ℝ := fun z => (if z.2 0 = b then (1 : ℝ) else 0) * F z.1
  have hm : Measurable Φ :=
    (Measurable.ite (measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd)
      measurable_const) measurable_const measurable_const).mul (hF.comp measurable_fst)
  have hbbit : BoundedRealTest (fun z : CoupledSample d =>
      if z.2 0 = b then (1 : ℝ) else 0) := by
    refine ⟨1, fun z => ?_⟩
    change |(if z.2 0 = b then (1 : ℝ) else 0)| ≤ 1
    split_ifs <;> norm_num
  have hbΦ : BoundedRealTest Φ := boundedRealTest_mul _ _ hbbit
    (by obtain ⟨C, hC⟩ := hbF; exact ⟨C, fun z => hC z.1⟩)
  have hzero (γ : Path d) : pathTimeShift γ 0 = γ := by
    apply ContinuousMap.ext
    intro t
    simp only [pathTimeShift, ContinuousMap.coe_mk, zero_add]
  have hfirst (y : Vec d) : (∫ q, Φ q ∂E (y, ω)) =
      if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω)
      else (∫ γ, F γ ∂P (y, ω)) -
        δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω) := by
    rw [show E (y, ω) = S (y, ⟨ω, hω⟩) from
      extendEnvironmentKernel_apply_of_mem G hG S ν y ω hω]
    simpa only [Φ, hzero] using
      splitGrid_firstInterval_integral_bit Δ hΔ R δ i hR P G hP hminor hδ₀ hδ₁
        (y, ⟨ω, hω⟩) b F hF hbF hloc
  have hr := extended_splitGrid_restart_at Δ hΔ R δ i hR P G hG hP hminor
    hδ₁ hstart x ω hω n H Φ hH hbH hm hbΦ
  change (∫ z, H z * Φ (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂E (x, ω)) =
    ∫ z, H z * (∫ q, Φ q ∂E (z.1 ((n : ℝ≥0) * Δ), ω)) ∂E (x, ω) at hr
  simp only [hfirst] at hr
  change (∫ z, H z * (if z.2 n = b then (1 : ℝ) else 0) *
    F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂E (x, ω)) = _
  convert hr using 1
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Φ, sampleTimeShift, gridIndex_mul Δ hΔ n, Nat.add_zero, mul_assoc]

/-- The literal one-interval conditions hold at every start in the good set. -/
theorem extended_splitGrid_oneInterval_at {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d)) (hG : MeasurableSet G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (x : Vec d) (ω : FieldPair d) (hω : ω ∈ G) :
    let E := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    Renewal.OneIntervalKernelAt Δ δ R i P E (x, ω) := by
  let S := splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
  let ν : Measure (CoupledSample d) := Measure.dirac ((0 : Path d), fun _ => false)
  let E := extendEnvironmentKernel G hG S ν
  let : IsMarkovKernel S :=
    isMarkovKernel_splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
  let : IsMarkovKernel E := isMarkovKernel_extendEnvironmentKernel G hG S ν
  change Renewal.OneIntervalKernelAt Δ δ R i P E (x, ω)
  intro n H F hH hbH hF hbF hloc
  have hi := oneInterval_integrabilities_of_probability Δ δ R i hR P E (x, ω)
    (hP ω hω) n H F hH hbH hF hbF
  have ht := extended_splitGrid_interval_bit_at Δ hΔ R δ i hR P G hG hP hminor
    hδ₀ hδ₁ hstart x ω hω n true H F hH hbH hF hbF hloc
  have hf := extended_splitGrid_interval_bit_at Δ hΔ R δ i hR P G hG hP hminor
    hδ₀ hδ₁ hstart x ω hω n false H F hH hbH hF hbF hloc
  change (∫ z, H z * (if z.2 n = true then (1 : ℝ) else 0) *
    F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂E (x, ω)) = _ at ht
  change (∫ z, H z * (if z.2 n = false then (1 : ℝ) else 0) *
    F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂E (x, ω)) = _ at hf
  simp only [↓reduceIte] at ht
  simp only [Bool.false_eq_true, ↓reduceIte] at hf
  refine ⟨hi.1, hi.2.1, ?_, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2, ?_⟩
  · rw [ht]
    simp_rw [mul_left_comm (H _) δ]
    rw [integral_const_mul]
  · convert hf using 1
    apply integral_congr_ae
    filter_upwards [] with z
    cases z.2 n <;> rfl

/-- Both source almost-everywhere one-interval conditions hold for the same kernel. -/
theorem extended_splitGrid_oneInterval {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R δ : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    let E := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    Renewal.HasOneIntervalKernel Q.measure Δ δ R i P E := by
  constructor
  · filter_upwards [hGae] with ω hω
    exact extended_splitGrid_oneInterval_at Δ hΔ R δ i hR P G hG hP hminor
      hδ₀ hδ₁ hstart 0 ω hω
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hGae] with a ha
    exact extended_splitGrid_oneInterval_at Δ hΔ R δ i hR P G hG hP hminor
      hδ₀ hδ₁ hstart a.1 a.2 ha

/-- Conditional construction of the literal GMP coupling from one split-grid kernel. -/
theorem extended_splitGrid_isGMPCouplingV2 {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hΔ : 0 < Renewal.regenDelta lam) (hR : 0 < l / lam)
    (P : QuenchedPathLaws d) (hGMP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d))
          (endpointBall (Renewal.forceCoord hd) (l / lam) x) ≤
        (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (l / lam) (Renewal.forceCoord hd) P x ω).map
          (fun γ : Path d => γ (Renewal.regenDelta lam)))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    let K := extendEnvironmentKernel G hG
      (splitGridCoupledLawKernel (Renewal.regenDelta lam) hΔ (l / lam) δ (Renewal.forceCoord hd)
        hR P G hP hminor hδ₁)
      (Measure.dirac ((0 : Path d), fun _ => false))
    Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0 h1 P K := by
  have hf := extended_splitGrid_accumulated_with_restart hd hΛ₀ Q lam h0 h1
    (Renewal.regenDelta lam) hΔ (l / lam) δ (Renewal.forceCoord hd) hR P hGMP
    G hG hGae hP hminor hδ₀ hδ₁ hstart
  have hi := extended_splitGrid_oneInterval Q (Renewal.regenDelta lam) hΔ (l / lam) δ
    (Renewal.forceCoord hd) hR P G hG hGae hP hminor hδ₀ hδ₁ hstart
  exact ⟨hf.1.1, hf.1.2.1, hGMP, hf.1.2.2.1, hf.2,
    hf.1.2.2.2.1, hf.1.2.2.2.2, hi⟩

/-- Positive force and radius give a measurable Markov kernel satisfying the
literal coupling, provided the stated all-start split inputs hold. -/
theorem exists_markov_splitGrid_isGMPCouplingV2 {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (hlam : 0 < lam) (h1 : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (hGMP : IsGMPReducedKernel hd hΛ₀ Q lam hlam.le h1 P)
    (G : Set (FieldPair d)) (hG : MeasurableSet G) (hGae : ∀ᵐ ω ∂Q.measure, ω ∈ G)
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d))
          (endpointBall (Renewal.forceCoord hd) (l / lam) x) ≤
        (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (l / lam) (Renewal.forceCoord hd) P x ω).map
          (fun γ : Path d => γ (Renewal.regenDelta lam)))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    ∃ K : Kernel (Vec d × FieldPair d) (CoupledSample d),
      IsMarkovKernel K ∧ Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ hlam.le h1 P K := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hlam))
  have hR : 0 < l / lam := div_pos hl hlam
  let S := splitGridCoupledLawKernel (Renewal.regenDelta lam) hΔ (l / lam) δ
    (Renewal.forceCoord hd) hR P G hP hminor hδ₁
  let ν : Measure (CoupledSample d) := Measure.dirac ((0 : Path d), fun _ => false)
  let K := extendEnvironmentKernel G hG S ν
  let : IsMarkovKernel S := isMarkovKernel_splitGridCoupledLawKernel
    (Renewal.regenDelta lam) hΔ (l / lam) δ (Renewal.forceCoord hd) hR P G hP hminor hδ₁
  refine ⟨K, isMarkovKernel_extendEnvironmentKernel G hG S ν, ?_⟩
  exact extended_splitGrid_isGMPCouplingV2 hd hΛ₀ Q lam l δ hlam.le h1 hΔ hR P hGMP
    G hG hGae hP hminor hδ₀ hδ₁ hstart

#print axioms exists_markov_splitGrid_isGMPCouplingV2
#print axioms extended_splitGrid_isGMPCouplingV2
#print axioms extended_splitGrid_oneInterval_at
#print axioms extended_splitGrid_oneInterval
#print axioms extended_splitGrid_interval_bit_at
#print axioms gridIntervalSample_local_test
#print axioms splitGrid_firstInterval_integral_bit
#print axioms splitStep_integral_stopped_bit
#print axioms extended_splitGrid_accumulated_with_integrabilities
#print axioms extended_splitGrid_accumulated_with_restart
#print axioms extended_splitGrid_restart_at
#print axioms extended_splitGrid_restart
#print axioms gridCoupledLawKernel_restart_succ
#print axioms gridCoupledLawKernel_stopped_sampleTimeShift_eq_fresh
#print axioms gridLawKernel_stopped_sampleTimeShift_eq_fresh
#print axioms gridLawKernel_prefix_sampleTimeShift_eq_fresh
#print axioms gridLawKernel_prefix_shiftedConcat_eq_fresh
#print axioms gridLawKernel_prefix_shiftedPairs_eq_fresh
#print axioms gridContinuation_shiftedPairs_eq_fresh
#print axioms gridContinuation_pair_prefix_next
#print axioms gridContinuation_shiftedPrefix_next
#print axioms gridShiftedPrefix_restrict
#print axioms measurable_gridShiftedPrefix
#print axioms gridContinuation_start_and_shiftedPairs
#print axioms gridContinuation_map_prefix_next
#print axioms gridContinuation_prefix_and_shiftedPairs
#print axioms gridContinuation_initial_and_shiftedPairs
#print axioms gridContinuation_map_first_eq_fresh
#print axioms gridContinuation_map_first
#print axioms gridLawKernel_map_prefix_shiftedPairs
#print axioms ae_gridLawKernel_coupledConcat_shift
#print axioms coupledConcat_shift
#print axioms extended_splitGrid_restart_zero
#print axioms deterministic_restart_zero_of_start

#print axioms extended_splitGrid_accumulated
#print axioms extended_splitGrid_uniform_successful_endpoint
#print axioms splitGrid_successful_endpoint_succ

#print axioms splitGrid_successful_endpoint_zero

#print axioms extended_splitGrid_success_support
#print axioms splitGrid_success_support
#print axioms splitGrid_local_success_support
#print axioms splitGrid_concat_success_support
#print axioms splitGrid_sampled_success_support
#print axioms splitStep_successful_endpoint
#print axioms splitGrid_freshBit
#print axioms extended_splitGrid_freshBits
#print axioms extended_splitGrid_marginals_and_freshBits
#lint

end EinsteinFull.SbxS1SplitGridFreshBits
