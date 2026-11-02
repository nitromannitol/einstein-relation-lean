import EinsteinFull.Regeneration.GMPSplitRestart
import EinsteinFull.Regeneration.GMPSplitTransition
import EinsteinFull.Regeneration.GMPSplitSupportTransfer
import EinsteinFull.Blueprint.G1.Proofs.SbxS4SplitResidual
import EinsteinFull.Blueprint.G1.Proofs.SbxS10BridgeIntegrability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration EinsteinRelation.Probability
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open EinsteinFull.SbxS10BridgeIntegrability

variable {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
  (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
  (P : QuenchedPathLaws d) [IsMarkovKernel P]
  (hminor : ∀ ω : FieldPair d, HasSourceMinorization (fun x => P (x, ω)) Δ δ R i)
  (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1)

include hstart

/-- The canonical first step is the literal bridge and residual split. -/
theorem s1_oneInterval_eq_firstCoinLaw (a : Vec d × FieldPair d) :
    oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor a =
      Blueprint.sbxS4FirstCoinLaw δ (P a)
        (Renewal.killedBridgeMixture Δ R i P a.1 a.2) := by
  rw [oneIntervalSplitKernel_apply]
  rfl

include hδ₁ in
/-- Both first-coin branches have the exact bridge and residual expectations. -/
theorem s1_oneInterval_integral_bit (a : Vec d × FieldPair d) (b : Bool)
    (F : Path d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F) :
    (∫ q, (if q.2 = b then (1 : ℝ) else 0) * F q.1
      ∂oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor a) =
      if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P a.1 a.2)
      else (∫ γ, F γ ∂P a) -
        δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P a.1 a.2) := by
  let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P a.1 a.2) :=
    isProbabilityMeasure_killedBridgeMixture P a.2 Δ δ R i hδ₀ hR (hminor a.2) a.1
  have hb : ∃ C : ℝ, ∀ γ, ‖F γ‖ ≤ C := by
    simpa only [BoundedRealTest, Real.norm_eq_abs] using hbF
  have hmin : ENNReal.ofReal δ •
      ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R a.1) ≤
      (Renewal.killedSegmentLaw Δ R i P a.1 a.2).map (fun γ => γ Δ) := by
    have hs : ENNReal.ofReal δ ≤ ENNReal.ofReal (2 * δ) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    calc
      _ ≤ ENNReal.ofReal (2 * δ) •
          ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R a.1) := by
            gcongr
      _ ≤ _ := source_minorization_le_killed_endpoint P a.2 Δ δ R i (hminor a.2) a.1
  have hbranch := (Blueprint.sbxS4_firstCoinLaw_integral_branch δ (P a)
    (Renewal.killedBridgeMixture Δ R i P a.1 a.2) hδ₀.le hδ₁
    (Blueprint.sbxS4_smul_killedBridgeMixture_le Δ R δ i P a.1 a.2 hR hmin)
    F hF.stronglyMeasurable hb b).2
  rw [s1_oneInterval_eq_firstCoinLaw (hδ₀ := hδ₀) (hstart := hstart)]
  have he : (∫ q, (if q.2 = b then (1 : ℝ) else 0) * F q.1
      ∂Blueprint.sbxS4FirstCoinLaw δ (P a) (Renewal.killedBridgeMixture Δ R i P a.1 a.2)) =
      ∫ q, {q : Path d × Bool | q.2 = b}.indicator (fun q => F q.1) q
        ∂Blueprint.sbxS4FirstCoinLaw δ (P a) (Renewal.killedBridgeMixture Δ R i P a.1 a.2) := by
    apply integral_congr_ae
    filter_upwards [] with q
    by_cases hq : q.2 = b <;> simp [Set.indicator, hq]
  rw [he, hbranch]
  cases b with
  | true => rfl
  | false =>
    exact Blueprint.sbxS4_failedSegmentLaw_integral_difference Δ R δ i P a.1 a.2
      hR hδ₀ hδ₁ hmin F hF hbF

/-- A local first-interval test under the canonical path law sees the
literal successful and failed bridge branches. -/
theorem s1_canonical_first_interval_bit (a : Vec d × FieldPair d) (b : Bool)
    (F : Path d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F)
    (hloc : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') :
    (∫ z, (if z.2 0 = b then (1 : ℝ) else 0) * F z.1
      ∂splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor a) =
      if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P a.1 a.2)
      else (∫ γ, F γ ∂P a) -
        δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P a.1 a.2) := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  let J := oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor
  let f : Path d × Bool → ℝ := fun q => (if q.2 = b then (1 : ℝ) else 0) * F q.1
  have hf : Measurable f :=
    (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      measurable_const measurable_const).mul (hF.comp measurable_fst)
  have hg : Measurable (fun q : Path d × Bool => (intervalPath Δ 0 q.1, q.2)) :=
    ((continuous_intervalPath Δ 0).measurable.comp measurable_fst).prodMk measurable_snd
  have he := integral_map_of_stronglyMeasurable (μ := K a)
    (measurable_intervalObservation Δ 0) hf.stronglyMeasurable
  have hk := congrArg (fun k => k a)
    (map_splitContinuousCouplingKernel_first_observation Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart)
  rw [Kernel.map_apply _ (measurable_intervalObservation Δ 0),
    Kernel.map_apply _ hg] at hk
  rw [hk, integral_map_of_stronglyMeasurable hg hf.stronglyMeasurable] at he
  have hstop (γ : Path d) : F (intervalPath Δ 0 γ) = F γ := by
    apply hloc
    intro t ht
    simp [intervalPath_apply, min_eq_left ht]
  have he' : (∫ z, (if z.2 0 = b then (1 : ℝ) else 0) * F z.1 ∂K a) =
      ∫ q, (if q.2 = b then (1 : ℝ) else 0) * F q.1 ∂J a := by
    simpa only [f, intervalObservation, hstop] using he.symm
  rw [he']
  exact s1_oneInterval_integral_bit Δ δ R i hδ₀ hδ₁ hR P hminor hstart a b F hF hbF

/-- Both bridge branches hold at every interval against finite history. -/
theorem s1_canonical_interval_bit (a : Vec d × FieldPair d) (n : ℕ) (b : Bool)
    (H : CoupledSample d → ℝ) (F : Path d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H)
    (hbH : BoundedRealTest H) (hF : Measurable F) (hbF : BoundedRealTest F)
    (hloc : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') :
    let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    (∫ z, H z * (if z.2 n = b then (1 : ℝ) else 0) *
      F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂K a) =
    ∫ z, H z * (if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
      (z.1 ((n : ℝ≥0) * Δ)) a.2) else
      (∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), a.2)) - δ *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (z.1 ((n : ℝ≥0) * Δ)) a.2)) ∂K a := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
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
  have hfirst (y : Vec d) : (∫ q, Φ q ∂K (y, a.2)) =
      if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y a.2)
      else (∫ γ, F γ ∂P (y, a.2)) -
        δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y a.2) := by
    exact s1_canonical_first_interval_bit Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart
      (y, a.2) b F hF hbF hloc
  have hr := deterministicRestartAt_splitContinuousCouplingKernel Δ hΔ δ R i
    hδ₀ hδ₁ hR P hminor hstart a n H Φ hH hbH hm hbΦ
  change (∫ z, H z * Φ (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂K a) =
    ∫ z, H z * (∫ q, Φ q ∂K (z.1 ((n : ℝ≥0) * Δ), a.2)) ∂K a at hr
  simp only [hfirst] at hr
  change (∫ z, H z * (if z.2 n = b then (1 : ℝ) else 0) *
    F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂K a) = _
  convert hr using 1
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Φ, sampleTimeShift, gridIndex_mul Δ hΔ n, Nat.add_zero, mul_assoc]

/-- The canonical split satisfies the full one-interval kernel condition at
all positions and environments under the global source inputs. -/
theorem s1_canonical_oneInterval_at (a : Vec d × FieldPair d) :
    Renewal.OneIntervalKernelAt Δ δ R i P
      (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor) a := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  change Renewal.OneIntervalKernelAt Δ δ R i P K a
  intro n H F hH hbH hF hbF hloc
  have hi := oneInterval_integrabilities_of_probability Δ δ R i hR P K a
    (fun _ => inferInstance) n H F hH hbH hF hbF
  have ht := s1_canonical_interval_bit Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart
    a n true H F hH hbH hF hbF hloc
  have hf := s1_canonical_interval_bit Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart
    a n false H F hH hbH hF hbF hloc
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

/-- Both almost-everywhere one-interval clauses hold for the joint split. -/
theorem s1_canonical_hasOneIntervalKernel (Q : Measure (FieldPair d)) :
    Renewal.HasOneIntervalKernel Q Δ δ R i P
      (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor) :=
  ⟨Filter.Eventually.of_forall (fun _ => s1_canonical_oneInterval_at Δ hΔ δ R i
      hδ₀ hδ₁ hR P hminor hstart _),
    Filter.Eventually.of_forall (fun _ => s1_canonical_oneInterval_at Δ hΔ δ R i
      hδ₀ hδ₁ hR P hminor hstart _)⟩

/-- Successful canonical segments stay in the source tube on every interval. -/
theorem s1_canonical_successfulSupport_at (a : Vec d × FieldPair d) :
    SuccessfulBridgeSupportAt Δ i R
      (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor) a := by
  classical
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  let S : Set (Path d) := {γ | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R (γ 0)}
  have hS : MeasurableSet S := measurableSet_source_split_support Δ i R
  let F : Path d → ℝ := Sᶜ.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hS.compl
  have hFbound : ∀ γ, |F γ| ≤ 1 := by
    intro γ
    by_cases hγ : γ ∈ S <;> simp [F, hγ]
  have hbF : BoundedRealTest F := ⟨1, hFbound⟩
  have hloc : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ' := by
    intro γ γ' h
    have he : γ ∈ S ↔ γ' ∈ S := by
      change (∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R (γ 0)) ↔
        (∀ t : ℝ≥0, t ≤ Δ → γ' t ∈ couplingRegion i R (γ' 0))
      constructor <;> intro hh t ht
      · simpa only [h 0 bot_le, h t ht] using hh t ht
      · simpa only [h 0 bot_le, h t ht] using hh t ht
    by_cases ha : γ ∈ S <;> by_cases hb : γ' ∈ S <;> simp_all [F]
  have hzero (y : Vec d) :
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y a.2) = 0 := by
    have hac : Renewal.killedBridgeMixture Δ R i P y a.2 ≪ P (y, a.2) :=
      (Measure.absolutelyContinuous_smul (ENNReal.ofReal_pos.mpr hδ₀).ne').trans
        (Measure.absolutelyContinuous_of_le
          (smul_killedBridgeMixture_le_pathLaw P a.2 Δ δ R i hδ₀.le (hminor a.2) y))
    apply integral_eq_zero_of_ae
    filter_upwards [hac.ae_le (hstart (y, a.2)),
      ae_killedBridgeMixture_stays_in_couplingRegion P a.2 Δ R i y] with γ hγ₀ hγ
    have hmem : γ ∈ S := by simpa only [S, Set.mem_setOf_eq, hγ₀] using hγ
    simp [F, hmem]
  have hall : ∀ n : ℕ, ∀ᵐ z ∂K a,
      z.2 n = true → pathTimeShift z.1 ((n : ℝ≥0) * Δ) ∈ S := by
    intro n
    have ht := s1_canonical_oneInterval_at Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a
      n (fun _ => 1) F measurable_const ⟨1, by simp⟩ hF hbF hloc
    have hi := ht.1
    have he := ht.2.2.1
    simp only [one_mul, hzero, mul_zero, integral_zero] at he hi
    have hn : 0 ≤ fun z : CoupledSample d =>
        (if z.2 n = true then (1 : ℝ) else 0) *
          F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) := by
      intro z
      apply mul_nonneg
      · split <;> norm_num
      · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hae := (integral_eq_zero_iff_of_nonneg hn hi).1 he
    filter_upwards [hae] with z hz hbit
    by_contra hbad
    have hone : (if z.2 n = true then (1 : ℝ) else 0) *
        F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) = 1 := by simp [hbit, F, hbad]
    rw [hone] at hz
    norm_num at hz
  filter_upwards [ae_all_iff.2 hall] with z hz
  intro n hbit t ht₀ ht₁
  have hu : t - (n : ℝ≥0) * Δ ≤ Δ := by
    have h := tsub_le_tsub_right ht₁ ((n : ℝ≥0) * Δ)
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_tsub_cancel_left] using h
  have h := hz n hbit (t - (n : ℝ≥0) * Δ) hu
  simpa only [pathTimeShift, ContinuousMap.coe_mk, add_zero,
    add_tsub_cancel_of_le ht₀] using h

/-- Successful bridge support holds on both source fibres. -/
theorem s1_canonical_hasSuccessfulBridgeSupport (Q : Measure (FieldPair d)) :
    HasSuccessfulBridgeSupport Q Δ i R
      (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor) :=
  ⟨Filter.Eventually.of_forall (fun _ => s1_canonical_successfulSupport_at Δ hΔ δ R i
      hδ₀ hδ₁ hR P hminor hstart _),
    Filter.Eventually.of_forall (fun _ => s1_canonical_successfulSupport_at Δ hΔ δ R i
      hδ₀ hδ₁ hR P hminor hstart _)⟩

/-- The successful endpoint has the literal uniform-ball law at every start. -/
theorem s1_canonical_uniformEndpoint_at (a : Vec d × FieldPair d) :
    UniformSuccessfulEndpointAt Δ δ R i
      (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor) a := by
  intro n H φ hH hbH hφ hbφ
  let F : Path d → ℝ := fun γ => φ (γ Δ)
  have hF : Measurable F := hφ.comp (continuous_eval_const Δ).measurable
  have hbF : BoundedRealTest F := by
    obtain ⟨C, hC⟩ := hbφ
    exact ⟨C, fun γ => hC (γ Δ)⟩
  have hloc : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ' := by
    intro γ γ' h
    exact congrArg φ (h Δ le_rfl)
  have ht := s1_canonical_interval_bit Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart
    a n true H F hH hbH hF hbF hloc
  simp only [↓reduceIte] at ht
  have he (x : Vec d) : (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P x a.2) =
      endpointAverage i R x φ := by
    change (∫ γ, φ (γ Δ) ∂Renewal.killedBridgeMixture Δ R i P x a.2) = _
    rw [← integral_map (continuous_eval_const Δ).measurable.aemeasurable hφ.aestronglyMeasurable,
      map_killedBridgeMixture_endpoint_eq_uniform P a.2 Δ δ R i hδ₀ (hminor a.2) x]
    exact Blueprint.sbxS4_integral_cond_endpointBall i R x φ
  simp only [he] at ht
  simp_rw [mul_left_comm (H _) δ] at ht
  rw [integral_const_mul] at ht
  convert ht using 1
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [F, pathTimeShift, ContinuousMap.coe_mk, Nat.cast_add, Nat.cast_one,
    add_mul, one_mul]

/-- The uniform successful endpoint clauses hold for the joint split. -/
theorem s1_canonical_hasUniformSuccessfulEndpoint (Q : Measure (FieldPair d)) :
    HasUniformSuccessfulEndpoint Q Δ δ R i
      (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor) :=
  ⟨Filter.Eventually.of_forall (fun _ => s1_canonical_uniformEndpoint_at Δ hΔ δ R i
      hδ₀ hδ₁ hR P hminor hstart _),
    Filter.Eventually.of_forall (fun _ => s1_canonical_uniformEndpoint_at Δ hΔ δ R i
      hδ₀ hδ₁ hR P hminor hstart _)⟩

/-- The jointly measurable canonical split has deterministic restart at every
starting position and environment. -/
theorem s1_canonical_hasDeterministicRestart (Q : Measure (FieldPair d)) :
    HasDeterministicRestart Q Δ
      (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor) :=
  hasDeterministicRestart_splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart Q

/-- At every environment identified with a GMP realization, the canonical
joint split has the whole original path law as its marginal. -/
theorem s1_canonical_pathMarginal_of_gmp {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω ωG : FieldPair d} {hω : IsRegular L ωG} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ωG hω lam h₀ h₁)
    (hG : ∀ x, P (x, ω) = G.pathLaw x) (x : Vec d) :
    (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor (x, ω)).map Prod.fst =
      P (x, ω) := by
  apply map_splitContinuousCouplingKernel_path Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart
  intro n
  have hs : P.comap (fun y : Vec d => (y, ω))
      (measurable_id.prodMk measurable_const) = G.pathLaw := by
    ext y : 1
    exact hG y
  rw [hG x, hs]
  exact gmpPathLaw_prefix_future_joint G ((n + 1 : ℕ) * Δ) x

/-- The marginal identification holds simultaneously at all starting points
for almost every environment of the actual reduced GMP law. -/
theorem s1_canonical_pathMarginal_ae (hd : 2 ≤ d) {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {lam : ℝ} (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀ h₁ P) :
    ∀ᵐ ω ∂Q.measure, ∀ x,
      (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor (x, ω)).map Prod.fst =
        P (x, ω) := by
  filter_upwards [hP] with ω hω
  obtain ⟨_, G, hG⟩ := hω
  intro x
  exact s1_canonical_pathMarginal_of_gmp Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart G hG x

/-- The actual joint construction has the paper's origin and product-a.e.
path marginals, as well as probability, fresh-bit and restart clauses. -/
theorem s1_canonical_core_clauses (hd : 2 ≤ d) {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {lam : ℝ} (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀ h₁ P) :
    let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P ∧
      HasFreshBits Q.measure Δ δ K ∧ HasDeterministicRestart Q.measure Δ K := by
  dsimp only
  have hm := s1_canonical_pathMarginal_ae Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart
    hd Q h₀ h₁ hP
  refine ⟨⟨Filter.Eventually.of_forall (fun _ => inferInstance),
    Filter.Eventually.of_forall (fun _ => inferInstance)⟩, ?_,
    hasFreshBits_splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor Q.measure hstart,
    s1_canonical_hasDeterministicRestart Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart Q.measure⟩
  constructor
  · filter_upwards [hm] with ω hω
    exact hω 0
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hm] with a ha
    exact ha a.1

/-- All eight source coupling clauses hold for the canonical joint kernel,
under the stated global minorization and starting-point assumptions. -/
theorem s1_canonical_all_clauses (hd : 2 ≤ d) {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {lam : ℝ} (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀ h₁ P) :
    let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P ∧
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀ h₁ P ∧
      HasFreshBits Q.measure Δ δ K ∧ HasDeterministicRestart Q.measure Δ K ∧
      HasSuccessfulBridgeSupport Q.measure Δ i R K ∧
      HasUniformSuccessfulEndpoint Q.measure Δ δ R i K ∧
      Renewal.HasOneIntervalKernel Q.measure Δ δ R i P K := by
  obtain ⟨hp, hm, hf, hr⟩ :=
    s1_canonical_core_clauses Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart hd Q h₀ h₁ hP
  exact ⟨hp, hm, hP, hf, hr,
    s1_canonical_hasSuccessfulBridgeSupport Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart Q.measure,
    s1_canonical_hasUniformSuccessfulEndpoint Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart Q.measure,
    s1_canonical_hasOneIntervalKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart Q.measure⟩


/-- Every finite cylinder of the canonical joint coin sequence has the
source Bernoulli product probability at every starting pair. -/
theorem s1_canonical_coin_cylinder (a : Vec d × FieldPair d)
    (S : Finset ℕ) (b : ℕ → Bool) :
    splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor a
      {z | ∀ k ∈ S, z.2 k = b k} =
      ∏ k ∈ S, ENNReal.ofReal (if b k then δ else 1 - δ) := by
  have hm : MeasurableSet {z : CoupledSample d | ∀ k ∈ S, z.2 k = b k} := by
    have he : {z : CoupledSample d | ∀ k ∈ S, z.2 k = b k} =
        ⋂ k ∈ S, {z : CoupledSample d | z.2 k = b k} := by ext z; simp
    rw [he]
    exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ =>
      measurableSet_eq_fun ((measurable_pi_apply k).comp measurable_snd) measurable_const))
  rw [splitContinuousCouplingKernel, Kernel.map_apply _
    (measurable_gluedSplitSegmentSample Δ hΔ), Measure.map_apply
      (measurable_gluedSplitSegmentSample Δ hΔ) hm]
  have h := splitSegmentSequenceKernel_coin_cylinder Δ δ R i hδ₀ hδ₁ hR P hminor a S
    (fun k => {b k}) (fun _ => measurableSet_singleton _)
  have he : (gluedSplitSegmentSample Δ hΔ) ⁻¹'
      {z : CoupledSample d | ∀ k ∈ S, z.2 k = b k} =
      ⋂ k ∈ S, (fun s : ℕ → SplitSegmentState d => (s k).2.2) ⁻¹' {b k} := by
    ext s
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_singleton_iff, gluedSplitSegmentSample]
  rw [he]
  simpa only [splitCoinLaw_singleton] using h


/-- The first three fixed-environment source clauses hold simultaneously at
all spatial starting points on the GMP identification event. -/
theorem s1_canonical_source_first_clauses_ae (hd : 2 ≤ d) {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {lam : ℝ} (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀ h₁ P) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      IsProbabilityMeasure (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor (x, ω)) ∧
      (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor (x, ω)).map Prod.fst = P (x, ω) ∧
      ∀ (S : Finset ℕ) (b : ℕ → Bool),
        splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor (x, ω)
          {z | ∀ k ∈ S, z.2 k = b k} =
          ∏ k ∈ S, ENNReal.ofReal (if b k then δ else 1 - δ) := by
  filter_upwards [s1_canonical_pathMarginal_ae Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart
    hd Q h₀ h₁ hP] with ω hω
  intro x
  exact ⟨inferInstance, hω x, fun S b =>
    s1_canonical_coin_cylinder Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart (x, ω) S b⟩


/-- Conditioning the canonical joint law on a successful first coin gives the
literal source tube support for its path marginal. -/
theorem s1_canonical_conditional_successfulSupport (a : Vec d × FieldPair d) :
    ∀ᵐ γ ∂conditionalPathLaw
        (fun x => splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor (x, a.2))
        a.1 true,
      ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R a.1 := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  let S : Set (Path d) := {γ | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R (γ 0)}
  have hS : MeasurableSet S := measurableSet_source_split_support Δ i R
  have hc : MeasurableSet {z : CoupledSample d | z.2 0 = true} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd) measurable_const
  have hgood : ∀ᵐ z ∂K a, z.2 0 = true → z.1 ∈ S := by
    filter_upwards [s1_canonical_successfulSupport_at Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a] with z hz hcoin
    intro t ht
    have h := hz 0 hcoin t (by simp) (by simpa using ht)
    simpa only [Nat.cast_zero, zero_mul] using h
  have hcond : ∀ᵐ z ∂ProbabilityTheory.cond (K a) {z | z.2 0 = true}, z.1 ∈ S := by
    unfold ProbabilityTheory.cond
    apply Measure.ae_smul_measure
    exact (ae_restrict_iff' hc).2 hgood
  have hpath : ∀ᵐ γ ∂conditionalPathLaw (fun x => K (x, a.2)) a.1 true, γ ∈ S := by
    apply (ae_map_iff measurable_fst.aemeasurable hS).2
    exact hcond
  have hstart' : ∀ᵐ γ ∂conditionalPathLaw (fun x => K (x, a.2)) a.1 true, γ 0 = a.1 := by
    apply (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_eq_fun (measurable_pathPosition 0) measurable_const)).2
    exact ProbabilityTheory.cond_absolutelyContinuous.ae_le
      (ae_splitContinuousCouplingKernel_start Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a)
  filter_upwards [hpath, hstart'] with γ hγ hγ₀ t ht
  simpa only [S, Set.mem_setOf_eq, hγ₀] using hγ t ht


/-- A successful first coin weights the conditional path integral by its
literal Bernoulli probability. -/
theorem s1_canonical_first_coin_integral (a : Vec d × FieldPair d)
    (F : Path d → ℝ) (hF : Measurable F) :
    (∫ z, (if z.2 0 = true then 1 else 0) * F z.1
      ∂splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor a) =
      δ * ∫ γ, F γ ∂conditionalPathLaw
        (fun x => splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor (x, a.2))
        a.1 true := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  have hs : MeasurableSet {z : CoupledSample d | z.2 0 = true} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd) measurable_const
  have hp : K a {z | z.2 0 = true} = ENNReal.ofReal δ := by
    have h := s1_canonical_coin_cylinder Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a
      ({0} : Finset ℕ) (fun _ => true)
    simpa using h
  change (∫ z, (if z.2 0 = true then 1 else 0) * F z.1 ∂K a) = _
  rw [conditionalPathLaw,
    integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable,
    ProbabilityTheory.cond, integral_smul_measure, hp,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hδ₀.le, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hδ₀.ne', one_mul]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : z.2 0 = true <;> simp [hz]


/-- The first successful conditional path law and the killed bridge agree on
all bounded measurable observations of the first interval. -/
theorem s1_canonical_conditional_bridge_integral (a : Vec d × FieldPair d)
    (F : Path d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F)
    (hloc : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') :
    (∫ γ, F γ ∂conditionalPathLaw
      (fun x => splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor (x, a.2))
        a.1 true) = ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P a.1 a.2 := by
  apply mul_left_cancel₀ hδ₀.ne'
  rw [← s1_canonical_first_coin_integral Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a F hF]
  simpa only [↓reduceIte] using s1_canonical_first_interval_bit Δ hΔ δ R i hδ₀ hδ₁ hR
    P hminor hstart a true F hF hbF hloc


/-- The first successful conditional endpoint has the exact uniform-ball law. -/
theorem s1_canonical_conditional_successfulEndpoint (a : Vec d × FieldPair d) :
    (conditionalPathLaw
      (fun x => splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor (x, a.2))
        a.1 true).map (fun γ => γ Δ) =
      ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R a.1) := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  let C := conditionalPathLaw (fun x => K (x, a.2)) a.1 true
  let B := Renewal.killedBridgeMixture Δ R i P a.1 a.2
  have hp : K a {z | z.2 0 = true} = ENNReal.ofReal δ := by
    have h := s1_canonical_coin_cylinder Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a
      ({0} : Finset ℕ) (fun _ => true)
    simpa using h
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond (K a) {z | z.2 0 = true}) :=
    ProbabilityTheory.cond_isProbabilityMeasure (by rw [hp]; exact (ENNReal.ofReal_pos.mpr hδ₀).ne')
  haveI : IsProbabilityMeasure C := by
    dsimp only [C, conditionalPathLaw]
    infer_instance
  haveI : IsProbabilityMeasure B :=
    isProbabilityMeasure_killedBridgeMixture P a.2 Δ δ R i hδ₀ hR (hminor a.2) a.1
  have he : C.map (fun γ => γ Δ) = B.map (fun γ => γ Δ) := by
    apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_map (continuous_eval_const Δ).measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable,
      integral_map (continuous_eval_const Δ).measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable]
    apply s1_canonical_conditional_bridge_integral Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a
    · exact f.continuous.measurable.comp (continuous_eval_const Δ).measurable
    · exact ⟨‖f‖, fun γ => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (γ Δ)⟩
    · intro γ γ' h
      exact congrArg f (h Δ le_rfl)
  rw [he]
  exact map_killedBridgeMixture_endpoint_eq_uniform P a.2 Δ δ R i hδ₀ (hminor a.2) a.1


/-- Future coin observations factor from every bounded finite-history test. -/
theorem s1_canonical_future_coins_integral (a : Vec d × FieldPair d) (n : ℕ)
    (H : CoupledSample d → ℝ) (G : (ℕ → Bool) → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H)
    (hbH : BoundedRealTest H) (hG : Measurable G) (hbG : BoundedRealTest G) :
    let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    (∫ z, H z * G (fun k => z.2 (n + k)) ∂K a) =
      (∫ z, H z ∂K a) * ∫ c, G c ∂Measure.infinitePi (fun _ : ℕ => splitCoinLaw δ) := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  let Φ : CoupledSample d → ℝ := fun z => G z.2
  have hm : Measurable Φ := hG.comp measurable_snd
  have hbΦ : BoundedRealTest Φ := by
    obtain ⟨C, hC⟩ := hbG
    exact ⟨C, fun z => hC z.2⟩
  have hi (y : Vec d) : (∫ z, Φ z ∂K (y, a.2)) =
      ∫ c, G c ∂Measure.infinitePi (fun _ : ℕ => splitCoinLaw δ) := by
    rw [← integral_map measurable_snd.aemeasurable hG.aestronglyMeasurable]
    have h := congrArg (fun κ => κ (y, a.2))
      (map_splitContinuousCouplingKernel_coin_product Δ δ R i hδ₀ hδ₁ hR P hminor hΔ)
    rw [Kernel.map_apply _ measurable_snd, Kernel.const_apply] at h
    rw [h]
  have hr := deterministicRestartAt_splitContinuousCouplingKernel Δ hΔ δ R i
    hδ₀ hδ₁ hR P hminor hstart a n H Φ hH hbH hm hbΦ
  change (∫ z, H z * Φ (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂K a) =
    ∫ z, H z * (∫ q, Φ q ∂K (z.1 ((n : ℝ≥0) * Δ), a.2)) ∂K a at hr
  simp only [hi, integral_mul_const] at hr
  convert hr using 1
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Φ, sampleTimeShift, gridIndex_mul Δ hΔ n]


/-- The whole future coin sequence is independent of the finite history. -/
theorem s1_canonical_future_coins_indep (a : Vec d × FieldPair d) (n : ℕ) :
    ProbabilityTheory.Indep
      (MeasurableSpace.comap (fun z : CoupledSample d => fun k : ℕ => z.2 (n + k))
        inferInstance) (finiteHistorySigma Δ n)
      (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor a) := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  haveI : IsProbabilityMeasure (K a) := inferInstance
  let future : CoupledSample d → (ℕ → Bool) := fun z k => z.2 (n + k)
  have hf : Measurable future := by
    fun_prop
  rw [ProbabilityTheory.Indep_iff]
  intro s t hs ht
  obtain ⟨A, hA, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have ht' : MeasurableSet t := (EinsteinRelation.Probability.finiteHistorySigma_le Δ n) t ht
  have hpre : MeasurableSet (future ⁻¹' A) := hf hA
  have hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance
      (t.indicator 1) := measurable_const.indicator ht
  have hG : Measurable (A.indicator (1 : (ℕ → Bool) → ℝ)) := measurable_const.indicator hA
  have hbH : BoundedRealTest (t.indicator (1 : CoupledSample d → ℝ)) := by
    refine ⟨1, fun z => ?_⟩
    by_cases hz : z ∈ t <;> simp [hz]
  have hbG : BoundedRealTest (A.indicator (1 : (ℕ → Bool) → ℝ)) := by
    refine ⟨1, fun z => ?_⟩
    by_cases hz : z ∈ A <;> simp [hz]
  have hfactor := s1_canonical_future_coins_integral Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    hstart a n (t.indicator 1) (A.indicator 1) hH hbH hG hbG
  have hone := s1_canonical_future_coins_integral Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    hstart a n (fun _ => 1) (A.indicator 1) measurable_const ⟨1, by simp⟩ hG hbG
  change (∫ z, t.indicator 1 z * A.indicator 1 (future z) ∂K a) = _ at hfactor
  change (∫ z, (1 : ℝ) * A.indicator 1 (future z) ∂K a) = _ at hone
  simp only [one_mul, integral_const, measure_univ, ENNReal.toReal_one, smul_eq_mul,
    mul_one, one_mul, measureReal_def] at hone
  rw [← hone, integral_indicator_one ht'] at hfactor
  have hleft : (∫ z, t.indicator 1 z * A.indicator 1 (future z) ∂K a) =
      (K a).real (future ⁻¹' A ∩ t) := by
    rw [← integral_indicator_one (hpre.inter ht')]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hza : future z ∈ A <;> by_cases hzt : z ∈ t <;> simp [hza, hzt]
  have hright : (∫ z, A.indicator 1 (future z) ∂K a) = (K a).real (future ⁻¹' A) := by
    rw [← integral_indicator_one hpre]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : future z ∈ A <;> simp [hz]
  rw [hleft, hright] at hfactor
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top (K a) _)
    (ENNReal.mul_ne_top (measure_ne_top (K a) _) (measure_ne_top (K a) _)), ENNReal.toReal_mul]
  simpa only [measureReal_def, mul_comm] using hfactor


/-- Each first coin branch weights its literal conditional path law. -/
theorem s1_canonical_first_coin_branch_integral (a : Vec d × FieldPair d) (b : Bool)
    (F : Path d → ℝ) (hF : Measurable F) :
    (∫ z, (if z.2 0 = b then 1 else 0) * F z.1
      ∂splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor a) =
      (if b then δ else 1 - δ) * ∫ γ, F γ ∂conditionalPathLaw
        (fun x => splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor (x, a.2))
        a.1 b := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  have hs : MeasurableSet {z : CoupledSample d | z.2 0 = b} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd) measurable_const
  have hw : 0 < (if b then δ else 1 - δ) := by
    cases b
    · exact sub_pos.mpr hδ₁
    · exact hδ₀
  have hp : K a {z | z.2 0 = b} = ENNReal.ofReal (if b then δ else 1 - δ) := by
    have h := s1_canonical_coin_cylinder Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a
      ({0} : Finset ℕ) (fun _ => b)
    simpa using h
  change (∫ z, (if z.2 0 = b then 1 else 0) * F z.1 ∂K a) = _
  rw [conditionalPathLaw,
    integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable,
    ProbabilityTheory.cond, integral_smul_measure, hp,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hw.le, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : z.2 0 = b <;> simp [hz]

/-- Restart on each current-coin branch against a finite-history test. -/
theorem s1_canonical_restart_coin_branch (a : Vec d × FieldPair d) (n : ℕ) (b : Bool)
    (H : CoupledSample d → ℝ) (F : Path d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H)
    (hbH : BoundedRealTest H) (hF : Measurable F) (hbF : BoundedRealTest F) :
    let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    (∫ z, H z * (if z.2 n = b then 1 else 0) *
      F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂K a) =
    ∫ z, H z * ((if b then δ else 1 - δ) * ∫ γ, F γ ∂conditionalPathLaw
      (fun x => K (x, a.2)) (z.1 ((n : ℝ≥0) * Δ)) b) ∂K a := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  let Φ : CoupledSample d → ℝ := fun z => (if z.2 0 = b then 1 else 0) * F z.1
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
  have hi (y : Vec d) : (∫ z, Φ z ∂K (y, a.2)) =
      (if b then δ else 1 - δ) * ∫ γ, F γ ∂conditionalPathLaw
        (fun x => K (x, a.2)) y b :=
    s1_canonical_first_coin_branch_integral Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart
      (y, a.2) b F hF
  have hr := deterministicRestartAt_splitContinuousCouplingKernel Δ hΔ δ R i
    hδ₀ hδ₁ hR P hminor hstart a n H Φ hH hbH hm hbΦ
  change (∫ z, H z * Φ (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂K a) =
    ∫ z, H z * (∫ q, Φ q ∂K (z.1 ((n : ℝ≥0) * Δ), a.2)) ∂K a at hr
  simp only [hi] at hr
  convert hr using 1
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Φ, sampleTimeShift, gridIndex_mul Δ hΔ n, Nat.add_zero, mul_assoc]


/-- A current-coin history test has a finite-history version on each coin branch. -/
theorem s1_current_coin_history_branch (n : ℕ) (b : Bool)
    (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (currentCoinHistory Δ n) inferInstance H)
    (hbH : BoundedRealTest H) :
    ∃ G : CoupledSample d → ℝ,
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance G ∧
      BoundedRealTest G ∧ ∀ z, z.2 n = b → G z = H z := by
  classical
  let fix : CoupledSample d → CoupledSample d :=
    fun z => (z.1, fun k => if k = n then b else z.2 k)
  let T : CoupledSample d → CoupledSample d × Bool :=
    fun z => (stoppedHistorySample Δ n z, z.2 n)
  have hstop (z : CoupledSample d) :
      stoppedHistorySample Δ n (fix z) = stoppedHistorySample Δ n z := by
    apply Prod.ext
    · rfl
    · funext k
      by_cases hk : k < n
      · have hkn : k ≠ n := Nat.ne_of_lt hk
        simp [stoppedHistorySample, fix, hk, hkn]
      · simp [stoppedHistorySample, fix, hk]
  have hspace : currentCoinHistory (d := d) Δ n =
      MeasurableSpace.comap T inferInstance := by
    rw [currentCoinHistory, EinsteinRelation.Probability.finiteHistorySigma_eq_comap_stopped,
      ← MeasurableSpace.comap_prodMk]
    rfl
  have hfix : @Measurable (CoupledSample d) (CoupledSample d)
      (finiteHistorySigma Δ n) (currentCoinHistory Δ n) fix := by
    rw [hspace]
    apply Measurable.of_comap_le
    have hm : @Measurable (CoupledSample d) (CoupledSample d × Bool)
        (finiteHistorySigma Δ n) inferInstance (T ∘ fix) := by
      have heq : T ∘ fix = fun z => (stoppedHistorySample Δ n z, b) := by
        funext z
        simp [Function.comp_def, T, fix, hstop]
      rw [heq]
      exact (EinsteinRelation.Probability.measurable_stoppedHistorySample Δ n).prodMk
        measurable_const
    simpa only [MeasurableSpace.comap_comp] using hm.comap_le
  refine ⟨H ∘ fix, hH.comp hfix, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hbH
    exact ⟨C, fun z => hC (fix z)⟩
  · intro z hz
    have hmeas := hH (measurableSet_singleton (H z))
    rw [hspace, MeasurableSpace.measurableSet_comap] at hmeas
    obtain ⟨A, hA, hpre⟩ := hmeas
    have hzA : T z ∈ A := by
      have : z ∈ H ⁻¹' {H z} := by simp
      rw [← hpre] at this
      exact this
    have hT : T (fix z) = T z := by
      simp [T, hstop, fix, hz]
    have hmem : fix z ∈ H ⁻¹' {H z} := by
      rw [← hpre]
      simpa [hT] using hzA
    exact hmem


/-- A finite-history observation factors from the current coin. -/
theorem s1_canonical_coin_test (a : Vec d × FieldPair d) (n : ℕ) (b : Bool)
    (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H) :
    let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    (∫ z, H z * (if z.2 n = b then 1 else 0) ∂K a) =
      (if b then δ else 1 - δ) * ∫ z, H z ∂K a := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  let χ : CoupledSample d → ℝ := fun z => if z.2 n = b then 1 else 0
  have hs : MeasurableSet {z : CoupledSample d | z.2 n = b} :=
    measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const
  have hχ : Measurable χ := measurable_const.ite hs measurable_const
  have hχfuture : @Measurable (CoupledSample d) ℝ
      (MeasurableSpace.comap (fun z : CoupledSample d => fun k : ℕ => z.2 (n + k))
        inferInstance) inferInstance χ := by
    have hf : @Measurable (CoupledSample d) (ℕ → Bool)
        (MeasurableSpace.comap (fun z : CoupledSample d => fun k : ℕ => z.2 (n + k))
          inferInstance) inferInstance (fun z => fun k : ℕ => z.2 (n + k)) :=
      Measurable.of_comap_le le_rfl
    have hc := (measurable_pi_apply 0).comp hf
    exact measurable_const.ite (measurableSet_eq_fun hc measurable_const) measurable_const
  have hind : IndepFun H χ (K a) :=
    indep_of_indep_of_le_right
      (indep_of_indep_of_le_left
        (s1_canonical_future_coins_indep Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a n).symm
        hH.comap_le) hχfuture.comap_le
  have hp : K a {z | z.2 n = b} = ENNReal.ofReal (if b then δ else 1 - δ) := by
    have h := s1_canonical_coin_cylinder Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a
      ({n} : Finset ℕ) (fun _ => b)
    simpa using h
  have hχint : (∫ z, χ z ∂K a) = if b then δ else 1 - δ := by
    have heq : χ = Set.indicator {z : CoupledSample d | z.2 n = b} (fun _ => 1) := by
      funext z
      simp only [χ, Set.indicator, Set.mem_setOf_eq]
    rw [heq, integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one,
      measureReal_def, hp, ENNReal.toReal_ofReal]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact sub_nonneg.mpr hδ₁.le
    · exact hδ₀.le
  change (∫ z, H z * χ z ∂K a) = _
  rw [hind.integral_fun_mul_eq_mul_integral
    (hH.mono (finiteHistorySigma_le Δ n) le_rfl).aestronglyMeasurable
    hχ.aestronglyMeasurable, hχint, mul_comm]


/-- Each conditional path branch of the canonical kernel is a probability kernel. -/
theorem s1_canonical_conditional_kernel_markov (ω : FieldPair d) (b : Bool) :
    IsMarkovKernel (sourceConditionalPathKernel
      ((splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor).comap
        (fun x => (x, ω)) (measurable_id.prodMk measurable_const)) b) := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  let L := K.comap (fun x => (x, ω)) (measurable_id.prodMk measurable_const)
  change IsMarkovKernel (sourceConditionalPathKernel L b)
  constructor
  intro x
  have hp : L x {z | z.2 0 = b} = ENNReal.ofReal (if b then δ else 1 - δ) := by
    have h := s1_canonical_coin_cylinder Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart (x, ω)
      ({0} : Finset ℕ) (fun _ => b)
    simpa [L, Kernel.comap_apply] using h
  have hw : 0 < (if b then δ else 1 - δ) := by
    cases b
    · exact sub_pos.mpr hδ₁
    · exact hδ₀
  haveI : IsProbabilityMeasure (L x) := inferInstance
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond (L x) {z | z.2 0 = b}) :=
    ProbabilityTheory.cond_isProbabilityMeasure (by rw [hp]; exact (ENNReal.ofReal_pos.mpr hw).ne')
  change IsProbabilityMeasure ((ProbabilityTheory.cond (L x) {z | z.2 0 = b}).map Prod.fst)
  infer_instance

/-- Conditional path expectations are measurable and bounded in the starting point. -/
theorem s1_canonical_conditional_expectation (ω : FieldPair d) (b : Bool)
    (F : Path d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F) :
    let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    Measurable (fun x => ∫ γ, F γ ∂conditionalPathLaw (fun y => K (y, ω)) x b) ∧
      BoundedRealTest (fun x => ∫ γ, F γ ∂conditionalPathLaw (fun y => K (y, ω)) x b) := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  let L := K.comap (fun x => (x, ω)) (measurable_id.prodMk measurable_const)
  let C := sourceConditionalPathKernel L b
  haveI : IsMarkovKernel C :=
    s1_canonical_conditional_kernel_markov Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart ω b
  change Measurable (fun x => ∫ γ, F γ ∂C x) ∧
    BoundedRealTest (fun x => ∫ γ, F γ ∂C x)
  refine ⟨hF.stronglyMeasurable.integral_kernel.measurable, ?_⟩
  obtain ⟨D, hD⟩ := hbF
  refine ⟨D, fun x => ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := C x)
    (Filter.Eventually.of_forall fun γ => (show ‖F γ‖ ≤ D by
      simpa only [Real.norm_eq_abs] using hD γ))
  simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using h


/-- Branch restart with the literal conditional path expectation inside the integral. -/
theorem s1_canonical_restart_coin_conditional (a : Vec d × FieldPair d) (n : ℕ) (b : Bool)
    (H : CoupledSample d → ℝ) (F : Path d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H)
    (hbH : BoundedRealTest H) (hF : Measurable F) (hbF : BoundedRealTest F) :
    let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    (∫ z, H z * (if z.2 n = b then 1 else 0) *
      F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂K a) =
    ∫ z, H z * (if z.2 n = b then 1 else 0) * ∫ γ, F γ ∂conditionalPathLaw
      (fun x => K (x, a.2)) (z.1 ((n : ℝ≥0) * Δ)) b ∂K a := by
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  let J : Vec d → ℝ := fun x => ∫ γ, F γ ∂conditionalPathLaw (fun y => K (y, a.2)) x b
  have hJ : Measurable J :=
    (s1_canonical_conditional_expectation Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a.2 b F hF hbF).1
  have hX : @Measurable (CoupledSample d) (Vec d) (finiteHistorySigma Δ n) inferInstance
      (fun z => z.1 ((n : ℝ≥0) * Δ)) := by
    apply measurable_of_finite_history_prefix Δ n _
      ((measurable_pathPosition _).comp measurable_fst)
    intro z z' hp _
    exact hp _ ⟨bot_le, le_rfl⟩
  have hcoin := s1_canonical_coin_test Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a n b
    (fun z => H z * J (z.1 ((n : ℝ≥0) * Δ))) (hH.mul (hJ.comp hX))
  have hr := s1_canonical_restart_coin_branch Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart
    a n b H F hH hbH hF hbF
  change (∫ z, H z * (if z.2 n = b then 1 else 0) *
    F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂K a) = _
  calc
    _ = ∫ z, H z * ((if b then δ else 1 - δ) * J (z.1 ((n : ℝ≥0) * Δ))) ∂K a := hr
    _ = (if b then δ else 1 - δ) * ∫ z, H z * J (z.1 ((n : ℝ≥0) * Δ)) ∂K a := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    _ = ∫ z, (H z * J (z.1 ((n : ℝ≥0) * Δ))) *
        (if z.2 n = b then 1 else 0) ∂K a := hcoin.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      ring


/-- The canonical kernel satisfies the source current-coin restart clause. -/
theorem s1_canonical_current_coin_restart (a : Vec d × FieldPair d) (n : ℕ)
    (H : CoupledSample d → ℝ) (F : Path d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (currentCoinHistory Δ n) inferInstance H)
    (hbH : BoundedRealTest H) (hF : Measurable F) (hbF : BoundedRealTest F) :
    let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    Integrable (fun z => H z * ∫ γ, F γ ∂conditionalPathLaw
      (fun x => K (x, a.2)) (z.1 ((n : ℝ≥0) * Δ)) (z.2 n)) (K a) ∧
    (∫ z, H z * F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂K a) =
      ∫ z, H z * ∫ γ, F γ ∂conditionalPathLaw
        (fun x => K (x, a.2)) (z.1 ((n : ℝ≥0) * Δ)) (z.2 n) ∂K a := by
  classical
  let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
  letI : IsProbabilityMeasure (K a) := inferInstance
  have hbranch (b : Bool) := s1_current_coin_history_branch (P := P) (hstart := hstart)
    Δ n b H hH hbH
  choose G hG hbG hGeq using hbranch
  let J : Bool → Vec d → ℝ := fun b x => ∫ γ, F γ ∂conditionalPathLaw (fun y => K (y, a.2)) x b
  have hJ (b : Bool) : Measurable (J b) ∧ BoundedRealTest (J b) :=
    s1_canonical_conditional_expectation Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a.2 b F hF hbF
  let χ : Bool → CoupledSample d → ℝ := fun b z => if z.2 n = b then 1 else 0
  let u : Bool → CoupledSample d → ℝ := fun b z => G b z * χ b z *
    F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))
  let v : Bool → CoupledSample d → ℝ := fun b z => G b z * χ b z * J b (z.1 ((n : ℝ≥0) * Δ))
  have hχ (b : Bool) : Measurable (χ b) := by
    exact measurable_const.ite (measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd)
      measurable_const) measurable_const
  have hbχ (b : Bool) : BoundedRealTest (χ b) := by
    refine ⟨1, fun z => ?_⟩
    dsimp [χ]
    split_ifs <;> norm_num
  have hpos : Measurable (fun z : CoupledSample d => z.1 ((n : ℝ≥0) * Δ)) :=
    (measurable_pathPosition _).comp measurable_fst
  have hu (b : Bool) : Integrable (u b) (K a) :=
    integrable_oneInterval_bit (K a) Δ n b (G b) F
      ((hG b).mono (finiteHistorySigma_le Δ n) le_rfl) (hbG b) hF hbF
  have hv (b : Bool) : Integrable (v b) (K a) := by
    apply integrable_boundedRealTest (K a)
    · exact (((hG b).mono (finiteHistorySigma_le Δ n) le_rfl).mul (hχ b)).mul
        ((hJ b).1.comp hpos)
    · exact boundedRealTest_mul _ _ (boundedRealTest_mul _ _ (hbG b) (hbχ b))
        (by obtain ⟨C, hC⟩ := (hJ b).2; exact ⟨C, fun z => hC _⟩)
  have heq (b : Bool) : (∫ z, u b z ∂K a) = ∫ z, v b z ∂K a :=
    s1_canonical_restart_coin_conditional Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart
      a n b (G b) F (hG b) (hbG b) hF hbF
  have hu_eq : (fun z => u false z + u true z) =
      (fun z => H z * F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) := by
    funext z
    cases hz : z.2 n <;> simp [u, χ, hz, hGeq _ z hz]
  have hv_eq : (fun z => v false z + v true z) =
      (fun z => H z * ∫ γ, F γ ∂conditionalPathLaw
        (fun x => K (x, a.2)) (z.1 ((n : ℝ≥0) * Δ)) (z.2 n)) := by
    funext z
    cases hz : z.2 n <;> simp [v, χ, hz, hGeq _ z hz, J]
  constructor
  · rw [← hv_eq]
    exact (hv false).add (hv true)
  · rw [← hu_eq, ← hv_eq, integral_add (hu false) (hu true),
      integral_add (hv false) (hv true), heq false, heq true]


/-- The canonical joint kernel has the complete source split coupling on the
GMP path-identification event, under the global source primitives. -/
theorem s1_canonical_source_coupling_ae (hd : 2 ≤ d) {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {lam : ℝ} (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀ h₁ P) :
    ∀ᵐ ω ∂Q.measure,
      IsSourceSplitCoupling (fun x => P (x, ω)) Δ δ R i
        (fun x => splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor (x, ω)) := by
  filter_upwards [s1_canonical_source_first_clauses_ae Δ hΔ δ R i hδ₀ hδ₁ hR
    P hminor hstart hd Q h₀ h₁ hP] with ω hω
  intro x
  obtain ⟨hp, hm, hc⟩ := hω x
  refine ⟨hp, hm, hc, ?_, ?_, ?_, ?_⟩
  · intro n
    exact s1_canonical_future_coins_indep Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart (x, ω) n
  · intro n H F hH hbH hF hbF
    exact s1_canonical_current_coin_restart Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart
      (x, ω) n H F hH hbH hF hbF
  · exact s1_canonical_conditional_successfulSupport Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart (x, ω)
  · exact s1_canonical_conditional_successfulEndpoint Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart (x, ω)

include hΔ hδ₀ hδ₁ hR hminor in
/-- The canonical kernel supplies the complete source fiber and both joint
restart and one-interval conclusions from the explicit global primitives. -/
theorem s1_canonical_joint_assembly (hd : 2 ≤ d) {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {lam : ℝ} (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀ h₁ P) :
    ∃ K : CoupledQuenchedLaws d,
      (∀ᵐ ω ∂Q.measure, IsSourceSplitCoupling (fun x => P (x, ω)) Δ δ R i
        (fun x => K (x, ω))) ∧
      HasDeterministicRestart Q.measure Δ K ∧
      Renewal.HasOneIntervalKernel Q.measure Δ δ R i P K := by
  refine ⟨splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor, ?_, ?_, ?_⟩
  · exact s1_canonical_source_coupling_ae Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart hd Q h₀ h₁ hP
  · exact s1_canonical_hasDeterministicRestart Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart Q.measure
  · exact s1_canonical_hasOneIntervalKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart Q.measure


end EinsteinFull.Regeneration
