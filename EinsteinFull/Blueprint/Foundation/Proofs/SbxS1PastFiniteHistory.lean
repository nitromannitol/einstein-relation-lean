import EinsteinRelation.Regeneration.FirstIntervalHalfSpaceLocality
import EinsteinRelation.Probability.FiniteHistorySplit
import EinsteinRelation.Probability.FiniteHistoryFiltration
import EinsteinRelation.Regeneration.Measurability
import EinsteinRelation.Regeneration.FirstRegenerationSliceFubini
import EinsteinRelation.Regeneration.EndpointGap
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import EinsteinRelation.Localization.CoefficientObservations
import EinsteinRelation.Probability.LocalSigma
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Integral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import EinsteinFull.Work.W1.StoppedKernelLocalitySupport
import Batteries.Tactic.Lint

/-!
Supported finite-history comparison for the actual coupled laws, used in
`paper/main.tex:1499`. These are mathematical consumers, not a reduction of the
past-kernel graph node. Supported diffusion/bridge comparisons still have to
be supplied; spatial measurability and bounds of the scalar families are proved.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinFull.Blueprint.PastFiniteHistory

open EinsteinRelation EinsteinRelation.Regeneration

/-- The literal closed past cutoff, including its right endpoint. -/
def pastBelow {d : ℕ} (Δ : ℝ≥0) (n : ℕ) (i : Fin d) (v : ℝ) :
    Set (CoupledSample d) :=
  {z | ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → z.1 t i ≤ v}

/-- The closed cutoff is an ambient measurable event. -/
theorem measurableSet_pastBelow {d : ℕ} (Δ : ℝ≥0) (n : ℕ) (i : Fin d) (v : ℝ) :
    MeasurableSet (pastBelow Δ n i v) := by
  have hc : IsClosed (pastBelow Δ n i v) := by
    change IsClosed {z : CoupledSample d | ∀ t : ℝ≥0,
      t ≤ (n : ℝ≥0) * Δ → z.1 t i ≤ v}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_le ((continuous_apply i).comp
        ((continuous_eval_const t).comp continuous_fst)) continuous_const
  exact hc.measurableSet

/-- The cutoff depends only on the retained path coordinates. -/
theorem measurableSet_pastBelow_history {d : ℕ}
    (Δ : ℝ≥0) (n : ℕ) (i : Fin d) (v : ℝ) :
    MeasurableSet[finiteHistorySigma Δ n] (pastBelow Δ n i v) := by
  classical
  let f : CoupledSample d → ℝ := (pastBelow Δ n i v).indicator (fun _ => 1)
  have hm : Measurable f := measurable_const.indicator (measurableSet_pastBelow Δ n i v)
  have hh := Probability.measurable_of_finite_history_prefix Δ n f hm ?_
  · have heq : pastBelow Δ n i v = f ⁻¹' {1} := by
      ext z
      by_cases hz : z ∈ pastBelow Δ n i v <;> simp [f, hz]
    rw [heq]
    exact hh (measurableSet_singleton 1)
  · intro z z' hp _
    have heq : z ∈ pastBelow Δ n i v ↔ z' ∈ pastBelow Δ n i v := by
      constructor
      · intro hz t ht
        rw [← hp t ⟨zero_le, ht⟩]
        exact hz t ht
      · intro hz t ht
        rw [hp t ⟨zero_le, ht⟩]
        exact hz t ht
    by_cases hz : z ∈ pastBelow Δ n i v
    · simp only [f, Set.indicator_of_mem hz, Set.indicator_of_mem (heq.mp hz)]
    · simp only [f, Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (fun hz' => hz (heq.mpr hz'))]

private theorem bounded_mul {α : Type*} {f g : α → ℝ}
    (hf : BoundedRealTest f) (hg : BoundedRealTest g) :
    BoundedRealTest (fun x => f x * g x) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C * D, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))

private theorem bounded_sub {α : Type*} {f g : α → ℝ}
    (hf : BoundedRealTest f) (hg : BoundedRealTest g) :
    BoundedRealTest (fun x => f x - g x) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun x => (abs_sub _ _).trans (add_le_add (hC x) (hD x))⟩

/-- The literal RN bridge has mass at most one, including when the target
conditional endpoint measure has zero mass. -/
theorem killedBridgeMixture_mass_le_one {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (y : Vec d) (ω : FieldPair d) :
    Renewal.killedBridgeMixture Δ R i P y ω Set.univ ≤ 1 := by
  calc
    Renewal.killedBridgeMixture Δ R i P y ω Set.univ =
        ((Renewal.killedBridgeMixture Δ R i P y ω).map
          (fun γ : Path d => γ Δ)) Set.univ := by
      rw [Measure.map_apply (continuous_eval_const Δ).measurable MeasurableSet.univ]
      rfl
    _ ≤ ProbabilityTheory.cond (volume : Measure (Vec d))
        (endpointBall i R y) Set.univ :=
      (Measure.le_iff.mp (map_killedBridgeMixture_endpoint_le_uniform Δ R i P y ω))
        Set.univ MeasurableSet.univ
    _ ≤ 1 := prob_le_one

/-- A bounded path test gives a uniformly bounded scalar for the exact bridge.
No minorization or extra bridge-normalization premise is needed. -/
theorem bounded_killedBridgeMixture_integral {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (ω : FieldPair d) (F : Path d → ℝ) (hF : BoundedRealTest F) :
    BoundedRealTest (fun y : Vec d =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω) := by
  obtain ⟨C, hC⟩ := hF
  have hC0 : 0 ≤ C := (abs_nonneg (F 0)).trans (hC 0)
  refine ⟨C, fun y => ?_⟩
  let μ := Renewal.killedBridgeMixture Δ R i P y ω
  have hm : μ Set.univ ≤ 1 := killedBridgeMixture_mass_le_one Δ R i P y ω
  let : IsFiniteMeasure μ := ⟨hm.trans_lt (by simp)⟩
  have hmreal : μ.real Set.univ ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa only [ENNReal.ofReal_one] using hm)
  calc
    |∫ γ, F γ ∂μ| = ‖∫ γ, F γ ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ C * μ.real Set.univ := norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun γ => by simpa only [Real.norm_eq_abs] using hC γ)
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hmreal hC0
    _ = C := mul_one C

private theorem bounded_integral_probability_family {α β : Type*}
    [MeasurableSpace β] (μ : α → Measure β)
    (hμ : ∀ a, IsProbabilityMeasure (μ a)) (F : β → ℝ)
    (hF : BoundedRealTest F) : BoundedRealTest (fun a => ∫ z, F z ∂μ a) := by
  obtain ⟨C, hC⟩ := hF
  refine ⟨C, fun a => ?_⟩
  let := hμ a
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ a) (f := F) (C := C)
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z))

/-- The literal bridge scalars are spatially measurable on a fixed environment
whose diffusion fibres are probabilities. A jointly measurable kernel RN
derivative agrees fibrewise almost everywhere with the measure RN derivative
in the source definition. -/
theorem measurable_killedBridgeMixture_integral {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (ω : FieldPair d) (hP : ∀ y : Vec d, IsProbabilityMeasure (P (y, ω)))
    (F : Path d → ℝ) (hF : Measurable F) :
    Measurable (fun y : Vec d =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω) := by
  classical
  let Pω : ProbabilityTheory.Kernel (Vec d) (Path d) :=
    P.comap (fun y => (y, ω)) (measurable_id.prodMk measurable_const)
  let : ProbabilityTheory.IsMarkovKernel Pω := ⟨hP⟩
  let S : Set (Vec d × Path d) :=
    {p | ∀ t : ℝ≥0, t ≤ Δ → p.2 t ∈ couplingRegion i R p.1}
  have hS : MeasurableSet S := by
    have hstay := (ContinuousMap.isOpen_setOfPred_mapsTo (X := ℝ≥0) (Y := Vec d)
      (K := Set.Icc (0 : ℝ≥0) Δ) isCompact_Icc (isOpen_couplingRegion i R 0)).measurableSet
    convert hstay.preimage Probability.continuous_path_recenter.measurable using 1
    ext p
    simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, Set.MapsTo, Set.mem_Icc,
      zero_le, true_and, couplingRegion, ContinuousMap.coe_mk, zero_add,
      sub_add_eq_sub_sub]
  let κ : ProbabilityTheory.Kernel (Vec d) (Path d) :=
    ⟨fun y => Renewal.killedSegmentLaw Δ R i P y ω,
      Measure.measurable_of_measurable_coe _ fun s hs => by
        have hm := Pω.measurable_kernel_prodMk_left (hS.inter (measurable_snd hs))
        simpa [Pω, ProbabilityTheory.Kernel.comap_apply, S,
          Renewal.killedSegmentLaw, Measure.restrict_apply hs, Set.inter_comm,
          Set.preimage_preimage, Function.comp_def] using hm⟩
  let : ProbabilityTheory.IsFiniteKernel κ := ⟨1, by simp, fun y => by
    let := hP y
    exact (Measure.restrict_apply_le _ _).trans prob_le_one⟩
  have hball := measurableSet_endpointBall_pair (d := d) i R
  let V : ProbabilityTheory.Kernel (Vec d) (Vec d) :=
    ProbabilityTheory.Kernel.const (Vec d) volume
  let η : ProbabilityTheory.Kernel (Vec d) (Vec d) :=
    ⟨fun y => ProbabilityTheory.cond volume (endpointBall i R y),
      Measure.measurable_of_measurable_coe _ fun s hs => by
        have hmass := V.measurable_kernel_prodMk_left hball
        have hsect := V.measurable_kernel_prodMk_left (hball.inter (measurable_snd hs))
        simpa [V, ProbabilityTheory.Kernel.const_apply,
          ProbabilityTheory.cond_apply' hs, Set.preimage_preimage,
          Function.comp_def] using hmass.fun_inv.fun_mul hsect⟩
  let : ProbabilityTheory.IsFiniteKernel η := ⟨1, by simp, fun y => by
    change ProbabilityTheory.cond (volume : Measure (Vec d))
      (endpointBall i R y) Set.univ ≤ 1
    exact prob_le_one⟩
  let e : Path d → Vec d := fun γ => γ Δ
  have he : Measurable e := (continuous_eval_const Δ).measurable
  let κe := κ.map e
  let w : Vec d → Path d → ℝ≥0∞ := fun y γ =>
    ProbabilityTheory.Kernel.rnDeriv η κe y (e γ)
  have hw : Measurable (Function.uncurry w) :=
    (ProbabilityTheory.Kernel.measurable_rnDeriv η κe).comp
      (measurable_fst.prodMk (he.comp measurable_snd))
  let B := κ.withDensity w
  have hB : ∀ y, B y = Renewal.killedBridgeMixture Δ R i P y ω := by
    intro y
    rw [ProbabilityTheory.Kernel.withDensity_apply κ hw y]
    apply withDensity_congr_ae
    have hrn : ProbabilityTheory.Kernel.rnDeriv η κe y =ᵐ[(κ y).map e]
        (η y).rnDeriv ((κ y).map e) := by
      simpa only [κe, ProbabilityTheory.Kernel.map_apply _ he] using
        (ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure (κ := η) (η := κe) (a := y))
    exact ae_of_ae_map he.aemeasurable hrn
  have hm := (hF.stronglyMeasurable.integral_kernel (κ := B)).measurable
  convert hm using 1
  funext y
  rw [hB y]

/-- Empty histories of probability fibres with the same actual start agree.
No positive-time or off-origin restart property is needed. -/
theorem integral_zero_history_eq_of_starts {d : ℕ} (Δ : ℝ≥0)
    (μ ν : Measure (CoupledSample d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : Vec d) (hμ : ∀ᵐ z ∂μ, z.1 0 = x) (hν : ∀ᵐ z ∂ν, z.1 0 = x)
    (F : CoupledSample d → ℝ)
    (hF : Measurable[finiteHistorySigma Δ 0] F) :
    (∫ z, F z ∂μ) = ∫ z, F z ∂ν := by
  let z₀ : CoupledSample d := (⟨fun _ => x, continuous_const⟩, fun _ => false)
  have hpoint : ∀ z : CoupledSample d, z.1 0 = x → F z = F z₀ := by
    intro z hz
    have hs : Probability.stoppedHistorySample Δ 0 z = z₀ := by
      apply Prod.ext
      · apply ContinuousMap.ext
        intro t
        simpa only [Probability.stoppedHistorySample, Nat.cast_zero, zero_mul,
          min_zero, z₀, ContinuousMap.coe_mk] using hz
      · funext k
        simp only [Probability.stoppedHistorySample, Nat.not_lt_zero, ↓reduceIte, z₀]
    rw [← Probability.finiteHistory_test_stopped Δ 0 F hF z, hs]
  exact (integral_eq_const (hμ.mono hpoint)).trans
    (integral_eq_const (hν.mono hpoint)).symm

/-- One supported induction step on the original two fibres. The coefficients
are the literal unrestricted and RN-reweighted bridge integrals. Both bit
identities have their genuine integrability supplied by `OneIntervalKernelAt`.
Only the first fibre's coefficient measurability and bounds are needed: the
supported comparison identifies the second fibre on the support of the past.
This is a conditional mathematical consumer, not an extra graph premise. -/
theorem integral_next_bit_eq_of_supported_scalar_comparison {d : ℕ}
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (P P' : QuenchedPathLaws d)
    (K K' : CoupledQuenchedLaws d) (xω xω' : Vec d × FieldPair d)
    (hone : Renewal.OneIntervalKernelAt Δ δ R i P K xω)
    (hone' : Renewal.OneIntervalKernelAt Δ δ R i P' K' xω')
    (n : ℕ) (S : Set (CoupledSample d))
    (hIH : ∀ H : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ n] H →
      BoundedRealTest H → (∀ z, z ∉ S → H z = 0) →
      (∫ z, H z ∂K xω) = ∫ z, H z ∂K' xω')
    (H : CoupledSample d → ℝ) (F : Path d → ℝ)
    (hH : Measurable[finiteHistorySigma Δ n] H) (hHb : BoundedRealTest H)
    (hHs : ∀ z, z ∉ S → H z = 0)
    (hF : Measurable F) (hFb : BoundedRealTest F)
    (hpre : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ')
    (hPm : Measurable[finiteHistorySigma Δ n] (fun z : CoupledSample d =>
      ∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), xω.2)))
    (hPb : BoundedRealTest (fun z : CoupledSample d =>
      ∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), xω.2)))
    (hBm : Measurable[finiteHistorySigma Δ n] (fun z : CoupledSample d =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (z.1 ((n : ℝ≥0) * Δ)) xω.2))
    (hBb : BoundedRealTest (fun z : CoupledSample d =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (z.1 ((n : ℝ≥0) * Δ)) xω.2))
    (heq : ∀ z ∈ S,
      (∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), xω.2)) =
        (∫ γ, F γ ∂P' (z.1 ((n : ℝ≥0) * Δ), xω'.2)) ∧
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (z.1 ((n : ℝ≥0) * Δ)) xω.2) =
        ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P' (z.1 ((n : ℝ≥0) * Δ)) xω'.2) :
    ∀ b : Bool,
      (∫ z, H z * (if z.2 n = b then (1 : ℝ) else 0) *
        F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂K xω) =
      ∫ z, H z * (if z.2 n = b then (1 : ℝ) else 0) *
        F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂K' xω' := by
  classical
  have hk := hone n H F hH hHb hF hFb hpre
  have hk' := hone' n H F hH hHb hF hFb hpre
  have hweight : ∀ (c c' : CoupledSample d → ℝ),
      Measurable[finiteHistorySigma Δ n] c → BoundedRealTest c →
      (∀ z ∈ S, c z = c' z) →
      (∫ z, H z * c z ∂K xω) = ∫ z, H z * c' z ∂K' xω' := by
    intro c c' hcm hcb hc
    calc
      _ = ∫ z, H z * c z ∂K' xω' := hIH _ (hH.mul hcm) (bounded_mul hHb hcb)
        (fun z hz => by rw [hHs z hz, zero_mul])
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun z => by
        change H z * c z = H z * c' z
        by_cases hz : z ∈ S
        · rw [hc z hz]
        · rw [hHs z hz, zero_mul, zero_mul])
  have hb := hweight _
    (fun z => ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P'
      (z.1 ((n : ℝ≥0) * Δ)) xω'.2) hBm hBb (fun z hz => (heq z hz).2)
  have hp := hweight
    (fun z => (∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), xω.2)) -
      δ * ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
        (z.1 ((n : ℝ≥0) * Δ)) xω.2)
    (fun z => (∫ γ, F γ ∂P' (z.1 ((n : ℝ≥0) * Δ), xω'.2)) -
      δ * ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P'
        (z.1 ((n : ℝ≥0) * Δ)) xω'.2)
    (hPm.sub (hBm.const_mul δ))
    (bounded_sub hPb (bounded_mul ⟨|δ|, fun _ => le_rfl⟩ hBb))
    (fun z hz => by rw [(heq z hz).1, (heq z hz).2])
  intro b
  cases b
  · have hf := hk.2.2.2.2.2.2.trans (hp.trans hk'.2.2.2.2.2.2.symm)
    have hbit : ∀ a : Bool, (if a = false then (1 : ℝ) else 0) =
        (if a = true then (0 : ℝ) else 1) := by
      intro a
      cases a <;> simp
    simpa only [hbit] using hf
  · exact hk.2.2.1.trans ((congrArg (δ * ·) hb).trans hk'.2.2.1.symm)

/-- The next closed window is the union of the old window and the shifted
closed one-interval window; the shared endpoint is retained on both sides. -/
theorem pastBelow_succ_iff {d : ℕ} (Δ : ℝ≥0) (n : ℕ) (i : Fin d) (v : ℝ)
    (z : CoupledSample d) :
    z ∈ pastBelow Δ (n + 1) i v ↔ z ∈ pastBelow Δ n i v ∧
      sampleTimeShift Δ z ((n : ℝ≥0) * Δ) ∈ pastBelow Δ 1 i v := by
  have htime : ((n + 1 : ℕ) : ℝ≥0) * Δ = (n : ℝ≥0) * Δ + Δ := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  constructor
  · intro h
    constructor
    · intro t ht
      exact h t (ht.trans (by rw [htime]; exact le_add_of_nonneg_right zero_le))
    · intro t ht
      change z.1 ((n : ℝ≥0) * Δ + t) i ≤ v
      apply h
      rw [htime]
      exact add_le_add le_rfl (by simpa only [Nat.cast_one, one_mul] using ht)
  · rintro ⟨hp, hf⟩ t ht
    by_cases htn : t ≤ (n : ℝ≥0) * Δ
    · exact hp t htn
    · have hnt : (n : ℝ≥0) * Δ ≤ t := le_of_not_ge htn
      have hrem : t - (n : ℝ≥0) * Δ ≤ (1 : ℝ≥0) * Δ := by
        rw [one_mul, tsub_le_iff_right, add_comm]
        simpa only [htime] using ht
      have h := hf (t - (n : ℝ≥0) * Δ) (by simpa only [Nat.cast_one] using hrem)
      change z.1 ((n : ℝ≥0) * Δ + (t - (n : ℝ≥0) * Δ)) i ≤ v at h
      rwa [add_tsub_cancel_of_le hnt] at h

/-- Rectangle comparison extends to every supported next-history test.
This finite-measure argument includes total mass, rather than assuming the
restricted histories are probability measures. -/
theorem integral_supported_history_succ_eq_of_rectangles {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ) (i : Fin d) (v : ℝ)
    (μ ν : Measure (CoupledSample d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hrect : ∀ H G : CoupledSample d → ℝ,
      Measurable[finiteHistorySigma Δ n] H → BoundedRealTest H →
      (∀ z, z ∉ pastBelow Δ n i v → H z = 0) →
      Measurable[finiteHistorySigma Δ 1] G → BoundedRealTest G →
      (∀ z, z ∉ pastBelow Δ 1 i v → G z = 0) →
      (∫ z, H z * G (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂μ) =
        ∫ z, H z * G (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂ν)
    (F : CoupledSample d → ℝ)
    (hF : Measurable[finiteHistorySigma Δ (n + 1)] F) (hb : BoundedRealTest F)
    (hs : ∀ z, z ∉ pastBelow Δ (n + 1) i v → F z = 0) :
    (∫ z, F z ∂μ) = ∫ z, F z ∂ν := by
  classical
  let S := pastBelow (d := d) Δ (n + 1) i v
  let split := Probability.splitHistory (d := d) Δ n
  have hS : MeasurableSet S := measurableSet_pastBelow Δ (n + 1) i v
  have hstop : ∀ m : ℕ, Measurable (Probability.stoppedHistorySample (d := d) Δ m) :=
    fun m => (Probability.measurable_stoppedHistorySample Δ m).mono
      (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hshift : Measurable (fun z : CoupledSample d =>
      sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) :=
    (measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_id)
  have hsplit : Measurable split := (hstop n).prodMk ((hstop 1).comp hshift)
  have hmap : (μ.restrict S).map split = (ν.restrict S).map split := by
    apply Measure.ext_prod
    intro s t hsm htm
    let H : CoupledSample d → ℝ := (pastBelow Δ n i v).indicator
      (fun z => s.indicator (fun _ => 1) (Probability.stoppedHistorySample Δ n z))
    let G : CoupledSample d → ℝ := (pastBelow Δ 1 i v).indicator
      (fun z => t.indicator (fun _ => 1) (Probability.stoppedHistorySample Δ 1 z))
    have hHm : Measurable[finiteHistorySigma Δ n] H :=
      ((measurable_const.indicator hsm).comp
        (Probability.measurable_stoppedHistorySample Δ n)).indicator
          (measurableSet_pastBelow_history Δ n i v)
    have hGm : Measurable[finiteHistorySigma Δ 1] G :=
      ((measurable_const.indicator htm).comp
        (Probability.measurable_stoppedHistorySample Δ 1)).indicator
          (measurableSet_pastBelow_history Δ 1 i v)
    have hHb : BoundedRealTest H := by
      refine ⟨1, fun z => ?_⟩
      by_cases h : z ∈ pastBelow Δ n i v <;>
        by_cases hh : Probability.stoppedHistorySample Δ n z ∈ s <;> simp [H, h, hh]
    have hGb : BoundedRealTest G := by
      refine ⟨1, fun z => ?_⟩
      by_cases h : z ∈ pastBelow Δ 1 i v <;>
        by_cases hh : Probability.stoppedHistorySample Δ 1 z ∈ t <;> simp [G, h, hh]
    have heq := hrect H G hHm hHb
      (fun z hz => Set.indicator_of_notMem hz _) hGm hGb
      (fun z hz => Set.indicator_of_notMem hz _)
    let J : CoupledSample d × CoupledSample d → ℝ := (s ×ˢ t).indicator (fun _ => 1)
    have hJ : Measurable J := measurable_const.indicator (hsm.prod htm)
    have hpoint : ∀ z, S.indicator (fun z => J (split z)) z =
        H z * G (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) := by
      intro z
      have hcut := pastBelow_succ_iff Δ n i v z
      by_cases hp : z ∈ pastBelow Δ n i v <;>
        by_cases hf : sampleTimeShift Δ z ((n : ℝ≥0) * Δ) ∈ pastBelow Δ 1 i v <;>
        by_cases hs' : Probability.stoppedHistorySample Δ n z ∈ s <;>
        by_cases ht' : Probability.stoppedHistorySample Δ 1
          (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∈ t <;>
        simp [S, hcut, hp, hf, H, G, J, split, Probability.splitHistory,
          Set.indicator_apply, Set.mem_prod, hs', ht']
    have hint : ∀ ρ : Measure (CoupledSample d),
        (∫ q, J q ∂(ρ.restrict S).map split) =
          ∫ z, H z * G (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂ρ := by
      intro ρ
      rw [integral_map hsplit.aemeasurable hJ.aestronglyMeasurable,
        ← integral_indicator hS]
      exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    have hreal : ((μ.restrict S).map split).real (s ×ˢ t) =
        ((ν.restrict S).map split).real (s ×ˢ t) := by
      have hj := (hint μ).trans (heq.trans (hint ν).symm)
      simpa only [J, integral_indicator (hsm.prod htm), setIntegral_one_eq_measureReal]
        using hj
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ((μ.restrict S).map split) _)
      (measure_ne_top ((ν.restrict S).map split) _)).mp hreal
  obtain ⟨G, hG, _, hfactor⟩ := Probability.exists_bounded_splitHistory_factor Δ hΔ n F hF hb
  have htransport : ∀ ρ : Measure (CoupledSample d),
      (∫ z, F z ∂ρ) = ∫ q, G q ∂(ρ.restrict S).map split := by
    intro ρ
    rw [integral_map hsplit.aemeasurable hG.aestronglyMeasurable,
      ← integral_indicator hS]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz]
        exact hfactor z
      · rw [Set.indicator_of_notMem hz]
        exact hs z hz
  rw [htransport μ, htransport ν, hmap]

private theorem integrable_of_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (F : α → ℝ)
    (hF : Measurable F) (hb : BoundedRealTest F) : Integrable F μ := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hF.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- The two actual coin branches determine a weighted first-history test
at any deterministic interval. The original fibres alone are used. -/
theorem integral_weighted_history_eq_of_bit_tests {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ) (i : Fin d) (v : ℝ)
    (μ ν : Measure (CoupledSample d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : CoupledSample d → ℝ) (hH : Measurable H) (hHb : BoundedRealTest H)
    (hbit : ∀ F : Path d → ℝ, Measurable F → BoundedRealTest F →
      (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') →
      (∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) → ∀ b : Bool,
      (∫ z, H z * (if z.2 n = b then (1 : ℝ) else 0) *
        F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂μ) =
      ∫ z, H z * (if z.2 n = b then (1 : ℝ) else 0) *
        F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂ν)
    (G : CoupledSample d → ℝ) (hG : Measurable[finiteHistorySigma Δ 1] G)
    (hGb : BoundedRealTest G) (hGs : ∀ z, z ∉ pastBelow Δ 1 i v → G z = 0) :
    (∫ z, H z * G (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂μ) =
      ∫ z, H z * G (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂ν := by
  classical
  let Fb := fun b γ => G (firstBitSample (Diffusion.stopPathAt Δ γ) b)
  have hFm : ∀ b, Measurable (Fb b) := fun b =>
    (hG.mono (Probability.finiteHistorySigma_le Δ 1) le_rfl).comp
      ((measurable_id.prodMk measurable_const).comp
        (Diffusion.continuous_stopPathAt Δ).measurable)
  have hFb : ∀ b, BoundedRealTest (Fb b) := by
    obtain ⟨C, hC⟩ := hGb
    exact fun b => ⟨C, fun γ => hC _⟩
  have hFp : ∀ b γ γ', (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → Fb b γ = Fb b γ' := by
    intro b γ γ' hh
    have hs : Diffusion.stopPathAt Δ γ = Diffusion.stopPathAt Δ γ' := by
      apply ContinuousMap.ext
      intro t
      exact hh _ (min_le_right _ _)
    exact congrArg (fun γ => G (firstBitSample γ b)) hs
  have hFs : ∀ b γ, Fb b γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v := by
    intro b γ hn t ht
    have hmem : firstBitSample (Diffusion.stopPathAt Δ γ) b ∈ pastBelow Δ 1 i v := by
      by_contra hh
      exact hn (hGs _ hh)
    have h := hmem t (by simpa only [Nat.cast_one, one_mul] using ht)
    change γ (min t Δ) i ≤ v at h
    rwa [min_eq_left ht] at h
  have hvalue : ∀ z : CoupledSample d,
      G (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) =
        Fb (z.2 n) (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) := by
    intro z
    have hs : Probability.stoppedHistorySample Δ 1
        (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) =
        firstBitSample (Diffusion.stopPathAt Δ
          (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) (z.2 n) := by
      apply Prod.ext
      · apply ContinuousMap.ext
        intro t
        simp only [Probability.stoppedHistorySample, firstBitSample, sampleTimeShift,
          Nat.cast_one, one_mul, Diffusion.stopPathAt, ContinuousMap.coe_mk]
      · funext k
        by_cases hk : k = 0
        · subst k
          simp only [Probability.stoppedHistorySample, firstBitSample, sampleTimeShift,
            gridIndex_mul Δ hΔ n, Nat.zero_lt_one, ite_eq_left, Nat.add_zero]
        · have hk' : ¬ k < 1 := by omega
          simp only [Probability.stoppedHistorySample, firstBitSample, hk, hk', ite_false]
    have h := Probability.finiteHistory_test_stopped Δ 1 G hG
      (sampleTimeShift Δ z ((n : ℝ≥0) * Δ))
    rw [hs] at h
    exact h.symm
  let B := fun b (z : CoupledSample d) => H z * (if z.2 n = b then (1 : ℝ) else 0) *
    Fb b (pathTimeShift z.1 ((n : ℝ≥0) * Δ))
  have hBm : ∀ b, Measurable (B b) := by
    intro b
    have hcoin : Measurable (fun z : CoupledSample d => z.2 n) :=
      (measurable_pi_apply (X := fun _ : ℕ => Bool) n).comp measurable_snd
    have hshift : Measurable (fun z : CoupledSample d =>
        pathTimeShift z.1 ((n : ℝ≥0) * Δ)) := ((measurable_sampleTimeShift Δ).comp
      (measurable_const.prodMk measurable_id)).fst
    exact (hH.mul (Measurable.ite (measurableSet_eq_fun hcoin measurable_const)
      measurable_const measurable_const)).mul ((hFm b).comp hshift)
  have hBb : ∀ b, BoundedRealTest (B b) := by
    intro b
    apply bounded_mul (bounded_mul hHb ?_)
    · obtain ⟨C, hC⟩ := hFb b
      exact ⟨C, fun z => hC _⟩
    · exact ⟨1, fun z => by by_cases hz : z.2 n = b <;> simp [hz]⟩
  have hsplit : ∀ z, H z * G (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) =
      B true z + B false z := by
    intro z
    rw [hvalue z]
    cases hz : z.2 n <;> simp [B, hz]
  have hint : ∀ ρ : Measure (CoupledSample d), IsProbabilityMeasure ρ →
      (∫ z, H z * G (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂ρ) =
        (∫ z, B true z ∂ρ) + ∫ z, B false z ∂ρ := by
    intro ρ hρ
    let := hρ
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
      integral_add (integrable_of_bounded ρ _ (hBm true) (hBb true))
        (integrable_of_bounded ρ _ (hBm false) (hBb false))]
  rw [hint μ inferInstance, hint ν inferInstance]
  exact congrArg₂ (· + ·)
    (hbit (Fb true) (hFm true) (hFb true) (hFp true) (hFs true) true)
    (hbit (Fb false) (hFm false) (hFb false) (hFp false) (hFs false) false)

/-- Finite-history induction from supported two-coin steps. This is an
independent measure-theoretic consumer: its step hypothesis can be instantiated
by `integral_next_bit_eq_of_supported_scalar_comparison` once the actual scalar
measurability, bounds, and supported diffusion/bridge comparisons are proved. -/
theorem integral_supported_finite_history_eq_of_bit_steps {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (i : Fin d) (v : ℝ)
    (μ ν : Measure (CoupledSample d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : Vec d) (hμ : ∀ᵐ z ∂μ, z.1 0 = x) (hν : ∀ᵐ z ∂ν, z.1 0 = x)
    (hstep : ∀ n : ℕ,
      (∀ H : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ n] H →
        BoundedRealTest H → (∀ z, z ∉ pastBelow Δ n i v → H z = 0) →
        (∫ z, H z ∂μ) = ∫ z, H z ∂ν) →
      ∀ (H : CoupledSample d → ℝ) (F : Path d → ℝ),
      Measurable[finiteHistorySigma Δ n] H → BoundedRealTest H →
      (∀ z, z ∉ pastBelow Δ n i v → H z = 0) →
      Measurable F → BoundedRealTest F →
      (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') →
      (∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) → ∀ b : Bool,
      (∫ z, H z * (if z.2 n = b then (1 : ℝ) else 0) *
        F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂μ) =
      ∫ z, H z * (if z.2 n = b then (1 : ℝ) else 0) *
        F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂ν) :
    ∀ n : ℕ, ∀ F : CoupledSample d → ℝ,
      Measurable[finiteHistorySigma Δ n] F → BoundedRealTest F →
      (∀ z, z ∉ pastBelow Δ n i v → F z = 0) →
      (∫ z, F z ∂μ) = ∫ z, F z ∂ν := by
  intro n
  induction n with
  | zero =>
      intro F hF _ _
      exact integral_zero_history_eq_of_starts Δ μ ν x hμ hν F hF
  | succ n ih =>
      apply integral_supported_history_succ_eq_of_rectangles Δ hΔ n i v μ ν
      intro H G hH hHb hHs hG hGb hGs
      apply integral_weighted_history_eq_of_bit_tests Δ hΔ n i v μ ν H
        (hH.mono (Probability.finiteHistorySigma_le Δ n) le_rfl) hHb
        (fun F hF hFb hpre hFs => hstep n ih H F hH hHb hHs hF hFb hpre hFs)
        G hG hGb hGs

/-- Supported finite-history comparison assembled directly from the literal
one-interval identities and the supported diffusion/bridge scalar comparisons.
All induction steps take place at the two original probability fibres. The
supported scalar comparisons remain analytic obligations; this helper asserts
neither half-space locality nor the graph-node reduction. -/
theorem integral_supported_finite_history_eq_of_scalar_comparison {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (P P' : QuenchedPathLaws d) (K K' : CoupledQuenchedLaws d)
    (x : Vec d) (ω ω' : FieldPair d)
    [IsProbabilityMeasure (K (x, ω))] [IsProbabilityMeasure (K' (x, ω'))]
    (hstart : ∀ᵐ z ∂K (x, ω), z.1 0 = x)
    (hstart' : ∀ᵐ z ∂K' (x, ω'), z.1 0 = x)
    (hone : Renewal.OneIntervalKernelAt Δ δ R i P K (x, ω))
    (hone' : Renewal.OneIntervalKernelAt Δ δ R i P' K' (x, ω'))
    (v : ℝ) (hPprob : ∀ y : Vec d, IsProbabilityMeasure (P (y, ω)))
    (hcompare : ∀ F : Path d → ℝ, Measurable F → BoundedRealTest F →
      (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') →
      (∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) →
      ∀ y : Vec d, y i ≤ v →
      (∫ γ, F γ ∂P (y, ω)) = (∫ γ, F γ ∂P' (y, ω')) ∧
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω) =
        ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P' y ω') :
    ∀ n : ℕ, ∀ F : CoupledSample d → ℝ,
      Measurable[finiteHistorySigma Δ n] F → BoundedRealTest F →
      (∀ z, z ∉ pastBelow Δ n i v → F z = 0) →
      (∫ z, F z ∂K (x, ω)) = ∫ z, F z ∂K' (x, ω') := by
  apply integral_supported_finite_history_eq_of_bit_steps Δ hΔ i v
    (K (x, ω)) (K' (x, ω')) x hstart hstart'
  intro n hIH H F hH hHb hHs hF hFb hpre hFs
  have hPm : Measurable (fun y : Vec d => ∫ γ, F γ ∂P (y, ω)) :=
    (hF.stronglyMeasurable.integral_kernel (κ := P)).measurable.comp
      (measurable_id.prodMk measurable_const)
  have hPb := bounded_integral_probability_family (fun y => P (y, ω)) hPprob F hFb
  have hBm := measurable_killedBridgeMixture_integral Δ R i P ω hPprob F hF
  have hBb := bounded_killedBridgeMixture_integral Δ R i P ω F hFb
  have heval : Measurable[finiteHistorySigma Δ n]
      (fun z : CoupledSample d => z.1 ((n : ℝ≥0) * Δ)) := by
    apply Measurable.of_comap_le
    unfold finiteHistorySigma
    exact le_sup_of_le_left (le_iSup_of_le
      (⟨(n : ℝ≥0) * Δ, zero_le, le_rfl⟩ : Set.Icc 0 ((n : ℝ≥0) * Δ)) le_rfl)
  have hPb' : BoundedRealTest (fun z : CoupledSample d =>
      ∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), ω)) := by
    obtain ⟨C, hC⟩ := hPb
    exact ⟨C, fun z => hC _⟩
  have hBb' : BoundedRealTest (fun z : CoupledSample d =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (z.1 ((n : ℝ≥0) * Δ)) ω) := by
    obtain ⟨C, hC⟩ := hBb
    exact ⟨C, fun z => hC _⟩
  exact integral_next_bit_eq_of_supported_scalar_comparison Δ δ R i P P' K K'
    (x, ω) (x, ω') hone hone' n (pastBelow Δ n i v) hIH H F hH hHb hHs hF hFb hpre
    (hPm.comp heval) hPb' (hBm.comp heval) hBb'
    (fun z hz => hcompare F hF hFb hpre hFs _ (hz _ le_rfl))

/-- The actual GMP coupling supplies the probability fibres, common origin
start, spatial diffusion probabilities and both-coin interval identities used
by the induction. No off-origin coupled-fibre restart is required. -/
theorem ae_origin_data_of_gmpCoupling {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0 h1 P K) :
    ∀ᵐ ω ∂Q.measure,
      IsProbabilityMeasure (K (0, ω)) ∧
      (∀ᵐ z ∂K (0, ω), z.1 0 = 0) ∧
      (∀ y : Vec d, IsProbabilityMeasure (P (y, ω))) ∧
      Renewal.OneIntervalKernelAt (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) P K (0, ω) := by
  filter_upwards [hK.1.1, hK.2.1.1, hK.2.2.1, hK.2.2.2.2.2.2.2.1]
    with ω hp hm hω hone
  obtain ⟨_, r, hr⟩ := hω
  refine ⟨hp, ?_, ?_, hone⟩
  · have hs : ∀ᵐ γ ∂P (0, ω), γ 0 = 0 := by
      rw [hr 0]
      exact r.pathLaw_starts_at 0
    rw [← hm] at hs
    exact ae_of_ae_map measurable_fst.aemeasurable hs
  · intro y
    rw [hr y]
    exact r.pathLaw_isMarkovKernel.isProbabilityMeasure y

/-- The empty-history expectation is constant in the environment, directly
from the actual GMP origin law. No scalar locality input is needed. -/
theorem exists_local_zero_history_integral_version_of_gmpCoupling {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0 h1 P K)
    (Δ : ℝ≥0) (U : Set (Vec d)) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma Δ 0] H) :
    ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧
      (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q.measure] A := by
  let z₀ : CoupledSample d := (⟨fun _ => 0, continuous_const⟩, fun _ => false)
  refine ⟨fun _ => H z₀, measurable_const, ?_⟩
  filter_upwards [ae_origin_data_of_gmpCoupling hd hΛ₀ Q lam l δ h0 h1 P K hK]
    with ω hω
  let : IsProbabilityMeasure (K (0, ω)) := hω.1
  have hz₀ : ∀ᵐ z ∂Measure.dirac z₀, z.1 0 = (0 : Vec d) := by
    rw [ae_dirac_eq]
    exact Filter.eventually_pure.mpr rfl
  exact (integral_zero_history_eq_of_starts Δ (K (0, ω)) (Measure.dirac z₀)
    0 hω.2.1 hz₀ H hH).trans (integral_dirac H z₀)

/-- A negative closed past cutoff excludes every path starting at the origin,
including at time zero. Its supported integrals therefore vanish at every
finite history length, without a diffusion-locality hypothesis. -/
theorem integral_eq_zero_of_negative_past_cutoff {d : ℕ} (Δ : ℝ≥0) (m : ℕ)
    (i : Fin d) (v : ℝ) (hv : v < 0) (μ : Measure (CoupledSample d))
    (hstart : ∀ᵐ z ∂μ, z.1 0 = 0) (H : CoupledSample d → ℝ)
    (hHs : ∀ z, z ∉ pastBelow Δ m i v → H z = 0) :
    (∫ z, H z ∂μ) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hstart] with z hz
  apply hHs z
  intro hpast
  have h := hpast 0 zero_le
  rw [hz] at h
  exact (not_le_of_gt hv) h

/-- The negative-barrier case of the past local-version conclusion follows
from the actual origin start alone, for every finite history. -/
theorem exists_local_past_integral_version_of_negative_barrier {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0 h1 P K)
    (Δ : ℝ≥0) (m : ℕ) (i : Fin d) (v : ℝ) (hv : v < 0)
    (U : Set (Vec d)) (H : CoupledSample d → ℝ)
    (hHs : ∀ z, z ∉ pastBelow Δ m i v → H z = 0) :
    ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧
      (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q.measure] A := by
  refine ⟨fun _ => 0, measurable_const, ?_⟩
  filter_upwards [ae_origin_data_of_gmpCoupling hd hΛ₀ Q lam l δ h0 h1 P K hK]
    with ω hω
  exact integral_eq_zero_of_negative_past_cutoff Δ m i v hv (K (0, ω)) hω.2.1 H hHs

section LocalVersions

open ProbabilityTheory

/-- The canonical joint-field carrier is standard Borel. -/
private theorem fieldPair_standardBorel (d : ℕ) : StandardBorelSpace (FieldPair d) := by
  let : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  let : PolishSpace (FieldPair d) := inferInstance
  infer_instance

attribute [local instance] fieldPair_standardBorel

-- These conditional-resampling arguments use Mathlib directly. They follow
-- ConditionalLocalVersions.lean:28–120 without importing the unrelated
-- LocalKernelVersion module, whose Lean 4.35 migration is owned elsewhere.
private theorem ae_condExpKernel_observation_eq {α E : Type*}
    [mα : MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace E] [MeasurableEq E]
    (μ : Measure α) [IsFiniteMeasure μ] (m : MeasurableSpace α) (hm : m ≤ mα)
    (X : α → E) (hX : Measurable[m] X) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂condExpKernel (mΩ := mα) μ m a, X a = X b := by
  let : MeasurableSpace α := mα
  let : MeasurableSpace (α × α) := m.prod mα
  have hp : @MeasurableSet (α × α) (m.prod mα) {p | X p.1 = X p.2} :=
    measurableSet_eq_fun (hX.comp (@measurable_fst α α m mα))
      ((hX.mono hm le_rfl).comp (@measurable_snd α α m mα))
  have hd : @Measurable α (α × α) mα (m.prod mα) (fun a => (a, a)) :=
    (measurable_id.mono le_rfl hm).prodMk measurable_id
  have hprod : ∀ᵐ p ∂(μ.trim hm).compProd (condExpKernel μ m), X p.1 = X p.2 := by
    rw [compProd_trim_condExpKernel hm]
    exact (ae_map_iff hd.aemeasurable hp).mpr (Filter.Eventually.of_forall fun _ => rfl)
  exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_compProd hprod)

private theorem ae_condExpKernel_of_ae {α : Type*}
    [mα : MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (m : MeasurableSpace α) (hm : m ≤ mα)
    {p : α → Prop} (hp : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂condExpKernel (mΩ := mα) μ m a, p b := by
  let : MeasurableSpace α := mα
  have hcomp : ∀ᵐ b ∂condExpKernel μ m ∘ₘ μ.trim hm, p b := by
    rw [condExpKernel_comp_trim hm]
    exact hp
  exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_comp hcomp)

private theorem ae_condExpKernel_fields_eq_on {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q] (U : Set (Vec d)) :
    ∀ᵐ ω ∂Q, ∀ᵐ ω' ∂condExpKernel Q (localSigma U) ω,
      ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y := by
  let : SecondCountableTopology (Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  obtain ⟨A, hAc, hAd⟩ := TopologicalSpace.exists_countable_dense U
  have : Countable A := hAc.to_subtype
  have hpoints : ∀ a : A, ∀ᵐ ω ∂Q, ∀ᵐ ω' ∂condExpKernel Q (localSigma U) ω,
      (ω.1 (a : U), ω.2 (a : U)) = (ω'.1 (a : U), ω'.2 (a : U)) := by
    intro a
    exact ae_condExpKernel_observation_eq Q (localSigma U) (Probability.localSigma_le_borel U)
      (fun ω : FieldPair d => (ω.1 (a : U), ω.2 (a : U)))
      (Measurable.of_comap_le (le_iSup
        (fun y : U => MeasurableSpace.comap
          (fun ω : FieldPair d => (ω.1 y, ω.2 y)) inferInstance) (a : U)))
  filter_upwards [ae_all_iff.mpr hpoints] with ω hω
  filter_upwards [ae_all_iff.mpr hω] with ω' hω'
  have hfun : (fun y : U => (ω.1 y, ω.2 y)) = fun y : U => (ω'.1 y, ω'.2 y) := by
    apply Continuous.ext_on hAd
      ((ω.1.continuous.comp continuous_subtype_val).prodMk
        (ω.2.continuous.comp continuous_subtype_val))
      ((ω'.1.continuous.comp continuous_subtype_val).prodMk
        (ω'.2.continuous.comp continuous_subtype_val))
    intro a ha
    exact hω' ⟨a, ha⟩
  intro y hy
  exact Prod.mk.inj (congrFun hfun ⟨y, hy⟩)

private theorem exists_local_version_of_fields_eq_on {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q] (U : Set (Vec d))
    (f : FieldPair d → ℝ) (hf : Measurable f)
    (G : Set (FieldPair d)) (hG : ∀ᵐ ω ∂Q, ω ∈ G)
    (hlocal : ∀ ω ∈ G, ∀ ω' ∈ G,
      (∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) → f ω = f ω') :
    ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧ A =ᵐ[Q] f := by
  refine ⟨fun ω => ∫ ω', f ω' ∂condExpKernel Q (localSigma U) ω,
    (hf.stronglyMeasurable.integral_condExpKernel).measurable, ?_⟩
  have heq : ∀ᵐ ω ∂Q, ∀ᵐ ω' ∂condExpKernel Q (localSigma U) ω, f ω = f ω' := by
    filter_upwards [hG,
      ae_condExpKernel_of_ae Q (localSigma U) (Probability.localSigma_le_borel U) hG,
      ae_condExpKernel_fields_eq_on Q U] with ω hω hgood heq
    filter_upwards [hgood, heq] with ω' hω' heq'
    exact hlocal ω hω ω' hω' heq'
  filter_upwards [heq] with ω hω
  calc
    _ = ∫ _ω', f ω ∂condExpKernel Q (localSigma U) ω :=
      integral_congr_ae (hω.mono fun _ h => h.symm)
    _ = f ω := by simp

/-- Supported scalar comparisons on a full-measure set give a joint-field local
version of every bounded finite-history observation. This conditional consumer
uses the original coupled fibres throughout; it does not supply the scalar
comparison or assert the past-kernel graph reduction. -/
theorem exists_local_supported_history_integral_version_of_scalar_comparison {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (U : Set (Vec d)) (v : ℝ) (G : Set (FieldPair d))
    (hG : ∀ᵐ ω ∂Q, ω ∈ G)
    (hdata : ∀ ω ∈ G,
      IsProbabilityMeasure (K (0, ω)) ∧
      (∀ᵐ z ∂K (0, ω), z.1 0 = 0) ∧
      (∀ y : Vec d, IsProbabilityMeasure (P (y, ω))) ∧
      Renewal.OneIntervalKernelAt Δ δ R i P K (0, ω))
    (hcompare : ∀ ω ∈ G, ∀ ω' ∈ G,
      (∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
      ∀ F : Path d → ℝ, Measurable F → BoundedRealTest F →
      (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') →
      (∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) →
      ∀ y : Vec d, y i ≤ v →
      (∫ γ, F γ ∂P (y, ω)) = (∫ γ, F γ ∂P (y, ω')) ∧
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω) =
        ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω')
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma Δ m] H) (hHb : BoundedRealTest H)
    (hHs : ∀ z, z ∉ pastBelow Δ m i v → H z = 0) :
    ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧
      (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q] A := by
  let f : FieldPair d → ℝ := fun ω =>
    ∫ z, H z ∂Probability.probabilityPart (originCoupledLaw K) ω
  have hf : Measurable f :=
    ((hH.mono (Probability.finiteHistorySigma_le Δ m) le_rfl).stronglyMeasurable.integral_kernel
      (κ := Probability.probabilityPart (originCoupledLaw K))).measurable
  have hlocal : ∀ ω ∈ G, ∀ ω' ∈ G,
      (∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) → f ω = f ω' := by
    intro ω hω ω' hω' heq
    obtain ⟨hp, hs, hprob, hone⟩ := hdata ω hω
    obtain ⟨hp', hs', _, hone'⟩ := hdata ω' hω'
    let : IsProbabilityMeasure (originCoupledLaw K ω) := hp
    let : IsProbabilityMeasure (originCoupledLaw K ω') := hp'
    change (∫ z, H z ∂Probability.probabilityPart (originCoupledLaw K) ω) =
      ∫ z, H z ∂Probability.probabilityPart (originCoupledLaw K) ω'
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure,
      Probability.probabilityPart_eq_of_isProbabilityMeasure]
    exact integral_supported_finite_history_eq_of_scalar_comparison Δ hΔ δ R i
      P P K K 0 ω ω' hs hs' hone hone' v hprob
      (hcompare ω hω ω' hω' heq) m H hH hHb hHs
  obtain ⟨A, hA, hAe⟩ :=
    exists_local_version_of_fields_eq_on Q U f hf G hG hlocal
  refine ⟨A, hA, ?_⟩
  filter_upwards [hAe, hG] with ω ha hω
  let : IsProbabilityMeasure (originCoupledLaw K ω) := (hdata ω hω).1
  change A ω = ∫ z, H z ∂Probability.probabilityPart (originCoupledLaw K) ω at ha
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure] at ha
  exact ha.symm

/-- Apply the finite-history comparison and local-version construction to the
actual reduced GMP realizations supplied by the coupling. The only remaining
input is the supported diffusion/bridge scalar comparison on those realizations;
this conditional consumer is not the past-kernel graph reduction. -/
theorem exists_local_past_integral_version_of_gmp_scalar_comparison {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K) :
    let R := l / lam
    let i := Renewal.forceCoord hd
    let Δ := Renewal.regenDelta lam
    ∀ (v : ℝ),
      (∀ (ω ω' : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
        (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
        (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω) hω lam h0.le h1)
        (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω') hω' lam h0.le h1),
        (∀ y : Vec d, P (y, ω) = r.pathLaw y) →
        (∀ y : Vec d, P (y, ω') = r'.pathLaw y) →
        (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
        ∀ F : Path d → ℝ, Measurable F → BoundedRealTest F →
        (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') →
        (∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) →
        ∀ y : Vec d, y i ≤ v →
        (∫ γ, F γ ∂P (y, ω)) = (∫ γ, F γ ∂P (y, ω')) ∧
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω) =
          ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω') →
      ∀ (m : ℕ) (H : CoupledSample d → ℝ),
        Measurable[finiteHistorySigma Δ m] H → BoundedRealTest H →
        (∀ z, (¬ ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → z.1 t i ≤ v) → H z = 0) →
        ∃ A : FieldPair d → ℝ,
          Measurable[localSigma {y : Vec d | y i ≤ v + 3 * R}] A ∧
          (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q.measure] A := by
  intro R i Δ v hcompare m H hH hHb hHs
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
  let G : Set (FieldPair d) := {ω |
    (IsProbabilityMeasure (K (0, ω)) ∧
      (∀ᵐ z ∂K (0, ω), z.1 0 = 0) ∧
      (∀ y : Vec d, IsProbabilityMeasure (P (y, ω))) ∧
      Renewal.OneIntervalKernelAt Δ δ R i P K (0, ω)) ∧
    ∃ hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω),
      ∃ r : External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
        (zeroPotentialReducedPair ω) hω lam h0.le h1,
        ∀ y : Vec d, P (y, ω) = r.pathLaw y}
  have hG : ∀ᵐ ω ∂Q.measure, ω ∈ G := by
    filter_upwards [ae_origin_data_of_gmpCoupling hd hΛ₀ Q lam l δ h0.le h1 P K hK,
      hK.2.2.1] with ω hdata hr
    exact ⟨hdata, hr⟩
  apply exists_local_supported_history_integral_version_of_scalar_comparison
    Q.measure Δ hΔ δ R i P K {y | y i ≤ v + 3 * R} v G hG
    (fun _ hω => hω.1) ?_ m H hH hHb hHs
  intro ω hωG ω' hω'G heq
  obtain ⟨hω, r, hr⟩ := hωG.2
  obtain ⟨hω', r', hr'⟩ := hω'G.2
  exact hcompare ω ω' hω hω' r r' hr hr' heq

/-- Conditional averaging turns individual scalar versions into a single local
finite kernel. The countably generated target is used by
`Kernel.ae_eq_of_compProd_eq` to obtain equality of measures on one common
full-measure set, rather than intersecting all measurable-event exceptional sets.
This is the Lean 4.35 form of `Probability.LocalKernelVersion`, kept here to
avoid importing its independently owned migration failure. -/
private theorem exists_local_kernel_of_integral_versions
    {α β : Type*} [mα : MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β) [IsFiniteKernel κ]
    (m : MeasurableSpace α) (hm : m ≤ mα)
    (hlocal : ∀ F : β → ℝ, Measurable F → BoundedRealTest F →
      ∃ A : α → ℝ, Measurable[m] A ∧ A =ᵐ[μ] fun a => ∫ b, F b ∂κ a) :
    ∃ η : @Kernel α β m inferInstance,
      IsFiniteKernel η ∧ ∀ᵐ a ∂μ, κ a = η a := by
  classical
  let : MeasurableSpace α := mα
  let η : @Kernel α β m inferInstance := κ ∘ₖ condExpKernel μ m
  let η' : Kernel α β := η.comap id (measurable_id.mono le_rfl hm)
  have heq : ∀ t : Set β, MeasurableSet t →
      (fun a => (κ a).real t) =ᵐ[μ] fun a => (η' a).real t := by
    intro t ht
    obtain ⟨A, hA, hAe⟩ := hlocal (t.indicator (fun _ => 1))
      (measurable_const.indicator ht) ⟨1, fun b => by by_cases hb : b ∈ t <;> simp [hb]⟩
    simp only [integral_indicator ht, setIntegral_one_eq_measureReal] at hAe
    have hfi := Kernel.IsFiniteKernel.integrable μ κ ht
    have hfm : AEStronglyMeasurable[m] (fun a => (κ a).real t) μ :=
      hA.stronglyMeasurable.aestronglyMeasurable.congr hAe
    have hc := condExp_ae_eq_integral_condExpKernel hm hfi
    have hf := condExp_of_aestronglyMeasurable' hm hfm hfi
    have hi : ∀ a, (η' a).real t =
        ∫ b, (κ b).real t ∂condExpKernel μ m a := by
      intro a
      have h := Kernel.integral_comp (η := κ) (κ := condExpKernel μ m) (a := a)
        ((integrable_const (μ := (κ ∘ₖ condExpKernel μ m) a) (1 : ℝ)).indicator ht)
      simpa only [η', Kernel.comap_apply, id_eq, η, integral_indicator ht,
        setIntegral_one_eq_measureReal] using h
    filter_upwards [hc, hf] with a ha hfa
    rw [hi, ← ha, hfa]
  have heq' : ∀ t : Set β, MeasurableSet t →
      (fun a => κ a t) =ᵐ[μ] fun a => η' a t := by
    intro t ht
    filter_upwards [heq t ht] with a ha
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (κ a) t)
      (measure_ne_top (η' a) t)).mp ha
  have hprod : μ.compProd κ = μ.compProd η' := by
    apply Measure.ext_prod
    intro s t hs ht
    rw [Measure.compProd_apply_prod hs ht, Measure.compProd_apply_prod hs ht]
    exact setLIntegral_congr_fun_ae hs ((heq' t ht).mono fun _ h _ => h)
  exact ⟨η, inferInstance, Kernel.ae_eq_of_compProd_eq hprod⟩

/-- The law of the literal stopped finite history, restricted to the closed
cutoff. Probability normalization is used only to make the ambient kernel finite;
on probability fibres this is exactly the restricted original law. -/
def supportedHistoryKernel {d : ℕ} (Δ : ℝ≥0) (m : ℕ) (i : Fin d) (v : ℝ)
    (K : CoupledQuenchedLaws d) : Kernel (FieldPair d) (CoupledSample d) :=
  ((Probability.probabilityPart (originCoupledLaw K)).restrict
    (measurableSet_pastBelow Δ m i v)).map (Probability.stoppedHistorySample Δ m)

instance supportedHistoryKernel_isFiniteKernel {d : ℕ}
    (Δ : ℝ≥0) (m : ℕ) (i : Fin d) (v : ℝ) (K : CoupledQuenchedLaws d) :
    IsFiniteKernel (supportedHistoryKernel Δ m i v K) := by
  unfold supportedHistoryKernel
  infer_instance

/-- Scalar past versions determine a single local kernel for the actual
restricted stopped history. The equality is simultaneous for every measurable
event. This consumer supplies no analytic locality premise for the root. -/
theorem exists_local_supported_history_kernel_of_integral_versions {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q]
    (Δ : ℝ≥0) (m : ℕ) (i : Fin d) (v : ℝ) (U : Set (Vec d))
    (K : CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (hlocal : ∀ H : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ m] H →
      BoundedRealTest H → (∀ z, z ∉ pastBelow Δ m i v → H z = 0) →
      ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧
        (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q] A) :
    ∃ η : @Kernel (FieldPair d) (CoupledSample d) (localSigma U) inferInstance,
      IsFiniteKernel η ∧ ∀ᵐ ω ∂Q,
        η ω = Measure.map (Probability.stoppedHistorySample Δ m)
          ((K (0, ω)).restrict (pastBelow Δ m i v)) := by
  have hstop : Measurable (Probability.stoppedHistorySample (d := d) Δ m) :=
    (Probability.measurable_stoppedHistorySample Δ m).mono
      (Probability.finiteHistorySigma_le Δ m) le_rfl
  obtain ⟨η, hη, hηe⟩ := exists_local_kernel_of_integral_versions Q
    (supportedHistoryKernel Δ m i v K) (localSigma U) (Probability.localSigma_le_borel U) (by
      intro F hF hFb
      let H : CoupledSample d → ℝ := (pastBelow Δ m i v).indicator
        (fun z => F (Probability.stoppedHistorySample Δ m z))
      have hH : Measurable[finiteHistorySigma Δ m] H :=
        (hF.comp (Probability.measurable_stoppedHistorySample Δ m)).indicator
          (measurableSet_pastBelow_history Δ m i v)
      have hHb : BoundedRealTest H := by
        obtain ⟨C, hC⟩ := hFb
        refine ⟨max C 0, fun z => ?_⟩
        by_cases hz : z ∈ pastBelow Δ m i v
        · simp only [H, Set.indicator_of_mem hz]
          exact (hC (Probability.stoppedHistorySample Δ m z)).trans (le_max_left _ _)
        · simp only [H, Set.indicator_of_notMem hz, abs_zero]
          exact le_max_right _ _
      obtain ⟨A, hA, he⟩ := hlocal H hH hHb (fun z hz => Set.indicator_of_notMem hz _)
      refine ⟨A, hA, ?_⟩
      filter_upwards [he, hprob] with ω hω hp
      let : IsProbabilityMeasure (originCoupledLaw K ω) := hp
      rw [hω.symm]
      unfold supportedHistoryKernel
      rw [Kernel.map_apply _ hstop, Kernel.restrict_apply,
        Probability.probabilityPart_eq_of_isProbabilityMeasure]
      rw [integral_map hstop.aemeasurable hF.aestronglyMeasurable,
        ← integral_indicator (measurableSet_pastBelow Δ m i v)]
      rfl)
  refine ⟨η, hη, ?_⟩
  filter_upwards [hηe, hprob] with ω hω hp
  let : IsProbabilityMeasure (originCoupledLaw K ω) := hp
  rw [← hω]
  unfold supportedHistoryKernel
  rw [Kernel.map_apply _ hstop, Kernel.restrict_apply,
    Probability.probabilityPart_eq_of_isProbabilityMeasure]
  rfl

/-- Equality of stopped restricted measures decodes all supported past tests
on one common full-measure set. No exceptional set is chosen separately for
individual tests, and no integrability premise is needed for this equality. -/
theorem ae_all_supported_history_integral_eq_of_kernel_eq {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (m : ℕ) (i : Fin d) (v : ℝ)
    (K : CoupledQuenchedLaws d) (U : Set (Vec d))
    (η : @Kernel (FieldPair d) (CoupledSample d) (localSigma U) inferInstance)
    (hη : ∀ᵐ ω ∂Q, η ω = Measure.map (Probability.stoppedHistorySample Δ m)
      ((K (0, ω)).restrict (pastBelow Δ m i v))) :
    ∀ᵐ ω ∂Q, ∀ H : CoupledSample d → ℝ,
      Measurable[finiteHistorySigma Δ m] H →
      (∀ z, z ∉ pastBelow Δ m i v → H z = 0) →
      (∫ z, H z ∂K (0, ω)) = ∫ z, H z ∂η ω := by
  have hstop : Measurable (Probability.stoppedHistorySample (d := d) Δ m) :=
    (Probability.measurable_stoppedHistorySample Δ m).mono
      (Probability.finiteHistorySigma_le Δ m) le_rfl
  filter_upwards [hη] with ω hω
  intro H hH hHs
  have hHm : Measurable H := hH.mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  rw [hω, integral_map hstop.aemeasurable hHm.aestronglyMeasurable]
  simp_rw [Probability.finiteHistory_test_stopped Δ m H hH]
  rw [← integral_indicator (measurableSet_pastBelow Δ m i v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : z ∈ pastBelow Δ m i v
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hHs z hz]

/-- The single local stopped-history kernel also handles genuinely joint
past/environment tests. The environment argument is the original joint field,
and its sigma-algebra is the actual local joint-field sigma-algebra. This
extends scalar versions without an uncountable union of exceptional sets. -/
theorem exists_local_joint_past_integral_version_of_integral_versions {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q]
    (Δ : ℝ≥0) (m : ℕ) (i : Fin d) (v : ℝ) (U : Set (Vec d))
    (K : CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (hlocal : ∀ H : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ m] H →
      BoundedRealTest H → (∀ z, z ∉ pastBelow Δ m i v → H z = 0) →
      ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧
        (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q] A)
    (Ψ : FieldPair d × CoupledSample d → ℝ)
    (hΨ : Measurable[(localSigma U).prod (finiteHistorySigma Δ m)] Ψ)
    (hΨs : ∀ ω z, z ∉ pastBelow Δ m i v → Ψ (ω, z) = 0) :
    ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧
      (fun ω => ∫ z, Ψ (ω, z) ∂K (0, ω)) =ᵐ[Q] A := by
  obtain ⟨η, hηfin, hηe⟩ :=
    exists_local_supported_history_kernel_of_integral_versions
      Q Δ m i v U K hprob hlocal
  let : IsFiniteKernel η := hηfin
  have hΨm : Measurable[(localSigma U).prod
      (inferInstance : MeasurableSpace (CoupledSample d))] Ψ :=
    hΨ.mono (sup_le_sup le_rfl
      (MeasurableSpace.comap_mono (Probability.finiteHistorySigma_le Δ m))) le_rfl
  refine ⟨fun ω => ∫ z, Ψ (ω, z) ∂η ω,
    (hΨm.stronglyMeasurable.integral_kernel_prod_right').measurable, ?_⟩
  filter_upwards [ae_all_supported_history_integral_eq_of_kernel_eq
    Q Δ m i v K U η hηe] with ω hω
  exact hω (fun z => Ψ (ω, z))
    (hΨ.comp (measurable_const.prodMk measurable_id)) (hΨs ω)

/-- A spatially joint local version, under a finite measure on starts and
original fields. Conditional resampling retains the start exactly and both
fields simultaneously at every point of the region. -/
private theorem exists_joint_start_version_of_fields_eq_on {d : ℕ}
    (μ : Measure (Vec d × FieldPair d)) [IsFiniteMeasure μ] (U : Set (Vec d))
    (f : Vec d × FieldPair d → ℝ) (hf : Measurable f)
    (G : Set (Vec d × FieldPair d)) (hG : ∀ᵐ p ∂μ, p ∈ G)
    (hlocal : ∀ p ∈ G, ∀ q ∈ G, p.1 = q.1 →
      (∀ y ∈ U, p.2.1 y = q.2.1 y ∧ p.2.2 y = q.2.2 y) → f p = f q) :
    ∃ A : Vec d × FieldPair d → ℝ,
      Measurable[(borel (Vec d)).prod (localSigma U)] A ∧ A =ᵐ[μ] f := by
  let mambient := (inferInstance : MeasurableSpace (Vec d × FieldPair d))
  let m := (borel (Vec d)).prod (localSigma U)
  let : MeasurableSpace (Vec d × FieldPair d) := mambient
  have hm : m ≤ (inferInstance : MeasurableSpace (Vec d × FieldPair d)) :=
    sup_le_sup (MeasurableSpace.comap_mono BorelSpace.measurable_eq.symm.le)
      (MeasurableSpace.comap_mono (Probability.localSigma_le_borel U))
  have hfst : Measurable[m] (fun p : Vec d × FieldPair d => p.1) :=
    (@measurable_fst (Vec d) (FieldPair d) (borel (Vec d)) (localSigma U)).mono
      le_rfl BorelSpace.measurable_eq.le
  have hfields : ∀ᵐ p ∂μ, ∀ᵐ q ∂condExpKernel μ m p,
      ∀ y ∈ U, p.2.1 y = q.2.1 y ∧ p.2.2 y = q.2.2 y := by
    let : SecondCountableTopology (Mat d) :=
      inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
    obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense U
    have : Countable D := hDc.to_subtype
    have hpoints : ∀ a : D, ∀ᵐ p ∂μ, ∀ᵐ q ∂condExpKernel μ m p,
        (p.2.1 (a : U), p.2.2 (a : U)) = (q.2.1 (a : U), q.2.2 (a : U)) := by
      intro a
      have hY : Measurable[localSigma U]
          (fun ω : FieldPair d => (ω.1 (a : U), ω.2 (a : U))) :=
        Measurable.of_comap_le (le_iSup (fun y : U => MeasurableSpace.comap
          (fun ω : FieldPair d => (ω.1 y, ω.2 y)) inferInstance) (a : U))
      exact ae_condExpKernel_observation_eq μ m hm
        (fun p : Vec d × FieldPair d => (p.2.1 (a : U), p.2.2 (a : U)))
        (hY.comp (@measurable_snd (Vec d) (FieldPair d) (borel (Vec d)) (localSigma U)))
    filter_upwards [ae_all_iff.mpr hpoints] with p hp
    filter_upwards [ae_all_iff.mpr hp] with q hq
    have hfun : (fun y : U => (p.2.1 y, p.2.2 y)) = fun y : U => (q.2.1 y, q.2.2 y) := by
      apply Continuous.ext_on hDd
        ((p.2.1.continuous.comp continuous_subtype_val).prodMk
          (p.2.2.continuous.comp continuous_subtype_val))
        ((q.2.1.continuous.comp continuous_subtype_val).prodMk
          (q.2.2.continuous.comp continuous_subtype_val))
      intro a ha
      exact hq ⟨a, ha⟩
    intro y hy
    exact Prod.mk.inj (congrFun hfun ⟨y, hy⟩)
  have heq : ∀ᵐ p ∂μ, ∀ᵐ q ∂condExpKernel μ m p, f p = f q := by
    filter_upwards [hG, ae_condExpKernel_of_ae μ m hm hG,
      ae_condExpKernel_observation_eq μ m hm _ hfst, hfields] with p hp hgood hx he
    filter_upwards [hgood, hx, he] with q hq hqx hqe
    exact hlocal p hp q hq hqx hqe
  refine ⟨fun p => ∫ q, f q ∂condExpKernel μ m p,
    (hf.stronglyMeasurable.integral_condExpKernel).measurable, ?_⟩
  filter_upwards [heq] with p hp
  calc
    _ = ∫ _q, f p ∂condExpKernel μ m p :=
      integral_congr_ae (hp.mono fun _ h => h.symm)
    _ = f p := by simp

/-- Construct one spatially joint local version with the correct origin
section. Product-a.e. information is transferred through an equivalent finite
measure; the separately proved Q-a.e. origin value is spliced in on `{x = 0}`. -/
private theorem exists_origin_and_joint_start_version_of_fields_eq_on {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q] (i : Fin d) (U : Set (Vec d))
    (f : Vec d × FieldPair d → ℝ) (hf : Measurable f)
    (G : Set (Vec d × FieldPair d)) (hG0 : ∀ᵐ ω ∂Q, (0, ω) ∈ G)
    (hGp : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), p ∈ G)
    (hlocal : ∀ p ∈ G, ∀ q ∈ G, p.1 = q.1 →
      (∀ y ∈ U, p.2.1 y = q.2.1 y ∧ p.2.2 y = q.2.2 y) → f p = f q) :
    ∃ A : Vec d × FieldPair d → ℝ,
      Measurable[(borel (Vec d)).prod (localSigma U)] A ∧
      (∀ᵐ ω ∂Q, A (0, ω) = f (0, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] f := by
  classical
  obtain ⟨A0, hA0, hA0e⟩ := exists_local_version_of_fields_eq_on Q U
    (fun ω => f (0, ω)) (hf.comp (measurable_const.prodMk measurable_id))
    {ω | (0, ω) ∈ G} hG0 (fun ω hω ω' hω' he => hlocal (0, ω) hω (0, ω') hω' rfl he)
  obtain ⟨ν, hνfin, hvν, hνv⟩ :=
    exists_isFiniteMeasure_absolutelyContinuous (volume : Measure (Vec d))
  have hpv : (volume : Measure (Vec d)).prod Q ≪ ν.prod Q :=
    Measure.AbsolutelyContinuous.prod hvν (Measure.AbsolutelyContinuous.refl Q)
  have hνp : ν.prod Q ≪ (volume : Measure (Vec d)).prod Q :=
    Measure.AbsolutelyContinuous.prod hνv (Measure.AbsolutelyContinuous.refl Q)
  obtain ⟨A1, hA1, hA1e⟩ := exists_joint_start_version_of_fields_eq_on
    (ν.prod Q) U f hf G (hνp.ae_le hGp) hlocal
  have hnot0 : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), p.1 ≠ 0 := by
    have : Nonempty (Fin d) := ⟨i⟩
    have hx : ∀ᵐ x ∂(volume : Measure (Vec d)), x ≠ 0 :=
      (compl_mem_ae_iff (s := ({0} : Set (Vec d)))).mpr (measure_singleton (0 : Vec d))
    exact (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Vec d))) (ν := Q)).ae hx
  refine ⟨fun p => if p.1 = 0 then A0 p.2 else A1 p, ?_, ?_, ?_⟩
  · have hs : MeasurableSet[borel (Vec d)] ({0} : Set (Vec d)) := by
      rw [← BorelSpace.measurable_eq]
      exact measurableSet_singleton _
    exact Measurable.ite
      ((@measurable_fst (Vec d) (FieldPair d) (borel (Vec d)) (localSigma U)) hs)
      (hA0.comp (@measurable_snd (Vec d) (FieldPair d) (borel (Vec d)) (localSigma U))) hA1
  · filter_upwards [hA0e] with ω hω
    rw [ite_eq_left rfl]
    exact hω
  · filter_upwards [hpv.ae_le hA1e, hnot0] with p hp hx
    rw [ite_eq_right hx]
    exact hp

/-- Both origin and product versions of every supported past test follow from
the original-fibre one-interval identities and the supported scalar comparisons.
The analytic comparisons remain explicit inputs of this mathematical consumer;
this does not assert the past-kernel graph reduction. -/
theorem hasPastHalfSpaceVersions_of_supported_scalar_comparison {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (G : Set (Vec d × FieldPair d)) (hG0 : ∀ᵐ ω ∂Q, (0, ω) ∈ G)
    (hGp : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), p ∈ G)
    (hdata : ∀ p ∈ G, IsProbabilityMeasure (K p) ∧
      (∀ᵐ z ∂K p, z.1 0 = p.1) ∧
      (∀ y : Vec d, IsProbabilityMeasure (P (y, p.2))) ∧
      Renewal.OneIntervalKernelAt Δ δ R i P K p)
    (hcompare : ∀ v : ℝ, ∀ p ∈ G, ∀ q ∈ G, p.1 = q.1 →
      (∀ y : Vec d, y i ≤ v + 3 * R → p.2.1 y = q.2.1 y ∧ p.2.2 y = q.2.2 y) →
      ∀ F : Path d → ℝ, Measurable F → BoundedRealTest F →
      (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') →
      (∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) →
      ∀ y : Vec d, y i ≤ v →
      (∫ γ, F γ ∂P (y, p.2)) = (∫ γ, F γ ∂P (y, q.2)) ∧
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y p.2) =
        ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y q.2) :
    HasPastHalfSpaceVersions Q Δ i R K := by
  intro m _ v H hH hHb hHs
  have hHm : Measurable H := hH.mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  apply exists_origin_and_joint_start_version_of_fields_eq_on Q i
    {y : Vec d | y i ≤ v + 3 * R} (fun p => ∫ z, H z ∂K p)
    hHm.stronglyMeasurable.integral_kernel.measurable G hG0 hGp
  rintro ⟨x, ω⟩ hp ⟨x', ω'⟩ hq hx he
  change x = x' at hx
  subst x'
  obtain ⟨hpK, hpstart, hpP, hpone⟩ := hdata (x, ω) hp
  obtain ⟨hqK, hqstart, _, hqone⟩ := hdata (x, ω') hq
  let : IsProbabilityMeasure (K (x, ω)) := hpK
  let : IsProbabilityMeasure (K (x, ω')) := hqK
  exact integral_supported_finite_history_eq_of_scalar_comparison Δ hΔ δ R i
    P P K K x ω ω' hpstart hqstart hpone hqone v hpP
    (hcompare v (x, ω) hp (x, ω') hq rfl he) m H hH hHb
    (fun z hz => by
      by_contra hn
      exact hz (hHs z hn))

/-- The actual GMP coupling and its supported scalar comparisons determine a
single local version of the full restricted stopped-history measure. This
conditional result uses the original kernel, with no new root premise. -/
theorem exists_local_supported_history_kernel_of_gmp_scalar_comparison {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K) :
    let R := l / lam
    let i := Renewal.forceCoord hd
    let Δ := Renewal.regenDelta lam
    ∀ (v : ℝ),
      (∀ (ω ω' : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
        (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
        (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω) hω lam h0.le h1)
        (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω') hω' lam h0.le h1),
        (∀ y : Vec d, P (y, ω) = r.pathLaw y) →
        (∀ y : Vec d, P (y, ω') = r'.pathLaw y) →
        (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
        ∀ F : Path d → ℝ, Measurable F → BoundedRealTest F →
        (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') →
        (∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) →
        ∀ y : Vec d, y i ≤ v →
        (∫ γ, F γ ∂P (y, ω)) = (∫ γ, F γ ∂P (y, ω')) ∧
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω) =
          ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω') →
      ∀ m : ℕ,
        ∃ η : @Kernel (FieldPair d) (CoupledSample d)
          (localSigma {y : Vec d | y i ≤ v + 3 * R}) inferInstance,
          IsFiniteKernel η ∧ ∀ᵐ ω ∂Q.measure,
            η ω = Measure.map (Probability.stoppedHistorySample Δ m)
              ((K (0, ω)).restrict (pastBelow Δ m i v)) := by
  intro R i Δ v hcompare m
  apply exists_local_supported_history_kernel_of_integral_versions Q.measure Δ m i v
    {y : Vec d | y i ≤ v + 3 * R} K
    ((ae_origin_data_of_gmpCoupling hd hΛ₀ Q lam l δ h0.le h1 P K hK).mono
      fun _ hω => hω.1)
  intro H hH hHb hHs
  exact exists_local_past_integral_version_of_gmp_scalar_comparison
    hd hΛ₀ Q lam l δ h0 h1 P K hK v hcompare m H hH hHb hHs

/-- Specialize the full origin-and-spatial version consumer to the actual
GMP coupling. Only supported diffusion and literal killed-bridge scalar
comparisons remain inputs; no locality statement is added to the graph root. -/
theorem hasPastHalfSpaceVersions_of_gmp_scalar_comparison {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K) :
    let R := l / lam
    let i := Renewal.forceCoord hd
    let Δ := Renewal.regenDelta lam
    (∀ (v : ℝ) (ω ω' : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
        (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
        (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω) hω lam h0.le h1)
        (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω') hω' lam h0.le h1),
        (∀ y : Vec d, P (y, ω) = r.pathLaw y) →
        (∀ y : Vec d, P (y, ω') = r'.pathLaw y) →
        (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
        ∀ F : Path d → ℝ, Measurable F → BoundedRealTest F →
        (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') →
        (∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) →
        ∀ y : Vec d, y i ≤ v →
        (∫ γ, F γ ∂P (y, ω)) = (∫ γ, F γ ∂P (y, ω')) ∧
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω) =
          ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω') →
    HasPastHalfSpaceVersions Q.measure Δ i R K := by
  intro R i Δ hcompare
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
  let G : Set (Vec d × FieldPair d) := {p |
    (IsProbabilityMeasure (K p) ∧
      (∀ᵐ z ∂K p, z.1 0 = p.1) ∧
      (∀ y : Vec d, IsProbabilityMeasure (P (y, p.2))) ∧
      Renewal.OneIntervalKernelAt Δ δ R i P K p) ∧
    ∃ hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair p.2),
      ∃ r : External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
        (zeroPotentialReducedPair p.2) hω lam h0.le h1,
        ∀ y : Vec d, P (y, p.2) = r.pathLaw y}
  have hG0 : ∀ᵐ ω ∂Q.measure, (0, ω) ∈ G := by
    filter_upwards [ae_origin_data_of_gmpCoupling hd hΛ₀ Q lam l δ h0.le h1 P K hK,
      hK.2.2.1] with ω hdata hr
    exact ⟨hdata, hr⟩
  have hGj : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure), p ∈ G := by
    filter_upwards [hK.1.2, hK.2.1.2,
      (Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure (Vec d))) (ν := Q.measure)).ae hK.2.2.1,
      hK.2.2.2.2.2.2.2.2] with p hp hm hω hone
    obtain ⟨hreg, r, hr⟩ := hω
    refine ⟨⟨hp, ?_, ?_, hone⟩, hreg, r, hr⟩
    · have hs : ∀ᵐ γ ∂P p, γ 0 = p.1 := by
        rw [show P p = r.pathLaw p.1 from hr p.1]
        exact r.pathLaw_starts_at p.1
      rw [← hm] at hs
      exact ae_of_ae_map measurable_fst.aemeasurable hs
    · intro y
      rw [hr y]
      exact r.pathLaw_isMarkovKernel.isProbabilityMeasure y
  apply hasPastHalfSpaceVersions_of_supported_scalar_comparison
    Q.measure Δ hΔ δ R i P K G hG0 hGj (fun _ hp => hp.1)
  intro v p hp q hq _ heq
  obtain ⟨hω, r, hr⟩ := hp.2
  obtain ⟨hω', r', hr'⟩ := hq.2
  exact hcompare v p.2 q.2 hω hω' r r' hr hr' heq

end LocalVersions

section EndpointPast

open ProbabilityTheory

/-- The literal trial and endpoint-ball test defining the source past factor. -/
def endpointPastTest {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (y : Vec d) : CoupledSample d → ℝ :=
  {z | y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))}.indicator
    ((forcedBitTrialEvent Δ lam R i m).indicator H)

/-- Both indicators retain the exact history, including only coins before `m`. -/
theorem measurable_endpointPastTest {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable[finiteHistorySigma Δ m] H)
    (y : Vec d) : Measurable[finiteHistorySigma Δ m]
      (endpointPastTest Δ lam R i m H y) :=
  (hH.indicator (measurableSet_forcedBitTrialEvent_finiteHistory Δ hΔ lam R hR i m)).indicator
    (measurableSet_endpointBall_past Δ R i m y)

/-- Endpoint selection never enlarges a bounded past observation. -/
theorem abs_endpointPastTest_le {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (m : ℕ) (H : CoupledSample d → ℝ) (y : Vec d) (z : CoupledSample d) :
    |endpointPastTest Δ lam R i m H y z| ≤ |H z| := by
  classical
  unfold endpointPastTest
  by_cases hy : z ∈ {w : CoupledSample d |
      y ∈ endpointBall i R (w.1 ((m : ℝ≥0) * Δ))}
  · rw [Set.indicator_of_mem hy]
    by_cases hz : z ∈ forcedBitTrialEvent Δ lam R i m
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, abs_zero]
      exact abs_nonneg _
  · rw [Set.indicator_of_notMem hy, abs_zero]
    exact abs_nonneg _

/-- The same constant bounds every endpoint test. -/
theorem bounded_endpointPastTest {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (m : ℕ) (H : CoupledSample d → ℝ) (hH : BoundedRealTest H) (y : Vec d) :
    BoundedRealTest (endpointPastTest Δ lam R i m H y) := by
  obtain ⟨C, hC⟩ := hH
  exact ⟨C, fun z => (abs_endpointPastTest_le Δ lam R i m H y z).trans (hC z)⟩

/-- The source geometry gives the closed cutoff `yᵢ - 7R` for this exact test. -/
theorem endpointPastTest_eq_zero_of_not_pastBelow {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (m : ℕ) (H : CoupledSample d → ℝ) (y : Vec d)
    (z : CoupledSample d) (hz : z ∉ pastBelow Δ m i (y i - 7 * R)) :
    endpointPastTest Δ lam R i m H y z = 0 := by
  classical
  by_cases hy : z ∈ {w : CoupledSample d |
      y ∈ endpointBall i R (w.1 ((m : ℝ≥0) * Δ))}
  · by_cases hΓ : z ∈ forcedBitTrialEvent Δ lam R i m
    · exact (hz (forcedBitTrialEvent_endpoint_past_barrier
        Δ hΔ lam R hlam hR i m z hΓ y hy)).elim
    · exact (Set.indicator_of_mem hy _).trans (Set.indicator_of_notMem hΓ _)
  · exact Set.indicator_of_notMem hy _

/-- Identifying the indicator test does not alter the endpoint disintegration. -/
theorem integral_endpointPastTest {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (m : ℕ) (K : CoupledQuenchedLaws d) (H : CoupledSample d → ℝ)
    (y : Vec d) (ω : FieldPair d) :
    (∫ z, endpointPastTest Δ lam R i m H y z ∂K (0, ω)) =
      firstSlicePastIntegral Δ lam R i m K H (y, ω) := by
  classical
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change endpointPastTest Δ lam R i m H y z =
      ((forcedBitTrialEvent Δ lam R i m).indicator H) z *
        (if y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) then 1 else 0)
    unfold endpointPastTest
    by_cases hy : z ∈ {w : CoupledSample d |
        y ∈ endpointBall i R (w.1 ((m : ℝ≥0) * Δ))}
    · rw [Set.indicator_of_mem hy,
        ite_eq_left (show y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) from hy), mul_one]
    · rw [Set.indicator_of_notMem hy,
        ite_eq_right (show y ∉ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) from hy), mul_zero]

/-- A pointwise bound on the source test dominates every endpoint past factor
on every probability fibre, with exactly the same constant. -/
theorem abs_firstSlicePastIntegral_le {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (m : ℕ) (K : CoupledQuenchedLaws d) (H : CoupledSample d → ℝ)
    (C : ℝ) (hC : ∀ z, |H z| ≤ C) (ω : FieldPair d)
    [IsProbabilityMeasure (K (0, ω))] (y : Vec d) :
    |firstSlicePastIntegral Δ lam R i m K H (y, ω)| ≤ C := by
  rw [← integral_endpointPastTest]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := K (0, ω))
      (f := endpointPastTest Δ lam R i m H y) (C := C)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using
          (abs_endpointPastTest_le Δ lam R i m H y z).trans (hC z)))

/-- Origin scalar versions suffice for the actual endpoint past factor.
This conditional consumer uses the literal test and the exact `7R - 3R`
margin; it does not require a spatial-a.e. version at the origin. -/
theorem exists_firstSlicePastIntegral_local_version_of_origin_versions {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma Δ m] H) (hbH : BoundedRealTest H)
    (y : Vec d)
    (hlocal : ∀ F : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ m] F →
      BoundedRealTest F →
      (∀ z, z ∉ pastBelow Δ m i (y i - 7 * R) → F z = 0) →
      ∃ A : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x i ≤ y i - 7 * R + 3 * R}] A ∧
        (fun ω => ∫ z, F z ∂K (0, ω)) =ᵐ[Q] A) :
    ∃ A : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] A ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q] A := by
  obtain ⟨A, hA, heq⟩ := hlocal (endpointPastTest Δ lam R i m H y)
    (measurable_endpointPastTest Δ hΔ lam R hR i m H hH y)
    (bounded_endpointPastTest Δ lam R i m H hbH y)
    (endpointPastTest_eq_zero_of_not_pastBelow Δ hΔ lam R hlam hR i m H y)
  have hmargin : y i - 7 * R + 3 * R = y i - 4 * R := by ring
  rw [hmargin] at hA
  exact ⟨A, hA, by simpa only [integral_endpointPastTest] using heq⟩

/-- A single equality of restricted stopped measures gives every endpoint
and every measurable history test on one common environment good set. The
endpoint parameter is inside the a.e. quantifier, not an intersection of
uncountably many separately chosen scalar exceptional sets. -/
theorem ae_all_endpoint_past_integral_eq_of_kernel_eq {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (m : ℕ) (i : Fin d) (v : ℝ)
    (K : CoupledQuenchedLaws d) (U : Set (Vec d))
    (η : @Kernel (FieldPair d) (CoupledSample d) (localSigma U) inferInstance)
    (hη : ∀ᵐ ω ∂Q, η ω = Measure.map (Probability.stoppedHistorySample Δ m)
      ((K (0, ω)).restrict (pastBelow Δ m i v))) :
    ∀ᵐ ω ∂Q, ∀ (y : Vec d), y i - 7 * R ≤ v →
      ∀ H : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ m] H →
      firstSlicePastIntegral Δ lam R i m K H (y, ω) =
        ∫ z, endpointPastTest Δ lam R i m H y z ∂η ω := by
  filter_upwards [ae_all_supported_history_integral_eq_of_kernel_eq
    Q Δ m i v K U η hη] with ω hω
  intro y hy H hH
  rw [← integral_endpointPastTest]
  apply hω _ (measurable_endpointPastTest Δ hΔ lam R hR i m H hH y)
  intro z hz
  apply endpointPastTest_eq_zero_of_not_pastBelow Δ hΔ lam R hlam hR i m H y z
  intro hzy
  exact hz (fun t ht => (hzy t ht).trans hy)

/-- A local endpoint version can be chosen with a global bound. Clipping
changes it only on the exceptional environment set and leaves the literal
past integral unchanged on every probability fibre where the version agrees. -/
theorem exists_bounded_firstSlicePastIntegral_local_version {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (C : ℝ) (hC : ∀ z, |H z| ≤ C)
    (y : Vec d) (U : Set (Vec d))
    (hlocal : ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q] A) :
    ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧
      (∀ ω, |A ω| ≤ C) ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q] A := by
  obtain ⟨A, hA, heq⟩ := hlocal
  have hC0 : 0 ≤ C := (abs_nonneg (H (0, fun _ => false))).trans (hC _)
  refine ⟨fun ω => max (-C) (min C (A ω)), measurable_const.max (measurable_const.min hA),
    fun ω => abs_le.mpr ⟨le_max_left _ _, ?_⟩, ?_⟩
  · exact max_le (by linarith) (min_le_left _ _)
  · filter_upwards [heq, hprob] with ω hω hp
    let : IsProbabilityMeasure (K (0, ω)) := hp
    have hb := abs_le.mp (abs_firstSlicePastIntegral_le Δ lam R i m K H C hC ω y)
    rw [← hω, min_eq_right hb.2, max_eq_right hb.1]

/-- Rational cutoffs and natural finite-history indices admit a common
environment good set. Each local kernel represents the actual restricted
stopped law there, so all endpoint/test pairs are decoded simultaneously.
The scalar-version producer remains an explicit input of this consumer. -/
theorem exists_countable_endpoint_past_kernels_of_integral_versions {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (K : CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (hlocal : ∀ (m : ℕ) (q : ℚ) (H : CoupledSample d → ℝ),
      Measurable[finiteHistorySigma Δ m] H → BoundedRealTest H →
      (∀ z, z ∉ pastBelow Δ m i (q : ℝ) → H z = 0) →
      ∃ A : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x i ≤ (q : ℝ) + 3 * R}] A ∧
        (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q] A) :
    ∃ η : (m : ℕ) → (q : ℚ) → @Kernel (FieldPair d) (CoupledSample d)
        (localSigma {x : Vec d | x i ≤ (q : ℝ) + 3 * R}) inferInstance,
      (∀ m q, IsFiniteKernel (η m q)) ∧
      ∀ᵐ ω ∂Q, ∀ (m : ℕ) (q : ℚ),
        η m q ω = Measure.map (Probability.stoppedHistorySample Δ m)
          ((K (0, ω)).restrict (pastBelow Δ m i (q : ℝ))) ∧
        ∀ (y : Vec d), y i - 7 * R ≤ (q : ℝ) →
          ∀ H : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ m] H →
          firstSlicePastIntegral Δ lam R i m K H (y, ω) =
            ∫ z, endpointPastTest Δ lam R i m H y z ∂η m q ω := by
  have hk := fun (m : ℕ) (q : ℚ) =>
    exists_local_supported_history_kernel_of_integral_versions Q Δ m i (q : ℝ)
      {x : Vec d | x i ≤ (q : ℝ) + 3 * R} K hprob (hlocal m q)
  choose η hfin heq using hk
  refine ⟨η, hfin, ae_all_iff.mpr fun m => ae_all_iff.mpr fun q => ?_⟩
  exact (heq m q).and (ae_all_endpoint_past_integral_eq_of_kernel_eq
    Q Δ hΔ lam R hlam hR m i (q : ℝ) K
      {x : Vec d | x i ≤ (q : ℝ) + 3 * R} (η m q) (heq m q))

/-- For an actual GMP coupling, supported diffusion and literal RN-bridge
scalar comparisons at the endpoint cutoff give a bounded version of the
literal past factor in the corrected half-space. Those two comparisons
remain analytic producer obligations; this is not a graph reduction. -/
theorem exists_firstSlicePastIntegral_local_version_of_gmp_scalar_comparison {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K) :
    let R := l / lam
    let i := Renewal.forceCoord hd
    let Δ := Renewal.regenDelta lam
    ∀ (y : Vec d),
    let v := y i - 7 * R;
      (∀ (ω ω' : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
        (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
        (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω) hω lam h0.le h1)
        (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω') hω' lam h0.le h1),
        (∀ y : Vec d, P (y, ω) = r.pathLaw y) →
        (∀ y : Vec d, P (y, ω') = r'.pathLaw y) →
        (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
        ∀ F : Path d → ℝ, Measurable F → BoundedRealTest F →
        (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') →
        (∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) →
        ∀ y : Vec d, y i ≤ v →
        (∫ γ, F γ ∂P (y, ω)) = (∫ γ, F γ ∂P (y, ω')) ∧
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω) =
          ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω') →
      ∀ (m : ℕ) (H : CoupledSample d → ℝ),
        Measurable[finiteHistorySigma Δ m] H → BoundedRealTest H →
        ∃ A : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] A ∧
          BoundedRealTest A ∧
          (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q.measure] A := by
  intro R i Δ y v hcompare m H hH hbH
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
  have hR : 0 < R := div_pos hl h0
  have hlocal := exists_firstSlicePastIntegral_local_version_of_origin_versions
    Q.measure K Δ hΔ lam R h0 hR i m H hH hbH y (by
      intro F hF hbF hsF
      exact exists_local_past_integral_version_of_gmp_scalar_comparison
        hd hΛ₀ Q lam l δ h0 h1 P K hK v hcompare m F hF hbF hsF)
  obtain ⟨C, hC⟩ := hbH
  obtain ⟨A, hA, hAb, heq⟩ := exists_bounded_firstSlicePastIntegral_local_version
    Q.measure K hK.1.1 Δ lam R i m H C hC y
      {x : Vec d | x i ≤ y i - 4 * R} hlocal
  exact ⟨A, hA, ⟨C, hAb⟩, heq⟩

/-- Joint measurability retains the moving endpoint ball in the literal test. -/
theorem measurable_endpointPastTest_joint {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (m : ℕ) (H : CoupledSample d → ℝ) (hH : Measurable H) :
    Measurable (fun p : Vec d × CoupledSample d =>
      endpointPastTest Δ lam R i m H p.1 p.2) := by
  have hE : MeasurableSet {p : Vec d × CoupledSample d |
      p.1 ∈ endpointBall i R (p.2.1 ((m : ℝ≥0) * Δ))} :=
    (measurableSet_endpointBall_pair i R).preimage
      (((continuous_eval_const _).measurable.comp measurable_snd.fst).prodMk measurable_fst)
  exact ((hH.indicator (measurableSet_forcedBitTrialEvent Δ lam R i m)).comp
    measurable_snd).indicator hE

/-- The literal past factor has a jointly measurable, globally bounded
version. Equality holds for every endpoint on one common origin environment
good set, using the actual a.e. probability qualifier on the coupled law. -/
theorem exists_measurable_bounded_firstSlicePastIntegral_version {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H) :
    ∃ A : Vec d × FieldPair d → ℝ, Measurable A ∧ BoundedRealTest A ∧
      ∀ᵐ ω ∂Q, ∀ y : Vec d,
        A (y, ω) = firstSlicePastIntegral Δ lam R i m K H (y, ω) := by
  let κ : Kernel (Vec d × FieldPair d) (CoupledSample d) :=
    (Probability.probabilityPart (originCoupledLaw K)).comap Prod.snd measurable_snd
  let : IsFiniteKernel κ := inferInstance
  let A : Vec d × FieldPair d → ℝ := fun p =>
    ∫ z, endpointPastTest Δ lam R i m H p.1 z ∂κ p
  have hF : Measurable (fun p : (Vec d × FieldPair d) × CoupledSample d =>
      endpointPastTest Δ lam R i m H p.1.1 p.2) :=
    Measurable.comp
      (g := fun p : Vec d × CoupledSample d => endpointPastTest Δ lam R i m H p.1 p.2)
      (f := fun p : (Vec d × FieldPair d) × CoupledSample d => (p.1.1, p.2))
      (measurable_endpointPastTest_joint Δ lam R i m H hH)
      (measurable_fst.fst.prodMk measurable_snd)
  have hA : Measurable A :=
    (hF.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  obtain ⟨C, hC⟩ := hbH
  have hC0 : 0 ≤ C := (abs_nonneg (H (0, fun _ => false))).trans (hC _)
  refine ⟨A, hA, ⟨C, fun p => ?_⟩, ?_⟩
  · change |∫ z, endpointPastTest Δ lam R i m H p.1 z
        ∂Probability.probabilityPart (originCoupledLaw K) p.2| ≤ C
    by_cases hp : originCoupledLaw K p.2 Set.univ = 1
    · let : IsProbabilityMeasure (originCoupledLaw K p.2) := ⟨hp⟩
      let : IsProbabilityMeasure (K (0, p.2)) := ⟨hp⟩
      rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
      exact (congrArg abs (integral_endpointPastTest Δ lam R i m K H p.1 p.2)).trans_le
        (abs_firstSlicePastIntegral_le Δ lam R i m K H C hC p.2 p.1)
    · rw [Probability.probabilityPart_apply, ite_eq_right hp, integral_zero_measure, abs_zero]
      exact hC0
  · filter_upwards [hprob] with ω hp
    let : IsProbabilityMeasure (originCoupledLaw K ω) := hp
    intro y
    change (∫ z, endpointPastTest Δ lam R i m H y z
      ∂Probability.probabilityPart (originCoupledLaw K) ω) = _
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
    exact integral_endpointPastTest Δ lam R i m K H y ω

/-- The successful-bridge comparison needs killed stopped-law equality only
at low starts. At high starts the literal RN bridge has zero contribution;
at low starts endpoint reweighting preserves both the endpoint denominator
and the measure, including its zero-mass branch. This conditional lemma
does not supply stopped diffusion locality. -/
theorem integral_supported_bridge_eq_of_low_killed_stopped_law_eq {d : ℕ}
    (Δ : ℝ≥0) (R v : ℝ) (i : Fin d) (P P' : QuenchedPathLaws d)
    (y : Vec d) (ω ω' : FieldPair d)
    (hkill : y i < v - 8 * R →
      (Renewal.killedSegmentLaw Δ R i P y ω).map (Diffusion.stopPathAt Δ) =
        (Renewal.killedSegmentLaw Δ R i P' y ω').map (Diffusion.stopPathAt Δ))
    (F : Path d → ℝ) (hF : Measurable F)
    (hsegment : ∀ γ γ' : Path d,
      (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ')
    (hsupport : ∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) :
    (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω) =
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P' y ω' := by
  by_cases hlow : y i < v - 8 * R
  · apply integral_eq_of_map_stopPathAt_eq Δ _ _ ?_ F hF hsegment
    exact map_endpoint_reweighted_eq_of_map_stopPathAt_eq Δ _ _
      (ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R y)) (hkill hlow)
  · rw [integral_killedBridgeMixture_eq_zero_of_past_barrier Δ R v i P y ω
      (not_lt.mp hlow) F hsupport,
      integral_killedBridgeMixture_eq_zero_of_past_barrier Δ R v i P' y ω'
        (not_lt.mp hlow) F hsupport]

/-- A local past version follows from the two distinct stopped-process
comparisons: supported diffusion integrals and low-start killed stopped laws.
This conditional consumer does not establish either comparison. -/
theorem exists_firstSlicePastIntegral_local_version_of_gmp_stopped_comparisons {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K) :
    let R := l / lam
    let i := Renewal.forceCoord hd
    let Δ := Renewal.regenDelta lam
    ∀ (y : Vec d),
    let v := y i - 7 * R;
      (∀ (ω ω' : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
        (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
        (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω) hω lam h0.le h1)
        (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω') hω' lam h0.le h1),
        (∀ y : Vec d, P (y, ω) = r.pathLaw y) →
        (∀ y : Vec d, P (y, ω') = r'.pathLaw y) →
        (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
        (∀ F : Path d → ℝ, Measurable F → BoundedRealTest F →
          (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') →
          (∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) →
          ∀ x : Vec d, x i ≤ v →
          (∫ γ, F γ ∂P (x, ω)) = ∫ γ, F γ ∂P (x, ω')) ∧
        (∀ x : Vec d, x i < v - 8 * R →
          (Renewal.killedSegmentLaw Δ R i P x ω).map (Diffusion.stopPathAt Δ) =
            (Renewal.killedSegmentLaw Δ R i P x ω').map (Diffusion.stopPathAt Δ))) →
      ∀ (m : ℕ) (H : CoupledSample d → ℝ),
        Measurable[finiteHistorySigma Δ m] H → BoundedRealTest H →
        ∃ A : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] A ∧
          BoundedRealTest A ∧
          (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q.measure] A := by
  intro R i Δ y v hcompare m H hH hbH
  apply exists_firstSlicePastIntegral_local_version_of_gmp_scalar_comparison
    hd hΛ₀ Q lam l δ h0 h1 hl P K hK y ?_ m H hH hbH
  intro ω ω' hω hω' r r' hr hr' hagree F hF hbF hsegment hsupport x hx
  obtain ⟨hdiff, hkill⟩ := hcompare ω ω' hω hω' r r' hr hr' hagree
  exact ⟨hdiff F hF hbF hsegment hsupport x hx,
    integral_supported_bridge_eq_of_low_killed_stopped_law_eq
      Δ R v i P P x ω ω' (hkill x) F hF hsegment hsupport⟩

end EndpointPast

section BoundedPastVersions

/-- Clipping a real representative uses only its own measurable observations. -/
def boundedRealVersion {α : Type*} (C : ℝ) (A : α → ℝ) : α → ℝ :=
  fun x => max (-C) (min C (A x))

theorem measurable_boundedRealVersion {α : Type*} [MeasurableSpace α]
    (C : ℝ) (A : α → ℝ) (hA : Measurable A) :
    Measurable (boundedRealVersion C A) :=
  measurable_const.max (measurable_const.min hA)

theorem abs_boundedRealVersion_le {α : Type*} (C : ℝ) (hC : 0 ≤ C)
    (A : α → ℝ) (x : α) : |boundedRealVersion C A x| ≤ C := by
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem boundedRealVersion_eq {α : Type*} (C : ℝ) (A : α → ℝ) (x : α)
    (hx : |A x| ≤ C) : boundedRealVersion C A x = A x := by
  exact (congrArg (max (-C)) (min_eq_right (abs_le.mp hx).2)).trans
    (max_eq_right (abs_le.mp hx).1)

/-- The original probability fibre gives the exact test bound, without any
regularity assumption on exceptional fibres of the coupled kernel. -/
theorem abs_integral_le_test_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (H : α → ℝ)
    (C : ℝ) (hC : ∀ z, |H z| ≤ C) : |∫ z, H z ∂μ| ≤ C := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := H) (C := C)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hC z))

/-- Clip one joint local representative while preserving its separately
specified origin and spatial-product equalities. No assertion on an
exceptional nonprobability fibre is used. -/
theorem exists_bounded_origin_and_joint_integral_version {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hprob0 : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (hprob : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), IsProbabilityMeasure (K p))
    (H : CoupledSample d → ℝ) (C : ℝ) (hC : ∀ z, |H z| ≤ C)
    (U : Set (Vec d))
    (hlocal : ∃ A : Vec d × FieldPair d → ℝ,
      Measurable[(borel (Vec d)).prod (localSigma U)] A ∧
      (∀ᵐ ω ∂Q, A (0, ω) = ∫ z, H z ∂K (0, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] fun p => ∫ z, H z ∂K p) :
    ∃ A : Vec d × FieldPair d → ℝ,
      Measurable[(borel (Vec d)).prod (localSigma U)] A ∧
      (∀ p, |A p| ≤ C) ∧
      (∀ᵐ ω ∂Q, A (0, ω) = ∫ z, H z ∂K (0, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] fun p => ∫ z, H z ∂K p := by
  obtain ⟨A, hA, hA0, hAp⟩ := hlocal
  have hC0 : 0 ≤ C := (abs_nonneg (H (0, fun _ => false))).trans (hC _)
  refine ⟨boundedRealVersion C A, measurable_const.max (measurable_const.min hA),
    abs_boundedRealVersion_le C hC0 A, ?_, ?_⟩
  · filter_upwards [hA0, hprob0] with ω hω hp
    let : IsProbabilityMeasure (K (0, ω)) := hp
    exact (boundedRealVersion_eq C A (0, ω)
      (hω ▸ abs_integral_le_test_bound (K (0, ω)) H C hC)).trans hω
  · filter_upwards [hAp, hprob] with p he hp
    let : IsProbabilityMeasure (K p) := hp
    exact (boundedRealVersion_eq C A p
      (he ▸ abs_integral_le_test_bound (K p) H C hC)).trans he

/-- Nonnegative tests admit local representatives in the literal interval
`[0,C]` at every input, with both original a.e. clauses intact. -/
theorem exists_nonnegative_origin_and_joint_integral_version {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hprob0 : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (hprob : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), IsProbabilityMeasure (K p))
    (H : CoupledSample d → ℝ) (C : ℝ) (hH0 : ∀ z, 0 ≤ H z)
    (hC : ∀ z, H z ≤ C) (U : Set (Vec d))
    (hlocal : ∃ A : Vec d × FieldPair d → ℝ,
      Measurable[(borel (Vec d)).prod (localSigma U)] A ∧
      (∀ᵐ ω ∂Q, A (0, ω) = ∫ z, H z ∂K (0, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] fun p => ∫ z, H z ∂K p) :
    ∃ A : Vec d × FieldPair d → ℝ,
      Measurable[(borel (Vec d)).prod (localSigma U)] A ∧
      (∀ p, 0 ≤ A p ∧ A p ≤ C) ∧
      (∀ᵐ ω ∂Q, A (0, ω) = ∫ z, H z ∂K (0, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] fun p => ∫ z, H z ∂K p := by
  have hbound : ∀ z, |H z| ≤ C := fun z => by rw [abs_of_nonneg (hH0 z)]; exact hC z
  obtain ⟨A, hA, hAb, hA0, hAp⟩ :=
    exists_bounded_origin_and_joint_integral_version Q K hprob0 hprob H C hbound U hlocal
  have hC0 : 0 ≤ C := (hH0 (0, fun _ => false)).trans (hC _)
  refine ⟨fun p => max 0 (A p), measurable_const.max hA,
    fun p => ⟨le_max_left _ _, max_le hC0 (abs_le.mp (hAb p)).2⟩, ?_, ?_⟩
  · filter_upwards [hA0] with ω hω
    rw [hω, max_eq_right (integral_nonneg hH0)]
  · filter_upwards [hAp] with p hp
    rw [hp, max_eq_right (integral_nonneg hH0)]

/-- Bounded normalization composes with the existing exact half-space
version property; it supplies no producer of that locality property. -/
theorem exists_bounded_past_halfSpace_version {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hprob0 : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (hprob : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), IsProbabilityMeasure (K p))
    (Δ : ℝ≥0) (i : Fin d) (R : ℝ) (hpast : HasPastHalfSpaceVersions Q Δ i R K)
    (m : ℕ) (hm : 1 ≤ m) (v : ℝ) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma Δ m] H)
    (C : ℝ) (hC : ∀ z, |H z| ≤ C)
    (hs : ∀ z, z ∉ pastBelow Δ m i v → H z = 0) :
    ∃ A : Vec d × FieldPair d → ℝ,
      Measurable[(borel (Vec d)).prod (localSigma {x : Vec d | x i ≤ v + 3 * R})] A ∧
      (∀ p, |A p| ≤ C) ∧
      (∀ᵐ ω ∂Q, A (0, ω) = ∫ z, H z ∂K (0, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] fun p => ∫ z, H z ∂K p := by
  apply exists_bounded_origin_and_joint_integral_version Q K hprob0 hprob H C hC
    {x : Vec d | x i ≤ v + 3 * R}
  apply hpast m hm v H hH ⟨C, hC⟩
  intro z hz
  by_contra hn
  exact hz (hs z hn)

/-- Any supplied countable family of local versions shares one origin good
set and one spatial-product good set. Bounds and local regions may vary
with the index, which can include mesh and finite-history indices. -/
theorem exists_countable_bounded_origin_and_joint_integral_versions {d : ℕ}
    {J : Type*} [Countable J] (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hprob0 : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (hprob : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), IsProbabilityMeasure (K p))
    (H : J → CoupledSample d → ℝ) (C : J → ℝ)
    (hC : ∀ j z, |H j z| ≤ C j) (U : J → Set (Vec d))
    (hlocal : ∀ j, ∃ A : Vec d × FieldPair d → ℝ,
      Measurable[(borel (Vec d)).prod (localSigma (U j))] A ∧
      (∀ᵐ ω ∂Q, A (0, ω) = ∫ z, H j z ∂K (0, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] fun p => ∫ z, H j z ∂K p) :
    ∃ A : J → Vec d × FieldPair d → ℝ,
      (∀ j, Measurable[(borel (Vec d)).prod (localSigma (U j))] (A j)) ∧
      (∀ j p, |A j p| ≤ C j) ∧
      (∀ᵐ ω ∂Q, ∀ j, A j (0, ω) = ∫ z, H j z ∂K (0, ω)) ∧
      (∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), ∀ j, A j p = ∫ z, H j z ∂K p) := by
  choose A hA hb h0 hp using fun j =>
    exists_bounded_origin_and_joint_integral_version Q K hprob0 hprob
      (H j) (C j) (hC j) (U j) (hlocal j)
  exact ⟨A, hA, hb, ae_all_iff.mpr h0, ae_all_iff.mpr hp⟩

/-- Signed addition preserves the actual integral versions. The probability
assumptions are used only to justify addition of the Bochner integrals. -/
theorem origin_and_joint_integral_version_add {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hprob0 : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (hprob : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), IsProbabilityMeasure (K p))
    (H G : CoupledSample d → ℝ) (hH : Measurable H) (hG : Measurable G)
    (C D : ℝ) (hC : ∀ z, |H z| ≤ C) (hD : ∀ z, |G z| ≤ D)
    (U : Set (Vec d)) (A B : Vec d × FieldPair d → ℝ)
    (hA : Measurable[(borel (Vec d)).prod (localSigma U)] A)
    (hB : Measurable[(borel (Vec d)).prod (localSigma U)] B)
    (hAb : ∀ p, |A p| ≤ C) (hBb : ∀ p, |B p| ≤ D)
    (hA0 : ∀ᵐ ω ∂Q, A (0, ω) = ∫ z, H z ∂K (0, ω))
    (hB0 : ∀ᵐ ω ∂Q, B (0, ω) = ∫ z, G z ∂K (0, ω))
    (hAp : A =ᵐ[((volume : Measure (Vec d)).prod Q)] fun p => ∫ z, H z ∂K p)
    (hBp : B =ᵐ[((volume : Measure (Vec d)).prod Q)] fun p => ∫ z, G z ∂K p) :
    Measurable[(borel (Vec d)).prod (localSigma U)] (fun p => A p + B p) ∧
      (∀ p, |A p + B p| ≤ C + D) ∧
      (∀ᵐ ω ∂Q, A (0, ω) + B (0, ω) = ∫ z, H z + G z ∂K (0, ω)) ∧
      (fun p => A p + B p) =ᵐ[((volume : Measure (Vec d)).prod Q)]
        fun p => ∫ z, H z + G z ∂K p := by
  refine ⟨hA.add hB, fun p => (abs_add_le _ _).trans (add_le_add (hAb p) (hBb p)), ?_, ?_⟩
  · filter_upwards [hA0, hB0, hprob0] with ω hω hω' hp
    let : IsProbabilityMeasure (K (0, ω)) := hp
    rw [hω, hω', integral_add
      (integrable_of_bounded _ H hH ⟨C, hC⟩) (integrable_of_bounded _ G hG ⟨D, hD⟩)]
  · filter_upwards [hAp, hBp, hprob] with p he he' hp
    let : IsProbabilityMeasure (K p) := hp
    rw [he, he', integral_add
      (integrable_of_bounded _ H hH ⟨C, hC⟩) (integrable_of_bounded _ G hG ⟨D, hD⟩)]

/-- Multiplication by any signed scalar preserves the exact local versions
and multiplies the uniform bound by its absolute value. -/
theorem origin_and_joint_integral_version_const_mul {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (H : CoupledSample d → ℝ) (c C : ℝ) (U : Set (Vec d))
    (A : Vec d × FieldPair d → ℝ)
    (hA : Measurable[(borel (Vec d)).prod (localSigma U)] A)
    (hAb : ∀ p, |A p| ≤ C)
    (hA0 : ∀ᵐ ω ∂Q, A (0, ω) = ∫ z, H z ∂K (0, ω))
    (hAp : A =ᵐ[((volume : Measure (Vec d)).prod Q)] fun p => ∫ z, H z ∂K p) :
    Measurable[(borel (Vec d)).prod (localSigma U)] (fun p => c * A p) ∧
      (∀ p, |c * A p| ≤ |c| * C) ∧
      (∀ᵐ ω ∂Q, c * A (0, ω) = ∫ z, c * H z ∂K (0, ω)) ∧
      (fun p => c * A p) =ᵐ[((volume : Measure (Vec d)).prod Q)]
        fun p => ∫ z, c * H z ∂K p := by
  refine ⟨measurable_const.mul hA, fun p => ?_, ?_, ?_⟩
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hAb p) (abs_nonneg c)
  · filter_upwards [hA0] with ω hω
    rw [hω, integral_const_mul]
  · filter_upwards [hAp] with p hp
    rw [hp, integral_const_mul]

/-- Countably many scalar integral identities suffice for a bounded
pointwise limit. This is used separately with the origin and product measures. -/
theorem ae_integral_eq_limsup_of_bounded_versions {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (K : α → Measure β)
    (hprob : ∀ᵐ p ∂μ, IsProbabilityMeasure (K p))
    (H : ℕ → β → ℝ) (F : β → ℝ) (hH : ∀ n, Measurable (H n))
    (C : ℝ) (hC : ∀ n z, |H n z| ≤ C)
    (hlim : ∀ z, Filter.Tendsto (fun n => H n z) Filter.atTop (nhds (F z)))
    (A : ℕ → α → ℝ)
    (hA : ∀ n, A n =ᵐ[μ] fun p => ∫ z, H n z ∂K p) :
    (fun p => Filter.limsup (fun n => A n p) Filter.atTop) =ᵐ[μ]
      fun p => ∫ z, F z ∂K p := by
  filter_upwards [ae_all_iff.mpr hA, hprob] with p hp hpK
  let : IsProbabilityMeasure (K p) := hpK
  have ht := tendsto_integral_of_dominated_convergence (μ := K p) (fun _ => C)
    (fun n => (hH n).aestronglyMeasurable) (integrable_const C)
    (fun n => Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hC n z)
    (Filter.Eventually.of_forall hlim)
  have he : (fun n => A n p) = fun n => ∫ z, H n z ∂K p := funext hp
  rw [he]
  exact ht.limsup_eq

/-- Uniformly bounded pointwise limits admit a globally bounded local
representative. A measurable limsup is clipped only on exceptional inputs;
dominated convergence identifies it on each of the two genuine a.e. sets. -/
theorem exists_origin_and_joint_integral_version_of_bounded_pointwise_limit {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hprob0 : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (hprob : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), IsProbabilityMeasure (K p))
    (H : ℕ → CoupledSample d → ℝ) (F : CoupledSample d → ℝ)
    (hH : ∀ n, Measurable (H n)) (C : ℝ) (hC : ∀ n z, |H n z| ≤ C)
    (hlim : ∀ z, Filter.Tendsto (fun n => H n z) Filter.atTop (nhds (F z)))
    (U : Set (Vec d))
    (hlocal : ∀ n, ∃ A : Vec d × FieldPair d → ℝ,
      Measurable[(borel (Vec d)).prod (localSigma U)] A ∧
      (∀ᵐ ω ∂Q, A (0, ω) = ∫ z, H n z ∂K (0, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] fun p => ∫ z, H n z ∂K p) :
    ∃ A : Vec d × FieldPair d → ℝ,
      Measurable[(borel (Vec d)).prod (localSigma U)] A ∧
      (∀ p, |A p| ≤ C) ∧
      (∀ᵐ ω ∂Q, A (0, ω) = ∫ z, F z ∂K (0, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] fun p => ∫ z, F z ∂K p := by
  choose A hA hA0 hAp using hlocal
  have hFC : ∀ z, |F z| ≤ C := fun z =>
    le_of_tendsto (hlim z).abs (Filter.Eventually.of_forall fun n => hC n z)
  apply exists_bounded_origin_and_joint_integral_version Q K hprob0 hprob F C hFC U
  exact ⟨fun p => Filter.limsup (fun n => A n p) Filter.atTop,
    Measurable.limsup hA,
    ae_integral_eq_limsup_of_bounded_versions Q (fun ω => K (0, ω)) hprob0
      H F hH C hC hlim (fun n ω => A n (0, ω)) hA0,
    ae_integral_eq_limsup_of_bounded_versions ((volume : Measure (Vec d)).prod Q)
      K hprob H F hH C hC hlim A hAp⟩

/-- The limiting history test retains its exact measurable space, bound,
and literal closed past support. The cutoff is fixed throughout the limit. -/
theorem measurable_supported_bounded_pointwise_limit {d : ℕ}
    (Δ : ℝ≥0) (m : ℕ) (i : Fin d) (v : ℝ)
    (H : ℕ → CoupledSample d → ℝ) (F : CoupledSample d → ℝ)
    (hH : ∀ n, Measurable[finiteHistorySigma Δ m] (H n))
    (C : ℝ) (hC : ∀ n z, |H n z| ≤ C)
    (hs : ∀ n z, z ∉ pastBelow Δ m i v → H n z = 0)
    (hlim : ∀ z, Filter.Tendsto (fun n => H n z) Filter.atTop (nhds (F z))) :
    Measurable[finiteHistorySigma Δ m] F ∧ (∀ z, |F z| ≤ C) ∧
      (∀ z, z ∉ pastBelow Δ m i v → F z = 0) := by
  refine ⟨?_,
    fun z => le_of_tendsto (hlim z).abs (Filter.Eventually.of_forall fun n => hC n z), ?_⟩
  · let : MeasurableSpace (CoupledSample d) := finiteHistorySigma Δ m
    exact measurable_of_tendsto_metrizable hH (tendsto_pi_nhds.mpr hlim)
  · intro z hz
    have hzero : Filter.Tendsto (fun n => H n z) Filter.atTop (nhds (0 : ℝ)) := by
      simpa only [hs _ z hz] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
    exact tendsto_nhds_unique (hlim z) hzero

/-- Both literal endpoint indicators preserve nonnegativity. -/
theorem nonneg_endpointPastTest {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (m : ℕ) (H : CoupledSample d → ℝ) (hH : ∀ z, 0 ≤ H z)
    (y : Vec d) (z : CoupledSample d) : 0 ≤ endpointPastTest Δ lam R i m H y z := by
  exact Set.indicator_nonneg (fun z _ =>
    Set.indicator_nonneg (fun z _ => hH z) z) z

/-- Nonnegative endpoint factors have representatives in `[0,C]` everywhere,
including environments where the original kernel is not a probability law. -/
theorem exists_nonnegative_firstSlicePastIntegral_local_version {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (C : ℝ) (hH0 : ∀ z, 0 ≤ H z)
    (hC : ∀ z, H z ≤ C) (y : Vec d) (U : Set (Vec d))
    (hlocal : ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q] A) :
    ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧
      (∀ ω, 0 ≤ A ω ∧ A ω ≤ C) ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q] A := by
  have hbound : ∀ z, |H z| ≤ C := fun z => by rw [abs_of_nonneg (hH0 z)]; exact hC z
  obtain ⟨A, hA, hAb, he⟩ := exists_bounded_firstSlicePastIntegral_local_version
    Q K hprob Δ lam R i m H C hbound y U hlocal
  have hC0 : 0 ≤ C := (hH0 (0, fun _ => false)).trans (hC _)
  refine ⟨fun ω => max 0 (A ω), measurable_const.max hA,
    fun ω => ⟨le_max_left _ _, max_le hC0 (abs_le.mp (hAb ω)).2⟩, ?_⟩
  filter_upwards [he] with ω hω
  have hn : 0 ≤ firstSlicePastIntegral Δ lam R i m K H (y, ω) := by
    rw [← integral_endpointPastTest]
    exact integral_nonneg (nonneg_endpointPastTest Δ lam R i m H hH0 y)
  rw [← hω, max_eq_right hn]

/-- Bounded local endpoint representatives can be integrated against any
integrable signed environment weight. The weighted literal factor has the
same Bochner integral; localSigma measurability is retained explicitly. -/
theorem exists_integrable_weighted_firstSlicePastIntegral_local_version {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q] (K : CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (C : ℝ) (hC : ∀ z, |H z| ≤ C)
    (y : Vec d) (U : Set (Vec d)) (w : FieldPair d → ℝ) (hw : Integrable w Q)
    (hlocal : ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q] A) :
    ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧
      (∀ ω, |A ω| ≤ C) ∧ Integrable A Q ∧
      Integrable (fun ω => w ω * A ω) Q ∧
      Integrable (fun ω => w ω * firstSlicePastIntegral Δ lam R i m K H (y, ω)) Q ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q] A ∧
      (∫ ω, w ω * firstSlicePastIntegral Δ lam R i m K H (y, ω) ∂Q) =
        ∫ ω, w ω * A ω ∂Q := by
  obtain ⟨A, hA, hAb, he⟩ := exists_bounded_firstSlicePastIntegral_local_version
    Q K hprob Δ lam R i m H C hC y U hlocal
  have hAm : Measurable A := hA.mono (Probability.localSigma_le_borel U) le_rfl
  have hAi : Integrable A Q := integrable_of_bounded Q A hAm ⟨C, hAb⟩
  have hwi : Integrable (fun ω => w ω * A ω) Q :=
    hw.mul_bdd hAm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using hAb ω)
  have hwe : (fun ω => w ω * firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q]
      fun ω => w ω * A ω := he.mono fun ω hω => congrArg (w ω * ·) hω
  exact ⟨A, hA, hAb, hAi, hwi, hwi.congr hwe.symm, he, integral_congr_ae hwe⟩

end BoundedPastVersions

section EndpointFubini

/-- The literal signed past factor is integrable on all endpoints and original
fields. The finite-integral estimate comes from the moving Euclidean endpoint
ball under the actual annealed probability law, rather than a uniform bound
integrated over the infinite spatial volume. -/
theorem integrable_firstSlicePastIntegral {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H) :
    Integrable (firstSlicePastIntegral Δ lam R i m K H)
      ((volume : Measure (Vec d)).prod Q) := by
  obtain ⟨A, hA, hbA, he⟩ := exists_measurable_bounded_firstSlicePastIntegral_version
    Q K hK.1 Δ lam R i m H hH hbH
  have hep : A =ᵐ[((volume : Measure (Vec d)).prod Q)]
      firstSlicePastIntegral Δ lam R i m K H := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Vec d))) (ν := Q)).ae he] with p hp
    exact hp p.1
  let μ := annealedCoupledLaw Q K
  let : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q K hK
  let X : FieldPair d × CoupledSample d → Vec d := fun q => q.2.1 ((m : ℝ≥0) * Δ)
  have hX : Measurable X := (continuous_eval_const _).measurable.comp measurable_snd.fst
  let G : CoupledSample d → ℝ := (forcedBitTrialEvent Δ lam R i m).indicator H
  have hG : Measurable G := hH.indicator (measurableSet_forcedBitTrialEvent Δ lam R i m)
  obtain ⟨C, hC⟩ := hbH
  have hC0 : 0 ≤ C := (abs_nonneg (H (0, fun _ => false))).trans (hC _)
  have hGb : ∀ z, |G z| ≤ C := by
    intro z
    by_cases hz : z ∈ forcedBitTrialEvent Δ lam R i m
    · simpa only [G, Set.indicator_of_mem hz] using hC z
    · simpa only [G, Set.indicator_of_notMem hz, abs_zero] using hC0
  let J : (FieldPair d × CoupledSample d) × Vec d → ℝ := fun q =>
    (endpointBall i R (X q.1)).indicator (fun _ => |G q.1.2|) q.2
  have hJi : Integrable J (μ.prod volume) :=
    integrable_endpointBall_indicator μ i R hR X hX
      (fun q => |G q.1.2|)
      (by simpa only [Real.norm_eq_abs, Function.comp_apply] using (hG.comp measurable_fst.snd).norm)
      ⟨C, fun q => by simpa only [abs_abs] using hGb q.1.2⟩
  have hsection : ∀ y : Vec d, Integrable (fun ω => A (y, ω)) Q :=
    fun y => integrable_of_bounded Q _ (hA.comp measurable_prodMk_left)
      (by obtain ⟨B, hB⟩ := hbA; exact ⟨B, fun ω => hB (y, ω)⟩)
  have hbound : ∀ y : Vec d, (∫ ω, ‖A (y, ω)‖ ∂Q) ≤ ∫ q, J (q, y) ∂μ := by
    intro y
    have hset : MeasurableSet {q : FieldPair d × CoupledSample d |
        y ∈ endpointBall i R (X q)} :=
      (measurableSet_endpointBall_pair i R).preimage (hX.prodMk measurable_const)
    have hJm : Measurable (fun q => J (q, y)) := by
      have hm : Measurable (fun q : FieldPair d × CoupledSample d => |G q.2|) := by
        simpa only [Real.norm_eq_abs, Function.comp_apply] using (hG.comp measurable_snd).norm
      exact hm.indicator hset
    have hJb : ∀ q, |J (q, y)| ≤ C := by
      intro q
      by_cases hy : y ∈ endpointBall i R (X q)
      · simpa only [J, Set.indicator_of_mem hy, abs_abs] using hGb q.2
      · simpa only [J, Set.indicator_of_notMem hy, abs_zero] using hC0
    rw [integral_annealedCoupledLaw Q K hK _ hJm ⟨C, hJb⟩]
    have hiJ : Integrable (fun ω => ∫ z, J ((ω, z), y) ∂K (0, ω)) Q := by
      have hi := integrable_of_bounded μ _ hJm ⟨C, hJb⟩
      have hi' := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi |>.2
      apply hi'.congr
      filter_upwards [hK.1] with ω hp
      let : IsProbabilityMeasure (originCoupledLaw K ω) := hp
      rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z =>
        Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => abs_nonneg _) y)
    apply integral_mono_ae (hsection y).norm hiJ
    filter_upwards [he, hK.1] with ω hω hp
    let : IsProbabilityMeasure (K (0, ω)) := hp
    rw [hω y, ← integral_endpointPastTest]
    calc
      ‖∫ z, endpointPastTest Δ lam R i m H y z ∂K (0, ω)‖ ≤
          ∫ z, ‖endpointPastTest Δ lam R i m H y z‖ ∂K (0, ω) :=
        norm_integral_le_integral_norm _
      _ = ∫ z, J ((ω, z), y) ∂K (0, ω) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          by_cases hy : y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))
          · have hz : z ∈ {z : CoupledSample d |
                y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))} := hy
            simp only [endpointPastTest, G, J, X, Set.indicator_of_mem hy,
              Set.indicator_of_mem hz, Real.norm_eq_abs]
          · have hz : z ∉ {z : CoupledSample d |
                y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))} := hy
            simp only [endpointPastTest, J, X, Set.indicator_of_notMem hy,
              Set.indicator_of_notMem hz, norm_zero]
  have hAi : Integrable A ((volume : Measure (Vec d)).prod Q) := by
    apply (integrable_prod_iff hA.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hsection, ?_⟩
    apply Integrable.mono' hJi.integral_prod_right
      hA.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hbound y
  exact hAi.congr hep

/-- Multiplying by a signed bounded measurable joint endpoint/environment
test preserves the genuine whole-space integrability of the past factor. -/
theorem integrable_firstSlicePastIntegral_mul {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B) :
    Integrable (fun p => firstSlicePastIntegral Δ lam R i m K H p * B p)
      ((volume : Measure (Vec d)).prod Q) := by
  obtain ⟨C, hC⟩ := hbB
  exact (integrable_firstSlicePastIntegral Q K hK Δ lam R hR i m H hH hbH).mul_bdd
    hB.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using hC p)

/-- Endpoint/environment Fubini for the literal signed factor. Both iterated
integrals are Bochner integrable; the spatial measure is unrestricted volume. -/
theorem firstSlicePastIntegral_mul_fubini {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B) :
    Integrable (fun y => ∫ ω, firstSlicePastIntegral Δ lam R i m K H (y, ω) *
      B (y, ω) ∂Q) volume ∧
    Integrable (fun ω => ∫ y, firstSlicePastIntegral Δ lam R i m K H (y, ω) *
      B (y, ω)) Q ∧
    (∫ y, ∫ ω, firstSlicePastIntegral Δ lam R i m K H (y, ω) * B (y, ω) ∂Q) =
      ∫ ω, (∫ y, firstSlicePastIntegral Δ lam R i m K H (y, ω) * B (y, ω)) ∂Q := by
  have hi := integrable_firstSlicePastIntegral_mul Q K hK Δ lam R hR i m H hH hbH B hB hbB
  exact ⟨hi.integral_prod_left, hi.integral_prod_right, integral_integral_swap hi⟩

/-- A bounded signed environment observable can be included in the endpoint
Fubini formula. In applications its measurability follows from its actual
local joint-field sigma algebra. -/
theorem weighted_firstSlicePastIntegral_fubini {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H)
    (F : FieldPair d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B) :
    Integrable (fun p => F p.2 * firstSlicePastIntegral Δ lam R i m K H p * B p)
      ((volume : Measure (Vec d)).prod Q) ∧
    (∫ y, ∫ ω, F ω * firstSlicePastIntegral Δ lam R i m K H (y, ω) * B (y, ω) ∂Q) =
      ∫ ω, F ω * (∫ y, firstSlicePastIntegral Δ lam R i m K H (y, ω) * B (y, ω)) ∂Q := by
  have hF' : Measurable (fun p : Vec d × FieldPair d => F p.2) := hF.comp measurable_snd
  have hbF' : BoundedRealTest (fun p : Vec d × FieldPair d => F p.2) := by
    obtain ⟨C, hC⟩ := hbF
    exact ⟨C, fun p => hC p.2⟩
  have hi := integrable_firstSlicePastIntegral_mul Q K hK Δ lam R hR i m H hH hbH
    (fun p => F p.2 * B p) (hF'.mul hB) (bounded_mul hbF' hbB)
  have hi' : Integrable (fun p => F p.2 * firstSlicePastIntegral Δ lam R i m K H p * B p)
      ((volume : Measure (Vec d)).prod Q) := by
    convert hi using 1
    funext p
    ring
  refine ⟨hi', (integral_integral_swap hi').trans ?_⟩
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    simpa only [mul_assoc] using
      (integral_const_mul (F ω)
        (fun y => firstSlicePastIntegral Δ lam R i m K H (y, ω) * B (y, ω)))

/-- A jointly measurable integrable representative and its moving local
sections refer to the same literal past factor. Locality is a separate
conditional input: ambient joint measurability alone supplies no half-space
information. The original fields and the exact `yᵢ - 4R` cutoff are retained. -/
theorem exists_joint_integrable_firstSlicePastIntegral_version_with_local_sections {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable H)
    (C : ℝ) (hC : ∀ z, |H z| ≤ C)
    (hlocal : ∀ y : Vec d, ∃ a : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q] a) :
    ∃ A : Vec d × FieldPair d → ℝ, Measurable A ∧
      (∀ p, |A p| ≤ C) ∧ Integrable A ((volume : Measure (Vec d)).prod Q) ∧
      (∀ᵐ ω ∂Q, ∀ y : Vec d, A (y, ω) = firstSlicePastIntegral Δ lam R i m K H (y, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] firstSlicePastIntegral Δ lam R i m K H ∧
      ∀ y : Vec d, ∃ a : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
        (∀ ω, |a ω| ≤ C) ∧ Integrable a Q ∧
        (fun ω => A (y, ω)) =ᵐ[Q] a := by
  obtain ⟨A, hA, _, he⟩ := exists_measurable_bounded_firstSlicePastIntegral_version
    Q K hK.1 Δ lam R i m H hH ⟨C, hC⟩
  let B := boundedRealVersion C A
  have hC0 : 0 ≤ C := (abs_nonneg (H (0, fun _ => false))).trans (hC _)
  have hB : Measurable B := measurable_boundedRealVersion C A hA
  have hBe : ∀ᵐ ω ∂Q, ∀ y : Vec d,
      B (y, ω) = firstSlicePastIntegral Δ lam R i m K H (y, ω) := by
    filter_upwards [he, hK.1] with ω hω hp
    let : IsProbabilityMeasure (K (0, ω)) := hp
    intro y
    exact (boundedRealVersion_eq C A (y, ω)
      ((congrArg abs (hω y)).trans_le
        (abs_firstSlicePastIntegral_le Δ lam R i m K H C hC ω y))).trans (hω y)
  have hBp : B =ᵐ[((volume : Measure (Vec d)).prod Q)]
      firstSlicePastIntegral Δ lam R i m K H := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Vec d))) (ν := Q)).ae hBe] with p hp
    exact hp p.1
  refine ⟨B, hB, abs_boundedRealVersion_le C hC0 A,
    (integrable_firstSlicePastIntegral Q K hK Δ lam R hR i m H hH ⟨C, hC⟩).congr hBp.symm,
    hBe, hBp, ?_⟩
  intro y
  obtain ⟨a, ha, hab, hae⟩ := exists_bounded_firstSlicePastIntegral_local_version
    Q K hK.1 Δ lam R i m H C hC y {x : Vec d | x i ≤ y i - 4 * R} (hlocal y)
  refine ⟨a, ha, hab,
    integrable_of_bounded Q a (ha.mono (Probability.localSigma_le_borel _) le_rfl) ⟨C, hab⟩, ?_⟩
  filter_upwards [hBe, hae] with ω hω haω
  exact (hω y).trans haω

/-- Countably many mesh/history tests share one environment event for every
endpoint, as well as a spatial-product event. The tests may be signed and
have different finite bounds; no uncountable intersection over endpoints is
used to create the common event. -/
theorem exists_countable_joint_integrable_firstSlicePastIntegral_versions {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d)
    (m : ℕ → ℕ) (H : ℕ → CoupledSample d → ℝ)
    (hH : ∀ k, Measurable (H k)) (hbH : ∀ k, BoundedRealTest (H k)) :
    ∃ A : ℕ → Vec d × FieldPair d → ℝ,
      (∀ k, Measurable (A k) ∧ BoundedRealTest (A k) ∧
        Integrable (A k) ((volume : Measure (Vec d)).prod Q)) ∧
      (∀ᵐ ω ∂Q, ∀ k y, A k (y, ω) = firstSlicePastIntegral Δ lam R i (m k) K (H k) (y, ω)) ∧
      ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
        ∀ k, A k p = firstSlicePastIntegral Δ lam R i (m k) K (H k) p := by
  have hversions := fun k => exists_measurable_bounded_firstSlicePastIntegral_version
    Q K hK.1 Δ lam R i (m k) (H k) (hH k) (hbH k)
  choose A hA hbA he using hversions
  have heall : ∀ᵐ ω ∂Q, ∀ k y,
      A k (y, ω) = firstSlicePastIntegral Δ lam R i (m k) K (H k) (y, ω) :=
    ae_all_iff.mpr he
  have hep : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
      ∀ k, A k p = firstSlicePastIntegral Δ lam R i (m k) K (H k) p := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Vec d))) (ν := Q)).ae heall] with p hp
    exact fun k => hp k p.1
  refine ⟨A, fun k => ⟨hA k, hbA k, ?_⟩, heall, hep⟩
  exact (integrable_firstSlicePastIntegral Q K hK Δ lam R hR i (m k) (H k) (hH k) (hbH k)).congr
    (hep.mono fun p hp => (hp k).symm)

/-- Decode moving local sections through the actual restricted stopped-history
kernels. Their identifying equality is required only under the original
`volume.prod Q` measure. The joint representative has a separate common
origin-environment event, so no origin assertion is extracted from a spatial
null set and no joint measurability is asserted for the chosen local sections. -/
theorem ae_local_sections_of_supported_endpoint_kernels {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q]
    (K : CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma Δ m] H) (C : ℝ) (hC : ∀ z, |H z| ≤ C)
    (η : (y : Vec d) → @ProbabilityTheory.Kernel (FieldPair d) (CoupledSample d)
      (localSigma {x : Vec d | x i ≤ y i - 4 * R}) inferInstance)
    (hη : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
      η p.1 p.2 = Measure.map (Probability.stoppedHistorySample Δ m)
        ((K (0, p.2)).restrict (pastBelow Δ m i (p.1 i - 7 * R))))
    (A : Vec d × FieldPair d → ℝ)
    (hA : ∀ᵐ ω ∂Q, ∀ y : Vec d,
      A (y, ω) = firstSlicePastIntegral Δ lam R i m K H (y, ω)) :
    ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ a : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
      (∀ ω, |a ω| ≤ C) ∧ Integrable a Q ∧
      (fun ω => A (y, ω)) =ᵐ[Q] a := by
  filter_upwards [Measure.ae_ae_of_ae_prod hη] with y hy
  have htest : Measurable (endpointPastTest Δ lam R i m H y) :=
    (measurable_endpointPastTest Δ hΔ lam R hR i m H hH y).mono
      (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hlocal : ∃ a : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q] a := by
    refine ⟨fun ω => ∫ z, endpointPastTest Δ lam R i m H y z ∂η y ω,
      (htest.stronglyMeasurable.integral_kernel (κ := η y)).measurable, ?_⟩
    filter_upwards [ae_all_endpoint_past_integral_eq_of_kernel_eq Q Δ hΔ
      lam R hlam hR m i (y i - 7 * R) K {x : Vec d | x i ≤ y i - 4 * R} (η y) hy]
      with ω hω
    exact hω y le_rfl H hH
  obtain ⟨a, ha, hab, hae⟩ := exists_bounded_firstSlicePastIntegral_local_version
    Q K hprob Δ lam R i m H C hC y {x : Vec d | x i ≤ y i - 4 * R} hlocal
  refine ⟨a, ha, hab,
    integrable_of_bounded Q a (ha.mono (Probability.localSigma_le_borel _) le_rfl) ⟨C, hab⟩, ?_⟩
  filter_upwards [hA, hae] with ω hω haω
  exact (hω y).trans haω

/-- The actual endpoint density is nonnegative, on every fibre. -/
theorem nonneg_firstSlicePastIntegral_one {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (K : CoupledQuenchedLaws d) (p : Vec d × FieldPair d) :
    0 ≤ firstSlicePastIntegral Δ lam R i m K (fun _ => 1) p := by
  rw [← integral_endpointPastTest Δ lam R i m K (fun _ => 1) p.1 p.2]
  exact integral_nonneg (nonneg_endpointPastTest Δ lam R i m (fun _ => 1)
    (fun _ => zero_le_one) p.1)

/-- A signed history factor is dominated by the actual endpoint density,
with the same history bound. The density retains both literal indicators. -/
theorem abs_firstSlicePastIntegral_le_density {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (K : CoupledQuenchedLaws d) (H : CoupledSample d → ℝ)
    (hH : Measurable H) (C : ℝ) (hC : ∀ z, |H z| ≤ C)
    (ω : FieldPair d) [IsProbabilityMeasure (K (0, ω))] (y : Vec d) :
    |firstSlicePastIntegral Δ lam R i m K H (y, ω)| ≤
      C * firstSlicePastIntegral Δ lam R i m K (fun _ => 1) (y, ω) := by
  have hm (G : CoupledSample d → ℝ) (hG : Measurable G) :
      Measurable (endpointPastTest Δ lam R i m G y) :=
    Measurable.comp
      (g := fun p : Vec d × CoupledSample d => endpointPastTest Δ lam R i m G p.1 p.2)
      (f := fun z : CoupledSample d => (y, z))
      (measurable_endpointPastTest_joint Δ lam R i m G hG)
      (measurable_const.prodMk measurable_id)
  have hi : Integrable (endpointPastTest Δ lam R i m H y) (K (0, ω)) :=
    integrable_of_bounded (K (0, ω)) _ (hm H hH)
      (bounded_endpointPastTest Δ lam R i m H ⟨C, hC⟩ y)
  have hi1 : Integrable (endpointPastTest Δ lam R i m (fun _ => 1) y) (K (0, ω)) :=
    integrable_of_bounded (K (0, ω)) _ (hm (fun _ => 1) measurable_const)
      (bounded_endpointPastTest Δ lam R i m (fun _ => 1) ⟨1, fun _ => by simp⟩ y)
  have hpoint : ∀ z, |endpointPastTest Δ lam R i m H y z| ≤
      C * endpointPastTest Δ lam R i m (fun _ => 1) y z := by
    intro z
    by_cases hy : z ∈ {w : CoupledSample d |
        y ∈ endpointBall i R (w.1 ((m : ℝ≥0) * Δ))}
    · by_cases hz : z ∈ forcedBitTrialEvent Δ lam R i m
      · simpa only [endpointPastTest, Set.indicator_of_mem hy,
          Set.indicator_of_mem hz, mul_one] using hC z
      · simp only [endpointPastTest, Set.indicator_of_mem hy,
          Set.indicator_of_notMem hz, abs_zero, mul_zero, le_refl]
    · simp only [endpointPastTest, Set.indicator_of_notMem hy, abs_zero, mul_zero, le_refl]
  calc
    |firstSlicePastIntegral Δ lam R i m K H (y, ω)| =
        |∫ z, endpointPastTest Δ lam R i m H y z ∂K (0, ω)| :=
      congrArg abs (integral_endpointPastTest Δ lam R i m K H y ω).symm
    _ ≤ ∫ z, |endpointPastTest Δ lam R i m H y z| ∂K (0, ω) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, C * endpointPastTest Δ lam R i m (fun _ => 1) y z ∂K (0, ω) :=
      integral_mono hi.abs (hi1.const_mul C) hpoint
    _ = C * firstSlicePastIntegral Δ lam R i m K (fun _ => 1) (y, ω) := by
      rw [integral_const_mul, integral_endpointPastTest]

/-- The original endpoint/environment measure weighted by the literal
first-slice density is finite. Its finite mass follows from the actual
annealed probability and moving Euclidean ball proved above. -/
theorem isFiniteMeasure_firstSlicePastIntegral_density {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ) :
    IsFiniteMeasure (((volume : Measure (Vec d)).prod Q).withDensity
      (fun p => ENNReal.ofReal (firstSlicePastIntegral Δ lam R i m K (fun _ => 1) p))) := by
  exact isFiniteMeasure_withDensity_ofReal
    (integrable_firstSlicePastIntegral Q K hK Δ lam R hR i m
      (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩).hasFiniteIntegral

/-- A measurable endpoint restriction of a signed factor has a finite integral
bounded by its mass under the actual endpoint density. -/
theorem integral_abs_firstSlicePastIntegral_restrict_le_density {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable H)
    (C : ℝ) (hC : ∀ z, |H z| ≤ C) (S : Set (Vec d × FieldPair d)) :
    Integrable (firstSlicePastIntegral Δ lam R i m K H)
      (((volume : Measure (Vec d)).prod Q).restrict S) ∧
    (∫ p in S, |firstSlicePastIntegral Δ lam R i m K H p|
      ∂((volume : Measure (Vec d)).prod Q)) ≤
      C * ∫ p in S, firstSlicePastIntegral Δ lam R i m K (fun _ => 1) p
        ∂((volume : Measure (Vec d)).prod Q) := by
  have hi := (integrable_firstSlicePastIntegral Q K hK Δ lam R hR i m H hH ⟨C, hC⟩).restrict (s := S)
  have hi1 := (integrable_firstSlicePastIntegral Q K hK Δ lam R hR i m
    (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩).restrict (s := S)
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  apply integral_mono_ae hi.abs (hi1.const_mul C)
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Vec d))) (ν := Q)).ae hK.1
  filter_upwards [ae_restrict_of_ae hp] with p hp
  let : IsProbabilityMeasure (K (0, p.2)) := hp
  exact abs_firstSlicePastIntegral_le_density Δ lam R i m K H hH C hC p.2 p.1

/-- Bounded history limits commute with the literal endpoint integral on
all endpoints of each probability fibre. No spatial exceptional set is used. -/
theorem tendsto_firstSlicePastIntegral_of_bounded_pointwise_limit {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (K : CoupledQuenchedLaws d) (H : ℕ → CoupledSample d → ℝ)
    (F : CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (C : ℝ) (hC : ∀ n z, |H n z| ≤ C)
    (hlim : ∀ z, Filter.Tendsto (fun n => H n z) Filter.atTop (nhds (F z)))
    (ω : FieldPair d) [IsProbabilityMeasure (K (0, ω))] (y : Vec d) :
    Filter.Tendsto (fun n => firstSlicePastIntegral Δ lam R i m K (H n) (y, ω))
      Filter.atTop (nhds (firstSlicePastIntegral Δ lam R i m K F (y, ω))) := by
  simp only [← integral_endpointPastTest]
  apply tendsto_integral_of_dominated_convergence (fun _ => C)
  · intro n
    exact ((measurable_endpointPastTest_joint Δ lam R i m (H n) (hH n)).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact integrable_const C
  · intro n
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using
        (abs_endpointPastTest_le Δ lam R i m (H n) y z).trans (hC n z)
  · apply Filter.Eventually.of_forall
    intro z
    by_cases hy : z ∈ {w : CoupledSample d |
        y ∈ endpointBall i R (w.1 ((m : ℝ≥0) * Δ))}
    · by_cases hz : z ∈ forcedBitTrialEvent Δ lam R i m
      · simpa only [endpointPastTest, Set.indicator_of_mem hy,
          Set.indicator_of_mem hz] using hlim z
      · simp only [endpointPastTest, Set.indicator_of_mem hy,
          Set.indicator_of_notMem hz]
        exact tendsto_const_nhds
    · simp only [endpointPastTest, Set.indicator_of_notMem hy]
      exact tendsto_const_nhds

/-- Bounded history approximations converge in signed L1 on unrestricted
endpoint volume times the original environment law. The integrable dominator
is twice the history bound times the genuine first-slice endpoint density. -/
theorem tendsto_integral_abs_sub_firstSlicePastIntegral {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : ℕ → CoupledSample d → ℝ) (F : CoupledSample d → ℝ)
    (hH : ∀ n, Measurable (H n)) (C : ℝ) (hC : ∀ n z, |H n z| ≤ C)
    (hlim : ∀ z, Filter.Tendsto (fun n => H n z) Filter.atTop (nhds (F z))) :
    Filter.Tendsto (fun n => ∫ p,
      |firstSlicePastIntegral Δ lam R i m K (H n) p -
        firstSlicePastIntegral Δ lam R i m K F p|
      ∂((volume : Measure (Vec d)).prod Q)) Filter.atTop (nhds 0) := by
  have hF : Measurable F := measurable_of_tendsto_metrizable hH (tendsto_pi_nhds.mpr hlim)
  have hFC : ∀ z, |F z| ≤ C := fun z =>
    le_of_tendsto (hlim z).abs (Filter.Eventually.of_forall fun n => hC n z)
  have hi n := integrable_firstSlicePastIntegral Q K hK Δ lam R hR i m
    (H n) (hH n) ⟨C, hC n⟩
  have hiF := integrable_firstSlicePastIntegral Q K hK Δ lam R hR i m F hF ⟨C, hFC⟩
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Vec d))) (ν := Q)).ae hK.1
  have ht := tendsto_integral_of_dominated_convergence
    (μ := ((volume : Measure (Vec d)).prod Q))
    (F := fun n p => |firstSlicePastIntegral Δ lam R i m K (H n) p -
      firstSlicePastIntegral Δ lam R i m K F p|) (f := fun _ => (0 : ℝ))
    (fun p => (2 * C) * firstSlicePastIntegral Δ lam R i m K (fun _ => 1) p)
    (fun n => by simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((hi n).sub hiF).norm.aestronglyMeasurable)
    ((integrable_firstSlicePastIntegral Q K hK Δ lam R hR i m
      (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩).const_mul (2 * C))
    (fun n => ?_) ?_
  · simpa only [integral_zero] using ht
  · filter_upwards [hp] with p hp
    let : IsProbabilityMeasure (K (0, p.2)) := hp
    rw [Real.norm_eq_abs, abs_abs]
    calc
      |firstSlicePastIntegral Δ lam R i m K (H n) p -
          firstSlicePastIntegral Δ lam R i m K F p| ≤
          |firstSlicePastIntegral Δ lam R i m K (H n) p| +
            |firstSlicePastIntegral Δ lam R i m K F p| := abs_sub _ _
      _ ≤ C * firstSlicePastIntegral Δ lam R i m K (fun _ => 1) p +
          C * firstSlicePastIntegral Δ lam R i m K (fun _ => 1) p :=
        add_le_add (abs_firstSlicePastIntegral_le_density Δ lam R i m K (H n) (hH n)
          C (hC n) p.2 p.1) (abs_firstSlicePastIntegral_le_density Δ lam R i m K F hF
          C hFC p.2 p.1)
      _ = _ := by ring
  · filter_upwards [hp] with p hp
    let : IsProbabilityMeasure (K (0, p.2)) := hp
    have ht := tendsto_firstSlicePastIntegral_of_bounded_pointwise_limit
      Δ lam R i m K H F hH C hC hlim p.2 p.1
    simpa only [sub_self, abs_zero] using (ht.sub_const (firstSlicePastIntegral Δ lam R i m K F p)).abs

/-- Signed bounded endpoint/environment pairings pass to the history limit.
In particular a signed environment weight can be included in `B`; the bound
is integrable under the original spatial-product measure. -/
theorem tendsto_integral_mul_firstSlicePastIntegral {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : ℕ → CoupledSample d → ℝ) (F : CoupledSample d → ℝ)
    (hH : ∀ n, Measurable (H n)) (C : ℝ) (hC : ∀ n z, |H n z| ≤ C)
    (hlim : ∀ z, Filter.Tendsto (fun n => H n z) Filter.atTop (nhds (F z)))
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B) :
    Filter.Tendsto (fun n => ∫ p, firstSlicePastIntegral Δ lam R i m K (H n) p * B p
      ∂((volume : Measure (Vec d)).prod Q)) Filter.atTop
      (nhds (∫ p, firstSlicePastIntegral Δ lam R i m K F p * B p
        ∂((volume : Measure (Vec d)).prod Q))) := by
  obtain ⟨D, hD⟩ := hbB
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Vec d))) (ν := Q)).ae hK.1
  apply tendsto_integral_of_dominated_convergence
    (fun p => (D * C) * firstSlicePastIntegral Δ lam R i m K (fun _ => 1) p)
  · intro n
    exact (integrable_firstSlicePastIntegral_mul Q K hK Δ lam R hR i m
      (H n) (hH n) ⟨C, hC n⟩ B hB ⟨D, hD⟩).aestronglyMeasurable
  · exact (integrable_firstSlicePastIntegral Q K hK Δ lam R hR i m
      (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩).const_mul (D * C)
  · intro n
    filter_upwards [hp] with p hp
    let : IsProbabilityMeasure (K (0, p.2)) := hp
    have hd := abs_firstSlicePastIntegral_le_density Δ lam R i m K (H n) (hH n)
      C (hC n) p.2 p.1
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (C * firstSlicePastIntegral Δ lam R i m K (fun _ => 1) p) * D :=
        mul_le_mul hd (hD p) (abs_nonneg _) ((abs_nonneg _).trans hd)
      _ = _ := by ring
  · filter_upwards [hp] with p hp
    let : IsProbabilityMeasure (K (0, p.2)) := hp
    exact (tendsto_firstSlicePastIntegral_of_bounded_pointwise_limit
      Δ lam R i m K H F hH C hC hlim p.2 p.1).mul tendsto_const_nhds

/-- Established moving local sections are closed under bounded finite-history
limits. Each endpoint keeps its single sigma algebra through the limit;
the resulting joint representative separately has a common all-endpoints
origin event and a spatial-product event. This consumes actual local sections,
not a claim that joint measurability establishes locality. -/
theorem exists_joint_integrable_local_firstSlicePastIntegral_version_of_limit {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : ℕ → CoupledSample d → ℝ) (F : CoupledSample d → ℝ)
    (hH : ∀ n, Measurable[finiteHistorySigma Δ m] (H n))
    (C : ℝ) (hC : ∀ n z, |H n z| ≤ C)
    (hlim : ∀ z, Filter.Tendsto (fun n => H n z) Filter.atTop (nhds (F z)))
    (hlocal : ∀ n (y : Vec d), ∃ a : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K (H n) (y, ω)) =ᵐ[Q] a) :
    ∃ A : Vec d × FieldPair d → ℝ, Measurable A ∧
      (∀ p, |A p| ≤ C) ∧ Integrable A ((volume : Measure (Vec d)).prod Q) ∧
      (∀ᵐ ω ∂Q, ∀ y : Vec d, A (y, ω) = firstSlicePastIntegral Δ lam R i m K F (y, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] firstSlicePastIntegral Δ lam R i m K F ∧
      ∀ y : Vec d, ∃ a : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
        (∀ ω, |a ω| ≤ C) ∧ Integrable a Q ∧
        (fun ω => A (y, ω)) =ᵐ[Q] a := by
  have hH' : ∀ n, Measurable (H n) := fun n =>
    (hH n).mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hF : Measurable F := measurable_of_tendsto_metrizable hH' (tendsto_pi_nhds.mpr hlim)
  have hFC : ∀ z, |F z| ≤ C := fun z =>
    le_of_tendsto (hlim z).abs (Filter.Eventually.of_forall fun n => hC n z)
  apply exists_joint_integrable_firstSlicePastIntegral_version_with_local_sections
    Q K hK Δ lam R hR i m F hF C hFC
  intro y
  choose a ha he using fun n => hlocal n y
  refine ⟨fun ω => Filter.limsup (fun n => a n ω) Filter.atTop, Measurable.limsup ha, ?_⟩
  filter_upwards [ae_all_iff.mpr he, hK.1] with ω hω hp
  let : IsProbabilityMeasure (K (0, ω)) := hp
  have heq : (fun n => a n ω) =
      (fun n => firstSlicePastIntegral Δ lam R i m K (H n) (y, ω)) :=
    funext fun n => (hω n).symm
  rw [heq]
  exact (tendsto_firstSlicePastIntegral_of_bounded_pointwise_limit
    Δ lam R i m K H F hH' C hC hlim ω y).limsup_eq.symm

/-- Countably many finite-history limit constructions retain one common
origin event for every endpoint, and one common spatial-product event.
The moving half-space is unchanged at every mesh/history index. -/
theorem exists_countable_joint_integrable_local_firstSlicePastIntegral_versions_of_limits
    {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ → ℕ)
    (H : ℕ → ℕ → CoupledSample d → ℝ) (F : ℕ → CoupledSample d → ℝ)
    (hH : ∀ k n, Measurable[finiteHistorySigma Δ (m k)] (H k n))
    (C : ℕ → ℝ) (hC : ∀ k n z, |H k n z| ≤ C k)
    (hlim : ∀ k z, Filter.Tendsto (fun n => H k n z) Filter.atTop (nhds (F k z)))
    (hlocal : ∀ k n (y : Vec d), ∃ a : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
      (fun ω => firstSlicePastIntegral Δ lam R i (m k) K (H k n) (y, ω)) =ᵐ[Q] a) :
    ∃ A : ℕ → Vec d × FieldPair d → ℝ,
      (∀ k, Measurable (A k) ∧ (∀ p, |A k p| ≤ C k) ∧
        Integrable (A k) ((volume : Measure (Vec d)).prod Q) ∧
        ∀ y : Vec d, ∃ a : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
          (∀ ω, |a ω| ≤ C k) ∧ Integrable a Q ∧
          (fun ω => A k (y, ω)) =ᵐ[Q] a) ∧
      (∀ᵐ ω ∂Q, ∀ k y, A k (y, ω) =
        firstSlicePastIntegral Δ lam R i (m k) K (F k) (y, ω)) ∧
      ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), ∀ k,
        A k p = firstSlicePastIntegral Δ lam R i (m k) K (F k) p := by
  have hv := fun k => exists_joint_integrable_local_firstSlicePastIntegral_version_of_limit
    Q K hK Δ lam R hR i (m k) (H k) (F k) (hH k) (C k) (hC k) (hlim k) (hlocal k)
  choose A hA hbA hiA he hp hl using hv
  exact ⟨A, fun k => ⟨hA k, hbA k, hiA k, hl k⟩,
    ae_all_iff.mpr he, ae_all_iff.mpr hp⟩

end EndpointFubini

section StoppedMesh

/-- The actual finite branch of a possibly infinite mesh selector. The test
retains the original sample, including its path and its coin record. -/
def meshBranchTest {α : Type*} (σ : α → ℕ∞) (H : ℕ → α → ℝ) (k : ℕ) : α → ℝ :=
  {z | σ z = (k : ℕ∞)}.indicator (H k)

/-- The selected observation is zero on the infinite branch. The branch at
zero is retained as an ordinary finite branch. -/
def stoppedMeshTest {α : Type*} (σ : α → ℕ∞) (H : ℕ → α → ℝ) (z : α) : ℝ :=
  if σ z = ⊤ then 0 else H (σ z).toNat z

/-- Truncate the actual branch partition, rather than the observation values. -/
def stoppedMeshPartialTest {α : Type*} (σ : α → ℕ∞) (H : ℕ → α → ℝ)
    (N : ℕ) (z : α) : ℝ :=
  ∑ k ∈ Finset.range N, meshBranchTest σ H k z

/-- A selected branch keeps precisely the history through its own mesh time. -/
theorem measurable_meshBranchTest_history {d : ℕ} (Δ : ℝ≥0)
    (σ : CoupledSample d → ℕ∞) (H : ℕ → CoupledSample d → ℝ)
    (hσ : ∀ k, MeasurableSet[finiteHistorySigma Δ k] {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable[finiteHistorySigma Δ k] (H k)) (k : ℕ) :
    Measurable[finiteHistorySigma Δ k] (meshBranchTest σ H k) :=
  (hH k).indicator (hσ k)

/-- Branch restriction commutes with retaining the literal stopped history;
in particular it cannot read the coin at the selected time. -/
theorem meshBranchTest_stoppedHistory {d : ℕ} (Δ : ℝ≥0)
    (σ : CoupledSample d → ℕ∞) (H : ℕ → CoupledSample d → ℝ)
    (hσ : ∀ k, MeasurableSet[finiteHistorySigma Δ k] {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable[finiteHistorySigma Δ k] (H k)) (k : ℕ)
    (z : CoupledSample d) :
    meshBranchTest σ H k (Probability.stoppedHistorySample Δ k z) =
      meshBranchTest σ H k z :=
  Probability.finiteHistory_test_stopped Δ k (meshBranchTest σ H k)
    (measurable_meshBranchTest_history Δ σ H hσ hH k) z

/-- Finite mesh selection is measurable in the prebridge history at the
truncation horizon. No future path or extra coin is introduced. -/
theorem measurable_stoppedMeshPartialTest_history {d : ℕ} (Δ : ℝ≥0)
    (σ : CoupledSample d → ℕ∞) (H : ℕ → CoupledSample d → ℝ)
    (hσ : ∀ k, MeasurableSet[finiteHistorySigma Δ k] {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable[finiteHistorySigma Δ k] (H k)) (N : ℕ) :
    Measurable[finiteHistorySigma Δ N] (stoppedMeshPartialTest σ H N) := by
  apply Finset.measurable_sum
  intro k hk
  exact (measurable_meshBranchTest_history Δ σ H hσ hH k).mono
    (finiteHistorySigma_mono Δ (Nat.le_of_lt (Finset.mem_range.mp hk))) le_rfl

/-- Exactly one finite branch contributes; no branch contributes at infinity. -/
theorem stoppedMeshPartialTest_eq {α : Type*} (σ : α → ℕ∞)
    (H : ℕ → α → ℝ) (N : ℕ) (z : α) :
    stoppedMeshPartialTest σ H N z =
      if σ z < (N : ℕ∞) then stoppedMeshTest σ H z else 0 := by
  classical
  cases hs : σ z using ENat.recTopCoe with
  | top => simp [stoppedMeshPartialTest, meshBranchTest, hs]
  | coe k =>
    simp only [stoppedMeshPartialTest, meshBranchTest, Set.indicator_apply,
      Set.mem_ofPred_eq, hs, ENat.natCast_inj, ENat.natCast_lt_natCast]
    by_cases hn : k < N
    · rw [ite_eq_left hn, Finset.sum_eq_single k]
      · simp only [stoppedMeshTest, hs, ENat.natCast_ne_top,
          ↓reduceIte, ENat.toNat_natCast]
      · intro j _ hk
        exact ite_eq_right (Ne.symm hk)
      · intro hk
        exact (hk (Finset.mem_range.mpr hn)).elim
    · rw [ite_eq_right hn]
      apply Finset.sum_eq_zero
      intro j hj
      exact ite_eq_right (fun heq : k = j => hn (heq.symm ▸ Finset.mem_range.mp hj))

/-- Disjoint branch selection preserves a uniform signed bound. -/
theorem abs_stoppedMeshPartialTest_le {α : Type*} (σ : α → ℕ∞)
    (H : ℕ → α → ℝ) (C : ℝ) (hC : 0 ≤ C) (hH : ∀ k z, |H k z| ≤ C)
    (N : ℕ) (z : α) : |stoppedMeshPartialTest σ H N z| ≤ C := by
  rw [stoppedMeshPartialTest_eq]
  split_ifs
  · unfold stoppedMeshTest
    split_ifs
    · exact (abs_zero).trans_le hC
    · exact hH _ z
  · exact (abs_zero).trans_le hC

/-- Truncations recover every finite selected observation, including time
zero, and converge to zero on the infinite branch. -/
theorem tendsto_stoppedMeshPartialTest {α : Type*} (σ : α → ℕ∞)
    (H : ℕ → α → ℝ) (z : α) :
    Filter.Tendsto (fun N => stoppedMeshPartialTest σ H N z)
      Filter.atTop (nhds (stoppedMeshTest σ H z)) := by
  by_cases ht : σ z = ⊤
  · simp only [stoppedMeshPartialTest_eq, ht, not_top_lt, ↓reduceIte,
      stoppedMeshTest]
    exact tendsto_const_nhds
  · apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_gt_atTop (σ z).toNat] with N hN
    have hlt : σ z < (N : ℕ∞) := by
      rw [← ENat.natCast_toNat ht, ENat.natCast_lt_natCast]
      exact hN
    rw [stoppedMeshPartialTest_eq, ite_eq_left hlt]

/-- Signed integrable weights commute with countable mesh selection. This
applies to the original quenched probability fibres as well as finite laws;
the infinite branch is already included in the selected test. -/
theorem tendsto_integral_mul_stoppedMeshPartialTest {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (σ : α → ℕ∞) (H : ℕ → α → ℝ)
    (hσ : ∀ k : ℕ, MeasurableSet {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable (H k)) (C : ℝ) (hC : 0 ≤ C)
    (hbH : ∀ k z, |H k z| ≤ C) (w : α → ℝ) (hw : Integrable w μ) :
    Filter.Tendsto (fun N => ∫ z, w z * stoppedMeshPartialTest σ H N z ∂μ)
      Filter.atTop (nhds (∫ z, w z * stoppedMeshTest σ H z ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun z => ‖w z‖ * C)
  · intro N
    exact hw.aestronglyMeasurable.mul
      (Finset.measurable_sum _ fun k _ => (hH k).indicator (hσ k)).aestronglyMeasurable
  · exact hw.norm.mul_const C
  · intro N
    exact Filter.Eventually.of_forall fun z => by
      rw [norm_mul, Real.norm_eq_abs (stoppedMeshPartialTest σ H N z)]
      exact mul_le_mul_of_nonneg_left
        (abs_stoppedMeshPartialTest_le σ H C hC hbH N z) (norm_nonneg _)
  · exact Filter.Eventually.of_forall fun z =>
      (tendsto_stoppedMeshPartialTest σ H z).const_mul (w z)

/-- A single branch preserves the same uniform signed bound. -/
theorem abs_meshBranchTest_le {α : Type*} (σ : α → ℕ∞)
    (H : ℕ → α → ℝ) (C : ℝ) (hC : 0 ≤ C) (hH : ∀ k z, |H k z| ≤ C)
    (k : ℕ) (z : α) : |meshBranchTest σ H k z| ≤ C := by
  classical
  unfold meshBranchTest
  by_cases hz : σ z = (k : ℕ∞)
  · rw [Set.indicator_of_mem (show z ∈ {z | σ z = (k : ℕ∞)} from hz)]
    exact hH k z
  · rw [Set.indicator_of_notMem (show z ∉ {z | σ z = (k : ℕ∞)} from hz), abs_zero]
    exact hC

/-- The full selected test is measurable, with its infinite branch fixed at
zero, whenever every finite branch event and observation is measurable. -/
theorem measurable_stoppedMeshTest {α : Type*} [MeasurableSpace α]
    (σ : α → ℕ∞) (H : ℕ → α → ℝ)
    (hσ : ∀ k : ℕ, MeasurableSet {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable (H k)) : Measurable (stoppedMeshTest σ H) := by
  apply measurable_of_tendsto_metrizable
    (fun N => (Finset.range N).measurable_sum fun k _ => (hH k).indicator (hσ k))
  exact tendsto_pi_nhds.mpr (tendsto_stoppedMeshPartialTest σ H)

/-- Disjoint finite branches give an unconditionally convergent signed
integral series. The countable union excludes only the zero infinite branch;
no assertion at the origin is obtained from a spatial almost-everywhere set. -/
theorem hasSum_integral_mul_meshBranchTest {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (σ : α → ℕ∞) (H : ℕ → α → ℝ)
    (hσ : ∀ k : ℕ, MeasurableSet {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable (H k)) (C : ℝ) (hC : 0 ≤ C)
    (hbH : ∀ k z, |H k z| ≤ C) (w : α → ℝ) (hw : Integrable w μ) :
    HasSum (fun k => ∫ z, w z * meshBranchTest σ H k z ∂μ)
      (∫ z, w z * stoppedMeshTest σ H z ∂μ) := by
  classical
  let f : α → ℝ := fun z => w z * stoppedMeshTest σ H z
  have hi : Integrable f μ := hw.mul_bdd
    (measurable_stoppedMeshTest σ H hσ hH).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      simp only [Real.norm_eq_abs, stoppedMeshTest]
      split_ifs
      · exact (abs_zero).trans_le hC
      · exact hbH _ z)
  have hd : Pairwise (fun k j : ℕ =>
      Disjoint {z | σ z = (k : ℕ∞)} {z | σ z = (j : ℕ∞)}) := by
    intro k j hkj
    apply Set.disjoint_left.mpr
    intro z hk hj
    exact hkj (ENat.natCast_inj.mp (hk.symm.trans hj))
  have hs := hasSum_integral_iUnion hσ hd hi.integrableOn
  have he : ∀ k : ℕ, (∫ z in {z | σ z = (k : ℕ∞)}, f z ∂μ) =
      ∫ z, w z * meshBranchTest σ H k z ∂μ := by
    intro k
    rw [← integral_indicator (hσ k)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      by_cases hz : σ z = (k : ℕ∞)
      · simp [f, meshBranchTest, stoppedMeshTest, hz]
      · simp [meshBranchTest, hz]
  have hu : (∫ z in ⋃ k : ℕ, {z | σ z = (k : ℕ∞)}, f z ∂μ) = ∫ z, f z ∂μ := by
    rw [← integral_indicator (MeasurableSet.iUnion hσ)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      by_cases ht : σ z = ⊤
      · simp [f, stoppedMeshTest, ht]
      · have hz : z ∈ ⋃ k : ℕ, {z | σ z = (k : ℕ∞)} :=
          Set.mem_iUnion.mpr ⟨(σ z).toNat, (ENat.natCast_toNat ht).symm⟩
        exact Set.indicator_of_mem hz f
  simpa only [he, hu] using hs

/-- The actual selected endpoint observation is measurable in its precise
stopped history and vanishes outside the source's `yᵢ - 7R` path cutoff. -/
theorem meshBranch_endpointPastTest_supported {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (σ : CoupledSample d → ℕ∞) (H : ℕ → CoupledSample d → ℝ)
    (hσ : ∀ k, MeasurableSet[finiteHistorySigma Δ k] {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable[finiteHistorySigma Δ k] (H k)) (k : ℕ) (y : Vec d) :
    Measurable[finiteHistorySigma Δ k]
      (endpointPastTest Δ lam R i k (meshBranchTest σ H k) y) ∧
    (∀ z, endpointPastTest Δ lam R i k (meshBranchTest σ H k) y
        (Probability.stoppedHistorySample Δ k z) =
      endpointPastTest Δ lam R i k (meshBranchTest σ H k) y z) ∧
    ∀ z, z ∉ pastBelow Δ k i (y i - 7 * R) →
      endpointPastTest Δ lam R i k (meshBranchTest σ H k) y z = 0 := by
  have hm := measurable_endpointPastTest Δ hΔ lam R hR i k
    (meshBranchTest σ H k) (measurable_meshBranchTest_history Δ σ H hσ hH k) y
  exact ⟨hm, Probability.finiteHistory_test_stopped Δ k _ hm,
    endpointPastTest_eq_zero_of_not_pastBelow Δ hΔ lam R hlam hR i k
      (meshBranchTest σ H k) y⟩

/-- Finite signed selected endpoint sums satisfy Fubini on unrestricted
spatial volume and the original fields. Each summand uses its actual branch
and its own deterministic history time. -/
theorem finite_meshBranchPastIntegral_weighted_fubini {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d)
    (σ : CoupledSample d → ℕ∞) (H : ℕ → CoupledSample d → ℝ)
    (hσ : ∀ k, MeasurableSet[finiteHistorySigma Δ k] {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable[finiteHistorySigma Δ k] (H k))
    (C : ℝ) (hC : 0 ≤ C) (hbH : ∀ k z, |H k z| ≤ C)
    (F : FieldPair d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F)
    (B : ℕ → Vec d × FieldPair d → ℝ) (hB : ∀ k, Measurable (B k))
    (hbB : ∀ k, BoundedRealTest (B k)) (s : Finset ℕ) :
    Integrable (fun p => ∑ k ∈ s, F p.2 *
      firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) p * B k p)
      ((volume : Measure (Vec d)).prod Q) ∧
    (∫ y, ∫ ω, ∑ k ∈ s, F ω *
      firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) (y, ω) * B k (y, ω) ∂Q) =
      ∫ ω, (∫ y, ∑ k ∈ s, F ω *
        firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) (y, ω) * B k (y, ω)) ∂Q := by
  have hi : ∀ k, Integrable (fun p => F p.2 *
      firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) p * B k p)
      ((volume : Measure (Vec d)).prod Q) := fun k =>
    (weighted_firstSlicePastIntegral_fubini Q K hK Δ lam R hR i k
      (meshBranchTest σ H k)
      ((measurable_meshBranchTest_history Δ σ H hσ hH k).mono
        (Probability.finiteHistorySigma_le Δ k) le_rfl)
      ⟨C, abs_meshBranchTest_le σ H C hC hbH k⟩ F hF hbF (B k) (hB k) (hbB k)).1
  have his := integrable_finsetSum s (fun k _ => hi k)
  exact ⟨his, integral_integral_swap his⟩

/-- When the actual supported branch integrals have moving local sections,
their jointly integrable versions share one origin event for every endpoint
and a separate spatial-product event. Locality remains an explicit internal
input; countable selection does not manufacture diffusion comparison. -/
theorem exists_countable_joint_integrable_meshBranchPastIntegral_versions {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d)
    (σ : CoupledSample d → ℕ∞) (H : ℕ → CoupledSample d → ℝ)
    (hσ : ∀ k, MeasurableSet[finiteHistorySigma Δ k] {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable[finiteHistorySigma Δ k] (H k))
    (C : ℝ) (hC : 0 ≤ C) (hbH : ∀ k z, |H k z| ≤ C)
    (hlocal : ∀ k (y : Vec d), ∃ a : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
      (fun ω => firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) (y, ω)) =ᵐ[Q] a) :
    ∃ A : ℕ → Vec d × FieldPair d → ℝ,
      (∀ k, Measurable (A k) ∧ (∀ p, |A k p| ≤ C) ∧
        Integrable (A k) ((volume : Measure (Vec d)).prod Q) ∧
        ∀ y : Vec d, ∃ a : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
          (∀ ω, |a ω| ≤ C) ∧ Integrable a Q ∧ (fun ω => A k (y, ω)) =ᵐ[Q] a) ∧
      (∀ᵐ ω ∂Q, ∀ k y, A k (y, ω) =
        firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) (y, ω)) ∧
      ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), ∀ k,
        A k p = firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) p := by
  have hv := fun k => exists_joint_integrable_firstSlicePastIntegral_version_with_local_sections
    Q K hK Δ lam R hR i k (meshBranchTest σ H k)
    ((measurable_meshBranchTest_history Δ σ H hσ hH k).mono
      (Probability.finiteHistorySigma_le Δ k) le_rfl)
    C (abs_meshBranchTest_le σ H C hC hbH k) (hlocal k)
  choose A hA hbA hiA he hp hl using hv
  exact ⟨A, fun k => ⟨hA k, hbA k, hiA k, hl k⟩,
    ae_all_iff.mpr he, ae_all_iff.mpr hp⟩

end StoppedMesh

section StoppedMeshEndpointSeries

/-- Countable signed endpoint pairings sum to the actual mesh-selected
endpoint average under the original annealed path/coin law. A common bound
and the disjoint selector branches supply integrability; the spatial measure
is unrestricted volume. The infinite selector branch contributes zero. -/
theorem hasSum_meshBranchPastIntegral_endpoint_pairings {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R) (i : Fin d)
    (σ : CoupledSample d → ℕ∞) (H : ℕ → CoupledSample d → ℝ)
    (hσ : ∀ k, MeasurableSet[finiteHistorySigma Δ k] {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable[finiteHistorySigma Δ k] (H k))
    (C : ℝ) (hC : 0 ≤ C) (hbH : ∀ k z, |H k z| ≤ C)
    (B : ℕ → Vec d × FieldPair d → ℝ) (hB : ∀ k, Measurable (B k))
    (D : ℝ) (hbB : ∀ k p, |B k p| ≤ D) :
    HasSum (fun k => (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
      ∫ y, ∫ ω, firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) (y, ω) *
        B k (y, ω) ∂Q)
      (∫ q, stoppedMeshTest (fun q : FieldPair d × CoupledSample d => σ q.2)
        (fun k q => ((forcedBitTrialEvent Δ lam R i k).indicator (H k)) q.2 *
          endpointAverage i R (q.2.1 ((k : ℝ≥0) * Δ)) (fun y => B k (y, q.1))) q
        ∂annealedCoupledLaw Q K) := by
  classical
  let μ := annealedCoupledLaw Q K
  let : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q K hK
  let ρ : FieldPair d × CoupledSample d → ℕ∞ := fun q => σ q.2
  let T : ℕ → FieldPair d × CoupledSample d → ℝ := fun k q =>
    ((forcedBitTrialEvent Δ lam R i k).indicator (H k)) q.2 *
      endpointAverage i R (q.2.1 ((k : ℝ≥0) * Δ)) (fun y => B k (y, q.1))
  have hσ' : ∀ k : ℕ, MeasurableSet {z | σ z = (k : ℕ∞)} := fun k =>
    (Probability.finiteHistorySigma_le Δ k) _ (hσ k)
  have hH' : ∀ k, Measurable (H k) := fun k =>
    (hH k).mono (Probability.finiteHistorySigma_le Δ k) le_rfl
  have hΓ : ∀ k, MeasurableSet (forcedBitTrialEvent Δ lam R i k) := fun k =>
    (Probability.finiteHistorySigma_le Δ k) _
      (measurableSet_forcedBitTrialEvent_finiteHistory Δ hΔ lam R hR i k)
  let X : (ℕ × (FieldPair d × CoupledSample d)) → Vec d := fun q =>
    q.2.2.1 ((q.1 : ℝ≥0) * Δ)
  let U : (ℕ × (FieldPair d × CoupledSample d)) × Vec d → ℝ := fun q =>
    B q.1.1 (q.2, q.1.2.1)
  obtain ⟨E, hE⟩ := boundedRealTest_endpointAverage i R hR X U
    ⟨D, fun q => hbB q.1.1 (q.2, q.1.2.1)⟩
  have hT : ∀ k, Measurable (T k) := by
    intro k
    exact (((hH' k).indicator (hΓ k)).comp measurable_snd).mul
      (measurable_endpointAverage i R _
        ((continuous_eval_const _).measurable.comp measurable_snd.fst) _
        ((hB k).comp (measurable_snd.prodMk measurable_fst.fst)))
  have hbT : ∀ k q, |T k q| ≤ C * max E 0 := by
    intro k q
    have hG : |((forcedBitTrialEvent Δ lam R i k).indicator (H k)) q.2| ≤ C := by
      by_cases hq : q.2 ∈ forcedBitTrialEvent Δ lam R i k
      · simpa only [Set.indicator_of_mem hq] using hbH k q.2
      · simpa only [Set.indicator_of_notMem hq, abs_zero] using hC
    exact (abs_mul _ _).trans_le
      (mul_le_mul hG ((hE (k, q)).trans (le_max_left E 0))
        (abs_nonneg _) hC)
  have hρ : ∀ k : ℕ, MeasurableSet {q | ρ q = (k : ℕ∞)} := fun k =>
    (hσ' k).preimage measurable_snd
  have hs := hasSum_integral_mul_meshBranchTest μ ρ T hρ hT
    (C * max E 0) (mul_nonneg hC (le_max_right E 0)) hbT
    (fun _ => 1) (integrable_const 1)
  simp only [one_mul] at hs
  have he : ∀ k, (∫ q, meshBranchTest ρ T k q ∂μ) =
      (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
        ∫ y, ∫ ω, firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) (y, ω) *
          B k (y, ω) ∂Q := by
    intro k
    let G := (forcedBitTrialEvent Δ lam R i k).indicator (meshBranchTest σ H k)
    have hG : Measurable G := ((hH' k).indicator (hσ' k)).indicator (hΓ k)
    have hbG : BoundedRealTest G := by
      refine ⟨C, fun z => ?_⟩
      by_cases hz : z ∈ forcedBitTrialEvent Δ lam R i k
      · simpa only [G, Set.indicator_of_mem hz] using
          abs_meshBranchTest_le σ H C hC hbH k z
      · simpa only [G, Set.indicator_of_notMem hz, abs_zero] using hC
    have hJ : Measurable (meshBranchTest ρ T k) := (hT k).indicator (hρ k)
    have hbJ : BoundedRealTest (meshBranchTest ρ T k) :=
      ⟨C * max E 0, abs_meshBranchTest_le ρ T (C * max E 0)
        (mul_nonneg hC (le_max_right E 0)) hbT k⟩
    have hf : meshBranchTest ρ T k = fun q => G q.2 *
        endpointAverage i R (q.2.1 ((k : ℝ≥0) * Δ)) (fun y => B k (y, q.1)) := by
      funext q
      by_cases hz : σ q.2 = (k : ℕ∞)
      · by_cases htrial : q.2 ∈ forcedBitTrialEvent Δ lam R i k <;>
          simp [meshBranchTest, ρ, T, G, hz, htrial]
      · by_cases htrial : q.2 ∈ forcedBitTrialEvent Δ lam R i k <;>
          simp [meshBranchTest, ρ, T, G, hz, htrial]
    rw [hf] at hJ hbJ ⊢
    change (∫ q, _ ∂annealedCoupledLaw Q K) = _
    rw [integral_annealedCoupledLaw Q K hK _ hJ hbJ]
    simpa only [firstSlicePastIntegral, G] using
      (integral_annealed_endpointAverage_fubini Q K hK Δ k i R hR G hG hbG
        (B k) (hB k) ⟨D, hbB k⟩)
  simpa only [he] using hs

end StoppedMeshEndpointSeries


section HistoryCylinders

/-- Rational observations determine the literal continuous path. Negative
rational times are sent to zero, so this also retains the time-zero value. -/
def rationalPathObservations {d : ℕ} (γ : Path d) (q : ℚ) : Vec d :=
  γ (q : ℝ).toNNReal

/-- The rational evaluation record carries exactly the path Borel structure. -/
theorem measurableEmbedding_rationalPathObservations {d : ℕ} :
    MeasurableEmbedding (rationalPathObservations (d := d)) := by
  have : PolishSpace (Path d) := by infer_instance
  have hd : DenseRange (fun q : ℚ => (q : ℝ).toNNReal) := by
    have hs : Function.Surjective Real.toNNReal := fun t => ⟨t, by simp⟩
    exact hs.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal
  have hc : Continuous (rationalPathObservations (d := d)) :=
    continuous_pi fun q => continuous_eval_const (q : ℝ).toNNReal
  apply hc.measurableEmbedding
  intro γ η h
  apply ContinuousMap.ext
  have heq : (γ : ℝ≥0 → Vec d) = η := by
    apply Continuous.ext_on hd γ.continuous η.continuous
    rintro _ ⟨q, rfl⟩
    exact congrFun h q
  exact congrFun heq

/-- One-coordinate generators of the exact finite past: rational evaluations
of the stopped path, and precisely the coin bits strictly before `n`. -/
def historyCylinderBase {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    (ℚ × ℕ) ⊕ (Fin n × Bool) → Set (CoupledSample d)
  | .inl (q, k) => (fun z => z.1 (min (q : ℝ).toNNReal ((n : ℝ≥0) * Δ))) ⁻¹'
      MeasurableSpace.natGeneratingSequence (Vec d) k
  | .inr (k, b) => {z | z.2 k = b}

/-- Finite intersections of the literal stopped path/coin generators.
The empty intersection retains the mass test. -/
def historyCylinders {d : ℕ} (Δ : ℝ≥0) (n : ℕ) : Set (Set (CoupledSample d)) :=
  Set.range fun F : Finset ((ℚ × ℕ) ⊕ (Fin n × Bool)) =>
    ⋂ j ∈ F, historyCylinderBase Δ n j

/-- Each base observation is measurable for the actual finite past. -/
theorem measurableSet_historyCylinderBase {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (j : (ℚ × ℕ) ⊕ (Fin n × Bool)) :
    MeasurableSet[finiteHistorySigma Δ n] (historyCylinderBase (d := d) Δ n j) := by
  rcases j with ⟨q, k⟩ | ⟨k, b⟩
  · exact ((continuous_eval_const (q : ℝ).toNNReal).measurable.comp
      (Probability.measurable_stoppedHistorySample Δ n).fst)
        (MeasurableSpace.measurableSet_natGeneratingSequence (α := Vec d) k)
  · have hb : Measurable[finiteHistorySigma (d := d) Δ n]
        (fun z => z.2 (k : ℕ)) := by
      apply Measurable.of_comap_le
      exact le_sup_of_le_right (le_iSup_of_le ⟨k.1, k.2⟩ le_rfl)
    exact hb (measurableSet_singleton b)

/-- There are only countably many finite stopped-history cylinders. -/
theorem countable_historyCylinders {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    (historyCylinders (d := d) Δ n).Countable := Set.countable_range _

/-- The genuine mass test is a member of the cylinder family. -/
theorem univ_mem_historyCylinders {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    Set.univ ∈ historyCylinders (d := d) Δ n := by
  exact ⟨∅, by simp⟩

/-- Intersecting cylinders combines their finitely many actual observations. -/
theorem isPiSystem_historyCylinders {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    IsPiSystem (historyCylinders (d := d) Δ n) := by
  classical
  rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩ _
  refine ⟨F ∪ G, ?_⟩
  ext z
  simp only [Finset.mem_union, Set.mem_inter_iff, Set.mem_iInter]
  exact ⟨fun h => ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩,
    fun ⟨hf, hg⟩ j hj => hj.elim (hf j) (hg j)⟩

/-- Rational observations and the permitted finite coin prefix generate the
literal finite-history sigma algebra, without any completion or positivity
assumption on the mesh. -/
theorem finiteHistorySigma_eq_generateFrom_historyCylinderBase {d : ℕ}
    (Δ : ℝ≥0) (n : ℕ) :
    finiteHistorySigma (d := d) Δ n =
      MeasurableSpace.generateFrom (Set.range (historyCylinderBase (d := d) Δ n)) := by
  apply le_antisymm
  · let M := MeasurableSpace.generateFrom
      (Set.range (historyCylinderBase (d := d) Δ n))
    have heval (q : ℚ) : Measurable[M]
        (fun z : CoupledSample d => z.1 (min (q : ℝ).toNNReal ((n : ℝ≥0) * Δ))) := by
      apply Measurable.of_comap_le
      rw [← MeasurableSpace.generateFrom_natGeneratingSequence (Vec d),
        MeasurableSpace.comap_generateFrom]
      apply MeasurableSpace.generateFrom_le
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact MeasurableSpace.measurableSet_generateFrom ⟨.inl (q, k), rfl⟩
    have hpath : Measurable[M]
        (fun z : CoupledSample d => (Probability.stoppedHistorySample Δ n z).1) := by
      have hr : Measurable[M] (fun z : CoupledSample d =>
          rationalPathObservations (Probability.stoppedHistorySample Δ n z).1) :=
        Measurable.of_eval heval
      exact (measurableEmbedding_rationalPathObservations.measurable_comp_iff).mp hr
    have hbits : Measurable[M]
        (fun z : CoupledSample d => (Probability.stoppedHistorySample Δ n z).2) := by
      refine Measurable.of_eval fun k => ?_
      by_cases hk : k < n
      · have hb : Measurable[M] (fun z : CoupledSample d => z.2 k) := by
          apply measurable_to_countable'
          intro b
          exact MeasurableSpace.measurableSet_generateFrom ⟨.inr (⟨k, hk⟩, b), rfl⟩
        simpa only [Probability.stoppedHistorySample, ite_eq_left hk] using hb
      · simp only [Probability.stoppedHistorySample, ite_eq_right hk]
        exact measurable_const
    rw [Probability.finiteHistorySigma_eq_comap_stopped]
    exact (hpath.prodMk hbits).comap_le
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨j, rfl⟩
    exact measurableSet_historyCylinderBase Δ n j

/-- The countable pi-system of finite cylinders generates the exact past. -/
theorem finiteHistorySigma_eq_generateFrom_historyCylinders {d : ℕ}
    (Δ : ℝ≥0) (n : ℕ) :
    finiteHistorySigma (d := d) Δ n =
      MeasurableSpace.generateFrom (historyCylinders (d := d) Δ n) := by
  classical
  apply le_antisymm
  · rw [finiteHistorySigma_eq_generateFrom_historyCylinderBase]
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨{j}, by simp⟩
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨F, rfl⟩
    exact Finset.measurableSet_biInter F fun j _ => measurableSet_historyCylinderBase Δ n j

/-- Each cylinder is an actual finite-past event. -/
theorem measurableSet_historyCylinders {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    {S : Set (CoupledSample d)} (hS : S ∈ historyCylinders Δ n) :
    MeasurableSet[finiteHistorySigma Δ n] S := by
  rw [finiteHistorySigma_eq_generateFrom_historyCylinders]
  exact MeasurableSpace.measurableSet_generateFrom hS


/-- Finite-measure uniqueness on the literal finite-past sigma algebra. -/
theorem measure_eq_on_history_of_cylinders {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (μ ν : Measure (CoupledSample d)) [IsFiniteMeasure μ]
    (hcyl : ∀ S ∈ historyCylinders Δ n, μ S = ν S)
    {S : Set (CoupledSample d)} (hS : MeasurableSet[finiteHistorySigma Δ n] S) :
    μ S = ν S :=
  ext_on_measurableSpace_of_generate_finite
    (inferInstance : MeasurableSpace (CoupledSample d)) (historyCylinders Δ n)
    hcyl (Probability.finiteHistorySigma_le Δ n)
    (finiteHistorySigma_eq_generateFrom_historyCylinders Δ n)
    (isPiSystem_historyCylinders Δ n) (hcyl Set.univ (univ_mem_historyCylinders Δ n)) hS

/-- Cylinder comparison determines signed integrals of actual past tests. -/
theorem integral_eq_on_history_of_cylinders {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (μ ν : Measure (CoupledSample d)) [IsFiniteMeasure μ]
    (hcyl : ∀ S ∈ historyCylinders Δ n, μ S = ν S)
    (H : CoupledSample d → ℝ) (hH : Measurable[finiteHistorySigma Δ n] H) :
    (∫ z, H z ∂μ) = ∫ z, H z ∂ν := by
  have heq : μ.trim (Probability.finiteHistorySigma_le Δ n) =
      ν.trim (Probability.finiteHistorySigma_le Δ n) := by
    apply @Measure.ext _ (finiteHistorySigma Δ n)
    intro S hS
    rw [trim_measurableSet_eq _ hS, trim_measurableSet_eq _ hS]
    exact measure_eq_on_history_of_cylinders Δ n μ ν hcyl hS
  calc
    (∫ z, H z ∂μ) = ∫ z, H z ∂μ.trim (Probability.finiteHistorySigma_le Δ n) :=
      integral_trim _ hH.stronglyMeasurable
    _ = ∫ z, H z ∂ν.trim (Probability.finiteHistorySigma_le Δ n) := by rw [heq]
    _ = ∫ z, H z ∂ν := (integral_trim _ hH.stronglyMeasurable).symm

/-- Agreement on countably many literal history cylinders gives one common
good event for all measurable past sets. The compared objects are genuine
measures; separate scalar representatives would not suffice. -/
theorem ae_measure_eq_on_history_of_cylinders {d : ℕ} {β : Type*}
    [MeasurableSpace β] (ρ : Measure β) (Δ : ℝ≥0) (n : ℕ)
    (μ ν : β → Measure (CoupledSample d))
    (hfinite : ∀ᵐ x ∂ρ, IsFiniteMeasure (μ x))
    (hcyl : ∀ S ∈ historyCylinders Δ n, ∀ᵐ x ∂ρ, μ x S = ν x S) :
    ∀ᵐ x ∂ρ, ∀ S, MeasurableSet[finiteHistorySigma Δ n] S → μ x S = ν x S := by
  let : Countable (historyCylinders (d := d) Δ n) :=
    (countable_historyCylinders Δ n).to_subtype
  have hc : ∀ᵐ x ∂ρ, ∀ S : historyCylinders (d := d) Δ n,
      μ x S = ν x S := ae_all_iff.mpr fun S => hcyl S S.2
  filter_upwards [hfinite, hc] with x hfin hx
  let : IsFiniteMeasure (μ x) := hfin
  intro S hS
  exact measure_eq_on_history_of_cylinders Δ n (μ x) (ν x) (fun T hT => hx ⟨T, hT⟩) hS

/-- A single event supports equality of every signed finite-history integral.
Trimming to the literal history sigma algebra keeps the ambient laws intact. -/
theorem ae_integral_eq_on_history_of_cylinders {d : ℕ} {β : Type*}
    [MeasurableSpace β] (ρ : Measure β) (Δ : ℝ≥0) (n : ℕ)
    (μ ν : β → Measure (CoupledSample d))
    (hfinite : ∀ᵐ x ∂ρ, IsFiniteMeasure (μ x))
    (hcyl : ∀ S ∈ historyCylinders Δ n, ∀ᵐ x ∂ρ, μ x S = ν x S) :
    ∀ᵐ x ∂ρ, ∀ H : CoupledSample d → ℝ,
      Measurable[finiteHistorySigma Δ n] H →
      (∫ z, H z ∂μ x) = ∫ z, H z ∂ν x := by
  filter_upwards [ae_measure_eq_on_history_of_cylinders ρ Δ n μ ν hfinite hcyl] with x hx
  intro H hH
  have heq : (μ x).trim (Probability.finiteHistorySigma_le Δ n) =
      (ν x).trim (Probability.finiteHistorySigma_le Δ n) := by
    apply @Measure.ext _ (finiteHistorySigma Δ n)
    intro S hS
    rw [trim_measurableSet_eq _ hS, trim_measurableSet_eq _ hS]
    exact hx S hS
  calc
    (∫ z, H z ∂μ x) =
        ∫ z, H z ∂(μ x).trim (Probability.finiteHistorySigma_le Δ n) :=
      integral_trim _ hH.stronglyMeasurable
    _ = ∫ z, H z ∂(ν x).trim (Probability.finiteHistorySigma_le Δ n) := by rw [heq]
    _ = ∫ z, H z ∂ν x := (integral_trim _ hH.stronglyMeasurable).symm

/-- The actual endpoint past integral is integration against this measure:
the original coupled law restricted to the trial and moving endpoint ball. -/
def firstSlicePastMeasure {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (m : ℕ) (K : CoupledQuenchedLaws d) (p : Vec d × FieldPair d) :
    Measure (CoupledSample d) :=
  ((K (0, p.2)).restrict
    {z | p.1 ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))}).restrict
      (forcedBitTrialEvent Δ lam R i m)

/-- The past measure is dominated by its original quenched law. -/
theorem firstSlicePastMeasure_le {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (m : ℕ) (K : CoupledQuenchedLaws d) (p : Vec d × FieldPair d) :
    firstSlicePastMeasure Δ lam R i m K p ≤ K (0, p.2) :=
  Measure.restrict_le_self.trans Measure.restrict_le_self

/-- Genuine finite quenched laws give finite endpoint past measures. -/
theorem isFiniteMeasure_firstSlicePastMeasure {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (m : ℕ) (K : CoupledQuenchedLaws d) (p : Vec d × FieldPair d)
    [IsFiniteMeasure (K (0, p.2))] :
    IsFiniteMeasure (firstSlicePastMeasure Δ lam R i m K p) := by
  unfold firstSlicePastMeasure
  infer_instance

/-- Restriction identifies every literal signed endpoint past factor, without
choosing any test-dependent representative. -/
theorem integral_firstSlicePastMeasure {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (m : ℕ) (K : CoupledQuenchedLaws d)
    (H : CoupledSample d → ℝ) (p : Vec d × FieldPair d) :
    (∫ z, H z ∂firstSlicePastMeasure Δ lam R i m K p) =
      firstSlicePastIntegral Δ lam R i m K H p := by
  rw [← integral_endpointPastTest]
  unfold endpointPastTest
  rw [integral_indicator
    ((Probability.finiteHistorySigma_le Δ m) _ (measurableSet_endpointBall_past Δ R i m p.1)),
    integral_indicator (measurableSet_forcedBitTrialEvent Δ lam R i m)]
  rfl

/-- The mass test is exactly the existing first-slice density. -/
theorem firstSlicePastMeasure_mass {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (m : ℕ) (K : CoupledQuenchedLaws d) (p : Vec d × FieldPair d) :
    (firstSlicePastMeasure Δ lam R i m K p Set.univ).toReal =
      firstSlicePastIntegral Δ lam R i m K (fun _ => 1) p := by
  simpa only [integral_const, smul_eq_mul, mul_one, measureReal_def] using
    integral_firstSlicePastMeasure Δ lam R i m K (fun _ => 1) p

/-- A genuine family of comparison measures agreeing with the actual past
measure on cylinders agrees for all signed past tests on one common event.
The parameter law may be the original environment law at a fixed endpoint,
or the spatial product law; neither good event is inferred from the other. -/
theorem ae_firstSlicePastIntegral_eq_of_cylinders {d : ℕ} {β : Type*}
    [MeasurableSpace β] (ρ : Measure β) (p : β → Vec d × FieldPair d)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ) (K : CoupledQuenchedLaws d)
    (ν : β → Measure (CoupledSample d))
    (hfinite : ∀ᵐ x ∂ρ, IsFiniteMeasure (K (0, (p x).2)))
    (hcyl : ∀ S ∈ historyCylinders Δ m, ∀ᵐ x ∂ρ,
      firstSlicePastMeasure Δ lam R i m K (p x) S = ν x S) :
    ∀ᵐ x ∂ρ, ∀ H : CoupledSample d → ℝ,
      Measurable[finiteHistorySigma Δ m] H →
      firstSlicePastIntegral Δ lam R i m K H (p x) = ∫ z, H z ∂ν x := by
  have hfin : ∀ᵐ x ∂ρ, IsFiniteMeasure (firstSlicePastMeasure Δ lam R i m K (p x)) := by
    filter_upwards [hfinite] with x hx
    let := hx
    exact isFiniteMeasure_firstSlicePastMeasure Δ lam R i m K (p x)
  filter_upwards [ae_integral_eq_on_history_of_cylinders ρ Δ m
    (fun x => firstSlicePastMeasure Δ lam R i m K (p x)) ν hfin hcyl] with x hx
  intro H hH
  rw [← integral_firstSlicePastMeasure]
  exact hx H hH


/-- Countably many comparisons that already share every endpoint yield one
origin event supporting all endpoints and all measurable history tests.
No intersection of uncountably many endpoint exceptional sets is taken. -/
theorem ae_all_endpoints_firstSlicePastIntegral_eq_of_cylinders {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (K : CoupledQuenchedLaws d) (ν : Vec d × FieldPair d → Measure (CoupledSample d))
    (hfinite : ∀ᵐ ω ∂Q, IsFiniteMeasure (K (0, ω)))
    (hcyl : ∀ S ∈ historyCylinders Δ m, ∀ᵐ ω ∂Q, ∀ y : Vec d,
      firstSlicePastMeasure Δ lam R i m K (y, ω) S = ν (y, ω) S) :
    ∀ᵐ ω ∂Q, ∀ (y : Vec d) (H : CoupledSample d → ℝ),
      Measurable[finiteHistorySigma Δ m] H →
      firstSlicePastIntegral Δ lam R i m K H (y, ω) = ∫ z, H z ∂ν (y, ω) := by
  let : Countable (historyCylinders (d := d) Δ m) :=
    (countable_historyCylinders Δ m).to_subtype
  have hc : ∀ᵐ ω ∂Q, ∀ S : historyCylinders (d := d) Δ m, ∀ y : Vec d,
      firstSlicePastMeasure Δ lam R i m K (y, ω) S = ν (y, ω) S :=
    ae_all_iff.mpr fun S => hcyl S S.2
  filter_upwards [hfinite, hc] with ω hfin hx
  let := hfin
  intro y H hH
  let := isFiniteMeasure_firstSlicePastMeasure Δ lam R i m K (y, ω)
  rw [← integral_firstSlicePastMeasure]
  exact integral_eq_on_history_of_cylinders Δ m _ _ (fun S hS => hx ⟨S, hS⟩ y) H hH

/-- Signed weighted integration consumes a genuine cylinder comparison and
an actual integrability estimate. The right-hand comparison family inherits
integrability from the original first-slice past factor. -/
theorem integral_mul_firstSlicePastIntegral_eq_of_cylinders {d : ℕ} {β : Type*}
    [MeasurableSpace β] (ρ : Measure β) (p : β → Vec d × FieldPair d)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ) (K : CoupledQuenchedLaws d)
    (ν : β → Measure (CoupledSample d))
    (hfinite : ∀ᵐ x ∂ρ, IsFiniteMeasure (K (0, (p x).2)))
    (hcyl : ∀ S ∈ historyCylinders Δ m, ∀ᵐ x ∂ρ,
      firstSlicePastMeasure Δ lam R i m K (p x) S = ν x S)
    (H : CoupledSample d → ℝ) (hH : Measurable[finiteHistorySigma Δ m] H)
    (w : β → ℝ) (hi : Integrable
      (fun x => w x * firstSlicePastIntegral Δ lam R i m K H (p x)) ρ) :
    Integrable (fun x => w x * ∫ z, H z ∂ν x) ρ ∧
    (∫ x, w x * firstSlicePastIntegral Δ lam R i m K H (p x) ∂ρ) =
      ∫ x, w x * (∫ z, H z ∂ν x) ∂ρ := by
  have he : (fun x => w x * firstSlicePastIntegral Δ lam R i m K H (p x)) =ᵐ[ρ]
      fun x => w x * ∫ z, H z ∂ν x := by
    filter_upwards [ae_firstSlicePastIntegral_eq_of_cylinders ρ p Δ lam R i m K ν
      hfinite hcyl] with x hx
    rw [hx H hH]
  exact ⟨hi.congr he, integral_congr_ae he⟩

/-- Whole-space signed endpoint pairing for bounded actual past tests.
The cylinder premise uses the spatial product law; an origin-only event is
not substituted for that premise. Integrability comes from the actual
first-slice endpoint-volume estimate, rather than a comparison-kernel bound. -/
theorem integral_firstSlicePastIntegral_mul_eq_of_cylinders {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (ν : Vec d × FieldPair d → Measure (CoupledSample d))
    (hcyl : ∀ S ∈ historyCylinders Δ m,
      ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
        firstSlicePastMeasure Δ lam R i m K p S = ν p S)
    (H : CoupledSample d → ℝ) (hH : Measurable[finiteHistorySigma Δ m] H)
    (hbH : BoundedRealTest H)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B) :
    Integrable (fun p => (∫ z, H z ∂ν p) * B p)
      ((volume : Measure (Vec d)).prod Q) ∧
    (∫ p, firstSlicePastIntegral Δ lam R i m K H p * B p
      ∂((volume : Measure (Vec d)).prod Q)) =
      ∫ p, (∫ z, H z ∂ν p) * B p ∂((volume : Measure (Vec d)).prod Q) := by
  have hfinite : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
      IsFiniteMeasure (K (0, p.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hK.1] with p hp
    let := hp
    infer_instance
  have hi := integrable_firstSlicePastIntegral_mul Q K hK Δ lam R hR i m H
    (hH.mono (Probability.finiteHistorySigma_le Δ m) le_rfl) hbH B hB hbB
  simpa only [id_eq, mul_comm] using
    integral_mul_firstSlicePastIntegral_eq_of_cylinders
      ((volume : Measure (Vec d)).prod Q) id Δ lam R i m K ν hfinite hcyl H hH B
      (by simpa only [id_eq, mul_comm] using hi)

end HistoryCylinders

section IntegrableEndpointTests

/-- The actual annealed disintegration formula for signed integrable tests.
The probability-part kernel changes no origin fibre on its common good event. -/
theorem integral_annealedCoupledLaw_of_integrable {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (F : FieldPair d × CoupledSample d → ℝ)
    (hF : Integrable F (annealedCoupledLaw Q K)) :
    (∫ q, F q ∂annealedCoupledLaw Q K) =
      ∫ ω, ∫ z, F (ω, z) ∂K (0, ω) ∂Q := by
  rw [annealedCoupledLaw, Measure.integral_compProd hF]
  apply integral_congr_ae
  filter_upwards [hK.1] with ω hp
  let : IsProbabilityMeasure (originCoupledLaw K ω) := hp
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
  rfl

/-- A constant-in-endpoint signed integrable observation remains integrable
on its moving Euclidean ball, with the literal, finite spatial volume. -/
theorem integrable_endpointBall_indicator_of_integrable {d : ℕ} {α : Type*}
    [MeasurableSpace α] (μ : Measure α)
    (i : Fin d) (R : ℝ) (hR : 0 < R) (X : α → Vec d) (hX : Measurable X)
    (F : α → ℝ) (hF : Measurable F) (hiF : Integrable F μ) :
    Integrable (fun q : α × Vec d =>
      (endpointBall i R (X q.1)).indicator (fun _ => F q.1) q.2)
      (μ.prod volume) := by
  have hball (x : Vec d) : MeasurableSet (endpointBall i R x) :=
    (measurableSet_endpointBall_pair i R).preimage
      (measurable_const.prodMk measurable_id)
  have hm : Measurable (fun q : α × Vec d =>
      (endpointBall i R (X q.1)).indicator (fun _ => F q.1) q.2) :=
    (hF.comp measurable_fst).indicator
      ((measurableSet_endpointBall_pair i R).preimage
        ((hX.comp measurable_fst).prodMk measurable_snd))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro a
    have hi : IntegrableOn (fun _ : Vec d => F a) (endpointBall i R (X a)) volume :=
      integrableOn_const (endpointBall_volume_ne_top i R hR (X a))
    exact hi.integrable_indicator (hball _)
  · have he (a : α) :
        (∫ y, ‖(endpointBall i R (X a)).indicator (fun _ => F a) y‖) =
          (volume (endpointBall i R (0 : Vec d))).toReal * ‖F a‖ := by
      simp only [norm_indicator_eq_indicator_norm, integral_indicator (hball _),
        setIntegral_const, smul_eq_mul, measureReal_def, endpointBall_volume_eq]
    simpa only [he] using hiF.norm.const_mul
      (volume (endpointBall i R (0 : Vec d))).toReal

/-- Signed endpoint Fubini and the exact L1 contraction for the supplied
origin law. The hypothesis is absolute integrability of the genuine joint
annealed/endpoint test, so endpoint and environment weights may be unbounded.
The equality of kernels is used on one origin event for every endpoint. -/
theorem integrable_origin_endpoint_integral {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (J : (FieldPair d × CoupledSample d) × Vec d → ℝ)
    (hJ : Measurable J)
    (hiJ : Integrable J ((annealedCoupledLaw Q K).prod volume)) :
    Integrable (fun p : Vec d × FieldPair d =>
      ∫ z, J ((p.2, z), p.1) ∂K (0, p.2)) ((volume : Measure (Vec d)).prod Q) ∧
    (∫ p : Vec d × FieldPair d, |∫ z, J ((p.2, z), p.1) ∂K (0, p.2)|
      ∂((volume : Measure (Vec d)).prod Q)) ≤
        ∫ q, |J q| ∂((annealedCoupledLaw Q K).prod volume) ∧
    (∫ p : Vec d × FieldPair d, (∫ z, J ((p.2, z), p.1) ∂K (0, p.2))
      ∂((volume : Measure (Vec d)).prod Q)) =
        ∫ q, J q ∂((annealedCoupledLaw Q K).prod volume) := by
  let μ := annealedCoupledLaw Q K
  let : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q K hK
  let κ : ProbabilityTheory.Kernel (Vec d × FieldPair d) (CoupledSample d) :=
    (Probability.probabilityPart (originCoupledLaw K)).comap Prod.snd measurable_snd
  let A : Vec d × FieldPair d → ℝ := fun p => ∫ z, J ((p.2, z), p.1) ∂κ p
  let N : Vec d × FieldPair d → ℝ := fun p => ∫ z, ‖J ((p.2, z), p.1)‖ ∂κ p
  have hm : Measurable (fun p : (Vec d × FieldPair d) × CoupledSample d =>
      J ((p.1.2, p.2), p.1.1)) :=
    hJ.comp ((measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst)
  have hA : Measurable A :=
    (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  have hN : Measurable N :=
    (hm.norm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  have hN0 (p) : 0 ≤ N p := integral_nonneg fun _ => norm_nonneg _
  have hNsec : ∀ᵐ y ∂(volume : Measure (Vec d)),
      Integrable (fun ω => N (y, ω)) Q := by
    filter_upwards [hiJ.prod_left_ae] with y hy
    have hn := (Measure.integrable_compProd_iff hy.aestronglyMeasurable).mp hy |>.2
    exact hn
  have hNe : ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, N (y, ω) ∂Q) = ∫ q, ‖J (q, y)‖ ∂μ := by
    filter_upwards [hiJ.prod_left_ae] with y hy
    exact (Measure.integral_compProd hy.norm).symm
  have hiN : Integrable N ((volume : Measure (Vec d)).prod Q) := by
    apply (integrable_prod_iff hN.aestronglyMeasurable).mpr
    refine ⟨hNsec, ?_⟩
    apply hiJ.norm.integral_prod_right.congr
    filter_upwards [hNe] with y hy
    simpa only [Real.norm_of_nonneg (hN0 _)] using hy.symm
  have hAN (p) : ‖A p‖ ≤ N p := norm_integral_le_integral_norm _
  have hiA : Integrable A ((volume : Measure (Vec d)).prod Q) :=
    hiN.mono' hA.aestronglyMeasurable (Filter.Eventually.of_forall hAN)
  have he : ∀ᵐ ω ∂Q, ∀ y,
      A (y, ω) = ∫ z, J ((ω, z), y) ∂K (0, ω) := by
    filter_upwards [hK.1] with ω hp
    let : IsProbabilityMeasure (originCoupledLaw K ω) := hp
    intro y
    change (∫ z, J ((ω, z), y)
      ∂Probability.probabilityPart (originCoupledLaw K) ω) = _
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
    rfl
  have hep : A =ᵐ[((volume : Measure (Vec d)).prod Q)]
      fun p => ∫ z, J ((p.2, z), p.1) ∂K (0, p.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae he] with p hp
    exact hp p.1
  have hNint : (∫ p, N p ∂((volume : Measure (Vec d)).prod Q)) =
      ∫ q, ‖J q‖ ∂(μ.prod volume) := by
    rw [integral_prod _ hiN]
    exact (integral_congr_ae hNe).trans (integral_prod_symm _ hiJ.norm).symm
  refine ⟨hiA.congr hep, ?_, ?_⟩
  · calc
      _ = ∫ p, ‖A p‖ ∂((volume : Measure (Vec d)).prod Q) :=
        integral_congr_ae (hep.mono fun p hp => by
          simpa only [Real.norm_eq_abs] using congrArg abs hp.symm)
      _ ≤ ∫ p, N p ∂((volume : Measure (Vec d)).prod Q) :=
        integral_mono hiA.norm hiN hAN
      _ = _ := by simpa only [Real.norm_eq_abs] using hNint
  · rw [← integral_congr_ae hep, integral_prod _ hiA]
    have hae : ∀ᵐ y ∂(volume : Measure (Vec d)),
        (∫ ω, A (y, ω) ∂Q) = ∫ q, J (q, y) ∂μ := by
      filter_upwards [hiJ.prod_left_ae] with y hy
      exact (Measure.integral_compProd hy).symm
    exact (integral_congr_ae hae).trans (integral_prod_symm _ hiJ).symm

/-- Spatial integration of an integrable signed constant on the actual
moving endpoint ball gives its original, translation-invariant volume. -/
theorem integral_endpointBall_indicator_of_integrable {d : ℕ} {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (i : Fin d) (R : ℝ) (hR : 0 < R) (X : α → Vec d) (hX : Measurable X)
    (F : α → ℝ) (hF : Measurable F) (hiF : Integrable F μ) :
    (∫ q : α × Vec d,
      (endpointBall i R (X q.1)).indicator (fun _ => F q.1) q.2 ∂μ.prod volume) =
      (volume (endpointBall i R (0 : Vec d))).toReal * ∫ a, F a ∂μ := by
  have hball (x : Vec d) : MeasurableSet (endpointBall i R x) :=
    (measurableSet_endpointBall_pair i R).preimage
      (measurable_const.prodMk measurable_id)
  rw [integral_prod _ (integrable_endpointBall_indicator_of_integrable
    μ i R hR X hX F hF hiF)]
  simp only [integral_indicator (hball _), setIntegral_const,
    smul_eq_mul, measureReal_def, endpointBall_volume_eq, integral_const_mul]

/-- The literal past operator extends to signed tests integrable under the
original joint annealed law. Its sharp L1 estimate retains the forced trial
cutoff and the exact Euclidean endpoint-ball volume. -/
theorem integrable_firstSlicePastIntegral_of_integrable {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable H)
    (hiH : Integrable (fun q : FieldPair d × CoupledSample d => H q.2)
      (annealedCoupledLaw Q K)) :
    Integrable (firstSlicePastIntegral Δ lam R i m K H)
      ((volume : Measure (Vec d)).prod Q) ∧
    (∫ p, |firstSlicePastIntegral Δ lam R i m K H p|
      ∂((volume : Measure (Vec d)).prod Q)) ≤
        (volume (endpointBall i R (0 : Vec d))).toReal *
          ∫ q, |((forcedBitTrialEvent Δ lam R i m).indicator H) q.2|
            ∂annealedCoupledLaw Q K ∧
    (∫ p, firstSlicePastIntegral Δ lam R i m K H p
      ∂((volume : Measure (Vec d)).prod Q)) =
        (volume (endpointBall i R (0 : Vec d))).toReal *
          ∫ q, ((forcedBitTrialEvent Δ lam R i m).indicator H) q.2
            ∂annealedCoupledLaw Q K := by
  let μ := annealedCoupledLaw Q K
  let : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q K hK
  let G : CoupledSample d → ℝ := (forcedBitTrialEvent Δ lam R i m).indicator H
  have hG : Measurable G := hH.indicator (measurableSet_forcedBitTrialEvent Δ lam R i m)
  have hiG : Integrable (fun q : FieldPair d × CoupledSample d => G q.2) μ :=
    hiH.indicator ((measurableSet_forcedBitTrialEvent Δ lam R i m).preimage measurable_snd)
  let X : FieldPair d × CoupledSample d → Vec d := fun q => q.2.1 ((m : ℝ≥0) * Δ)
  have hX : Measurable X := (continuous_eval_const _).measurable.comp measurable_snd.fst
  let J : (FieldPair d × CoupledSample d) × Vec d → ℝ := fun q =>
    endpointPastTest Δ lam R i m H q.2 q.1.2
  have he : J = fun q =>
      (endpointBall i R (X q.1)).indicator (fun _ => G q.1.2) q.2 := by
    funext q
    by_cases hy : q.2 ∈ endpointBall i R (X q.1) <;>
      simp [J, endpointPastTest, X, G, hy]
  have hiJ : Integrable J (μ.prod volume) := by
    rw [he]
    exact integrable_endpointBall_indicator_of_integrable μ i R hR X hX
      _ (hG.comp measurable_snd) hiG
  have hJ : Measurable J := Measurable.comp
    (g := fun p : Vec d × CoupledSample d => endpointPastTest Δ lam R i m H p.1 p.2)
    (f := fun q : (FieldPair d × CoupledSample d) × Vec d => (q.2, q.1.2))
    (measurable_endpointPastTest_joint Δ lam R i m H hH)
    (measurable_snd.prodMk measurable_fst.snd)
  have hmass : (∫ q, |J q| ∂μ.prod volume) =
      (volume (endpointBall i R (0 : Vec d))).toReal * ∫ q, |G q.2| ∂μ := by
    rw [he]
    simp only [← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]
    exact integral_endpointBall_indicator_of_integrable μ i R hR X hX
      _ (hG.comp measurable_snd).norm hiG.norm
  have hmassSigned : (∫ q, J q ∂μ.prod volume) =
      (volume (endpointBall i R (0 : Vec d))).toReal * ∫ q, G q.2 ∂μ := by
    rw [he]
    exact integral_endpointBall_indicator_of_integrable μ i R hR X hX
      _ (hG.comp measurable_snd) hiG
  have hres := integrable_origin_endpoint_integral Q K hK J hJ hiJ
  have hpoint (p : Vec d × FieldPair d) :
      (∫ z, J ((p.2, z), p.1) ∂K (0, p.2)) =
        firstSlicePastIntegral Δ lam R i m K H p :=
    integral_endpointPastTest Δ lam R i m K H p.1 p.2
  simp only [hpoint] at hres
  exact ⟨hres.1, hres.2.1.trans_eq hmass, hres.2.2.trans hmassSigned⟩

/-- The preceding L1 contraction with the source's actual endpoint
normalization. No constant is integrated over unrestricted spatial volume. -/
theorem normalized_integral_abs_firstSlicePastIntegral_le {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable H)
    (hiH : Integrable (fun q : FieldPair d × CoupledSample d => H q.2)
      (annealedCoupledLaw Q K)) :
    (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
      (∫ p, |firstSlicePastIntegral Δ lam R i m K H p|
        ∂((volume : Measure (Vec d)).prod Q)) ≤
      ∫ q, |((forcedBitTrialEvent Δ lam R i m).indicator H) q.2|
        ∂annealedCoupledLaw Q K := by
  have hV : 0 < (volume (endpointBall i R (0 : Vec d))).toReal :=
    ENNReal.toReal_pos (endpointBall_volume_pos i R hR _).ne'
      (endpointBall_volume_ne_top i R hR _)
  have hb := (integrable_firstSlicePastIntegral_of_integrable
    Q K hK Δ lam R hR i m H hH hiH).2.1
  calc
    _ ≤ (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
        ((volume (endpointBall i R (0 : Vec d))).toReal *
          ∫ q, |((forcedBitTrialEvent Δ lam R i m).indicator H) q.2|
            ∂annealedCoupledLaw Q K) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hV.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hV.ne', one_mul]

/-- Signed truncation cuts only the tail of the original test. In particular
it preserves every history sigma algebra and every existing support cutoff. -/
def signedTestTruncation {α : Type*} (n : ℕ) (H : α → ℝ) : α → ℝ :=
  {z | |H z| ≤ (n : ℝ)}.indicator H

theorem measurable_signedTestTruncation {α : Type*} [MeasurableSpace α]
    (n : ℕ) (H : α → ℝ) (hH : Measurable H) :
    Measurable (signedTestTruncation n H) :=
  hH.indicator (measurableSet_le (by simpa only [Real.norm_eq_abs] using hH.norm) measurable_const)

theorem abs_signedTestTruncation_le {α : Type*} (n : ℕ) (H : α → ℝ) (z : α) :
    |signedTestTruncation n H z| ≤ |H z| := by
  by_cases hz : |H z| ≤ (n : ℝ)
  · simp [signedTestTruncation, hz]
  · simp [signedTestTruncation, hz]

theorem boundedRealTest_signedTestTruncation {α : Type*} (n : ℕ) (H : α → ℝ) :
    BoundedRealTest (signedTestTruncation n H) := by
  refine ⟨(n : ℝ), fun z => ?_⟩
  by_cases hz : |H z| ≤ (n : ℝ)
  · simp [signedTestTruncation, hz]
  · simp [signedTestTruncation, hz]

theorem tendsto_signedTestTruncation {α : Type*} (H : α → ℝ) (z : α) :
    Filter.Tendsto (fun n => signedTestTruncation n H z) Filter.atTop (nhds (H z)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |H z|
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hz : |H z| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
  simpa only [signedTestTruncation] using
    (Set.indicator_of_mem (show z ∈ {z | |H z| ≤ (n : ℝ)} from hz) H).symm

/-- Signed truncations converge in the actual joint L1 space; no boundedness
of the original test or of a spatial/environment weight is inferred. -/
theorem tendsto_integral_abs_sub_signedTestTruncation {α : Type*}
    [MeasurableSpace α] (μ : Measure α) (H : α → ℝ)
    (hH : Measurable H) (hiH : Integrable H μ) :
    Filter.Tendsto (fun n => ∫ z, |signedTestTruncation n H z - H z| ∂μ)
      Filter.atTop (nhds 0) := by
  have ht := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n z => |signedTestTruncation n H z - H z|)
    (f := fun _ => (0 : ℝ)) (fun z => 2 * |H z|)
    (fun n => by simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((measurable_signedTestTruncation n H hH).sub hH).norm.aestronglyMeasurable)
    (hiH.abs.const_mul 2) (fun n => ?_) ?_
  · simpa only [integral_zero] using ht
  · exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_abs]
      calc
        _ ≤ |signedTestTruncation n H z| + |H z| := abs_sub _ _
        _ ≤ |H z| + |H z| := add_le_add (abs_signedTestTruncation_le n H z) le_rfl
        _ = _ := (two_mul _).symm
  · exact Filter.Eventually.of_forall fun z => by
      simpa only [sub_self, abs_zero] using ((tendsto_signedTestTruncation H z).sub_const (H z)).abs

/-- Disjoint finite selector branches give signed countable additivity from
absolute integrability of the actual selected test. Its infinite branch is
literally zero; no uniform bound on the individual branch tests is needed. -/
theorem hasSum_integral_meshBranchTest_of_integrable {α : Type*}
    [MeasurableSpace α] (μ : Measure α) (σ : α → ℕ∞) (H : ℕ → α → ℝ)
    (hσ : ∀ k : ℕ, MeasurableSet {z | σ z = (k : ℕ∞)})
    (hi : Integrable (stoppedMeshTest σ H) μ) :
    HasSum (fun k => ∫ z, meshBranchTest σ H k z ∂μ)
      (∫ z, stoppedMeshTest σ H z ∂μ) := by
  classical
  have hd : Pairwise (fun k j : ℕ =>
      Disjoint {z | σ z = (k : ℕ∞)} {z | σ z = (j : ℕ∞)}) := by
    intro k j hkj
    apply Set.disjoint_left.mpr
    intro z hk hj
    exact hkj (ENat.natCast_inj.mp (hk.symm.trans hj))
  have hs := hasSum_integral_iUnion hσ hd hi.integrableOn
  have he : ∀ k : ℕ,
      (∫ z in {z | σ z = (k : ℕ∞)}, stoppedMeshTest σ H z ∂μ) =
        ∫ z, meshBranchTest σ H k z ∂μ := by
    intro k
    rw [← integral_indicator (hσ k)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      by_cases hz : σ z = (k : ℕ∞) <;> simp [meshBranchTest, stoppedMeshTest, hz]
  have hu : (∫ z in ⋃ k : ℕ, {z | σ z = (k : ℕ∞)}, stoppedMeshTest σ H z ∂μ) =
      ∫ z, stoppedMeshTest σ H z ∂μ := by
    rw [← integral_indicator (MeasurableSet.iUnion hσ)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      by_cases ht : σ z = ⊤
      · simp [stoppedMeshTest, ht]
      · have hz : z ∈ ⋃ k : ℕ, {z | σ z = (k : ℕ∞)} :=
          Set.mem_iUnion.mpr ⟨(σ z).toNat, (ENat.natCast_toNat ht).symm⟩
        exact Set.indicator_of_mem hz _
  simpa only [he, hu] using hs

/-- Every actual finite branch of an integrable selected test is integrable. -/
theorem integrable_meshBranchTest_of_integrable_stopped {α : Type*}
    [MeasurableSpace α] (μ : Measure α) (σ : α → ℕ∞) (H : ℕ → α → ℝ)
    (hσ : ∀ k : ℕ, MeasurableSet {z | σ z = (k : ℕ∞)})
    (hi : Integrable (stoppedMeshTest σ H) μ) (k : ℕ) :
    Integrable (meshBranchTest σ H k) μ := by
  apply (hi.indicator (hσ k)).congr
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : σ z = (k : ℕ∞) <;> simp [meshBranchTest, stoppedMeshTest, hz]

/-- Exact countable endpoint pairings for signed, possibly unbounded history,
field and endpoint tests. The one integrability premise is on the actual
selected joint annealed/endpoint test, retaining the forced event, the moving
Euclidean ball and zero on the infinite selector branch. -/
theorem hasSum_integrable_meshBranchPastIntegral_endpoint_pairings {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (σ : CoupledSample d → ℕ∞) (H : ℕ → CoupledSample d → ℝ)
    (hσ : ∀ k, MeasurableSet[finiteHistorySigma Δ k] {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable[finiteHistorySigma Δ k] (H k))
    (B : ℕ → Vec d × FieldPair d → ℝ) (hB : ∀ k, Measurable (B k))
    (hi : Integrable
      (stoppedMeshTest (fun q : (FieldPair d × CoupledSample d) × Vec d => σ q.1.2)
        (fun k q => endpointPastTest Δ lam R i k (H k) q.2 q.1.2 * B k (q.2, q.1.1)))
      ((annealedCoupledLaw Q K).prod volume)) :
    (∀ k, Integrable (fun p =>
      firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) p * B k p)
      ((volume : Measure (Vec d)).prod Q)) ∧
    HasSum (fun k => (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
      ∫ y, ∫ ω, firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) (y, ω) *
        B k (y, ω) ∂Q)
      ((volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
        ∫ q, stoppedMeshTest
          (fun q : (FieldPair d × CoupledSample d) × Vec d => σ q.1.2)
          (fun k q => endpointPastTest Δ lam R i k (H k) q.2 q.1.2 * B k (q.2, q.1.1)) q
          ∂((annealedCoupledLaw Q K).prod volume)) := by
  let μ := (annealedCoupledLaw Q K).prod (volume : Measure (Vec d))
  let ρ : (FieldPair d × CoupledSample d) × Vec d → ℕ∞ := fun q => σ q.1.2
  let T : ℕ → (FieldPair d × CoupledSample d) × Vec d → ℝ := fun k q =>
    endpointPastTest Δ lam R i k (H k) q.2 q.1.2 * B k (q.2, q.1.1)
  have hρ : ∀ k : ℕ, MeasurableSet {q | ρ q = (k : ℕ∞)} := fun k =>
    ((Probability.finiteHistorySigma_le Δ k) _ (hσ k)).preimage measurable_fst.snd
  have hH' : ∀ k, Measurable (H k) := fun k =>
    (hH k).mono (Probability.finiteHistorySigma_le Δ k) le_rfl
  let J : ℕ → (FieldPair d × CoupledSample d) × Vec d → ℝ := fun k q =>
    endpointPastTest Δ lam R i k (meshBranchTest σ H k) q.2 q.1.2 * B k (q.2, q.1.1)
  have hJe : ∀ k, J k = meshBranchTest ρ T k := by
    intro k
    funext q
    by_cases hs : σ q.1.2 = (k : ℕ∞)
    · by_cases hb : q.2 ∈ endpointBall i R (q.1.2.1 ((k : ℝ≥0) * Δ)) <;>
        by_cases ht : q.1.2 ∈ forcedBitTrialEvent Δ lam R i k <;>
        simp [J, T, ρ, endpointPastTest, meshBranchTest, hs, hb, ht]
    · by_cases hb : q.2 ∈ endpointBall i R (q.1.2.1 ((k : ℝ≥0) * Δ)) <;>
        by_cases ht : q.1.2 ∈ forcedBitTrialEvent Δ lam R i k <;>
        simp [J, T, ρ, endpointPastTest, meshBranchTest, hs, hb, ht]
  have hJi (k) : Integrable (J k) μ := by
    rw [hJe k]
    exact integrable_meshBranchTest_of_integrable_stopped μ ρ T hρ hi k
  have hJm (k) : Measurable (J k) :=
    ((measurable_endpointPastTest_joint Δ lam R i k (meshBranchTest σ H k)
      ((hH' k).indicator ((Probability.finiteHistorySigma_le Δ k) _ (hσ k)))).comp
        (measurable_snd.prodMk measurable_fst.snd)).mul
      ((hB k).comp (measurable_snd.prodMk measurable_fst.fst))
  have hres (k) := integrable_origin_endpoint_integral Q K hK (J k) (hJm k) (hJi k)
  have hpoint (k) (p : Vec d × FieldPair d) :
      (∫ z, J k ((p.2, z), p.1) ∂K (0, p.2)) =
        firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) p * B k p := by
    dsimp only [J]
    rw [integral_mul_const, integral_endpointPastTest]
  simp only [hpoint] at hres
  refine ⟨fun k => (hres k).1, ?_⟩
  have he (k) : (∫ q, meshBranchTest ρ T k q ∂μ) =
      ∫ y, ∫ ω, firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) (y, ω) *
        B k (y, ω) ∂Q := by
    rw [← hJe k, ← (hres k).2.2, integral_prod _ (hres k).1]
  have hs := (hasSum_integral_meshBranchTest_of_integrable μ ρ T hρ hi).mul_left
    (volume (endpointBall i R (0 : Vec d))).toReal⁻¹
  simpa only [he] using hs


/-- Joint measurability of the actual endpoint integral has a version on one
origin-environment event valid for every endpoint, also for unbounded tests. -/
theorem exists_measurable_firstSlicePastIntegral_version {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable H) :
    ∃ A : Vec d × FieldPair d → ℝ, Measurable A ∧
      ∀ᵐ ω ∂Q, ∀ y, A (y, ω) = firstSlicePastIntegral Δ lam R i m K H (y, ω) := by
  let κ : ProbabilityTheory.Kernel (Vec d × FieldPair d) (CoupledSample d) :=
    (Probability.probabilityPart (originCoupledLaw K)).comap Prod.snd measurable_snd
  let A : Vec d × FieldPair d → ℝ := fun p =>
    ∫ z, endpointPastTest Δ lam R i m H p.1 z ∂κ p
  have hm : Measurable (fun p : (Vec d × FieldPair d) × CoupledSample d =>
      endpointPastTest Δ lam R i m H p.1.1 p.2) :=
    Measurable.comp
      (g := fun p : Vec d × CoupledSample d => endpointPastTest Δ lam R i m H p.1 p.2)
      (f := fun p : (Vec d × FieldPair d) × CoupledSample d => (p.1.1, p.2))
      (measurable_endpointPastTest_joint Δ lam R i m H hH)
      (measurable_fst.fst.prodMk measurable_snd)
  refine ⟨A, (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable, ?_⟩
  filter_upwards [hprob] with ω hp
  let : IsProbabilityMeasure (originCoupledLaw K ω) := hp
  intro y
  change (∫ z, endpointPastTest Δ lam R i m H y z
    ∂Probability.probabilityPart (originCoupledLaw K) ω) = _
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
  exact integral_endpointPastTest Δ lam R i m K H y ω

/-- Signed integrability under the genuine joint law gives origin-fibre
integrability on its own environment event, without using a spatial null set. -/
theorem ae_integrable_origin_of_annealed_integrable {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (H : CoupledSample d → ℝ)
    (hiH : Integrable (fun q : FieldPair d × CoupledSample d => H q.2)
      (annealedCoupledLaw Q K)) :
    ∀ᵐ ω ∂Q, Integrable H (K (0, ω)) := by
  have hf := (Measure.integrable_compProd_iff hiH.aestronglyMeasurable).mp hiH |>.1
  filter_upwards [hf, hK.1] with ω hω hp
  let : IsProbabilityMeasure (originCoupledLaw K ω) := hp
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure] at hω
  exact hω

/-- An integrable history dominator controls the literal endpoint factor,
including both the forced trial and moving-ball indicators. -/
theorem abs_firstSlicePastIntegral_le_of_integrable_dominator {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (K : CoupledQuenchedLaws d) (ω : FieldPair d)
    (H : CoupledSample d → ℝ) (hH : Measurable H)
    (W : CoupledSample d → ℝ) (hiW : Integrable W (K (0, ω)))
    (hdom : ∀ z, |H z| ≤ W z) (y : Vec d) :
    |firstSlicePastIntegral Δ lam R i m K H (y, ω)| ≤
      firstSlicePastIntegral Δ lam R i m K W (y, ω) := by
  have hb : MeasurableSet {z : CoupledSample d |
      y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))} :=
    (measurableSet_endpointBall_pair i R).preimage
      (((continuous_eval_const _).measurable.comp measurable_fst).prodMk measurable_const)
  have hiWE : Integrable (endpointPastTest Δ lam R i m W y) (K (0, ω)) :=
    (hiW.indicator (measurableSet_forcedBitTrialEvent Δ lam R i m)).indicator hb
  have hmHE : Measurable (endpointPastTest Δ lam R i m H y) :=
    Measurable.comp
      (g := fun p : Vec d × CoupledSample d => endpointPastTest Δ lam R i m H p.1 p.2)
      (f := fun z : CoupledSample d => (y, z))
      (measurable_endpointPastTest_joint Δ lam R i m H hH)
      (measurable_const.prodMk measurable_id)
  have hpoint (z) : |endpointPastTest Δ lam R i m H y z| ≤
      endpointPastTest Δ lam R i m W y z := by
    by_cases hy : z ∈ {z : CoupledSample d |
        y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))}
    · by_cases ht : z ∈ forcedBitTrialEvent Δ lam R i m
      · simpa only [endpointPastTest, Set.indicator_of_mem hy,
          Set.indicator_of_mem ht] using hdom z
      · simp only [endpointPastTest, Set.indicator_of_mem hy,
          Set.indicator_of_notMem ht, abs_zero, le_refl]
    · simp only [endpointPastTest, Set.indicator_of_notMem hy, abs_zero, le_refl]
  have hiHE : Integrable (endpointPastTest Δ lam R i m H y) (K (0, ω)) :=
    hiWE.mono' hmHE.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hpoint z)
  rw [← integral_endpointPastTest, ← integral_endpointPastTest]
  exact abs_integral_le_integral_abs.trans (integral_mono hiHE.abs hiWE hpoint)

/-- Signed truncations converge on every endpoint of one common origin
fibre event. The original supplied law, rather than a spatial section, is used. -/
theorem ae_all_endpoints_tendsto_firstSlicePastIntegral_truncation {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable H)
    (hiH : Integrable (fun q : FieldPair d × CoupledSample d => H q.2)
      (annealedCoupledLaw Q K)) :
    ∀ᵐ ω ∂Q, ∀ y,
      Filter.Tendsto (fun n => firstSlicePastIntegral Δ lam R i m K
        (signedTestTruncation n H) (y, ω)) Filter.atTop
        (nhds (firstSlicePastIntegral Δ lam R i m K H (y, ω))) := by
  filter_upwards [ae_integrable_origin_of_annealed_integrable Q K hK H hiH] with ω hω
  intro y
  simp only [← integral_endpointPastTest]
  apply tendsto_integral_of_dominated_convergence (fun z => |H z|)
  · intro n
    exact (Measurable.comp
      (g := fun p : Vec d × CoupledSample d =>
        endpointPastTest Δ lam R i m (signedTestTruncation n H) p.1 p.2)
      (f := fun z : CoupledSample d => (y, z))
      (measurable_endpointPastTest_joint Δ lam R i m
        (signedTestTruncation n H) (measurable_signedTestTruncation n H hH))
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact hω.abs
  · intro n
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using
        (abs_endpointPastTest_le Δ lam R i m (signedTestTruncation n H) y z).trans
          (abs_signedTestTruncation_le n H z)
  · exact Filter.Eventually.of_forall fun z => by
      by_cases hy : z ∈ {w : CoupledSample d |
          y ∈ endpointBall i R (w.1 ((m : ℝ≥0) * Δ))}
      · by_cases ht : z ∈ forcedBitTrialEvent Δ lam R i m
        · simpa only [endpointPastTest, Set.indicator_of_mem hy,
            Set.indicator_of_mem ht] using tendsto_signedTestTruncation H z
        · simp only [endpointPastTest, Set.indicator_of_mem hy,
            Set.indicator_of_notMem ht]
          exact tendsto_const_nhds
      · simp only [endpointPastTest, Set.indicator_of_notMem hy]
        exact tendsto_const_nhds

/-- Signed annealed-integrable histories inherit moving local sections from
local versions of their bounded truncations. The common origin event is
separate from the spatial-product event. -/
theorem exists_joint_integrable_local_firstSlicePastIntegral_version_of_truncations {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable H)
    (hiH : Integrable (fun q : FieldPair d × CoupledSample d => H q.2)
      (annealedCoupledLaw Q K))
    (hlocal : ∀ n (y : Vec d), ∃ a : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K (signedTestTruncation n H)
        (y, ω)) =ᵐ[Q] a) :
    ∃ A : Vec d × FieldPair d → ℝ, Measurable A ∧
      Integrable A ((volume : Measure (Vec d)).prod Q) ∧
      (∀ᵐ ω ∂Q, ∀ y, A (y, ω) = firstSlicePastIntegral Δ lam R i m K H (y, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] firstSlicePastIntegral Δ lam R i m K H ∧
      ∀ y : Vec d, ∃ a : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
        (fun ω => A (y, ω)) =ᵐ[Q] a := by
  obtain ⟨A, hA, he⟩ := exists_measurable_firstSlicePastIntegral_version
    Q K hK.1 Δ lam R i m H hH
  have hp : A =ᵐ[((volume : Measure (Vec d)).prod Q)]
      firstSlicePastIntegral Δ lam R i m K H := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Vec d))) (ν := Q)).ae he] with p hp
    exact hp p.1
  refine ⟨A, hA, (integrable_firstSlicePastIntegral_of_integrable
    Q K hK Δ lam R hR i m H hH hiH).1.congr hp.symm, he, hp, ?_⟩
  intro y
  choose a ha hae using fun n => hlocal n y
  refine ⟨fun ω => Filter.limsup (fun n => a n ω) Filter.atTop, Measurable.limsup ha, ?_⟩
  filter_upwards [he, ae_all_iff.mpr hae,
    ae_all_endpoints_tendsto_firstSlicePastIntegral_truncation Q K hK Δ lam R i m H hH hiH]
    with ω hω heq hlim
  rw [hω y]
  have heq' : (fun n => a n ω) = (fun n => firstSlicePastIntegral Δ lam R i m K
      (signedTestTruncation n H) (y, ω)) := funext fun n => (heq n).symm
  rw [heq']
  exact (hlim y).limsup_eq.symm

/-- Signed truncation converges in endpoint/environment L1 on unrestricted
volume. Its integrable dominator is the actual absolute-history past factor,
whose mass has the original finite endpoint-ball normalization. -/
theorem tendsto_integral_abs_sub_firstSlicePastIntegral_truncation {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable H)
    (hiH : Integrable (fun q : FieldPair d × CoupledSample d => H q.2)
      (annealedCoupledLaw Q K)) :
    Filter.Tendsto (fun n => ∫ p,
      |firstSlicePastIntegral Δ lam R i m K (signedTestTruncation n H) p -
        firstSlicePastIntegral Δ lam R i m K H p|
      ∂((volume : Measure (Vec d)).prod Q)) Filter.atTop (nhds 0) := by
  have hi n := integrable_firstSlicePastIntegral Q K hK Δ lam R hR i m
    (signedTestTruncation n H) (measurable_signedTestTruncation n H hH)
    (boundedRealTest_signedTestTruncation n H)
  have hiF := (integrable_firstSlicePastIntegral_of_integrable
    Q K hK Δ lam R hR i m H hH hiH).1
  have hiAbs := (integrable_firstSlicePastIntegral_of_integrable
    Q K hK Δ lam R hR i m (fun z => |H z|) (by simpa only [Real.norm_eq_abs] using hH.norm) hiH.abs).1
  have hp := Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Vec d))) |>.ae
      (ae_integrable_origin_of_annealed_integrable Q K hK H hiH)
  have ht := tendsto_integral_of_dominated_convergence
    (μ := ((volume : Measure (Vec d)).prod Q))
    (F := fun n p => |firstSlicePastIntegral Δ lam R i m K (signedTestTruncation n H) p -
      firstSlicePastIntegral Δ lam R i m K H p|) (f := fun _ => (0 : ℝ))
    (fun p => 2 * firstSlicePastIntegral Δ lam R i m K (fun z => |H z|) p)
    (fun n => by simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((hi n).sub hiF).norm.aestronglyMeasurable)
    (hiAbs.const_mul 2) (fun n => ?_) ?_
  · simpa only [integral_zero] using ht
  · filter_upwards [hp] with p hp
    rw [Real.norm_eq_abs, abs_abs]
    calc
      _ ≤ |firstSlicePastIntegral Δ lam R i m K (signedTestTruncation n H) p| +
          |firstSlicePastIntegral Δ lam R i m K H p| := abs_sub _ _
      _ ≤ firstSlicePastIntegral Δ lam R i m K (fun z => |H z|) p +
          firstSlicePastIntegral Δ lam R i m K (fun z => |H z|) p :=
        add_le_add
          (abs_firstSlicePastIntegral_le_of_integrable_dominator Δ lam R i m K p.2
            (signedTestTruncation n H) (measurable_signedTestTruncation n H hH)
            (fun z => |H z|) hp.abs (abs_signedTestTruncation_le n H) p.1)
          (abs_firstSlicePastIntegral_le_of_integrable_dominator Δ lam R i m K p.2
            H hH (fun z => |H z|) hp.abs (fun _ => le_rfl) p.1)
      _ = _ := (two_mul _).symm
  · filter_upwards [Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Vec d))) |>.ae
        (ae_all_endpoints_tendsto_firstSlicePastIntegral_truncation Q K hK Δ lam R i m H hH hiH)]
      with p hp
    simpa only [sub_self, abs_zero] using
      ((hp p.1).sub_const (firstSlicePastIntegral Δ lam R i m K H p)).abs

/-- The literal endpoint integral has the source's normalized moving-ball
average, including the forced trial factor. This algebraic identity also
applies to signed unbounded endpoint weights. -/
theorem normalized_integral_endpointPastTest_mul {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (z : CoupledSample d) (B : Vec d → ℝ) :
    (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
      (∫ y, endpointPastTest Δ lam R i m H y z * B y) =
      ((forcedBitTrialEvent Δ lam R i m).indicator H) z *
        endpointAverage i R (z.1 ((m : ℝ≥0) * Δ)) B := by
  have hb : MeasurableSet (endpointBall i R (z.1 ((m : ℝ≥0) * Δ))) :=
    (measurableSet_endpointBall_pair i R).preimage
      (measurable_const.prodMk measurable_id)
  have he : (fun y => endpointPastTest Δ lam R i m H y z * B y) =
      (endpointBall i R (z.1 ((m : ℝ≥0) * Δ))).indicator
        (fun y => ((forcedBitTrialEvent Δ lam R i m).indicator H) z * B y) := by
    funext y
    by_cases hy : y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) <;>
      simp [endpointPastTest, hy]
  rw [he, integral_indicator hb, integral_const_mul]
  simp only [endpointAverage, endpointBall_volume_eq, div_eq_mul_inv]
  ring

/-- The signed countable endpoint pairings equal the actual selected
annealed moving-ball average. Absolute integrability is imposed before any
interchange; every finite branch and the infinite branch retain their exact
selector, supplied law, trial event and endpoint-dependent weight. -/
theorem hasSum_integrable_meshBranchPastIntegral_endpoint_averages {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (σ : CoupledSample d → ℕ∞) (H : ℕ → CoupledSample d → ℝ)
    (hσ : ∀ k, MeasurableSet[finiteHistorySigma Δ k] {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable[finiteHistorySigma Δ k] (H k))
    (B : ℕ → Vec d × FieldPair d → ℝ) (hB : ∀ k, Measurable (B k))
    (hi : Integrable
      (stoppedMeshTest (fun q : (FieldPair d × CoupledSample d) × Vec d => σ q.1.2)
        (fun k q => endpointPastTest Δ lam R i k (H k) q.2 q.1.2 * B k (q.2, q.1.1)))
      ((annealedCoupledLaw Q K).prod volume)) :
    Integrable
      (stoppedMeshTest (fun q : FieldPair d × CoupledSample d => σ q.2)
        (fun k q => ((forcedBitTrialEvent Δ lam R i k).indicator (H k)) q.2 *
          endpointAverage i R (q.2.1 ((k : ℝ≥0) * Δ)) (fun y => B k (y, q.1))))
      (annealedCoupledLaw Q K) ∧
    HasSum (fun k => (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
      ∫ y, ∫ ω, firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) (y, ω) *
        B k (y, ω) ∂Q)
      (∫ q, stoppedMeshTest (fun q : FieldPair d × CoupledSample d => σ q.2)
        (fun k q => ((forcedBitTrialEvent Δ lam R i k).indicator (H k)) q.2 *
          endpointAverage i R (q.2.1 ((k : ℝ≥0) * Δ)) (fun y => B k (y, q.1))) q
        ∂annealedCoupledLaw Q K) := by
  let : IsProbabilityMeasure (annealedCoupledLaw Q K) :=
    annealedCoupledLaw_isProbabilityMeasure Q K hK
  let J : (FieldPair d × CoupledSample d) × Vec d → ℝ :=
    stoppedMeshTest (fun q => σ q.1.2)
      (fun k q => endpointPastTest Δ lam R i k (H k) q.2 q.1.2 * B k (q.2, q.1.1))
  let A : FieldPair d × CoupledSample d → ℝ :=
    stoppedMeshTest (fun q => σ q.2)
      (fun k q => ((forcedBitTrialEvent Δ lam R i k).indicator (H k)) q.2 *
        endpointAverage i R (q.2.1 ((k : ℝ≥0) * Δ)) (fun y => B k (y, q.1)))
  have he (q : FieldPair d × CoupledSample d) :
      A q = (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ * ∫ y, J (q, y) := by
    by_cases ht : σ q.2 = ⊤
    · simp only [A, J, stoppedMeshTest, ht, ite_true, integral_zero, mul_zero]
    · simpa only [A, J, stoppedMeshTest, ht, ite_false] using
        (normalized_integral_endpointPastTest_mul Δ lam R i (σ q.2).toNat
          (H (σ q.2).toNat) q.2 (fun y => B (σ q.2).toNat (y, q.1))).symm
  have hiA : Integrable A (annealedCoupledLaw Q K) := by
    apply (hi.integral_prod_left.const_mul
      (volume (endpointBall i R (0 : Vec d))).toReal⁻¹).congr
    exact Filter.Eventually.of_forall fun q => (he q).symm
  have heint : (∫ q, A q ∂annealedCoupledLaw Q K) =
      (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
        ∫ q, J q ∂((annealedCoupledLaw Q K).prod volume) := by
    simp_rw [he]
    rw [integral_const_mul, integral_prod _ hi]
  refine ⟨hiA, ?_⟩
  change HasSum _ (∫ q, A q ∂annealedCoupledLaw Q K)
  rw [heint]
  exact (hasSum_integrable_meshBranchPastIntegral_endpoint_pairings
    Q K hK Δ lam R i σ H hσ hH B hB hi).2

/-- A signed finite-past cylinder criterion for conditional expectation under
the literal restricted endpoint measure. The signed integral identities are
extended by uniqueness of trimmed vector measures. -/
theorem ae_eq_condExp_firstSlicePastMeasure_of_cylinders {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (K : CoupledQuenchedLaws d) (p : Vec d × FieldPair d)
    [IsFiniteMeasure (K (0, p.2))] (f g : CoupledSample d → ℝ)
    (hf : Integrable f (firstSlicePastMeasure Δ lam R i m K p))
    (hg : Integrable g (firstSlicePastMeasure Δ lam R i m K p))
    (hgm : AEStronglyMeasurable[finiteHistorySigma Δ m] g
      (firstSlicePastMeasure Δ lam R i m K p))
    (hcyl : ∀ S ∈ historyCylinders Δ m,
      (∫ z in S, g z ∂firstSlicePastMeasure Δ lam R i m K p) =
        ∫ z in S, f z ∂firstSlicePastMeasure Δ lam R i m K p) :
    g =ᵐ[firstSlicePastMeasure Δ lam R i m K p]
      (firstSlicePastMeasure Δ lam R i m K p)[f | finiteHistorySigma Δ m] := by
  let μ := firstSlicePastMeasure Δ lam R i m K p
  let hm := Probability.finiteHistorySigma_le (d := d) Δ m
  let : IsFiniteMeasure μ := isFiniteMeasure_firstSlicePastMeasure Δ lam R i m K p
  have heq : (μ.withDensityᵥ g).trim hm = (μ.withDensityᵥ f).trim hm := by
    apply VectorMeasure.ext_of_generateFrom (historyCylinders Δ m) ?_
      (finiteHistorySigma_eq_generateFrom_historyCylinders Δ m)
      (isPiSystem_historyCylinders Δ m) ?_
    · intro S hS
      have hs := measurableSet_historyCylinders Δ m hS
      rw [hg.withDensityᵥ_trim_eq_integral hm hs,
        hf.withDensityᵥ_trim_eq_integral hm hs]
      exact hcyl S hS
    · rw [hg.withDensityᵥ_trim_eq_integral hm MeasurableSet.univ,
        hf.withDensityᵥ_trim_eq_integral hm MeasurableSet.univ]
      exact hcyl Set.univ (univ_mem_historyCylinders Δ m)
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hf
    (fun _ _ _ => hg.integrableOn) ?_ hgm
  intro S hs _
  have h := congrArg (fun v => v S) heq
  rw [hg.withDensityᵥ_trim_eq_integral hm hs,
    hf.withDensityᵥ_trim_eq_integral hm hs] at h
  exact h

/-- Countably many genuine cylinder comparisons share one spatial-product
exceptional set, simultaneously for every measurable test at every index. -/
theorem ae_countable_firstSlicePastIntegral_eq_of_cylinders {d : ℕ} {ι : Type*}
    [Countable ι] (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ι → ℕ)
    (ν : ι → Vec d × FieldPair d → Measure (CoupledSample d))
    (hcyl : ∀ k, ∀ S ∈ historyCylinders Δ (m k),
      ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
        firstSlicePastMeasure Δ lam R i (m k) K p S = ν k p S) :
    ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), ∀ k,
      ∀ H : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ (m k)] H →
        firstSlicePastIntegral Δ lam R i (m k) K H p = ∫ z, H z ∂ν k p := by
  have hfinite : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
      IsFiniteMeasure (K (0, p.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hK.1] with p hp
    let := hp
    infer_instance
  exact ae_all_iff.mpr fun k =>
    ae_firstSlicePastIntegral_eq_of_cylinders ((volume : Measure (Vec d)).prod Q)
      id Δ lam R i (m k) K (ν k) hfinite (hcyl k)

/-- Separately, countably many origin comparisons that each hold for every
endpoint share one origin-environment exceptional set for all endpoints. -/
theorem ae_countable_all_endpoints_firstSlicePastIntegral_eq_of_cylinders
    {d : ℕ} {ι : Type*} [Countable ι] (Q : Measure (FieldPair d))
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ι → ℕ)
    (K : CoupledQuenchedLaws d)
    (ν : ι → Vec d × FieldPair d → Measure (CoupledSample d))
    (hfinite : ∀ᵐ ω ∂Q, IsFiniteMeasure (K (0, ω)))
    (hcyl : ∀ k, ∀ S ∈ historyCylinders Δ (m k), ∀ᵐ ω ∂Q, ∀ y,
      firstSlicePastMeasure Δ lam R i (m k) K (y, ω) S = ν k (y, ω) S) :
    ∀ᵐ ω ∂Q, ∀ k, ∀ (y : Vec d) (H : CoupledSample d → ℝ),
      Measurable[finiteHistorySigma Δ (m k)] H →
        firstSlicePastIntegral Δ lam R i (m k) K H (y, ω) =
          ∫ z, H z ∂ν k (y, ω) := by
  exact ae_all_iff.mpr fun k =>
    ae_all_endpoints_firstSlicePastIntegral_eq_of_cylinders Q Δ lam R i (m k) K
      (ν k) hfinite (hcyl k)

/-- A genuine comparison family consumes a parameter-dependent signed past
observation. Integrability and the L1 bound are taken under the actual joint
annealed and endpoint law, including unbounded observations. -/
theorem joint_firstSlicePastIntegral_eq_of_cylinders {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (ν : Vec d × FieldPair d → Measure (CoupledSample d))
    (hcyl : ∀ S ∈ historyCylinders Δ m,
      ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
        firstSlicePastMeasure Δ lam R i m K p S = ν p S)
    (H : (Vec d × FieldPair d) → CoupledSample d → ℝ)
    (hH : ∀ p, Measurable[finiteHistorySigma Δ m] (H p))
    (hjoint : Measurable (fun q : (Vec d × FieldPair d) × CoupledSample d =>
      H q.1 q.2))
    (hiJ : Integrable (fun q : (FieldPair d × CoupledSample d) × Vec d =>
      endpointPastTest Δ lam R i m (H (q.2, q.1.1)) q.2 q.1.2)
      ((annealedCoupledLaw Q K).prod volume)) :
    Integrable (fun p => ∫ z, H p z ∂ν p) ((volume : Measure (Vec d)).prod Q) ∧
    (∫ p, |∫ z, H p z ∂ν p| ∂((volume : Measure (Vec d)).prod Q)) ≤
      ∫ q, |endpointPastTest Δ lam R i m (H (q.2, q.1.1)) q.2 q.1.2|
        ∂((annealedCoupledLaw Q K).prod volume) ∧
    (∫ p, (∫ z, H p z ∂ν p) ∂((volume : Measure (Vec d)).prod Q)) =
      ∫ q, endpointPastTest Δ lam R i m (H (q.2, q.1.1)) q.2 q.1.2
        ∂((annealedCoupledLaw Q K).prod volume) := by
  have hfinite : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
      IsFiniteMeasure (K (0, p.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hK.1] with p hp
    let := hp
    infer_instance
  have he : (fun p : Vec d × FieldPair d =>
      ∫ z, endpointPastTest Δ lam R i m (H p) p.1 z ∂K (0, p.2)) =ᵐ[
        (volume : Measure (Vec d)).prod Q] fun p => ∫ z, H p z ∂ν p := by
    filter_upwards [ae_firstSlicePastIntegral_eq_of_cylinders
      ((volume : Measure (Vec d)).prod Q) id Δ lam R i m K ν hfinite hcyl] with p hp
    rw [integral_endpointPastTest]
    exact hp (H p) (hH p)
  have hJ : Measurable (fun q : (FieldPair d × CoupledSample d) × Vec d =>
      endpointPastTest Δ lam R i m (H (q.2, q.1.1)) q.2 q.1.2) := by
    have hE : MeasurableSet {q : (FieldPair d × CoupledSample d) × Vec d |
        q.2 ∈ endpointBall i R (q.1.2.1 ((m : ℝ≥0) * Δ))} :=
      (measurableSet_endpointBall_pair i R).preimage
        (((continuous_eval_const _).measurable.comp measurable_fst.snd.fst).prodMk
          measurable_snd)
    have hT : MeasurableSet {q : (FieldPair d × CoupledSample d) × Vec d |
        q.1.2 ∈ forcedBitTrialEvent Δ lam R i m} :=
      (measurableSet_forcedBitTrialEvent Δ lam R i m).preimage measurable_fst.snd
    exact ((hjoint.comp ((measurable_snd.prodMk measurable_fst.fst).prodMk
      measurable_fst.snd)).indicator hT).indicator hE
  have hr := integrable_origin_endpoint_integral Q K hK _ hJ hiJ
  refine ⟨hr.1.congr he, ?_, ?_⟩
  · rw [← integral_congr_ae (he.mono fun p hp => congrArg abs hp)]
    exact hr.2.1
  · rw [← integral_congr_ae he]
    exact hr.2.2


/-- Joint observations dominated by a single integrable past test inherit the
sharp normalized endpoint-ball L1 bound, including the forced trial cutoff. -/
theorem normalized_joint_firstSlicePastIntegral_le_of_dominated_cylinders {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (ν : Vec d × FieldPair d → Measure (CoupledSample d))
    (hcyl : ∀ S ∈ historyCylinders Δ m,
      ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
        firstSlicePastMeasure Δ lam R i m K p S = ν p S)
    (H : (Vec d × FieldPair d) → CoupledSample d → ℝ)
    (hH : ∀ p, Measurable[finiteHistorySigma Δ m] (H p))
    (hjoint : Measurable (fun q : (Vec d × FieldPair d) × CoupledSample d =>
      H q.1 q.2))
    (hiJ : Integrable (fun q : (FieldPair d × CoupledSample d) × Vec d =>
      endpointPastTest Δ lam R i m (H (q.2, q.1.1)) q.2 q.1.2)
      ((annealedCoupledLaw Q K).prod volume))
    (G : CoupledSample d → ℝ) (hG : Measurable G)
    (hiG : Integrable (fun q : FieldPair d × CoupledSample d => G q.2)
      (annealedCoupledLaw Q K)) (hdom : ∀ p z, |H p z| ≤ |G z|) :
    (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
      (∫ p, |∫ z, H p z ∂ν p| ∂((volume : Measure (Vec d)).prod Q)) ≤
      ∫ q, |((forcedBitTrialEvent Δ lam R i m).indicator G) q.2|
        ∂annealedCoupledLaw Q K := by
  let μ := annealedCoupledLaw Q K
  let : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q K hK
  let F : FieldPair d × CoupledSample d → ℝ := fun q =>
    |((forcedBitTrialEvent Δ lam R i m).indicator G) q.2|
  let X : FieldPair d × CoupledSample d → Vec d := fun q => q.2.1 ((m : ℝ≥0) * Δ)
  have hX : Measurable X := (continuous_eval_const _).measurable.comp
    (measurable_fst.comp measurable_snd)
  have hF : Measurable F := by
    exact (((hG.indicator (measurableSet_forcedBitTrialEvent Δ lam R i m)).comp
      measurable_snd).norm)
  have hiF : Integrable F μ := by
    apply (hiG.indicator ((measurableSet_forcedBitTrialEvent Δ lam R i m).preimage
      measurable_snd)).norm.congr
    filter_upwards [] with q
    by_cases h : q.2 ∈ forcedBitTrialEvent Δ lam R i m <;>
      simp [F, h, Real.norm_eq_abs]
  have hiB := integrable_endpointBall_indicator_of_integrable μ i R hR X hX F hF hiF
  have hb : (∫ q, |endpointPastTest Δ lam R i m (H (q.2, q.1.1)) q.2 q.1.2|
      ∂μ.prod volume) ≤ (volume (endpointBall i R (0 : Vec d))).toReal * ∫ q, F q ∂μ := by
    rw [← integral_endpointBall_indicator_of_integrable μ i R hR X hX F hF hiF]
    apply integral_mono (by simpa only [Real.norm_eq_abs] using hiJ.norm) hiB
    intro q
    by_cases hy : q.2 ∈ endpointBall i R (X q.1)
    · by_cases ht : q.1.2 ∈ forcedBitTrialEvent Δ lam R i m
      · simpa [endpointPastTest, F, X, hy, ht] using hdom (q.2, q.1.1) q.1.2
      · simp [endpointPastTest, F, X, hy, ht]
    · simp [endpointPastTest, X, hy, F]
  have hV : 0 < (volume (endpointBall i R (0 : Vec d))).toReal :=
    ENNReal.toReal_pos (endpointBall_volume_pos i R hR _).ne'
      (endpointBall_volume_ne_top i R hR _)
  have hj := (joint_firstSlicePastIntegral_eq_of_cylinders Q K hK Δ lam R i m ν
    hcyl H hH hjoint hiJ).2.1
  calc
    _ ≤ (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
        ((volume (endpointBall i R (0 : Vec d))).toReal * ∫ q, F q ∂μ) :=
      mul_le_mul_of_nonneg_left (hj.trans hb) (inv_nonneg.mpr hV.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hV.ne', one_mul]

/-- Countable local limit versions and actual cylinder comparisons share one
spatial-product event. The origin event remains separate and applies to every
endpoint; the signed integrals of the two versions agree. -/
theorem exists_countable_local_versions_with_cylinder_integrals {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ → ℕ)
    (H : ℕ → ℕ → CoupledSample d → ℝ) (F : ℕ → CoupledSample d → ℝ)
    (hH : ∀ k n, Measurable[finiteHistorySigma Δ (m k)] (H k n))
    (hF : ∀ k, Measurable[finiteHistorySigma Δ (m k)] (F k))
    (C : ℕ → ℝ) (hC : ∀ k n z, |H k n z| ≤ C k)
    (hlim : ∀ k z, Filter.Tendsto (fun n => H k n z) Filter.atTop (nhds (F k z)))
    (hlocal : ∀ k n (y : Vec d), ∃ a : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
      (fun ω => firstSlicePastIntegral Δ lam R i (m k) K (H k n) (y, ω)) =ᵐ[Q] a)
    (ν : ℕ → Vec d × FieldPair d → Measure (CoupledSample d))
    (hcyl : ∀ k, ∀ S ∈ historyCylinders Δ (m k),
      ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
        firstSlicePastMeasure Δ lam R i (m k) K p S = ν k p S) :
    ∃ A : ℕ → Vec d × FieldPair d → ℝ,
      (∀ k, Measurable (A k) ∧ Integrable (A k) ((volume : Measure (Vec d)).prod Q) ∧
        ∀ y : Vec d, ∃ a : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
          Integrable a Q ∧ (fun ω => A k (y, ω)) =ᵐ[Q] a) ∧
      (∀ᵐ ω ∂Q, ∀ k y, A k (y, ω) =
        firstSlicePastIntegral Δ lam R i (m k) K (F k) (y, ω)) ∧
      (∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), ∀ k,
        A k p = ∫ z, F k z ∂ν k p) ∧
      ∀ k, Integrable (fun p => ∫ z, F k z ∂ν k p)
          ((volume : Measure (Vec d)).prod Q) ∧
        (∫ p, A k p ∂((volume : Measure (Vec d)).prod Q)) =
          ∫ p, (∫ z, F k z ∂ν k p) ∂((volume : Measure (Vec d)).prod Q) := by
  obtain ⟨A, hA, horigin, hproduct⟩ :=
    exists_countable_joint_integrable_local_firstSlicePastIntegral_versions_of_limits
      Q K hK Δ lam R hR i m H F hH C hC hlim hlocal
  have hc := ae_countable_firstSlicePastIntegral_eq_of_cylinders Q K hK Δ lam R i m ν hcyl
  have he : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), ∀ k,
      A k p = ∫ z, F k z ∂ν k p := by
    filter_upwards [hproduct, hc] with p hp hc
    intro k
    exact (hp k).trans (hc k (F k) (hF k))
  refine ⟨A, ?_, horigin, he, ?_⟩
  · intro k
    refine ⟨(hA k).1, (hA k).2.2.1, ?_⟩
    intro y
    obtain ⟨a, ha, _, hi, heq⟩ := (hA k).2.2.2 y
    exact ⟨a, ha, hi, heq⟩
  · intro k
    have hk : A k =ᵐ[((volume : Measure (Vec d)).prod Q)]
        fun p => ∫ z, F k z ∂ν k p := he.mono fun p hp => hp k
    exact ⟨(hA k).2.2.1.congr hk, integral_congr_ae hk⟩

/-- Integrable signed weights preserve the countable comparison identities.
When their environment sections are local, the weighted representatives also
have local sections, using the same moving half-space as the past factor. -/
theorem exists_countable_weighted_local_versions_of_cylinders {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ → ℕ)
    (H : ℕ → ℕ → CoupledSample d → ℝ) (F : ℕ → CoupledSample d → ℝ)
    (hH : ∀ k n, Measurable[finiteHistorySigma Δ (m k)] (H k n))
    (hF : ∀ k, Measurable[finiteHistorySigma Δ (m k)] (F k))
    (C : ℕ → ℝ) (hC : ∀ k n z, |H k n z| ≤ C k)
    (hlim : ∀ k z, Filter.Tendsto (fun n => H k n z) Filter.atTop (nhds (F k z)))
    (hlocal : ∀ k n (y : Vec d), ∃ a : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
      (fun ω => firstSlicePastIntegral Δ lam R i (m k) K (H k n) (y, ω)) =ᵐ[Q] a)
    (ν : ℕ → Vec d × FieldPair d → Measure (CoupledSample d))
    (hcyl : ∀ k, ∀ S ∈ historyCylinders Δ (m k),
      ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
        firstSlicePastMeasure Δ lam R i (m k) K p S = ν k p S)
    (w : ℕ → Vec d × FieldPair d → ℝ)
    (hw : ∀ k, Integrable (w k) ((volume : Measure (Vec d)).prod Q))
    (hwlocal : ∀ k y, Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}]
      (fun ω => w k (y, ω)))
    (hwsection : ∀ k y, Integrable (fun ω => w k (y, ω)) Q) :
    ∃ A : ℕ → Vec d × FieldPair d → ℝ,
      (∀ᵐ ω ∂Q, ∀ k y, A k (y, ω) =
        firstSlicePastIntegral Δ lam R i (m k) K (F k) (y, ω)) ∧
      (∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), ∀ k,
        A k p = ∫ z, F k z ∂ν k p) ∧
      (∀ k, Integrable (fun p => w k p * A k p) ((volume : Measure (Vec d)).prod Q) ∧
        Integrable (fun p => w k p * (∫ z, F k z ∂ν k p))
          ((volume : Measure (Vec d)).prod Q) ∧
        (∫ p, w k p * A k p ∂((volume : Measure (Vec d)).prod Q)) =
          ∫ p, w k p * (∫ z, F k z ∂ν k p) ∂((volume : Measure (Vec d)).prod Q)) ∧
      ∀ k y, ∃ a : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
        Integrable a Q ∧ (fun ω => w k (y, ω) * A k (y, ω)) =ᵐ[Q] a := by
  obtain ⟨A, hA, horigin, hproduct⟩ :=
    exists_countable_joint_integrable_local_firstSlicePastIntegral_versions_of_limits
      Q K hK Δ lam R hR i m H F hH C hC hlim hlocal
  have hc := ae_countable_firstSlicePastIntegral_eq_of_cylinders Q K hK Δ lam R i m ν hcyl
  have he : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), ∀ k,
      A k p = ∫ z, F k z ∂ν k p := by
    filter_upwards [hproduct, hc] with p hp hc
    intro k
    exact (hp k).trans (hc k (F k) (hF k))
  refine ⟨A, horigin, he, ?_, ?_⟩
  · intro k
    have hi : Integrable (fun p => w k p * A k p) ((volume : Measure (Vec d)).prod Q) :=
      (hw k).mul_bdd (hA k).1.aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => by
          simpa only [Real.norm_eq_abs] using (hA k).2.1 p)
    have hk : (fun p => w k p * A k p) =ᵐ[((volume : Measure (Vec d)).prod Q)]
        fun p => w k p * (∫ z, F k z ∂ν k p) :=
      he.mono fun p hp => congrArg (w k p * ·) (hp k)
    exact ⟨hi, hi.congr hk, integral_congr_ae hk⟩
  · intro k y
    obtain ⟨a, ha, hab, _, heq⟩ := (hA k).2.2.2 y
    have ham : Measurable a := ha.mono (Probability.localSigma_le_borel _) le_rfl
    refine ⟨fun ω => w k (y, ω) * a ω, (hwlocal k y).mul ha, ?_, ?_⟩
    · exact (hwsection k y).mul_bdd ham.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hab ω)
    · exact heq.mono fun ω hω => congrArg (w k (y, ω) * ·) hω

/-- Annealed L1 observations are integrable on every restricted origin fibre
and on every genuine comparison measure with the same history cylinders.
All counts and endpoints share one origin event, independently of the spatial
product event obtained from it. -/
theorem ae_all_endpoints_integrable_comparisons_of_cylinders {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ → ℕ)
    (H : ℕ → CoupledSample d → ℝ)
    (hH : ∀ k, Measurable[finiteHistorySigma Δ (m k)] (H k))
    (hiH : ∀ k, Integrable (fun q : FieldPair d × CoupledSample d => H k q.2)
      (annealedCoupledLaw Q K))
    (ν : ℕ → Vec d × FieldPair d → Measure (CoupledSample d))
    (hcyl : ∀ k, ∀ S ∈ historyCylinders Δ (m k), ∀ᵐ ω ∂Q, ∀ y,
      firstSlicePastMeasure Δ lam R i (m k) K (y, ω) S = ν k (y, ω) S) :
    (∀ᵐ ω ∂Q, ∀ k y,
      Integrable (H k) (firstSlicePastMeasure Δ lam R i (m k) K (y, ω)) ∧
      Integrable (H k) (ν k (y, ω)) ∧
      (∫ z, H k z ∂firstSlicePastMeasure Δ lam R i (m k) K (y, ω)) =
        ∫ z, H k z ∂ν k (y, ω)) ∧
    (∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), ∀ k,
      Integrable (H k) (firstSlicePastMeasure Δ lam R i (m k) K p) ∧
      Integrable (H k) (ν k p) ∧
      (∫ z, H k z ∂firstSlicePastMeasure Δ lam R i (m k) K p) =
        ∫ z, H k z ∂ν k p) := by
  have hc (k : ℕ) : ∀ᵐ ω ∂Q, ∀ S ∈ historyCylinders Δ (m k), ∀ y,
      firstSlicePastMeasure Δ lam R i (m k) K (y, ω) S = ν k (y, ω) S := by
    let : Countable (historyCylinders (d := d) Δ (m k)) :=
      (countable_historyCylinders Δ (m k)).to_subtype
    have ht : ∀ᵐ ω ∂Q, ∀ S : historyCylinders (d := d) Δ (m k), ∀ y,
        firstSlicePastMeasure Δ lam R i (m k) K (y, ω) S = ν k (y, ω) S :=
      ae_all_iff.mpr fun S => hcyl k S S.2
    filter_upwards [ht] with ω hω
    intro S hS y
    exact hω ⟨S, hS⟩ y
  have he : ∀ᵐ ω ∂Q, ∀ k y,
      Integrable (H k) (firstSlicePastMeasure Δ lam R i (m k) K (y, ω)) ∧
      Integrable (H k) (ν k (y, ω)) ∧
      (∫ z, H k z ∂firstSlicePastMeasure Δ lam R i (m k) K (y, ω)) =
        ∫ z, H k z ∂ν k (y, ω) := by
    filter_upwards [hK.1, ae_all_iff.mpr hc,
      ae_all_iff.mpr fun k => ae_integrable_origin_of_annealed_integrable Q K hK (H k) (hiH k)]
      with ω hp hc' hi
    let : IsProbabilityMeasure (K (0, ω)) := hp
    intro k y
    let μ := firstSlicePastMeasure Δ lam R i (m k) K (y, ω)
    let hm := Probability.finiteHistorySigma_le (d := d) Δ (m k)
    let : IsFiniteMeasure μ := isFiniteMeasure_firstSlicePastMeasure Δ lam R i (m k) K (y, ω)
    have hμ : Integrable (H k) μ := (hi k).mono_measure
      (firstSlicePastMeasure_le Δ lam R i (m k) K (y, ω))
    have htrim : μ.trim hm = (ν k (y, ω)).trim hm := by
      apply @Measure.ext _ (finiteHistorySigma Δ (m k))
      intro S hS
      rw [trim_measurableSet_eq _ hS, trim_measurableSet_eq _ hS]
      exact measure_eq_on_history_of_cylinders Δ (m k) μ (ν k (y, ω))
        (fun S hS => hc' k S hS y) hS
    have hν : Integrable (H k) (ν k (y, ω)) := by
      apply integrable_of_integrable_trim hm
      rw [← htrim]
      exact Integrable.trim hm hμ (hH k).stronglyMeasurable
    exact ⟨hμ, hν, integral_eq_on_history_of_cylinders Δ (m k) μ (ν k (y, ω))
      (fun S hS => hc' k S hS y) (H k) (hH k)⟩
  refine ⟨he, ?_⟩
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae he] with p hp
  exact fun k => hp k p.1


/-- Cylinder comparison transports signed truncations and their limits to the
actual comparison fibres, on one event for all observations and endpoints. -/
theorem ae_all_endpoints_comparison_truncations {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ → ℕ)
    (H : ℕ → CoupledSample d → ℝ)
    (hH : ∀ k, Measurable[finiteHistorySigma Δ (m k)] (H k))
    (hiH : ∀ k, Integrable (fun q : FieldPair d × CoupledSample d => H k q.2)
      (annealedCoupledLaw Q K))
    (ν : ℕ → Vec d × FieldPair d → Measure (CoupledSample d))
    (hcyl : ∀ k, ∀ S ∈ historyCylinders Δ (m k), ∀ᵐ ω ∂Q, ∀ y,
      firstSlicePastMeasure Δ lam R i (m k) K (y, ω) S = ν k (y, ω) S) :
    ∀ᵐ ω ∂Q, ∀ k y,
      Integrable (H k) (ν k (y, ω)) ∧
      (∀ n, firstSlicePastIntegral Δ lam R i (m k) K
        (signedTestTruncation n (H k)) (y, ω) =
          ∫ z, signedTestTruncation n (H k) z ∂ν k (y, ω)) ∧
      Filter.Tendsto (fun n => ∫ z, signedTestTruncation n (H k) z ∂ν k (y, ω))
        Filter.atTop (nhds (∫ z, H k z ∂ν k (y, ω))) := by
  have hf : ∀ᵐ ω ∂Q, IsFiniteMeasure (K (0, ω)) := by
    filter_upwards [hK.1] with ω hω
    let : IsProbabilityMeasure (K (0, ω)) := hω
    infer_instance
  filter_upwards [
    (ae_all_endpoints_integrable_comparisons_of_cylinders Q K hK Δ lam R i m H hH hiH ν hcyl).1,
    ae_countable_all_endpoints_firstSlicePastIntegral_eq_of_cylinders Q Δ lam R i m K ν hf hcyl,
    ae_all_iff.mpr fun k => ae_all_endpoints_tendsto_firstSlicePastIntegral_truncation
      Q K hK Δ lam R i (m k) (H k)
      ((hH k).mono (Probability.finiteHistorySigma_le Δ (m k)) le_rfl) (hiH k)]
      with ω hi he ht
  intro k y
  have htr (n : ℕ) : Measurable[finiteHistorySigma Δ (m k)]
      (signedTestTruncation n (H k)) := by
    let := finiteHistorySigma (d := d) Δ (m k)
    exact measurable_signedTestTruncation n (H k) (hH k)
  have hetr n := he k y (signedTestTruncation n (H k)) (htr n)
  refine ⟨(hi k y).2.1, hetr, ?_⟩
  have hc := ht k y
  simp_rw [hetr] at hc
  rw [he k y (H k) (hH k)] at hc
  exact hc


/-- All finite sums of a countable family of integrable past tests retain
integrability and comparison on the same event and at every endpoint. -/
theorem ae_all_endpoints_integrable_finite_sums_of_cylinders {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (H : ℕ → CoupledSample d → ℝ)
    (hH : ∀ k, Measurable[finiteHistorySigma Δ m] (H k))
    (hiH : ∀ k, Integrable (fun q : FieldPair d × CoupledSample d => H k q.2)
      (annealedCoupledLaw Q K))
    (ν : Vec d × FieldPair d → Measure (CoupledSample d))
    (hcyl : ∀ S ∈ historyCylinders Δ m, ∀ᵐ ω ∂Q, ∀ y,
      firstSlicePastMeasure Δ lam R i m K (y, ω) S = ν (y, ω) S) :
    ∀ᵐ ω ∂Q, ∀ y (s : Finset ℕ),
      Integrable (fun z => ∑ k ∈ s, H k z)
        (firstSlicePastMeasure Δ lam R i m K (y, ω)) ∧
      Integrable (fun z => ∑ k ∈ s, H k z) (ν (y, ω)) ∧
      (∫ z, ∑ k ∈ s, H k z ∂firstSlicePastMeasure Δ lam R i m K (y, ω)) =
        ∫ z, ∑ k ∈ s, H k z ∂ν (y, ω) := by
  filter_upwards [(ae_all_endpoints_integrable_comparisons_of_cylinders
    Q K hK Δ lam R i (fun _ => m) H hH hiH (fun _ => ν)
    (fun _ => hcyl)).1] with ω hω
  intro y s
  have hμ k : Integrable (H k) (firstSlicePastMeasure Δ lam R i m K (y, ω)) :=
    (hω k y).1
  have hν k : Integrable (H k) (ν (y, ω)) := (hω k y).2.1
  refine ⟨integrable_finsetSum s (fun k _ => hμ k),
    integrable_finsetSum s (fun k _ => hν k), ?_⟩
  rw [integral_finsetSum s (fun k _ => hμ k),
    integral_finsetSum s (fun k _ => hν k)]
  exact Finset.sum_congr rfl (fun k _ => (hω k y).2.2)

/-- Cylinder comparisons transport the signed, countable stopped-branch
endpoint sum to comparison fibres. Fibre integrability holds simultaneously
at every endpoint on one origin event and on a spatial-product event. -/
theorem hasSum_integrable_comparison_meshBranch_endpoint_pairings {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (σ : CoupledSample d → ℕ∞) (H : ℕ → CoupledSample d → ℝ)
    (hσ : ∀ k, MeasurableSet[finiteHistorySigma Δ k] {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable[finiteHistorySigma Δ k] (H k))
    (hbranch : ∀ k, Integrable
      (fun q : FieldPair d × CoupledSample d => meshBranchTest σ H k q.2)
      (annealedCoupledLaw Q K))
    (B : ℕ → Vec d × FieldPair d → ℝ) (hB : ∀ k, Measurable (B k))
    (hi : Integrable
      (stoppedMeshTest (fun q : (FieldPair d × CoupledSample d) × Vec d => σ q.1.2)
        (fun k q => endpointPastTest Δ lam R i k (H k) q.2 q.1.2 * B k (q.2, q.1.1)))
      ((annealedCoupledLaw Q K).prod volume))
    (ν : ℕ → Vec d × FieldPair d → Measure (CoupledSample d))
    (hcyl : ∀ k, ∀ S ∈ historyCylinders Δ k, ∀ᵐ ω ∂Q, ∀ y,
      firstSlicePastMeasure Δ lam R i k K (y, ω) S = ν k (y, ω) S) :
    (∀ᵐ ω ∂Q, ∀ k y, Integrable (meshBranchTest σ H k) (ν k (y, ω))) ∧
    (∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), ∀ k,
      Integrable (meshBranchTest σ H k) (ν k p)) ∧
    (∀ k, Integrable (fun p => (∫ z, meshBranchTest σ H k z ∂ν k p) * B k p)
      ((volume : Measure (Vec d)).prod Q)) ∧
    HasSum (fun k => (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
      ∫ y, ∫ ω, (∫ z, meshBranchTest σ H k z ∂ν k (y, ω)) * B k (y, ω) ∂Q)
      ((volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
        ∫ q, stoppedMeshTest
          (fun q : (FieldPair d × CoupledSample d) × Vec d => σ q.1.2)
          (fun k q => endpointPastTest Δ lam R i k (H k) q.2 q.1.2 * B k (q.2, q.1.1)) q
          ∂((annealedCoupledLaw Q K).prod volume)) := by
  have hc := ae_all_endpoints_integrable_comparisons_of_cylinders Q K hK Δ lam R i
    (fun k => k) (meshBranchTest σ H)
    (measurable_meshBranchTest_history Δ σ H hσ hH) hbranch ν hcyl
  have hs := hasSum_integrable_meshBranchPastIntegral_endpoint_pairings
    Q K hK Δ lam R i σ H hσ hH B hB hi
  have he (k : ℕ) : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
      firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) p * B k p =
        (∫ z, meshBranchTest σ H k z ∂ν k p) * B k p := by
    filter_upwards [hc.2] with p hp
    rw [← integral_firstSlicePastMeasure]
    exact congrArg (fun x => x * B k p) (hp k).2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hc.1] with ω hω
    exact fun k y => (hω k y).2.1
  · filter_upwards [hc.2] with p hp
    exact fun k => (hp k).2.1
  · exact fun k => (hs.1 k).congr (he k)
  · have heint (k : ℕ) :
        (∫ y, ∫ ω, firstSlicePastIntegral Δ lam R i k K (meshBranchTest σ H k) (y, ω) *
          B k (y, ω) ∂Q) =
        ∫ y, ∫ ω, (∫ z, meshBranchTest σ H k z ∂ν k (y, ω)) * B k (y, ω) ∂Q := by
      apply integral_congr_ae
      filter_upwards [] with y
      apply integral_congr_ae
      filter_upwards [hc.1] with ω hω
      rw [← integral_firstSlicePastMeasure]
      exact congrArg (fun x => x * B k (y, ω)) (hω k y).2.2
    simpa only [heint] using hs.2

/-- The signed comparison-fibre series recovers the selected annealed
moving-ball average, including the infinite-selector branch. -/
theorem hasSum_integrable_comparison_meshBranch_endpoint_averages {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (σ : CoupledSample d → ℕ∞) (H : ℕ → CoupledSample d → ℝ)
    (hσ : ∀ k, MeasurableSet[finiteHistorySigma Δ k] {z | σ z = (k : ℕ∞)})
    (hH : ∀ k, Measurable[finiteHistorySigma Δ k] (H k))
    (hbranch : ∀ k, Integrable
      (fun q : FieldPair d × CoupledSample d => meshBranchTest σ H k q.2)
      (annealedCoupledLaw Q K))
    (B : ℕ → Vec d × FieldPair d → ℝ) (hB : ∀ k, Measurable (B k))
    (hi : Integrable
      (stoppedMeshTest (fun q : (FieldPair d × CoupledSample d) × Vec d => σ q.1.2)
        (fun k q => endpointPastTest Δ lam R i k (H k) q.2 q.1.2 * B k (q.2, q.1.1)))
      ((annealedCoupledLaw Q K).prod volume))
    (ν : ℕ → Vec d × FieldPair d → Measure (CoupledSample d))
    (hcyl : ∀ k, ∀ S ∈ historyCylinders Δ k, ∀ᵐ ω ∂Q, ∀ y,
      firstSlicePastMeasure Δ lam R i k K (y, ω) S = ν k (y, ω) S) :
    Integrable
      (stoppedMeshTest (fun q : FieldPair d × CoupledSample d => σ q.2)
        (fun k q => ((forcedBitTrialEvent Δ lam R i k).indicator (H k)) q.2 *
          endpointAverage i R (q.2.1 ((k : ℝ≥0) * Δ)) (fun y => B k (y, q.1))))
      (annealedCoupledLaw Q K) ∧
    HasSum (fun k => (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
      ∫ y, ∫ ω, (∫ z, meshBranchTest σ H k z ∂ν k (y, ω)) * B k (y, ω) ∂Q)
      (∫ q, stoppedMeshTest (fun q : FieldPair d × CoupledSample d => σ q.2)
        (fun k q => ((forcedBitTrialEvent Δ lam R i k).indicator (H k)) q.2 *
          endpointAverage i R (q.2.1 ((k : ℝ≥0) * Δ)) (fun y => B k (y, q.1))) q
        ∂annealedCoupledLaw Q K) := by
  have hc := hasSum_integrable_comparison_meshBranch_endpoint_pairings
    Q K hK Δ lam R i σ H hσ hH hbranch B hB hi ν hcyl
  have hp := hasSum_integrable_meshBranchPastIntegral_endpoint_pairings
    Q K hK Δ lam R i σ H hσ hH B hB hi
  have ha := hasSum_integrable_meshBranchPastIntegral_endpoint_averages
    Q K hK Δ lam R i σ H hσ hH B hB hi
  refine ⟨ha.1, ?_⟩
  rw [← hp.2.unique ha.2]
  exact hc.2.2.2

/-- For almost every endpoint, an integrable signed history has an integrable
local representative that also represents its cylinder comparison integral. -/
theorem ae_endpoint_integrable_local_version_of_truncations_and_cylinders {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable[finiteHistorySigma Δ m] H)
    (hiH : Integrable (fun q : FieldPair d × CoupledSample d => H q.2)
      (annealedCoupledLaw Q K))
    (hlocal : ∀ n (y : Vec d), ∃ a : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K (signedTestTruncation n H)
        (y, ω)) =ᵐ[Q] a)
    (ν : Vec d × FieldPair d → Measure (CoupledSample d))
    (hcyl : ∀ S ∈ historyCylinders Δ m,
      ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
        firstSlicePastMeasure Δ lam R i m K p S = ν p S) :
    ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ a : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
      Integrable a Q ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q] a ∧
      (fun ω => ∫ z, H z ∂ν (y, ω)) =ᵐ[Q] a := by
  obtain ⟨A, hA, hiA, horigin, hproduct, hsections⟩ :=
    exists_joint_integrable_local_firstSlicePastIntegral_version_of_truncations
      Q K hK Δ lam R hR i m H
      (hH.mono (Probability.finiteHistorySigma_le Δ m) le_rfl) hiH hlocal
  have hc := ae_countable_firstSlicePastIntegral_eq_of_cylinders Q K hK Δ lam R i
    (fun _ : Unit => m) (fun _ => ν) (fun _ => hcyl)
  have he : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
      A p = ∫ z, H z ∂ν p := by
    filter_upwards [hproduct, hc] with p hp hc
    exact hp.trans (hc () H hH)
  filter_upwards [hiA.prod_right_ae, Measure.ae_ae_of_ae_prod hproduct,
    Measure.ae_ae_of_ae_prod he] with y hi hy hc
  obtain ⟨a, ha, hae⟩ := hsections y
  refine ⟨a, ha, hi.congr hae, ?_, ?_⟩
  · filter_upwards [hy, hae] with ω hy ha
    exact hy.symm.trans ha
  · filter_upwards [hc, hae] with ω hc ha
    exact hc.symm.trans ha


/-- A countable family of signed integrable histories has simultaneous joint
versions and endpoint-local integrable representatives under cylinder comparison. -/
theorem exists_countable_signed_local_versions_of_cylinders {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ → ℕ)
    (H : ℕ → CoupledSample d → ℝ)
    (hH : ∀ k, Measurable[finiteHistorySigma Δ (m k)] (H k))
    (hiH : ∀ k, Integrable (fun q : FieldPair d × CoupledSample d => H k q.2)
      (annealedCoupledLaw Q K))
    (hlocal : ∀ k n (y : Vec d), ∃ a : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
      (fun ω => firstSlicePastIntegral Δ lam R i (m k) K (signedTestTruncation n (H k))
        (y, ω)) =ᵐ[Q] a)
    (ν : ℕ → Vec d × FieldPair d → Measure (CoupledSample d))
    (hcyl : ∀ k, ∀ S ∈ historyCylinders Δ (m k),
      ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q),
        firstSlicePastMeasure Δ lam R i (m k) K p S = ν k p S) :
    ∃ A : ℕ → Vec d × FieldPair d → ℝ,
      (∀ k, Measurable (A k) ∧ Integrable (A k) ((volume : Measure (Vec d)).prod Q)) ∧
      (∀ᵐ ω ∂Q, ∀ k y, A k (y, ω) =
        firstSlicePastIntegral Δ lam R i (m k) K (H k) (y, ω)) ∧
      (∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), ∀ k,
        A k p = ∫ z, H k z ∂ν k p) ∧
      ∀ᵐ y ∂(volume : Measure (Vec d)), ∀ k, ∃ a : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
        Integrable a Q ∧ (fun ω => A k (y, ω)) =ᵐ[Q] a := by
  choose A hA hiA horigin hproduct hsections using fun k =>
    exists_joint_integrable_local_firstSlicePastIntegral_version_of_truncations
      Q K hK Δ lam R hR i (m k) (H k)
      ((hH k).mono (Probability.finiteHistorySigma_le Δ (m k)) le_rfl) (hiH k) (hlocal k)
  have hc := ae_countable_firstSlicePastIntegral_eq_of_cylinders Q K hK Δ lam R i m ν hcyl
  refine ⟨A, fun k => ⟨hA k, hiA k⟩, ?_, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr horigin] with ω hω
    exact fun k => hω k
  · filter_upwards [ae_all_iff.mpr hproduct, hc] with p hp hc
    exact fun k => (hp k).trans (hc k (H k) (hH k))
  · filter_upwards [ae_all_iff.mpr (fun k => (hiA k).prod_right_ae)] with y hy
    intro k
    obtain ⟨a, ha, he⟩ := hsections k y
    exact ⟨a, ha, (hy k).congr he, he⟩

end IntegrableEndpointTests

/-- Stopped-map equality for a pair of supplied laws implies both supported
one-interval comparisons. This does not establish stopped-law locality. -/
theorem integral_pair_eq_of_locality_stopped_law_eq {d : ℕ}
    (Δ : ℝ≥0) (R v : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (y : Vec d) (ω ω' : FieldPair d)
    (hstop : (P (y, ω)).map (Diffusion.localityStoppedPath {x | x i < v + 3 * R}) =
      (P (y, ω')).map (Diffusion.localityStoppedPath {x | x i < v + 3 * R}))
    (F : Path d → ℝ) (hF : Measurable F)
    (hsegment : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ')
    (hsupport : ∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) :
    (∫ γ, F γ ∂P (y, ω)) = (∫ γ, F γ ∂P (y, ω')) ∧
    (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω) =
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω' := by
  let U : Set (Vec d) := {x | x i < v + 3 * R}
  have hU : IsOpen U := isOpen_lt (continuous_apply i) continuous_const
  have hm : Measurable (Diffusion.localityStoppedPath U) :=
    EinsteinFull.measurable_localityStoppedPath U hU
  have hstay : ∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ U := by
    intro γ hne t ht
    change γ t i < v + 3 * R
    have hle := hsupport γ hne t ht
    linarith
  have hfirst := integral_supported_segment_eq_of_stoppedLaw_eq U hU Δ
    (P (y, ω)) (P (y, ω')) hm hstop F hF hsegment hstay
  have hkill : y i < v - 8 * R →
      (Renewal.killedSegmentLaw Δ R i P y ω).map (Diffusion.stopPathAt Δ) =
        (Renewal.killedSegmentLaw Δ R i P y ω').map (Diffusion.stopPathAt Δ) := by
    intro hlow
    have hVU : couplingRegion i R y ⊆ U :=
      couplingRegion_subset_past_halfSpace i R v y hlow
    simpa only [Renewal.killedSegmentLaw] using
      Diffusion.map_restrict_stopPathAt_eq_of_stoppedLaw_eq U
        (couplingRegion i R y) hU (isOpen_couplingRegion i R y) hVU Δ
        (P (y, ω)) (P (y, ω')) hm hstop
  exact ⟨hfirst, integral_supported_bridge_eq_of_low_killed_stopped_law_eq
    Δ R v i P P y ω ω' hkill F hF hsegment hsupport⟩

/-- For two coupled fibres, stopped-map equality of the same supplied path
laws gives the full supported finite-history comparison. -/
theorem integral_supported_finite_history_eq_assuming_stopped_law_eq {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R v : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (x : Vec d) (ω ω' : FieldPair d)
    [IsProbabilityMeasure (K (x, ω))] [IsProbabilityMeasure (K (x, ω'))]
    (hstart : ∀ᵐ z ∂K (x, ω), z.1 0 = x)
    (hstart' : ∀ᵐ z ∂K (x, ω'), z.1 0 = x)
    (hone : Renewal.OneIntervalKernelAt Δ δ R i P K (x, ω))
    (hone' : Renewal.OneIntervalKernelAt Δ δ R i P K (x, ω'))
    (hPprob : ∀ y : Vec d, IsProbabilityMeasure (P (y, ω)))
    (hstop : ∀ y : Vec d, y i ≤ v →
      (P (y, ω)).map (Diffusion.localityStoppedPath {z | z i < v + 3 * R}) =
        (P (y, ω')).map (Diffusion.localityStoppedPath {z | z i < v + 3 * R})) :
    ∀ n : ℕ, ∀ F : CoupledSample d → ℝ,
      Measurable[finiteHistorySigma Δ n] F → BoundedRealTest F →
      (∀ z, z ∉ pastBelow Δ n i v → F z = 0) →
      (∫ z, F z ∂K (x, ω)) = ∫ z, F z ∂K (x, ω') := by
  apply integral_supported_finite_history_eq_of_scalar_comparison Δ hΔ δ R i P P K K
    x ω ω' hstart hstart' hone hone' v hPprob
  intro F hF _ hsegment hsupport y hy
  exact integral_pair_eq_of_locality_stopped_law_eq Δ R v hR i P y ω ω'
    (hstop y hy) F hF hsegment hsupport

/-- Every finite-history event has the same mass on the closed past cutoff,
conditional on stopped-map equality for all low starts. -/
theorem supported_finite_history_event_eq_assuming_stopped_law_eq {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R v : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (x : Vec d) (ω ω' : FieldPair d)
    [IsProbabilityMeasure (K (x, ω))] [IsProbabilityMeasure (K (x, ω'))]
    (hstart : ∀ᵐ z ∂K (x, ω), z.1 0 = x)
    (hstart' : ∀ᵐ z ∂K (x, ω'), z.1 0 = x)
    (hone : Renewal.OneIntervalKernelAt Δ δ R i P K (x, ω))
    (hone' : Renewal.OneIntervalKernelAt Δ δ R i P K (x, ω'))
    (hPprob : ∀ y : Vec d, IsProbabilityMeasure (P (y, ω)))
    (hstop : ∀ y : Vec d, y i ≤ v →
      (P (y, ω)).map (Diffusion.localityStoppedPath {z | z i < v + 3 * R}) =
        (P (y, ω')).map (Diffusion.localityStoppedPath {z | z i < v + 3 * R}))
    (n : ℕ) (S : Set (CoupledSample d)) (hS : MeasurableSet[finiteHistorySigma Δ n] S) :
    K (x, ω) (S ∩ pastBelow Δ n i v) = K (x, ω') (S ∩ pastBelow Δ n i v) := by
  let T := S ∩ pastBelow Δ n i v
  have hT : MeasurableSet[finiteHistorySigma Δ n] T :=
    hS.inter (measurableSet_pastBelow_history Δ n i v)
  have hTa : MeasurableSet T := (Probability.finiteHistorySigma_le Δ n) T hT
  have he := integral_supported_finite_history_eq_assuming_stopped_law_eq
    Δ hΔ δ R v hR i P K x ω ω' hstart hstart' hone hone' hPprob hstop n
    (T.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hT)
    ⟨1, fun z => by by_cases hz : z ∈ T <;> simp [hz]⟩
    (fun z hz => Set.indicator_of_notMem (fun ht => hz ht.2) _)
  have he' : (K (x, ω) T).toReal = (K (x, ω') T).toReal := by
    simpa [integral_indicator_const, hTa, measureReal_def] using he
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp he'

/-- The restricted supplied coupling laws agree on every literal history
cylinder, and hence on integrals of arbitrary measurable history tests. -/
theorem restricted_history_cylinders_and_integrals_assuming_stopped_law_eq {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R v : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (x : Vec d) (ω ω' : FieldPair d)
    [IsProbabilityMeasure (K (x, ω))] [IsProbabilityMeasure (K (x, ω'))]
    (hstart : ∀ᵐ z ∂K (x, ω), z.1 0 = x)
    (hstart' : ∀ᵐ z ∂K (x, ω'), z.1 0 = x)
    (hone : Renewal.OneIntervalKernelAt Δ δ R i P K (x, ω))
    (hone' : Renewal.OneIntervalKernelAt Δ δ R i P K (x, ω'))
    (hPprob : ∀ y : Vec d, IsProbabilityMeasure (P (y, ω)))
    (hstop : ∀ y : Vec d, y i ≤ v →
      (P (y, ω)).map (Diffusion.localityStoppedPath {z | z i < v + 3 * R}) =
        (P (y, ω')).map (Diffusion.localityStoppedPath {z | z i < v + 3 * R}))
    (n : ℕ) :
    (∀ S ∈ historyCylinders Δ n,
      (K (x, ω)).restrict (pastBelow Δ n i v) S =
        (K (x, ω')).restrict (pastBelow Δ n i v) S) ∧
    (∀ H : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ n] H →
      (∫ z, H z ∂(K (x, ω)).restrict (pastBelow Δ n i v)) =
        ∫ z, H z ∂(K (x, ω')).restrict (pastBelow Δ n i v)) := by
  have hc : ∀ S ∈ historyCylinders Δ n,
      (K (x, ω)).restrict (pastBelow Δ n i v) S =
        (K (x, ω')).restrict (pastBelow Δ n i v) S := by
    intro S hS
    have hs := measurableSet_historyCylinders Δ n hS
    have ha := (Probability.finiteHistorySigma_le Δ n) S hs
    rw [Measure.restrict_apply ha, Measure.restrict_apply ha]
    exact supported_finite_history_event_eq_assuming_stopped_law_eq Δ hΔ δ R v hR i
      P K x ω ω' hstart hstart' hone hone' hPprob hstop n S hs
  refine ⟨hc, ?_⟩
  intro H hH
  exact integral_eq_on_history_of_cylinders Δ n _ _ hc H hH

#print axioms restricted_history_cylinders_and_integrals_assuming_stopped_law_eq

#print axioms integral_supported_finite_history_eq_assuming_stopped_law_eq
#print axioms supported_finite_history_event_eq_assuming_stopped_law_eq

/-- Conditional assembly for the actual regular realizations and supplied law
family. The stopped-law producer remains an explicit hypothesis. -/
theorem exists_local_past_integral_version_assuming_stopped_law_eq {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K) :
    let R := l / lam
    let i := Renewal.forceCoord hd
    let Δ := Renewal.regenDelta lam
    ∀ (v : ℝ),
      (∀ (ω ω' : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
        (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
        (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω) hω lam h0.le h1)
        (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω') hω' lam h0.le h1),
        (∀ y : Vec d, P (y, ω) = r.pathLaw y) →
        (∀ y : Vec d, P (y, ω') = r'.pathLaw y) →
        (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
        ∀ y : Vec d, y i ≤ v →
          (P (y, ω)).map (Diffusion.localityStoppedPath {x | x i < v + 3 * R}) =
            (P (y, ω')).map (Diffusion.localityStoppedPath {x | x i < v + 3 * R})) →
      ∀ (m : ℕ) (H : CoupledSample d → ℝ),
        Measurable[finiteHistorySigma Δ m] H → BoundedRealTest H →
        (∀ z, (¬ ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → z.1 t i ≤ v) → H z = 0) →
        ∃ A : FieldPair d → ℝ,
          Measurable[localSigma {y : Vec d | y i ≤ v + 3 * R}] A ∧
          (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q.measure] A := by
  intro R i Δ v hstop m H hH hHb hHs
  apply exists_local_past_integral_version_of_gmp_scalar_comparison
    hd hΛ₀ Q lam l δ h0 h1 P K hK v ?_ m H hH hHb hHs
  intro ω ω' hω hω' r r' hassoc hassoc' hfields F hF _ hsegment hsupport y hy
  exact integral_pair_eq_of_locality_stopped_law_eq Δ R v (div_pos hl h0) i P y ω ω'
    (hstop ω ω' hω hω' r r' hassoc hassoc' hfields y hy) F hF hsegment hsupport

/-- A bounded local version of the actual first-slice past integral follows
from the same supplied-law stopped-map comparison at the endpoint cutoff.
The comparison remains an explicit, unproved hypothesis. -/
theorem exists_firstSlicePastIntegral_local_version_assuming_stopped_law_eq {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K) :
    let R := l / lam
    let i := Renewal.forceCoord hd
    let Δ := Renewal.regenDelta lam
    ∀ (y : Vec d),
    let v := y i - 7 * R;
      (∀ (ω ω' : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
        (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
        (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω) hω lam h0.le h1)
        (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω') hω' lam h0.le h1),
        (∀ x : Vec d, P (x, ω) = r.pathLaw x) →
        (∀ x : Vec d, P (x, ω') = r'.pathLaw x) →
        (∀ x : Vec d, x i ≤ v + 3 * R → ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) →
        ∀ x : Vec d, x i ≤ v →
          (P (x, ω)).map (Diffusion.localityStoppedPath {z | z i < v + 3 * R}) =
            (P (x, ω')).map (Diffusion.localityStoppedPath {z | z i < v + 3 * R})) →
      ∀ (m : ℕ) (H : CoupledSample d → ℝ),
        Measurable[finiteHistorySigma Δ m] H → BoundedRealTest H →
        ∃ A : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] A ∧
          BoundedRealTest A ∧
          (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q.measure] A := by
  intro R i Δ y v hstop m H hH hbH
  apply exists_firstSlicePastIntegral_local_version_of_gmp_scalar_comparison
    hd hΛ₀ Q lam l δ h0 h1 hl P K hK y ?_ m H hH hbH
  intro ω ω' hω hω' r r' hassoc hassoc' hfields F hF _ hsegment hsupport x hx
  exact integral_pair_eq_of_locality_stopped_law_eq Δ R v (div_pos hl h0) i P x ω ω'
    (hstop ω ω' hω hω' r r' hassoc hassoc' hfields x hx) F hF hsegment hsupport

/-- Conditional finite-history cylinder assembly for signed integrable tests. -/
theorem exists_countable_signed_local_versions_of_cylinders_assuming_stopped_law_eq {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K) :
    let R := l / lam
    let i := Renewal.forceCoord hd
    let Δ := Renewal.regenDelta lam
    (∀ (y : Vec d),
    let v := y i - 7 * R;
      (∀ (ω ω' : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
        (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
        (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω) hω lam h0.le h1)
        (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω') hω' lam h0.le h1),
        (∀ x : Vec d, P (x, ω) = r.pathLaw x) →
        (∀ x : Vec d, P (x, ω') = r'.pathLaw x) →
        (∀ x : Vec d, x i ≤ v + 3 * R → ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) →
        ∀ x : Vec d, x i ≤ v →
          (P (x, ω)).map (Diffusion.localityStoppedPath {z | z i < v + 3 * R}) =
            (P (x, ω')).map (Diffusion.localityStoppedPath {z | z i < v + 3 * R}))) →
    ∀ (m : ℕ → ℕ) (H : ℕ → CoupledSample d → ℝ),
      (∀ k, Measurable[finiteHistorySigma Δ (m k)] (H k)) →
      (∀ k, Integrable (fun q : FieldPair d × CoupledSample d => H k q.2)
        (annealedCoupledLaw Q.measure K)) →
      ∀ (ν : ℕ → Vec d × FieldPair d → Measure (CoupledSample d)),
      (∀ k, ∀ S ∈ historyCylinders Δ (m k),
        ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
          firstSlicePastMeasure Δ lam R i (m k) K p S = ν k p S) →
      ∃ A : ℕ → Vec d × FieldPair d → ℝ,
        (∀ k, Measurable (A k) ∧ Integrable (A k) ((volume : Measure (Vec d)).prod Q.measure)) ∧
        (∀ᵐ ω ∂Q.measure, ∀ k y, A k (y, ω) =
          firstSlicePastIntegral Δ lam R i (m k) K (H k) (y, ω)) ∧
        (∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure), ∀ k,
          A k p = ∫ z, H k z ∂ν k p) ∧
        ∀ᵐ y ∂(volume : Measure (Vec d)), ∀ k, ∃ a : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
          Integrable a Q.measure ∧ (fun ω => A k (y, ω)) =ᵐ[Q.measure] a := by
  intro R i Δ hstop m H hH hiH ν hcyl
  apply exists_countable_signed_local_versions_of_cylinders
    Q.measure K hK.1 Δ lam R (div_pos hl h0) i m H hH hiH ?_ ν hcyl
  intro k n y
  obtain ⟨a, ha, _, he⟩ :=
    exists_firstSlicePastIntegral_local_version_assuming_stopped_law_eq
      hd hΛ₀ Q lam l δ h0 h1 hl P K hK y (hstop y) (m k)
      (signedTestTruncation n (H k))
      (@measurable_signedTestTruncation (CoupledSample d) (finiteHistorySigma Δ (m k))
        n (H k) (hH k))
      (boundedRealTest_signedTestTruncation n (H k))
  exact ⟨a, ha, he⟩

/-- Local signed versions and all-endpoint cylinder comparisons on common events. -/
theorem exists_countable_signed_local_versions_with_endpoint_comparisons_assuming_stopped_law_eq {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K) :
    let R := l / lam
    let i := Renewal.forceCoord hd
    let Δ := Renewal.regenDelta lam
    (∀ (y : Vec d),
    let v := y i - 7 * R;
      (∀ (ω ω' : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
        (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
        (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω) hω lam h0.le h1)
        (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω') hω' lam h0.le h1),
        (∀ x : Vec d, P (x, ω) = r.pathLaw x) →
        (∀ x : Vec d, P (x, ω') = r'.pathLaw x) →
        (∀ x : Vec d, x i ≤ v + 3 * R → ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) →
        ∀ x : Vec d, x i ≤ v →
          (P (x, ω)).map (Diffusion.localityStoppedPath {z | z i < v + 3 * R}) =
            (P (x, ω')).map (Diffusion.localityStoppedPath {z | z i < v + 3 * R}))) →
    ∀ (m : ℕ → ℕ) (H : ℕ → CoupledSample d → ℝ),
      (∀ k, Measurable[finiteHistorySigma Δ (m k)] (H k)) →
      (∀ k, Integrable (fun q : FieldPair d × CoupledSample d => H k q.2)
        (annealedCoupledLaw Q.measure K)) →
      ∀ (ν : ℕ → Vec d × FieldPair d → Measure (CoupledSample d)),
      (∀ k, ∀ S ∈ historyCylinders Δ (m k),
        ∀ᵐ ω ∂Q.measure, ∀ y,
          firstSlicePastMeasure Δ lam R i (m k) K (y, ω) S = ν k (y, ω) S) →
      ∃ A : ℕ → Vec d × FieldPair d → ℝ,
        (∀ k, Measurable (A k) ∧ Integrable (A k) ((volume : Measure (Vec d)).prod Q.measure)) ∧
        (∀ᵐ ω ∂Q.measure, ∀ k y, A k (y, ω) =
          firstSlicePastIntegral Δ lam R i (m k) K (H k) (y, ω)) ∧
        (∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure), ∀ k,
          A k p = ∫ z, H k z ∂ν k p) ∧
        (∀ᵐ y ∂(volume : Measure (Vec d)), ∀ k, ∃ a : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] a ∧
          Integrable a Q.measure ∧ (fun ω => A k (y, ω)) =ᵐ[Q.measure] a) ∧
        (∀ᵐ ω ∂Q.measure, ∀ k y,
          Integrable (H k) (ν k (y, ω)) ∧
          (∀ n, firstSlicePastIntegral Δ lam R i (m k) K
            (signedTestTruncation n (H k)) (y, ω) =
              ∫ z, signedTestTruncation n (H k) z ∂ν k (y, ω)) ∧
          Filter.Tendsto (fun n => ∫ z, signedTestTruncation n (H k) z ∂ν k (y, ω))
            Filter.atTop (nhds (∫ z, H k z ∂ν k (y, ω)))) := by
  intro R i Δ hstop m H hH hiH ν hcyl
  have hcylProd : ∀ k, ∀ S ∈ historyCylinders Δ (m k),
      ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
        firstSlicePastMeasure Δ lam R i (m k) K p S = ν k p S := by
    intro k S hS
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (hcyl k S hS)] with p hp
    exact hp p.1
  obtain ⟨A, hA, he, hc, hlA⟩ :=
    exists_countable_signed_local_versions_of_cylinders_assuming_stopped_law_eq
      hd hΛ₀ Q lam l δ h0 h1 hl P K hK hstop m H hH hiH ν hcylProd
  exact ⟨A, hA, he, hc, hlA,
    ae_all_endpoints_comparison_truncations Q.measure K hK.1 Δ lam R i m H hH hiH ν hcyl⟩

#print axioms exists_countable_signed_local_versions_with_endpoint_comparisons_assuming_stopped_law_eq

/-- A common environment event and local kernels for all rational barriers and
finite histories, conditional on stopped-law equality for the supplied laws. -/
theorem exists_countable_endpoint_past_kernels_assuming_stopped_law_eq {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K) :
    let R := l / lam
    let i := Renewal.forceCoord hd
    let Δ := Renewal.regenDelta lam
    (∀ (q : ℚ) (ω ω' : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
        (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
        (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω) hω lam h0.le h1)
        (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          (zeroPotentialReducedPair ω') hω' lam h0.le h1),
        (∀ y : Vec d, P (y, ω) = r.pathLaw y) →
        (∀ y : Vec d, P (y, ω') = r'.pathLaw y) →
        (∀ y : Vec d, y i ≤ (q : ℝ) + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
        ∀ y : Vec d, y i ≤ (q : ℝ) →
          (P (y, ω)).map (Diffusion.localityStoppedPath {x | x i < (q : ℝ) + 3 * R}) =
            (P (y, ω')).map (Diffusion.localityStoppedPath {x | x i < (q : ℝ) + 3 * R})) →
    ∃ η : (m : ℕ) → (q : ℚ) → @ProbabilityTheory.Kernel (FieldPair d) (CoupledSample d)
        (localSigma {x : Vec d | x i ≤ (q : ℝ) + 3 * R}) inferInstance,
      (∀ m q, ProbabilityTheory.IsFiniteKernel (η m q)) ∧
      ∀ᵐ ω ∂Q.measure, ∀ (m : ℕ) (q : ℚ),
        η m q ω = Measure.map (Probability.stoppedHistorySample Δ m)
          ((K (0, ω)).restrict (pastBelow Δ m i (q : ℝ))) ∧
        ∀ (y : Vec d), y i - 7 * R ≤ (q : ℝ) →
          ∀ H : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ m] H →
          firstSlicePastIntegral Δ lam R i m K H (y, ω) =
            ∫ z, endpointPastTest Δ lam R i m H y z ∂η m q ω := by
  intro R i Δ hstop
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
  apply exists_countable_endpoint_past_kernels_of_integral_versions Q.measure Δ hΔ
    lam R h0 (div_pos hl h0) i K
    ((ae_origin_data_of_gmpCoupling hd hΛ₀ Q lam l δ h0.le h1 P K hK).mono
      fun _ hω => hω.1)
  intro m q H hH hHb hHs
  apply exists_local_past_integral_version_assuming_stopped_law_eq
    hd hΛ₀ Q lam l δ h0 h1 hl P K hK (q : ℝ) (hstop q) m H hH hHb
  intro z hz
  exact hHs z hz

/-- A shorter stopped history of a longer stopped history is the shorter
stopped history of the original sample. -/
theorem stoppedHistorySample_prefix {d : ℕ} (Δ : ℝ≥0) {m n : ℕ}
    (hmn : m ≤ n) (z : CoupledSample d) :
    Probability.stoppedHistorySample Δ m (Probability.stoppedHistorySample Δ n z) =
      Probability.stoppedHistorySample Δ m z := by
  have ht : (m : ℝ≥0) * Δ ≤ (n : ℝ≥0) * Δ :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmn) (zero_le : 0 ≤ Δ)
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    change z.1 (min (min t _) _) = z.1 (min t _)
    rw [min_eq_left ((min_le_right _ _).trans ht)]
  · funext k
    by_cases hk : k < m
    · have hkn : k < n := lt_of_lt_of_le hk hmn
      simp only [Probability.stoppedHistorySample, hk, hkn, ite_true]
    · simp only [Probability.stoppedHistorySample, hk, ite_false]

/-- On the common kernel representation event, shortening a restricted history
and increasing its barrier can only increase the resulting measure. The
longer-history cutoff remains in the mapped measure. -/
theorem ae_countable_past_kernel_prefix_domination {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (i : Fin d)
    (K : CoupledQuenchedLaws d) (R : ℝ)
    (η : (m : ℕ) → (q : ℚ) → @ProbabilityTheory.Kernel (FieldPair d)
      (CoupledSample d) (localSigma {x : Vec d | x i ≤ (q : ℝ) + 3 * R}) inferInstance)
    (hη : ∀ᵐ ω ∂Q, ∀ m q, η m q ω =
      Measure.map (Probability.stoppedHistorySample Δ m)
        ((K (0, ω)).restrict (pastBelow Δ m i (q : ℝ)))) :
    ∀ᵐ ω ∂Q, ∀ (m n : ℕ) (q r : ℚ), m ≤ n → q ≤ r →
      (η n q ω).map (Probability.stoppedHistorySample Δ m) ≤ η m r ω := by
  filter_upwards [hη] with ω hω
  intro m n q r hmn hqr
  rw [hω n q, hω m r]
  have hm : Measurable (Probability.stoppedHistorySample (d := d) Δ m) :=
    (Probability.measurable_stoppedHistorySample Δ m).mono
      (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hn : Measurable (Probability.stoppedHistorySample (d := d) Δ n) :=
    (Probability.measurable_stoppedHistorySample Δ n).mono
      (Probability.finiteHistorySigma_le Δ n) le_rfl
  rw [Measure.map_map hm hn]
  have hc : Probability.stoppedHistorySample (d := d) Δ m ∘ Probability.stoppedHistorySample Δ n =
      Probability.stoppedHistorySample Δ m := funext (stoppedHistorySample_prefix Δ hmn)
  rw [hc]
  apply Measure.map_mono _ hm
  apply Measure.restrict_mono_set
  intro z hz t ht
  exact (hz t (ht.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmn) (zero_le : 0 ≤ Δ)))).trans
    (Rat.cast_le.mpr hqr)

/-- Every bounded nonnegative shorter-history test inherits the simultaneous
prefix and barrier comparison, with integrability from the finite kernels. -/
theorem ae_countable_past_kernel_prefix_integral_le {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (i : Fin d)
    (K : CoupledQuenchedLaws d) (R : ℝ)
    (η : (m : ℕ) → (q : ℚ) → @ProbabilityTheory.Kernel (FieldPair d)
      (CoupledSample d) (localSigma {x : Vec d | x i ≤ (q : ℝ) + 3 * R}) inferInstance)
    (hfin : ∀ m q, ProbabilityTheory.IsFiniteKernel (η m q))
    (hη : ∀ᵐ ω ∂Q, ∀ m q, η m q ω =
      Measure.map (Probability.stoppedHistorySample Δ m)
        ((K (0, ω)).restrict (pastBelow Δ m i (q : ℝ)))) :
    ∀ᵐ ω ∂Q, ∀ (m n : ℕ) (q r : ℚ), m ≤ n → q ≤ r →
      ∀ H : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ m] H →
        BoundedRealTest H → (∀ z, 0 ≤ H z) →
        (∫ z, H z ∂η n q ω) ≤ ∫ z, H z ∂η m r ω := by
  filter_upwards [ae_countable_past_kernel_prefix_domination Q Δ i K R η hη] with ω hω
  intro m n q r hmn hqr H hH hb hnonneg
  let := hfin m r
  have hHm : Measurable H := hH.mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hstop : Measurable (Probability.stoppedHistorySample (d := d) Δ m) :=
    (Probability.measurable_stoppedHistorySample Δ m).mono
      (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hi : Integrable H (η m r ω) := integrable_of_bounded _ H hHm hb
  have hle := integral_mono_measure (hω m n q r hmn hqr)
    (Filter.Eventually.of_forall hnonneg) hi
  rw [integral_map hstop.aemeasurable hHm.aestronglyMeasurable] at hle
  simpa only [Probability.finiteHistory_test_stopped Δ m H hH] using hle

#print axioms ae_countable_past_kernel_prefix_integral_le
/-- The local kernel mass is exactly the original probability of the
longer-history cutoff, with no normalization. -/
theorem ae_countable_past_kernel_mass {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (i : Fin d)
    (K : CoupledQuenchedLaws d) (R : ℝ)
    (η : (m : ℕ) → (q : ℚ) → @ProbabilityTheory.Kernel (FieldPair d)
      (CoupledSample d) (localSigma {x : Vec d | x i ≤ (q : ℝ) + 3 * R}) inferInstance)
    (hη : ∀ᵐ ω ∂Q, ∀ m q, η m q ω =
      Measure.map (Probability.stoppedHistorySample Δ m)
        ((K (0, ω)).restrict (pastBelow Δ m i (q : ℝ)))) :
    ∀ᵐ ω ∂Q, ∀ m q, η m q ω Set.univ = K (0, ω) (pastBelow Δ m i (q : ℝ)) := by
  filter_upwards [hη] with ω hω
  intro m q
  rw [hω m q]
  have hm : Measurable (Probability.stoppedHistorySample (d := d) Δ m) :=
    (Probability.measurable_stoppedHistorySample Δ m).mono
      (Probability.finiteHistorySigma_le Δ m) le_rfl
  rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]

#print axioms ae_countable_past_kernel_mass
/-- The comparison applies to the literal endpoint past test. The right-hand
side is the original endpoint factor on the same common environment event. -/
theorem ae_countable_endpoint_past_kernel_prefix_integral_le {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d)
    (K : CoupledQuenchedLaws d)
    (η : (m : ℕ) → (q : ℚ) → @ProbabilityTheory.Kernel (FieldPair d)
      (CoupledSample d) (localSigma {x : Vec d | x i ≤ (q : ℝ) + 3 * R}) inferInstance)
    (hfin : ∀ m q, ProbabilityTheory.IsFiniteKernel (η m q))
    (hη : ∀ᵐ ω ∂Q, ∀ m q, η m q ω =
      Measure.map (Probability.stoppedHistorySample Δ m)
        ((K (0, ω)).restrict (pastBelow Δ m i (q : ℝ)))) :
    ∀ᵐ ω ∂Q, ∀ (m n : ℕ) (q r : ℚ), m ≤ n → q ≤ r →
      ∀ (y : Vec d), y i - 7 * R ≤ (r : ℝ) →
      ∀ H : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ m] H →
        BoundedRealTest H → (∀ z, 0 ≤ H z) →
        (∫ z, endpointPastTest Δ lam R i m H y z ∂η n q ω) ≤
          firstSlicePastIntegral Δ lam R i m K H (y, ω) := by
  have he : ∀ᵐ ω ∂Q, ∀ (m : ℕ) (r : ℚ), ∀ (y : Vec d),
      y i - 7 * R ≤ (r : ℝ) → ∀ H : CoupledSample d → ℝ,
      Measurable[finiteHistorySigma Δ m] H →
      firstSlicePastIntegral Δ lam R i m K H (y, ω) =
        ∫ z, endpointPastTest Δ lam R i m H y z ∂η m r ω := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro r
    apply ae_all_endpoint_past_integral_eq_of_kernel_eq Q Δ hΔ lam R hlam hR m i
      (r : ℝ) K _ (η m r)
    filter_upwards [hη] with ω hω
    exact hω m r
  filter_upwards [ae_countable_past_kernel_prefix_integral_le Q Δ i K R η hfin hη, he]
    with ω hc he
  intro m n q r hmn hqr y hy H hH hb hn
  rw [he m r y hy H hH]
  apply hc m n q r hmn hqr (endpointPastTest Δ lam R i m H y)
    (measurable_endpointPastTest Δ hΔ lam R hR i m H hH y)
    (bounded_endpointPastTest Δ lam R i m H hb y)
  intro z
  exact Set.indicator_nonneg (fun w _ => Set.indicator_nonneg (fun x _ => hn x) w) z

#print axioms ae_countable_endpoint_past_kernel_prefix_integral_le
#print axioms stoppedHistorySample_prefix
#print axioms ae_countable_past_kernel_prefix_domination

#print axioms exists_countable_endpoint_past_kernels_assuming_stopped_law_eq

#print axioms exists_countable_signed_local_versions_of_cylinders_assuming_stopped_law_eq

#print axioms exists_firstSlicePastIntegral_local_version_assuming_stopped_law_eq
#print axioms exists_local_past_integral_version_assuming_stopped_law_eq
#print axioms integral_pair_eq_of_locality_stopped_law_eq

#print axioms exists_countable_signed_local_versions_of_cylinders
#print axioms ae_endpoint_integrable_local_version_of_truncations_and_cylinders
#print axioms exists_measurable_firstSlicePastIntegral_version
#print axioms ae_integrable_origin_of_annealed_integrable
#print axioms abs_firstSlicePastIntegral_le_of_integrable_dominator
#print axioms ae_all_endpoints_tendsto_firstSlicePastIntegral_truncation
#print axioms exists_joint_integrable_local_firstSlicePastIntegral_version_of_truncations
#print axioms tendsto_integral_abs_sub_firstSlicePastIntegral_truncation
#print axioms normalized_integral_endpointPastTest_mul
#print axioms hasSum_integrable_meshBranchPastIntegral_endpoint_averages

#print axioms integral_endpointBall_indicator_of_integrable
#print axioms integrable_firstSlicePastIntegral_of_integrable
#print axioms normalized_integral_abs_firstSlicePastIntegral_le
#print axioms signedTestTruncation
#print axioms measurable_signedTestTruncation
#print axioms abs_signedTestTruncation_le
#print axioms boundedRealTest_signedTestTruncation
#print axioms tendsto_signedTestTruncation
#print axioms tendsto_integral_abs_sub_signedTestTruncation
#print axioms hasSum_integral_meshBranchTest_of_integrable
#print axioms integrable_meshBranchTest_of_integrable_stopped
#print axioms hasSum_integrable_meshBranchPastIntegral_endpoint_pairings

#print axioms integral_annealedCoupledLaw_of_integrable
#print axioms integrable_endpointBall_indicator_of_integrable
#print axioms ae_eq_condExp_firstSlicePastMeasure_of_cylinders
#print axioms ae_countable_firstSlicePastIntegral_eq_of_cylinders
#print axioms ae_countable_all_endpoints_firstSlicePastIntegral_eq_of_cylinders
#print axioms normalized_joint_firstSlicePastIntegral_le_of_dominated_cylinders
#print axioms ae_all_endpoints_integrable_finite_sums_of_cylinders
#print axioms ae_all_endpoints_comparison_truncations
#print axioms ae_all_endpoints_integrable_comparisons_of_cylinders
#print axioms exists_countable_weighted_local_versions_of_cylinders
#print axioms exists_countable_local_versions_with_cylinder_integrals
#print axioms joint_firstSlicePastIntegral_eq_of_cylinders
#print axioms integrable_origin_endpoint_integral

#print axioms integral_firstSlicePastIntegral_mul_eq_of_cylinders
#print axioms measure_eq_on_history_of_cylinders
#print axioms integral_eq_on_history_of_cylinders
#print axioms ae_all_endpoints_firstSlicePastIntegral_eq_of_cylinders
#print axioms integral_mul_firstSlicePastIntegral_eq_of_cylinders
#print axioms ae_measure_eq_on_history_of_cylinders
#print axioms ae_integral_eq_on_history_of_cylinders
#print axioms firstSlicePastMeasure
#print axioms firstSlicePastMeasure_le
#print axioms isFiniteMeasure_firstSlicePastMeasure
#print axioms integral_firstSlicePastMeasure
#print axioms firstSlicePastMeasure_mass
#print axioms ae_firstSlicePastIntegral_eq_of_cylinders

#print axioms rationalPathObservations
#print axioms measurableEmbedding_rationalPathObservations
#print axioms historyCylinderBase
#print axioms historyCylinders
#print axioms measurableSet_historyCylinderBase
#print axioms countable_historyCylinders
#print axioms univ_mem_historyCylinders
#print axioms isPiSystem_historyCylinders
#print axioms finiteHistorySigma_eq_generateFrom_historyCylinderBase
#print axioms finiteHistorySigma_eq_generateFrom_historyCylinders
#print axioms measurableSet_historyCylinders

#print axioms meshBranchTest
#print axioms stoppedMeshTest
#print axioms stoppedMeshPartialTest
#print axioms measurable_meshBranchTest_history
#print axioms meshBranchTest_stoppedHistory
#print axioms measurable_stoppedMeshPartialTest_history
#print axioms stoppedMeshPartialTest_eq
#print axioms abs_stoppedMeshPartialTest_le
#print axioms tendsto_stoppedMeshPartialTest
#print axioms tendsto_integral_mul_stoppedMeshPartialTest
#print axioms abs_meshBranchTest_le
#print axioms measurable_stoppedMeshTest
#print axioms hasSum_integral_mul_meshBranchTest
#print axioms meshBranch_endpointPastTest_supported
#print axioms finite_meshBranchPastIntegral_weighted_fubini
#print axioms exists_countable_joint_integrable_meshBranchPastIntegral_versions
#print axioms hasSum_meshBranchPastIntegral_endpoint_pairings

#print axioms exists_countable_joint_integrable_local_firstSlicePastIntegral_versions_of_limits
#print axioms tendsto_integral_mul_firstSlicePastIntegral
#print axioms exists_joint_integrable_local_firstSlicePastIntegral_version_of_limit

#print axioms nonneg_firstSlicePastIntegral_one
#print axioms abs_firstSlicePastIntegral_le_density
#print axioms isFiniteMeasure_firstSlicePastIntegral_density
#print axioms integral_abs_firstSlicePastIntegral_restrict_le_density
#print axioms tendsto_firstSlicePastIntegral_of_bounded_pointwise_limit
#print axioms tendsto_integral_abs_sub_firstSlicePastIntegral

#print axioms integrable_firstSlicePastIntegral
#print axioms integrable_firstSlicePastIntegral_mul
#print axioms firstSlicePastIntegral_mul_fubini
#print axioms weighted_firstSlicePastIntegral_fubini
#print axioms exists_joint_integrable_firstSlicePastIntegral_version_with_local_sections
#print axioms exists_countable_joint_integrable_firstSlicePastIntegral_versions
#print axioms ae_local_sections_of_supported_endpoint_kernels

#print axioms boundedRealVersion
#print axioms measurable_boundedRealVersion
#print axioms abs_boundedRealVersion_le
#print axioms boundedRealVersion_eq
#print axioms abs_integral_le_test_bound
#print axioms exists_bounded_origin_and_joint_integral_version
#print axioms exists_nonnegative_origin_and_joint_integral_version
#print axioms exists_bounded_past_halfSpace_version
#print axioms exists_countable_bounded_origin_and_joint_integral_versions
#print axioms origin_and_joint_integral_version_add
#print axioms origin_and_joint_integral_version_const_mul
#print axioms ae_integral_eq_limsup_of_bounded_versions
#print axioms exists_origin_and_joint_integral_version_of_bounded_pointwise_limit
#print axioms measurable_supported_bounded_pointwise_limit
#print axioms nonneg_endpointPastTest
#print axioms exists_nonnegative_firstSlicePastIntegral_local_version
#print axioms exists_integrable_weighted_firstSlicePastIntegral_local_version

#print axioms integral_supported_bridge_eq_of_low_killed_stopped_law_eq
#print axioms exists_measurable_bounded_firstSlicePastIntegral_version
#print axioms measurable_endpointPastTest_joint
#print axioms exists_firstSlicePastIntegral_local_version_of_gmp_scalar_comparison
#print axioms exists_countable_endpoint_past_kernels_of_integral_versions
#print axioms exists_bounded_firstSlicePastIntegral_local_version
#print axioms endpointPastTest
#print axioms measurable_endpointPastTest
#print axioms abs_endpointPastTest_le
#print axioms bounded_endpointPastTest
#print axioms endpointPastTest_eq_zero_of_not_pastBelow
#print axioms integral_endpointPastTest
#print axioms abs_firstSlicePastIntegral_le
#print axioms exists_firstSlicePastIntegral_local_version_of_origin_versions
#print axioms ae_all_endpoint_past_integral_eq_of_kernel_eq

#print axioms hasPastHalfSpaceVersions_of_gmp_scalar_comparison
#print axioms exists_joint_start_version_of_fields_eq_on
#print axioms exists_origin_and_joint_start_version_of_fields_eq_on
#print axioms hasPastHalfSpaceVersions_of_supported_scalar_comparison
#print axioms exists_local_supported_history_kernel_of_gmp_scalar_comparison
#print axioms ae_all_supported_history_integral_eq_of_kernel_eq
#print axioms exists_local_joint_past_integral_version_of_integral_versions
#print axioms exists_local_kernel_of_integral_versions
#print axioms supportedHistoryKernel
#print axioms supportedHistoryKernel_isFiniteKernel
#print axioms exists_local_supported_history_kernel_of_integral_versions
#print axioms fieldPair_standardBorel
#print axioms ae_condExpKernel_observation_eq
#print axioms ae_condExpKernel_of_ae
#print axioms ae_condExpKernel_fields_eq_on
#print axioms exists_local_version_of_fields_eq_on
#print axioms exists_local_supported_history_integral_version_of_scalar_comparison
#print axioms exists_local_past_integral_version_of_gmp_scalar_comparison
#print axioms exists_local_zero_history_integral_version_of_gmpCoupling
#print axioms integral_eq_zero_of_negative_past_cutoff
#print axioms exists_local_past_integral_version_of_negative_barrier
#print axioms pastBelow
#print axioms measurableSet_pastBelow
#print axioms measurableSet_pastBelow_history
#print axioms bounded_mul
#print axioms bounded_sub
#print axioms killedBridgeMixture_mass_le_one
#print axioms bounded_killedBridgeMixture_integral
#print axioms bounded_integral_probability_family
#print axioms measurable_killedBridgeMixture_integral
#print axioms integral_zero_history_eq_of_starts
#print axioms integral_next_bit_eq_of_supported_scalar_comparison
#print axioms pastBelow_succ_iff
#print axioms integral_supported_history_succ_eq_of_rectangles
#print axioms integrable_of_bounded
#print axioms integral_weighted_history_eq_of_bit_tests
#print axioms integral_supported_finite_history_eq_of_bit_steps
#print axioms integral_supported_finite_history_eq_of_scalar_comparison
#print axioms ae_origin_data_of_gmpCoupling

#print axioms exists_firstSlicePastIntegral_local_version_of_gmp_stopped_comparisons
#print axioms hasSum_integrable_comparison_meshBranch_endpoint_pairings
#print axioms hasSum_integrable_comparison_meshBranch_endpoint_averages

#lint

end EinsteinFull.Blueprint.PastFiniteHistory

