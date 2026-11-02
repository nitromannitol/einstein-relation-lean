import EinsteinRelation.Regeneration.OneIntervalBridgeSupport
import EinsteinRelation.Regeneration.KilledSegmentMeasurability
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Independence.Integration
import EinsteinRelation.Probability.FiniteHistoryStopping
import EinsteinRelation.Probability.PathMaps
import EinsteinRelation.Diffusion.StoppedPathLocality
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.Linter.Lint

/-!
Single-fibre splitting of the actual killed bridge mixture (`paper/main.tex:1499`).
Endpoint minorization
is an explicit analytic input to this construction, not an assertion of its
existence. Supplied measurable split kernels yield exact deterministic-grid
finite-prefix laws. No process realization or full regeneration coupling is
assumed or produced here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration

/-- Reweighting by the endpoint RN derivative recovers an absolutely continuous
endpoint law, including its null sets. -/
theorem sbxS4_map_endpoint_reweight {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : α → β) (he : Measurable e)
    (hac : ν ≪ μ.map e) :
    (μ.withDensity ((ν.rnDeriv (μ.map e)) ∘ e)).map e = ν := by
  calc
    (μ.withDensity ((ν.rnDeriv (μ.map e)) ∘ e)).map e =
        (μ.map e).withDensity (ν.rnDeriv (μ.map e)) := by
      apply Measure.ext
      intro s hs
      rw [Measure.map_apply he hs, withDensity_apply _ (he hs), withDensity_apply _ hs,
        setLIntegral_map hs (Measure.measurable_rnDeriv _ _) he]
      rfl
    _ = ν := Measure.withDensity_rnDeriv_eq _ _ hac

/-- An endpoint minorization bounds the pulled-back density on paths. No
strictly positive density or pointwise choice of bridges is required. -/
theorem sbxS4_endpoint_reweight_le_of_minorization {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : α → β) (he : Measurable e)
    (a : ℝ≥0∞) (ha : a ≠ ∞) (hminor : a • ν ≤ μ.map e) :
    a • μ.withDensity ((ν.rnDeriv (μ.map e)) ∘ e) ≤ μ := by
  have hrn := Measure.rnDeriv_smul_left_of_ne_top ν (μ.map e) ha
  have hbound := Measure.rnDeriv_le_one_of_le hminor
  have hend : ∀ᵐ y ∂μ.map e, a * ν.rnDeriv (μ.map e) y ≤ 1 := by
    filter_upwards [hrn, hbound] with y hy hb
    simpa only [hy, Pi.smul_apply, smul_eq_mul, Pi.one_apply] using hb
  have hpath : ∀ᵐ x ∂μ, a * ν.rnDeriv (μ.map e) (e x) ≤ 1 :=
    ae_of_ae_map he.aemeasurable hend
  rw [← withDensity_smul a ((Measure.measurable_rnDeriv _ _).comp he)]
  calc
    μ.withDensity (a • ((ν.rnDeriv (μ.map e)) ∘ e)) ≤ μ.withDensity 1 :=
      withDensity_mono hpath
    _ = μ := withDensity_one

/-- Positive endpoint minorization eliminates the singular endpoint part. -/
theorem sbxS4_endpoint_ac_of_minorization {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (ν : Measure β) (e : α → β)
    (a : ℝ≥0∞) (ha : a ≠ 0) (hminor : a • ν ≤ μ.map e) :
    ν ≪ μ.map e :=
  (Measure.absolutelyContinuous_smul ha).trans (Measure.absolutelyContinuous_of_le hminor)

/-- Under the actual endpoint minorization the killed bridge has precisely the
conditional uniform endpoint law, rather than only a dominated endpoint law. -/
theorem sbxS4_map_killedBridgeMixture_endpoint {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ : 0 < δ)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ)) :
    (Renewal.killedBridgeMixture Δ R i P z ω).map (fun γ : Path d => γ Δ) =
      cond (volume : Measure (Vec d)) (endpointBall i R z) := by
  let : IsProbabilityMeasure (cond (volume : Measure (Vec d)) (endpointBall i R z)) :=
    cond_isProbabilityMeasure_of_finite (endpointBall_volume_pos i R hR z).ne'
      (endpointBall_volume_ne_top i R hR z)
  let : IsFiniteMeasure (Renewal.killedSegmentLaw Δ R i P z ω) := by
    unfold Renewal.killedSegmentLaw
    infer_instance
  exact sbxS4_map_endpoint_reweight _ _ _ (continuous_eval_const Δ).measurable
    (sbxS4_endpoint_ac_of_minorization _ _ _ _ (ENNReal.ofReal_pos.mpr hδ).ne' hminor)

/-- Integrable signed endpoint tests transport through the actual successful
bridge endpoint law. -/
theorem sbxS4_killedBridgeMixture_integrable_endpoint {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ : 0 < δ)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ))
    (φ : Vec d → ℝ) (hφ : Measurable φ)
    (hφint : Integrable φ (cond (volume : Measure (Vec d)) (endpointBall i R z))) :
    Integrable (fun γ => φ (γ Δ)) (Renewal.killedBridgeMixture Δ R i P z ω) ∧
      (∫ γ, φ (γ Δ) ∂Renewal.killedBridgeMixture Δ R i P z ω) =
        ∫ y, φ y ∂cond (volume : Measure (Vec d)) (endpointBall i R z) := by
  have hmap := sbxS4_map_killedBridgeMixture_endpoint Δ R δ i P z ω hR hδ hminor
  have hint : Integrable φ ((Renewal.killedBridgeMixture Δ R i P z ω).map
      (fun γ : Path d => γ Δ)) := by rw [hmap]; exact hφint
  refine ⟨hint.comp_measurable (continuous_eval_const Δ).measurable, ?_⟩
  rw [← integral_map (continuous_eval_const Δ).measurable.aemeasurable
    hφ.aestronglyMeasurable, hmap]

/-- The successful single-fibre bridge is a probability law under endpoint
minorization; no mass is lost on singular or null endpoint sets. -/
theorem sbxS4_killedBridgeMixture_isProbabilityMeasure {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ : 0 < δ)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ)) :
    IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P z ω) := by
  let : IsProbabilityMeasure (cond (volume : Measure (Vec d)) (endpointBall i R z)) :=
    cond_isProbabilityMeasure_of_finite (endpointBall_volume_pos i R hR z).ne'
      (endpointBall_volume_ne_top i R hR z)
  have hm := sbxS4_map_killedBridgeMixture_endpoint Δ R δ i P z ω hR hδ hminor
  let : IsProbabilityMeasure
      ((Renewal.killedBridgeMixture Δ R i P z ω).map (fun γ : Path d => γ Δ)) :=
    hm.symm ▸ inferInstance
  exact Measure.isProbabilityMeasure_of_map (continuous_eval_const Δ).measurable.aemeasurable

/-- Endpoint minorization gives the domination needed for genuine measure
subtraction from the unrestricted path law. -/
theorem sbxS4_smul_killedBridgeMixture_le {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ)) :
    ENNReal.ofReal δ • Renewal.killedBridgeMixture Δ R i P z ω ≤ P (z, ω) := by
  let : IsProbabilityMeasure (cond (volume : Measure (Vec d)) (endpointBall i R z)) :=
    cond_isProbabilityMeasure_of_finite (endpointBall_volume_pos i R hR z).ne'
      (endpointBall_volume_ne_top i R hR z)
  let : IsFiniteMeasure (Renewal.killedSegmentLaw Δ R i P z ω) := by
    unfold Renewal.killedSegmentLaw
    infer_instance
  exact (sbxS4_endpoint_reweight_le_of_minorization _ _ _
    (continuous_eval_const Δ).measurable _ ENNReal.ofReal_ne_top hminor).trans
      Measure.restrict_le_self

/-- Normalized failed branch of a split probability law, defined by actual
measure subtraction. Its probability property requires the domination below. -/
def sbxS4SplitResidual {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) : Measure α :=
  (ENNReal.ofReal (1 - δ))⁻¹ • (P - ENNReal.ofReal δ • B)

/-- The failed branch has total mass one when the successful branch is
probability and its weighted measure is dominated by the original law. -/
theorem sbxS4_splitResidual_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure B]
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (hdom : ENNReal.ofReal δ • B ≤ P) :
    IsProbabilityMeasure (sbxS4SplitResidual δ P B) := by
  let : IsFiniteMeasure (ENNReal.ofReal δ • B) := B.smul_finite ENNReal.ofReal_ne_top
  have hmass : (P - ENNReal.ofReal δ • B) Set.univ = ENNReal.ofReal (1 - δ) := by
    rw [Measure.sub_apply MeasurableSet.univ hdom]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_sub 1 hδ₀, ENNReal.ofReal_one]
  constructor
  change (ENNReal.ofReal (1 - δ))⁻¹ * (P - ENNReal.ofReal δ • B) Set.univ = 1
  rw [hmass]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (sub_pos.mpr hδ₁)).ne'
    ENNReal.ofReal_ne_top

/-- Multiplying the normalized failed law by its selection probability gives
exactly the measure difference. -/
theorem sbxS4_smul_splitResidual {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) (hδ : δ < 1) :
    ENNReal.ofReal (1 - δ) • sbxS4SplitResidual δ P B = P - ENNReal.ofReal δ • B := by
  unfold sbxS4SplitResidual
  rw [smul_smul, ENNReal.mul_inv_cancel
    (ENNReal.ofReal_pos.mpr (sub_pos.mpr hδ)).ne' ENNReal.ofReal_ne_top, one_smul]

/-- Exact weighted-mixture recovery of the original probability measure. -/
theorem sbxS4_splitResidual_recovery {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) [IsFiniteMeasure B]
    (hδ : δ < 1) (hdom : ENNReal.ofReal δ • B ≤ P) :
    ENNReal.ofReal δ • B + ENNReal.ofReal (1 - δ) • sbxS4SplitResidual δ P B = P := by
  let : IsFiniteMeasure (ENNReal.ofReal δ • B) := B.smul_finite ENNReal.ofReal_ne_top
  rw [sbxS4_smul_splitResidual δ P B hδ, add_comm]
  exact Measure.sub_add_cancel_of_le hdom

/-- Recovery holds on every measurable path event (indeed every set). -/
theorem sbxS4_splitResidual_recovery_apply {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) [IsFiniteMeasure B]
    (hδ : δ < 1) (hdom : ENNReal.ofReal δ • B ≤ P) (s : Set α) :
    ENNReal.ofReal δ * B s + ENNReal.ofReal (1 - δ) * sbxS4SplitResidual δ P B s = P s := by
  have h := congrArg (fun μ : Measure α => μ s) (sbxS4_splitResidual_recovery δ P B hδ hdom)
  simpa only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] using h

/-- An integrable test for the original law remains integrable for the
normalized residual; the difference is bounded by the original measure. -/
theorem sbxS4_integrable_splitResidual {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] (δ : ℝ) (P B : Measure α) (hδ : δ < 1)
    (F : α → E) (hF : Integrable F P) :
    Integrable F (sbxS4SplitResidual δ P B) := by
  exact (hF.mono_measure Measure.sub_le).smul_measure
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (sub_pos.mpr hδ)).ne')

/-- Exact recovery for Bochner tests integrable under the original law. The
weighted branches are integrable, so no default-zero integral is used. -/
theorem sbxS4_splitResidual_integral_recovery {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (δ : ℝ) (P B : Measure α)
    [IsFiniteMeasure B] (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (hdom : ENNReal.ofReal δ • B ≤ P) (F : α → E) (hF : Integrable F P) :
    (∫ x, F x ∂P) = δ • (∫ x, F x ∂B) +
      (1 - δ) • (∫ x, F x ∂sbxS4SplitResidual δ P B) := by
  have hsuccess : Integrable F (ENNReal.ofReal δ • B) := hF.mono_measure hdom
  have hfailed : Integrable F (ENNReal.ofReal (1 - δ) • sbxS4SplitResidual δ P B) := by
    rw [sbxS4_smul_splitResidual δ P B hδ₁]
    exact hF.mono_measure Measure.sub_le
  have h := integral_add_measure hsuccess hfailed
  rw [sbxS4_splitResidual_recovery δ P B hδ₁ hdom] at h
  rw [integral_eq F hF] at h ⊢
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal hδ₀,
    ENNReal.toReal_ofReal (sub_pos.mpr hδ₁).le] using h

/-- The literal failed path law for the killed-bridge split at one fibre. -/
def sbxS4FailedSegmentLaw {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (z : Vec d) (ω : FieldPair d) : Measure (Path d) :=
  sbxS4SplitResidual δ (P (z, ω)) (Renewal.killedBridgeMixture Δ R i P z ω)

/-- Actual failed-segment normalization from the endpoint minorization. -/
theorem sbxS4_failedSegmentLaw_isProbabilityMeasure {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ)) :
    IsProbabilityMeasure (sbxS4FailedSegmentLaw Δ R δ i P z ω) := by
  let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P z ω) :=
    sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P z ω hR hδ₀ hminor
  exact sbxS4_splitResidual_isProbabilityMeasure δ _ _ hδ₀.le hδ₁
    (sbxS4_smul_killedBridgeMixture_le Δ R δ i P z ω hR hminor)

/-- The two actual single-fibre laws recover the unrestricted path law. -/
theorem sbxS4_failedSegmentLaw_recovery {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ)) :
    ENNReal.ofReal δ • Renewal.killedBridgeMixture Δ R i P z ω +
      ENNReal.ofReal (1 - δ) • sbxS4FailedSegmentLaw Δ R δ i P z ω = P (z, ω) := by
  let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P z ω) :=
    sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P z ω hR hδ₀ hminor
  exact sbxS4_splitResidual_recovery δ _ _ hδ₁
    (sbxS4_smul_killedBridgeMixture_le Δ R δ i P z ω hR hminor)

/-- Actual mixture recovery for bounded strongly measurable Bochner tests. -/
theorem sbxS4_failedSegmentLaw_integral_recovery {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ))
    (F : Path d → E) (hF : StronglyMeasurable F)
    (hbounded : ∃ C : ℝ, ∀ γ, ‖F γ‖ ≤ C) :
    (∫ γ, F γ ∂P (z, ω)) = δ • (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω) +
      (1 - δ) • (∫ γ, F γ ∂sbxS4FailedSegmentLaw Δ R δ i P z ω) := by
  let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P z ω) :=
    sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P z ω hR hδ₀ hminor
  obtain ⟨C, hC⟩ := hbounded
  have hi : Integrable F (P (z, ω)) :=
    (integrable_const C).mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  exact sbxS4_splitResidual_integral_recovery δ _ _ hδ₀.le hδ₁
    (sbxS4_smul_killedBridgeMixture_le Δ R δ i P z ω hR hminor) F hi

/-- The residual evaluates to the normalized difference on measurable events.
The domination hypothesis is essential for evaluating measure subtraction. -/
theorem sbxS4_splitResidual_apply {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) [IsFiniteMeasure B]
    (hdom : ENNReal.ofReal δ • B ≤ P) (s : Set α) (hs : MeasurableSet s) :
    sbxS4SplitResidual δ P B s =
      (ENNReal.ofReal (1 - δ))⁻¹ * (P s - ENNReal.ofReal δ * B s) := by
  let : IsFiniteMeasure (ENNReal.ofReal δ • B) := B.smul_finite ENNReal.ofReal_ne_top
  unfold sbxS4SplitResidual
  rw [Measure.smul_apply, Measure.sub_apply hs hdom, Measure.smul_apply]
  rfl

/-- The normalized failed branch has exactly the subtraction formula on actual
measurable path events. -/
theorem sbxS4_failedSegmentLaw_apply {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ))
    (s : Set (Path d)) (hs : MeasurableSet s) :
    sbxS4FailedSegmentLaw Δ R δ i P z ω s =
      (ENNReal.ofReal (1 - δ))⁻¹ *
        (P (z, ω) s - ENNReal.ofReal δ * Renewal.killedBridgeMixture Δ R i P z ω s) := by
  let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P z ω) :=
    sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P z ω hR hδ₀ hminor
  exact sbxS4_splitResidual_apply δ _ _
    (sbxS4_smul_killedBridgeMixture_le Δ R δ i P z ω hR hminor) s hs

/-- The failed-branch test identity in the real-valued form used in
`Renewal.OneIntervalKernelAt`. All three integrals have integrable tests. -/
theorem sbxS4_failedSegmentLaw_integral_difference {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ))
    (F : Path d → ℝ) (hF : Measurable F) (hbounded : BoundedRealTest F) :
    (1 - δ) * (∫ γ, F γ ∂sbxS4FailedSegmentLaw Δ R δ i P z ω) =
      (∫ γ, F γ ∂P (z, ω)) - δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω) := by
  have hb : ∃ C : ℝ, ∀ γ, ‖F γ‖ ≤ C := by
    simpa only [BoundedRealTest, Real.norm_eq_abs] using hbounded
  have h := sbxS4_failedSegmentLaw_integral_recovery Δ R δ i P z ω
    hR hδ₀ hδ₁ hminor F hF.stronglyMeasurable hb
  apply eq_sub_iff_add_eq.mpr
  simpa only [smul_eq_mul, add_comm] using h.symm

/-- The actual first split coin, retaining the original path coordinate.
The unsuccessful branch is the normalized measure difference, not an
independently postulated path law. -/
def sbxS4FirstCoinLaw {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) : Measure (α × Bool) :=
  ENNReal.ofReal δ • B.map (fun x => (x, true)) +
    ENNReal.ofReal (1 - δ) • (sbxS4SplitResidual δ P B).map (fun x => (x, false))

/-- Exact joint event masses on each branch of the first coin. -/
theorem sbxS4_firstCoinLaw_apply {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) (s : Set α) (hs : MeasurableSet s) (b : Bool) :
    sbxS4FirstCoinLaw δ P B {q | q.1 ∈ s ∧ q.2 = b} =
      if b then ENNReal.ofReal δ * B s
      else ENNReal.ofReal (1 - δ) * sbxS4SplitResidual δ P B s := by
  have hm : MeasurableSet {q : α × Bool | q.1 ∈ s ∧ q.2 = b} :=
    (hs.preimage measurable_fst).inter (measurable_snd (measurableSet_singleton b))
  have ht : Measurable (fun x : α => (x, true)) := measurable_id.prodMk measurable_const
  have hf : Measurable (fun x : α => (x, false)) := measurable_id.prodMk measurable_const
  simp only [sbxS4FirstCoinLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply ht hm, Measure.map_apply hf hm]
  cases b <;> simp

/-- Forgetting the first coin recovers the original path law exactly. -/
theorem sbxS4_firstCoinLaw_map_fst {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) [IsFiniteMeasure B]
    (hδ : δ < 1) (hdom : ENNReal.ofReal δ • B ≤ P) :
    (sbxS4FirstCoinLaw δ P B).map Prod.fst = P := by
  unfold sbxS4FirstCoinLaw
  rw [Measure.map_add _ _ measurable_fst,
    Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_map measurable_fst
      (show Measurable (fun x : α => (x, true)) from measurable_id.prodMk measurable_const),
    Measure.map_map measurable_fst
      (show Measurable (fun x : α => (x, false)) from measurable_id.prodMk measurable_const)]
  simpa only [Function.comp_def, Measure.map_id'] using
    sbxS4_splitResidual_recovery δ P B hδ hdom

/-- The constructed joint law is a probability measure. -/
theorem sbxS4_firstCoinLaw_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) [IsProbabilityMeasure P] [IsFiniteMeasure B]
    (hδ : δ < 1) (hdom : ENNReal.ofReal δ • B ≤ P) :
    IsProbabilityMeasure (sbxS4FirstCoinLaw δ P B) := by
  have hm := sbxS4_firstCoinLaw_map_fst δ P B hδ hdom
  let : IsProbabilityMeasure ((sbxS4FirstCoinLaw δ P B).map Prod.fst) :=
    hm.symm ▸ inferInstance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

/-- The first-coin marginal is Bernoulli with success probability `δ`. -/
theorem sbxS4_firstCoinLaw_map_snd {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure B]
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (hdom : ENNReal.ofReal δ • B ≤ P) :
    (sbxS4FirstCoinLaw δ P B).map Prod.snd =
      ENNReal.ofReal δ • Measure.dirac true +
        ENNReal.ofReal (1 - δ) • Measure.dirac false := by
  let : IsProbabilityMeasure (sbxS4SplitResidual δ P B) :=
    sbxS4_splitResidual_isProbabilityMeasure δ P B hδ₀ hδ₁ hdom
  unfold sbxS4FirstCoinLaw
  rw [Measure.map_add _ _ measurable_snd,
    Measure.map_smul _ measurable_snd.aemeasurable,
    Measure.map_smul _ measurable_snd.aemeasurable,
    Measure.map_map measurable_snd
      (show Measurable (fun x : α => (x, true)) from measurable_id.prodMk measurable_const),
    Measure.map_map measurable_snd
      (show Measurable (fun x : α => (x, false)) from measurable_id.prodMk measurable_const)]
  simp only [Function.comp_def, Measure.map_const, measure_univ, one_smul]

/-- Restricting to either first-coin outcome and forgetting the coin gives
its weighted path law on every measurable event. -/
theorem sbxS4_firstCoinLaw_restrict_map_fst {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) (b : Bool) :
    ((sbxS4FirstCoinLaw δ P B).restrict {q | q.2 = b}).map Prod.fst =
      if b then ENNReal.ofReal δ • B
      else ENNReal.ofReal (1 - δ) • sbxS4SplitResidual δ P B := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_fst hs,
    Measure.restrict_apply (hs.preimage measurable_fst)]
  have he : Prod.fst ⁻¹' s ∩ {q : α × Bool | q.2 = b} =
      {q | q.1 ∈ s ∧ q.2 = b} := rfl
  rw [he, sbxS4_firstCoinLaw_apply δ P B s hs b]
  cases b <;> rfl

/-- Conditioning on the actual first coin yields precisely the successful
bridge or the normalized failed law; both conditioning events have positive mass. -/
theorem sbxS4_firstCoinLaw_cond_map_fst {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure B]
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hdom : ENNReal.ofReal δ • B ≤ P) (b : Bool) :
    (cond (sbxS4FirstCoinLaw δ P B) {q | q.2 = b}).map Prod.fst =
      if b then B else sbxS4SplitResidual δ P B := by
  let : IsProbabilityMeasure (sbxS4SplitResidual δ P B) :=
    sbxS4_splitResidual_isProbabilityMeasure δ P B hδ₀.le hδ₁ hdom
  have hmass : sbxS4FirstCoinLaw δ P B {q | q.2 = b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ) := by
    simpa only [Set.mem_univ, true_and, measure_univ, mul_one] using
      sbxS4_firstCoinLaw_apply δ P B Set.univ MeasurableSet.univ b
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul _ measurable_fst.aemeasurable,
    sbxS4_firstCoinLaw_restrict_map_fst, hmass]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, smul_smul]
  · rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (sub_pos.mpr hδ₁)).ne'
      ENNReal.ofReal_ne_top, one_smul]
  · rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hδ₀).ne'
      ENNReal.ofReal_ne_top, one_smul]

/-- Bounded strongly measurable Bochner tests have integrable coin-selected
observables and the exact weighted branch expectations. This applies in
particular to tests depending only on the genuine interval `[0, Δ]`. -/
theorem sbxS4_firstCoinLaw_integral_branch {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (δ : ℝ) (P B : Measure α) [IsProbabilityMeasure P] [IsFiniteMeasure B]
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (hdom : ENNReal.ofReal δ • B ≤ P)
    (F : α → E) (hF : StronglyMeasurable F) (hbounded : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (b : Bool) :
    Integrable ({q : α × Bool | q.2 = b}.indicator (fun q => F q.1))
      (sbxS4FirstCoinLaw δ P B) ∧
    (∫ q, {q : α × Bool | q.2 = b}.indicator (fun q => F q.1) q
      ∂sbxS4FirstCoinLaw δ P B) =
      if b then δ • (∫ x, F x ∂B)
      else (1 - δ) • (∫ x, F x ∂sbxS4SplitResidual δ P B) := by
  let : IsProbabilityMeasure (sbxS4FirstCoinLaw δ P B) :=
    sbxS4_firstCoinLaw_isProbabilityMeasure δ P B hδ₁ hdom
  have hs : MeasurableSet {q : α × Bool | q.2 = b} :=
    measurable_snd (measurableSet_singleton b)
  obtain ⟨C, hC⟩ := hbounded
  have hi : Integrable (fun q : α × Bool => F q.1) (sbxS4FirstCoinLaw δ P B) :=
    (integrable_const C).mono' (hF.comp_measurable measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => hC q.1)
  refine ⟨hi.indicator hs, ?_⟩
  rw [integral_indicator hs]
  have he := (integral_map_of_stronglyMeasurable
    (μ := (sbxS4FirstCoinLaw δ P B).restrict {q | q.2 = b}) measurable_fst hF).symm
  rw [integral_eq _ hi.restrict] at he ⊢
  rw [he, sbxS4_firstCoinLaw_restrict_map_fst δ P B b]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, integral_smul_measure,
    ENNReal.toReal_ofReal hδ₀, ENNReal.toReal_ofReal (sub_pos.mpr hδ₁).le]

/-- An integrable signed path test can be split on either coin branch. -/
theorem sbxS4_firstCoinLaw_integrable_branch {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) [IsFiniteMeasure B]
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (hdom : ENNReal.ofReal δ • B ≤ P)
    (F : α → ℝ) (hF : StronglyMeasurable F) (hfi : Integrable F P) (b : Bool) :
    Integrable ({q : α × Bool | q.2 = b}.indicator (fun q => F q.1))
      (sbxS4FirstCoinLaw δ P B) ∧
    (∫ q, {q : α × Bool | q.2 = b}.indicator (fun q => F q.1) q
      ∂sbxS4FirstCoinLaw δ P B) =
      if b then δ * (∫ x, F x ∂B)
      else (1 - δ) * (∫ x, F x ∂sbxS4SplitResidual δ P B) := by
  have hs : MeasurableSet {q : α × Bool | q.2 = b} :=
    measurable_snd (measurableSet_singleton b)
  have hi : Integrable (fun q : α × Bool => F q.1) (sbxS4FirstCoinLaw δ P B) := by
    apply Integrable.comp_measurable _ measurable_fst
    rw [sbxS4_firstCoinLaw_map_fst δ P B hδ₁ hdom]
    exact hfi
  refine ⟨hi.indicator hs, ?_⟩
  rw [integral_indicator hs]
  have he := (integral_map_of_stronglyMeasurable
    (μ := (sbxS4FirstCoinLaw δ P B).restrict {q | q.2 = b}) measurable_fst hF).symm
  rw [integral_eq _ hi.restrict] at he ⊢
  rw [he, sbxS4_firstCoinLaw_restrict_map_fst δ P B b]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, integral_smul_measure,
    ENNReal.toReal_ofReal hδ₀, ENNReal.toReal_ofReal (sub_pos.mpr hδ₁).le,
    smul_eq_mul]

/-- The literal first-interval joint law of a path and its split coin. -/
def sbxS4FirstSegmentLaw {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (z : Vec d) (ω : FieldPair d) : Measure (Path d × Bool) :=
  sbxS4FirstCoinLaw δ (P (z, ω)) (Renewal.killedBridgeMixture Δ R i P z ω)

/-- A single-fibre first-step construction from the precise endpoint
minorization. The conclusion supplies the probability law, both marginals and
both conditional path laws. It asserts no later-time restart or locality. -/
theorem sbxS4_firstSegmentLaw_spec {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ)) :
    IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) ∧
    (sbxS4FirstSegmentLaw Δ R δ i P z ω).map Prod.fst = P (z, ω) ∧
    (sbxS4FirstSegmentLaw Δ R δ i P z ω).map Prod.snd =
      ENNReal.ofReal δ • Measure.dirac true +
        ENNReal.ofReal (1 - δ) • Measure.dirac false ∧
    ∀ b : Bool,
      (cond (sbxS4FirstSegmentLaw Δ R δ i P z ω) {q | q.2 = b}).map Prod.fst =
        if b then Renewal.killedBridgeMixture Δ R i P z ω
        else sbxS4FailedSegmentLaw Δ R δ i P z ω := by
  let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P z ω) :=
    sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P z ω hR hδ₀ hminor
  have hdom := sbxS4_smul_killedBridgeMixture_le Δ R δ i P z ω hR hminor
  exact ⟨sbxS4_firstCoinLaw_isProbabilityMeasure δ _ _ hδ₁ hdom,
    sbxS4_firstCoinLaw_map_fst δ _ _ hδ₁ hdom,
    sbxS4_firstCoinLaw_map_snd δ _ _ hδ₀.le hδ₁ hdom,
    sbxS4_firstCoinLaw_cond_map_fst δ _ _ hδ₀ hδ₁ hdom⟩

/-- The successful conditional first-step endpoint is exactly uniform on the
source endpoint ball. -/
theorem sbxS4_firstSegmentLaw_cond_endpoint {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ)) :
    (cond (sbxS4FirstSegmentLaw Δ R δ i P z ω) {q | q.2 = true}).map
      (fun q : Path d × Bool => q.1 Δ) =
        cond (volume : Measure (Vec d)) (endpointBall i R z) := by
  have hs := (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ hminor).2.2.2 true
  change (cond (sbxS4FirstSegmentLaw Δ R δ i P z ω) {q | q.2 = true}).map
    ((fun γ : Path d => γ Δ) ∘ Prod.fst) = _
  rw [← Measure.map_map (continuous_eval_const Δ).measurable measurable_fst]
  rw [hs]
  exact sbxS4_map_killedBridgeMixture_endpoint Δ R δ i P z ω hR hδ₀ hminor

/-- Staying in the coupling region on the entire closed first interval is
measurable in the actual continuous-path carrier. -/
theorem sbxS4_measurableSet_stays {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (z : Vec d) :
    MeasurableSet {γ : Path d | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R z} := by
  have hS : MeasurableSet {p : Vec d × Path d | ∀ t : ℝ≥0, t ≤ Δ →
      p.2 t ∈ couplingRegion i R p.1} :=
    (Renewal.isOpen_killedSegment_event Δ R i).measurableSet
  exact measurable_prodMk_left hS

/-- The actual bridge mixture inherits the killed law's confinement without
any endpoint-minorization hypothesis. -/
theorem sbxS4_ae_killedBridgeMixture_stays {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) :
    ∀ᵐ γ ∂Renewal.killedBridgeMixture Δ R i P z ω,
      ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R z := by
  have hk : ∀ᵐ γ ∂Renewal.killedSegmentLaw Δ R i P z ω,
      ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R z := by
    unfold Renewal.killedSegmentLaw
    exact ae_restrict_mem (sbxS4_measurableSet_stays Δ R i z)
  have hac : Renewal.killedBridgeMixture Δ R i P z ω ≪
      Renewal.killedSegmentLaw Δ R i P z ω := by
    unfold Renewal.killedBridgeMixture
    exact withDensity_absolutelyContinuous _ _
  exact hac.ae_le hk

/-- The successful conditional path stays in the actual coupling region
throughout the whole first interval, including its endpoints. -/
theorem sbxS4_firstSegmentLaw_cond_stays {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ)) :
    ∀ᵐ q ∂cond (sbxS4FirstSegmentLaw Δ R δ i P z ω) {q | q.2 = true},
      ∀ t : ℝ≥0, t ≤ Δ → q.1 t ∈ couplingRegion i R z := by
  have hstay := sbxS4_ae_killedBridgeMixture_stays Δ R i P z ω
  have hs := (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ hminor).2.2.2 true
  simp only [↓reduceIte] at hs
  rw [← hs] at hstay
  exact ae_of_ae_map measurable_fst.aemeasurable hstay

/-- Actual first-coin Bochner identities with integrability, for either coin
outcome and every bounded strongly measurable path test. -/
theorem sbxS4_firstSegmentLaw_integral_branch {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ))
    (F : Path d → E) (hF : StronglyMeasurable F)
    (hbounded : ∃ C : ℝ, ∀ γ, ‖F γ‖ ≤ C) (b : Bool) :
    Integrable ({q : Path d × Bool | q.2 = b}.indicator (fun q => F q.1))
      (sbxS4FirstSegmentLaw Δ R δ i P z ω) ∧
    (∫ q, {q : Path d × Bool | q.2 = b}.indicator (fun q => F q.1) q
      ∂sbxS4FirstSegmentLaw Δ R δ i P z ω) =
      if b then δ • (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω)
      else (1 - δ) • (∫ γ, F γ ∂sbxS4FailedSegmentLaw Δ R δ i P z ω) := by
  let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P z ω) :=
    sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P z ω hR hδ₀ hminor
  exact sbxS4_firstCoinLaw_integral_branch δ _ _ hδ₀.le hδ₁
    (sbxS4_smul_killedBridgeMixture_le Δ R δ i P z ω hR hminor) F hF hbounded b

/-- The genuine independent Bernoulli law for the remaining coins. -/
def sbxS4RemainingBitsLaw (δ : ℝ) : Measure BernoulliSequence :=
  Measure.infinitePi fun _ : ℕ => ENNReal.ofReal δ • Measure.dirac true +
    ENNReal.ofReal (1 - δ) • Measure.dirac false

/-- The remaining-bit product law is probability for a Bernoulli parameter. -/
theorem sbxS4_remainingBitsLaw_isProbabilityMeasure (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) : IsProbabilityMeasure (sbxS4RemainingBitsLaw δ) := by
  let : IsProbabilityMeasure (ENNReal.ofReal δ • Measure.dirac true +
      ENNReal.ofReal (1 - δ) • Measure.dirac false) := by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hδ₀ (sub_nonneg.mpr hδ₁), add_sub_cancel, ENNReal.ofReal_one]
  unfold sbxS4RemainingBitsLaw
  infer_instance

/-- Each coordinate of the independent remaining-bit law is the same genuine
Bernoulli measure as the first coin. -/
theorem sbxS4_remainingBitsLaw_map_eval (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (n : ℕ) :
    (sbxS4RemainingBitsLaw δ).map (fun β => β n) =
      ENNReal.ofReal δ • Measure.dirac true +
        ENNReal.ofReal (1 - δ) • Measure.dirac false := by
  let : IsProbabilityMeasure (ENNReal.ofReal δ • Measure.dirac true +
      ENNReal.ofReal (1 - δ) • Measure.dirac false) := by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hδ₀ (sub_nonneg.mpr hδ₁), add_sub_cancel, ENNReal.ofReal_one]
  exact Measure.infinitePi_map_eval _ n

/-- Attach an independent remaining-bit sequence after the actual first coin. -/
def sbxS4AttachRemainingBits {α : Type*}
    (q : (α × Bool) × BernoulliSequence) : α × BernoulliSequence :=
  (q.1.1, fun n => match n with | 0 => q.1.2 | n + 1 => q.2 n)

/-- Attaching the remaining bits is measurable in every coordinate. -/
theorem sbxS4_measurable_attachRemainingBits {α : Type*} [MeasurableSpace α] :
    Measurable (sbxS4AttachRemainingBits (α := α)) := by
  refine measurable_fst.fst.prodMk (Measurable.of_eval fun n => ?_)
  cases n with
  | zero => exact measurable_fst.snd
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

/-- Independent extension of an actual first-coin joint law to the literal
path/sequence carrier. -/
def sbxS4AttachBitsLaw {α : Type*} [MeasurableSpace α]
    (J : Measure (α × Bool)) (M : Measure BernoulliSequence) : Measure (α × BernoulliSequence) :=
  (J.prod M).map sbxS4AttachRemainingBits

/-- Reading the first coin and the remaining bits recovers the original
product measure. In particular the remaining bits are independent of the
entire first-step path/coin pair, not only of its coin marginal. -/
theorem sbxS4_attachBitsLaw_map_split {α : Type*} [MeasurableSpace α]
    (J : Measure (α × Bool)) (M : Measure BernoulliSequence) :
    (sbxS4AttachBitsLaw J M).map
      (fun q => ((q.1, q.2 0), fun n => q.2 (n + 1))) = J.prod M := by
  unfold sbxS4AttachBitsLaw
  rw [Measure.map_map (by fun_prop) sbxS4_measurable_attachRemainingBits]
  change (J.prod M).map id = J.prod M
  exact Measure.map_id

/-- Independent extension preserves probability. -/
theorem sbxS4_attachBitsLaw_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    (J : Measure (α × Bool)) (M : Measure BernoulliSequence)
    [IsProbabilityMeasure J] [IsProbabilityMeasure M] :
    IsProbabilityMeasure (sbxS4AttachBitsLaw J M) := by
  unfold sbxS4AttachBitsLaw
  infer_instance

/-- Reading the path and its first coin after extension gives exactly `J`. -/
theorem sbxS4_attachBitsLaw_map_first {α : Type*} [MeasurableSpace α]
    (J : Measure (α × Bool)) (M : Measure BernoulliSequence) [IsProbabilityMeasure M] :
    (sbxS4AttachBitsLaw J M).map (fun q => (q.1, q.2 0)) = J := by
  have he := congrArg (fun μ => μ.map Prod.fst) (sbxS4_attachBitsLaw_map_split J M)
  rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod,
    measure_univ, one_smul] at he
  exact he

/-- Literal path/sequence law for the first split step with independent
Bernoulli remaining bits. No later-interval diffusion is asserted. -/
def sbxS4FirstSegmentWithBitsLaw {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (z : Vec d) (ω : FieldPair d) : Measure (CoupledSample d) :=
  sbxS4AttachBitsLaw (sbxS4FirstSegmentLaw Δ R δ i P z ω) (sbxS4RemainingBitsLaw δ)

/-- The actual single-fibre first-step law on the coupled carrier is
probability, has the exact original path marginal, and has exactly the
constructed first-step law times the genuine independent Bernoulli tail. -/
theorem sbxS4_firstSegmentWithBitsLaw_spec {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ)) :
    IsProbabilityMeasure (sbxS4FirstSegmentWithBitsLaw Δ R δ i P z ω) ∧
    (sbxS4FirstSegmentWithBitsLaw Δ R δ i P z ω).map Prod.fst = P (z, ω) ∧
    (sbxS4FirstSegmentWithBitsLaw Δ R δ i P z ω).map
      (fun q => ((q.1, q.2 0), fun n => q.2 (n + 1))) =
        (sbxS4FirstSegmentLaw Δ R δ i P z ω).prod (sbxS4RemainingBitsLaw δ) := by
  have hs := sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ hminor
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) := hs.1
  let : IsProbabilityMeasure (sbxS4RemainingBitsLaw δ) :=
    sbxS4_remainingBitsLaw_isProbabilityMeasure δ hδ₀.le hδ₁.le
  refine ⟨sbxS4_attachBitsLaw_isProbabilityMeasure _ _, ?_,
    sbxS4_attachBitsLaw_map_split _ _⟩
  have he := congrArg (fun μ => μ.map Prod.fst)
    (sbxS4_attachBitsLaw_map_first (sbxS4FirstSegmentLaw Δ R δ i P z ω)
      (sbxS4RemainingBitsLaw δ))
  rw [Measure.map_map measurable_fst (by fun_prop), hs.2.1] at he
  exact he

/-! Finite prefixes of supplied measurable split transitions. Index zero is
literally the first segment and first coin; extending history `n` appends
segment/coin `n + 1`. These finite laws make no infinite concatenation claim. -/

/-- The first `n + 1` segment/coin pairs, in their chronological order. -/
abbrev sbxS4SplitHistory (α : Type*) (n : ℕ) :=
  (j : Finset.Iic n) → α × Bool

/-- Embed the actual first pair as the length-one history. -/
def sbxS4InitialHistory {α : Type*} (q : α × Bool) : sbxS4SplitHistory α 0 :=
  fun _ => q

/-- Initial-history embedding preserves measurability. -/
theorem sbxS4_measurable_initialHistory {α : Type*} [MeasurableSpace α] :
    Measurable (sbxS4InitialHistory (α := α)) :=
  measurable_pi_iff.mpr fun _ => measurable_id

/-- Finite history law obtained by iterating the supplied transition kernel.
Its initial measure is kept explicit so the first-coin construction can be
instantiated directly, without any extra initial randomness. -/
def sbxS4SplitPrefixLaw {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    (μ : Measure (α × Bool)) (n : ℕ) : Measure (sbxS4SplitHistory α n) :=
  Kernel.partialTraj (X := fun _ => α × Bool) κ 0 n ∘ₘ μ.map sbxS4InitialHistory

/-- All finite prefixes are normalized when the supplied steps are Markov. -/
theorem sbxS4_splitPrefixLaw_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    [∀ n, IsMarkovKernel (κ n)] (μ : Measure (α × Bool)) [IsProbabilityMeasure μ]
    (n : ℕ) : IsProbabilityMeasure (sbxS4SplitPrefixLaw κ μ n) := by
  unfold sbxS4SplitPrefixLaw
  infer_instance

/-- The initial pair is the actual pair supplied to the construction. -/
theorem sbxS4_splitPrefixLaw_zero {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    (μ : Measure (α × Bool)) :
    sbxS4SplitPrefixLaw κ μ 0 = μ.map sbxS4InitialHistory := by
  simp only [sbxS4SplitPrefixLaw, Kernel.partialTraj_self, Measure.id_comp]

/-- Forgetting a terminal part recovers exactly the shorter prefix. -/
theorem sbxS4_splitPrefixLaw_truncate {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    [∀ n, IsMarkovKernel (κ n)] (μ : Measure (α × Bool))
    {m n : ℕ} (hmn : m ≤ n) :
    (sbxS4SplitPrefixLaw κ μ n).map (Preorder.frestrictLe₂ (π := fun _ => α × Bool) hmn) =
      sbxS4SplitPrefixLaw κ μ m := by
  rw [sbxS4SplitPrefixLaw, Measure.map_comp _ _ (Preorder.measurable_frestrictLe₂ (X := fun _ => α × Bool) hmn),
    Kernel.partialTraj_map_frestrictLe₂]
  rfl

/-- Exact deterministic-time restart of the entire finite history law. -/
theorem sbxS4_splitPrefixLaw_restart {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    (μ : Measure (α × Bool)) {m n : ℕ} (hmn : m ≤ n) :
    Kernel.partialTraj (X := fun _ => α × Bool) κ m n ∘ₘ sbxS4SplitPrefixLaw κ μ m =
      sbxS4SplitPrefixLaw κ μ n := by
  rw [sbxS4SplitPrefixLaw, Measure.comp_assoc,
    Kernel.partialTraj_comp_partialTraj (Nat.zero_le m) hmn]
  rfl

/-- Bounded finite-history observations satisfy the exact restart identity. -/
theorem sbxS4_splitPrefixLaw_integral_restart {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    [∀ n, IsMarkovKernel (κ n)] (μ : Measure (α × Bool)) [IsProbabilityMeasure μ]
    {m n : ℕ} (hmn : m ≤ n) (F : sbxS4SplitHistory α n → E)
    (hF : StronglyMeasurable F) (hb : ∃ C : ℝ, ∀ h, ‖F h‖ ≤ C) :
    Integrable F (sbxS4SplitPrefixLaw κ μ n) ∧
      (∫ h, F h ∂sbxS4SplitPrefixLaw κ μ n) =
        ∫ h, ∫ h', F h' ∂Kernel.partialTraj (X := fun _ => α × Bool) κ m n h
          ∂sbxS4SplitPrefixLaw κ μ m := by
  let : IsProbabilityMeasure (sbxS4SplitPrefixLaw κ μ n) :=
    sbxS4_splitPrefixLaw_isProbabilityMeasure κ μ n
  obtain ⟨C, hC⟩ := hb
  have hi : Integrable F (sbxS4SplitPrefixLaw κ μ n) :=
    (integrable_const C).mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  refine ⟨hi, ?_⟩
  rw [← sbxS4_splitPrefixLaw_restart κ μ hmn,
    Measure.comp_eq_comp_const_apply] at hi ⊢
  exact Kernel.integral_comp hi

/-- Append the next actual segment and its coin to a finite history. -/
def sbxS4AppendHistory {α : Type*} [MeasurableSpace α] (n : ℕ)
    (q : sbxS4SplitHistory α n × (α × Bool)) : sbxS4SplitHistory α (n + 1) :=
  _root_.IicProdIoc (X := fun _ => α × Bool) n (n + 1)
    (q.1, MeasurableEquiv.piSingleton (X := fun _ => α × Bool) n q.2)

/-- The chronological history-extension operation is measurable. -/
theorem sbxS4_measurable_appendHistory {α : Type*} [MeasurableSpace α] (n : ℕ) :
    Measurable (sbxS4AppendHistory (α := α) n) :=
  (measurable_IicProdIoc (X := fun _ => α × Bool)).comp (measurable_fst.prodMk
    ((MeasurableEquiv.piSingleton (X := fun _ => α × Bool) n).measurable.comp measurable_snd))

/-- One step of `partialTraj` is the supplied transition with its past retained. -/
theorem sbxS4_partialTraj_succ {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    Kernel.partialTraj (X := fun _ => α × Bool) κ n (n + 1) =
      (Kernel.id ×ₖ κ n).map (sbxS4AppendHistory n) := by
  rw [Kernel.partialTraj_succ_self]
  have he := Kernel.map_prod_map (Kernel.id (α := sbxS4SplitHistory α n)) (κ n)
    measurable_id (MeasurableEquiv.piSingleton (X := fun _ => α × Bool) n).measurable
  rw [Kernel.map_id] at he
  rw [he, ← Kernel.map_comp_right _
    (measurable_id.prodMap
      (MeasurableEquiv.piSingleton (X := fun _ => α × Bool) n).measurable)
    (measurable_IicProdIoc (X := fun _ => α × Bool))]
  rfl

/-- The successor prefix is the genuine past/next-step composition-product,
pushed forward only by chronological concatenation of finite histories. -/
theorem sbxS4_splitPrefixLaw_succ {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    [∀ n, IsMarkovKernel (κ n)] (μ : Measure (α × Bool)) [IsProbabilityMeasure μ]
    (n : ℕ) :
    sbxS4SplitPrefixLaw κ μ (n + 1) =
      ((sbxS4SplitPrefixLaw κ μ n) ⊗ₘ κ n).map (sbxS4AppendHistory n) := by
  let : IsProbabilityMeasure (sbxS4SplitPrefixLaw κ μ n) :=
    sbxS4_splitPrefixLaw_isProbabilityMeasure κ μ n
  rw [← sbxS4_splitPrefixLaw_restart κ μ n.le_succ, sbxS4_partialTraj_succ,
    ← Measure.map_comp _ _ (sbxS4_measurable_appendHistory n),
    ← Measure.compProd_eq_comp_prod]

/-- Exact branch test at a finite prefix. `P h` and `B h` are the actual
laws at the endpoint encoded by `h`; the failed branch remains the literal
normalized subtraction. Only the supplied single-step kernel is assumed. -/
theorem sbxS4_splitPrefixLaw_integral_branch {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    [∀ n, IsMarkovKernel (κ n)] (μ : Measure (α × Bool)) [IsProbabilityMeasure μ]
    (n : ℕ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (P B : sbxS4SplitHistory α n → Measure α)
    (hP : ∀ h, IsProbabilityMeasure (P h)) (hB : ∀ h, IsFiniteMeasure (B h))
    (hdom : ∀ h, ENNReal.ofReal δ • B h ≤ P h)
    (hκ : ∀ h, κ n h = sbxS4FirstCoinLaw δ (P h) (B h))
    (F : sbxS4SplitHistory α n × α → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ q, ‖F q‖ ≤ C) (b : Bool) :
    (∫ q, {q : sbxS4SplitHistory α n × (α × Bool) | q.2.2 = b}.indicator
      (fun q => F (q.1, q.2.1)) q ∂((sbxS4SplitPrefixLaw κ μ n) ⊗ₘ κ n)) =
      ∫ h, if b then δ * (∫ x, F (h, x) ∂B h)
        else (1 - δ) * (∫ x, F (h, x) ∂sbxS4SplitResidual δ (P h) (B h))
          ∂sbxS4SplitPrefixLaw κ μ n := by
  let : IsProbabilityMeasure (sbxS4SplitPrefixLaw κ μ n) :=
    sbxS4_splitPrefixLaw_isProbabilityMeasure κ μ n
  have hs : MeasurableSet {q : sbxS4SplitHistory α n × (α × Bool) | q.2.2 = b} :=
    (measurable_snd.comp measurable_snd) (measurableSet_singleton b)
  have hm : Measurable (fun q : sbxS4SplitHistory α n × (α × Bool) =>
      F (q.1, q.2.1)) := hF.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  obtain ⟨C, hC⟩ := hb
  have hi : Integrable (fun q : sbxS4SplitHistory α n × (α × Bool) => F (q.1, q.2.1))
      ((sbxS4SplitPrefixLaw κ μ n) ⊗ₘ κ n) :=
    (integrable_const C).mono' hm.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => hC (q.1, q.2.1))
  rw [Measure.integral_compProd (hi.indicator hs)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro h
  let : IsProbabilityMeasure (P h) := hP h
  let : IsFiniteMeasure (B h) := hB h
  dsimp only
  rw [hκ h]
  have he := (sbxS4_firstCoinLaw_integral_branch δ (P h) (B h) hδ₀ hδ₁ (hdom h)
    (fun x => F (h, x)) (hF.comp measurable_prodMk_left).stronglyMeasurable
    ⟨C, fun x => hC (h, x)⟩ b).2
  simpa only [Set.indicator, Set.mem_ofPred_eq, smul_eq_mul] using he

/-- The branch integral only needs the split identities on histories reached
almost surely by the finite prefix. -/
theorem sbxS4_splitPrefixLaw_integral_branch_ae {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    [∀ n, IsMarkovKernel (κ n)] (μ : Measure (α × Bool)) [IsProbabilityMeasure μ]
    (n : ℕ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (P B : sbxS4SplitHistory α n → Measure α)
    (hgood : ∀ᵐ h ∂sbxS4SplitPrefixLaw κ μ n,
      IsProbabilityMeasure (P h) ∧ IsFiniteMeasure (B h) ∧
      ENNReal.ofReal δ • B h ≤ P h ∧ κ n h = sbxS4FirstCoinLaw δ (P h) (B h))
    (F : sbxS4SplitHistory α n × α → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ q, ‖F q‖ ≤ C) (b : Bool) :
    (∫ q, {q : sbxS4SplitHistory α n × (α × Bool) | q.2.2 = b}.indicator
      (fun q => F (q.1, q.2.1)) q ∂((sbxS4SplitPrefixLaw κ μ n) ⊗ₘ κ n)) =
      ∫ h, if b then δ * (∫ x, F (h, x) ∂B h)
        else (1 - δ) * (∫ x, F (h, x) ∂sbxS4SplitResidual δ (P h) (B h))
          ∂sbxS4SplitPrefixLaw κ μ n := by
  let : IsProbabilityMeasure (sbxS4SplitPrefixLaw κ μ n) :=
    sbxS4_splitPrefixLaw_isProbabilityMeasure κ μ n
  have hs : MeasurableSet {q : sbxS4SplitHistory α n × (α × Bool) | q.2.2 = b} :=
    (measurable_snd.comp measurable_snd) (measurableSet_singleton b)
  have hm : Measurable (fun q : sbxS4SplitHistory α n × (α × Bool) =>
      F (q.1, q.2.1)) := hF.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  obtain ⟨C, hC⟩ := hb
  have hi : Integrable (fun q : sbxS4SplitHistory α n × (α × Bool) => F (q.1, q.2.1))
      ((sbxS4SplitPrefixLaw κ μ n) ⊗ₘ κ n) :=
    (integrable_const C).mono' hm.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => hC (q.1, q.2.1))
  rw [Measure.integral_compProd (hi.indicator hs)]
  apply integral_congr_ae
  filter_upwards [hgood] with h hh
  let : IsProbabilityMeasure (P h) := hh.1
  let : IsFiniteMeasure (B h) := hh.2.1
  rw [hh.2.2.2]
  have he := (sbxS4_firstCoinLaw_integral_branch δ (P h) (B h) hδ₀ hδ₁ hh.2.2.1
    (fun x => F (h, x)) (hF.comp measurable_prodMk_left).stronglyMeasurable
    ⟨C, fun x => hC (h, x)⟩ b).2
  simpa only [Set.indicator, Set.mem_ofPred_eq, smul_eq_mul] using he

/-- An integrable history and next-path test splits on either actual next coin. -/
theorem sbxS4_splitPrefixLaw_integrable_branch {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    [∀ n, IsMarkovKernel (κ n)] (μ : Measure (α × Bool)) [IsProbabilityMeasure μ]
    (n : ℕ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (P B : sbxS4SplitHistory α n → Measure α)
    (hB : ∀ h, IsFiniteMeasure (B h))
    (hdom : ∀ h, ENNReal.ofReal δ • B h ≤ P h)
    (hκ : ∀ h, κ n h = sbxS4FirstCoinLaw δ (P h) (B h))
    (F : sbxS4SplitHistory α n × α → ℝ) (hF : Measurable F)
    (hi : Integrable (fun q : sbxS4SplitHistory α n × (α × Bool) => F (q.1, q.2.1))
      ((sbxS4SplitPrefixLaw κ μ n) ⊗ₘ κ n)) (b : Bool) :
    Integrable ({q : sbxS4SplitHistory α n × (α × Bool) | q.2.2 = b}.indicator
      (fun q => F (q.1, q.2.1))) ((sbxS4SplitPrefixLaw κ μ n) ⊗ₘ κ n) ∧
    (∫ q, {q : sbxS4SplitHistory α n × (α × Bool) | q.2.2 = b}.indicator
      (fun q => F (q.1, q.2.1)) q ∂((sbxS4SplitPrefixLaw κ μ n) ⊗ₘ κ n)) =
      ∫ h, if b then δ * (∫ x, F (h, x) ∂B h)
        else (1 - δ) * (∫ x, F (h, x) ∂sbxS4SplitResidual δ (P h) (B h))
          ∂sbxS4SplitPrefixLaw κ μ n := by
  let : IsProbabilityMeasure (sbxS4SplitPrefixLaw κ μ n) :=
    sbxS4_splitPrefixLaw_isProbabilityMeasure κ μ n
  have hs : MeasurableSet {q : sbxS4SplitHistory α n × (α × Bool) | q.2.2 = b} :=
    (measurable_snd.comp measurable_snd) (measurableSet_singleton b)
  have ha := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi
  refine ⟨hi.indicator hs, ?_⟩
  rw [Measure.integral_compProd (hi.indicator hs)]
  apply integral_congr_ae
  filter_upwards [ha.1] with h hh
  let : IsFiniteMeasure (B h) := hB h
  rw [hκ h] at hh ⊢
  have hf : Integrable (fun x => F (h, x)) (P h) := by
    rw [← sbxS4_firstCoinLaw_map_fst δ (P h) (B h) hδ₁ (hdom h)]
    exact (integrable_map_measure (hF.comp measurable_prodMk_left).aestronglyMeasurable
      measurable_fst.aemeasurable).mpr hh
  have he := (sbxS4_firstCoinLaw_integrable_branch δ (P h) (B h) hδ₀ hδ₁ (hdom h)
    (fun x => F (h, x)) (hF.comp measurable_prodMk_left).stronglyMeasurable hf b).2
  simpa only [Set.indicator, Set.mem_ofPred_eq] using he

/-- The last new pair is precisely the appended pair. -/
theorem sbxS4_appendHistory_last {α : Type*} [MeasurableSpace α] (n : ℕ)
    (q : sbxS4SplitHistory α n × (α × Bool)) :
    sbxS4AppendHistory n q ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ = q.2 := by
  simp [sbxS4AppendHistory, _root_.IicProdIoc, MeasurableEquiv.piSingleton]

/-- Appending a new pair preserves every earlier pair. -/
theorem sbxS4_appendHistory_old {α : Type*} [MeasurableSpace α] (n : ℕ)
    (q : sbxS4SplitHistory α n × (α × Bool)) (j : Finset.Iic n) :
    sbxS4AppendHistory n q ⟨j.1, Finset.mem_Iic.mpr
      ((Finset.mem_Iic.mp j.2).trans n.le_succ)⟩ = q.1 j := by
  simp [sbxS4AppendHistory, _root_.IicProdIoc, Finset.mem_Iic.mp j.2]

/-- The literal coin cylinder specifying outcomes zero through `n`. -/
def sbxS4CoinPrefixEvent {α : Type*} (b : ℕ → Bool) (n : ℕ) :
    Set (sbxS4SplitHistory α n) := {h | ∀ j, (h j).2 = b j.1}

/-- Every finite coin cylinder is measurable. -/
theorem sbxS4_measurableSet_coinPrefixEvent {α : Type*} [MeasurableSpace α]
    (b : ℕ → Bool) (n : ℕ) : MeasurableSet (sbxS4CoinPrefixEvent (α := α) b n) := by
  rw [sbxS4CoinPrefixEvent, Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    (measurable_snd.comp (measurable_pi_apply j)) (measurableSet_singleton (b j.1))

/-- A cylinder at the next horizon is the old cylinder and the next outcome. -/
theorem sbxS4_appendHistory_preimage_coinPrefixEvent {α : Type*} [MeasurableSpace α]
    (b : ℕ → Bool) (n : ℕ) :
    sbxS4AppendHistory (α := α) n ⁻¹' sbxS4CoinPrefixEvent b (n + 1) =
      sbxS4CoinPrefixEvent b n ×ˢ {q : α × Bool | q.2 = b (n + 1)} := by
  ext q
  change (∀ j, (sbxS4AppendHistory n q j).2 = b j.1) ↔
    (∀ j, (q.1 j).2 = b j.1) ∧ q.2.2 = b (n + 1)
  constructor
  · intro h
    constructor
    · intro j
      simpa only [sbxS4_appendHistory_old] using
        h ⟨j.1, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp j.2).trans n.le_succ)⟩
    · simpa only [sbxS4_appendHistory_last] using h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩
  · rintro ⟨hold, hnew⟩ j
    by_cases hj : j.1 ≤ n
    · have he : j = ⟨j.1, Finset.mem_Iic.mpr (hj.trans n.le_succ)⟩ := rfl
      rw [he, sbxS4_appendHistory_old n q ⟨j.1, Finset.mem_Iic.mpr hj⟩]
      exact hold ⟨j.1, Finset.mem_Iic.mpr hj⟩
    · have hlast : j = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := by
        apply Subtype.ext
        change j.1 = n + 1
        have hj' := Finset.mem_Iic.mp j.2
        omega
      rw [hlast, sbxS4_appendHistory_last]
      exact hnew

/-- Total masses of the two coins, including the genuine residual branch. -/
theorem sbxS4_firstCoinLaw_coin_mass {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure B]
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (hdom : ENNReal.ofReal δ • B ≤ P) (b : Bool) :
    sbxS4FirstCoinLaw δ P B {q | q.2 = b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ) := by
  let : IsProbabilityMeasure (sbxS4SplitResidual δ P B) :=
    sbxS4_splitResidual_isProbabilityMeasure δ P B hδ₀ hδ₁ hdom
  simpa only [Set.mem_univ, true_and, measure_univ, mul_one] using
    sbxS4_firstCoinLaw_apply δ P B Set.univ MeasurableSet.univ b

/-- A next coin is Bernoulli independently of every measurable event in the
entire finite past. This uses the supplied step's exact coin marginal. -/
theorem sbxS4_splitPrefixLaw_nextCoin_mass {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    [∀ n, IsMarkovKernel (κ n)] (μ : Measure (α × Bool)) [IsProbabilityMeasure μ]
    (n : ℕ) (δ : ℝ) (b : Bool)
    (hcoin : ∀ h, κ n h {q | q.2 = b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ))
    (H : Set (sbxS4SplitHistory α n)) (hH : MeasurableSet H) :
    ((sbxS4SplitPrefixLaw κ μ n) ⊗ₘ κ n) (H ×ˢ {q | q.2 = b}) =
      sbxS4SplitPrefixLaw κ μ n H *
        (if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ)) := by
  let : IsProbabilityMeasure (sbxS4SplitPrefixLaw κ μ n) :=
    sbxS4_splitPrefixLaw_isProbabilityMeasure κ μ n
  have hb : MeasurableSet {q : α × Bool | q.2 = b} :=
    measurable_snd (measurableSet_singleton b)
  rw [Measure.compProd_apply_prod hH hb]
  simp_rw [hcoin]
  simp only [lintegral_const, Measure.restrict_apply_univ]
  exact mul_comm _ _

/-- The complete finite coin cylinder has exactly the product of its
Bernoulli factors, including the actual first coin at index zero. -/
theorem sbxS4_splitPrefixLaw_coin_cylinder {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    [∀ n, IsMarkovKernel (κ n)] (μ : Measure (α × Bool)) [IsProbabilityMeasure μ]
    (δ : ℝ)
    (hμ : ∀ b : Bool, μ {q | q.2 = b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ))
    (hcoin : ∀ n h (b : Bool), κ n h {q | q.2 = b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ))
    (b : ℕ → Bool) (n : ℕ) :
    sbxS4SplitPrefixLaw κ μ n (sbxS4CoinPrefixEvent b n) =
      ∏ j ∈ Finset.range (n + 1),
        (if b j then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ)) := by
  induction n with
  | zero =>
    rw [sbxS4_splitPrefixLaw_zero,
      Measure.map_apply sbxS4_measurable_initialHistory
        (sbxS4_measurableSet_coinPrefixEvent b 0)]
    have he : sbxS4InitialHistory (α := α) ⁻¹' sbxS4CoinPrefixEvent b 0 =
        {q | q.2 = b 0} := by
      ext q
      simp only [Set.mem_preimage, sbxS4CoinPrefixEvent, Set.mem_ofPred_eq,
        sbxS4InitialHistory]
      constructor
      · intro h
        exact h ⟨0, Finset.mem_Iic.mpr le_rfl⟩
      · intro h j
        have hj : j.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp j.2)
        simpa only [hj] using h
    rw [he, hμ]
    simp only [Nat.zero_add, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  | succ n ih =>
    rw [sbxS4_splitPrefixLaw_succ,
      Measure.map_apply (sbxS4_measurable_appendHistory n)
        (sbxS4_measurableSet_coinPrefixEvent b (n + 1)),
      sbxS4_appendHistory_preimage_coinPrefixEvent,
      sbxS4_splitPrefixLaw_nextCoin_mass κ μ n δ (b (n + 1)) (fun h => hcoin n h _)
        _ (sbxS4_measurableSet_coinPrefixEvent b n), ih]
    exact (Finset.prod_range_succ _ (n + 1)).symm

/-- Truncation after appending a segment returns the entire previous history. -/
theorem sbxS4_appendHistory_restrict {α : Type*} [MeasurableSpace α] (n : ℕ)
    (q : sbxS4SplitHistory α n × (α × Bool)) :
    Preorder.frestrictLe₂ (π := fun _ => α × Bool) n.le_succ
      (sbxS4AppendHistory n q) = q.1 := by
  exact congrFun (frestrictLe₂_comp_IicProdIoc (X := fun _ => α × Bool) n.le_succ)
    (q.1, MeasurableEquiv.piSingleton (X := fun _ => α × Bool) n q.2)

/-- The same two-branch formula expressed directly on the longer prefix law,
with its whole earlier history and last segment retained in the test. -/
theorem sbxS4_splitPrefixLaw_integral_last {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    [∀ n, IsMarkovKernel (κ n)] (μ : Measure (α × Bool)) [IsProbabilityMeasure μ]
    (n : ℕ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (P B : sbxS4SplitHistory α n → Measure α)
    (hP : ∀ h, IsProbabilityMeasure (P h)) (hB : ∀ h, IsFiniteMeasure (B h))
    (hdom : ∀ h, ENNReal.ofReal δ • B h ≤ P h)
    (hκ : ∀ h, κ n h = sbxS4FirstCoinLaw δ (P h) (B h))
    (F : sbxS4SplitHistory α n × α → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ q, ‖F q‖ ≤ C) (b : Bool) :
    (∫ h, {h : sbxS4SplitHistory α (n + 1) |
        (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2 = b}.indicator
      (fun h => F (Preorder.frestrictLe₂ (π := fun _ => α × Bool) n.le_succ h,
        (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1)) h
      ∂sbxS4SplitPrefixLaw κ μ (n + 1)) =
      ∫ h, if b then δ * (∫ x, F (h, x) ∂B h)
        else (1 - δ) * (∫ x, F (h, x) ∂sbxS4SplitResidual δ (P h) (B h))
          ∂sbxS4SplitPrefixLaw κ μ n := by
  have hm : Measurable (fun h : sbxS4SplitHistory α (n + 1) =>
      F (Preorder.frestrictLe₂ (π := fun _ => α × Bool) n.le_succ h,
        (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1)) :=
    hF.comp ((Preorder.measurable_frestrictLe₂ (X := fun _ => α × Bool) n.le_succ).prodMk
      (measurable_fst.comp (measurable_pi_apply _)))
  have hs : MeasurableSet {h : sbxS4SplitHistory α (n + 1) |
      (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2 = b} :=
    (measurable_snd.comp (measurable_pi_apply _)) (measurableSet_singleton b)
  rw [sbxS4_splitPrefixLaw_succ,
    integral_map_of_stronglyMeasurable (sbxS4_measurable_appendHistory n)
      (hm.indicator hs).stronglyMeasurable]
  simpa only [Set.indicator, Set.mem_ofPred_eq, sbxS4_appendHistory_restrict,
    sbxS4_appendHistory_last] using
    sbxS4_splitPrefixLaw_integral_branch κ μ n δ hδ₀ hδ₁ P B hP hB hdom hκ F hF hb b

/-- The next grid segment starts at the endpoint of the last segment. -/
def sbxS4HistoryEndpoint {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (h : sbxS4SplitHistory (Path d) n) : Vec d :=
  (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1 Δ

/-- Reading the last actual segment endpoint is measurable. -/
theorem sbxS4_measurable_historyEndpoint {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    Measurable (sbxS4HistoryEndpoint (d := d) Δ n) :=
  (continuous_eval_const Δ).measurable.comp
    (measurable_fst.comp
      (measurable_pi_apply (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)))

/-- A supplied measurable split kernel is restarted at the actual last endpoint. -/
def sbxS4EndpointHistoryKernel {d : ℕ} (Δ : ℝ≥0)
    (K : Kernel (Vec d) (Path d × Bool)) (n : ℕ) :
    Kernel (sbxS4SplitHistory (Path d) n) (Path d × Bool) :=
  K.comap (sbxS4HistoryEndpoint Δ n) (sbxS4_measurable_historyEndpoint Δ n)

/-- Endpoint restart preserves normalization of the supplied split kernel. -/
instance sbxS4_endpointHistoryKernel_isMarkov {d : ℕ} (Δ : ℝ≥0)
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (sbxS4EndpointHistoryKernel Δ K n) := by
  unfold sbxS4EndpointHistoryKernel
  infer_instance

/-- Forgetting the next split coin retains the entire finite prefix and
recovers the supplied path kernel at its actual last endpoint. -/
theorem sbxS4_endpointHistoryKernel_forget_coin {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (ω : FieldPair d) (hP : ∀ x, IsProbabilityMeasure (P (x, ω)))
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
      (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K]
    (hK : ∀ x, K x = sbxS4FirstSegmentLaw Δ R δ i P x ω)
    (n : ℕ) (μ : Measure (sbxS4SplitHistory (Path d) n)) [SFinite μ] :
    (μ ⊗ₘ sbxS4EndpointHistoryKernel Δ K n).map
        (Prod.map id Prod.fst) =
      μ ⊗ₘ P.comap (fun h => (sbxS4HistoryEndpoint Δ n h, ω))
        ((sbxS4_measurable_historyEndpoint Δ n).prodMk measurable_const) := by
  rw [← Measure.compProd_map measurable_fst]
  congr 1
  ext h s hs
  rw [Kernel.map_apply _ measurable_fst, Kernel.comap_apply]
  unfold sbxS4EndpointHistoryKernel
  rw [Kernel.comap_apply, hK]
  let : IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) := hP _
  rw [(sbxS4_firstSegmentLaw_spec Δ R δ i P _ ω hR hδ₀ hδ₁ (hminor _)).2.1]

/-- Forgetting the coin requires the split construction only at endpoints
actually reached by the supplied finite-prefix law. -/
theorem sbxS4_endpointHistoryKernel_forget_coin_ae {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    [IsSFiniteKernel P] (ω : FieldPair d) (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K]
    (n : ℕ) (μ : Measure (sbxS4SplitHistory (Path d) n)) [SFinite μ]
    (hgood : ∀ᵐ h ∂μ, IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) ∧
      ENNReal.ofReal δ • cond (volume : Measure (Vec d))
        (endpointBall i R (sbxS4HistoryEndpoint Δ n h)) ≤
        (Renewal.killedSegmentLaw Δ R i P (sbxS4HistoryEndpoint Δ n h) ω).map
          (fun γ : Path d => γ Δ) ∧
      K (sbxS4HistoryEndpoint Δ n h) =
        sbxS4FirstSegmentLaw Δ R δ i P (sbxS4HistoryEndpoint Δ n h) ω) :
    (μ ⊗ₘ sbxS4EndpointHistoryKernel Δ K n).map (Prod.map id Prod.fst) =
      μ ⊗ₘ P.comap (fun h => (sbxS4HistoryEndpoint Δ n h, ω))
        ((sbxS4_measurable_historyEndpoint Δ n).prodMk measurable_const) := by
  rw [← Measure.compProd_map measurable_fst]
  apply Measure.compProd_congr
  filter_upwards [hgood] with h hh
  ext s hs
  rw [Kernel.map_apply _ measurable_fst, Kernel.comap_apply]
  unfold sbxS4EndpointHistoryKernel
  rw [Kernel.comap_apply, hh.2.2]
  let : IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) := hh.1
  rw [(sbxS4_firstSegmentLaw_spec Δ R δ i P _ ω hR hδ₀ hδ₁ hh.2.1).2.1]

/-- The same recovered joint law retains the complete prefix and the
literal next segment stopped at the interval endpoint. -/
theorem sbxS4_endpointHistoryKernel_forget_coin_stopped {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (ω : FieldPair d) (hP : ∀ x, IsProbabilityMeasure (P (x, ω)))
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
      (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K]
    (hK : ∀ x, K x = sbxS4FirstSegmentLaw Δ R δ i P x ω)
    (n : ℕ) (μ : Measure (sbxS4SplitHistory (Path d) n)) [SFinite μ] :
    (μ ⊗ₘ sbxS4EndpointHistoryKernel Δ K n).map
        (fun q => (q.1, Diffusion.stopPathAt Δ q.2.1)) =
      (μ ⊗ₘ P.comap (fun h => (sbxS4HistoryEndpoint Δ n h, ω))
        ((sbxS4_measurable_historyEndpoint Δ n).prodMk measurable_const)).map
        (fun q => (q.1, Diffusion.stopPathAt Δ q.2)) := by
  have hm : Measurable (fun q : sbxS4SplitHistory (Path d) n × Path d =>
      (q.1, Diffusion.stopPathAt Δ q.2)) :=
    measurable_fst.prodMk ((Diffusion.continuous_stopPathAt Δ).measurable.comp measurable_snd)
  have hp : Measurable (Prod.map id Prod.fst :
      sbxS4SplitHistory (Path d) n × (Path d × Bool) →
        sbxS4SplitHistory (Path d) n × Path d) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have he := congrArg (fun ν : Measure (sbxS4SplitHistory (Path d) n × Path d) =>
    ν.map (fun q => (q.1, Diffusion.stopPathAt Δ q.2)))
    (sbxS4_endpointHistoryKernel_forget_coin Δ R δ i P ω hP hR hδ₀ hδ₁ hminor K hK n μ)
  rw [Measure.map_map hm hp] at he
  exact he

/-- Signed integrable tests of the retained prefix and stopped next segment
transfer from the supplied law to the actual split joint law. -/
theorem sbxS4_endpointHistoryKernel_stopped_integral {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (ω : FieldPair d) (hP : ∀ x, IsProbabilityMeasure (P (x, ω)))
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
      (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K]
    (hK : ∀ x, K x = sbxS4FirstSegmentLaw Δ R δ i P x ω)
    (n : ℕ) (μ : Measure (sbxS4SplitHistory (Path d) n)) [SFinite μ]
    (F : sbxS4SplitHistory (Path d) n × Path d → ℝ)
    (hF : Integrable F ((μ ⊗ₘ P.comap
      (fun h => (sbxS4HistoryEndpoint Δ n h, ω))
      ((sbxS4_measurable_historyEndpoint Δ n).prodMk measurable_const)).map
      (fun q => (q.1, Diffusion.stopPathAt Δ q.2)))) :
    Integrable (fun q => F (q.1, Diffusion.stopPathAt Δ q.2.1))
        (μ ⊗ₘ sbxS4EndpointHistoryKernel Δ K n) ∧
      (∫ q, F (q.1, Diffusion.stopPathAt Δ q.2.1)
          ∂(μ ⊗ₘ sbxS4EndpointHistoryKernel Δ K n)) =
        ∫ q, F q ∂((μ ⊗ₘ P.comap
          (fun h => (sbxS4HistoryEndpoint Δ n h, ω))
          ((sbxS4_measurable_historyEndpoint Δ n).prodMk measurable_const)).map
          (fun q => (q.1, Diffusion.stopPathAt Δ q.2))) := by
  have hm : Measurable (fun q : sbxS4SplitHistory (Path d) n × (Path d × Bool) =>
      (q.1, Diffusion.stopPathAt Δ q.2.1)) :=
    measurable_fst.prodMk ((Diffusion.continuous_stopPathAt Δ).measurable.comp
      (measurable_fst.comp measurable_snd))
  have he := sbxS4_endpointHistoryKernel_forget_coin_stopped Δ R δ i P ω hP hR
    hδ₀ hδ₁ hminor K hK n μ
  have hi : Integrable F ((μ ⊗ₘ sbxS4EndpointHistoryKernel Δ K n).map
      (fun q => (q.1, Diffusion.stopPathAt Δ q.2.1))) := by
    rw [he]
    exact hF
  refine ⟨hi.comp_measurable hm, ?_⟩
  calc
    _ = ∫ q, F q ∂((μ ⊗ₘ sbxS4EndpointHistoryKernel Δ K n).map
        (fun q => (q.1, Diffusion.stopPathAt Δ q.2.1))) :=
      (integral_map hm.aemeasurable hi.aestronglyMeasurable).symm
    _ = _ := by rw [he]

/-- Under almost-everywhere good endpoints the recovered law retains the prefix and the
literal next segment stopped at the interval endpoint. -/
theorem sbxS4_endpointHistoryKernel_forget_coin_stopped_ae {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    [IsSFiniteKernel P] (ω : FieldPair d) (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K]
    (n : ℕ) (μ : Measure (sbxS4SplitHistory (Path d) n)) [SFinite μ]
    (hgood : ∀ᵐ h ∂μ, IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) ∧
      ENNReal.ofReal δ • cond (volume : Measure (Vec d))
        (endpointBall i R (sbxS4HistoryEndpoint Δ n h)) ≤
        (Renewal.killedSegmentLaw Δ R i P (sbxS4HistoryEndpoint Δ n h) ω).map
          (fun γ : Path d => γ Δ) ∧
      K (sbxS4HistoryEndpoint Δ n h) =
        sbxS4FirstSegmentLaw Δ R δ i P (sbxS4HistoryEndpoint Δ n h) ω) :
    (μ ⊗ₘ sbxS4EndpointHistoryKernel Δ K n).map
        (fun q => (q.1, Diffusion.stopPathAt Δ q.2.1)) =
      (μ ⊗ₘ P.comap (fun h => (sbxS4HistoryEndpoint Δ n h, ω))
        ((sbxS4_measurable_historyEndpoint Δ n).prodMk measurable_const)).map
        (fun q => (q.1, Diffusion.stopPathAt Δ q.2)) := by
  have hm : Measurable (fun q : sbxS4SplitHistory (Path d) n × Path d =>
      (q.1, Diffusion.stopPathAt Δ q.2)) :=
    measurable_fst.prodMk ((Diffusion.continuous_stopPathAt Δ).measurable.comp measurable_snd)
  have hp : Measurable (Prod.map id Prod.fst :
      sbxS4SplitHistory (Path d) n × (Path d × Bool) →
        sbxS4SplitHistory (Path d) n × Path d) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have he := congrArg (fun ν : Measure (sbxS4SplitHistory (Path d) n × Path d) =>
    ν.map (fun q => (q.1, Diffusion.stopPathAt Δ q.2)))
    (sbxS4_endpointHistoryKernel_forget_coin_ae Δ R δ i P ω hR hδ₀ hδ₁ K n μ hgood)
  rw [Measure.map_map hm hp] at he
  exact he

/-- With almost-everywhere good endpoints, signed integrable tests of the prefix and stopped segment
transfer from the supplied law to the actual split joint law. -/
theorem sbxS4_endpointHistoryKernel_stopped_integral_ae {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    [IsSFiniteKernel P] (ω : FieldPair d) (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K]
    (n : ℕ) (μ : Measure (sbxS4SplitHistory (Path d) n)) [SFinite μ]
    (hgood : ∀ᵐ h ∂μ, IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) ∧
      ENNReal.ofReal δ • cond (volume : Measure (Vec d))
        (endpointBall i R (sbxS4HistoryEndpoint Δ n h)) ≤
        (Renewal.killedSegmentLaw Δ R i P (sbxS4HistoryEndpoint Δ n h) ω).map
          (fun γ : Path d => γ Δ) ∧
      K (sbxS4HistoryEndpoint Δ n h) =
        sbxS4FirstSegmentLaw Δ R δ i P (sbxS4HistoryEndpoint Δ n h) ω)
    (F : sbxS4SplitHistory (Path d) n × Path d → ℝ)
    (hF : Integrable F ((μ ⊗ₘ P.comap
      (fun h => (sbxS4HistoryEndpoint Δ n h, ω))
      ((sbxS4_measurable_historyEndpoint Δ n).prodMk measurable_const)).map
      (fun q => (q.1, Diffusion.stopPathAt Δ q.2)))) :
    Integrable (fun q => F (q.1, Diffusion.stopPathAt Δ q.2.1))
        (μ ⊗ₘ sbxS4EndpointHistoryKernel Δ K n) ∧
      (∫ q, F (q.1, Diffusion.stopPathAt Δ q.2.1)
          ∂(μ ⊗ₘ sbxS4EndpointHistoryKernel Δ K n)) =
        ∫ q, F q ∂((μ ⊗ₘ P.comap
          (fun h => (sbxS4HistoryEndpoint Δ n h, ω))
          ((sbxS4_measurable_historyEndpoint Δ n).prodMk measurable_const)).map
          (fun q => (q.1, Diffusion.stopPathAt Δ q.2))) := by
  have hm : Measurable (fun q : sbxS4SplitHistory (Path d) n × (Path d × Bool) =>
      (q.1, Diffusion.stopPathAt Δ q.2.1)) :=
    measurable_fst.prodMk ((Diffusion.continuous_stopPathAt Δ).measurable.comp
      (measurable_fst.comp measurable_snd))
  have he := sbxS4_endpointHistoryKernel_forget_coin_stopped_ae Δ R δ i P ω hR
    hδ₀ hδ₁ K n μ hgood
  have hi : Integrable F ((μ ⊗ₘ sbxS4EndpointHistoryKernel Δ K n).map
      (fun q => (q.1, Diffusion.stopPathAt Δ q.2.1))) := by
    rw [he]
    exact hF
  refine ⟨hi.comp_measurable hm, ?_⟩
  calc
    _ = ∫ q, F q ∂((μ ⊗ₘ sbxS4EndpointHistoryKernel Δ K n).map
        (fun q => (q.1, Diffusion.stopPathAt Δ q.2.1))) :=
      (integral_map hm.aemeasurable hi.aestronglyMeasurable).symm
    _ = _ := by rw [he]

/-- Finite deterministic-grid law with the actual first segment at index zero. -/
def sbxS4SegmentPrefixLaw {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (z : Vec d) (ω : FieldPair d)
    (K : Kernel (Vec d) (Path d × Bool)) (n : ℕ) :
    Measure (sbxS4SplitHistory (Path d) n) :=
  sbxS4SplitPrefixLaw (sbxS4EndpointHistoryKernel Δ K)
    (sbxS4FirstSegmentLaw Δ R δ i P z ω) n

/-- The actual first segment has precisely the Bernoulli coin mass. -/
theorem sbxS4_firstSegmentLaw_coin_mass {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ)) (b : Bool) :
    sbxS4FirstSegmentLaw Δ R δ i P z ω {q | q.2 = b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ) := by
  let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P z ω) :=
    sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P z ω hR hδ₀ hminor
  exact sbxS4_firstCoinLaw_coin_mass δ _ _ hδ₀.le hδ₁
    (sbxS4_smul_killedBridgeMixture_le Δ R δ i P z ω hR hminor) b

/-- Every finite actual segment/coin prefix is normalized. -/
theorem sbxS4_segmentPrefixLaw_isProbabilityMeasure {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ))
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K] (n : ℕ) :
    IsProbabilityMeasure (sbxS4SegmentPrefixLaw Δ R δ i P z ω K n) := by
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ hminor).1
  exact sbxS4_splitPrefixLaw_isProbabilityMeasure _ _ n

/-- The stopped last segment of the actual successor prefix has the supplied
restart law, together with the entire preceding prefix. -/
theorem sbxS4_segmentPrefixLaw_stopped_last_ae {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    [IsSFiniteKernel P] (z : Vec d) (ω : FieldPair d)
    [IsProbabilityMeasure (P (z, ω))] (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor0 : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ))
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K] (n : ℕ)
    (hgood : ∀ᵐ h ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n,
      IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) ∧
      ENNReal.ofReal δ • cond (volume : Measure (Vec d))
        (endpointBall i R (sbxS4HistoryEndpoint Δ n h)) ≤
        (Renewal.killedSegmentLaw Δ R i P (sbxS4HistoryEndpoint Δ n h) ω).map
          (fun γ : Path d => γ Δ) ∧
      K (sbxS4HistoryEndpoint Δ n h) =
        sbxS4FirstSegmentLaw Δ R δ i P (sbxS4HistoryEndpoint Δ n h) ω) :
    (sbxS4SegmentPrefixLaw Δ R δ i P z ω K (n + 1)).map
        (fun h => (Preorder.frestrictLe₂ (π := fun _ => Path d × Bool) n.le_succ h,
          Diffusion.stopPathAt Δ (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1)) =
      ((sbxS4SegmentPrefixLaw Δ R δ i P z ω K n) ⊗ₘ
        P.comap (fun h => (sbxS4HistoryEndpoint Δ n h, ω))
          ((sbxS4_measurable_historyEndpoint Δ n).prodMk measurable_const)).map
        (fun q => (q.1, Diffusion.stopPathAt Δ q.2)) := by
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ hminor0).1
  let : IsProbabilityMeasure (sbxS4SplitPrefixLaw (sbxS4EndpointHistoryKernel Δ K)
      (sbxS4FirstSegmentLaw Δ R δ i P z ω) n) :=
    sbxS4_segmentPrefixLaw_isProbabilityMeasure Δ R δ i P z ω hR hδ₀ hδ₁ hminor0 K n
  have hm : Measurable (fun h : sbxS4SplitHistory (Path d) (n + 1) =>
      (Preorder.frestrictLe₂ (π := fun _ => Path d × Bool) n.le_succ h,
        Diffusion.stopPathAt Δ (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1)) :=
    (Preorder.measurable_frestrictLe₂ (X := fun _ => Path d × Bool) n.le_succ).prodMk
      ((Diffusion.continuous_stopPathAt Δ).measurable.comp
        (measurable_fst.comp (measurable_pi_apply _)))
  change (sbxS4SplitPrefixLaw (sbxS4EndpointHistoryKernel Δ K)
    (sbxS4FirstSegmentLaw Δ R δ i P z ω) (n + 1)).map _ = _
  rw [sbxS4_splitPrefixLaw_succ, Measure.map_map hm (sbxS4_measurable_appendHistory n)]
  have he : (fun q : sbxS4SplitHistory (Path d) n × (Path d × Bool) =>
      (Preorder.frestrictLe₂ (π := fun _ => Path d × Bool) n.le_succ
        (sbxS4AppendHistory n q),
        Diffusion.stopPathAt Δ ((sbxS4AppendHistory n q)
          ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1)) =
      (fun q => (q.1, Diffusion.stopPathAt Δ q.2.1)) := by
    funext q
    rw [sbxS4_appendHistory_restrict, sbxS4_appendHistory_last]
  simp only [Function.comp_def]
  rw [he]
  exact sbxS4_endpointHistoryKernel_forget_coin_stopped_ae Δ R δ i P ω hR hδ₀ hδ₁ K n _ hgood

/-- At almost every reached endpoint, the actual next coin splits a bounded
whole-history test into the successful bridge and normalized failed laws. -/
theorem sbxS4_segmentPrefixLaw_integral_last_ae {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor0 : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ))
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K] (n : ℕ)
    (hgood : ∀ᵐ h ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n,
      IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) ∧
      ENNReal.ofReal δ • cond (volume : Measure (Vec d))
        (endpointBall i R (sbxS4HistoryEndpoint Δ n h)) ≤
        (Renewal.killedSegmentLaw Δ R i P (sbxS4HistoryEndpoint Δ n h) ω).map
          (fun γ : Path d => γ Δ) ∧
      K (sbxS4HistoryEndpoint Δ n h) =
        sbxS4FirstSegmentLaw Δ R δ i P (sbxS4HistoryEndpoint Δ n h) ω)
    (F : sbxS4SplitHistory (Path d) n × Path d → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ q, ‖F q‖ ≤ C) (b : Bool) :
    (∫ h, {h : sbxS4SplitHistory (Path d) (n + 1) |
        (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2 = b}.indicator
      (fun h => F (Preorder.frestrictLe₂ (π := fun _ => Path d × Bool) n.le_succ h,
        (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1)) h
      ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K (n + 1)) =
    ∫ h, if b then δ * (∫ γ, F (h, γ) ∂Renewal.killedBridgeMixture Δ R i P
        (sbxS4HistoryEndpoint Δ n h) ω)
      else (1 - δ) * (∫ γ, F (h, γ) ∂sbxS4FailedSegmentLaw Δ R δ i P
        (sbxS4HistoryEndpoint Δ n h) ω)
      ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n := by
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ hminor0).1
  have hfiber : ∀ᵐ h ∂sbxS4SplitPrefixLaw (sbxS4EndpointHistoryKernel Δ K)
      (sbxS4FirstSegmentLaw Δ R δ i P z ω) n,
      IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) ∧
      IsFiniteMeasure (Renewal.killedBridgeMixture Δ R i P (sbxS4HistoryEndpoint Δ n h) ω) ∧
      ENNReal.ofReal δ • Renewal.killedBridgeMixture Δ R i P (sbxS4HistoryEndpoint Δ n h) ω ≤
        P (sbxS4HistoryEndpoint Δ n h, ω) ∧
      sbxS4EndpointHistoryKernel Δ K n h = sbxS4FirstCoinLaw δ
        (P (sbxS4HistoryEndpoint Δ n h, ω))
        (Renewal.killedBridgeMixture Δ R i P (sbxS4HistoryEndpoint Δ n h) ω) := by
    filter_upwards [hgood] with h hh
    let : IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) := hh.1
    let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P
        (sbxS4HistoryEndpoint Δ n h) ω) :=
      sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P _ ω hR hδ₀ hh.2.1
    exact ⟨hh.1, inferInstance, sbxS4_smul_killedBridgeMixture_le Δ R δ i P _ ω hR hh.2.1,
      hh.2.2⟩
  have hm : Measurable (fun h : sbxS4SplitHistory (Path d) (n + 1) =>
      F (Preorder.frestrictLe₂ (π := fun _ => Path d × Bool) n.le_succ h,
        (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1)) :=
    hF.comp ((Preorder.measurable_frestrictLe₂ (X := fun _ => Path d × Bool) n.le_succ).prodMk
      (measurable_fst.comp (measurable_pi_apply _)))
  have hs : MeasurableSet {h : sbxS4SplitHistory (Path d) (n + 1) |
      (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2 = b} :=
    (measurable_snd.comp (measurable_pi_apply _)) (measurableSet_singleton b)
  change (∫ h, _ ∂sbxS4SplitPrefixLaw (sbxS4EndpointHistoryKernel Δ K)
    (sbxS4FirstSegmentLaw Δ R δ i P z ω) (n + 1)) = _
  rw [sbxS4_splitPrefixLaw_succ,
    integral_map_of_stronglyMeasurable (sbxS4_measurable_appendHistory n)
      (hm.indicator hs).stronglyMeasurable]
  simpa only [Set.indicator, Set.mem_ofPred_eq, sbxS4_appendHistory_restrict,
    sbxS4_appendHistory_last, sbxS4SegmentPrefixLaw, sbxS4FailedSegmentLaw] using
    sbxS4_splitPrefixLaw_integral_branch_ae (sbxS4EndpointHistoryKernel Δ K)
      (sbxS4FirstSegmentLaw Δ R δ i P z ω) n δ hδ₀.le hδ₁
      (fun h => P (sbxS4HistoryEndpoint Δ n h, ω))
      (fun h => Renewal.killedBridgeMixture Δ R i P (sbxS4HistoryEndpoint Δ n h) ω)
      hfiber F hF hb b

/-- Chronologically append a path at a deterministic time, translating its
initial point to the preceding endpoint. -/
def sbxS4AppendPaths {d : ℕ} (T : ℝ≥0) (γ η : Path d) : Path d :=
  ⟨fun t => γ (min t T) + η (t - T) - η 0,
    ((γ.continuous.comp (continuous_id.min continuous_const)).add
      (η.continuous.comp (continuous_id.sub continuous_const))).sub continuous_const⟩

/-- Recovery is preserved when the stopped successor is appended to a stopped
assembly of the entire preceding history. The assembly is supplied by the
finite-path consumer; the two nested maps require no measurability premise. -/
theorem sbxS4_segmentPrefixLaw_stopped_append_ae {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    [IsSFiniteKernel P] (z : Vec d) (ω : FieldPair d)
    [IsProbabilityMeasure (P (z, ω))] (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor0 : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ))
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K] (n : ℕ)
    (hgood : ∀ᵐ h ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n,
      IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) ∧
      ENNReal.ofReal δ • cond (volume : Measure (Vec d))
        (endpointBall i R (sbxS4HistoryEndpoint Δ n h)) ≤
        (Renewal.killedSegmentLaw Δ R i P (sbxS4HistoryEndpoint Δ n h) ω).map
          (fun γ : Path d => γ Δ) ∧
      K (sbxS4HistoryEndpoint Δ n h) =
        sbxS4FirstSegmentLaw Δ R δ i P (sbxS4HistoryEndpoint Δ n h) ω)
    (A : sbxS4SplitHistory (Path d) n → Path d) :
    ((sbxS4SegmentPrefixLaw Δ R δ i P z ω K (n + 1)).map
        (fun h => (Preorder.frestrictLe₂ (π := fun _ => Path d × Bool) n.le_succ h,
          Diffusion.stopPathAt Δ (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1))).map
        (fun q => (q.1, sbxS4AppendPaths (((n + 1 : ℕ) : ℝ≥0) * Δ)
          (Diffusion.stopPathAt (((n + 1 : ℕ) : ℝ≥0) * Δ) (A q.1)) q.2)) =
    (((sbxS4SegmentPrefixLaw Δ R δ i P z ω K n) ⊗ₘ
        P.comap (fun h => (sbxS4HistoryEndpoint Δ n h, ω))
          ((sbxS4_measurable_historyEndpoint Δ n).prodMk measurable_const)).map
        (fun q => (q.1, Diffusion.stopPathAt Δ q.2))).map
        (fun q => (q.1, sbxS4AppendPaths (((n + 1 : ℕ) : ℝ≥0) * Δ)
          (Diffusion.stopPathAt (((n + 1 : ℕ) : ℝ≥0) * Δ) (A q.1)) q.2)) := by
  exact congrArg (fun μ => μ.map (fun q => (q.1,
    sbxS4AppendPaths (((n + 1 : ℕ) : ℝ≥0) * Δ)
      (Diffusion.stopPathAt (((n + 1 : ℕ) : ℝ≥0) * Δ) (A q.1)) q.2)))
    (sbxS4_segmentPrefixLaw_stopped_last_ae Δ R δ i P z ω hR hδ₀ hδ₁ hminor0 K n hgood)

/-- The stopped appended path and its preceding history have the same law
when the next split coin is forgotten as when the original path law restarts
at the endpoint. The measurable assembly is provided by the finite-path consumer. -/
theorem sbxS4_segmentPrefixLaw_stopped_append_map_ae {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    [IsSFiniteKernel P] (z : Vec d) (ω : FieldPair d)
    [IsProbabilityMeasure (P (z, ω))] (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor0 : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ))
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K] (n : ℕ)
    (hgood : ∀ᵐ h ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n,
      IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) ∧
      ENNReal.ofReal δ • cond (volume : Measure (Vec d))
        (endpointBall i R (sbxS4HistoryEndpoint Δ n h)) ≤
        (Renewal.killedSegmentLaw Δ R i P (sbxS4HistoryEndpoint Δ n h) ω).map
          (fun γ : Path d => γ Δ) ∧
      K (sbxS4HistoryEndpoint Δ n h) =
        sbxS4FirstSegmentLaw Δ R δ i P (sbxS4HistoryEndpoint Δ n h) ω)
    (A : sbxS4SplitHistory (Path d) n → Path d) (hA : Measurable A) :
    (sbxS4SegmentPrefixLaw Δ R δ i P z ω K (n + 1)).map
      (fun h =>
        let p := Preorder.frestrictLe₂ (π := fun _ => Path d × Bool) n.le_succ h
        let T := (((n + 1 : ℕ) : ℝ≥0) * Δ)
        (p, Diffusion.stopPathAt (T + Δ) (sbxS4AppendPaths T
          (Diffusion.stopPathAt T (A p))
          (Diffusion.stopPathAt Δ (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1)))) =
    ((sbxS4SegmentPrefixLaw Δ R δ i P z ω K n) ⊗ₘ
      P.comap (fun h => (sbxS4HistoryEndpoint Δ n h, ω))
        ((sbxS4_measurable_historyEndpoint Δ n).prodMk measurable_const)).map
      (fun q =>
        let T := (((n + 1 : ℕ) : ℝ≥0) * Δ)
        (q.1, Diffusion.stopPathAt (T + Δ) (sbxS4AppendPaths T
          (Diffusion.stopPathAt T (A q.1)) (Diffusion.stopPathAt Δ q.2)))) := by
  let T : ℝ≥0 := (((n + 1 : ℕ) : ℝ≥0) * Δ)
  let F : sbxS4SplitHistory (Path d) n × Path d → sbxS4SplitHistory (Path d) n × Path d :=
    fun q => (q.1, Diffusion.stopPathAt (T + Δ)
      (sbxS4AppendPaths T (Diffusion.stopPathAt T (A q.1)) q.2))
  have hc : Continuous (fun q : Path d × Path d => sbxS4AppendPaths T q.1 q.2) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (((continuous_fst.fst).eval (continuous_snd.min continuous_const)).add
      ((continuous_fst.snd).eval (continuous_snd.sub continuous_const))).sub
        ((continuous_fst.snd).eval continuous_const)
  have hF : Measurable F := measurable_fst.prodMk
    ((Diffusion.continuous_stopPathAt (T + Δ)).measurable.comp
      (hc.measurable.comp (((Diffusion.continuous_stopPathAt T).measurable.comp
        (hA.comp measurable_fst)).prodMk measurable_snd)))
  have hp : Measurable (fun h : sbxS4SplitHistory (Path d) (n + 1) =>
      (Preorder.frestrictLe₂ (π := fun _ => Path d × Bool) n.le_succ h,
        Diffusion.stopPathAt Δ (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1)) :=
    (Preorder.measurable_frestrictLe₂ (X := fun _ => Path d × Bool) n.le_succ).prodMk
      ((Diffusion.continuous_stopPathAt Δ).measurable.comp
        (measurable_fst.comp (measurable_pi_apply _)))
  have hq : Measurable (fun q : sbxS4SplitHistory (Path d) n × Path d =>
      (q.1, Diffusion.stopPathAt Δ q.2)) :=
    measurable_fst.prodMk ((Diffusion.continuous_stopPathAt Δ).measurable.comp measurable_snd)
  have he := congrArg (fun μ => μ.map F)
    (sbxS4_segmentPrefixLaw_stopped_last_ae Δ R δ i P z ω hR hδ₀ hδ₁ hminor0 K n hgood)
  rw [Measure.map_map hF hp, Measure.map_map hF hq] at he
  exact he

/-- A good endpoint set is preserved by every finite actual split prefix if
it holds for the first segment and is preserved by each endpoint restart. -/
theorem sbxS4_segmentPrefixLaw_endpoint_mem_ae {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor0 : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ))
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K]
    (G : Set (Vec d)) (hG : MeasurableSet G)
    (hfirst : ∀ᵐ q ∂sbxS4FirstSegmentLaw Δ R δ i P z ω, q.1 Δ ∈ G)
    (hstep : ∀ x ∈ G, ∀ᵐ q ∂K x, q.1 Δ ∈ G) (n : ℕ) :
    ∀ᵐ h ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n,
      sbxS4HistoryEndpoint Δ n h ∈ G := by
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ hminor0).1
  induction n with
  | zero =>
    change ∀ᵐ h ∂sbxS4SplitPrefixLaw (sbxS4EndpointHistoryKernel Δ K)
      (sbxS4FirstSegmentLaw Δ R δ i P z ω) 0, sbxS4HistoryEndpoint Δ 0 h ∈ G
    rw [sbxS4_splitPrefixLaw_zero]
    apply (ae_map_iff sbxS4_measurable_initialHistory.aemeasurable
      ((sbxS4_measurable_historyEndpoint Δ 0) hG)).mpr
    simpa only [sbxS4HistoryEndpoint, sbxS4InitialHistory] using hfirst
  | succ n ih =>
    change ∀ᵐ h ∂sbxS4SplitPrefixLaw (sbxS4EndpointHistoryKernel Δ K)
      (sbxS4FirstSegmentLaw Δ R δ i P z ω) (n + 1),
        sbxS4HistoryEndpoint Δ (n + 1) h ∈ G
    rw [sbxS4_splitPrefixLaw_succ]
    apply (ae_map_iff (sbxS4_measurable_appendHistory n).aemeasurable
      ((sbxS4_measurable_historyEndpoint Δ (n + 1)) hG)).mpr
    apply Measure.ae_compProd_of_ae_ae
      (((sbxS4_measurable_historyEndpoint Δ (n + 1)).comp
        (sbxS4_measurable_appendHistory n)) hG)
    filter_upwards [ih] with h hh
    change ∀ᵐ q ∂K (sbxS4HistoryEndpoint Δ n h),
      sbxS4HistoryEndpoint Δ (n + 1) (sbxS4AppendHistory n (h, q)) ∈ G
    filter_upwards [hstep _ hh] with q hq
    simpa only [sbxS4HistoryEndpoint, sbxS4_appendHistory_last] using hq

/-- A good endpoint set supplies exactly the fibre conditions needed for
stopped-append recovery, provided the actual prefix reaches it almost surely. -/
theorem sbxS4_segmentPrefixLaw_good_endpoints_ae {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) (K : Kernel (Vec d) (Path d × Bool)) (n : ℕ)
    (G : Set (Vec d))
    (hmem : ∀ᵐ h ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n,
      sbxS4HistoryEndpoint Δ n h ∈ G)
    (hP : ∀ x ∈ G, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ x ∈ G, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
      (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hK : ∀ x ∈ G, K x = sbxS4FirstSegmentLaw Δ R δ i P x ω) :
    ∀ᵐ h ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n,
      IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) ∧
      ENNReal.ofReal δ • cond (volume : Measure (Vec d))
        (endpointBall i R (sbxS4HistoryEndpoint Δ n h)) ≤
        (Renewal.killedSegmentLaw Δ R i P (sbxS4HistoryEndpoint Δ n h) ω).map
          (fun γ : Path d => γ Δ) ∧
      K (sbxS4HistoryEndpoint Δ n h) =
        sbxS4FirstSegmentLaw Δ R δ i P (sbxS4HistoryEndpoint Δ n h) ω := by
  filter_upwards [hmem] with h hh
  exact ⟨hP _ hh, hminor _ hh, hK _ hh⟩

/-- Original path-law endpoint preservation transfers through the split coin
and hence to every finite segment prefix. -/
theorem sbxS4_segmentPrefixLaw_endpoint_mem_of_original_ae {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (z, ω))]
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor0 : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R z) ≤
      (Renewal.killedSegmentLaw Δ R i P z ω).map (fun γ : Path d => γ Δ))
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K]
    (G : Set (Vec d)) (hG : MeasurableSet G)
    (hP : ∀ x ∈ G, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ x ∈ G, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
      (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hK : ∀ x ∈ G, K x = sbxS4FirstSegmentLaw Δ R δ i P x ω)
    (hfirst : ∀ᵐ γ ∂P (z, ω), γ Δ ∈ G)
    (hstep : ∀ x ∈ G, ∀ᵐ γ ∂P (x, ω), γ Δ ∈ G) (n : ℕ) :
    ∀ᵐ h ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n,
      sbxS4HistoryEndpoint Δ n h ∈ G := by
  have transfer (x : Vec d) [IsProbabilityMeasure (P (x, ω))]
      (hm : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
      (ha : ∀ᵐ γ ∂P (x, ω), γ Δ ∈ G) :
      ∀ᵐ q ∂sbxS4FirstSegmentLaw Δ R δ i P x ω, q.1 Δ ∈ G := by
    rw [← (sbxS4_firstSegmentLaw_spec Δ R δ i P x ω hR hδ₀ hδ₁ hm).2.1] at ha
    exact (ae_map_iff measurable_fst.aemeasurable
      ((continuous_eval_const Δ).measurable hG)).mp ha
  apply sbxS4_segmentPrefixLaw_endpoint_mem_ae Δ R δ i P z ω hR hδ₀ hδ₁
    hminor0 K G hG (transfer z hminor0 hfirst) ?_ n
  intro x hx
  let : IsProbabilityMeasure (P (x, ω)) := hP x hx
  rw [hK x hx]
  exact transfer x (hminor x hx) (hstep x hx)

/-- Exact finite Bernoulli factors for endpoint-restarted actual split segments.
The kernel fibre identity is supplied by the measurable-kernel construction. -/
theorem sbxS4_segmentPrefixLaw_coin_cylinder {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) (hP : ∀ x, IsProbabilityMeasure (P (x, ω)))
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
      (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K]
    (hK : ∀ x, K x = sbxS4FirstSegmentLaw Δ R δ i P x ω)
    (b : ℕ → Bool) (n : ℕ) :
    sbxS4SegmentPrefixLaw Δ R δ i P z ω K n (sbxS4CoinPrefixEvent b n) =
      ∏ j ∈ Finset.range (n + 1),
        (if b j then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ)) := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  refine sbxS4_splitPrefixLaw_coin_cylinder _ _ δ
    (sbxS4_firstSegmentLaw_coin_mass Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)) ?_ b n
  intro k h c
  change K (sbxS4HistoryEndpoint Δ k h) _ = _
  rw [hK]
  let : IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ k h, ω)) := hP _
  exact sbxS4_firstSegmentLaw_coin_mass Δ R δ i P _ ω hR hδ₀ hδ₁ (hminor _) c

/-- The bounded finite-history branch test uses the genuine killed bridge on
success and the normalized subtraction residual on failure, at the last endpoint. -/
theorem sbxS4_segmentPrefixLaw_integral_branch {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) (hP : ∀ x, IsProbabilityMeasure (P (x, ω)))
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
      (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K]
    (hK : ∀ x, K x = sbxS4FirstSegmentLaw Δ R δ i P x ω)
    (n : ℕ) (F : sbxS4SplitHistory (Path d) n × Path d → ℝ)
    (hF : Measurable F) (hb : ∃ C : ℝ, ∀ q, ‖F q‖ ≤ C) (b : Bool) :
    (∫ q, {q : sbxS4SplitHistory (Path d) n × (Path d × Bool) | q.2.2 = b}.indicator
      (fun q => F (q.1, q.2.1)) q
        ∂(sbxS4SegmentPrefixLaw Δ R δ i P z ω K n ⊗ₘ sbxS4EndpointHistoryKernel Δ K n)) =
      ∫ h, if b then δ * (∫ γ, F (h, γ)
          ∂Renewal.killedBridgeMixture Δ R i P (sbxS4HistoryEndpoint Δ n h) ω)
        else (1 - δ) * (∫ γ, F (h, γ)
          ∂sbxS4FailedSegmentLaw Δ R δ i P (sbxS4HistoryEndpoint Δ n h) ω)
        ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  apply sbxS4_splitPrefixLaw_integral_branch _ _ n δ hδ₀.le hδ₁
    (fun h => P (sbxS4HistoryEndpoint Δ n h, ω))
    (fun h => Renewal.killedBridgeMixture Δ R i P (sbxS4HistoryEndpoint Δ n h) ω)
    (fun h => hP _) ?_ ?_ ?_ F hF hb b
  · intro h
    let : IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) := hP _
    let : IsProbabilityMeasure
        (Renewal.killedBridgeMixture Δ R i P (sbxS4HistoryEndpoint Δ n h) ω) :=
      sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P _ ω hR hδ₀ (hminor _)
    infer_instance
  · intro h
    let : IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) := hP _
    exact sbxS4_smul_killedBridgeMixture_le Δ R δ i P _ ω hR (hminor _)
  · intro h
    exact hK _


/-! Countable extensions of the checked finite-prefix laws. The extension is
supplied by the sequence construction; only its actual finite marginals are
used. The first retained prefix includes coin zero; its fresh tail starts at
`n + 1`, so it contains no coin already present in that history. -/

/-- The common one-coordinate Bernoulli measure. -/
def sbxS4BernoulliLaw (δ : ℝ) : Measure Bool :=
  ENNReal.ofReal δ • Measure.dirac true +
    ENNReal.ofReal (1 - δ) • Measure.dirac false

/-- Both Bernoulli masses, with the original first-coin convention. -/
theorem sbxS4_bernoulliLaw_singleton (δ : ℝ) (b : Bool) :
    sbxS4BernoulliLaw δ {b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ) := by
  cases b <;> simp [sbxS4BernoulliLaw]

/-- The common coin law is normalized in the full closed parameter range. -/
theorem sbxS4_bernoulliLaw_isProbabilityMeasure (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) : IsProbabilityMeasure (sbxS4BernoulliLaw δ) := by
  constructor
  simp only [sbxS4BernoulliLaw, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hδ₀ (sub_nonneg.mpr hδ₁), add_sub_cancel,
    ENNReal.ofReal_one]

/-- All future coins strictly after the retained prefix. -/
def sbxS4FutureCoins {α : Type*} (n : ℕ) (s : ℕ → α × Bool) : BernoulliSequence :=
  fun k => (s (n + k + 1)).2

/-- The whole shifted tail is measurable, not just each finite cylinder. -/
theorem sbxS4_measurable_futureCoins {α : Type*} [MeasurableSpace α] (n : ℕ) :
    Measurable (sbxS4FutureCoins (α := α) n) :=
  measurable_pi_iff.mpr fun k => (measurable_pi_apply (n + k + 1)).snd

section CountableExtension
variable {α : Type*} [MeasurableSpace α]
  (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
  [hκ : ∀ n, IsMarkovKernel (κ n)]
  (μ : Measure (α × Bool)) [hμprob : IsProbabilityMeasure μ] (δ : ℝ)
  (hcoin : ∀ n h (b : Bool), κ n h {q | q.2 = b} =
    if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ))

include hcoin

omit hκ in
/-- Exact coin masses identify the whole next-coin kernel, including all events. -/
theorem sbxS4_historyKernel_map_coin (n : ℕ) :
    (κ n).map Prod.snd = Kernel.const _ (sbxS4BernoulliLaw δ) := by
  ext h : 1
  rw [Kernel.map_apply _ measurable_snd, Kernel.const_apply]
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply measurable_snd (measurableSet_singleton b),
    sbxS4_bernoulliLaw_singleton]
  exact hcoin n h b

/-- The retained history and the very next coin have their exact product law. -/
theorem sbxS4_splitPrefixLaw_prefix_nextCoin (n : ℕ) :
    (sbxS4SplitPrefixLaw κ μ (n + 1)).map
      (fun h => (Preorder.frestrictLe₂ (π := fun _ => α × Bool) n.le_succ h,
        (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2)) =
      (sbxS4SplitPrefixLaw κ μ n).prod (sbxS4BernoulliLaw δ) := by
  let : IsProbabilityMeasure (sbxS4SplitPrefixLaw κ μ n) :=
    sbxS4_splitPrefixLaw_isProbabilityMeasure κ μ n
  have hm : Measurable (fun h : sbxS4SplitHistory α (n + 1) =>
      (Preorder.frestrictLe₂ (π := fun _ => α × Bool) n.le_succ h,
        (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2)) :=
    (Preorder.measurable_frestrictLe₂ (X := fun _ => α × Bool) n.le_succ).prodMk
      (measurable_pi_apply (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1))).snd
  rw [sbxS4_splitPrefixLaw_succ, Measure.map_map hm
    (sbxS4_measurable_appendHistory n)]
  have he : (fun h : sbxS4SplitHistory α (n + 1) =>
      (Preorder.frestrictLe₂ (π := fun _ => α × Bool) n.le_succ h,
        (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2)) ∘ sbxS4AppendHistory n =
      Prod.map id Prod.snd := by
    funext q
    change (_, _) = (q.1, q.2.2)
    exact congrArg₂ Prod.mk (sbxS4_appendHistory_restrict n q)
      (congrArg Prod.snd (sbxS4_appendHistory_last n q))
  rw [he, ← Measure.compProd_map measurable_snd,
    sbxS4_historyKernel_map_coin κ δ hcoin, Measure.compProd_const]

variable (ν : Measure (ℕ → α × Bool))
  (hν : ∀ n, ν.map (Preorder.frestrictLe n) = sbxS4SplitPrefixLaw κ μ n)

omit hcoin
include hν

/-- A countable extension of the actual normalized prefixes is itself normalized. -/
theorem sbxS4_extension_isProbabilityMeasure : IsProbabilityMeasure ν := by
  let : IsProbabilityMeasure (sbxS4SplitPrefixLaw κ μ 0) :=
    sbxS4_splitPrefixLaw_isProbabilityMeasure κ μ 0
  have : IsProbabilityMeasure (ν.map (Preorder.frestrictLe 0)) := (hν 0).symm ▸ inferInstance
  exact Measure.isProbabilityMeasure_of_map
    (Preorder.measurable_frestrictLe 0).aemeasurable

include hcoin

/-- The supplied extension retains exactly the finite history/next-coin law. -/
theorem sbxS4_extension_prefix_nextCoin (n : ℕ) :
    ν.map (fun s => (Preorder.frestrictLe n s, (s (n + 1)).2)) =
      (sbxS4SplitPrefixLaw κ μ n).prod (sbxS4BernoulliLaw δ) := by
  calc
    _ = (ν.map (Preorder.frestrictLe (n + 1))).map
        (fun h => (Preorder.frestrictLe₂ (π := fun _ => α × Bool) n.le_succ h,
          (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2)) := by
      rw [Measure.map_map
        ((Preorder.measurable_frestrictLe₂ (X := fun _ => α × Bool) n.le_succ).prodMk
      (measurable_pi_apply (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1))).snd)
        (Preorder.measurable_frestrictLe (n + 1))]
      rfl
    _ = _ := by
      rw [hν, sbxS4_splitPrefixLaw_prefix_nextCoin κ μ δ hcoin]

/-- The extension's next-coin marginal has no dependence on the past state. -/
theorem sbxS4_extension_map_nextCoin (n : ℕ) :
    ν.map (fun s => (s (n + 1)).2) = sbxS4BernoulliLaw δ := by
  let : IsProbabilityMeasure (sbxS4SplitPrefixLaw κ μ n) :=
    sbxS4_splitPrefixLaw_isProbabilityMeasure κ μ n
  have he := congrArg (fun η => η.map Prod.snd)
    (sbxS4_extension_prefix_nextCoin κ μ δ hcoin ν hν n)
  rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod,
    measure_univ, one_smul] at he
  exact he

/-- All earlier path and coin coordinates are independent of the next coin. -/
theorem sbxS4_extension_indep_prefix_nextCoin (n : ℕ) :
    IndepFun (Preorder.frestrictLe n) (fun s => (s (n + 1)).2) ν := by
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure κ μ ν hν
  rw [indepFun_iff_map_prod_eq_prod_map_map
    (Preorder.measurable_frestrictLe n).aemeasurable
    (measurable_pi_apply (n + 1)).snd.aemeasurable, hν,
    sbxS4_extension_map_nextCoin κ μ δ hcoin ν hν]
  exact sbxS4_extension_prefix_nextCoin κ μ δ hcoin ν hν n

/-- Any finite set of future coins factors against every measurable event in
the entire retained segment/coin history. The finite set may have gaps. -/
theorem sbxS4_extension_future_coin_cylinder (n : ℕ)
    (H : Set (sbxS4SplitHistory α n)) (hH : MeasurableSet H)
    (S : Finset ℕ) (sets : ℕ → Set Bool) (hsets : ∀ k, MeasurableSet (sets k)) :
    ν ((Preorder.frestrictLe (π := fun _ : ℕ => α × Bool) n) ⁻¹' H ∩
      ⋂ k ∈ S, (fun s => (s (n + k + 1)).2) ⁻¹' sets k) =
      sbxS4SplitPrefixLaw κ μ n H * ∏ k ∈ S, sbxS4BernoulliLaw δ (sets k) := by
  classical
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure κ μ ν hν
  refine Finset.induction_on_max S ?_ ?_
  · simpa using (Measure.map_apply (Preorder.measurable_frestrictLe n) hH).symm.trans
      (congrArg (fun η => η H) (hν n))
  · intro k S hmax ih
    have hk : k ∉ S := fun hk => (lt_irrefl k) (hmax k hk)
    let A : Set (sbxS4SplitHistory α (n + k)) :=
      (Preorder.frestrictLe₂ (π := fun _ => α × Bool) (Nat.le_add_right n k)) ⁻¹' H ∩
        ⋂ j : S, {h | (h ⟨n + j + 1,
          Finset.mem_Iic.mpr (by have hj := hmax j j.2; omega)⟩).2 ∈ sets j}
    have hA : MeasurableSet A :=
      (hH.preimage (Preorder.measurable_frestrictLe₂ _)).inter
        (MeasurableSet.iInter fun j => (hsets j).preimage (by fun_prop))
    have hpre : (Preorder.frestrictLe (n + k)) ⁻¹' A =
        (Preorder.frestrictLe (π := fun _ : ℕ => α × Bool) n) ⁻¹' H ∩
          ⋂ j ∈ S, (fun s => (s (n + j + 1)).2) ⁻¹' sets j := by
      ext s
      have hr : Preorder.frestrictLe₂ (π := fun _ : ℕ => α × Bool)
          (Nat.le_add_right n k) (Preorder.frestrictLe (n + k) s) =
          Preorder.frestrictLe n s :=
        congrFun (Preorder.frestrictLe₂_comp_frestrictLe (Nat.le_add_right n k)) s
      simp only [A, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_ofPred_eq]
      rw [hr]
      simp
    have hind := (sbxS4_extension_indep_prefix_nextCoin κ μ δ hcoin ν hν (n + k)).measure_inter_preimage_eq_mul A (sets k) hA (hsets k)
    rw [hpre, ih, ← Measure.map_apply (by fun_prop) (hsets k),
      sbxS4_extension_map_nextCoin κ μ δ hcoin ν hν] at hind
    simpa only [Finset.set_biInter_insert, Finset.prod_insert hk,
      Set.inter_comm, Set.inter_left_comm, Set.inter_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hind

/-- A restricted history event has its scalar mass times the full infinite
Bernoulli tail measure. Square-cylinder uniqueness supplies all tail events. -/
theorem sbxS4_extension_restrict_map_futureCoins (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (H : Set (sbxS4SplitHistory α n)) (hH : MeasurableSet H) :
    (ν.restrict ((Preorder.frestrictLe (π := fun _ : ℕ => α × Bool) n) ⁻¹' H)).map (sbxS4FutureCoins n) =
      sbxS4SplitPrefixLaw κ μ n H • sbxS4RemainingBitsLaw δ := by
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure κ μ ν hν
  let : IsProbabilityMeasure (sbxS4RemainingBitsLaw δ) :=
    sbxS4_remainingBitsLaw_isProbabilityMeasure δ hδ₀ hδ₁
  let : IsProbabilityMeasure (sbxS4BernoulliLaw δ) :=
    sbxS4_bernoulliLaw_isProbabilityMeasure δ hδ₀ hδ₁
  refine ext_of_generate_finite
    (squareCylinders fun _ : ℕ => {s : Set Bool | MeasurableSet s})
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet) (fun _ => by change MeasurableSet (Set.univ : Set Bool); exact .univ))
    ?_ ?_
  · rintro _ ⟨S, sets, hsets, rfl⟩
    have hm : ∀ k, MeasurableSet (sets k) := fun k => hsets k (Set.mem_univ k)
    have hbox : MeasurableSet (Set.pi (S : Set ℕ) sets) :=
      MeasurableSet.pi S.countable_toSet (fun k _ => hm k)
    have hpi : sbxS4RemainingBitsLaw δ (Set.pi (S : Set ℕ) sets) =
        ∏ k ∈ S, sbxS4BernoulliLaw δ (sets k) := by
      exact Measure.infinitePi_pi (fun _ : ℕ => sbxS4BernoulliLaw δ) (fun k _ => hm k)
    rw [Measure.map_apply (sbxS4_measurable_futureCoins n) hbox,
      Measure.restrict_apply ((sbxS4_measurable_futureCoins n) hbox),
      Measure.smul_apply, hpi]
    have he : (sbxS4FutureCoins (α := α) n) ⁻¹' Set.pi (S : Set ℕ) sets =
        ⋂ k ∈ S, (fun s => (s (n + k + 1)).2) ⁻¹' sets k := by
      ext s
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_iInter,
        sbxS4FutureCoins]
    rw [he, Set.inter_comm]
    exact sbxS4_extension_future_coin_cylinder κ μ δ hcoin ν hν n H hH S sets hm
  · rw [Measure.map_apply (sbxS4_measurable_futureCoins n) MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply_univ, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one,
      ← Measure.map_apply (Preorder.measurable_frestrictLe n) hH, hν]

/-- The whole future tail, at every deterministic prefix, has the genuine
Bernoulli product law. -/
theorem sbxS4_extension_map_futureCoins (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (n : ℕ) :
    ν.map (sbxS4FutureCoins n) = sbxS4RemainingBitsLaw δ := by
  let : IsProbabilityMeasure (sbxS4SplitPrefixLaw κ μ n) :=
    sbxS4_splitPrefixLaw_isProbabilityMeasure κ μ n
  simpa only [Set.preimage_univ, Measure.restrict_univ, measure_univ, one_smul] using
    sbxS4_extension_restrict_map_futureCoins κ μ δ hcoin ν hν hδ₀ hδ₁ n
      Set.univ MeasurableSet.univ

/-- The joint law of the full retained history and the entire shifted coin
sequence is a product, with no independence assumption on the extension. -/
theorem sbxS4_extension_prefix_futureCoins (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (n : ℕ) :
    ν.map (fun s => (Preorder.frestrictLe n s, sbxS4FutureCoins n s)) =
      (sbxS4SplitPrefixLaw κ μ n).prod (sbxS4RemainingBitsLaw δ) := by
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure κ μ ν hν
  let : IsProbabilityMeasure (sbxS4RemainingBitsLaw δ) :=
    sbxS4_remainingBitsLaw_isProbabilityMeasure δ hδ₀ hδ₁
  apply Measure.ext_prod
  intro H T hH hT
  rw [Measure.map_apply
    ((Preorder.measurable_frestrictLe n).prodMk (sbxS4_measurable_futureCoins n))
    (hH.prod hT), Measure.prod_prod]
  have he := congrArg (fun η => η T)
    (sbxS4_extension_restrict_map_futureCoins κ μ δ hcoin ν hν hδ₀ hδ₁ n H hH)
  rw [Measure.map_apply (sbxS4_measurable_futureCoins n) hT,
    Measure.restrict_apply ((sbxS4_measurable_futureCoins n) hT),
    Measure.smul_apply, smul_eq_mul] at he
  simpa only [Set.mk_preimage_prod, Set.inter_comm] using he

/-- Full-tail independence from every path and bit coordinate in the retained past. -/
theorem sbxS4_extension_indep_prefix_futureCoins (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) : IndepFun (Preorder.frestrictLe n) (sbxS4FutureCoins n) ν := by
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure κ μ ν hν
  rw [indepFun_iff_map_prod_eq_prod_map_map
    (Preorder.measurable_frestrictLe n).aemeasurable
    (sbxS4_measurable_futureCoins n).aemeasurable, hν,
    sbxS4_extension_map_futureCoins κ μ δ hcoin ν hν hδ₀ hδ₁]
  exact sbxS4_extension_prefix_futureCoins κ μ δ hcoin ν hν hδ₀ hδ₁ n

/-- Bounded tests of the complete infinite tail factor against arbitrary
bounded measurable observations of the actual retained finite history. -/
theorem sbxS4_extension_integral_futureCoins (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (H : sbxS4SplitHistory α n → ℝ) (hH : Measurable H)
    (hbH : ∃ C : ℝ, ∀ h, ‖H h‖ ≤ C)
    (F : BernoulliSequence → ℝ) (hF : Measurable F)
    (hbF : ∃ C : ℝ, ∀ β, ‖F β‖ ≤ C) :
    Integrable (fun s => H (Preorder.frestrictLe n s) * F (sbxS4FutureCoins n s)) ν ∧
      (∫ s, H (Preorder.frestrictLe n s) * F (sbxS4FutureCoins n s) ∂ν) =
        (∫ h, H h ∂sbxS4SplitPrefixLaw κ μ n) * (∫ β, F β ∂sbxS4RemainingBitsLaw δ) := by
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure κ μ ν hν
  have hHm := hH.comp (Preorder.measurable_frestrictLe (X := fun _ : ℕ => α × Bool) n)
  have hFm := hF.comp (sbxS4_measurable_futureCoins (α := α) n)
  obtain ⟨C, hC⟩ := hbH
  obtain ⟨D, hD⟩ := hbF
  have hi : Integrable (fun s => H (Preorder.frestrictLe n s) *
      F (sbxS4FutureCoins n s)) ν := by
    refine Integrable.of_bound (hHm.mul hFm).aestronglyMeasurable
      (max C 0 * max D 0) (Filter.Eventually.of_forall fun s => ?_)
    rw [norm_mul]
    exact mul_le_mul ((hC _).trans (le_max_left _ _))
      ((hD _).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  refine ⟨hi, ?_⟩
  have hind := (sbxS4_extension_indep_prefix_futureCoins κ μ δ hcoin ν hν hδ₀ hδ₁ n).comp hH hF
  have he := hind.integral_fun_mul_eq_mul_integral hHm.aestronglyMeasurable
    hFm.aestronglyMeasurable
  simp only [Function.comp_apply] at he
  rw [he]
  have hHI : (∫ s, H (Preorder.frestrictLe n s) ∂ν) =
      ∫ h, H h ∂sbxS4SplitPrefixLaw κ μ n := by
    rw [← hν n, integral_map (Preorder.measurable_frestrictLe n).aemeasurable
      hH.aestronglyMeasurable]
  have hFI : (∫ s, F (sbxS4FutureCoins n s) ∂ν) =
      ∫ β, F β ∂sbxS4RemainingBitsLaw δ := by
    rw [← sbxS4_extension_map_futureCoins κ μ δ hcoin ν hν hδ₀ hδ₁ n,
      integral_map (sbxS4_measurable_futureCoins n).aemeasurable hF.aestronglyMeasurable]
  rw [hHI, hFI]

omit hcoin

omit hκ hμprob in
/-- Coordinate zero of the extension is the actual initial split coin. -/
theorem sbxS4_extension_map_zeroCoin
    (hμ : ∀ b : Bool, μ {q | q.2 = b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ)) :
    ν.map (fun s => (s 0).2) = sbxS4BernoulliLaw δ := by
  calc
    _ = (ν.map (Preorder.frestrictLe 0)).map
        (fun h : sbxS4SplitHistory α 0 => (h ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2) := by
      rw [Measure.map_map (measurable_pi_apply (X := fun _ : Finset.Iic 0 => α × Bool)
        (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic 0)).snd
        (Preorder.measurable_frestrictLe 0)]
      rfl
    _ = μ.map Prod.snd := by
      rw [hν, sbxS4_splitPrefixLaw_zero, Measure.map_map (measurable_pi_apply (X := fun _ : Finset.Iic 0 => α × Bool)
        (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic 0)).snd
        sbxS4_measurable_initialHistory]
      rfl
    _ = _ := by
      apply Measure.ext_of_singleton
      intro b
      rw [Measure.map_apply measurable_snd (measurableSet_singleton b),
        sbxS4_bernoulliLaw_singleton]
      exact hμ b

include hcoin

/-- Every coin of the supplied extension has its actual Bernoulli marginal,
including the first coin; no tail reindexing discards that first step. -/
theorem sbxS4_extension_map_coin
    (hμ : ∀ b : Bool, μ {q | q.2 = b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ)) (n : ℕ) :
    ν.map (fun s => (s n).2) = sbxS4BernoulliLaw δ := by
  cases n with
  | zero => exact sbxS4_extension_map_zeroCoin κ μ δ ν hν hμ
  | succ n => exact sbxS4_extension_map_nextCoin κ μ δ hcoin ν hν n

/-- Arbitrary finite coin cylinders, including those that use coordinate zero,
have the exact Bernoulli factors. -/
theorem sbxS4_extension_coin_cylinder
    (hμ : ∀ b : Bool, μ {q | q.2 = b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ))
    (S : Finset ℕ) (sets : ℕ → Set Bool) (hsets : ∀ n, MeasurableSet (sets n)) :
    ν (⋂ k ∈ S, (fun s => (s k).2) ⁻¹' sets k) =
      ∏ k ∈ S, sbxS4BernoulliLaw δ (sets k) := by
  classical
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure κ μ ν hν
  have hm (n : ℕ) : ν ((fun s => (s n).2) ⁻¹' sets n) =
      sbxS4BernoulliLaw δ (sets n) := by
    rw [← Measure.map_apply (measurable_pi_apply n).snd (hsets n),
      sbxS4_extension_map_coin κ μ δ hcoin ν hν hμ]
  refine Finset.induction_on_max S (by simp) ?_
  intro k S hmax ih
  have hk : k ∉ S := fun hk => (lt_irrefl k) (hmax k hk)
  rw [Finset.prod_insert hk]
  cases k with
  | zero =>
    have hS : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun j hj => Nat.not_lt_zero j (hmax j hj))
    simpa [hS] using hm 0
  | succ n =>
    let A : Set (sbxS4SplitHistory α n) :=
      ⋂ j : S, {h | (h ⟨j, Finset.mem_Iic.mpr
        (Nat.le_of_lt_succ (hmax j j.2))⟩).2 ∈ sets j}
    have hA : MeasurableSet A :=
      MeasurableSet.iInter fun j => (hsets j).preimage (measurable_pi_apply _).snd
    have hpre : (Preorder.frestrictLe (π := fun _ : ℕ => α × Bool) n) ⁻¹' A =
        ⋂ j ∈ S, (fun s => (s j).2) ⁻¹' sets j := by
      ext s
      simp [A]
    have hind := (sbxS4_extension_indep_prefix_nextCoin κ μ δ hcoin ν hν n).measure_inter_preimage_eq_mul A (sets (n + 1)) hA (hsets (n + 1))
    rw [hpre, hm, ih] at hind
    simpa only [Finset.set_biInter_insert, Set.inter_comm, mul_comm] using hind

/-- The entire actual coin sequence, starting with the first split coin, has
the Bernoulli product law. -/
theorem sbxS4_extension_map_coins (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hμ : ∀ b : Bool, μ {q | q.2 = b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ)) :
    ν.map (fun s n => (s n).2) = sbxS4RemainingBitsLaw δ := by
  let : IsProbabilityMeasure (sbxS4BernoulliLaw δ) :=
    sbxS4_bernoulliLaw_isProbabilityMeasure δ hδ₀ hδ₁
  change ν.map (fun s n => (s n).2) = Measure.infinitePi (fun _ => sbxS4BernoulliLaw δ)
  apply Measure.eq_infinitePi
  intro S sets hsets
  rw [Measure.map_apply (by fun_prop)
    (MeasurableSet.pi S.countable_toSet (fun n _ => hsets n))]
  have he : (fun s : ℕ → α × Bool => fun n => (s n).2) ⁻¹'
      Set.pi (S : Set ℕ) sets = ⋂ k ∈ S, (fun s => (s k).2) ⁻¹' sets k := by
    ext s
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_iInter]
  rw [he]
  exact sbxS4_extension_coin_cylinder κ μ δ hcoin ν hν hμ S sets hsets

/-- The normalized split-coin marginal has exactly the real mean used in
`FreshBitsAt`; this includes the initial coin. -/
theorem sbxS4_extension_integral_coin (hδ₀ : 0 ≤ δ)
    (hμ : ∀ b : Bool, μ {q | q.2 = b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ)) (n : ℕ) :
    (∫ s, (if (s n).2 = true then (1 : ℝ) else 0) ∂ν) = δ := by
  have he : (fun s : ℕ → α × Bool => if (s n).2 = true then (1 : ℝ) else 0) =
      {s | (s n).2 = true}.indicator (1 : (ℕ → α × Bool) → ℝ) := by
    funext s
    simp [Set.indicator]
  have hm : MeasurableSet {s : ℕ → α × Bool | (s n).2 = true} :=
    (measurable_pi_apply n).snd (measurableSet_singleton true)
  rw [he, integral_indicator_one hm]
  change (ν {s | (s n).2 = true}).toReal = δ
  have hmass : ν {s | (s n).2 = true} = ENNReal.ofReal δ := by
    calc
      _ = (ν.map (fun s => (s n).2)) {true} :=
        (Measure.map_apply (measurable_pi_apply n).snd (measurableSet_singleton true)).symm
      _ = _ := by
        rw [sbxS4_extension_map_coin κ μ δ hcoin ν hν hμ,
          sbxS4_bernoulliLaw_singleton]
        rfl
  rw [hmass, ENNReal.toReal_ofReal hδ₀]

/-- A supplied measurable realization with the actual bits and stopped histories
inherits the literal deterministic-history fresh-bit identity. The initial
stopped history is treated separately from all positive grid times. -/
theorem sbxS4_extension_freshBitsAt {d : ℕ} (Δ : ℝ≥0) (hδ₀ : 0 ≤ δ)
    (hμ : ∀ b : Bool, μ {q | q.2 = b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ))
    (L : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    (g : (ℕ → α × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L xω)
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory α n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s)) : FreshBitsAt Δ δ L xω := by
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure κ μ ν hν
  have hgood : ∀ᵐ s ∂ν,
      Probability.stoppedHistorySample Δ 0 (g s) = z₀ ∧
      (∀ n, (g s).2 n = (s n).2) ∧
      ∀ n, Probability.stoppedHistorySample Δ (n + 1) (g s) =
        past n (Preorder.frestrictLe n s) :=
    hzero.and ((ae_all_iff.mpr hbits).and (ae_all_iff.mpr hstop))
  intro n H hH _hbH
  have hHm : Measurable H := hH.mono (Probability.finiteHistorySigma_le Δ n) le_rfl
  have hind : IndepFun (fun s => H (g s)) (fun s => (s n).2) ν := by
    cases n with
    | zero =>
      refine (indepFun_const_left (H z₀) (fun s : ℕ → α × Bool => (s 0).2)).congr
        ?_ Filter.EventuallyEq.rfl
      filter_upwards [hgood] with s hs
      rw [← hs.1, Probability.finiteHistory_test_stopped Δ 0 H hH]
    | succ n =>
      have hi := (sbxS4_extension_indep_prefix_nextCoin κ μ δ hcoin ν hν n).comp (hHm.comp (hpast n)) measurable_id
      refine hi.congr ?_ Filter.EventuallyEq.rfl
      filter_upwards [hgood] with s hs
      change H (past n (Preorder.frestrictLe n s)) = H (g s)
      rw [← hs.2.2 n, Probability.finiteHistory_test_stopped Δ (n + 1) H hH]
  have hcm : Measurable (fun b : Bool => if b = true then (1 : ℝ) else 0) :=
    measurable_of_finite _
  have hprod : Measurable (fun z : CoupledSample d =>
      H z * (if z.2 n = true then (1 : ℝ) else 0)) :=
    hHm.mul (hcm.comp ((measurable_pi_apply n).comp measurable_snd))
  rw [← hmap, integral_map hg.aemeasurable hprod.aestronglyMeasurable,
    integral_map hg.aemeasurable hHm.aestronglyMeasurable]
  have he : (fun s => H (g s) * (if (g s).2 n = true then (1 : ℝ) else 0)) =ᵐ[ν]
      (fun s => H (g s) * (if (s n).2 = true then (1 : ℝ) else 0)) := by
    filter_upwards [hgood] with s hs
    rw [hs.2.1 n]
  rw [integral_congr_ae he]
  calc
    _ = (∫ s, H (g s) ∂ν) *
        (∫ s, (if (s n).2 = true then (1 : ℝ) else 0) ∂ν) := by
      simpa only [Function.comp_apply, id_eq] using
        (hind.comp measurable_id hcm).integral_fun_mul_eq_mul_integral
          (hHm.comp hg).aestronglyMeasurable
          (hcm.comp (measurable_pi_apply n).snd).aestronglyMeasurable
    _ = _ := by
      rw [sbxS4_extension_integral_coin κ μ δ hcoin ν hν hδ₀ hμ, mul_comm]

end CountableExtension

/-- Transfer on separate origin and spatial-product good sets. Each good fibre
supplies normalized prefixes and a history-faithful realization; no freshness
or independence assertion is among the premises. All natural indices are
inside each fibre's good-set quantifier. -/
theorem sbxS4_extensions_hasFreshBits {α : Type*} [MeasurableSpace α] {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (δ : ℝ) (hδ₀ : 0 ≤ δ)
    (κ : (Vec d × FieldPair d) → (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    (μ : (Vec d × FieldPair d) → Measure (α × Bool))
    (ν : (Vec d × FieldPair d) → Measure (ℕ → α × Bool))
    (L : CoupledQuenchedLaws d)
    (g : (Vec d × FieldPair d) → (ℕ → α × Bool) → CoupledSample d)
    (z₀ : (Vec d × FieldPair d) → CoupledSample d)
    (past : (Vec d × FieldPair d) → (n : ℕ) → sbxS4SplitHistory α n → CoupledSample d)
    (horigin : ∀ᵐ ω ∂Q,
      (∀ n, IsMarkovKernel (κ (0, ω) n)) ∧
      IsProbabilityMeasure (μ (0, ω)) ∧ Measurable (g (0, ω)) ∧
      (∀ n, Measurable (past (0, ω) n)) ∧
      (∀ n h (b : Bool), κ (0, ω) n h {q | q.2 = b} =
        if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ)) ∧
      (∀ b : Bool, μ (0, ω) {q | q.2 = b} =
        if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ)) ∧
      (∀ n, (ν (0, ω)).map (Preorder.frestrictLe n) =
        sbxS4SplitPrefixLaw (κ (0, ω)) (μ (0, ω)) n) ∧
      (ν (0, ω)).map (g (0, ω)) = L (0, ω) ∧
      (∀ n, ∀ᵐ s ∂ν (0, ω), (g (0, ω) s).2 n = (s n).2) ∧
      (∀ᵐ s ∂ν (0, ω), Probability.stoppedHistorySample Δ 0 (g (0, ω) s) = z₀ (0, ω)) ∧
      ∀ n, ∀ᵐ s ∂ν (0, ω), Probability.stoppedHistorySample Δ (n + 1) (g (0, ω) s) =
        past (0, ω) n (Preorder.frestrictLe n s))
    (hproduct : ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q),
      (∀ n, IsMarkovKernel (κ xω n)) ∧
      IsProbabilityMeasure (μ xω) ∧ Measurable (g xω) ∧
      (∀ n, Measurable (past xω n)) ∧
      (∀ n h (b : Bool), κ xω n h {q | q.2 = b} =
        if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ)) ∧
      (∀ b : Bool, μ xω {q | q.2 = b} =
        if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ)) ∧
      (∀ n, (ν xω).map (Preorder.frestrictLe n) =
        sbxS4SplitPrefixLaw (κ xω) (μ xω) n) ∧
      (ν xω).map (g xω) = L xω ∧
      (∀ n, ∀ᵐ s ∂ν xω, (g xω s).2 n = (s n).2) ∧
      (∀ᵐ s ∂ν xω, Probability.stoppedHistorySample Δ 0 (g xω s) = z₀ xω) ∧
      ∀ n, ∀ᵐ s ∂ν xω, Probability.stoppedHistorySample Δ (n + 1) (g xω s) =
        past xω n (Preorder.frestrictLe n s)) : HasFreshBits Q Δ δ L := by
  constructor
  · filter_upwards [horigin] with ω h
    rcases h with ⟨hκ, hμprob, hg, hpast, hcoin, hμ, hν, hmap, hbits, hzero, hstop⟩
    let : ∀ n, IsMarkovKernel (κ (0, ω) n) := hκ
    let : IsProbabilityMeasure (μ (0, ω)) := hμprob
    exact sbxS4_extension_freshBitsAt (κ (0, ω)) (μ (0, ω)) δ hcoin
      (ν (0, ω)) hν Δ hδ₀ hμ L (0, ω) (g (0, ω)) hg hmap hbits
      (z₀ (0, ω)) hzero (past (0, ω)) hpast hstop
  · filter_upwards [hproduct] with xω h
    rcases h with ⟨hκ, hμprob, hg, hpast, hcoin, hμ, hν, hmap, hbits, hzero, hstop⟩
    let : ∀ n, IsMarkovKernel (κ xω n) := hκ
    let : IsProbabilityMeasure (μ xω) := hμprob
    exact sbxS4_extension_freshBitsAt (κ xω) (μ xω) δ hcoin
      (ν xω) hν Δ hδ₀ hμ L xω (g xω) hg hmap hbits
      (z₀ xω) hzero (past xω) hpast hstop


section ActualCountableExtensions

variable {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
  (z : Vec d) (ω : FieldPair d) (hP : ∀ x, IsProbabilityMeasure (P (x, ω)))
  (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
  (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
    (endpointBall i R x) ≤
    (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
  (K : Kernel (Vec d) (Path d × Bool)) [hKM : IsMarkovKernel K]
  (hK : ∀ x, K x = sbxS4FirstSegmentLaw Δ R δ i P x ω)

include hP hR hδ₀ hδ₁ hminor hK

omit hKM in
/-- Endpoint restart carries the exact actual Bernoulli masses at every history. -/
theorem sbxS4_endpointHistoryKernel_coin_mass (n : ℕ)
    (h : sbxS4SplitHistory (Path d) n) (b : Bool) :
    sbxS4EndpointHistoryKernel Δ K n h {q | q.2 = b} =
      if b then ENNReal.ofReal δ else ENNReal.ofReal (1 - δ) := by
  change K (sbxS4HistoryEndpoint Δ n h) _ = _
  rw [hK]
  let : IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) := hP _
  exact sbxS4_firstSegmentLaw_coin_mass Δ R δ i P _ ω hR hδ₀ hδ₁ (hminor _) b

variable (ν : Measure (ℕ → Path d × Bool))
  (hν : ∀ n, ν.map (Preorder.frestrictLe n) =
    sbxS4SegmentPrefixLaw Δ R δ i P z ω K n)

include hν

/-- An extension of the actual killed-bridge/residual prefixes has the complete
Bernoulli coin law, including its initial split coin. -/
theorem sbxS4_segmentExtension_map_coins :
    ν.map (fun s n => (s n).2) = sbxS4RemainingBitsLaw δ := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  exact sbxS4_extension_map_coins _ _ δ
    (sbxS4_endpointHistoryKernel_coin_mass Δ R δ i P ω hP hR hδ₀ hδ₁ hminor K hK)
    ν hν hδ₀.le hδ₁.le
    (sbxS4_firstSegmentLaw_coin_mass Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z))

/-- The complete future Bernoulli tail factors from the entire actual retained
segment/coin history, on every supplied countable extension of these prefixes. -/
theorem sbxS4_segmentExtension_prefix_futureCoins (n : ℕ) :
    ν.map (fun s => (Preorder.frestrictLe n s, sbxS4FutureCoins n s)) =
      (sbxS4SegmentPrefixLaw Δ R δ i P z ω K n).prod (sbxS4RemainingBitsLaw δ) := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  exact sbxS4_extension_prefix_futureCoins _ _ δ
    (sbxS4_endpointHistoryKernel_coin_mass Δ R δ i P ω hP hR hδ₀ hδ₁ hminor K hK)
    ν hν hδ₀.le hδ₁.le n

/-- Bounded tests of an actual extension's full tail and full retained history
are integrable and have the exact factorized integral. -/
theorem sbxS4_segmentExtension_integral_futureCoins (n : ℕ)
    (H : sbxS4SplitHistory (Path d) n → ℝ) (hH : Measurable H)
    (hbH : ∃ C : ℝ, ∀ h, ‖H h‖ ≤ C)
    (F : BernoulliSequence → ℝ) (hF : Measurable F)
    (hbF : ∃ C : ℝ, ∀ β, ‖F β‖ ≤ C) :
    Integrable (fun s => H (Preorder.frestrictLe n s) * F (sbxS4FutureCoins n s)) ν ∧
      (∫ s, H (Preorder.frestrictLe n s) * F (sbxS4FutureCoins n s) ∂ν) =
        (∫ h, H h ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n) *
          (∫ β, F β ∂sbxS4RemainingBitsLaw δ) := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  exact sbxS4_extension_integral_futureCoins _ _ δ
    (sbxS4_endpointHistoryKernel_coin_mass Δ R δ i P ω hP hR hδ₀ hδ₁ hminor K hK)
    ν hν hδ₀.le hδ₁.le n H hH hbH F hF hbF

/-- The literal fresh-bit consequence for a supplied realization of the actual
endpoint-restarted killed-bridge/residual segment law. -/
theorem sbxS4_segmentExtension_freshBitsAt
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s)) : FreshBitsAt Δ δ L (z, ω) := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  exact sbxS4_extension_freshBitsAt _ _ δ
    (sbxS4_endpointHistoryKernel_coin_mass Δ R δ i P ω hP hR hδ₀ hδ₁ hminor K hK)
    ν hν Δ hδ₀.le
    (sbxS4_firstSegmentLaw_coin_mass Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z))
    L (z, ω) g hg hmap hbits z₀ hzero past hpast hstop

end ActualCountableExtensions

/-! The complete next pair, rather than only its coin, is retained here.
These identities consume precisely the supplied finite marginals. -/

/-- Undoing chronological append recovers the genuine history/next-pair law. -/
theorem sbxS4_splitPrefixLaw_prefix_nextPair {α : Type*} [MeasurableSpace α]
    (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
    [∀ n, IsMarkovKernel (κ n)] (μ : Measure (α × Bool)) [IsProbabilityMeasure μ]
    (n : ℕ) :
    (sbxS4SplitPrefixLaw κ μ (n + 1)).map
      (fun h => (Preorder.frestrictLe₂ (π := fun _ => α × Bool) n.le_succ h,
        h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)) =
      sbxS4SplitPrefixLaw κ μ n ⊗ₘ κ n := by
  rw [sbxS4_splitPrefixLaw_succ, Measure.map_map
    ((Preorder.measurable_frestrictLe₂ (X := fun _ => α × Bool) n.le_succ).prodMk
      (measurable_pi_apply _)) (sbxS4_measurable_appendHistory n)]
  have he : (fun h : sbxS4SplitHistory α (n + 1) =>
      (Preorder.frestrictLe₂ (π := fun _ => α × Bool) n.le_succ h,
        h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)) ∘ sbxS4AppendHistory n = id := by
    funext q
    exact Prod.ext (sbxS4_appendHistory_restrict n q) (sbxS4_appendHistory_last n q)
  rw [he, Measure.map_id]

section IntervalExtension
variable {α : Type*} [MeasurableSpace α]
  (κ : (n : ℕ) → Kernel (sbxS4SplitHistory α n) (α × Bool))
  [∀ n, IsMarkovKernel (κ n)] (μ : Measure (α × Bool)) [IsProbabilityMeasure μ]
  (ν : Measure (ℕ → α × Bool))
  (hν : ∀ n, ν.map (Preorder.frestrictLe n) = sbxS4SplitPrefixLaw κ μ n)

include hν

omit [∀ n, IsMarkovKernel (κ n)] [IsProbabilityMeasure μ] in
/-- Index zero of a consistent extension is the literal initial segment/coin. -/
theorem sbxS4_extension_map_zeroPair : ν.map (fun s => s 0) = μ := by
  calc
    _ = (ν.map (Preorder.frestrictLe 0)).map
        (fun h : sbxS4SplitHistory α 0 => h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) := by
      exact (Measure.map_map (μ := ν)
        (show Measurable (fun h : sbxS4SplitHistory α 0 =>
          h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) from measurable_pi_apply _)
        (Preorder.measurable_frestrictLe 0)).symm
    _ = μ := by
      rw [hν, sbxS4_splitPrefixLaw_zero, Measure.map_map (measurable_pi_apply
        (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic 0))
        sbxS4_measurable_initialHistory]
      exact Measure.map_id

/-- Exact prefix/next-segment disintegration of the supplied infinite law. -/
theorem sbxS4_extension_prefix_nextPair (n : ℕ) :
    ν.map (fun s => (Preorder.frestrictLe n s, s (n + 1))) =
      sbxS4SplitPrefixLaw κ μ n ⊗ₘ κ n := by
  calc
    _ = (ν.map (Preorder.frestrictLe (n + 1))).map
        (fun h => (Preorder.frestrictLe₂ (π := fun _ => α × Bool) n.le_succ h,
          h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)) := by
      rw [Measure.map_map
        ((Preorder.measurable_frestrictLe₂ (X := fun _ => α × Bool) n.le_succ).prodMk
          (measurable_pi_apply _)) (Preorder.measurable_frestrictLe (n + 1))]
      rfl
    _ = _ := by rw [hν, sbxS4_splitPrefixLaw_prefix_nextPair]

/-- A bounded branch test on the actual countable extension has the same
integral as its finite disintegration, with an integrable left-hand test. -/
theorem sbxS4_extension_integral_branch (n : ℕ) (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (P B : sbxS4SplitHistory α n → Measure α)
    (hP : ∀ h, IsProbabilityMeasure (P h)) (hB : ∀ h, IsFiniteMeasure (B h))
    (hdom : ∀ h, ENNReal.ofReal δ • B h ≤ P h)
    (hκ : ∀ h, κ n h = sbxS4FirstCoinLaw δ (P h) (B h))
    (F : sbxS4SplitHistory α n × α → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ q, ‖F q‖ ≤ C) (b : Bool) :
    Integrable ({s : ℕ → α × Bool | (s (n + 1)).2 = b}.indicator
      (fun s => F (Preorder.frestrictLe n s, (s (n + 1)).1))) ν ∧
    (∫ s, {s : ℕ → α × Bool | (s (n + 1)).2 = b}.indicator
      (fun s => F (Preorder.frestrictLe n s, (s (n + 1)).1)) s ∂ν) =
      ∫ h, if b then δ * (∫ x, F (h, x) ∂B h)
        else (1 - δ) * (∫ x, F (h, x) ∂sbxS4SplitResidual δ (P h) (B h))
          ∂sbxS4SplitPrefixLaw κ μ n := by
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure κ μ ν hν
  have hm : Measurable (fun s : ℕ → α × Bool =>
      F (Preorder.frestrictLe n s, (s (n + 1)).1)) :=
    hF.comp ((Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply _).fst)
  have hs : MeasurableSet {s : ℕ → α × Bool | (s (n + 1)).2 = b} :=
    (measurable_pi_apply _).snd (measurableSet_singleton b)
  obtain ⟨C, hC⟩ := hb
  refine ⟨((integrable_const C).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => hC _)).indicator hs, ?_⟩
  have htest : Measurable (fun q : sbxS4SplitHistory α n × (α × Bool) =>
      {q : sbxS4SplitHistory α n × (α × Bool) | q.2.2 = b}.indicator
        (fun q => F (q.1, q.2.1)) q) :=
    (hF.comp (measurable_fst.prodMk measurable_snd.fst)).indicator
      (measurable_snd.snd (measurableSet_singleton b))
  have he := integral_map (μ := ν) ((Preorder.measurable_frestrictLe n).prodMk
    (measurable_pi_apply (n + 1))).aemeasurable htest.aestronglyMeasurable
  rw [sbxS4_extension_prefix_nextPair κ μ ν hν] at he
  have hbranch := sbxS4_splitPrefixLaw_integral_branch κ μ n δ hδ₀ hδ₁
    P B hP hB hdom hκ F hF ⟨C, hC⟩ b
  simpa only [Set.indicator, Set.mem_ofPred_eq] using he.symm.trans hbranch

/-- Signed tests on the actual countable extension disintegrate over the next coin. -/
theorem sbxS4_extension_integrable_branch (n : ℕ) (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (P B : sbxS4SplitHistory α n → Measure α)
    (hB : ∀ h, IsFiniteMeasure (B h))
    (hdom : ∀ h, ENNReal.ofReal δ • B h ≤ P h)
    (hκ : ∀ h, κ n h = sbxS4FirstCoinLaw δ (P h) (B h))
    (F : sbxS4SplitHistory α n × α → ℝ) (hF : Measurable F)
    (hi : Integrable (fun s : ℕ → α × Bool =>
      F (Preorder.frestrictLe n s, (s (n + 1)).1)) ν) (b : Bool) :
    Integrable ({s : ℕ → α × Bool | (s (n + 1)).2 = b}.indicator
      (fun s => F (Preorder.frestrictLe n s, (s (n + 1)).1))) ν ∧
    (∫ s, {s : ℕ → α × Bool | (s (n + 1)).2 = b}.indicator
      (fun s => F (Preorder.frestrictLe n s, (s (n + 1)).1)) s ∂ν) =
      ∫ h, if b then δ * (∫ x, F (h, x) ∂B h)
        else (1 - δ) * (∫ x, F (h, x) ∂sbxS4SplitResidual δ (P h) (B h))
          ∂sbxS4SplitPrefixLaw κ μ n := by
  have hs : MeasurableSet {s : ℕ → α × Bool | (s (n + 1)).2 = b} :=
    (measurable_pi_apply _).snd (measurableSet_singleton b)
  let f : sbxS4SplitHistory α n × (α × Bool) → ℝ := fun q => F (q.1, q.2.1)
  have hf : Measurable f := hF.comp (measurable_fst.prodMk measurable_snd.fst)
  have hm : Measurable (fun s : ℕ → α × Bool =>
      (Preorder.frestrictLe n s, s (n + 1))) :=
    (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  have hj : Integrable f (sbxS4SplitPrefixLaw κ μ n ⊗ₘ κ n) := by
    rw [← sbxS4_extension_prefix_nextPair κ μ ν hν]
    exact (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mpr hi
  refine ⟨hi.indicator hs, ?_⟩
  have htest : Measurable (fun q : sbxS4SplitHistory α n × (α × Bool) =>
      {q : sbxS4SplitHistory α n × (α × Bool) | q.2.2 = b}.indicator f q) :=
    hf.indicator (measurable_snd.snd (measurableSet_singleton b))
  have he := integral_map (μ := ν) hm.aemeasurable htest.aestronglyMeasurable
  rw [sbxS4_extension_prefix_nextPair κ μ ν hν] at he
  have hbranch := (sbxS4_splitPrefixLaw_integrable_branch κ μ n δ hδ₀ hδ₁
    P B hB hdom hκ F hF hj b).2
  simpa only [f, Set.indicator, Set.mem_ofPred_eq] using he.symm.trans hbranch

end IntervalExtension

/-- A bounded measurable past, coin and path observable is integrable on a
finite law. This does not use any conditional interval identity. -/
theorem sbxS4_integrable_interval_bit {β : Type*} [MeasurableSpace β] {d : ℕ}
    (η : Measure β) [IsFiniteMeasure η]
    (H : β → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H)
    (γ : β → Path d) (hγ : Measurable γ) (c : β → Bool) (hc : Measurable c)
    (F : Path d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F) (b : Bool) :
    Integrable (fun q => H q * (if c q = b then (1 : ℝ) else 0) * F (γ q)) η := by
  obtain ⟨A, hA⟩ := hbH
  obtain ⟨C, hC⟩ := hbF
  have hi : Integrable (fun q => F (γ q)) η :=
    (integrable_const C).mono' (hF.comp hγ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hC _)
  have hiH := hi.bdd_mul hH.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => show ‖H q‖ ≤ A from hA q)
  have hm : Measurable (fun q => if c q = b then (1 : ℝ) else 0) :=
    (measurable_of_finite (fun a : Bool => if a = b then (1 : ℝ) else 0)).comp hc
  have hbound : ∀ᵐ q ∂η, ‖if c q = b then (1 : ℝ) else 0‖ ≤ 1 :=
    Filter.Eventually.of_forall fun q => by split <;> norm_num
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    hiH.mul_bdd hm.aestronglyMeasurable hbound

section ActualIntervalExtension
variable {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
  (z : Vec d) (ω : FieldPair d) (hP : ∀ x, IsProbabilityMeasure (P (x, ω)))
  (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
  (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
    (endpointBall i R x) ≤
    (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
  (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K]
  (hK : ∀ x, K x = sbxS4FirstSegmentLaw Δ R δ i P x ω)

include hP hR hδ₀ hδ₁ hminor hK

omit [IsMarkovKernel K] in
/-- Measurability of both literal source expectations follows from the actual
split kernel, including the RN bridge and its exceptional density branches. -/
theorem sbxS4_measurable_split_expectations
    (F : Path d → ℝ) (hF : Measurable F) (hb : BoundedRealTest F) :
    Measurable (fun x => ∫ γ, F γ ∂P (x, ω)) ∧
      Measurable (fun x => ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P x ω) := by
  have hb' : ∃ C : ℝ, ∀ γ, ‖F γ‖ ≤ C := by
    simpa only [BoundedRealTest, Real.norm_eq_abs] using hb
  have hpath := (hF.comp measurable_fst).stronglyMeasurable.integral_kernel (κ := K)
  have he : (fun x => ∫ q, F q.1 ∂K x) = fun x => ∫ γ, F γ ∂P (x, ω) := by
    funext x
    let : IsProbabilityMeasure (P (x, ω)) := hP x
    let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P x ω) :=
      sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P x ω hR hδ₀ (hminor x)
    rw [← integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable,
      hK x, sbxS4FirstSegmentLaw, sbxS4_firstCoinLaw_map_fst δ _ _ hδ₁
        (sbxS4_smul_killedBridgeMixture_le Δ R δ i P x ω hR (hminor x))]
  refine ⟨he ▸ hpath.measurable, ?_⟩
  have hm : Measurable ({q : Path d × Bool | q.2 = true}.indicator
      (fun q => F q.1)) :=
    (hF.comp measurable_fst).indicator (measurable_snd (measurableSet_singleton true))
  have hbridge := hm.stronglyMeasurable.integral_kernel (κ := K)
  have heB : (fun x => δ⁻¹ * ∫ q,
      {q : Path d × Bool | q.2 = true}.indicator (fun q => F q.1) q ∂K x) =
      fun x => ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P x ω := by
    funext x
    let : IsProbabilityMeasure (P (x, ω)) := hP x
    let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P x ω) :=
      sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P x ω hR hδ₀ (hminor x)
    rw [hK x, sbxS4FirstSegmentLaw]
    have h := (sbxS4_firstCoinLaw_integral_branch δ _ _ hδ₀.le hδ₁
      (sbxS4_smul_killedBridgeMixture_le Δ R δ i P x ω hR (hminor x))
      F hF.stronglyMeasurable hb' true).2
    change _ = δ * _ at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hδ₀.ne', one_mul]
  exact heB ▸ (measurable_const.mul hbridge.measurable)

omit z [IsMarkovKernel K] in
/-- Bounded past factors times either literal source expectation are integrable
on any finite measure with a measurable endpoint map. -/
theorem sbxS4_integrable_split_expectations {β : Type*} [MeasurableSpace β]
    (η : Measure β) [IsFiniteMeasure η] (e : β → Vec d) (he : Measurable e)
    (H : β → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H)
    (F : Path d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F) :
    Integrable (fun q => H q * (∫ γ, F γ ∂P (e q, ω))) η ∧
      Integrable (fun q => H q *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (e q) ω)) η := by
  obtain ⟨C, hC⟩ := hbF
  obtain ⟨A, hA⟩ := hbH
  have hm := sbxS4_measurable_split_expectations Δ R δ i P ω hP hR hδ₀ hδ₁
    hminor K hK F hF ⟨C, hC⟩
  have hpath : Integrable (fun q => ∫ γ, F γ ∂P (e q, ω)) η := by
    apply (integrable_const C).mono' (hm.1.comp he).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro q
    let : IsProbabilityMeasure (P (e q, ω)) := hP _
    simpa using norm_integral_le_of_norm_le_const (μ := P (e q, ω)) (f := F)
      (Filter.Eventually.of_forall fun γ => (hC γ : |F γ| ≤ C))
  have hbridge : Integrable
      (fun q => ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (e q) ω) η := by
    apply (integrable_const C).mono' (hm.2.comp he).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro q
    let : IsProbabilityMeasure (P (e q, ω)) := hP _
    let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P (e q) ω) :=
      sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P _ ω hR hδ₀ (hminor _)
    simpa using norm_integral_le_of_norm_le_const
      (μ := Renewal.killedBridgeMixture Δ R i P (e q) ω) (f := F)
      (Filter.Eventually.of_forall fun γ => (hC γ : |F γ| ≤ C))
  have hbound : ∀ᵐ q ∂η, ‖H q‖ ≤ A :=
    Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hA q
  exact ⟨hpath.bdd_mul hH.aestronglyMeasurable hbound,
    hbridge.bdd_mul hH.aestronglyMeasurable hbound⟩

variable (ν : Measure (ℕ → Path d × Bool))
  (hν : ∀ n, ν.map (Preorder.frestrictLe n) =
    sbxS4SegmentPrefixLaw Δ R δ i P z ω K n)

include hν

/-- The literal success and normalized failure laws at the next endpoint
govern every bounded past/segment test on a consistent infinite extension. -/
theorem sbxS4_segmentExtension_integral_branch (n : ℕ)
    (F : sbxS4SplitHistory (Path d) n × Path d → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ q, ‖F q‖ ≤ C) (b : Bool) :
    Integrable ({s : ℕ → Path d × Bool | (s (n + 1)).2 = b}.indicator
      (fun s => F (Preorder.frestrictLe n s, (s (n + 1)).1))) ν ∧
    (∫ s, {s : ℕ → Path d × Bool | (s (n + 1)).2 = b}.indicator
      (fun s => F (Preorder.frestrictLe n s, (s (n + 1)).1)) s ∂ν) =
      ∫ h, if b then δ * (∫ γ, F (h, γ)
          ∂Renewal.killedBridgeMixture Δ R i P (sbxS4HistoryEndpoint Δ n h) ω)
        else (1 - δ) * (∫ γ, F (h, γ)
          ∂sbxS4FailedSegmentLaw Δ R δ i P (sbxS4HistoryEndpoint Δ n h) ω)
        ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  apply sbxS4_extension_integral_branch _ _ ν hν n δ hδ₀.le hδ₁
    (fun h => P (sbxS4HistoryEndpoint Δ n h, ω))
    (fun h => Renewal.killedBridgeMixture Δ R i P (sbxS4HistoryEndpoint Δ n h) ω)
    (fun h => hP _) ?_ ?_ ?_ F hF hb b
  · intro h
    let : IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) := hP _
    let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P
        (sbxS4HistoryEndpoint Δ n h) ω) :=
      sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P _ ω hR hδ₀ (hminor _)
    infer_instance
  · intro h
    let : IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) := hP _
    exact sbxS4_smul_killedBridgeMixture_le Δ R δ i P _ ω hR (hminor _)
  · intro h
    exact hK _

/-- A signed test of the actual past and next segment disintegrates over
both literal coin branches whenever it is integrable on the extension. -/
theorem sbxS4_segmentExtension_integrable_branch (n : ℕ)
    (F : sbxS4SplitHistory (Path d) n × Path d → ℝ) (hF : Measurable F)
    (hi : Integrable (fun s : ℕ → Path d × Bool =>
      F (Preorder.frestrictLe n s, (s (n + 1)).1)) ν) (b : Bool) :
    Integrable ({s : ℕ → Path d × Bool | (s (n + 1)).2 = b}.indicator
      (fun s => F (Preorder.frestrictLe n s, (s (n + 1)).1))) ν ∧
    (∫ s, {s : ℕ → Path d × Bool | (s (n + 1)).2 = b}.indicator
      (fun s => F (Preorder.frestrictLe n s, (s (n + 1)).1)) s ∂ν) =
      ∫ h, if b then δ * (∫ γ, F (h, γ)
          ∂Renewal.killedBridgeMixture Δ R i P (sbxS4HistoryEndpoint Δ n h) ω)
        else (1 - δ) * (∫ γ, F (h, γ)
          ∂sbxS4FailedSegmentLaw Δ R δ i P (sbxS4HistoryEndpoint Δ n h) ω)
        ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  apply sbxS4_extension_integrable_branch _ _ ν hν n δ hδ₀.le hδ₁
    (fun h => P (sbxS4HistoryEndpoint Δ n h, ω))
    (fun h => Renewal.killedBridgeMixture Δ R i P (sbxS4HistoryEndpoint Δ n h) ω)
    ?_ ?_ ?_ F hF hi b
  · intro h
    let : IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) := hP _
    let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P
        (sbxS4HistoryEndpoint Δ n h) ω) :=
      sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P _ ω hR hδ₀ (hminor _)
    infer_instance
  · intro h
    let : IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) := hP _
    exact sbxS4_smul_killedBridgeMixture_le Δ R δ i P _ ω hR (hminor _)
  · intro h
    exact hK _

/-- Both unnormalized interval identities, on the supplied infinite law. The
failure identity contains the literal source difference, rather than a new
residual premise. All three displayed tests are integrable. -/
theorem sbxS4_segmentExtension_interval_test (n : ℕ)
    (H : sbxS4SplitHistory (Path d) n → ℝ) (hH : Measurable H)
    (hbH : BoundedRealTest H) (F : Path d → ℝ) (hF : Measurable F)
    (hbF : BoundedRealTest F) (b : Bool) :
    Integrable (fun s => H (Preorder.frestrictLe n s) *
      (if (s (n + 1)).2 = b then (1 : ℝ) else 0) * F (s (n + 1)).1) ν ∧
    Integrable (fun s => H (Preorder.frestrictLe n s) *
      (∫ γ, F γ ∂P (sbxS4HistoryEndpoint Δ n (Preorder.frestrictLe n s), ω))) ν ∧
    Integrable (fun s => H (Preorder.frestrictLe n s) *
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
        (sbxS4HistoryEndpoint Δ n (Preorder.frestrictLe n s)) ω)) ν ∧
    (∫ s, H (Preorder.frestrictLe n s) *
      (if (s (n + 1)).2 = b then (1 : ℝ) else 0) * F (s (n + 1)).1 ∂ν) =
      if b then δ * (∫ s, H (Preorder.frestrictLe n s) *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
          (sbxS4HistoryEndpoint Δ n (Preorder.frestrictLe n s)) ω) ∂ν)
      else ∫ s, H (Preorder.frestrictLe n s) *
        ((∫ γ, F γ ∂P (sbxS4HistoryEndpoint Δ n (Preorder.frestrictLe n s), ω)) -
          δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
            (sbxS4HistoryEndpoint Δ n (Preorder.frestrictLe n s)) ω)) ∂ν := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure _ _ ν hν
  have hm := sbxS4_measurable_split_expectations Δ R δ i P ω hP hR hδ₀ hδ₁
    hminor K hK F hF hbF
  have hi := sbxS4_integrable_split_expectations Δ R δ i P ω hP hR hδ₀ hδ₁ hminor
    K hK ν (fun s => sbxS4HistoryEndpoint Δ n (Preorder.frestrictLe n s))
    ((sbxS4_measurable_historyEndpoint Δ n).comp (Preorder.measurable_frestrictLe n))
    (H ∘ Preorder.frestrictLe n) (hH.comp (Preorder.measurable_frestrictLe n))
    (by obtain ⟨C, hC⟩ := hbH; exact ⟨C, fun s => hC _⟩) F hF hbF
  obtain ⟨A, hA⟩ := hbH
  obtain ⟨C, hC⟩ := hbF
  have hprod : ∃ D : ℝ, ∀ q : sbxS4SplitHistory (Path d) n × Path d,
      ‖H q.1 * F q.2‖ ≤ D := by
    refine ⟨A * C, fun q => ?_⟩
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hA q.1) (hC q.2) (abs_nonneg _)
      ((abs_nonneg _).trans (hA q.1))
  have hbranch := sbxS4_segmentExtension_integral_branch Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν n (fun q => H q.1 * F q.2)
    ((hH.comp measurable_fst).mul (hF.comp measurable_snd)) hprod b
  have hind : ({s : ℕ → Path d × Bool | (s (n + 1)).2 = b}.indicator
      (fun s => H (Preorder.frestrictLe n s) * F (s (n + 1)).1)) =
      fun s => H (Preorder.frestrictLe n s) *
        (if (s (n + 1)).2 = b then (1 : ℝ) else 0) * F (s (n + 1)).1 := by
    funext s
    by_cases hs : (s (n + 1)).2 = b <;> simp [Set.indicator, hs]
  rw [hind] at hbranch
  refine ⟨hbranch.1, hi.1, hi.2, ?_⟩
  rw [hbranch.2]
  let E : sbxS4SplitHistory (Path d) n → ℝ := fun h =>
    if b then δ * (H h * (∫ γ, F γ
      ∂Renewal.killedBridgeMixture Δ R i P (sbxS4HistoryEndpoint Δ n h) ω))
    else H h * ((∫ γ, F γ ∂P (sbxS4HistoryEndpoint Δ n h, ω)) -
      δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
        (sbxS4HistoryEndpoint Δ n h) ω))
  have hE : Measurable E := by
    dsimp only [E]
    cases b with
    | true =>
      exact measurable_const.mul
        (hH.mul (hm.2.comp (sbxS4_measurable_historyEndpoint Δ n)))
    | false =>
      exact hH.mul ((hm.1.comp (sbxS4_measurable_historyEndpoint Δ n)).sub
        (measurable_const.mul (hm.2.comp (sbxS4_measurable_historyEndpoint Δ n))))
  have he : (∫ h, if b then δ * (∫ γ, H h * F γ
        ∂Renewal.killedBridgeMixture Δ R i P (sbxS4HistoryEndpoint Δ n h) ω)
      else (1 - δ) * (∫ γ, H h * F γ
        ∂sbxS4FailedSegmentLaw Δ R δ i P (sbxS4HistoryEndpoint Δ n h) ω)
        ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n) =
      ∫ h, E h ∂sbxS4SegmentPrefixLaw Δ R δ i P z ω K n := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro h
    let : IsProbabilityMeasure (P (sbxS4HistoryEndpoint Δ n h, ω)) := hP _
    cases b with
    | true => simp only [E, ↓reduceIte, integral_const_mul]
    | false =>
      simp only [E, Bool.false_eq_true, ↓reduceIte, integral_const_mul]
      rw [mul_left_comm (1 - δ), sbxS4_failedSegmentLaw_integral_difference
        Δ R δ i P _ ω hR hδ₀ hδ₁ (hminor _) F hF ⟨C, hC⟩]
  rw [he, ← hν n, integral_map (Preorder.measurable_frestrictLe n).aemeasurable
    hE.aestronglyMeasurable]
  cases b with
  | false => rfl
  | true => exact integral_const_mul δ _

omit [IsMarkovKernel K] hK in
/-- The first interval uses coin zero and the supplied initial position,
without pretending that an earlier sampled segment exists. -/
theorem sbxS4_segmentExtension_initial_test
    (F : Path d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F) (b : Bool) :
    (∫ s, (if (s 0).2 = b then (1 : ℝ) else 0) * F (s 0).1 ∂ν) =
      if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω)
      else (∫ γ, F γ ∂P (z, ω)) -
        δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω) := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P z ω) :=
    sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P z ω hR hδ₀ (hminor z)
  have hb : ∃ C : ℝ, ∀ γ, ‖F γ‖ ≤ C := by
    simpa only [BoundedRealTest, Real.norm_eq_abs] using hbF
  have hbranch := (sbxS4_firstCoinLaw_integral_branch δ (P (z, ω))
    (Renewal.killedBridgeMixture Δ R i P z ω) hδ₀.le hδ₁
    (sbxS4_smul_killedBridgeMixture_le Δ R δ i P z ω hR (hminor z))
    F hF.stronglyMeasurable hb b).2
  have hm : Measurable (fun q : Path d × Bool =>
      (if q.2 = b then (1 : ℝ) else 0) * F q.1) :=
    ((measurable_of_finite (fun a : Bool => if a = b then (1 : ℝ) else 0)).comp
      measurable_snd).mul (hF.comp measurable_fst)
  have hmap0 := integral_map (μ := ν)
    (show Measurable (fun s : ℕ → Path d × Bool => s 0) from
      measurable_pi_apply 0).aemeasurable hm.aestronglyMeasurable
  rw [sbxS4_extension_map_zeroPair _ _ ν hν] at hmap0
  rw [← hmap0]
  have he : (∫ q, (if q.2 = b then (1 : ℝ) else 0) * F q.1
      ∂sbxS4FirstSegmentLaw Δ R δ i P z ω) =
      ∫ q, {q : Path d × Bool | q.2 = b}.indicator (fun q => F q.1) q
        ∂sbxS4FirstCoinLaw δ (P (z, ω)) (Renewal.killedBridgeMixture Δ R i P z ω) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro q
    by_cases hq : q.2 = b <;> simp [Set.indicator, hq]
  rw [he, hbranch]
  cases b with
  | true => rfl
  | false =>
    exact sbxS4_failedSegmentLaw_integral_difference Δ R δ i P z ω hR hδ₀ hδ₁
      (hminor z) F hF hbF

omit [IsMarkovKernel K] hK in
/-- Signed integrable path tests retain the literal success and failure laws
on the initial interval of the realized extension. -/
theorem sbxS4_segmentExtension_initial_integrable_branch
    (F : Path d → ℝ) (hF : Measurable F) (hfi : Integrable F (P (z, ω)))
    (b : Bool) :
    Integrable ({s : ℕ → Path d × Bool | (s 0).2 = b}.indicator
      (fun s => F (s 0).1)) ν ∧
    (∫ s, {s : ℕ → Path d × Bool | (s 0).2 = b}.indicator
      (fun s => F (s 0).1) s ∂ν) =
      if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω)
      else (1 - δ) * (∫ γ, F γ ∂sbxS4FailedSegmentLaw Δ R δ i P z ω) := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P z ω) :=
    sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P z ω hR hδ₀ (hminor z)
  have hbranch := sbxS4_firstCoinLaw_integrable_branch δ (P (z, ω))
    (Renewal.killedBridgeMixture Δ R i P z ω) hδ₀.le hδ₁
    (sbxS4_smul_killedBridgeMixture_le Δ R δ i P z ω hR (hminor z))
    F hF.stronglyMeasurable hfi b
  have hm : Measurable (fun q : Path d × Bool =>
      {q : Path d × Bool | q.2 = b}.indicator (fun q => F q.1) q) :=
    (hF.comp measurable_fst).indicator (measurable_snd (measurableSet_singleton b))
  have hmap := sbxS4_extension_map_zeroPair _ _ ν hν
  have hi : Integrable (fun s : ℕ → Path d × Bool =>
      {q : Path d × Bool | q.2 = b}.indicator (fun q => F q.1) (s 0)) ν := by
    apply (integrable_map_measure hm.aestronglyMeasurable
      (measurable_pi_apply 0).aemeasurable).mp
    rw [hmap]
    exact hbranch.1
  refine ⟨?_, ?_⟩
  · exact hi
  · have he := integral_map (μ := ν) (measurable_pi_apply 0).aemeasurable
      hm.aestronglyMeasurable
    rw [hmap] at he
    simpa only [Set.indicator, Set.mem_ofPred_eq, sbxS4FirstSegmentLaw,
      sbxS4FailedSegmentLaw] using he.symm.trans hbranch.2

/-- A history-faithful realization of the actual consistent split law satisfies
the literal one-interval clause. The supplied data are only segment, bit and
stopped-history projection identities; no interval identity is a premise. -/
theorem sbxS4_segmentExtension_oneIntervalKernelAt
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (hstart : ∀ᵐ s ∂ν, (g s).1 0 = z)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (hsegment : ∀ (n : ℕ), ∀ᵐ s ∂ν, ∀ t : ℝ≥0, t ≤ Δ →
      (g s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t) :
    Renewal.OneIntervalKernelAt Δ δ R i P L (z, ω) := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure _ _ ν hν
  let : IsProbabilityMeasure (L (z, ω)) := hmap ▸ (inferInstance : IsProbabilityMeasure (ν.map g))
  have hgood : ∀ᵐ s ∂ν,
      Probability.stoppedHistorySample Δ 0 (g s) = z₀ ∧ (g s).1 0 = z ∧
      (∀ n, (g s).2 n = (s n).2) ∧
      (∀ n, Probability.stoppedHistorySample Δ (n + 1) (g s) =
        past n (Preorder.frestrictLe n s)) ∧
      ∀ (n : ℕ) (t : ℝ≥0), t ≤ Δ → (g s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t := by
    filter_upwards [hzero, hstart, ae_all_iff.mpr hbits, ae_all_iff.mpr hstop,
      ae_all_iff.mpr hsegment] with s hz hs hb hp hi
    exact ⟨hz, hs, hb, hp, hi⟩
  intro n H F hH hbH hF hbF hlocal
  have hHm : Measurable H := hH.mono (Probability.finiteHistorySigma_le Δ n) le_rfl
  have hshift : Measurable (fun q : CoupledSample d =>
      pathTimeShift q.1 ((n : ℝ≥0) * Δ)) :=
    Probability.continuous_path_time_shift.measurable.comp
      (measurable_const.prodMk measurable_fst)
  have hend : Measurable (fun q : CoupledSample d => q.1 ((n : ℝ≥0) * Δ)) :=
    (continuous_eval_const _).measurable.comp measurable_fst
  have hm := sbxS4_measurable_split_expectations Δ R δ i P ω hP hR hδ₀ hδ₁
    hminor K hK F hF hbF
  have hi := sbxS4_integrable_split_expectations Δ R δ i P ω hP hR hδ₀ hδ₁
    hminor K hK (L (z, ω)) _ hend H hHm hbH F hF hbF
  have hib (b : Bool) := sbxS4_integrable_interval_bit (L (z, ω)) H hHm hbH _ hshift
    (fun q : CoupledSample d => q.2 n) ((measurable_pi_apply n).comp measurable_snd)
    F hF hbF b
  have hbm (b : Bool) : Measurable (fun q : CoupledSample d =>
      H q * (if q.2 n = b then (1 : ℝ) else 0) *
        F (pathTimeShift q.1 ((n : ℝ≥0) * Δ))) :=
    (hHm.mul ((measurable_of_finite (fun a : Bool => if a = b then (1 : ℝ) else 0)).comp
      ((measurable_pi_apply n).comp measurable_snd))).mul (hF.comp hshift)
  have hrm (b : Bool) : Measurable (fun q : CoupledSample d => H q *
      (if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
          (q.1 ((n : ℝ≥0) * Δ)) ω)
        else (∫ γ, F γ ∂P (q.1 ((n : ℝ≥0) * Δ), ω)) -
          δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
            (q.1 ((n : ℝ≥0) * Δ)) ω))) := by
    cases b with
    | true => exact hHm.mul (measurable_const.mul (hm.2.comp hend))
    | false => exact hHm.mul ((hm.1.comp hend).sub (measurable_const.mul (hm.2.comp hend)))
  have hpull (f : CoupledSample d → ℝ) (hf : Measurable f) :
      (∫ q, f q ∂L (z, ω)) = ∫ s, f (g s) ∂ν := by
    rw [← hmap, integral_map hg.aemeasurable hf.aestronglyMeasurable]
  have hseq (b : Bool) :
      (∫ s, H (g s) * (if (g s).2 n = b then (1 : ℝ) else 0) *
        F (pathTimeShift (g s).1 ((n : ℝ≥0) * Δ)) ∂ν) =
      ∫ s, H (g s) *
        (if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
            ((g s).1 ((n : ℝ≥0) * Δ)) ω)
          else (∫ γ, F γ ∂P ((g s).1 ((n : ℝ≥0) * Δ), ω)) -
            δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
              ((g s).1 ((n : ℝ≥0) * Δ)) ω)) ∂ν := by
    cases n with
    | zero =>
      have hH0 : ∀ᵐ s ∂ν, H (g s) = H z₀ := by
        filter_upwards [hgood] with s hs
        rw [← hs.1, Probability.finiteHistory_test_stopped Δ 0 H hH]
      have heq : ∀ᵐ s ∂ν,
          F (pathTimeShift (g s).1 (((0 : ℕ) : ℝ≥0) * Δ)) = F (s 0).1 := by
        filter_upwards [hgood] with s hs
        apply hlocal
        intro t ht
        exact hs.2.2.2.2 0 t ht
      calc
        _ = H z₀ * (∫ s, (if (s 0).2 = b then (1 : ℝ) else 0) * F (s 0).1 ∂ν) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [hH0, heq, hgood] with s hh hf hs
          rw [hh, hf, hs.2.2.1 0, mul_assoc]
        _ = H z₀ * (if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω)
            else (∫ γ, F γ ∂P (z, ω)) -
              δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω)) := by
          rw [sbxS4_segmentExtension_initial_test Δ R δ i P z ω hP hR hδ₀ hδ₁
            hminor K ν hν F hF hbF b]
        _ = _ := by
          symm
          calc
            _ = ∫ _s, H z₀ * (if b then δ *
                (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω)
              else (∫ γ, F γ ∂P (z, ω)) - δ *
                (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω)) ∂ν := by
              apply integral_congr_ae
              filter_upwards [hH0, hgood] with s hh hs
              simp only [Nat.cast_zero, zero_mul, hh]
              rw [hs.2.1]
            _ = _ := by simp
    | succ m =>
      have hHpast : ∀ᵐ s ∂ν, H (g s) = H (past m (Preorder.frestrictLe m s)) := by
        filter_upwards [hgood] with s hs
        rw [← hs.2.2.2.1 m, Probability.finiteHistory_test_stopped Δ (m + 1) H hH]
      have heq : ∀ᵐ s ∂ν,
          F (pathTimeShift (g s).1 (((m + 1 : ℕ) : ℝ≥0) * Δ)) = F (s (m + 1)).1 := by
        filter_upwards [hgood] with s hs
        exact hlocal _ _ (fun t ht => hs.2.2.2.2 (m + 1) t ht)
      have he : ∀ᵐ s ∂ν, (g s).1 (((m + 1 : ℕ) : ℝ≥0) * Δ) =
          sbxS4HistoryEndpoint Δ m (Preorder.frestrictLe m s) := by
        filter_upwards [hgood] with s hs
        have ht : ((m + 1 : ℕ) : ℝ≥0) * Δ = (m : ℝ≥0) * Δ + Δ := by
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        rw [ht]
        exact hs.2.2.2.2 m Δ le_rfl
      have htest := sbxS4_segmentExtension_interval_test Δ R δ i P z ω hP hR hδ₀ hδ₁
        hminor K hK ν hν m (H ∘ past m) (hHm.comp (hpast m))
        (by obtain ⟨C, hC⟩ := hbH; exact ⟨C, fun h => hC _⟩) F hF hbF b
      simp only [Function.comp_apply] at htest
      calc
        _ = ∫ s, H (past m (Preorder.frestrictLe m s)) *
            (if (s (m + 1)).2 = b then (1 : ℝ) else 0) * F (s (m + 1)).1 ∂ν := by
          apply integral_congr_ae
          filter_upwards [hHpast, heq, hgood] with s hh hf hs
          simp only [hh, hf, hs.2.2.1 (m + 1)]
        _ = _ := by
          rw [htest.2.2.2]
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            apply integral_congr_ae
            filter_upwards [hHpast, he] with s hh hs
            rw [hh, hs]
          | true =>
            simp only [↓reduceIte]
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards [hHpast, he] with s hh hs
            rw [hh, hs]
            ring
  have hid (b : Bool) :
      (∫ q, H q * (if q.2 n = b then (1 : ℝ) else 0) *
        F (pathTimeShift q.1 ((n : ℝ≥0) * Δ)) ∂L (z, ω)) =
      ∫ q, H q * (if b then δ *
          (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (q.1 ((n : ℝ≥0) * Δ)) ω)
        else (∫ γ, F γ ∂P (q.1 ((n : ℝ≥0) * Δ), ω)) - δ *
          (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
            (q.1 ((n : ℝ≥0) * Δ)) ω)) ∂L (z, ω) := by
    rw [hpull _ (hbm b), hpull _ (hrm b)]
    exact hseq b
  have hf : (fun q : CoupledSample d => H q *
      (if q.2 n = true then (0 : ℝ) else 1) * F (pathTimeShift q.1 ((n : ℝ≥0) * Δ))) =
      fun q : CoupledSample d => H q *
        (if q.2 n = false then (1 : ℝ) else 0) * F (pathTimeShift q.1 ((n : ℝ≥0) * Δ)) := by
    funext q
    cases q.2 n <;> rfl
  refine ⟨hib true, hi.2, ?_, ?_, ?_, hi.1, ?_⟩
  · rw [hid true]
    calc
      _ = ∫ q, δ * (H q * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
          (q.1 ((n : ℝ≥0) * Δ)) ω)) ∂L (z, ω) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun _ => by simp only [↓reduceIte]; ring
      _ = _ := integral_const_mul δ _
  · rw [hf]
    exact hib false
  · convert hi.1.sub (hi.2.const_mul δ) using 1
    funext q
    simp only [Pi.sub_apply]
    ring
  · rw [hf]
    simpa only [Bool.false_eq_true, ↓reduceIte] using hid false

end ActualIntervalExtension

/-- The literal interval clause on separate origin and spatial-product fibres.
The fibre premises describe the supplied split extension and its realization. -/
theorem sbxS4_segmentExtensions_hasOneIntervalKernel {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (L : CoupledQuenchedLaws d)
    (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (K : Vec d × FieldPair d → Kernel (Vec d) (Path d × Bool))
    (ν : Vec d × FieldPair d → Measure (ℕ → Path d × Bool))
    (g : Vec d × FieldPair d → (ℕ → Path d × Bool) → CoupledSample d)
    (z₀ : Vec d × FieldPair d → CoupledSample d)
    (past : Vec d × FieldPair d → (n : ℕ) →
      sbxS4SplitHistory (Path d) n → CoupledSample d) :
    let Good : Vec d × FieldPair d → Prop := fun xω =>
      (∀ x, IsProbabilityMeasure (P (x, xω.2))) ∧
      (∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x xω.2).map (fun γ : Path d => γ Δ)) ∧
      IsMarkovKernel (K xω) ∧
      (∀ x, K xω x = sbxS4FirstSegmentLaw Δ R δ i P x xω.2) ∧
      Measurable (g xω) ∧ (∀ n, Measurable (past xω n)) ∧
      (∀ n, (ν xω).map (Preorder.frestrictLe n) =
        sbxS4SegmentPrefixLaw Δ R δ i P xω.1 xω.2 (K xω) n) ∧
      (ν xω).map (g xω) = L xω ∧
      (∀ n, ∀ᵐ s ∂ν xω, (g xω s).2 n = (s n).2) ∧
      (∀ᵐ s ∂ν xω, Probability.stoppedHistorySample Δ 0 (g xω s) = z₀ xω) ∧
      (∀ᵐ s ∂ν xω, (g xω s).1 0 = xω.1) ∧
      (∀ n, ∀ᵐ s ∂ν xω, Probability.stoppedHistorySample Δ (n + 1) (g xω s) =
        past xω n (Preorder.frestrictLe n s)) ∧
      ∀ (n : ℕ), ∀ᵐ s ∂ν xω, ∀ t : ℝ≥0, t ≤ Δ →
        (g xω s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t
    (∀ᵐ ω ∂Q, Good (0, ω)) →
    (∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q), Good xω) →
    Renewal.HasOneIntervalKernel Q Δ δ R i P L := by
  dsimp only
  intro horigin hproduct
  constructor
  · filter_upwards [horigin] with ω h
    rcases h with ⟨hP, hminor, hKM, hK, hg, hpast, hν, hmap, hbits,
      hzero, hstart, hstop, hsegment⟩
    let : IsMarkovKernel (K (0, ω)) := hKM
    exact sbxS4_segmentExtension_oneIntervalKernelAt Δ R δ i P 0 ω hP hR hδ₀ hδ₁
      hminor (K (0, ω)) hK (ν (0, ω)) hν L (g (0, ω)) hg hmap hbits
      (z₀ (0, ω)) hzero hstart (past (0, ω)) hpast hstop hsegment
  · filter_upwards [hproduct] with xω h
    rcases h with ⟨hP, hminor, hKM, hK, hg, hpast, hν, hmap, hbits,
      hzero, hstart, hstop, hsegment⟩
    let : IsMarkovKernel (K xω) := hKM
    exact sbxS4_segmentExtension_oneIntervalKernelAt Δ R δ i P xω.1 xω.2 hP hR hδ₀ hδ₁
      hminor (K xω) hK (ν xω) hν L (g xω) hg hmap hbits
      (z₀ xω) hzero hstart (past xω) hpast hstop hsegment


/-- Any almost sure successful-path property transfers to the actual coin
restriction, including when that restriction has zero mass. -/
theorem sbxS4_firstCoinLaw_ae_success {α : Type*} [MeasurableSpace α]
    (δ : ℝ) (P B : Measure α) {p : α → Prop} (hp : ∀ᵐ x ∂B, p x) :
    ∀ᵐ q ∂sbxS4FirstCoinLaw δ P B, q.2 = true → p q.1 := by
  apply (ae_restrict_iff' (measurable_snd (measurableSet_singleton true))).mp
  have h := Measure.ae_smul_measure hp (ENNReal.ofReal δ)
  have hm := sbxS4_firstCoinLaw_restrict_map_fst δ P B true
  simp only [↓reduceIte] at hm
  rw [← hm] at h
  exact ae_of_ae_map measurable_fst.aemeasurable h

/-- The successful segment has the genuine endpoint-ball and closed-interval
support. This support transfer does not require endpoint minorization. -/
theorem sbxS4_firstSegmentLaw_ae_success_support {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (x : Vec d) (ω : FieldPair d) :
    ∀ᵐ q ∂sbxS4FirstSegmentLaw Δ R δ i P x ω, q.2 = true →
      q.1 Δ ∈ endpointBall i R x ∧
        ∀ t : ℝ≥0, t ≤ Δ → q.1 t ∈ couplingRegion i R x := by
  exact sbxS4_firstCoinLaw_ae_success δ (P (x, ω))
    (Renewal.killedBridgeMixture Δ R i P x ω)
    ((ae_killedBridgeMixture_endpoint_mem Δ R i P x ω).and
      (sbxS4_ae_killedBridgeMixture_stays Δ R i P x ω))

/-- The successful-segment support event is measurable jointly with an actual
prebridge base point. The coin is observed only in this joint event. -/
theorem sbxS4_measurableSet_success_support {α : Type*} [MeasurableSpace α]
    {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (X : α → Vec d) (hX : Measurable X) :
    MeasurableSet {q : α × (Path d × Bool) | q.2.2 = true →
      q.2.1 Δ ∈ endpointBall i R (X q.1) ∧
        ∀ t : ℝ≥0, t ≤ Δ → q.2.1 t ∈ couplingRegion i R (X q.1)} := by
  have hx : Measurable (fun q : α × (Path d × Bool) => X q.1) :=
    hX.comp measurable_fst
  have hγ : Measurable (fun q : α × (Path d × Bool) => q.2.1) :=
    measurable_fst.comp measurable_snd
  exact ((measurable_snd.comp measurable_snd) (measurableSet_singleton true)).imp
    (((measurableSet_endpointBall_pair i R).preimage
      (hx.prodMk ((continuous_eval_const Δ).measurable.comp hγ))).inter
      ((Renewal.isOpen_killedSegment_event Δ R i).measurableSet.preimage (hx.prodMk hγ)))

/-- The real base point used for a segment in the chronological extension. -/
def sbxS4SegmentBase {d : ℕ} (Δ : ℝ≥0) (z : Vec d) :
    ℕ → (ℕ → Path d × Bool) → Vec d
  | 0, _ => z
  | n + 1, s => sbxS4HistoryEndpoint Δ n (Preorder.frestrictLe n s)

section StoppingGrid

/-- An observation of the selected index and its exact stopped path/coin past.
In particular the selected bit itself is absent from this observation. -/
def sbxS4GridPastTest {d : ℕ} (Δ : ℝ≥0) (N : CoupledSample d → ℕ)
    (H : ℕ → CoupledSample d → ℝ) (q : CoupledSample d) : ℝ :=
  H (N q) (Probability.stoppedHistorySample Δ (N q) q)

/-- Countably selected measurable maps remain measurable. -/
theorem sbxS4_measurable_grid_select {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (N : α → ℕ) (hN : Measurable N)
    (f : ℕ → α → β) (hf : ∀ n, Measurable (f n)) :
    Measurable (fun q => f (N q) q) :=
  (measurable_from_prod_countable_right (f := fun p : ℕ × α => f p.1 p.2) hf).comp
    (hN.prodMk measurable_id)

/-- Exact stopping events are ambient measurable and define a measurable index. -/
theorem sbxS4_measurable_grid_index {d : ℕ} (Δ : ℝ≥0)
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n}) : Measurable N := by
  apply measurable_to_countable'
  intro n
  exact Probability.finiteHistorySigma_le Δ n _ (hN n)

/-- A bounded observation of the actual stopped sample is ambient measurable. -/
theorem sbxS4_measurable_gridPastTest {d : ℕ} (Δ : ℝ≥0)
    (N : CoupledSample d → ℕ) (hN : Measurable N)
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n)) :
    Measurable (sbxS4GridPastTest Δ N H) := by
  change Measurable (fun q => H (N q) (Probability.stoppedHistorySample Δ (N q) q))
  refine sbxS4_measurable_grid_select N hN
    (fun n q => H n (Probability.stoppedHistorySample Δ n q)) ?_
  intro n
  exact (hH n).comp ((Probability.measurable_stoppedHistorySample Δ n).mono
    (Probability.finiteHistorySigma_le Δ n) le_rfl)

/-- Restricting a stopped-history observation to its stopping event makes it
measurable for precisely the finite history before the selected bit. -/
theorem sbxS4_gridPastTest_branch_measurable {d : ℕ} (Δ : ℝ≥0)
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n)) (n : ℕ) :
    @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance
      ({q | N q = n}.indicator (sbxS4GridPastTest Δ N H)) := by
  have hm := ((hH n).comp (Probability.measurable_stoppedHistorySample Δ n)).indicator
    (hN n)
  have he : {q | N q = n}.indicator (sbxS4GridPastTest Δ N H) =
      {q | N q = n}.indicator (fun q => H n (Probability.stoppedHistorySample Δ n q)) := by
    funext q
    by_cases h : N q = n <;>
      simp only [Set.indicator, Set.mem_ofPred_eq, sbxS4GridPastTest, h, ↓reduceIte]
  rw [he]
  exact hm

/-- The same bound works on every stopped branch, including the zero branch. -/
theorem sbxS4_gridPastTest_bounded {d : ℕ} (Δ : ℝ≥0)
    (N : CoupledSample d → ℕ) (H : ℕ → CoupledSample d → ℝ)
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C) :
    BoundedRealTest (sbxS4GridPastTest Δ N H) := by
  obtain ⟨C, hC⟩ := hbH
  exact ⟨C, fun q => hC _ _⟩

/-- Bounded measurable tests stay bounded after multiplication by a stopping
branch indicator. -/
theorem sbxS4_indicator_bounded {α : Type*} (s : Set α) (H : α → ℝ)
    (hbH : BoundedRealTest H) : BoundedRealTest (s.indicator H) := by
  obtain ⟨C, hC⟩ := hbH
  refine ⟨max C 0, fun q => ?_⟩
  by_cases h : q ∈ s
  · simpa only [Set.indicator_of_mem h] using (hC q).trans (le_max_left _ _)
  · simp only [Set.indicator_of_notMem h, abs_zero]
    exact le_max_right _ _

/-- A finite grid selection decomposes into its finitely many branches. -/
theorem sbxS4_integral_bounded_grid {α : Type*} [MeasurableSpace α]
    (η : Measure α) (N : α → ℕ) (hN : Measurable N) (M : ℕ)
    (hM : ∀ q, N q ≤ M) (f : α → ℝ) (hf : Integrable f η) :
    (∫ q, f q ∂η) = ∑ n ∈ Finset.range (M + 1), ∫ q in {q | N q = n}, f q ∂η := by
  have hm (n : ℕ) : MeasurableSet {q | N q = n} := hN (measurableSet_singleton n)
  have he : f = fun q => ∑ n ∈ Finset.range (M + 1),
      {q | N q = n}.indicator f q := by
    funext q
    symm
    calc
      _ = {r | N r = N q}.indicator f q := Finset.sum_eq_single (N q) ?_ ?_
      _ = _ := by simp only [Set.indicator, Set.mem_ofPred_eq, ↓reduceIte]
    · intro n _ hn
      have hne : ¬N q = n := Ne.symm hn
      simp only [Set.indicator, Set.mem_ofPred_eq, hne, ↓reduceIte]
    · intro h
      exact (h (Finset.mem_range.mpr (Nat.lt_succ_of_le (hM q)))).elim
  conv_lhs => rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _
    exact integral_indicator (hm n)
  · intro n _
    exact hf.indicator (hm n)

/-- Countable stopping branches have a genuine convergent integral sum. -/
theorem sbxS4_hasSum_integral_grid {α : Type*} [MeasurableSpace α]
    (η : Measure α) (N : α → ℕ) (hN : Measurable N)
    (f : α → ℝ) (hf : Integrable f η) :
    HasSum (fun n => ∫ q in {q | N q = n}, f q ∂η) (∫ q, f q ∂η) := by
  have hm (n : ℕ) : MeasurableSet {q | N q = n} := hN (measurableSet_singleton n)
  have hd : Pairwise (fun n m => Disjoint {q | N q = n} {q | N q = m}) := by
    intro n m hnm
    exact Set.disjoint_left.mpr (fun q hn hm => hnm (hn.symm.trans hm))
  have hu : (⋃ n : ℕ, {q | N q = n}) = Set.univ := by
    ext q
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨N q, rfl⟩
  have hs := hasSum_integral_iUnion hm hd (hf.integrableOn (s := ⋃ n, {q | N q = n}))
  simpa only [hu, Measure.restrict_univ] using hs

/-- Equality on every stopping branch lifts to equality of the full integrals;
the summability is supplied by actual global integrability. -/
theorem sbxS4_integral_grid_transfer {α : Type*} [MeasurableSpace α]
    (η : Measure α) (N : α → ℕ) (hN : Measurable N)
    (f g : α → ℝ) (hf : Integrable f η) (hg : Integrable g η)
    (hbranch : ∀ n, (∫ q in {q | N q = n}, f q ∂η) =
      ∫ q in {q | N q = n}, g q ∂η) :
    (∫ q, f q ∂η) = ∫ q, g q ∂η := by
  have hs := sbxS4_hasSum_integral_grid η N hN f hf
  simp_rw [hbranch] at hs
  exact hs.unique (sbxS4_hasSum_integral_grid η N hN g hg)

/-- Countable transport of deterministic past-test identities. The hypotheses
require the actual selected integrands to be integrable, before summing. -/
theorem sbxS4_integral_grid_test_transfer {d : ℕ}
    (η : Measure (CoupledSample d)) (N : CoupledSample d → ℕ) (hN : Measurable N)
    (A : CoupledSample d → ℝ) (f g : ℕ → CoupledSample d → ℝ)
    (hf : Integrable (fun q => A q * f (N q) q) η)
    (hg : Integrable (fun q => A q * g (N q) q) η)
    (hbranch : ∀ n, (∫ q, {q | N q = n}.indicator A q * f n q ∂η) =
      ∫ q, {q | N q = n}.indicator A q * g n q ∂η) :
    (∫ q, A q * f (N q) q ∂η) = ∫ q, A q * g (N q) q ∂η := by
  apply sbxS4_integral_grid_transfer η N hN _ _ hf hg
  intro n
  have hm : MeasurableSet {q | N q = n} := hN (measurableSet_singleton n)
  calc
    _ = ∫ q, {q | N q = n}.indicator A q * f n q ∂η := by
      rw [← integral_indicator hm]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by
        by_cases h : N q = n <;> simp only [Set.indicator, Set.mem_ofPred_eq, h,
          ↓reduceIte, zero_mul]
    _ = _ := hbranch n
    _ = _ := by
      rw [← integral_indicator hm]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by
        by_cases h : N q = n <;> simp only [Set.indicator, Set.mem_ofPred_eq, h,
          ↓reduceIte, zero_mul]

/-- The literal fresh-bit identity at an arbitrary natural-valued stopping
index, derived by disjoint branch decomposition of the deterministic identity. -/
theorem sbxS4_freshBitsAt_stoppingGrid {d : ℕ} (Δ : ℝ≥0) (δ : ℝ)
    (L : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    [IsFiniteMeasure (L xω)] (hfresh : FreshBitsAt Δ δ L xω)
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C) :
    Integrable (sbxS4GridPastTest Δ N H) (L xω) ∧
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0)) (L xω) ∧
    (∫ q, sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) ∂L xω) =
      δ * ∫ q, sbxS4GridPastTest Δ N H q ∂L xω := by
  have hNm := sbxS4_measurable_grid_index Δ N hN
  have hA := sbxS4_measurable_gridPastTest Δ N hNm H hH
  have hbA := sbxS4_gridPastTest_bounded Δ N H hbH
  obtain ⟨C, hC⟩ := hbA
  have hi : Integrable (sbxS4GridPastTest Δ N H) (L xω) :=
    Integrable.of_bound hA.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun q => (hC q : |sbxS4GridPastTest Δ N H q| ≤ C))
  have hc : Measurable (fun q : CoupledSample d =>
      if q.2 (N q) = true then (1 : ℝ) else 0) := by
    refine sbxS4_measurable_grid_select N hNm
      (fun n q => if q.2 n = true then (1 : ℝ) else 0) ?_
    intro n
    exact (measurable_of_finite (fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
      ((measurable_pi_apply n).comp measurable_snd)
  have hip := hi.mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => show
      ‖if q.2 (N q) = true then (1 : ℝ) else 0‖ ≤ 1 from by split <;> norm_num)
  refine ⟨hi, hip, ?_⟩
  rw [mul_comm δ, ← integral_mul_const]
  apply sbxS4_integral_grid_test_transfer (L xω) N hNm _
    (fun n q => if q.2 n = true then (1 : ℝ) else 0) (fun _ _ => δ) hip (hi.mul_const δ)
  intro n
  rw [integral_mul_const, mul_comm]
  exact hfresh n _ (sbxS4_gridPastTest_branch_measurable Δ N hN H hH n)
    (sbxS4_indicator_bounded _ _ ⟨C, hC⟩)

/-- Almost surely finite extended grid indices also give a convergent branch
sum. The exceptional infinite-index event is discarded only by its proved
nullity, and no branch at infinity is folded into the time-zero history. -/
theorem sbxS4_hasSum_integral_grid_ae {α : Type*} [MeasurableSpace α]
    (η : Measure α) (T : α → WithTop ℕ)
    (hT : ∀ n : ℕ, MeasurableSet {q | T q = n})
    (hfinite : ∀ᵐ q ∂η, ∃ n : ℕ, T q = n)
    (f : α → ℝ) (hf : Integrable f η) :
    HasSum (fun n : ℕ => ∫ q in {q | T q = n}, f q ∂η) (∫ q, f q ∂η) := by
  have hd : Pairwise (fun n m : ℕ => Disjoint {q | T q = n} {q | T q = m}) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro q hn hm
    exact hnm (WithTop.coe_injective (hn.symm.trans hm))
  have hu : ∀ᵐ q ∂η, q ∈ ⋃ n : ℕ, {q | T q = n} := by
    simpa only [Set.mem_iUnion, Set.mem_ofPred_eq] using hfinite
  have hs := hasSum_integral_iUnion hT hd
    (hf.integrableOn (s := ⋃ n : ℕ, {q | T q = n}))
  rwa [Measure.restrict_eq_self_of_ae_mem hu] at hs

/-- AE-finite stopping branches transport integral identities without any
claim about the value or history of the exceptional infinite-index event. -/
theorem sbxS4_integral_grid_transfer_ae {α : Type*} [MeasurableSpace α]
    (η : Measure α) (T : α → WithTop ℕ)
    (hT : ∀ n : ℕ, MeasurableSet {q | T q = n})
    (hfinite : ∀ᵐ q ∂η, ∃ n : ℕ, T q = n)
    (f g : α → ℝ) (hf : Integrable f η) (hg : Integrable g η)
    (hbranch : ∀ n : ℕ, (∫ q in {q | T q = n}, f q ∂η) =
      ∫ q in {q | T q = n}, g q ∂η) :
    (∫ q, f q ∂η) = ∫ q, g q ∂η := by
  have hs := sbxS4_hasSum_integral_grid_ae η T hT hfinite f hf
  simp_rw [hbranch] at hs
  exact hs.unique (sbxS4_hasSum_integral_grid_ae η T hT hfinite g hg)

/-- A total representative of an extended grid index; its value on infinity
is used only on the explicitly discarded null event. -/
def sbxS4ExtendedGridIndex {α : Type*} (T : α → WithTop ℕ) (q : α) : ℕ :=
  (T q).untopD 0

/-- The finite representative of a measurable extended index is measurable. -/
theorem sbxS4_measurable_extendedGridIndex {α : Type*} [MeasurableSpace α]
    (T : α → WithTop ℕ) (hT : Measurable T) : Measurable (sbxS4ExtendedGridIndex T) :=
  (measurable_of_countable (fun n : WithTop ℕ => n.untopD 0)).comp hT

/-- On a finite stopping event the total representative retains precisely the
finite past, even if the extended index can be infinite elsewhere. -/
theorem sbxS4_extendedGridPastTest_branch_measurable {d : ℕ} (Δ : ℝ≥0)
    (T : CoupledSample d → WithTop ℕ)
    (hT : ∀ n : ℕ, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | T q = n})
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n)) (n : ℕ) :
    @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance
      ({q | T q = n}.indicator (sbxS4GridPastTest Δ (sbxS4ExtendedGridIndex T) H)) := by
  have hm := ((hH n).comp (Probability.measurable_stoppedHistorySample Δ n)).indicator
    (hT n)
  have he : {q | T q = n}.indicator (sbxS4GridPastTest Δ (sbxS4ExtendedGridIndex T) H) =
      {q | T q = n}.indicator (fun q => H n (Probability.stoppedHistorySample Δ n q)) := by
    funext q
    by_cases h : T q = n
    · have hidx : sbxS4ExtendedGridIndex T q = n := by
        dsimp only [sbxS4ExtendedGridIndex]
        rw [h]
        rfl
      simp only [Set.indicator, Set.mem_ofPred_eq, h, ↓reduceIte, sbxS4GridPastTest, hidx]
    · simp only [Set.indicator, Set.mem_ofPred_eq, h, ↓reduceIte]
  rw [he]
  exact hm

/-- AE-finite transport of deterministic test identities. Every finite branch
uses its original index, and no infinite event is assigned to branch zero. -/
theorem sbxS4_integral_grid_test_transfer_ae {d : ℕ}
    (η : Measure (CoupledSample d)) (T : CoupledSample d → WithTop ℕ)
    (hT : ∀ n : ℕ, MeasurableSet {q | T q = n})
    (hfinite : ∀ᵐ q ∂η, ∃ n : ℕ, T q = n)
    (A : CoupledSample d → ℝ) (f g : ℕ → CoupledSample d → ℝ)
    (hf : Integrable (fun q => A q * f (sbxS4ExtendedGridIndex T q) q) η)
    (hg : Integrable (fun q => A q * g (sbxS4ExtendedGridIndex T q) q) η)
    (hbranch : ∀ n : ℕ, (∫ q, {q | T q = n}.indicator A q * f n q ∂η) =
      ∫ q, {q | T q = n}.indicator A q * g n q ∂η) :
    (∫ q, A q * f (sbxS4ExtendedGridIndex T q) q ∂η) =
      ∫ q, A q * g (sbxS4ExtendedGridIndex T q) q ∂η := by
  apply sbxS4_integral_grid_transfer_ae η T hT hfinite _ _ hf hg
  intro n
  calc
    _ = ∫ q, {q | T q = n}.indicator A q * f n q ∂η := by
      rw [← integral_indicator (hT n)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by
        by_cases h : T q = n
        · have hidx : sbxS4ExtendedGridIndex T q = n := by
            dsimp only [sbxS4ExtendedGridIndex]
            rw [h]
            rfl
          simp only [Set.indicator, Set.mem_ofPred_eq, h, ↓reduceIte, hidx]
        · simp only [Set.indicator, Set.mem_ofPred_eq, h, ↓reduceIte, zero_mul]
    _ = _ := hbranch n
    _ = _ := by
      rw [← integral_indicator (hT n)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by
        by_cases h : T q = n
        · have hidx : sbxS4ExtendedGridIndex T q = n := by
            dsimp only [sbxS4ExtendedGridIndex]
            rw [h]
            rfl
          simp only [Set.indicator, Set.mem_ofPred_eq, h, ↓reduceIte, hidx]
        · simp only [Set.indicator, Set.mem_ofPred_eq, h, ↓reduceIte, zero_mul]

/-- The fresh selected bit at an almost surely finite extended stopping index. -/
theorem sbxS4_freshBitsAt_stoppingGrid_ae {d : ℕ} (Δ : ℝ≥0) (δ : ℝ)
    (L : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    [IsFiniteMeasure (L xω)] (hfresh : FreshBitsAt Δ δ L xω)
    (T : CoupledSample d → WithTop ℕ) (hTm : Measurable T)
    (hT : ∀ n : ℕ, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | T q = n})
    (hfinite : ∀ᵐ q ∂L xω, ∃ n : ℕ, T q = n)
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C) :
    let N := sbxS4ExtendedGridIndex T
    Integrable (sbxS4GridPastTest Δ N H) (L xω) ∧
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0)) (L xω) ∧
    (∫ q, sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) ∂L xω) =
      δ * ∫ q, sbxS4GridPastTest Δ N H q ∂L xω := by
  let N := sbxS4ExtendedGridIndex T
  have hNm : Measurable N := sbxS4_measurable_extendedGridIndex T hTm
  have hA := sbxS4_measurable_gridPastTest Δ N hNm H hH
  have hbA := sbxS4_gridPastTest_bounded Δ N H hbH
  obtain ⟨C, hC⟩ := hbA
  have hi : Integrable (sbxS4GridPastTest Δ N H) (L xω) :=
    Integrable.of_bound hA.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun q => (hC q : |sbxS4GridPastTest Δ N H q| ≤ C))
  have hc : Measurable (fun q : CoupledSample d =>
      if q.2 (N q) = true then (1 : ℝ) else 0) := by
    refine sbxS4_measurable_grid_select N hNm
      (fun n q => if q.2 n = true then (1 : ℝ) else 0) ?_
    intro n
    exact (measurable_of_finite (fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
      ((measurable_pi_apply n).comp measurable_snd)
  have hip := hi.mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => show
      ‖if q.2 (N q) = true then (1 : ℝ) else 0‖ ≤ 1 from by split <;> norm_num)
  refine ⟨hi, hip, ?_⟩
  rw [mul_comm δ, ← integral_mul_const]
  apply sbxS4_integral_grid_test_transfer_ae (L xω) T
    (fun n => Probability.finiteHistorySigma_le Δ n _ (hT n)) hfinite _
    (fun n q => if q.2 n = true then (1 : ℝ) else 0) (fun _ _ => δ) hip (hi.mul_const δ)
  intro n
  rw [integral_mul_const, mul_comm]
  exact hfresh n _ (sbxS4_extendedGridPastTest_branch_measurable Δ T hT H hH n)
    (sbxS4_indicator_bounded _ _ ⟨C, hC⟩)

/-- The two actual killed-bridge/residual identities at a selected grid index,
with integrability of every term and the original endpoint and shifted path. -/
def sbxS4GridIntervalTest {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (L : CoupledQuenchedLaws d)
    (xω : Vec d × FieldPair d) (N : CoupledSample d → ℕ)
    (A : CoupledSample d → ℝ) (F : Path d → ℝ) : Prop :=
  Integrable (fun q => A q * (∫ γ, F γ ∂P (q.1 ((N q : ℝ≥0) * Δ), xω.2))) (L xω) ∧
  Integrable (fun q => A q * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
    (q.1 ((N q : ℝ≥0) * Δ)) xω.2)) (L xω) ∧
  ∀ b : Bool,
    Integrable (fun q => A q * (if q.2 (N q) = b then (1 : ℝ) else 0) *
      F (pathTimeShift q.1 ((N q : ℝ≥0) * Δ))) (L xω) ∧
    Integrable (fun q => A q * (if b then δ *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (q.1 ((N q : ℝ≥0) * Δ)) xω.2)
      else (∫ γ, F γ ∂P (q.1 ((N q : ℝ≥0) * Δ), xω.2)) - δ *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
          (q.1 ((N q : ℝ≥0) * Δ)) xω.2))) (L xω) ∧
    (∫ q, A q * (if q.2 (N q) = b then (1 : ℝ) else 0) *
      F (pathTimeShift q.1 ((N q : ℝ≥0) * Δ)) ∂L xω) =
      ∫ q, A q * (if b then δ *
          (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
            (q.1 ((N q : ℝ≥0) * Δ)) xω.2)
        else (∫ γ, F γ ∂P (q.1 ((N q : ℝ≥0) * Δ), xω.2)) - δ *
          (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
            (q.1 ((N q : ℝ≥0) * Δ)) xω.2)) ∂L xω

/-- The source endpoint average is exactly integration against conditional
Lebesgue measure, with its original Euclidean ball and real normalization. -/
theorem sbxS4_integral_cond_endpointBall {d : ℕ}
    (i : Fin d) (R : ℝ) (x : Vec d) (φ : Vec d → ℝ) :
    (∫ y, φ y ∂cond (volume : Measure (Vec d)) (endpointBall i R x)) =
      endpointAverage i R x φ := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
  simp only [endpointAverage, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The actual bridge endpoint has the source endpoint average for every
bounded signed measurable observation. -/
theorem sbxS4_integral_killedBridgeMixture_endpoint {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (x : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (x, ω))]
    (hR : 0 < R) (hδ : 0 < δ)
    (hminor : ENNReal.ofReal δ • cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (φ : Vec d → ℝ) (hφ : Measurable φ) :
    (∫ γ, φ (γ Δ) ∂Renewal.killedBridgeMixture Δ R i P x ω) =
      endpointAverage i R x φ := by
  rw [← integral_map (continuous_eval_const Δ).measurable.aemeasurable
    hφ.aestronglyMeasurable,
    sbxS4_map_killedBridgeMixture_endpoint Δ R δ i P x ω hR hδ hminor]
  exact sbxS4_integral_cond_endpointBall i R x φ

/-- All source ball normalizations are positive finite real numbers. -/
theorem sbxS4_endpointBall_normalization {d : ℕ}
    (i : Fin d) (R : ℝ) (hR : 0 < R) (x : Vec d) :
    0 < volume (endpointBall i R x) ∧
    volume (endpointBall i R x) ≠ ∞ ∧
    0 < (volume (endpointBall i R x)).toReal :=
  ⟨endpointBall_volume_pos i R hR x, endpointBall_volume_ne_top i R hR x,
    ENNReal.toReal_pos (endpointBall_volume_pos i R hR x).ne'
      (endpointBall_volume_ne_top i R hR x)⟩

/-- Indicator endpoint averages are literal Euclidean volume ratios;
intersecting with the source ball handles all zero-mass branches. -/
theorem sbxS4_endpointAverage_indicator {d : ℕ}
    (i : Fin d) (R : ℝ) (x : Vec d) (S : Set (Vec d)) (hS : MeasurableSet S) :
    endpointAverage i R x (S.indicator (fun _ => (1 : ℝ))) =
      (volume (S ∩ endpointBall i R x)).toReal /
        (volume (endpointBall i R x)).toReal := by
  rw [endpointAverage, integral_indicator_const (1 : ℝ) hS,
    measureReal_restrict_apply hS, smul_eq_mul, mul_one]
  rfl

/-- A contained measurable endpoint target has its own volume in the numerator.
Containment is required; nonzero mass alone gives no uniform no-return bound. -/
theorem sbxS4_endpointAverage_indicator_of_subset {d : ℕ}
    (i : Fin d) (R : ℝ) (x : Vec d) (S : Set (Vec d)) (hS : MeasurableSet S)
    (hsub : S ⊆ endpointBall i R x) :
    endpointAverage i R x (S.indicator (fun _ => (1 : ℝ))) =
      (volume S).toReal / (volume (endpointBall i R x)).toReal := by
  rw [sbxS4_endpointAverage_indicator i R x S hS, Set.inter_eq_left.mpr hsub]

/-- The actual endpoint normalization sends the constant test to one. -/
theorem sbxS4_endpointAverage_one {d : ℕ} (i : Fin d) (R : ℝ) (hR : 0 < R)
    (x : Vec d) : endpointAverage i R x (fun _ => (1 : ℝ)) = 1 := by
  have h := sbxS4_endpointAverage_indicator i R x Set.univ MeasurableSet.univ
  simpa only [Set.indicator_univ, Set.univ_inter,
    div_self (sbxS4_endpointBall_normalization i R hR x).2.2.ne'] using h

/-- Positive homotheties scale the actual Euclidean endpoint balls. -/
theorem sbxS4_endpointBall_smul {d : ℕ} (i : Fin d) (R c : ℝ) (hc : 0 < c) :
    endpointBall i (c * R) 0 = c • endpointBall i R 0 := by
  have hm (v : Vec d) : c • v ∈ endpointBall i (c * R) 0 ↔
      v ∈ endpointBall i R 0 := by
    change euclideanNorm (c • v - (0 + (9 * (c * R)) • unitVector i)) < c * R ↔
      euclideanNorm (v - (0 + (9 * R) • unitVector i)) < R
    have he : c • v - (0 + (9 * (c * R)) • unitVector i) =
        c • (v - (0 + (9 * R) • unitVector i)) := by
      simp only [zero_add, smul_sub, smul_smul]
      congr 2
      ring
    rw [he, EinsteinRelation.TimeChange.euclideanNorm_smul, abs_of_pos hc,
      mul_lt_mul_iff_right₀ hc]
  ext y
  constructor
  · intro hy
    refine ⟨c⁻¹ • y, (hm _).mp ?_, smul_inv_smul₀ hc.ne' y⟩
    simpa only [smul_inv_smul₀ hc.ne'] using hy
  · rintro ⟨v, hv, rfl⟩
    exact (hm v).mpr hv

/-- Lebesgue volume scales with the genuine Euclidean dimension. -/
theorem sbxS4_endpointBall_volume_scale {d : ℕ} (i : Fin d) (R c : ℝ) (hc : 0 < c) :
    volume (endpointBall i (c * R) 0) =
      ENNReal.ofReal (c ^ d) * volume (endpointBall i R 0) := by
  rw [sbxS4_endpointBall_smul i R c hc, Measure.addHaar_smul_of_nonneg volume hc.le]
  simp only [Vec, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The exact real volume ratio of two source Euclidean endpoint balls;
translation of either center does not change the ratio. -/
theorem sbxS4_endpointBall_volume_ratio {d : ℕ} (i : Fin d) (R ρ : ℝ)
    (hR : 0 < R) (hρ : 0 < ρ) (x y : Vec d) :
    (volume (endpointBall i ρ y)).toReal / (volume (endpointBall i R x)).toReal =
      (ρ / R) ^ d := by
  have hv := sbxS4_endpointBall_volume_scale i R (ρ / R) (div_pos hρ hR)
  rw [div_mul_cancel₀ _ hR.ne'] at hv
  rw [endpointBall_volume_eq i ρ y, endpointBall_volume_eq i R x, hv,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (div_pos hρ hR).le _)]
  exact mul_div_cancel_right₀ _ (sbxS4_endpointBall_normalization i R hR 0).2.2.ne'

/-- A concentric smaller Euclidean ball lies in the source endpoint ball. -/
theorem sbxS4_endpointSubball_subset {d : ℕ} (i : Fin d) (R ρ : ℝ) (x : Vec d)
    (hρR : ρ ≤ R) :
    endpointBall i ρ (x + (9 * (R - ρ)) • unitVector i) ⊆ endpointBall i R x := by
  have he : x + (9 * (R - ρ)) • unitVector i + (9 * ρ) • unitVector i =
      x + (9 * R) • unitVector i := by
    rw [add_assoc, ← add_smul]
    congr 2
    ring
  intro y hy
  change euclideanNorm (y - (x + (9 * (R - ρ)) • unitVector i +
    (9 * ρ) • unitVector i)) < ρ at hy
  rw [he] at hy
  exact hy.trans_le hρR

/-- An actual contained endpoint subball has its Euclidean power-law mass. -/
theorem sbxS4_endpointAverage_subball {d : ℕ} (i : Fin d) (R ρ : ℝ)
    (hR : 0 < R) (hρ : 0 < ρ) (x y : Vec d)
    (hsub : endpointBall i ρ y ⊆ endpointBall i R x) :
    endpointAverage i R x ((endpointBall i ρ y).indicator (fun _ => (1 : ℝ))) =
      (ρ / R) ^ d := by
  have hm : MeasurableSet (endpointBall i ρ y) :=
    (measurableSet_endpointBall_pair i ρ).preimage (measurable_const.prodMk measurable_id)
  exact (sbxS4_endpointAverage_indicator_of_subset i R x (endpointBall i ρ y) hm hsub).trans
    (sbxS4_endpointBall_volume_ratio i R ρ hR hρ x y)

/-- The checked grid split identity implies the joint successful-coin/endpoint
identity against the actual bounded prebridge test. -/
theorem sbxS4_gridInterval_successful_endpoint {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (L : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    (hP : ∀ x, IsProbabilityMeasure (P (x, xω.2)))
    (hR : 0 < R) (hδ : 0 < δ)
    (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
      (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x xω.2).map (fun γ : Path d => γ Δ))
    (N : CoupledSample d → ℕ) (A : CoupledSample d → ℝ)
    (φ : Vec d → ℝ) (hφ : Measurable φ)
    (hI : sbxS4GridIntervalTest Δ δ R i P L xω N A (fun γ => φ (γ Δ))) :
    Integrable (fun q => A q * (if q.2 (N q) = true then (1 : ℝ) else 0) *
      φ (q.1 ((N q : ℝ≥0) * Δ + Δ))) (L xω) ∧
    Integrable (fun q => A q * endpointAverage i R (q.1 ((N q : ℝ≥0) * Δ)) φ) (L xω) ∧
    (∫ q, A q * (if q.2 (N q) = true then (1 : ℝ) else 0) *
      φ (q.1 ((N q : ℝ≥0) * Δ + Δ)) ∂L xω) =
      δ * (∫ q, A q * endpointAverage i R (q.1 ((N q : ℝ≥0) * Δ)) φ ∂L xω) := by
  have he (x : Vec d) : (∫ γ, φ (γ Δ)
      ∂Renewal.killedBridgeMixture Δ R i P x xω.2) = endpointAverage i R x φ := by
    let : IsProbabilityMeasure (P (x, xω.2)) := hP x
    exact sbxS4_integral_killedBridgeMixture_endpoint Δ R δ i P x xω.2 hR hδ
      (hminor x) φ hφ
  obtain ⟨_, hi, hb⟩ := hI
  have ht := hb true
  simp only [he] at hi
  refine ⟨ht.1, hi, ?_⟩
  calc
    _ = ∫ q, A q * (δ * endpointAverage i R (q.1 ((N q : ℝ≥0) * Δ)) φ) ∂L xω := by
      simpa only [↓reduceIte, he, pathTimeShift, ContinuousMap.coe_mk] using ht.2.2
    _ = δ * (∫ q, A q * endpointAverage i R (q.1 ((N q : ℝ≥0) * Δ)) φ ∂L xω) := by
      rw [← integral_const_mul]
      congr 1
      funext q
      ring

/-- The selected success event has the genuine source probability delta.
In particular the normalization is positive and finite. -/
theorem sbxS4_gridInterval_success_mass {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (L : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    [IsProbabilityMeasure (L xω)]
    (hP : ∀ x, IsProbabilityMeasure (P (x, xω.2)))
    (hR : 0 < R) (hδ : 0 < δ)
    (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
      (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x xω.2).map (fun γ : Path d => γ Δ))
    (N : CoupledSample d → ℕ) (hN : Measurable N)
    (hI : sbxS4GridIntervalTest Δ δ R i P L xω N (fun _ => 1) (fun _ => 1)) :
    L xω {q | q.2 (N q) = true} = ENNReal.ofReal δ ∧
      0 < L xω {q | q.2 (N q) = true} ∧ L xω {q | q.2 (N q) = true} ≠ ∞ := by
  have hm : MeasurableSet {q : CoupledSample d | q.2 (N q) = true} :=
    (sbxS4_measurable_grid_select N hN (fun n q => q.2 n)
      (fun n => (measurable_pi_apply n).comp measurable_snd)) (measurableSet_singleton true)
  have h := sbxS4_gridInterval_successful_endpoint Δ R δ i P L xω hP hR hδ
    hminor N (fun _ => 1) (fun _ => 1) measurable_const hI
  have hi : (∫ q, if q.2 (N q) = true then (1 : ℝ) else 0 ∂L xω) = δ := by
    simpa only [one_mul, mul_one, sbxS4_endpointAverage_one i R hR,
      integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using h.2.2
  have hv : (L xω {q | q.2 (N q) = true}).toReal = δ := by
    have hi' : (∫ q, {q : CoupledSample d | q.2 (N q) = true}.indicator
        (fun _ => (1 : ℝ)) q ∂L xω) = δ := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hi
    simpa only [integral_indicator_const (1 : ℝ) hm, smul_eq_mul, mul_one, Measure.real] using hi'
  have he : L xω {q | q.2 (N q) = true} = ENNReal.ofReal δ := by
    rw [← hv, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine ⟨he, ?_, measure_ne_top _ _⟩
  rw [he]
  exact ENNReal.ofReal_pos.mpr hδ

/-- Conditioning on the actual selected success event cancels exactly the
positive source delta. The right side keeps the actual prebridge position. -/
theorem sbxS4_gridInterval_cond_successful_endpoint {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (L : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    [IsProbabilityMeasure (L xω)]
    (hP : ∀ x, IsProbabilityMeasure (P (x, xω.2)))
    (hR : 0 < R) (hδ : 0 < δ)
    (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
      (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x xω.2).map (fun γ : Path d => γ Δ))
    (N : CoupledSample d → ℕ) (hN : Measurable N)
    (hIone : sbxS4GridIntervalTest Δ δ R i P L xω N (fun _ => 1) (fun _ => 1))
    (A : CoupledSample d → ℝ) (φ : Vec d → ℝ) (hφ : Measurable φ)
    (hI : sbxS4GridIntervalTest Δ δ R i P L xω N A (fun γ => φ (γ Δ))) :
    (∫ q, A q * φ (q.1 ((N q : ℝ≥0) * Δ + Δ))
      ∂cond (L xω) {q | q.2 (N q) = true}) =
        ∫ q, A q * endpointAverage i R (q.1 ((N q : ℝ≥0) * Δ)) φ ∂L xω := by
  have hm : MeasurableSet {q : CoupledSample d | q.2 (N q) = true} :=
    (sbxS4_measurable_grid_select N hN (fun n q => q.2 n)
      (fun n => (measurable_pi_apply n).comp measurable_snd)) (measurableSet_singleton true)
  have hmass := (sbxS4_gridInterval_success_mass Δ R δ i P L xω hP hR hδ
    hminor N hN hIone).1
  have h := sbxS4_gridInterval_successful_endpoint Δ R δ i P L xω hP hR hδ
    hminor N A φ hφ hI
  have hi : (∫ q in {q : CoupledSample d | q.2 (N q) = true},
      A q * φ (q.1 ((N q : ℝ≥0) * Δ + Δ)) ∂L xω) =
        δ * (∫ q, A q * endpointAverage i R (q.1 ((N q : ℝ≥0) * Δ)) φ ∂L xω) := by
    rw [← integral_indicator hm]
    convert h.2.2 using 1
    congr 1
    funext q
    by_cases hb : q.2 (N q) = true <;> simp [Set.indicator, hb]
  rw [ProbabilityTheory.cond, integral_smul_measure, hmass, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hδ.le, hi, smul_eq_mul, inv_mul_cancel_left₀ hδ.ne']

/-- The selected successful mass of a contained Euclidean subball has the
literal dimension-dependent volume ratio. The containment is required at the
actual prebridge locations, without any no-return conclusion. -/
theorem sbxS4_gridInterval_successful_subball {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (L : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    (hP : ∀ x, IsProbabilityMeasure (P (x, xω.2)))
    (hR : 0 < R) (hδ : 0 < δ)
    (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
      (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x xω.2).map (fun γ : Path d => γ Δ))
    (N : CoupledSample d → ℕ) (A : CoupledSample d → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) (y : Vec d)
    (hsub : ∀ᵐ q ∂L xω,
      endpointBall i ρ y ⊆ endpointBall i R (q.1 ((N q : ℝ≥0) * Δ)))
    (hI : sbxS4GridIntervalTest Δ δ R i P L xω N A
      (fun γ => (endpointBall i ρ y).indicator (fun _ => (1 : ℝ)) (γ Δ))) :
    Integrable (fun q => A q * (if q.2 (N q) = true then (1 : ℝ) else 0) *
      (endpointBall i ρ y).indicator (fun _ => (1 : ℝ))
        (q.1 ((N q : ℝ≥0) * Δ + Δ))) (L xω) ∧
    Integrable (fun q => A q * (ρ / R) ^ d) (L xω) ∧
    (∫ q, A q * (if q.2 (N q) = true then (1 : ℝ) else 0) *
      (endpointBall i ρ y).indicator (fun _ => (1 : ℝ))
        (q.1 ((N q : ℝ≥0) * Δ + Δ)) ∂L xω) =
      δ * (∫ q, A q * (ρ / R) ^ d ∂L xω) := by
  have h := sbxS4_gridInterval_successful_endpoint Δ R δ i P L xω hP hR hδ
    hminor N A ((endpointBall i ρ y).indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator ((measurableSet_endpointBall_pair i ρ).preimage
      (measurable_const.prodMk measurable_id))) hI
  have he : ∀ᵐ q ∂L xω, A q * endpointAverage i R (q.1 ((N q : ℝ≥0) * Δ))
      ((endpointBall i ρ y).indicator (fun _ => (1 : ℝ))) = A q * (ρ / R) ^ d := by
    filter_upwards [hsub] with q hq
    rw [sbxS4_endpointAverage_subball i R ρ hR hρ _ y hq]
  refine ⟨h.1, h.2.1.congr he, ?_⟩
  rw [h.2.2, integral_congr_ae he]

/-- Conditional probability of a contained endpoint subball at the selected
successful trial, with the genuine Euclidean volume ratio. -/
theorem sbxS4_gridInterval_cond_successful_subball {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (L : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    [IsProbabilityMeasure (L xω)]
    (hP : ∀ x, IsProbabilityMeasure (P (x, xω.2)))
    (hR : 0 < R) (hδ : 0 < δ)
    (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
      (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x xω.2).map (fun γ : Path d => γ Δ))
    (N : CoupledSample d → ℕ) (hN : Measurable N)
    (hIone : sbxS4GridIntervalTest Δ δ R i P L xω N (fun _ => 1) (fun _ => 1))
    (ρ : ℝ) (hρ : 0 < ρ) (y : Vec d)
    (hsub : ∀ᵐ q ∂L xω,
      endpointBall i ρ y ⊆ endpointBall i R (q.1 ((N q : ℝ≥0) * Δ)))
    (hI : sbxS4GridIntervalTest Δ δ R i P L xω N (fun _ => 1)
      (fun γ => (endpointBall i ρ y).indicator (fun _ => (1 : ℝ)) (γ Δ))) :
    (∫ q, (endpointBall i ρ y).indicator (fun _ => (1 : ℝ))
      (q.1 ((N q : ℝ≥0) * Δ + Δ))
      ∂cond (L xω) {q | q.2 (N q) = true}) = (ρ / R) ^ d := by
  have h := sbxS4_gridInterval_cond_successful_endpoint Δ R δ i P L xω hP hR hδ
    hminor N hN hIone (fun _ => 1)
    ((endpointBall i ρ y).indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator ((measurableSet_endpointBall_pair i ρ).preimage
      (measurable_const.prodMk measurable_id))) hI
  have he : ∀ᵐ q ∂L xω,
      endpointAverage i R (q.1 ((N q : ℝ≥0) * Δ))
        ((endpointBall i ρ y).indicator (fun _ => (1 : ℝ))) = (ρ / R) ^ d := by
    filter_upwards [hsub] with q hq
    exact sbxS4_endpointAverage_subball i R ρ hR hρ _ y hq
  simpa only [one_mul, integral_congr_ae he, integral_const, Measure.real,
    measure_univ, ENNReal.toReal_one, one_smul] using h

/-- The conditional law assigns the stated probability to the actual
selected endpoint lying in a contained Euclidean subball. -/
theorem sbxS4_gridInterval_cond_successful_subball_probability {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (L : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    [IsProbabilityMeasure (L xω)]
    (hP : ∀ x, IsProbabilityMeasure (P (x, xω.2)))
    (hR : 0 < R) (hδ : 0 < δ)
    (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
      (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x xω.2).map (fun γ : Path d => γ Δ))
    (N : CoupledSample d → ℕ) (hN : Measurable N)
    (hIone : sbxS4GridIntervalTest Δ δ R i P L xω N (fun _ => 1) (fun _ => 1))
    (ρ : ℝ) (hρ : 0 < ρ) (y : Vec d)
    (hsub : ∀ᵐ q ∂L xω,
      endpointBall i ρ y ⊆ endpointBall i R (q.1 ((N q : ℝ≥0) * Δ)))
    (hI : sbxS4GridIntervalTest Δ δ R i P L xω N (fun _ => 1)
      (fun γ => (endpointBall i ρ y).indicator (fun _ => (1 : ℝ)) (γ Δ))) :
    (cond (L xω) {q | q.2 (N q) = true}
      {q | q.1 ((N q : ℝ≥0) * Δ + Δ) ∈ endpointBall i ρ y}).toReal = (ρ / R) ^ d := by
  have hm : Measurable (fun q : CoupledSample d =>
      q.1 ((N q : ℝ≥0) * Δ + Δ)) := by
    refine sbxS4_measurable_grid_select N hN (fun n q => q.1 ((n : ℝ≥0) * Δ + Δ)) ?_
    intro n
    exact (continuous_eval_const _).measurable.comp measurable_fst
  have hs : MeasurableSet {q : CoupledSample d |
      q.1 ((N q : ℝ≥0) * Δ + Δ) ∈ endpointBall i ρ y} :=
    ((measurableSet_endpointBall_pair i ρ).preimage
      (measurable_const.prodMk measurable_id)).preimage hm
  have h := sbxS4_gridInterval_cond_successful_subball Δ R δ i P L xω hP hR hδ
    hminor N hN hIone ρ hρ y hsub hI
  have he : (fun q : CoupledSample d => (endpointBall i ρ y).indicator (fun _ => (1 : ℝ))
      (q.1 ((N q : ℝ≥0) * Δ + Δ))) =
      {q : CoupledSample d | q.1 ((N q : ℝ≥0) * Δ + Δ) ∈ endpointBall i ρ y}.indicator
        (fun _ => (1 : ℝ)) := by
    funext q
    rfl
  rw [he, integral_indicator_const (1 : ℝ) hs] at h
  simpa only [smul_eq_mul, mul_one, Measure.real] using h

/-- Simultaneous actual support can be consumed at any selected natural index;
no measurability of an unrevealed coin is used. -/
theorem sbxS4_selected_success_support {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (L : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    (hend : ∀ᵐ q ∂L xω, ∀ n : ℕ, q.2 n = true →
      q.1 ((n : ℝ≥0) * Δ + Δ) ∈ endpointBall i R (q.1 ((n : ℝ≥0) * Δ)))
    (hs : SuccessfulBridgeSupportAt Δ i R L xω) (N : CoupledSample d → ℕ) :
    ∀ᵐ q ∂L xω, q.2 (N q) = true →
      q.1 ((N q : ℝ≥0) * Δ + Δ) ∈ endpointBall i R (q.1 ((N q : ℝ≥0) * Δ)) ∧
      ∀ u : ℝ≥0, u ≤ Δ → q.1 ((N q : ℝ≥0) * Δ + u) ∈
        couplingRegion i R (q.1 ((N q : ℝ≥0) * Δ)) := by
  filter_upwards [hend, hs] with q he hq
  intro hb
  refine ⟨he (N q) hb, fun u hu => hq (N q) hb _ (le_add_of_nonneg_right zero_le) ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
    (add_le_add (le_refl ((N q : ℝ≥0) * Δ)) hu)

section ActualStoppingGrid
variable {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
  (z : Vec d) (ω : FieldPair d) (hP : ∀ x, IsProbabilityMeasure (P (x, ω)))
  (hR : 0 < R) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
  (hminor : ∀ x, ENNReal.ofReal δ • cond (volume : Measure (Vec d))
    (endpointBall i R x) ≤
    (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
  (K : Kernel (Vec d) (Path d × Bool)) [IsMarkovKernel K]
  (hK : ∀ x, K x = sbxS4FirstSegmentLaw Δ R δ i P x ω)
  (ν : Measure (ℕ → Path d × Bool))
  (hν : ∀ n, ν.map (Preorder.frestrictLe n) =
    sbxS4SegmentPrefixLaw Δ R δ i P z ω K n)

include hP hR hδ₀ hδ₁ hminor hK hν

/-- Stopping-grid split identities for the actual supplied segment extension.
The deterministic clause is proved from its prefix marginals and realization,
then transported by countable branch sums; it is not an input premise. -/
theorem sbxS4_segmentExtension_stoppingGrid_interval
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (hstart : ∀ᵐ s ∂ν, (g s).1 0 = z)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (hsegment : ∀ (n : ℕ), ∀ᵐ s ∂ν, ∀ t : ℝ≥0, t ≤ Δ →
      (g s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t)
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C)
    (F : Path d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F)
    (hlocal : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') :
    sbxS4GridIntervalTest Δ δ R i P L (z, ω) N (sbxS4GridPastTest Δ N H) F := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure _ _ ν hν
  let : IsProbabilityMeasure (L (z, ω)) := hmap ▸ (inferInstance : IsProbabilityMeasure (ν.map g))
  have hI := sbxS4_segmentExtension_oneIntervalKernelAt Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν L g hg hmap hbits z₀ hzero hstart past hpast hstop hsegment
  have hNm := sbxS4_measurable_grid_index Δ N hN
  let A := sbxS4GridPastTest Δ N H
  have hA : Measurable A := sbxS4_measurable_gridPastTest Δ N hNm H hH
  have hbA : BoundedRealTest A := sbxS4_gridPastTest_bounded Δ N H hbH
  have he : Measurable (fun q : CoupledSample d => q.1 ((N q : ℝ≥0) * Δ)) := by
    refine sbxS4_measurable_grid_select N hNm
      (fun n q => q.1 ((n : ℝ≥0) * Δ)) ?_
    intro n
    exact (continuous_eval_const _).measurable.comp measurable_fst
  have hs : Measurable (fun q : CoupledSample d =>
      pathTimeShift q.1 ((N q : ℝ≥0) * Δ)) := by
    refine sbxS4_measurable_grid_select N hNm
      (fun n q => pathTimeShift q.1 ((n : ℝ≥0) * Δ)) ?_
    intro n
    exact Probability.continuous_path_time_shift.measurable.comp
      (measurable_const.prodMk measurable_fst)
  have hc : Measurable (fun q : CoupledSample d => q.2 (N q)) := by
    refine sbxS4_measurable_grid_select N hNm (fun n q => q.2 n) ?_
    intro n
    exact (measurable_pi_apply n).comp measurable_snd
  have hi := sbxS4_integrable_split_expectations Δ R δ i P ω hP hR hδ₀ hδ₁
    hminor K hK (L (z, ω)) _ he A hA hbA F hF hbF
  refine ⟨hi.1, hi.2, fun b => ?_⟩
  have hib := sbxS4_integrable_interval_bit (L (z, ω)) A hA hbA _ hs _ hc F hF hbF b
  have hir : Integrable (fun q : CoupledSample d => A q * (if b then δ *
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (q.1 ((N q : ℝ≥0) * Δ)) ω)
    else (∫ γ, F γ ∂P (q.1 ((N q : ℝ≥0) * Δ), ω)) - δ *
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
        (q.1 ((N q : ℝ≥0) * Δ)) ω))) (L (z, ω)) := by
    cases b with
    | true =>
      convert hi.2.const_mul δ using 1
      funext q
      simp only [↓reduceIte]
      ring
    | false =>
      convert hi.1.sub (hi.2.const_mul δ) using 1
      funext q
      simp only [Bool.false_eq_true, ↓reduceIte, Pi.sub_apply]
      ring
  refine ⟨hib, hir, ?_⟩
  have hib' : Integrable (fun q : CoupledSample d => A q *
      ((if q.2 (N q) = b then (1 : ℝ) else 0) *
        F (pathTimeShift q.1 ((N q : ℝ≥0) * Δ)))) (L (z, ω)) := by
    simpa only [mul_assoc] using hib
  have hid := sbxS4_integral_grid_test_transfer (L (z, ω)) N hNm A
    (fun n q => (if q.2 n = b then (1 : ℝ) else 0) *
      F (pathTimeShift q.1 ((n : ℝ≥0) * Δ)))
    (fun n q => if b then δ *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (q.1 ((n : ℝ≥0) * Δ)) ω)
      else (∫ γ, F γ ∂P (q.1 ((n : ℝ≥0) * Δ), ω)) - δ *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
          (q.1 ((n : ℝ≥0) * Δ)) ω)) hib' hir ?_
  · simpa only [mul_assoc] using hid
  · intro n
    have hdet := hI n ({q | N q = n}.indicator A) F
      (sbxS4_gridPastTest_branch_measurable Δ N hN H hH n)
      (sbxS4_indicator_bounded _ A hbA) hF hbF hlocal
    cases b with
    | true =>
      simp only [↓reduceIte, ← mul_assoc]
      rw [hdet.2.2.1, ← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by ring
    | false =>
      have hb (q : CoupledSample d) :
          (if q.2 n = true then (0 : ℝ) else 1) =
            (if q.2 n = false then (1 : ℝ) else 0) := by cases q.2 n <;> rfl
      simpa only [Bool.false_eq_true, ↓reduceIte, ← mul_assoc, hb] using hdet.2.2.2.2.2.2

/-- Selected fresh bits for the same supplied actual extension and realization.
The fresh-bit premise is derived from the prefix laws, not supplied. -/
theorem sbxS4_segmentExtension_stoppingGrid_freshBit
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C) :
    (∫ q, sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) ∂L (z, ω)) =
      δ * ∫ q, sbxS4GridPastTest Δ N H q ∂L (z, ω) := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure _ _ ν hν
  let : IsProbabilityMeasure (L (z, ω)) := hmap ▸ (inferInstance : IsProbabilityMeasure (ν.map g))
  exact (sbxS4_freshBitsAt_stoppingGrid Δ δ L (z, ω)
    (sbxS4_segmentExtension_freshBitsAt Δ R δ i P z ω hP hR hδ₀ hδ₁
      hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop)
    N hN H hH hbH).2.2

/-- The same actual split identities for an AE-finite extended stopping index. -/
theorem sbxS4_segmentExtension_stoppingGrid_interval_ae
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (hstart : ∀ᵐ s ∂ν, (g s).1 0 = z)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (hsegment : ∀ (n : ℕ), ∀ᵐ s ∂ν, ∀ t : ℝ≥0, t ≤ Δ →
      (g s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t)
    (T : CoupledSample d → WithTop ℕ) (hTm : Measurable T)
    (hT : ∀ n : ℕ, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | T q = n})
    (hfinite : ∀ᵐ q ∂L (z, ω), ∃ n : ℕ, T q = n)
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C)
    (F : Path d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F)
    (hlocal : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') :
    let N := sbxS4ExtendedGridIndex T
    sbxS4GridIntervalTest Δ δ R i P L (z, ω) N (sbxS4GridPastTest Δ N H) F := by
  let N := sbxS4ExtendedGridIndex T
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure _ _ ν hν
  let : IsProbabilityMeasure (L (z, ω)) := hmap ▸ (inferInstance : IsProbabilityMeasure (ν.map g))
  have hI := sbxS4_segmentExtension_oneIntervalKernelAt Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν L g hg hmap hbits z₀ hzero hstart past hpast hstop hsegment
  have hNm : Measurable N := sbxS4_measurable_extendedGridIndex T hTm
  let A := sbxS4GridPastTest Δ N H
  have hA : Measurable A := sbxS4_measurable_gridPastTest Δ N hNm H hH
  have hbA : BoundedRealTest A := sbxS4_gridPastTest_bounded Δ N H hbH
  have he : Measurable (fun q : CoupledSample d => q.1 ((N q : ℝ≥0) * Δ)) := by
    refine sbxS4_measurable_grid_select N hNm
      (fun n q => q.1 ((n : ℝ≥0) * Δ)) ?_
    intro n
    exact (continuous_eval_const _).measurable.comp measurable_fst
  have hs : Measurable (fun q : CoupledSample d =>
      pathTimeShift q.1 ((N q : ℝ≥0) * Δ)) := by
    refine sbxS4_measurable_grid_select N hNm
      (fun n q => pathTimeShift q.1 ((n : ℝ≥0) * Δ)) ?_
    intro n
    exact Probability.continuous_path_time_shift.measurable.comp
      (measurable_const.prodMk measurable_fst)
  have hc : Measurable (fun q : CoupledSample d => q.2 (N q)) := by
    refine sbxS4_measurable_grid_select N hNm (fun n q => q.2 n) ?_
    intro n
    exact (measurable_pi_apply n).comp measurable_snd
  have hi := sbxS4_integrable_split_expectations Δ R δ i P ω hP hR hδ₀ hδ₁
    hminor K hK (L (z, ω)) _ he A hA hbA F hF hbF
  refine ⟨hi.1, hi.2, fun b => ?_⟩
  have hib := sbxS4_integrable_interval_bit (L (z, ω)) A hA hbA _ hs _ hc F hF hbF b
  have hir : Integrable (fun q : CoupledSample d => A q * (if b then δ *
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (q.1 ((N q : ℝ≥0) * Δ)) ω)
    else (∫ γ, F γ ∂P (q.1 ((N q : ℝ≥0) * Δ), ω)) - δ *
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
        (q.1 ((N q : ℝ≥0) * Δ)) ω))) (L (z, ω)) := by
    cases b with
    | true =>
      convert hi.2.const_mul δ using 1
      funext q
      simp only [↓reduceIte]
      ring
    | false =>
      convert hi.1.sub (hi.2.const_mul δ) using 1
      funext q
      simp only [Bool.false_eq_true, ↓reduceIte, Pi.sub_apply]
      ring
  refine ⟨hib, hir, ?_⟩
  have hib' : Integrable (fun q : CoupledSample d => A q *
      ((if q.2 (N q) = b then (1 : ℝ) else 0) *
        F (pathTimeShift q.1 ((N q : ℝ≥0) * Δ)))) (L (z, ω)) := by
    simpa only [mul_assoc] using hib
  have hid := sbxS4_integral_grid_test_transfer_ae (L (z, ω)) T
    (fun n => Probability.finiteHistorySigma_le Δ n _ (hT n)) hfinite A
    (fun n q => (if q.2 n = b then (1 : ℝ) else 0) *
      F (pathTimeShift q.1 ((n : ℝ≥0) * Δ)))
    (fun n q => if b then δ *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P (q.1 ((n : ℝ≥0) * Δ)) ω)
      else (∫ γ, F γ ∂P (q.1 ((n : ℝ≥0) * Δ), ω)) - δ *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
          (q.1 ((n : ℝ≥0) * Δ)) ω)) hib' hir ?_
  · simpa only [mul_assoc] using hid
  · intro n
    have hdet := hI n ({q | T q = n}.indicator A) F
      (sbxS4_extendedGridPastTest_branch_measurable Δ T hT H hH n)
      (sbxS4_indicator_bounded _ A hbA) hF hbF hlocal
    cases b with
    | true =>
      simp only [↓reduceIte, ← mul_assoc]
      rw [hdet.2.2.1, ← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by ring
    | false =>
      have hb (q : CoupledSample d) :
          (if q.2 n = true then (0 : ℝ) else 1) =
            (if q.2 n = false then (1 : ℝ) else 0) := by cases q.2 n <;> rfl
      simpa only [Bool.false_eq_true, ↓reduceIte, ← mul_assoc, hb] using hdet.2.2.2.2.2.2


/-- The entire future coin sequence, including the next split bit, factors
from the exact deterministic past of the supplied segment realization. -/
theorem sbxS4_segmentExtension_futureBits_test
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (n : ℕ) (J : CoupledSample d → ℝ)
    (hJ : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance J)
    (hbJ : BoundedRealTest J) (F : BernoulliSequence → ℝ) (hF : Measurable F)
    (hbF : BoundedRealTest F) :
    (∫ q, J q * F (fun k => q.2 (n + k)) ∂L (z, ω)) =
      (∫ q, J q ∂L (z, ω)) * (∫ β, F β ∂sbxS4RemainingBitsLaw δ) := by
  have hJm : Measurable J := hJ.mono (Probability.finiteHistorySigma_le Δ n) le_rfl
  have htail : Measurable (fun q : CoupledSample d => fun k => q.2 (n + k)) :=
    measurable_pi_iff.mpr fun k => (measurable_pi_apply (n + k)).comp measurable_snd
  rw [← hmap, integral_map (f := fun q => J q * F (fun k => q.2 (n + k)))
      hg.aemeasurable (hJm.mul (hF.comp htail)).aestronglyMeasurable,
    integral_map hg.aemeasurable hJm.aestronglyMeasurable]
  have hgood := hzero.and ((ae_all_iff.mpr hbits).and (ae_all_iff.mpr hstop))
  cases n with
  | zero =>
    have hJ0 : ∀ᵐ s ∂ν, J (g s) = J z₀ := by
      filter_upwards [hgood] with s hs
      rw [← hs.1, Probability.finiteHistory_test_stopped Δ 0 J hJ]
    have he : (fun s => J (g s) * F (fun k => (g s).2 (0 + k))) =ᵐ[ν]
        (fun s => J z₀ * F (fun k => (s k).2)) := by
      filter_upwards [hJ0, hgood] with s hj hs
      rw [hj]
      congr 2
      funext k
      simpa only [Nat.zero_add] using hs.2.1 k
    rw [integral_congr_ae he, integral_const_mul]
    have hJF : (∫ s, J (g s) ∂ν) = J z₀ := by
      rw [integral_congr_ae hJ0]
      let : IsProbabilityMeasure (P (z, ω)) := hP z
      let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
        (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
      let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure _ _ ν hν
      simp only [integral_const, probReal_univ, one_smul]
    rw [hJF]
    congr 1
    rw [← sbxS4_segmentExtension_map_coins Δ R δ i P z ω hP hR hδ₀ hδ₁
      hminor K hK ν hν]
    exact (integral_map (φ := fun s : ℕ → Path d × Bool => fun k => (s k).2)
      (measurable_pi_iff.mpr fun k =>
        measurable_snd.comp (measurable_pi_apply k)).aemeasurable hF.aestronglyMeasurable).symm
  | succ m =>
    have hJpast : ∀ᵐ s ∂ν, J (g s) = J (past m (Preorder.frestrictLe m s)) := by
      filter_upwards [hgood] with s hs
      rw [← hs.2.2 m, Probability.finiteHistory_test_stopped Δ (m + 1) J hJ]
    have he : (fun s => J (g s) * F (fun k => (g s).2 (m + 1 + k))) =ᵐ[ν]
        (fun s => J (past m (Preorder.frestrictLe m s)) * F (sbxS4FutureCoins m s)) := by
      filter_upwards [hJpast, hgood] with s hj hs
      rw [hj]
      congr 2
      funext k
      dsimp only [sbxS4FutureCoins]
      rw [hs.2.1]
      congr 2
      omega
    rw [integral_congr_ae he]
    have ht := sbxS4_segmentExtension_integral_futureCoins Δ R δ i P z ω hP hR hδ₀ hδ₁
      hminor K hK ν hν m (J ∘ past m) (hJm.comp (hpast m))
      (by obtain ⟨C, hC⟩ := hbJ; exact ⟨C, fun q => hC _⟩)
      F hF (by obtain ⟨C, hC⟩ := hbF; exact ⟨C, fun β => hC _⟩)
    simp only [Function.comp_apply] at ht
    rw [ht.2]
    congr 1
    rw [← hν m, integral_map (Preorder.measurable_frestrictLe m).aemeasurable
      (hJm.comp (hpast m)).aestronglyMeasurable]
    exact (integral_congr_ae hJpast).symm

/-- The whole future bit sequence at a natural stopping grid has the original
Bernoulli product law and factors against bounded stopped-history tests. -/
theorem sbxS4_segmentExtension_stoppingGrid_futureBits
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C)
    (F : BernoulliSequence → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F) :
    Integrable (sbxS4GridPastTest Δ N H) (L (z, ω)) ∧
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      F (fun k => q.2 (N q + k))) (L (z, ω)) ∧
    (∫ q, sbxS4GridPastTest Δ N H q * F (fun k => q.2 (N q + k)) ∂L (z, ω)) =
      (∫ q, sbxS4GridPastTest Δ N H q ∂L (z, ω)) *
        (∫ β, F β ∂sbxS4RemainingBitsLaw δ) := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure _ _ ν hν
  let : IsProbabilityMeasure (L (z, ω)) := hmap ▸ (inferInstance : IsProbabilityMeasure (ν.map g))
  have hNm := sbxS4_measurable_grid_index Δ N hN
  let A := sbxS4GridPastTest Δ N H
  have hA : Measurable A := sbxS4_measurable_gridPastTest Δ N hNm H hH
  have hbA : BoundedRealTest A := sbxS4_gridPastTest_bounded Δ N H hbH
  obtain ⟨C, hC⟩ := hbA
  have hi : Integrable A (L (z, ω)) := Integrable.of_bound hA.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun q => (hC q : |A q| ≤ C))
  have htail : Measurable (fun q : CoupledSample d => fun k => q.2 (N q + k)) := by
    refine sbxS4_measurable_grid_select N hNm (fun n q => fun k => q.2 (n + k)) ?_
    intro n
    exact measurable_pi_iff.mpr fun k => (measurable_pi_apply (n + k)).comp measurable_snd
  obtain ⟨D, hD⟩ := hbF
  have hip := hi.mul_bdd (hF.comp htail).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => show ‖F (fun k => q.2 (N q + k))‖ ≤ D from hD _)
  refine ⟨hi, hip, ?_⟩
  rw [← integral_mul_const]
  apply sbxS4_integral_grid_test_transfer (L (z, ω)) N hNm A
    (fun n q => F (fun k => q.2 (n + k)))
    (fun _ _ => ∫ β, F β ∂sbxS4RemainingBitsLaw δ) hip (hi.mul_const _)
  intro n
  rw [integral_mul_const]
  exact sbxS4_segmentExtension_futureBits_test Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop n _
    (sbxS4_gridPastTest_branch_measurable Δ N hN H hH n)
    (sbxS4_indicator_bounded _ A ⟨C, hC⟩) F hF ⟨D, hD⟩

/-- The selected future sequence has the actual Bernoulli product law. -/
theorem sbxS4_segmentExtension_stoppingGrid_map_futureBits
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    : (L (z, ω)).map (fun q => fun k => q.2 (N q + k)) =
      sbxS4RemainingBitsLaw δ := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure _ _ ν hν
  let : IsProbabilityMeasure (L (z, ω)) := hmap ▸ (inferInstance : IsProbabilityMeasure (ν.map g))
  let : IsProbabilityMeasure (sbxS4RemainingBitsLaw δ) :=
    sbxS4_remainingBitsLaw_isProbabilityMeasure δ (le_of_lt hδ₀) (le_of_lt hδ₁)
  have hNm := sbxS4_measurable_grid_index Δ N hN
  have htail : Measurable (fun q : CoupledSample d => fun k => q.2 (N q + k)) := by
    refine sbxS4_measurable_grid_select N hNm (fun n q => fun k => q.2 (n + k)) ?_
    intro n
    exact measurable_pi_iff.mpr fun k => (measurable_pi_apply (n + k)).comp measurable_snd
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have h := sbxS4_segmentExtension_stoppingGrid_futureBits Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop N hN
    (fun _ _ => (1 : ℝ)) (fun _ => measurable_const) ⟨1, by simp⟩
    (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs)
    (sbxS4_indicator_bounded s (fun _ => (1 : ℝ)) ⟨1, by simp⟩)
  have hi : (∫ q, s.indicator (fun _ => (1 : ℝ)) (fun k => q.2 (N q + k))
      ∂L (z, ω)) = ∫ β, s.indicator (fun _ => (1 : ℝ)) β ∂sbxS4RemainingBitsLaw δ := by
    simpa only [sbxS4GridPastTest, one_mul, integral_const, probReal_univ, one_smul] using h.2.2
  rw [← integral_map htail.aemeasurable (measurable_const.indicator hs).aestronglyMeasurable] at hi
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one, Measure.real] using hi

/-- Integrable signed future-bit observations stay integrable at the selected grid. -/
theorem sbxS4_segmentExtension_stoppingGrid_integrable_futureBits
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    (F : BernoulliSequence → ℝ)
    (hF : Integrable F (sbxS4RemainingBitsLaw δ)) :
    Integrable (fun q => F (fun k => q.2 (N q + k))) (L (z, ω)) := by
  have hNm := sbxS4_measurable_grid_index Δ N hN
  have htail : Measurable (fun q : CoupledSample d => fun k => q.2 (N q + k)) := by
    refine sbxS4_measurable_grid_select N hNm (fun n q => fun k => q.2 (n + k)) ?_
    intro n
    exact measurable_pi_iff.mpr fun k => (measurable_pi_apply (n + k)).comp measurable_snd
  have hi : Integrable F ((L (z, ω)).map (fun q => fun k => q.2 (N q + k))) := by
    rw [sbxS4_segmentExtension_stoppingGrid_map_futureBits Δ R δ i P z ω hP hR hδ₀ hδ₁
      hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop N hN]
    exact hF
  exact hi.comp_measurable htail

/-- A bounded selected past multiplied by an integrable future-bit observation
is integrable under the actual coupled law. -/
theorem sbxS4_segmentExtension_stoppingGrid_integrable_past_futureBits
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C)
    (F : BernoulliSequence → ℝ) (hF : Integrable F (sbxS4RemainingBitsLaw δ)) :
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      F (fun k => q.2 (N q + k))) (L (z, ω)) := by
  have hi := sbxS4_segmentExtension_stoppingGrid_integrable_futureBits Δ R δ i P z ω
    hP hR hδ₀ hδ₁ hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop N hN F hF
  have hNm := sbxS4_measurable_grid_index Δ N hN
  have hA := sbxS4_measurable_gridPastTest Δ N hNm H hH
  obtain ⟨C, hC⟩ := sbxS4_gridPastTest_bounded Δ N H hbH
  have hp := hi.mul_bdd hA.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => show ‖sbxS4GridPastTest Δ N H q‖ ≤ C from hC q)
  simpa only [mul_comm] using hp

/-- A selected stopped-history observation is independent of the entire future coin sequence. -/
theorem sbxS4_segmentExtension_stoppingGrid_indep_futureBits
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n)) :
    IndepFun (sbxS4GridPastTest Δ N H) (fun q => fun k => q.2 (N q + k)) (L (z, ω)) := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure _ _ ν hν
  let : IsProbabilityMeasure (L (z, ω)) := hmap ▸ (inferInstance : IsProbabilityMeasure (ν.map g))
  let : IsProbabilityMeasure (sbxS4RemainingBitsLaw δ) :=
    sbxS4_remainingBitsLaw_isProbabilityMeasure δ (le_of_lt hδ₀) (le_of_lt hδ₁)
  let A := sbxS4GridPastTest Δ N H
  let B := fun q : CoupledSample d => fun k => q.2 (N q + k)
  have hNm := sbxS4_measurable_grid_index Δ N hN
  have hA : Measurable A := sbxS4_measurable_gridPastTest Δ N hNm H hH
  have hB : Measurable B := by
    refine sbxS4_measurable_grid_select N hNm (fun n q => fun k => q.2 (n + k)) ?_
    intro n
    exact measurable_pi_iff.mpr fun k => (measurable_pi_apply (n + k)).comp measurable_snd
  have hBmap : (L (z, ω)).map B = sbxS4RemainingBitsLaw δ :=
    sbxS4_segmentExtension_stoppingGrid_map_futureBits Δ R δ i P z ω hP hR hδ₀ hδ₁
      hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop N hN
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have h := sbxS4_segmentExtension_stoppingGrid_futureBits Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop N hN
    (fun n q => s.indicator (fun _ => (1 : ℝ)) (H n q))
    (fun n => (measurable_const.indicator hs).comp (hH n))
    (by
      obtain ⟨C, hC⟩ := sbxS4_indicator_bounded s (fun _ => (1 : ℝ)) ⟨1, by simp⟩
      exact ⟨C, fun n q => hC (H n q)⟩)
    (t.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator ht)
    (sbxS4_indicator_bounded t (fun _ => (1 : ℝ)) ⟨1, by simp⟩)
  have hleft : (fun q => sbxS4GridPastTest Δ N
      (fun n q => s.indicator (fun _ => (1 : ℝ)) (H n q)) q *
      t.indicator (fun _ => (1 : ℝ)) (B q)) =
      (A ⁻¹' s ∩ B ⁻¹' t).indicator (fun _ => (1 : ℝ)) := by
    funext q
    change s.indicator (fun _ => (1 : ℝ)) (A q) *
      t.indicator (fun _ => (1 : ℝ)) (B q) =
      (A ⁻¹' s ∩ B ⁻¹' t).indicator (fun _ => (1 : ℝ)) q
    by_cases ha : A q ∈ s <;> by_cases hb : B q ∈ t <;>
      simp [Set.indicator_apply, ha, hb]
  have hright : sbxS4GridPastTest Δ N
      (fun n q => s.indicator (fun _ => (1 : ℝ)) (H n q)) =
      (A ⁻¹' s).indicator (fun _ => (1 : ℝ)) := by
    funext q
    rfl
  rw [hleft, hright, ← hBmap,
    integral_map hB.aemeasurable (measurable_const.indicator ht).aestronglyMeasurable] at h
  have hcomp : (fun q => t.indicator (fun _ => (1 : ℝ)) (B q)) =
      (B ⁻¹' t).indicator (fun _ => (1 : ℝ)) := rfl
  rw [hcomp] at h
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
  simpa only [integral_indicator_const (1 : ℝ) ((hA hs).inter (hB ht)),
    integral_indicator_const (1 : ℝ) (hA hs),
    integral_indicator_const (1 : ℝ) (hB ht), smul_eq_mul, mul_one, Measure.real,
    ENNReal.toReal_mul] using h.2.2

/-- Signed integrable future-bit tests factor against bounded selected past tests. -/
theorem sbxS4_segmentExtension_stoppingGrid_integral_past_futureBits
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C)
    (F : BernoulliSequence → ℝ) (hF : Integrable F (sbxS4RemainingBitsLaw δ)) :
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      F (fun k => q.2 (N q + k))) (L (z, ω)) ∧
    (∫ q, sbxS4GridPastTest Δ N H q * F (fun k => q.2 (N q + k)) ∂L (z, ω)) =
      (∫ q, sbxS4GridPastTest Δ N H q ∂L (z, ω)) *
        (∫ β, F β ∂sbxS4RemainingBitsLaw δ) := by
  have hi := sbxS4_segmentExtension_stoppingGrid_integrable_past_futureBits Δ R δ i P z ω
    hP hR hδ₀ hδ₁ hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop N hN H hH hbH F hF
  refine ⟨hi, ?_⟩
  let A := sbxS4GridPastTest Δ N H
  let B := fun q : CoupledSample d => fun k => q.2 (N q + k)
  have hNm := sbxS4_measurable_grid_index Δ N hN
  have hA : Measurable A := sbxS4_measurable_gridPastTest Δ N hNm H hH
  have hB : Measurable B := by
    refine sbxS4_measurable_grid_select N hNm (fun n q => fun k => q.2 (n + k)) ?_
    intro n
    exact measurable_pi_iff.mpr fun k => (measurable_pi_apply (n + k)).comp measurable_snd
  have hBmap : (L (z, ω)).map B = sbxS4RemainingBitsLaw δ :=
    sbxS4_segmentExtension_stoppingGrid_map_futureBits Δ R δ i P z ω hP hR hδ₀ hδ₁
      hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop N hN
  have hind := sbxS4_segmentExtension_stoppingGrid_indep_futureBits Δ R δ i P z ω
    hP hR hδ₀ hδ₁ hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop N hN H hH
  have hFm : AEStronglyMeasurable F ((L (z, ω)).map B) := by
    rw [hBmap]
    exact hF.aestronglyMeasurable
  have hfact := hind.integral_fun_comp_mul_comp hA.aemeasurable hB.aemeasurable
    (measurable_id.aestronglyMeasurable) hFm
  rw [← integral_map hB.aemeasurable hFm, hBmap] at hfact
  simpa only [id_eq] using hfact

/-- The whole future bit sequence at an almost surely finite extended grid;
the infinite-index event is removed by the countable AE branch transport. -/
theorem sbxS4_segmentExtension_stoppingGrid_futureBits_ae
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (T : CoupledSample d → WithTop ℕ) (hTm : Measurable T)
    (hT : ∀ n : ℕ, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | T q = n})
    (hfinite : ∀ᵐ q ∂L (z, ω), ∃ n : ℕ, T q = n)
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C)
    (F : BernoulliSequence → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F) :
    let N := sbxS4ExtendedGridIndex T
    Integrable (sbxS4GridPastTest Δ N H) (L (z, ω)) ∧
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      F (fun k => q.2 (N q + k))) (L (z, ω)) ∧
    (∫ q, sbxS4GridPastTest Δ N H q * F (fun k => q.2 (N q + k)) ∂L (z, ω)) =
      (∫ q, sbxS4GridPastTest Δ N H q ∂L (z, ω)) *
        (∫ β, F β ∂sbxS4RemainingBitsLaw δ) := by
  let N := sbxS4ExtendedGridIndex T
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure _ _ ν hν
  let : IsProbabilityMeasure (L (z, ω)) := hmap ▸ (inferInstance : IsProbabilityMeasure (ν.map g))
  have hNm := sbxS4_measurable_extendedGridIndex T hTm
  let A := sbxS4GridPastTest Δ N H
  have hA : Measurable A := sbxS4_measurable_gridPastTest Δ N hNm H hH
  have hbA : BoundedRealTest A := sbxS4_gridPastTest_bounded Δ N H hbH
  obtain ⟨C, hC⟩ := hbA
  have hi : Integrable A (L (z, ω)) := Integrable.of_bound hA.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun q => (hC q : |A q| ≤ C))
  have htail : Measurable (fun q : CoupledSample d => fun k => q.2 (N q + k)) := by
    refine sbxS4_measurable_grid_select N hNm (fun n q => fun k => q.2 (n + k)) ?_
    intro n
    exact measurable_pi_iff.mpr fun k => (measurable_pi_apply (n + k)).comp measurable_snd
  obtain ⟨D, hD⟩ := hbF
  have hip := hi.mul_bdd (hF.comp htail).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => show ‖F (fun k => q.2 (N q + k))‖ ≤ D from hD _)
  refine ⟨hi, hip, ?_⟩
  rw [← integral_mul_const]
  apply sbxS4_integral_grid_test_transfer_ae (L (z, ω)) T
    (fun n => Probability.finiteHistorySigma_le Δ n _ (hT n)) hfinite A
    (fun n q => F (fun k => q.2 (n + k)))
    (fun _ _ => ∫ β, F β ∂sbxS4RemainingBitsLaw δ) hip (hi.mul_const _)
  intro n
  rw [integral_mul_const]
  exact sbxS4_segmentExtension_futureBits_test Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop n _
    (sbxS4_extendedGridPastTest_branch_measurable Δ T hT H hH n)
    (sbxS4_indicator_bounded _ A ⟨C, hC⟩) F hF ⟨D, hD⟩

/-- The selected future sequence has the Bernoulli law at an almost surely finite grid. -/
theorem sbxS4_segmentExtension_stoppingGrid_map_futureBits_ae
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (T : CoupledSample d → WithTop ℕ) (hTm : Measurable T)
    (hT : ∀ n : ℕ, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | T q = n})
    (hfinite : ∀ᵐ q ∂L (z, ω), ∃ n : ℕ, T q = n)
    : let N := sbxS4ExtendedGridIndex T
      (L (z, ω)).map (fun q => fun k => q.2 (N q + k)) =
      sbxS4RemainingBitsLaw δ := by
  let N := sbxS4ExtendedGridIndex T
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure _ _ ν hν
  let : IsProbabilityMeasure (L (z, ω)) := hmap ▸ (inferInstance : IsProbabilityMeasure (ν.map g))
  let : IsProbabilityMeasure (sbxS4RemainingBitsLaw δ) :=
    sbxS4_remainingBitsLaw_isProbabilityMeasure δ (le_of_lt hδ₀) (le_of_lt hδ₁)
  have hNm := sbxS4_measurable_extendedGridIndex T hTm
  have htail : Measurable (fun q : CoupledSample d => fun k => q.2 (N q + k)) := by
    refine sbxS4_measurable_grid_select N hNm (fun n q => fun k => q.2 (n + k)) ?_
    intro n
    exact measurable_pi_iff.mpr fun k => (measurable_pi_apply (n + k)).comp measurable_snd
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have h := sbxS4_segmentExtension_stoppingGrid_futureBits_ae Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop T hTm hT hfinite
    (fun _ _ => (1 : ℝ)) (fun _ => measurable_const) ⟨1, by simp⟩
    (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs)
    (sbxS4_indicator_bounded s (fun _ => (1 : ℝ)) ⟨1, by simp⟩)
  have hi : (∫ q, s.indicator (fun _ => (1 : ℝ)) (fun k => q.2 (N q + k))
      ∂L (z, ω)) = ∫ β, s.indicator (fun _ => (1 : ℝ)) β ∂sbxS4RemainingBitsLaw δ := by
    simpa only [sbxS4GridPastTest, one_mul, integral_const, probReal_univ, one_smul] using h.2.2
  rw [← integral_map htail.aemeasurable (measurable_const.indicator hs).aestronglyMeasurable] at hi
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one, Measure.real] using hi

/-- Integrable future-bit observations remain integrable at an almost surely finite grid. -/
theorem sbxS4_segmentExtension_stoppingGrid_integrable_futureBits_ae
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (T : CoupledSample d → WithTop ℕ) (hTm : Measurable T)
    (hT : ∀ n : ℕ, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | T q = n})
    (hfinite : ∀ᵐ q ∂L (z, ω), ∃ n : ℕ, T q = n)
    (F : BernoulliSequence → ℝ)
    (hF : Integrable F (sbxS4RemainingBitsLaw δ)) :
    let N := sbxS4ExtendedGridIndex T
    Integrable (fun q => F (fun k => q.2 (N q + k))) (L (z, ω)) := by
  let N := sbxS4ExtendedGridIndex T
  have hNm := sbxS4_measurable_extendedGridIndex T hTm
  have htail : Measurable (fun q : CoupledSample d => fun k => q.2 (N q + k)) := by
    refine sbxS4_measurable_grid_select N hNm (fun n q => fun k => q.2 (n + k)) ?_
    intro n
    exact measurable_pi_iff.mpr fun k => (measurable_pi_apply (n + k)).comp measurable_snd
  have hi : Integrable F ((L (z, ω)).map (fun q => fun k => q.2 (N q + k))) := by
    rw [sbxS4_segmentExtension_stoppingGrid_map_futureBits_ae Δ R δ i P z ω hP hR hδ₀ hδ₁
      hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop T hTm hT hfinite]
    exact hF
  exact hi.comp_measurable htail

/-- A bounded selected past multiplied by an integrable future-bit observation
is integrable under the actual coupled law. -/
theorem sbxS4_segmentExtension_stoppingGrid_integrable_past_futureBits_ae
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (T : CoupledSample d → WithTop ℕ) (hTm : Measurable T)
    (hT : ∀ n : ℕ, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | T q = n})
    (hfinite : ∀ᵐ q ∂L (z, ω), ∃ n : ℕ, T q = n)
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C)
    (F : BernoulliSequence → ℝ) (hF : Integrable F (sbxS4RemainingBitsLaw δ)) :
    let N := sbxS4ExtendedGridIndex T
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      F (fun k => q.2 (N q + k))) (L (z, ω)) := by
  let N := sbxS4ExtendedGridIndex T
  have hi := sbxS4_segmentExtension_stoppingGrid_integrable_futureBits_ae Δ R δ i P z ω
    hP hR hδ₀ hδ₁ hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop T hTm hT hfinite F hF
  have hNm := sbxS4_measurable_extendedGridIndex T hTm
  have hA := sbxS4_measurable_gridPastTest Δ N hNm H hH
  obtain ⟨C, hC⟩ := sbxS4_gridPastTest_bounded Δ N H hbH
  have hp := hi.mul_bdd hA.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => show ‖sbxS4GridPastTest Δ N H q‖ ≤ C from hC q)
  simpa only [mul_comm] using hp

/-- Joint observations of the actual coupled path and selected future bits are
integrable when dominated by an integrable future-bit observation. -/
theorem sbxS4_segmentExtension_stoppingGrid_integrable_joint_futureBits
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    (F : CoupledSample d × BernoulliSequence → ℝ) (hF : Measurable F)
    (G : BernoulliSequence → ℝ) (hG : Integrable G (sbxS4RemainingBitsLaw δ))
    (hbound : ∀ q β, ‖F (q, β)‖ ≤ ‖G β‖) :
    Integrable (fun q => F (q, fun k => q.2 (N q + k))) (L (z, ω)) := by
  have hNm := sbxS4_measurable_grid_index Δ N hN
  have htail : Measurable (fun q : CoupledSample d => fun k => q.2 (N q + k)) := by
    refine sbxS4_measurable_grid_select N hNm (fun n q => fun k => q.2 (n + k)) ?_
    intro n
    exact measurable_pi_iff.mpr fun k => (measurable_pi_apply (n + k)).comp measurable_snd
  have hi := sbxS4_segmentExtension_stoppingGrid_integrable_futureBits Δ R δ i P z ω
    hP hR hδ₀ hδ₁ hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop N hN G hG
  exact hi.mono (hF.comp (measurable_id.prodMk htail)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => hbound q _)

/-- Joint observations of the actual coupled path and selected future bits are
integrable when dominated by an integrable future-bit observation. -/
theorem sbxS4_segmentExtension_stoppingGrid_integrable_joint_futureBits_ae
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (T : CoupledSample d → WithTop ℕ) (hTm : Measurable T)
    (hT : ∀ n : ℕ, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | T q = n})
    (hfinite : ∀ᵐ q ∂L (z, ω), ∃ n : ℕ, T q = n)
    (F : CoupledSample d × BernoulliSequence → ℝ) (hF : Measurable F)
    (G : BernoulliSequence → ℝ) (hG : Integrable G (sbxS4RemainingBitsLaw δ))
    (hbound : ∀ q β, ‖F (q, β)‖ ≤ ‖G β‖) :
    let N := sbxS4ExtendedGridIndex T
    Integrable (fun q => F (q, fun k => q.2 (N q + k))) (L (z, ω)) := by
  let N := sbxS4ExtendedGridIndex T
  have hNm := sbxS4_measurable_extendedGridIndex T hTm
  have htail : Measurable (fun q : CoupledSample d => fun k => q.2 (N q + k)) := by
    refine sbxS4_measurable_grid_select N hNm (fun n q => fun k => q.2 (n + k)) ?_
    intro n
    exact measurable_pi_iff.mpr fun k => (measurable_pi_apply (n + k)).comp measurable_snd
  have hi := sbxS4_segmentExtension_stoppingGrid_integrable_futureBits_ae Δ R δ i P z ω
    hP hR hδ₀ hδ₁ hminor K hK ν hν L g hg hmap hbits z₀ hzero past hpast hstop T hTm hT hfinite G hG
  exact hi.mono (hF.comp (measurable_id.prodMk htail)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => hbound q _)

/-- The literal uniform successful endpoint law at a selected natural trial,
derived from the supplied split-prefix laws and their history-faithful realization. -/
theorem sbxS4_segmentExtension_stoppingGrid_endpoint
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (hstart : ∀ᵐ s ∂ν, (g s).1 0 = z)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (hsegment : ∀ (n : ℕ), ∀ᵐ s ∂ν, ∀ t : ℝ≥0, t ≤ Δ →
      (g s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t)
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C)
    (φ : Vec d → ℝ) (hφ : Measurable φ) (hbφ : BoundedRealTest φ) :
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) *
      φ (q.1 ((N q : ℝ≥0) * Δ + Δ))) (L (z, ω)) ∧
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      endpointAverage i R (q.1 ((N q : ℝ≥0) * Δ)) φ) (L (z, ω)) ∧
    (∫ q, sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) *
      φ (q.1 ((N q : ℝ≥0) * Δ + Δ)) ∂L (z, ω)) =
      δ * (∫ q, sbxS4GridPastTest Δ N H q *
        endpointAverage i R (q.1 ((N q : ℝ≥0) * Δ)) φ ∂L (z, ω)) := by
  apply sbxS4_gridInterval_successful_endpoint Δ R δ i P L (z, ω) hP hR hδ₀
    hminor N (sbxS4GridPastTest Δ N H) φ hφ
  exact sbxS4_segmentExtension_stoppingGrid_interval Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν L g hg hmap hbits z₀ hzero hstart past hpast hstop hsegment
    N hN H hH hbH (fun γ => φ (γ Δ)) (hφ.comp (continuous_eval_const Δ).measurable)
    (by obtain ⟨C, hC⟩ := hbφ; exact ⟨C, fun γ => hC (γ Δ)⟩)
    (fun γ γ' h => congrArg φ (h Δ le_rfl))

/-- Selected successful endpoints tested against a measurable set, with the
actual Lebesgue intersection ratio and source normalization. -/
theorem sbxS4_segmentExtension_stoppingGrid_endpoint_indicator
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (hstart : ∀ᵐ s ∂ν, (g s).1 0 = z)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (hsegment : ∀ (n : ℕ), ∀ᵐ s ∂ν, ∀ t : ℝ≥0, t ≤ Δ →
      (g s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t)
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C)
    (S : Set (Vec d)) (hS : MeasurableSet S) :
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) *
      (S.indicator (fun _ => (1 : ℝ))) (q.1 ((N q : ℝ≥0) * Δ + Δ))) (L (z, ω)) ∧
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      ((volume (S ∩ endpointBall i R (q.1 ((N q : ℝ≥0) * Δ)))).toReal /
        (volume (endpointBall i R (q.1 ((N q : ℝ≥0) * Δ)))).toReal)) (L (z, ω)) ∧
    (∫ q, sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) *
      (S.indicator (fun _ => (1 : ℝ))) (q.1 ((N q : ℝ≥0) * Δ + Δ)) ∂L (z, ω)) =
      δ * (∫ q, sbxS4GridPastTest Δ N H q *
        ((volume (S ∩ endpointBall i R (q.1 ((N q : ℝ≥0) * Δ)))).toReal /
        (volume (endpointBall i R (q.1 ((N q : ℝ≥0) * Δ)))).toReal) ∂L (z, ω)) := by
  have h := sbxS4_segmentExtension_stoppingGrid_endpoint Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν L g hg hmap hbits z₀ hzero hstart past hpast hstop hsegment
    N hN H hH hbH (S.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hS) (sbxS4_indicator_bounded S _ ⟨1, by simp⟩)
  simpa only [sbxS4_endpointAverage_indicator i R _ S hS] using h

/-- Actual selected-past subball mass from the checked split realization. -/
theorem sbxS4_segmentExtension_stoppingGrid_successful_subball
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (hstart : ∀ᵐ s ∂ν, (g s).1 0 = z)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (hsegment : ∀ (n : ℕ), ∀ᵐ s ∂ν, ∀ t : ℝ≥0, t ≤ Δ →
      (g s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t)
    (N : CoupledSample d → ℕ)
    (hN : ∀ n, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | N q = n})
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C)
    (ρ : ℝ) (hρ : 0 < ρ) (y : Vec d)
    (hsub : ∀ᵐ q ∂L (z, ω), endpointBall i ρ y ⊆
      endpointBall i R (q.1 ((N q : ℝ≥0) * Δ))) :
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) *
      (endpointBall i ρ y).indicator (fun _ => (1 : ℝ))
        (q.1 ((N q : ℝ≥0) * Δ + Δ))) (L (z, ω)) ∧
    Integrable (fun q => sbxS4GridPastTest Δ N H q * (ρ / R) ^ d) (L (z, ω)) ∧
    (∫ q, sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) *
      (endpointBall i ρ y).indicator (fun _ => (1 : ℝ))
        (q.1 ((N q : ℝ≥0) * Δ + Δ)) ∂L (z, ω)) =
      δ * (∫ q, sbxS4GridPastTest Δ N H q * (ρ / R) ^ d ∂L (z, ω)) := by
  apply sbxS4_gridInterval_successful_subball Δ R δ i P L (z, ω) hP hR hδ₀
    hminor N (sbxS4GridPastTest Δ N H) ρ hρ y hsub
  have hm : MeasurableSet (endpointBall i ρ y) :=
    (measurableSet_endpointBall_pair i ρ).preimage (measurable_const.prodMk measurable_id)
  exact sbxS4_segmentExtension_stoppingGrid_interval Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν L g hg hmap hbits z₀ hzero hstart past hpast hstop hsegment
    N hN H hH hbH (fun γ => (endpointBall i ρ y).indicator (fun _ => (1 : ℝ)) (γ Δ))
    ((measurable_const.indicator hm).comp (continuous_eval_const Δ).measurable)
    (by
      obtain ⟨C, hC⟩ := sbxS4_indicator_bounded (endpointBall i ρ y)
        (fun _ => (1 : ℝ)) ⟨1, by simp⟩
      exact ⟨C, fun γ => hC (γ Δ)⟩)
    (fun γ γ' h => congrArg ((endpointBall i ρ y).indicator (fun _ => (1 : ℝ)))
      (h Δ le_rfl))

/-- The same endpoint identity at an almost surely finite extended selected trial;
the infinite-index branch is removed by the checked countable branch transport. -/
theorem sbxS4_segmentExtension_stoppingGrid_endpoint_ae
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (hstart : ∀ᵐ s ∂ν, (g s).1 0 = z)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (hsegment : ∀ (n : ℕ), ∀ᵐ s ∂ν, ∀ t : ℝ≥0, t ≤ Δ →
      (g s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t)
    (T : CoupledSample d → WithTop ℕ) (hTm : Measurable T)
    (hT : ∀ n : ℕ, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | T q = n})
    (hfinite : ∀ᵐ q ∂L (z, ω), ∃ n : ℕ, T q = n)
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C)
    (φ : Vec d → ℝ) (hφ : Measurable φ) (hbφ : BoundedRealTest φ) :
    let N := sbxS4ExtendedGridIndex T
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) *
      φ (q.1 ((N q : ℝ≥0) * Δ + Δ))) (L (z, ω)) ∧
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      endpointAverage i R (q.1 ((N q : ℝ≥0) * Δ)) φ) (L (z, ω)) ∧
    (∫ q, sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) *
      φ (q.1 ((N q : ℝ≥0) * Δ + Δ)) ∂L (z, ω)) =
      δ * (∫ q, sbxS4GridPastTest Δ N H q *
        endpointAverage i R (q.1 ((N q : ℝ≥0) * Δ)) φ ∂L (z, ω)) := by
  dsimp only
  apply sbxS4_gridInterval_successful_endpoint Δ R δ i P L (z, ω) hP hR hδ₀
    hminor (sbxS4ExtendedGridIndex T) _ φ hφ
  exact sbxS4_segmentExtension_stoppingGrid_interval_ae Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν L g hg hmap hbits z₀ hzero hstart past hpast hstop hsegment
    T hTm hT hfinite H hH hbH (fun γ => φ (γ Δ))
    (hφ.comp (continuous_eval_const Δ).measurable)
    (by obtain ⟨C, hC⟩ := hbφ; exact ⟨C, fun γ => hC (γ Δ)⟩)
    (fun γ γ' h => congrArg φ (h Δ le_rfl))

/-- At an almost surely finite selected trial, a contained subball has its
actual volume ratio against every bounded selected-past test. -/
theorem sbxS4_segmentExtension_stoppingGrid_successful_subball_ae
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (hstart : ∀ᵐ s ∂ν, (g s).1 0 = z)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (hsegment : ∀ (n : ℕ), ∀ᵐ s ∂ν, ∀ t : ℝ≥0, t ≤ Δ →
      (g s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t)
    (T : CoupledSample d → WithTop ℕ) (hTm : Measurable T)
    (hT : ∀ n : ℕ, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | T q = n})
    (hfinite : ∀ᵐ q ∂L (z, ω), ∃ n : ℕ, T q = n)
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C)
    (ρ : ℝ) (hρ : 0 < ρ) (y : Vec d)
    (hsub : ∀ᵐ q ∂L (z, ω), endpointBall i ρ y ⊆
      endpointBall i R (q.1 ((sbxS4ExtendedGridIndex T q : ℝ≥0) * Δ))) :
    let N := sbxS4ExtendedGridIndex T
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) *
      (endpointBall i ρ y).indicator (fun _ => (1 : ℝ))
        (q.1 ((N q : ℝ≥0) * Δ + Δ))) (L (z, ω)) ∧
    Integrable (fun q => sbxS4GridPastTest Δ N H q * (ρ / R) ^ d) (L (z, ω)) ∧
    (∫ q, sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) *
      (endpointBall i ρ y).indicator (fun _ => (1 : ℝ))
        (q.1 ((N q : ℝ≥0) * Δ + Δ)) ∂L (z, ω)) =
      δ * (∫ q, sbxS4GridPastTest Δ N H q * (ρ / R) ^ d ∂L (z, ω)) := by
  let φ : Vec d → ℝ := (endpointBall i ρ y).indicator (fun _ => (1 : ℝ))
  have hm : Measurable φ := measurable_const.indicator
    ((measurableSet_endpointBall_pair i ρ).preimage (measurable_const.prodMk measurable_id))
  have hb : BoundedRealTest φ := sbxS4_indicator_bounded _ _ ⟨1, by simp⟩
  have he := sbxS4_segmentExtension_stoppingGrid_endpoint_ae Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν L g hg hmap hbits z₀ hzero hstart past hpast hstop hsegment
    T hTm hT hfinite H hH hbH φ hm hb
  have havg : ∀ᵐ q ∂L (z, ω),
      sbxS4GridPastTest Δ (sbxS4ExtendedGridIndex T) H q *
        endpointAverage i R (q.1 ((sbxS4ExtendedGridIndex T q : ℝ≥0) * Δ)) φ =
      sbxS4GridPastTest Δ (sbxS4ExtendedGridIndex T) H q * (ρ / R) ^ d := by
    filter_upwards [hsub] with q hq
    rw [sbxS4_endpointAverage_subball i R ρ hR hρ _ y hq]
  exact ⟨he.1, he.2.1.congr havg, he.2.2.trans (congrArg (fun x : ℝ => δ * x)
    (integral_congr_ae havg))⟩

/-- The realized selected success branch assigns a contained subball its
Lebesgue volume ratio, including for an almost surely finite extended grid. -/
theorem sbxS4_segmentExtension_stoppingGrid_cond_subball_probability_ae
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (hstart : ∀ᵐ s ∂ν, (g s).1 0 = z)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (hsegment : ∀ (n : ℕ), ∀ᵐ s ∂ν, ∀ t : ℝ≥0, t ≤ Δ →
      (g s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t)
    (T : CoupledSample d → WithTop ℕ) (hTm : Measurable T)
    (hT : ∀ n : ℕ, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | T q = n})
    (hfinite : ∀ᵐ q ∂L (z, ω), ∃ n : ℕ, T q = n)
    (ρ : ℝ) (hρ : 0 < ρ) (y : Vec d)
    (hsub : ∀ᵐ q ∂L (z, ω), endpointBall i ρ y ⊆
      endpointBall i R (q.1 ((sbxS4ExtendedGridIndex T q : ℝ≥0) * Δ))) :
    let N := sbxS4ExtendedGridIndex T
    (cond (L (z, ω)) {q | q.2 (N q) = true}
      {q | q.1 ((N q : ℝ≥0) * Δ + Δ) ∈ endpointBall i ρ y}).toReal = (ρ / R) ^ d := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  let : IsProbabilityMeasure ν := sbxS4_extension_isProbabilityMeasure _ _ ν hν
  let : IsProbabilityMeasure (L (z, ω)) := hmap ▸ (inferInstance : IsProbabilityMeasure (ν.map g))
  let N := sbxS4ExtendedGridIndex T
  have hNm := sbxS4_measurable_extendedGridIndex T hTm
  have hm : MeasurableSet (endpointBall i ρ y) :=
    (measurableSet_endpointBall_pair i ρ).preimage (measurable_const.prodMk measurable_id)
  have hpastOne : sbxS4GridPastTest Δ N (fun _ _ => 1) = (fun _ => 1) := by
    funext q
    rfl
  have hIone : sbxS4GridIntervalTest Δ δ R i P L (z, ω) N (fun _ => 1) (fun _ => 1) := by
    rw [← hpastOne]
    exact (sbxS4_segmentExtension_stoppingGrid_interval_ae Δ R δ i P z ω hP hR hδ₀ hδ₁
        hminor K hK ν hν L g hg hmap hbits z₀ hzero hstart past hpast hstop hsegment
        T hTm hT hfinite (fun _ _ => 1) (fun _ => measurable_const)
        ⟨1, by simp⟩ (fun _ => 1) measurable_const ⟨1, by simp⟩ (by intros; rfl))
  have hI : sbxS4GridIntervalTest Δ δ R i P L (z, ω) N (fun _ => 1)
      (fun γ => (endpointBall i ρ y).indicator (fun _ => (1 : ℝ)) (γ Δ)) := by
    rw [← hpastOne]
    exact (sbxS4_segmentExtension_stoppingGrid_interval_ae Δ R δ i P z ω hP hR hδ₀ hδ₁
        hminor K hK ν hν L g hg hmap hbits z₀ hzero hstart past hpast hstop hsegment
        T hTm hT hfinite (fun _ _ => 1) (fun _ => measurable_const) ⟨1, by simp⟩
        (fun γ => (endpointBall i ρ y).indicator (fun _ => (1 : ℝ)) (γ Δ))
        ((measurable_const.indicator hm).comp (continuous_eval_const Δ).measurable)
        (by
          obtain ⟨C, hC⟩ := sbxS4_indicator_bounded (endpointBall i ρ y)
            (fun _ => (1 : ℝ)) ⟨1, by simp⟩
          exact ⟨C, fun γ => hC (γ Δ)⟩)
        (fun γ γ' h => congrArg ((endpointBall i ρ y).indicator (fun _ => (1 : ℝ)))
          (h Δ le_rfl)))
  exact sbxS4_gridInterval_cond_successful_subball_probability Δ R δ i P L (z, ω)
    hP hR hδ₀ hminor N hNm hIone ρ hρ y hsub hI

/-- Selected successful endpoints tested against a measurable set, with the
actual Lebesgue intersection ratio and source normalization. -/
theorem sbxS4_segmentExtension_stoppingGrid_endpoint_ae_indicator
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (z₀ : CoupledSample d)
    (hzero : ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ 0 (g s) = z₀)
    (hstart : ∀ᵐ s ∂ν, (g s).1 0 = z)
    (past : (n : ℕ) → sbxS4SplitHistory (Path d) n → CoupledSample d)
    (hpast : ∀ n, Measurable (past n))
    (hstop : ∀ n, ∀ᵐ s ∂ν, Probability.stoppedHistorySample Δ (n + 1) (g s) =
      past n (Preorder.frestrictLe n s))
    (hsegment : ∀ (n : ℕ), ∀ᵐ s ∂ν, ∀ t : ℝ≥0, t ≤ Δ →
      (g s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t)
    (T : CoupledSample d → WithTop ℕ) (hTm : Measurable T)
    (hT : ∀ n : ℕ, @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      {q | T q = n})
    (hfinite : ∀ᵐ q ∂L (z, ω), ∃ n : ℕ, T q = n)
    (H : ℕ → CoupledSample d → ℝ) (hH : ∀ n, Measurable (H n))
    (hbH : ∃ C : ℝ, ∀ n q, |H n q| ≤ C)
    (S : Set (Vec d)) (hS : MeasurableSet S) :
    let N := sbxS4ExtendedGridIndex T
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) *
      (S.indicator (fun _ => (1 : ℝ))) (q.1 ((N q : ℝ≥0) * Δ + Δ))) (L (z, ω)) ∧
    Integrable (fun q => sbxS4GridPastTest Δ N H q *
      ((volume (S ∩ endpointBall i R (q.1 ((N q : ℝ≥0) * Δ)))).toReal /
        (volume (endpointBall i R (q.1 ((N q : ℝ≥0) * Δ)))).toReal)) (L (z, ω)) ∧
    (∫ q, sbxS4GridPastTest Δ N H q *
      (if q.2 (N q) = true then (1 : ℝ) else 0) *
      (S.indicator (fun _ => (1 : ℝ))) (q.1 ((N q : ℝ≥0) * Δ + Δ)) ∂L (z, ω)) =
      δ * (∫ q, sbxS4GridPastTest Δ N H q *
        ((volume (S ∩ endpointBall i R (q.1 ((N q : ℝ≥0) * Δ)))).toReal /
        (volume (endpointBall i R (q.1 ((N q : ℝ≥0) * Δ)))).toReal) ∂L (z, ω)) := by
  dsimp only
  have h := sbxS4_segmentExtension_stoppingGrid_endpoint_ae Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν L g hg hmap hbits z₀ hzero hstart past hpast hstop hsegment
    T hTm hT hfinite H hH hbH (S.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hS) (sbxS4_indicator_bounded S _ ⟨1, by simp⟩)
  simpa only [sbxS4_endpointAverage_indicator i R _ S hS] using h

/-- All successful segments of the supplied infinite split law have the
source support at their actual previous endpoint. -/
theorem sbxS4_segmentExtension_ae_success_support :
    ∀ᵐ s ∂ν, ∀ n : ℕ, (s n).2 = true →
      (s n).1 Δ ∈ endpointBall i R (sbxS4SegmentBase Δ z n s) ∧
      ∀ t : ℝ≥0, t ≤ Δ →
        (s n).1 t ∈ couplingRegion i R (sbxS4SegmentBase Δ z n s) := by
  let : IsProbabilityMeasure (P (z, ω)) := hP z
  let : IsProbabilityMeasure (sbxS4FirstSegmentLaw Δ R δ i P z ω) :=
    (sbxS4_firstSegmentLaw_spec Δ R δ i P z ω hR hδ₀ hδ₁ (hminor z)).1
  apply ae_all_iff.mpr
  intro n
  cases n with
  | zero =>
    have h := sbxS4_firstSegmentLaw_ae_success_support Δ R δ i P z ω
    rw [← sbxS4_extension_map_zeroPair (sbxS4EndpointHistoryKernel Δ K) _ ν hν] at h
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable h
  | succ n =>
    have hm := sbxS4_extension_prefix_nextPair (sbxS4EndpointHistoryKernel Δ K)
      (sbxS4FirstSegmentLaw Δ R δ i P z ω) ν hν n
    have hs : ∀ᵐ q ∂(sbxS4SegmentPrefixLaw Δ R δ i P z ω K n ⊗ₘ
        sbxS4EndpointHistoryKernel Δ K n), q.2.2 = true →
        q.2.1 Δ ∈ endpointBall i R (sbxS4HistoryEndpoint Δ n q.1) ∧
        ∀ t : ℝ≥0, t ≤ Δ → q.2.1 t ∈ couplingRegion i R (sbxS4HistoryEndpoint Δ n q.1) := by
      apply Measure.ae_compProd_of_ae_ae
        (sbxS4_measurableSet_success_support Δ R i _ (sbxS4_measurable_historyEndpoint Δ n))
      apply Filter.Eventually.of_forall
      intro h
      change ∀ᵐ q ∂K (sbxS4HistoryEndpoint Δ n h), _
      rw [hK (sbxS4HistoryEndpoint Δ n h)]
      exact sbxS4_firstSegmentLaw_ae_success_support Δ R δ i P
        (sbxS4HistoryEndpoint Δ n h) ω
    dsimp only [sbxS4SegmentPrefixLaw] at hs
    rw [← hm] at hs
    exact ae_of_ae_map ((Preorder.measurable_frestrictLe n).prodMk
      (measurable_pi_apply (n + 1))).aemeasurable hs

omit hP hR hδ₀ hδ₁ hminor hK hν in
/-- The interval projection identifies each chronological base point with the
actual continuous path at that grid time. -/
theorem sbxS4_segmentBase_eq_realized
    (g : (ℕ → Path d × Bool) → CoupledSample d)
    (hstart : ∀ᵐ s ∂ν, (g s).1 0 = z)
    (hsegment : ∀ (n : ℕ), ∀ᵐ s ∂ν, ∀ t : ℝ≥0, t ≤ Δ →
      (g s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t) :
    ∀ᵐ s ∂ν, ∀ n : ℕ, sbxS4SegmentBase Δ z n s = (g s).1 ((n : ℝ≥0) * Δ) := by
  filter_upwards [hstart, ae_all_iff.mpr hsegment] with s hs hi
  intro n
  cases n with
  | zero => simpa only [sbxS4SegmentBase, Nat.cast_zero, zero_mul] using hs.symm
  | succ n =>
    change (s n).1 Δ = (g s).1 ((↑(n + 1) : ℝ≥0) * Δ)
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact (hi n Δ le_rfl).symm

/-- The actual realized law has simultaneous successful support at every grid
trial. This statement is stronger than support at any selected index. -/
theorem sbxS4_segmentExtension_successfulBridgeSupportAt
    (L : CoupledQuenchedLaws d)
    (g : (ℕ → Path d × Bool) → CoupledSample d) (hg : Measurable g)
    (hmap : ν.map g = L (z, ω))
    (hbits : ∀ n, ∀ᵐ s ∂ν, (g s).2 n = (s n).2)
    (hstart : ∀ᵐ s ∂ν, (g s).1 0 = z)
    (hsegment : ∀ (n : ℕ), ∀ᵐ s ∂ν, ∀ t : ℝ≥0, t ≤ Δ →
      (g s).1 ((n : ℝ≥0) * Δ + t) = (s n).1 t) :
    (∀ᵐ q ∂L (z, ω), ∀ n : ℕ, q.2 n = true →
      q.1 ((n : ℝ≥0) * Δ + Δ) ∈ endpointBall i R (q.1 ((n : ℝ≥0) * Δ))) ∧
    SuccessfulBridgeSupportAt Δ i R L (z, ω) := by
  have hs := sbxS4_segmentExtension_ae_success_support Δ R δ i P z ω hP hR hδ₀ hδ₁
    hminor K hK ν hν
  have hx := sbxS4_segmentBase_eq_realized Δ z ν g hstart hsegment
  have hm : MeasurableSet {q : CoupledSample d | ∀ n : ℕ, q.2 n = true →
      q.1 ((n : ℝ≥0) * Δ + Δ) ∈ endpointBall i R (q.1 ((n : ℝ≥0) * Δ)) ∧
      ∀ u : ℝ≥0, u ≤ Δ →
        q.1 ((n : ℝ≥0) * Δ + u) ∈ couplingRegion i R (q.1 ((n : ℝ≥0) * Δ))} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    have he : Measurable (fun q : CoupledSample d => q.1 ((n : ℝ≥0) * Δ)) :=
      (continuous_eval_const _).measurable.comp measurable_fst
    have ht : Measurable (fun q : CoupledSample d => pathTimeShift q.1 ((n : ℝ≥0) * Δ)) :=
      Probability.continuous_path_time_shift.measurable.comp
        (measurable_const.prodMk measurable_fst)
    have hc : Measurable (fun q : CoupledSample d => q.2 n) :=
      (measurable_pi_apply n).comp measurable_snd
    exact (sbxS4_measurableSet_success_support Δ R i _ he).preimage
      (measurable_id.prodMk (ht.prodMk hc))
  have hreal : ∀ᵐ q ∂L (z, ω), ∀ n : ℕ, q.2 n = true →
      q.1 ((n : ℝ≥0) * Δ + Δ) ∈ endpointBall i R (q.1 ((n : ℝ≥0) * Δ)) ∧
      ∀ u : ℝ≥0, u ≤ Δ →
        q.1 ((n : ℝ≥0) * Δ + u) ∈ couplingRegion i R (q.1 ((n : ℝ≥0) * Δ)) := by
    rw [← hmap]
    apply (ae_map_iff hg.aemeasurable hm).mpr
    filter_upwards [ae_all_iff.mpr hbits, hs, hx, ae_all_iff.mpr hsegment] with s hb hs hx hi
    intro n hbtrue
    have h := hs n (hb n ▸ hbtrue)
    rw [hx n] at h
    constructor
    · rw [hi n Δ le_rfl]
      exact h.1
    · intro u hu
      rw [hi n u hu]
      exact h.2 u hu
  refine ⟨hreal.mono fun _ h n hb => (h n hb).1, ?_⟩
  filter_upwards [hreal] with q h
  intro n hb t ht₀ ht₁
  have ht : t - (n : ℝ≥0) * Δ ≤ Δ := by
    rw [tsub_le_iff_right]
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using ht₁
  have hi := (h n hb).2 (t - (n : ℝ≥0) * Δ) ht
  rwa [add_tsub_cancel_of_le ht₀] at hi

end ActualStoppingGrid

end StoppingGrid

#print axioms sbxS4_gridInterval_cond_successful_endpoint
#print axioms sbxS4_endpointAverage_one
#print axioms sbxS4_gridInterval_success_mass
#print axioms sbxS4_gridInterval_successful_subball
#print axioms sbxS4_selected_success_support
#print axioms sbxS4_endpointBall_smul
#print axioms sbxS4_endpointBall_volume_scale
#print axioms sbxS4_endpointBall_volume_ratio
#print axioms sbxS4_endpointSubball_subset
#print axioms sbxS4_endpointAverage_subball

#print axioms sbxS4_firstCoinLaw_ae_success
#print axioms sbxS4_firstSegmentLaw_ae_success_support
#print axioms sbxS4_measurableSet_success_support
#print axioms sbxS4SegmentBase
#print axioms sbxS4_segmentExtension_ae_success_support
#print axioms sbxS4_segmentBase_eq_realized
#print axioms sbxS4_segmentExtension_successfulBridgeSupportAt

#print axioms sbxS4_integral_cond_endpointBall
#print axioms sbxS4_integral_killedBridgeMixture_endpoint
#print axioms sbxS4_endpointBall_normalization
#print axioms sbxS4_endpointAverage_indicator
#print axioms sbxS4_endpointAverage_indicator_of_subset
#print axioms sbxS4_gridInterval_successful_endpoint
#print axioms sbxS4_segmentExtension_stoppingGrid_endpoint
#print axioms sbxS4_segmentExtension_stoppingGrid_endpoint_indicator
#print axioms sbxS4_segmentExtension_stoppingGrid_endpoint_ae
#print axioms sbxS4_segmentExtension_stoppingGrid_endpoint_ae_indicator

#print axioms sbxS4_integral_grid_test_transfer
#print axioms sbxS4_freshBitsAt_stoppingGrid
#print axioms sbxS4_hasSum_integral_grid_ae
#print axioms sbxS4_integral_grid_transfer_ae

#print axioms sbxS4GridIntervalTest
#print axioms sbxS4_segmentExtension_stoppingGrid_interval
#print axioms sbxS4_segmentExtension_stoppingGrid_freshBit

#print axioms sbxS4ExtendedGridIndex
#print axioms sbxS4_measurable_extendedGridIndex
#print axioms sbxS4_extendedGridPastTest_branch_measurable
#print axioms sbxS4_integral_grid_test_transfer_ae
#print axioms sbxS4_freshBitsAt_stoppingGrid_ae
#print axioms sbxS4_segmentExtension_stoppingGrid_interval_ae
#print axioms sbxS4_segmentExtension_futureBits_test
#print axioms sbxS4_segmentExtension_stoppingGrid_futureBits
#print axioms sbxS4_segmentExtension_stoppingGrid_map_futureBits
#print axioms sbxS4_segmentExtension_stoppingGrid_integrable_futureBits
#print axioms sbxS4_segmentExtension_stoppingGrid_integrable_past_futureBits
#print axioms sbxS4_segmentExtension_stoppingGrid_futureBits_ae
#print axioms sbxS4_segmentExtension_stoppingGrid_map_futureBits_ae
#print axioms sbxS4_segmentExtension_stoppingGrid_integrable_futureBits_ae
#print axioms sbxS4_segmentExtension_stoppingGrid_integrable_past_futureBits_ae
#print axioms sbxS4_segmentExtension_stoppingGrid_integrable_joint_futureBits
#print axioms sbxS4_segmentExtension_stoppingGrid_integrable_joint_futureBits_ae

#print axioms sbxS4GridPastTest
#print axioms sbxS4_measurable_grid_select
#print axioms sbxS4_measurable_grid_index
#print axioms sbxS4_measurable_gridPastTest
#print axioms sbxS4_gridPastTest_branch_measurable
#print axioms sbxS4_gridPastTest_bounded
#print axioms sbxS4_indicator_bounded
#print axioms sbxS4_integral_bounded_grid
#print axioms sbxS4_hasSum_integral_grid
#print axioms sbxS4_integral_grid_transfer


#print axioms sbxS4_segmentExtensions_hasOneIntervalKernel
#print axioms sbxS4_splitPrefixLaw_prefix_nextPair
#print axioms sbxS4_extension_map_zeroPair
#print axioms sbxS4_extension_prefix_nextPair
#print axioms sbxS4_extension_integral_branch
#print axioms sbxS4_extension_integrable_branch
#print axioms sbxS4_measurable_split_expectations
#print axioms sbxS4_integrable_split_expectations
#print axioms sbxS4_segmentExtension_integrable_branch
#print axioms sbxS4_segmentExtension_integral_branch
#print axioms sbxS4_segmentExtension_interval_test
#print axioms sbxS4_integrable_interval_bit
#print axioms sbxS4_segmentExtension_initial_test
#print axioms sbxS4_segmentExtension_oneIntervalKernelAt


#print axioms sbxS4_map_endpoint_reweight
#print axioms sbxS4_endpoint_reweight_le_of_minorization
#print axioms sbxS4_endpoint_ac_of_minorization
#print axioms sbxS4_map_killedBridgeMixture_endpoint
#print axioms sbxS4_killedBridgeMixture_integrable_endpoint
#print axioms sbxS4_gridInterval_cond_successful_subball
#print axioms sbxS4_gridInterval_cond_successful_subball_probability
#print axioms sbxS4_segmentExtension_stoppingGrid_successful_subball
#print axioms sbxS4_segmentExtension_stoppingGrid_successful_subball_ae
#print axioms sbxS4_segmentExtension_stoppingGrid_cond_subball_probability_ae
#print axioms sbxS4_killedBridgeMixture_isProbabilityMeasure
#print axioms sbxS4_smul_killedBridgeMixture_le
#print axioms sbxS4SplitResidual
#print axioms sbxS4_splitResidual_isProbabilityMeasure
#print axioms sbxS4_smul_splitResidual
#print axioms sbxS4_splitResidual_recovery
#print axioms sbxS4_splitResidual_recovery_apply
#print axioms sbxS4_integrable_splitResidual
#print axioms sbxS4_splitResidual_integral_recovery
#print axioms sbxS4FailedSegmentLaw
#print axioms sbxS4_failedSegmentLaw_isProbabilityMeasure
#print axioms sbxS4_failedSegmentLaw_recovery
#print axioms sbxS4_failedSegmentLaw_integral_recovery
#print axioms sbxS4_splitResidual_apply
#print axioms sbxS4_failedSegmentLaw_apply
#print axioms sbxS4_failedSegmentLaw_integral_difference

#print axioms sbxS4FirstCoinLaw
#print axioms sbxS4_firstCoinLaw_apply
#print axioms sbxS4_firstCoinLaw_map_fst
#print axioms sbxS4_firstCoinLaw_isProbabilityMeasure
#print axioms sbxS4_firstCoinLaw_map_snd
#print axioms sbxS4_firstCoinLaw_restrict_map_fst
#print axioms sbxS4_firstCoinLaw_cond_map_fst

#print axioms sbxS4_firstCoinLaw_integral_branch
#print axioms sbxS4_firstCoinLaw_integrable_branch
#print axioms sbxS4FirstSegmentLaw
#print axioms sbxS4_firstSegmentLaw_spec
#print axioms sbxS4_firstSegmentLaw_cond_endpoint
#print axioms sbxS4_measurableSet_stays
#print axioms sbxS4_ae_killedBridgeMixture_stays
#print axioms sbxS4_firstSegmentLaw_cond_stays
#print axioms sbxS4_firstSegmentLaw_integral_branch

#print axioms sbxS4RemainingBitsLaw
#print axioms sbxS4_remainingBitsLaw_isProbabilityMeasure
#print axioms sbxS4_remainingBitsLaw_map_eval
#print axioms sbxS4AttachRemainingBits
#print axioms sbxS4_measurable_attachRemainingBits
#print axioms sbxS4AttachBitsLaw
#print axioms sbxS4_attachBitsLaw_map_split
#print axioms sbxS4_attachBitsLaw_isProbabilityMeasure
#print axioms sbxS4_attachBitsLaw_map_first
#print axioms sbxS4FirstSegmentWithBitsLaw
#print axioms sbxS4_firstSegmentWithBitsLaw_spec

#print axioms sbxS4SplitHistory
#print axioms sbxS4InitialHistory
#print axioms sbxS4_measurable_initialHistory
#print axioms sbxS4SplitPrefixLaw
#print axioms sbxS4_splitPrefixLaw_isProbabilityMeasure
#print axioms sbxS4_splitPrefixLaw_zero
#print axioms sbxS4_splitPrefixLaw_truncate
#print axioms sbxS4_splitPrefixLaw_restart
#print axioms sbxS4_splitPrefixLaw_integral_restart
#print axioms sbxS4AppendHistory
#print axioms sbxS4_measurable_appendHistory
#print axioms sbxS4_partialTraj_succ
#print axioms sbxS4_splitPrefixLaw_succ
#print axioms sbxS4_splitPrefixLaw_integral_branch
#print axioms sbxS4_splitPrefixLaw_integrable_branch

#print axioms sbxS4_appendHistory_last
#print axioms sbxS4_appendHistory_old
#print axioms sbxS4CoinPrefixEvent
#print axioms sbxS4_measurableSet_coinPrefixEvent
#print axioms sbxS4_appendHistory_preimage_coinPrefixEvent
#print axioms sbxS4_firstCoinLaw_coin_mass
#print axioms sbxS4_splitPrefixLaw_nextCoin_mass
#print axioms sbxS4_splitPrefixLaw_coin_cylinder

#print axioms sbxS4HistoryEndpoint
#print axioms sbxS4_measurable_historyEndpoint
#print axioms sbxS4EndpointHistoryKernel
#print axioms sbxS4_endpointHistoryKernel_isMarkov
#print axioms sbxS4SegmentPrefixLaw
#print axioms sbxS4_firstSegmentLaw_coin_mass
#print axioms sbxS4_segmentPrefixLaw_isProbabilityMeasure
#print axioms sbxS4_segmentPrefixLaw_coin_cylinder
#print axioms sbxS4_segmentPrefixLaw_integral_branch

#print axioms sbxS4_appendHistory_restrict
#print axioms sbxS4_splitPrefixLaw_integral_last

#print axioms sbxS4BernoulliLaw
#print axioms sbxS4_bernoulliLaw_singleton
#print axioms sbxS4_bernoulliLaw_isProbabilityMeasure
#print axioms sbxS4FutureCoins
#print axioms sbxS4_measurable_futureCoins
#print axioms sbxS4_historyKernel_map_coin
#print axioms sbxS4_splitPrefixLaw_prefix_nextCoin
#print axioms sbxS4_extension_isProbabilityMeasure
#print axioms sbxS4_extension_prefix_nextCoin
#print axioms sbxS4_extension_map_nextCoin
#print axioms sbxS4_extension_indep_prefix_nextCoin
#print axioms sbxS4_extension_future_coin_cylinder
#print axioms sbxS4_extension_restrict_map_futureCoins
#print axioms sbxS4_extension_map_futureCoins
#print axioms sbxS4_extension_prefix_futureCoins
#print axioms sbxS4_extension_indep_prefix_futureCoins

#print axioms sbxS4_extension_integral_futureCoins

#print axioms sbxS4_extension_map_zeroCoin

#print axioms sbxS4_extension_map_coin

#print axioms sbxS4_extension_coin_cylinder

#print axioms sbxS4_extension_map_coins

#print axioms sbxS4_extension_integral_coin

#print axioms sbxS4_extension_freshBitsAt

#print axioms sbxS4_endpointHistoryKernel_coin_mass

#print axioms sbxS4_segmentExtension_map_coins

#print axioms sbxS4_segmentExtension_prefix_futureCoins

#print axioms sbxS4_segmentExtension_integral_futureCoins

#print axioms sbxS4_extensions_hasFreshBits

#print axioms sbxS4_segmentExtension_freshBitsAt

end EinsteinFull.Blueprint

#print axioms EinsteinFull.Blueprint.sbxS4_segmentExtension_initial_integrable_branch

#lint

#print axioms EinsteinFull.Blueprint.sbxS4_segmentExtension_stoppingGrid_indep_futureBits

#print axioms EinsteinFull.Blueprint.sbxS4_segmentExtension_stoppingGrid_integral_past_futureBits

#print axioms EinsteinFull.Blueprint.sbxS4_endpointHistoryKernel_forget_coin

#print axioms EinsteinFull.Blueprint.sbxS4_endpointHistoryKernel_forget_coin_stopped

#print axioms EinsteinFull.Blueprint.sbxS4_endpointHistoryKernel_stopped_integral

#print axioms EinsteinFull.Blueprint.sbxS4_endpointHistoryKernel_forget_coin_ae

#print axioms EinsteinFull.Blueprint.sbxS4_endpointHistoryKernel_forget_coin_stopped_ae
#print axioms EinsteinFull.Blueprint.sbxS4_endpointHistoryKernel_stopped_integral_ae

#print axioms EinsteinFull.Blueprint.sbxS4_segmentPrefixLaw_stopped_last_ae

#print axioms EinsteinFull.Blueprint.sbxS4AppendPaths
#print axioms EinsteinFull.Blueprint.sbxS4_segmentPrefixLaw_stopped_append_ae

#print axioms EinsteinFull.Blueprint.sbxS4_segmentPrefixLaw_stopped_append_map_ae

#print axioms EinsteinFull.Blueprint.sbxS4_segmentPrefixLaw_good_endpoints_ae

#print axioms EinsteinFull.Blueprint.sbxS4_segmentPrefixLaw_endpoint_mem_ae

#print axioms EinsteinFull.Blueprint.sbxS4_segmentPrefixLaw_endpoint_mem_of_original_ae

#print axioms EinsteinFull.Blueprint.sbxS4_splitPrefixLaw_integral_branch_ae

#print axioms EinsteinFull.Blueprint.sbxS4_segmentPrefixLaw_integral_last_ae
