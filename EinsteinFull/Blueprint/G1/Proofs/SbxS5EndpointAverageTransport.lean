import EinsteinFull.Blueprint.G1.Proofs.SbxS9CouplingAlgebraRecenter
import EinsteinFull.Blueprint.G1.Proofs.SbxS5Independence
import EinsteinFull.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinRelation.Regeneration.EndpointAverageFubini
import EinsteinFull.Blueprint.G1.Proofs.SbxS5CouplingAnalyticRecenter
import EinsteinFull.Frozen.RegenerationRecord
import EinsteinFull.Frozen.RegenerationNoReturn
import EinsteinRelation.Regeneration.RecenterNoBacktracking
import EinsteinRelation.Regeneration.KilledFutureConditionalMean
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Tactic.Linter

/-!
# Spatial transport of the actual successful-endpoint average

Source `paper/main.tex:1510–1516`. This module isolates the endpoint clause
from the Radon–Nikodym bridge assembly. Translation preserves the literal
Euclidean ball and its volume normalization. Bounded measurable tests give
integrable expressions on the actual probability fibres. The origin and
product-a.e. conclusions share a volume-a.e. set of recentering points.
The local-field-weighted slice calculation factors the translated-origin
comparison and expresses the remaining actual slice defect as an integrable
difference between the original and recentered origin coupling measures.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinFull.Blueprint.EndpointAverageTransport

open EinsteinRelation EinsteinRelation.Regeneration

/-- Translating the restricted spatial volume preserves the exact endpoint ball. -/
theorem map_endpointBall_volume_sub {d : ℕ} (a x : Vec d) (i : Fin d) (R : ℝ) :
    (volume.restrict (endpointBall i R x)).map (MeasurableEquiv.addRight (-a)) =
      volume.restrict (endpointBall i R (x - a)) := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight (-a)
  have hv : (volume : Measure (Vec d)).map e = volume :=
    (measurePreserving_add_right volume (-a)).map_eq
  have hB : e ⁻¹' endpointBall i R (x - a) = endpointBall i R x := by
    ext v
    exact sub_mem_endpointBall_iff i R a v x
  rw [← hB, ← e.restrict_map, hv]

/-- Translation preserves both the integral and its conditional-volume denominator.
No positivity is needed for this equality of the literal real-valued averages. -/
theorem endpointAverage_sub {d : ℕ} (a x : Vec d) (i : Fin d)
    (R : ℝ) (φ : Vec d → ℝ) :
    endpointAverage i R (x - a) φ =
      endpointAverage i R x (fun v => φ (v - a)) := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight (-a)
  have hv : (volume : Measure (Vec d)).map e = volume :=
    (measurePreserving_add_right volume (-a)).map_eq
  have hB : e ⁻¹' endpointBall i R (x - a) = endpointBall i R x := by
    ext v
    exact sub_mem_endpointBall_iff i R a v x
  have hm : volume (endpointBall i R (x - a)) =
      volume (endpointBall i R x) := by
    calc
      _ = (volume.map e) (endpointBall i R (x - a)) := by rw [hv]
      _ = _ := by rw [e.measurableEmbedding.map_apply, hB]
  unfold endpointAverage
  rw [hm]
  congr 1
  calc
    _ = ∫ v in endpointBall i R (x - a), φ v ∂(volume.map e) := by rw [hv]
    _ = _ := by rw [e.restrict_map, hB, integral_map_equiv]; rfl

/-- The moving endpoint average is a measurable function of the actual path. -/
theorem measurable_endpointAverage_path {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (i : Fin d) (R : ℝ) (φ : Vec d → ℝ) (hφ : Measurable φ) :
    Measurable (fun z : CoupledSample d =>
      endpointAverage i R (z.1 ((n : ℝ≥0) * Δ)) φ) :=
  measurable_endpointAverage i R _
    ((measurable_pathPosition _).comp measurable_fst)
    (fun q : CoupledSample d × Vec d => φ q.2) (hφ.comp measurable_snd)

/-- Positive-radius endpoint averaging preserves boundedness on the actual paths. -/
theorem boundedRealTest_endpointAverage_path {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (i : Fin d) (R : ℝ) (hR : 0 < R) (φ : Vec d → ℝ)
    (hbφ : BoundedRealTest φ) :
    BoundedRealTest (fun z : CoupledSample d =>
      endpointAverage i R (z.1 ((n : ℝ≥0) * Δ)) φ) := by
  obtain ⟨C, hC⟩ := hbφ
  exact boundedRealTest_endpointAverage i R hR _
    (fun q : CoupledSample d × Vec d => φ q.2) ⟨C, fun q => hC q.2⟩

/-- The true-bit weighted endpoint test is integrable on every finite fibre. -/
theorem integrable_successfulEndpoint_test {d : ℕ}
    (μ : Measure (CoupledSample d)) [IsFiniteMeasure μ] (Δ : ℝ≥0) (n : ℕ)
    (H : CoupledSample d → ℝ) (φ : Vec d → ℝ)
    (hH : Measurable H) (hbH : BoundedRealTest H)
    (hφ : Measurable φ) (hbφ : BoundedRealTest φ) :
    Integrable (fun z => H z * (if z.2 n = true then (1 : ℝ) else 0) *
      φ (z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ))) μ := by
  have hbit : Measurable (fun z : CoupledSample d =>
      if z.2 n = true then (1 : ℝ) else 0) :=
    Measurable.ite
      (((measurable_pi_apply (X := fun _ : ℕ => Bool) n).comp measurable_snd)
        (measurableSet_singleton true)) measurable_const measurable_const
  have hm : Measurable (fun z : CoupledSample d =>
      H z * (if z.2 n = true then (1 : ℝ) else 0) *
        φ (z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ))) := (hH.mul hbit).mul
    (hφ.comp ((measurable_pathPosition _).comp measurable_fst))
  obtain ⟨C, hC⟩ := hbH
  obtain ⟨B, hB⟩ := hbφ
  apply Integrable.of_bound hm.aestronglyMeasurable (max C 0 * max B 0)
  filter_upwards [] with z
  change ‖H z * (if z.2 n = true then (1 : ℝ) else 0) *
    φ (z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ))‖ ≤ _
  by_cases hz : z.2 n = true
  · simp only [hz, ↓reduceIte, mul_one, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((hC z).trans (le_max_left _ _))
      ((hB _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  · rw [ite_eq_right hz, mul_zero, zero_mul, norm_zero]
    exact mul_nonneg (le_max_right C 0) (le_max_right B 0)

/-- The past test times its moving endpoint average is integrable on finite fibres. -/
theorem integrable_endpointAverage_test {d : ℕ}
    (μ : Measure (CoupledSample d)) [IsFiniteMeasure μ] (Δ : ℝ≥0) (n : ℕ)
    (i : Fin d) (R : ℝ) (hR : 0 < R)
    (H : CoupledSample d → ℝ) (φ : Vec d → ℝ)
    (hH : Measurable H) (hbH : BoundedRealTest H)
    (hφ : Measurable φ) (hbφ : BoundedRealTest φ) :
    Integrable (fun z => H z *
      endpointAverage i R (z.1 ((n : ℝ≥0) * Δ)) φ) μ := by
  have hm := hH.mul (measurable_endpointAverage_path Δ n i R φ hφ)
  obtain ⟨C, hC⟩ := hbH
  obtain ⟨B, hB⟩ := boundedRealTest_endpointAverage_path Δ n i R hR φ hbφ
  apply Integrable.of_bound hm.aestronglyMeasurable (max C 0 * max B 0)
  filter_upwards [] with z
  change ‖H z * endpointAverage i R (z.1 ((n : ℝ≥0) * Δ)) φ‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul ((hC z).trans (le_max_left _ _))
    ((hB z).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)

/-- Pulling back the finite past and endpoint test transports the exact true-bit
identity, with the same parameters and the same conjugated kernel as the other clauses. -/
theorem uniformSuccessfulEndpointAt_recenter {d : ℕ}
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (K : CoupledQuenchedLaws d)
    (a : Vec d) (p : Vec d × FieldPair d)
    (hK : UniformSuccessfulEndpointAt Δ δ R i K (sbxS9RecenterInput a p)) :
    UniformSuccessfulEndpointAt Δ δ R i (sbxS9RecenteredCoupledLaws K a) p := by
  intro n H φ hH hbH hφ hbφ
  obtain ⟨C, hC⟩ := hbH
  obtain ⟨B, hB⟩ := hbφ
  have h := hK n (fun z => H (recenterSample a z)) (fun v => φ (v - a))
    (measurable_finiteHistory_comp_recenter Δ n a H hH) ⟨C, fun z => hC _⟩
    (hφ.comp (measurable_id.sub measurable_const)) ⟨B, fun v => hB _⟩
  rw [sbxS9RecenteredCoupledLaws_apply]
  simp only [integral_map_equiv, recenterSampleEquiv_apply, recenterSample,
    ContinuousMap.coe_mk, endpointAverage_sub]
  exact h

/-- Both endpoint expressions are genuine integrable tests on a recentered
probability fibre, using the finite-history sigma algebra of the source clause. -/
theorem endpoint_integrands_integrable_recenter {d : ℕ}
    (Δ : ℝ≥0) (n : ℕ) (i : Fin d) (R : ℝ) (hR : 0 < R)
    (K : CoupledQuenchedLaws d) (a : Vec d) (p : Vec d × FieldPair d)
    (hp : IsProbabilityMeasure (K (sbxS9RecenterInput a p)))
    (H : CoupledSample d → ℝ) (φ : Vec d → ℝ)
    (hH : Measurable[finiteHistorySigma Δ n] H) (hbH : BoundedRealTest H)
    (hφ : Measurable φ) (hbφ : BoundedRealTest φ) :
    Integrable (fun z => H z * (if z.2 n = true then (1 : ℝ) else 0) *
      φ (z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ))) (sbxS9RecenteredCoupledLaws K a p) ∧
    Integrable (fun z => H z * endpointAverage i R (z.1 ((n : ℝ≥0) * Δ)) φ)
      (sbxS9RecenteredCoupledLaws K a p) := by
  have := sbxS9_probability_recenter K a p hp
  have hm : Measurable H := hH.mono (Probability.finiteHistorySigma_le Δ n) le_rfl
  exact ⟨integrable_successfulEndpoint_test _ Δ n H φ hm hbH hφ hbφ,
    integrable_endpointAverage_test _ Δ n i R hR H φ hm hbH hφ hbφ⟩

/-- Stationarity and Fubini transport the origin and product-a.e. endpoint
clauses on one common spatial good set, without selecting an exceptional fibre. -/
theorem hasUniformSuccessfulEndpoint_recenter {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (K : CoupledQuenchedLaws d)
    (hK : HasUniformSuccessfulEndpoint Q Δ δ R i K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      HasUniformSuccessfulEndpoint Q Δ δ R i (sbxS9RecenteredCoupledLaws K a) := by
  filter_upwards [sbxS9_ae_recenterInput Q hQ hK.2] with a ha
  constructor
  · filter_upwards [ha.1] with η hη
    exact uniformSuccessfulEndpointAt_recenter Δ δ R i K a (0, η) hη
  · filter_upwards [ha.2] with p hp
    exact uniformSuccessfulEndpointAt_recenter Δ δ R i K a p hp

/-- The actual environment law gives a common spatial good set carrying both
probability fibres and their uniform successful-endpoint identities. -/
theorem probability_and_endpoint_recenter {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d) (hp : HasProbabilityLaws Q.measure K)
    (he : HasUniformSuccessfulEndpoint Q.measure Δ δ R i K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      HasProbabilityLaws Q.measure (sbxS9RecenteredCoupledLaws K a) ∧
      HasUniformSuccessfulEndpoint Q.measure Δ δ R i (sbxS9RecenteredCoupledLaws K a) := by
  filter_upwards [sbxS9_hasProbabilityLaws_recenter Q.measure Q.stationary K hp,
    hasUniformSuccessfulEndpoint_recenter Q.measure Q.stationary Δ δ R i K he]
    with a hpa hea
  exact ⟨hpa, hea⟩

/-- The whole future triple, including both reduced fields and every bit,
commutes with physical recentering. -/
theorem spatialFutureRecord_recenter {d : ℕ} (R : ℝ) (i : Fin d)
    (y : Vec d) (ω : FieldPair d) (z : CoupledSample d) :
    spatialFutureRecord R i (0, translate y ω) (recenterSample y z) =
      spatialFutureRecord R i (y, ω) z := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    simp only [spatialFutureRecord, recenterSample, ContinuousMap.coe_mk, sub_zero]
  · apply Prod.ext
    · rfl
    · funext x
      simp only [spatialFutureRecord, reduce_translate, translate_zero]

/-- The literal no-backtracking indicator is retained by the same change of variables. -/
theorem killedFutureTest_recenter_origin {d : ℕ} (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (y : Vec d) (ω : FieldPair d) (z : CoupledSample d) :
    killedFutureTest R i Φ ((0, translate y ω), recenterSample y z) =
      killedFutureTest R i Φ ((y, ω), z) := by
  unfold killedFutureTest
  rw [EinsteinRelation.Regeneration.noBacktracking_recenterSample_iff,
    spatialFutureRecord_recenter]

/-- Exact change of variables for the actual conjugated kernel, before any
comparison with the originally supplied kernel. -/
theorem killed_future_integral_recenter {d : ℕ} (K : CoupledQuenchedLaws d)
    (R : ℝ) (i : Fin d) (Φ : FutureState d i R → ℝ)
    (y : Vec d) (η : FieldPair d) :
    (∫ z, killedFutureTest R i Φ ((0, η), z)
      ∂sbxS9RecenteredCoupledLaws K y (0, η)) =
    ∫ z, killedFutureTest R i Φ ((y, translate (-y) η), z)
      ∂K (y, translate (-y) η) := by
  rw [sbxS5_analyticRecenterCoupling_apply, add_zero, integral_map_equiv]
  apply integral_congr_ae
  filter_upwards [] with z
  have hη : translate y (translate (-y) η) = η := by
    rw [translate_add, add_neg_cancel, translate_zero]
  simpa only [hη, recenterSampleEquiv_apply] using
    killedFutureTest_recenter_origin R i Φ y (translate (-y) η) z

/-- A bounded measurable killed test is Bochner integrable on every finite fibre. -/
theorem integrable_killedFutureTest {d : ℕ} (μ : Measure (CoupledSample d))
    [IsFiniteMeasure μ] (R : ℝ) (i : Fin d) (Φ : FutureState d i R → ℝ)
    (hΦ : Measurable Φ) (hb : BoundedRealTest Φ) (p : Vec d × FieldPair d) :
    Integrable (fun z => killedFutureTest R i Φ (p, z)) μ := by
  obtain ⟨C, hC⟩ := boundedRealTest_killedFutureTest R i Φ hb
  exact Integrable.of_bound
    ((measurable_killedFutureTest R i Φ hΦ).comp measurable_prodMk_left).aestronglyMeasurable
    C (ae_of_all _ fun z => (Real.norm_eq_abs _).symm ▸ hC (p, z))

/-- The finite probability part gives a jointly measurable killed-future mean. -/
theorem measurable_killed_future_mean {d : ℕ} (K : CoupledQuenchedLaws d)
    (R : ℝ) (i : Fin d) (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) :
    Measurable (fun p => ∫ z, killedFutureTest R i Φ (p, z)
      ∂Probability.probabilityPart K p) :=
  stronglyMeasurable_iff_measurable.mp
    ((measurable_killedFutureTest R i Φ hΦ).stronglyMeasurable.integral_kernel_prod_right'
      (κ := Probability.probabilityPart K))

/-- A common bound holds everywhere for the measurable probability-part mean. -/
theorem boundedRealTest_killed_future_mean {d : ℕ} (K : CoupledQuenchedLaws d)
    (R : ℝ) (i : Fin d) (Φ : FutureState d i R → ℝ) (hb : BoundedRealTest Φ) :
    BoundedRealTest (fun p => ∫ z, killedFutureTest R i Φ (p, z)
      ∂Probability.probabilityPart K p) := by
  obtain ⟨C, hC⟩ := boundedRealTest_killedFutureTest R i Φ hb
  refine ⟨max C 0, fun p => ?_⟩
  classical
  change |∫ z, killedFutureTest R i Φ (p, z) ∂Probability.probabilityPart K p| ≤ _
  rw [Probability.probabilityPart_apply]
  split_ifs with hp
  · have : IsProbabilityMeasure (K p) := ⟨hp⟩
    simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one,
      mul_one] using
      (norm_integral_le_of_norm_le_const (f := fun z => killedFutureTest R i Φ (p, z))
        (C := max C 0)
        (ae_of_all (K p) fun z => by
          simpa only [Real.norm_eq_abs] using (hC (p, z)).trans (le_max_left C 0)))
  · simp only [integral_zero_measure, abs_zero, le_max_iff, le_refl, or_true]

/-- Stationarity transports the actual annealed mean to the origin of the
conjugated kernel. The spatial qualifier comes from probability fibres only. -/
theorem annealed_killed_future_mean_recenter {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (R : ℝ) (i : Fin d) (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, ∫ z, killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω) ∂Q) =
      ∫ η, ∫ z, killedFutureTest R i Φ ((0, η), z)
        ∂sbxS9RecenteredCoupledLaws K y (0, η) ∂Q := by
  filter_upwards [Measure.ae_ae_of_ae_prod hK.2] with y hy
  let B : Vec d × FieldPair d → ℝ := fun p =>
    ∫ z, killedFutureTest R i Φ (p, z) ∂Probability.probabilityPart K p
  have hB := measurable_killed_future_mean K R i Φ hΦ
  have heq : ∀ᵐ ω ∂Q, B (y, ω) =
      ∫ z, killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω) := by
    filter_upwards [hy] with ω hω
    have := hω
    dsimp only [B]
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
  have ht : ∀ᵐ η ∂Q, B (y, translate (-y) η) =
      ∫ z, killedFutureTest R i Φ ((y, translate (-y) η), z)
        ∂K (y, translate (-y) η) :=
    (show MeasurePreserving (translate (-y)) Q Q from
      ⟨Probability.measurable_translate (-y), hQ (-y)⟩).quasiMeasurePreserving.ae heq
  calc
    _ = ∫ ω, B (y, ω) ∂Q := (integral_congr_ae heq).symm
    _ = ∫ η, B (y, translate (-y) η) ∂Q :=
      (Probability.integral_translate Q hQ (-y) _
        (hB.comp measurable_prodMk_left)).symm
    _ = _ := (integral_congr_ae ht).trans <|
      integral_congr_ae (ae_of_all _ fun η =>
        (killed_future_integral_recenter K R i Φ y η).symm)

/-- The measurable finite-part version has the original origin and product
qualifiers; hence both actual annealed means are Bochner integrable. -/
theorem integrable_annealed_killed_future_means {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (R : ℝ) (i : Fin d) (Φ : FutureState d i R → ℝ)
    (hΦ : Measurable Φ) (hb : BoundedRealTest Φ) :
    Integrable (fun ω => ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω)) Q ∧
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      Integrable (fun ω => ∫ z, killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω)) Q := by
  let B : Vec d × FieldPair d → ℝ := fun p =>
    ∫ z, killedFutureTest R i Φ (p, z) ∂Probability.probabilityPart K p
  have hB := measurable_killed_future_mean K R i Φ hΦ
  obtain ⟨C, hC⟩ := boundedRealTest_killed_future_mean K R i Φ hb
  have hint (y : Vec d) : Integrable (fun ω => B (y, ω)) Q :=
    Integrable.of_bound (hB.comp measurable_prodMk_left).aestronglyMeasurable C
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hC (y, ω))
  have heq (y : Vec d) (hy : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (y, ω))) :
      (fun ω => B (y, ω)) =ᵐ[Q]
        (fun ω => ∫ z, killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω)) := by
    filter_upwards [hy] with ω hω
    have := hω
    dsimp only [B]
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
  exact ⟨(hint 0).congr (heq 0 hK.1),
    (Measure.ae_ae_of_ae_prod hK.2).mono fun y hy => (hint y).congr (heq y hy)⟩

/-- The literal origin killed mean is the frozen zero-th record integral
restricted to the frozen no-return event. -/
theorem killed_future_origin_eq_frozen_record {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hb : BoundedRealTest Φ) :
    (∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, ω), z)
      ∂K (0, ω) ∂Q.measure) =
    ∫ q in regenerationNoReturn hd (l / lam), Φ (regenerationRecord hd lam l 0 q)
      ∂annealedCoupledLaw Q.measure K := by
  classical
  let F : FieldPair d × CoupledSample d → ℝ := fun q =>
    killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, q.1), q.2)
  have hF : Measurable F :=
    (measurable_killedFutureTest _ _ Φ hΦ).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hbF : BoundedRealTest F := by
    obtain ⟨C, hC⟩ := boundedRealTest_killedFutureTest _ _ Φ hb
    exact ⟨C, fun q => hC _⟩
  have hD : MeasurableSet (regenerationNoReturn hd (l / lam)) :=
    (measurableSet_NoBacktracking _ _).preimage measurable_snd.fst
  rw [← integral_annealedCoupledLaw Q.measure K hK.1 F hF hbF,
    ← integral_indicator hD]
  apply integral_congr_ae
  filter_upwards [ae_origin_start_of_isGMPReducedKernel hd Q lam h0 h1 P K
    hK.1 hK.2.1 hK.2.2.1] with q hq
  have hr := spatialFutureRecord_origin_eq_iteratedRecord_zero
    (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) q.1 q.2 hq
  change spatialFutureRecord _ _ _ _ = regenerationRecord hd lam l 0 q at hr
  change (if NoBacktracking (l / lam) q.2.1 (Renewal.forceCoord hd) then
    Φ (spatialFutureRecord _ _ _ _) else 0) = _
  rw [hr]
  rfl

/-- Recentered paths start at the declared point, using only the supplied
path law's all-start property in the translated environment. -/
theorem path_starts_recenter {d : ℕ} (P : QuenchedPathLaws d)
    (a : Vec d) (η : FieldPair d)
    (hs : ∀ x, ∀ᵐ γ ∂P (x, translate (-a) η), γ 0 = x) :
    ∀ x, ∀ᵐ γ ∂sbxS9RecenteredPathLaws P a (x, η), γ 0 = x := by
  intro x
  rw [sbxS5_analyticRecenterPaths_apply,
    (recenterPathEquiv a).measurableEmbedding.ae_map_iff]
  filter_upwards [hs (a + x)] with γ hγ
  change γ 0 - a = x
  rw [hγ]
  abel

/-- Conditional structural comparison. Its only new mathematical premise is
the precise underlying path-measure identity, at the origin and product-a.e.
No second GMP realization or killed-mean identity is assumed. -/
theorem coupling_origin_eq_recenter_assuming_path_laws {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      ((∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
        ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
          P p = sbxS9RecenteredPathLaws P a p) →
      ∀ᵐ η ∂Q.measure, K (0, η) = sbxS9RecenteredCoupledLaws K a (0, η) := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2))
  have hg := ae_coupledEnvironmentRegular hd Q lam h0.le h1 P K
    hK.1 hK.2.1 hK.2.2.1 (Renewal.regenDelta lam) hΔ δ (l / lam)
    (Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.2
  filter_upwards [sbxS5_seven_coupling_clauses_recenter hd Q.ellipticity_parameter
    Q lam l δ h0.le h1 P K hK] with a ha
  intro hP
  obtain ⟨hp, hm, _, hr, _, _, ho⟩ := ha
  have hreg : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) (sbxS9RecenteredPathLaws P a)
        (sbxS9RecenteredCoupledLaws K a) p := by
    filter_upwards [hp.2, hm.2, hr.2, ho.2] with p hpp hmp hrp hop
    exact ⟨hpp, hmp, hrp, hop⟩
  have hsp := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := Q.measure)
      (ν := (volume : Measure (Vec d)))).quasiMeasurePreserving.ae
      (hreg.and hP.2))
  have htrans := (show MeasurePreserving (translate (-a)) Q.measure Q.measure from
    ⟨Probability.measurable_translate (-a), Q.stationary (-a)⟩).quasiMeasurePreserving.ae
      hK.2.2.1
  filter_upwards [hg, htrans, hp.1, hm.1, hr.1, ho.1, hP.1, hsp]
    with η hgη htη hpη hmη hrη hoη hPη hspη
  have hs : ∀ x, ∀ᵐ γ ∂P (x, η), γ 0 = x := by
    obtain ⟨_, r, heq⟩ := hgη.1
    intro x
    rw [heq x]
    exact r.pathLaw_starts_at x
  have hs' : ∀ x, ∀ᵐ γ ∂sbxS9RecenteredPathLaws P a (x, η), γ 0 = x := by
    apply path_starts_recenter
    obtain ⟨_, r, heq⟩ := htη
    intro x
    rw [heq x]
    exact r.pathLaw_starts_at x
  have hboth : ∀ᵐ x ∂(volume : Measure (Vec d)),
      CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) P K (x, η) ∧
      CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) (sbxS9RecenteredPathLaws P a)
        (sbxS9RecenteredCoupledLaws K a) (x, η) ∧
      P (x, η) = sbxS9RecenteredPathLaws P a (x, η) := by
    filter_upwards [hgη.2.2.1, hspη] with x hx hx'
    exact ⟨hx, hx'.1, hx'.2⟩
  have := hgη.2.1.1
  have := hpη
  exact measure_eq_of_finite_history_integrals _ _ (Renewal.regenDelta lam) hΔ
    (sbxS9_finite_histories_eq_of_path_laws_eq _ hΔ δ (l / lam)
      (Renewal.forceCoord hd) P (sbxS9RecenteredPathLaws P a) K
      (sbxS9RecenteredCoupledLaws K a) 0 η hs hs' hgη.2.1
      ⟨hpη, hmη, hrη, hoη⟩ hPη hboth (fun n hn => hgη.2.2.2 n hn 0))

/-- The literal future-mean conclusion used in the source factorization,
conditional on the outstanding CARVER-F path-law identity. All seven coupling
clauses, all starts, and endpoint densities are derived from the supplied `hK`.
This support theorem is not an independence reduction. -/
theorem annealed_killed_future_mean_eq_frozen_record_assuming_path_laws {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hP : ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        P p = sbxS9RecenteredPathLaws P a p)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hb : BoundedRealTest Φ) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((y, ω), z)
        ∂K (y, ω) ∂Q.measure) =
      ∫ q in regenerationNoReturn hd (l / lam), Φ (regenerationRecord hd lam l 0 q)
        ∂annealedCoupledLaw Q.measure K := by
  filter_upwards [annealed_killed_future_mean_recenter Q.measure Q.stationary K hK.1
    (l / lam) (Renewal.forceCoord hd) Φ hΦ,
    coupling_origin_eq_recenter_assuming_path_laws hd Q lam h0 h1 l δ P K hK, hP]
    with y hmean hcompare hPy
  rw [hmean]
  calc
    _ = ∫ η, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, η), z)
        ∂K (0, η) ∂Q.measure :=
      integral_congr_ae ((hcompare hPy).mono fun η hη => by rw [← hη])
    _ = _ := killed_future_origin_eq_frozen_record hd Q lam h0.le h1 l δ P K hK Φ hΦ hb

/-- The finite-range calculation with the source's local environment factor
`F`. The only local-version input not supplied by the past and slice nodes is
that of `B` itself. This is a support calculation, not an extra graph premise
or an independence reduction. Low endpoints are removed using the actual
origin path law and source slice geometry. -/
theorem weighted_spatial_factor_of_local_future_versions
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) (B : Vec d × FieldPair d → ℝ)
    (hlocal : ∀ᵐ y ∂(volume : Measure (Vec d)),
      10 * (l / lam) ≤ y (Renewal.forceCoord hd) →
      ∃ B' : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d |
          y (Renewal.forceCoord hd) - 2 * (l / lam) ≤ x (Renewal.forceCoord hd)}] B' ∧
        (fun ω => B (y, ω)) =ᵐ[Q.measure] B') :
    (∫ y, ∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1) K H (y, ω)) * B (y, ω) ∂Q.measure) =
      ∫ y, (∫ ω, F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω) ∂Q.measure) *
          ∫ ω, B (y, ω) ∂Q.measure := by
  apply integral_congr_ae
  filter_upwards [hlocal] with y hy
  by_cases hhigh : 10 * (l / lam) ≤ y (Renewal.forceCoord hd)
  · obtain ⟨A', hA', hAe⟩ := sbxS5_pastFactor_local hd Q lam h0 h1 l δ
      hl hsep hδ0 hδ1 P K hK hpast F hF (n - 1) H hH hbH y hhigh
    obtain ⟨B', hB', hBe⟩ := hy hhigh
    exact integral_mul_eq_of_corrected_halfSpace_versions Q (Renewal.forceCoord hd)
      (y (Renewal.forceCoord hd)) (l / lam) (sbxS5_radius_gap hl h0 h1 hsep)
      _ _ A' B' hA' hB' hAe hBe
  · have hz := sbxS5_firstSlicePast_zero hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
      P K hK hslices n hn H y (lt_of_not_ge hhigh)
    have hA0 : (∫ ω, F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω) ∂Q.measure) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hz] with ω hω
      simp only [Pi.zero_apply] at hω ⊢
      rw [hω, mul_zero]
    have hAB0 : (∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)) * B (y, ω) ∂Q.measure) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hz] with ω hω
      simp only [Pi.zero_apply] at hω ⊢
      rw [hω, mul_zero, zero_mul]
    rw [hAB0, hA0, zero_mul]

/-- The same weighted calculation when the future mean is spatially constant.
The local version and mean remain visible internal producer obligations. -/
theorem weighted_spatial_factor_of_local_future_versions_and_mean
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) (B : Vec d × FieldPair d → ℝ)
    (hlocal : ∀ᵐ y ∂(volume : Measure (Vec d)),
      10 * (l / lam) ≤ y (Renewal.forceCoord hd) →
      ∃ B' : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d |
          y (Renewal.forceCoord hd) - 2 * (l / lam) ≤ x (Renewal.forceCoord hd)}] B' ∧
        (fun ω => B (y, ω)) =ᵐ[Q.measure] B')
    (b : ℝ) (hmean : ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, B (y, ω) ∂Q.measure) = b) :
    (∫ y, ∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1) K H (y, ω)) * B (y, ω) ∂Q.measure) =
      (∫ y, ∫ ω, F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω) ∂Q.measure) * b := by
  rw [weighted_spatial_factor_of_local_future_versions hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hpast hslices F hF n hn H hH hbH B hlocal,
    ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [hmean] with y hy
  rw [hy]

/-- The source past/future nodes directly instantiate the weighted calculation
for the translated origin future. This consumer uses their actual joint-field
versions and stationarity, with no assumed local version or mean. Identifying
this comparison factor with the off-origin factor remains separate. -/
theorem weighted_translated_origin_future_spatial_factor
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ y, ∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1) K H (y, ω)) *
        (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
          ((0, translate y ω), z) ∂K (0, translate y ω)) ∂Q.measure) =
      (∫ y, ∫ ω, F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω) ∂Q.measure) *
      ∫ q in regenerationNoReturn hd (l / lam), Φ (regenerationRecord hd lam l 0 q)
        ∂annealedCoupledLaw Q.measure K := by
  refine weighted_spatial_factor_of_local_future_versions_and_mean hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hpast hslices F hF n hn H hH hbH
    (fun p => ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
      ((0, translate p.1 p.2), z) ∂K (0, translate p.1 p.2)) ?_
    (∫ q in regenerationNoReturn hd (l / lam), Φ (regenerationRecord hd lam l 0 q)
      ∂annealedCoupledLaw Q.measure K) ?_
  · exact ae_of_all _ fun y _ => by
      obtain ⟨B', hB', hBe, _⟩ := sbxS5_shiftedOriginFuture_local_mean hd Q lam h0 h1
        l δ hl hsep hδ0 hδ1 P K hK hfuture Φ hΦ hbΦ y
      exact ⟨B', hB', hBe⟩
  · exact ae_of_all _ fun y => by
      obtain ⟨_, _, _, hmean⟩ := sbxS5_shiftedOriginFuture_local_mean hd Q lam h0 h1
        l δ hl hsep hδ0 hδ1 P K hK hfuture Φ hΦ hbΦ y
      exact hmean.trans
        (killed_future_origin_eq_frozen_record hd Q lam h0.le h1 l δ P K hK Φ hΦ hbΦ)

/-- The actual future discrepancy is precisely a difference of two origin
coupling expectations. This is an identity of the supplied measures, with no
covariance, locality, mean, or foundation premise. -/
theorem killed_future_difference_eq_origin_coupling_difference {d : ℕ}
    (K : CoupledQuenchedLaws d) (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (y : Vec d) (ω : FieldPair d) :
    ((∫ z, killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω)) -
      ∫ z, killedFutureTest R i Φ ((0, translate y ω), z) ∂K (0, translate y ω)) =
    ((∫ z, killedFutureTest R i Φ ((0, translate y ω), z)
      ∂sbxS9RecenteredCoupledLaws K y (0, translate y ω)) -
      ∫ z, killedFutureTest R i Φ ((0, translate y ω), z) ∂K (0, translate y ω)) := by
  have ht : translate (-y) (translate y ω) = ω := by
    rw [translate_add, neg_add_cancel, translate_zero]
  rw [killed_future_integral_recenter, ht]

/-- The signed past weight times the actual difference of origin coupling
expectations is jointly Bochner integrable. Thus identifying these laws will
discharge an actual integrable remainder, rather than a formal total integral. -/
theorem integrable_weighted_origin_coupling_difference {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (hR : 0 < R) (m : ℕ)
    (F : FieldPair d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F)
    (H : CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    Integrable (fun p : Vec d × FieldPair d =>
      (F p.2 * firstSlicePastIntegral Δ lam R i m K H p) *
        ((∫ z, killedFutureTest R i Φ ((0, translate p.1 p.2), z)
          ∂sbxS9RecenteredCoupledLaws K p.1 (0, translate p.1 p.2)) -
          ∫ z, killedFutureTest R i Φ ((0, translate p.1 p.2), z)
            ∂K (0, translate p.1 p.2))) (volume.prod Q) := by
  apply (sbxS5_integrable_firstSlicePast_future_difference Q hQ K hK Δ lam R i hR m
    F hF hbF H hH hbH Φ hΦ hbΦ).congr
  exact ae_of_all _ fun p => congrArg
    (fun b => (F p.2 * firstSlicePastIntegral Δ lam R i m K H p) * b)
    (killed_future_difference_eq_origin_coupling_difference K R i Φ p.1 p.2)

/-- The exact weighted slice defect is an integrable discrepancy of two
actual origin coupling measures, after centering the full joint future test
by its conditioned mean. All five inputs are the existing source nodes;
no law identification or additional graph premise is assumed. The unresolved
measure comparison is displayed on the right-hand side. -/
theorem weighted_slice_defect_eq_origin_coupling_difference
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let b := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
    let Ψ := fun r => Φ r - b
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂μ) -
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 * H q.2 ∂μ) * b =
    (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
      ∫ y, ∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)) *
        ((∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
          ((0, translate y ω), z) ∂sbxS9RecenteredCoupledLaws K y (0, translate y ω)) -
          ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
            ((0, translate y ω), z) ∂K (0, translate y ω)) ∂Q.measure := by
  intro μ ν b Ψ
  have heq := sbxS5_sliceIndependence_centered_remainder hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hendpoint hpast hfuture hslices hscope hD
    F hF hbF n hn H hH hbH Φ hΦ hbΦ
  dsimp only at heq
  refine heq.trans (congrArg
    (fun t => (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) * t)
    (integral_congr_ae (ae_of_all _ fun y => ?_)))
  apply integral_congr_ae
  exact ae_of_all _ fun ω => congrArg
    (fun t => (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1) K H (y, ω)) * t)
    (killed_future_difference_eq_origin_coupling_difference K (l / lam)
      (Renewal.forceCoord hd) Ψ y ω)

/-- Projecting an actual annealed coupling onto any measurable environment
observation gives exactly the observation of the supplied environment law.
Only the origin probability qualifier is used, including its null exception. -/
theorem map_annealedCoupledLaw_environment_observation {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    {α : Type*} [MeasurableSpace α] (U : FieldPair d → α) (hU : Measurable U) :
    (annealedCoupledLaw Q K).map (fun q => U q.1) = Q.map U := by
  classical
  have : IsProbabilityMeasure (annealedCoupledLaw Q K) :=
    annealedCoupledLaw_isProbabilityMeasure Q K hK
  apply Measure.ext
  intro s hs
  let f : α → ℝ := s.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hb : BoundedRealTest (fun q : FieldPair d × CoupledSample d => f (U q.1)) :=
    ⟨1, fun q => by by_cases hq : U q.1 ∈ s <;> simp [f, hq]⟩
  have hUg : Measurable (fun q : FieldPair d × CoupledSample d => U q.1) :=
    hU.comp measurable_fst
  have hint := integral_annealedCoupledLaw Q K hK _ (hf.comp hUg) hb
  change (∫ q, f (U q.1) ∂annealedCoupledLaw Q K) =
    ∫ ω, ∫ _z, f (U ω) ∂K (0, ω) ∂Q at hint
  have hinner : (fun ω => ∫ _z, f (U ω) ∂K (0, ω)) =ᵐ[Q] fun ω => f (U ω) := by
    filter_upwards [hK.1] with ω hω
    have : IsProbabilityMeasure (K (0, ω)) := hω
    rw [integral_const, probReal_univ, one_smul]
  rw [integral_congr_ae hinner,
    ← integral_map (μ := annealedCoupledLaw Q K) hUg.aemeasurable
      hf.aestronglyMeasurable,
    ← integral_map (μ := Q) hU.aemeasurable hf.aestronglyMeasurable] at hint
  simp only [f, integral_indicator hs, setIntegral_one_eq_measureReal,
    measureReal_def] at hint
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hint

/-- Bounded product tests determine the joint law on arbitrary measurable
carriers. Rectangles suffice, so no topological assumptions on the frozen
record carrier or the local observation carrier are needed. -/
theorem joint_law_eq_prod_of_bounded_product_tests
    {Ω Ω' α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (U : Ω → α) (X : Ω → β) (Y : Ω' → β)
    (hU : Measurable U) (hX : Measurable X) (hY : Measurable Y)
    (htest : ∀ (f : α → ℝ), Measurable f → BoundedRealTest f →
      ∀ (g : β → ℝ), Measurable g → BoundedRealTest g →
        (∫ q, f (U q) * g (X q) ∂μ) =
          (∫ q, f (U q) ∂μ) * ∫ q, g (Y q) ∂ν) :
    μ.map (fun q => (U q, X q)) = (μ.map U).prod (ν.map Y) := by
  classical
  apply Measure.ext_prod
  intro s t hs ht
  let f : α → ℝ := s.indicator (fun _ => 1)
  let g : β → ℝ := t.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hg : Measurable g := measurable_const.indicator ht
  have hbf : BoundedRealTest f := ⟨1, fun x => by
    by_cases hx : x ∈ s <;> simp [f, hx]⟩
  have hbg : BoundedRealTest g := ⟨1, fun x => by
    by_cases hx : x ∈ t <;> simp [g, hx]⟩
  have heq : (fun q => f (U q) * g (X q)) =
      (fun q => (s ×ˢ t).indicator (fun _ => (1 : ℝ)) (U q, X q)) := by
    funext q
    by_cases hqs : U q ∈ s <;> by_cases hqt : X q ∈ t <;>
      simp [f, g, hqs, hqt]
  have hint := htest f hf hbf g hg hbg
  rw [heq, ← integral_map (hU.prodMk hX).aemeasurable
      (measurable_const.indicator (hs.prod ht)).aestronglyMeasurable,
    ← integral_map hU.aemeasurable hf.aestronglyMeasurable,
    ← integral_map hY.aemeasurable hg.aestronglyMeasurable] at hint
  simp only [f, g, integral_indicator hs, integral_indicator ht,
    integral_indicator (hs.prod ht), setIntegral_one_eq_measureReal,
    measureReal_def] at hint
  rw [Measure.prod_prod]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
  simpa only [ENNReal.toReal_mul] using hint

section SliceSummation

variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)

include hl hsep hδ0 hδ1 hK

/-- The actual bounded joint observable is Bochner integrable under either
source law. Its environment test observes the Euclidean local field, its
past test observes the stated finite history, and its record is literal. -/
theorem integrable_weighted_regeneration_record
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (k m : ℕ) (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) m] H)
    (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (ρ : Measure (FieldPair d × CoupledSample d))
    (hρ : ρ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} : Set _)) :
    Integrable (fun q => F q.1 * H q.2 * Φ (regenerationRecord hd lam l k q)) ρ := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure ρ := by
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · infer_instance
    · have heq := Set.mem_singleton_iff.mp hρ
      subst ρ
      exact ProbabilityTheory.cond_isProbabilityMeasure hD
  have hrecord := (hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK hD k).2.1
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hHg : Measurable H := hH.mono (Probability.finiteHistorySigma_le _ _) le_rfl
  obtain ⟨CF, hCF⟩ := hbF
  obtain ⟨CH, hCH⟩ := hbH
  obtain ⟨CΦ, hCΦ⟩ := hbΦ
  apply Integrable.of_bound
    (((hFg.comp measurable_fst).mul (hHg.comp measurable_snd)).mul
      (hΦ.comp hrecord)).aestronglyMeasurable (max CF 0 * max CH 0 * max CΦ 0)
  exact ae_of_all _ fun q => by
    change ‖F q.1 * H q.2 * Φ (regenerationRecord hd lam l k q)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul ((hCF _).trans (le_max_left _ _))
        ((hCH _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _))
      ((hCΦ _).trans (le_max_left _ _)) (abs_nonneg _)
      (mul_nonneg (le_max_right _ _) (le_max_right _ _))

/-- The source scope excludes the first two grid slices under both actual
laws. Thus dropping indices zero and one in the summation loses no mass. -/
theorem first_cycle_early_slice_null
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (n : ℕ) (hn : n < 2) (ρ : Measure (FieldPair d × CoupledSample d))
    (hρ : ρ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} : Set _)) :
    ρ {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [(hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK hD 1).2.2 ρ hρ] with q hq
  obtain ⟨m, hm, ht, _⟩ := hq
  intro hqn
  have heq := ENNReal.coe_inj.mp (ht.symm.trans hqn)
  have hcast := mul_right_cancel₀ (EinsteinRelation.regenDelta_pos h0).ne' heq
  have hmn : m = n := by exact_mod_cast hcast
  omega

/-- Summation on the exact first-regeneration slices works under either
actual law, retaining the lower index two and every null exceptional set. -/
theorem first_cycle_hasSum_integral_of_scope
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (ρ : Measure (FieldPair d × CoupledSample d))
    (hρ : ρ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} : Set _))
    (f : FieldPair d × CoupledSample d → ℝ) (hf : Integrable f ρ) :
    HasSum (fun n : ℕ =>
      ∫ q in {q | regenerationTime hd lam l 1 q.2 =
        ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}, f q ∂ρ)
      (∫ q, f q ∂ρ) := by
  have hsc := hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1
  let s : ℕ → Set (FieldPair d × CoupledSample d) := fun n =>
    {q | regenerationTime hd lam l 1 q.2 =
      ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hs (n : ℕ) : MeasurableSet (s n) :=
    (hsc.1.comp measurable_snd) (measurableSet_singleton _)
  have hdis : Pairwise (fun m n => Disjoint (s m) (s n)) := by
    intro m n hmn
    apply Set.disjoint_left.mpr
    intro q hm hn
    have heq := ENNReal.coe_inj.mp (hm.symm.trans hn)
    have hcast := mul_right_cancel₀ (EinsteinRelation.regenDelta_pos h0).ne' heq
    have hnat : m + 2 = n + 2 := by exact_mod_cast hcast
    exact hmn (Nat.add_right_cancel hnat)
  have hcover : ∀ᵐ q ∂ρ, q ∈ ⋃ n, s n := by
    filter_upwards [hsc.2.2 ρ hρ] with q hq
    obtain ⟨n, hn, ht, _⟩ := hq
    have hn₂ : n - 2 + 2 = n := by omega
    refine Set.mem_iUnion.mpr ⟨n - 2, ?_⟩
    change regenerationTime hd lam l 1 q.2 =
      ((((n - 2 + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)
    simpa only [hn₂] using ht
  have hsum := hasSum_integral_iUnion hs hdis hf.integrableOn
  rw [Measure.restrict_eq_self_of_ae_mem hcover] at hsum
  exact hsum

/-- The actual slice probabilities sum to one before and after literal
no-return conditioning. The conditioning denominator is the supplied
positive event mass; no asymptotic tail estimate or new scale is used. -/
theorem first_cycle_slice_probabilities_hasSum
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (ρ : Measure (FieldPair d × CoupledSample d))
    (hρ : ρ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} : Set _)) :
    HasSum (fun n : ℕ => (ρ {q | regenerationTime hd lam l 1 q.2 =
      ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}).toReal) 1 := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure ρ := by
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · infer_instance
    · have heq := Set.mem_singleton_iff.mp hρ
      subst ρ
      exact ProbabilityTheory.cond_isProbabilityMeasure hD
  simpa only [setIntegral_one_eq_measureReal, integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one,
    Measure.restrict_apply_univ] using
    first_cycle_hasSum_integral_of_scope hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
      P K hK hscope hD ρ hρ (fun _ => (1 : ℝ)) (integrable_const 1)

/-- Centering the literal joint slice observable is a valid Bochner
subtraction. Its integral equals the weighted discrepancy between the
original and recentered origin coupling expectations. -/
theorem weighted_centered_slice_integral_eq_origin_coupling_difference
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let b := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
    let Ψ := fun r => Φ r - b
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * (Φ (regenerationRecord hd lam l 1 q) - b) ∂μ) =
    (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
      ∫ y, ∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)) *
        ((∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
          ((0, translate y ω), z) ∂sbxS9RecenteredCoupledLaws K y (0, translate y ω)) -
          ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
            ((0, translate y ω), z) ∂K (0, translate y ω)) ∂Q.measure := by
  intro μ ν b Ψ
  have hiFull := integrable_weighted_regeneration_record hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hscope hD 1 (n - 1) F hF hbF H hH hbH Φ hΦ hbΦ
    μ (Set.mem_insert _ _)
  have hiPast : Integrable (fun q => F q.1 * H q.2) μ := by
    simpa only [mul_one] using
      integrable_weighted_regeneration_record hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
        P K hK hscope hD 1 (n - 1) F hF hbF H hH hbH (fun _ => 1) measurable_const
        ⟨1, fun _ => by norm_num⟩ μ (Set.mem_insert _ _)
  have heq : (fun q : FieldPair d × CoupledSample d =>
      F q.1 * H q.2 * (Φ (regenerationRecord hd lam l 1 q) - b)) =
      (fun q => F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) -
        (F q.1 * H q.2) * b) := by
    funext q
    exact mul_sub _ _ _
  rw [heq, integral_sub hiFull.integrableOn (hiPast.mul_const b).integrableOn,
    integral_mul_const]
  exact weighted_slice_defect_eq_origin_coupling_difference hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hendpoint hpast hfuture hslices hscope hD
    F hF hbF n hn H hH hbH Φ hΦ hbΦ

/-- Summing the signed, local-field-weighted origin coupling discrepancies
gives the exact joint first-marginal defect. The constant past test is used
only after the predecessor's full weighted slice calculation. -/
theorem weighted_first_marginal_origin_remainders_hasSum
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let b := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
    let Ψ := fun r => Φ r - b
    let C := fun (y : Vec d) (ω : FieldPair d) =>
      (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
        ((0, translate y ω), z) ∂sbxS9RecenteredCoupledLaws K y (0, translate y ω)) -
        ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
          ((0, translate y ω), z) ∂K (0, translate y ω)
    let a := fun n : ℕ =>
      (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
        ∫ y, ∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n + 2 - 1) K (fun _ => 1) (y, ω)) * C y ω ∂Q.measure
    HasSum a ((∫ q, F q.1 * Φ (regenerationRecord hd lam l 1 q) ∂μ) -
      (∫ q, F q.1 ∂μ) * b) := by
  intro μ ν b Ψ C a
  have hb1 {α : Type} : BoundedRealTest (fun _ : α => (1 : ℝ)) :=
    ⟨1, fun _ => by norm_num⟩
  have hiΦ : Integrable (fun q => F q.1 * Φ (regenerationRecord hd lam l 1 q)) μ := by
    simpa only [mul_one] using
      integrable_weighted_regeneration_record hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
        P K hK hscope hD 1 0 F hF hbF (fun _ => 1) measurable_const hb1
        Φ hΦ hbΦ μ (Set.mem_insert _ _)
  have hiF : Integrable (fun q => F q.1) μ := by
    simpa only [mul_one] using
      integrable_weighted_regeneration_record hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
        P K hK hscope hD 1 0 F hF hbF (fun _ => 1) measurable_const hb1
        (fun _ => 1) measurable_const hb1 μ (Set.mem_insert _ _)
  have hi : Integrable (fun q => F q.1 * (Φ (regenerationRecord hd lam l 1 q) - b)) μ := by
    have hiSub : Integrable (fun q =>
        F q.1 * Φ (regenerationRecord hd lam l 1 q) - F q.1 * b) μ :=
      hiΦ.sub (hiF.mul_const b)
    simpa only [mul_sub] using hiSub
  have heq : a = fun n : ℕ =>
      ∫ q in {q | regenerationTime hd lam l 1 q.2 =
        ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 * (Φ (regenerationRecord hd lam l 1 q) - b) ∂μ := by
    funext n
    simpa only [mul_one] using
      (weighted_centered_slice_integral_eq_origin_coupling_difference hd Q lam h0 h1
        l δ hl hsep hδ0 hδ1 P K hK hendpoint hpast hfuture hslices hscope hD
        F hF hbF (n + 2) (by omega) (fun _ => 1) measurable_const hb1 Φ hΦ hbΦ).symm
  have hsum := first_cycle_hasSum_integral_of_scope hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK hscope hD μ (Set.mem_insert _ _)
    (fun q => F q.1 * (Φ (regenerationRecord hd lam l 1 q) - b)) hi
  rw [← heq] at hsum
  have hint : (∫ q, F q.1 * (Φ (regenerationRecord hd lam l 1 q) - b) ∂μ) =
      (∫ q, F q.1 * Φ (regenerationRecord hd lam l 1 q) ∂μ) - (∫ q, F q.1 ∂μ) * b := by
    simp_rw [mul_sub]
    rw [integral_sub hiΦ (hiF.mul_const b), integral_mul_const]
  exact hint ▸ hsum

/-- The weighted origin discrepancies are absolutely summable. Their total
variation is bounded by the actual centered joint observable; in particular,
the first-marginal defect cannot be hidden in a conditionally convergent sum. -/
theorem weighted_first_marginal_origin_remainders_absSummable
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let b := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
    let Ψ := fun r => Φ r - b
    let C := fun (y : Vec d) (ω : FieldPair d) =>
      (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
        ((0, translate y ω), z) ∂sbxS9RecenteredCoupledLaws K y (0, translate y ω)) -
        ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
          ((0, translate y ω), z) ∂K (0, translate y ω)
    let a := fun n : ℕ =>
      (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
        ∫ y, ∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n + 2 - 1) K (fun _ => 1) (y, ω)) * C y ω ∂Q.measure
    Summable (fun n => |a n|) ∧
      |(∫ q, F q.1 * Φ (regenerationRecord hd lam l 1 q) ∂μ) -
        (∫ q, F q.1 ∂μ) * b| ≤ (∑' n, |a n|) ∧
      (∑' n, |a n|) ≤ ∫ q, |F q.1 * (Φ (regenerationRecord hd lam l 1 q) - b)| ∂μ := by
  intro μ ν b Ψ C a
  have hb1 {α : Type} : BoundedRealTest (fun _ : α => (1 : ℝ)) :=
    ⟨1, fun _ => by norm_num⟩
  have hiΦ : Integrable (fun q => F q.1 * Φ (regenerationRecord hd lam l 1 q)) μ := by
    simpa only [mul_one] using
      integrable_weighted_regeneration_record hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
        P K hK hscope hD 1 0 F hF hbF (fun _ => 1) measurable_const hb1
        Φ hΦ hbΦ μ (Set.mem_insert _ _)
  have hiF : Integrable (fun q => F q.1) μ := by
    simpa only [mul_one] using
      integrable_weighted_regeneration_record hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
        P K hK hscope hD 1 0 F hF hbF (fun _ => 1) measurable_const hb1
        (fun _ => 1) measurable_const hb1 μ (Set.mem_insert _ _)
  have hi : Integrable (fun q => F q.1 * (Φ (regenerationRecord hd lam l 1 q) - b)) μ := by
    have hiSub : Integrable (fun q =>
        F q.1 * Φ (regenerationRecord hd lam l 1 q) - F q.1 * b) μ :=
      hiΦ.sub (hiF.mul_const b)
    simpa only [mul_sub] using hiSub
  have habs := sbxS5_firstCycle_summable_abs_integrals hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK hscope hD (fun q => F q.1 * (Φ (regenerationRecord hd lam l 1 q) - b)) hi
  have heq : a = fun n : ℕ =>
      ∫ q in {q | regenerationTime hd lam l 1 q.2 =
        ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 * (Φ (regenerationRecord hd lam l 1 q) - b) ∂μ := by
    funext n
    simpa only [mul_one] using
      (weighted_centered_slice_integral_eq_origin_coupling_difference hd Q lam h0 h1
        l δ hl hsep hδ0 hδ1 P K hK hendpoint hpast hfuture hslices hscope hD
        F hF hbF (n + 2) (by omega) (fun _ => 1) measurable_const hb1 Φ hΦ hbΦ).symm
  have ha : Summable (fun n => |a n|) := by
    rw [heq]
    exact habs.1
  have hsum := weighted_first_marginal_origin_remainders_hasSum hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hendpoint hpast hfuture hslices hscope hD F hF hbF Φ hΦ hbΦ
  refine ⟨ha, ?_, ?_⟩
  · rw [← hsum.tsum_eq]
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm (f := a) (by simpa only [Real.norm_eq_abs] using ha))
  · rw [heq]
    exact habs.2

/-- Sum the signed local-environment slice factorization with constant past
test. This consumer works under either actual law. Its slice premise remains
an internal mathematical input and does not discharge the independence root. -/
theorem weighted_first_cycle_integral_of_slice_integrals
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (ρ : Measure (FieldPair d × CoupledSample d))
    (hρ : ρ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} : Set _))
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (hslice : ∀ n : ℕ, 2 ≤ n →
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}, F q.1 ∂ρ) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) :
    (∫ q, F q.1 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
      (∫ q, F q.1 ∂ρ) * ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  have hb1 {α : Type} : BoundedRealTest (fun _ : α => (1 : ℝ)) :=
    ⟨1, fun _ => by norm_num⟩
  have hi : Integrable (fun q => F q.1 * Φ (regenerationRecord hd lam l 1 q)) ρ := by
    simpa only [mul_one] using
      integrable_weighted_regeneration_record hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
        P K hK hscope hD 1 0 F hF hbF (fun _ => 1) measurable_const hb1 Φ hΦ hbΦ ρ hρ
  have hiF : Integrable (fun q => F q.1) ρ := by
    simpa only [mul_one] using
      integrable_weighted_regeneration_record hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
        P K hK hscope hD 1 0 F hF hbF (fun _ => 1) measurable_const hb1
        (fun _ => 1) measurable_const hb1 ρ hρ
  have hsum := first_cycle_hasSum_integral_of_scope hd Q lam h0 h1 l δ hl hsep
    hδ0 hδ1 P K hK hscope hD ρ hρ _ hi
  have hsumF := (first_cycle_hasSum_integral_of_scope hd Q lam h0 h1 l δ hl hsep
    hδ0 hδ1 P K hK hscope hD ρ hρ _ hiF).mul_right
      (∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD)
  apply hsum.unique
  convert hsumF using 1
  funext n
  exact hslice (n + 2) (by omega)

/-- The actual first record is independent of any measurable observation
of the local joint field once its weighted deterministic slice identities
are supplied. The right-hand record law uses literal no-return conditioning.
This is a slice-to-joint-law consumer, not an independence-root reduction. -/
theorem first_record_joint_law_of_local_slice_integrals
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (ρ : Measure (FieldPair d × CoupledSample d))
    (hρ : ρ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} : Set _))
    {α : Type*} [MeasurableSpace α] (U : FieldPair d → α)
    (hU : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] U)
    (hslice : ∀ (F : FieldPair d → ℝ),
      Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F →
      BoundedRealTest F →
      ∀ (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ),
      Measurable Φ → BoundedRealTest Φ → ∀ n : ℕ, 2 ≤ n →
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}, F q.1 ∂ρ) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) :
    ρ.map (fun q => (U q.1, regenerationRecord hd lam l 1 q)) =
      (ρ.map (fun q => U q.1)).prod
        ((regenerationConditionedLaw hd Q lam l K hK.1 hD).map
          (regenerationRecord hd lam l 0)) := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure (regenerationConditionedLaw hd Q lam l K hK.1 hD) :=
    ProbabilityTheory.cond_isProbabilityMeasure hD
  have : IsProbabilityMeasure ρ := by
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · infer_instance
    · have heq := Set.mem_singleton_iff.mp hρ
      subst ρ
      infer_instance
  have hUg : Measurable U := hU.mono (Probability.localSigma_le_borel _) le_rfl
  have hr (k : ℕ) : Measurable (regenerationRecord hd lam l k) :=
    (hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD k).2.1
  apply joint_law_eq_prod_of_bounded_product_tests ρ
    (regenerationConditionedLaw hd Q lam l K hK.1 hD) _ _ _
    (hUg.comp measurable_fst) (hr 1) (hr 0)
  intro f hf hbf Φ hΦ hbΦ
  have hbF : BoundedRealTest (fun ω => f (U ω)) := by
    obtain ⟨C, hC⟩ := hbf
    exact ⟨C, fun ω => hC (U ω)⟩
  exact weighted_first_cycle_integral_of_slice_integrals hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hscope hD ρ hρ (fun ω => f (U ω))
    (hf.comp hU) hbF Φ hΦ hbΦ (hslice _ (hf.comp hU) hbF Φ hΦ hbΦ)

/-- Finite tuples of local measurable environment observables have the
product joint law with the literal first record under either actual source
law, given the weighted slice identities. The second conclusion is its
first-record marginal projection, with no extra slice or law assumption. -/
theorem first_record_local_tuple_law_of_slice_integrals
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (ρ : Measure (FieldPair d × CoupledSample d))
    (hρ : ρ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} : Set _))
    (m : ℕ) (U : Fin m → FieldPair d → ℝ)
    (hU : ∀ j, Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] (U j))
    (hslice : ∀ (F : FieldPair d → ℝ),
      Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F →
      BoundedRealTest F →
      ∀ (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ),
      Measurable Φ → BoundedRealTest Φ → ∀ n : ℕ, 2 ≤ n →
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}, F q.1 ∂ρ) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) :
    ρ.map (fun q => ((fun j => U j q.1), regenerationRecord hd lam l 1 q)) =
      (ρ.map (fun q j => U j q.1)).prod
        ((regenerationConditionedLaw hd Q lam l K hK.1 hD).map
          (regenerationRecord hd lam l 0)) ∧
    ρ.map (regenerationRecord hd lam l 1) =
      (regenerationConditionedLaw hd Q lam l K hK.1 hD).map
        (regenerationRecord hd lam l 0) := by
  have htuple : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}]
      (fun ω j => U j ω) := by
    let : MeasurableSpace (FieldPair d) :=
      localSigma {x : Vec d | euclideanNorm x < l / lam}
    exact measurable_pi_iff.mpr hU
  have hjoint := first_record_joint_law_of_local_slice_integrals hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hscope hD ρ hρ (fun ω j => U j ω) htuple hslice
  refine ⟨hjoint, ?_⟩
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure ρ := by
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · infer_instance
    · have heq := Set.mem_singleton_iff.mp hρ
      subst ρ
      exact ProbabilityTheory.cond_isProbabilityMeasure hD
  have hUg : Measurable (fun q : FieldPair d × CoupledSample d => fun j => U j q.1) :=
    (htuple.mono (Probability.localSigma_le_borel _) le_rfl).comp measurable_fst
  have hr : Measurable (regenerationRecord hd lam l 1) :=
    (hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1).2.1
  have : IsProbabilityMeasure (regenerationConditionedLaw hd Q lam l K hK.1 hD) :=
    ProbabilityTheory.cond_isProbabilityMeasure hD
  have hproj := congrArg (Measure.map Prod.snd) hjoint
  rw [Measure.map_map measurable_snd (hUg.prodMk hr), Measure.map_snd_prod,
    measure_univ, one_smul] at hproj
  exact hproj

end SliceSummation

section OriginalPathCovariance

variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hP : ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        P p = sbxS9RecenteredPathLaws P a p)

include hK hP

/-- Exact transport of the actual off-origin future integral to the original
origin coupling. The path covariance premise has both exceptional-set
qualifiers; no off-origin kernel equality is postulated. -/
theorem killed_future_eq_shifted_origin_assuming_path_laws
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (fun ω => ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((y, ω), z) ∂K (y, ω)) =ᵐ[Q.measure]
      (fun ω => ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω)) := by
  filter_upwards [coupling_origin_eq_recenter_assuming_path_laws hd Q lam h0 h1
    l δ P K hK, hP] with y hy hPy
  have htranslate : MeasurePreserving (translate y) Q.measure Q.measure :=
    ⟨Probability.measurable_translate y, Q.stationary y⟩
  filter_upwards [htranslate.quasiMeasurePreserving.ae (hy hPy)] with ω hω
  have ht : translate (-y) (translate y ω) = ω := by
    rw [translate_add, neg_add_cancel, translate_zero]
  calc
    _ = ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂sbxS9RecenteredCoupledLaws K y (0, translate y ω) := by
      rw [killed_future_integral_recenter, ht]
    _ = _ := by rw [← hω]

include hl hsep hδ0 hδ1

/-- The supplied future-kernel node gives the separated JOINT-field version
of the actual endpoint factor once the original path covariance is known.
Its expectation is the literal no-return integral of the frozen origin record. -/
theorem killed_future_local_mean_assuming_path_laws
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∃ B' : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d |
          y (Renewal.forceCoord hd) - 2 * (l / lam) ≤ x (Renewal.forceCoord hd)}] B' ∧
        (fun ω => ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
          ((y, ω), z) ∂K (y, ω)) =ᵐ[Q.measure] B') ∧
      (∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((y, ω), z) ∂K (y, ω) ∂Q.measure) =
        ∫ q in regenerationNoReturn hd (l / lam), Φ (regenerationRecord hd lam l 0 q)
          ∂annealedCoupledLaw Q.measure K := by
  filter_upwards [killed_future_eq_shifted_origin_assuming_path_laws hd Q lam h0 h1
    l δ P K hK hP Φ] with y hy
  obtain ⟨B', hB', hBe, hmean⟩ := sbxS5_shiftedOriginFuture_local_mean hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hfuture Φ hΦ hbΦ y
  exact ⟨⟨B', hB', hy.trans hBe⟩,
    (integral_congr_ae hy).trans (hmean.trans
      (killed_future_origin_eq_frozen_record hd Q lam h0.le h1 l δ P K hK Φ hΦ hbΦ))⟩

/-- The exact signed triple-test slice identity on the supplied annealed law.
Every normalization and centering conversion is inherited from the checked
endpoint calculation. Only the precise original path covariance is additional;
this conditional support theorem is not a graph reduction. -/
theorem weighted_slice_identity_assuming_path_laws
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q)
        ∂annealedCoupledLaw Q.measure K) =
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 ∂annealedCoupledLaw Q.measure K) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let b := ∫ q, Φ (regenerationRecord hd lam l 0 q)
    ∂regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Ψ := fun r => Φ r - b
  apply sub_eq_zero.mp
  rw [sbxS5_sliceIndependence_centered_remainder hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK hendpoint hpast hfuture hslices hscope hD F hF hbF n hn H hH hbH Φ hΦ hbΦ]
  suffices hz : (∫ y, ∫ ω,
      (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)) *
      ((∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ ((y, ω), z) ∂K (y, ω)) -
        ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
          ((0, translate y ω), z) ∂K (0, translate y ω)) ∂Q.measure) = 0 by
    exact mul_eq_zero_of_right _ hz
  apply integral_eq_zero_of_ae
  filter_upwards [killed_future_eq_shifted_origin_assuming_path_laws hd Q lam h0 h1
    l δ P K hK hP Ψ] with y hy
  apply integral_eq_zero_of_ae
  filter_upwards [hy] with ω hω
  simp only [Pi.zero_apply]
  rw [hω, sub_self, mul_zero]

end OriginalPathCovariance

/-- Complete conditional assembly of the literal frozen independence V2
statement from its six ordered source dependencies. The additional premise is
only the actual original/recentered path-law covariance, with its origin and
product-a.e. qualifiers. It remains an internal CARVER-F producer obligation;
this theorem is support and does not close the six-argument graph reduction.
The tail node is retained in graph order; the supplied scope already gives
the finite first-cycle coverage needed for the marginal summation. -/
theorem independence_assuming_original_path_covariance
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (_htails : node_app_u3A_regen_u2D_tailsStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hcov : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
      ∀ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCoupling hd Q lam l δ h0.le h1 P K →
      ∀ᵐ a ∂(volume : Measure (Vec d)),
        (∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
        ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
          P p = sbxS9RecenteredPathLaws P a p) :
    node_app_u3A_factorization_u23_independenceStmtV2 := by
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  dsimp only
  intro Φ hΦ hbΦ
  have hP := hcov d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK
  have hfuture_local := killed_future_local_mean_assuming_path_laws hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hfuture Φ hΦ hbΦ
  constructor
  · intro F hF hbF n hn H hH hbH
    refine ⟨sbxS5_radius_gap hl h0 h1 hsep, ?_, ?_, ?_, ?_⟩
    · exact ae_of_all _ fun y hy => by
        filter_upwards [sbxS5_firstSlicePast_zero hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
          P K hK hslices n hn H y hy] with ω hω
        simp only [Pi.zero_apply] at hω ⊢
        rw [hω, mul_zero]
    · filter_upwards [hfuture_local] with y hy
      intro hhigh
      obtain ⟨A', hA', hAe⟩ := sbxS5_pastFactor_local hd Q lam h0 h1 l δ
        hl hsep hδ0 hδ1 P K hK hpast F hF (n - 1) H hH hbH y hhigh
      obtain ⟨B', hB', hBe⟩ := hy.1
      exact ⟨⟨A', B', hA', hB', hAe, hBe⟩,
        integral_mul_eq_of_corrected_halfSpace_versions Q (Renewal.forceCoord hd)
          (y (Renewal.forceCoord hd)) (l / lam) (sbxS5_radius_gap hl h0 h1 hsep)
          _ _ A' B' hA' hB' hAe hBe⟩
    · exact hfuture_local.mono fun _ hy => hy.2
    · exact weighted_slice_identity_assuming_path_laws hd Q lam h0 h1 l δ hl hsep
        hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
        F hF hbF n hn H hH hbH Φ hΦ hbΦ
  · apply sbxS5_firstMarginal_of_sliceIdentity hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
      P K hK hscope hD Φ hΦ hbΦ
    intro n hn
    have hb1 {α : Type} : BoundedRealTest (fun _ : α => (1 : ℝ)) :=
      ⟨1, fun _ => by norm_num⟩
    simpa only [one_mul] using
      weighted_slice_identity_assuming_path_laws hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
        P K hK hP hendpoint hpast hfuture hslices hscope hD
        (fun _ => 1) measurable_const hb1 n hn (fun _ => 1) measurable_const hb1 Φ hΦ hbΦ

/-- The admissible first-cycle past includes the actual grid index and the
path through the preceding grid time, with only the strictly earlier coins.
At an infinite regeneration time the conventional index is zero; the scope
hypothesis later excludes that event under the actual law. -/
def firstCyclePastRecord {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (z : CoupledSample d) : ℕ × CoupledSample d :=
  let n := gridIndex (Renewal.regenDelta lam) (regenerationTime hd lam l 1 z).toNNReal
  (n, Probability.stoppedHistorySample (Renewal.regenDelta lam) (n - 1) z)

/-- On a literal deterministic regeneration slice the random past record
is precisely the stopped history at index `n - 1`. -/
theorem firstCyclePastRecord_on_slice {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (h0 : 0 < lam) (n : ℕ) (z : CoupledSample d)
    (hz : regenerationTime hd lam l 1 z =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)) :
    firstCyclePastRecord hd lam l z =
      (n, Probability.stoppedHistorySample (Renewal.regenDelta lam) (n - 1) z) := by
  unfold firstCyclePastRecord
  rw [hz, ENNReal.toNNReal_coe, gridIndex_mul _ (EinsteinRelation.regenDelta_pos h0)]

/-- Every measurable test of this stopped record has an admissible finite
history representative on slice `n`; the unrevealed bridge is not included. -/
theorem firstCyclePastRecord_slice_test_measurable {d : ℕ} (lam : ℝ) (n : ℕ)
    {α : Type*} [MeasurableSpace α] (H : ℕ × CoupledSample d → α)
    (hH : Measurable H) :
    Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)]
      (fun z => H (n, Probability.stoppedHistorySample (Renewal.regenDelta lam) (n - 1) z)) :=
  hH.comp (measurable_const.prodMk (Probability.measurable_stoppedHistorySample _ _))

/-- The complete admissible random past record is measurable whenever the
actual first regeneration time is measurable. -/
theorem measurable_firstCyclePastRecord {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (ht : Measurable (regenerationTime hd lam l 1)) :
    Measurable (firstCyclePastRecord hd lam l) := by
  let N := fun z : CoupledSample d =>
    gridIndex (Renewal.regenDelta lam) (regenerationTime hd lam l 1 z).toNNReal
  have hn : Measurable N :=
    ((ht.ennreal_toNNReal.coe_nnreal_real).div_const _).nat_floor
  have hstop (n : ℕ) : Measurable (fun z : CoupledSample d =>
      Probability.stoppedHistorySample (Renewal.regenDelta lam) (n - 1) z) :=
    (Probability.measurable_stoppedHistorySample (d := d)
      (Renewal.regenDelta lam) (n - 1)).mono
        (Probability.finiteHistorySigma_le _ _) le_rfl
  have hs : Measurable (fun p : ℕ × CoupledSample d =>
      Probability.stoppedHistorySample (Renewal.regenDelta lam) (p.1 - 1) p.2) :=
    measurable_from_prod_countable_right hstop
  change Measurable (fun z =>
    (N z, Probability.stoppedHistorySample (Renewal.regenDelta lam) (N z - 1) z))
  exact hn.prodMk (hs.comp (hn.prodMk measurable_id))

/-- On a literal first-regeneration slice, replace the random admissible past
record inside any scalar integral by its deterministic finite-history version. -/
theorem firstCyclePastRecord_setIntegral_eq {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (h0 : 0 < lam) (n : ℕ) (μ : Measure (FieldPair d × CoupledSample d))
    (hs : MeasurableSet {q : FieldPair d × CoupledSample d |
      regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)})
    (f : (FieldPair d × CoupledSample d) → (ℕ × CoupledSample d) → ℝ) :
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      f q (firstCyclePastRecord hd lam l q.2) ∂μ) =
    ∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      f q (n, Probability.stoppedHistorySample (Renewal.regenDelta lam) (n - 1) q.2) ∂μ :=
  setIntegral_congr_fun hs fun q hq =>
    congrArg (f q) (firstCyclePastRecord_on_slice hd lam l h0 n q.2 hq)

/-- An admissible finite-history test is unchanged when the actual sample
is replaced by its stopped path and its strictly earlier bits. -/
theorem finiteHistory_test_eq_stopped {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable[finiteHistorySigma Δ n] H)
    (z : CoupledSample d) : H z = H (Probability.stoppedHistorySample Δ n z) := by
  have hs := hH (measurableSet_singleton (H z))
  rw [Probability.finiteHistorySigma_eq_comap_stopped] at hs
  obtain ⟨s, _, hs⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hz : z ∈ H ⁻¹' {H z} := by simp
  have hz' : Probability.stoppedHistorySample Δ n z ∈ H ⁻¹' {H z} := by
    rw [← hs] at hz ⊢
    simpa only [Set.mem_preimage, Probability.stoppedHistorySample_idempotent] using hz
  exact (Set.mem_singleton_iff.mp hz').symm

/-- On a deterministic first-cycle slice, the stopped record retains every
admissible test of the original finite history. -/
theorem finiteHistory_test_eq_firstCyclePastRecord_on_slice {d : ℕ}
    (hd : 2 ≤ d) (lam l : ℝ) (h0 : 0 < lam) (n : ℕ)
    (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (z : CoupledSample d)
    (hz : regenerationTime hd lam l 1 z =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)) :
    H z = H (firstCyclePastRecord hd lam l z).2 := by
  rw [firstCyclePastRecord_on_slice hd lam l h0 n z hz]
  exact finiteHistory_test_eq_stopped (Renewal.regenDelta lam) (n - 1) H hH z

section StoppedFirstCycle

variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hP : ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        P p = sbxS9RecenteredPathLaws P a p)

include hl hsep hδ0 hδ1 hK

/-- Bounded local-field, admissible stopped-history and complete-record tests
are integrable under the true finite annealed law. No uniform bound on the
regeneration time or an artificial stopped-process law is used. -/
theorem integrable_weighted_firstCyclePastRecord
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (H : ℕ × CoupledSample d → ℝ)
    (hH : Measurable H) (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    Integrable (fun q => F q.1 * H (firstCyclePastRecord hd lam l q.2) *
      Φ (regenerationRecord hd lam l 1 q)) (annealedCoupledLaw Q.measure K) := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hsc := hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hpast : Measurable (fun q : FieldPair d × CoupledSample d =>
      firstCyclePastRecord hd lam l q.2) :=
    (measurable_firstCyclePastRecord hd lam l hsc.1).comp measurable_snd
  obtain ⟨CF, hCF⟩ := hbF
  obtain ⟨CH, hCH⟩ := hbH
  obtain ⟨CΦ, hCΦ⟩ := hbΦ
  apply Integrable.of_bound
    (((hFg.comp measurable_fst).mul (hH.comp hpast)).mul
      (hΦ.comp hsc.2.1)).aestronglyMeasurable (max CF 0 * max CH 0 * max CΦ 0)
  exact ae_of_all _ fun q => by
    change ‖F q.1 * H (firstCyclePastRecord hd lam l q.2) *
      Φ (regenerationRecord hd lam l 1 q)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul ((hCF _).trans (le_max_left _ _))
        ((hCH _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _))
      ((hCΦ _).trans (le_max_left _ _)) (abs_nonneg _)
      (mul_nonneg (le_max_right _ _) (le_max_right _ _))

/-- The literal first-cycle slice integrals of the weighted stopped-history
test are absolutely summable under the actual probability law. Their total
variation is bounded by its genuine absolute integral; no covariance is needed. -/
theorem weighted_firstCyclePastRecord_slices_absSummable
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (H : ℕ × CoupledSample d → ℝ)
    (hH : Measurable H) (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    let μ := annealedCoupledLaw Q.measure K
    let f := fun q => F q.1 * H (firstCyclePastRecord hd lam l q.2) *
      Φ (regenerationRecord hd lam l 1 q)
    let a := fun n : ℕ => ∫ q in {q | regenerationTime hd lam l 1 q.2 =
      ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}, f q ∂μ
    Summable (fun n => |a n|) ∧ (∑' n, |a n|) ≤ ∫ q, |f q| ∂μ :=
  sbxS5_firstCycle_summable_abs_integrals hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK hscope hD _
      (integrable_weighted_firstCyclePastRecord hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
        P K hK hscope hD F hF hbF H hH hbH Φ hΦ hbΦ)

include hP in
/-- A bounded admissible past observation has the exact weighted factorization
on each literal first-regeneration slice. Its representative belongs to the
preceding finite-history sigma algebra. Supplied-law covariance is explicit. -/
theorem weighted_firstCyclePastRecord_slice_identity_assuming_path_laws
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (n : ℕ) (hn : 2 ≤ n)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (H : ℕ × CoupledSample d → ℝ)
    (hH : Measurable H) (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}, F q.1 * H (firstCyclePastRecord hd lam l q.2) *
      Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}, F q.1 * H (firstCyclePastRecord hd lam l q.2) ∂annealedCoupledLaw Q.measure K) *
      ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  have hset : MeasurableSet {q : FieldPair d × CoupledSample d |
      regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} :=
    (hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1).1.comp
      measurable_snd (measurableSet_singleton _)
  let T := fun z : CoupledSample d =>
    H (n, Probability.stoppedHistorySample (Renewal.regenDelta lam) (n - 1) z)
  have hT : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] T :=
    firstCyclePastRecord_slice_test_measurable lam n H hH
  have hbT : BoundedRealTest T := ⟨hbH.choose, fun z => hbH.choose_spec _⟩
  have hleft := firstCyclePastRecord_setIntegral_eq hd lam l h0 n
    (annealedCoupledLaw Q.measure K) hset
      (fun q p => F q.1 * H p * Φ (regenerationRecord hd lam l 1 q))
  have hright := firstCyclePastRecord_setIntegral_eq hd lam l h0 n
    (annealedCoupledLaw Q.measure K) hset (fun q p => F q.1 * H p)
  have hslice := weighted_slice_identity_assuming_path_laws hd Q lam h0 h1 l δ hl hsep
    hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD F hF hbF n hn
    T hT hbT Φ hΦ hbΦ
  exact hleft.trans (hslice.trans (congrArg (fun a : ℝ => a *
    ∫ q, Φ (regenerationRecord hd lam l 0 q)
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) hright.symm))


include hP in
/-- Sum the actual deterministic `n ≥ 2` slice identities for a bounded
observation of the admissible first-cycle history, retaining the local joint
field factor. The only additional internal input is the exact supplied-law
covariance; this support theorem does not close the graph reduction. -/
theorem weighted_firstCyclePastRecord_identity_assuming_path_laws
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (H : ℕ × CoupledSample d → ℝ)
    (hH : Measurable H) (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ q, F q.1 * H (firstCyclePastRecord hd lam l q.2) *
      Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
    (∫ q, F q.1 * H (firstCyclePastRecord hd lam l q.2) ∂annealedCoupledLaw Q.measure K) *
      ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  have hb1 {α : Type} : BoundedRealTest (fun _ : α => (1 : ℝ)) :=
    ⟨1, fun _ => by norm_num⟩
  have hi := integrable_weighted_firstCyclePastRecord hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK hscope hD F hF hbF H hH hbH Φ hΦ hbΦ
  have hiPast : Integrable (fun q => F q.1 * H (firstCyclePastRecord hd lam l q.2))
      (annealedCoupledLaw Q.measure K) := by
    simpa only [mul_one] using
      integrable_weighted_firstCyclePastRecord hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
        P K hK hscope hD F hF hbF H hH hbH (fun _ => 1) measurable_const hb1
  have hsum := first_cycle_hasSum_integral_of_scope hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK hscope hD _ (Set.mem_insert _ _) _ hi
  have hsumPast := (first_cycle_hasSum_integral_of_scope hd Q lam h0 h1 l δ hl hsep
    hδ0 hδ1 P K hK hscope hD _ (Set.mem_insert _ _) _ hiPast).mul_right
      (∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD)
  apply hsum.unique
  convert hsumPast using 1
  funext m
  exact weighted_firstCyclePastRecord_slice_identity_assuming_path_laws hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
    (m + 2) (by omega) F hF hbF H hH hbH Φ hΦ hbΦ

end StoppedFirstCycle

/-- Bounded triple tests determine the joint law of two observations with a
future record. Triple-rectangle uniqueness extends the tests
to the whole product sigma algebra, without separability assumptions. -/
theorem joint_law_eq_prod_of_bounded_triple_tests
    {Ω Ω' α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (U : Ω → α) (V : Ω → β) (X : Ω → γ) (Y : Ω' → γ)
    (hU : Measurable U) (hV : Measurable V) (hX : Measurable X) (hY : Measurable Y)
    (htest : ∀ (f : α → ℝ), Measurable f → BoundedRealTest f →
      ∀ (g : β → ℝ), Measurable g → BoundedRealTest g →
      ∀ (h : γ → ℝ), Measurable h → BoundedRealTest h →
        (∫ q, f (U q) * g (V q) * h (X q) ∂μ) =
          (∫ q, f (U q) * g (V q) ∂μ) * ∫ q, h (Y q) ∂ν) :
    μ.map (fun q => ((U q, V q), X q)) =
      (μ.map (fun q => (U q, V q))).prod (ν.map Y) := by
  classical
  have hUV := hU.prodMk hV
  apply Measure.ext_prod₃_iff'.mpr
  intro s t w hs ht hw
  let f : α → ℝ := s.indicator (fun _ => 1)
  let g : β → ℝ := t.indicator (fun _ => 1)
  let h : γ → ℝ := w.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hg : Measurable g := measurable_const.indicator ht
  have hh : Measurable h := measurable_const.indicator hw
  have hbf : BoundedRealTest f := ⟨1, fun x => by
    by_cases hx : x ∈ s <;> simp [f, hx]⟩
  have hbg : BoundedRealTest g := ⟨1, fun x => by
    by_cases hx : x ∈ t <;> simp [g, hx]⟩
  have hbh : BoundedRealTest h := ⟨1, fun x => by
    by_cases hx : x ∈ w <;> simp [h, hx]⟩
  have hfg : (fun q => f (U q) * g (V q)) =
      ((fun q => (U q, V q)) ⁻¹' (s ×ˢ t)).indicator (fun _ => (1 : ℝ)) := by
    funext q
    by_cases hqs : U q ∈ s <;> by_cases hqt : V q ∈ t <;> simp [f, g, hqs, hqt]
  have hfgh : (fun q => f (U q) * g (V q) * h (X q)) =
      (((fun q => (U q, V q)) ⁻¹' (s ×ˢ t)) ∩ (X ⁻¹' w)).indicator
        (fun _ => (1 : ℝ)) := by
    funext q
    by_cases hqs : U q ∈ s <;> by_cases hqt : V q ∈ t <;>
      by_cases hqw : X q ∈ w <;> simp [f, g, h, hqs, hqt, hqw]
  have hhy : (fun q => h (Y q)) = (Y ⁻¹' w).indicator (fun _ => (1 : ℝ)) := rfl
  have hint := htest f hf hbf g hg hbg h hh hbh
  rw [hfgh, hfg, hhy, integral_indicator ((hUV (hs.prod ht)).inter (hX hw)),
    integral_indicator (hUV (hs.prod ht)), integral_indicator (hY hw)] at hint
  simp only [setIntegral_one_eq_measureReal, measureReal_def] at hint
  rw [Measure.map_apply (hUV.prodMk hX) ((hs.prod ht).prod hw), Measure.prod_prod,
    Measure.map_apply hUV (hs.prod ht), Measure.map_apply hY hw]
  have hpre : (fun q => ((U q, V q), X q)) ⁻¹' ((s ×ˢ t) ×ˢ w) =
      ((fun q => (U q, V q)) ⁻¹' (s ×ˢ t)) ∩ (X ⁻¹' w) := by
    ext q
    rfl
  rw [hpre]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
  simpa only [ENNReal.toReal_mul] using hint

section StoppedFirstCycleLaw

variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hP : ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        P p = sbxS9RecenteredPathLaws P a p)
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)

include hl hsep hδ0 hδ1 hK hP hendpoint hpast hfuture hslices hscope

/-- The signed first-cycle identity with the literal no-return mass exposed.
The covariance hypothesis is the outstanding supplied-path producer. -/
theorem weighted_firstCyclePastRecord_normalized_assuming_path_laws
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (H : ℕ × CoupledSample d → ℝ)
    (hH : Measurable H) (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ q, F q.1 * H (firstCyclePastRecord hd lam l q.2) *
      Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
    (∫ q, F q.1 * H (firstCyclePastRecord hd lam l q.2) ∂annealedCoupledLaw Q.measure K) *
      ((annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal⁻¹ *
        ∫ q in regenerationNoReturn hd (l / lam), Φ (regenerationRecord hd lam l 0 q)
          ∂annealedCoupledLaw Q.measure K) := by
  have h := weighted_firstCyclePastRecord_identity_assuming_path_laws hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
    F hF hbF H hH hbH Φ hΦ hbΦ
  rw [regenerationConditionedLaw, ProbabilityTheory.cond, integral_smul_measure,
    ENNReal.toReal_inv, smul_eq_mul] at h
  exact h

/-- The first future record has the normalized no-return marginal, conditional
on the supplied-path covariance. -/
theorem firstRecord_integral_normalized_assuming_path_laws
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ q, Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
    (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal⁻¹ *
      ∫ q in regenerationNoReturn hd (l / lam), Φ (regenerationRecord hd lam l 0 q)
        ∂annealedCoupledLaw Q.measure K := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hb1 {α : Type} : BoundedRealTest (fun _ : α => (1 : ℝ)) :=
    ⟨1, fun _ => by norm_num⟩
  have h := weighted_firstCyclePastRecord_normalized_assuming_path_laws hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
    (fun _ => 1) measurable_const hb1 (fun _ => 1) measurable_const hb1 Φ hΦ hbΦ
  simpa only [one_mul, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, mul_one] using h

/-- The complete future record has its literal no-return conditioned law
jointly with any allowed local-field observation and the actual admissible
first-cycle past. Rectangle uniqueness supplies the measurable-generator
extension; the extra supplied-path covariance remains an internal obligation. -/
theorem firstCyclePastRecord_joint_law_assuming_path_laws
    {α : Type*} [MeasurableSpace α] (U : FieldPair d → α)
    (hU : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] U) :
    (annealedCoupledLaw Q.measure K).map (fun q =>
      ((U q.1, firstCyclePastRecord hd lam l q.2), regenerationRecord hd lam l 1 q)) =
    ((annealedCoupledLaw Q.measure K).map
      (fun q => (U q.1, firstCyclePastRecord hd lam l q.2))).prod
        ((regenerationConditionedLaw hd Q lam l K hK.1 hD).map
          (regenerationRecord hd lam l 0)) := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure (regenerationConditionedLaw hd Q lam l K hK.1 hD) :=
    ProbabilityTheory.cond_isProbabilityMeasure hD
  have hsc := hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1
  have hUg : Measurable (fun q : FieldPair d × CoupledSample d => U q.1) :=
    (hU.mono (Probability.localSigma_le_borel _) le_rfl).comp measurable_fst
  have hPast : Measurable (fun q : FieldPair d × CoupledSample d =>
      firstCyclePastRecord hd lam l q.2) :=
    (measurable_firstCyclePastRecord hd lam l hsc.1).comp measurable_snd
  apply joint_law_eq_prod_of_bounded_triple_tests
    (annealedCoupledLaw Q.measure K) (regenerationConditionedLaw hd Q lam l K hK.1 hD)
    (fun q => U q.1) (fun q => firstCyclePastRecord hd lam l q.2)
    (regenerationRecord hd lam l 1) (regenerationRecord hd lam l 0)
    hUg hPast
    hsc.2.1 (hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 0).2.1
  intro f hf hbf g hg hbg Φ hΦ hbΦ
  exact weighted_firstCyclePastRecord_identity_assuming_path_laws hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
    (fun ω => f (U ω)) (hf.comp hU) ⟨hbf.choose, fun ω => hbf.choose_spec _⟩
    g hg hbg Φ hΦ hbΦ

/-- A jointly measurable, product-integrable signed test transfers to the
actual stopped first-cycle joint law. The product law is the literal law of
the stopped past and conditioned origin future. -/
theorem firstCyclePastRecord_joint_integrable_assuming_path_laws
    {α : Type*} [MeasurableSpace α] (U : FieldPair d → α)
    (hU : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] U)
    (T : (α × (ℕ × CoupledSample d)) ×
      FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hT : Measurable T)
    (hiT : Integrable T (((annealedCoupledLaw Q.measure K).map
      (fun q => (U q.1, firstCyclePastRecord hd lam l q.2))).prod
      ((regenerationConditionedLaw hd Q lam l K hK.1 hD).map
        (regenerationRecord hd lam l 0)))) :
    Integrable (fun q => T ((U q.1, firstCyclePastRecord hd lam l q.2),
      regenerationRecord hd lam l 1 q)) (annealedCoupledLaw Q.measure K) ∧
    (∫ q, T ((U q.1, firstCyclePastRecord hd lam l q.2),
      regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
    ∫ p, T p ∂(((annealedCoupledLaw Q.measure K).map
      (fun q => (U q.1, firstCyclePastRecord hd lam l q.2))).prod
      ((regenerationConditionedLaw hd Q lam l K hK.1 hD).map
        (regenerationRecord hd lam l 0))) := by
  have hsc := hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1
  have hV : Measurable (fun q : FieldPair d × CoupledSample d =>
      (U q.1, firstCyclePastRecord hd lam l q.2)) :=
    ((hU.mono (Probability.localSigma_le_borel _) le_rfl).comp measurable_fst).prodMk
      ((measurable_firstCyclePastRecord hd lam l hsc.1).comp measurable_snd)
  have hJ := hV.prodMk hsc.2.1
  have hjoint := firstCyclePastRecord_joint_law_assuming_path_laws hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD U hU
  constructor
  · rw [← hjoint] at hiT
    exact hiT.comp_measurable hJ
  · rw [← hjoint, integral_map hJ.aemeasurable hT.aestronglyMeasurable]

/-- Fubini for a genuinely jointly integrable signed observation of the
local field, stopped past and complete first-cycle future. -/
theorem firstCyclePastRecord_joint_integral_iterated_assuming_path_laws
    {α : Type*} [MeasurableSpace α] (U : FieldPair d → α)
    (hU : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] U)
    (T : (α × (ℕ × CoupledSample d)) ×
      FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hT : Measurable T)
    (hiT : Integrable T (((annealedCoupledLaw Q.measure K).map
      (fun q => (U q.1, firstCyclePastRecord hd lam l q.2))).prod
      ((regenerationConditionedLaw hd Q lam l K hK.1 hD).map
        (regenerationRecord hd lam l 0)))) :
    (∫ q, T ((U q.1, firstCyclePastRecord hd lam l q.2),
      regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
    ∫ p, ∫ v, T (p, v) ∂((regenerationConditionedLaw hd Q lam l K hK.1 hD).map
      (regenerationRecord hd lam l 0)) ∂((annealedCoupledLaw Q.measure K).map
        (fun q => (U q.1, firstCyclePastRecord hd lam l q.2))) := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure (regenerationConditionedLaw hd Q lam l K hK.1 hD) :=
    ProbabilityTheory.cond_isProbabilityMeasure hD
  have h := firstCyclePastRecord_joint_integrable_assuming_path_laws hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
    U hU T hT hiT
  exact h.2.trans (integral_prod T hiT)

/-- A jointly integrable mixed observation with the no-return conditioning
mass and the original restricted annealed law displayed explicitly. -/
theorem firstCyclePastRecord_joint_integral_normalized_assuming_path_laws
    {α : Type*} [MeasurableSpace α] (U : FieldPair d → α)
    (hU : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] U)
    (T : (α × (ℕ × CoupledSample d)) ×
      FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hT : Measurable T)
    (hiT : Integrable T (((annealedCoupledLaw Q.measure K).map
      (fun q => (U q.1, firstCyclePastRecord hd lam l q.2))).prod
      ((regenerationConditionedLaw hd Q lam l K hK.1 hD).map
        (regenerationRecord hd lam l 0)))) :
    (∫ q, T ((U q.1, firstCyclePastRecord hd lam l q.2),
      regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
    ∫ p, ((annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam))).toReal⁻¹ *
      ∫ q in regenerationNoReturn hd (l / lam),
        T (p, regenerationRecord hd lam l 0 q) ∂annealedCoupledLaw Q.measure K)
      ∂((annealedCoupledLaw Q.measure K).map
        (fun q => (U q.1, firstCyclePastRecord hd lam l q.2))) := by
  have hr := (hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 0).2.1
  have hinner (p : α × (ℕ × CoupledSample d)) :
      (∫ v, T (p, v) ∂((regenerationConditionedLaw hd Q lam l K hK.1 hD).map
        (regenerationRecord hd lam l 0))) =
      (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal⁻¹ *
        ∫ q in regenerationNoReturn hd (l / lam),
          T (p, regenerationRecord hd lam l 0 q) ∂annealedCoupledLaw Q.measure K := by
    rw [integral_map hr.aemeasurable (f := fun v => T (p, v))
      (hT.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      regenerationConditionedLaw, ProbabilityTheory.cond, integral_smul_measure,
      ENNReal.toReal_inv, smul_eq_mul]
  have h := firstCyclePastRecord_joint_integral_iterated_assuming_path_laws hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
    U hU T hT hiT
  simpa only [hinner] using h

/-- The jointly integrable observation sums over the literal first-cycle
grid slices, with the iterated integral taken under the two actual laws. -/
theorem firstCyclePastRecord_joint_slices_hasSum_assuming_path_laws
    {α : Type*} [MeasurableSpace α] (U : FieldPair d → α)
    (hU : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] U)
    (T : (α × (ℕ × CoupledSample d)) ×
      FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hT : Measurable T)
    (hiT : Integrable T (((annealedCoupledLaw Q.measure K).map
      (fun q => (U q.1, firstCyclePastRecord hd lam l q.2))).prod
      ((regenerationConditionedLaw hd Q lam l K hK.1 hD).map
        (regenerationRecord hd lam l 0)))) :
    HasSum (fun n : ℕ =>
      ∫ q in {q | regenerationTime hd lam l 1 q.2 =
        ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        T ((U q.1, firstCyclePastRecord hd lam l q.2),
          regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K)
      (∫ p, ∫ v, T (p, v) ∂((regenerationConditionedLaw hd Q lam l K hK.1 hD).map
        (regenerationRecord hd lam l 0)) ∂((annealedCoupledLaw Q.measure K).map
          (fun q => (U q.1, firstCyclePastRecord hd lam l q.2)))) := by
  have hi := (firstCyclePastRecord_joint_integrable_assuming_path_laws hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
    U hU T hT hiT).1
  have hs := first_cycle_hasSum_integral_of_scope hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK hscope hD (annealedCoupledLaw Q.measure K) (Set.mem_insert _ _)
    (fun q => T ((U q.1, firstCyclePastRecord hd lam l q.2),
      regenerationRecord hd lam l 1 q)) hi
  rw [firstCyclePastRecord_joint_integral_iterated_assuming_path_laws hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
    U hU T hT hiT] at hs
  exact hs

/-- Conditional on the sigma algebra generated jointly by the allowed local
joint-field observation and the admissible first-cycle past, a bounded test
of the full future record has the constant literal conditioned-origin mean.
This first-cycle consumer retains the exact missing supplied-law covariance. -/
theorem firstCyclePastRecord_condExp_assuming_path_laws
    {α : Type*} [MeasurableSpace α] (U : FieldPair d → α)
    (hU : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] U)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    Integrable (fun q => Φ (regenerationRecord hd lam l 1 q))
      (annealedCoupledLaw Q.measure K) ∧
    (annealedCoupledLaw Q.measure K)[(fun q => Φ (regenerationRecord hd lam l 1 q)) |
      MeasurableSpace.comap (fun q => (U q.1, firstCyclePastRecord hd lam l q.2))
        inferInstance] =ᵐ[annealedCoupledLaw Q.measure K]
      (fun _ => ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let V := fun q : FieldPair d × CoupledSample d =>
    (U q.1, firstCyclePastRecord hd lam l q.2)
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hD
  have hsc := hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1
  have hV : Measurable V :=
    ((hU.mono (Probability.localSigma_le_borel _) le_rfl).comp measurable_fst).prodMk
      ((measurable_firstCyclePastRecord hd lam l hsc.1).comp measurable_snd)
  have hi : Integrable (fun q => Φ (regenerationRecord hd lam l 1 q)) μ := by
    obtain ⟨C, hC⟩ := hbΦ
    exact Integrable.of_bound (hΦ.comp hsc.2.1).aestronglyMeasurable C
      (ae_of_all _ fun q => by simpa only [Real.norm_eq_abs] using hC _)
  refine ⟨hi, ?_⟩
  have hjoint := firstCyclePastRecord_joint_law_assuming_path_laws hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD U hU
  have hmarg : μ.map (regenerationRecord hd lam l 1) =
      ν.map (regenerationRecord hd lam l 0) := by
    have hproj := congrArg (Measure.map Prod.snd) hjoint
    rw [Measure.map_map measurable_snd (hV.prodMk hsc.2.1), Measure.map_snd_prod,
      measure_univ, one_smul] at hproj
    exact hproj
  have hind : IndepFun V (regenerationRecord hd lam l 1) μ := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hsc.2.1.aemeasurable).mpr
    rw [hmarg]
    exact hjoint
  let f := fun q => Φ (regenerationRecord hd lam l 1 q)
  have hf : Measurable f := hΦ.comp hsc.2.1
  have hindf : IndepFun f V μ := hind.symm.comp hΦ measurable_id
  have hcond := condExp_indep_eq hf.comap_le hV.comap_le
    (show StronglyMeasurable[MeasurableSpace.comap f inferInstance] f from
      (Measurable.of_comap_le le_rfl).stronglyMeasurable) hindf
  have hmean : (∫ q, f q ∂μ) = ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν := by
    rw [← integral_map hsc.2.1.aemeasurable hΦ.aestronglyMeasurable, hmarg,
      integral_map (hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1
        P K hK hD 0).2.1.aemeasurable hΦ.aestronglyMeasurable]
  exact hcond.trans (ae_of_all _ fun _ => hmean)

/-- The preceding conditional identity holds for the entire allowed local
joint-field sigma algebra together with the admissible first-cycle past.
Taking the identity as a local-space-valued observation retains both fields. -/
theorem firstCyclePastRecord_localSigma_condExp_assuming_path_laws
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    Integrable (fun q => Φ (regenerationRecord hd lam l 1 q))
      (annealedCoupledLaw Q.measure K) ∧
    (annealedCoupledLaw Q.measure K)[(fun q => Φ (regenerationRecord hd lam l 1 q)) |
      (localSigma {x : Vec d | euclideanNorm x < l / lam}).comap Prod.fst ⊔
        (inferInstance : MeasurableSpace (ℕ × CoupledSample d)).comap
          (fun q : FieldPair d × CoupledSample d => firstCyclePastRecord hd lam l q.2)]
      =ᵐ[annealedCoupledLaw Q.measure K]
        (fun _ => ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
  have h := @firstCyclePastRecord_condExp_assuming_path_laws d hd Λ₀ r₀ Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
    (FieldPair d) (localSigma {x : Vec d | euclideanNorm x < l / lam})
    id measurable_id Φ hΦ hbΦ
  have hm := MeasurableSpace.comap_prodMk
    (mβ := localSigma {x : Vec d | euclideanNorm x < l / lam})
    (mγ := inferInstance) (Prod.fst : FieldPair d × CoupledSample d → FieldPair d)
    (fun q : FieldPair d × CoupledSample d => firstCyclePastRecord hd lam l q.2)
  rw [← hm]
  exact h

/-- Integrable future tests have the same conditional mean as under the
literal no-return conditioned origin law, given the stopped first-cycle past
and an allowed local-field observation. -/
theorem firstCyclePastRecord_integrable_condExp_assuming_path_laws
    {α : Type*} [MeasurableSpace α] (U : FieldPair d → α)
    (hU : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] U)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ)
    (hiΦ : Integrable (fun q => Φ (regenerationRecord hd lam l 0 q))
      (regenerationConditionedLaw hd Q lam l K hK.1 hD)) :
    Integrable (fun q => Φ (regenerationRecord hd lam l 1 q))
      (annealedCoupledLaw Q.measure K) ∧
    (annealedCoupledLaw Q.measure K)[(fun q => Φ (regenerationRecord hd lam l 1 q)) |
      MeasurableSpace.comap (fun q => (U q.1, firstCyclePastRecord hd lam l q.2))
        inferInstance] =ᵐ[annealedCoupledLaw Q.measure K]
      (fun _ => ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let V := fun q : FieldPair d × CoupledSample d =>
    (U q.1, firstCyclePastRecord hd lam l q.2)
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hD
  have hsc := hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1
  have hsc0 := hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 0
  have hV : Measurable V :=
    ((hU.mono (Probability.localSigma_le_borel _) le_rfl).comp measurable_fst).prodMk
      ((measurable_firstCyclePastRecord hd lam l hsc.1).comp measurable_snd)
  have hjoint := firstCyclePastRecord_joint_law_assuming_path_laws hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD U hU
  have hmarg : μ.map (regenerationRecord hd lam l 1) =
      ν.map (regenerationRecord hd lam l 0) := by
    have hproj := congrArg (Measure.map Prod.snd) hjoint
    rw [Measure.map_map measurable_snd (hV.prodMk hsc.2.1), Measure.map_snd_prod,
      measure_univ, one_smul] at hproj
    exact hproj
  have hiMap : Integrable Φ (ν.map (regenerationRecord hd lam l 0)) :=
    (integrable_map_measure hΦ.aestronglyMeasurable hsc0.2.1.aemeasurable).2 hiΦ
  have hi : Integrable (fun q => Φ (regenerationRecord hd lam l 1 q)) μ :=
    (integrable_map_measure hΦ.aestronglyMeasurable hsc.2.1.aemeasurable).1 (hmarg.symm ▸ hiMap)
  refine ⟨hi, ?_⟩
  have hind : IndepFun V (regenerationRecord hd lam l 1) μ := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hsc.2.1.aemeasurable).mpr
    rw [hmarg]
    exact hjoint
  let f := fun q => Φ (regenerationRecord hd lam l 1 q)
  have hf : Measurable f := hΦ.comp hsc.2.1
  have hindf : IndepFun f V μ := hind.symm.comp hΦ measurable_id
  have hcond := condExp_indep_eq hf.comap_le hV.comap_le
    (show StronglyMeasurable[MeasurableSpace.comap f inferInstance] f from
      (Measurable.of_comap_le le_rfl).stronglyMeasurable) hindf
  have hmean : (∫ q, f q ∂μ) = ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν := by
    rw [← integral_map hsc.2.1.aemeasurable hΦ.aestronglyMeasurable, hmarg,
      integral_map hsc0.2.1.aemeasurable hΦ.aestronglyMeasurable]
  exact hcond.trans (ae_of_all _ fun _ => hmean)

/-- The integrable-test conditional identity also holds given the entire
allowed local-field sigma algebra and the admissible stopped past. -/
theorem firstCyclePastRecord_integrable_localSigma_condExp_assuming_path_laws
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ)
    (hiΦ : Integrable (fun q => Φ (regenerationRecord hd lam l 0 q))
      (regenerationConditionedLaw hd Q lam l K hK.1 hD)) :
    Integrable (fun q => Φ (regenerationRecord hd lam l 1 q))
      (annealedCoupledLaw Q.measure K) ∧
    (annealedCoupledLaw Q.measure K)[(fun q => Φ (regenerationRecord hd lam l 1 q)) |
      (localSigma {x : Vec d | euclideanNorm x < l / lam}).comap Prod.fst ⊔
        (inferInstance : MeasurableSpace (ℕ × CoupledSample d)).comap
          (fun q : FieldPair d × CoupledSample d => firstCyclePastRecord hd lam l q.2)]
      =ᵐ[annealedCoupledLaw Q.measure K]
        (fun _ => ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
  have h := @firstCyclePastRecord_integrable_condExp_assuming_path_laws d hd Λ₀ r₀ Q lam
    h0 h1 l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
    (FieldPair d) (localSigma {x : Vec d | euclideanNorm x < l / lam})
    id measurable_id Φ hΦ hiΦ
  have hm := MeasurableSpace.comap_prodMk
    (mβ := localSigma {x : Vec d | euclideanNorm x < l / lam})
    (mγ := inferInstance) (Prod.fst : FieldPair d × CoupledSample d → FieldPair d)
    (fun q : FieldPair d × CoupledSample d => firstCyclePastRecord hd lam l q.2)
  rw [← hm]
  exact h

include hD
omit hP hendpoint hpast hfuture hslices

/-- On the full-measure grid supplied by the scope theorem, membership in
an actual first-cycle slice is determined by the stopped past record. -/
theorem firstCyclePastRecord_slice_iff_ae (n : ℕ) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      (regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)) ↔
      (firstCyclePastRecord hd lam l q.2).1 = n := by
  have hsc := hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1
  filter_upwards [hsc.2.2 (annealedCoupledLaw Q.measure K) (Set.mem_insert _ _)] with q hq
  obtain ⟨m, hm, ht, _⟩ := hq
  have hr : (firstCyclePastRecord hd lam l q.2).1 = m := by
    rw [firstCyclePastRecord_on_slice hd lam l h0 m q.2 ht]
  rw [hr]
  constructor
  · intro hs
    have heq := ENNReal.coe_inj.mp (ht.symm.trans hs)
    have hcast := mul_right_cancel₀ (EinsteinRelation.regenDelta_pos h0).ne' heq
    exact_mod_cast hcast
  · intro hmn
    simpa only [hmn] using ht

include hP hendpoint hpast hfuture hslices

/-- The bounded local-field and stopped-history factors preserve genuine
integrability of the signed first-cycle future test. -/
theorem integrable_weighted_firstCyclePastRecord_assuming_path_laws
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (H : ℕ × CoupledSample d → ℝ)
    (hH : Measurable H) (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ)
    (hiΦ : Integrable (fun q => Φ (regenerationRecord hd lam l 0 q))
      (regenerationConditionedLaw hd Q lam l K hK.1 hD)) :
    Integrable (fun q => F q.1 * H (firstCyclePastRecord hd lam l q.2) *
      Φ (regenerationRecord hd lam l 1 q)) (annealedCoupledLaw Q.measure K) := by
  have hi := (firstCyclePastRecord_integrable_condExp_assuming_path_laws hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
    F hF Φ hΦ hiΦ).1
  have hsc := hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1
  have hPast : Measurable (fun q : FieldPair d × CoupledSample d =>
      firstCyclePastRecord hd lam l q.2) :=
    (measurable_firstCyclePastRecord hd lam l hsc.1).comp measurable_snd
  obtain ⟨C, hC⟩ := hbH
  obtain ⟨D, hD'⟩ := hbF
  have hiH := hi.bdd_mul (hH.comp hPast).aestronglyMeasurable
    (ae_of_all _ fun q => by simpa only [Function.comp_def, Real.norm_eq_abs] using hC (firstCyclePastRecord hd lam l q.2))
  have hiF := hiH.bdd_mul
    ((hF.mono (Probability.localSigma_le_borel _) le_rfl).comp measurable_fst).aestronglyMeasurable
    (ae_of_all _ fun q => by simpa only [Function.comp_def, Real.norm_eq_abs] using hD' q.1)
  simpa only [Function.comp_def, mul_assoc] using hiF

/-- The first-cycle weighted factorization extends to measurable signed
future tests under the actual conditioned origin law. -/
theorem weighted_firstCyclePastRecord_measurable_identity_assuming_path_laws
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (H : ℕ × CoupledSample d → ℝ) (hH : Measurable H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) :
    (∫ q, F q.1 * H (firstCyclePastRecord hd lam l q.2) *
      Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
    (∫ q, F q.1 * H (firstCyclePastRecord hd lam l q.2) ∂annealedCoupledLaw Q.measure K) *
      ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let V := fun q : FieldPair d × CoupledSample d =>
    (F q.1, firstCyclePastRecord hd lam l q.2)
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hD
  have hsc := hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1
  have hsc0 := hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 0
  have hV : Measurable V :=
    ((hF.mono (Probability.localSigma_le_borel _) le_rfl).comp measurable_fst).prodMk
      ((measurable_firstCyclePastRecord hd lam l hsc.1).comp measurable_snd)
  have hjoint := firstCyclePastRecord_joint_law_assuming_path_laws hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD F hF
  have hmarg : μ.map (regenerationRecord hd lam l 1) =
      ν.map (regenerationRecord hd lam l 0) := by
    have hproj := congrArg (Measure.map Prod.snd) hjoint
    rw [Measure.map_map measurable_snd (hV.prodMk hsc.2.1), Measure.map_snd_prod,
      measure_univ, one_smul] at hproj
    exact hproj
  have hind : IndepFun V (regenerationRecord hd lam l 1) μ := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hsc.2.1.aemeasurable).mpr
    rw [hmarg]
    exact hjoint
  have hw : Measurable (fun p : ℝ × (ℕ × CoupledSample d) => p.1 * H p.2) :=
    measurable_fst.mul (hH.comp measurable_snd)
  have hind' := hind.comp hw hΦ
  have heq := hind'.integral_fun_mul_eq_mul_integral
    (hw.comp hV).aestronglyMeasurable (hΦ.comp hsc.2.1).aestronglyMeasurable
  have hmean : (∫ q, Φ (regenerationRecord hd lam l 1 q) ∂μ) =
      ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν := by
    rw [← integral_map hsc.2.1.aemeasurable hΦ.aestronglyMeasurable, hmarg,
      integral_map hsc0.2.1.aemeasurable hΦ.aestronglyMeasurable]
  change (∫ q, F q.1 * H (firstCyclePastRecord hd lam l q.2) *
      Φ (regenerationRecord hd lam l 1 q) ∂μ) = _
  dsimp only [Function.comp_def, V] at heq
  rw [heq, hmean]

/-- On each literal slice, an arbitrary admissible finite-history test and
an integrable signed future test have a genuinely integrable product. -/
theorem integrableOn_weighted_firstCycle_slice_assuming_path_laws
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ)
    (hiΦ : Integrable (fun q => Φ (regenerationRecord hd lam l 0 q))
      (regenerationConditionedLaw hd Q lam l K hK.1 hD)) :
    IntegrableOn (fun q => F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q))
      {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
      (annealedCoupledLaw Q.measure K) := by
  have hHg : Measurable H := hH.mono (Probability.finiteHistorySigma_le _ _) le_rfl
  have hb : BoundedRealTest (fun p : ℕ × CoupledSample d => H p.2) :=
    ⟨hbH.choose, fun p => hbH.choose_spec p.2⟩
  have hi := integrable_weighted_firstCyclePastRecord_assuming_path_laws hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
    F hF hbF (fun p => H p.2) (hHg.comp measurable_snd) hb Φ hΦ hiΦ
  have hset : MeasurableSet {q : FieldPair d × CoupledSample d |
      regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} :=
    (hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1).1.comp
      measurable_snd (measurableSet_singleton _)
  apply (integrableOn_congr_fun ?_ hset).mp hi.integrableOn
  intro q hq
  change F q.1 * H (firstCyclePastRecord hd lam l q.2).2 *
    Φ (regenerationRecord hd lam l 1 q) = F q.1 * H q.2 *
    Φ (regenerationRecord hd lam l 1 q)
  rw [← finiteHistory_test_eq_firstCyclePastRecord_on_slice hd lam l h0 n H hH q.2 hq]

/-- The literal finite-history slice identity for a signed future test.
The supplied-law covariance remains an explicit conditional input. -/
theorem weighted_firstCycle_slice_integrable_identity_assuming_path_laws
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (n : ℕ) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) :
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q)
        ∂annealedCoupledLaw Q.measure K) =
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 ∂annealedCoupledLaw Q.measure K) *
      ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let S : Set (FieldPair d × CoupledSample d) := {q |
    regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hS : MeasurableSet S :=
    (hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1).1.comp
      measurable_snd (measurableSet_singleton _)
  let G : ℕ × CoupledSample d → ℝ := fun p => if p.1 = n then H p.2 else 0
  have hG : Measurable G := by
    apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    · exact ((hH.mono (Probability.finiteHistorySigma_le _ _) le_rfl).comp measurable_snd)
    · exact measurable_const
  have heq := weighted_firstCyclePastRecord_measurable_identity_assuming_path_laws
    hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture
    hslices hscope hD F hF G hG Φ hΦ
  have hslice := firstCyclePastRecord_slice_iff_ae hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK hscope hD n
  have hleft : (∫ q, F q.1 * G (firstCyclePastRecord hd lam l q.2) *
      Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
      ∫ q in S, F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q)
        ∂annealedCoupledLaw Q.measure K := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hslice] with q hq
    by_cases h : q ∈ S
    · have hrec := finiteHistory_test_eq_firstCyclePastRecord_on_slice hd lam l h0 n H hH q.2 h
      simp only [Set.indicator_of_mem h, G, ite_eq_left (hq.mp h), hrec]
    · have hn : (firstCyclePastRecord hd lam l q.2).1 ≠ n := fun hn => h (hq.mpr hn)
      simp only [Set.indicator_of_notMem h, G, ite_eq_right hn, mul_zero, zero_mul]
  have hright : (∫ q, F q.1 * G (firstCyclePastRecord hd lam l q.2)
      ∂annealedCoupledLaw Q.measure K) =
      ∫ q in S, F q.1 * H q.2 ∂annealedCoupledLaw Q.measure K := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hslice] with q hq
    by_cases h : q ∈ S
    · have hrec := finiteHistory_test_eq_firstCyclePastRecord_on_slice hd lam l h0 n H hH q.2 h
      simp only [Set.indicator_of_mem h, G, ite_eq_left (hq.mp h), hrec]
    · have hn : (firstCyclePastRecord hd lam l q.2).1 ≠ n := fun hn => h (hq.mpr hn)
      simp only [Set.indicator_of_notMem h, G, ite_eq_right hn, mul_zero]
  exact hleft.symm.trans (heq.trans (congrArg (fun x : ℝ => x *
    ∫ q, Φ (regenerationRecord hd lam l 0 q)
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) hright))

/-- Summing the actual disjoint first-cycle slices gives the signed
weighted product with the conditioned future mean. -/
theorem weighted_firstCyclePastRecord_integrable_slices_hasSum_assuming_path_laws
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (H : ℕ × CoupledSample d → ℝ)
    (hH : Measurable H) (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ)
    (hiΦ : Integrable (fun q => Φ (regenerationRecord hd lam l 0 q))
      (regenerationConditionedLaw hd Q lam l K hK.1 hD)) :
    HasSum (fun n : ℕ =>
      ∫ q in {q | regenerationTime hd lam l 1 q.2 =
        ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 * H (firstCyclePastRecord hd lam l q.2) *
          Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K)
      ((∫ q, F q.1 * H (firstCyclePastRecord hd lam l q.2)
          ∂annealedCoupledLaw Q.measure K) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
  have hi := integrable_weighted_firstCyclePastRecord_assuming_path_laws hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
    F hF hbF H hH hbH Φ hΦ hiΦ
  have hs := first_cycle_hasSum_integral_of_scope hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK hscope hD (annealedCoupledLaw Q.measure K) (Set.mem_insert _ _)
    (fun q => F q.1 * H (firstCyclePastRecord hd lam l q.2) *
      Φ (regenerationRecord hd lam l 1 q)) hi
  rw [weighted_firstCyclePastRecord_measurable_identity_assuming_path_laws hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD F hF H hH Φ hΦ] at hs
  exact hs

/-- A uniformly bounded family of admissible tests may vary with the actual
first-cycle slice. The sum retains the stopped record selected by that slice. -/
theorem weighted_firstCycle_finiteHistory_slices_hasSum_assuming_path_laws
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (H : ℕ → CoupledSample d → ℝ)
    (hH : ∀ n, Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] (H n))
    (C : ℝ) (hbH : ∀ n z, |H n z| ≤ C)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ)
    (hiΦ : Integrable (fun q => Φ (regenerationRecord hd lam l 0 q))
      (regenerationConditionedLaw hd Q lam l K hK.1 hD)) :
    HasSum (fun n : ℕ =>
      ∫ q in {q | regenerationTime hd lam l 1 q.2 =
        ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 * H (n + 2) q.2 * Φ (regenerationRecord hd lam l 1 q)
          ∂annealedCoupledLaw Q.measure K)
      ((∫ q, F q.1 * H (firstCyclePastRecord hd lam l q.2).1
          (firstCyclePastRecord hd lam l q.2).2 ∂annealedCoupledLaw Q.measure K) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
  let G : ℕ × CoupledSample d → ℝ := fun p => H p.1 p.2
  have hG : Measurable G := measurable_from_prod_countable_right fun n =>
    (hH n).mono (Probability.finiteHistorySigma_le _ _) le_rfl
  have hbG : BoundedRealTest G := ⟨C, fun p => hbH p.1 p.2⟩
  have hs := weighted_firstCyclePastRecord_integrable_slices_hasSum_assuming_path_laws
    hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture
    hslices hscope hD F hF hbF G hG hbG Φ hΦ hiΦ
  apply HasSum.congr_fun hs
  intro n
  have hset : MeasurableSet {q : FieldPair d × CoupledSample d |
      regenerationTime hd lam l 1 q.2 =
        ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} :=
    (hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1).1.comp
      measurable_snd (measurableSet_singleton _)
  apply setIntegral_congr_fun hset
  intro q hq
  change F q.1 * H (n + 2) q.2 * Φ (regenerationRecord hd lam l 1 q) =
    F q.1 * G (firstCyclePastRecord hd lam l q.2) * Φ (regenerationRecord hd lam l 1 q)
  rw [firstCyclePastRecord_on_slice hd lam l h0 (n + 2) q.2 hq]
  dsimp only [G]
  rw [← finiteHistory_test_eq_stopped (Renewal.regenDelta lam) (n + 2 - 1)
    (H (n + 2)) (hH (n + 2)) q.2]

/-- The factorized terms on the original slices sum to the stopped-past
expectation times the conditioned future mean. -/
theorem weighted_firstCycle_finiteHistory_factorized_slices_hasSum_assuming_path_laws
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (H : ℕ → CoupledSample d → ℝ)
    (hH : ∀ n, Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] (H n))
    (C : ℝ) (hbH : ∀ n z, |H n z| ≤ C)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ)
    (hiΦ : Integrable (fun q => Φ (regenerationRecord hd lam l 0 q))
      (regenerationConditionedLaw hd Q lam l K hK.1 hD)) :
    HasSum (fun n : ℕ =>
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 * H (n + 2) q.2 ∂annealedCoupledLaw Q.measure K) *
      ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD)
      ((∫ q, F q.1 * H (firstCyclePastRecord hd lam l q.2).1
          (firstCyclePastRecord hd lam l q.2).2 ∂annealedCoupledLaw Q.measure K) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
  have hs := weighted_firstCycle_finiteHistory_slices_hasSum_assuming_path_laws
    hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture
    hslices hscope hD F hF hbF H hH C hbH Φ hΦ hiΦ
  apply HasSum.congr_fun hs
  intro n
  exact (weighted_firstCycle_slice_integrable_identity_assuming_path_laws
    hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hP hendpoint hpast hfuture
    hslices hscope hD F hF (n + 2) (H (n + 2)) (hH (n + 2)) Φ hΦ).symm

end StoppedFirstCycleLaw

#print axioms weighted_firstCyclePastRecord_normalized_assuming_path_laws
#print axioms finiteHistory_test_eq_stopped
#print axioms finiteHistory_test_eq_firstCyclePastRecord_on_slice
#print axioms weighted_firstCycle_slice_integrable_identity_assuming_path_laws
#print axioms firstCyclePastRecord_slice_iff_ae
#print axioms integrable_weighted_firstCyclePastRecord_assuming_path_laws
#print axioms weighted_firstCyclePastRecord_measurable_identity_assuming_path_laws
#print axioms integrableOn_weighted_firstCycle_slice_assuming_path_laws
#print axioms weighted_firstCyclePastRecord_integrable_slices_hasSum_assuming_path_laws
#print axioms weighted_firstCycle_finiteHistory_slices_hasSum_assuming_path_laws
#print axioms weighted_firstCycle_finiteHistory_factorized_slices_hasSum_assuming_path_laws

#print axioms firstCyclePastRecord_joint_integrable_assuming_path_laws
#print axioms firstCyclePastRecord_joint_integral_iterated_assuming_path_laws
#print axioms firstCyclePastRecord_joint_integral_normalized_assuming_path_laws
#print axioms firstCyclePastRecord_joint_slices_hasSum_assuming_path_laws
#print axioms firstCyclePastRecord_setIntegral_eq
#print axioms weighted_firstCyclePastRecord_slice_identity_assuming_path_laws
#print axioms weighted_firstCyclePastRecord_slices_absSummable
#print axioms firstCyclePastRecord_localSigma_condExp_assuming_path_laws
#print axioms joint_law_eq_prod_of_bounded_triple_tests
#print axioms firstCyclePastRecord_joint_law_assuming_path_laws
#print axioms firstCyclePastRecord_condExp_assuming_path_laws

#print axioms firstCyclePastRecord
#print axioms firstCyclePastRecord_on_slice
#print axioms firstCyclePastRecord_slice_test_measurable
#print axioms measurable_firstCyclePastRecord
#print axioms integrable_weighted_firstCyclePastRecord
#print axioms weighted_firstCyclePastRecord_identity_assuming_path_laws

#print axioms independence_assuming_original_path_covariance
#print axioms killed_future_eq_shifted_origin_assuming_path_laws
#print axioms killed_future_local_mean_assuming_path_laws
#print axioms weighted_slice_identity_assuming_path_laws

#print axioms map_annealedCoupledLaw_environment_observation
#print axioms first_record_local_tuple_law_of_slice_integrals
#print axioms first_record_joint_law_of_local_slice_integrals
#print axioms weighted_first_cycle_integral_of_slice_integrals
#print axioms joint_law_eq_prod_of_bounded_product_tests

#print axioms integrable_weighted_regeneration_record
#print axioms first_cycle_early_slice_null
#print axioms first_cycle_hasSum_integral_of_scope
#print axioms first_cycle_slice_probabilities_hasSum
#print axioms weighted_centered_slice_integral_eq_origin_coupling_difference
#print axioms weighted_first_marginal_origin_remainders_hasSum
#print axioms weighted_first_marginal_origin_remainders_absSummable
#print axioms weighted_translated_origin_future_spatial_factor
#print axioms weighted_slice_defect_eq_origin_coupling_difference
#print axioms weighted_spatial_factor_of_local_future_versions
#print axioms weighted_spatial_factor_of_local_future_versions_and_mean
#print axioms killed_future_difference_eq_origin_coupling_difference
#print axioms integrable_weighted_origin_coupling_difference
#print axioms annealed_killed_future_mean_eq_frozen_record_assuming_path_laws
#print axioms integrable_annealed_killed_future_means
#print axioms killed_future_origin_eq_frozen_record
#print axioms path_starts_recenter
#print axioms coupling_origin_eq_recenter_assuming_path_laws
#print axioms spatialFutureRecord_recenter
#print axioms killedFutureTest_recenter_origin
#print axioms killed_future_integral_recenter
#print axioms integrable_killedFutureTest
#print axioms measurable_killed_future_mean
#print axioms boundedRealTest_killed_future_mean
#print axioms annealed_killed_future_mean_recenter
#print axioms map_endpointBall_volume_sub
#print axioms endpointAverage_sub
#print axioms measurable_endpointAverage_path
#print axioms boundedRealTest_endpointAverage_path
#print axioms integrable_successfulEndpoint_test
#print axioms integrable_endpointAverage_test
#print axioms uniformSuccessfulEndpointAt_recenter
#print axioms endpoint_integrands_integrable_recenter
#print axioms hasUniformSuccessfulEndpoint_recenter
#print axioms probability_and_endpoint_recenter

#print axioms firstCyclePastRecord_integrable_condExp_assuming_path_laws
#print axioms firstRecord_integral_normalized_assuming_path_laws
#print axioms firstCyclePastRecord_integrable_localSigma_condExp_assuming_path_laws
#print axioms weighted_firstCyclePastRecord_measurable_identity_assuming_path_laws
#print axioms integrable_weighted_firstCyclePastRecord_assuming_path_laws
#print axioms firstCyclePastRecord_slice_iff_ae
#print axioms weighted_firstCyclePastRecord_integrable_slices_hasSum_assuming_path_laws
#print axioms finiteHistory_test_eq_stopped
#print axioms finiteHistory_test_eq_firstCyclePastRecord_on_slice
#print axioms integrableOn_weighted_firstCycle_slice_assuming_path_laws
#lint-

end EinsteinFull.Blueprint.EndpointAverageTransport
