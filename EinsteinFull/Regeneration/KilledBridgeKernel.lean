import EinsteinFull.Regeneration.KilledBridgeNormalization
import EinsteinRelation.Regeneration.KilledSegmentMeasurability
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Joint kernels for the literal killed bridge

The starting point and environment are both kernel parameters. Mathlib's
jointly measurable kernel Radon--Nikodym derivative agrees fibrewise almost
everywhere with the measure derivative in the existing bridge definition.
Thus no measurability of arbitrarily selected pointwise derivatives is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration

/-- The actual uniform endpoint law as a joint starting-point/environment
kernel. The normalizing volume is independent of the starting point. -/
def uniformEndpointKernel {d : ℕ} (R : ℝ) (i : Fin d) :
    Kernel (Vec d × FieldPair d) (Vec d) :=
  (Kernel.const _ (volume : Measure (Vec d))).withDensity fun a y =>
    (endpointBall i R a.1).indicator
      (fun _ => (volume (endpointBall i R (0 : Vec d)))⁻¹) y

/-- The joint density used for the uniform endpoint law is measurable. -/
theorem measurable_uniformEndpoint_density {d : ℕ} (R : ℝ) (i : Fin d) :
    Measurable (fun p : (Vec d × FieldPair d) × Vec d =>
      (endpointBall i R p.1.1).indicator
        (fun _ => (volume (endpointBall i R (0 : Vec d)))⁻¹) p.2) := by
  exact measurable_const.indicator ((measurableSet_endpointBall_pair i R).preimage
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

/-- Every fibre is exactly the conditional uniform volume in the original
definition; this equality does not need a positive-radius premise. -/
theorem uniformEndpointKernel_apply {d : ℕ} (R : ℝ) (i : Fin d)
    (a : Vec d × FieldPair d) :
    uniformEndpointKernel R i a =
      cond (volume : Measure (Vec d)) (endpointBall i R a.1) := by
  rw [uniformEndpointKernel,
    Kernel.withDensity_apply _ (measurable_uniformEndpoint_density R i)]
  change volume.withDensity ((endpointBall i R a.1).indicator
    (fun _ => (volume (endpointBall i R (0 : Vec d)))⁻¹)) = _
  have hB : MeasurableSet (endpointBall i R a.1) :=
    (measurableSet_endpointBall_pair i R).preimage
      (measurable_const.prodMk measurable_id)
  rw [withDensity_indicator hB, withDensity_const, ProbabilityTheory.cond, endpointBall_volume_eq i R a.1]

/-- At positive radius the joint endpoint kernel is Markov. -/
theorem isMarkovKernel_uniformEndpointKernel {d : ℕ} (R : ℝ) (i : Fin d)
    (hR : 0 < R) : IsMarkovKernel (uniformEndpointKernel R i) := by
  constructor
  intro a
  rw [uniformEndpointKernel_apply]
  exact cond_isProbabilityMeasure_of_finite (endpointBall_volume_pos i R hR a.1).ne'
    (endpointBall_volume_ne_top i R hR a.1)

/-- The actual killed-segment density is jointly measurable in starting
point, environment, and path. -/
theorem measurable_killedSegment_density {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) :
    Measurable (fun p : (Vec d × FieldPair d) × Path d =>
      ({γ : Path d | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R p.1.1}).indicator
        (fun _ => (1 : ℝ≥0∞)) p.2) := by
  let S : Set ((Vec d × FieldPair d) × Path d) :=
    {p | ∀ t : ℝ≥0, t ≤ Δ → p.2 t ∈ couplingRegion i R p.1.1}
  have hm : Measurable (fun p : (Vec d × FieldPair d) × Path d => (p.1.1, p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hS₀ : MeasurableSet {p : Vec d × Path d |
      ∀ t : ℝ≥0, t ≤ Δ → p.2 t ∈ couplingRegion i R p.1} :=
    (Renewal.isOpen_killedSegment_event Δ R i).measurableSet
  have hSpre := hS₀.preimage hm
  have hS : MeasurableSet S := hSpre
  have hmeas : Measurable (S.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hS
  have heq : (fun p : (Vec d × FieldPair d) × Path d =>
      ({γ : Path d | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R p.1.1}).indicator
        (fun _ => (1 : ℝ≥0∞)) p.2) = S.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext p
    rcases p with ⟨⟨x, ω⟩, γ⟩
    rfl
  rw [heq]
  exact hmeas

/-- The literal killed-segment kernel, including environment as a parameter. -/
def killedSegmentKernel {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) [IsFiniteKernel P] : QuenchedPathLaws d :=
  P.withDensity fun a γ =>
    ({γ : Path d | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R a.1}).indicator
      (fun _ => (1 : ℝ≥0∞)) γ

/-- The joint killed kernel has exactly the already defined killed laws. -/
theorem killedSegmentKernel_apply {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) [IsFiniteKernel P] (a : Vec d × FieldPair d) :
    killedSegmentKernel Δ R i P a = Renewal.killedSegmentLaw Δ R i P a.1 a.2 := by
  rcases a with ⟨x, ω⟩
  rw [killedSegmentKernel,
    Kernel.withDensity_apply _ (measurable_killedSegment_density Δ R i)]
  have hm : Measurable (fun γ : Path d => (x, γ)) :=
    measurable_const.prodMk measurable_id
  have hS₀ : MeasurableSet {p : Vec d × Path d |
      ∀ t : ℝ≥0, t ≤ Δ → p.2 t ∈ couplingRegion i R p.1} :=
    (Renewal.isOpen_killedSegment_event Δ R i).measurableSet
  have hSpre := hS₀.preimage hm
  have hS : MeasurableSet {γ : Path d |
      ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R x} := hSpre
  exact withDensity_indicator_one hS

/-- Killing preserves a uniform finite bound on all joint fibres. -/
instance isFiniteKernel_killedSegmentKernel {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) [IsFiniteKernel P] :
    IsFiniteKernel (killedSegmentKernel Δ R i P) := by
  apply Kernel.isFiniteKernel_withDensity_of_bounded P (B := 1) ENNReal.one_ne_top
  intro a γ
  exact Set.indicator_le_self' (fun _ _ => zero_le) _

/-- A jointly measurable successful kernel using Mathlib's kernel derivative.
The next identity identifies it with the frozen measure-derivative formula. -/
def killedBridgeKernel {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) [IsFiniteKernel P] : QuenchedPathLaws d :=
  (killedSegmentKernel Δ R i P).withDensity fun a γ =>
    (uniformEndpointKernel R i).rnDeriv
      ((killedSegmentKernel Δ R i P).map (fun γ => γ Δ)) a (γ Δ)

/-- The successful-kernel density is jointly measurable. -/
theorem measurable_killedBridge_density {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) [IsFiniteKernel P] :
    Measurable (fun p : (Vec d × FieldPair d) × Path d =>
      (uniformEndpointKernel R i).rnDeriv
        ((killedSegmentKernel Δ R i P).map (fun γ => γ Δ)) p.1 (p.2 Δ)) := by
  exact (Kernel.measurable_rnDeriv _ _).comp
    (measurable_fst.prodMk (((continuous_eval_const Δ).measurable).comp measurable_snd))

/-- The joint successful kernel is fibrewise the actual canonical killed
bridge. The derivative equality holds on each endpoint law, so it pulls back
to each killed path law before taking `withDensity`. -/
theorem killedBridgeKernel_apply {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (hR : 0 < R) (P : QuenchedPathLaws d) [IsFiniteKernel P]
    (a : Vec d × FieldPair d) :
    killedBridgeKernel Δ R i P a = Renewal.killedBridgeMixture Δ R i P a.1 a.2 := by
  haveI := isMarkovKernel_uniformEndpointKernel R i hR
  have hderiv := Kernel.rnDeriv_eq_rnDeriv_measure
    (κ := uniformEndpointKernel R i)
    (η := (killedSegmentKernel Δ R i P).map (fun γ => γ Δ)) (a := a)
  rw [Kernel.map_apply _ (continuous_eval_const Δ).measurable] at hderiv
  have hpull := ae_of_ae_map ((continuous_eval_const Δ).measurable).aemeasurable hderiv
  rw [killedBridgeKernel,
    Kernel.withDensity_apply _ (measurable_killedBridge_density Δ R i P)]
  rw [withDensity_congr_ae hpull, uniformEndpointKernel_apply, killedSegmentKernel_apply]
  rfl

/-- The successful kernel is uniformly finite even before a minorization is
provided: its endpoint measure is bounded by the uniform probability law. -/
theorem isFiniteKernel_killedBridgeKernel {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (hR : 0 < R) (P : QuenchedPathLaws d) [IsFiniteKernel P] :
    IsFiniteKernel (killedBridgeKernel Δ R i P) := by
  constructor
  refine ⟨1, ENNReal.one_lt_top, fun a => ?_⟩
  rw [killedBridgeKernel_apply Δ R i hR]
  haveI : IsProbabilityMeasure (cond (volume : Measure (Vec d)) (endpointBall i R a.1)) :=
    cond_isProbabilityMeasure_of_finite (endpointBall_volume_pos i R hR a.1).ne'
      (endpointBall_volume_ne_top i R hR a.1)
  have hle := map_killedBridgeMixture_endpoint_le_uniform Δ R i P a.1 a.2 Set.univ
  simpa only [Measure.map_apply (continuous_eval_const Δ).measurable MeasurableSet.univ,
    Set.preimage_univ, measure_univ] using hle

/-- Pointwise source minorization makes the jointly measurable canonical
successful kernel Markov, with no arbitrary coupling-selection premise. -/
theorem isMarkovKernel_killedBridgeKernel {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (hδ : 0 < δ) (hR : 0 < R) (P : QuenchedPathLaws d) [IsFiniteKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) :
    IsMarkovKernel (killedBridgeKernel Δ R i P) := by
  constructor
  intro a
  rw [killedBridgeKernel_apply Δ R i hR]
  exact isProbabilityMeasure_killedBridgeMixture P a.2 Δ δ R i hδ hR (hminor a.2) a.1

/-- Joint measurability of the actual failed law follows from its dominated
measure difference, rather than from any selection of conditional laws. -/
theorem measurable_failedKilledBridgeLaw {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (hδ : 0 ≤ δ) (hR : 0 < R) (P : QuenchedPathLaws d) [IsFiniteKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) :
    Measurable (fun a : Vec d × FieldPair d => failedKilledBridgeLaw Δ δ R i P a.1 a.2) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have heq : (fun a : Vec d × FieldPair d => failedKilledBridgeLaw Δ δ R i P a.1 a.2 A) =
      fun a => (ENNReal.ofReal (1 - δ))⁻¹ *
        (P a A - ENNReal.ofReal δ * killedBridgeKernel Δ R i P a A) := by
    funext a
    rcases a with ⟨x, ω⟩
    have hle := smul_killedBridgeMixture_le_pathLaw P ω Δ δ R i hδ (hminor ω) x
    haveI : IsFiniteMeasure (ENNReal.ofReal δ • Renewal.killedBridgeMixture Δ R i P x ω) :=
      isFiniteMeasure_of_le (P (x, ω)) hle
    rw [failedKilledBridgeLaw, Measure.smul_apply, smul_eq_mul,
      Measure.sub_apply hA hle, Measure.smul_apply, smul_eq_mul,
      killedBridgeKernel_apply Δ R i hR]
  rw [heq]
  exact measurable_const.mul ((Kernel.measurable_coe P hA).sub
    (measurable_const.mul (Kernel.measurable_coe (killedBridgeKernel Δ R i P) hA)))

/-- The actual failed branch as a joint kernel. The source minorization is
used only to prove measurability of the dominated measure difference. -/
def failedKilledBridgeKernel {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (hδ : 0 ≤ δ) (hR : 0 < R) (P : QuenchedPathLaws d) [IsFiniteKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) : QuenchedPathLaws d where
  toFun a := failedKilledBridgeLaw Δ δ R i P a.1 a.2
  measurable' := measurable_failedKilledBridgeLaw Δ δ R i hδ hR P hminor

/-- The failure kernel uses exactly the literal source residual measure. -/
theorem failedKilledBridgeKernel_apply {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (hδ : 0 ≤ δ) (hR : 0 < R) (P : QuenchedPathLaws d) [IsFiniteKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) (a : Vec d × FieldPair d) :
    failedKilledBridgeKernel Δ δ R i hδ hR P hminor a =
      failedKilledBridgeLaw Δ δ R i P a.1 a.2 := rfl

/-- Under the source range `0 < delta < 1`, the actual failed joint kernel
is Markov whenever the original path kernel is Markov. -/
theorem isMarkovKernel_failedKilledBridgeKernel {d : ℕ} (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
    (P : QuenchedPathLaws d) [IsMarkovKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) :
    IsMarkovKernel (failedKilledBridgeKernel Δ δ R i hδ₀.le hR P hminor) := by
  constructor
  intro a
  exact isProbabilityMeasure_failedKilledBridgeLaw P a.2 Δ δ R i
    hδ₀ hδ₁ hR (hminor a.2) a.1

end EinsteinFull.Regeneration
