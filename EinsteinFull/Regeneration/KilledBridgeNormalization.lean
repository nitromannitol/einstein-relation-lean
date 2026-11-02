import EinsteinFull.External.Source.GMPSplitCoupling
import EinsteinRelation.Regeneration.OneIntervalBridgeSupport
import EinsteinRelation.Regeneration.EndpointBallVolume
import Mathlib.MeasureTheory.Measure.Sub

/-!
# Normalization of the actual killed bridge

Shen (2003), (2.8)--(2.9), and the one-interval construction used in the
factorization argument of `paper/main.tex`. The literal endpoint-Radon--Nikodym
mixture is a probability measure under the killed-kernel minorization. Its
weighted mass is dominated by the original path law, so the failed branch is
a genuine probability measure and recombines with the successful branch.

These are internal measure-theoretic proofs. No locality, joint-environment
measurability, minorization, or global path/coin construction is assumed as a
new literature input here.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration
open EinsteinFull.External.Source.GMP

/-- Endpoint reweighting recovers the whole target law when it is absolutely
continuous with respect to the endpoint law. -/
theorem map_withDensity_rnDeriv_comp_eq {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (η : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (e : α → β) (he : Measurable e) (hη : η ≪ μ.map e) :
    (μ.withDensity ((η.rnDeriv (μ.map e)) ∘ e)).map e = η := by
  have hm : (μ.withDensity ((η.rnDeriv (μ.map e)) ∘ e)).map e =
      (μ.map e).withDensity (η.rnDeriv (μ.map e)) := by
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply he hs, withDensity_apply _ (he hs),
      withDensity_apply _ hs,
      setLIntegral_map hs (Measure.measurable_rnDeriv _ _) he]
    rfl
  rw [hm, Measure.withDensity_rnDeriv_eq _ _ hη]

/-- An endpoint minorization bounds the corresponding literal reweighted
path law, with precisely the same scalar. -/
theorem smul_withDensity_rnDeriv_comp_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (η : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (e : α → β) (he : Measurable e) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hminor : c • η ≤ μ.map e) :
    c • μ.withDensity ((η.rnDeriv (μ.map e)) ∘ e) ≤ μ := by
  have hbound : ∀ᵐ y ∂μ.map e, c * η.rnDeriv (μ.map e) y ≤ 1 := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hminor,
      Measure.rnDeriv_smul_left_of_ne_top η (μ.map e) hc] with y hy hderiv
    simpa only [hderiv, Pi.smul_apply, smul_eq_mul, Pi.one_apply] using hy
  have hpull := ae_of_ae_map he.aemeasurable hbound
  rw [← withDensity_smul c ((Measure.measurable_rnDeriv _ _).comp he)]
  exact (withDensity_mono hpull).trans_eq withDensity_one

/-- The source minorization is exactly an inequality for the endpoint map of
the actual killed segment, including the source factor `2 delta`. -/
theorem source_minorization_le_killed_endpoint {d : ℕ}
    (P : QuenchedPathLaws d) (ω : FieldPair d) (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d)
    (hminor : HasSourceMinorization (fun z => P (z, ω)) Δ δ R i)
    (x : Vec d) :
    ENNReal.ofReal (2 * δ) •
        ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ => γ Δ) := by
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (continuous_eval_const Δ).measurable hA]
  change ENNReal.ofReal (2 * δ) *
      ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) A ≤
    (P (x, ω)).restrict {γ | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R x}
      ((fun γ : Path d => γ Δ) ⁻¹' A)
  rw [Measure.restrict_apply ((continuous_eval_const Δ).measurable hA)]
  simpa only [Set.preimage, Set.inter_comm, Set.setOf_and] using hminor x A hA

/-- The killed endpoint dominates the target uniform law absolutely
continuously as soon as the minorization scalar is strictly positive. -/
theorem uniform_endpoint_absolutelyContinuous_killed {d : ℕ}
    (P : QuenchedPathLaws d) (ω : FieldPair d) (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ : 0 < δ)
    (hminor : HasSourceMinorization (fun z => P (z, ω)) Δ δ R i)
    (x : Vec d) :
    ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≪
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ => γ Δ) := by
  exact (Measure.absolutelyContinuous_smul
    (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) hδ)).ne').trans
      (Measure.absolutelyContinuous_of_le
        (source_minorization_le_killed_endpoint P ω Δ δ R i hminor x))

/-- The actual canonical successful bridge has exactly the uniform endpoint
law, not merely a submeasure of it. -/
theorem map_killedBridgeMixture_endpoint_eq_uniform {d : ℕ}
    (P : QuenchedPathLaws d) (ω : FieldPair d) (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ : 0 < δ)
    (hminor : HasSourceMinorization (fun z => P (z, ω)) Δ δ R i)
    (x : Vec d) [IsFiniteMeasure (P (x, ω))] :
    (Renewal.killedBridgeMixture Δ R i P x ω).map (fun γ => γ Δ) =
      ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) := by
  haveI : IsFiniteMeasure (Renewal.killedSegmentLaw Δ R i P x ω) := by
    dsimp only [Renewal.killedSegmentLaw]
    infer_instance
  exact map_withDensity_rnDeriv_comp_eq
    (Renewal.killedSegmentLaw Δ R i P x ω) _ _ ((continuous_eval_const Δ).measurable)
    (uniform_endpoint_absolutelyContinuous_killed P ω Δ δ R i hδ hminor x)

/-- The literal successful bridge is normalized; no global split coupling
or selected conditional probability law is needed for this conclusion. -/
theorem isProbabilityMeasure_killedBridgeMixture {d : ℕ}
    (P : QuenchedPathLaws d) (ω : FieldPair d) (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ : 0 < δ) (hR : 0 < R)
    (hminor : HasSourceMinorization (fun z => P (z, ω)) Δ δ R i)
    (x : Vec d) [IsFiniteMeasure (P (x, ω))] :
    IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P x ω) := by
  haveI : IsProbabilityMeasure
      (ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x)) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (endpointBall_volume_pos i R hR x).ne' (endpointBall_volume_ne_top i R hR x)
  constructor
  have hm := congrArg (fun μ : Measure (Vec d) => μ Set.univ)
    (map_killedBridgeMixture_endpoint_eq_uniform P ω Δ δ R i hδ hminor x)
  simpa only [Measure.map_apply ((continuous_eval_const Δ).measurable) MeasurableSet.univ,
    Set.preimage_univ, measure_univ] using hm

/-- The source factor two is retained at the level of path measures: the
weighted canonical bridge is dominated by the killed law. -/
theorem two_smul_killedBridgeMixture_le_killed {d : ℕ}
    (P : QuenchedPathLaws d) (ω : FieldPair d) (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d)
    (hminor : HasSourceMinorization (fun z => P (z, ω)) Δ δ R i)
    (x : Vec d) [IsFiniteMeasure (P (x, ω))] :
    ENNReal.ofReal (2 * δ) • Renewal.killedBridgeMixture Δ R i P x ω ≤
      Renewal.killedSegmentLaw Δ R i P x ω := by
  haveI : IsFiniteMeasure (Renewal.killedSegmentLaw Δ R i P x ω) := by
    dsimp only [Renewal.killedSegmentLaw]
    infer_instance
  exact smul_withDensity_rnDeriv_comp_le
    (Renewal.killedSegmentLaw Δ R i P x ω) _ _ ((continuous_eval_const Δ).measurable) _
    ENNReal.ofReal_ne_top (source_minorization_le_killed_endpoint P ω Δ δ R i hminor x)

/-- The canonical successful bridge stays inside the actual coupling ball on
the whole closed interval, since it is absolutely continuous with respect to
the killed segment. -/
theorem ae_killedBridgeMixture_stays_in_couplingRegion {d : ℕ}
    (P : QuenchedPathLaws d) (ω : FieldPair d) (Δ : ℝ≥0)
    (R : ℝ) (i : Fin d) (x : Vec d) :
    ∀ᵐ γ ∂Renewal.killedBridgeMixture Δ R i P x ω,
      ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R x := by
  have hS : MeasurableSet {γ : Path d |
      ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R x} := by
    have ho := ContinuousMap.isOpen_setOf_mapsTo
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) Δ))
      (isOpen_couplingRegion i R x)
    simpa only [Set.MapsTo, Set.mem_Icc, zero_le, true_and] using ho.measurableSet
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hS)

/-- The success mass can be subtracted from the original path law as a
measure, rather than as a possibly negative set function. -/
theorem smul_killedBridgeMixture_le_pathLaw {d : ℕ}
    (P : QuenchedPathLaws d) (ω : FieldPair d) (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ : 0 ≤ δ)
    (hminor : HasSourceMinorization (fun z => P (z, ω)) Δ δ R i)
    (x : Vec d) [IsFiniteMeasure (P (x, ω))] :
    ENNReal.ofReal δ • Renewal.killedBridgeMixture Δ R i P x ω ≤ P (x, ω) := by
  have hscalar : ENNReal.ofReal δ ≤ ENNReal.ofReal (2 * δ) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hle : ENNReal.ofReal δ • Renewal.killedBridgeMixture Δ R i P x ω ≤
      ENNReal.ofReal (2 * δ) • Renewal.killedBridgeMixture Δ R i P x ω := by
    intro A
    exact mul_le_mul_left hscalar _
  exact (hle.trans (two_smul_killedBridgeMixture_le_killed P ω Δ δ R i hminor x)).trans
    Measure.restrict_le_self

/-- The literal failed branch `(P - delta S)/(1-delta)` of Shen (2.9),
formed from the actual canonical killed bridge. Its positivity and
normalization are proved below from the source minorization. -/
def failedKilledBridgeLaw {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (x : Vec d) (ω : FieldPair d) : Measure (Path d) :=
  (ENNReal.ofReal (1 - δ))⁻¹ •
    (P (x, ω) - ENNReal.ofReal δ • Renewal.killedBridgeMixture Δ R i P x ω)

/-- The actual failed branch is a probability measure, with the precise
source denominator and no coupling-selection hypothesis. -/
theorem isProbabilityMeasure_failedKilledBridgeLaw {d : ℕ}
    (P : QuenchedPathLaws d) (ω : FieldPair d) (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
    (hminor : HasSourceMinorization (fun z => P (z, ω)) Δ δ R i)
    (x : Vec d) [IsProbabilityMeasure (P (x, ω))] :
    IsProbabilityMeasure (failedKilledBridgeLaw Δ δ R i P x ω) := by
  haveI := isProbabilityMeasure_killedBridgeMixture P ω Δ δ R i hδ₀ hR hminor x
  have hle := smul_killedBridgeMixture_le_pathLaw P ω Δ δ R i hδ₀.le hminor x
  haveI : IsFiniteMeasure (ENNReal.ofReal δ • Renewal.killedBridgeMixture Δ R i P x ω) :=
    isFiniteMeasure_of_le (P (x, ω)) hle
  constructor
  rw [failedKilledBridgeLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sub_apply MeasurableSet.univ hle, Measure.smul_apply,
    smul_eq_mul, measure_univ, measure_univ, mul_one,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hδ₀.le]
  simpa only [ENNReal.ofReal_one] using ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.mpr (sub_pos.mpr hδ₁)).ne' ENNReal.ofReal_ne_top

/-- The canonical successful and failed laws recombine to exactly the
original path law with the source Bernoulli weights. -/
theorem killedBridge_split_mixture_eq_pathLaw {d : ℕ}
    (P : QuenchedPathLaws d) (ω : FieldPair d) (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : HasSourceMinorization (fun z => P (z, ω)) Δ δ R i)
    (x : Vec d) [IsProbabilityMeasure (P (x, ω))] :
    ENNReal.ofReal δ • Renewal.killedBridgeMixture Δ R i P x ω +
      ENNReal.ofReal (1 - δ) • failedKilledBridgeLaw Δ δ R i P x ω = P (x, ω) := by
  have hle := smul_killedBridgeMixture_le_pathLaw P ω Δ δ R i hδ₀.le hminor x
  haveI : IsFiniteMeasure (ENNReal.ofReal δ • Renewal.killedBridgeMixture Δ R i P x ω) :=
    isFiniteMeasure_of_le (P (x, ω)) hle
  rw [failedKilledBridgeLaw, smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (sub_pos.mpr hδ₁)).ne'
      ENNReal.ofReal_ne_top, one_smul, add_comm]
  exact Measure.sub_add_cancel_of_le hle

/-- Integrability under the actual path law gives integrability under both
canonical conditional branches. In particular the failed-kernel formula does
not use the zero value assigned to a nonintegrable Bochner integral. -/
theorem integrable_killedBridge_branches {d : ℕ}
    (P : QuenchedPathLaws d) (ω : FieldPair d) (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : HasSourceMinorization (fun z => P (z, ω)) Δ δ R i)
    (x : Vec d) [IsProbabilityMeasure (P (x, ω))]
    (F : Path d → ℝ) (hF : Integrable F (P (x, ω))) :
    Integrable F (Renewal.killedBridgeMixture Δ R i P x ω) ∧
      Integrable F (failedKilledBridgeLaw Δ δ R i P x ω) := by
  rw [← killedBridge_split_mixture_eq_pathLaw P ω Δ δ R i hδ₀ hδ₁ hminor x,
    integrable_add_measure] at hF
  exact ⟨(integrable_smul_measure (ENNReal.ofReal_pos.mpr hδ₀).ne'
      ENNReal.ofReal_ne_top).mp hF.1,
    (integrable_smul_measure (ENNReal.ofReal_pos.mpr (sub_pos.mpr hδ₁)).ne'
      ENNReal.ofReal_ne_top).mp hF.2⟩

/-- Shen (2.9) for every integrable test of the actual path law, with the
literal successful and failed measures and the exact normalization. -/
theorem integral_failedKilledBridgeLaw {d : ℕ}
    (P : QuenchedPathLaws d) (ω : FieldPair d) (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hminor : HasSourceMinorization (fun z => P (z, ω)) Δ δ R i)
    (x : Vec d) [IsProbabilityMeasure (P (x, ω))]
    (F : Path d → ℝ) (hF : Integrable F (P (x, ω))) :
    (∫ γ, F γ ∂failedKilledBridgeLaw Δ δ R i P x ω) =
      ((∫ γ, F γ ∂P (x, ω)) -
        δ * ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P x ω) / (1 - δ) := by
  have hi := hF
  rw [← killedBridge_split_mixture_eq_pathLaw P ω Δ δ R i hδ₀ hδ₁ hminor x,
    integrable_add_measure] at hi
  have heq := congrArg (fun μ : Measure (Path d) => ∫ γ, F γ ∂μ)
    (killedBridge_split_mixture_eq_pathLaw P ω Δ δ R i hδ₀ hδ₁ hminor x)
  rw [integral_add_measure hi.1 hi.2, integral_smul_measure,
    integral_smul_measure, ENNReal.toReal_ofReal hδ₀.le,
    ENNReal.toReal_ofReal (sub_pos.mpr hδ₁).le, smul_eq_mul, smul_eq_mul] at heq
  apply (eq_div_iff (sub_pos.mpr hδ₁).ne').mpr
  linarith only [heq]

end EinsteinFull.Regeneration
