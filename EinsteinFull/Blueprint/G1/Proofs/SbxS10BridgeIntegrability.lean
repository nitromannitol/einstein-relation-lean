import EinsteinFull.Regeneration.KilledBridgeKernel
import EinsteinFull.Blueprint.G1.Proofs.SbxS4SplitResidual
import EinsteinRelation.Diffusion.GMPFamilyAPI
import EinsteinFull.Work.W1.GMPFullPastRestartSupport
import EinsteinRelation.Probability.FiniteHistoryMeasurability
import EinsteinRelation.Probability.PathMaps
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Tactic.Linter.Lint

/-!
# Joint split kernels and bounded tests for the literal one-interval bridge

The endpoint domination bounds the RN bridge mass without minorization.
The finite probability part supplies a joint measurable kernel, with explicit
identification with the original law on its measurable probability carrier.
The precise endpoint minorization supplies successful and residual probability
kernels, with literal first-coin fibres and bounded-test formulas. A measurable
conull environment carrier preserves all-start and spatial-product a.e. fibres.
The countable endpoint/coin law uses these literal transitions. A measurable
concatenation preserves matching segments and finite stopped histories.
No process existence assertion or original-law path-marginal identification is assumed here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinFull.SbxS10BridgeIntegrability
open EinsteinRelation EinsteinRelation.Regeneration

/-- Endpoint domination bounds the mass of the actual bridge, whether or
not the uniform endpoint law is absolutely continuous with respect to it. -/
theorem killedBridgeMixture_mass_le_one {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (x : Vec d) (ω : FieldPair d) :
    Renewal.killedBridgeMixture Δ R i P x ω Set.univ ≤ 1 := by
  have : IsProbabilityMeasure
      (cond (volume : Measure (Vec d)) (endpointBall i R x)) :=
    cond_isProbabilityMeasure_of_finite (endpointBall_volume_pos i R hR x).ne'
      (endpointBall_volume_ne_top i R hR x)
  have h := map_killedBridgeMixture_endpoint_le_uniform Δ R i P x ω Set.univ
  simpa only [Measure.map_apply (continuous_eval_const Δ).measurable MeasurableSet.univ,
    Set.preimage_univ, measure_univ] using h

/-- Every actual bridge fibre is finite, including exceptional source fibres. -/
theorem isFiniteMeasure_killedBridgeMixture {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (x : Vec d) (ω : FieldPair d) :
    IsFiniteMeasure (Renewal.killedBridgeMixture Δ R i P x ω) :=
  ⟨(killedBridgeMixture_mass_le_one Δ R i hR P x ω).trans_lt ENNReal.one_lt_top⟩

/-- A bounded measurable real test is integrable under each literal bridge. -/
theorem integrable_killedBridgeMixture {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (x : Vec d) (ω : FieldPair d)
    (F : Path d → ℝ) (hF : Measurable F) (hb : BoundedRealTest F) :
    Integrable F (Renewal.killedBridgeMixture Δ R i P x ω) := by
  have := isFiniteMeasure_killedBridgeMixture Δ R i hR P x ω
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hF.aestronglyMeasurable C
    (ae_of_all _ fun γ => (Real.norm_eq_abs _).symm ▸ hC γ)

/-- Quantitative expectation bound for the actual RN bridge. Its mass is
at most one; neither endpoint AC nor a source minorization is required. -/
theorem abs_integral_killedBridgeMixture_le {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (x : Vec d) (ω : FieldPair d)
    (F : Path d → ℝ) (C : ℝ) (hC : 0 ≤ C) (hFC : ∀ γ, |F γ| ≤ C) :
    |∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P x ω| ≤ C := by
  have := isFiniteMeasure_killedBridgeMixture Δ R i hR P x ω
  have hm : (Renewal.killedBridgeMixture Δ R i P x ω).real Set.univ ≤ 1 := by
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
      (killedBridgeMixture_mass_le_one Δ R i hR P x ω)
  have hb := norm_integral_le_of_norm_le_const
    (μ := Renewal.killedBridgeMixture Δ R i P x ω)
    (ae_of_all _ fun γ => (Real.norm_eq_abs _).symm ▸ hFC γ)
  exact (Real.norm_eq_abs _ ▸ hb).trans ((mul_le_mul_of_nonneg_left hm hC).trans_eq
    (mul_one C))

/-- Probability-part normalization leaves the entire literal RN formula
unchanged at each probability fibre, not just its integrals. -/
theorem killedBridgeMixture_probabilityPart {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (x : Vec d) (ω : FieldPair d) [IsProbabilityMeasure (P (x, ω))] :
    Renewal.killedBridgeMixture Δ R i (Probability.probabilityPart P) x ω =
      Renewal.killedBridgeMixture Δ R i P x ω := by
  simp only [Renewal.killedBridgeMixture, Renewal.killedSegmentLaw,
    Probability.probabilityPart_eq_of_isProbabilityMeasure]

/-- The normalized expectation is jointly measurable on all parameters.
Only its probability fibres will be identified with the original law. -/
theorem measurable_killedBridge_expectation_probabilityPart {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (F : Path d → ℝ) (hF : Measurable F) :
    Measurable (fun a : Vec d × FieldPair d =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i
        (Probability.probabilityPart P) a.1 a.2) := by
  have hm := (hF.stronglyMeasurable.integral_kernel
    (κ := Regeneration.killedBridgeKernel Δ R i (Probability.probabilityPart P))).measurable
  simpa only [Regeneration.killedBridgeKernel_apply Δ R i hR] using hm

/-- On the measurable carrier of genuine probability fibres the original
bridge expectation is jointly measurable, with its original RN derivative. -/
theorem measurable_killedBridge_expectation_good {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (F : Path d → ℝ) (hF : Measurable F) :
    Measurable (fun a : {a : Vec d × FieldPair d // P a Set.univ = 1} =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P a.1.1 a.1.2) := by
  have hm : Measurable (fun a : {a : Vec d × FieldPair d // P a Set.univ = 1} =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i
        (Probability.probabilityPart P) a.1.1 a.1.2) :=
    (measurable_killedBridge_expectation_probabilityPart Δ R i hR P F hF).comp
      measurable_subtype_coe
  convert hm using 1
  funext a
  have : IsProbabilityMeasure (P a.1) := ⟨a.2⟩
  rw [killedBridgeMixture_probabilityPart]

/-- The good carrier is measurable in the original parameter space. -/
theorem measurableSet_probability_fibres {d : ℕ} (P : QuenchedPathLaws d) :
    MeasurableSet {a : Vec d × FieldPair d | P a Set.univ = 1} :=
  (P.measurable_coe MeasurableSet.univ) (measurableSet_singleton 1)

/-- An all-start a.e. probability statement has a measurable conull
environment carrier on which every original path law is a probability. -/
theorem exists_measurable_probability_environments {d : ℕ}
    (μ : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (hP : ∀ᵐ ω ∂μ, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω))) :
    ∃ G : Set (FieldPair d), MeasurableSet G ∧ (∀ᵐ ω ∂μ, ω ∈ G) ∧
      ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)) := by
  classical
  have hbad : μ {ω | ¬ ∀ x : Vec d, IsProbabilityMeasure (P (x, ω))} = 0 := hP
  obtain ⟨N, hsub, hN, hnull⟩ := exists_measurable_superset_of_null hbad
  refine ⟨Nᶜ, hN.compl, ?_, ?_⟩
  · show μ {ω | ω ∉ Nᶜ} = 0
    simpa using hnull
  · intro ω hω
    by_contra h
    exact hω (hsub h)

/-- The literal bridge expectation is jointly measurable in position and
environment on any carrier of all-start probability environments. -/
theorem measurable_killedBridge_expectation_on_environments {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (F : Path d → ℝ) (hF : Measurable F) :
    Measurable (fun a : Vec d × G =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P a.1 a.2.1) := by
  have hm : Measurable (fun a : Vec d × G =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i
        (Probability.probabilityPart P) a.1 a.2.1) :=
    (measurable_killedBridge_expectation_probabilityPart Δ R i hR P F hF).comp
      (f := fun a : Vec d × G => (a.1, a.2.1))
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  convert hm using 1
  funext a
  have := hP a.2.1 a.2.2 a.1
  rw [killedBridgeMixture_probabilityPart]

/-- All-start probability in a fixed environment suffices for spatial
measurability of the original bridge expectation. -/
theorem measurable_killedBridge_expectation_of_probability {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (ω : FieldPair d)
    (hP : ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (F : Path d → ℝ) (hF : Measurable F) :
    Measurable (fun x : Vec d =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P x ω) := by
  have hm : Measurable (fun x : Vec d =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i
        (Probability.probabilityPart P) x ω) :=
    (measurable_killedBridge_expectation_probabilityPart Δ R i hR P F hF).comp
      (f := fun x : Vec d => (x, ω)) (measurable_id.prodMk measurable_const)
  convert hm using 1
  funext x
  have := hP x
  rw [killedBridgeMixture_probabilityPart]

/-- Bounded tests remain bounded under pointwise multiplication. -/
theorem boundedRealTest_mul {α : Type*} (f g : α → ℝ)
    (hf : BoundedRealTest f) (hg : BoundedRealTest g) :
    BoundedRealTest (fun x => f x * g x) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨max C 0 * max D 0, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hC x).trans (le_max_left _ _))
    ((hD x).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)

/-- Bounded measurable tests are integrable for any finite outer law. -/
theorem integrable_boundedRealTest {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    (hf : Measurable f) (hb : BoundedRealTest f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun x => (Real.norm_eq_abs _).symm ▸ hC x)

/-- Both literal bit branches are integrable, for every grid index. -/
theorem integrable_oneInterval_bit {d : ℕ}
    (μ : Measure (CoupledSample d)) [IsFiniteMeasure μ]
    (Δ : ℝ≥0) (n : ℕ) (b : Bool)
    (H : CoupledSample d → ℝ) (F : Path d → ℝ)
    (hH : Measurable H) (hbH : BoundedRealTest H)
    (hF : Measurable F) (hbF : BoundedRealTest F) :
    Integrable (fun z : CoupledSample d =>
      H z * (if z.2 n = b then (1 : ℝ) else 0) *
        F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) μ := by
  have hcoord : Measurable (fun z : CoupledSample d => z.2 n) :=
    (measurable_pi_apply (X := fun _ : ℕ => Bool) n).comp measurable_snd
  have hset : MeasurableSet {z : CoupledSample d | z.2 n = b} :=
    hcoord (measurableSet_singleton b)
  have hbit : Measurable (fun z : CoupledSample d =>
      if z.2 n = b then (1 : ℝ) else 0) :=
    Measurable.ite hset measurable_const measurable_const
  have hbbit : BoundedRealTest (fun z : CoupledSample d =>
      if z.2 n = b then (1 : ℝ) else 0) := by
    refine ⟨1, fun z => ?_⟩
    change |(if z.2 n = b then (1 : ℝ) else 0)| ≤ 1
    split_ifs <;> norm_num
  have hshift : Measurable (fun z : CoupledSample d =>
      pathTimeShift z.1 ((n : ℝ≥0) * Δ)) :=
    Probability.continuous_path_time_shift.measurable.comp
      (measurable_const.prodMk measurable_fst)
  have hbshift : BoundedRealTest (fun z : CoupledSample d =>
      F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) := by
    obtain ⟨C, hC⟩ := hbF
    exact ⟨C, fun z => hC _⟩
  exact integrable_boundedRealTest μ _ ((hH.mul hbit).mul (hF.comp hshift))
    (boundedRealTest_mul _ _ (boundedRealTest_mul _ _ hbH hbbit) hbshift)

/-- The bridge expectation weighted by a bounded history is integrable
under the original finite outer law. -/
theorem integrable_oneInterval_bridge {d : ℕ}
    (μ : Measure (CoupledSample d)) [IsFiniteMeasure μ]
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hR : 0 < R) (n : ℕ)
    (P : QuenchedPathLaws d) (ω : FieldPair d)
    (hP : ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (H : CoupledSample d → ℝ) (F : Path d → ℝ)
    (hH : Measurable H) (hbH : BoundedRealTest H)
    (hF : Measurable F) (hbF : BoundedRealTest F) :
    Integrable (fun z : CoupledSample d => H z *
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
        (z.1 ((n : ℝ≥0) * Δ)) ω)) μ := by
  have hm : Measurable (fun z : CoupledSample d =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
        (z.1 ((n : ℝ≥0) * Δ)) ω) :=
    (measurable_killedBridge_expectation_of_probability Δ R i hR P ω hP F hF).comp
      ((continuous_eval_const ((n : ℝ≥0) * Δ)).measurable.comp measurable_fst)
  have hb : BoundedRealTest (fun z : CoupledSample d =>
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
        (z.1 ((n : ℝ≥0) * Δ)) ω) := by
    obtain ⟨C, hC⟩ := hbF
    exact ⟨max C 0, fun z => abs_integral_killedBridgeMixture_le Δ R i hR P _ ω F
      (max C 0) (le_max_right _ _) (fun γ => (hC γ).trans (le_max_left _ _))⟩
  exact integrable_boundedRealTest μ _ (hH.mul hm) (boundedRealTest_mul _ _ hbH hb)

/-- The unconditioned path expectation has its literal outer integrability. -/
theorem integrable_oneInterval_path {d : ℕ}
    (μ : Measure (CoupledSample d)) [IsFiniteMeasure μ]
    (Δ : ℝ≥0) (n : ℕ) (P : QuenchedPathLaws d) (ω : FieldPair d)
    (hP : ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (H : CoupledSample d → ℝ) (F : Path d → ℝ)
    (hH : Measurable H) (hbH : BoundedRealTest H)
    (hF : Measurable F) (hbF : BoundedRealTest F) :
    Integrable (fun z : CoupledSample d =>
      H z * (∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), ω))) μ := by
  have hm : Measurable (fun z : CoupledSample d =>
      ∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), ω)) :=
    (hF.stronglyMeasurable.integral_kernel (κ := P)).measurable.comp
      (((continuous_eval_const ((n : ℝ≥0) * Δ)).measurable.comp measurable_fst).prodMk
        measurable_const)
  have hb : BoundedRealTest (fun z : CoupledSample d =>
      ∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), ω)) := by
    obtain ⟨C, hC⟩ := hbF
    refine ⟨C, fun z => ?_⟩
    have := hP (z.1 ((n : ℝ≥0) * Δ))
    have hb : ‖∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), ω)‖ ≤
        C * (P (z.1 ((n : ℝ≥0) * Δ), ω)).real Set.univ :=
      norm_integral_le_of_norm_le_const
        (ae_of_all _ fun γ => (Real.norm_eq_abs _).symm ▸ hC γ)
    rw [Real.norm_eq_abs, probReal_univ, mul_one] at hb
    exact hb
  exact integrable_boundedRealTest μ _ (hH.mul hm) (boundedRealTest_mul _ _ hbH hb)

/-- The residual expression is integrable for every signed real scalar.
This proves the fourth source clause without assuming a split identity. -/
theorem integrable_oneInterval_residual {d : ℕ}
    (μ : Measure (CoupledSample d)) [IsFiniteMeasure μ]
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (hR : 0 < R) (n : ℕ)
    (P : QuenchedPathLaws d) (ω : FieldPair d)
    (hP : ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (H : CoupledSample d → ℝ) (F : Path d → ℝ)
    (hH : Measurable H) (hbH : BoundedRealTest H)
    (hF : Measurable F) (hbF : BoundedRealTest F) :
    Integrable (fun z : CoupledSample d => H z *
      ((∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), ω)) -
        δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
          (z.1 ((n : ℝ≥0) * Δ)) ω))) μ := by
  have hp := integrable_oneInterval_path μ Δ n P ω hP H F hH hbH hF hbF
  have hb := integrable_oneInterval_bridge μ Δ R i hR n P ω hP H F hH hbH hF hbF
  convert hp.sub (hb.const_mul δ) using 1
  funext z
  simp only [Pi.sub_apply]
  ring

/-- All five integrability clauses of `OneIntervalKernelAt`, proved
independently of either one-interval identity, on the original source laws. -/
theorem oneInterval_integrabilities_of_probability {d : ℕ}
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (xω : Vec d × FieldPair d) [IsProbabilityMeasure (K xω)]
    (hP : ∀ x : Vec d, IsProbabilityMeasure (P (x, xω.2)))
    (n : ℕ) (H : CoupledSample d → ℝ) (F : Path d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H)
    (hbH : BoundedRealTest H) (hF : Measurable F) (hbF : BoundedRealTest F) :
    Integrable (fun z : CoupledSample d =>
        H z * (if z.2 n = true then (1 : ℝ) else 0) *
          F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) (K xω) ∧
      Integrable (fun z : CoupledSample d => H z *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
          (z.1 ((n : ℝ≥0) * Δ)) xω.2)) (K xω) ∧
      Integrable (fun z : CoupledSample d =>
        H z * (if z.2 n = true then (0 : ℝ) else 1) *
          F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) (K xω) ∧
      Integrable (fun z : CoupledSample d => H z *
        ((∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), xω.2)) -
          δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
            (z.1 ((n : ℝ≥0) * Δ)) xω.2))) (K xω) ∧
      Integrable (fun z : CoupledSample d =>
        H z * (∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), xω.2))) (K xω) := by
  have hHm := hH.mono (Probability.finiteHistorySigma_le Δ n) le_rfl
  refine ⟨integrable_oneInterval_bit (K xω) Δ n true H F hHm hbH hF hbF,
    integrable_oneInterval_bridge (K xω) Δ R i hR n P xω.2 hP H F hHm hbH hF hbF,
    ?_, integrable_oneInterval_residual (K xω) Δ δ R i hR n P xω.2 hP H F hHm hbH hF hbF,
    integrable_oneInterval_path (K xω) Δ n P xω.2 hP H F hHm hbH hF hbF⟩
  have heq : (fun z : CoupledSample d =>
      H z * (if z.2 n = true then (0 : ℝ) else 1) *
        F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) =
      (fun z : CoupledSample d =>
        H z * (if z.2 n = false then (1 : ℝ) else 0) *
          F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) := by
    funext z
    cases z.2 n <;> rfl
  rw [heq]
  exact integrable_oneInterval_bit (K xω) Δ n false H F hHm hbH hF hbF

/-- The five literal source integrabilities hold at the origin in a.e.
GMP environment, for all grid indices and bounded tests simultaneously. -/
theorem ae_oneInterval_integrabilities_origin
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
    (hK : HasProbabilityLaws Q.measure K)
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (hR : 0 < R) :
    ∀ᵐ ω ∂Q.measure, ∀ (n : ℕ) (H : CoupledSample d → ℝ) (F : Path d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H →
      BoundedRealTest H → Measurable F → BoundedRealTest F →
      Integrable (fun z : CoupledSample d =>
        H z * (if z.2 n = true then (1 : ℝ) else 0) *
          F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) (K (0, ω)) ∧
      Integrable (fun z : CoupledSample d => H z *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
          (z.1 ((n : ℝ≥0) * Δ)) ω)) (K (0, ω)) ∧
      Integrable (fun z : CoupledSample d =>
        H z * (if z.2 n = true then (0 : ℝ) else 1) *
          F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) (K (0, ω)) ∧
      Integrable (fun z : CoupledSample d => H z *
        ((∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), ω)) -
          δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
            (z.1 ((n : ℝ≥0) * Δ)) ω))) (K (0, ω)) ∧
      Integrable (fun z : CoupledSample d =>
        H z * (∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), ω))) (K (0, ω)) := by
  filter_upwards [isProbabilityMeasure_of_isGMPReducedKernel hd hΛ₀ Q lam h0 h1 P hP,
    hK.1] with ω hp hk
  have := hk
  intro n H F hH hbH hF hbF
  exact oneInterval_integrabilities_of_probability Δ δ R i hR P K (0, ω)
    hp n H F hH hbH hF hbF

/-- The spatial source qualifier is product-a.e.; probability normalization
is used only on identified good fibres and leaves every displayed integrand literal. -/
theorem ae_oneInterval_integrabilities_product
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
    (hK : HasProbabilityLaws Q.measure K)
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (hR : 0 < R) :
    ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q.measure), ∀ (n : ℕ) (H : CoupledSample d → ℝ) (F : Path d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H →
      BoundedRealTest H → Measurable F → BoundedRealTest F →
      Integrable (fun z : CoupledSample d =>
        H z * (if z.2 n = true then (1 : ℝ) else 0) *
          F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) (K xω) ∧
      Integrable (fun z : CoupledSample d => H z *
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
          (z.1 ((n : ℝ≥0) * Δ)) xω.2)) (K xω) ∧
      Integrable (fun z : CoupledSample d =>
        H z * (if z.2 n = true then (0 : ℝ) else 1) *
          F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) (K xω) ∧
      Integrable (fun z : CoupledSample d => H z *
        ((∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), xω.2)) -
          δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P
            (z.1 ((n : ℝ≥0) * Δ)) xω.2))) (K xω) ∧
      Integrable (fun z : CoupledSample d =>
        H z * (∫ γ, F γ ∂P (z.1 ((n : ℝ≥0) * Δ), xω.2))) (K xω) := by
  have hp := isProbabilityMeasure_of_isGMPReducedKernel hd hΛ₀ Q lam h0 h1 P hP
  have hpp : ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q.measure),
      ∀ x : Vec d, IsProbabilityMeasure (P (x, xω.2)) :=
    Measure.quasiMeasurePreserving_snd.ae hp
  filter_upwards [hpp, hK.2] with xω hx hk
  have := hk
  intro n H F hH hbH hF hbF
  exact oneInterval_integrabilities_of_probability Δ δ R i hR P K xω
    hx n H F hH hbH hF hbF

/-- Restrict only the parameters: the path law itself remains the original law. -/
def pathKernelOnEnvironments {d : ℕ} (P : QuenchedPathLaws d)
    (G : Set (FieldPair d)) : Kernel (Vec d × G) (Path d) :=
  P.comap (fun a => (a.1, a.2.1))
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

/-- Literal identification of the restricted path law. -/
theorem pathKernelOnEnvironments_apply {d : ℕ} (P : QuenchedPathLaws d)
    (G : Set (FieldPair d)) (a : Vec d × G) :
    pathKernelOnEnvironments P G a = P (a.1, a.2.1) := rfl

/-- All-start probability on the carrier gives a genuine Markov kernel. -/
theorem isMarkovKernel_pathKernelOnEnvironments {d : ℕ} (P : QuenchedPathLaws d)
    (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω))) :
    IsMarkovKernel (pathKernelOnEnvironments P G) :=
  ⟨fun a => hP a.2.1 a.2.2 a.1⟩

/-- Joint killed-segment kernel on the carrier. The next theorem identifies
its fibres with restrictions of the original source law. -/
def killedSegmentKernelOnEnvironments {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d)) : Kernel (Vec d × G) (Path d) :=
  (Regeneration.killedSegmentKernel Δ R i (Probability.probabilityPart P)).comap
    (fun a => (a.1, a.2.1))
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

/-- Killing and carrier restriction preserve the literal original measure. -/
theorem killedSegmentKernelOnEnvironments_apply {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω))) (a : Vec d × G) :
    killedSegmentKernelOnEnvironments Δ R i P G a =
      Renewal.killedSegmentLaw Δ R i P a.1 a.2.1 := by
  have := hP a.2.1 a.2.2 a.1
  rw [killedSegmentKernelOnEnvironments, Kernel.comap_apply,
    Regeneration.killedSegmentKernel_apply]
  simp only [Renewal.killedSegmentLaw,
    Probability.probabilityPart_eq_of_isProbabilityMeasure]

/-- The killed endpoint law, jointly measurable in position and environment. -/
def killedEndpointKernelOnEnvironments {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d)) : Kernel (Vec d × G) (Vec d) :=
  (killedSegmentKernelOnEnvironments Δ R i P G).map (fun γ => γ Δ)

/-- The endpoint pushforward is the actual killed endpoint measure. -/
theorem killedEndpointKernelOnEnvironments_apply {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω))) (a : Vec d × G) :
    killedEndpointKernelOnEnvironments Δ R i P G a =
      (Renewal.killedSegmentLaw Δ R i P a.1 a.2.1).map (fun γ : Path d => γ Δ) := by
  rw [killedEndpointKernelOnEnvironments, Kernel.map_apply _
    (continuous_eval_const Δ).measurable, killedSegmentKernelOnEnvironments_apply Δ R i P G hP]

/-- Joint successful bridge on the carrier, before any minorization is supplied. -/
def bridgeKernelOnEnvironments {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d)) : Kernel (Vec d × G) (Path d) :=
  (Regeneration.killedBridgeKernel Δ R i (Probability.probabilityPart P)).comap
    (fun a => (a.1, a.2.1))
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

/-- The joint bridge uses the exact measure derivative of the original law
on every carrier fibre, rather than merely agreeing on bounded tests. -/
theorem bridgeKernelOnEnvironments_apply {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω))) (a : Vec d × G) :
    bridgeKernelOnEnvironments Δ R i P G a =
      Renewal.killedBridgeMixture Δ R i P a.1 a.2.1 := by
  have := hP a.2.1 a.2.2 a.1
  rw [bridgeKernelOnEnvironments, Kernel.comap_apply,
    Regeneration.killedBridgeKernel_apply Δ R i hR, killedBridgeMixture_probabilityPart]

/-- Uniform bridge finiteness holds without the source minorization. -/
theorem isFiniteKernel_bridgeKernelOnEnvironments {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d)) : IsFiniteKernel (bridgeKernelOnEnvironments Δ R i P G) := by
  have := Regeneration.isFiniteKernel_killedBridgeKernel Δ R i hR
    (Probability.probabilityPart P)
  unfold bridgeKernelOnEnvironments
  infer_instance

/-- Parameter-dependent bridge tests have a jointly measurable expectation. -/
theorem measurable_bridgeKernelOnEnvironments_integral {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hR : 0 < R) (P : QuenchedPathLaws d)
    (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (F : (Vec d × G) × Path d → ℝ) (hF : Measurable F) :
    Measurable (fun a : Vec d × G =>
      ∫ γ, F (a, γ) ∂Renewal.killedBridgeMixture Δ R i P a.1 a.2.1) := by
  have := isFiniteKernel_bridgeKernelOnEnvironments Δ R i hR P G
  have hm := hF.stronglyMeasurable.integral_kernel_prod_right
    (f := fun a γ => F (a, γ))
    (κ := bridgeKernelOnEnvironments Δ R i P G)
  simpa only [Function.uncurry, bridgeKernelOnEnvironments_apply Δ R i hR P G hP]
    using hm.measurable

section Residual
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A dominated difference of joint kernels gives the actual normalized
residual kernel; subtraction is evaluated only under its domination proof. -/
def splitResidualKernel (δ : ℝ) (P B : Kernel α β) [IsFiniteKernel B]
    (hdom : ∀ a, ENNReal.ofReal δ • B a ≤ P a) : Kernel α β where
  toFun a := Blueprint.sbxS4SplitResidual δ (P a) (B a)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Blueprint.sbxS4_splitResidual_apply δ _ _ (hdom _) s hs]
    exact measurable_const.mul ((P.measurable_coe hs).sub
      (measurable_const.mul (B.measurable_coe hs)))

/-- Literal normalized measure subtraction on every parameter fibre. -/
theorem splitResidualKernel_apply (δ : ℝ) (P B : Kernel α β) [IsFiniteKernel B]
    (hdom : ∀ a, ENNReal.ofReal δ • B a ≤ P a) (a : α) :
    splitResidualKernel δ P B hdom a = Blueprint.sbxS4SplitResidual δ (P a) (B a) := rfl

/-- Probability of the residual is proved fibrewise from the actual laws. -/
theorem isMarkovKernel_splitResidualKernel (δ : ℝ) (P B : Kernel α β)
    [IsMarkovKernel P] [IsMarkovKernel B]
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (hdom : ∀ a, ENNReal.ofReal δ • B a ≤ P a) :
    IsMarkovKernel (splitResidualKernel δ P B hdom) :=
  ⟨fun a => Blueprint.sbxS4_splitResidual_isProbabilityMeasure δ (P a) (B a)
    hδ₀ hδ₁ (hdom a)⟩

/-- The delta-weighted mixture recovers the original kernel fibre exactly. -/
theorem splitResidualKernel_recovery (δ : ℝ) (P B : Kernel α β) [IsFiniteKernel B]
    (hδ : δ < 1) (hdom : ∀ a, ENNReal.ofReal δ • B a ≤ P a) (a : α) :
    ENNReal.ofReal δ • B a +
      ENNReal.ofReal (1 - δ) • splitResidualKernel δ P B hdom a = P a :=
  Blueprint.sbxS4_splitResidual_recovery δ (P a) (B a) hδ (hdom a)

/-- The first-coin law is jointly measurable whenever the successful branch
is joint and dominated. The actual normalized residual supplies the false branch. -/
def firstCoinKernel (δ : ℝ) (P B : Kernel α β) [IsFiniteKernel B]
    (hdom : ∀ a, ENNReal.ofReal δ • B a ≤ P a) : Kernel α (β × Bool) where
  toFun a := Blueprint.sbxS4FirstCoinLaw δ (P a) (B a)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have ht : Measurable (fun x : β => (x, true)) :=
      measurable_id.prodMk measurable_const
    have hf : Measurable (fun x : β => (x, false)) :=
      measurable_id.prodMk measurable_const
    have hm₁ := (B.map (fun x => (x, true))).measurable_coe hs
    have hm₀ := ((splitResidualKernel δ P B hdom).map
      (fun x => (x, false))).measurable_coe hs
    simp only [Kernel.map_apply _ ht] at hm₁
    simp only [Kernel.map_apply _ hf, splitResidualKernel_apply] at hm₀
    exact (hm₁.const_mul (ENNReal.ofReal δ)).add
      (hm₀.const_mul (ENNReal.ofReal (1 - δ)))

/-- Fibrewise equality to the already normalized first-coin construction. -/
theorem firstCoinKernel_apply (δ : ℝ) (P B : Kernel α β) [IsFiniteKernel B]
    (hdom : ∀ a, ENNReal.ofReal δ • B a ≤ P a) (a : α) :
    firstCoinKernel δ P B hdom a = Blueprint.sbxS4FirstCoinLaw δ (P a) (B a) := rfl

/-- The jointly measurable split step is a probability kernel. -/
theorem isMarkovKernel_firstCoinKernel (δ : ℝ) (P B : Kernel α β)
    [IsMarkovKernel P] [IsFiniteKernel B]
    (hδ : δ < 1) (hdom : ∀ a, ENNReal.ofReal δ • B a ≤ P a) :
    IsMarkovKernel (firstCoinKernel δ P B hdom) :=
  ⟨fun a => Blueprint.sbxS4_firstCoinLaw_isProbabilityMeasure δ (P a) (B a) hδ (hdom a)⟩

/-- The original path marginal is recovered without modifying any fibre. -/
theorem map_firstCoinKernel_fst (δ : ℝ) (P B : Kernel α β) [IsFiniteKernel B]
    (hδ : δ < 1) (hdom : ∀ a, ENNReal.ofReal δ • B a ≤ P a) (a : α) :
    (firstCoinKernel δ P B hdom a).map Prod.fst = P a :=
  Blueprint.sbxS4_firstCoinLaw_map_fst δ (P a) (B a) hδ (hdom a)

/-- Joint parameter measurability of bounded-test expectations, allowing
observations to depend on the starting point and environment as well. -/
theorem measurable_firstCoinKernel_integral (δ : ℝ) (P B : Kernel α β)
    [IsMarkovKernel P] [IsFiniteKernel B]
    (hδ : δ < 1) (hdom : ∀ a, ENNReal.ofReal δ • B a ≤ P a)
    (F : α × (β × Bool) → ℝ) (hF : Measurable F) :
    Measurable (fun a => ∫ q, F (a, q) ∂firstCoinKernel δ P B hdom a) := by
  have := isMarkovKernel_firstCoinKernel δ P B hδ hdom
  exact (hF.stronglyMeasurable.integral_kernel_prod_right
    (f := fun a q => F (a, q)) (κ := firstCoinKernel δ P B hdom)).measurable

/-- Both first-coin bounded-test formulas have integrable left-hand sides.
The false branch is the actual normalized residual, not an abstract second law. -/
theorem firstCoinKernel_integral_bit (δ : ℝ) (P B : Kernel α β)
    [IsMarkovKernel P] [IsFiniteKernel B]
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (hdom : ∀ a, ENNReal.ofReal δ • B a ≤ P a)
    (a : α) (b : Bool) (F : β → ℝ) (hF : Measurable F) (hb : BoundedRealTest F) :
    Integrable (fun q : β × Bool => (if q.2 = b then (1 : ℝ) else 0) * F q.1)
      (firstCoinKernel δ P B hdom a) ∧
    (∫ q, (if q.2 = b then (1 : ℝ) else 0) * F q.1 ∂firstCoinKernel δ P B hdom a) =
      if b then δ * (∫ x, F x ∂B a)
      else (1 - δ) * (∫ x, F x ∂splitResidualKernel δ P B hdom a) := by
  classical
  have heq : (fun q : β × Bool => (if q.2 = b then (1 : ℝ) else 0) * F q.1) =
      {q : β × Bool | q.2 = b}.indicator (fun q => F q.1) := by
    funext q
    by_cases hq : q.2 = b <;> simp [hq]
  have hbounded : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C := by
    simpa only [BoundedRealTest, Real.norm_eq_abs] using hb
  have h := Blueprint.sbxS4_firstCoinLaw_integral_branch δ (P a) (B a)
    hδ₀ hδ₁ (hdom a) F hF.stronglyMeasurable hbounded b
  simpa only [heq, firstCoinKernel_apply, splitResidualKernel_apply, smul_eq_mul] using h

end Residual

section CarrierSplit
variable {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
  (P : QuenchedPathLaws d) (G : Set (FieldPair d))
  (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
  (hminor : ∀ ω ∈ G, ∀ x : Vec d,
    ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))

include hR hP hminor

/-- Actual endpoint minorization makes the joint successful bridge Markov. -/
theorem isMarkovKernel_bridgeKernelOnEnvironments (hδ : 0 < δ) :
    IsMarkovKernel (bridgeKernelOnEnvironments Δ R i P G) := by
  constructor
  intro a
  rw [bridgeKernelOnEnvironments_apply Δ R i hR P G hP]
  have := hP a.2.1 a.2.2 a.1
  exact Blueprint.sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P
    a.1 a.2.1 hR hδ (hminor a.2.1 a.2.2 a.1)

/-- The weighted successful joint kernel is dominated by the original law. -/
theorem smul_bridgeKernelOnEnvironments_le (a : Vec d × G) :
    ENNReal.ofReal δ • bridgeKernelOnEnvironments Δ R i P G a ≤
      pathKernelOnEnvironments P G a := by
  rw [bridgeKernelOnEnvironments_apply Δ R i hR P G hP, pathKernelOnEnvironments_apply]
  have := hP a.2.1 a.2.2 a.1
  exact Blueprint.sbxS4_smul_killedBridgeMixture_le Δ R δ i P
    a.1 a.2.1 hR (hminor a.2.1 a.2.2 a.1)

/-- The actual failed bridge kernel on the all-start probability carrier. -/
def failedBridgeKernelOnEnvironments : Kernel (Vec d × G) (Path d) := by
  haveI := isFiniteKernel_bridgeKernelOnEnvironments Δ R i hR P G
  exact splitResidualKernel δ (pathKernelOnEnvironments P G)
    (bridgeKernelOnEnvironments Δ R i P G)
    (smul_bridgeKernelOnEnvironments_le Δ R δ i hR P G hP hminor)

/-- Literal identification with s4's failed segment law of the original P. -/
theorem failedBridgeKernelOnEnvironments_apply (a : Vec d × G) :
    failedBridgeKernelOnEnvironments Δ R δ i hR P G hP hminor a =
      Blueprint.sbxS4FailedSegmentLaw Δ R δ i P a.1 a.2.1 := by
  unfold failedBridgeKernelOnEnvironments
  rw [splitResidualKernel_apply, pathKernelOnEnvironments_apply,
    bridgeKernelOnEnvironments_apply Δ R i hR P G hP]
  rfl

/-- The normalized residual is a genuine joint probability kernel. -/
theorem isMarkovKernel_failedBridgeKernelOnEnvironments (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    IsMarkovKernel (failedBridgeKernelOnEnvironments Δ R δ i hR P G hP hminor) := by
  have := isMarkovKernel_pathKernelOnEnvironments P G hP
  have := isMarkovKernel_bridgeKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₀
  exact isMarkovKernel_splitResidualKernel δ _ _ hδ₀.le hδ₁ _

/-- The jointly measurable one-step path/coin kernel, using the actual bridge
and actual residual of P on the good environment carrier. -/
def splitStepKernelOnEnvironments : Kernel (Vec d × G) (Path d × Bool) := by
  haveI := isFiniteKernel_bridgeKernelOnEnvironments Δ R i hR P G
  exact firstCoinKernel δ (pathKernelOnEnvironments P G)
    (bridgeKernelOnEnvironments Δ R i P G)
    (smul_bridgeKernelOnEnvironments_le Δ R δ i hR P G hP hminor)

/-- The step fibre is exactly the first-coin law made from original P. -/
theorem splitStepKernelOnEnvironments_apply (a : Vec d × G) :
    splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor a =
      Blueprint.sbxS4FirstCoinLaw δ (P (a.1, a.2.1))
        (Renewal.killedBridgeMixture Δ R i P a.1 a.2.1) := by
  unfold splitStepKernelOnEnvironments
  rw [firstCoinKernel_apply, pathKernelOnEnvironments_apply,
    bridgeKernelOnEnvironments_apply Δ R i hR P G hP]

/-- The one-step construction is a Markov kernel without assuming a coupled law. -/
theorem isMarkovKernel_splitStepKernelOnEnvironments (hδ₁ : δ < 1) :
    IsMarkovKernel (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor) := by
  have := isMarkovKernel_pathKernelOnEnvironments P G hP
  have := isFiniteKernel_bridgeKernelOnEnvironments Δ R i hR P G
  exact isMarkovKernel_firstCoinKernel δ _ _ hδ₁ _

/-- Forgetting the one-step coin recovers the original path law P. -/
theorem map_splitStepKernelOnEnvironments_fst (hδ₁ : δ < 1) (a : Vec d × G) :
    (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor a).map Prod.fst =
      P (a.1, a.2.1) := by
  have := isFiniteKernel_bridgeKernelOnEnvironments Δ R i hR P G
  exact map_firstCoinKernel_fst δ _ _ hδ₁ _ a

/-- The literal bridge and residual recover P with the source weights. -/
theorem bridge_residual_mixture_on_environments (hδ₁ : δ < 1) (a : Vec d × G) :
    ENNReal.ofReal δ • Renewal.killedBridgeMixture Δ R i P a.1 a.2.1 +
      ENNReal.ofReal (1 - δ) •
        failedBridgeKernelOnEnvironments Δ R δ i hR P G hP hminor a = P (a.1, a.2.1) := by
  have := isFiniteKernel_bridgeKernelOnEnvironments Δ R i hR P G
  have h := splitResidualKernel_recovery δ (pathKernelOnEnvironments P G)
    (bridgeKernelOnEnvironments Δ R i P G) hδ₁
    (smul_bridgeKernelOnEnvironments_le Δ R δ i hR P G hP hminor) a
  simpa only [failedBridgeKernelOnEnvironments,
    bridgeKernelOnEnvironments_apply Δ R i hR P G hP, pathKernelOnEnvironments_apply] using h

/-- Both coin outcomes give the literal one-step real-test identities,
with integrability and with the false branch written as P minus delta times bridge. -/
theorem splitStepKernelOnEnvironments_integral_bit
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (a : Vec d × G) (b : Bool)
    (F : Path d → ℝ) (hF : Measurable F) (hb : BoundedRealTest F) :
    Integrable (fun q : Path d × Bool => (if q.2 = b then (1 : ℝ) else 0) * F q.1)
      (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor a) ∧
    (∫ q, (if q.2 = b then (1 : ℝ) else 0) * F q.1
      ∂splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor a) =
      if b then δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P a.1 a.2.1)
      else (∫ γ, F γ ∂P (a.1, a.2.1)) -
        δ * (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P a.1 a.2.1) := by
  have := isMarkovKernel_pathKernelOnEnvironments P G hP
  have := isFiniteKernel_bridgeKernelOnEnvironments Δ R i hR P G
  have h := firstCoinKernel_integral_bit δ (pathKernelOnEnvironments P G)
    (bridgeKernelOnEnvironments Δ R i P G) hδ₀.le hδ₁
    (smul_bridgeKernelOnEnvironments_le Δ R δ i hR P G hP hminor) a b F hF hb
  refine ⟨h.1, h.2.trans ?_⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    change (1 - δ) * (∫ γ, F γ
      ∂failedBridgeKernelOnEnvironments Δ R δ i hR P G hP hminor a) = _
    rw [failedBridgeKernelOnEnvironments_apply Δ R δ i hR P G hP hminor]
    have := hP a.2.1 a.2.2 a.1
    exact Blueprint.sbxS4_failedSegmentLaw_integral_difference Δ R δ i P
      a.1 a.2.1 hR hδ₀ hδ₁ (hminor a.2.1 a.2.2 a.1) F hF hb
  · simp only [↓reduceIte, bridgeKernelOnEnvironments_apply Δ R i hR P G hP]

end CarrierSplit

section Extension
variable {X Ω β : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace β]

/-- Extend a joint kernel from a measurable environment carrier, assigning
an explicit fallback law only to environments outside that carrier. -/
def extendEnvironmentKernel (G : Set Ω) (hG : MeasurableSet G)
    (K : Kernel (X × G) β) (ν : Measure β) : Kernel (X × Ω) β where
  toFun a := @dite (Measure β) (a.2 ∈ G) (Classical.propDecidable _)
    (fun h => K (a.1, ⟨a.2, h⟩)) (fun _ => ν)
  measurable' := by
    classical
    have hm : Measurable (fun a : {a : X × Ω // a.2 ∈ G} =>
        K (a.1.1, ⟨a.1.2, a.2⟩)) :=
      K.measurable.comp ((measurable_fst.comp measurable_subtype_coe).prodMk
        (measurable_snd.comp measurable_subtype_coe).subtype_mk)
    exact hm.dite measurable_const (hG.preimage measurable_snd)

/-- No fibre on the carrier is changed by the extension. -/
theorem extendEnvironmentKernel_apply_of_mem (G : Set Ω) (hG : MeasurableSet G)
    (K : Kernel (X × G) β) (ν : Measure β) (x : X) (ω : Ω) (hω : ω ∈ G) :
    extendEnvironmentKernel G hG K ν (x, ω) = K (x, ⟨ω, hω⟩) := by
  classical
  exact dite_eq_left hω

/-- Extending by a probability fallback preserves the Markov property. -/
theorem isMarkovKernel_extendEnvironmentKernel (G : Set Ω) (hG : MeasurableSet G)
    (K : Kernel (X × G) β) [IsMarkovKernel K] (ν : Measure β) [IsProbabilityMeasure ν] :
    IsMarkovKernel (extendEnvironmentKernel G hG K ν) := by
  classical
  constructor
  intro a
  change IsProbabilityMeasure (if h : a.2 ∈ G then K (a.1, ⟨a.2, h⟩) else ν)
  split_ifs <;> infer_instance

/-- A measurable conull environment carrier preserves origin fibres a.e. -/
theorem ae_extendEnvironmentKernel_origin (G : Set Ω) (hG : MeasurableSet G)
    (μ : Measure Ω) (hμ : ∀ᵐ ω ∂μ, ω ∈ G) (K : Kernel (X × G) β)
    (ν : Measure β) (x₀ : X) (L : X × Ω → Measure β)
    (hL : ∀ x ω (hω : ω ∈ G), K (x, ⟨ω, hω⟩) = L (x, ω)) :
    ∀ᵐ ω ∂μ, extendEnvironmentKernel G hG K ν (x₀, ω) = L (x₀, ω) := by
  filter_upwards [hμ] with ω hω
  rw [extendEnvironmentKernel_apply_of_mem G hG K ν x₀ ω hω]
  exact hL x₀ ω hω

/-- The same literal identification holds for the spatial product measure. -/
theorem ae_extendEnvironmentKernel_product (G : Set Ω) (hG : MeasurableSet G)
    (μ : Measure Ω) [SFinite μ] (hμ : ∀ᵐ ω ∂μ, ω ∈ G)
    (m : Measure X) (K : Kernel (X × G) β) (ν : Measure β)
    (L : X × Ω → Measure β)
    (hL : ∀ x ω (hω : ω ∈ G), K (x, ⟨ω, hω⟩) = L (x, ω)) :
    ∀ᵐ a ∂m.prod μ, extendEnvironmentKernel G hG K ν a = L a := by
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hμ] with a ha
  rw [extendEnvironmentKernel_apply_of_mem G hG K ν a.1 a.2 ha]
  exact hL a.1 a.2 ha

end Extension

/-- Probability and the precise endpoint minorization admit a common
measurable conull all-start carrier. Neither assumption is replaced by an
almost-everywhere-in-position premise. -/
theorem exists_measurable_split_environments {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (μ : Measure (FieldPair d))
    (P : QuenchedPathLaws d)
    (hP : ∀ᵐ ω ∂μ, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ᵐ ω ∂μ, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ)) :
    ∃ G : Set (FieldPair d), MeasurableSet G ∧ (∀ᵐ ω ∂μ, ω ∈ G) ∧
      (∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω))) ∧
      ∀ ω ∈ G, ∀ x : Vec d,
        ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
          (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ) := by
  classical
  obtain ⟨G₀, hG₀, hμ₀, hp₀⟩ := exists_measurable_probability_environments μ P hP
  have hbad : μ {ω | ¬ ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ)} = 0 := hminor
  obtain ⟨N, hsub, hN, hnull⟩ := exists_measurable_superset_of_null hbad
  have hμN : ∀ᵐ ω ∂μ, ω ∈ Nᶜ := by
    show μ {ω | ω ∉ Nᶜ} = 0
    simpa using hnull
  refine ⟨G₀ ∩ Nᶜ, hG₀.inter hN.compl, hμ₀.and hμN,
    fun ω hω => hp₀ ω hω.1, ?_⟩
  intro ω hω
  by_contra h
  exact hω.2 (hsub h)


/-- A.e. all-start probability and the exact a.e. all-start endpoint
minorization produce a full joint one-step probability kernel. Its origin and
volume-product fibres are the original first-segment laws. The fallback is
used only on the explicitly excluded null set of environments. -/
theorem exists_splitStepKernel_of_ae_minorization {d : ℕ}
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (hR : 0 < R) (hδ₁ : δ < 1)
    (μ : Measure (FieldPair d)) [SFinite μ] (P : QuenchedPathLaws d)
    (hP : ∀ᵐ ω ∂μ, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ᵐ ω ∂μ, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ)) :
    ∃ K : Kernel (Vec d × FieldPair d) (Path d × Bool), IsMarkovKernel K ∧
      (∀ᵐ ω ∂μ, ∀ x : Vec d,
        K (x, ω) = Blueprint.sbxS4FirstSegmentLaw Δ R δ i P x ω) ∧
      ∀ᵐ a ∂((volume : Measure (Vec d)).prod μ),
        K a = Blueprint.sbxS4FirstSegmentLaw Δ R δ i P a.1 a.2 := by
  obtain ⟨G, hG, hμ, hp, hm⟩ := exists_measurable_split_environments Δ R δ i μ P hP hminor
  let S := splitStepKernelOnEnvironments Δ R δ i hR P G hp hm
  have : IsMarkovKernel S :=
    isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hp hm hδ₁
  let ν : Measure (Path d × Bool) := Measure.dirac (0, false)
  let K := extendEnvironmentKernel G hG S ν
  have : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  refine ⟨K, isMarkovKernel_extendEnvironmentKernel G hG S ν, ?_, ?_⟩
  · filter_upwards [hμ] with ω hω
    intro x
    rw [extendEnvironmentKernel_apply_of_mem G hG S ν x ω hω]
    exact splitStepKernelOnEnvironments_apply Δ R δ i hR P G hp hm (x, ⟨ω, hω⟩)
  · exact ae_extendEnvironmentKernel_product G hG μ hμ volume S ν
      (fun a => Blueprint.sbxS4FirstSegmentLaw Δ R δ i P a.1 a.2)
      (fun x ω hω => splitStepKernelOnEnvironments_apply Δ R δ i hR P G hp hm
        (x, ⟨ω, hω⟩))

/-- Apply the carrier construction to the actual GMP reduced path kernel.
The only additional analytic input is the displayed endpoint minorization. -/
theorem exists_splitStepKernel_of_isGMPReducedKernel
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
    (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (hR : 0 < R) (hδ₁ : δ < 1)
    (hminor : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ)) :
    ∃ K : Kernel (Vec d × FieldPair d) (Path d × Bool), IsMarkovKernel K ∧
      (∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
        K (x, ω) = Blueprint.sbxS4FirstSegmentLaw Δ R δ i P x ω) ∧
      ∀ᵐ a ∂((volume : Measure (Vec d)).prod Q.measure),
        K a = Blueprint.sbxS4FirstSegmentLaw Δ R δ i P a.1 a.2 :=
  exists_splitStepKernel_of_ae_minorization Δ R δ i hR hδ₁ Q.measure P
    (isProbabilityMeasure_of_isGMPReducedKernel hd hΛ₀ Q lam h0 h1 P hP) hminor

/-! ## Countable endpoint-driven segment trajectories

Coordinate zero stores the starting position and environment. Coordinate `n + 1`
stores segment `n` and coin `n`. In particular the initial coordinate introduces
no dummy coin. Each subsequent segment is sampled at the preceding endpoint,
with the same environment read from coordinate zero.
-/

/-- Initial data followed by the actual segment/coin pairs. -/
abbrev gridState (d : ℕ) (Ω : Type) : ℕ → Type
  | 0 => Vec d × Ω
  | _ + 1 => Path d × Bool

@[reducible]
instance gridStateMeasurableSpace (d : ℕ) (Ω : Type) [MeasurableSpace Ω] :
    ∀ n, MeasurableSpace (gridState d Ω n)
  | 0 => inferInstanceAs (MeasurableSpace (Vec d × Ω))
  | _ + 1 => inferInstanceAs (MeasurableSpace (Path d × Bool))

/-- A finite history includes its initial data and all already sampled pairs. -/
abbrev gridHistory (d : ℕ) (Ω : Type) (n : ℕ) :=
  (j : Finset.Iic n) → gridState d Ω j.1

section Grid
variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- Read the next starting position and the unchanged environment. -/
def gridHistoryStart (Δ : ℝ≥0) : (n : ℕ) → gridHistory d Ω n → Vec d × Ω
  | 0, h => h ⟨0, Finset.mem_Iic.mpr le_rfl⟩
  | n + 1, h => ((h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1 Δ,
      (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩).2)

/-- Reading the preceding endpoint and initial environment is measurable. -/
theorem measurable_gridHistoryStart (Δ : ℝ≥0) (n : ℕ) :
    Measurable (gridHistoryStart (d := d) (Ω := Ω) Δ n) := by
  cases n with
  | zero => exact measurable_pi_apply _
  | succ n =>
    exact ((continuous_eval_const Δ).measurable.comp
      (measurable_fst.comp (measurable_pi_apply _))).prodMk
      (measurable_snd.comp (measurable_pi_apply _))

/-- The history transition uses the supplied joint segment kernel at the
previous endpoint, without drawing a new environment. -/
def gridStep (Δ : ℝ≥0) (K : Kernel (Vec d × Ω) (Path d × Bool)) (n : ℕ) :
    Kernel (gridHistory d Ω n) (gridState d Ω (n + 1)) :=
  K.comap (gridHistoryStart Δ n) (measurable_gridHistoryStart Δ n)

/-- Literal evaluation of the history transition. -/
theorem gridStep_apply (Δ : ℝ≥0) (K : Kernel (Vec d × Ω) (Path d × Bool))
    (n : ℕ) (h : gridHistory d Ω n) :
    gridStep Δ K n h = K (gridHistoryStart Δ n h) := rfl

instance isMarkovKernel_gridStep (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (gridStep Δ K n) := by
  exact Kernel.IsMarkovKernel.comap K (measurable_gridHistoryStart Δ n)

/-- Initial data occupy the unique coordinate in the zero history. -/
def gridInitialHistory (a : Vec d × Ω) : gridHistory d Ω 0 :=
  fun j => (Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp j.2)).symm ▸ a

/-- The initial embedding is measurable jointly in position and environment. -/
theorem measurable_gridInitialHistory :
    Measurable (gridInitialHistory (d := d) (Ω := Ω)) := by
  apply measurable_pi_iff.mpr
  rintro ⟨j, hj⟩
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp hj)
  subst j
  exact measurable_id

omit [MeasurableSpace Ω] in
/-- Reading the initial history returns precisely the supplied initial data. -/
theorem gridHistoryStart_initial (Δ : ℝ≥0) (a : Vec d × Ω) :
    gridHistoryStart Δ 0 (gridInitialHistory a) = a := rfl

/-- The countable law is jointly measurable in its actual initial data. -/
def gridLawKernel (Δ : ℝ≥0) (K : Kernel (Vec d × Ω) (Path d × Bool))
    [IsMarkovKernel K] : Kernel (Vec d × Ω) ((n : ℕ) → gridState d Ω n) :=
  (Kernel.traj (gridStep Δ K) 0).comap gridInitialHistory measurable_gridInitialHistory

instance isMarkovKernel_gridLawKernel (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K] :
    IsMarkovKernel (gridLawKernel Δ K) := by
  unfold gridLawKernel
  infer_instance

/-- The actual finite-prefix kernel iterates these same endpoint transitions. -/
def gridPrefixKernel (Δ : ℝ≥0) (K : Kernel (Vec d × Ω) (Path d × Bool)) (n : ℕ) :
    Kernel (Vec d × Ω) (gridHistory d Ω n) :=
  (Kernel.partialTraj (gridStep Δ K) 0 n).comap
    gridInitialHistory measurable_gridInitialHistory

instance isMarkovKernel_gridPrefixKernel (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (gridPrefixKernel Δ K n) := by
  unfold gridPrefixKernel
  infer_instance

/-- Every finite prefix of the countable law is the actual iterated split law. -/
theorem gridLawKernel_map_prefix (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ) :
    (gridLawKernel Δ K a).map (Preorder.frestrictLe n) = gridPrefixKernel Δ K n a :=
  Kernel.traj_map_frestrictLe_apply (κ := gridStep Δ K) 0 n (gridInitialHistory a)

/-- Prefixes are compatible under restriction, including the initial data. -/
theorem gridPrefixKernel_map_truncate (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) {m n : ℕ} (hmn : m ≤ n) :
    (gridPrefixKernel Δ K n a).map (Preorder.frestrictLe₂ hmn) =
      gridPrefixKernel Δ K m a :=
  Kernel.partialTraj_map_frestrictLe₂_apply (gridInitialHistory a) hmn

/-- Finite histories retain the original starting position and environment. -/
theorem ae_gridPrefixKernel_initial [MeasurableSingletonClass Ω] (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ) :
    ∀ᵐ h ∂gridPrefixKernel Δ K n a,
      h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ = a := by
  have hzero : gridPrefixKernel Δ K 0 a = Measure.dirac (gridInitialHistory a) := by
    simp [gridPrefixKernel, Kernel.partialTraj_self, Kernel.deterministic_apply]
  have hm := gridPrefixKernel_map_truncate Δ K a (Nat.zero_le n)
  rw [hzero] at hm
  have hp : MeasurableSet {h : gridHistory d Ω 0 | h ⟨0, Finset.mem_Iic.mpr le_rfl⟩ = a} := by
    change MeasurableSet {h : gridHistory d Ω 0 | gridHistoryStart Δ 0 h = a}
    exact measurable_gridHistoryStart Δ 0 (measurableSet_singleton a)
  have ha : ∀ᵐ h ∂(gridPrefixKernel Δ K n a).map
      (Preorder.frestrictLe₂ (Nat.zero_le n)),
      h ⟨0, Finset.mem_Iic.mpr le_rfl⟩ = a := by
    rw [hm]
    exact (ae_dirac_iff hp).mpr rfl
  exact (ae_map_iff (Preorder.measurable_frestrictLe₂ (Nat.zero_le n)).aemeasurable hp).mp ha

/-- Every restart reads the original environment from its finite history. -/
theorem ae_gridPrefixKernel_restart_environment [MeasurableSingletonClass Ω] (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ) :
    ∀ᵐ h ∂gridPrefixKernel Δ K (n + 1) a,
      (gridHistoryStart Δ (n + 1) h).2 = a.2 := by
  filter_upwards [ae_gridPrefixKernel_initial Δ K a (n + 1)] with h hh
  change (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩).2 = a.2
  exact congrArg Prod.snd hh

/-- Forgetting the next coin in the finite-history disintegration retains the
full next-path transition kernel. -/
theorem gridPrefixKernel_compProd_map_nextPath (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ) :
    ((gridPrefixKernel Δ K n a) ⊗ₘ gridStep Δ K n).map
        (fun hq => (hq.1, hq.2.1)) =
      (gridPrefixKernel Δ K n a) ⊗ₘ ((gridStep Δ K n).map Prod.fst) := by
  exact (Measure.compProd_map measurable_fst).symm

/-- The first sampled coordinate is segment zero with coin zero. -/
theorem gridLawKernel_map_first (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K] (a : Vec d × Ω) :
    (gridLawKernel Δ K a).map (fun z => z 1) = K a := by
  have hm := congrArg (fun L => L (gridInitialHistory a))
    (Kernel.map_traj_succ_self (κ := gridStep Δ K) (a := 0))
  rw [Kernel.map_apply _ (measurable_pi_apply 1)] at hm
  exact hm.trans (congrArg K (gridHistoryStart_initial Δ a))

/-- Joint prefix/next-pair law, the exact deterministic-grid restart identity. -/
theorem gridLawKernel_map_prefix_next (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ) :
    (gridLawKernel Δ K a).map (fun z => (Preorder.frestrictLe n z, z (n + 1))) =
      (gridPrefixKernel Δ K n a) ⊗ₘ gridStep Δ K n :=
  (Kernel.partialTraj_compProd_eq_map_traj (κ := gridStep Δ K)
    (Nat.zero_le n) (x₀ := gridInitialHistory a)).symm

/-- Every bounded joint finite-history test satisfies the actual step integral. -/
theorem gridLawKernel_integral_prefix_next (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ)
    (F : gridHistory d Ω n × (Path d × Bool) → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ q, ‖F q‖ ≤ C) :
    (∫ z, F (Preorder.frestrictLe n z, z (n + 1)) ∂gridLawKernel Δ K a) =
      ∫ h, ∫ q, F (h, q) ∂K (gridHistoryStart Δ n h) ∂gridPrefixKernel Δ K n a := by
  have hm : Measurable (fun z : (n : ℕ) → gridState d Ω n =>
      (Preorder.frestrictLe n z, z (n + 1))) :=
    (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  obtain ⟨C, hC⟩ := hb
  have hi : Integrable F ((gridPrefixKernel Δ K n a) ⊗ₘ gridStep Δ K n) :=
    (integrable_const C).mono' hF.aestronglyMeasurable (ae_of_all _ hC)
  calc
    _ = ∫ q, F q ∂((gridPrefixKernel Δ K n a) ⊗ₘ gridStep Δ K n) := by
      rw [← gridLawKernel_map_prefix_next,
        integral_map_of_stronglyMeasurable hm hF.stronglyMeasurable]
    _ = _ := Measure.integral_compProd hi

/-- Coordinates of the segment/coin sequence use precisely the shift `n + 1`. -/
def gridPairs (z : (n : ℕ) → gridState d Ω n) (n : ℕ) : Path d × Bool := z (n + 1)

/-- Extracting the segment/coin sequence is measurable. -/
theorem measurable_gridPairs : Measurable (gridPairs (d := d) (Ω := Ω)) :=
  measurable_pi_iff.mpr fun n => measurable_pi_apply (n + 1)

/-- The countable pair law retains chronological segment/coin indexing. -/
def gridPairLawKernel (Δ : ℝ≥0) (K : Kernel (Vec d × Ω) (Path d × Bool))
    [IsMarkovKernel K] : Kernel (Vec d × Ω) (ℕ → Path d × Bool) :=
  (gridLawKernel Δ K).map gridPairs

instance isMarkovKernel_gridPairLawKernel (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K] :
    IsMarkovKernel (gridPairLawKernel Δ K) := by
  unfold gridPairLawKernel
  exact Kernel.IsMarkovKernel.map _ measurable_gridPairs

/-- Starts-at support passes through the prefix/next-step disintegration. -/
theorem ae_gridLawKernel_step_starts (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (hstart : ∀ a : Vec d × Ω, ∀ᵐ q ∂K a, q.1 0 = a.1)
    (a : Vec d × Ω) (n : ℕ) :
    ∀ᵐ z ∂gridLawKernel Δ K a,
      (z (n + 1)).1 0 = (gridHistoryStart Δ n (Preorder.frestrictLe n z)).1 := by
  have hm : Measurable (fun z : (n : ℕ) → gridState d Ω n =>
      (Preorder.frestrictLe n z, z (n + 1))) :=
    (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  have hp : MeasurableSet {q : gridHistory d Ω n × (Path d × Bool) |
      q.2.1 0 = (gridHistoryStart Δ n q.1).1} :=
    measurableSet_eq_fun
      ((continuous_eval_const 0).measurable.comp (measurable_fst.comp measurable_snd))
      ((measurable_gridHistoryStart Δ n).fst.comp measurable_fst)
  apply (ae_map_iff hm.aemeasurable hp).mp
  rw [gridLawKernel_map_prefix_next]
  exact Measure.ae_compProd_of_ae_ae hp (ae_of_all _ fun h => hstart (gridHistoryStart Δ n h))

/-- All consecutive segments match at their actual grid endpoints almost surely. -/
theorem ae_gridLawKernel_matching (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (hstart : ∀ a : Vec d × Ω, ∀ᵐ q ∂K a, q.1 0 = a.1) (a : Vec d × Ω) :
    ∀ᵐ z ∂gridLawKernel Δ K a, ∀ n : ℕ,
      (gridPairs z (n + 1)).1 0 = (gridPairs z n).1 Δ := by
  have h := ae_all_iff.mpr (fun n : ℕ => ae_gridLawKernel_step_starts Δ K hstart a (n + 1))
  filter_upwards [h] with z hz n
  exact hz n

end Grid

section SplitGrid
variable {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
  (P : QuenchedPathLaws d) (G : Set (FieldPair d))
  (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
  (hminor : ∀ ω ∈ G, ∀ x : Vec d,
    ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
  (hδ₁ : δ < 1)

/-- The actual countable split law on the all-start good environment carrier. -/
def splitGridLawKernel : Kernel (Vec d × G) ((n : ℕ) → gridState d G n) := by
  letI := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  exact gridLawKernel Δ (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor)

/-- The actual infinite split-segment law is a joint probability kernel. -/
theorem isMarkovKernel_splitGridLawKernel :
    IsMarkovKernel (splitGridLawKernel Δ R δ i hR P G hP hminor hδ₁) := by
  unfold splitGridLawKernel
  infer_instance

/-- Every history transition has the literal original-P bridge/residual fibre. -/
theorem splitGridStep_apply (n : ℕ) (h : gridHistory d G n) :
    gridStep Δ (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor) n h =
      Blueprint.sbxS4FirstSegmentLaw Δ R δ i P
        (gridHistoryStart Δ n h).1 (gridHistoryStart Δ n h).2.1 :=
  splitStepKernelOnEnvironments_apply Δ R δ i hR P G hP hminor _

/-- The infinite law's first segment/coin marginal is the literal one-step law. -/
theorem splitGridLawKernel_map_first (a : Vec d × G) :
    (splitGridLawKernel Δ R δ i hR P G hP hminor hδ₁ a).map (fun z => z 1) =
      Blueprint.sbxS4FirstSegmentLaw Δ R δ i P a.1 a.2.1 := by
  letI := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  exact (gridLawKernel_map_first Δ _ a).trans
    (splitStepKernelOnEnvironments_apply Δ R δ i hR P G hP hminor a)

include hδ₁ in
/-- Original-law starting-point support is preserved by the split transition. -/
theorem ae_splitStepKernel_starts
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) (a : Vec d × G) :
    ∀ᵐ q ∂splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor a,
      q.1 0 = a.1 := by
  have hs := hstart a.2.1 a.2.2 a.1
  rw [← map_splitStepKernelOnEnvironments_fst Δ R δ i hR P G hP hminor hδ₁ a] at hs
  exact (ae_map_iff measurable_fst.aemeasurable
    (measurableSet_eq_fun (continuous_eval_const 0).measurable measurable_const)).mp hs

/-- The actual split law has matching segment endpoints whenever P starts at x. -/
theorem ae_splitGridLawKernel_matching
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) (a : Vec d × G) :
    ∀ᵐ z ∂splitGridLawKernel Δ R δ i hR P G hP hminor hδ₁ a, ∀ n : ℕ,
      (gridPairs z (n + 1)).1 0 = (gridPairs z n).1 Δ := by
  letI := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  exact ae_gridLawKernel_matching Δ _
    (ae_splitStepKernel_starts Δ R δ i hR P G hP hminor hδ₁ hstart) a

end SplitGrid

/-! ## Finite concatenation in the original continuous-path carrier

The total append map translates the second path to meet the first endpoint.
On matching segments this translation is zero, so the resulting path agrees
literally with each original segment. Continuity and measurability are proved
before any probability or martingale-problem identification is asserted.
-/

/-- Append at `T`, translating the second path to the first endpoint. -/
def appendPaths {d : ℕ} (T : ℝ≥0) (γ η : Path d) : Path d :=
  ⟨fun t => γ (min t T) + η (t - T) - η 0,
    ((γ.continuous.comp (continuous_id.min continuous_const)).add
      (η.continuous.comp (continuous_id.sub continuous_const))).sub continuous_const⟩

/-- Appending is jointly continuous for the compact-open path topology. -/
theorem continuous_appendPaths {d : ℕ} (T : ℝ≥0) :
    Continuous (fun q : Path d × Path d => appendPaths T q.1 q.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (((continuous_fst.fst).eval (continuous_snd.min continuous_const)).add
    ((continuous_fst.snd).eval (continuous_snd.sub continuous_const))).sub
      ((continuous_fst.snd).eval continuous_const)

/-- The initial part is unchanged, including the joining time. -/
theorem appendPaths_left {d : ℕ} (T : ℝ≥0) (γ η : Path d) {t : ℝ≥0} (ht : t ≤ T) :
    appendPaths T γ η t = γ t := by
  change γ (min t T) + η (t - T) - η 0 = γ t
  rw [min_eq_left ht, tsub_eq_zero_of_le ht, add_sub_cancel_right]

/-- Matching segments are used literally after the join. -/
theorem appendPaths_right {d : ℕ} (T : ℝ≥0) (γ η : Path d)
    (hmatch : η 0 = γ T) {t : ℝ≥0} (ht : T ≤ t) :
    appendPaths T γ η t = η (t - T) := by
  change γ (min t T) + η (t - T) - η 0 = η (t - T)
  rw [min_eq_right ht, ← hmatch, add_sub_cancel_left]

/-- Concatenate segments zero through `n`, keeping their chronological order.
The last segment supplies the continuous extension beyond its grid interval. -/
def finiteConcat {d : ℕ} (Δ : ℝ≥0) (q : ℕ → Path d × Bool) : ℕ → Path d
  | 0 => (q 0).1
  | n + 1 => appendPaths (((n + 1 : ℕ) : ℝ≥0) * Δ) (finiteConcat Δ q n) (q (n + 1)).1

/-- Every finite path assembly is continuous in the segment sequence. -/
theorem continuous_finiteConcat {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    Continuous (fun q : ℕ → Path d × Bool => finiteConcat Δ q n) := by
  induction n with
  | zero => exact (continuous_apply 0).fst
  | succ n ih =>
    exact (continuous_appendPaths _).comp
      (ih.prodMk (continuous_apply (n + 1)).fst)

/-- Every finite assembly is a measurable map to the original `Path d`. -/
theorem measurable_finiteConcat {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    Measurable (fun q : ℕ → Path d × Bool => finiteConcat Δ q n) :=
  (continuous_finiteConcat Δ n).measurable

/-- Extending a finite assembly preserves its entire earlier path. -/
theorem finiteConcat_succ_left {d : ℕ} (Δ : ℝ≥0) (q : ℕ → Path d × Bool)
    (n : ℕ) {t : ℝ≥0} (ht : t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ) :
    finiteConcat Δ q (n + 1) t = finiteConcat Δ q n t :=
  appendPaths_left _ _ _ ht

/-- Compatible prefixes have their literal final segment endpoint. -/
theorem finiteConcat_endpoint {d : ℕ} (Δ : ℝ≥0) (q : ℕ → Path d × Bool)
    (n : ℕ) (hmatch : ∀ j < n, (q (j + 1)).1 0 = (q j).1 Δ) :
    finiteConcat Δ q n (((n + 1 : ℕ) : ℝ≥0) * Δ) = (q n).1 Δ := by
  induction n with
  | zero => simp [finiteConcat]
  | succ n ih =>
    have hm : (q (n + 1)).1 0 = finiteConcat Δ q n (((n + 1 : ℕ) : ℝ≥0) * Δ) :=
      (hmatch n n.lt_succ_self).trans
        (ih (fun j hj => hmatch j (hj.trans n.lt_succ_self))).symm
    have he : ((n + 1 + 1 : ℕ) : ℝ≥0) * Δ = ((n + 1 : ℕ) : ℝ≥0) * Δ + Δ := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    rw [finiteConcat, he, appendPaths_right _ _ _ hm
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ Δ from bot_le)), add_tsub_cancel_left]

/-- On each grid interval a compatible finite assembly is the literal segment. -/
theorem finiteConcat_segment {d : ℕ} (Δ : ℝ≥0) (q : ℕ → Path d × Bool)
    (n : ℕ) (hmatch : ∀ j < n, (q (j + 1)).1 0 = (q j).1 Δ)
    (j : ℕ) (hj : j ≤ n) (t : ℝ≥0) (ht : t ≤ Δ) :
    finiteConcat Δ q n ((j : ℝ≥0) * Δ + t) = (q j).1 t := by
  induction n with
  | zero =>
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simp only [finiteConcat, Nat.cast_zero, zero_mul, zero_add]
  | succ n ih =>
    by_cases hjn : j ≤ n
    · have htime : (j : ℝ≥0) * Δ + t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ := by
        calc
          (j : ℝ≥0) * Δ + t ≤ (n : ℝ≥0) * Δ + Δ :=
            add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjn) (show (0 : ℝ≥0) ≤ Δ from bot_le)) ht
          _ = ((n + 1 : ℕ) : ℝ≥0) * Δ := by
            simp only [Nat.cast_add, Nat.cast_one]
            ring
      rw [finiteConcat_succ_left Δ q n htime]
      exact ih (fun k hk => hmatch k (hk.trans n.lt_succ_self)) hjn
    · have hje : j = n + 1 := by omega
      subst j
      have hm : (q (n + 1)).1 0 = finiteConcat Δ q n (((n + 1 : ℕ) : ℝ≥0) * Δ) :=
        (hmatch n n.lt_succ_self).trans
          (finiteConcat_endpoint Δ q n (fun k hk => hmatch k (hk.trans n.lt_succ_self))).symm
      rw [finiteConcat, appendPaths_right _ _ _ hm
        (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le)), add_tsub_cancel_left]

/-- All later finite assemblies preserve the earlier closed grid window. -/
theorem finiteConcat_prefix {d : ℕ} (Δ : ℝ≥0) (q : ℕ → Path d × Bool)
    {m n : ℕ} (hmn : m ≤ n) {t : ℝ≥0} (ht : t ≤ ((m + 1 : ℕ) : ℝ≥0) * Δ) :
    finiteConcat Δ q n t = finiteConcat Δ q m t := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    have htime : t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ :=
      ht.trans (mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.succ_le_succ hmn)) (show (0 : ℝ≥0) ≤ Δ from bot_le))
    exact (finiteConcat_succ_left Δ q n htime).trans ih

/-- A finite assembly uses exactly its first `n + 1` segment paths. -/
theorem finiteConcat_congr {d : ℕ} (Δ : ℝ≥0) (q q' : ℕ → Path d × Bool)
    (n : ℕ) (h : ∀ j ≤ n, (q j).1 = (q' j).1) :
    finiteConcat Δ q n = finiteConcat Δ q' n := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ n ih =>
    exact congrArg₂ (appendPaths (((n + 1 : ℕ) : ℝ≥0) * Δ))
      (ih (fun j hj => h j (hj.trans n.le_succ))) (h (n + 1) le_rfl)

/-- Within two retained grid windows, the finite path values agree. -/
theorem finiteConcat_agree {d : ℕ} (Δ : ℝ≥0) (q : ℕ → Path d × Bool)
    (m n : ℕ) (t : ℝ≥0) (hm : t ≤ ((m + 1 : ℕ) : ℝ≥0) * Δ) (hn : t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ) :
    finiteConcat Δ q m t = finiteConcat Δ q n t := by
  rcases le_total m n with hmn | hnm
  · exact (finiteConcat_prefix Δ q hmn hm).symm
  · exact finiteConcat_prefix Δ q hnm hn

/-- Positive grid spacing eventually exceeds each finite observation time. -/
theorem exists_concatIndex (Δ : ℝ≥0) (hΔ : 0 < Δ) (t : ℝ≥0) :
    ∃ n : ℕ, t < ((n + 1 : ℕ) : ℝ≥0) * Δ := by
  obtain ⟨n, hn⟩ := exists_lt_nsmul hΔ t
  rw [nsmul_eq_mul] at hn
  exact ⟨n, hn.trans_le (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr n.le_succ) (show (0 : ℝ≥0) ≤ Δ from bot_le))⟩

/-- Select any finite grid window strictly containing a fixed time. -/
def concatIndex (Δ : ℝ≥0) (hΔ : 0 < Δ) (t : ℝ≥0) : ℕ :=
  (exists_concatIndex Δ hΔ t).choose

/-- The chosen grid window strictly contains its observation time. -/
theorem concatIndex_spec (Δ : ℝ≥0) (hΔ : 0 < Δ) (t : ℝ≥0) :
    t < ((concatIndex Δ hΔ t + 1 : ℕ) : ℝ≥0) * Δ :=
  (exists_concatIndex Δ hΔ t).choose_spec

/-- Countable path concatenation, defined by the locally fixed finite assembly.
The total map normalizes joins; on matching segments no normalization remains. -/
def infiniteConcat {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (q : ℕ → Path d × Bool) : Path d :=
  ⟨fun t => finiteConcat Δ q (concatIndex Δ hΔ t) t, by
    rw [continuous_iff_continuousAt]
    intro t
    apply (finiteConcat Δ q (concatIndex Δ hΔ t)).continuous.continuousAt.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (concatIndex_spec Δ hΔ t)] with u hu
    exact finiteConcat_agree Δ q _ _ u (concatIndex_spec Δ hΔ u).le hu.le⟩

/-- The assembled path agrees with every sufficiently long finite prefix. -/
theorem infiniteConcat_eq_finite {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (q : ℕ → Path d × Bool) (n : ℕ) (t : ℝ≥0) (ht : t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ) :
    infiniteConcat Δ hΔ q t = finiteConcat Δ q n t :=
  finiteConcat_agree Δ q _ n t (concatIndex_spec Δ hΔ t).le ht

/-- Infinite concatenation is measurable into the original continuous-path space. -/
theorem measurable_infiniteConcat {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    Measurable (infiniteConcat (d := d) Δ hΔ) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  change Measurable (fun q => finiteConcat Δ q (concatIndex Δ hΔ t) t)
  exact (continuous_eval_const t).measurable.comp
    (measurable_finiteConcat Δ (concatIndex Δ hΔ t))

/-- Matching countable segments are preserved literally on every grid interval. -/
theorem infiniteConcat_segment {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (q : ℕ → Path d × Bool) (hmatch : ∀ j, (q (j + 1)).1 0 = (q j).1 Δ)
    (j : ℕ) (t : ℝ≥0) (ht : t ≤ Δ) :
    infiniteConcat Δ hΔ q ((j : ℝ≥0) * Δ + t) = (q j).1 t := by
  have htime : (j : ℝ≥0) * Δ + t ≤ ((j + 1 : ℕ) : ℝ≥0) * Δ := by
    calc
      (j : ℝ≥0) * Δ + t ≤ (j : ℝ≥0) * Δ + Δ := add_le_add_right ht _
      _ = ((j + 1 : ℕ) : ℝ≥0) * Δ := by
        simp only [Nat.cast_add, Nat.cast_one]
        ring
  rw [infiniteConcat_eq_finite Δ hΔ q j _ htime]
  exact finiteConcat_segment Δ q j (fun k _ => hmatch k) j le_rfl t ht

/-- Concatenation starts at the literal first segment origin. -/
theorem infiniteConcat_zero {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (q : ℕ → Path d × Bool) : infiniteConcat Δ hΔ q 0 = (q 0).1 0 :=
  infiniteConcat_eq_finite Δ hΔ q 0 0 bot_le

/-- Original coupled sample: the concatenated path and the same indexed coins. -/
def coupledConcat {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (q : ℕ → Path d × Bool) :
    CoupledSample d := (infiniteConcat Δ hΔ q, fun n => (q n).2)

/-- The complete path/coin assembly is measurable, with no reindexing of coins. -/
theorem measurable_coupledConcat {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    Measurable (coupledConcat (d := d) Δ hΔ) :=
  (measurable_infiniteConcat Δ hΔ).prodMk
    (measurable_pi_iff.mpr fun n => (measurable_pi_apply n).snd)

/-- The exact stopped history is already determined by the finite assembly. -/
theorem coupledConcat_stoppedHistory {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (q : ℕ → Path d × Bool) (n : ℕ) :
    Probability.stoppedHistorySample Δ (n + 1) (coupledConcat Δ hΔ q) =
      Probability.stoppedHistorySample Δ (n + 1)
        (finiteConcat Δ q n, fun j => (q j).2) := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    exact infiniteConcat_eq_finite Δ hΔ q n _ (min_le_right _ _)
  · rfl

/-- Equal segment/coin prefixes yield exactly equal stopped coupled histories. -/
theorem coupledConcat_stoppedHistory_congr {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (q q' : ℕ → Path d × Bool) (n : ℕ) (h : ∀ j ≤ n, q j = q' j) :
    Probability.stoppedHistorySample Δ (n + 1) (coupledConcat Δ hΔ q) =
      Probability.stoppedHistorySample Δ (n + 1) (coupledConcat Δ hΔ q') := by
  rw [coupledConcat_stoppedHistory, coupledConcat_stoppedHistory,
    finiteConcat_congr Δ q q' n (fun j hj => congrArg Prod.fst (h j hj))]
  apply Prod.ext
  · rfl
  · funext j
    change (if j < n + 1 then (q j).2 else false) =
      (if j < n + 1 then (q' j).2 else false)
    by_cases hj : j < n + 1
    · rw [ite_eq_left hj, ite_eq_left hj, h j (Nat.le_of_lt_succ hj)]
    · rw [ite_eq_right hj, ite_eq_right hj]

section CoupledGrid
variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- Countable segment construction pushed to the original coupled path space. -/
def gridCoupledLawKernel (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K] :
    Kernel (Vec d × Ω) (CoupledSample d) :=
  (gridPairLawKernel Δ K).map (coupledConcat Δ hΔ)

instance isMarkovKernel_gridCoupledLawKernel (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K] :
    IsMarkovKernel (gridCoupledLawKernel Δ hΔ K) :=
  Kernel.IsMarkovKernel.map _ (measurable_coupledConcat Δ hΔ)

/-- Under starts-at support, every assembled grid interval is its sampled segment.
This is simultaneous in all intervals and all real times in each interval. -/
theorem ae_gridLawKernel_concat_segments (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (hstart : ∀ a : Vec d × Ω, ∀ᵐ q ∂K a, q.1 0 = a.1) (a : Vec d × Ω) :
    ∀ᵐ z ∂gridLawKernel Δ K a, ∀ n : ℕ, ∀ t : ℝ≥0, t ≤ Δ →
      (coupledConcat Δ hΔ (gridPairs z)).1 ((n : ℝ≥0) * Δ + t) = (gridPairs z n).1 t := by
  filter_upwards [ae_gridLawKernel_matching Δ K hstart a] with z hz n t ht
  exact infiniteConcat_segment Δ hΔ _ hz n t ht

end CoupledGrid


section SplitCoupledGrid
variable {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
  (P : QuenchedPathLaws d) (G : Set (FieldPair d))
  (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
  (hminor : ∀ ω ∈ G, ∀ x : Vec d,
    ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
  (hδ₁ : δ < 1)

/-- The actual split segments assembled into the original coupled sample space. -/
def splitGridCoupledLawKernel : Kernel (Vec d × G) (CoupledSample d) := by
  letI := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  exact gridCoupledLawKernel Δ hΔ
    (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor)

/-- The actual assembled split law is jointly measurable and probabilistic. -/
theorem isMarkovKernel_splitGridCoupledLawKernel :
    IsMarkovKernel (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁) := by
  unfold splitGridCoupledLawKernel
  infer_instance

/-- Forgetting the coin at a history transition gives the original path law
at that history's actual restart position and environment. -/
theorem gridStep_split_map_nextPath (hδ₁ : δ < 1) (n : ℕ) (h : gridHistory d G n) :
    ((gridStep Δ (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor) n h).map
      Prod.fst) =
      P ((gridHistoryStart Δ n h).1, (gridHistoryStart Δ n h).2.1) := by
  rw [gridStep_apply]
  exact map_splitStepKernelOnEnvironments_fst Δ R δ i hR P G hP hminor hδ₁ _

/-- Forgetting the coin in the next-step joint law yields the original
path kernel at the restart position and environment. -/
theorem splitGridPrefix_compProd_nextPath (hδ₁ : δ < 1) (a : Vec d × G) (n : ℕ) :
    ((gridPrefixKernel Δ (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor) n a) ⊗ₘ
      gridStep Δ (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor) n).map
        (fun hq => (hq.1, hq.2.1)) =
      (gridPrefixKernel Δ (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor) n a) ⊗ₘ
        (P.comap (fun h : gridHistory d G n =>
          ((gridHistoryStart Δ n h).1, (gridHistoryStart Δ n h).2.1))
          ((measurable_gridHistoryStart Δ n).fst.prodMk
            (measurable_subtype_coe.comp (measurable_gridHistoryStart Δ n).snd))) := by
  letI := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  rw [gridPrefixKernel_compProd_map_nextPath]
  congr 1
  apply Kernel.ext
  intro h
  rw [Kernel.map_apply _ measurable_fst, Kernel.comap_apply]
  exact gridStep_split_map_nextPath Δ R δ i hR P G hP hminor hδ₁ n h

/-- Every actual sampled split segment survives the assembly literally. -/
theorem ae_splitGridLawKernel_concat_segments
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x) (a : Vec d × G) :
    ∀ᵐ z ∂splitGridLawKernel Δ R δ i hR P G hP hminor hδ₁ a,
      ∀ n : ℕ, ∀ t : ℝ≥0, t ≤ Δ →
        (coupledConcat Δ hΔ (gridPairs z)).1 ((n : ℝ≥0) * Δ + t) = (gridPairs z n).1 t := by
  letI := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  exact ae_gridLawKernel_concat_segments Δ hΔ _
    (ae_splitStepKernel_starts Δ R δ i hR P G hP hminor hδ₁ hstart) a

end SplitCoupledGrid


/-! ## Deterministic restart in the assembled path and coin space -/

section AssembledRestart
variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- Extend a finite segment/coin history by zero pairs. The extension is used
only under a stopped-history map, where the later coordinates are irrelevant. -/
def gridHistoryPairs (n : ℕ) (h : gridHistory d Ω (n + 1))
    (j : ℕ) : Path d × Bool :=
  if hj : j ≤ n then h ⟨j + 1, Finset.mem_Iic.mpr (Nat.add_le_add_right hj 1)⟩
  else (0, false)

/-- Finite history extension is measurable in every coordinate. -/
theorem measurable_gridHistoryPairs (n : ℕ) :
    Measurable (gridHistoryPairs (d := d) (Ω := Ω) n) := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases hj : j ≤ n
  · simpa only [gridHistoryPairs, dite_eq_left hj] using
      (measurable_pi_apply
        (⟨j + 1, Finset.mem_Iic.mpr (Nat.add_le_add_right hj 1)⟩ : Finset.Iic (n + 1)))
  · simpa only [gridHistoryPairs, dite_eq_right hj] using
      (measurable_const : Measurable (fun _ : gridHistory d Ω (n + 1) =>
        ((0 : Path d), false)))

/-- The stopped coupled sample assembled from precisely the first `n + 1` pairs. -/
def gridStoppedHistory (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ)
    (h : gridHistory d Ω (n + 1)) : CoupledSample d :=
  Probability.stoppedHistorySample Δ (n + 1)
    (coupledConcat Δ hΔ (gridHistoryPairs n h))

/-- The assembled finite past is measurable in the finite grid history. -/
theorem measurable_gridStoppedHistory (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ) :
    Measurable (gridStoppedHistory (d := d) (Ω := Ω) Δ hΔ n) := by
  exact ((Probability.measurable_stoppedHistorySample Δ (n + 1)).mono
    (Probability.finiteHistorySigma_le Δ (n + 1)) le_rfl).comp
      ((measurable_coupledConcat Δ hΔ).comp (measurable_gridHistoryPairs n))

omit [MeasurableSpace Ω] in
/-- Stopping the infinite assembly agrees pointwise with finite assembly.
No starts-at or Markov assumption is needed for this finite dependence fact. -/
theorem gridStoppedHistory_restrict (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ)
    (z : (n : ℕ) → gridState d Ω n) :
    gridStoppedHistory Δ hΔ n (Preorder.frestrictLe (n + 1) z) =
      Probability.stoppedHistorySample Δ (n + 1) (coupledConcat Δ hΔ (gridPairs z)) := by
  apply coupledConcat_stoppedHistory_congr
  intro j hj
  simp only [gridHistoryPairs, dite_eq_left hj, gridPairs, Preorder.frestrictLe]
  rfl

/-- The assembled coupled law is the pushforward of the same grid law,
with no additional randomization of either paths or coins. -/
theorem gridCoupledLawKernel_apply (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K] (a : Vec d × Ω) :
    gridCoupledLawKernel Δ hΔ K a =
      (gridLawKernel Δ K a).map (fun z => coupledConcat Δ hΔ (gridPairs z)) := by
  rw [gridCoupledLawKernel, Kernel.map_apply _ (measurable_coupledConcat Δ hΔ),
    gridPairLawKernel, Kernel.map_apply _ measurable_gridPairs,
    Measure.map_map (measurable_coupledConcat Δ hΔ) measurable_gridPairs]
  rfl

/-- The actual stopped coupled law is already determined by its finite prefix. -/
theorem gridCoupledLawKernel_map_stoppedHistory (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ) :
    (gridCoupledLawKernel Δ hΔ K a).map (Probability.stoppedHistorySample Δ (n + 1)) =
      (gridPrefixKernel Δ K (n + 1) a).map (gridStoppedHistory Δ hΔ n) := by
  have hs := (Probability.measurable_stoppedHistorySample (d := d) Δ (n + 1)).mono
    (Probability.finiteHistorySigma_le Δ (n + 1)) le_rfl
  rw [gridCoupledLawKernel_apply, Measure.map_map
    (f := fun z : (j : ℕ) → gridState d Ω j => coupledConcat Δ hΔ (gridPairs z)) hs
    ((measurable_coupledConcat Δ hΔ).comp measurable_gridPairs)]
  simp only [Function.comp_def]
  have he : (fun z : (j : ℕ) → gridState d Ω j =>
      Probability.stoppedHistorySample Δ (n + 1) (coupledConcat Δ hΔ (gridPairs z))) =
      (gridStoppedHistory Δ hΔ n) ∘ Preorder.frestrictLe (n + 1) := by
    funext z
    exact (gridStoppedHistory_restrict Δ hΔ n z).symm
  rw [he, ← Measure.map_map (measurable_gridStoppedHistory Δ hΔ n)
    (Preorder.measurable_frestrictLe (n + 1)), gridLawKernel_map_prefix]

/-- Joint law of the literal assembled past and the next sampled path/coin pair. -/
theorem gridLawKernel_map_stopped_next (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ) :
    (gridLawKernel Δ K a).map (fun z =>
      (Probability.stoppedHistorySample Δ (n + 1) (coupledConcat Δ hΔ (gridPairs z)),
        z (n + 1 + 1))) =
      ((gridPrefixKernel Δ K (n + 1) a) ⊗ₘ gridStep Δ K (n + 1)).map
        (fun hq => (gridStoppedHistory Δ hΔ n hq.1, hq.2)) := by
  rw [← gridLawKernel_map_prefix_next,
    Measure.map_map
      (f := fun z : (j : ℕ) → gridState d Ω j =>
        (Preorder.frestrictLe (n + 1) z, z (n + 1 + 1)))
      (g := fun hq => (gridStoppedHistory Δ hΔ n hq.1, hq.2))
      ((measurable_gridStoppedHistory Δ hΔ n).comp measurable_fst |>.prodMk
      measurable_snd)
      ((Preorder.measurable_frestrictLe (n + 1)).prodMk (measurable_pi_apply _))]
  simp only [Function.comp_def]
  congr 1
  funext z
  exact congrArg (fun h => (h, z (n + 1 + 1)))
    (gridStoppedHistory_restrict Δ hΔ n z).symm

/-- Bounded tests of the actual assembled past and the next pair satisfy
restart with the original endpoint and the unchanged environment in `K`. -/
theorem gridLawKernel_integral_stopped_next (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ)
    (F : CoupledSample d × (Path d × Bool) → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ q, ‖F q‖ ≤ C) :
    (∫ z, F (Probability.stoppedHistorySample Δ (n + 1)
        (coupledConcat Δ hΔ (gridPairs z)), z (n + 1 + 1)) ∂gridLawKernel Δ K a) =
      ∫ h, ∫ q, F (gridStoppedHistory Δ hΔ n h, q)
        ∂K (gridHistoryStart Δ (n + 1) h) ∂gridPrefixKernel Δ K (n + 1) a := by
  have hf : Measurable (fun hq : gridHistory d Ω (n + 1) × (Path d × Bool) =>
      F (gridStoppedHistory Δ hΔ n hq.1, hq.2)) :=
    hF.comp (((measurable_gridStoppedHistory Δ hΔ n).comp measurable_fst).prodMk
      measurable_snd)
  obtain ⟨C, hC⟩ := hb
  have he := gridLawKernel_integral_prefix_next Δ K a (n + 1) _ hf
    ⟨C, fun hq => hC (gridStoppedHistory Δ hΔ n hq.1, hq.2)⟩
  simpa only [gridStoppedHistory_restrict] using he

/-- Deterministic restart of any finite endpoint/coin history, including
zero-length and nonzero-length restart times. -/
theorem gridPrefixKernel_restart (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) (a : Vec d × Ω)
    {m n : ℕ} (hmn : m ≤ n) :
    Kernel.partialTraj (gridStep Δ K) m n ∘ₘ gridPrefixKernel Δ K m a =
      gridPrefixKernel Δ K n a := by
  change (Kernel.partialTraj (gridStep Δ K) m n ∘ₖ
    Kernel.partialTraj (gridStep Δ K) 0 m) (gridInitialHistory a) =
      Kernel.partialTraj (gridStep Δ K) 0 n (gridInitialHistory a)
  rw [Kernel.partialTraj_comp_partialTraj (Nat.zero_le m) hmn]

/-- Bounded tests of arbitrary finite histories satisfy deterministic restart. -/
theorem gridPrefixKernel_integral_restart (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) {m n : ℕ} (hmn : m ≤ n)
    (F : gridHistory d Ω n → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ h, ‖F h‖ ≤ C) :
    (∫ h, F h ∂gridPrefixKernel Δ K n a) =
      ∫ h, ∫ h', F h' ∂Kernel.partialTraj (gridStep Δ K) m n h
        ∂gridPrefixKernel Δ K m a := by
  obtain ⟨C, hC⟩ := hb
  have hi : Integrable F (gridPrefixKernel Δ K n a) :=
    (integrable_const C).mono' hF.aestronglyMeasurable (ae_of_all _ hC)
  rw [← gridPrefixKernel_restart Δ K a hmn, Measure.comp_eq_comp_const_apply] at hi ⊢
  exact Kernel.integral_comp hi

/-- The whole countable continuation, jointly with its actual finite past,
has the exact Ionescu--Tulcea disintegration at every deterministic grid time. -/
theorem gridLawKernel_map_prefix_continuation (Δ : ℝ≥0)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ) :
    (gridLawKernel Δ K a).map (fun z => (Preorder.frestrictLe n z, z)) =
      (gridPrefixKernel Δ K n a) ⊗ₘ Kernel.traj (gridStep Δ K) n :=
  (Kernel.partialTraj_compProd_traj (κ := gridStep Δ K)
    (Nat.zero_le n) (gridInitialHistory a)).symm

end AssembledRestart


/-! ## Continuous-path marginal tests and the genuine first interval -/

/-- Stop a continuous path at the stated time, keeping its terminal value. -/
def stopPathAt {d : ℕ} (T : ℝ≥0) (γ : Path d) : Path d :=
  ⟨fun t => γ (min t T), γ.continuous.comp (continuous_id.min continuous_const)⟩

/-- Stopping is continuous in the compact-open path topology. -/
theorem continuous_stopPathAt {d : ℕ} (T : ℝ≥0) :
    Continuous (stopPathAt (d := d) T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_fst.eval (continuous_snd.min continuous_const)

/-- In particular the stopped-path map is Borel measurable. -/
theorem measurable_stopPathAt {d : ℕ} (T : ℝ≥0) :
    Measurable (stopPathAt (d := d) T) := (continuous_stopPathAt T).measurable

/-- A later stopping time does not affect an earlier stopped path. -/
theorem stopPathAt_comp_of_le {d : ℕ} {S T : ℝ≥0} (hST : S ≤ T) (γ : Path d) :
    stopPathAt S (stopPathAt T γ) = stopPathAt S γ := by
  apply ContinuousMap.ext
  intro t
  change γ (min (min t S) T) = γ (min t S)
  rw [min_eq_left ((min_le_right t S).trans hST)]

/-- The entire Borel sigma-algebra of actual continuous paths is generated
by their stopped paths along any positive deterministic grid. The proof uses
all genuine time evaluations, rather than a replacement cylinder space. -/
theorem pathSigma_eq_iSup_stopped {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    (inferInstance : MeasurableSpace (Path d)) =
      ⨆ n : ℕ, MeasurableSpace.comap
        (stopPathAt (d := d) (((n + 1 : ℕ) : ℝ≥0) * Δ)) inferInstance := by
  apply le_antisymm
  · calc
      (inferInstance : MeasurableSpace (Path d)) =
          ⨆ t : ℝ≥0, MeasurableSpace.comap (fun γ : Path d => γ t) inferInstance :=
        ContinuousMap.measurableSpace_eq_iSup_comap_eval
      _ ≤ _ := by
        apply iSup_le
        intro t
        obtain ⟨n, hn⟩ := exists_concatIndex Δ hΔ t
        apply le_iSup_of_le n
        apply MeasurableSpace.comap_le_comap_of_eq_comp
          (fun γ : Path d => γ t) (continuous_eval_const t).measurable
        funext γ
        change γ t = γ (min t (((n + 1 : ℕ) : ℝ≥0) * Δ))
        rw [min_eq_left hn.le]
  · exact iSup_le fun n => (measurable_stopPathAt _).comap_le

/-- Equality of the actual stopped-path marginals on a positive grid implies
equality of finite Borel path laws. This is an extension criterion, without any
assumption that the supplied original process already has a restart property. -/
theorem measure_eq_of_stoppedPath_marginals {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (μ ν : Measure (Path d)) [IsFiniteMeasure μ]
    (h : ∀ n : ℕ, μ.map (stopPathAt (((n + 1 : ℕ) : ℝ≥0) * Δ)) =
      ν.map (stopPathAt (((n + 1 : ℕ) : ℝ≥0) * Δ))) : μ = ν := by
  let m : ℕ → MeasurableSpace (Path d) := fun n =>
    MeasurableSpace.comap (stopPathAt (((n + 1 : ℕ) : ℝ≥0) * Δ)) inferInstance
  have hm : Monotone m := by
    intro j k hjk
    apply MeasurableSpace.comap_le_comap_of_eq_comp
      (stopPathAt (((j + 1 : ℕ) : ℝ≥0) * Δ)) (measurable_stopPathAt _)
    funext γ
    exact (stopPathAt_comp_of_le
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.add_le_add_right hjk 1))
        (show (0 : ℝ≥0) ≤ Δ from bot_le)) γ).symm
  have hgen : (inferInstance : MeasurableSpace (Path d)) =
      MeasurableSpace.generateFrom (⋃ n : ℕ, {s | MeasurableSet[m n] s}) := by
    rw [MeasurableSpace.generateFrom_iUnion_measurableSet m]
    exact pathSigma_eq_iSup_stopped Δ hΔ
  apply ext_of_generate_finite _ hgen
    (isPiSystem_iUnion_of_monotone _ (fun n => @MeasurableSpace.isPiSystem_measurableSet _ (m n))
      (fun j k hjk _ hs => hm hjk _ hs))
  · intro s hs
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hs
    obtain ⟨t, ht, rfl⟩ := hn
    rw [← Measure.map_apply (measurable_stopPathAt _) ht, h n,
      Measure.map_apply (measurable_stopPathAt _) ht]
  · have he := congrArg (fun ρ : Measure (Path d) => ρ Set.univ) (h 0)
    simpa only [Measure.map_apply (measurable_stopPathAt _) MeasurableSet.univ,
      Set.preimage_univ] using he

/-- The stopped path/coin pair of one actual assembled interval. The path
is stopped at the interval endpoint, since later parts of a sampled segment
are not used by the concatenation. -/
def gridIntervalSample {d : ℕ} (Δ : ℝ≥0) (n : ℕ) (z : CoupledSample d) :
    Path d × Bool :=
  (⟨fun t => z.1 ((n : ℝ≥0) * Δ + min t Δ),
    z.1.continuous.comp (continuous_const.add (continuous_id.min continuous_const))⟩,
    z.2 n)

/-- Reading an assembled interval, including its actual coin, is measurable. -/
theorem measurable_gridIntervalSample {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    Measurable (gridIntervalSample (d := d) Δ n) := by
  apply Measurable.prodMk
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    change Measurable (fun z : CoupledSample d => z.1 ((n : ℝ≥0) * Δ + min t Δ))
    exact (continuous_eval_const _).measurable.comp measurable_fst
  · exact (measurable_pi_apply n).comp measurable_snd

/-- The first assembled interval is the literal first sampled pair, stopped
at its endpoint, even for sequences whose later segments do not match. -/
theorem gridIntervalSample_concat_zero {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (q : ℕ → Path d × Bool) :
    gridIntervalSample Δ 0 (coupledConcat Δ hΔ q) =
      (stopPathAt Δ (q 0).1, (q 0).2) := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    simp only [gridIntervalSample, coupledConcat, stopPathAt, ContinuousMap.coe_mk,
      Nat.cast_zero, zero_mul, zero_add]
    exact infiniteConcat_eq_finite Δ hΔ q 0 _ (by simpa using min_le_right t Δ)
  · rfl

section IntervalMarginals
variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- Exact first-interval marginal of the actual infinite coupled law. -/
theorem gridCoupledLawKernel_map_firstInterval (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K] (a : Vec d × Ω) :
    (gridCoupledLawKernel Δ hΔ K a).map (gridIntervalSample Δ 0) =
      (K a).map (fun q => (stopPathAt Δ q.1, q.2)) := by
  rw [gridCoupledLawKernel_apply, Measure.map_map
    (f := fun z : (j : ℕ) → gridState d Ω j => coupledConcat Δ hΔ (gridPairs z))
    (measurable_gridIntervalSample Δ 0)
    ((measurable_coupledConcat Δ hΔ).comp measurable_gridPairs)]
  simp only [Function.comp_def]
  have he : (fun z : (n : ℕ) → gridState d Ω n =>
      gridIntervalSample Δ 0 (coupledConcat Δ hΔ (gridPairs z))) =
      (fun q : Path d × Bool => (stopPathAt Δ q.1, q.2)) ∘ (fun z => z 1) := by
    funext z
    exact gridIntervalSample_concat_zero Δ hΔ (gridPairs z)
  rw [he, ← Measure.map_map
    (f := fun z : (j : ℕ) → gridState d Ω j => z 1)
    (g := fun q : Path d × Bool => (stopPathAt Δ q.1, q.2))
    (((measurable_stopPathAt Δ).comp measurable_fst).prodMk measurable_snd)
      (measurable_pi_apply 1), gridLawKernel_map_first]

/-- Forgetting the first-interval coin gives exactly the stopped first-step
path law; it makes no full original-process identification claim. -/
theorem gridCoupledLawKernel_map_firstPath (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K] (a : Vec d × Ω) :
    (gridCoupledLawKernel Δ hΔ K a).map (fun z => stopPathAt Δ z.1) =
      ((K a).map Prod.fst).map (stopPathAt Δ) := by
  have he := congrArg (fun μ : Measure (Path d × Bool) => μ.map Prod.fst)
    (gridCoupledLawKernel_map_firstInterval Δ hΔ K a)
  rw [Measure.map_map measurable_fst (measurable_gridIntervalSample Δ 0),
    Measure.map_map (f := fun q : Path d × Bool => (stopPathAt Δ q.1, q.2)) measurable_fst
      (((measurable_stopPathAt Δ).comp measurable_fst).prodMk measurable_snd)] at he
  rw [Measure.map_map (measurable_stopPathAt Δ) measurable_fst]
  have hzero : (fun z : CoupledSample d => (gridIntervalSample Δ 0 z).1) =
      (fun z => stopPathAt Δ z.1) := by
    funext z
    apply ContinuousMap.ext
    intro t
    simp only [gridIntervalSample, stopPathAt, ContinuousMap.coe_mk, Nat.cast_zero,
      zero_mul, zero_add]
  simpa only [Function.comp_def, hzero] using he


/-- With the actual starts-at support, every assembled interval is its sampled
segment stopped at `Δ`, with the identical coin. -/
theorem ae_gridLawKernel_intervalSample (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (hstart : ∀ a : Vec d × Ω, ∀ᵐ q ∂K a, q.1 0 = a.1) (a : Vec d × Ω) :
    ∀ᵐ z ∂gridLawKernel Δ K a, ∀ n : ℕ,
      gridIntervalSample Δ n (coupledConcat Δ hΔ (gridPairs z)) =
        (stopPathAt Δ (gridPairs z n).1, (gridPairs z n).2) := by
  filter_upwards [ae_gridLawKernel_concat_segments Δ hΔ K hstart a] with z hz n
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    exact hz n (min t Δ) (min_le_right t Δ)
  · rfl

/-- The restart position in the finite history is the endpoint of the literal
assembled stopped path, almost surely under that same finite-prefix law. -/
theorem ae_gridPrefixKernel_stopped_endpoint (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (hstart : ∀ a : Vec d × Ω, ∀ᵐ q ∂K a, q.1 0 = a.1)
    (a : Vec d × Ω) (n : ℕ) :
    ∀ᵐ h ∂gridPrefixKernel Δ K (n + 1) a,
      (gridStoppedHistory Δ hΔ n h).1 (((n + 1 : ℕ) : ℝ≥0) * Δ) =
        (gridHistoryStart Δ (n + 1) h).1 := by
  have hp : MeasurableSet {h : gridHistory d Ω (n + 1) |
      (gridStoppedHistory Δ hΔ n h).1 (((n + 1 : ℕ) : ℝ≥0) * Δ) =
        (gridHistoryStart Δ (n + 1) h).1} :=
    measurableSet_eq_fun
      ((continuous_eval_const _).measurable.comp
        (measurable_gridStoppedHistory Δ hΔ n).fst)
      (measurable_gridHistoryStart Δ (n + 1)).fst
  rw [← gridLawKernel_map_prefix Δ K a (n + 1)]
  apply (ae_map_iff (Preorder.measurable_frestrictLe (n + 1)).aemeasurable hp).mpr
  filter_upwards [ae_gridLawKernel_concat_segments Δ hΔ K hstart a] with z hz
  rw [gridStoppedHistory_restrict]
  have he := hz n Δ le_rfl
  simpa only [Probability.stoppedHistorySample, ContinuousMap.coe_mk, min_self,
    gridHistoryStart, Preorder.frestrictLe, Finset.restrict, gridPairs,
    Nat.cast_add, Nat.cast_one, add_mul, one_mul] using he

/-- The finite-prefix restart state is the stopped endpoint together with the
original environment, on one common good set for that prefix. -/
theorem ae_gridPrefixKernel_stopped_restart [MeasurableSingletonClass Ω]
    (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (hstart : ∀ a : Vec d × Ω, ∀ᵐ q ∂K a, q.1 0 = a.1)
    (a : Vec d × Ω) (n : ℕ) :
    ∀ᵐ h ∂gridPrefixKernel Δ K (n + 1) a,
      gridHistoryStart Δ (n + 1) h =
        ((gridStoppedHistory Δ hΔ n h).1 (((n + 1 : ℕ) : ℝ≥0) * Δ), a.2) := by
  filter_upwards [ae_gridPrefixKernel_stopped_endpoint Δ hΔ K hstart a n,
    ae_gridPrefixKernel_restart_environment Δ K a n] with h hp he
  exact Prod.ext hp.symm he

/-- Restart of the SAME coupled law, tested against its literal stopped past
and next stopped segment/coin pair. The transition retains the original
endpoint and the initial environment through `gridHistoryStart`. -/
theorem gridCoupledLawKernel_map_stopped_nextInterval (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (hstart : ∀ a : Vec d × Ω, ∀ᵐ q ∂K a, q.1 0 = a.1)
    (a : Vec d × Ω) (n : ℕ) :
    (gridCoupledLawKernel Δ hΔ K a).map (fun z =>
      (Probability.stoppedHistorySample Δ (n + 1) z, gridIntervalSample Δ (n + 1) z)) =
      ((gridPrefixKernel Δ K (n + 1) a) ⊗ₘ gridStep Δ K (n + 1)).map
        (fun hq => (gridStoppedHistory Δ hΔ n hq.1,
          (stopPathAt Δ hq.2.1, hq.2.2))) := by
  have hs := (Probability.measurable_stoppedHistorySample (d := d) Δ (n + 1)).mono
    (Probability.finiteHistorySigma_le Δ (n + 1)) le_rfl
  rw [gridCoupledLawKernel_apply, Measure.map_map
    (f := fun z : (j : ℕ) → gridState d Ω j => coupledConcat Δ hΔ (gridPairs z))
    (g := fun z => (Probability.stoppedHistorySample Δ (n + 1) z,
      gridIntervalSample Δ (n + 1) z))
    (hs.prodMk (measurable_gridIntervalSample Δ (n + 1)))
    ((measurable_coupledConcat Δ hΔ).comp measurable_gridPairs)]
  simp only [Function.comp_def]
  calc
    _ = (gridLawKernel Δ K a).map (fun z =>
        (Probability.stoppedHistorySample Δ (n + 1) (coupledConcat Δ hΔ (gridPairs z)),
          (stopPathAt Δ (z (n + 1 + 1)).1, (z (n + 1 + 1)).2))) := by
      apply Measure.map_congr
      filter_upwards [ae_gridLawKernel_intervalSample Δ hΔ K hstart a] with z hz
      exact congrArg (fun q =>
        (Probability.stoppedHistorySample Δ (n + 1) (coupledConcat Δ hΔ (gridPairs z)), q))
          (hz (n + 1))
    _ = _ := by
      have he := congrArg
        (fun μ : Measure (CoupledSample d × (Path d × Bool)) =>
          μ.map (fun hq => (hq.1, (stopPathAt Δ hq.2.1, hq.2.2))))
        (gridLawKernel_map_stopped_next Δ hΔ K a n)
      rw [Measure.map_map
        (f := fun z : (j : ℕ) → gridState d Ω j =>
          (Probability.stoppedHistorySample Δ (n + 1) (coupledConcat Δ hΔ (gridPairs z)),
            z (n + 1 + 1)))
        (g := fun hq => (hq.1, (stopPathAt Δ hq.2.1, hq.2.2)))
        (measurable_fst.prodMk
          (((measurable_stopPathAt Δ).comp (measurable_fst.comp measurable_snd)).prodMk
            (measurable_snd.comp measurable_snd)))
        (hs.comp ((measurable_coupledConcat Δ hΔ).comp measurable_gridPairs) |>.prodMk
          (measurable_pi_apply _)),
        Measure.map_map
          (f := fun hq : gridHistory d Ω (n + 1) × (Path d × Bool) =>
            (gridStoppedHistory Δ hΔ n hq.1, hq.2))
          (g := fun hq => (hq.1, (stopPathAt Δ hq.2.1, hq.2.2)))
          (measurable_fst.prodMk
            (((measurable_stopPathAt Δ).comp (measurable_fst.comp measurable_snd)).prodMk
              (measurable_snd.comp measurable_snd)))
          (((measurable_gridStoppedHistory Δ hΔ n).comp measurable_fst).prodMk
            measurable_snd)] at he
      simpa only [Function.comp_def] using he

/-- Bounded measurable tests of the actual past and next interval satisfy
the deterministic-grid restart integral, simultaneously for both coin branches. -/
theorem gridCoupledLawKernel_integral_stopped_nextInterval (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (hstart : ∀ a : Vec d × Ω, ∀ᵐ q ∂K a, q.1 0 = a.1)
    (a : Vec d × Ω) (n : ℕ)
    (F : CoupledSample d × (Path d × Bool) → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ q, ‖F q‖ ≤ C) :
    (∫ z, F (Probability.stoppedHistorySample Δ (n + 1) z,
        gridIntervalSample Δ (n + 1) z) ∂gridCoupledLawKernel Δ hΔ K a) =
      ∫ h, ∫ q, F (gridStoppedHistory Δ hΔ n h, (stopPathAt Δ q.1, q.2))
        ∂K (gridHistoryStart Δ (n + 1) h) ∂gridPrefixKernel Δ K (n + 1) a := by
  have hs := (Probability.measurable_stoppedHistorySample (d := d) Δ (n + 1)).mono
    (Probability.finiteHistorySigma_le Δ (n + 1)) le_rfl
  have hm := hs.prodMk (measurable_gridIntervalSample Δ (n + 1))
  have hg : Measurable (fun hq : gridHistory d Ω (n + 1) × (Path d × Bool) =>
      (gridStoppedHistory Δ hΔ n hq.1, (stopPathAt Δ hq.2.1, hq.2.2))) :=
    ((measurable_gridStoppedHistory Δ hΔ n).comp measurable_fst).prodMk
      (((measurable_stopPathAt Δ).comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  obtain ⟨C, hC⟩ := hb
  have hi : Integrable (F ∘ fun hq =>
      (gridStoppedHistory Δ hΔ n hq.1, (stopPathAt Δ hq.2.1, hq.2.2)))
      ((gridPrefixKernel Δ K (n + 1) a) ⊗ₘ gridStep Δ K (n + 1)) :=
    (integrable_const C).mono' (hF.comp hg).aestronglyMeasurable
      (ae_of_all _ fun hq => hC _)
  calc
    _ = ∫ u, F u ∂((gridCoupledLawKernel Δ hΔ K a).map (fun z =>
        (Probability.stoppedHistorySample Δ (n + 1) z, gridIntervalSample Δ (n + 1) z))) :=
      (integral_map_of_stronglyMeasurable hm hF.stronglyMeasurable).symm
    _ = _ := by
      rw [gridCoupledLawKernel_map_stopped_nextInterval Δ hΔ K hstart a n,
        integral_map_of_stronglyMeasurable hg hF.stronglyMeasurable]
      exact Measure.integral_compProd hi

/-- Disintegration of the full assembled coupled path and its actual stopped
past. The continuation law is the original trajectory kernel with the literal
finite history as its input, without any replacement process. -/
theorem gridCoupledLawKernel_map_stopped_continuation (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ) :
    (gridCoupledLawKernel Δ hΔ K a).map (fun z =>
      (Probability.stoppedHistorySample Δ (n + 1) z, z)) =
      ((gridPrefixKernel Δ K (n + 1) a) ⊗ₘ Kernel.traj (gridStep Δ K) (n + 1)).map
        (fun hz => (gridStoppedHistory Δ hΔ n hz.1,
          coupledConcat Δ hΔ (gridPairs hz.2))) := by
  have hs := (Probability.measurable_stoppedHistorySample (d := d) Δ (n + 1)).mono
    (Probability.finiteHistorySigma_le Δ (n + 1)) le_rfl
  rw [gridCoupledLawKernel_apply, Measure.map_map
    (f := fun z : (j : ℕ) → gridState d Ω j => coupledConcat Δ hΔ (gridPairs z))
    (g := fun z => (Probability.stoppedHistorySample Δ (n + 1) z, z))
    (hs.prodMk measurable_id)
    ((measurable_coupledConcat Δ hΔ).comp measurable_gridPairs),
    ← gridLawKernel_map_prefix_continuation,
    Measure.map_map
      (f := fun z : (j : ℕ) → gridState d Ω j => (Preorder.frestrictLe (n + 1) z, z))
      (g := fun hz => (gridStoppedHistory Δ hΔ n hz.1,
        coupledConcat Δ hΔ (gridPairs hz.2)))
      (((measurable_gridStoppedHistory Δ hΔ n).comp measurable_fst).prodMk
        (((measurable_coupledConcat Δ hΔ).comp measurable_gridPairs).comp measurable_snd))
      ((Preorder.measurable_frestrictLe (n + 1)).prodMk measurable_id)]
  simp only [Function.comp_def]
  congr 1
  funext z
  exact congrArg (fun h => (h, coupledConcat Δ hΔ (gridPairs z)))
    (gridStoppedHistory_restrict Δ hΔ n z).symm

end IntervalMarginals

/-- The infinite split construction already has the correct original `P`
path marginal on its first deterministic interval, with both coins integrated out. -/
theorem splitGridCoupledLawKernel_map_firstPath {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1) (a : Vec d × G) :
    (splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a).map
      (fun z => stopPathAt Δ z.1) = (P (a.1, a.2.1)).map (stopPathAt Δ) := by
  haveI := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  change (gridCoupledLawKernel Δ hΔ
    (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor) a).map _ = _
  rw [gridCoupledLawKernel_map_firstPath,
    map_splitStepKernelOnEnvironments_fst Δ R δ i hR P G hP hminor hδ₁]

/-- The supplied reduced law has the actual deterministic restart identity
under every Borel event of its complete past, simultaneously at all starting
points. This transports the existing GMP full-past theorem through the literal
all-start identification in `IsGMPReducedKernel`; no restart premise is added. -/
theorem ae_originalLaw_deterministic_restart {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P) :
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

/-- The actual supplied law disintegrates into its complete stopped past and
its complete shifted future, using its own endpoint restart kernel. -/
theorem ae_originalLaw_joint_restart {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (s : ℝ≥0) (x : Vec d),
      (P (x, ω)).map (fun γ => (stopPathAt s γ, gmpShiftPath s γ)) =
        ((P (x, ω)).map (stopPathAt s)) ⊗ₘ
          (P.comap (fun γ : Path d => (γ s, ω))
            ((continuous_eval_const s).measurable.prodMk measurable_const)) := by
  filter_upwards [ae_originalLaw_deterministic_restart hd hΛ₀ Q lam h0 h1 P hP,
    isProbabilityMeasure_of_isGMPReducedKernel hd hΛ₀ Q lam h0 h1 P hP]
    with ω hr hprob
  intro s x
  let J : Kernel (Path d) (Path d) := P.comap (fun γ : Path d => (γ s, ω))
    ((continuous_eval_const s).measurable.prodMk measurable_const)
  haveI : IsProbabilityMeasure (P (x, ω)) := hprob x
  haveI : IsMarkovKernel J := ⟨fun γ => hprob (γ s)⟩
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

/-- The supplied GMP law starts at every requested point on a common set of
environments. -/
theorem ae_originalLaw_all_starts {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x := by
  filter_upwards [hP] with ω hω
  obtain ⟨_, r, hr⟩ := hω
  intro x
  rw [hr x]
  exact r.pathLaw_starts_at x

/-- A path is literally recovered by appending its shifted future to its
stopped past; no almost-everywhere or starts-at assumption is required. -/
theorem appendPaths_stopped_shift {d : ℕ} (T : ℝ≥0) (γ : Path d) :
    appendPaths T (stopPathAt T γ) (gmpShiftPath T γ) = γ := by
  apply ContinuousMap.ext
  intro t
  by_cases ht : t ≤ T
  · rw [appendPaths_left T _ _ ht]
    change γ (min t T) = γ t
    rw [min_eq_left ht]
  · have hT : T ≤ t := le_of_not_ge ht
    have hm : gmpShiftPath T γ 0 = stopPathAt T γ T := by
      change γ (T + 0) = γ (min T T)
      simp only [add_zero, min_self]
    rw [appendPaths_right T _ _ hm hT]
    change γ (T + (t - T)) = γ t
    rw [add_tsub_cancel_of_le hT]

/-- Observing an appended path only up to `T + U` uses only the first `U`
units of the second path, including both joining endpoints. -/
theorem stopPathAt_append_stop {d : ℕ} (T U : ℝ≥0) (γ η : Path d) :
    stopPathAt (T + U) (appendPaths T γ (stopPathAt U η)) =
      stopPathAt (T + U) (appendPaths T γ η) := by
  apply ContinuousMap.ext
  intro t
  have ht : min t (T + U) - T ≤ U := by
    apply tsub_le_iff_right.mpr
    simpa only [add_comm] using (min_le_right t (T + U))
  change γ (min (min t (T + U)) T) + η (min (min t (T + U) - T) U) -
      η (min 0 U) = γ (min (min t (T + U)) T) + η (min t (T + U) - T) - η 0
  rw [min_eq_left ht, zero_min]

/-- The original law's stopped marginals satisfy the literal concatenation
recurrence, derived from its proved full-past restart rather than supplied as
an extra premise. This includes the entire next path interval. -/
theorem ae_originalLaw_stopped_append {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (T U : ℝ≥0) (x : Vec d),
      (P (x, ω)).map (stopPathAt (T + U)) =
        (((P (x, ω)).map (stopPathAt T)) ⊗ₘ
          (P.comap (fun γ : Path d => (γ T, ω))
            ((continuous_eval_const T).measurable.prodMk measurable_const))).map
          (fun q => stopPathAt (T + U) (appendPaths T q.1 (stopPathAt U q.2))) := by
  filter_upwards [ae_originalLaw_joint_restart hd hΛ₀ Q lam h0 h1 P hP] with ω hr
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

/-- A stopped path is recovered from its stopped past and its next stopped
interval. This pointwise identity is independent of the underlying law. -/
theorem stopPathAt_eq_append_stopped_shift {d : ℕ} (T U : ℝ≥0) (γ : Path d) :
    stopPathAt (T + U) γ =
      stopPathAt (T + U)
        (appendPaths T (stopPathAt T γ) (stopPathAt U (gmpShiftPath T γ))) := by
  rw [stopPathAt_append_stop, appendPaths_stopped_shift]

/-- A matching sampled segment recovers the next stopped prefix. -/
theorem stopPathAt_eq_append_segment {d : ℕ} (T U : ℝ≥0) (γ η : Path d)
    (hseg : ∀ t : ℝ≥0, t ≤ U → γ (T + t) = η t) :
    stopPathAt (T + U) γ =
      stopPathAt (T + U)
        (appendPaths T (stopPathAt T γ) (stopPathAt U η)) := by
  have he : stopPathAt U (gmpShiftPath T γ) = stopPathAt U η := by
    apply ContinuousMap.ext
    intro t
    exact hseg (min t U) (min_le_right t U)
  rw [stopPathAt_eq_append_stopped_shift T U γ, he]

/-- Each next assembled prefix is recovered from its actual sampled segment,
simultaneously over the deterministic grid. -/
theorem ae_splitGridLawKernel_stopped_append {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (a : Vec d × G) :
    ∀ᵐ z ∂splitGridLawKernel Δ R δ i hR P G hP hminor hδ₁ a, ∀ n : ℕ,
      stopPathAt ((((n + 1 : ℕ) : ℝ≥0) * Δ) + Δ)
        (coupledConcat Δ hΔ (gridPairs z)).1 =
      stopPathAt ((((n + 1 : ℕ) : ℝ≥0) * Δ) + Δ)
        (appendPaths (((n + 1 : ℕ) : ℝ≥0) * Δ)
          (stopPathAt (((n + 1 : ℕ) : ℝ≥0) * Δ)
            (coupledConcat Δ hΔ (gridPairs z)).1)
          (stopPathAt Δ (gridPairs z (n + 1)).1)) := by
  filter_upwards [ae_splitGridLawKernel_concat_segments Δ hΔ R δ i hR P G hP hminor
    hδ₁ hstart a] with z hz n
  exact stopPathAt_eq_append_segment _ _ _ _ (hz (n + 1))

/-- The assembled stopped past and next path use the original path kernel
at the literal finite-history restart state. -/
theorem splitGridLawKernel_map_stopped_nextPath {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1) (a : Vec d × G) (n : ℕ) :
    (splitGridLawKernel Δ R δ i hR P G hP hminor hδ₁ a).map
      (fun z => (Probability.stoppedHistorySample Δ (n + 1)
        (coupledConcat Δ hΔ (gridPairs z)), (z (n + 1 + 1)).1)) =
      ((gridPrefixKernel Δ (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor)
        (n + 1) a) ⊗ₘ
        (P.comap (fun h : gridHistory d G (n + 1) =>
          ((gridHistoryStart Δ (n + 1) h).1, (gridHistoryStart Δ (n + 1) h).2.1))
          ((measurable_gridHistoryStart Δ (n + 1)).fst.prodMk
            (measurable_subtype_coe.comp (measurable_gridHistoryStart Δ (n + 1)).snd)))).map
        (fun hq => (gridStoppedHistory Δ hΔ n hq.1, hq.2)) := by
  letI := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  calc
    _ = ((gridLawKernel Δ (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor) a).map
        (fun z => (Preorder.frestrictLe (n + 1) z, z (n + 1 + 1)))).map
        (fun hq => (gridStoppedHistory Δ hΔ n hq.1, hq.2.1)) := by
      rw [Measure.map_map
        (f := fun z : (j : ℕ) → gridState d G j =>
          (Preorder.frestrictLe (n + 1) z, z (n + 1 + 1)))
        (g := fun hq => (gridStoppedHistory Δ hΔ n hq.1, hq.2.1))
        ((measurable_gridStoppedHistory Δ hΔ n).comp measurable_fst |>.prodMk
        (measurable_fst.comp measurable_snd))
        ((Preorder.measurable_frestrictLe (n + 1)).prodMk (measurable_pi_apply _))]
      congr 1
      funext z
      exact congrArg (fun h => (h, (z (n + 1 + 1)).1))
        (gridStoppedHistory_restrict Δ hΔ n z).symm
    _ = _ := by
      rw [gridLawKernel_map_prefix_next,
        ← splitGridPrefix_compProd_nextPath Δ R δ i hR P G hP hminor hδ₁ a (n + 1),
        Measure.map_map
          (f := fun hq : gridHistory d G (n + 1) × (Path d × Bool) => (hq.1, hq.2.1))
          (g := fun hq => (gridStoppedHistory Δ hΔ n hq.1, hq.2))
          ((measurable_gridStoppedHistory Δ hΔ n).comp measurable_fst |>.prodMk
          measurable_snd) (measurable_fst.prodMk (measurable_fst.comp measurable_snd))]
      rfl

/-- Reindex a Markov transition along the observed past. -/
theorem map_compProd_comap_statistic {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel β γ) [IsMarkovKernel κ] (f : α → β) (hf : Measurable f) :
    (μ ⊗ₘ κ.comap f hf).map (fun p => (f p.1, p.2)) = μ.map f ⊗ₘ κ := by
  apply Measure.ext_prod
  intro s t hs ht
  have hm : Measurable (fun p : α × γ => (f p.1, p.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_apply hm (hs.prod ht)]
  change (μ ⊗ₘ κ.comap f hf) ((f ⁻¹' s) ×ˢ t) = _
  rw [Measure.compProd_apply_prod (hf hs) ht, Measure.compProd_apply_prod hs ht,
    setLIntegral_map hs (κ.measurable_coe ht) hf]
  rfl

/-- Reindex a transition whose restart state agrees almost everywhere with a
measurable function of the observed past. -/
theorem map_compProd_comap_statistic_ae {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel δ γ) [IsMarkovKernel κ]
    (f : α → β) (hf : Measurable f) (r : β → δ) (hr : Measurable r)
    (g : α → δ) (hg : Measurable g) (he : ∀ᵐ x ∂μ, g x = r (f x)) :
    (μ ⊗ₘ κ.comap g hg).map (fun p => (f p.1, p.2)) =
      μ.map f ⊗ₘ κ.comap r hr := by
  have hk : κ.comap g hg =ᵐ[μ] (κ.comap r hr).comap f hf := by
    filter_upwards [he] with x hx
    simp only [Kernel.comap_apply, hx]
  rw [Measure.compProd_congr hk]
  exact map_compProd_comap_statistic μ (κ.comap r hr) f hf

/-- Forget a history coordinate when the transition depends only on the
remaining statistic. -/
theorem map_compProd_fst_comap {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (κ : Kernel γ δ) [IsMarkovKernel κ] (r : α → γ) (hr : Measurable r) :
    (μ ⊗ₘ (κ.comap r hr).comap Prod.fst measurable_fst).map
      (fun q => (q.1.1, q.2)) = μ.map Prod.fst ⊗ₘ κ.comap r hr := by
  exact map_compProd_comap_statistic μ (κ.comap r hr) Prod.fst measurable_fst

/-- The next original path depends on the assembled past only through its
endpoint and the unchanged environment. -/
theorem splitGridLawKernel_map_stopped_nextPath_endpoint {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (a : Vec d × G) (n : ℕ) :
    (splitGridLawKernel Δ R δ i hR P G hP hminor hδ₁ a).map
      (fun z => (Probability.stoppedHistorySample Δ (n + 1)
        (coupledConcat Δ hΔ (gridPairs z)), (z (n + 1 + 1)).1)) =
      ((gridPrefixKernel Δ (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor)
        (n + 1) a).map (gridStoppedHistory Δ hΔ n)) ⊗ₘ
        (pathKernelOnEnvironments P G).comap
          (fun q : CoupledSample d => (q.1 (((n + 1 : ℕ) : ℝ≥0) * Δ), a.2))
          (((continuous_eval_const _).measurable.comp measurable_fst).prodMk measurable_const) := by
  let := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  let := isMarkovKernel_pathKernelOnEnvironments P G hP
  rw [splitGridLawKernel_map_stopped_nextPath Δ hΔ R δ i hR P G hP hminor hδ₁ a n]
  have he := ae_gridPrefixKernel_stopped_restart Δ hΔ
    (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor)
    (ae_splitStepKernel_starts Δ R δ i hR P G hP hminor hδ₁ hstart) a n
  exact map_compProd_comap_statistic_ae _ (pathKernelOnEnvironments P G)
    (gridStoppedHistory Δ hΔ n) (measurable_gridStoppedHistory Δ hΔ n)
    (fun q => (q.1 (((n + 1 : ℕ) : ℝ≥0) * Δ), a.2))
    (((continuous_eval_const _).measurable.comp measurable_fst).prodMk measurable_const)
    (gridHistoryStart Δ (n + 1)) (measurable_gridHistoryStart Δ (n + 1)) he

/-- The stopped path and the next path have the endpoint restart law. -/
theorem splitGridLawKernel_map_stoppedPath_nextPath_endpoint {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (a : Vec d × G) (n : ℕ) :
    (splitGridLawKernel Δ R δ i hR P G hP hminor hδ₁ a).map
      (fun z => ((Probability.stoppedHistorySample Δ (n + 1)
        (coupledConcat Δ hΔ (gridPairs z))).1, (z (n + 1 + 1)).1)) =
      (((gridPrefixKernel Δ (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor)
        (n + 1) a).map (gridStoppedHistory Δ hΔ n)).map Prod.fst) ⊗ₘ
        (pathKernelOnEnvironments P G).comap
          (fun γ : Path d => (γ (((n + 1 : ℕ) : ℝ≥0) * Δ), a.2))
          ((continuous_eval_const _).measurable.prodMk measurable_const) := by
  let := isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  let := isMarkovKernel_pathKernelOnEnvironments P G hP
  have hs := (Probability.measurable_stoppedHistorySample (d := d) Δ (n + 1)).mono
    (Probability.finiteHistorySigma_le Δ (n + 1)) le_rfl
  have hm : Measurable (fun z : (j : ℕ) → gridState d G j =>
      (Probability.stoppedHistorySample Δ (n + 1) (coupledConcat Δ hΔ (gridPairs z)),
        (z (n + 1 + 1)).1)) :=
    (hs.comp ((measurable_coupledConcat Δ hΔ).comp measurable_gridPairs)).prodMk
      (measurable_fst.comp (measurable_pi_apply (n + 1 + 1)))
  have he := congrArg (fun μ : Measure (CoupledSample d × Path d) =>
    μ.map (fun q => (q.1.1, q.2)))
    (splitGridLawKernel_map_stopped_nextPath_endpoint Δ hΔ R δ i hR P G hP hminor hδ₁ hstart a n)
  rw [Measure.map_map (g := fun q : CoupledSample d × Path d => (q.1.1, q.2))
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd) hm] at he
  simp only [Function.comp_def] at he
  rw [he]
  exact map_compProd_fst_comap _ (pathKernelOnEnvironments P G)
    (fun γ : Path d => (γ (((n + 1 : ℕ) : ℝ≥0) * Δ), a.2))
    ((continuous_eval_const _).measurable.prodMk measurable_const)

/-- The next stopped prefix follows the endpoint restart recurrence. -/
theorem splitGridLawKernel_stopped_prefix_recurrence {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (a : Vec d × G) (n : ℕ) :
    (splitGridLawKernel Δ R δ i hR P G hP hminor hδ₁ a).map
      (fun z => stopPathAt ((((n + 1 : ℕ) : ℝ≥0) * Δ) + Δ)
        (coupledConcat Δ hΔ (gridPairs z)).1) =
      ((((gridPrefixKernel Δ (splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor)
        (n + 1) a).map (gridStoppedHistory Δ hΔ n)).map Prod.fst) ⊗ₘ
        (pathKernelOnEnvironments P G).comap
          (fun γ : Path d => (γ (((n + 1 : ℕ) : ℝ≥0) * Δ), a.2))
          ((continuous_eval_const _).measurable.prodMk measurable_const)).map
        (fun q => stopPathAt ((((n + 1 : ℕ) : ℝ≥0) * Δ) + Δ)
          (appendPaths (((n + 1 : ℕ) : ℝ≥0) * Δ) q.1 (stopPathAt Δ q.2))) := by
  let T : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0) * Δ
  let f : Path d × Path d → Path d := fun q =>
    stopPathAt (T + Δ) (appendPaths T q.1 (stopPathAt Δ q.2))
  have hf : Measurable f := (measurable_stopPathAt (T + Δ)).comp
    ((continuous_appendPaths T).measurable.comp
      (measurable_fst.prodMk ((measurable_stopPathAt Δ).comp measurable_snd)))
  have hs := (Probability.measurable_stoppedHistorySample (d := d) Δ (n + 1)).mono
    (Probability.finiteHistorySigma_le Δ (n + 1)) le_rfl
  have hg : Measurable (fun z : (j : ℕ) → gridState d G j =>
      ((Probability.stoppedHistorySample Δ (n + 1)
        (coupledConcat Δ hΔ (gridPairs z))).1, (z (n + 1 + 1)).1)) :=
    ((measurable_fst.comp hs).comp ((measurable_coupledConcat Δ hΔ).comp
      measurable_gridPairs)).prodMk (measurable_fst.comp (measurable_pi_apply (n + 1 + 1)))
  rw [← splitGridLawKernel_map_stoppedPath_nextPath_endpoint Δ hΔ R δ i hR P G hP
    hminor hδ₁ hstart a n, Measure.map_map hf hg]
  apply Measure.map_congr
  filter_upwards [ae_splitGridLawKernel_stopped_append Δ hΔ R δ i hR P G hP hminor
    hδ₁ hstart a] with z hz
  simpa only [Function.comp_def, f, T, Probability.stoppedHistorySample, gridPairs, stopPathAt] using hz n

/-- The path projection of the finite stopped history is the stopped assembled law. -/
theorem gridCoupledLawKernel_map_stoppedPath {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (K : Kernel (Vec d × Ω) (Path d × Bool)) [IsMarkovKernel K]
    (a : Vec d × Ω) (n : ℕ) :
    (gridCoupledLawKernel Δ hΔ K a).map
      (fun z => stopPathAt (((n + 1 : ℕ) : ℝ≥0) * Δ) z.1) =
      ((gridPrefixKernel Δ K (n + 1) a).map (gridStoppedHistory Δ hΔ n)).map Prod.fst := by
  have hs := (Probability.measurable_stoppedHistorySample (d := d) Δ (n + 1)).mono
    (Probability.finiteHistorySigma_le Δ (n + 1)) le_rfl
  rw [← gridCoupledLawKernel_map_stoppedHistory Δ hΔ K a n,
    Measure.map_map measurable_fst hs]
  rfl

/-- The actual split assembly has the supplied original law on every grid prefix. -/
theorem ae_splitGridCoupledLawKernel_stoppedPath_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (hGMP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
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
  filter_upwards [ae_originalLaw_stopped_append hd hΛ₀ Q lam h0 h1 P hGMP] with ω hr
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

/-- The path marginal of the actual split assembly is the supplied original law. -/
theorem ae_splitGridCoupledLawKernel_path_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (hGMP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
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
  filter_upwards [ae_splitGridCoupledLawKernel_stoppedPath_eq hd hΛ₀ Q lam h0 h1
    Δ hΔ R δ i hR P hGMP G hP hminor hδ₁ hstart] with ω hω'
  intro x hω
  let := isMarkovKernel_splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁
  apply measure_eq_of_stoppedPath_marginals Δ hΔ
  intro n
  rw [Measure.map_map (measurable_stopPathAt _) measurable_fst]
  exact hω' x hω n

/-- The actual extended split assembly has both exact probability and path
marginal qualifiers, including the origin and the spatial product measure. -/
theorem extended_splitGridCoupledLawKernel_marginals {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (hGMP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
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
  have hm := ae_splitGridCoupledLawKernel_path_eq hd hΛ₀ Q lam h0 h1
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

/-- The next actual split coin has the prescribed mean against every bounded
measurable test of the stopped past at a positive grid index. -/
theorem splitGridCoupledLawKernel_freshBit_succ {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (a : Vec d × G) (n : ℕ) (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ (n + 1)) inferInstance H)
    (hb : BoundedRealTest H) :
    (∫ z, H z * (if z.2 (n + 1) = true then (1 : ℝ) else 0)
      ∂splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a) =
      δ * ∫ z, H z ∂splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a := by
  let K := splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor
  have : IsMarkovKernel K :=
    isMarkovKernel_splitStepKernelOnEnvironments Δ R δ i hR P G hP hminor hδ₁
  have hs : ∀ a : Vec d × G, ∀ᵐ q ∂K a, q.1 0 = a.1 :=
    ae_splitStepKernel_starts Δ R δ i hR P G hP hminor hδ₁ hstart
  have hHm : Measurable H := hH.mono (Probability.finiteHistorySigma_le Δ (n + 1)) le_rfl
  have hbit : Measurable (fun q : Path d × Bool => if q.2 = true then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      measurable_const measurable_const
  obtain ⟨C, hC⟩ := hb
  have hbound : ∀ z, ‖H z‖ ≤ C := by simpa only [Real.norm_eq_abs] using hC
  have hF : Measurable (fun z : CoupledSample d × (Path d × Bool) =>
      H z.1 * (if z.2.2 = true then (1 : ℝ) else 0)) :=
    (hHm.comp measurable_fst).mul (hbit.comp measurable_snd)
  have hFb : ∃ C : ℝ, ∀ z : CoupledSample d × (Path d × Bool),
      ‖H z.1 * (if z.2.2 = true then (1 : ℝ) else 0)‖ ≤ C := by
    refine ⟨C, ?_⟩
    intro z
    by_cases hz : z.2.2 = true
    · simpa [hz] using hbound z.1
    · simpa [hz] using le_trans (norm_nonneg (H z.1)) (hbound z.1)
  have h1 := gridCoupledLawKernel_integral_stopped_nextInterval Δ hΔ K hs a n _ hF hFb
  have h2 := gridCoupledLawKernel_integral_stopped_nextInterval Δ hΔ K hs a n
    (fun z => H z.1) (hHm.comp measurable_fst) ⟨C, fun z => hbound z.1⟩
  have hc (b : Vec d × G) :
      (∫ q, (if q.2 = true then (1 : ℝ) else 0) ∂K b) = δ := by
    have he := (splitStepKernelOnEnvironments_integral_bit Δ R δ i hR P G hP hminor
      hδ₀ hδ₁ b true (fun _ => 1) measurable_const ⟨1, by simp⟩).2
    have := hP b.2.1 b.2.2 b.1
    have : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P b.1 b.2.1) :=
      Blueprint.sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P
        b.1 b.2.1 hR hδ₀ (hminor b.2.1 b.2.2 b.1)
    simpa [K, integral_const] using he
  change (∫ z, H z * (if z.2 (n + 1) = true then (1 : ℝ) else 0)
      ∂gridCoupledLawKernel Δ hΔ K a) = δ * ∫ z, H z ∂gridCoupledLawKernel Δ hΔ K a
  simp only [Probability.finiteHistory_test_stopped Δ (n + 1) H hH,
    gridIntervalSample] at h1 h2
  simp only [integral_const_mul, hc] at h1
  have h2' : (∫ z, H z ∂gridCoupledLawKernel Δ hΔ K a) =
      ∫ h, H (gridStoppedHistory Δ hΔ n h) ∂gridPrefixKernel Δ K (n + 1) a := by
    simpa only [integral_const, smul_eq_mul, measureReal_def, measure_univ,
      ENNReal.toReal_one, one_mul] using h2
  calc
    _ = ∫ h, H (gridStoppedHistory Δ hΔ n h) * δ ∂gridPrefixKernel Δ K (n + 1) a := h1
    _ = δ * ∫ h, H (gridStoppedHistory Δ hΔ n h) ∂gridPrefixKernel Δ K (n + 1) a := by
      simp only [mul_comm, integral_const_mul]
    _ = _ := congrArg (fun x : ℝ => δ * x) h2'.symm

/-- The initial split coin has the prescribed mean against the actual initial history. -/
theorem splitGridCoupledLawKernel_freshBit_zero {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R δ : ℝ) (i : Fin d) (hR : 0 < R)
    (P : QuenchedPathLaws d) (G : Set (FieldPair d))
    (hP : ∀ ω ∈ G, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (hminor : ∀ ω ∈ G, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) ≤
        (Renewal.killedSegmentLaw Δ R i P x ω).map (fun γ : Path d => γ Δ))
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hstart : ∀ ω ∈ G, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (a : Vec d × G) (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 0) inferInstance H) :
    (∫ z, H z * (if z.2 0 = true then (1 : ℝ) else 0)
      ∂splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a) =
      δ * ∫ z, H z ∂splitGridCoupledLawKernel Δ hΔ R δ i hR P G hP hminor hδ₁ a := by
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
  have hfirst := gridCoupledLawKernel_map_firstInterval Δ hΔ K a
  have hI := integral_map_of_stronglyMeasurable (μ := gridCoupledLawKernel Δ hΔ K a)
    (measurable_gridIntervalSample Δ 0)
    (hFm.mul hbit).stronglyMeasurable
  have hJ := integral_map_of_stronglyMeasurable (μ := gridCoupledLawKernel Δ hΔ K a)
    (measurable_gridIntervalSample Δ 0)
    hFm.stronglyMeasurable
  have hg : Measurable (fun q : Path d × Bool => (stopPathAt Δ q.1, q.2)) :=
    ((measurable_stopPathAt Δ).comp measurable_fst).prodMk measurable_snd
  rw [hfirst, integral_map_of_stronglyMeasurable hg
    (hFm.mul hbit).stronglyMeasurable] at hI
  rw [hfirst, integral_map_of_stronglyMeasurable hg hFm.stronglyMeasurable] at hJ
  have hc (q : Path d × Bool) (hq : q.1 0 = a.1) :
      F (stopPathAt Δ q.1, q.2) = H c := by
    simp [F, c, stopPathAt, hq]
  have hcoin : (∫ q, (if q.2 = true then (1 : ℝ) else 0) ∂K a) = δ := by
    have he := (splitStepKernelOnEnvironments_integral_bit Δ R δ i hR P G hP hminor
      hδ₀ hδ₁ a true (fun _ => 1) measurable_const ⟨1, by simp⟩).2
    have := hP a.2.1 a.2.2 a.1
    have : IsProbabilityMeasure (Renewal.killedBridgeMixture Δ R i P a.1 a.2.1) :=
      Blueprint.sbxS4_killedBridgeMixture_isProbabilityMeasure Δ R δ i P
        a.1 a.2.1 hR hδ₀ (hminor a.2.1 a.2.2 a.1)
    simpa [K, integral_const] using he
  change (∫ z, H z * (if z.2 0 = true then (1 : ℝ) else 0)
      ∂gridCoupledLawKernel Δ hΔ K a) = δ * ∫ z, H z ∂gridCoupledLawKernel Δ hΔ K a
  simp only [Pi.mul_apply, hFz] at hI hJ
  rw [show (∫ q, F (stopPathAt Δ q.1, q.2) * (if q.2 = true then (1 : ℝ) else 0) ∂K a) =
      H c * δ from by
        rw [integral_congr_ae (hs.mono fun q hq => by rw [hc q hq]), integral_const_mul, hcoin]] at hI
  rw [show (∫ q, F (stopPathAt Δ q.1, q.2) ∂K a) = H c from by
        rw [integral_congr_ae (hs.mono fun q hq => hc q hq)]
        simp] at hJ
  change H c * δ = (∫ z, H z * (if z.2 0 = true then (1 : ℝ) else 0)
    ∂gridCoupledLawKernel Δ hΔ K a) at hI
  rw [← hI, ← hJ, mul_comm]

#print axioms splitGridCoupledLawKernel_freshBit_zero

#print axioms splitGridCoupledLawKernel_freshBit_succ

#print axioms extended_splitGridCoupledLawKernel_marginals

#print axioms ae_splitGridCoupledLawKernel_path_eq

#print axioms ae_splitGridCoupledLawKernel_stoppedPath_eq

#print axioms gridCoupledLawKernel_map_stoppedPath
#print axioms splitGridLawKernel_stopped_prefix_recurrence
#print axioms splitGridLawKernel_map_stoppedPath_nextPath_endpoint
#print axioms ae_originalLaw_all_starts
#print axioms map_compProd_fst_comap
#print axioms ae_splitGridLawKernel_stopped_append
#print axioms stopPathAt_eq_append_segment
#print axioms splitGridLawKernel_map_stopped_nextPath_endpoint
#print axioms map_compProd_comap_statistic_ae
#print axioms map_compProd_comap_statistic
#print axioms splitGridLawKernel_map_stopped_nextPath
#print axioms ae_gridPrefixKernel_stopped_restart
#print axioms splitGridPrefix_compProd_nextPath
#print axioms gridStep_split_map_nextPath
#print axioms ae_gridPrefixKernel_restart_environment
#print axioms gridPrefixKernel_compProd_map_nextPath
#print axioms ae_gridPrefixKernel_initial
#print axioms stopPathAt_eq_append_stopped_shift
#print axioms ae_originalLaw_joint_restart
#print axioms appendPaths_stopped_shift
#print axioms stopPathAt_append_stop
#print axioms ae_originalLaw_stopped_append
#print axioms gridState
#print axioms gridStateMeasurableSpace
#print axioms gridHistory
#print axioms gridHistoryStart
#print axioms measurable_gridHistoryStart
#print axioms gridStep
#print axioms gridStep_apply
#print axioms isMarkovKernel_gridStep
#print axioms gridInitialHistory
#print axioms measurable_gridInitialHistory
#print axioms gridHistoryStart_initial
#print axioms gridLawKernel
#print axioms isMarkovKernel_gridLawKernel
#print axioms gridPrefixKernel
#print axioms isMarkovKernel_gridPrefixKernel
#print axioms gridLawKernel_map_prefix
#print axioms gridPrefixKernel_map_truncate
#print axioms gridLawKernel_map_first
#print axioms gridLawKernel_map_prefix_next
#print axioms gridLawKernel_integral_prefix_next
#print axioms gridPairs
#print axioms measurable_gridPairs
#print axioms gridPairLawKernel
#print axioms isMarkovKernel_gridPairLawKernel
#print axioms ae_gridLawKernel_step_starts
#print axioms ae_gridLawKernel_matching
#print axioms splitGridLawKernel
#print axioms isMarkovKernel_splitGridLawKernel
#print axioms splitGridStep_apply
#print axioms splitGridLawKernel_map_first
#print axioms ae_splitStepKernel_starts
#print axioms ae_splitGridLawKernel_matching
#print axioms appendPaths
#print axioms continuous_appendPaths
#print axioms appendPaths_left
#print axioms appendPaths_right
#print axioms finiteConcat
#print axioms continuous_finiteConcat
#print axioms measurable_finiteConcat
#print axioms finiteConcat_succ_left
#print axioms finiteConcat_endpoint
#print axioms finiteConcat_segment
#print axioms finiteConcat_prefix
#print axioms finiteConcat_congr
#print axioms finiteConcat_agree
#print axioms exists_concatIndex
#print axioms concatIndex
#print axioms concatIndex_spec
#print axioms infiniteConcat
#print axioms infiniteConcat_eq_finite
#print axioms measurable_infiniteConcat
#print axioms infiniteConcat_segment
#print axioms infiniteConcat_zero
#print axioms coupledConcat
#print axioms measurable_coupledConcat
#print axioms coupledConcat_stoppedHistory
#print axioms coupledConcat_stoppedHistory_congr
#print axioms gridCoupledLawKernel
#print axioms isMarkovKernel_gridCoupledLawKernel
#print axioms ae_gridLawKernel_concat_segments
#print axioms splitGridCoupledLawKernel
#print axioms isMarkovKernel_splitGridCoupledLawKernel
#print axioms ae_splitGridLawKernel_concat_segments

#print axioms killedBridgeMixture_mass_le_one
#print axioms isFiniteMeasure_killedBridgeMixture
#print axioms integrable_killedBridgeMixture
#print axioms abs_integral_killedBridgeMixture_le
#print axioms killedBridgeMixture_probabilityPart
#print axioms measurable_killedBridge_expectation_probabilityPart
#print axioms measurable_killedBridge_expectation_good
#print axioms measurableSet_probability_fibres
#print axioms exists_measurable_probability_environments
#print axioms measurable_killedBridge_expectation_on_environments
#print axioms measurable_killedBridge_expectation_of_probability

#print axioms boundedRealTest_mul
#print axioms integrable_boundedRealTest
#print axioms integrable_oneInterval_bit
#print axioms integrable_oneInterval_bridge
#print axioms integrable_oneInterval_path
#print axioms integrable_oneInterval_residual

#print axioms oneInterval_integrabilities_of_probability
#print axioms ae_oneInterval_integrabilities_origin
#print axioms ae_oneInterval_integrabilities_product

#print axioms pathKernelOnEnvironments
#print axioms pathKernelOnEnvironments_apply
#print axioms isMarkovKernel_pathKernelOnEnvironments
#print axioms killedSegmentKernelOnEnvironments
#print axioms killedSegmentKernelOnEnvironments_apply
#print axioms killedEndpointKernelOnEnvironments
#print axioms killedEndpointKernelOnEnvironments_apply
#print axioms bridgeKernelOnEnvironments
#print axioms bridgeKernelOnEnvironments_apply
#print axioms isFiniteKernel_bridgeKernelOnEnvironments
#print axioms measurable_bridgeKernelOnEnvironments_integral
#print axioms splitResidualKernel
#print axioms splitResidualKernel_apply
#print axioms isMarkovKernel_splitResidualKernel
#print axioms splitResidualKernel_recovery

#print axioms firstCoinKernel
#print axioms firstCoinKernel_apply
#print axioms isMarkovKernel_firstCoinKernel
#print axioms map_firstCoinKernel_fst
#print axioms measurable_firstCoinKernel_integral
#print axioms firstCoinKernel_integral_bit
#print axioms isMarkovKernel_bridgeKernelOnEnvironments
#print axioms smul_bridgeKernelOnEnvironments_le
#print axioms failedBridgeKernelOnEnvironments
#print axioms failedBridgeKernelOnEnvironments_apply
#print axioms isMarkovKernel_failedBridgeKernelOnEnvironments
#print axioms splitStepKernelOnEnvironments
#print axioms splitStepKernelOnEnvironments_apply
#print axioms isMarkovKernel_splitStepKernelOnEnvironments
#print axioms map_splitStepKernelOnEnvironments_fst

#print axioms bridge_residual_mixture_on_environments
#print axioms splitStepKernelOnEnvironments_integral_bit
#print axioms extendEnvironmentKernel
#print axioms extendEnvironmentKernel_apply_of_mem
#print axioms isMarkovKernel_extendEnvironmentKernel
#print axioms ae_extendEnvironmentKernel_origin
#print axioms ae_extendEnvironmentKernel_product
#print axioms exists_measurable_split_environments

#print axioms exists_splitStepKernel_of_ae_minorization
#print axioms exists_splitStepKernel_of_isGMPReducedKernel

#print axioms gridHistoryPairs
#print axioms measurable_gridHistoryPairs
#print axioms gridStoppedHistory
#print axioms measurable_gridStoppedHistory
#print axioms gridStoppedHistory_restrict
#print axioms gridCoupledLawKernel_apply
#print axioms gridCoupledLawKernel_map_stoppedHistory
#print axioms gridLawKernel_map_stopped_next
#print axioms gridLawKernel_integral_stopped_next
#print axioms gridPrefixKernel_restart
#print axioms gridPrefixKernel_integral_restart
#print axioms gridLawKernel_map_prefix_continuation

#print axioms stopPathAt
#print axioms continuous_stopPathAt
#print axioms measurable_stopPathAt
#print axioms stopPathAt_comp_of_le
#print axioms pathSigma_eq_iSup_stopped
#print axioms measure_eq_of_stoppedPath_marginals
#print axioms gridIntervalSample
#print axioms measurable_gridIntervalSample
#print axioms gridIntervalSample_concat_zero
#print axioms gridCoupledLawKernel_map_firstInterval
#print axioms gridCoupledLawKernel_map_firstPath
#print axioms splitGridCoupledLawKernel_map_firstPath

#print axioms ae_gridLawKernel_intervalSample
#print axioms ae_gridPrefixKernel_stopped_endpoint
#print axioms gridCoupledLawKernel_map_stopped_nextInterval
#print axioms gridCoupledLawKernel_integral_stopped_nextInterval
#print axioms gridCoupledLawKernel_map_stopped_continuation

#print axioms ae_originalLaw_deterministic_restart

#lint

end EinsteinFull.SbxS10BridgeIntegrability
