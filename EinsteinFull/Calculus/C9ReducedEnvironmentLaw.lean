import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ReducedEnvironment
import EinsteinRelation.Calculus.Generator
import EinsteinRelation.Diffusion.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # The environment law of the reduced coefficient with zero potential

The map below is literally `(a₀,V) ↦ (exp(-2V) a₀,0)`. Its pushforward
reuses the proved joint-law construction for `zeroPotentialReducedPair`.
The physical generator on this pair is the original reduced generator,
for every signed force. Identifying supplied path kernels is a separate step.
-/

open MeasureTheory
open scoped Topology NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The actual reduced matrix coefficient, with identically zero potential. -/
noncomputable def flatReducedEnvironment {d : ℕ} (ω : FieldPair d) : FieldPair d :=
  ((reduce ω).1, 0)

/-- This is the existing zero-potential coefficient pair, on the same carrier. -/
theorem flatReducedEnvironment_eq_zeroPotentialReducedPair {d : ℕ} (ω : FieldPair d) :
    flatReducedEnvironment ω = zeroPotentialReducedPair ω := rfl

/-- The actual reduction is continuous for the compact-open field topology. -/
theorem continuous_flatReducedEnvironment {d : ℕ} :
    Continuous (flatReducedEnvironment (d := d)) :=
  Blueprint.coupling_scope_continuous_zeroPotentialReducedPair

/-- The pushed-forward environment law uses a measurable coefficient map. -/
theorem measurable_flatReducedEnvironment {d : ℕ} :
    Measurable (flatReducedEnvironment (d := d)) :=
  continuous_flatReducedEnvironment.measurable

/-- The zero-potential coefficient pair retains the source reduced bound. -/
theorem flatReducedEnvironment_regular {d : ℕ} {L : ℝ} (hL : 1 ≤ L)
    {ω : FieldPair d} (hω : IsRegular L ω) :
    IsRegular (sourceReducedBound L) (flatReducedEnvironment ω) :=
  isRegular_zeroPotentialReducedPair hL hω

/-- The transformation commutes with spatial translation. -/
theorem flatReducedEnvironment_translate {d : ℕ} (x : Vec d) (ω : FieldPair d) :
    flatReducedEnvironment (translate x ω) = translate x (flatReducedEnvironment ω) :=
  Blueprint.coupling_scope_zeroPotentialReducedPair_translate x ω

/-- Joint observations on a set depend only on the original pair on that set. -/
theorem localSigma_flatReducedEnvironment_comap_le {d : ℕ} (U : Set (Vec d)) :
    (localSigma U).comap (flatReducedEnvironment (d := d)) ≤ localSigma U :=
  Blueprint.coupling_scope_localSigma_zeroPotentialReducedPair_comap_le U

/-- The actual pushed-forward joint law has the same finite-range radius and
the regularity bound determined solely by the original coefficient bound. -/
noncomputable def flatReducedEnvironmentLaw {d : ℕ} {L r : ℝ}
    (Q : EnvironmentLaw d L r) : EnvironmentLaw d (sourceReducedBound L) r :=
  Blueprint.couplingScopeReducedEnvironmentLaw Q

/-- The measure is the literal pushforward of the supplied environment law. -/
theorem flatReducedEnvironmentLaw_measure {d : ℕ} {L r : ℝ}
    (Q : EnvironmentLaw d L r) :
    (flatReducedEnvironmentLaw Q).measure = Q.measure.map flatReducedEnvironment := rfl

/-- Measurable predicates transport through the actual environment map. -/
theorem flatReducedEnvironmentLaw_ae_iff {d : ℕ} {L r : ℝ}
    (Q : EnvironmentLaw d L r) {p : FieldPair d → Prop}
    (hp : MeasurableSet {ω | p ω}) :
    (∀ᵐ ω ∂(flatReducedEnvironmentLaw Q).measure, p ω) ↔
      ∀ᵐ ω ∂Q.measure, p (flatReducedEnvironment ω) :=
  ae_map_iff measurable_flatReducedEnvironment.aemeasurable hp

/-- Reducing the zero-potential pair leaves the original reduced coefficient. -/
theorem reducedCoefficient_flatReducedEnvironment {d : ℕ} (ω : FieldPair d)
    (x : Vec d) :
    reducedCoefficient (flatReducedEnvironment ω) x = reducedCoefficient ω x :=
  reducedCoefficient_zeroPotentialReducedPair ω x

/-- The physical generator on the actual flat pair is exactly the original
reduced generator, with no restriction on the signed force. -/
theorem physicalGenerator_flatReducedEnvironment {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (lam : ℝ) (f : Vec d → ℝ) (x : Vec d) :
    physicalGenerator i (flatReducedEnvironment ω) lam f x =
      reducedGenerator i ω lam f x := by
  simp only [physicalGenerator, reducedGenerator, reducedCoefficient_flatReducedEnvironment]
  change (Real.exp (2 * (0 : ℝ)) / 2) * _ + _ = _
  rw [mul_zero, Real.exp_zero]
  rfl

/-- Pull back a supplied flat-environment velocity through the actual
almost-everywhere identity of path laws. The measurable function `K` is bundled
as a kernel using precisely its supplied measurability proof. -/
theorem velocity_of_flat_environment_law {d : ℕ} {L r : ℝ}
    (Q : EnvironmentLaw d L r) (Y : QuenchedPathLaws d)
    (K : FieldPair d → Measure (Path d)) (v : Vec d)
    (hK : Measurable K)
    (hid : ∀ᵐ ω ∂Q.measure, originLaw Y ω = K (flatReducedEnvironment ω))
    (hv : HasQuenchedVelocity (flatReducedEnvironmentLaw Q).measure
      (ProbabilityTheory.Kernel.mk K hK) v) :
    HasQuenchedVelocity Q.measure (originLaw Y) v := by
  have hflat : ∀ᵐ ω ∂Q.measure,
      ∀ᵐ γ ∂K (flatReducedEnvironment ω), HasPathVelocity γ v :=
    ae_of_ae_map measurable_flatReducedEnvironment.aemeasurable hv
  filter_upwards [hid, hflat] with ω hω hvelocity
  rw [hω]
  exact hvelocity

/-- The full continuous-time velocity event is jointly Borel in the path and
candidate velocity. Each uniform tail bound is an arbitrary intersection of
closed fixed-time bounds; only the filter and neighborhood bases are countable. -/
theorem measurableSet_joint_path_velocity {d : ℕ} :
    MeasurableSet {p : Path d × Vec d | Filter.Tendsto
      (fun t : ℝ≥0 => (t : ℝ)⁻¹ • p.1 t) Filter.atTop (𝓝 p.2)} := by
  obtain ⟨u, hu⟩ := (Filter.atTop : Filter ℝ≥0).exists_antitone_basis
  let S : ℕ → ℕ → Set (Path d × Vec d) := fun n N =>
    {p | ∀ t ∈ u N, dist ((t : ℝ)⁻¹ • p.1 t) p.2 ≤ 1 / ((n : ℝ) + 1)}
  have hclosed (n N : ℕ) : IsClosed (S n N) := by
    simp only [S, Set.ofPred_forall]
    refine isClosed_iInter fun t => isClosed_iInter fun _ht => ?_
    have heval : Continuous (fun p : Path d × Vec d => p.1 t) :=
      (continuous_eval_const t).comp continuous_fst
    have hscaled : Continuous (fun p : Path d × Vec d => (t : ℝ)⁻¹ • p.1 t) :=
      heval.const_smul ((t : ℝ)⁻¹)
    exact isClosed_le (hscaled.dist continuous_snd) continuous_const
  have hmeas : MeasurableSet (⋂ n : ℕ, ⋃ N : ℕ, S n N) :=
    MeasurableSet.iInter fun n => MeasurableSet.iUnion fun N =>
      (hclosed n N).measurableSet
  convert hmeas using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
  simpa only [S, Set.mem_ofPred_eq, true_imp_iff, true_and, Metric.mem_closedBall] using
    (hu.toHasBasis.tendsto_iff (f := fun t : ℝ≥0 => (t : ℝ)⁻¹ • p.1 t)
      (Metric.nhds_basis_closedBall_inv_nat_succ (x := p.2)))

/-- For a supplied s-finite path kernel, the probability of a continuous-time
velocity event is measurable jointly in the environment and candidate velocity. -/
theorem measurable_kernel_path_velocity {d : ℕ} {E : Type*} [MeasurableSpace E]
    (K : ProbabilityTheory.Kernel E (Path d)) [ProbabilityTheory.IsSFiniteKernel K] :
    Measurable (fun p : E × Vec d => K p.1 {γ : Path d | Filter.Tendsto
      (fun t : ℝ≥0 => (t : ℝ)⁻¹ • γ t) Filter.atTop (𝓝 p.2)}) := by
  have hevent : MeasurableSet {p : (E × Vec d) × Path d | Filter.Tendsto
      (fun t : ℝ≥0 => (t : ℝ)⁻¹ • p.2 t) Filter.atTop (𝓝 p.1.2)} :=
    measurableSet_joint_path_velocity.preimage
      (measurable_snd.prodMk measurable_fst.snd)
  exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left
    (κ := K.comap Prod.fst measurable_fst) hevent

end EinsteinFull
