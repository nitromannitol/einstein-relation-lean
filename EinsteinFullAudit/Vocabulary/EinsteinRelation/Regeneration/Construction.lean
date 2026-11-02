import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Diffusion.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Probability.ProbabilityPart

/-! Vocabulary for `EinsteinRelation.Regeneration.Construction`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

open scoped NNReal ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

abbrev BernoulliSequence := ℕ → Bool

abbrev CoupledSample (d : ℕ) := Path d × BernoulliSequence

abbrev CoupledQuenchedLaws (d : ℕ) :=
  ProbabilityTheory.Kernel (Vec d × FieldPair d) (CoupledSample d)

/-- Source regen.hitting: the empty hitting set has extended infimum infinity. -/
def firstHittingAbove {d : ℕ} (γ : Path d) (i : Fin d) (a : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : a ≤ γ t i - γ 0 i), (t : ℝ≥0∞)

/-- Source regen.D: downward crossings include equality with the level. -/
def firstHittingBelow {d : ℕ} (γ : Path d) (i : Fin d) (a : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : γ t i - γ 0 i ≤ a), (t : ℝ≥0∞)

/-- Source rounding convention: infinity stays infinity. Physical use has Δ>0. -/
def roundUp (Δ : ℝ≥0) (t : ℝ≥0∞) : ℝ≥0∞ :=
  if t = ⊤ then ⊤ else
    (((Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)

/-- This index is used only at finite grid times; source θ shifts by t/Δ bits. -/
def gridIndex (Δ t : ℝ≥0) : ℕ := Nat.floor ((t : ℝ) / (Δ : ℝ))

/-- Time shift retains the absolute starting position in the quenched kernel. -/
def pathTimeShift {d : ℕ} (γ : Path d) (t : ℝ≥0) : Path d :=
  ⟨fun u => γ (t + u), γ.continuous.comp (continuous_const.add continuous_id)⟩

def sampleTimeShift {d : ℕ} (Δ : ℝ≥0) (z : CoupledSample d)
    (t : ℝ≥0) : CoupledSample d :=
  (pathTimeShift z.1 t, fun n => z.2 (gridIndex Δ t + n))

/-- Source M(t), only evaluated at a finite time. Continuity ensures boundedness. -/
def coordinateMaximum {d : ℕ} (γ : Path d) (i : Fin d) (t : ℝ≥0) : ℝ :=
  sSup ((fun u : ℝ≥0 => γ u i - γ 0 i) '' Set.Icc 0 t)

/-- Source V_j(a). Guards prevent evaluating a path at an infinite time. -/
def passageSequence {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ)
    (γ : Path d) (i : Fin d) : ℕ → ℝ≥0∞
  | 0 => firstHittingAbove γ i (a / lam)
  | n + 1 =>
    let t := roundUp Δ (passageSequence Δ lam R a γ i n)
    if t = ⊤ then ⊤ else firstHittingAbove γ i (coordinateMaximum γ i t.toNNReal + R)

/-- The oscillation event used to select the first rounded trial candidate. -/
def IsGoodPassage {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ)
    (γ : Path d) (i : Fin d) (n : ℕ) : Prop :=
  let t := passageSequence Δ lam R a γ i n
  let u := roundUp Δ t
  t ≠ ⊤ ∧ u ≠ ⊤ ∧ ∀ s ∈ Set.Icc t.toNNReal u.toNNReal,
    |γ s i - γ t.toNNReal i| ≤ R / 2

/-- Source Ñ₁(a), the infimum of eligible rounded times. Attainment and its
first-index characterization at positive scales remain internal proof obligations. -/
def firstRoundedCandidate {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ)
    (γ : Path d) (i : Fin d) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (_ : IsGoodPassage Δ lam R a γ i n),
    roundUp Δ (passageSequence Δ lam R a γ i n)

/-- Source Ñ_j(a), indexed here by zero for the paper's j=1. -/
def roundedCandidateSequence {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ)
    (z : CoupledSample d) (i : Fin d) : ℕ → ℝ≥0∞
  | 0 => firstRoundedCandidate Δ lam R a z.1 i
  | n + 1 =>
    let t := roundedCandidateSequence Δ lam R a z i n
    if t = ⊤ then ⊤ else
      t + firstRoundedCandidate Δ lam R (3 * lam * R) (pathTimeShift z.1 t.toNNReal) i

/-- Source N(a): finite candidates with a successful actual Bernoulli bit. -/
def IsSuccessfulCandidate {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ)
    (z : CoupledSample d) (i : Fin d) (n : ℕ) : Prop :=
  let t := roundedCandidateSequence Δ lam R a z i n
  t ≠ ⊤ ∧ z.2 (gridIndex Δ t.toNNReal) = true

def firstSuccessfulCandidate {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ)
    (z : CoupledSample d) (i : Fin d) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (_ : IsSuccessfulCandidate Δ lam R a z i n),
    roundedCandidateSequence Δ lam R a z i n

/-- A trial's first downward hit and rounded failure time, source J_i,R_i. -/
def trialDownwardTime {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (z : CoupledSample d)
    (i : Fin d) (S : ℝ≥0∞) : ℝ≥0∞ :=
  if S = ⊤ then ⊤ else
    S + firstHittingBelow (sampleTimeShift Δ z S.toNNReal).1 i (-R)

def trialFailureTime {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (z : CoupledSample d)
    (i : Fin d) (S : ℝ≥0∞) : ℝ≥0∞ :=
  roundUp Δ (trialDownwardTime Δ R z i S)

/-- Source S_i. Index zero denotes the first trial. Infinite failures propagate. -/
def trialStartSequence {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) : ℕ → ℝ≥0∞
  | 0 => firstSuccessfulCandidate Δ lam R (3 * lam * R) z i + (Δ : ℝ≥0∞)
  | n + 1 =>
    let t := trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n)
    if t = ⊤ then ⊤ else
      let a := lam * (coordinateMaximum z.1 i t.toNNReal -
        (z.1 t.toNNReal i - z.1 0 i) + R)
      t + firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i +
        (Δ : ℝ≥0∞)

/-- Source τ₁ is the infimum of finite full-trial times with infinite failure time. -/
def IsRegenerationTrial {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) (n : ℕ) : Prop :=
  let S := trialStartSequence Δ lam R z i n
  S ≠ ⊤ ∧ trialFailureTime Δ R z i S = ⊤

def firstRegenerationTime {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (_ : IsRegenerationTrial Δ lam R z i n),
    trialStartSequence Δ lam R z i n

def regenerationTime {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) : ℕ → ℝ≥0∞
  | 0 => 0
  | n + 1 =>
    let t := regenerationTime Δ lam R z i n
    if t = ⊤ then ⊤ else
      t + firstRegenerationTime Δ lam R (sampleTimeShift Δ z t.toNNReal) i

/-- Source D, relative to the actual initial point. -/
def NoBacktracking {d : ℕ} (R : ℝ) (γ : Path d) (i : Fin d) : Prop :=
  firstHittingBelow γ i (-R) = ⊤

/-- Exact finite-history sigma: path through nΔ and bits strictly before n. -/
def finiteHistorySigma {d : ℕ} (Δ : ℝ≥0) (n : ℕ) : MeasurableSpace (CoupledSample d) :=
  (⨆ t : Set.Icc 0 ((n : ℝ≥0) * Δ),
    MeasurableSpace.comap (fun z : CoupledSample d => z.1 t) inferInstance) ⊔
  ⨆ k : {k : ℕ // k < n},
    MeasurableSpace.comap (fun z : CoupledSample d => z.2 k) inferInstance

end EinsteinRelation.Regeneration
