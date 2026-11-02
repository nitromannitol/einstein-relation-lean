import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Environment.CoefficientRestriction
import EinsteinRelation.Probability.ReductionLocality
import EinsteinRelation.Probability.ProbabilityPart
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # The literal regeneration-time construction

The definitions below translate the actual
path/Bernoulli construction in paper/main.tex:265–340. The environment argument
is physical; the future record explicitly evaluates reduce ω. No regeneration,
renewal, occupation, or tail conclusion is assumed here.
-/

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

abbrev FutureHalfSpace (d : ℕ) (i : Fin d) (R : ℝ) := {x : Vec d // -2 * R ≤ x i}
abbrev FutureState (d : ℕ) (i : Fin d) (R : ℝ) :=
  Path d × BernoulliSequence × (FutureHalfSpace d i R → Mat d × ℝ)

/-- Source Y_k record at a finite time. The environment argument is PHYSICAL. -/
def futureRecord {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (ω : FieldPair d)
    (z : CoupledSample d) (i : Fin d) (t : ℝ≥0) : FutureState d i R :=
  (⟨fun u => z.1 (t + u) - z.1 t,
      (z.1.continuous.comp (continuous_const.add continuous_id)).sub continuous_const⟩,
    (sampleTimeShift Δ z t).2,
    fun x => ((translate (z.1 t) (reduce ω)).1 x, (translate (z.1 t) (reduce ω)).2 x))

/-- Every past coordinate displacement is bounded by the actual finite maximum. -/
theorem displacement_le_coordinateMaximum {d : ℕ} (γ : Path d) (i : Fin d)
    (s t : ℝ≥0) (hst : s ≤ t) :
    γ s i - γ 0 i ≤ coordinateMaximum γ i t := by
  have hc : Continuous (fun u : ℝ≥0 => γ u i - γ 0 i) :=
    ((continuous_apply i).comp γ.continuous).sub continuous_const
  have hcompact : IsCompact ((fun u : ℝ≥0 => γ u i - γ 0 i) '' Set.Icc 0 t) :=
    isCompact_Icc.image hc
  exact le_csSup hcompact.bddAbove ⟨s, ⟨zero_le, hst⟩, rfl⟩

/-- The initial point is among the finite maximum's observations. -/
theorem coordinateMaximum_nonneg {d : ℕ} (γ : Path d) (i : Fin d) (t : ℝ≥0) :
    0 ≤ coordinateMaximum γ i t := by
  simpa using displacement_le_coordinateMaximum γ i 0 t zero_le

/-- A literal upper bound for the displacements bounds the source maximum. -/
theorem coordinateMaximum_le {d : ℕ} (γ : Path d) (i : Fin d) (t : ℝ≥0)
    (M : ℝ) (hM : ∀ s ∈ Set.Icc 0 t, γ s i - γ 0 i ≤ M) :
    coordinateMaximum γ i t ≤ M := by
  apply csSup_le
  · exact ⟨γ 0 i - γ 0 i, ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact hM s hs

/-- At a positive grid spacing the bit index of nΔ is exactly n. -/
theorem gridIndex_mul (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ) :
    gridIndex Δ ((n : ℝ≥0) * Δ) = n := by
  have hne : (Δ : ℝ) ≠ 0 := ne_of_gt hΔ
  simp [gridIndex, hne]

/-- Rounding leaves each positive-grid multiple unchanged, including time zero. -/
theorem roundUp_gridTime (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ) :
    roundUp Δ (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) =
      (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  have hne : (Δ : ℝ) ≠ 0 := ne_of_gt hΔ
  rw [roundUp, if_neg ENNReal.coe_ne_top]
  simp [hne]

/-- Exact lower-bound characterization of the first rounded TIME. -/
theorem le_firstRoundedCandidate_iff {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ)
    (γ : Path d) (i : Fin d) (t : ℝ≥0∞) :
    t ≤ firstRoundedCandidate Δ lam R a γ i ↔
      ∀ n, IsGoodPassage Δ lam R a γ i n →
        t ≤ roundUp Δ (passageSequence Δ lam R a γ i n) := by
  simp only [firstRoundedCandidate, le_iInf_iff]

/-- The infimum of eligible rounded times is attained on a positive grid.
This proves the first-TIME meaning without assuming candidate chronology. -/
theorem firstRoundedCandidate_attained {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (γ : Path d) (i : Fin d)
    (hexists : ∃ n, IsGoodPassage Δ lam R a γ i n) :
    ∃ n, IsGoodPassage Δ lam R a γ i n ∧
      firstRoundedCandidate Δ lam R a γ i =
        roundUp Δ (passageSequence Δ lam R a γ i n) := by
  let idx : ℕ → ℕ := fun n =>
    Nat.ceil ((passageSequence Δ lam R a γ i n).toReal / (Δ : ℝ))
  have hex : ∃ k : ℕ, ∃ n, IsGoodPassage Δ lam R a γ i n ∧ idx n = k := by
    obtain ⟨n, hn⟩ := hexists
    exact ⟨idx n, n, hn, rfl⟩
  obtain ⟨n, hn, hidx⟩ := Nat.find_spec hex
  refine ⟨n, hn, le_antisymm ?_ ?_⟩
  · exact iInf_le_of_le n (iInf_le_of_le hn le_rfl)
  · unfold firstRoundedCandidate
    refine le_iInf fun m => le_iInf fun hm => ?_
    have hnfin : passageSequence Δ lam R a γ i n ≠ ⊤ := hn.1
    have hmfin : passageSequence Δ lam R a γ i m ≠ ⊤ := hm.1
    have hmin : idx n ≤ idx m := by
      rw [hidx]
      exact Nat.find_min' hex ⟨m, hm, rfl⟩
    simp only [roundUp, if_neg hnfin, if_neg hmfin]
    apply ENNReal.coe_le_coe.mpr
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmin) hΔ.le

/-- A real first consumer of the extended hitting-time definition. -/
theorem firstHittingAbove_le_of_crossing {d : ℕ} (γ : Path d) (i : Fin d)
    (a : ℝ) (t : ℝ≥0) (h : a ≤ γ t i - γ 0 i) :
    firstHittingAbove γ i a ≤ (t : ℝ≥0∞) :=
  iInf_le_of_le t (iInf_le_of_le h le_rfl)

theorem firstHittingBelow_le_of_crossing {d : ℕ} (γ : Path d) (i : Fin d)
    (a : ℝ) (t : ℝ≥0) (h : γ t i - γ 0 i ≤ a) :
    firstHittingBelow γ i a ≤ (t : ℝ≥0∞) :=
  iInf_le_of_le t (iInf_le_of_le h le_rfl)

/-- The future path really is recentered at zero, as in source regen.future. -/
theorem futureRecord_path_zero {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (ω : FieldPair d)
    (z : CoupledSample d) (i : Fin d) (t : ℝ≥0) :
    (futureRecord Δ R ω z i t).1 0 = 0 := by
  simp [futureRecord]

/-- The finite-time future record is measurable for its literal product sigma
algebra, including every reduced environment observation in the future halfspace. -/
theorem measurable_futureRecord {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (t : ℝ≥0) :
    Measurable (fun p : FieldPair d × CoupledSample d => futureRecord Δ R p.1 p.2 i t) := by
  have hpath : Continuous (fun γ : Path d =>
      (⟨fun u => γ (t + u) - γ t,
        (γ.continuous.comp (continuous_const.add continuous_id)).sub continuous_const⟩ : Path d)) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_fst.eval (continuous_const.add continuous_snd)).sub
      (continuous_fst.eval continuous_const)
  have hbits : Measurable (fun p : FieldPair d × CoupledSample d =>
      (futureRecord Δ R p.1 p.2 i t).2.1) := by
    apply measurable_pi_iff.mpr
    intro n
    exact (measurable_pi_apply (gridIndex Δ t + n)).comp measurable_snd.snd
  have henv : Measurable (fun p : FieldPair d × CoupledSample d =>
      translate (p.2.1 t) (reduce p.1)) :=
    Probability.continuous_translate.measurable.comp
      ((((continuous_eval_const t).measurable).comp measurable_snd.fst).prodMk
        (Probability.measurable_reduce.comp measurable_fst))
  have hfield : Measurable (fun p : FieldPair d × CoupledSample d =>
      (futureRecord Δ R p.1 p.2 i t).2.2) := by
    apply measurable_pi_iff.mpr
    intro x
    have heval : Continuous (fun ω : FieldPair d => (ω.1 (x : Vec d), ω.2 (x : Vec d))) :=
      (continuous_fst.eval continuous_const).prodMk (continuous_snd.eval continuous_const)
    exact heval.measurable.comp henv
  exact (hpath.measurable.comp measurable_snd.fst).prodMk (hbits.prodMk hfield)

end EinsteinRelation.Regeneration
