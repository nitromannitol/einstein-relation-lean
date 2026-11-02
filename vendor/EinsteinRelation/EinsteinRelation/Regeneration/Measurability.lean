import EinsteinRelation.Regeneration.Construction
import EinsteinRelation.Probability.JointHittingTimes
import EinsteinRelation.Regeneration.Rounding
import EinsteinRelation.Regeneration.MaximumContinuity
import EinsteinRelation.Regeneration.GoodPassageEvents
import EinsteinRelation.Probability.PathMaps
import EinsteinRelation.Probability.BitShift
import EinsteinRelation.Probability.GuardedInfimum

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-! # Measurability of the literal regeneration construction

Source `paper/main.tex:278–340,353–370`. The actual trial and regeneration-time
recursions retain infinity, finite-history and bit-index conventions.
-/
namespace EinsteinRelation.Regeneration

theorem measurable_firstHittingAbove {d : ℕ} (i : Fin d) :
    Measurable (fun p : ℝ × Path d => firstHittingAbove p.2 i p.1) :=
  Probability.measurable_joint_upcrossing_inf i

theorem measurable_firstHittingBelow {d : ℕ} (i : Fin d) :
    Measurable (fun p : ℝ × Path d => firstHittingBelow p.2 i p.1) :=
  Probability.measurable_joint_downcrossing_inf i

theorem measurable_roundUp (Δ : ℝ≥0) : Measurable (roundUp Δ) := by
  have heq : roundUp Δ = (fun t : ℝ≥0∞ => @ite ℝ≥0∞ (t = ⊤) (LinearOrder.toDecidableEq t ⊤) ⊤
      (((Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) := by
    funext t
    unfold roundUp
    by_cases ht : t = ⊤
    · simp only [ht, if_pos]
    · simp only [ht]
  rw [heq]
  exact Regeneration.measurable_extended_grid_rounding Δ

theorem measurable_coordinateMaximum {d : ℕ} (i : Fin d) :
    Measurable (fun p : ℝ≥0 × Path d => coordinateMaximum p.2 i p.1) :=
  (Regeneration.continuous_coordinate_maximum i).measurable

attribute [local irreducible] firstHittingAbove firstHittingBelow coordinateMaximum roundUp

theorem measurable_passageSequence_joint {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (n : ℕ) :
    Measurable (fun p : ℝ × Path d => passageSequence Δ lam R p.1 p.2 i n) := by
  induction n with
  | zero =>
      exact (measurable_firstHittingAbove i).comp
        ((measurable_fst.div_const lam).prodMk measurable_snd)
  | succ n ih =>
      have ht : Measurable (fun p : ℝ × Path d =>
          roundUp Δ (passageSequence Δ lam R p.1 p.2 i n)) :=
        (measurable_roundUp Δ).comp ih
      have hM : Measurable (fun p : ℝ × Path d => coordinateMaximum p.2 i
          (roundUp Δ (passageSequence Δ lam R p.1 p.2 i n)).toNNReal) :=
        (measurable_coordinateMaximum i).comp
          (ht.ennreal_toNNReal.prodMk measurable_snd)
      have hhit : Measurable (fun p : ℝ × Path d => firstHittingAbove p.2 i
          (coordinateMaximum p.2 i
            (roundUp Δ (passageSequence Δ lam R p.1 p.2 i n)).toNNReal + R)) :=
        (measurable_firstHittingAbove i).comp ((hM.add_const R).prodMk measurable_snd)
      change Measurable (fun p : ℝ × Path d => if
        roundUp Δ (passageSequence Δ lam R p.1 p.2 i n) = ⊤ then ⊤ else
        firstHittingAbove p.2 i
          (coordinateMaximum p.2 i
            (roundUp Δ (passageSequence Δ lam R p.1 p.2 i n)).toNNReal + R))
      exact Measurable.ite (measurableSet_eq_fun ht measurable_const) measurable_const hhit

attribute [local irreducible] passageSequence

/-- The universal interval condition retains its literal vacuous meaning when
its lower endpoint exceeds the upper endpoint. -/
private theorem measurableSet_interval_oscillation {d : ℕ} (i : Fin d) (R : ℝ) :
    MeasurableSet {p : (ℝ≥0 × ℝ≥0) × Path d |
      ∀ u ∈ Set.Icc p.1.1 p.1.2, |p.2 u i - p.2 p.1.1 i| ≤ R / 2} := by
  have heq : {p : (ℝ≥0 × ℝ≥0) × Path d |
      ∀ u ∈ Set.Icc p.1.1 p.1.2, |p.2 u i - p.2 p.1.1 i| ≤ R / 2} =
      {p | p.1.2 < p.1.1} ∪ {p | p.1.1 ≤ p.1.2 ∧
        ∀ u ∈ Set.Icc p.1.1 p.1.2, |p.2 u i - p.2 p.1.1 i| ≤ R / 2} := by
    ext p
    constructor
    · intro h
      rcases lt_or_ge p.1.2 p.1.1 with hlt | hle
      · exact Or.inl hlt
      · exact Or.inr ⟨hle, h⟩
    · rintro (hlt | ⟨_, h⟩)
      · intro u hu
        exact False.elim ((not_le_of_gt hlt) (hu.1.trans hu.2))
      · exact h
  rw [heq]
  exact (measurableSet_lt measurable_fst.snd measurable_fst.fst).union
    (Regeneration.isClosed_good_passage_interval i R).measurableSet

theorem measurableSet_IsGoodPassage {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (n : ℕ) :
    MeasurableSet {p : ℝ × Path d | IsGoodPassage Δ lam R p.1 p.2 i n} := by
  have ht := measurable_passageSequence_joint Δ lam R i n
  have hu := (measurable_roundUp Δ).comp ht
  have hobs : Measurable (fun p : ℝ × Path d =>
      (((passageSequence Δ lam R p.1 p.2 i n).toNNReal,
        (roundUp Δ (passageSequence Δ lam R p.1 p.2 i n)).toNNReal), p.2)) :=
    (ht.ennreal_toNNReal.prodMk hu.ennreal_toNNReal).prodMk measurable_snd
  have htop : Measurable (fun _ : ℝ × Path d => (⊤ : ℝ≥0∞)) := measurable_const
  exact (measurableSet_eq_fun ht htop).compl.inter
    ((measurableSet_eq_fun hu htop).compl.inter
      (hobs (measurableSet_interval_oscillation i R)))

attribute [local irreducible] IsGoodPassage

theorem measurable_sampleTimeShift {d : ℕ} (Δ : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × CoupledSample d => sampleTimeShift Δ p.2 p.1) := by
  have hpath : Measurable (fun p : ℝ≥0 × CoupledSample d =>
      pathTimeShift p.2.1 p.1) :=
    Probability.continuous_path_time_shift.measurable.comp
      (measurable_fst.prodMk measurable_snd.fst)
  have hbits : Measurable (fun p : ℝ≥0 × CoupledSample d =>
      fun n => p.2.2 (gridIndex Δ p.1 + n)) :=
    (Probability.measurable_time_indexed_bit_shift Δ).comp
      (measurable_fst.prodMk measurable_snd.snd)
  exact hpath.prodMk hbits

attribute [local irreducible] sampleTimeShift

theorem measurable_trialDownwardTime {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) :
    Measurable (fun p : ℝ≥0∞ × CoupledSample d => trialDownwardTime Δ R p.2 i p.1) := by
  have hshift : Measurable (fun p : ℝ≥0∞ × CoupledSample d =>
      sampleTimeShift Δ p.2 p.1.toNNReal) :=
    (measurable_sampleTimeShift Δ).comp
      (ENNReal.measurable_toNNReal.comp measurable_fst |>.prodMk measurable_snd)
  have hhit : Measurable (fun p : ℝ≥0∞ × CoupledSample d =>
      firstHittingBelow (sampleTimeShift Δ p.2 p.1.toNNReal).1 i (-R)) :=
    (measurable_firstHittingBelow i).comp (measurable_const.prodMk hshift.fst)
  change Measurable (fun p : ℝ≥0∞ × CoupledSample d => if p.1 = ⊤ then ⊤ else
    p.1 + firstHittingBelow (sampleTimeShift Δ p.2 p.1.toNNReal).1 i (-R))
  exact Measurable.ite (measurableSet_eq_fun measurable_fst
    (measurable_const : Measurable (fun _ : ℝ≥0∞ × CoupledSample d => (⊤ : ℝ≥0∞))))
      measurable_const (measurable_fst.add hhit)

attribute [local irreducible] trialDownwardTime

theorem measurable_trialFailureTime {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) :
    Measurable (fun p : ℝ≥0∞ × CoupledSample d => trialFailureTime Δ R p.2 i p.1) :=
  (measurable_roundUp Δ).comp (measurable_trialDownwardTime Δ R i)

theorem measurableSet_NoBacktracking {d : ℕ} (R : ℝ) (i : Fin d) :
    MeasurableSet {γ : Path d | NoBacktracking R γ i} :=
  measurableSet_eq_fun
    ((measurable_firstHittingBelow i).comp (measurable_const.prodMk measurable_id))
    (measurable_const : Measurable (fun _ : Path d => (⊤ : ℝ≥0∞)))

theorem measurable_firstRoundedCandidate {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) :
    Measurable (fun p : ℝ × Path d => firstRoundedCandidate Δ lam R p.1 p.2 i) := by
  exact Probability.measurable_guarded_nat_iInf (Ω := ℝ × Path d)
    (fun n p => roundUp Δ (passageSequence Δ lam R p.1 p.2 i n))
    (fun n p => IsGoodPassage Δ lam R p.1 p.2 i n)
    (fun n => (measurable_roundUp Δ).comp (measurable_passageSequence_joint Δ lam R i n))
    (measurableSet_IsGoodPassage Δ lam R i)

attribute [local irreducible] firstRoundedCandidate

theorem measurable_roundedCandidateSequence {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (n : ℕ) : Measurable (fun p : ℝ × CoupledSample d =>
      roundedCandidateSequence Δ lam R p.1 p.2 i n) := by
  induction n with
  | zero =>
      exact (measurable_firstRoundedCandidate Δ lam R i).comp
        (measurable_fst.prodMk measurable_snd.fst)
  | succ n ih =>
      have hshift : Measurable (fun p : ℝ × CoupledSample d =>
          pathTimeShift p.2.1 (roundedCandidateSequence Δ lam R p.1 p.2 i n).toNNReal) :=
        Probability.continuous_path_time_shift.measurable.comp
          (ih.ennreal_toNNReal.prodMk measurable_snd.fst)
      have hnext : Measurable (fun p : ℝ × CoupledSample d =>
          firstRoundedCandidate Δ lam R (3 * lam * R)
            (pathTimeShift p.2.1 (roundedCandidateSequence Δ lam R p.1 p.2 i n).toNNReal) i) :=
        (measurable_firstRoundedCandidate Δ lam R i).comp
          (measurable_const.prodMk hshift)
      change Measurable (fun p : ℝ × CoupledSample d =>
        if roundedCandidateSequence Δ lam R p.1 p.2 i n = ⊤ then ⊤ else
          roundedCandidateSequence Δ lam R p.1 p.2 i n +
            firstRoundedCandidate Δ lam R (3 * lam * R)
              (pathTimeShift p.2.1 (roundedCandidateSequence Δ lam R p.1 p.2 i n).toNNReal) i)
      exact Measurable.ite (measurableSet_eq_fun ih
        (measurable_const : Measurable (fun _ : ℝ × CoupledSample d => (⊤ : ℝ≥0∞))))
          measurable_const (ih.add hnext)

attribute [local irreducible] roundedCandidateSequence

theorem measurableSet_IsSuccessfulCandidate {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (n : ℕ) :
    MeasurableSet {p : ℝ × CoupledSample d | IsSuccessfulCandidate Δ lam R p.1 p.2 i n} := by
  have ht := measurable_roundedCandidateSequence Δ lam R i n
  have hb : Measurable (fun p : ℝ × CoupledSample d =>
      p.2.2 (gridIndex Δ (roundedCandidateSequence Δ lam R p.1 p.2 i n).toNNReal)) := by
    have hbits := (Probability.measurable_time_indexed_bit_shift Δ).comp
      (ht.ennreal_toNNReal.prodMk measurable_snd.snd)
    simpa only [gridIndex, Nat.add_zero, Function.comp_def] using
      (measurable_pi_apply 0).comp hbits
  exact (measurableSet_eq_fun ht
    (measurable_const : Measurable (fun _ : ℝ × CoupledSample d => (⊤ : ℝ≥0∞)))).compl.inter
      (measurableSet_eq_fun hb
        (measurable_const : Measurable (fun _ : ℝ × CoupledSample d => true)))

attribute [local irreducible] IsSuccessfulCandidate

theorem measurable_firstSuccessfulCandidate {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) :
    Measurable (fun p : ℝ × CoupledSample d => firstSuccessfulCandidate Δ lam R p.1 p.2 i) :=
  Probability.measurable_guarded_nat_iInf (Ω := ℝ × CoupledSample d)
    (fun n p => roundedCandidateSequence Δ lam R p.1 p.2 i n)
    (fun n p => IsSuccessfulCandidate Δ lam R p.1 p.2 i n)
    (measurable_roundedCandidateSequence Δ lam R i)
    (measurableSet_IsSuccessfulCandidate Δ lam R i)

attribute [local irreducible] firstSuccessfulCandidate trialFailureTime

theorem measurable_trialStartSequence {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (n : ℕ) :
    Measurable (fun z : CoupledSample d => trialStartSequence Δ lam R z i n) := by
  induction n with
  | zero =>
      exact ((measurable_firstSuccessfulCandidate Δ lam R i).comp
        (measurable_const.prodMk measurable_id)).add_const (Δ : ℝ≥0∞)
  | succ n ih =>
      let t : CoupledSample d → ℝ≥0∞ := fun z =>
        trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n)
      have ht : Measurable t := (measurable_trialFailureTime Δ R i).comp
        (ih.prodMk measurable_id)
      have hM : Measurable (fun z : CoupledSample d => coordinateMaximum z.1 i (t z).toNNReal) :=
        (measurable_coordinateMaximum i).comp
          (ht.ennreal_toNNReal.prodMk measurable_fst)
      have hcoord : Continuous (fun p : ℝ≥0 × Path d => p.2 p.1 i) :=
        (continuous_apply i).comp (continuous_snd.eval continuous_fst)
      have hcurrent : Measurable (fun z : CoupledSample d => z.1 (t z).toNNReal i) :=
        hcoord.measurable.comp (ht.ennreal_toNNReal.prodMk measurable_fst)
      have hzero : Measurable (fun z : CoupledSample d => z.1 0 i) :=
        hcoord.measurable.comp (measurable_const.prodMk measurable_fst)
      have ha : Measurable (fun z : CoupledSample d =>
          lam * (coordinateMaximum z.1 i (t z).toNNReal -
            (z.1 (t z).toNNReal i - z.1 0 i) + R)) :=
        (hM.sub (hcurrent.sub hzero) |>.add_const R).const_mul lam
      have hshift : Measurable (fun z : CoupledSample d => sampleTimeShift Δ z (t z).toNNReal) :=
        (measurable_sampleTimeShift Δ).comp (ht.ennreal_toNNReal.prodMk measurable_id)
      have hnext : Measurable (fun z : CoupledSample d =>
          firstSuccessfulCandidate Δ lam R
            (lam * (coordinateMaximum z.1 i (t z).toNNReal -
              (z.1 (t z).toNNReal i - z.1 0 i) + R))
            (sampleTimeShift Δ z (t z).toNNReal) i) :=
        (measurable_firstSuccessfulCandidate Δ lam R i).comp (ha.prodMk hshift)
      change Measurable (fun z : CoupledSample d => if t z = ⊤ then ⊤ else
        t z + firstSuccessfulCandidate Δ lam R
          (lam * (coordinateMaximum z.1 i (t z).toNNReal -
            (z.1 (t z).toNNReal i - z.1 0 i) + R))
          (sampleTimeShift Δ z (t z).toNNReal) i + (Δ : ℝ≥0∞))
      exact Measurable.ite (measurableSet_eq_fun ht
        (measurable_const : Measurable (fun _ : CoupledSample d => (⊤ : ℝ≥0∞))))
          measurable_const ((ht.add hnext).add_const (Δ : ℝ≥0∞))

attribute [local irreducible] trialStartSequence

theorem measurableSet_IsRegenerationTrial {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (n : ℕ) :
    MeasurableSet {z : CoupledSample d | IsRegenerationTrial Δ lam R z i n} := by
  have hS := measurable_trialStartSequence Δ lam R i n
  have hJ := (measurable_trialFailureTime Δ R i).comp (hS.prodMk measurable_id)
  have htop : Measurable (fun _ : CoupledSample d => (⊤ : ℝ≥0∞)) := measurable_const
  exact (measurableSet_eq_fun hS htop).compl.inter (measurableSet_eq_fun hJ htop)

attribute [local irreducible] IsRegenerationTrial

theorem measurable_firstRegenerationTime {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) :
    Measurable (fun z : CoupledSample d => firstRegenerationTime Δ lam R z i) :=
  Probability.measurable_guarded_nat_iInf (Ω := CoupledSample d)
    (fun n z => trialStartSequence Δ lam R z i n)
    (fun n z => IsRegenerationTrial Δ lam R z i n)
    (measurable_trialStartSequence Δ lam R i)
    (measurableSet_IsRegenerationTrial Δ lam R i)

attribute [local irreducible] firstRegenerationTime

theorem measurable_regenerationTime {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (n : ℕ) :
    Measurable (fun z : CoupledSample d => regenerationTime Δ lam R z i n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hshift : Measurable (fun z : CoupledSample d =>
          sampleTimeShift Δ z (regenerationTime Δ lam R z i n).toNNReal) :=
        (measurable_sampleTimeShift Δ).comp (ih.ennreal_toNNReal.prodMk measurable_id)
      have hnext := (measurable_firstRegenerationTime Δ lam R i).comp hshift
      change Measurable (fun z : CoupledSample d =>
        if regenerationTime Δ lam R z i n = ⊤ then ⊤ else
          regenerationTime Δ lam R z i n +
            firstRegenerationTime Δ lam R
              (sampleTimeShift Δ z (regenerationTime Δ lam R z i n).toNNReal) i)
      exact Measurable.ite (measurableSet_eq_fun ih
        (measurable_const : Measurable (fun _ : CoupledSample d => (⊤ : ℝ≥0∞))))
          measurable_const (ih.add hnext)

end EinsteinRelation.Regeneration
