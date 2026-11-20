import EinsteinFull.Regeneration.CoupledCandidateMoment
import EinsteinFull.Regeneration.TrialFailureFactor
import EinsteinRelation.Regeneration.TrialPrefix
import EinsteinRelation.Regeneration.LastBit
import EinsteinRelation.Regeneration.TrialGeometry
import EinsteinRelation.Regeneration.TrialBounds
import EinsteinRelation.Regeneration.RegenerationGrid

/-!
# One step of the regeneration trials

The exponential height of the next trial start is the exponential of the running
maximum at the failure time, plus one slab, times the exponential overshoot of the
candidate search started at the failure time. The exponential of the running maximum
at the failure time is at most the exponential height of the current trial start
times the failure weight of the path after the start, when the path before the start
stays within `12R` of the start.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

attribute [local irreducible] firstRoundedCandidate roundedCandidateSequence passageSequence
  firstSuccessfulCandidate

/-- Rounding commutes with a shift by a grid time. -/
theorem roundUp_grid_add (Δ : ℝ≥0) (hΔ : 0 < Δ) (k : ℕ) (t : ℝ≥0∞) :
    roundUp Δ ((((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) + t) =
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) + roundUp Δ t := by
  by_cases ht : t = ⊤
  · rw [ht, add_top]
    simp [roundUp]
  · have hsum : (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) + t ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ht⟩
    rw [roundUp, ite_eq_right hsum, roundUp, ite_eq_right ht, ← ENNReal.coe_add]
    congr 1
    have hΔR : (0 : ℝ) < Δ := NNReal.coe_pos.mpr hΔ
    have htoReal : ((((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) + t).toReal = (k : ℝ) * Δ + t.toReal := by
      rw [ENNReal.toReal_add ENNReal.coe_ne_top ht]
      simp
    rw [htoReal]
    have hdiv : ((k : ℝ) * Δ + t.toReal) / (Δ : ℝ) = t.toReal / (Δ : ℝ) + k := by
      field_simp
      ring
    rw [hdiv, Nat.ceil_add_natCast (div_nonneg ENNReal.toReal_nonneg hΔR.le)]
    push_cast
    ring

/-- The exponential height of the `n`th trial start. -/
noncomputable def trialStartWeight {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) (i : Fin d) (n : ℕ)
    (z : CoupledSample d) : ℝ≥0∞ :=
  {z : CoupledSample d | trialStartSequence Δ lam R z i n ≠ ⊤}.indicator
    (fun z => ENNReal.ofReal (Real.exp (a * (lam *
      (z.1 (trialStartSequence Δ lam R z i n).toNNReal i - z.1 0 i))))) z

/-- The failure time of the `n`th trial. -/
noncomputable def trialFailure {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (n : ℕ)
    (z : CoupledSample d) : ℝ≥0∞ :=
  trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n)

/-- The search level after the failure of the `n`th trial. -/
noncomputable def trialLevel {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (n : ℕ)
    (z : CoupledSample d) : ℝ :=
  lam * (coordinateMaximum z.1 i (trialFailure Δ lam R i n z).toNNReal -
    (z.1 (trialFailure Δ lam R i n z).toNNReal i - z.1 0 i) + R)

/-- The exponential of the running maximum at the failure of the `n`th trial, plus `R`. -/
noncomputable def trialFailureHeight {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) (i : Fin d) (n : ℕ)
    (z : CoupledSample d) : ℝ≥0∞ :=
  {z : CoupledSample d | trialFailure Δ lam R i n z ≠ ⊤}.indicator
    (fun z => ENNReal.ofReal (Real.exp (a * lam *
      (coordinateMaximum z.1 i (trialFailure Δ lam R i n z).toNNReal + R)))) z

theorem trialLevel_nonneg {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (n : ℕ) (z : CoupledSample d) : 0 ≤ trialLevel Δ lam R i n z := by
  have h := displacement_le_coordinateMaximum z.1 i (trialFailure Δ lam R i n z).toNNReal
    (trialFailure Δ lam R i n z).toNNReal le_rfl
  unfold trialLevel
  apply mul_nonneg hlam.le
  linarith

/-- The next trial start splits into the failure height and the candidate overshoot. -/
theorem trialStartWeight_succ {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) (hlam : 0 < lam) (i : Fin d)
    (n : ℕ) (z : CoupledSample d) :
    trialStartWeight Δ lam R a i (n + 1) z =
      {z : CoupledSample d | trialFailure Δ lam R i n z ≠ ⊤}.indicator (fun z =>
        trialFailureHeight Δ lam R a i n z *
          candidateOvershootWeight Δ lam R (trialLevel Δ lam R i n z) a i
            (sampleTimeShift Δ z (trialFailure Δ lam R i n z).toNNReal)) z := by
  set F := trialFailure Δ lam R i n z with hFdef
  by_cases hF : F = ⊤
  · have hS : trialStartSequence Δ lam R z i (n + 1) = ⊤ := by
      rw [trialStartSequence]
      simp only
      rw [ite_eq_left (show trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n) = ⊤ from hF)]
    simp only [trialStartWeight]
    rw [Set.indicator_of_notMem (show z ∉ {z : CoupledSample d |
        trialStartSequence Δ lam R z i (n + 1) ≠ ⊤} from fun h => h hS),
      Set.indicator_of_notMem (show z ∉ {z : CoupledSample d | trialFailure Δ lam R i n z ≠ ⊤}
        from fun h => h hF)]
  · set w := sampleTimeShift Δ z F.toNNReal with hw
    set L := trialLevel Δ lam R i n z with hL
    have hSdef : trialStartSequence Δ lam R z i (n + 1) =
        F + firstSuccessfulCandidate Δ lam R L w i + Δ := by
      rw [trialStartSequence]
      simp only
      rw [ite_eq_right (show ¬ trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n) = ⊤
        from hF)]
      rfl
    rw [Set.indicator_of_mem (show z ∈ {z : CoupledSample d | trialFailure Δ lam R i n z ≠ ⊤}
      from hF)]
    simp only [trialFailureHeight]
    rw [Set.indicator_of_mem (show z ∈ {z : CoupledSample d | trialFailure Δ lam R i n z ≠ ⊤}
      from hF)]
    by_cases hC : firstSuccessfulCandidate Δ lam R L w i = ⊤
    · have hS : trialStartSequence Δ lam R z i (n + 1) = ⊤ := by
        rw [hSdef, hC, add_top, top_add]
      simp only [trialStartWeight, candidateOvershootWeight]
      rw [Set.indicator_of_notMem (show z ∉ {z : CoupledSample d |
          trialStartSequence Δ lam R z i (n + 1) ≠ ⊤} from fun h => h hS),
        Set.indicator_of_notMem (show w ∉ {w : CoupledSample d |
          firstSuccessfulCandidate Δ lam R L w i ≠ ⊤} from fun h => h hC), mul_zero]
    · have hSfin : trialStartSequence Δ lam R z i (n + 1) ≠ ⊤ := by
        rw [hSdef]
        exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hF, hC⟩, ENNReal.coe_ne_top⟩
      have htime : (trialStartSequence Δ lam R z i (n + 1)).toNNReal =
          F.toNNReal + (firstSuccessfulCandidate Δ lam R L w i + Δ).toNNReal := by
        rw [hSdef, add_assoc, ENNReal.toNNReal_add hF
          (ENNReal.add_ne_top.mpr ⟨hC, ENNReal.coe_ne_top⟩)]
      simp only [trialStartWeight, candidateOvershootWeight]
      rw [Set.indicator_of_mem (show z ∈ {z : CoupledSample d |
          trialStartSequence Δ lam R z i (n + 1) ≠ ⊤} from hSfin),
        Set.indicator_of_mem (show w ∈ {w : CoupledSample d |
          firstSuccessfulCandidate Δ lam R L w i ≠ ⊤} from hC),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      rw [htime]
      change a * (lam * (z.1 (F.toNNReal + (firstSuccessfulCandidate Δ lam R L w i + Δ).toNNReal) i -
          z.1 0 i)) = a * lam * (coordinateMaximum z.1 i F.toNNReal + R) +
        a * lam * (z.1 (F.toNNReal + (firstSuccessfulCandidate Δ lam R L w i + Δ).toNNReal) i -
          z.1 (F.toNNReal + 0) i - L / lam)
      rw [add_zero, hL]
      unfold trialLevel
      rw [← hFdef]
      field_simp
      ring

end EinsteinFull.Regeneration
