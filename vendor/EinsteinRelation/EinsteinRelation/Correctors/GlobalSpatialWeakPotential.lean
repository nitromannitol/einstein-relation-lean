import EinsteinRelation.Correctors.WeakPotentialSubtraction
import EinsteinRelation.Correctors.BallPotentialUniqueness
import EinsteinRelation.Correctors.HarmonicRepresentativeNormalization
import EinsteinRelation.Calculus.WeakPotentialGluing
import EinsteinRelation.Calculus.WeakGradientExhaustion
import EinsteinRelation.Calculus.WeakRepresentativeOperations

/-!
# Global scalar potentials from centered local potentials

Source: `paper/main.tex:693-698`. Normalize every local potential by its
unit-ball mean. Poincaré uniqueness makes these potentials compatible;
countable gluing and locality give one scalar weak potential on all space.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Local weak potentials on all positive balls glue to a global,
locally square-integrable scalar potential. -/
theorem exists_global_weakPotential_of_ball_potentials
    (hP : BallPoincareEstimate) {d : ℕ} (hd : 2 ≤ d) (G : Vec d → Vec d)
    (hG : ∀ R : ℝ, 0 < R → MemLp G 2 (volume.restrict (ball 0 R)))
    (hpot : ∀ R : ℝ, 0 < R → ∃ u : Vec d → ℝ,
      MemLp u 2 (volume.restrict (ball 0 R)) ∧ HasWeakGradient (ball 0 R) u G) :
    ∃ u : Vec d → ℝ, HasWeakGradient Set.univ u G ∧
      (∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) ∧
      (∫ x in ball (0 : Vec d) 1, u x) = 0 := by
  classical
  let U := fun n : ℕ => ball (0 : Vec d) ((n : ℝ) + 2)
  have hpos (n : ℕ) : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hfin (n : ℕ) : IsFiniteMeasure (volume.restrict (U n)) :=
    isFiniteMeasure_restrict.mpr
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d _ (hpos n))).2.ne
  have hsub (n m : ℕ) (hnm : n ≤ m) : U n ⊆ U m := by
    intro x hx
    change euclideanNorm (x - 0) < (n : ℝ) + 2 at hx
    change euclideanNorm (x - 0) < (m : ℝ) + 2
    exact lt_of_lt_of_le hx (by exact_mod_cast Nat.add_le_add_right hnm 2)
  have hunit (n : ℕ) : ball (0 : Vec d) 1 ⊆ U n := by
    intro x hx
    change euclideanNorm (x - 0) < 1 at hx
    change euclideanNorm (x - 0) < (n : ℝ) + 2
    exact lt_of_lt_of_le hx (by linarith [Nat.cast_nonneg (α := ℝ) n])
  choose v hv hw using fun (n : ℕ) => hpot ((n : ℝ) + 2) (hpos n)
  let w := fun n x => v n x - ⨍ y in ball (0 : Vec d) 1, v n y ∂volume
  have hsol (n : ℕ) : WeakSolution (U n) (fun _ => 0) (v n) G := by
    refine ⟨hv n, hG _ (hpos n), hw n, ?_⟩
    simpa using hasWeakDivergence_zero (U n)
  have hws (n : ℕ) : WeakSolution (U n) (fun _ => 0) (w n) G := by
    letI := hfin n
    exact weakSolution_sub_const (hsol n) _
  have hmean (n : ℕ) : (∫ x in ball (0 : Vec d) 1, w n x) = 0 :=
    integral_unitBall_sub_average_eq_zero ((hv n).mono_measure
      (Measure.restrict_mono_set volume (hunit n)))
  have hcompat (n m : ℕ) (hnm : n ≤ m) : w m =ᵐ[volume.restrict (U n)] w n := by
    letI := hfin n
    have hvm := (hws m).1.mono_measure (Measure.restrict_mono_set volume (hsub n m hnm))
    have hgm := hG _ (hpos n)
    have hdiff : HasWeakGradient (U n) (fun x => w m x - w n x) (fun _ => 0) := by
      have hm := (weakSolution_restrict_subset (by
        unfold U ball euclideanNorm euclideanSq dot
        exact (isOpen_lt (by fun_prop) continuous_const).measurableSet) (hsub n m hnm) (hws m)).2.2.1
      simpa only [sub_self] using hasWeakGradient_sub_of_memLp (U n)
        (w m) (w n) G G hvm (hws n).1 hgm hgm hm (hws n).2.2.1
    have hzero := ae_eq_zero_of_weakGradient_zero_and_unitBall_mean hP hd
      ((n : ℝ) + 2) (by linarith [Nat.cast_nonneg (α := ℝ) n]) (fun x => w m x - w n x)
      (hvm.sub (hws n).1) hdiff (by
        letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) 1)) :=
          isFiniteMeasure_restrict.mpr
            (ENNReal.toReal_pos_iff.mp (unitBall_volume_pos_finite d)).2.ne
        rw [integral_sub
          ((hvm.mono_measure (Measure.restrict_mono_set volume (hunit n))).integrable (by norm_num))
          (((hws n).1.mono_measure (Measure.restrict_mono_set volume (hunit n))).integrable (by norm_num)),
          hmean m, hmean n, sub_self])
    exact hzero.mono fun _ hx => sub_eq_zero.mp hx
  have hopen (n : ℕ) : IsOpen (U n) := by
    unfold U ball euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hcover (x : Vec d) : ∃ n : ℕ, x ∈ U n := by
    obtain ⟨n, hn⟩ := exists_nat_gt (euclideanNorm (x - 0))
    exact ⟨n, lt_trans hn (by linarith)⟩
  obtain ⟨u, hu⟩ := exists_ae_glue_of_exhaustion volume U
    (fun n => (hopen n).measurableSet) (fun _ _ h => hsub _ _ h) hcover w hcompat
  have hweak (n : ℕ) : HasWeakGradient (U n) u G :=
    fun j => ((hws n).2.2.1 j).congr_ae (hu n).symm (ae_eq_refl _)
  refine ⟨u, hasWeakGradient_univ_of_balls u G (fun n j =>
    HasWeakPartialDerivative.restrict_subset (show ball (0 : Vec d) ((n : ℝ) + 1) ⊆ U n from by
      intro x hx
      change euclideanNorm (x - 0) < (n : ℝ) + 1 at hx
      change euclideanNorm (x - 0) < (n : ℝ) + 2
      linarith)
      (hopen n).measurableSet (hweak n j)), ?_, ?_⟩
  · intro R hR
    obtain ⟨n, hn⟩ := exists_nat_gt R
    have hs : ball (0 : Vec d) R ⊆ U n := by
      intro x hx
      change euclideanNorm (x - 0) < R at hx
      change euclideanNorm (x - 0) < (n : ℝ) + 2
      linarith
    exact ((memLp_congr_ae (hu n)).mpr (hws n).1).mono_measure (Measure.restrict_mono_set volume hs)
  · rw [integral_congr_ae ((hu 0).filter_mono
      (ae_mono (Measure.restrict_mono_set volume (hunit 0))))]
    exact hmean 0

end EinsteinRelation.Correctors
