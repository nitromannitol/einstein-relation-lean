import EinsteinFull.External.DFGW.WeightedVectorArray
import EinsteinFull.External.DFGW.MartingaleVectorMaximalTail
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Maximal increments of bounded weighted arrays

Uniformly bounded deterministic vector weights preserve the vanishing maximal-increment
property of the diffusively normalized martingale array.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Bounded vector weights yield diffusively scaled array maxima converging to zero in probability. -/
theorem tendstoInMeasure_max_scaledVectorWeightedIncrement
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (w : ℕ → ℕ → Vec d) (C : ℝ) (hw : ∀ n k, ‖w n k‖ ≤ C) :
    TendstoInMeasure P (fun n η => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k => |scaledVectorWeightedIncrement N w n k η|))
      atTop (fun _ => 0) := by
  let : IsProbabilityMeasure P := hP.probability
  let K : ℝ := (d : ℝ) * (|C| + 1) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hdot (v z : Vec d) : |dot v z| ≤ (d : ℝ) * ‖v‖ * ‖z‖ := by
    calc
      _ ≤ ∑ i, |v i * z i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin d, ‖v‖ * ‖z‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i)
          (abs_nonneg _) (norm_nonneg _)
      _ = _ := by simp; ring
  have hbound (n k : ℕ) (η : C(ℝ, S)) :
      |dot (w n k) (N ((k : ℝ≥0) + 1) η - N k η)| ≤
        K * ‖N ((k : ℝ≥0) + 1) η - N k η‖ := by
    have hw' : ‖w n k‖ ≤ |C| + 1 := (hw n k).trans (by linarith [le_abs_self C])
    have hcoef : (d : ℝ) * ‖w n k‖ ≤ K := by
      dsimp [K]
      have h := mul_le_mul_of_nonneg_left hw' (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
      linarith
    exact (hdot _ _).trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _))
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have hδ : 0 < (ε / K) ^ 2 := sq_pos_of_pos (div_pos hε hK)
  have htail := (tendsto_measureReal_max_martingale_increment_norm_sq hP N hN hN2 hstat hδ).comp
    (tendsto_add_atTop_nat 1)
  apply squeeze_zero (g := fun n : ℕ => P.real {η | ∃ k < n + 1, (ε / K) ^ 2 * (n + 1) ≤
    ‖N ((k : ℝ≥0) + 1) η - N k η‖ ^ 2})
  · intro n
    exact measureReal_nonneg
  · intro n
    refine measureReal_mono ?_ (measure_ne_top P _)
    intro η hη
    have hn : 0 < (n + 1 : ℝ) := by positivity
    have hroot : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.2 hn
    have hnonneg : 0 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => |scaledVectorWeightedIncrement N w n k η|) := by
      have hsmall := Finset.le_sup' (fun k => |scaledVectorWeightedIncrement N w n k η|)
        (Finset.mem_range.2 (Nat.zero_lt_succ n))
      exact (abs_nonneg _).trans hsmall
    simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnonneg,
      Finset.le_sup'_iff, Finset.mem_range] at hη
    obtain ⟨k, hk, hlarge⟩ := hη
    refine ⟨k, hk, ?_⟩
    have hlarge' : ε ≤ (Real.sqrt (n + 1))⁻¹ *
        (K * ‖N ((k : ℝ≥0) + 1) η - N k η‖) := by
      apply hlarge.trans
      simp only [scaledVectorWeightedIncrement, abs_mul, abs_inv, abs_of_pos hroot]
      exact mul_le_mul_of_nonneg_left (hbound n k η) (inv_nonneg.mpr hroot.le)
    have hprod : ε * Real.sqrt (n + 1) ≤
        K * ‖N ((k : ℝ≥0) + 1) η - N k η‖ := by
      apply (le_div_iff₀ hroot).1
      simpa only [div_eq_mul_inv, mul_comm] using hlarge'
    have hdiv : (ε / K) * Real.sqrt (n + 1) ≤
        ‖N ((k : ℝ≥0) + 1) η - N k η‖ := by
      have hdiv' : ε * Real.sqrt (n + 1) / K ≤
          ‖N ((k : ℝ≥0) + 1) η - N k η‖ := by
        apply (div_le_iff₀ hK).2
        simpa only [mul_comm] using hprod
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv'
    have hs := (sq_le_sq₀ (mul_nonneg (div_nonneg hε.le hK.le) hroot.le) (norm_nonneg _)).2 hdiv
    rw [mul_pow, Real.sq_sqrt hn.le] at hs
    exact hs
  · simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using htail

end EinsteinFull.External.DFGW
