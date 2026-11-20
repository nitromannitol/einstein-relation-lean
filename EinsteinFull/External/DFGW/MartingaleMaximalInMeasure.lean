import EinsteinFull.External.DFGW.MartingaleMaximalTail
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Diffusively scaled maximal martingale increments

The largest projected unit increment in a row of length `n + 1`, scaled by `√(n + 1)`,
converges to zero in probability.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The maximal diffusively scaled unit increment of a stationary-increment martingale converges
to zero in probability. -/
theorem tendstoInMeasure_max_scaled_martingale_increment
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d) :
    TendstoInMeasure P (fun n : ℕ => fun η =>
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k =>
        |(Real.sqrt (n + 1))⁻¹ * dot e (N ((k : ℝ≥0) + 1) η - N k η)|))
      atTop (fun _ => 0) := by
  let : IsProbabilityMeasure P := hP.probability
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have htail := (tendsto_measureReal_max_martingale_increment_sq hP N hN hN2 hstat e
    (sq_pos_of_pos hε)).comp (tendsto_add_atTop_nat 1)
  apply squeeze_zero (g := fun n : ℕ => P.real {η | ∃ k < n + 1, ε ^ 2 * (n + 1) ≤
    (dot e (N ((k : ℝ≥0) + 1) η - N k η)) ^ 2})
  · intro n
    exact measureReal_nonneg
  · intro n
    refine measureReal_mono ?_ (measure_ne_top P _)
    intro η hη
    have hn : 0 < (n + 1 : ℝ) := by positivity
    have hroot : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.2 hn
    have hnonneg : 0 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k =>
        |(Real.sqrt (n + 1))⁻¹ * dot e (N ((k : ℝ≥0) + 1) η - N k η)|) := by
      have hsmall := Finset.le_sup' (fun k : ℕ => |(Real.sqrt (n + 1))⁻¹ *
        dot e (N ((k : ℝ≥0) + 1) η - N k η)|)
        (Finset.mem_range.2 (Nat.zero_lt_succ n))
      exact (abs_nonneg _).trans hsmall
    simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnonneg,
      Finset.le_sup'_iff, Finset.mem_range] at hη
    obtain ⟨k, hk, hlarge⟩ := hη
    refine ⟨k, hk, ?_⟩
    rw [abs_mul, abs_inv, abs_of_pos hroot] at hlarge
    have hprod : ε * Real.sqrt (n + 1) ≤
        |dot e (N ((k : ℝ≥0) + 1) η - N k η)| := by
      apply (le_div_iff₀ hroot).1
      simpa only [div_eq_mul_inv, mul_comm] using hlarge
    have hs := (sq_le_sq₀ (mul_nonneg hε.le hroot.le) (abs_nonneg _)).2 hprod
    rw [mul_pow, Real.sq_sqrt hn.le, sq_abs] at hs
    exact hs
  · simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using htail

end EinsteinFull.External.DFGW
