import EinsteinFull.External.DFGW.MartingaleMaximalInMeasure
import EinsteinFull.External.DFGW.MaximalSecondMoment

/-! # Moments of maximal martingale increments

The squared maximum of the diffusively scaled projected unit increments of a stationary
square-integrable martingale has a uniformly bounded expectation.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The maximal squared scaled projected unit increment is integrable and its expectation is at
most the second moment of the projected unit martingale value. -/
theorem integrable_max_scaled_martingale_sq_and_integral_le
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d) (n : ℕ) :
    Integrable (fun η => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ((Real.sqrt (n + 1))⁻¹ *
        dot e (N ((k : ℝ≥0) + 1) η - N k η)) ^ 2)) P ∧
    (∫ η, (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ((Real.sqrt (n + 1))⁻¹ *
        dot e (N ((k : ℝ≥0) + 1) η - N k η)) ^ 2) ∂P) ≤
      ∫ η, dot e (N 1 η) ^ 2 ∂P := by
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  let g : ℕ → C(ℝ, S) → ℝ := fun k η => dot e (N ((k : ℝ≥0) + 1) η - N k η)
  have hg (k : ℕ) : StronglyMeasurable (g k) := by
    have h1 := (hN.stronglyAdapted ((k : ℝ≥0) + 1)).mono (Draft.dfgwPast.le _)
    have h2 := (hN.stronglyAdapted (k : ℝ≥0)).mono (Draft.dfgwPast.le _)
    simpa only [g, hL, Pi.sub_apply] using L.continuous.comp_stronglyMeasurable (h1.sub h2)
  have hg2 (k : ℕ) : MemLp (g k) 2 P := by
    simpa only [g, hL, Pi.sub_apply] using ((hN2 ((k : ℝ≥0) + 1)).sub (hN2 k)).continuousLinearMap_comp L
  have hf : StronglyMeasurable (fun η => dot e (N 1 η)) := by
    simpa only [hL] using L.continuous.comp_stronglyMeasurable
      ((hN.stronglyAdapted 1).mono (Draft.dfgwPast.le 1))
  have hmean (k : ℕ) : (∫ η, (g k η) ^ 2 ∂P) = ∫ η, dot e (N 1 η) ^ 2 ∂P := by
    calc
      (∫ η, (g k η) ^ 2 ∂P) = ∫ η, dot e (N 1 (Draft.dfgwShift (k : ℝ) η)) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hstat (k : ℝ≥0) 1] with η hη
        simp only [g, hη, NNReal.coe_natCast]
      _ = ∫ η, dot e (N 1 η) ^ 2 ∂P.map (Draft.dfgwShift (k : ℝ)) := by
        symm
        apply integral_map (measurable_shift _).aemeasurable
        rw [hP.stationary]
        exact (hf.pow 2).aestronglyMeasurable
      _ = _ := by rw [hP.stationary]
  have h := integrable_max_sq_and_integral_le g hg hg2 _ hmean n
  have hn : 0 ≤ (n + 1 : ℝ) := by positivity
  have heq (k : ℕ) (η : C(ℝ, S)) :
      ((Real.sqrt (n + 1))⁻¹ * g k η) ^ 2 = ((n + 1 : ℝ)⁻¹) * (g k η) ^ 2 := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hn]
  simpa only [heq, g] using h

end EinsteinFull.External.DFGW
