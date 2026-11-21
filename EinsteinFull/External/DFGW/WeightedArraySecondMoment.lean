import EinsteinFull.External.DFGW.WeightedArrayMaximal
import EinsteinFull.External.DFGW.MaximalSecondMoment

/-! # Second moments of weighted array maxima

A uniform bound on deterministic vector weights bounds the expected squared maximum of
scaled stationary martingale increments.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Uniformly bounded weights give integrable squared array maxima, uniformly bounded in mean. -/
theorem integrable_max_scaledVectorWeightedIncrement_sq_and_integral_le
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (w : ℕ → ℕ → Vec d) (C : ℝ) (hw : ∀ n k, ‖w n k‖ ≤ C) (n : ℕ) :
    Integrable (fun η => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => (scaledVectorWeightedIncrement N w n k η) ^ 2)) P ∧
    (∫ η, (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => (scaledVectorWeightedIncrement N w n k η) ^ 2) ∂P) ≤
      (((d : ℝ) * (|C| + 1) + 1) ^ 2) * ∫ η, ‖N 1 η‖ ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  let K : ℝ := (d : ℝ) * (|C| + 1) + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
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
  have hbound (k : ℕ) (η : C(ℝ, S)) :
      |dot (w n k) (N ((k : ℝ≥0) + 1) η - N k η)| ≤
        K * ‖N ((k : ℝ≥0) + 1) η - N k η‖ := by
    have hw' : ‖w n k‖ ≤ |C| + 1 := (hw n k).trans (by linarith [le_abs_self C])
    have hcoef : (d : ℝ) * ‖w n k‖ ≤ K := by
      dsimp [K]
      have h := mul_le_mul_of_nonneg_left hw' (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
      linarith
    exact (hdot _ _).trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _))
  let g : ℕ → C(ℝ, S) → ℝ := fun k η => ‖N ((k : ℝ≥0) + 1) η - N k η‖
  have hg (k : ℕ) : StronglyMeasurable (g k) := by
    have h1 := (hN.stronglyAdapted ((k : ℝ≥0) + 1)).mono (Draft.dfgwPast.le _)
    have h2 := (hN.stronglyAdapted (k : ℝ≥0)).mono (Draft.dfgwPast.le _)
    simpa only [g, Pi.sub_apply] using (h1.sub h2).norm
  have hg2 (k : ℕ) : MemLp (g k) 2 P := ((hN2 _).sub (hN2 _)).norm
  have hf : StronglyMeasurable (fun η => ‖N 1 η‖) :=
    ((hN.stronglyAdapted 1).mono (Draft.dfgwPast.le 1)).norm
  have hmean (k : ℕ) : (∫ η, (g k η) ^ 2 ∂P) = ∫ η, ‖N 1 η‖ ^ 2 ∂P := by
    calc
      (∫ η, (g k η) ^ 2 ∂P) = ∫ η, ‖N 1 (Draft.dfgwShift (k : ℝ) η)‖ ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hstat (k : ℝ≥0) 1] with η hη
        simp only [g, hη, NNReal.coe_natCast]
      _ = ∫ η, ‖N 1 η‖ ^ 2 ∂P.map (Draft.dfgwShift (k : ℝ)) := by
        symm
        apply integral_map (measurable_shift _).aemeasurable
        rw [hP.stationary]
        exact (hf.pow 2).aestronglyMeasurable
      _ = _ := by rw [hP.stationary]
  have hmax := integrable_max_sq_and_integral_le g hg hg2 _ hmean n
  let Y : C(ℝ, S) → ℝ := fun η => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => (scaledVectorWeightedIncrement N w n k η) ^ 2)
  let Z : C(ℝ, S) → ℝ := fun η => K ^ 2 * (Finset.range (n + 1)).sup'
    Finset.nonempty_range_add_one (fun k => ((n + 1 : ℝ)⁻¹) * (g k η) ^ 2)
  have hYmeas : StronglyMeasurable Y := by
    apply Measurable.stronglyMeasurable
    apply Finset.measurable_range_sup''
    intro k hk
    let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (w n k i) • ContinuousLinearMap.proj i
    have hL (v : Vec d) : L v = dot (w n k) v := by
      simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
    have h1 := (hN.stronglyAdapted ((k : ℝ≥0) + 1)).mono (Draft.dfgwPast.le _)
    have h2 := (hN.stronglyAdapted (k : ℝ≥0)).mono (Draft.dfgwPast.le _)
    have h := L.continuous.comp_stronglyMeasurable (h1.sub h2)
    simpa only [scaledVectorWeightedIncrement, hL, Pi.sub_apply, Pi.mul_apply] using
      (stronglyMeasurable_const.mul h).measurable.pow_const 2
  have hZ : Integrable Z P := hmax.1.const_mul (K ^ 2)
  have hY0 (η : C(ℝ, S)) : 0 ≤ Y η := by
    exact (sq_nonneg _).trans (Finset.le_sup'
      (fun k => (scaledVectorWeightedIncrement N w n k η) ^ 2)
      (Finset.mem_range.2 (Nat.zero_lt_succ n)))
  have hYZ (η : C(ℝ, S)) : Y η ≤ Z η := by
    apply Finset.sup'_le
    intro k hk
    have hsq : |dot (w n k) (N ((k : ℝ≥0) + 1) η - N k η)| ^ 2 ≤ (K * g k η) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hK (norm_nonneg _))).2 (hbound k η)
    have hn : 0 ≤ (n + 1 : ℝ) := by positivity
    have hscale : (scaledVectorWeightedIncrement N w n k η) ^ 2 ≤
        K ^ 2 * (((n + 1 : ℝ)⁻¹) * (g k η) ^ 2) := by
      simp only [scaledVectorWeightedIncrement, mul_pow, inv_pow, Real.sq_sqrt hn]
      rw [sq_abs, mul_pow] at hsq
      nlinarith [mul_nonneg (inv_nonneg.mpr hn) (sub_nonneg.mpr hsq)]
    exact hscale.trans (mul_le_mul_of_nonneg_left
      (Finset.le_sup' (fun k => ((n + 1 : ℝ)⁻¹) * (g k η) ^ 2) hk) (sq_nonneg K))
  have hY : Integrable Y P := hZ.mono' hYmeas.aestronglyMeasurable
    (ae_of_all P fun η => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hY0 η)] using hYZ η)
  refine ⟨hY, (integral_mono hY hZ hYZ).trans ?_⟩
  simpa only [Z, integral_const_mul, K] using
    mul_le_mul_of_nonneg_left hmax.2 (sq_nonneg K)

end EinsteinFull.External.DFGW
