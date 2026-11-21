import EinsteinFull.External.DFGW.WeightedPrefixCLT

/-! # Telescoping prefix-weighted increments

A prefix-weighted array sum is a finite linear combination of martingale values at the
corresponding grid times.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

omit [MeasurableSpace S] [BorelSpace S] in
/-- A prefix-weighted sum telescopes to projected endpoint differences. -/
theorem sum_scaledVectorWeightedIncrement_prefix {J : Type*} (s : Finset J)
    (m : ℕ → J → ℕ) (e : J → Vec d) (N : ℝ≥0 → C(ℝ, S) → Vec d)
    (n : ℕ) (η : C(ℝ, S)) (hm : ∀ j ∈ s, m n j ≤ n + 1) :
    ∑ k ∈ Finset.range (n + 1),
      scaledVectorWeightedIncrement N (prefixVectorWeight s m e) n k η =
    ∑ j ∈ s, (Real.sqrt (n + 1))⁻¹ *
      (dot (e j) (N (m n j) η) - dot (e j) (N 0 η)) := by
  classical
  have h (k : ℕ) : scaledVectorWeightedIncrement N (prefixVectorWeight s m e) n k η =
      ∑ j ∈ s, if k < m n j then scaledProjectedIncrement N (e j) n k η else 0 := by
    simp only [scaledVectorWeightedIncrement, scaledProjectedIncrement, prefixVectorWeight,
      dot, Finset.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range (n + 1)).filter (fun k => k < m n j) =
      Finset.range (m n j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h (hm j hj), h⟩⟩
  rw [hfilter]
  simp only [scaledProjectedIncrement, ← Finset.mul_sum]
  congr 1
  have hsub (k : ℕ) : dot (e j) (N ((k : ℝ≥0) + 1) η - N k η) =
      dot (e j) (N ((k + 1 : ℕ) : ℝ≥0) η) - dot (e j) (N k η) := by
    simp only [Nat.cast_add, Nat.cast_one, dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  simp_rw [hsub]
  simpa only [Nat.cast_zero] using Finset.sum_range_sub (fun k : ℕ => dot (e j) (N k η)) (m n j)

/-- Finite projected sums of rounded martingale values converge to a centered Gaussian. -/
theorem tendstoInDistribution_sum_rounded_martingale
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    {J : Type*} (s : Finset J) (e : J → Vec d) (r : J → ℝ)
    (hr : ∀ j ∈ s, 0 ≤ r j ∧ r j ≤ 1) :
    letI : IsProbabilityMeasure P := hP.probability
    TendstoInDistribution (fun (n : ℕ) η => ∑ j ∈ s, (Real.sqrt (n + 1))⁻¹ *
      dot (e j) (N ⌊r j * (n + 1 : ℝ)⌋₊ η)) atTop
      (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal (∑ j ∈ s, ∑ l ∈ s, min (r j) (r l) *
        ∫ η, dot (e j) (N 1 η) * dot (e l) (N 1 η) ∂P))) := by
  let : IsProbabilityMeasure P := hP.probability
  have hzero : N 0 =ᵐ[P] 0 := by
    filter_upwards [hstat 0 0] with η hη
    simp only [zero_add, NNReal.coe_zero, shift_zero, Pi.zero_apply] at hη ⊢
    have hη' : N 0 η - N 0 η = N 0 η := hη
    simpa only [sub_self] using hη'.symm
  have hm (n : ℕ) (j : J) (hj : j ∈ s) : ⌊r j * (n + 1 : ℝ)⌋₊ ≤ n + 1 := by
    apply Nat.floor_le_of_le
    have h := mul_le_mul_of_nonneg_right (hr j hj).2 (show (0 : ℝ) ≤ n + 1 by positivity)
    simpa only [one_mul, Nat.cast_add, Nat.cast_one] using h
  let : IsProbabilityMeasure (gaussianReal 0 (Real.toNNReal (∑ j ∈ s, ∑ l ∈ s,
      min (r j) (r l) * ∫ η, dot (e j) (N 1 η) * dot (e l) (N 1 η) ∂P))) :=
    instIsProbabilityMeasureGaussianReal _ _
  have h := tendstoInDistribution_scaledVectorWeightedIncrement_prefix
    hP hcoord hμ hPfin N hN hN2 hstat s e r hr
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl h
  intro n
  filter_upwards [hzero] with η hη
  rw [sum_scaledVectorWeightedIncrement_prefix s _ e N n η (hm n)]
  simp only [hη, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]

end EinsteinFull.External.DFGW
