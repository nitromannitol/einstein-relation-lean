import EinsteinFull.External.DFGW.MartingaleArrayCLT

/-! # One-time scalar martingale central limit theorem

The martingale array limit telescopes to the projected martingale value at a large integer time.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A projected stationary-increment martingale at time `n + 1`, divided by `√(n + 1)`,
converges in distribution to its centered normal law. -/
theorem tendstoInDistribution_projected_martingale_grid
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d) :
    letI : IsProbabilityMeasure P := hP.probability
    let σsq : ℝ≥0 := ⟨∫ η, dot e (N 1 η) ^ 2 ∂P,
      integral_nonneg fun _ => sq_nonneg _⟩
    TendstoInDistribution (fun (n : ℕ) η => (Real.sqrt (n + 1))⁻¹ *
      dot e (N ((n + 1 : ℕ) : ℝ≥0) η)) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 σsq) := by
  let : IsProbabilityMeasure P := hP.probability
  have hzero : N 0 =ᵐ[P] 0 := by
    filter_upwards [hstat 0 0] with η hη
    simp only [zero_add, NNReal.coe_zero, shift_zero, Pi.zero_apply] at hη ⊢
    have hη' : N 0 η - N 0 η = N 0 η := hη
    simpa only [sub_self] using hη'.symm
  let σsq : ℝ≥0 := ⟨∫ η, dot e (N 1 η) ^ 2 ∂P, integral_nonneg fun _ => sq_nonneg _⟩
  let : IsProbabilityMeasure (gaussianReal 0 σsq) := instIsProbabilityMeasureGaussianReal 0 σsq
  have h := tendstoInDistribution_scaledProjectedIncrement_sum hP hcoord hμ hPfin N hN hN2 hstat e
  have heq (n : ℕ) : (fun η => ∑ k ∈ Finset.range (n + 1),
      scaledProjectedIncrement N e n k η) =ᵐ[P] (fun η => (Real.sqrt (n + 1))⁻¹ *
      dot e (N ((n + 1 : ℕ) : ℝ≥0) η)) := by
    filter_upwards [hzero] with η hη
    simp only [scaledProjectedIncrement, ← Finset.mul_sum]
    congr 1
    have hsub (k : ℕ) : dot e (N ((k : ℝ≥0) + 1) η - N k η) =
        dot e (N ((k + 1 : ℕ) : ℝ≥0) η) - dot e (N k η) := by
      simp only [Nat.cast_add, Nat.cast_one, dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    simp_rw [hsub]
    have htel := Finset.sum_range_sub (fun k : ℕ => dot e (N k η)) (n + 1)
    simp only [Nat.cast_zero, hη, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero] at htel
    exact htel
  exact TendstoInDistribution.congr heq EventuallyEq.rfl h

end EinsteinFull.External.DFGW
