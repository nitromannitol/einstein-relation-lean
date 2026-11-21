import EinsteinFull.External.DFGW.MartingaleTimeRoundingAt
import EinsteinFull.External.DFGW.FiniteDimensionalMeasure

/-! # Bounded time perturbations of scaled martingales

Changing observation times by a uniformly bounded amount is negligible under diffusive
scaling for stationary-increment square-integrable martingales.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A bounded time perturbation of a projected martingale vanishes in probability. -/
theorem tendstoInMeasure_scaled_martingale_time_perturbation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d)
    (a b : ℝ → ℝ≥0) (C : ℝ)
    (horder : ∀ ε, b ε ≤ a ε) (hbound : ∀ ε, ((a ε - b ε : ℝ≥0) : ℝ) ≤ C) :
    TendstoInMeasure P (fun (ε : ℝ) η => ε *
      dot e (N (a ε) η - N (b ε) η)) (𝓝[>] 0) (fun _ => 0) := by
  let : IsProbabilityMeasure P := hP.probability
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  let F (ε : ℝ) (η : C(ℝ, S)) : ℝ := ε * dot e (N (a ε) η - N (b ε) η)
  have hF (ε : ℝ) : MemLp (F ε) 2 P := by
    have h := ((hN2 (a ε)).sub (hN2 (b ε))).continuousLinearMap_comp L
    simpa only [F, hL, Pi.sub_apply] using h.const_mul ε
  let q : ℝ := ∫ η, dot e (N 1 η) ^ 2 ∂P
  have hq : 0 ≤ q := integral_nonneg fun _ => sq_nonneg _
  have heq (ε : ℝ) : (∫ η, F ε η ^ 2 ∂P) = ε ^ 2 *
      (((a ε - b ε : ℝ≥0) : ℝ)) * q := by
    rw [show (fun η => F ε η ^ 2) = (fun η => ε ^ 2 *
      dot e (N (a ε) η - N (b ε) η) ^ 2) by
      funext η; simp only [F]; ring, integral_const_mul,
      integral_dot_martingale_increment_sq hP N hN hN2 hstat e (horder ε)]
    simp only [q, mul_assoc]
  have hupper (ε : ℝ) : (∫ η, F ε η ^ 2 ∂P) ≤ ε ^ 2 * (C * q) := by
    rw [heq]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hbound ε) hq) (sq_nonneg ε)
  have htop : Tendsto (fun ε : ℝ => ε ^ 2 * (C * q)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => ε ^ 2 * (C * q)) := by fun_prop
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa using h
  have hlim : Tendsto (fun ε : ℝ => ∫ η, F ε η ^ 2 ∂P) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htop
      (fun _ => integral_nonneg fun _ => sq_nonneg _) hupper
  exact tendstoInMeasure_zero_of_integral_sq F hF hlim

/-- A finite family of bounded martingale time perturbations vanishes jointly in probability. -/
theorem tendstoInMeasure_scaled_martingale_finite_time_perturbation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    {J : Type*} [Fintype J] (a b : ℝ → J → ℝ≥0) (C : ℝ)
    (horder : ∀ ε j, b ε j ≤ a ε j)
    (hbound : ∀ ε j, ((a ε j - b ε j : ℝ≥0) : ℝ) ≤ C) :
    TendstoInMeasure P (fun (ε : ℝ) η j => ε •
      (N (a ε j) η - N (b ε j) η)) (𝓝[>] 0) (fun _ => 0) := by
  let : IsProbabilityMeasure P := hP.probability
  apply tendstoInMeasure_pi_zero
  intro j
  apply tendstoInMeasure_pi_zero
  intro i
  have h := tendstoInMeasure_scaled_martingale_time_perturbation hP N hN hN2 hstat
    (unitVector i) (fun ε => a ε j) (fun ε => b ε j) C
    (fun ε => horder ε j) (fun ε => hbound ε j)
  simpa only [dot, unitVector, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h

end EinsteinFull.External.DFGW
