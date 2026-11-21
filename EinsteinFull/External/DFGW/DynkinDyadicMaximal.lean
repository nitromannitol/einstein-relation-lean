import EinsteinFull.External.DFGW.DynkinGridEnergyMaximal
import Mathlib.MeasureTheory.Measure.Continuity

/-! # Maximal inequality on a dense dyadic grid

The reversible grid estimate extends by monotone convergence to all dyadic observation times
in a fixed interval.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Dyadic grid points with denominator `2 ^ r` on `[0,t]`. -/
noncomputable def dyadicGridTime (t : ℝ≥0) (r k : ℕ) : ℝ≥0 :=
  k • (t / ((2 ^ r : ℕ) : ℝ≥0))

/-- The last point of each dyadic grid is the endpoint. -/
theorem dyadicGridTime_last (t : ℝ≥0) (r : ℕ) : dyadicGridTime t r (2 ^ r) = t := by
  apply NNReal.eq
  simp only [dyadicGridTime, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast]
  have h : (2 ^ r : ℕ) ≠ 0 := pow_ne_zero r (by norm_num)
  have hr : ((2 ^ r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h
  field_simp

/-- Each dyadic grid is contained in the next one. -/
theorem dyadicGridTime_succ (t : ℝ≥0) (r k : ℕ) :
    dyadicGridTime t (r + 1) (2 * k) = dyadicGridTime t r k := by
  apply NNReal.eq
  simp only [dyadicGridTime, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
    Nat.cast_mul, Nat.cast_ofNat, pow_succ, Nat.cast_pow]
  have hr : (2 : ℝ) ^ r ≠ 0 := pow_ne_zero r (by norm_num)
  field_simp

/-- The reversible observable maximal estimate holds on the countable dyadic grid of any
bounded time interval. -/
theorem measureReal_max_dynkin_dyadic_le_energy
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) (a : ℝ) (ha : 0 < a) :
    (a / 4) * P.real {η | ∃ r k, k ≤ 2 ^ r ∧
      a ≤ |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))|} ≤
      Real.sqrt (∫ η, (f : Lp ℝ 2 μ) (η 0) ^ 2 ∂P) + 2 *
        Real.sqrt ((t : ℝ) *
          (2 * -inner ℝ (f : Lp ℝ 2 μ) ((transitionSemigroup hP).generator f))) := by
  let : IsProbabilityMeasure P := hP.probability
  let A : ℕ → Set C(ℝ, S) := fun r => {η | ∃ k ≤ 2 ^ r,
    a ≤ |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))|}
  have hmono : Monotone A := by
    apply monotone_nat_of_le_succ
    intro r η hη
    obtain ⟨k, hk, hval⟩ := hη
    refine ⟨2 * k, ?_, ?_⟩
    · rw [pow_succ]
      omega
    · simpa only [dyadicGridTime_succ] using hval
  have hlim : Tendsto (fun r => P.real (A r)) atTop (𝓝 (P.real (⋃ r, A r))) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top P _)).comp (tendsto_measure_iUnion_atTop hmono)
  have hbound (r : ℕ) : (a / 4) * P.real (A r) ≤
      Real.sqrt (∫ η, (f : Lp ℝ 2 μ) (η 0) ^ 2 ∂P) + 2 *
        Real.sqrt ((t : ℝ) *
          (2 * -inner ℝ (f : Lp ℝ 2 μ) ((transitionSemigroup hP).generator f))) := by
    have h := measureReal_max_dynkin_grid_le_energy hP hcoord f
      (t / ((2 ^ r : ℕ) : ℝ≥0)) (2 ^ r) a ha
    have hlast : (2 ^ r : ℕ) • (t / ((2 ^ r : ℕ) : ℝ≥0)) = t := dyadicGridTime_last t r
    simpa only [A, dyadicGridTime, hlast] using h
  have h := le_of_tendsto (hlim.const_mul (a / 4)) (Eventually.of_forall hbound)
  have heq : {η : C(ℝ, S) | ∃ r k, k ≤ 2 ^ r ∧
      a ≤ |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))|} = ⋃ r, A r := by
    ext η
    simp [A]
  simpa only [heq] using h

end EinsteinFull.External.DFGW
