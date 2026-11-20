import EinsteinFull.External.DFGW.DynkinDyadicEnergyNorm
import EinsteinFull.External.DFGW.ResolventNormScale

/-! # Diffusive maximal bounds for resolvent differences

The reversible dyadic maximal inequality at time `n + 1` separates the normalized resolvent
difference norm from its Dirichlet energy.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A diffusive-scale dyadic maximal probability for a resolvent difference is bounded by
its normalized `L²` norm and its Dirichlet energy. -/
theorem measureReal_max_resolvent_difference_le
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ) (n m : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    let F := transitionResolventDomain hP (reciprocalShift n) f -
      transitionResolventDomain hP (reciprocalShift m) f
    (θ / 4) * P.real {η | ∃ r k, k ≤ 2 ^ r ∧ θ * Real.sqrt (n + 1) ≤
      |(F : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k))|} ≤
      (Real.sqrt (n + 1))⁻¹ * ‖(F : Lp ℝ 2 μ)‖ +
        2 * Real.sqrt (2 * -inner ℝ (F : Lp ℝ 2 μ) ((transitionSemigroup hP).generator F)) := by
  let F := transitionResolventDomain hP (reciprocalShift n) f -
    transitionResolventDomain hP (reciprocalShift m) f
  have hroot : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
  have h := measureReal_max_dynkin_dyadic_le_norm_energy hP hcoord F
    ((n + 1 : ℕ) : ℝ≥0) (θ * Real.sqrt (n + 1)) (mul_pos hθ hroot)
  simp only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one] at h
  have hfac : Real.sqrt ((n + 1 : ℝ) *
      (2 * -inner ℝ (F : Lp ℝ 2 μ) ((transitionSemigroup hP).generator F))) =
      Real.sqrt (n + 1) *
        Real.sqrt (2 * -inner ℝ (F : Lp ℝ 2 μ) ((transitionSemigroup hP).generator F)) := by
    exact Real.sqrt_mul (show 0 ≤ (n + 1 : ℝ) by positivity) _
  rw [hfac] at h
  have hinv := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hroot.le)
  have hcancel : (Real.sqrt (n + 1))⁻¹ * Real.sqrt (n + 1) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hroot)
  have hleft (p : ℝ) : (Real.sqrt (n + 1))⁻¹ * (θ * Real.sqrt (n + 1) / 4 * p) =
      (θ / 4) * p := by
    calc
      _ = ((Real.sqrt (n + 1))⁻¹ * Real.sqrt (n + 1)) * ((θ / 4) * p) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have hright (x y : ℝ) : (Real.sqrt (n + 1))⁻¹ * (x + 2 * (Real.sqrt (n + 1) * y)) =
      (Real.sqrt (n + 1))⁻¹ * x + 2 * y := by
    calc
      _ = (Real.sqrt (n + 1))⁻¹ * x +
          2 * (((Real.sqrt (n + 1))⁻¹ * Real.sqrt (n + 1)) * y) := by ring
      _ = _ := by rw [hcancel, one_mul]
  rw [hleft, hright] at hinv
  simpa only [Nat.cast_add, Nat.cast_one] using hinv

end EinsteinFull.External.DFGW
