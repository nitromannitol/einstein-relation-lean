import EinsteinFull.External.DFGW.DynkinMartingale
import EinsteinFull.External.DFGW.AdditiveVariance

/-! # Stationary increments of Dynkin martingales

The Dynkin martingale has stationary increments, whose second moments grow linearly in time.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A Dynkin martingale increment is the initial increment of the shifted trajectory. -/
theorem dynkinProcess_increment_shift (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : (transitionSemigroup hP).generatorDomain) (s t : ℝ≥0) :
    (fun η => dynkinProcess hP f (s + t) η - dynkinProcess hP f s η) =ᵐ[P]
      fun η => dynkinProcess hP f t (Draft.dfgwShift s η) -
        dynkinProcess hP f 0 (Draft.dfgwShift s η) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let g := (transitionSemigroup hP).generator f
  have hst : (s : ℝ) ≤ (s + t : ℝ≥0) := by exact_mod_cast (show s ≤ s + t by simp)
  have h1 := (integrable_joint_observable hP g ((Lp.memLp g).integrable one_le_two) 0 s).prod_left_ae
  have h2 := (integrable_joint_observable hP g ((Lp.memLp g).integrable one_le_two) s (s + t)).prod_left_ae
  filter_upwards [h1, h2] with η h1η h2η
  have hi1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le s.coe_nonneg).2 h1η
  have hi2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2 h2η
  have hsum := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hshift : (∫ v in (0 : ℝ)..t, g (η (v + s))) =
      ∫ v in (s : ℝ)..(s + t : ℝ≥0), g (η v) := by
    simpa only [zero_add, add_zero, NNReal.coe_add, add_comm (t : ℝ) (s : ℝ)] using
      (intervalIntegral.integral_comp_add_right (fun v => g (η v)) (a := 0) (b := t) s)
  simp only [NNReal.coe_add] at hsum hshift
  simp only [dynkinProcess, Draft.dfgwShift, ContinuousMap.coe_comp, ContinuousMap.coe_mk,
    Function.comp_apply, NNReal.coe_add, NNReal.coe_zero, zero_add,
    intervalIntegral.integral_same, sub_zero]
  rw [hshift, ← hsum]
  dsimp only [g]
  ring

/-- Stationarity identifies the second moment of any Dynkin increment with that at the origin. -/
theorem integral_dynkin_increment_sq_stationary (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : (transitionSemigroup hP).generatorDomain) (s t : ℝ≥0) :
    (∫ η, (dynkinProcess hP f (s + t) η - dynkinProcess hP f s η) ^ 2 ∂P) =
      ∫ η, (dynkinProcess hP f t η - dynkinProcess hP f 0 η) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  let Z : C(ℝ, S) → ℝ := fun η => dynkinProcess hP f t η - dynkinProcess hP f 0 η
  have hZ : Integrable (fun η => (Z η) ^ 2) P :=
    ((dynkinProcess_memLp hP f t).sub (dynkinProcess_memLp hP f 0)).integrable_sq
  have hm : AEStronglyMeasurable (fun η => (Z η) ^ 2) (P.map (Draft.dfgwShift s)) := by
    rw [hP.stationary]
    exact hZ.aestronglyMeasurable
  have he := dynkinProcess_increment_shift hP f s t
  calc
    _ = ∫ η, (Z (Draft.dfgwShift s η)) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [he] with η hη
      exact congrArg (fun x : ℝ => x ^ 2) hη
    _ = ∫ η, (Z η) ^ 2 ∂P.map (Draft.dfgwShift s) :=
      (integral_map (measurable_shift s).aemeasurable hm).symm
    _ = _ := by rw [hP.stationary]

/-- The second moment of the initial Dynkin increment grows linearly in time. -/
theorem integral_dynkin_increment_sq_eq_mul (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    (∫ η, (dynkinProcess hP f t η - dynkinProcess hP f 0 η) ^ 2 ∂P) =
      (t : ℝ) * ∫ η, (dynkinProcess hP f 1 η - dynkinProcess hP f 0 η) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  let M := dynkinProcess hP f
  let V : ℝ≥0 → ℝ := fun u => ∫ η, (M u η - M 0 η) ^ 2 ∂P
  have hM := martingale_dynkinProcess hP hcoord f
  have hL2 := dynkinProcess_memLp hP f
  have hadd (s u : ℝ≥0) : V (s + u) = V s + V u := by
    have h1 := integral_martingale_increment_sq hM (show (0 : ℝ≥0) ≤ s + u by simp)
      (hL2 0) (hL2 (s + u))
    have h2 := integral_martingale_increment_sq hM (show (0 : ℝ≥0) ≤ s by simp)
      (hL2 0) (hL2 s)
    have h3 := integral_martingale_increment_sq hM (show s ≤ s + u by simp)
      (hL2 s) (hL2 (s + u))
    have hstat := integral_dynkin_increment_sq_stationary hP f s u
    change V (s + u) = V s + V u
    dsimp only [V, M]
    linarith
  exact nonnegative_additive_eq_mul V hadd
    (fun u => integral_nonneg fun _ => sq_nonneg _) t

end EinsteinFull.External.DFGW
