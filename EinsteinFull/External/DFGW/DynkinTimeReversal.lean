import EinsteinFull.External.DFGW.DynkinStationary
import EinsteinFull.External.DFGW.ReflectionDrift

/-! # Forward and reversed Dynkin increments

A reversible trajectory represents the difference of a state observable at two times as the
sum of a forward and a reflected Dynkin increment.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S]

/-- A state-observable difference equals a forward Dynkin increment minus the corresponding
reversed increment. -/
theorem observable_difference_eq_forward_sub_reversed
    (f g : S → ℝ) (η : C(ℝ, S)) (s T : ℝ)
    (h1 : IntervalIntegrable (fun u => g (Draft.dfgwRefl (T / 2) η u)) volume 0 (T - s))
    (h2 : IntervalIntegrable (fun u => g (Draft.dfgwRefl (T / 2) η u)) volume (T - s) T) :
    let M (t : ℝ) (γ : C(ℝ, S)) : ℝ := f (γ t) - ∫ u in (0 : ℝ)..t, g (γ u)
    2 * (f (η s) - f (η 0)) =
      (M s η - M 0 η) - (M T (Draft.dfgwRefl (T / 2) η) -
        M (T - s) (Draft.dfgwRefl (T / 2) η)) := by
  have hsum := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hrev : (∫ u in (T - s)..T, g (Draft.dfgwRefl (T / 2) η u)) =
      ∫ u in (0 : ℝ)..s, g (η u) := by
    change (∫ u in (T - s)..T, g (η (2 * (T / 2) - u))) = _
    have hT : 2 * (T / 2) = T := by ring
    rw [hT]
    have h := intervalIntegral.integral_comp_sub_left (fun u => g (η u))
      (a := T - s) (b := T) T
    have ht : T - (T - s) = s := by ring
    simpa only [sub_self, ht] using h
  have hzero : Draft.dfgwRefl (T / 2) η T = η 0 := by
    change η (2 * (T / 2) - T) = η 0
    congr 1
    ring
  have hs : Draft.dfgwRefl (T / 2) η (T - s) = η s := by
    change η (2 * (T / 2) - (T - s)) = η s
    congr 1
    ring
  dsimp only
  rw [hzero, hs, intervalIntegral.integral_same, sub_zero]
  linarith

variable [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The forward and reflected Dynkin representation holds almost surely under a reversible
stationary trajectory law. -/
theorem ae_observable_difference_eq_dynkin_forward_sub_reversed
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : (transitionSemigroup hP).generatorDomain) (s t : ℝ≥0) (hst : s ≤ t) :
    ∀ᵐ η ∂P,
      2 * ((f : Lp ℝ 2 μ) (η s) - (f : Lp ℝ 2 μ) (η 0)) =
        (dynkinProcess hP f s η - dynkinProcess hP f 0 η) -
          (dynkinProcess hP f t (Draft.dfgwRefl ((t : ℝ) / 2) η) -
            dynkinProcess hP f (t - s) (Draft.dfgwRefl ((t : ℝ) / 2) η)) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let g := (transitionSemigroup hP).generator f
  have hg : Integrable g μ := (Lp.memLp g).integrable one_le_two
  have hts : (t : ℝ) - s = ((t - s : ℝ≥0) : ℝ) := (NNReal.coe_sub hst).symm
  have h0 : (0 : ℝ) ≤ t - s := by rw [hts]; exact (t - s).coe_nonneg
  have hle : (t : ℝ) - s ≤ t := by linarith [s.coe_nonneg]
  have hi1 : ∀ᵐ η ∂P, IntervalIntegrable (fun u => g (η u)) volume 0 ((t : ℝ) - s) := by
    have h := (integrable_joint_observable hP g hg 0 ((t : ℝ) - s)).prod_left_ae
    filter_upwards [h] with η hη
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h0).2 hη
  have hi2 : ∀ᵐ η ∂P, IntervalIntegrable (fun u => g (η u)) volume ((t : ℝ) - s) t := by
    have h := (integrable_joint_observable hP g hg ((t : ℝ) - s) t).prod_left_ae
    filter_upwards [h] with η hη
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).2 hη
  have hR : MeasurePreserving (Draft.dfgwRefl (S := S) ((t : ℝ) / 2)) P P :=
    ⟨measurable_refl _, hP.reversible _⟩
  filter_upwards [hR.quasiMeasurePreserving.ae hi1, hR.quasiMeasurePreserving.ae hi2] with η h1 h2
  have h := observable_difference_eq_forward_sub_reversed (f : Lp ℝ 2 μ) g η s t h1 h2
  simpa only [dynkinProcess, NNReal.coe_zero, NNReal.coe_sub hst] using h

end EinsteinFull.External.DFGW
