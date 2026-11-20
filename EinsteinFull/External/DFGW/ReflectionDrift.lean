import EinsteinFull.External.DFGW.IncrementSecondMoment
import EinsteinFull.External.DFGW.ReflectionPairing

/-! # Reflection of integrated observables

The time integral of a state observable is unchanged by reflecting the trajectory about the
midpoint of the time interval. It is orthogonal to an antisymmetric increment.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

omit [MeasurableSpace S] [BorelSpace S] in
/-- Time reflection leaves an integrated state observable unchanged. -/
theorem intervalIntegral_observable_refl (g : S → ℝ) (t : ℝ) (η : C(ℝ, S)) :
    (∫ u in (0 : ℝ)..t, g (Draft.dfgwRefl (t / 2) η u)) =
      ∫ u in (0 : ℝ)..t, g (η u) := by
  change (∫ u in (0 : ℝ)..t, g (η (2 * (t / 2) - u))) = _
  have he : 2 * (t / 2) = t := by ring
  rw [he]
  simpa only [sub_self, sub_zero] using
    (intervalIntegral.integral_comp_sub_left (fun u => g (η u)) (a := 0) (b := t) t)

/-- A square-integrable antisymmetric increment is orthogonal to a time-integrated
square-integrable state observable. -/
theorem integral_increment_mul_time_integral_eq_zero
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (g : S → ℝ) (hg : MemLp g 2 μ)
    (t : ℝ≥0) (i : Fin d) (hXt : MemLp (fun η => X 0 t η i) 2 P) :
    (∫ η, X 0 t η i * (∫ u in (0 : ℝ)..(t : ℝ), g (η u)) ∂P) = 0 := by
  have hG := (time_integral_memLp_and_sq_le hP g hg t.coe_nonneg).1
  have hint := hXt.integrable_mul hG
  have hm : AEStronglyMeasurable
      (fun η => X 0 t η i * (∫ u in (0 : ℝ)..(t : ℝ), g (η u)))
      (P.map (Draft.dfgwRefl ((t : ℝ) / 2))) := by
    rw [hP.reversible]
    exact hint.aestronglyMeasurable
  have he : (∫ η, X 0 t η i * (∫ u in (0 : ℝ)..(t : ℝ), g (η u)) ∂P) =
      -(∫ η, X 0 t η i * (∫ u in (0 : ℝ)..(t : ℝ), g (η u)) ∂P) := by
    calc
      _ = ∫ η, X 0 t η i * (∫ u in (0 : ℝ)..(t : ℝ), g (η u))
          ∂P.map (Draft.dfgwRefl ((t : ℝ) / 2)) := by rw [hP.reversible]
      _ = ∫ η, X 0 t (Draft.dfgwRefl ((t : ℝ) / 2) η) i *
          (∫ u in (0 : ℝ)..(t : ℝ), g (Draft.dfgwRefl ((t : ℝ) / 2) η u)) ∂P :=
        integral_map (measurable_refl _).aemeasurable hm
      _ = ∫ η, -(X 0 t η i * (∫ u in (0 : ℝ)..(t : ℝ), g (η u))) ∂P := by
        apply integral_congr_ae
        filter_upwards [hX.antisymmetric 0 (t : ℝ) t.coe_nonneg] with η hη
        simp only [zero_add] at hη
        rw [intervalIntegral_observable_refl, congrFun hη i]
        simp only [Pi.neg_apply, neg_mul]
      _ = _ := integral_neg _
  linarith

end EinsteinFull.External.DFGW
