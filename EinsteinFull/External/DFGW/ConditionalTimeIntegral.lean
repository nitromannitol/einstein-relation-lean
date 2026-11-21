import EinsteinFull.External.DFGW.MarkovL2
import EinsteinFull.External.DFGW.OrbitPairing
import EinsteinFull.External.DFGW.TimeIntegralPairing
import EinsteinFull.External.DFGW.TimeAverage

/-! # Conditional expectations of time-integrated observables

The conditional mean of a future integral of a stationary square-integrable observable is
the time integral of its transition-semigroup orbit evaluated at the present state.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Conditional expectation of a time-integrated stationary observable. -/
theorem condExp_time_integral (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (g : Lp ℝ 2 μ) (t : ℝ≥0) :
    P[fun η : C(ℝ, S) => ∫ u in (0 : ℝ)..t, g (η u) |
      Draft.dfgwCoordSigma (Set.Iic 0)] =ᵐ[P]
      fun η => (∫ u in (0 : ℝ)..t, transitionSemigroup hP u.toNNReal g) (η 0) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let G : Lp ℝ 2 μ := ∫ u in (0 : ℝ)..t, transitionSemigroup hP u.toNNReal g
  have hσ : Draft.dfgwCoordSigma (S := S) (Set.Iic 0) ≤ Draft.dfgwTrajectoryMeasurableSpace (S := S) :=
    (Draft.dfgwPast (S := S)).le 0
  have hzero : Measurable[Draft.dfgwCoordSigma (S := S) (Set.Iic 0)] (fun η : C(ℝ, S) => η 0) := by
    apply Measurable.of_comap_le
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Iic (0 : ℝ)) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance) 0 (by change (0 : ℝ) ≤ 0; exact le_rfl) le_rfl
  have hev : MeasurePreserving (fun η : C(ℝ, S) => η (0 : ℝ)) P μ :=
    ⟨(continuous_eval_const (0 : ℝ)).measurable, hP.marginal 0⟩
  have hG : Integrable (fun η : C(ℝ, S) => G (η 0)) P :=
    ((Lp.memLp G).comp_measurePreserving hev).integrable one_le_two
  have hi : Integrable (fun η : C(ℝ, S) => ∫ u in (0 : ℝ)..t, g (η u)) P :=
    (integral_time_observable hP g ((Lp.memLp g).integrable one_le_two) t.coe_nonneg).1
  refine (ae_eq_condExp_of_forall_setIntegral_eq hσ hi (fun B _ _ => hG.integrableOn)
    (fun B hB _ => ?_) ((Lp.stronglyMeasurable G).comp_measurable hzero).aestronglyMeasurable).symm
  have hBm : @MeasurableSet _ (Draft.dfgwTrajectoryMeasurableSpace (S := S)) B := hσ B hB
  have hA : MemLp (B.indicator (fun _ : C(ℝ, S) => (1 : ℝ))) 2 P :=
    memLp_indicator_const (μ := P) 2 hBm (1 : ℝ) (Or.inr (measure_ne_top P B))
  have hpair := integral_mul_time_integral hP _ hA g (Lp.memLp g) t.coe_nonneg
  have hset : (∫ η in B, (∫ u in (0 : ℝ)..t, g (η u)) ∂P) =
      ∫ u in (0 : ℝ)..t, ∫ η in B, g (η u) ∂P := by
    have hind (f : C(ℝ, S) → ℝ) :
        (fun η => B.indicator (fun _ => (1 : ℝ)) η * f η) = B.indicator f := by
      funext η
      by_cases hη : η ∈ B <;> simp [hη]
    simp_rw [hind, integral_indicator hBm] at hpair
    exact hpair
  rw [setIntegral_transition_orbit hP g t B hBm, hset]
  apply intervalIntegral.integral_congr
  intro u hu
  have hmark := condExp_shifted_L2 hP 0 u.toNNReal g
  have hmark' : P[fun η : C(ℝ, S) => g (η u) | Draft.dfgwCoordSigma (Set.Iic 0)] =ᵐ[P]
      fun η => transitionSemigroup hP u.toNNReal g (η 0) := by
    have hu0 : 0 ≤ u := (Set.uIcc_of_le t.coe_nonneg ▸ hu).1
    change P[fun η : C(ℝ, S) => g (η u) | Draft.dfgwCoordSigma (Set.Iic 0)] =ᵐ[P]
      fun η => transitionOperator hP u.toNNReal g (η 0)
    simpa only [NNReal.coe_zero, add_zero, Real.coe_toNNReal u hu0] using hmark
  have heq := setIntegral_condExp hσ
    (((Lp.memLp g).comp_measurePreserving
      ⟨(continuous_eval_const u).measurable, hP.marginal u⟩).integrable one_le_two) hB
  calc
    (∫ η in B, transitionSemigroup hP u.toNNReal g (η 0) ∂P) =
        ∫ η in B, P[fun η : C(ℝ, S) => g (η u) | Draft.dfgwCoordSigma (Set.Iic 0)] η ∂P := by
          apply setIntegral_congr_ae hBm
          filter_upwards [hmark'] with η hη _
          exact hη.symm
    _ = _ := heq

end EinsteinFull.External.DFGW
