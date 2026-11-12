import EinsteinRelation.Correctors.StationarySpatialHorizontal

/-! # Spatial divergence of stationary observables

Source: `paper/main.tex:926–938`. Spatial weak divergence transfers to
the environment by testing with a compact spatial weight times the orbit
of a horizontal test. The derivative of the compact weight has zero
expectation. Every exchanged integral is genuinely integrable.
-/

open MeasureTheory Filter

namespace EinsteinRelation.Correctors

/-- A stationary spatial divergence satisfies integration by parts on
the actual bounded smooth horizontal core.
Source: `paper/main.tex:926–938`. -/
theorem stationarySpatialDivergence_integral_test {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {W : FieldPair d → Vec d} {h : FieldPair d → ℝ}
    (hWm : Measurable W) (hhm : Measurable h)
    (hW : ∀ i, MemLp (fun ω => W ω i) 2 Q) (hh : MemLp h 2 Q)
    (hweak : ∀ᵐ ω ∂Q, HasWeakDivergence Set.univ
      (fun x => W (translate x ω)) (orbit h ω))
    {H : FieldPair d → ℝ} (hH : IsHorizontalTest H) :
    (∫ ω, ∑ i, W ω i * horizontalDerivative i H ω ∂Q) =
      -(∫ ω, h ω * H ω ∂Q) := by
  let η := mollifier d
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := contDiff_mollifier d
  have hηc : HasCompactSupport η := hasCompactSupport_mollifier d
  have hη1 : (∫ x, η x ∂volume) = 1 := integral_mollifier d
  have hηi : Integrable η volume := hη.continuous.integrable_of_hasCompactSupport hηc
  have hηD (i : Fin d) : Continuous (coordinateDerivative i η) :=
    ((contDiff_infty_iff_fderiv.mp hη).2.clm_apply contDiff_const).continuous
  have hηDi (i : Fin d) : Integrable (coordinateDerivative i η) volume :=
    (hηD i).integrable_of_hasCompactSupport (hηc.fderiv_apply ℝ (unitVector i))
  have hWim (i : Fin d) : Measurable (fun ω => W ω i) :=
    (measurable_pi_apply i).comp hWm
  have hA (i : Fin d) := integrable_weighted_orbit Q hQ hη.continuous.measurable hηi
    ((hWim i).mul (hH.measurable_derivative i))
    ((hW i).integrable_mul (hH.memLp_derivative Q 2 i))
  have hB (i : Fin d) := integrable_weighted_orbit Q hQ (hηD i).measurable (hηDi i)
    ((hWim i).mul hH.1) ((hW i).integrable_mul (hH.memLp Q 2))
  have hsections : ∀ᵐ ω ∂Q, ∀ i : Fin d,
      Integrable (fun x => η x * (W (translate x ω) i *
        horizontalDerivative i H (translate x ω))) volume ∧
      Integrable (fun x => coordinateDerivative i η x *
        (W (translate x ω) i * H (translate x ω))) volume :=
    ae_all_iff.mpr fun i => (hA i).prod_left_ae.and (hB i).prod_left_ae
  have heq :
      (fun ω => (∑ i : Fin d, ∫ x, η x * (W (translate x ω) i *
          horizontalDerivative i H (translate x ω))) +
        ∑ i : Fin d, ∫ x, coordinateDerivative i η x *
          (W (translate x ω) i * H (translate x ω))) =ᵐ[Q]
      fun ω => -(∫ x, η x * (h (translate x ω) * H (translate x ω))) := by
    filter_upwards [hweak, hsections] with ω hω hs
    have ht : IsSpatialTest Set.univ (fun x => η x * orbit H ω x) :=
      ⟨hη.mul (hH.2.1 ω), hηc.mul_right, Set.subset_univ _⟩
    have hw := hω.2.2 _ ht
    rw [Measure.restrict_univ] at hw
    rw [← integral_finset_sum Finset.univ (fun i _ => (hs i).1),
      ← integral_finset_sum Finset.univ (fun i _ => (hs i).2),
      ← integral_add (integrable_finset_sum Finset.univ (fun i _ => (hs i).1))
        (integrable_finset_sum Finset.univ (fun i _ => (hs i).2))]
    calc
      _ = ∫ x, dot (W (translate x ω))
          (gradient (fun y => η y * orbit H ω y) x) := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          dsimp only
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          change _ = W (translate x ω) i *
            coordinateDerivative i (fun y => η y * orbit H ω y) x
          rw [coordinateDerivative_mul i η (orbit H ω) x
            (hη.differentiable (by simp) x) ((hH.2.1 ω).differentiable (by simp) x)]
          rw [← horizontalDerivative_translate]
          simp only [orbit]
          ring
      _ = -(∫ x, orbit h ω x * (η x * orbit H ω x)) := hw
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun x => by simp only [orbit]; ring
  have hexp := integral_congr_ae heq
  rw [integral_add (integrable_finset_sum Finset.univ
      (fun i _ => (hA i).integral_prod_right))
      (integrable_finset_sum Finset.univ (fun i _ => (hB i).integral_prod_right)),
    integral_finset_sum Finset.univ (fun i _ => (hA i).integral_prod_right),
    integral_finset_sum Finset.univ (fun i _ => (hB i).integral_prod_right),
    integral_neg] at hexp
  have hEA (i : Fin d) :
      (∫ ω, ∫ x, η x * (W (translate x ω) i *
        horizontalDerivative i H (translate x ω)) ∂volume ∂Q) =
      ∫ ω, W ω i * horizontalDerivative i H ω ∂Q := by
    rw [integral_weighted_orbit Q hQ hη.continuous.measurable hηi
      ((hWim i).mul (hH.measurable_derivative i))
      ((hW i).integrable_mul (hH.memLp_derivative Q 2 i)), hη1, one_mul]
  have hEB (i : Fin d) :
      (∫ ω, ∫ x, coordinateDerivative i η x *
        (W (translate x ω) i * H (translate x ω)) ∂volume ∂Q) = 0 := by
    rw [integral_weighted_orbit Q hQ (hηD i).measurable (hηDi i)
      ((hWim i).mul hH.1) ((hW i).integrable_mul (hH.memLp Q 2)),
      integral_coordinateDerivative_eq_zero hη hηc i, zero_mul]
  rw [integral_weighted_orbit Q hQ hη.continuous.measurable hηi
    (hhm.mul hH.1) (hh.integrable_mul (hH.memLp Q 2)), hη1, one_mul] at hexp
  simp only [hEA, hEB, Finset.sum_const_zero, add_zero] at hexp
  rw [integral_finset_sum (f := fun i ω => W ω i * horizontalDerivative i H ω) Finset.univ
    (fun i _ => (hW i).integrable_mul (hH.memLp_derivative Q 2 i))]
  exact hexp

end EinsteinRelation.Correctors
