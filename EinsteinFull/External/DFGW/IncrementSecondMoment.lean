import EinsteinFull.External.DFGW.VarianceAdditivity
import EinsteinFull.External.DFGW.TimeIntegralBound

/-! # Second moment of a trajectory increment

The martingale and integrated-drift bounds give a small-time second-moment bound for the
original trajectory increment.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The increment at time `1 / n` is square-integrable and its second moment is controlled by
the martingale and drift second moments. -/
theorem increment_memLp_and_sq_le_inv_nat (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (i : Fin d) (n : ℕ) (hn : 0 < n) :
    MemLp (fun η => X 0 ((n : ℝ)⁻¹) η i) 2 P ∧
      (∫ η, (X 0 ((n : ℝ)⁻¹) η i) ^ 2 ∂P) ≤
        2 * ((n : ℝ)⁻¹ * ∫ η, (compensated X φ 1 η i) ^ 2 ∂P +
          (n : ℝ)⁻¹ ^ 2 * ∫ x, φ x i ^ 2 ∂μ) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let q : ℝ≥0 := (n : ℝ≥0)⁻¹
  have hq : (q : ℝ) = (n : ℝ)⁻¹ := by simp [q]
  have hq0 : 0 ≤ (q : ℝ) := q.coe_nonneg
  have hφint : Integrable φ μ := hφ.integrable one_le_two
  have haetime := ae_intervalIntegrable_observable hP φ hφint hq0
  let A : C(ℝ, S) → ℝ := fun η => (∫ u in (0 : ℝ)..(q : ℝ), φ (η u)) i
  let B : C(ℝ, S) → ℝ := fun η => ∫ u in (0 : ℝ)..(q : ℝ), φ (η u) i
  have hAB : B =ᵐ[P] A := by
    filter_upwards [haetime] with η hη
    have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).intervalIntegral_comp_comm hη
    simpa only [A, B, ContinuousLinearMap.proj_apply] using h
  have hB := time_integral_memLp_and_sq_le hP (fun x => φ x i) (hφ.eval i) hq0
  have hA : MemLp A 2 P := (memLp_congr_ae hAB).mp hB.1
  have hA_sq : (∫ η, A η ^ 2 ∂P) ≤ (q : ℝ) ^ 2 * ∫ x, φ x i ^ 2 ∂μ := by
    have h := integral_congr_ae (hAB.fun_comp (fun x : ℝ => x ^ 2))
    change (∫ η, B η ^ 2 ∂P) = ∫ η, A η ^ 2 ∂P at h
    rw [← h]
    exact hB.2
  let M : C(ℝ, S) → ℝ := fun η => compensated X φ q η i
  let Z : C(ℝ, S) → ℝ := fun η => X 0 (q : ℝ) η i
  have hMi : MemLp M 2 P := (hL2 q).eval i
  have hZ : MemLp Z 2 P := by
    apply (memLp_congr_ae ?_).mp (hMi.add hA)
    exact ae_of_all P fun η => by simp only [M, A, Z, compensated, Pi.sub_apply, Pi.add_apply]; ring
  have hZbound : (∫ η, Z η ^ 2 ∂P) ≤
      2 * ((∫ η, M η ^ 2 ∂P) + ∫ η, A η ^ 2 ∂P) := by
    have hi : Integrable (fun η => 2 * (M η ^ 2 + A η ^ 2)) P :=
      (hMi.integrable_sq.add hA.integrable_sq).const_mul 2
    have h := integral_mono_ae hZ.integrable_sq hi (ae_of_all P fun η => by
      simp only [M, A, Z, compensated, Pi.sub_apply]
      nlinarith [sq_nonneg ((X 0 (q : ℝ) η) i -
        2 * (∫ u in (0 : ℝ)..(q : ℝ), φ (η u)) i)])
    rw [integral_const_mul, integral_add hMi.integrable_sq hA.integrable_sq] at h
    exact h
  have hM_sq := integral_compensated_sq_inv_nat hP hX φ hφint hL2 hM i n hn
  change (∫ η, M η ^ 2 ∂P) = _ at hM_sq
  rw [hM_sq] at hZbound
  constructor
  · simpa only [Z, hq] using hZ
  · rw [← hq]
    change (∫ η, Z η ^ 2 ∂P) ≤ _
    rw [← hq] at hZbound
    nlinarith

end EinsteinFull.External.DFGW
