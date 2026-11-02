import EinsteinRelation.Correctors.StationarySpatialGradientApproximation

/-!
# Samplewise convergence of a prescribed rapid approximation

Source: `paper/main.tex:693-698`. The samplewise argument applies to any
specified rapid horizontal approximation, including coefficient projections.
-/
open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open StationarySpatialRealization

/-- Rapid environment-L² convergence gives actual spatial scalar
approximations on one common event, for the prescribed sequence. -/
theorem samplewise_scalar_gradient_approximation_of_rapid {d : ℕ} [Fact (2 ≤ d)]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (f : ℕ → horizontalH1 Q hQ)
    (hf : ∀ n, ‖horizontalEuclideanGradient Q hQ (f n) - G‖ ≤ (1 / 2 : ℝ)^n) :
    ∀ᵐ ω ∂Q,
      (∀ n, HasWeakGradient Set.univ
        (fun x => (f n : Lp ℝ 2 Q) (translate x ω))
        (fun x => (horizontalEuclideanGradient Q hQ (f n) (translate x ω)).ofLp)) ∧
      (∀ n (K : Set (Vec d)), IsCompact K →
        MemLp (fun x => (f n : Lp ℝ 2 Q) (translate x ω)) 2 (volume.restrict K)) ∧
      ∀ K : Set (Vec d), IsCompact K → Tendsto (fun n => ∫ x in K,
        ‖horizontalEuclideanGradient Q hQ (f n) (translate x ω) - G (translate x ω)‖ ^ 2)
          atTop (𝓝 0) := by
  let D := fun n => horizontalEuclideanGradient Q hQ (f n)
  have hballs (k : ℕ) : ∀ᵐ ω ∂Q,
      Tendsto (fun n => ∫ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1),
        ‖D n (translate x ω) - G (translate x ω)‖^2 ∂volume) atTop (𝓝 0) := by
    let K := Metric.closedBall (0 : Vec d) ((k : ℝ) + 1)
    let ν := volume.restrict K
    letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
      (isCompact_closedBall (0 : Vec d) _).measure_ne_top
    let H : ℕ → FieldPair d → ℝ := fun n ω =>
      ∫ x, ‖D n (translate x ω) - G (translate x ω)‖^2 ∂ν
    have hcalc (n : ℕ) := integral_spatial_sq_norm_eq_volume_mul Q hQ ν (D n) G
    have hnonneg (n : ℕ) (ω : FieldPair d) : 0 ≤ H n ω :=
      integral_nonneg fun _ => sq_nonneg _
    have hmean (n : ℕ) : (∫ ω, ‖H n ω‖ ∂Q) = (ν Set.univ).toReal * ‖D n - G‖^2 := by
      calc
        _ = ∫ ω, H n ω ∂Q := integral_congr_ae
          (ae_of_all _ fun ω => Real.norm_of_nonneg (hnonneg n ω))
        _ = _ := (hcalc n).2
    have hs : Summable (fun n => ∫ ω, ‖H n ω‖ ∂Q) := by
      apply Summable.of_nonneg_of_le
        (fun n => integral_nonneg fun _ => norm_nonneg _) ?_
        ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (ν Set.univ).toReal)
      intro n
      rw [hmean]
      calc
        (ν Set.univ).toReal * ‖D n - G‖^2 ≤
            (ν Set.univ).toReal * ((1 / 2 : ℝ)^n)^2 := by
          gcongr
          exact hf n
        _ = (ν Set.univ).toReal * (1 / 4 : ℝ)^n := by
          congr 1
          rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
          norm_num
    exact ae_tendsto_zero_of_summable_integral_norm Q H (fun n => (hcalc n).1) hs
  filter_upwards [ae_all_iff.mpr hballs,
    ae_all_iff.mpr (fun n => ae_horizontalH1_hasWeakGradient_orbit Q hQ (f n)),
    ae_all_iff.mpr (fun n => ae_scalar_orbit_memLp_on_all_compacts Q hQ (f n : Lp ℝ 2 Q)),
    ae_all_iff.mpr (fun n => ae_spatialRealization_memLp_on_all_compacts hQ (D n)),
    ae_spatialRealization_memLp_on_all_compacts hQ G] with ω hB hW hS hD hGG
  refine ⟨hW, hS, ?_⟩
  intro K hK
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp hK.isBounded
  obtain ⟨k, hk⟩ := exists_nat_gt R
  have hsub : K ⊆ Metric.closedBall (0 : Vec d) ((k : ℝ) + 1) :=
    hR.trans (Metric.closedBall_subset_closedBall (le_trans hk.le (by norm_num)))
  apply squeeze_zero (fun n => integral_nonneg fun _ => sq_nonneg _) ?_ (hB k)
  intro n
  let B := Metric.closedBall (0 : Vec d) ((k : ℝ) + 1)
  have hm := (hD n B (isCompact_closedBall (0 : Vec d) _)).sub
    (hGG B (isCompact_closedBall (0 : Vec d) _))
  apply setIntegral_mono_set
    ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)
    (ae_of_all _ fun _ => sq_nonneg _)
    (ae_of_all _ fun _ hx => hsub hx)

end EinsteinRelation.Correctors
