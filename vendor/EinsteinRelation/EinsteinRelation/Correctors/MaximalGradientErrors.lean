import EinsteinRelation.Correctors.StationaryCubeMaximal
import EinsteinRelation.Correctors.CubeMaximalLocalization
import EinsteinRelation.Correctors.SpatialApproximationIntegrals
import EinsteinRelation.Correctors.EuclideanBallAverageComparison
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform spatial errors of rapid stationary gradient approximations

Source: `paper/main.tex:693-698`. A weak maximal estimate and
Borel--Cantelli make rapid environment-L² errors uniformly small over
all positive integer coordinate cubes on a single full-law event.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors

/-- Geometric maximal tail bounds are summable and eventually exclude
all bad radius indices at once. -/
theorem ae_eventually_uniform_small_of_geometric_tails
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (E : ℕ → ℕ → A → ℝ) (C : ℝ)
    (hbound : ∀ n, μ {a | ∃ k, (1 / 2 : ℝ)^n < E n k a} ≤
      ENNReal.ofReal (C * (1 / 2 : ℝ)^n)) :
    ∀ᵐ a ∂μ, ∀ᶠ n : ℕ in atTop, ∀ k, E n k a ≤ (1 / 2 : ℝ)^n := by
  have hs : Summable (fun n : ℕ => C * (1 / 2 : ℝ)^n) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left C
  have ht : (∑' n, μ {a | ∃ k, (1 / 2 : ℝ)^n < E n k a}) ≠ ⊤ :=
    ne_top_of_le_ne_top hs.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hbound)
  filter_upwards [ae_eventually_notMem ht] with a ha
  exact ha.mono fun n hn k => le_of_not_gt fun hk => hn ⟨k, hk⟩

/-- Rapid L² approximations have almost-sure gradient errors uniformly
small over every positive integer cube radius. -/
theorem ae_uniform_integerCube_gradient_errors_of_rapid {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (D : ℕ → Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (H : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hrapid : ∀ n, ‖D n - H‖ ≤ (1 / 2 : ℝ)^n) :
    ∀ᵐ ω ∂Q, ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (⨍ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1),
        ‖D n (translate x ω) - H (translate x ω)‖ ^ 2 ∂volume) ≤ (1 / 2 : ℝ)^n := by
  obtain ⟨C, hC, hmax⟩ := exists_cube_maximal_weak_bound d
  let F := fun n (ω : FieldPair d) => ‖D n ω - H ω‖ ^ 2
  have hm (n : ℕ) : Measurable (F n) :=
    (((Lp.stronglyMeasurable (D n)).measurable.sub
      (Lp.stronglyMeasurable H).measurable).norm.pow_const 2)
  have hi (n : ℕ) : Integrable (F n) Q :=
    (memLp_two_iff_integrable_sq_norm
      (((Lp.memLp (D n)).sub (Lp.memLp H)).aestronglyMeasurable)).mp
      ((Lp.memLp (D n)).sub (Lp.memLp H))
  have hmean (n : ℕ) : (∫ ω, F n ω ∂Q) = ‖D n - H‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (D n) H] with ω hω
    rw [hω, real_inner_self_eq_norm_sq]
    rfl
  apply ae_eventually_uniform_small_of_geometric_tails Q
    (fun n k ω => ⨍ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1),
      ‖D n (translate x ω) - H (translate x ω)‖ ^ 2 ∂volume) C
  intro n
  have hn : 0 < (1 / 2 : ℝ)^n := pow_pos (by norm_num) _
  have hb := stationary_integerCube_maximal_of_localization d C hC
    (fun f hf N R t hR ht hi => localized_integerCube_maximal_bound d C hmax f hf N R t hR ht hi)
    Q hQ (F n) (hm n) (hi n) (fun _ => sq_nonneg _) _ hn
  have hsub : {ω | ∃ k : ℕ, (1 / 2 : ℝ)^n <
      (⨍ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1),
        ‖D n (translate x ω) - H (translate x ω)‖ ^ 2 ∂volume)} ⊆
      {ω | ∃ k : ℕ, (1 / 2 : ℝ)^n *
        volume.real (Metric.closedBall (0 : Vec d) ((k : ℝ) + 1)) <
        ∫ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1), F n (translate x ω) ∂volume} := by
    rintro ω ⟨k, hk⟩
    have hV : 0 < volume.real (Metric.closedBall (0 : Vec d) ((k : ℝ) + 1)) := by
      rw [Measure.real, Real.volume_pi_closedBall _ (by positivity),
        ENNReal.toReal_ofReal (by positivity)]
      exact pow_pos (by positivity) _
    refine ⟨k, (lt_div_iff₀ hV).mp ?_⟩
    simpa only [average_eq, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
      div_eq_mul_inv, mul_comm, F] using hk
  refine (measure_mono hsub).trans (hb.trans (ENNReal.ofReal_le_ofReal ?_))
  rw [hmean]
  calc
    C / (1 / 2 : ℝ)^n * ‖D n - H‖ ^ 2 ≤ C / (1 / 2 : ℝ)^n * ((1 / 2 : ℝ)^n)^2 := by
      gcongr
      exact hrapid n
    _ = C * (1 / 2 : ℝ)^n := by
      field_simp

/-- The maximal error bound holds simultaneously for every real Euclidean
ball radius at least one, with a constant depending only on dimension. -/
theorem ae_uniform_ball_gradient_errors_of_rapid (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
      (hQ : IsStationary Q) (D : ℕ → Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
      (H : Lp (EuclideanSpace ℝ (Fin d)) 2 Q),
      (∀ n, ‖D n - H‖ ≤ (1 / 2 : ℝ)^n) →
      ∀ᵐ ω ∂Q, ∀ᶠ n : ℕ in atTop, ∀ R : ℝ, 1 ≤ R →
        (⨍ x in External.AKM.ball 0 R,
          ‖D n (translate x ω) - H (translate x ω)‖ ^ 2 ∂volume) ≤ C * (1 / 2 : ℝ)^n := by
  obtain ⟨C, hC, hcompare⟩ := exists_ball_average_le_cube_average d
  refine ⟨C, hC, ?_⟩
  intro Q _ hQ D H hrapid
  have hD := ae_all_iff.mpr fun n =>
    StationarySpatialRealization.ae_spatialRealization_memLp_on_all_compacts hQ (D n)
  have hH := StationarySpatialRealization.ae_spatialRealization_memLp_on_all_compacts hQ H
  filter_upwards [ae_uniform_integerCube_gradient_errors_of_rapid Q hQ D H hrapid, hD, hH]
    with ω hω hDω hHω
  apply hω.mono
  intro n hn R hR
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let k : ℕ := ⌊R⌋₊
  have hlow : R ≤ (k : ℝ) + 1 := (Nat.lt_floor_add_one R).le
  have hhigh : (k : ℝ) + 1 ≤ 2 * R := by
    have hf : (k : ℝ) ≤ R := Nat.floor_le hRpos.le
    linarith
  let K := Metric.closedBall (0 : Vec d) ((k : ℝ) + 1)
  have hmem := (hDω n K (isCompact_closedBall _ _)).sub (hHω K (isCompact_closedBall _ _))
  calc
    _ ≤ C * (⨍ x in K, ‖D n (translate x ω) - H (translate x ω)‖ ^ 2 ∂volume) :=
      hcompare R ((k : ℝ) + 1) hRpos hlow hhigh _ (fun _ => sq_nonneg _)
        ((memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem)
    _ ≤ C * (1 / 2 : ℝ)^n := mul_le_mul_of_nonneg_left (hn k) hC.le

end EinsteinRelation.Correctors
