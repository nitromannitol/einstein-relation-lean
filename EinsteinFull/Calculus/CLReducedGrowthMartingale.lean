import EinsteinFull.Calculus.CLReducedCoordinateMartingale
import EinsteinFull.Calculus.CLQuadraticVariationLinear

/-!
# Martingales of compensated tests of linear growth

On a smooth regular environment every solution of the reduced martingale problem from the origin
makes the compensated test of a smooth function with bounded gradient and linear growth a
martingale. The proof is the one for the coordinates (`CLReducedCoordinateMartingale`), with the
second moment of the limit test from `integral_sq_compensated_reduced_of_growth`.
-/

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

/-- On a smooth regular environment the compensated test of a smooth function with bounded
gradient and linear growth is a martingale under every solution of the reduced martingale problem
from the origin. -/
theorem reduced_growth_martingale {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ)
    {P : Measure (Path d)} (hP : SolvesMartingaleProblem (reducedGenerator i ω lam) 0 P)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {G0 a b : ℝ}
    (hG0 : ∀ y j, |fderiv ℝ f y (unitVector j)| ≤ G0) (hgrow : ∀ y, |f y| ≤ a + b * ‖y‖)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Martingale (compensatedTest (reducedGenerator i ω lam) f) (pathFiltration d) P := by
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨χ, B, hχ, hχ1, hχ0, hB⟩ :=
    reduced_cutoff_bound hΛ hω hs i lam hf hG0 hgrow ha hb
  let F : ℕ → Vec d → ℝ := fun k => cutoffFn χ ((k : ℝ) + 1) f
  have hk0 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hFd : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (F k) := fun k => contDiff_cutoffFn hχ hf _
  have hFc : ∀ k, HasCompactSupport (F k) := fun k => hasCompactSupport_cutoffFn f (hk0 k) hχ0
  have hLc : Continuous (reducedGenerator i ω lam f) :=
    continuous_reducedGenerator_apply hs i lam hf
  have hMc (t : ℝ≥0) : Continuous (compensatedTest (reducedGenerator i ω lam) f t) :=
    continuous_compensatedTest_path hf.continuous hLc t
  have hMkc (k : ℕ) (t : ℝ≥0) :
      Continuous (compensatedTest (reducedGenerator i ω lam) (F k) t) :=
    continuous_compensatedTest_path (hFd k).continuous
      (continuous_reducedGenerator_apply hs i lam (hFd k)) t
  -- second moments of the limit test
  set B' : ℝ := (d : ℝ) * d * (Real.exp (2 * Λ₀) * Λ₀ * (G0 * G0)) with hB'def
  have hB' (t : ℝ≥0) :
      MemLp (compensatedTest (reducedGenerator i ω lam) f t) 2 P ∧
        ∫ γ, compensatedTest (reducedGenerator i ω lam) f t γ ^ 2 ∂P ≤ B' * t := by
    obtain ⟨h1, h2⟩ := integral_sq_compensated_reduced_of_growth hΛ hω hs i lam hP hf hG0 hgrow
      ha hb t
    refine ⟨(memLp_two_iff_integrable_sq (hMc t).aestronglyMeasurable).2 h1, ?_⟩
    have hΓ : ∀ y, |carreDuChamp ω f y| ≤ B' := fun y => by
      rw [abs_of_nonneg (carreDuChamp_nonneg hΛ hω _ y)]
      exact carreDuChamp_le hΛ hω hG0 y
    rw [h2]
    calc ∫ γ, pathInt (carreDuChamp ω f) γ t ∂P ≤ ∫ _γ, B' * (t : ℝ) ∂P :=
          integral_mono (integrable_pathInt (continuous_carreDuChamp ω hf) hΓ t)
            (integrable_const _) fun γ => by
              have h := norm_pathInt_le hΓ γ t
              rw [Real.norm_eq_abs] at h
              exact (le_abs_self _).trans h
      _ = B' * t := by simp
  -- uniform second moments of the cutoff tests
  have hsqk (k : ℕ) (t : ℝ≥0) :
      Integrable (fun γ => compensatedTest (reducedGenerator i ω lam) (F k) t γ ^ 2) P ∧
      ∫ γ, compensatedTest (reducedGenerator i ω lam) (F k) t γ ^ 2 ∂P ≤ B * t := by
    obtain ⟨K, hK⟩ := bounded_reducedGenerator_apply hΛ hω hs i lam (hFd k) (hFc k)
    have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun z => F k z ^ 2) := (hFd k).pow 2
    have hsqc : HasCompactSupport (fun z => F k z ^ 2) :=
      (hFc k).comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    obtain ⟨K2, hK2⟩ := bounded_reducedGenerator_apply hΛ hω hs i lam hsq hsqc
    obtain ⟨C, hC⟩ := (hFd k).continuous.bounded_above_of_compact_support (hFc k)
    exact ⟨integrable_sq_compensatedTest (hFd k).continuous
        (fun y => by have := hC y; rwa [Real.norm_eq_abs] at this)
        (continuous_reducedGenerator_apply hs i lam (hFd k)) hK t,
      integral_sq_compensatedTest_le hP (hFd k) (hFc k) hK
        (continuous_reducedGenerator_apply hs i lam (hFd k)) hK2
        (continuous_reducedGenerator_apply hs i lam hsq)
        (fun y => hB _ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) y) t⟩
  -- every path stays in the cutoff ball eventually
  have hev (t : ℝ≥0) (γ : Path d) : ∀ᶠ k : ℕ in atTop,
      compensatedTest (reducedGenerator i ω lam) (F k) t γ =
        compensatedTest (reducedGenerator i ω lam) f t γ := by
    obtain ⟨R0, hR0⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).image
      γ.continuous).isBounded.exists_norm_le
    obtain ⟨N, hN⟩ := exists_nat_gt R0
    filter_upwards [eventually_ge_atTop N] with k hk
    have hR : R0 < (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ k := Nat.cast_le.2 hk
      linarith
    have hball : ∀ u : ℝ≥0, u ≤ t → ‖γ u‖ < (k : ℝ) + 1 := fun u hu =>
      lt_of_le_of_lt (hR0 _ ⟨u, ⟨bot_le, hu⟩, rfl⟩) hR
    have e1 : F k (γ t) = f (γ t) := cutoffFn_eq f (hk0 k) hχ1 (hball t le_rfl).le
    have e0 : F k (γ 0) = f (γ 0) := cutoffFn_eq f (hk0 k) hχ1 (hball 0 bot_le).le
    unfold compensatedTest
    rw [e1, e0]
    congr 1
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le t.coe_nonneg] at hu
    have hut : u.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hu.2
    exact reducedGenerator_congr_nhds hs i lam (hFd k) hf
      (cutoffFn_eventuallyEq f (hk0 k) hχ1 (hball _ hut))
  -- L¹ convergence of the cutoff tests
  have hL1 (t : ℝ≥0) : Tendsto (fun k : ℕ => ∫ γ,
      |compensatedTest (reducedGenerator i ω lam) (F k) t γ -
        compensatedTest (reducedGenerator i ω lam) f t γ| ∂P) atTop (𝓝 0) := by
    let Z : ℕ → Path d → ℝ := fun k γ =>
      compensatedTest (reducedGenerator i ω lam) (F k) t γ -
        compensatedTest (reducedGenerator i ω lam) f t γ
    have hZc (k : ℕ) : Continuous (Z k) := (hMkc k t).sub (hMc t)
    have hXsq : Integrable (fun γ => compensatedTest (reducedGenerator i ω lam) f t γ ^ 2) P :=
      ((memLp_two_iff_integrable_sq (hMc t).aestronglyMeasurable).1 (hB' t).1)
    let V : ℝ := 2 * (B * t) + 2 * (B' * t)
    have hZsq (k : ℕ) : Integrable (fun γ => Z k γ ^ 2) P ∧ ∫ γ, Z k γ ^ 2 ∂P ≤ V := by
      have hi : Integrable (fun γ => 2 * compensatedTest (reducedGenerator i ω lam) (F k) t γ ^ 2 +
          2 * compensatedTest (reducedGenerator i ω lam) f t γ ^ 2) P :=
        ((hsqk k t).1.const_mul 2).add (hXsq.const_mul 2)
      have hle : ∀ γ, Z k γ ^ 2 ≤ 2 * compensatedTest (reducedGenerator i ω lam) (F k) t γ ^ 2 +
          2 * compensatedTest (reducedGenerator i ω lam) f t γ ^ 2 := fun γ => by
        nlinarith [sq_nonneg (compensatedTest (reducedGenerator i ω lam) (F k) t γ +
          compensatedTest (reducedGenerator i ω lam) f t γ)]
      have hZi : Integrable (fun γ => Z k γ ^ 2) P :=
        hi.mono' ((hZc k).pow 2).aestronglyMeasurable
          (ae_of_all _ fun γ => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hle γ)
      refine ⟨hZi, (integral_mono hZi hi hle).trans ?_⟩
      rw [integral_add ((hsqk k t).1.const_mul 2) (hXsq.const_mul 2), integral_const_mul,
        integral_const_mul]
      linarith [(hsqk k t).2, (hB' t).2]
    let ind : ℕ → Path d → ℝ := fun k γ => if Z k γ = 0 then 0 else 1
    have hind_meas (k : ℕ) : Measurable (ind k) :=
      Measurable.ite (measurableSet_eq_fun (hZc k).measurable measurable_const)
        measurable_const measurable_const
    have hind : Tendsto (fun k => ∫ γ, ind k γ ∂P) atTop (𝓝 0) := by
      have h := tendsto_integral_of_dominated_convergence (μ := P) (f := fun _ : Path d => (0 : ℝ))
        (fun _ : Path d => (1 : ℝ))
        (fun k => (hind_meas k).aestronglyMeasurable) (integrable_const 1)
        (fun k => ae_of_all _ fun γ => by
          by_cases hz : Z k γ = 0 <;> simp [ind, hz])
        (ae_of_all _ fun γ => by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [hev t γ] with k hk
          have : Z k γ = 0 := by simp only [Z, hk, sub_self]
          simp [ind, this])
      simpa only [integral_zero] using h
    have hint_ind (k : ℕ) : Integrable (ind k) P :=
      (integrable_const (1 : ℝ)).mono' (hind_meas k).aestronglyMeasurable
        (ae_of_all _ fun γ => by by_cases hz : Z k γ = 0 <;> simp [ind, hz])
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    have hV : 0 ≤ V := by
      have := (hZsq 0).2
      exact le_trans (integral_nonneg fun γ => sq_nonneg _) this
    set c : ℝ := 2 * (V + 1) / ε with hc
    have hcpos : 0 < c := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hind (ε / 2 / (c / 2)) (by positivity)
    refine ⟨N, fun k hk => ?_⟩
    have hb := hN k hk
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun γ => by
      by_cases hz : Z k γ = 0 <;> simp [ind, hz])] at hb
    have hpt : ∀ γ, |Z k γ| ≤ Z k γ ^ 2 / (2 * c) + c / 2 * ind k γ :=
      fun γ => abs_le_sq_div_add_indicator (Z k γ) hcpos
    have hint_rhs : Integrable (fun γ => Z k γ ^ 2 / (2 * c) + c / 2 * ind k γ) P :=
      ((hZsq k).1.div_const _).add ((hint_ind k).const_mul _)
    have habs : Integrable (fun γ => |Z k γ|) P :=
      hint_rhs.mono' (hZc k).abs.aestronglyMeasurable
        (ae_of_all _ fun γ => by rw [Real.norm_eq_abs, abs_abs]; exact hpt γ)
    have hmono := integral_mono habs hint_rhs hpt
    rw [integral_add ((hZsq k).1.div_const _) ((hint_ind k).const_mul _), integral_div,
      integral_const_mul] at hmono
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun γ => abs_nonneg _)]
    have h1 : (∫ γ, Z k γ ^ 2 ∂P) / (2 * c) ≤ V / (2 * c) :=
      div_le_div_of_nonneg_right (hZsq k).2 (by positivity)
    have h2 : V / (2 * c) < ε / 2 := by
      rw [hc, div_lt_iff₀ (by positivity)]
      field_simp
      nlinarith
    have h3 : c / 2 * ∫ γ, ind k γ ∂P < ε / 2 := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < c / 2)] at hb
      linarith [mul_comm (c / 2) (∫ γ, ind k γ ∂P)]
    change (∫ γ, |Z k γ| ∂P) < ε
    linarith
  -- set integrals converge
  have hset (t : ℝ≥0) {A : Set (Path d)} (hA : MeasurableSet A) :
      Tendsto (fun k : ℕ => ∫ γ in A, compensatedTest (reducedGenerator i ω lam) (F k) t γ ∂P)
        atTop (𝓝 (∫ γ in A, compensatedTest (reducedGenerator i ω lam) f t γ ∂P)) := by
    have hXi : Integrable (compensatedTest (reducedGenerator i ω lam) f t) P :=
      (hB' t).1.integrable one_le_two
    have hXki (k : ℕ) : Integrable (compensatedTest (reducedGenerator i ω lam) (F k) t) P :=
      (hP.2.2 (F k) (hFd k) (hFc k)).2.1 t
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
      (fun k => ?_) (hL1 t))
    rw [← integral_sub (hXki k).integrableOn hXi.integrableOn]
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [Real.norm_eq_abs]
    exact setIntegral_le_integral ((hXki k).sub hXi).abs
      (ae_of_all _ fun γ => abs_nonneg _)
  have hadapt := stronglyAdapted_compensatedTest_of_measurable (reducedGenerator i ω lam) f
    hf.continuous hLc.measurable
  refine ⟨hadapt, fun s t hst => ?_⟩
  have hXti : Integrable (compensatedTest (reducedGenerator i ω lam) f t) P :=
    (hB' t).1.integrable one_le_two
  have hXsi : Integrable (compensatedTest (reducedGenerator i ω lam) f s) P :=
    (hB' s).1.integrable one_le_two
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((pathFiltration d).le s) hXti
    (fun _ _ _ => hXsi.integrableOn) (fun A hA _ => ?_)
    (hadapt s).aestronglyMeasurable).symm
  have hA' : MeasurableSet A := (pathFiltration d).le s _ hA
  have hk (k : ℕ) := (hP.2.2 (F k) (hFd k) (hFc k)).2.2.setIntegral_eq hst hA
  exact tendsto_nhds_unique ((hset s hA').congr hk) (hset t hA')

end EinsteinFull.Blueprint
