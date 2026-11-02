import EinsteinFull.Calculus.S4MartingaleSllnSupport

/-!
# Second moments of the reduced diffusion, uniformly in the environment

The second moment of a compensated test function of linear growth is at most `B t`, with `B`
depending only on the ellipticity, the dimension and the growth constants, not on the
environment: the carré du champ is bounded by the explicit coefficient bound. In particular the
compensated coordinates and the coordinates have uniform second moments.
-/

open MeasureTheory Filter
open scoped BigOperators NNReal Topology ENNReal

namespace EinsteinFull
open EinsteinRelation

/-- The second-moment estimate for a given cutoff and carré du champ bound. -/
theorem lintegral_sq_reduced_le_of_cutoff {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ)
    {P : Measure (Path d)} (hP : SolvesMartingaleProblem (reducedGenerator i ω lam) 0 P)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {χ : Vec d → ℝ} {B : ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ1 : ∀ y, ‖y‖ ≤ 1 → χ y = 1)
    (hχ0 : ∀ y, 2 ≤ ‖y‖ → χ y = 0)
    (hB : ∀ R : ℝ, 1 ≤ R → ∀ y : Vec d,
      reducedGenerator i ω lam (fun z => cutoffFn χ R f z ^ 2) y -
        2 * cutoffFn χ R f y * reducedGenerator i ω lam (cutoffFn χ R f) y ≤ B) (t : ℝ≥0) :
    ∫⁻ γ, ENNReal.ofReal (compensatedTest (reducedGenerator i ω lam) f t γ ^ 2) ∂P ≤
      ENNReal.ofReal (B * t) := by
  have := hP.1
  have hk0 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hFd : ∀ k : ℕ, ContDiff ℝ (⊤ : ℕ∞) (cutoffFn χ ((k : ℝ) + 1) f) :=
    fun k => contDiff_cutoffFn hχ hf _
  have hFc : ∀ k : ℕ, HasCompactSupport (cutoffFn χ ((k : ℝ) + 1) f) :=
    fun k => hasCompactSupport_cutoffFn f (hk0 k) hχ0
  have hint : ∀ k : ℕ, ∫ γ, compensatedTest (reducedGenerator i ω lam)
      (cutoffFn χ ((k : ℝ) + 1) f) t γ ^ 2 ∂P ≤ B * t := by
    intro k
    obtain ⟨K, hK⟩ := bounded_reducedGenerator_apply hΛ hω hs i lam (hFd k) (hFc k)
    have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun z => cutoffFn χ ((k : ℝ) + 1) f z ^ 2) := (hFd k).pow 2
    have hsqc : HasCompactSupport (fun z => cutoffFn χ ((k : ℝ) + 1) f z ^ 2) :=
      (hFc k).comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    obtain ⟨K2, hK2⟩ := bounded_reducedGenerator_apply hΛ hω hs i lam hsq hsqc
    exact integral_sq_compensatedTest_le hP (hFd k) (hFc k) hK
      (continuous_reducedGenerator_apply hs i lam (hFd k)) hK2
      (continuous_reducedGenerator_apply hs i lam hsq)
      (fun y => hB _ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) y) t
  have hintg : ∀ k : ℕ, Integrable (fun γ => compensatedTest (reducedGenerator i ω lam)
      (cutoffFn χ ((k : ℝ) + 1) f) t γ ^ 2) P := by
    intro k
    obtain ⟨K, hK⟩ := bounded_reducedGenerator_apply hΛ hω hs i lam (hFd k) (hFc k)
    obtain ⟨C, hC⟩ := (hFd k).continuous.bounded_above_of_compact_support (hFc k)
    exact integrable_sq_compensatedTest (hFd k).continuous
      (fun y => by have := hC y; rwa [Real.norm_eq_abs] at this)
      (continuous_reducedGenerator_apply hs i lam (hFd k)) hK t
  have hev : ∀ γ : Path d, ∀ᶠ k : ℕ in atTop,
      compensatedTest (reducedGenerator i ω lam) (cutoffFn χ ((k : ℝ) + 1) f) t γ =
        compensatedTest (reducedGenerator i ω lam) f t γ := by
    intro γ
    obtain ⟨R0, hR0⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).image
      γ.continuous).isBounded.exists_norm_le
    obtain ⟨N, hN⟩ := exists_nat_gt R0
    filter_upwards [eventually_ge_atTop N] with k hk
    have hR : R0 < (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ k := Nat.cast_le.2 hk
      linarith
    have hball : ∀ u : ℝ≥0, u ≤ t → ‖γ u‖ < (k : ℝ) + 1 := fun u hu =>
      lt_of_le_of_lt (hR0 _ ⟨u, ⟨bot_le, hu⟩, rfl⟩) hR
    have e1 : cutoffFn χ ((k : ℝ) + 1) f (γ t) = f (γ t) :=
      cutoffFn_eq f (hk0 k) hχ1 (hball t le_rfl).le
    have e0 : cutoffFn χ ((k : ℝ) + 1) f (γ 0) = f (γ 0) :=
      cutoffFn_eq f (hk0 k) hχ1 (hball 0 bot_le).le
    unfold compensatedTest
    rw [e1, e0]
    congr 1
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le t.coe_nonneg] at hu
    have hut : u.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hu.2
    exact reducedGenerator_congr_nhds hs i lam (hFd k) hf
      (cutoffFn_eventuallyEq f (hk0 k) hχ1 (hball _ hut))
  have hmeas : ∀ k : ℕ, Measurable fun γ : Path d => ENNReal.ofReal
      (compensatedTest (reducedGenerator i ω lam) (cutoffFn χ ((k : ℝ) + 1) f) t γ ^ 2) :=
    fun k => ENNReal.measurable_ofReal.comp
      (((continuous_compensatedTest_path (hFd k).continuous
        (continuous_reducedGenerator_apply hs i lam (hFd k)) t).pow 2).measurable)
  have hfatou := lintegral_liminf_le (μ := P) (u := (atTop : Filter ℕ)) hmeas
  have hlim : ∀ γ : Path d, liminf (fun k : ℕ => ENNReal.ofReal
      (compensatedTest (reducedGenerator i ω lam) (cutoffFn χ ((k : ℝ) + 1) f) t γ ^ 2)) atTop =
      ENNReal.ofReal (compensatedTest (reducedGenerator i ω lam) f t γ ^ 2) := by
    intro γ
    rw [Filter.liminf_congr ((hev γ).mono fun k hk => by rw [hk])]
    exact Filter.liminf_const _
  simp only [hlim] at hfatou
  refine hfatou.trans ?_
  have hle : ∀ k : ℕ, ∫⁻ γ, ENNReal.ofReal (compensatedTest (reducedGenerator i ω lam)
      (cutoffFn χ ((k : ℝ) + 1) f) t γ ^ 2) ∂P ≤ ENNReal.ofReal (B * t) := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hintg k) (ae_of_all _ fun γ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hint k)
  calc liminf (fun k : ℕ => ∫⁻ γ, ENNReal.ofReal (compensatedTest (reducedGenerator i ω lam)
        (cutoffFn χ ((k : ℝ) + 1) f) t γ ^ 2) ∂P) atTop
      ≤ liminf (fun _ : ℕ => ENNReal.ofReal (B * t)) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)
    _ = ENNReal.ofReal (B * t) := Filter.liminf_const _

/-- The carré du champ bound of the cutoffs, uniformly in the environment. -/
theorem reduced_cutoff_bound_uniform {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) (i : Fin d) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {G0 a b : ℝ}
    (hG0 : ∀ y j, |fderiv ℝ f y (unitVector j)| ≤ G0) (hgrow : ∀ y, |f y| ≤ a + b * ‖y‖)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ (χ : Vec d → ℝ) (B : ℝ), ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ y, ‖y‖ ≤ 1 → χ y = 1) ∧
      (∀ y, 2 ≤ ‖y‖ → χ y = 0) ∧ ∀ ω : FieldPair d, IsRegular Λ₀ ω → IsSmoothFieldPair ω →
        ∀ R : ℝ, 1 ≤ R → ∀ y : Vec d,
          reducedGenerator i ω lam (fun z => cutoffFn χ R f z ^ 2) y -
            2 * cutoffFn χ R f y * reducedGenerator i ω lam (cutoffFn χ R f) y ≤ B := by
  obtain ⟨χ, hχ, hχc, hχ01, hχ1, hχ0⟩ := exists_cutoff d
  obtain ⟨c, hc⟩ := exists_cutoff_deriv_bound hχ hχc
  set G : ℝ := G0 + (a + 2 * b) * c with hG
  refine ⟨χ, (d : ℝ) * d * (Real.exp (2 * Λ₀) * Λ₀ * (G * G)), hχ, hχ1, hχ0,
    fun ω hω hs R hR y => ?_⟩
  have hM1 : ∀ x k j, |reducedCoefficient ω x k j| ≤ Real.exp (2 * Λ₀) * Λ₀ :=
    abs_reducedCoefficient_le hΛ hω
  have hfR := contDiff_cutoffFn hχ hf R
  have hfR2 : ContDiff ℝ 2 (cutoffFn χ R f) := contDiff_two_of_top hfR
  have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun z => cutoffFn χ R f z ^ 2) := hfR.pow 2
  rw [reducedGenerator_eq_svGenerator hs i lam (contDiff_two_of_top hsq),
    reducedGenerator_eq_svGenerator hs i lam hfR2, svGenerator_sq_sub _ _ hfR2 y]
  exact carre_du_champ_le hM1 (fun j => fderiv ℝ (cutoffFn χ R f) y (unitVector j))
    (fun j => abs_fderiv_cutoffFn_le hχ hf hχ0 hχ01 hG0 hgrow ha hb hc hR y j) y

/-- Second moments of compensated test functions, uniformly in the environment. -/
theorem lintegral_sq_reduced_le_uniform {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) (i : Fin d) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {G0 a b : ℝ}
    (hG0 : ∀ y j, |fderiv ℝ f y (unitVector j)| ≤ G0) (hgrow : ∀ y, |f y| ≤ a + b * ‖y‖)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ω : FieldPair d, IsRegular Λ₀ ω → IsSmoothFieldPair ω →
      ∀ P : Measure (Path d), SolvesMartingaleProblem (reducedGenerator i ω lam) 0 P →
        ∀ t : ℝ≥0, ∫⁻ γ, ENNReal.ofReal (compensatedTest (reducedGenerator i ω lam) f t γ ^ 2)
          ∂P ≤ ENNReal.ofReal (B * t) := by
  obtain ⟨χ, B, hχ, hχ1, hχ0, hB⟩ := reduced_cutoff_bound_uniform hΛ i lam hf hG0 hgrow ha hb
  refine ⟨max B 0, le_max_right _ _, fun ω hω hs P hP t => ?_⟩
  refine (lintegral_sq_reduced_le_of_cutoff hΛ hω hs i lam hP hf hχ hχ1 hχ0
    (fun R hR y => (hB ω hω hs R hR y).trans (le_max_left _ _)) t)

end EinsteinFull
