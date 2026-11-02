import EinsteinFull.Calculus.S4GammaSupport
import EinsteinFull.Calculus.S4MartingaleVarianceSupport
import EinsteinFull.Calculus.S4SllnProbSupport

/-!
# A martingale strong law for solutions of the reduced martingale problem

For a smooth regular environment, a solution `P` of the reduced martingale problem and a smooth
`f` with bounded first partials and at most linear growth, the compensated test function
`M_t = f(γ_t) - f(γ_0) - ∫₀ᵗ L f(γ_u) du` satisfies `M_{n²} / n² → 0` almost surely.

The proof cuts `f` off (`cutoffFn`), applies the quadratic-variation bound uniformly in the cutoff
radius (only the first partials of the cutoff enter the carré du champ), lets the radius tend to
infinity with Fatou's lemma, and finishes with Chebyshev and Borel–Cantelli.
-/

open MeasureTheory Filter
open scoped BigOperators NNReal Topology ENNReal

namespace EinsteinFull
open EinsteinRelation

theorem svGenerator_congr {d : ℕ} (A : Vec d → Mat d) (b : Vec d → Vec d) {f g : Vec d → ℝ}
    {y : Vec d} (h : f =ᶠ[𝓝 y] g) :
    External.Draft.svGenerator A b f y = External.Draft.svGenerator A b g y := by
  have h1 : fderiv ℝ f y = fderiv ℝ g y := h.fderiv_eq
  have h2 : ∀ j : Fin d, fderiv ℝ (fun z => fderiv ℝ f z (unitVector j)) y =
      fderiv ℝ (fun z => fderiv ℝ g z (unitVector j)) y := fun j => by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [h.eventuallyEq_nhds] with z hz
    rw [hz.fderiv_eq]
  unfold External.Draft.svGenerator
  simp only [h1, h2]

theorem reducedGenerator_congr_nhds {d : ℕ} {ω : FieldPair d} (hs : IsSmoothFieldPair ω)
    (i : Fin d) (lam : ℝ) {f g : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {y : Vec d} (h : f =ᶠ[𝓝 y] g) :
    reducedGenerator i ω lam f y = reducedGenerator i ω lam g y := by
  rw [reducedGenerator_eq_svGenerator hs i lam (contDiff_two_of_top hf),
    reducedGenerator_eq_svGenerator hs i lam (contDiff_two_of_top hg)]
  exact svGenerator_congr _ _ h

/-- A uniform carré-du-champ bound for the cutoffs of `f`. -/
theorem reduced_cutoff_bound {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {G0 a b : ℝ}
    (hG0 : ∀ y j, |fderiv ℝ f y (unitVector j)| ≤ G0) (hgrow : ∀ y, |f y| ≤ a + b * ‖y‖)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ (χ : Vec d → ℝ) (B : ℝ), ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ y, ‖y‖ ≤ 1 → χ y = 1) ∧
      (∀ y, 2 ≤ ‖y‖ → χ y = 0) ∧ ∀ R : ℝ, 1 ≤ R → ∀ y : Vec d,
        reducedGenerator i ω lam (fun z => cutoffFn χ R f z ^ 2) y -
          2 * cutoffFn χ R f y * reducedGenerator i ω lam (cutoffFn χ R f) y ≤ B := by
  obtain ⟨χ, hχ, hχc, hχ01, hχ1, hχ0⟩ := exists_cutoff d
  obtain ⟨c, hc⟩ := exists_cutoff_deriv_bound hχ hχc
  obtain ⟨_, _, ⟨M1, hM1⟩, _, _, _⟩ := reduced_svHypotheses hΛ hω i lam
  set G : ℝ := G0 + (a + 2 * b) * c with hG
  refine ⟨χ, (d : ℝ) * d * (M1 * (G * G)), hχ, hχ1, hχ0, fun R hR y => ?_⟩
  have hfR := contDiff_cutoffFn hχ hf R
  have hfR2 : ContDiff ℝ 2 (cutoffFn χ R f) := contDiff_two_of_top hfR
  have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun z => cutoffFn χ R f z ^ 2) := hfR.pow 2
  rw [reducedGenerator_eq_svGenerator hs i lam (contDiff_two_of_top hsq),
    reducedGenerator_eq_svGenerator hs i lam hfR2, svGenerator_sq_sub _ _ hfR2 y]
  exact carre_du_champ_le hM1 (fun j => fderiv ℝ (cutoffFn χ R f) y (unitVector j))
    (fun j => abs_fderiv_cutoffFn_le hχ hf hχ0 hχ01 hG0 hgrow ha hb hc hR y j) y

theorem continuous_compensatedTest_path {d : ℕ} {L : (Vec d → ℝ) → Vec d → ℝ} {φ : Vec d → ℝ}
    (hφ : Continuous φ) (hL : Continuous (L φ)) (t : ℝ≥0) :
    Continuous (compensatedTest L φ t) :=
  ((continuous_compensatedTest (L := L) hφ hL).comp
    (continuous_id.prodMk (continuous_const : Continuous fun _ : Path d => (t : ℝ)))).congr
    (fun γ => by simp)

theorem integrable_sq_compensatedTest {d : ℕ} {L : (Vec d → ℝ) → Vec d → ℝ}
    {P : Measure (Path d)} [IsFiniteMeasure P] {φ : Vec d → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hC : ∀ y, |φ y| ≤ C) (hL : Continuous (L φ)) {K : ℝ} (hK : ∀ y, |L φ y| ≤ K) (t : ℝ≥0) :
    Integrable (fun γ => compensatedTest L φ t γ ^ 2) P :=
  integrable_of_continuous_bounded ((continuous_compensatedTest_path hφ hL t).pow 2)
    (C := (2 * C + K * t) ^ 2) fun γ => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_compensatedTest_le hC hK t γ) 2

/-- Second-moment bound, uniform in time, for the compensated test function of `f`. -/
theorem lintegral_sq_reduced_le {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ)
    {P : Measure (Path d)} (hP : SolvesMartingaleProblem (reducedGenerator i ω lam) 0 P)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {G0 a b : ℝ}
    (hG0 : ∀ y j, |fderiv ℝ f y (unitVector j)| ≤ G0) (hgrow : ∀ y, |f y| ≤ a + b * ‖y‖)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ B : ℝ, ∀ t : ℝ≥0,
      ∫⁻ γ, ENNReal.ofReal (compensatedTest (reducedGenerator i ω lam) f t γ ^ 2) ∂P ≤
        ENNReal.ofReal (B * t) := by
  obtain ⟨χ, B, hχ, hχ1, hχ0, hB⟩ := reduced_cutoff_bound hΛ hω hs i lam hf hG0 hgrow ha hb
  refine ⟨B, fun t => ?_⟩
  haveI := hP.1
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

/-- **Strong law along the squares.** -/
theorem reduced_slln_squares {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ)
    {P : Measure (Path d)} (hP : SolvesMartingaleProblem (reducedGenerator i ω lam) 0 P)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {G0 a b : ℝ}
    (hG0 : ∀ y j, |fderiv ℝ f y (unitVector j)| ≤ G0) (hgrow : ∀ y, |f y| ≤ a + b * ‖y‖)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ᵐ γ ∂P, Tendsto (fun n : ℕ =>
      compensatedTest (reducedGenerator i ω lam) f ((n : ℝ≥0) ^ 2) γ / (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := lintegral_sq_reduced_le hΛ hω hs i lam hP hf hG0 hgrow ha hb
  refine ae_tendsto_div_sq (X := fun n γ =>
    compensatedTest (reducedGenerator i ω lam) f ((n : ℝ≥0) ^ 2) γ) (B := B)
    (fun n => (continuous_compensatedTest_path hf.continuous
      (continuous_reducedGenerator_apply hs i lam hf) _).measurable) (fun n => ?_)
  have h := hB ((n : ℝ≥0) ^ 2)
  rw [NNReal.coe_pow, NNReal.coe_natCast] at h
  exact h

end EinsteinFull
