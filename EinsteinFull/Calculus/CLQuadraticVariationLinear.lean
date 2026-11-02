import EinsteinFull.Calculus.CLQuadraticVariation
import EinsteinFull.Calculus.CLTwoSidedDFGWInputs

/-!
# The quadratic variation of linear test functions

The compensated linear test function `e · y` of the unforced reduced diffusion has second moment
equal to the expected time integral of `e · a e`. The linear function is approximated by smooth
cutoffs; differences of cutoffs have carré du champ supported outside a large ball and bounded
uniformly, so the compensated cutoffs converge in `L²`, and the carré du champ of the cutoffs is
uniformly bounded with the right pointwise limit.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology ENNReal BigOperators

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

/-- The linear form `y ↦ e · y`. -/
def dotCLM (e : Vec d) : Vec d →L[ℝ] ℝ := ∑ k, e k • ContinuousLinearMap.proj (R := ℝ)
  (φ := fun _ : Fin d => ℝ) k

theorem dotCLM_apply (e y : Vec d) : dotCLM e y = dot e y := by
  simp [dotCLM, dot]

theorem contDiff_dot (e : Vec d) : ContDiff ℝ (⊤ : ℕ∞) fun y : Vec d => dot e y := by
  have h : (fun y : Vec d => dot e y) = dotCLM e := funext fun y => (dotCLM_apply e y).symm
  rw [h]
  exact (dotCLM e).contDiff

theorem fderiv_dot_apply (e y : Vec d) (k : Fin d) :
    fderiv ℝ (fun y : Vec d => dot e y) y (unitVector k) = e k := by
  have h : (fun y : Vec d => dot e y) = dotCLM e := funext fun y => (dotCLM_apply e y).symm
  rw [h, (dotCLM e).fderiv, dotCLM_apply]
  simp [dot, unitVector, Pi.single_apply]

theorem abs_dot_le (e y : Vec d) : |dot e y| ≤ 0 + (∑ k, |e k|) * ‖y‖ := by
  rw [zero_add, dot, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y k)
    (abs_nonneg _)

theorem carreDuChamp_eq_dot (ω : FieldPair d) (u : Vec d → ℝ) (y : Vec d) :
    carreDuChamp ω u y = dot (fun k => fderiv ℝ u y (unitVector k))
      ((reducedCoefficient ω y).mulVec fun k => fderiv ℝ u y (unitVector k)) := by
  simp only [carreDuChamp, dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem carreDuChamp_nonneg {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (u : Vec d → ℝ) (y : Vec d) : 0 ≤ carreDuChamp ω u y := by
  obtain ⟨c, hc, hell⟩ := reducedCoefficient_elliptic hΛ hω
  rw [carreDuChamp_eq_dot]
  refine le_trans ?_ (hell y _)
  have : 0 ≤ euclideanSq (fun k => fderiv ℝ u y (unitVector k)) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun k _ => mul_self_nonneg _
  positivity

theorem carreDuChamp_le {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    {u : Vec d → ℝ} {g : ℝ} (hg : ∀ y k, |fderiv ℝ u y (unitVector k)| ≤ g) (y : Vec d) :
    carreDuChamp ω u y ≤ (d : ℝ) * d * (Real.exp (2 * Λ₀) * Λ₀ * (g * g)) :=
  carre_du_champ_le (abs_reducedCoefficient_le hΛ hω) _ (fun k => hg y k) y

theorem carreDuChamp_congr {ω : FieldPair d} {u v : Vec d → ℝ} {y : Vec d} (h : u =ᶠ[𝓝 y] v) :
    carreDuChamp ω u y = carreDuChamp ω v y := by
  simp only [carreDuChamp, h.fderiv_eq]

theorem carreDuChamp_dot (ω : FieldPair d) (e y : Vec d) :
    carreDuChamp ω (fun y => dot e y) y = dot e ((reducedCoefficient ω y).mulVec e) := by
  rw [carreDuChamp_eq_dot]
  simp only [fderiv_dot_apply]

/-- Fubini for the time integral along paths of a bounded measurable observable. -/
theorem integral_pathInt_eq {P : Measure (Path d)} [IsProbabilityMeasure P] {h : Vec d → ℝ}
    (hm : Measurable h) {B : ℝ} (hB : ∀ y, |h y| ≤ B) (t : ℝ≥0) :
    ∫ γ, pathInt h γ t ∂P = ∫ s in (0 : ℝ)..t, ∫ γ, h (γ s.toNNReal) ∂P := by
  have hF : Measurable fun p : Path d × ℝ => h (p.1 p.2.toNNReal) :=
    hm.comp (continuous_pathEval d).measurable
  have hint : Integrable (fun p : Path d × ℝ => h (p.1 p.2.toNNReal))
      (P.prod (volume.restrict (Set.Ioc 0 (t : ℝ)))) := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
      constructor
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    exact Integrable.of_bound hF.aestronglyMeasurable B (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      exact hB _)
  simp only [pathInt]
  rw [intervalIntegral.integral_of_le t.coe_nonneg]
  simp_rw [intervalIntegral.integral_of_le t.coe_nonneg]
  exact integral_integral_swap hint

theorem norm_pathInt_le {g : Vec d → ℝ} {B : ℝ} (hB : ∀ y, |g y| ≤ B) (γ : Path d) (t : ℝ≥0) :
    ‖pathInt g γ t‖ ≤ B * t := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0)
    (b := (t : ℝ)) (C := B) (f := fun u : ℝ => g (γ u.toNNReal))
    (fun u _ => by rw [Real.norm_eq_abs]; exact hB _)
  rwa [sub_zero, abs_of_nonneg t.coe_nonneg] at this

theorem integrable_pathInt {P : Measure (Path d)} [IsFiniteMeasure P] {g : Vec d → ℝ}
    (hg : Continuous g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) (t : ℝ≥0) :
    Integrable (fun γ => pathInt g γ t) P :=
  Integrable.of_bound (continuous_pathInt_path hg t).aestronglyMeasurable (B * t)
    (ae_of_all _ fun γ => norm_pathInt_le hB γ t)

theorem pathInt_mono {g h : Vec d → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hle : ∀ y, g y ≤ h y) (γ : Path d) (t : ℝ≥0) : pathInt g γ t ≤ pathInt h γ t :=
  intervalIntegral.integral_mono_on t.coe_nonneg
    ((hg.comp (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable 0 t)
    ((hh.comp (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable 0 t)
    fun _ _ => hle _

/-- Expected path integrals converge when the integrands are uniformly bounded and eventually
agree with the limit on every ball. -/
theorem tendsto_integral_pathInt {P : Measure (Path d)} [IsProbabilityMeasure P]
    {g : ℕ → Vec d → ℝ} {h : Vec d → ℝ} (hg : ∀ n, Continuous (g n)) {B : ℝ}
    (hB : ∀ n y, |g n y| ≤ B) (hev : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ y : Vec d, ‖y‖ ≤ R → g n y = h y)
    (t : ℝ≥0) :
    Tendsto (fun n => ∫ γ, pathInt (g n) γ t ∂P) atTop (𝓝 (∫ γ, pathInt h γ t ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => B * t)
    (fun n => (continuous_pathInt_path (hg n) t).aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all _ fun γ => norm_pathInt_le (hB n) γ t) (ae_of_all _ fun γ => ?_)
  obtain ⟨R0, hR0⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).image
    γ.continuous).isBounded.exists_norm_le
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev R0] with n hn
  simp only [pathInt]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le t.coe_nonneg] at hu
  have hut : u.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hu.2
  exact (hn _ (hR0 _ ⟨u.toNNReal, ⟨bot_le, hut⟩, rfl⟩)).symm

theorem continuous_carreDuChamp (ω : FieldPair d) {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    Continuous (carreDuChamp ω u) := by
  unfold carreDuChamp
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
  exact ((continuous_reducedCoefficient ω).matrix_elem k l).mul
    ((continuous_fderiv_apply_first (contDiff_two_of_top hu) k).mul
      (continuous_fderiv_apply_first (contDiff_two_of_top hu) l))

theorem sq_add_le_mul {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    (x + y) ^ 2 ≤ (1 + δ) * x ^ 2 + (1 + δ⁻¹) * y ^ 2 := by
  have hδ' : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
  have e : δ⁻¹ * (δ * x - y) ^ 2 = δ * x ^ 2 - 2 * x * y + δ⁻¹ * y ^ 2 := by
    have : δ⁻¹ * (δ * x - y) ^ 2 =
        (δ⁻¹ * δ) * δ * x ^ 2 - 2 * (δ⁻¹ * δ) * x * y + δ⁻¹ * y ^ 2 := by ring
    rw [this, hδ']
    ring
  have h0 : 0 ≤ δ⁻¹ * (δ * x - y) ^ 2 := by positivity
  nlinarith [h0, e]

theorem le_of_forall_one_add_mul_le {x y : ℝ} (h : ∀ δ : ℝ, 0 < δ → x ≤ (1 + δ) * y) : x ≤ y := by
  have hlim : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1)) * y) atTop (𝓝 ((1 + 0) * y)) :=
    (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).mul tendsto_const_nhds
  rw [add_zero, one_mul] at hlim
  exact ge_of_tendsto' hlim fun n => h _ (by positivity)

section Growth

variable {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (hs : IsSmoothFieldPair ω)
  (i : Fin d) (lam : ℝ) {P : Measure (Path d)}
  (hP : SolvesMartingaleProblem (reducedGenerator i ω lam) 0 P)

include hΛ hω hs hP in
/-- For a smooth function with bounded gradient and linear growth, the compensated process is
square integrable under a reduced martingale problem and its second moment is the expected time
integral of the carré du champ. -/
theorem integral_sq_compensated_reduced_of_growth {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {G0 a b : ℝ} (hG0 : ∀ y j, |fderiv ℝ f y (unitVector j)| ≤ G0)
    (hgrow : ∀ y, |f y| ≤ a + b * ‖y‖) (ha : 0 ≤ a) (hb : 0 ≤ b) (t : ℝ≥0) :
    Integrable (fun γ => compensatedTest (reducedGenerator i ω lam) f t γ ^ 2) P ∧
      ∫ γ, compensatedTest (reducedGenerator i ω lam) f t γ ^ 2 ∂P =
        ∫ γ, pathInt (carreDuChamp ω f) γ (t : ℝ) ∂P := by
  have := hP.1
  obtain ⟨χ, hχ, hχc, hχ01, hχ1, hχ0⟩ := exists_cutoff d
  obtain ⟨c, hc⟩ := exists_cutoff_deriv_bound hχ hχc
  set G : ℝ := G0 + (a + 2 * b) * c with hG
  set Mc : ℝ := Real.exp (2 * Λ₀) * Λ₀ with hMc
  have hMc0 : 0 ≤ Mc := by positivity
  let F : ℕ → Vec d → ℝ := fun n => cutoffFn χ ((n : ℝ) + 1) f
  have hk0 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hk1 : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hFd : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (F k) := fun k => contDiff_cutoffFn hχ hf _
  have hFc : ∀ k, HasCompactSupport (F k) := fun k => hasCompactSupport_cutoffFn f (hk0 k) hχ0
  have hFg : ∀ k y j, |fderiv ℝ (F k) y (unitVector j)| ≤ G := fun k y j =>
    abs_fderiv_cutoffFn_le hχ hf hχ0 hχ01 hG0 hgrow ha hb hc (hk1 k) y j
  have hFeq : ∀ (k : ℕ) (y : Vec d), ‖y‖ < (k : ℝ) + 1 → F k =ᶠ[𝓝 y] f := fun k y hy =>
    cutoffFn_eventuallyEq f (hk0 k) hχ1 hy
  let M : Path d → ℝ := compensatedTest (reducedGenerator i ω lam) f t
  let Mn : ℕ → Path d → ℝ := fun n => compensatedTest (reducedGenerator i ω lam) (F n) t
  have hMc' : Continuous M := continuous_compensatedTest_path hf.continuous
    (continuous_reducedGenerator_apply hs i lam hf) t
  have hMnc : ∀ n, Continuous (Mn n) := fun n => continuous_compensatedTest_path
    (hFd n).continuous (continuous_reducedGenerator_apply hs i lam (hFd n)) t
  have hsqint : ∀ {u : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      Integrable (fun γ => compensatedTest (reducedGenerator i ω lam) u t γ ^ 2) P := by
    intro u hu huc
    obtain ⟨K, hK⟩ := bounded_reducedGenerator_apply hΛ hω hs i lam hu huc
    obtain ⟨C, hC⟩ := hu.continuous.bounded_above_of_compact_support huc
    exact integrable_sq_compensatedTest hu.continuous
      (fun y => by have := hC y; rwa [Real.norm_eq_abs] at this)
      (continuous_reducedGenerator_apply hs i lam hu) hK t
  have hMev : ∀ γ : Path d, ∀ᶠ k : ℕ in atTop, Mn k γ = M γ := by
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
    have e1 : F k (γ t) = f (γ t) := cutoffFn_eq f (hk0 k) hχ1 (hball t le_rfl).le
    have e0 : F k (γ 0) = f (γ 0) := cutoffFn_eq f (hk0 k) hχ1 (hball 0 bot_le).le
    show compensatedTest (reducedGenerator i ω lam) (F k) t γ = compensatedTest (reducedGenerator i ω lam) f t γ
    unfold compensatedTest
    rw [e1, e0]
    congr 1
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le t.coe_nonneg] at hu
    have hut : u.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hu.2
    exact reducedGenerator_congr_nhds hs i lam (hFd k) hf (hFeq k _ (hball _ hut))
  -- the tail weights
  let h : ℕ → Vec d → ℝ := fun n y => min 1 (max 0 (‖y‖ - n))
  have hhc : ∀ n, Continuous (h n) := fun n =>
    continuous_const.min (continuous_const.max (continuous_norm.sub continuous_const))
  have hh0 : ∀ n y, 0 ≤ h n y := fun n y => le_min zero_le_one (le_max_left _ _)
  have hh01 : ∀ n y, |h n y| ≤ 1 := fun n y => by
    rw [abs_of_nonneg (hh0 n y)]
    exact min_le_left _ _
  have hh1 : ∀ (n : ℕ) (y : Vec d), (n : ℝ) + 1 ≤ ‖y‖ → h n y = 1 := fun n y hy => by
    refine min_eq_left ?_
    exact le_max_of_le_right (by linarith)
  set ε : ℕ → ℝ := fun n => ∫ γ, pathInt (h n) γ t ∂P with hε
  have hε0 : ∀ n, 0 ≤ ε n := fun n => integral_nonneg fun γ =>
    intervalIntegral.integral_nonneg t.coe_nonneg fun u _ => hh0 n _
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := tendsto_integral_pathInt (P := P) (h := fun _ => (0 : ℝ)) hhc hh01 (fun R => by
      obtain ⟨N, hN⟩ := exists_nat_gt R
      filter_upwards [eventually_ge_atTop N] with n hn y hy
      have : (N : ℝ) ≤ n := Nat.cast_le.2 hn
      show min 1 (max 0 (‖y‖ - n)) = 0
      rw [max_eq_left (by linarith), min_eq_right zero_le_one]) t
    have h0 : ∫ γ, pathInt (fun _ : Vec d => (0 : ℝ)) γ t ∂P = 0 := by simp [pathInt]
    rw [h0] at this
    exact this
  set B' : ℝ := (d : ℝ) * d * (Mc * ((2 * G) * (2 * G))) with hB'
  have hB'0 : 0 ≤ B' := mul_nonneg (by positivity) (mul_nonneg hMc0 (mul_self_nonneg _))
  -- cutoff differences
  have hdiffint : ∀ n m, Integrable (fun γ => (Mn m γ - Mn n γ) ^ 2) P := by
    intro n m
    refine (hsqint ((hFd m).sub (hFd n)) ((hFc m).sub (hFc n))).congr (ae_of_all _ fun γ => ?_)
    show compensatedTest _ (fun x => F m x - F n x) t γ ^ 2 =
      (compensatedTest _ (F m) t γ - compensatedTest _ (F n) t γ) ^ 2
    rw [compensatedTest_sub_reduced hs i lam (hFd m) (hFd n)]
  have hdiff : ∀ n m, n ≤ m → ∫ γ, (Mn m γ - Mn n γ) ^ 2 ∂P ≤ B' * ε n := by
    intro n m hnm
    have e1 := integral_sq_compensated_reduced hΛ hω hs i lam hP ((hFd m).sub (hFd n))
      ((hFc m).sub (hFc n)) t
    have e2 : ∫ γ, (Mn m γ - Mn n γ) ^ 2 ∂P =
        ∫ γ, pathInt (carreDuChamp ω (fun y => F m y - F n y)) γ t ∂P := by
      rw [← e1]
      refine integral_congr_ae (ae_of_all _ fun γ => ?_)
      show (compensatedTest _ (F m) t γ - compensatedTest _ (F n) t γ) ^ 2 =
        compensatedTest _ (fun x => F m x - F n x) t γ ^ 2
      rw [compensatedTest_sub_reduced hs i lam (hFd m) (hFd n)]
    have hpt : ∀ y, carreDuChamp ω (fun y => F m y - F n y) y ≤ B' * h n y := by
      intro y
      by_cases hy : ‖y‖ < (n : ℝ) + 1
      · have hy' : ‖y‖ < (m : ℝ) + 1 := hy.trans_le (by
          have : (n : ℝ) ≤ m := Nat.cast_le.2 hnm
          linarith)
        have hz : (fun y => F m y - F n y) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
          filter_upwards [hFeq m y hy', hFeq n y hy] with z h1 h2
          simp [h1, h2]
        rw [carreDuChamp_congr hz]
        have : carreDuChamp ω (fun _ => (0 : ℝ)) y = 0 := by simp [carreDuChamp]
        rw [this]
        exact mul_nonneg hB'0 (hh0 n y)
      · rw [hh1 n y (not_lt.1 hy), mul_one]
        refine carreDuChamp_le hΛ hω (g := 2 * G) (fun z k => ?_) y
        have hd : HasFDerivAt (fun y => F m y - F n y)
            (fderiv ℝ (F m) z - fderiv ℝ (F n) z) z :=
          ((hFd m).differentiable (by simp) z).hasFDerivAt.sub
            ((hFd n).differentiable (by simp) z).hasFDerivAt
        rw [hd.fderiv, sub_apply]
        have h1 := abs_le.1 (hFg m z k)
        have h2 := abs_le.1 (hFg n z k)
        exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    have hcD : Continuous (carreDuChamp ω (fun y => F m y - F n y)) :=
      continuous_carreDuChamp ω ((hFd m).sub (hFd n))
    have hcB : Continuous fun y => B' * h n y := continuous_const.mul (hhc n)
    rw [e2]
    calc ∫ γ, pathInt (carreDuChamp ω (fun y => F m y - F n y)) γ t ∂P
        ≤ ∫ γ, pathInt (fun y => B' * h n y) γ t ∂P := by
          refine integral_mono (integrable_pathInt hcD (B := B' * 1) (fun y => ?_) t)
            (integrable_pathInt hcB (B := B' * 1) (fun y => ?_) t)
            (fun γ => pathInt_mono hcD hcB hpt γ t)
          · rw [abs_of_nonneg (carreDuChamp_nonneg hΛ hω _ y)]
            exact (hpt y).trans (mul_le_mul_of_nonneg_left
              ((le_abs_self _).trans (hh01 n y)) hB'0)
          · rw [abs_mul, abs_of_nonneg hB'0]
            exact mul_le_mul_of_nonneg_left (hh01 n y) hB'0
      _ = B' * ε n := by
          simp only [pathInt, intervalIntegral.integral_const_mul]
          exact integral_const_mul _ _
  -- Fatou in the first index
  have hfat : ∀ n, ∫⁻ γ, ENNReal.ofReal ((M γ - Mn n γ) ^ 2) ∂P ≤ ENNReal.ofReal (B' * ε n) := by
    intro n
    have hmeas : ∀ m, Measurable fun γ => ENNReal.ofReal ((Mn m γ - Mn n γ) ^ 2) := fun m =>
      ENNReal.measurable_ofReal.comp ((((hMnc m).sub (hMnc n)).pow 2).measurable)
    have hfatou := lintegral_liminf_le (μ := P) (u := (atTop : Filter ℕ)) hmeas
    have hlim : ∀ γ, liminf (fun m => ENNReal.ofReal ((Mn m γ - Mn n γ) ^ 2)) atTop =
        ENNReal.ofReal ((M γ - Mn n γ) ^ 2) := by
      intro γ
      rw [Filter.liminf_congr ((hMev γ).mono fun m hm => by rw [hm])]
      exact Filter.liminf_const _
    simp only [hlim] at hfatou
    refine hfatou.trans ?_
    calc liminf (fun m => ∫⁻ γ, ENNReal.ofReal ((Mn m γ - Mn n γ) ^ 2) ∂P) atTop
        ≤ liminf (fun _ : ℕ => ENNReal.ofReal (B' * ε n)) atTop := by
          refine Filter.liminf_le_liminf ?_
          filter_upwards [eventually_ge_atTop n] with m hm
          rw [← ofReal_integral_eq_lintegral_ofReal (hdiffint n m)
            (ae_of_all _ fun γ => sq_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hdiff n m hm)
      _ = ENNReal.ofReal (B' * ε n) := Filter.liminf_const _
  have hlimint : ∀ n, Integrable (fun γ => (M γ - Mn n γ) ^ 2) P := by
    intro n
    refine ⟨((hMc'.sub (hMnc n)).pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun γ => sq_nonneg _)]
    exact (hfat n).trans_lt ENNReal.ofReal_lt_top
  have hlimle : ∀ n, ∫ γ, (M γ - Mn n γ) ^ 2 ∂P ≤ B' * ε n := by
    intro n
    have h1 := ofReal_integral_eq_lintegral_ofReal (hlimint n) (ae_of_all _ fun γ => sq_nonneg _)
    have h2 := hfat n
    rw [← h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB'0 (hε0 n))).1 h2
  have hMnint : ∀ n, Integrable (fun γ => Mn n γ ^ 2) P := fun n => hsqint (hFd n) (hFc n)
  have hMint : Integrable (fun γ => M γ ^ 2) P := by
    refine ((hlimint 0).const_mul 2 |>.add ((hMnint 0).const_mul 2)).mono'
      ((hMc'.pow 2).aestronglyMeasurable) (ae_of_all _ fun γ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    show M γ ^ 2 ≤ 2 * (M γ - Mn 0 γ) ^ 2 + 2 * Mn 0 γ ^ 2
    nlinarith [sq_nonneg (M γ - 2 * Mn 0 γ)]
  refine ⟨hMint, ?_⟩
  -- the carré du champ integrals of the cutoffs
  have hcn : ∀ n, ∫ γ, Mn n γ ^ 2 ∂P = ∫ γ, pathInt (carreDuChamp ω (F n)) γ t ∂P := fun n =>
    integral_sq_compensated_reduced hΛ hω hs i lam hP (hFd n) (hFc n) t
  have hclim : Tendsto (fun n => ∫ γ, Mn n γ ^ 2 ∂P) atTop
      (𝓝 (∫ γ, pathInt (carreDuChamp ω f) γ t ∂P)) := by
    simp only [hcn]
    refine tendsto_integral_pathInt (fun n => continuous_carreDuChamp ω (hFd n))
      (B := (d : ℝ) * d * (Mc * (G * G))) (fun n y => ?_) (fun R => ?_) t
    · rw [abs_of_nonneg (carreDuChamp_nonneg hΛ hω _ y)]
      exact carreDuChamp_le hΛ hω (hFg n) y
    · obtain ⟨N, hN⟩ := exists_nat_gt R
      filter_upwards [eventually_ge_atTop N] with n hn y hy
      have : (N : ℝ) ≤ n := Nat.cast_le.2 hn
      exact carreDuChamp_congr (hFeq n y (by linarith))
  set A := ∫ γ, M γ ^ 2 ∂P with hA
  set C := ∫ γ, pathInt (carreDuChamp ω f) γ t ∂P with hC
  have hA0 : 0 ≤ A := integral_nonneg fun γ => sq_nonneg _
  have hpair : ∀ δ : ℝ, 0 < δ → ∀ n, ∫ γ, Mn n γ ^ 2 ∂P ≤ (1 + δ) * A + (1 + δ⁻¹) * (B' * ε n) ∧
      A ≤ (1 + δ) * ∫ γ, Mn n γ ^ 2 ∂P + (1 + δ⁻¹) * (B' * ε n) := by
    intro δ hδ n
    have hdi : Integrable (fun γ => (Mn n γ - M γ) ^ 2) P :=
      (hlimint n).congr (ae_of_all _ fun γ => by ring)
    constructor
    · calc ∫ γ, Mn n γ ^ 2 ∂P
          ≤ ∫ γ, ((1 + δ) * M γ ^ 2 + (1 + δ⁻¹) * (M γ - Mn n γ) ^ 2) ∂P := by
            refine integral_mono (hMnint n) ((hMint.const_mul _).add ((hlimint n).const_mul _))
              fun γ => ?_
            have := sq_add_le_mul hδ (M γ) (Mn n γ - M γ)
            rw [add_sub_cancel] at this
            calc Mn n γ ^ 2 ≤ (1 + δ) * M γ ^ 2 + (1 + δ⁻¹) * (Mn n γ - M γ) ^ 2 := this
              _ = (1 + δ) * M γ ^ 2 + (1 + δ⁻¹) * (M γ - Mn n γ) ^ 2 := by ring
        _ = (1 + δ) * A + (1 + δ⁻¹) * ∫ γ, (M γ - Mn n γ) ^ 2 ∂P := by
            rw [integral_add (hMint.const_mul _) ((hlimint n).const_mul _), integral_const_mul,
              integral_const_mul]
        _ ≤ (1 + δ) * A + (1 + δ⁻¹) * (B' * ε n) := by
            have : 0 ≤ 1 + δ⁻¹ := by positivity
            nlinarith [hlimle n]
    · calc A ≤ ∫ γ, ((1 + δ) * Mn n γ ^ 2 + (1 + δ⁻¹) * (M γ - Mn n γ) ^ 2) ∂P := by
            refine integral_mono hMint (((hMnint n).const_mul _).add ((hlimint n).const_mul _))
              fun γ => ?_
            have := sq_add_le_mul hδ (Mn n γ) (M γ - Mn n γ)
            rwa [add_sub_cancel] at this
        _ = (1 + δ) * ∫ γ, Mn n γ ^ 2 ∂P + (1 + δ⁻¹) * ∫ γ, (M γ - Mn n γ) ^ 2 ∂P := by
            rw [integral_add ((hMnint n).const_mul _) ((hlimint n).const_mul _),
              integral_const_mul, integral_const_mul]
        _ ≤ (1 + δ) * ∫ γ, Mn n γ ^ 2 ∂P + (1 + δ⁻¹) * (B' * ε n) := by
            have : 0 ≤ 1 + δ⁻¹ := by positivity
            nlinarith [hlimle n]
  have hεt : ∀ δ : ℝ, Tendsto (fun n => (1 + δ⁻¹) * (B' * ε n)) atTop (𝓝 0) := fun δ => by
    simpa using (tendsto_const_nhds (x := 1 + δ⁻¹)).mul
      ((tendsto_const_nhds (x := B')).mul hεlim)
  refine le_antisymm (le_of_forall_one_add_mul_le fun δ hδ => ?_)
    (le_of_forall_one_add_mul_le fun δ hδ => ?_)
  · have := le_of_tendsto_of_tendsto' tendsto_const_nhds
      ((hclim.const_mul (1 + δ)).add (hεt δ)) fun n => (hpair δ hδ n).2
    simpa using this
  · have := le_of_tendsto_of_tendsto' hclim (tendsto_const_nhds.add (hεt δ))
      fun n => (hpair δ hδ n).1
    simpa using this

include hΛ hω hs hP in
/-- The second moment of the compensated linear test function `e · y` is the expected time
integral of `e · a e` along the path. -/
theorem integral_sq_compensated_dot (e : Vec d) (t : ℝ≥0) :
    Integrable (fun γ => compensatedTest (reducedGenerator i ω lam) (fun y => dot e y) t γ ^ 2)
        P ∧
      ∫ γ, compensatedTest (reducedGenerator i ω lam) (fun y => dot e y) t γ ^ 2 ∂P =
        ∫ γ, pathInt (fun y => dot e ((reducedCoefficient ω y).mulVec e)) γ (t : ℝ) ∂P := by
  have hG0 : ∀ (y : Vec d) j, |fderiv ℝ (fun y : Vec d => dot e y) y (unitVector j)| ≤
      ∑ k, |e k| := fun y j => by
    rw [fderiv_dot_apply]
    exact Finset.single_le_sum (f := fun k => |e k|) (fun k _ => abs_nonneg _)
      (Finset.mem_univ j)
  obtain ⟨h1, h2⟩ := integral_sq_compensated_reduced_of_growth hΛ hω hs i lam hP (contDiff_dot e)
    hG0 (abs_dot_le e) le_rfl (Finset.sum_nonneg fun k _ => abs_nonneg _) t
  refine ⟨h1, h2.trans ?_⟩
  congr 1
  funext γ
  congr 1
  funext y
  exact carreDuChamp_dot ω e y

end Growth

end EinsteinFull.Blueprint
