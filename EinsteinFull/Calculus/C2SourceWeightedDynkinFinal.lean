import EinsteinFull.Calculus.C2SourceWeightedDynkin
import EinsteinFull.Calculus.C16ReducedMPExistence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull

/-- The reduced force potential is measurable and uniformly bounded. -/
theorem c2_reduced_force_potential_measurable_bounded {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) :
    Measurable (fun x : Vec d =>
      lam * forcedDrift (reducedCoefficient ω) i 0 x i +
      (lam ^ 2 / 2) * reducedCoefficient ω x i i) ∧
    ∃ K : ℝ, ∀ x : Vec d,
      |lam * forcedDrift (reducedCoefficient ω) i 0 x i +
        (lam ^ 2 / 2) * reducedCoefficient ω x i i| ≤ K := by
  obtain ⟨hc, _, ⟨A, hA⟩, _, hm, ⟨B, hB⟩⟩ := reduced_svHypotheses hΛ hω i 0
  refine ⟨(measurable_const.mul (measurable_pi_apply i |>.comp hm)).add
      (measurable_const.mul (((continuous_apply i).comp ((continuous_apply i).comp hc)).measurable)),
    |lam| * |B| + |lam ^ 2 / 2| * |A|, fun x => ?_⟩
  calc
    |lam * forcedDrift (reducedCoefficient ω) i 0 x i +
        (lam ^ 2 / 2) * reducedCoefficient ω x i i| ≤
        |lam| * |forcedDrift (reducedCoefficient ω) i 0 x i| +
        |lam ^ 2 / 2| * |reducedCoefficient ω x i i| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
    _ ≤ |lam| * |B| + |lam ^ 2 / 2| * |A| :=
      add_le_add (mul_le_mul_of_nonneg_left ((hB x i).trans (le_abs_self B)) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left ((hA x i i).trans (le_abs_self A)) (abs_nonneg _))

/-- The exponential weight of a measurable path potential is adapted to the path filtration. -/
theorem c2_path_weight_stronglyAdapted_of_measurable {d : ℕ} {g : Vec d → ℝ}
    (hg : Measurable g) :
    StronglyAdapted (pathFiltration d) (fun t : ℝ≥0 => fun γ : Path d =>
      Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (t : ℝ), g (γ u.toNNReal)))) := by
  intro t
  rw [pathFiltration_eq_canonical]
  have h := stronglyMeasurable_pathIntegral_of_measurable g hg t
  have hfun : (fun γ : Path d => Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (t : ℝ), g (γ u.toNNReal)))) =
      fun γ : Path d => Real.exp (-(∫ u in (0 : ℝ)..t, g (γ u.toNNReal))) := by
    funext γ
    rw [intervalIntegral.integral_of_le t.coe_nonneg]
  dsimp only
  rw [hfun]
  exact Real.continuous_exp.comp_stronglyMeasurable h.neg

/-- The exponential weight of a bounded path potential has the expected a.e. time derivative. -/
theorem c2_path_weight_ae_hasDerivAt {d : ℕ} {g : Vec d → ℝ} (hg : Measurable g)
    {K : ℝ} (hK : ∀ y, |g y| ≤ K) (γ : Path d) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      HasDerivAt (fun u : ℝ => Real.exp
        (-(∫ v in Set.Ioc (0 : ℝ) u, g (γ v.toNNReal))))
        (-g (γ t.toNNReal) * Real.exp
          (-(∫ v in Set.Ioc (0 : ℝ) t, g (γ v.toNNReal)))) t := by
  let f : ℝ → ℝ := fun s => g (γ s.toNNReal)
  have hfmeas : Measurable f :=
    hg.comp (γ.continuous.measurable.comp continuous_real_toNNReal.measurable)
  have hfloc : LocallyIntegrable f volume := by
    intro x
    refine ⟨Set.Ioo (x - 1) (x + 1), isOpen_Ioo.mem_nhds (by simp), ?_⟩
    apply IntegrableOn.of_bound (by simp) hfmeas.aestronglyMeasurable K
    exact Filter.Eventually.of_forall fun s => by simpa only [f, Real.norm_eq_abs] using hK (γ s.toNNReal)
  have hderiv := LocallyIntegrable.ae_hasDerivAt_integral hfloc
  filter_upwards [ae_restrict_of_ae hderiv, ae_restrict_mem measurableSet_Ioi] with t ht hpos
  have heq : (fun u : ℝ => ∫ v in Set.Ioc (0 : ℝ) u, f v) =ᶠ[𝓝 t]
      (fun u : ℝ => ∫ v in (0 : ℝ)..u, f v) := by
    filter_upwards [isOpen_Ioi.mem_nhds hpos] with u hu
    exact (intervalIntegral.integral_of_le hu.le).symm
  have hd : HasDerivAt (fun u : ℝ => Real.exp (-(∫ v in Set.Ioc (0 : ℝ) u, f v)))
      (Real.exp (-(∫ v in Set.Ioc (0 : ℝ) t, f v)) * -f t) t :=
    ((ht 0).congr_of_eventuallyEq heq).neg.exp
  refine hd.congr_deriv ?_
  simp only [f]
  ring

/-- A bounded-potential exponential weight is absolutely continuous on every finite interval. -/
theorem c2_path_weight_absolutelyContinuousOnInterval {d : ℕ} {g : Vec d → ℝ}
    (hg : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K) (γ : Path d) (T : ℝ≥0) :
    AbsolutelyContinuousOnInterval (fun u : ℝ => Real.exp
      (-(∫ v in Set.Ioc (0 : ℝ) u, g (γ v.toNNReal)))) 0 T := by
  let f : ℝ → ℝ := fun s => g (γ s.toNNReal)
  have hfmeas : Measurable f :=
    hg.comp (γ.continuous.measurable.comp continuous_real_toNNReal.measurable)
  have hint : IntervalIntegrable f volume 0 T := by
    apply intervalIntegrable_iff.mpr
    apply IntegrableOn.of_bound (by simp) hfmeas.aestronglyMeasurable K
    exact Filter.Eventually.of_forall fun s => by simpa only [f, Real.norm_eq_abs] using hK (γ s.toNNReal)
  have hPhi : AbsolutelyContinuousOnInterval (fun u : ℝ => ∫ v in (0 : ℝ)..u, f v) 0 T :=
    hint.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  obtain ⟨Lc, hLc⟩ := (Real.contDiff_exp (n := 1)).contDiffOn.exists_lipschitzOnWith
    (s := Set.Icc (-(K * T)) (K * T)) (by decide) (convex_Icc _ _) isCompact_Icc
  have hmaps : Set.MapsTo (fun u : ℝ => -(∫ v in (0 : ℝ)..u, f v)) (Set.uIcc 0 (T : ℝ))
      (Set.Icc (-(K * T)) (K * T)) := by
    intro u hu
    rw [Set.uIcc_of_le T.coe_nonneg] at hu
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := u)
      (f := f) (C := K) (fun s _ => by simpa only [f, Real.norm_eq_abs] using hK (γ s.toNNReal))
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hu.1] at hb
    have hu' := mul_le_mul_of_nonneg_left hu.2 hK0
    have hl := abs_le.mp hb
    constructor <;> linarith [hl.1, hl.2]
  have hcomp := hLc.comp_absolutelyContinuousOnInterval hmaps hPhi.neg
  refine hcomp.congr ?_
  intro u hu
  rw [Set.uIcc_of_le T.coe_nonneg] at hu
  simp only [Function.comp_apply, intervalIntegral.integral_of_le hu.1]
  rfl

/-- The real-time weight, frozen at nonnegative times, is absolutely continuous on `[0, T]`. -/
theorem c2_path_weight_toNNReal_absolutelyContinuousOnInterval {d : ℕ} {g : Vec d → ℝ}
    (hg : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K) (γ : Path d) (T : ℝ≥0) :
    AbsolutelyContinuousOnInterval (fun u : ℝ => Real.exp
      (-(∫ v in Set.Ioc (0 : ℝ) (u.toNNReal : ℝ), g (γ v.toNNReal)))) 0 T := by
  refine (c2_path_weight_absolutelyContinuousOnInterval hg hK γ T).congr ?_
  intro u hu
  rw [Set.uIcc_of_le T.coe_nonneg] at hu
  simp only [Real.coe_toNNReal u hu.1]

/-- Almost everywhere on `(0, T]`, the derivative of the weight is `-g(γ_s) * weight`. -/
theorem c2_path_weight_toNNReal_ae_deriv {d : ℕ} {g : Vec d → ℝ} (hg : Measurable g)
    {K : ℝ} (hK : ∀ y, |g y| ≤ K) (γ : Path d) (T : ℝ≥0) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      deriv (fun u : ℝ => Real.exp
        (-(∫ v in Set.Ioc (0 : ℝ) (u.toNNReal : ℝ), g (γ v.toNNReal)))) s =
        -(g (γ s.toNNReal) * Real.exp
          (-(∫ v in Set.Ioc (0 : ℝ) (s.toNNReal : ℝ), g (γ v.toNNReal)))) := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Ioi_self
    (c2_path_weight_ae_hasDerivAt hg hK γ), ae_restrict_mem measurableSet_Ioc] with t ht hmem
  have heq : (fun u : ℝ => Real.exp
      (-(∫ v in Set.Ioc (0 : ℝ) (u.toNNReal : ℝ), g (γ v.toNNReal)))) =ᶠ[𝓝 t]
      (fun u : ℝ => Real.exp (-(∫ v in Set.Ioc (0 : ℝ) u, g (γ v.toNNReal)))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hmem.1] with u hu
    simp only [Real.coe_toNNReal u (le_of_lt hu)]
  rw [(ht.congr_of_eventuallyEq heq).deriv, Real.coe_toNNReal t hmem.1.le]
  ring

/-- Pathwise weighted Dynkin identity, with all time functions and integrability supplied. -/
theorem c2_pathwise_weighted_dynkin_core {T : ℝ≥0} {W G ℓ F M A : ℝ → ℝ} {F0 : ℝ}
    (hW : AbsolutelyContinuousOnInterval W 0 T) (hW0 : W 0 = 1)
    (hWG : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), deriv W s = G s)
    (hℓ : IntervalIntegrable ℓ volume 0 T)
    (hA : ∀ s ∈ Set.uIcc (0 : ℝ) T, A s = ∫ v in (0 : ℝ)..s, ℓ v)
    (hrel : ∀ s ∈ Set.uIcc (0 : ℝ) T, F s = M s + F0 + A s)
    (hg : IntervalIntegrable G volume 0 T)
    (hmg : IntervalIntegrable (fun s => M s * G s) volume 0 T)
    (hga : IntervalIntegrable (fun s => G s * A s) volume 0 T)
    (hwl : IntervalIntegrable (fun s => W s * ℓ s) volume 0 T) :
    W T * F T - F0 = M T + M T * (∫ s in (0 : ℝ)..T, G s) +
      (∫ s in (0 : ℝ)..T, W s * ℓ s + G s * F s) -
      ∫ s in (0 : ℝ)..T, M s * G s := by
  have hT : (0 : ℝ) ≤ T := T.coe_nonneg
  have hweight := c2_weight_integral_of_ae_deriv hT hW hW0 hWG
  have hprod := c2_integral_product_indefinite hT hW hℓ hWG
  have hAT : A T = ∫ v in (0 : ℝ)..T, ℓ v := hA T (Set.right_mem_uIcc)
  have hproduct : W T * A T = ∫ s in (0 : ℝ)..T, G s * A s + W s * ℓ s := by
    rw [hAT, hprod]
    apply intervalIntegral.integral_congr
    intro s hs
    simp only [hA s hs]
  exact c2_pointwise_weighted_dynkin_assembly hrel hweight hproduct hg hmg hga hwl

/-- A product of bounded factors is bounded by the product of the bounds. -/
theorem c2_abs_mul_le_of_bounds {Ω : Type*} {J₁ J₂ : ℝ → Ω → ℝ} {S : Set ℝ} {C₁ C₂ : ℝ}
    (h₁ : ∀ s ∈ S, ∀ ω, |J₁ s ω| ≤ C₁) (h₂ : ∀ s ∈ S, ∀ ω, |J₂ s ω| ≤ C₂) :
    ∀ s ∈ S, ∀ ω, |J₁ s ω * J₂ s ω| ≤ C₁ * C₂ := fun s hs ω => by
  rw [abs_mul]
  exact mul_le_mul (h₁ s hs ω) (h₂ s hs ω) (abs_nonneg _) ((abs_nonneg _).trans (h₁ s hs ω))

/-- Weighted Dynkin identity for a bounded measurable potential and a bounded generator image. -/
theorem c2_weighted_dynkin_of_bounded_generator {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hL : Measurable (L f)) {C : ℝ} (hC : ∀ y, |L f y| ≤ C)
    {g : Vec d → ℝ} (hg : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K) (T : ℝ≥0) :
    (∫ γ, Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (T : ℝ), g (γ u.toNNReal))) * f (γ T) ∂P) -
        f x =
      ∫ γ, (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        Real.exp (-(∫ v in Set.Ioc (0 : ℝ) (u.toNNReal : ℝ), g (γ v.toNNReal))) *
          (L f (γ u.toNNReal) - g (γ u.toNNReal) * f (γ u.toNNReal))) ∂P := by
  letI : IsProbabilityMeasure P := hP.1
  obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hc
  have hfB : ∀ y, |f y| ≤ B := fun y => by simpa only [Real.norm_eq_abs] using hB y
  have hfm : Measurable f := hf.continuous.measurable
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  have heval : Measurable (fun p : ℝ × Path d => p.2 p.1.toNNReal) :=
    (continuous_snd.eval (continuous_real_toNNReal.comp continuous_fst)).measurable
  have hLmj : Measurable (fun p : ℝ × Path d => L f (p.2 p.1.toNNReal)) := hL.comp heval
  have hFmj : Measurable (fun p : ℝ × Path d => f (p.2 p.1.toNNReal)) := hfm.comp heval
  have hWmj := c2_path_weight_joint_measurable hg hK
  obtain ⟨hGmj, D, hD⟩ := c2_path_weight_derivative_joint_bound hg hK T
  obtain ⟨Bw, hBw0, hBw⟩ := c2_path_weight_horizon_bound hK T
  have hMmj := c2_compensatedTest_joint_measurable hfm hL hC
  have hMb := c2_compensatedTest_horizon_bound hfB hC T
  have hAmj := c2_measurable_path_integral_joint hL hC
  have hsT : ∀ s ∈ Set.uIcc (0 : ℝ) T, 0 ≤ s ∧ s ≤ T ∧ s.toNNReal ≤ T := fun s hs => by
    rw [Set.uIcc_of_le hT0] at hs
    exact ⟨hs.1, hs.2, Real.toNNReal_le_iff_le_coe.mpr hs.2⟩
  have hbG : ∀ s ∈ Set.uIcc (0 : ℝ) T, ∀ γ : Path d, |-(g (γ s.toNNReal) * Real.exp
      (-(∫ u in Set.Ioc (0 : ℝ) (s.toNNReal : ℝ), g (γ u.toNNReal))))| ≤ D :=
    fun s hs γ => hD s (hsT s hs).2.2 γ
  have hbM : ∀ s ∈ Set.uIcc (0 : ℝ) T, ∀ γ : Path d,
      |compensatedTest L f s.toNNReal γ| ≤ 2 * B + C * T :=
    fun s hs γ => hMb s.toNNReal (hsT s hs).2.2 γ
  have hbW : ∀ s ∈ Set.uIcc (0 : ℝ) T, ∀ γ : Path d, |Real.exp
      (-(∫ u in Set.Ioc (0 : ℝ) (s.toNNReal : ℝ), g (γ u.toNNReal)))| ≤ Bw :=
    fun s hs γ => hBw s.toNNReal (hsT s hs).2.2 γ
  have hbL : ∀ s ∈ Set.uIcc (0 : ℝ) T, ∀ γ : Path d, |L f (γ s.toNNReal)| ≤ C :=
    fun s _ γ => hC _
  have hbF : ∀ s ∈ Set.uIcc (0 : ℝ) T, ∀ γ : Path d, |f (γ s.toNNReal)| ≤ B :=
    fun s _ γ => hfB _
  have hbA : ∀ s ∈ Set.uIcc (0 : ℝ) T, ∀ γ : Path d,
      |∫ u in (0 : ℝ)..(s.toNNReal : ℝ), L f (γ u.toNNReal)| ≤ C * T := by
    intro s hs γ
    have h := abs_pathInt_le hC γ (s.toNNReal).coe_nonneg
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    have hs' : (s.toNNReal : ℝ) ≤ T := by
      exact_mod_cast (hsT s hs).2.2
    exact h.trans (mul_le_mul_of_nonneg_left hs' hC0)
  let Wf : ℝ → Path d → ℝ := fun s γ =>
    Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (s.toNNReal : ℝ), g (γ u.toNNReal)))
  let Gf : ℝ → Path d → ℝ := fun s γ => -(g (γ s.toNNReal) * Wf s γ)
  let Mf : ℝ → Path d → ℝ := fun s γ => compensatedTest L f s.toNNReal γ
  let Lt : ℝ → Path d → ℝ := fun s γ => L f (γ s.toNNReal)
  let Ff : ℝ → Path d → ℝ := fun s γ => f (γ s.toNNReal)
  let Af : ℝ → Path d → ℝ := fun s γ => ∫ u in (0 : ℝ)..(s.toNNReal : ℝ), L f (γ u.toNNReal)
  let Zf : ℝ → Path d → ℝ := fun s γ => Wf s γ * Lt s γ + Gf s γ * Ff s γ
  have hWm : Measurable (fun p : ℝ × Path d => Wf p.1 p.2) := hWmj
  have hGm : Measurable (fun p : ℝ × Path d => Gf p.1 p.2) := hGmj
  have hMm : Measurable (fun p : ℝ × Path d => Mf p.1 p.2) := hMmj
  have hLm : Measurable (fun p : ℝ × Path d => Lt p.1 p.2) := hLmj
  have hFm : Measurable (fun p : ℝ × Path d => Ff p.1 p.2) := hFmj
  have hAm : Measurable (fun p : ℝ × Path d => Af p.1 p.2) := hAmj
  have hZm : Measurable (fun p : ℝ × Path d => Zf p.1 p.2) :=
    (hWm.mul hLm).add (hGm.mul hFm)
  have hbG' : ∀ s ∈ Set.uIcc (0 : ℝ) T, ∀ γ : Path d, |Gf s γ| ≤ D := hbG
  have hbM' : ∀ s ∈ Set.uIcc (0 : ℝ) T, ∀ γ : Path d, |Mf s γ| ≤ 2 * B + C * T := hbM
  have hbW' : ∀ s ∈ Set.uIcc (0 : ℝ) T, ∀ γ : Path d, |Wf s γ| ≤ Bw := hbW
  have hbL' : ∀ s ∈ Set.uIcc (0 : ℝ) T, ∀ γ : Path d, |Lt s γ| ≤ C := hbL
  have hbF' : ∀ s ∈ Set.uIcc (0 : ℝ) T, ∀ γ : Path d, |Ff s γ| ≤ B := hbF
  have hbA' : ∀ s ∈ Set.uIcc (0 : ℝ) T, ∀ γ : Path d, |Af s γ| ≤ C * T := hbA
  have hbMG := c2_abs_mul_le_of_bounds hbM' hbG'
  have hbGA := c2_abs_mul_le_of_bounds hbG' hbA'
  have hbWL := c2_abs_mul_le_of_bounds hbW' hbL'
  have hbGF := c2_abs_mul_le_of_bounds hbG' hbF'
  have hbZ : ∀ s ∈ Set.uIcc (0 : ℝ) T, ∀ γ : Path d, |Zf s γ| ≤ Bw * C + D * B :=
    fun s hs γ => (abs_add_le _ _).trans (add_le_add (hbWL s hs γ) (hbGF s hs γ))
  have hTT : (T : ℝ).toNNReal = T := Real.toNNReal_coe
  -- pathwise identity
  have hpath : ∀ γ : Path d, Wf T γ * Ff T γ - f (γ 0) = Mf T γ +
      Mf T γ * (∫ s in (0 : ℝ)..T, Gf s γ) + (∫ s in (0 : ℝ)..T, Zf s γ) -
        ∫ s in (0 : ℝ)..T, Mf s γ * Gf s γ := by
    intro γ
    refine c2_pathwise_weighted_dynkin_core (W := fun s => Wf s γ) (G := fun s => Gf s γ)
      (ℓ := fun s => Lt s γ) (F := fun s => Ff s γ) (M := fun s => Mf s γ)
      (A := fun s => Af s γ) (F0 := f (γ 0))
      (c2_path_weight_toNNReal_absolutelyContinuousOnInterval hg hK γ T) (by simp [Wf])
      (c2_path_weight_toNNReal_ae_deriv hg hK γ T)
      (c2_intervalIntegrable_bounded_time_slice hLm hbL' γ) ?_ ?_
      (c2_intervalIntegrable_bounded_time_slice hGm hbG' γ)
      (c2_intervalIntegrable_bounded_time_slice (hMm.mul hGm) hbMG γ) ?_
      (c2_intervalIntegrable_bounded_time_slice (hWm.mul hLm) hbWL γ)
    · intro s hs
      simp only [Af, Real.coe_toNNReal s (hsT s hs).1]
      rfl
    · intro s hs
      simp only [Ff, Mf, Af, compensatedTest_eq, pathInt]
      ring
    · exact c2_intervalIntegrable_bounded_time_slice (hGm.mul hAm) hbGA γ
  have hIi : Integrable (fun γ : Path d => ∫ s in (0 : ℝ)..T, Gf s γ) P :=
    c2_integrable_bounded_time_integral hT0 hGm hbG'
  have hHi : Integrable (fun γ : Path d => ∫ s in (0 : ℝ)..T, Mf s γ * Gf s γ) P :=
    c2_integrable_bounded_time_integral hT0 (hMm.mul hGm) hbMG
  have hZi : Integrable (fun γ : Path d => ∫ s in (0 : ℝ)..T, Zf s γ) P :=
    c2_integrable_bounded_time_integral hT0 hZm hbZ
  have hFpos : ∀ s : ℝ≥0, Integrable (fun γ : Path d => f (γ s)) P := fun s =>
    Integrable.of_bound (hfm.comp (measurable_pathPosition s)).aestronglyMeasurable B
      (ae_of_all _ fun γ => hB (γ s))
  have hMi : Integrable (compensatedTest L f T) P := (hP.2.2 f hf hc).2.1 T
  have hIb : ∀ γ : Path d, |∫ s in (0 : ℝ)..T, Gf s γ| ≤ D * T := fun γ => by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T)
      (f := fun s => Gf s γ) (C := D) fun s hs => by
        simpa only [Real.norm_eq_abs] using hbG' s (Set.uIoc_subset_uIcc hs) γ
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT0] using h
  have hWMi : Integrable (fun γ : Path d => compensatedTest L f T γ * ∫ s in (0 : ℝ)..T, Gf s γ) P := by
    refine Integrable.of_bound (hMi.aestronglyMeasurable.mul hIi.aestronglyMeasurable)
      ((2 * B + C * T) * (D * T)) (ae_of_all _ fun γ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hM' := hMb T le_rfl γ
    exact mul_le_mul hM' (hIb γ) (abs_nonneg _) ((abs_nonneg _).trans hM')
  have hWT : StronglyMeasurable (fun γ : Path d => Real.exp
      (-(∫ u in Set.Ioc (0 : ℝ) (T : ℝ), g (γ u.toNNReal)))) :=
    (c2_path_weight_stronglyAdapted_of_measurable hg T).mono ((pathFiltration d).le T)
  have hWFi : Integrable (fun γ : Path d => Real.exp
      (-(∫ u in Set.Ioc (0 : ℝ) (T : ℝ), g (γ u.toNNReal))) * f (γ T)) P := by
    refine Integrable.of_bound (hWT.aestronglyMeasurable.mul (hFpos T).aestronglyMeasurable)
      (Bw * B) (ae_of_all _ fun γ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hBw T le_rfl γ) (hB (γ T)) (abs_nonneg _) hBw0
  have hcross : (∫ γ, compensatedTest L f T γ * (∫ s in (0 : ℝ)..T, Gf s γ) ∂P) =
      ∫ γ, (∫ s in (0 : ℝ)..T, Mf s γ * Gf s γ) ∂P :=
    c2_integral_martingale_mul_adapted_integral (hP.2.2 f hf hc).2.2 hMmj hGmj
      (fun s => c2_path_weight_derivative_stronglyAdapted hg
        (c2_path_weight_stronglyAdapted_of_measurable hg) s.toNNReal) hD
      (c2_compensatedTest_horizon_bound hfB hC T)
  have hzero : (∫ γ, compensatedTest L f T γ ∂P) = 0 :=
    c16_integral_compensated_test_eq_zero hP hf hc T
  have hstart : (∫ γ, f (γ 0) ∂P) = f x := by
    calc
      (∫ γ, f (γ 0) ∂P) = ∫ _ : Path d, f x ∂P :=
        integral_congr_ae (hP.2.1.mono fun _ h => congrArg f h)
      _ = f x := by simp
  have hfin := c2_weighted_dynkin_assembly P (hFpos 0) hMi hWMi hHi hZi hWFi hzero hcross
    (F := fun γ : Path d => f (γ T)) (W := fun γ : Path d => Real.exp
      (-(∫ u in Set.Ioc (0 : ℝ) (T : ℝ), g (γ u.toNNReal)))) (F0 := fun γ => f (γ 0))
    (fun γ => by
      have h := hpath γ
      simp only [Wf, Mf, Ff, Gf, Zf, hTT] at h ⊢
      exact h)
  rw [hstart] at hfin
  rw [hfin]
  refine integral_congr_ae (ae_of_all _ fun γ => ?_)
  show (∫ s in (0 : ℝ)..T, Zf s γ) = _
  rw [intervalIntegral.integral_of_le hT0]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  simp only [Zf, Wf, Gf, Lt, Ff]
  ring

/-- Weighted Dynkin identity for the reduced forced problem with compact smooth tests:
the exponential potential weight, built from the actual reduced force and diffusion
coefficients, turns the weak Dynkin identity into one with the potential `V`. -/
theorem c2_reduced_force_weighted_dynkin {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (T : ℝ≥0) :
    let V := fun y : Vec d => lam * forcedDrift (reducedCoefficient ω) i 0 y i +
      (lam ^ 2 / 2) * reducedCoefficient ω y i i
    let W : ℝ≥0 → Path d → ℝ := fun t γ =>
      Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (t : ℝ), V (γ u.toNNReal)))
    (∫ γ, W T γ * f (γ T) ∂P) - f x =
      ∫ γ, (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        W u.toNNReal γ * (External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i 0) f (γ u.toNNReal) -
            V (γ u.toNNReal) * f (γ u.toNNReal))) ∂P := by
  dsimp only
  obtain ⟨hVm, K, hK⟩ := c2_reduced_force_potential_measurable_bounded hΛ hω i lam
  obtain ⟨hL, C, hC⟩ := c2_reduced_generator_measurable_bounded hΛ hω i hf hc
  exact c2_weighted_dynkin_of_bounded_generator hP hf hc hL hC hVm hK T

end EinsteinFull
