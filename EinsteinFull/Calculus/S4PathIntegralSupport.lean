import EinsteinFull.Calculus.S4PathClockSupport
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Time integrals along continuous paths

Continuity of `(γ, s) ↦ ∫₀ˢ g (γ u) du` on path space, its derivative in `s`, and the
pathwise identity relating the compensated test function of `f` with that of `f²`
(the algebra behind the quadratic-variation bound `E M_t² ≤ B t`).
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The running integral `s ↦ ∫₀ˢ g (γ u⁺) du` of an observable along a path. -/
noncomputable def pathInt {d : ℕ} (g : Vec d → ℝ) (γ : Path d) (s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..s, g (γ u.toNNReal)

theorem continuous_pathEval (d : ℕ) :
    Continuous (fun p : Path d × ℝ => p.1 p.2.toNNReal) :=
  continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))

theorem continuous_pathInt_prod {d : ℕ} {g : Vec d → ℝ} (hg : Continuous g) :
    Continuous (fun p : Path d × ℝ => pathInt g p.1 p.2) := by
  have hf : Continuous (Function.uncurry fun (p : Path d × ℝ) (u : ℝ) => g (p.1 u.toNNReal)) :=
    hg.comp ((continuous_pathEval d).comp ((continuous_fst.comp continuous_fst).prodMk
      continuous_snd))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) hf
    continuous_snd

theorem continuous_pathInt_path {d : ℕ} {g : Vec d → ℝ} (hg : Continuous g) (s : ℝ) :
    Continuous (fun γ : Path d => pathInt g γ s) :=
  (continuous_pathInt_prod hg).comp (continuous_id.prodMk continuous_const)

theorem continuous_pathInt_real {d : ℕ} {g : Vec d → ℝ} (hg : Continuous g) (γ : Path d) :
    Continuous (fun s : ℝ => pathInt g γ s) :=
  (continuous_pathInt_prod hg).comp (continuous_const.prodMk continuous_id)

theorem hasDerivAt_pathInt {d : ℕ} {g : Vec d → ℝ} (hg : Continuous g) (γ : Path d) (s : ℝ) :
    HasDerivAt (fun r => pathInt g γ r) (g (γ s.toNNReal)) s := by
  have hc : Continuous fun u : ℝ => g (γ u.toNNReal) :=
    hg.comp (γ.continuous.comp continuous_real_toNNReal)
  exact (hc.integral_hasStrictDerivAt 0 s).hasDerivAt

theorem pathInt_zero {d : ℕ} (g : Vec d → ℝ) (γ : Path d) : pathInt g γ 0 = 0 := by
  simp [pathInt]

theorem abs_pathInt_le {d : ℕ} {g : Vec d → ℝ} {K : ℝ} (hK : ∀ y, |g y| ≤ K) (γ : Path d)
    {t : ℝ} (ht : 0 ≤ t) : |pathInt g γ t| ≤ K * t := by
  unfold pathInt
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := K)
    (f := fun u : ℝ => g (γ u.toNNReal)) (fun u _ => by rw [Real.norm_eq_abs]; exact hK _)
  rw [sub_zero, abs_of_nonneg ht] at h
  exact h

/-- The compensated test function, in real time. -/
theorem compensatedTest_eq {d : ℕ} (L : (Vec d → ℝ) → Vec d → ℝ) (f : Vec d → ℝ) (t : ℝ≥0)
    (γ : Path d) :
    compensatedTest L f t γ = f (γ t) - f (γ 0) - pathInt (L f) γ (t : ℝ) := rfl

/-- The real-variable algebra behind `M^{f²} = (M^f)² + 2 M^f A + 2 f₀ M^f - 2 ∫ M^f a - ∫ Γ`. -/
theorem square_identity_aux (F a A h' : ℝ → ℝ) (t : ℝ) (hFc : Continuous F)
    (hac : Continuous a) (hAc : Continuous A) (hhc : Continuous h')
    (hA0 : A 0 = 0) (hAd : ∀ s, HasDerivAt A (a s) s) (hAt : A t = ∫ s in (0 : ℝ)..t, a s) :
    (F t ^ 2 - F 0 ^ 2 - ∫ s in (0 : ℝ)..t, h' s) =
      (F t - F 0 - A t) ^ 2 + 2 * (F t - F 0 - A t) * A t + 2 * F 0 * (F t - F 0 - A t) -
      2 * (∫ s in (0 : ℝ)..t, (F s - F 0 - A s) * a s) -
      ∫ s in (0 : ℝ)..t, (h' s - 2 * F s * a s) := by
  have hder : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (fun r => A r * A r / 2) (A s * a s) s := by
    intro s _
    exact (((hAd s).mul (hAd s)).div_const 2).congr_deriv (by ring)
  have cAa : Continuous fun s => A s * a s := by fun_prop
  have hAa : ∫ s in (0 : ℝ)..t, A s * a s = A t * A t / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (cAa.intervalIntegrable _ _)]
    simp [hA0]
  have c1 : Continuous fun s => F 0 * a s := by fun_prop
  have c2 : Continuous fun s => (F s - F 0 - A s) * a s := by fun_prop
  have c12 : Continuous fun s => F 0 * a s + (F s - F 0 - A s) * a s := by fun_prop
  have hFa : ∫ s in (0 : ℝ)..t, F s * a s =
      F 0 * A t + (∫ s in (0 : ℝ)..t, (F s - F 0 - A s) * a s) + A t * A t / 2 := by
    have e : ∀ s, F s * a s = F 0 * a s + (F s - F 0 - A s) * a s + A s * a s :=
      fun s => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add (c12.intervalIntegrable _ _) (cAa.intervalIntegrable _ _),
      intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, ← hAt]
    linarith [hAa]
  have cFa : Continuous fun s => 2 * (F s * a s) := by fun_prop
  have hΓ : ∫ s in (0 : ℝ)..t, (h' s - 2 * F s * a s) =
      (∫ s in (0 : ℝ)..t, h' s) - 2 * ∫ s in (0 : ℝ)..t, F s * a s := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hhc.intervalIntegrable _ _) (cFa.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show h' s - 2 * F s * a s = h' s - 2 * (F s * a s)
    ring
  rw [hΓ, hFa]
  generalize (∫ s in (0 : ℝ)..t, (F s - F 0 - A s) * a s) = I1
  generalize (∫ s in (0 : ℝ)..t, h' s) = I2
  ring

/-- The algebra relating `M^f`, `M^{f²}` and the carré du champ along a path. -/
theorem pathwise_square_identity {d : ℕ} {f g h : Vec d → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) (γ : Path d) (t : ℝ) :
    (f (γ t.toNNReal) ^ 2 - f (γ 0) ^ 2 - pathInt h γ t) =
      (f (γ t.toNNReal) - f (γ 0) - pathInt g γ t) ^ 2 +
      2 * (f (γ t.toNNReal) - f (γ 0) - pathInt g γ t) * pathInt g γ t +
      2 * f (γ 0) * (f (γ t.toNNReal) - f (γ 0) - pathInt g γ t) -
      2 * (∫ s in (0 : ℝ)..t, (f (γ s.toNNReal) - f (γ 0) - pathInt g γ s) * g (γ s.toNNReal)) -
      pathInt (fun y => h y - 2 * f y * g y) γ t := by
  have hFc : Continuous fun s : ℝ => f (γ s.toNNReal) :=
    hf.comp (γ.continuous.comp continuous_real_toNNReal)
  have hac : Continuous fun s : ℝ => g (γ s.toNNReal) :=
    hg.comp (γ.continuous.comp continuous_real_toNNReal)
  have hhc : Continuous fun s : ℝ => h (γ s.toNNReal) :=
    hh.comp (γ.continuous.comp continuous_real_toNNReal)
  have hF0 : f (γ (0 : ℝ).toNNReal) = f (γ 0) := by simp
  have key := square_identity_aux (fun s => f (γ s.toNNReal)) (fun s => g (γ s.toNNReal))
    (fun s => pathInt g γ s) (fun s => h (γ s.toNNReal)) t hFc hac (continuous_pathInt_real hg γ)
    hhc (pathInt_zero g γ) (hasDerivAt_pathInt hg γ) rfl
  simp only [hF0] at key
  exact key

end EinsteinFull
