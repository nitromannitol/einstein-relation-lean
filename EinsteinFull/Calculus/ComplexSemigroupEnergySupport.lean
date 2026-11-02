import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Stationary energy along the full complex generator domain

Coercivity controls the actual Euclidean horizontal gradient in the generator
graph topology. Full-domain semigroup orbits therefore have continuous gradients.
The weighted squared norm identity then controls their integrated gradient energy.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Forced coercivity controls the norm of the unique actual Euclidean gradient. -/
theorem IsComplexGeneratorPair.gradient_coercive {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * ‖G‖ ^ 2 ≤
      -(inner ℂ f g).re + complexForceShift d Λ₀ ζ * ‖f‖ ^ 2 := by
  obtain ⟨H, hH, hb⟩ := hfg.forced_coercive
  rw [hH.unique hG, ← PiLp.norm_sq_eq_of_L2] at hb
  exact hb

/-- Graph coercivity bounds any actual horizontal gradient by the value and generator output. -/
theorem IsComplexGeneratorPair.gradient_sq_le {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * ‖G‖ ^ 2 ≤
      ‖f‖ * ‖g‖ + complexForceShift d Λ₀ ζ * ‖f‖ ^ 2 := by
  have hi : -(inner ℂ f g).re ≤ ‖f‖ * ‖g‖ := by
    calc
      _ ≤ ‖inner ℂ f g‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      _ ≤ _ := norm_inner_le_norm _ _
  exact (hfg.gradient_coercive (G := G) hG).trans (add_le_add hi le_rfl)

/-- Convergence in the full generator graph implies convergence of the actual Euclidean gradient. -/
theorem tendsto_complexHorizontalGradient_of_generator {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ} {α : Type*} {l : Filter α}
    {u v : α → Lp ℂ 2 (reducedLaw Q)}
    {G : α → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    {f g : Lp ℂ 2 (reducedLaw Q)}
    {H : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hg : ∀ x, IsComplexGeneratorPair Q i ζ (u x) (v x))
    (hG : ∀ x, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u x) (G x))
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f H)
    (hu : Tendsto u l (𝓝 f)) (hv : Tendsto v l (𝓝 g)) : Tendsto G l (𝓝 H) := by
  let c := (Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4
  have hc : 0 < c := div_pos (inv_pos.mpr (mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter))) (by norm_num)
  have hb (x : α) : ‖G x - H‖ ^ 2 ≤
      (‖u x-f‖ * ‖v x-g‖ + complexForceShift d Λ₀ ζ * ‖u x-f‖ ^ 2) / c := by
    apply (le_div_iff₀ hc).mpr
    have hd : IsComplexGeneratorPair Q i ζ (u x-f) (v x-g) := by
      simpa only [neg_one_smul, ← sub_eq_add_neg] using (hg x).add (hfg.smul (-1))
    have hD : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (u x-f) (G x-H) := by
      intro j
      simpa only [PiLp.sub_apply, Pi.sub_apply, neg_one_smul, ← sub_eq_add_neg] using
        (hG x j).add ((hH j).smul (-1))
    rw [mul_comm]
    exact hd.gradient_sq_le (G := G x-H) hD
  have hu0 := (hu.sub_const f).norm
  have hv0 := (hv.sub_const g).norm
  simp only [sub_self, norm_zero] at hu0 hv0
  have he : Tendsto (fun x =>
      (‖u x-f‖ * ‖v x-g‖ + complexForceShift d Λ₀ ζ * ‖u x-f‖ ^ 2) / c) l (𝓝 0) := by
    simpa only [mul_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero, zero_div] using ((hu0.mul hv0).add ((hu0.pow 2).const_mul _)).div_const c
  have hn := (squeeze_zero (fun x => sq_nonneg ‖G x-H‖) hb he).sqrt
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- A continuous curve in the full generator graph has a continuous actual horizontal gradient. -/
theorem continuous_complexHorizontalGradient_of_generator {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {α : Type*} [TopologicalSpace α]
    {u v : α → Lp ℂ 2 (reducedLaw Q)}
    {G : α → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hg : ∀ x, IsComplexGeneratorPair Q i ζ (u x) (v x))
    (hG : ∀ x, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u x) (G x))
    (hu : Continuous u) (hv : Continuous v) : Continuous G :=
  continuous_iff_continuousAt.mpr fun x =>
    tendsto_complexHorizontalGradient_of_generator hg hG (hg x) (hG x)
      (hu.tendsto x) (hv.tendsto x)

private theorem realL2_inner_eq_re {d : ℕ} (Q : Measure (FieldPair d)) (f g : Lp ℂ 2 Q) :
    inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) f g)

/-- The exponentially weighted squared norm has the exact full-domain right derivative. -/
theorem IsComplexEnvironmentSemigroup.hasDerivWithinAt_weighted_norm_sq
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (s : ℝ) (hs : 0 ≤ s) :
    HasDerivWithinAt
      (fun r : ℝ => Real.exp (-2 * complexForceShift d Λ₀ ζ * r) * ‖P r.toNNReal f‖ ^ 2)
      (-2 * (Real.exp (-2 * complexForceShift d Λ₀ ζ * s) *
        (-(inner ℂ (P s.toNNReal f) (P s.toNNReal g)).re +
          complexForceShift d Λ₀ ζ * ‖P s.toNNReal f‖ ^ 2))) (Ici s) s := by
  have he := (((hasDerivAt_id s).const_mul (-2 * complexForceShift d Λ₀ ζ)).exp).hasDerivWithinAt (s := Ici s)
  have hd := he.mul (hP.hasDerivWithinAt_orbit hfg s hs).norm_sq
  rw [realL2_inner_eq_re] at hd
  simp only [id_eq] at hd
  convert hd using 1
  ring

/-- The full generator-domain orbit satisfies the weighted stationary energy identity. -/
theorem IsComplexEnvironmentSemigroup.integral_weighted_energy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-2 * complexForceShift d Λ₀ ζ * s) *
      (-(inner ℂ (P s.toNNReal f) (P s.toNNReal g)).re +
        complexForceShift d Λ₀ ζ * ‖P s.toNNReal f‖ ^ 2)) =
      (‖f‖ ^ 2 - Real.exp (-2 * complexForceShift d Λ₀ ζ * (t : ℝ)) * ‖P t f‖ ^ 2) / 2 := by
  let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P s.toNNReal f
  let v : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P s.toNNReal g
  let w : ℝ → ℝ := fun s => Real.exp (-2 * complexForceShift d Λ₀ ζ * s)
  let E : ℝ → ℝ := fun s => w s * (-(inner ℂ (u s) (v s)).re +
    complexForceShift d Λ₀ ζ * ‖u s‖ ^ 2)
  have hu : Continuous u := (hP.2.2.1 f).comp continuous_real_toNNReal
  have hv : Continuous v := (hP.2.2.1 g).comp continuous_real_toNNReal
  have hw : Continuous w := Real.continuous_exp.comp (continuous_const.fun_mul continuous_id)
  have hE : Continuous E := hw.fun_mul
    ((Complex.continuous_re.comp (hu.inner hv)).neg.add (continuous_const.fun_mul (hu.norm.pow 2)))
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (a := (0 : ℝ)) (b := (t : ℝ)) t.property
    (hw.fun_mul (hu.norm.pow 2)).continuousOn
    (f' := fun s => -2 * E s)
    (fun s hs => (hP.hasDerivWithinAt_weighted_norm_sq hfg s hs.1.le).mono
      (Ioi_subset_Ici_self)) ((continuous_const.fun_mul hE).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul] at hi
  have hu0 : u 0 = f := by
    simp only [u, Real.toNNReal_zero, hP.1, ContinuousLinearMap.id_apply]
  have hut : u (t : ℝ) = P t f := by
    simp only [u, Real.toNNReal_coe]
  simp only [Pi.pow_apply] at hi
  rw [hu0, hut] at hi
  simp only [w, mul_zero, Real.exp_zero, one_mul] at hi
  change (∫ s in (0 : ℝ)..(t : ℝ), E s) = _
  linarith only [hi]

/-- Every full-domain orbit has a continuous actual Euclidean horizontal gradient. -/
theorem IsComplexEnvironmentSemigroup.exists_continuous_gradient_orbit
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      Continuous G ∧ ∀ s, HasComplexHorizontalGradient (reducedLaw Q)
        (reducedLaw_stationary Q) (P s.toNNReal f) (G s) := by
  have he (s : ℝ) : ∃ G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P s.toNNReal f) G := by
    obtain ⟨G, hG, _⟩ := hP.map_generator hfg s.toNNReal
    exact ⟨WithLp.toLp 2 G, hG⟩
  choose G hG using he
  exact ⟨G, continuous_complexHorizontalGradient_of_generator
    (fun s => hP.map_generator hfg s.toNNReal) hG
    ((hP.2.2.1 f).comp continuous_real_toNNReal)
    ((hP.2.2.1 g).comp continuous_real_toNNReal), hG⟩

/-- The full-domain actual horizontal gradient has the weighted integrated energy bound. -/
theorem IsComplexEnvironmentSemigroup.integral_weighted_gradient_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : ∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P s.toNNReal f) (G s)) (t : ℝ≥0) :
    ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) *
      (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-2 * complexForceShift d Λ₀ ζ * s) * ‖G s‖ ^ 2) ≤
      (‖f‖ ^ 2 - Real.exp (-2 * complexForceShift d Λ₀ ζ * (t : ℝ)) * ‖P t f‖ ^ 2) / 2 := by
  let c := (Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4
  let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P s.toNNReal f
  let v : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P s.toNNReal g
  let w : ℝ → ℝ := fun s => Real.exp (-2 * complexForceShift d Λ₀ ζ * s)
  have hu : Continuous u := (hP.2.2.1 f).comp continuous_real_toNNReal
  have hv : Continuous v := (hP.2.2.1 g).comp continuous_real_toNNReal
  have hw : Continuous w := Real.continuous_exp.comp (continuous_const.fun_mul continuous_id)
  have hGc : Continuous G := continuous_complexHorizontalGradient_of_generator
    (fun s => hP.map_generator hfg s.toNNReal) hG hu hv
  have hE : Continuous (fun s => w s * (-(inner ℂ (u s) (v s)).re +
      complexForceShift d Λ₀ ζ * ‖u s‖ ^ 2)) := hw.fun_mul
    ((Complex.continuous_re.comp (hu.inner hv)).neg.add (continuous_const.fun_mul (hu.norm.pow 2)))
  have hi := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ)) t.property
    (((continuous_const (y := c)).fun_mul (hw.fun_mul (hGc.norm.pow 2))).intervalIntegrable 0 t)
    (hE.intervalIntegrable 0 t) (fun s _ => show
      c * (w s * ‖G s‖ ^ 2) ≤ w s * (-(inner ℂ (u s) (v s)).re +
        complexForceShift d Λ₀ ζ * ‖u s‖ ^ 2) from by
      have hb := mul_le_mul_of_nonneg_left
        ((hP.map_generator hfg s.toNNReal).gradient_coercive (G := G s) (hG s))
        (Real.exp_pos (-2 * complexForceShift d Λ₀ ζ * s)).le
      simpa only [mul_left_comm] using hb)
  rw [intervalIntegral.integral_const_mul] at hi
  exact hi.trans_eq (hP.integral_weighted_energy hfg t)

/-- In particular the weighted total gradient energy is bounded just by the initial L2 norm. -/
theorem IsComplexEnvironmentSemigroup.integral_weighted_gradient_le_initial
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : ∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P s.toNNReal f) (G s)) (t : ℝ≥0) :
    ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) *
      (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-2 * complexForceShift d Λ₀ ζ * s) * ‖G s‖ ^ 2) ≤
      ‖f‖ ^ 2 / 2 :=
  (hP.integral_weighted_gradient_le hfg hG t).trans
    (div_le_div_of_nonneg_right (sub_le_self _ (mul_nonneg (Real.exp_pos _).le
      (sq_nonneg _))) (by norm_num))

/-- Removing the weight gives total gradient energy with quadratic-force exponential growth. -/
theorem IsComplexEnvironmentSemigroup.integral_gradient_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : ∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P s.toNNReal f) (G s)) (t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ), ‖G s‖ ^ 2) ≤
      2 * (Real.exp (2 * Λ₀) * Λ₀) *
        Real.exp (2 * complexForceShift d Λ₀ ζ * (t : ℝ)) * ‖f‖ ^ 2 := by
  let K := Real.exp (2 * Λ₀) * Λ₀
  let c := K⁻¹ / 4
  let ω := complexForceShift d Λ₀ ζ
  have hK : 0 < K := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hc : 0 < c := div_pos (inv_pos.mpr hK) (by norm_num)
  have hω : 0 ≤ ω := complexForceShift_nonneg Q ζ
  have hGc : Continuous G := continuous_complexHorizontalGradient_of_generator
    (fun s => hP.map_generator hfg s.toNNReal) hG
    ((hP.2.2.1 f).comp continuous_real_toNNReal)
    ((hP.2.2.1 g).comp continuous_real_toNNReal)
  have hw : Continuous (fun s : ℝ => Real.exp (-2 * ω * s)) :=
    Real.continuous_exp.comp (continuous_const.fun_mul continuous_id)
  have hi := intervalIntegral.integral_mono_on (μ := volume)
    (a := (0 : ℝ)) (b := (t : ℝ)) t.property
    ((continuous_const.fun_mul (hGc.norm.pow 2)).intervalIntegrable 0 t)
    ((hw.fun_mul (hGc.norm.pow 2)).intervalIntegrable 0 t)
    (fun s hs => mul_le_mul_of_nonneg_right
      (show Real.exp (-2 * ω * (t : ℝ)) ≤ Real.exp (-2 * ω * s) from
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hs.2
          (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hω))) (sq_nonneg ‖G s‖))
  rw [intervalIntegral.integral_const_mul] at hi
  have hb : c * (Real.exp (-2 * ω * (t : ℝ)) *
      (∫ s in (0 : ℝ)..(t : ℝ), ‖G s‖ ^ 2)) ≤ ‖f‖ ^ 2 / 2 :=
    (mul_le_mul_of_nonneg_left hi hc.le).trans
      (hP.integral_weighted_gradient_le_initial hfg hG t)
  have he : Real.exp (2 * ω * (t : ℝ)) * Real.exp (-2 * ω * (t : ℝ)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  calc
    _ = (Real.exp (2 * ω * (t : ℝ)) / c) *
        (c * (Real.exp (-2 * ω * (t : ℝ)) *
          (∫ s in (0 : ℝ)..(t : ℝ), ‖G s‖ ^ 2))) := by
      calc
        _ = (Real.exp (2 * ω * (t : ℝ)) * Real.exp (-2 * ω * (t : ℝ))) *
            (∫ s in (0 : ℝ)..(t : ℝ), ‖G s‖ ^ 2) := by rw [he, one_mul]
        _ = _ := by field_simp
    _ ≤ (Real.exp (2 * ω * (t : ℝ)) / c) * (‖f‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hb (div_nonneg (Real.exp_pos _).le hc.le)
    _ = _ := by
      change (Real.exp (2 * ω * (t : ℝ)) / c) * (‖f‖ ^ 2 / 2) =
        2 * K * Real.exp (2 * ω * (t : ℝ)) * ‖f‖ ^ 2
      dsimp only [c]
      field_simp
      ring

/-- A single continuous actual orbit gradient satisfies the total energy bound at every time. -/
theorem IsComplexEnvironmentSemigroup.exists_gradient_orbit_energy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      Continuous G ∧
      (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P s.toNNReal f) (G s)) ∧
      ∀ t : ℝ≥0, (∫ s in (0 : ℝ)..(t : ℝ), ‖G s‖ ^ 2) ≤
        2 * (Real.exp (2 * Λ₀) * Λ₀) *
          Real.exp (2 * complexForceShift d Λ₀ ζ * (t : ℝ)) * ‖f‖ ^ 2 := by
  obtain ⟨G, hGc, hG⟩ := hP.exists_continuous_gradient_orbit hfg
  exact ⟨G, hGc, hG, fun t => hP.integral_gradient_le hfg hG t⟩

end EinsteinFull
