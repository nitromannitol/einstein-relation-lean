import EinsteinFull.Calculus.ComplexForceOperatorSupport
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Strong approximation of the shifted forced stationary generator

The normalized shifted forced resolvents are contractions and converge
strongly to the identity on the whole actual complex L2 space. The proof
first uses the exact full generator graph and then its proved dense domain.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Resolvents normalized by their distance above the force shift are contractions. -/
theorem norm_smul_forcedComplexResolvent_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖((s - complexForceShift d Λ₀ ζ : ℝ) : ℂ) •
      forcedComplexResolvent Q i ζ s hs f‖ ≤ ‖f‖ := by
  have hb := (forcedComplexResolvent_spec Q i ζ s hs f).forced_resolvent_bound s
  simpa only [sub_sub_cancel, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr hs)] using hb

/-- The exact normalized resolvent error on the full forced generator domain. -/
theorem IsComplexGeneratorPair.forced_resolvent_error {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) :
    ((s - complexForceShift d Λ₀ ζ : ℝ) : ℂ) • forcedComplexResolvent Q i ζ s hs f - f =
      forcedComplexResolvent Q i ζ s hs (g - (complexForceShift d Λ₀ ζ : ℂ) • f) := by
  have he := (isComplexGeneratorPair_iff_forced_resolvent Q i ζ s hs f g).mp hfg
  rw [map_sub, map_smul] at he
  rw [map_sub, map_smul]
  have herr : (s : ℂ) • forcedComplexResolvent Q i ζ s hs f - f =
      forcedComplexResolvent Q i ζ s hs g :=
    sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp he).trans (add_comm _ _))
  push_cast
  calc
    _ = ((s : ℂ) • forcedComplexResolvent Q i ζ s hs f - f) -
        (complexForceShift d Λ₀ ζ : ℂ) • forcedComplexResolvent Q i ζ s hs f := by module
    _ = _ := by rw [herr]

/-- Normalized actual forced resolvents at the integer shifts above the force shift. -/
def forcedComplexResolventApproximation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (((n : ℝ) + 1 : ℝ) : ℂ) •
    forcedComplexResolvent Q i ζ (complexForceShift d Λ₀ ζ + ((n : ℝ) + 1))
      (by exact lt_add_of_pos_right _ (by positivity))

/-- Every member of the normalized resolvent sequence is a contraction. -/
theorem norm_forcedComplexResolventApproximation_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖forcedComplexResolventApproximation Q i ζ n f‖ ≤ ‖f‖ := by
  have h := norm_smul_forcedComplexResolvent_le Q i ζ
    (complexForceShift d Λ₀ ζ + ((n : ℝ) + 1))
      (by exact lt_add_of_pos_right _ (by positivity)) f
  simpa only [add_sub_cancel_left] using! h

private theorem tendsto_approximation_on_domain {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q i ζ f g) :
    Tendsto (fun n => forcedComplexResolventApproximation Q i ζ n f) atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb (n : ℕ) : ‖forcedComplexResolventApproximation Q i ζ n f - f‖ ≤
      ((n : ℝ) + 1)⁻¹ * ‖g - (complexForceShift d Λ₀ ζ : ℂ) • f‖ := by
    let s := complexForceShift d Λ₀ ζ + ((n : ℝ) + 1)
    have hs : complexForceShift d Λ₀ ζ < s :=
      lt_add_of_pos_right _ (by positivity)
    have he := hfg.forced_resolvent_error s hs
    simp only [s, add_sub_cancel_left] at he
    change ‖(((n : ℝ) + 1 : ℝ) : ℂ) • forcedComplexResolvent Q i ζ s hs f - f‖ ≤ _
    rw [he]
    exact ((forcedComplexResolvent Q i ζ s hs).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right
        (by simpa only [s, add_sub_cancel_left] using norm_forcedComplexResolvent_le Q i ζ s hs)
        (norm_nonneg _))
  have hz : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ *
      ‖g - (complexForceShift d Λ₀ ζ : ℂ) • f‖) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      ‖g - (complexForceShift d Λ₀ ζ : ℂ) • f‖
    simpa only [one_div, zero_mul] using h
  exact squeeze_zero (fun _ => norm_nonneg _) hb hz

/-- The actual normalized forced resolvents converge strongly to the identity on all complex L2. -/
theorem tendsto_forcedComplexResolventApproximation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun n => forcedComplexResolventApproximation Q i ζ n f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨u, ⟨g, hug⟩, hfu⟩ :=
    (dense_complexGenerator_domain Q i ζ).exists_dist_lt f (by positivity : 0 < ε/3)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_approximation_on_domain Q i ζ u g hug)
    (ε/3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hc : dist (forcedComplexResolventApproximation Q i ζ n f)
      (forcedComplexResolventApproximation Q i ζ n u) ≤ dist f u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact norm_forcedComplexResolventApproximation_le Q i ζ n (f-u)
  calc
    dist (forcedComplexResolventApproximation Q i ζ n f) f ≤
        dist (forcedComplexResolventApproximation Q i ζ n f)
          (forcedComplexResolventApproximation Q i ζ n u) +
          dist (forcedComplexResolventApproximation Q i ζ n u) f := dist_triangle _ _ _
    _ ≤ dist f u + (dist (forcedComplexResolventApproximation Q i ζ n u) u + dist u f) :=
      add_le_add hc (dist_triangle _ _ _)
    _ < ε := by
      have hnu := hN n hn
      rw [dist_comm u f]
      linarith only [hfu, hnu]

/-- Bounded Yosida approximations constructed from the actual forced resolvents. -/
def forcedComplexYosida {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (n : ℕ) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (((n : ℝ) + 1 : ℝ) : ℂ) • (forcedComplexResolventApproximation Q i ζ n -
    ContinuousLinearMap.id ℂ (Lp ℂ 2 (reducedLaw Q)))

/-- A Yosida approximation and its regularized value lie in the entire actual generator graph. -/
theorem forcedComplexYosida_graph {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexGeneratorPair Q i ζ (forcedComplexResolventApproximation Q i ζ n f)
      (forcedComplexYosida Q i ζ n f + (complexForceShift d Λ₀ ζ : ℂ) •
        forcedComplexResolventApproximation Q i ζ n f) := by
  have h := (forcedComplexResolvent_spec Q i ζ (complexForceShift d Λ₀ ζ + ((n : ℝ) + 1))
      (by exact lt_add_of_pos_right _ (by positivity)) f).smul
    (((n : ℝ) + 1 : ℝ) : ℂ)
  convert! h using 1
  let c : ℂ := (((n : ℝ) + 1 : ℝ) : ℂ)
  let r := forcedComplexResolvent Q i ζ (complexForceShift d Λ₀ ζ + ((n : ℝ) + 1))
    (by exact lt_add_of_pos_right _ (by positivity)) f
  change c • (c • r - f) + (complexForceShift d Λ₀ ζ : ℂ) • (c • r) =
    c • ((↑(complexForceShift d Λ₀ ζ + ((n : ℝ) + 1)) : ℂ) • r - f)
  dsimp only [c]
  push_cast
  module

/-- Each bounded Yosida approximation is dissipative on the whole complex L2 space. -/
theorem forcedComplexYosida_re_inner_nonpos {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) :
    (inner ℂ f (forcedComplexYosida Q i ζ n f)).re ≤ 0 := by
  have hc := norm_forcedComplexResolventApproximation_le Q i ζ n f
  have hh : (inner ℂ f (forcedComplexResolventApproximation Q i ζ n f)).re ≤ ‖f‖ ^ 2 := by
    calc
      _ ≤ ‖inner ℂ f (forcedComplexResolventApproximation Q i ζ n f)‖ := Complex.re_le_norm _
      _ ≤ ‖f‖ * ‖forcedComplexResolventApproximation Q i ζ n f‖ := norm_inner_le_norm _ _
      _ ≤ ‖f‖ * ‖f‖ := mul_le_mul_of_nonneg_left hc (norm_nonneg f)
      _ = ‖f‖ ^ 2 := (pow_two _).symm
  have hself : (inner ℂ f f).re = ‖f‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) f).symm
  change (inner ℂ f ((((n : ℝ) + 1 : ℝ) : ℂ) •
    (forcedComplexResolventApproximation Q i ζ n f - f))).re ≤ 0
  rw [inner_smul_right, inner_sub_right, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re, hself]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hh)

/-- On the full domain, the bounded shifted generator is the regularized shifted output. -/
theorem IsComplexGeneratorPair.forcedComplexYosida_eq {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g) (n : ℕ) :
    forcedComplexYosida Q i ζ n f = forcedComplexResolventApproximation Q i ζ n
      (g - (complexForceShift d Λ₀ ζ : ℂ) • f) := by
  change (((n : ℝ) + 1 : ℝ) : ℂ) •
    ((((n : ℝ) + 1 : ℝ) : ℂ) • forcedComplexResolvent Q i ζ
      (complexForceShift d Λ₀ ζ + ((n : ℝ) + 1)) _ f - f) = _
  have he := hfg.forced_resolvent_error (complexForceShift d Λ₀ ζ + ((n : ℝ) + 1))
   
      (by exact lt_add_of_pos_right _ (by positivity))
  simp only [add_sub_cancel_left] at he
  rw [he]
  rfl

/-- Bounded Yosida approximations converge to the shifted generator on its full domain. -/
theorem IsComplexGeneratorPair.tendsto_forcedComplexYosida {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g) :
    Tendsto (fun n => forcedComplexYosida Q i ζ n f) atTop
      (𝓝 (g - (complexForceShift d Λ₀ ζ : ℂ) • f)) := by
  simp_rw [hfg.forcedComplexYosida_eq]
  exact tendsto_forcedComplexResolventApproximation Q i ζ
    (g - (complexForceShift d Λ₀ ζ : ℂ) • f)

end EinsteinFull
