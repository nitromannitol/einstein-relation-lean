import EinsteinFull.Calculus.ComplexGeneratorOperatorSupport
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Strong approximation by actual stationary resolvents

The normalized positive unforced resolvents are contractions and converge
strongly to the identity on the whole actual complex L2 space. The proof
first uses the exact full generator graph and then its proved dense domain.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Normalized positive unforced resolvents are contractions on actual complex L2. -/
theorem norm_smul_unforcedComplexResolvent_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖(s : ℂ) • unforcedComplexResolvent Q i s hs f‖ ≤ ‖f‖ := by
  have hb := (unforcedComplexResolvent_spec Q i s hs f).unforced_resolvent_bound s
  simpa only [sub_sub_cancel, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs] using hb

/-- On the full generator domain, the normalized resolvent error is the resolvent of the output. -/
theorem IsComplexGeneratorPair.unforced_resolvent_error {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i 0 f g) (s : ℝ) (hs : 0 < s) :
    (s : ℂ) • unforcedComplexResolvent Q i s hs f - f =
      unforcedComplexResolvent Q i s hs g := by
  have he := (isComplexGeneratorPair_iff_resolvent Q i s hs f g).mp hfg
  rw [map_sub, map_smul] at he
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp he).trans (add_comm _ _))

/-- Normalized actual unforced resolvents at the positive integer shifts. -/
def unforcedComplexResolventApproximation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (((n : ℝ) + 1 : ℝ) : ℂ) • unforcedComplexResolvent Q i ((n : ℝ) + 1) (by positivity)

/-- Every member of the normalized resolvent sequence is a contraction. -/
theorem norm_unforcedComplexResolventApproximation_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖unforcedComplexResolventApproximation Q i n f‖ ≤ ‖f‖ :=
  norm_smul_unforcedComplexResolvent_le Q i ((n : ℝ) + 1) (by positivity) f

private theorem tendsto_approximation_on_domain {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q i 0 f g) :
    Tendsto (fun n => unforcedComplexResolventApproximation Q i n f) atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb (n : ℕ) : ‖unforcedComplexResolventApproximation Q i n f - f‖ ≤
      ((n : ℝ) + 1)⁻¹ * ‖g‖ := by
    change ‖(((n : ℝ) + 1 : ℝ) : ℂ) •
      unforcedComplexResolvent Q i ((n : ℝ) + 1) (by positivity) f - f‖ ≤ _
    rw [hfg.unforced_resolvent_error]
    exact (unforcedComplexResolvent Q i ((n : ℝ) + 1) (by positivity)).le_opNorm g |>.trans
      (mul_le_mul_of_nonneg_right
        (norm_unforcedComplexResolvent_le Q i ((n : ℝ) + 1) (by positivity)) (norm_nonneg g))
  have hz : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * ‖g‖) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖g‖
    simpa only [one_div, zero_mul] using h
  exact squeeze_zero (fun _ => norm_nonneg _) hb hz

/-- The actual normalized unforced resolvents converge strongly to the identity on all complex L2. -/
theorem tendsto_unforcedComplexResolventApproximation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun n => unforcedComplexResolventApproximation Q i n f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨u, ⟨g, hug⟩, hfu⟩ :=
    (dense_unforced_complexGenerator_domain Q i).exists_dist_lt f (by positivity : 0 < ε/3)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_approximation_on_domain Q i u g hug)
    (ε/3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hc : dist (unforcedComplexResolventApproximation Q i n f)
      (unforcedComplexResolventApproximation Q i n u) ≤ dist f u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact norm_unforcedComplexResolventApproximation_le Q i n (f-u)
  calc
    dist (unforcedComplexResolventApproximation Q i n f) f ≤
        dist (unforcedComplexResolventApproximation Q i n f)
          (unforcedComplexResolventApproximation Q i n u) +
          dist (unforcedComplexResolventApproximation Q i n u) f := dist_triangle _ _ _
    _ ≤ dist f u + (dist (unforcedComplexResolventApproximation Q i n u) u + dist u f) :=
      add_le_add hc (dist_triangle _ _ _)
    _ < ε := by
      have hnu := hN n hn
      rw [dist_comm u f]
      linarith only [hfu, hnu]

/-- Bounded Yosida approximations constructed from the actual unforced resolvents. -/
def unforcedComplexYosida {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (n : ℕ) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (((n : ℝ) + 1 : ℝ) : ℂ) • (unforcedComplexResolventApproximation Q i n -
    ContinuousLinearMap.id ℂ (Lp ℂ 2 (reducedLaw Q)))

/-- A Yosida approximation and its regularized value lie in the entire actual generator graph. -/
theorem unforcedComplexYosida_graph {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexGeneratorPair Q i 0 (unforcedComplexResolventApproximation Q i n f)
      (unforcedComplexYosida Q i n f) := by
  have h := (unforcedComplexResolvent_spec Q i ((n : ℝ) + 1) (by positivity) f).smul
    (((n : ℝ) + 1 : ℝ) : ℂ)
  exact h

/-- Each bounded Yosida approximation is dissipative on the whole complex L2 space. -/
theorem unforcedComplexYosida_re_inner_nonpos {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) :
    (inner ℂ f (unforcedComplexYosida Q i n f)).re ≤ 0 := by
  have hc := norm_unforcedComplexResolventApproximation_le Q i n f
  have hh : (inner ℂ f (unforcedComplexResolventApproximation Q i n f)).re ≤ ‖f‖ ^ 2 := by
    calc
      _ ≤ ‖inner ℂ f (unforcedComplexResolventApproximation Q i n f)‖ := Complex.re_le_norm _
      _ ≤ ‖f‖ * ‖unforcedComplexResolventApproximation Q i n f‖ := norm_inner_le_norm _ _
      _ ≤ ‖f‖ * ‖f‖ := mul_le_mul_of_nonneg_left hc (norm_nonneg f)
      _ = ‖f‖ ^ 2 := (pow_two _).symm
  have hself : (inner ℂ f f).re = ‖f‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) f).symm
  change (inner ℂ f ((((n : ℝ) + 1 : ℝ) : ℂ) •
    (unforcedComplexResolventApproximation Q i n f - f))).re ≤ 0
  rw [inner_smul_right, inner_sub_right, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re, hself]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hh)

/-- Bounded Yosida approximations converge to the actual generator on its full domain. -/
theorem IsComplexGeneratorPair.tendsto_unforcedComplexYosida {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i 0 f g) :
    Tendsto (fun n => unforcedComplexYosida Q i n f) atTop (𝓝 g) := by
  have he (n : ℕ) : unforcedComplexYosida Q i n f =
      unforcedComplexResolventApproximation Q i n g := by
    change (((n : ℝ) + 1 : ℝ) : ℂ) •
      ((((n : ℝ) + 1 : ℝ) : ℂ) •
        unforcedComplexResolvent Q i ((n : ℝ) + 1) (by positivity) f - f) = _
    rw [hfg.unforced_resolvent_error]
    rfl
  simp_rw [he]
  exact tendsto_unforcedComplexResolventApproximation Q i g

end EinsteinFull
