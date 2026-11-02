import EinsteinFull.Calculus.S4DivisionNine
import EinsteinFull.Frozen.ReducedLaw
import EinsteinRelation.Probability.ReductionLocality

/-!
# Small facts for the `e:division` assembly

* the total norm bound of the coefficients `divRecip`, `divB`, `divC`;
* `divB` at index zero;
* the mean clock density `m` is at least `exp (-2 Λ₀)` for a law with `IsRegular Λ₀` almost surely.
-/

open Finset MeasureTheory EinsteinRelation EinsteinRelation.TimeChange

namespace EinsteinFull

theorem div_total_bound {d : ℕ} {m C₁ Λ : ℝ} (hΛ : 0 ≤ Λ) (hC₁ : 0 ≤ C₁) (hmΛ : |m⁻¹| ≤ Λ)
    {etaC : Fin d → ℝ} (he : ∀ j, |etaC j| ≤ C₁) {aVec : Fin (d + 1) → Vec d}
    {χf : Option (Fin d) → ℝ}
    (hχ : euclideanNorm (fun i => χf (some i)) + |χf none| ≤ C₁) {Ae : Vec d}
    (hAe : euclideanNorm Ae ≤ C₁) (haC : ∀ n, euclideanNorm (aVec n) ≤ C₁) :
    ∑ n : Fin (d + 1), |divRecip d m etaC n| + ∑ n : Fin (d + 1), euclideanNorm (divB d m etaC aVec n) +
        euclideanNorm (divC m χf Ae) ≤
      ((d : ℝ) + 1) * recipBound Λ C₁ d +
        ((d : ℝ) + 1) * (((d : ℝ) + 1) * (recipBound Λ C₁ d * C₁)) +
        (2 * Λ * C₁ + 2 * C₁ * Λ ^ 2 * C₁) := by
  have h1 : ∑ n : Fin (d + 1), |divRecip d m etaC n| ≤ ((d : ℝ) + 1) * recipBound Λ C₁ d := by
    calc ∑ n : Fin (d + 1), |divRecip d m etaC n| ≤ ∑ _n : Fin (d + 1), recipBound Λ C₁ d :=
          Finset.sum_le_sum fun n _ => abs_divRecip_le hΛ hC₁ hmΛ he n
      _ = ((d : ℝ) + 1) * recipBound Λ C₁ d := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have h2 : ∑ n : Fin (d + 1), euclideanNorm (divB d m etaC aVec n) ≤
      ((d : ℝ) + 1) * (((d : ℝ) + 1) * (recipBound Λ C₁ d * C₁)) := by
    calc ∑ n : Fin (d + 1), euclideanNorm (divB d m etaC aVec n) ≤
          ∑ _n : Fin (d + 1), ((d : ℝ) + 1) * (recipBound Λ C₁ d * C₁) :=
          Finset.sum_le_sum fun n _ => euclideanNorm_divB_le hΛ hC₁ hmΛ he haC n
      _ = ((d : ℝ) + 1) * (((d : ℝ) + 1) * (recipBound Λ C₁ d * C₁)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have h3 := euclideanNorm_divC_le (m := m) (χf := χf) hΛ hC₁ hmΛ hχ hAe
  linarith

theorem divB_zero {d : ℕ} (m : ℝ) (etaC : Fin d → ℝ) (aVec : Fin (d + 1) → Vec d)
    {Ae : Vec d} (hAe : aVec ⟨0, Nat.zero_lt_succ d⟩ = Ae) :
    divB d m etaC aVec ⟨0, Nat.zero_lt_succ d⟩ = m⁻¹ • Ae := by
  unfold divB
  rw [Fin.sum_univ_succ]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  have := divRecip_zero d m etaC
  simp only [Fin.val_zero, Nat.sub_zero] at *
  rw [← hAe, ← this]

theorem clock_mean_lower {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    Real.exp (-2 * Λ₀) ≤ ∫ ω, clockDensity ω (0 : Vec d) ∂Q.measure := by
  haveI := Q.probability
  have hc : Continuous fun ω : FieldPair d => clockDensity ω (0 : Vec d) :=
    Real.continuous_exp.comp (continuous_const.mul
      ((continuous_eval_const (0 : Vec d)).comp continuous_snd))
  have hlow : ∀ᵐ ω ∂Q.measure, Real.exp (-2 * Λ₀) ≤ clockDensity ω (0 : Vec d) := by
    filter_upwards [Q.regular] with ω hω
    have h := (abs_le.1 (hω.2.1 0)).2
    show Real.exp (-2 * Λ₀) ≤ Real.exp (-2 * ω.2 0)
    exact Real.exp_le_exp.2 (by linarith)
  have hup : ∀ᵐ ω ∂Q.measure, ‖clockDensity ω (0 : Vec d)‖ ≤ Real.exp (2 * Λ₀) := by
    filter_upwards [Q.regular] with ω hω
    have h := (abs_le.1 (hω.2.1 0)).1
    rw [Real.norm_eq_abs, abs_of_pos (clockDensity_pos ω 0)]
    show Real.exp (-2 * ω.2 0) ≤ Real.exp (2 * Λ₀)
    exact Real.exp_le_exp.2 (by linarith)
  have hint : Integrable (fun ω : FieldPair d => clockDensity ω (0 : Vec d)) Q.measure :=
    Integrable.mono' (integrable_const (Real.exp (2 * Λ₀))) hc.aestronglyMeasurable hup
  have := integral_mono_ae (integrable_const (Real.exp (-2 * Λ₀))) hint hlow
  simpa using this

end EinsteinFull
