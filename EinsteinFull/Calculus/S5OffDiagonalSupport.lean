import EinsteinFull.Calculus.S5GaussianSupport

/-!
# Exponentially weighted bound for the physical semigroups

For every real `q`, every Euclidean-`1`-Lipschitz `ψ`, and every datum `f` with
`e^{qψ} f ∈ L²`, the forward and transpose evolutions satisfy
`‖e^{qψ} S_t f‖ ≤ exp (5 Λ³ (|ζ|² + q²) t) ‖e^{qψ} f‖`.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

section S5OffDiagonal

variable {d : ℕ}

theorem s5_weighted_forward {a : Vec d → Mat d} {Λ : ℝ}
    (hell : ∀ x, S5Elliptic (fun j k => a x j k) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k) (i : Fin d) (ζ : ℂ)
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P) (t : ℝ≥0) (q : ℝ) {ψ : Vec d → ℝ}
    (hψ : ∀ x y, |ψ x - ψ y| ≤ euclideanNorm (x - y))
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (hf : MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume) :
    MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * (P t f) x) 2 volume ∧
      (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * (P t f) x) 2 volume).toReal ≤
        Real.exp (5 * Λ ^ 3 * (‖ζ‖ ^ 2 + q ^ 2) * (t : ℝ)) *
          (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume).toReal := by
  have hK : 0 ≤ Real.exp (5 * Λ ^ 3 * (‖ζ‖ ^ 2 + q ^ 2) * (t : ℝ)) := (Real.exp_pos _).le
  obtain ⟨hm, hn⟩ := s5_signed_limit (q := q)
    (K := Real.exp (5 * Λ ^ 3 * (‖ζ‖ ^ 2 + q ^ 2) * (t : ℝ))) hK hψ f (P t f)
    (fun φ B hφ => by
      have h := s5_forward_growth hell hmeas hφ i ζ hP f t
      rwa [show (5 * Λ ^ 3 * (|q| ^ 2 + ‖ζ‖ ^ 2)) * (t : ℝ) =
        5 * Λ ^ 3 * (‖ζ‖ ^ 2 + q ^ 2) * (t : ℝ) from by rw [sq_abs]; ring] at h) hf
  refine ⟨hm, ?_⟩
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_lt_top.ne) hn
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] at h2

theorem s5_weighted_transpose {a : Vec d → Mat d} {Λ : ℝ}
    (hell : ∀ x, S5Elliptic (fun j k => a x j k) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k) (i : Fin d) (ζ : ℂ)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag) (t : ℝ≥0) (q : ℝ)
    {ψ : Vec d → ℝ} (hψ : ∀ x y, |ψ x - ψ y| ≤ euclideanNorm (x - y))
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (hf : MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume) :
    MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * (Pdag t f) x) 2 volume ∧
      (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * (Pdag t f) x) 2 volume).toReal ≤
        Real.exp (5 * Λ ^ 3 * (‖ζ‖ ^ 2 + q ^ 2) * (t : ℝ)) *
          (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume).toReal := by
  have hK : 0 ≤ Real.exp (5 * Λ ^ 3 * (‖ζ‖ ^ 2 + q ^ 2) * (t : ℝ)) := (Real.exp_pos _).le
  obtain ⟨hm, hn⟩ := s5_signed_limit (q := q)
    (K := Real.exp (5 * Λ ^ 3 * (‖ζ‖ ^ 2 + q ^ 2) * (t : ℝ))) hK hψ f (Pdag t f)
    (fun φ B hφ => by
      have h := s5_transpose_growth hell hmeas hφ i ζ hP f t
      rwa [show (5 * Λ ^ 3 * (|q| ^ 2 + ‖ζ‖ ^ 2)) * (t : ℝ) =
        5 * Λ ^ 3 * (‖ζ‖ ^ 2 + q ^ 2) * (t : ℝ) from by rw [sq_abs]; ring] at h) hf
  refine ⟨hm, ?_⟩
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_lt_top.ne) hn
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] at h2

end S5OffDiagonal

end EinsteinFull
