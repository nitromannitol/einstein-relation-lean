import EinsteinFull.Calculus.C3FluxSplitBochnerRecovery
import EinsteinFull.Calculus.C1FluxSchwartzConditionalBound

open MeasureTheory EinsteinRelation

namespace EinsteinFull.Blueprint

theorem c1_actual_schwartz_site_condExp_bound {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (z : Vec d) (J : Lp ℂ 2 (reducedLaw Q)) (c₀ c₁ : ℂ)
    (χ : Vec d → ℝ) (ψ : SchwartzMap (Vec d) ℂ)
    (θ : Bool → Bool → Vec d → ℝ) (baseline : Vec d → ℝ)
    (hθ : ∀ b q, ContDiff ℝ (⊤ : ℕ∞) (θ b q) ∧ HasCompactSupport (θ b q))
    (hb : ContDiff ℝ (⊤ : ℕ∞) baseline) (hbc : HasCompactSupport baseline)
    (hrec : ∀ y : Vec d,
      (χ (y - z) : ℂ) * ψ (-y) =
        c₀ * homogenizedGaussianKernel Q i s hs 0 (-(y - z)) *
          (((θ true false (y - z) - baseline (y - z) : ℝ) : ℂ) +
            Complex.I * ((θ true true (y - z) - baseline (y - z) : ℝ) : ℂ)) -
        c₁ * fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) (-(y - z)) (unitVector j) *
          (((θ false false (y - z) - baseline (y - z) : ℝ) : ℂ) +
            Complex.I * ((θ false true (y - z) - baseline (y - z) : ℝ) : ℂ))) :
    let B₀ := fun ξ : Vec d → ℝ => centeredComplexLp Q (∫ y : Vec d,
      ((ξ (y - z) : ℂ) * homogenizedGaussianKernel Q i s hs 0 (z - y)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
    let B₁ := fun ξ : Vec d → ℝ => centeredComplexLp Q (∫ y : Vec d,
      ((ξ (y - z) : ℂ) * fderiv ℝ (homogenizedGaussianKernel Q i s hs 0)
        (z - y) (unitVector j)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
    let U : Bool → Bool → FieldPair d → ℂ := fun b q =>
      if b then B₀ (θ b q) else B₁ (θ b q)
    let B : Bool → FieldPair d → ℂ := fun b => if b then B₀ baseline else B₁ baseline
    ∀ (q : ENNReal), 1 ≤ q → ∀ (m : MeasurableSpace (FieldPair d))
      (T : Bool → ℝ) (w : ℝ),
      (∀ b a, MemLp (U b a) q (reducedLaw Q)) →
      (∀ b, MemLp (B b) q (reducedLaw Q)) →
      (∀ b a, MemLp (U b a - (reducedLaw Q)[U b a | m]) q (reducedLaw Q)) →
      (∀ b, MemLp (B b - (reducedLaw Q)[B b | m]) q (reducedLaw Q)) →
      (∀ b a, (eLpNorm (U b a - (reducedLaw Q)[U b a | m]) q (reducedLaw Q)).toReal ≤ T b * w) →
      (∀ b, (eLpNorm (B b - (reducedLaw Q)[B b | m]) q (reducedLaw Q)).toReal ≤ T b * w) →
      let F := centeredComplexLp Q (∫ y : Vec d, ((χ (y-z) : ℂ) * ψ (-y)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
      MemLp ((F : FieldPair d → ℂ) - (reducedLaw Q)[(F : FieldPair d → ℂ) | m]) q (reducedLaw Q) ∧
      (eLpNorm ((F : FieldPair d → ℂ) - (reducedLaw Q)[(F : FieldPair d → ℂ) | m]) q (reducedLaw Q)).toReal ≤
        (4 * ‖c₀‖ * T true + 4 * ‖c₁‖ * T false) * w := by
  dsimp only
  intro q hq m T w hU hB hUE hBE hUb hBb
  let B₀ := fun ξ : Vec d → ℝ => centeredComplexLp Q (∫ y : Vec d,
      ((ξ (y - z) : ℂ) * homogenizedGaussianKernel Q i s hs 0 (z - y)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
  let B₁ := fun ξ : Vec d → ℝ => centeredComplexLp Q (∫ y : Vec d,
      ((ξ (y - z) : ℂ) * fderiv ℝ (homogenizedGaussianKernel Q i s hs 0)
        (z - y) (unitVector j)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
  let U : Bool → Bool → FieldPair d → ℂ := fun b q =>
      if b then B₀ (θ b q) else B₁ (θ b q)
  let B : Bool → FieldPair d → ℂ := fun b => if b then B₀ baseline else B₁ baseline
  have heq := c3_cutoff_site_as_eight_v2_blocks_split Q i j s hs z J c₀ c₁ χ ψ θ baseline hθ hb hbc hrec
  have hbound := c1_actual_eight_blocks_condExp_bound Q q hq m c₀ c₁ U B T w hU hB hUE hBE hUb hBb
  dsimp only at heq hbound
  change centeredComplexLp Q (∫ y : Vec d, ((χ (y-z) : ℂ) * ψ (-y)) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) =
    c₀ • ((B₀ (θ true false) - B₀ baseline) + Complex.I • (B₀ (θ true true) - B₀ baseline)) -
    c₁ • ((B₁ (θ false false) - B₁ baseline) + Complex.I • (B₁ (θ false true) - B₁ baseline)) at heq
  have hae := congrArg (fun v : Lp ℂ 2 (reducedLaw Q) => (v : FieldPair d → ℂ)) heq
  have ha : (centeredComplexLp Q (∫ y : Vec d, ((χ (y-z) : ℂ) * ψ (-y)) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      c₀ • ((U true false - B true) + Complex.I • (U true true - B true)) -
      c₁ • ((U false false - B false) + Complex.I • (U false true - B false)) := by
    rw [hae]
    simp only [U, B, if_true, Bool.false_eq_true, if_false]
    let v₀ := B₀ (θ true false) - B₀ baseline
    let v₁ := B₀ (θ true true) - B₀ baseline
    let v₂ := B₁ (θ false false) - B₁ baseline
    let v₃ := B₁ (θ false true) - B₁ baseline
    filter_upwards [Lp.coeFn_sub (c₀ • (v₀ + Complex.I • v₁)) (c₁ • (v₂ + Complex.I • v₃)),
      Lp.coeFn_smul c₀ (v₀ + Complex.I • v₁), Lp.coeFn_smul c₁ (v₂ + Complex.I • v₃),
      Lp.coeFn_add v₀ (Complex.I • v₁), Lp.coeFn_add v₂ (Complex.I • v₃),
      Lp.coeFn_sub (B₀ (θ true false)) (B₀ baseline),
      Lp.coeFn_sub (B₀ (θ true true)) (B₀ baseline),
      Lp.coeFn_sub (B₁ (θ false false)) (B₁ baseline),
      Lp.coeFn_sub (B₁ (θ false true)) (B₁ baseline),
      Lp.coeFn_smul Complex.I v₁, Lp.coeFn_smul Complex.I v₃] with
      x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁
    simp_all only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, v₀, v₁, v₂, v₃]

  have hc := condExp_congr_ae ha (m := m)
  have hr := ha.sub hc
  exact ⟨hbound.1.ae_eq hr.symm, by rw [eLpNorm_congr_ae hr]; exact hbound.2⟩

end EinsteinFull.Blueprint
