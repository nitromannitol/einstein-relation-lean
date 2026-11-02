import EinsteinFull.Blueprint.Foundation.node_e_u3A_lp_u2D_growth
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_environment
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup
import EinsteinFull.Calculus.ComplexHighExponentSupport
import EinsteinFull.Calculus.ComplexSemigroupCenteringSupport

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

private theorem centered_highLp_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {p : ℝ} (hp : 2 ≤ p)
    (f : Lp ℂ 2 (reducedLaw Q)) (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
    MemLp (centeredComplexLp Q f) (ENNReal.ofReal p) (reducedLaw Q) ∧
    eLpNorm (centeredComplexLp Q f) (ENNReal.ofReal p) (reducedLaw Q) ≤
      2 * eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) := by
  letI := reducedLaw_probability Q
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (by linarith)
  let c : ℂ := ∫ ω, f ω ∂reducedLaw Q
  have hc : MemLp (fun _ : FieldPair d => c) (ENNReal.ofReal p) (reducedLaw Q) :=
    memLp_const c
  have he := Lp.coeFn_const 2 (reducedLaw Q) c
  have hcm : MemLp (Lp.const 2 (reducedLaw Q) c) (ENNReal.ofReal p) (reducedLaw Q) :=
    hc.ae_eq he.symm
  have hb : eLpNorm (Lp.const 2 (reducedLaw Q) c) (ENNReal.ofReal p) (reducedLaw Q) ≤
      eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) := by
    rw [eLpNorm_congr_ae he]
    change eLpNorm (fun _ : FieldPair d => c) _ _ ≤ _
    rw [eLpNorm_const c (ne_zero_of_lt (lt_of_lt_of_le zero_lt_one hp1))
      (IsProbabilityMeasure.ne_zero (reducedLaw Q))]
    simp only [measure_univ, ENNReal.one_rpow, mul_one]
    exact (enorm_integral_le_lintegral_enorm _).trans (by
      rw [← eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
      exact eLpNorm_le_eLpNorm_of_exponent_le hp1)
  have hs := Lp.coeFn_sub f (Lp.const 2 (reducedLaw Q) c)
  refine ⟨(hf.sub hcm).ae_eq hs.symm, ?_⟩
  change eLpNorm (f - Lp.const 2 (reducedLaw Q) c) _ _ ≤ _
  rw [eLpNorm_congr_ae hs]
  exact (eLpNorm_sub_le hp1).trans
    (by simpa only [two_mul] using! add_le_add le_rfl hb)

/-- The adopted full-domain energy and cutoff-limit arguments provide the actual
forward and transpose bounds. The graph dependencies remain explicit for composition. -/
@[nolint unusedArguments]
theorem node_e_u3A_lp_u2D_growth_of_deps
    (_henv : node_stationary_u2D_environmentStmt)
    (_hanalytic : node_stationary_u2D_analytic_u2D_semigroupStmt) :
    node_e_u3A_lp_u2D_growthStmt := by
  intro d Λ₀ r₀ p _hd hp
  let K := Real.exp (2 * Λ₀) * Λ₀
  let A := (d : ℝ) * K ^ 3
  let C := 1 + |A| * (1 + (p - 1) ^ 2)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hforward : A ≤ C := by
    have h := mul_nonneg (abs_nonneg A) (sq_nonneg (p - 1))
    dsimp only [C]
    nlinarith [le_abs_self A]
  have htranspose : A * (p - 1) ^ 2 ≤ C := by
    have h := mul_le_mul_of_nonneg_right (le_abs_self A) (sq_nonneg (p - 1))
    dsimp only [C]
    nlinarith [abs_nonneg A]
  refine ⟨C, hC, ?_⟩
  intro Q i ζ P T hP hT
  dsimp only
  have hrate (B : ℝ) (hB : B ≤ C) (t : ℝ≥0) :
      Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hB (sq_nonneg ‖ζ‖)) t.property)
  have hbound (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) := hP.highLp_bound hp f hf t
  refine ⟨?_, hP.map_const, ?_, ?_⟩
  · intro t f hf
    obtain ⟨hPf, hbP⟩ := hbound t f hf
    obtain ⟨hTf, hbT⟩ := hT.highLp_bound hP hp f hf t
    have hbP' : eLpNorm (P t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal (Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) *
          eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) := by
      have he : ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) * (t : ℝ) =
          A * ‖ζ‖ ^ 2 * (t : ℝ) := by dsimp only [A, K]; ring
      rw [he] at hbP
      exact hbP.trans (by
        rw [mul_comm]
        exact _root_.mul_le_mul_left (ENNReal.ofReal_le_ofReal (hrate A hforward t)) _)
    have hbT' : eLpNorm (T t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal (Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) *
          eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) := by
      have he : ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (p - 1)) ^ 2) * (t : ℝ) =
          (A * (p - 1) ^ 2) * ‖ζ‖ ^ 2 * (t : ℝ) := by dsimp only [A, K]; ring
      rw [he] at hbT
      exact hbT.trans (by
        rw [mul_comm]
        exact _root_.mul_le_mul_left (ENNReal.ofReal_le_ofReal (hrate _ htranspose t)) _)
    rw [hP.centered_apply]
    obtain ⟨hSf, hbS⟩ := centered_highLp_bound Q hp (P t f) hPf
    refine ⟨hPf, hTf, hSf, hbP', hbT', ?_⟩
    calc
      _ ≤ 2 * eLpNorm (P t f) (ENNReal.ofReal p) (reducedLaw Q) := hbS
      _ ≤ 2 * (ENNReal.ofReal (Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) *
          eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)) := _root_.mul_le_mul_right hbP' _
      _ = _ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        exact (mul_assoc _ _ _).symm
  · intro f
    rw [hP.1, ContinuousLinearMap.id_apply, centeredComplexLp_idempotent]
  · intro s t f
    rw [hP.centered_apply, hP.centered_apply, hP.centered_apply,
      ← ContinuousLinearMap.comp_apply, ← hP.2.1, hP.centered_apply]

end EinsteinFull.Blueprint
