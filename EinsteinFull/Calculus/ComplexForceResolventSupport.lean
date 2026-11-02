import EinsteinFull.Calculus.ComplexForceCoercivitySupport
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Option

/-!
# Resolvents of the actual forced stationary generator

The closed strong horizontal value-gradient graph is a real Hilbert space.
Its actual anisotropic energy and column drift give a continuous real form.
The proved quadratic force shift makes the form coercive. The closed graph
realization and conjugate-test algebra follow ComplexGeneratorResolventSupport,
now using the public actual coefficient multipliers. Real Lax–Milgram,
with imaginary test multiples, gives the full complex weak generator graph.
-/

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

private theorem realL2Inner_eq_re {d : ℕ} (Q : Measure (FieldPair d))
    (u v : Lp ℂ 2 Q) : inner ℝ u v = (inner ℂ u v).re := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) u v)

private def horizontalGraph {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q) :
    Submodule ℝ (PiLp 2 (fun _ : Option (Fin d) => Lp ℂ 2 Q)) where
  carrier := {u | HasComplexHorizontalGradient Q hQ (u none) (fun j => u (some j))}
  zero_mem' := HasComplexHorizontalDerivative.zero Q hQ
  add_mem' := fun hu hv j => (hu j).add (hv j)
  smul_mem' := by
    intro c u hu j
    simpa only [Complex.coe_smul, PiLp.smul_apply] using! (hu j).smul (c : ℂ)

private theorem horizontalGraph_closed {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) :
    IsClosed (horizontalGraph Q hQ : Set (PiLp 2 (fun _ : Option (Fin d) => Lp ℂ 2 Q))) := by
  have hc : Continuous (fun u : PiLp 2 (fun _ : Option (Fin d) => Lp ℂ 2 Q) =>
      (u none, fun j : Fin d => u (some j))) :=
    (PiLp.continuous_apply 2 _ none).prodMk
      (continuous_pi fun j => PiLp.continuous_apply 2 _ (some j))
  exact IsClosed.preimage hc (isClosed_complexHorizontalGradient_graph Q hQ)

private theorem horizontalGraph_norm_sq {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (u : horizontalGraph Q hQ) :
    ‖u‖ ^ 2 = ‖(u.val) none‖ ^ 2 + ∑ j : Fin d, ‖(u.val) (some j)‖ ^ 2 := by
  rw [← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2, univ_option, Finset.sum_insertNone]

private theorem energy_eq_inner_sum {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, ∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * H k ω ∂reducedLaw Q) =
      ∑ j, ∑ k, inner ℂ (G j) (complexCoefficientMul Q j k (H k)) := by
  have hint (j k : Fin d) : Integrable
      (fun ω => star (G j ω) * (ω.1 0 j k : ℂ) * H k ω) (reducedLaw Q) := by
    have hp := ((Lp.memLp (G j)).star.integrable_mul
      (Lp.memLp (H k))).mul_of_top_right (memLp_reduced_coefficient_complex Q j k)
    convert hp using 1
    ext ω
    simp only [Pi.mul_apply, Pi.star_apply]
    ring
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hint j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum _ (fun k _ => hint j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [complexCoefficientMul_coe Q j k (H k)] with ω hω
  simp only [hω, RCLike.inner_apply, Complex.star_def]
  ring

private def graphEval {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (o : Option (Fin d)) : horizontalGraph Q hQ →L[ℝ] Lp ℂ 2 Q :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin d) => Lp ℂ 2 Q) o).comp
    (horizontalGraph Q hQ).subtypeL

private def graphDrift {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q) →L[ℝ]
      Lp ℂ 2 (reducedLaw Q) :=
  ∑ j, ((complexCoefficientMul Q j i).restrictScalars ℝ).comp
    (graphEval (reducedLaw Q) (reducedLaw_stationary Q) (some j))

private theorem graphDrift_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (u : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) :
    graphDrift Q i u = complexForceDrift Q i (WithLp.toLp 2 (fun j => u.val (some j))) := by
  simp only [graphDrift, complexForceDrift, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    graphEval, PiLp.proj_apply, Submodule.subtypeL_apply]

private def resolventForm {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ) :
    horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q) →L[ℝ]
      horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q) →L[ℝ] ℝ :=
  let E := graphEval (reducedLaw Q) (reducedLaw_stationary Q)
  let I : Lp ℂ 2 (reducedLaw Q) →L[ℝ] Lp ℂ 2 (reducedLaw Q) →L[ℝ] ℝ := innerSL ℝ
  s • I.bilinearComp (E none) (E none) + (1 / 2 : ℝ) •
    ∑ j : Fin d, ∑ k : Fin d,
      (I.bilinearComp (E (some j))
        (((complexCoefficientMul Q j k).restrictScalars ℝ).comp (E (some k)))).flip -
    I.bilinearComp (ζ • graphDrift Q i) (E none)

private def resolventExpression {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (u v : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) : ℂ :=
  (s : ℂ) * inner ℂ (v.val none) (u.val none) + ((1 / 2 : ℝ) : ℂ) *
    ∑ j, ∑ k, inner ℂ (v.val (some j)) (complexCoefficientMul Q j k (u.val (some k))) -
    ζ * inner ℂ (v.val none) (graphDrift Q i u)

private theorem resolventForm_eq_re_expression {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (u v : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) :
    resolventForm Q i ζ s u v = (resolventExpression Q i ζ s u v).re := by
  simp only [resolventForm, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    graphEval, PiLp.proj_apply, Submodule.subtypeL_apply, smul_eq_mul]
  change s * inner ℝ (u.val none) (v.val none) + (1 / 2 : ℝ) *
    (∑ j, ∑ k, inner ℝ (v.val (some j)) (complexCoefficientMul Q j k (u.val (some k)))) -
    inner ℝ (ζ • graphDrift Q i u) (v.val none) = _
  simp only [realL2Inner_eq_re, resolventExpression, Complex.add_re, Complex.sub_re,
    Complex.re_ofReal_mul, Complex.re_sum]
  have hm : (inner ℂ (u.val none) (v.val none)).re =
      (inner ℂ (v.val none) (u.val none)).re := inner_re_symm (𝕜 := ℂ) _ _
  have hd : (inner ℂ (ζ • graphDrift Q i u) (v.val none)).re =
      (inner ℂ (v.val none) (ζ • graphDrift Q i u)).re := inner_re_symm (𝕜 := ℂ) _ _
  rw [hm, hd, inner_smul_right]

private theorem resolventForm_coercive {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) : IsCoercive (resolventForm Q i ζ s) := by
  let K := Real.exp (2 * Λ₀) * Λ₀
  have hK : 0 < K := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  let a := min (s - complexForceShift d Λ₀ ζ) (K⁻¹ / 4)
  refine ⟨a, lt_min (sub_pos.mpr hs) (div_pos (inv_pos.mpr hK) (by norm_num)), ?_⟩
  intro u
  have hb := reduced_complex_energy_lowerBound Q (fun j => u.val (some j))
  have hy := re_complexForceDrift_pair_le Q i ζ (u.val none)
    (WithLp.toLp 2 (fun j => u.val (some j)))
  rw [← graphDrift_apply] at hy
  rw [energy_eq_inner_sum] at hb
  have hn : 0 ≤ ∑ j : Fin d, ‖u.val (some j)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hself : (inner ℂ (u.val none) (u.val none)).re = ‖u.val none‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (u.val none)).symm
  have hl : a * ‖u‖ * ‖u‖ ≤
      (s - complexForceShift d Λ₀ ζ) * ‖u.val none‖ ^ 2 +
        (K⁻¹ / 4) * (∑ j : Fin d, ‖u.val (some j)‖ ^ 2) := by
    calc
      _ = a * (‖u.val none‖ ^ 2 + ∑ j : Fin d, ‖u.val (some j)‖ ^ 2) := by
        rw [← horizontalGraph_norm_sq]
        ring
      _ ≤ _ := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (min_le_right _ _) hn)
  rw [resolventForm_eq_re_expression]
  simp only [resolventExpression, Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul,
    hself]
  linarith only [hb, hy, hl]

private theorem exists_real_variational_solution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃ u : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q),
      ∀ v, resolventForm Q i ζ s u v = inner ℝ rhs (graphEval (reducedLaw Q)
        (reducedLaw_stationary Q) none v) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  letI : CompleteSpace (horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) :=
    (horizontalGraph_closed (reducedLaw Q) (reducedLaw_stationary Q)).completeSpace_coe
  let S := graphEval (reducedLaw Q) (reducedLaw_stationary Q) none
  let hB := resolventForm_coercive Q i ζ s hs
  let u := hB.continuousLinearEquivOfBilin.symm (S.adjoint rhs)
  refine ⟨u, fun v => ?_⟩
  have hb := hB.continuousLinearEquivOfBilin_apply u v
  rw [hB.continuousLinearEquivOfBilin.apply_symm_apply] at hb
  exact hb.symm.trans (S.adjoint_inner_left v rhs)

private def graphComplexSmul {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (c : ℂ) (v : horizontalGraph Q hQ) : horizontalGraph Q hQ :=
  ⟨c • v.val, fun j => (v.property j).smul c⟩

private theorem resolventExpression_I {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (u v : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) :
    resolventExpression Q i ζ s u
      (graphComplexSmul (reducedLaw Q) (reducedLaw_stationary Q) Complex.I v) =
      -Complex.I * resolventExpression Q i ζ s u v := by
  simp only [resolventExpression, graphComplexSmul, PiLp.smul_apply, inner_smul_left,
    Complex.conj_I, ← Finset.mul_sum]
  ring

private theorem exists_complex_variational_solution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃ u : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q),
      ∀ v, resolventExpression Q i ζ s u v = inner ℂ (v.val none) rhs := by
  obtain ⟨u, hu⟩ := exists_real_variational_solution Q i ζ s hs rhs
  refine ⟨u, fun v => Complex.ext ?_ ?_⟩
  · have h := hu v
    rw [resolventForm_eq_re_expression, realL2Inner_eq_re] at h
    exact h.trans (inner_re_symm (𝕜 := ℂ) _ _)
  · have h := hu (graphComplexSmul (reducedLaw Q) (reducedLaw_stationary Q) Complex.I v)
    rw [resolventForm_eq_re_expression, resolventExpression_I, realL2Inner_eq_re] at h
    change (-Complex.I * resolventExpression Q i ζ s u v).re =
      (inner ℂ rhs (Complex.I • v.val none)).re at h
    rw [inner_smul_right] at h
    simp only [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] at h
    have him : (inner ℂ rhs (v.val none)).im = -(inner ℂ (v.val none) rhs).im :=
      inner_im_symm (𝕜 := ℂ) _ _
    linarith only [h, him]

private theorem inner_star_eq_integral_mul {d : ℕ} (Q : Measure (FieldPair d))
    (v f : Lp ℂ 2 Q) : inner ℂ (star v) f = ∫ ω, v ω * f ω ∂Q := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star v] with ω hω
  change (star v) ω = star (v ω) at hω
  simp only [hω, RCLike.inner_apply, Complex.star_def, starRingEnd_self_apply]
  ring

private theorem unforcedPair_of_variational {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ)
    (rhs : Lp ℂ 2 (reducedLaw Q))
    (u : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q))
    (hu : ∀ v : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q),
      (s : ℂ) * inner ℂ (v.val none) (u.val none) + ((1 / 2 : ℝ) : ℂ) *
        ∑ j, ∑ k, inner ℂ (v.val (some j)) (complexCoefficientMul Q j k (u.val (some k))) =
          inner ℂ (v.val none) rhs) :
    IsComplexGeneratorPair Q i 0 (u.val none) ((s : ℂ) • u.val none - rhs) := by
  refine ⟨fun j => u.val (some j), u.property, ?_⟩
  intro v Gv hv
  let w : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q) :=
    ⟨WithLp.toLp 2 (fun o => o.elim (star v) (fun j => star (Gv j))),
      fun j => (hv j).star⟩
  have ht := hu w
  change (s : ℂ) * inner ℂ (star v) (u.val none) + ((1 / 2 : ℝ) : ℂ) *
    (∑ j, ∑ k, inner ℂ (star (Gv j)) (complexCoefficientMul Q j k (u.val (some k)))) =
    inner ℂ (star v) rhs at ht
  rw [← energy_eq_inner_sum] at ht
  simp only [inner_star_eq_integral_mul] at ht
  have hE : (∫ ω, ∑ j, ∑ k, star ((star (Gv j) : Lp ℂ 2 (reducedLaw Q)) ω) *
      (ω.1 0 j k : ℂ) * u.val (some k) ω ∂reducedLaw Q) =
      ∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * u.val (some k) ω * Gv j ω ∂reducedLaw Q := by
    apply integral_congr_ae
    have ha : ∀ᵐ ω ∂reducedLaw Q, ∀ j, (star (Gv j) : Lp ℂ 2 (reducedLaw Q)) ω =
        star (Gv j ω) := ae_all_iff.mpr fun j => Lp.coeFn_star (Gv j)
    filter_upwards [ha] with ω hω
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hω j, star_star]
    ring
  rw [hE] at ht
  have hm : (∫ ω, ((s : ℂ) • u.val none - rhs : Lp ℂ 2 (reducedLaw Q)) ω * v ω
      ∂reducedLaw Q) =
      (s : ℂ) * (∫ ω, v ω * u.val none ω ∂reducedLaw Q) -
        ∫ ω, v ω * rhs ω ∂reducedLaw Q := by
    calc
      _ = ∫ ω, (s : ℂ) * (v ω * u.val none ω) - v ω * rhs ω ∂reducedLaw Q := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub ((s : ℂ) • u.val none) rhs,
          Lp.coeFn_smul (s : ℂ) (u.val none)] with ω ha hb
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ha hb
        rw [ha, hb]
        ring
      _ = _ := by
        have h1 : Integrable (fun ω => (s : ℂ) * (v ω * u.val none ω)) (reducedLaw Q) := by
          simpa only [Pi.mul_apply] using
            (((Lp.memLp v).integrable_mul (Lp.memLp (u.val none))).const_mul (s : ℂ))
        have h2 : Integrable (fun ω => v ω * rhs ω) (reducedLaw Q) :=
          (Lp.memLp v).integrable_mul (Lp.memLp rhs)
        rw [integral_sub h1 h2, integral_const_mul]
  rw [hm]
  simp only [zero_mul, add_zero]
  have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf] at ht
  linear_combination ht

/-- Every real shift above the structural quadratic force shift is onto the
full actual complex L2 weak generator graph, with the shifted norm bound. -/
theorem exists_forced_complexGenerator_resolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃ f : Lp ℂ 2 (reducedLaw Q),
      IsComplexGeneratorPair Q i ζ f ((s : ℂ) • f - rhs) ∧
        (s - complexForceShift d Λ₀ ζ) * ‖f‖ ≤ ‖rhs‖ := by
  obtain ⟨u, hu⟩ := exists_complex_variational_solution Q i ζ s hs rhs
  have hv : ∀ v : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q),
      (s : ℂ) * inner ℂ (v.val none) (u.val none) + ((1 / 2 : ℝ) : ℂ) *
        ∑ j, ∑ k, inner ℂ (v.val (some j)) (complexCoefficientMul Q j k (u.val (some k))) =
          inner ℂ (v.val none) (rhs + ζ • graphDrift Q i u) := by
    intro v
    have ht := hu v
    rw [inner_add_right, inner_smul_right]
    unfold resolventExpression at ht
    linear_combination ht
  have hf := (unforcedPair_of_variational Q i s (rhs + ζ • graphDrift Q i u) u hv).change_force
    ζ u.property
  simp only [sub_zero] at hf
  rw [← graphDrift_apply] at hf
  have he : ((s : ℂ) • u.val none - (rhs + ζ • graphDrift Q i u)) + ζ • graphDrift Q i u =
      (s : ℂ) • u.val none - rhs := by module
  rw [he] at hf
  refine ⟨u.val none, hf, ?_⟩
  have hb := hf.forced_resolvent_bound s
  simpa only [sub_sub_cancel] using hb

/-- The full forced resolvent problem has exactly one L2 solution above the shift. -/
theorem existsUnique_forced_complexGenerator_resolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃! f : Lp ℂ 2 (reducedLaw Q), IsComplexGeneratorPair Q i ζ f ((s : ℂ) • f - rhs) := by
  obtain ⟨f, hf, _⟩ := exists_forced_complexGenerator_resolvent Q i ζ s hs rhs
  exact ⟨f, hf, fun h hh => hh.forced_resolvent_unique hs hf⟩


private theorem exists_real_transpose_variational_solution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃ u : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q),
      ∀ v, resolventForm Q i ζ s v u = inner ℝ rhs (graphEval (reducedLaw Q)
        (reducedLaw_stationary Q) none v) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  letI : CompleteSpace (horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) :=
    (horizontalGraph_closed (reducedLaw Q) (reducedLaw_stationary Q)).completeSpace_coe
  let S := graphEval (reducedLaw Q) (reducedLaw_stationary Q) none
  have hB : IsCoercive (resolventForm Q i ζ s).flip := by
    obtain ⟨a, ha, hb⟩ := resolventForm_coercive Q i ζ s hs
    exact ⟨a, ha, hb⟩
  let u := hB.continuousLinearEquivOfBilin.symm (S.adjoint rhs)
  refine ⟨u, fun v => ?_⟩
  have hb := hB.continuousLinearEquivOfBilin_apply u v
  rw [hB.continuousLinearEquivOfBilin.apply_symm_apply] at hb
  exact hb.symm.trans (S.adjoint_inner_left v rhs)

private theorem graphDrift_complexSmul {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (c : ℂ)
    (v : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) :
    graphDrift Q i (graphComplexSmul (reducedLaw Q) (reducedLaw_stationary Q) c v) =
      c • graphDrift Q i v := by
  simp only [graphDrift, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', graphEval, PiLp.proj_apply,
    Submodule.subtypeL_apply, graphComplexSmul, PiLp.smul_apply, map_smul,
    Finset.smul_sum]

private theorem resolventExpression_first_I {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (u v : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) :
    resolventExpression Q i ζ s
      (graphComplexSmul (reducedLaw Q) (reducedLaw_stationary Q) Complex.I v) u =
      Complex.I * resolventExpression Q i ζ s v u := by
  unfold resolventExpression
  rw [graphDrift_complexSmul]
  simp only [graphComplexSmul, PiLp.smul_apply, map_smul, inner_smul_right,
    ← Finset.mul_sum]
  ring

private theorem exists_complex_transpose_variational_solution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃ u : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q),
      ∀ v, resolventExpression Q i ζ s v u = inner ℂ rhs (v.val none) := by
  obtain ⟨u, hu⟩ := exists_real_transpose_variational_solution Q i ζ s hs rhs
  refine ⟨u, fun v => Complex.ext ?_ ?_⟩
  · have h := hu v
    rw [resolventForm_eq_re_expression, realL2Inner_eq_re] at h
    exact h
  · have h := hu (graphComplexSmul (reducedLaw Q) (reducedLaw_stationary Q) Complex.I v)
    rw [resolventForm_eq_re_expression, resolventExpression_first_I, realL2Inner_eq_re] at h
    change (Complex.I * resolventExpression Q i ζ s v u).re =
      (inner ℂ rhs (Complex.I • v.val none)).re at h
    rw [inner_smul_right] at h
    simpa only [Complex.I_mul_re, neg_inj] using h

/-- The actual transposed H1 variational problem is onto above the same force
shift. Every H1 test is allowed, and its differentiated coefficient column is
retained in the drift. The solution and its gradient are constructed. -/
theorem exists_forced_complexTranspose_variational {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (f : Lp ℂ 2 (reducedLaw Q)) (Gf : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f Gf ∧
      ∀ (v : Lp ℂ 2 (reducedLaw Q)) (Gv : Fin d → Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v Gv →
        (s : ℂ) * (∫ ω, f ω * v ω ∂reducedLaw Q) + (1 / 2 : ℂ) *
          (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * Gf k ω * Gv j ω ∂reducedLaw Q) -
          ζ * (∫ ω, f ω * (∑ j, (ω.1 0 j i : ℂ) * Gv j ω) ∂reducedLaw Q) =
          ∫ ω, rhs ω * v ω ∂reducedLaw Q := by
  obtain ⟨u, hu⟩ := exists_complex_transpose_variational_solution Q i ζ s hs (star rhs)
  refine ⟨star (u.val none), fun j => star (u.val (some j)),
    fun j => (u.property j).star, ?_⟩
  intro v Gv hv
  let w : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q) :=
    ⟨WithLp.toLp 2 (fun o => o.elim v Gv), hv⟩
  have ht := hu w
  change (s : ℂ) * inner ℂ (u.val none) v + ((1 / 2 : ℝ) : ℂ) *
    (∑ j, ∑ k, inner ℂ (u.val (some j)) (complexCoefficientMul Q j k (Gv k))) -
    ζ * inner ℂ (u.val none) (graphDrift Q i w) = inner ℂ (star rhs) v at ht
  rw [← energy_eq_inner_sum, inner_star_eq_integral_mul] at ht
  have hm : inner ℂ (u.val none) v =
      ∫ ω, (star (u.val none) : Lp ℂ 2 (reducedLaw Q)) ω * v ω ∂reducedLaw Q := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star (u.val none)] with ω hω
    change (star (u.val none) : Lp ℂ 2 (reducedLaw Q)) ω = star (u.val none ω) at hω
    simp only [hω, RCLike.inner_apply, Complex.star_def, mul_comm]
  have hE : (∫ ω, ∑ j, ∑ k, star (u.val (some j) ω) * (ω.1 0 j k : ℂ) * Gv k ω
      ∂reducedLaw Q) = ∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) *
        (star (u.val (some k)) : Lp ℂ 2 (reducedLaw Q)) ω * Gv j ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr fun j => Lp.coeFn_star (u.val (some j)),
      Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q] with ω hstar hω
    change ∀ j, (star (u.val (some j)) : Lp ℂ 2 (reducedLaw Q)) ω =
      star (u.val (some j) ω) at hstar
    have hsA (j k : Fin d) : ω.1 0 j k = ω.1 0 k j :=
      congrArg (fun M : Mat d => M k j) (hω 0).1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hsA k j, hstar k]
    ring
  have hD : inner ℂ (u.val none) (graphDrift Q i w) =
      ∫ ω, (star (u.val none) : Lp ℂ 2 (reducedLaw Q)) ω *
        (∑ j, (ω.1 0 j i : ℂ) * Gv j ω) ∂reducedLaw Q := by
    rw [graphDrift_apply]
    change inner ℂ (u.val none) (complexForceDrift Q i (WithLp.toLp 2 Gv)) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star (u.val none),
      complexForceDrift_coe Q i (WithLp.toLp 2 Gv)] with ω hstar hD
    change (star (u.val none) : Lp ℂ 2 (reducedLaw Q)) ω = star (u.val none ω) at hstar
    change (complexForceDrift Q i (WithLp.toLp 2 Gv)) ω = _ at hD
    simp only [hstar, hD, RCLike.inner_apply, Complex.star_def, mul_comm]
  simpa only [hm, hE, hD, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    using ht

end EinsteinFull
