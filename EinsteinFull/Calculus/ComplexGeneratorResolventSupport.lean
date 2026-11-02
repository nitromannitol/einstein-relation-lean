import EinsteinFull.Calculus.ComplexGeneratorEnergySupport
import EinsteinFull.Calculus.ComplexGeneratorUniquenessSupport
import EinsteinFull.Frozen.ReducedLawProbability
import EinsteinFull.Calculus.ComplexHorizontalClosedGraphSupport
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Option

/-!
# Positive resolvents of the actual unforced stationary generator

The full strong horizontal value-gradient graph is realized as a closed real
subspace of a finite L2 product, with norm squared equal to the value norm
squared plus the Euclidean sum of the coordinate gradient norms squared.
Bounded multiplication by the actual anisotropic coefficient entries gives
its continuous energy form. Ellipticity makes every positive real shift
coercive. Real Lax–Milgram, tested also on imaginary multiples, gives the full
complex weak identity and hence a solution of the frozen generator graph.
No semigroup, resolvent or regularity premise is assumed.
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

private def coefficientMul {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (j k : Fin d) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (reducedLaw Q) ∞ 2 2
    ((memLp_reduced_coefficient_complex Q j k).toLp (fun ω => (ω.1 0 j k : ℂ)))

private theorem coefficientMul_coe {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (j k : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    coefficientMul Q j k f =ᵐ[reducedLaw Q] fun ω => (ω.1 0 j k : ℂ) * f ω := by
  have hc := (memLp_reduced_coefficient_complex Q j k).coeFn_toLp
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((memLp_reduced_coefficient_complex Q j k).toLp (fun ω => (ω.1 0 j k : ℂ))) f
  filter_upwards [hc, hm] with ω ha hb
  simpa only [coefficientMul, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', ha] using hb

private theorem energy_eq_inner_sum {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, ∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * H k ω ∂reducedLaw Q) =
      ∑ j, ∑ k, inner ℂ (G j) (coefficientMul Q j k (H k)) := by
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
  filter_upwards [coefficientMul_coe Q j k (H k)] with ω hω
  simp only [hω, RCLike.inner_apply, Complex.star_def]
  ring

private def graphEval {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (o : Option (Fin d)) : horizontalGraph Q hQ →L[ℝ] Lp ℂ 2 Q :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin d) => Lp ℂ 2 Q) o).comp
    (horizontalGraph Q hQ).subtypeL

private def resolventForm {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) :
    horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q) →L[ℝ]
      horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q) →L[ℝ] ℝ :=
  let E := graphEval (reducedLaw Q) (reducedLaw_stationary Q)
  let I : Lp ℂ 2 (reducedLaw Q) →L[ℝ] Lp ℂ 2 (reducedLaw Q) →L[ℝ] ℝ := innerSL ℝ
  s • I.bilinearComp (E none) (E none) + (1 / 2 : ℝ) •
    ∑ j : Fin d, ∑ k : Fin d,
      (I.bilinearComp (E (some j))
        (((coefficientMul Q j k).restrictScalars ℝ).comp (E (some k)))).flip

private theorem resolventForm_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ)
    (u v : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) :
    resolventForm Q s u v = s * (inner ℂ (u.val none) (v.val none)).re + (1 / 2 : ℝ) *
      (∫ ω, ∑ j, ∑ k, star (v.val (some j) ω) * (ω.1 0 j k : ℂ) *
        u.val (some k) ω ∂reducedLaw Q).re := by
  simp only [resolventForm, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', graphEval, PiLp.proj_apply,
    Submodule.subtypeL_apply, smul_eq_mul]
  change s * inner ℝ (u.val none) (v.val none) + (1 / 2 : ℝ) *
    (∑ j, ∑ k, inner ℝ (v.val (some j)) (coefficientMul Q j k (u.val (some k)))) = _
  simp only [realL2Inner_eq_re]
  rw [energy_eq_inner_sum]
  simp only [Complex.re_sum]

private theorem resolventForm_coercive {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) (hs : 0 < s) : IsCoercive (resolventForm Q s) := by
  let K := Real.exp (2 * Λ₀) * Λ₀
  have hK : 0 < K := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  refine ⟨min s (K⁻¹ / 2), lt_min hs (div_pos (inv_pos.mpr hK) (by norm_num)), ?_⟩
  intro u
  have hb := reduced_complex_energy_lowerBound Q (fun j => u.val (some j))
  have hn : 0 ≤ ∑ j : Fin d, ‖u.val (some j)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hself : (inner ℂ (u.val none) (u.val none)).re = ‖u.val none‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (u.val none)).symm
  rw [resolventForm_apply, hself]
  calc
    min s (K⁻¹ / 2) * ‖u‖ * ‖u‖ = min s (K⁻¹ / 2) *
        (‖u.val none‖ ^ 2 + ∑ j : Fin d, ‖u.val (some j)‖ ^ 2) := by
      rw [← horizontalGraph_norm_sq]
      ring
    _ ≤ s * ‖u.val none‖ ^ 2 + (K⁻¹ / 2) *
        (∑ j : Fin d, ‖u.val (some j)‖ ^ 2) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (min_le_right _ _) hn)
    _ ≤ _ := by linarith only [hb]

private theorem exists_real_variational_solution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) (hs : 0 < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃ u : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q),
      ∀ v, resolventForm Q s u v = inner ℝ rhs (graphEval (reducedLaw Q)
        (reducedLaw_stationary Q) none v) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  letI : CompleteSpace (horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) :=
    (horizontalGraph_closed (reducedLaw Q) (reducedLaw_stationary Q)).completeSpace_coe
  let S := graphEval (reducedLaw Q) (reducedLaw_stationary Q) none
  let hB := resolventForm_coercive Q s hs
  let u := hB.continuousLinearEquivOfBilin.symm (S.adjoint rhs)
  refine ⟨u, fun v => ?_⟩
  have hb := hB.continuousLinearEquivOfBilin_apply u v
  rw [hB.continuousLinearEquivOfBilin.apply_symm_apply] at hb
  exact hb.symm.trans (S.adjoint_inner_left v rhs)

private def graphComplexSmul {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (c : ℂ) (v : horizontalGraph Q hQ) : horizontalGraph Q hQ :=
  ⟨c • v.val, fun j => (v.property j).smul c⟩

private def resolventExpression {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ)
    (u v : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) : ℂ :=
  (s : ℂ) * inner ℂ (v.val none) (u.val none) + ((1 / 2 : ℝ) : ℂ) *
    ∑ j, ∑ k, inner ℂ (v.val (some j)) (coefficientMul Q j k (u.val (some k)))

private theorem resolventForm_eq_re_expression {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ)
    (u v : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) :
    resolventForm Q s u v = (resolventExpression Q s u v).re := by
  rw [resolventForm_apply, energy_eq_inner_sum]
  simp only [resolventExpression, Complex.add_re, Complex.re_ofReal_mul]
  rw [show (inner ℂ (u.val none) (v.val none)).re =
    (inner ℂ (v.val none) (u.val none)).re from inner_re_symm (𝕜 := ℂ) _ _]

private theorem resolventExpression_I {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ)
    (u v : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) :
    resolventExpression Q s u
      (graphComplexSmul (reducedLaw Q) (reducedLaw_stationary Q) Complex.I v) =
      -Complex.I * resolventExpression Q s u v := by
  simp only [resolventExpression, graphComplexSmul, PiLp.smul_apply, inner_smul_left,
    Complex.conj_I, ← Finset.mul_sum]
  ring

private theorem exists_complex_variational_solution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) (hs : 0 < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃ u : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q),
      ∀ v, resolventExpression Q s u v = inner ℂ (v.val none) rhs := by
  obtain ⟨u, hu⟩ := exists_real_variational_solution Q s hs rhs
  refine ⟨u, fun v => Complex.ext ?_ ?_⟩
  · have h := hu v
    rw [resolventForm_eq_re_expression, realL2Inner_eq_re] at h
    exact h.trans (inner_re_symm (𝕜 := ℂ) _ _)
  · have h := hu (graphComplexSmul (reducedLaw Q) (reducedLaw_stationary Q) Complex.I v)
    rw [resolventForm_eq_re_expression, resolventExpression_I, realL2Inner_eq_re] at h
    change (-Complex.I * resolventExpression Q s u v).re =
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

/-- Every positive real shift of the full unforced stationary generator is onto L2. -/
private theorem exists_unforced_resolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃ f : Lp ℂ 2 (reducedLaw Q), IsComplexGeneratorPair Q i 0 f ((s : ℂ) • f - rhs) := by
  obtain ⟨u, hu⟩ := exists_complex_variational_solution Q s hs rhs
  refine ⟨u.val none, fun j => u.val (some j), u.property, ?_⟩
  intro v Gv hv
  let w : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q) :=
    ⟨WithLp.toLp 2 (fun o => o.elim (star v) (fun j => star (Gv j))),
      fun j => (hv j).star⟩
  have ht := hu w
  change (s : ℂ) * inner ℂ (star v) (u.val none) + ((1 / 2 : ℝ) : ℂ) *
    (∑ j, ∑ k, inner ℂ (star (Gv j)) (coefficientMul Q j k (u.val (some k)))) =
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

/-- Every positive real shift has an actual full-domain unforced generator solution
with the L2 resolvent bound. -/
theorem exists_unforced_complexGenerator_resolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃ f : Lp ℂ 2 (reducedLaw Q),
      IsComplexGeneratorPair Q i 0 f ((s : ℂ) • f - rhs) ∧ s * ‖f‖ ≤ ‖rhs‖ := by
  obtain ⟨f, hf⟩ := exists_unforced_resolvent Q i s hs rhs
  refine ⟨f, hf, ?_⟩
  have hb := hf.unforced_resolvent_bound s
  have he : (s : ℂ) • f - ((s : ℂ) • f - rhs) = rhs := sub_sub_cancel _ _
  simpa only [he] using hb

private theorem resolventExpression_eq_of_generatorPair {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ)
    (rhs : Lp ℂ 2 (reducedLaw Q))
    (u : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q))
    (hu : IsComplexGeneratorPair Q i 0 (u.val none) ((s : ℂ) • u.val none - rhs))
    (v : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) :
    resolventExpression Q s u v = inner ℂ (v.val none) rhs := by
  obtain ⟨G, hG, hw⟩ := hu
  have hgrad : G = fun j => u.val (some j) := hG.unique u.property
  subst G
  have hv : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (star (v.val none)) (fun j => star (v.val (some j))) :=
    fun j => (v.property j).star
  have ht := hw (star (v.val none)) (fun j => star (v.val (some j))) hv
  have hm (g : Lp ℂ 2 (reducedLaw Q)) :
      (∫ ω, g ω * (star (v.val none) : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) =
        inner ℂ (v.val none) g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star (v.val none)] with ω hω
    change (star (v.val none) : Lp ℂ 2 (reducedLaw Q)) ω = star (v.val none ω) at hω
    simp only [hω, RCLike.inner_apply, Complex.star_def]
  have hE : (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * u.val (some k) ω *
      (star (v.val (some j)) : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) =
      ∫ ω, ∑ j, ∑ k, star (v.val (some j) ω) * (ω.1 0 j k : ℂ) *
        u.val (some k) ω ∂reducedLaw Q := by
    apply integral_congr_ae
    have ha : ∀ᵐ ω ∂reducedLaw Q, ∀ j,
        (star (v.val (some j)) : Lp ℂ 2 (reducedLaw Q)) ω = star (v.val (some j) ω) :=
      ae_all_iff.mpr fun j => Lp.coeFn_star (v.val (some j))
    filter_upwards [ha] with ω hω
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hω j]
    ring
  rw [hm, inner_sub_right, inner_smul_right, hE] at ht
  simp only [zero_mul, add_zero] at ht
  unfold resolventExpression
  rw [← energy_eq_inner_sum]
  have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf]
  linear_combination ht

/-- The positive real unforced resolvent solution is unique on the full generator graph. -/
theorem IsComplexGeneratorPair.unforced_resolvent_unique {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {s : ℝ} (hs : 0 < s)
    {rhs f h : Lp ℂ 2 (reducedLaw Q)}
    (hf : IsComplexGeneratorPair Q i 0 f ((s : ℂ) • f - rhs))
    (hh : IsComplexGeneratorPair Q i 0 h ((s : ℂ) • h - rhs)) : f = h := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  letI : CompleteSpace (horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q)) :=
    (horizontalGraph_closed (reducedLaw Q) (reducedLaw_stationary Q)).completeSpace_coe
  have hfc := hf
  have hhc := hh
  obtain ⟨G, hG, _⟩ := hfc
  obtain ⟨H, hH, _⟩ := hhc
  let u : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q) :=
    ⟨WithLp.toLp 2 (fun o => o.elim f G), hG⟩
  let w : horizontalGraph (reducedLaw Q) (reducedLaw_stationary Q) :=
    ⟨WithLp.toLp 2 (fun o => o.elim h H), hH⟩
  let hB := resolventForm_coercive Q s hs
  have he : hB.continuousLinearEquivOfBilin u = hB.continuousLinearEquivOfBilin w := by
    apply ext_inner_right ℝ
    intro v
    rw [hB.continuousLinearEquivOfBilin_apply, hB.continuousLinearEquivOfBilin_apply,
      resolventForm_eq_re_expression, resolventForm_eq_re_expression,
      resolventExpression_eq_of_generatorPair Q i s rhs u hf,
      resolventExpression_eq_of_generatorPair Q i s rhs w hh]
  exact congrArg (fun v => v.val none) (hB.continuousLinearEquivOfBilin.injective he)

end EinsteinFull
