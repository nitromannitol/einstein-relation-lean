import EinsteinFull.Calculus.U5RegularPhysicalOccupation
import EinsteinFull.Calculus.C4FoundationPhysicalLawUniqueness
import EinsteinRelation.Entropy.DynkinFromFukushima
import EinsteinFull.Calculus.S1SharpBoundSupport
import Mathlib.Tactic.Linter

open EinsteinRelation MeasureTheory ProbabilityTheory Filter Topology
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal BigOperators

namespace EinsteinFull

private theorem u5_measurable_reduced_generator {d : ℕ} (ω : FieldPair d)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) :
    Measurable (reducedGenerator i ω lam f) := by
  unfold reducedGenerator divergence coordinateDerivative dot
  refine Measurable.add (measurable_const.mul ?_) (measurable_const.mul ?_)
  · exact Finset.measurable_sum _ fun k _ => measurable_fderiv_apply_const ℝ _ _
  · refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
    · simpa only [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
        ((continuous_reducedCoefficient ω).matrix_elem k i).measurable
    · exact measurable_fderiv_apply_const ℝ f (unitVector k)

private theorem u5_measurable_physical_generator {d : ℕ} (ω : FieldPair d)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) :
    Measurable (physicalGenerator i ω lam f) := by
  have he : physicalGenerator i ω lam f =
      fun x => (clockDensity ω x)⁻¹ * reducedGenerator i ω lam f x :=
    funext fun x => physicalGenerator_eq_inv_mul ω i lam f x
  rw [he]
  exact (reduce ω).2.continuous.measurable.inv.mul (u5_measurable_reduced_generator ω i lam f)


/-- Locally equal tests have equal physical generators, including at points
where a coefficient derivative is interpreted by the default Fréchet derivative. -/
theorem u5_physicalGenerator_congr_of_eventuallyEq {d : ℕ} (ω : FieldPair d)
    (i : Fin d) (lam : ℝ) {f g : Vec d → ℝ} {z : Vec d}
    (h : f =ᶠ[𝓝 z] g) : physicalGenerator i ω lam f z = physicalGenerator i ω lam g z := by
  have hgrad : gradient f =ᶠ[𝓝 z] gradient g := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with w hw
    funext j
    exact congrArg (fun D => D (unitVector j)) hw
  have hflux : (fun w => (reducedCoefficient ω w).mulVec (gradient f w)) =ᶠ[𝓝 z]
      (fun w => (reducedCoefficient ω w).mulVec (gradient g w)) := by
    filter_upwards [hgrad] with w hw
    rw [hw]
  have hdiv : divergence (fun w => (reducedCoefficient ω w).mulVec (gradient f w)) z =
      divergence (fun w => (reducedCoefficient ω w).mulVec (gradient g w)) z := by
    unfold divergence coordinateDerivative
    apply Finset.sum_congr rfl
    intro j _
    have he : (fun w => (reducedCoefficient ω w).mulVec (gradient f w) j) =ᶠ[𝓝 z]
        (fun w => (reducedCoefficient ω w).mulVec (gradient g w) j) := by
      filter_upwards [hflux] with w hw
      exact congrFun hw j
    exact congrArg (fun D => D (unitVector j)) (he.fderiv_eq (𝕜 := ℝ))
  simp only [physicalGenerator, hdiv, hgrad.eq_of_nhds]

/-- A concrete cutoff approximation obligation for the polynomial test: the
compact tests and their physical generators are uniformly bounded, and the
tests eventually agree locally with the literal kernel. -/
def U5PolynomialCutoffBounds {d : ℕ} (ω : FieldPair d) (i : Fin d) (lam r : ℝ)
    (y : Vec d) : Prop :=
  ∃ (u : ℕ → Vec d → ℝ) (C D : ℝ),
    (∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n) ∧ HasCompactSupport (u n)) ∧
    (∀ n z, ‖u n z‖ ≤ C) ∧
    (∀ n z, ‖physicalGenerator i ω lam (u n) z‖ ≤ D) ∧
    (∀ z, ∀ᶠ n in Filter.atTop, u n =ᶠ[𝓝 z]
      (fun w => c16NormalizedPolynomialKernel r (d + 1) (w - y)))

/-- The polynomial occupation equation follows from the explicit compact cutoff
bounds, for the same supplied physical law and any signed force. -/
theorem u5_polynomial_occupation_of_cutoff_bounds
    {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (r : ℝ) (y : Vec d) (T : ℝ≥0) (hcut : U5PolynomialCutoffBounds ω i lam r y) :
    let f : Vec d → ℝ := fun z => c16NormalizedPolynomialKernel r (d + 1) (z-y)
    let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
    (∫ z, physicalGenerator i ω lam f z ∂μ) =
      (∫ γ, f (γ T) ∂P) - f x := by
  let _ : IsProbabilityMeasure P := hP.1
  let μ : Measure (Vec d) := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  obtain ⟨u, C, D, hu, hval, hgen, hlocal⟩ := hcut
  have hlimval (z : Vec d) : Filter.Tendsto (fun n => u n z) Filter.atTop
      (𝓝 (c16NormalizedPolynomialKernel r (d + 1) (z - y))) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hlocal z] with n hn
    exact hn.eq_of_nhds.symm
  have hlimgen (z : Vec d) : Filter.Tendsto
      (fun n => physicalGenerator i ω lam (u n) z) Filter.atTop
      (𝓝 (physicalGenerator i ω lam
        (fun w => c16NormalizedPolynomialKernel r (d + 1) (w - y)) z)) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hlocal z] with n hn
    exact (u5_physicalGenerator_congr_of_eventuallyEq ω i lam hn).symm
  have hg : Filter.Tendsto (fun n => ∫ z, physicalGenerator i ω lam (u n) z ∂μ)
      Filter.atTop (𝓝 (∫ z, physicalGenerator i ω lam
        (fun w => c16NormalizedPolynomialKernel r (d + 1) (w - y)) z ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => D)
      (fun n => (u5_measurable_physical_generator ω i lam (u n)).aestronglyMeasurable)
      (integrable_const _) (fun n => Filter.Eventually.of_forall (hgen n)) ?_
    exact Filter.Eventually.of_forall hlimgen
  have hv : Filter.Tendsto (fun n => ∫ γ, u n (γ T) ∂P) Filter.atTop
      (𝓝 (∫ γ, c16NormalizedPolynomialKernel r (d + 1) (γ T - y) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => ((hu n).1.continuous.measurable.comp
        (measurable_pathPosition T)).aestronglyMeasurable)
      (integrable_const _) (fun n => Filter.Eventually.of_forall fun γ => hval n (γ T)) ?_
    exact Filter.Eventually.of_forall fun γ => hlimval (γ T)
  have heq (n : ℕ) : (∫ z, physicalGenerator i ω lam (u n) z ∂μ) =
      (∫ γ, u n (γ T) ∂P) - u n x :=
    u5_supplied_physical_occupation_weak_equation hΛ hω i lam hP (hu n).1 (hu n).2 T
  exact tendsto_nhds_unique hg ((hv.sub (hlimval x)).congr fun n => (heq n).symm)

-- The quadratic denominator and its derivative, used to control the
-- polynomial kernel's second derivative at a fixed positive scale.
private noncomputable def u5_sq_gradient {d : ℕ} (w : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ j, (w j • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) +
    w j • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ))

private theorem u5_hasFDerivAt_euclideanSq {d : ℕ} (w : Vec d) :
    HasFDerivAt (fun z : Vec d => euclideanSq z) (u5_sq_gradient w) w := by
  unfold euclideanSq dot u5_sq_gradient
  exact HasFDerivAt.fun_sum fun j _ =>
    (hasFDerivAt_apply (𝕜 := ℝ) j w).fun_mul (hasFDerivAt_apply (𝕜 := ℝ) j w)

private theorem u5_sq_gradient_unit {d : ℕ} (w : Vec d) (l : Fin d) :
    u5_sq_gradient w (unitVector l) = 2 * w l := by
  simp [u5_sq_gradient, unitVector, Pi.single_apply, Finset.sum_add_distrib, two_mul]

private theorem u5_coordinate_sq_le_denominator {d : ℕ} {r : ℝ}
    (w : Vec d) (j : Fin d) : (w j) ^ 2 ≤ r ^ 2 + euclideanSq w := by
  have h : (w j) ^ 2 ≤ euclideanSq w := by
    simpa only [euclideanSq, dot, pow_two] using
      Finset.single_le_sum (fun k _ => mul_self_nonneg (w k)) (Finset.mem_univ j)
  nlinarith [sq_nonneg r]

private theorem u5_coordinate_product_le_denominator {d : ℕ} {r : ℝ}
    (w : Vec d) (j k : Fin d) : |w j * w k| ≤ r ^ 2 + euclideanSq w := by
  have hj := u5_coordinate_sq_le_denominator (r := r) w j
  have hk := u5_coordinate_sq_le_denominator (r := r) w k
  have hdiff := sq_nonneg (|w j| - |w k|)
  rw [abs_mul]
  nlinarith [sq_abs (w j), sq_abs (w k)]

private theorem u5_inverse_denominator_coordinate_product_le_one
    {d : ℕ} {r : ℝ} (hr : 0 < r) (w : Vec d) (j k : Fin d) :
    |(r ^ 2 + euclideanSq w)⁻¹ * (w j * w k)| ≤ 1 := by
  have hsq : 0 ≤ euclideanSq w := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg (fun l _ => mul_self_nonneg (w l))
  have hq : 0 < r ^ 2 + euclideanSq w := by nlinarith [sq_pos_of_pos hr]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hq)]
  calc
    (r ^ 2 + euclideanSq w)⁻¹ * |w j * w k| ≤
        (r ^ 2 + euclideanSq w)⁻¹ * (r ^ 2 + euclideanSq w) :=
      mul_le_mul_of_nonneg_left (u5_coordinate_product_le_denominator w j k)
        (inv_nonneg.mpr hq.le)
    _ = 1 := inv_mul_cancel₀ hq.ne'

private theorem u5_reciprocal_kernel_coordinate_derivative {d : ℕ} {r : ℝ}
    (hr : 0 < r) (w : Vec d) (j : Fin d) :
    fderiv ℝ (c16PolynomialKernel r 1) w (unitVector j) =
      -((r ^ 2 + euclideanSq w) ^ 2)⁻¹ * (2 * w j) := by
  have hsq : 0 ≤ euclideanSq w := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg (fun k _ => mul_self_nonneg (w k))
  have hq : 0 < r ^ 2 + euclideanSq w := by nlinarith [sq_pos_of_pos hr]
  have hD := (hasDerivAt_inv hq.ne').comp_hasFDerivAt w
    ((u5_hasFDerivAt_euclideanSq w).const_add (r ^ 2))
  unfold c16PolynomialKernel
  simp only [pow_one]
  simpa only [Function.comp_def, smul_apply, smul_eq_mul, u5_sq_gradient_unit] using
    congrArg (fun D : Vec d →L[ℝ] ℝ => D (unitVector j)) hD.fderiv

private theorem u5_polynomial_kernel_coordinate_derivative {d : ℕ} {r : ℝ}
    (hr : 0 < r) (m : ℕ) (w : Vec d) (j : Fin d) :
    fderiv ℝ (c16PolynomialKernel r m) w (unitVector j) =
      (m : ℝ) * ((r ^ 2 + euclideanSq w)⁻¹) ^ (m - 1) *
        (-((r ^ 2 + euclideanSq w) ^ 2)⁻¹ * (2 * w j)) := by
  let κ : Vec d → ℝ := c16PolynomialKernel r 1
  have hκ : DifferentiableAt ℝ κ w :=
    ((c16_polynomial_kernel_contDiff hr 1).differentiable (by simp)) w
  have heq : c16PolynomialKernel (d := d) r m = fun z => κ z ^ m := by
    funext z
    simp only [κ, c16PolynomialKernel, pow_one]
  rw [heq, fderiv_fun_pow m hκ]
  simp only [nsmul_eq_mul, smul_apply, smul_eq_mul,
    u5_reciprocal_kernel_coordinate_derivative hr, κ, c16PolynomialKernel, pow_one]

private theorem u5_polynomial_kernel_succ_coordinate_derivative {d : ℕ} {r : ℝ}
    (hr : 0 < r) (n : ℕ) (w : Vec d) (j : Fin d) :
    fderiv ℝ (c16PolynomialKernel r (n + 1)) w (unitVector j) =
      -2 * ((n + 1 : ℕ) : ℝ) *
        ((r ^ 2 + euclideanSq w)⁻¹) ^ (n + 2) * w j := by
  rw [u5_polynomial_kernel_coordinate_derivative hr, Nat.add_sub_cancel, ← inv_pow]
  rw [pow_succ, pow_succ]
  ring

private theorem u5_polynomial_kernel_second_coordinate_derivative {d : ℕ} {r : ℝ}
    (hr : 0 < r) (n : ℕ) (w : Vec d) (j k : Fin d) :
    fderiv ℝ (fun z => fderiv ℝ (c16PolynomialKernel r (n + 1)) z
      (unitVector j)) w (unitVector k) =
      (-2 * ((n + 1 : ℕ) : ℝ)) *
        (((n + 2 : ℕ) : ℝ) * ((r ^ 2 + euclideanSq w)⁻¹) ^ (n + 1) *
          (-((r ^ 2 + euclideanSq w) ^ 2)⁻¹ * (2 * w k)) * w j +
          ((r ^ 2 + euclideanSq w)⁻¹) ^ (n + 2) * (unitVector k) j) := by
  have hsq : 0 ≤ euclideanSq w := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg (fun l _ => mul_self_nonneg (w l))
  have hq : 0 < r ^ 2 + euclideanSq w := by nlinarith [sq_pos_of_pos hr]
  have hi := (hasDerivAt_inv hq.ne').comp_hasFDerivAt w
    ((u5_hasFDerivAt_euclideanSq w).const_add (r ^ 2))
  have hd := ((hi.pow (n + 2)).fun_mul (hasFDerivAt_apply (𝕜 := ℝ) j w)).const_mul
    (-2 * ((n + 1 : ℕ) : ℝ))
  have heq : (fun z => fderiv ℝ (c16PolynomialKernel r (n + 1)) z (unitVector j)) =
      (fun z => (-2 * ((n + 1 : ℕ) : ℝ)) *
        (((r ^ 2 + euclideanSq z)⁻¹) ^ (n + 2) * z j)) := by
    funext z
    rw [u5_polynomial_kernel_succ_coordinate_derivative hr]
    ring
  rw [heq]
  have h := congrArg (fun D : Vec d →L[ℝ] ℝ => D (unitVector k)) hd.fderiv
  have hpred : n + 2 - 1 = n + 1 := by omega
  simp only [Function.comp_def, add_apply, smul_apply, smul_eq_mul, nsmul_eq_mul,
    u5_sq_gradient_unit, ContinuousLinearMap.proj_apply, hpred] at h
  convert h using 1 <;> ring

private theorem u5_polynomial_kernel_second_coordinate_factor {d : ℕ} {r : ℝ}
    (hr : 0 < r) (n : ℕ) (w : Vec d) (j k : Fin d) :
    fderiv ℝ (fun z => fderiv ℝ (c16PolynomialKernel r (n + 1)) z
      (unitVector j)) w (unitVector k) =
      (-2 * ((n + 1 : ℕ) : ℝ)) *
        ((r ^ 2 + euclideanSq w)⁻¹) ^ (n + 2) *
          (-2 * ((n + 2 : ℕ) : ℝ) *
            ((r ^ 2 + euclideanSq w)⁻¹ * (w j * w k)) + (unitVector k) j) := by
  rw [u5_polynomial_kernel_second_coordinate_derivative hr, ← inv_pow]
  rw [pow_succ]
  ring

private theorem u5_polynomial_kernel_second_coordinate_bounded {d : ℕ} {r : ℝ}
    (hr : 0 < r) (n : ℕ) (w : Vec d) (j k : Fin d) :
    |fderiv ℝ (fun z => fderiv ℝ (c16PolynomialKernel r (n + 1)) z
      (unitVector j)) w (unitVector k)| ≤
      (2 * ((n + 1 : ℕ) : ℝ)) * ((r ^ 2)⁻¹) ^ (n + 2) *
        (2 * ((n + 2 : ℕ) : ℝ) + 1) := by
  have hunit : |(unitVector k) j| ≤ 1 := by
    by_cases h : j = k
    · subst j
      simp [unitVector]
    · simp [unitVector, h]
  have hprod := u5_inverse_denominator_coordinate_product_le_one hr w j k
  have hpow : |((r ^ 2 + euclideanSq w)⁻¹) ^ (n + 2)| ≤
      ((r ^ 2)⁻¹) ^ (n + 2) := by
    have hp := c16_polynomial_kernel_pos (d := d) hr (n + 2) w
    have hb := c16_polynomial_kernel_le (d := d) hr (n + 2) w
    have hp' : 0 < ((r ^ 2 + euclideanSq w)⁻¹) ^ (n + 2) := by
      simpa only [c16PolynomialKernel] using hp
    simpa only [c16PolynomialKernel, abs_of_pos hp'] using hb
  have hn1 : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hn2 : 0 ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hinner : |-2 * ((n + 2 : ℕ) : ℝ) *
      ((r ^ 2 + euclideanSq w)⁻¹ * (w j * w k)) + (unitVector k) j| ≤
      2 * ((n + 2 : ℕ) : ℝ) + 1 := by
    calc
      _ ≤ |-2 * ((n + 2 : ℕ) : ℝ) *
          ((r ^ 2 + euclideanSq w)⁻¹ * (w j * w k))| + |(unitVector k) j| :=
        abs_add_le _ _
      _ ≤ 2 * ((n + 2 : ℕ) : ℝ) + 1 := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg hn2]
        nlinarith [mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 * ((n + 2 : ℕ) : ℝ) by positivity)]
  rw [u5_polynomial_kernel_second_coordinate_factor hr, abs_mul, abs_mul,
    abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hn1]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hinner
    (abs_nonneg _) (by positivity)

-- A uniform coordinate Hessian estimate controls the full second derivative.
private theorem u5_second_iterated_norm_of_coordinate_bounds {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ z j k, |fderiv ℝ (fun w => fderiv ℝ f w (unitVector j)) z
      (unitVector k)| ≤ B) (z : Vec d) :
    ‖iteratedFDeriv ℝ 2 f z‖ ≤ ∑ _dirs : Fin 2 → Fin d, B := by
  classical
  have hbasis (dirs : Fin 2 → Fin d) :
      |iteratedFDeriv ℝ 2 f z (fun i => unitVector (dirs i))| ≤ B := by
    have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
      ((contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp)) z
    have heq : (fun i : Fin 2 => unitVector (dirs i)) =
        ![unitVector (dirs 0), unitVector (dirs 1)] := by
      funext i
      fin_cases i <;> simp
    rw [heq, iteratedFDeriv_two_apply]
    have hc := hcoord z (dirs 1) (dirs 0)
    rw [fderiv_clm_apply hd (differentiableAt_const _)] at hc
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using hc
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun _ _ => hB) fun v => ?_
  rw [Real.norm_eq_abs, EinsteinFull.Calculus.S1.multilinear_expand]
  calc
    _ ≤ ∑ dirs : Fin 2 → Fin d,
        |(∏ j, v j (dirs j)) * iteratedFDeriv ℝ 2 f z (fun j => unitVector (dirs j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _dirs : Fin 2 → Fin d, (∏ j, ‖v j‖) * B := by
      apply Finset.sum_le_sum
      intro dirs _
      rw [abs_mul, Finset.abs_prod]
      exact mul_le_mul
        (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm (v j) (dirs j)))
        (hbasis dirs) (abs_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = (∑ _dirs : Fin 2 → Fin d, B) * ∏ j, ‖v j‖ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The polynomial cutoff obligation follows from a global bound on its first
two iterated derivatives. The generator bound uses the regular coefficient
estimates at every point, including default derivatives. -/
theorem u5_polynomial_cutoff_bounds_of_iterated_bounds {d : ℕ} {Λ : ℝ}
    (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω)
    (i : Fin d) (lam r : ℝ) (y : Vec d)
    (hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec d => c16NormalizedPolynomialKernel r (d + 1) (z - y)))
    (hB : ∃ B : ℝ, ∀ k ≤ 2, ∀ z : Vec d,
      ‖iteratedFDeriv ℝ k
        (fun w : Vec d => c16NormalizedPolynomialKernel r (d + 1) (w - y)) z‖ ≤ B) :
    U5PolynomialCutoffBounds ω i lam r y := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨u, hu, ⟨C, hC⟩, hlocal⟩ := c16_exists_bounded_smooth_cutoffs hf hB
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 0 (by omega) 0)
  obtain ⟨K, hK0, hK⟩ := c4_physical_generator_quantitative hΛ hω i lam
  let H : ℝ≥0 := Real.toNNReal ((d : ℝ) * C)
  refine ⟨u, C, K * (C + H), hu, ?_, ?_, hlocal⟩
  · intro n z
    simpa only [norm_iteratedFDeriv_zero] using hC n 0 (by omega) z
  · intro n z
    have hb (w : Vec d) := c16_test_coordinate_derivative_bounds (hu n).1 (hC n) w
    have hgrad : ∀ w j, |coordinateDerivative j (u n) w| ≤ C := by
      intro w j
      exact (hb w).1 j
    have hlip (j : Fin d) : LipschitzWith H
        (fun w => coordinateDerivative j (u n) w) := by
      apply lipschitzWith_of_coordinateDerivative_le
      · exact (((contDiff_two_of_top (hu n).1).fderiv_right
          (le_of_eq one_add_one_eq_two)).clm_apply contDiff_const).differentiable (by simp)
      · intro w k
        exact (hb w).2 k j
    simpa only [Real.norm_eq_abs] using hK (u n) C H hC0 hgrad hlip z




/-- The translated normalized polynomial kernel has uniformly bounded
iterated derivatives through order two. -/
theorem u5_normalized_polynomial_iterated_bounded {d : ℕ} {r : ℝ}
    (hr : 0 < r) (y : Vec d) :
    ∃ B : ℝ, ∀ k ≤ 2, ∀ z : Vec d,
      ‖iteratedFDeriv ℝ k
        (fun w : Vec d => c16NormalizedPolynomialKernel r (d + 1) (w - y)) z‖ ≤ B := by
  let A : ℝ := (2 * ((d + 1 : ℕ) : ℝ)) * ((r ^ 2)⁻¹) ^ (d + 2) *
    (2 * ((d + 2 : ℕ) : ℝ) + 1)
  let E : ℝ := ∑ _dirs : Fin 2 → Fin d, A
  let c : ℝ := (∫ z : Vec d, c16PolynomialKernel r (d + 1) z)⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : ∀ z : Vec d, ‖iteratedFDeriv ℝ 2 (c16PolynomialKernel r (d + 1)) z‖ ≤ E := by
    intro z
    exact u5_second_iterated_norm_of_coordinate_bounds
      (c16_polynomial_kernel_contDiff hr (d + 1)) hA
      (fun z j k => u5_polynomial_kernel_second_coordinate_bounded hr d z j k) z
  obtain ⟨K, D, hK, hD⟩ := c16_normalized_polynomial_kernel_bounded (d := d) hr (d + 1)
  refine ⟨(K : ℝ) + (D : ℝ) + |c| * E, ?_⟩
  intro k hk z
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun _ _ => hA
  have htrans := iteratedFDeriv_comp_sub (𝕜 := ℝ)
    (f := c16NormalizedPolynomialKernel (d := d) r (d + 1)) k y z
  rw [htrans]
  interval_cases k
  · simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      (show |c16NormalizedPolynomialKernel r (d + 1) (z - y)| ≤
        (K : ℝ) + (D : ℝ) + |c| * E from by
          have := hK (z - y); nlinarith [D.coe_nonneg, abs_nonneg c, hE0])
  · simpa only [norm_iteratedFDeriv_one] using
      (show ‖fderiv ℝ (c16NormalizedPolynomialKernel r (d + 1)) (z - y)‖ ≤
        (K : ℝ) + (D : ℝ) + |c| * E from by
          have := hD (z - y); nlinarith [K.coe_nonneg, abs_nonneg c, hE0])
  · have hs : ContDiffAt ℝ 2 (c16PolynomialKernel (d := d) r (d + 1)) (z - y) :=
      ((c16_polynomial_kernel_contDiff hr (d + 1)).of_le (by simp)).contDiffAt
    change ‖iteratedFDeriv ℝ 2 (fun w : Vec d => c • c16PolynomialKernel r (d + 1) w) (z - y)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' hs, norm_smul, Real.norm_eq_abs]
    have hh := mul_le_mul_of_nonneg_left (hE (z - y)) (abs_nonneg c)
    nlinarith [K.coe_nonneg, D.coe_nonneg]

/-- The unshifted kernel satisfies the derivative bound used by the uniform
physical-generator estimate. -/
theorem u5_normalized_polynomial_unshifted_iterated_bounded {d : ℕ} {r : ℝ}
    (hr : 0 < r) :
    ∃ B : ℝ, ∀ k ≤ 2, ∀ z : Vec d,
      ‖iteratedFDeriv ℝ k (c16NormalizedPolynomialKernel r (d + 1)) z‖ ≤ B := by
  simpa only [sub_zero] using
    (u5_normalized_polynomial_iterated_bounded (d := d) hr (0 : Vec d))

/-- The finite occupation law of the supplied physical solution satisfies the
weak equation for the translated normalized polynomial kernel. -/
theorem u5_supplied_physical_polynomial_occupation_weak_equation
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (r : ℝ) (hr : 0 < r) (y : Vec d) (T : ℝ≥0) :
    let f : Vec d → ℝ := fun z => c16NormalizedPolynomialKernel r (d + 1) (z-y)
    let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
    (∫ z, physicalGenerator i ω lam f z ∂μ) =
      (∫ γ, f (γ T) ∂P) - f x := by
  have hdm : (d : ℝ) < 2 * ((d + 1 : ℕ) : ℝ) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast
    linarith
  have hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec d => c16NormalizedPolynomialKernel r (d + 1) (z - y)) := by
    exact ((c16_normalized_polynomial_kernel_properties hr (d + 1) hdm).2.1).comp
      (contDiff_id.sub contDiff_const)
  exact u5_polynomial_occupation_of_cutoff_bounds hΛ hω i lam hP r y T
    (u5_polynomial_cutoff_bounds_of_iterated_bounds hΛ hω i lam r y hf
      (u5_normalized_polynomial_iterated_bounded hr y))


/-! Exact signature and stored proof audit for the polynomial export. -/

example {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (r : ℝ) (hr : 0 < r) (y : Vec d) (T : ℝ≥0) :
    let f : Vec d → ℝ := fun z => c16NormalizedPolynomialKernel r (d + 1) (z-y)
    let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
    (∫ z, physicalGenerator i ω lam f z ∂μ) =
      (∫ γ, f (γ T) ∂P) - f x :=
  u5_supplied_physical_polynomial_occupation_weak_equation hd hΛ hω i lam hP r hr y T

open Lean Elab Command Batteries.Tactic.Lint in
run_cmd do
  let name := `EinsteinFull.u5_supplied_physical_polynomial_occupation_weak_equation
  let decls := #[name]
  let linters ← liftCoreM (getChecks true none none)
  unless linters.size == 15 do throwError "Expected all fifteen linters"
  let results ← liftCoreM (lintCore decls linters)
  let msg ← liftCoreM <| formatLinterResults results decls false
    "in U5 polynomial occupation" true .medium linters.size
  if results.any (!·.2.isEmpty) then logError msg else logInfo msg
  liftTermElabM <| withOptions (fun opts => opts.setBool `smartUnfolding false) <|
    Meta.withTransparency .all do
      let ci ← getConstInfo name
      Meta.check ci.type
      if let some value := ci.value? (allowOpaque := true) then
        Meta.check value
        unless ← Meta.isDefEq (← Meta.inferType value) ci.type do
          throwError "Type/value mismatch in {name}"
      else
        throwError "Missing value for {name}"
  let axioms ← collectAxioms name
  for ax in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound,
        `EinsteinFull.External.bass_continuous_elliptic_well_posed].contains ax do
      throwError "Unexpected axiom {ax} in {name}"
  elabCommand (← `(command| #print axioms $(mkIdent name)))
  logInfo m!"U5 polynomial audit: stored type/value and axiom checks; {linters.size} linters"

/-! Focused audit of the public derivative bound and its unshifted application. -/

example {d : ℕ} {r : ℝ} (hr : 0 < r) (y : Vec d) :
    ∃ B : ℝ, ∀ k ≤ 2, ∀ z : Vec d,
      ‖iteratedFDeriv ℝ k
        (fun w : Vec d => c16NormalizedPolynomialKernel r (d + 1) (w - y)) z‖ ≤ B :=
  u5_normalized_polynomial_iterated_bounded hr y

example {d : ℕ} {r : ℝ} (hr : 0 < r) :
    ∃ B : ℝ, ∀ k ≤ 2, ∀ z : Vec d,
      ‖iteratedFDeriv ℝ k (c16NormalizedPolynomialKernel r (d + 1)) z‖ ≤ B :=
  u5_normalized_polynomial_unshifted_iterated_bounded hr

open Lean Elab Command Batteries.Tactic.Lint in
run_cmd do
  let decls := #[`EinsteinFull.u5_normalized_polynomial_iterated_bounded,
    `EinsteinFull.u5_normalized_polynomial_unshifted_iterated_bounded]
  let linters ← liftCoreM (getChecks true none none)
  unless linters.size == 15 do throwError "Expected all fifteen linters"
  let results ← liftCoreM (lintCore decls linters)
  let msg ← liftCoreM <| formatLinterResults results decls false
    "in U5 polynomial derivative bounds" true .medium linters.size
  if results.any (!·.2.isEmpty) then logError msg else logInfo msg
  for name in decls do
    liftTermElabM <| withOptions (fun opts => opts.setBool `smartUnfolding false) <|
      Meta.withTransparency .all do
        let ci ← getConstInfo name
        Meta.check ci.type
        if let some value := ci.value? (allowOpaque := true) then
          Meta.check value
          unless ← Meta.isDefEq (← Meta.inferType value) ci.type do
            throwError "Type/value mismatch in {name}"
        else
          throwError "Missing value for {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound,
          `EinsteinFull.External.bass_continuous_elliptic_well_posed].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    elabCommand (← `(command| #print axioms $(mkIdent name)))
  logInfo m!"U5 polynomial derivative audit: {decls.size} stored type/value and axiom checks; {linters.size} linters"


end EinsteinFull
