import EinsteinRelation.Environment.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.ConjExponents
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Instances.Matrix

/-!
# Cauchy–Schwarz bound for the Fisher pairing

Pointwise and integrated Cauchy–Schwarz estimate behind Lemma 4.2
(`entropy.divergence`, `paper/main.tex` lines 628–639). For a symmetric coefficient
matrix `A` with `Λ⁻¹|ξ|² ≤ ξ·Aξ`, the pairing `v·w` satisfies
`(v·w)² ≤ Λ (v·Av) |w|²`. Applied with `v = Dρ`, `w = F`, and integrated against the
Fisher integrand `Dρ·aDρ / ρ` and the weight `ρ|F|²`, this gives
`∫ |Dρ·F| ≤ (∫ Fisher)^{1/2} (Λ ∫ ρ|F|²)^{1/2}`.

The integrated statement holds for any measure. The gradient `Dρ` is taken to vanish
on `{ρ = 0}`, which is the convention used for the Fisher integrand.
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinRelation

/-- Exchange of arguments through a symmetric matrix: `x·(Ay) = y·(Ax)`. -/
theorem dot_mulVec_swap {d : ℕ} (A : Mat d) (hA : A.transpose = A) (x y : Vec d) :
    dot x (A.mulVec y) = dot y (A.mulVec x) := by
  have h1 : Matrix.vecMul x A = Matrix.mulVec A x := by
    rw [← Matrix.vecMul_transpose A x, hA]
  show dotProduct x (Matrix.mulVec A y) = dotProduct y (Matrix.mulVec A x)
  rw [Matrix.dotProduct_mulVec x A y, h1, dotProduct_comm (Matrix.mulVec A x) y]

/-- Expansion of the quadratic form at `s • v - u` for a symmetric matrix `A`. -/
theorem dot_quad_expand {d : ℕ} (A : Mat d) (hA : A.transpose = A) (v u : Vec d) (s : ℝ) :
    dot (s • v - u) (A.mulVec (s • v - u)) =
      s ^ 2 * dot v (A.mulVec v) - 2 * s * dot v (A.mulVec u) + dot u (A.mulVec u) := by
  have h1 : dotProduct u (A.mulVec v) = dotProduct v (A.mulVec u) :=
    dot_mulVec_swap A hA u v
  show dotProduct (s • v - u) (A.mulVec (s • v - u)) =
    s ^ 2 * dotProduct v (A.mulVec v) - 2 * s * dotProduct v (A.mulVec u) +
      dotProduct u (A.mulVec u)
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, h1]
  ring

/-- Nonnegativity of the Euclidean square. -/
theorem euclideanSq_nonneg_fisher {d : ℕ} (x : Vec d) : 0 ≤ euclideanSq x := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- A nonpositive Euclidean square forces the vector to vanish. -/
theorem eq_zero_of_euclideanSq_le {d : ℕ} {x : Vec d} (h : euclideanSq x ≤ 0) : x = 0 := by
  have hsum : ∑ i, x i * x i = 0 :=
    le_antisymm h (Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (x i)).mp hsum i
    (Finset.mem_univ i)
  exact mul_self_eq_zero.mp hi

/-- Scalar Cauchy–Schwarz for a positive quadratic form `s² P - 2 s X + Q ≥ 0`. -/
theorem sq_le_mul_of_quadratic_nonneg {P X Q : ℝ} (hP : 0 < P)
    (h : ∀ s : ℝ, 0 ≤ s ^ 2 * P - 2 * s * X + Q) : X ^ 2 ≤ P * Q := by
  obtain ⟨s, rfl⟩ : ∃ s : ℝ, X = s * P := ⟨X / P, (div_mul_cancel₀ X hP.ne').symm⟩
  have h1 := h s
  have h2 : s ^ 2 * P ≤ Q := by
    have e : 2 * s * (s * P) = 2 * (s ^ 2 * P) := by ring
    rw [e] at h1
    linarith
  calc (s * P) ^ 2 = P * (s ^ 2 * P) := by ring
    _ ≤ P * Q := mul_le_mul_of_nonneg_left h2 hP.le

/-- Cauchy–Schwarz in the `A`-inner product: for symmetric `A` with `Λ⁻¹|ξ|² ≤ ξ·Aξ`,
`(v·w)² ≤ Λ (v·Av) |w|²`. -/
theorem sq_dot_le_of_lower_bound {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) (A : Mat d)
    (hA : A.transpose = A) (hlow : ∀ ξ : Vec d, Λ⁻¹ * euclideanSq ξ ≤ dot ξ (A.mulVec ξ))
    (v w : Vec d) : dot v w ^ 2 ≤ Λ * dot v (A.mulVec v) * euclideanSq w := by
  -- The lower bound makes `A` injective, hence invertible.
  have hdet : A.det ≠ 0 := by
    intro hdet0
    obtain ⟨x, hx, hAx⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := A)).mpr hdet0
    have h0 := hlow x
    rw [hAx] at h0
    have hz : dot x 0 = 0 := by simp [dot]
    rw [hz] at h0
    have h1 : euclideanSq x ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      have := mul_pos (inv_pos.mpr hΛ) hcon
      linarith
    exact hx (eq_zero_of_euclideanSq_le h1)
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv (A := A) hunit
  have hsolve : Matrix.mulVec A (Matrix.mulVec A⁻¹ w) = w := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  obtain ⟨u, hu⟩ : ∃ u : Vec d, A.mulVec u = w := ⟨Matrix.mulVec A⁻¹ w, hsolve⟩
  -- The quadratic form along `s v - u` is nonnegative for every real `s`.
  have hq : ∀ s : ℝ, 0 ≤ s ^ 2 * dot v (A.mulVec v) - 2 * s * dot v w + dot u w := by
    intro s
    have h0 : 0 ≤ dot (s • v - u) (A.mulVec (s • v - u)) :=
      le_trans (mul_nonneg (inv_nonneg.mpr hΛ.le) (euclideanSq_nonneg_fisher (s • v - u)))
        (hlow (s • v - u))
    rw [dot_quad_expand A hA v u s, hu] at h0
    exact h0
  -- Upper bound `u·w ≤ Λ|w|²` from the lower bound at `u`.
  have hu2 : euclideanSq u ≤ Λ * dot u w := by
    have h := hlow u
    rw [hu] at h
    have h' := mul_le_mul_of_nonneg_left h hΛ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hΛ.ne', one_mul] at h'
  have hcs : dot u w ^ 2 ≤ euclideanSq u * euclideanSq w := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u w
    unfold euclideanSq dot
    simpa only [sq] using h
  have h1 : dot u w ^ 2 ≤ Λ * dot u w * euclideanSq w :=
    le_trans hcs (mul_le_mul_of_nonneg_right hu2 (euclideanSq_nonneg_fisher w))
  have hY : dot u w ≤ Λ * euclideanSq w := by
    by_cases hYpos : 0 < dot u w
    · have h2 : dot u w * dot u w ≤ dot u w * (Λ * euclideanSq w) := by
        calc dot u w * dot u w = dot u w ^ 2 := (sq _).symm
          _ ≤ Λ * dot u w * euclideanSq w := h1
          _ = dot u w * (Λ * euclideanSq w) := by ring
      exact le_of_mul_le_mul_left h2 hYpos
    · push_neg at hYpos
      exact le_trans hYpos (mul_nonneg hΛ.le (euclideanSq_nonneg_fisher w))
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    simp [dot]
  · have he : 0 < euclideanSq v :=
      lt_of_le_of_ne (euclideanSq_nonneg_fisher v)
        (fun h => hv (eq_zero_of_euclideanSq_le h.symm.le))
    have hP : 0 < dot v (A.mulVec v) :=
      lt_of_lt_of_le (mul_pos (inv_pos.mpr hΛ) he) (hlow v)
    have key : dot v w ^ 2 ≤ dot v (A.mulVec v) * dot u w :=
      sq_le_mul_of_quadratic_nonneg hP hq
    calc dot v w ^ 2 ≤ dot v (A.mulVec v) * dot u w := key
      _ ≤ dot v (A.mulVec v) * (Λ * euclideanSq w) := mul_le_mul_of_nonneg_left hY hP.le
      _ = Λ * dot v (A.mulVec v) * euclideanSq w := by ring

/-- Pointwise Fisher–Cauchy–Schwarz bound:
`|v·w| ≤ (v·Av / ρ)^{1/2} (Λ ρ |w|²)^{1/2}` for `ρ > 0`. -/
theorem abs_dot_le_sqrt_mul_sqrt {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) (A : Mat d)
    (hA : A.transpose = A) (hlow : ∀ ξ : Vec d, Λ⁻¹ * euclideanSq ξ ≤ dot ξ (A.mulVec ξ))
    {ρ : ℝ} (hρ : 0 < ρ) (v w : Vec d) :
    |dot v w| ≤ Real.sqrt (dot v (A.mulVec v) / ρ) * Real.sqrt (Λ * (ρ * euclideanSq w)) := by
  have hP : 0 ≤ dot v (A.mulVec v) :=
    le_trans (mul_nonneg (inv_nonneg.mpr hΛ.le) (euclideanSq_nonneg_fisher v)) (hlow v)
  have hsq := sq_dot_le_of_lower_bound Λ hΛ A hA hlow v w
  have hdiv : dot v (A.mulVec v) / ρ * (Λ * (ρ * euclideanSq w)) =
      Λ * dot v (A.mulVec v) * euclideanSq w := by
    rw [div_mul_eq_mul_div, div_eq_iff hρ.ne']
    ring
  calc |dot v w| = Real.sqrt (dot v w ^ 2) := (Real.sqrt_sq_eq_abs (dot v w)).symm
    _ ≤ Real.sqrt (dot v (A.mulVec v) / ρ * (Λ * (ρ * euclideanSq w))) :=
        Real.sqrt_le_sqrt (by rw [hdiv]; exact hsq)
    _ = Real.sqrt (dot v (A.mulVec v) / ρ) * Real.sqrt (Λ * (ρ * euclideanSq w)) :=
        Real.sqrt_mul (div_nonneg hP hρ.le) _

/-- `ofReal (√x ^ 2) ≤ ofReal x` for every real `x`. -/
theorem ofReal_sqrt_sq_le (x : ℝ) : ENNReal.ofReal (Real.sqrt x ^ 2) ≤ ENNReal.ofReal x := by
  rcases le_total 0 x with hx | hx
  · exact (congrArg ENNReal.ofReal (Real.sq_sqrt hx)).le
  · rw [Real.sqrt_eq_zero'.mpr hx]
    simp

/-- The square of `ofReal √φ` in the Hölder exponent `2` is dominated by `ofReal φ`. -/
theorem lintegral_rpow_sqrt_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (φ : α → ℝ) :
    ∫⁻ a, ENNReal.ofReal (Real.sqrt (φ a)) ^ (2 : ℝ) ∂μ ≤ ∫⁻ a, ENNReal.ofReal (φ a) ∂μ := by
  refine lintegral_mono fun a => ?_
  rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg (φ a)) 2]
  exact ofReal_sqrt_sq_le (φ a)

/-- `ofReal x ^ (1/2) = ofReal (√x)` for every real `x`. -/
theorem ofReal_rpow_half (x : ℝ) :
    ENNReal.ofReal x ^ (1 / (2 : ℝ)) = ENNReal.ofReal (Real.sqrt x) := by
  rcases le_total 0 x with hx | hx
  · rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.sqrt_eq_rpow]
  · rw [ENNReal.ofReal_of_nonpos hx, Real.sqrt_eq_zero'.mpr hx, ENNReal.ofReal_zero]
    exact ENNReal.zero_rpow_of_pos (by norm_num)

/-- Cauchy–Schwarz for lower integrals: if `|h| ≤ √f · √g` a.e. with
`∫ f ≤ K` and `∫ g ≤ L`, then `∫ |h| ≤ √K · √L`. -/
theorem lintegral_abs_le_sqrt_mul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (h f g : α → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hpt : ∀ᵐ a ∂μ, |h a| ≤ Real.sqrt (f a) * Real.sqrt (g a)) (K L : ℝ)
    (hK : ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≤ ENNReal.ofReal K)
    (hL : ∫⁻ a, ENNReal.ofReal (g a) ∂μ ≤ ENNReal.ofReal L) :
    ∫⁻ a, ENNReal.ofReal |h a| ∂μ ≤ ENNReal.ofReal (Real.sqrt K * Real.sqrt L) := by
  have hF : Measurable fun a => ENNReal.ofReal (Real.sqrt (f a)) :=
    ENNReal.measurable_ofReal.comp hf.sqrt
  have hG : Measurable fun a => ENNReal.ofReal (Real.sqrt (g a)) :=
    ENNReal.measurable_ofReal.comp hg.sqrt
  have hpt' : ∫⁻ a, ENNReal.ofReal |h a| ∂μ ≤
      ∫⁻ a, ENNReal.ofReal (Real.sqrt (f a)) * ENNReal.ofReal (Real.sqrt (g a)) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hpt] with a ha
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg (f a))]
    exact ENNReal.ofReal_le_ofReal ha
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hF.aemeasurable hG.aemeasurable
  have hFK : ∫⁻ a, ENNReal.ofReal (Real.sqrt (f a)) ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal K :=
    (lintegral_rpow_sqrt_le μ f).trans hK
  have hGL : ∫⁻ a, ENNReal.ofReal (Real.sqrt (g a)) ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal L :=
    (lintegral_rpow_sqrt_le μ g).trans hL
  calc ∫⁻ a, ENNReal.ofReal |h a| ∂μ
      ≤ ∫⁻ a, ENNReal.ofReal (Real.sqrt (f a)) * ENNReal.ofReal (Real.sqrt (g a)) ∂μ := hpt'
    _ ≤ (∫⁻ a, ENNReal.ofReal (Real.sqrt (f a)) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫⁻ a, ENNReal.ofReal (Real.sqrt (g a)) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hHolder
    _ ≤ (ENNReal.ofReal K) ^ (1 / (2 : ℝ)) *
          (∫⁻ a, ENNReal.ofReal (Real.sqrt (g a)) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hFK (by norm_num)) zero_le
    _ ≤ (ENNReal.ofReal K) ^ (1 / (2 : ℝ)) * (ENNReal.ofReal L) ^ (1 / (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hGL (by norm_num)) zero_le
    _ = ENNReal.ofReal (Real.sqrt K) * ENNReal.ofReal (Real.sqrt L) := by
        rw [ofReal_rpow_half K, ofReal_rpow_half L]
    _ = ENNReal.ofReal (Real.sqrt K * Real.sqrt L) :=
        (ENNReal.ofReal_mul (Real.sqrt_nonneg K)).symm

/-- Scaling by a nonnegative constant inside a lower integral of `ofReal`. -/
theorem lintegral_ofReal_const_mul_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (Λ M : ℝ) (hΛ : 0 ≤ Λ) (φ : α → ℝ) (hφ : ∫⁻ a, ENNReal.ofReal (φ a) ∂μ ≤ ENNReal.ofReal M) :
    ∫⁻ a, ENNReal.ofReal (Λ * φ a) ∂μ ≤ ENNReal.ofReal (Λ * M) := by
  calc ∫⁻ a, ENNReal.ofReal (Λ * φ a) ∂μ
      = ∫⁻ a, ENNReal.ofReal Λ * ENNReal.ofReal (φ a) ∂μ :=
        lintegral_congr fun a => ENNReal.ofReal_mul hΛ
    _ = ENNReal.ofReal Λ * ∫⁻ a, ENNReal.ofReal (φ a) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal M := mul_le_mul_of_nonneg_left hφ zero_le
    _ = ENNReal.ofReal (Λ * M) := (ENNReal.ofReal_mul hΛ).symm

/-- Measurability of `ω ↦ v ω · (A ω v ω)` for measurable coefficient and vector fields. -/
theorem measurable_dot_mulVec_apply {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (A : Ω → Mat d)
    (v : Ω → Vec d) (hA : Measurable A) (hv : Measurable v) :
    Measurable fun ω => dot (v ω) ((A ω).mulVec (v ω)) := by
  have hcont : Continuous fun M : Mat d => M := continuous_id
  have hentry : ∀ i j : Fin d, Measurable fun ω => A ω i j := fun i j =>
    (hcont.matrix_elem i j).measurable.comp hA
  have hcoord : ∀ i : Fin d, Measurable fun ω => v ω i := fun i =>
    (measurable_pi_apply i).comp hv
  show Measurable fun ω => ∑ i, v ω i * ∑ j, A ω i j * v ω j
  exact Finset.measurable_sum _ fun i _ =>
    (hcoord i).mul (Finset.measurable_sum _ fun j _ => (hentry i j).mul (hcoord j))

/-- Fisher–Cauchy–Schwarz bound (Lemma 4.2, `paper/main.tex` lines 628–639):
`∫ |Dρ·F| ≤ (∫ Fisher)^{1/2} (Λ ∫ ρ|F|²)^{1/2}`, where the Fisher integrand is
`Dρ·aDρ / ρ`, set to zero on `{ρ = 0}`, and `Dρ` vanishes on `{ρ = 0}`. -/
theorem fisher_cauchy_schwarz_lintegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) (a : Ω → Mat d) (ha : Measurable a)
    (hell : ∀ᵐ ω ∂μ, (a ω).transpose = a ω ∧
      ∀ ξ : Vec d, Λ⁻¹ * euclideanSq ξ ≤ dot ξ ((a ω).mulVec ξ) ∧
        dot ξ ((a ω).mulVec ξ) ≤ Λ * euclideanSq ξ)
    (ρ : Ω → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ᵐ ω ∂μ, 0 ≤ ρ ω)
    (Drho F : Ω → Vec d) (hDrho : Measurable Drho) (hF : Measurable F)
    (hzero : ∀ᵐ ω ∂μ, ρ ω = 0 → Drho ω = 0)
    (K M : ℝ)
    (hK : ∫⁻ ω, ENNReal.ofReal
        (if ρ ω = 0 then 0 else dot (Drho ω) ((a ω).mulVec (Drho ω)) / ρ ω) ∂μ ≤
      ENNReal.ofReal K)
    (hM : ∫⁻ ω, ENNReal.ofReal (ρ ω * euclideanSq (F ω)) ∂μ ≤ ENNReal.ofReal M) :
    ∫⁻ ω, ENNReal.ofReal |dot (Drho ω) (F ω)| ∂μ ≤
      ENNReal.ofReal (Real.sqrt K * Real.sqrt (Λ * M)) := by
  have hW : Measurable fun ω => euclideanSq (F ω) := by
    have hc : ∀ i : Fin d, Measurable fun ω => F ω i := fun i =>
      (measurable_pi_apply i).comp hF
    show Measurable fun ω => ∑ i, F ω i * F ω i
    exact Finset.measurable_sum _ fun i _ => (hc i).mul (hc i)
  have hfeq : (fun ω => if ρ ω = 0 then 0 else dot (Drho ω) ((a ω).mulVec (Drho ω)) / ρ ω) =
      fun ω => dot (Drho ω) ((a ω).mulVec (Drho ω)) / ρ ω := by
    funext ω
    by_cases h : ρ ω = 0 <;> simp [h]
  have hf : Measurable fun ω =>
      if ρ ω = 0 then 0 else dot (Drho ω) ((a ω).mulVec (Drho ω)) / ρ ω := by
    rw [hfeq]
    exact (measurable_dot_mulVec_apply a Drho ha hDrho).div hρ
  have hg : Measurable fun ω => Λ * (ρ ω * euclideanSq (F ω)) :=
    measurable_const.mul (hρ.mul hW)
  have hpt : ∀ᵐ ω ∂μ, |dot (Drho ω) (F ω)| ≤
      Real.sqrt (if ρ ω = 0 then 0 else dot (Drho ω) ((a ω).mulVec (Drho ω)) / ρ ω) *
        Real.sqrt (Λ * (ρ ω * euclideanSq (F ω))) := by
    filter_upwards [hell, hρ0, hzero] with ω hω hρω hz
    obtain ⟨hsymm, hbounds⟩ := hω
    by_cases h0 : ρ ω = 0
    · have hD : Drho ω = 0 := hz h0
      have habs : |dot (Drho ω) (F ω)| = 0 := by
        rw [hD]
        simp [dot]
      rw [habs]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · have hpos : 0 < ρ ω := lt_of_le_of_ne hρω (Ne.symm h0)
      rw [if_neg h0]
      exact abs_dot_le_sqrt_mul_sqrt Λ hΛ (a ω) hsymm (fun ξ => (hbounds ξ).1) hpos
        (Drho ω) (F ω)
  exact lintegral_abs_le_sqrt_mul μ (fun ω => dot (Drho ω) (F ω))
    (fun ω => if ρ ω = 0 then 0 else dot (Drho ω) ((a ω).mulVec (Drho ω)) / ρ ω)
    (fun ω => Λ * (ρ ω * euclideanSq (F ω))) hf hg hpt K (Λ * M) hK
    (lintegral_ofReal_const_mul_le μ Λ M hΛ.le (fun ω => ρ ω * euclideanSq (F ω)) hM)

end EinsteinRelation
