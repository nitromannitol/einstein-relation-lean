import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Basic.NNReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.Taylor
import MarkovProcess.Semigroup.Generator

open Filter Topology
open scoped NNReal ENNReal Interval BigOperators

namespace EinsteinFull

/-- The quadratic form at time `t` is the squared norm at half time. -/
theorem u5_symmetric_semigroup_inner_eq_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (t : ℝ≥0) (v : E) :
    inner ℝ v (T t v) = ‖T (t / 2) v‖ ^ 2 := by
  have ht : t / 2 + t / 2 = t := add_halves t
  conv_lhs => rw [← ht, hadd]
  change inner ℝ v (T (t / 2) (T (t / 2) v)) = _
  rw [hsym, real_inner_self_eq_norm_sq]

/-- Every operator in a symmetric semigroup is positive in the quadratic-form sense. -/
theorem u5_symmetric_semigroup_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (t : ℝ≥0) (v : E) : 0 ≤ inner ℝ v (T t v) := by
  rw [u5_symmetric_semigroup_inner_eq_norm_sq T hadd hsym]
  exact sq_nonneg _

/-- A symmetric contraction semigroup has quadratic forms bounded by the initial norm. -/
theorem u5_symmetric_contraction_semigroup_inner_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (hbound : ∀ t, ‖T t‖ ≤ 1) (t : ℝ≥0) (v : E) :
    inner ℝ v (T t v) ≤ ‖v‖ ^ 2 := by
  rw [u5_symmetric_semigroup_inner_eq_norm_sq T hadd hsym]
  have hn : ‖T (t / 2) v‖ ≤ ‖v‖ := calc
    ‖T (t / 2) v‖ ≤ ‖T (t / 2)‖ * ‖v‖ := (T (t / 2)).le_opNorm v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (hbound (t / 2)) (norm_nonneg v)
    _ = ‖v‖ := one_mul _
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- A contraction semigroup decreases the norm along each orbit. -/
theorem u5_contraction_semigroup_norm_add_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hbound : ∀ t, ‖T t‖ ≤ 1) (s t : ℝ≥0) (v : E) :
    ‖T (s + t) v‖ ≤ ‖T t v‖ := by
  rw [hadd]
  change ‖T s (T t v)‖ ≤ ‖T t v‖
  calc
    ‖T s (T t v)‖ ≤ ‖T s‖ * ‖T t v‖ := (T s).le_opNorm (T t v)
    _ ≤ 1 * ‖T t v‖ := mul_le_mul_of_nonneg_right (hbound s) (norm_nonneg _)
    _ = ‖T t v‖ := one_mul _

/-- Each diagonal scalar pairing decreases as the semigroup time increases. -/
theorem u5_symmetric_contraction_semigroup_inner_add_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (hbound : ∀ t, ‖T t‖ ≤ 1) (s t : ℝ≥0) (v : E) :
    inner ℝ v (T (s + t) v) ≤ inner ℝ v (T t v) := by
  rw [u5_symmetric_semigroup_inner_eq_norm_sq T hadd hsym,
    u5_symmetric_semigroup_inner_eq_norm_sq T hadd hsym, add_div]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (u5_contraction_semigroup_norm_add_le T hadd hbound (s / 2) (t / 2) v) 2

/-- Diagonal semigroup pairings have nonnegative second differences. -/
theorem u5_symmetric_semigroup_inner_second_difference_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (t s : ℝ≥0) (v : E) :
    0 ≤ inner ℝ v (T t v) - 2 * inner ℝ v (T (t + s) v) +
      inner ℝ v (T (t + (s + s)) v) := by
  let w := T (t / 2) v
  have hcross : inner ℝ v (T (t + s) v) = inner ℝ w (T s w) := by
    have ht : t + s = t / 2 + (s + t / 2) := by
      conv_lhs => rw [← add_halves t]
      ac_rfl
    rw [ht, hadd, hadd]
    change inner ℝ v (T (t / 2) (T s (T (t / 2) v))) = _
    exact hsym _ _ _
  have hlast : inner ℝ v (T (t + (s + s)) v) = ‖T s w‖ ^ 2 := by
    have ht : t + (s + s) = t / 2 + (s + (s + t / 2)) := by
      conv_lhs => rw [← add_halves t]
      ac_rfl
    rw [ht, hadd, hadd, hadd]
    change inner ℝ v (T (t / 2) (T s (T s (T (t / 2) v)))) = _
    rw [hsym, hsym, real_inner_self_eq_norm_sq]
  rw [u5_symmetric_semigroup_inner_eq_norm_sq T hadd hsym, hcross, hlast]
  exact (norm_sub_sq_real w (T s w)) ▸ sq_nonneg ‖w - T s w‖

/-- Convex sequences have first differences controlled by their total drop. -/
theorem u5_convex_sequence_first_difference_le (f : ℕ → ℝ)
    (hconv : ∀ n, 0 ≤ f n - 2 * f (n + 1) + f (n + 2)) (n : ℕ) :
    (n : ℝ) * (f n - f (n + 1)) ≤ f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hd : 0 ≤ (f n - f (n + 1)) - (f (n + 1) - f (n + 2)) := by
      linarith [hconv n]
    have hm := mul_nonneg hn hd
    simp only [Nat.cast_succ] at *
    nlinarith

/-- Operators at different semigroup times commute. -/
theorem u5_semigroup_apply_comm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (s t : ℝ≥0) (v : E) : T s (T t v) = T t (T s v) := by
  have h := congrArg (fun A : E →L[ℝ] E => A v)
    ((hadd s t).symm.trans ((congrArg T (add_comm s t)).trans (hadd t s)))
  exact h

/-- The displacement has a nonnegative quadratic form. -/
theorem u5_symmetric_semigroup_displacement_inner_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (hbound : ∀ t, ‖T t‖ ≤ 1) (t : ℝ≥0) (v : E) :
    0 ≤ inner ℝ v (v - T t v) := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  exact sub_nonneg.mpr (u5_symmetric_contraction_semigroup_inner_le T hadd hsym hbound t v)

/-- The displacement operator of a symmetric contraction semigroup is contractive. -/
theorem u5_symmetric_semigroup_displacement_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (hbound : ∀ t, ‖T t‖ ≤ 1) (t : ℝ≥0) (v : E) :
    ‖v - T t v‖ ≤ ‖v‖ := by
  have ht : t / 2 + t / 2 = t := add_halves t
  have hn : ‖T t v‖ ≤ ‖T (t / 2) v‖ := calc
    ‖T t v‖ = ‖T (t / 2 + t / 2) v‖ := by rw [ht]
    _ ≤ ‖T (t / 2) v‖ :=
      u5_contraction_semigroup_norm_add_le T hadd hbound _ _ v
  have hs : ‖T t v‖ ^ 2 ≤ inner ℝ v (T t v) := by
    rw [u5_symmetric_semigroup_inner_eq_norm_sq T hadd hsym]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have he := norm_sub_sq_real v (T t v)
  nlinarith [norm_nonneg (v - T t v), norm_nonneg v]

/-- The semigroup displacement is a contraction in operator norm. -/
theorem u5_symmetric_semigroup_displacement_opNorm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (hbound : ∀ t, ‖T t‖ ≤ 1) (t : ℝ≥0) :
    ‖ContinuousLinearMap.id ℝ E - T t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [sub_apply, ContinuousLinearMap.id_apply, one_mul] using
    u5_symmetric_semigroup_displacement_norm_le T hadd hsym hbound t v

/-- Integer time subdivision is expressed by powers of the step operator. -/
theorem u5_semigroup_nsmul_eq_pow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hzero : T 0 = ContinuousLinearMap.id ℝ E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (n : ℕ) (t : ℝ≥0) : T (n • t) = (T t) ^ n := by
  induction n with
  | zero =>
    ext v
    change T 0 v = v
    simpa only [ContinuousLinearMap.id_apply] using
      congrArg (fun A : E →L[ℝ] E => A v) hzero
  | succ n ih =>
    rw [succ_nsmul, hadd, ih, pow_succ]
    rfl

/-- A quadratic-form bound controls the norm of a symmetric real operator. -/
theorem u5_symmetric_opNorm_le_of_quadratic_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (hA : A.IsSymmetric) (C : ℝ) (hC : 0 ≤ C)
    (hquad : ∀ x, |inner ℝ (A x) x| ≤ C * ‖x‖ ^ 2) : ‖A‖ ≤ C := by
  rw [A.norm_eq_iSup_rayleighQuotient hA]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp [hx, hC]
  · have hp : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) _
    have hb := hquad x
    have hquot : |inner ℝ (A x) x| / ‖x‖ ^ 2 ≤ C :=
      (div_le_iff₀ hp).2 (by simpa [mul_comm] using hb)
    simpa [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, abs_div, abs_of_pos hp] using hquot

/-- The first diagonal difference at step `n` is bounded by the initial energy. -/
theorem u5_symmetric_semigroup_discrete_difference_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hzero : T 0 = ContinuousLinearMap.id ℝ E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (h : ℝ≥0) (v : E) (n : ℕ) :
    (n : ℝ) * (inner ℝ v (T (n • h) v) -
      inner ℝ v (T ((n + 1) • h) v)) ≤ ‖v‖ ^ 2 := by
  let f : ℕ → ℝ := fun k => inner ℝ v (T (k • h) v)
  have hconv : ∀ k, 0 ≤ f k - 2 * f (k + 1) + f (k + 2) := by
    intro k
    simpa only [f, add_nsmul, one_nsmul, two_nsmul] using
      u5_symmetric_semigroup_inner_second_difference_nonneg T hadd hsym (k • h) h v
  have hbound := u5_convex_sequence_first_difference_le f hconv n
  have hnonneg : 0 ≤ f n := u5_symmetric_semigroup_nonneg T hadd hsym (n • h) v
  have hf0 : f 0 = ‖v‖ ^ 2 := by
    simp only [f, zero_nsmul, hzero, ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq]
  rw [hf0] at hbound
  exact le_trans hbound (sub_le_self _ hnonneg)

/-- The scaled discrete-time semigroup difference has norm at most one. -/
theorem u5_symmetric_semigroup_discrete_opNorm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hzero : T 0 = ContinuousLinearMap.id ℝ E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (hbound : ∀ t, ‖T t‖ ≤ 1) (h : ℝ≥0) (n : ℕ) :
    ‖(n : ℝ) • (T (n • h) - T ((n + 1) • h))‖ ≤ 1 := by
  let A : E →L[ℝ] E := (n : ℝ) • (T (n • h) - T ((n + 1) • h))
  have hA : A.IsSymmetric := by
    intro x y
    simp [A, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, hsym]
  apply u5_symmetric_opNorm_le_of_quadratic_bound A hA 1 zero_le_one
  intro x
  have hm : inner ℝ x (T ((n + 1) • h) x) ≤ inner ℝ x (T (n • h) x) := by
    simpa only [add_nsmul, one_nsmul, add_comm] using
      u5_symmetric_contraction_semigroup_inner_add_le T hadd hsym hbound h (n • h) x
  have hb := u5_symmetric_semigroup_discrete_difference_le T hzero hadd hsym h x n
  have hnonneg : 0 ≤ (n : ℝ) * (inner ℝ x (T (n • h) x) -
      inner ℝ x (T ((n + 1) • h) x)) :=
    mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hm)
  have heq : inner ℝ (A x) x = (n : ℝ) *
      (inner ℝ x (T (n • h) x) - inner ℝ x (T ((n + 1) • h) x)) := by
    simp [A, inner_smul_left, inner_sub_left, real_inner_comm]
  rw [heq, abs_of_nonneg hnonneg, one_mul]
  exact hb

/-- Subdividing a fixed time gives uniformly bounded scaled differences. -/
theorem u5_symmetric_semigroup_subdivision_opNorm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hzero : T 0 = ContinuousLinearMap.id ℝ E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (hbound : ∀ t, ‖T t‖ ≤ 1) (t : ℝ≥0) (n : ℕ) :
    ‖((n + 1 : ℕ) : ℝ) • (T t - T (t + t / (n + 1)))‖ ≤ 1 := by
  have hn : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have ht : (n + 1) • (t / (n + 1)) = t := by
    rw [nsmul_eq_mul, mul_comm]
    simpa only [Nat.cast_add, Nat.cast_one] using div_mul_cancel₀ t hn
  have hs : ((n + 1) + 1) • (t / (n + 1)) = t + t / (n + 1) := by
    rw [add_nsmul, one_nsmul, ht]
  simpa only [ht, hs] using
    u5_symmetric_semigroup_discrete_opNorm_le T hzero hadd hsym hbound
      (t / (n + 1)) (n + 1)


/-- Scaled differences along a positive-time subdivision are uniformly bounded
    on each vector. -/
theorem u5_symmetric_semigroup_subdivision_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hzero : T 0 = ContinuousLinearMap.id ℝ E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (hbound : ∀ t, ‖T t‖ ≤ 1) (t : ℝ≥0) (n : ℕ) (x : E) :
    ‖((n + 1 : ℕ) : ℝ) • (T t x - T (t + t / (n + 1)) x)‖ ≤ ‖x‖ := by
  let A : E →L[ℝ] E := ((n + 1 : ℕ) : ℝ) • (T t - T (t + t / (n + 1)))
  have hA : ‖A‖ ≤ 1 :=
    u5_symmetric_semigroup_subdivision_opNorm_le T hzero hadd hsym hbound t n
  calc
    ‖((n + 1 : ℕ) : ℝ) • (T t x - T (t + t / (n + 1)) x)‖ = ‖A x‖ := by
      simp [A]
    _ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg x)
    _ = ‖x‖ := one_mul _


/-- Difference quotients at the subdivision times have the bound needed for
    the positive-time generator estimate. -/
theorem u5_symmetric_semigroup_subdivision_quotient_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hzero : T 0 = ContinuousLinearMap.id ℝ E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (hbound : ∀ t, ‖T t‖ ≤ 1) (t : ℝ≥0) (n : ℕ) (x : E) :
    ‖(t : ℝ)⁻¹ • (((n + 1 : ℕ) : ℝ) •
      (T (t + t / (n + 1)) x - T t x))‖ ≤ (t : ℝ)⁻¹ * ‖x‖ := by
  have h := u5_symmetric_semigroup_subdivision_norm_le T hzero hadd hsym hbound t n x
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr t.coe_nonneg)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr t.coe_nonneg)
  have he : ((n + 1 : ℕ) : ℝ) • (T (t + t / (n + 1)) x - T t x) =
      -(((n + 1 : ℕ) : ℝ) • (T t x - T (t + t / (n + 1)) x)) := by
    simp only [← smul_neg, neg_sub]
  rw [he, norm_neg]
  exact h

/-- On the generator domain, the positive-time generator has the subdivision bound. -/
theorem u5_symmetric_semigroup_generator_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (t : ℝ≥0) (ht : 0 < t) (f : S.generatorDomain) :
    ‖S t (S.generator f)‖ ≤ (t : ℝ)⁻¹ * ‖(f : E)‖ := by
  have hseq : Tendsto (fun n : ℕ => t / (n + 1 : ℝ≥0)) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_const_div_atTop_nhds_zero_nat t).comp
        (tendsto_add_atTop_nat 1)
    · exact Eventually.of_forall fun n => div_pos ht (by positivity)
  have hlim := (S.tendsto_differenceQuotient_add f t).comp hseq
  have hlim' : Tendsto (fun n : ℕ => (t : ℝ)⁻¹ • (((n + 1 : ℕ) : ℝ) •
      (S (t + t / (n + 1)) f - S t f))) atTop (𝓝 (S t (S.generator f))) := by
    convert hlim using 1
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, smul_smul]
    rw [mul_comm]
    simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_add, NNReal.coe_natCast,
      NNReal.coe_one, mul_inv_rev, inv_inv]
  exact le_of_tendsto hlim'.norm (Eventually.of_forall fun n =>
    u5_symmetric_semigroup_subdivision_quotient_norm_le S.operator S.operator_zero
      S.operator_add hsym S.opNorm_le_one t n f)

/-- Positive-time orbits of generator-domain vectors have a bounded derivative. -/
theorem u5_symmetric_semigroup_domain_orbit_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (t : ℝ) (ht : 0 < t) (f : S.generatorDomain) :
    HasDerivAt (fun r : ℝ => S r.toNNReal f) (S t.toNNReal (S.generator f)) t ∧
      ‖S t.toNNReal (S.generator f)‖ ≤ t⁻¹ * ‖(f : E)‖ := by
  refine ⟨S.hasDerivAt_operator_toNNReal f ht, ?_⟩
  simpa only [Real.coe_toNNReal t ht.le] using
    u5_symmetric_semigroup_generator_norm_le S hsym t.toNNReal
      (Real.toNNReal_pos.mpr ht) f

/-- Positive-time semigroup increments are Lipschitz uniformly in the vector. -/
theorem u5_symmetric_semigroup_positive_time_increment_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (x : E) :
    ‖S b.toNNReal x - S a.toNNReal x‖ ≤ (a⁻¹ * ‖x‖) * (b - a) := by
  refine S.dense_generatorDomain.induction (P := fun y =>
    ‖S b.toNNReal y - S a.toNNReal y‖ ≤ (a⁻¹ * ‖y‖) * (b - a)) ?_ ?_ x
  · intro y hy
    let f : S.generatorDomain := ⟨y, hy⟩
    have hd : ∀ r ∈ Set.Icc a b,
        HasDerivWithinAt (fun z : ℝ => S z.toNNReal f)
          (S r.toNNReal (S.generator f)) (Set.Icc a b) r := by
      intro r hr
      exact (S.hasDerivAt_operator_toNNReal f (ha.trans_le hr.1)).hasDerivWithinAt
    have hb : ∀ r ∈ Set.Ico a b,
        ‖S r.toNNReal (S.generator f)‖ ≤ a⁻¹ * ‖y‖ := by
      intro r hr
      have hrpos : 0 < r := ha.trans_le hr.1
      calc
        ‖S r.toNNReal (S.generator f)‖ ≤ r⁻¹ * ‖y‖ :=
          (u5_symmetric_semigroup_domain_orbit_derivative S hsym r hrpos f).2
        _ ≤ a⁻¹ * ‖y‖ := mul_le_mul_of_nonneg_right
          ((inv_le_inv₀ hrpos ha).2 hr.1) (norm_nonneg y)
    exact norm_image_sub_le_of_norm_deriv_le_segment' hd hb b ⟨hab, le_rfl⟩
  · apply isClosed_le
    · exact ((S b.toNNReal).continuous.sub (S a.toNNReal).continuous).norm
    · exact (continuous_const.mul continuous_norm).mul continuous_const

/-- Positive-time semigroup increments are Lipschitz in operator norm. -/
theorem u5_symmetric_semigroup_positive_time_opNorm_increment_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ‖S b.toNNReal - S a.toNNReal‖ ≤ a⁻¹ * (b - a) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (inv_nonneg.mpr ha.le) (sub_nonneg.mpr hab))
  intro x
  simpa only [sub_apply, mul_assoc, mul_comm, mul_left_comm] using
    u5_symmetric_semigroup_positive_time_increment_le S hsym a b ha hab x

/-- The positive-time generator extends to a bounded operator on the whole space. -/
theorem u5_symmetric_semigroup_generator_bounded_extension
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ A : E →L[ℝ] E, ‖A‖ ≤ (t : ℝ)⁻¹ ∧
      ∀ f : S.generatorDomain, A f = S t (S.generator f) := by
  let F : S.generatorDomain →ₗ[ℝ] E := (S.operator t).toLinearMap.comp S.generator
  let e : S.generatorDomain →ₗ[ℝ] E := S.generatorDomain.subtype
  have hdense : DenseRange e := by
    change Dense (Set.range (fun f : S.generatorDomain => (f : E)))
    simpa using S.dense_generatorDomain
  have hb : ∀ f, ‖F f‖ ≤ (t : ℝ)⁻¹ * ‖e f‖ := by
    intro f
    exact u5_symmetric_semigroup_generator_norm_le S hsym t ht f
  refine ⟨F.extendOfNorm e, LinearMap.opNorm_extendOfNorm_le hdense
    (inv_nonneg.mpr t.coe_nonneg) hb, ?_⟩
  intro f
  exact LinearMap.extendOfNorm_eq hdense ⟨_, hb⟩ f

/-- Every bounded extension of the positive-time generator commutes with the semigroup. -/
theorem u5_semigroup_generator_extension_commutes
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (t s : ℝ≥0) (A : E →L[ℝ] E)
    (hA : ∀ f : S.generatorDomain, A f = S t (S.generator f)) (x : E) :
    A (S s x) = S s (A x) := by
  refine S.dense_generatorDomain.induction (P := fun y => A (S s y) = S s (A y)) ?_ ?_ x
  · intro y hy
    let f : S.generatorDomain := ⟨y, hy⟩
    calc
      A (S s y) = S t (S.generator ⟨S s f, S.operator_mem_generatorDomain f s⟩) :=
        by
          change A (S s (f : E)) = _
          exact hA ⟨S s f, S.operator_mem_generatorDomain f s⟩
      _ = S t (S s (S.generator f)) := by rw [S.generator_operator]
      _ = S s (S t (S.generator f)) := S.commute_apply t s (S.generator f)
      _ = S s (A y) := by rw [hA f]
  · exact isClosed_eq (A.continuous.comp (S s).continuous)
      ((S s).continuous.comp A.continuous)

/-- Positive-time generator extensions factor along the semigroup. -/
theorem u5_semigroup_generator_extension_factor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (s t : ℝ≥0) (A B : E →L[ℝ] E)
    (hA : ∀ f : S.generatorDomain, A f = S s (S.generator f))
    (hB : ∀ f : S.generatorDomain, B f = S (s + t) (S.generator f)) (x : E) :
    B x = S t (A x) := by
  refine S.dense_generatorDomain.induction (P := fun y => B y = S t (A y)) ?_ ?_ x
  · intro y hy
    let f : S.generatorDomain := ⟨y, hy⟩
    calc
      B y = S (s + t) (S.generator f) := hB f
      _ = S s (S t (S.generator f)) := S.add_apply s t _
      _ = S t (S s (S.generator f)) := S.commute_apply s t (S.generator f)
      _ = S t (A y) := by rw [hA f]
  · exact isClosed_eq B.continuous ((S t).continuous.comp A.continuous)

/-- Integration of a contraction-semigroup orbit is a bounded linear map. -/
noncomputable def u5SemigroupOrbitIntegralCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (t : ℝ≥0) : E →L[ℝ] E := by
  let F : E →ₗ[ℝ] E :=
    { toFun := fun x => S.orbitIntegral x t
      map_add' := by
        intro x y
        simp only [S.orbitIntegral_apply, map_add]
        exact intervalIntegral.integral_add
          ((S.continuous_operator_toNNReal x).intervalIntegrable _ _)
          ((S.continuous_operator_toNNReal y).intervalIntegrable _ _)
      map_smul' := by
        intro c x
        simp only [S.orbitIntegral_apply, map_smul, intervalIntegral.integral_smul,
          RingHom.id_apply] }
  apply F.mkContinuous (t : ℝ)
  intro x
  change ‖S.orbitIntegral x t‖ ≤ (t : ℝ) * ‖x‖
  rw [S.orbitIntegral_apply]
  calc
    ‖∫ r in (0 : ℝ)..(t : ℝ), S r.toNNReal x‖ ≤ ‖x‖ * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun r _ => S.norm_apply_le _ x
    _ = (t : ℝ) * ‖x‖ := by rw [sub_zero, abs_of_nonneg t.coe_nonneg, mul_comm]

@[simp] theorem u5SemigroupOrbitIntegralCLM_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (t : ℝ≥0) (x : E) : u5SemigroupOrbitIntegralCLM S t x = S.orbitIntegral x t := rfl

/-- The positive-time generator extension satisfies the integral evolution identity. -/
theorem u5_semigroup_extension_integral_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (t s : ℝ≥0) (A : E →L[ℝ] E)
    (hA : ∀ f : S.generatorDomain, A f = S t (S.generator f)) (x : E) :
    S (t + s) x - S t x = S.orbitIntegral (A x) s := by
  refine S.dense_generatorDomain.induction (P := fun y =>
    S (t + s) y - S t y = S.orbitIntegral (A y) s) ?_ ?_ x
  · intro y hy
    let f : S.generatorDomain := ⟨y, hy⟩
    calc
      S (t + s) y - S t y = S s (S t f) - S t f := by
        rw [S.add_apply, S.commute_apply]
      _ = S.orbitIntegral (S t (S.generator f)) s := by
        simpa only [S.orbitIntegral_apply, S.generator_operator] using
          S.operator_sub_eq_integral ⟨S t f, S.operator_mem_generatorDomain f t⟩ s
      _ = S.orbitIntegral (A y) s := by rw [hA f]
  · apply isClosed_eq
    · exact (S (t + s)).continuous.sub (S t).continuous
    · simpa only [Function.comp_def, u5SemigroupOrbitIntegralCLM_apply] using
        (u5SemigroupOrbitIntegralCLM S s).continuous.comp A.continuous

/-- A bounded positive-time generator extension controls every orbit difference quotient. -/
theorem u5_semigroup_extension_differenceQuotient_tendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (t : ℝ≥0) (A : E →L[ℝ] E)
    (hA : ∀ f : S.generatorDomain, A f = S t (S.generator f)) (x : E) :
    Tendsto (fun h : ℝ≥0 => (h : ℝ)⁻¹ • (S h (S t x) - S t x))
      (𝓝[>] 0) (𝓝 (A x)) := by
  convert S.tendsto_inv_smul_orbitIntegral (A x) using 1
  funext h
  rw [← S.add_apply h t x, add_comm h t,
    u5_semigroup_extension_integral_identity S t h A hA x]

/-- Every positive-time semigroup image belongs to the generator domain. -/
theorem u5_symmetric_semigroup_positive_time_mem_generatorDomain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (t : ℝ≥0) (ht : 0 < t) (x : E) : S t x ∈ S.generatorDomain := by
  obtain ⟨A, _, hA⟩ := u5_symmetric_semigroup_generator_bounded_extension S hsym t ht
  exact S.mem_generatorDomain_of_tendsto
    (u5_semigroup_extension_differenceQuotient_tendsto S t A hA x)

/-- Every orbit of a symmetric contraction semigroup is differentiable at positive times. -/
theorem u5_symmetric_semigroup_orbit_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (t : ℝ) (ht : 0 < t) (x : E) :
    DifferentiableAt ℝ (fun r : ℝ => S r.toNNReal x) t := by
  let a : ℝ := t / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hat : a < t := by dsimp [a]; linarith
  let f : S.generatorDomain := ⟨S a.toNNReal x,
    u5_symmetric_semigroup_positive_time_mem_generatorDomain S hsym a.toNNReal
      (Real.toNNReal_pos.mpr ha) x⟩
  have hd := (S.hasDerivAt_operator_toNNReal f (show 0 < t - a by linarith)).scomp
    t ((hasDerivAt_id t).sub_const a)
  have heq : (fun r : ℝ => S r.toNNReal x) =ᶠ[𝓝 t]
      (fun r : ℝ => S (r - a).toNNReal f) := by
    filter_upwards [Ioi_mem_nhds hat] with r hr
    have hsum : (r - a).toNNReal + a.toNNReal = r.toNNReal := by
      rw [← Real.toNNReal_add (sub_nonneg.mpr hr.le) ha.le]
      congr 1
      ring
    change S r.toNNReal x = S (r - a).toNNReal (S a.toNNReal x)
    rw [← hsum, S.add_apply]
  exact (hd.congr_of_eventuallyEq heq).differentiableAt


/-- Positive-time orbit derivatives admit a uniform bound for arbitrary vectors. -/
theorem u5_symmetric_semigroup_orbit_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (t : ℝ) (ht : 0 < t) (x : E) :
    ∃ y : E, HasDerivAt (fun r : ℝ => S r.toNNReal x) y t ∧
      ‖y‖ ≤ (t / 2)⁻¹ * ‖x‖ := by
  let a : ℝ := t / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hat : a < t := by dsimp [a]; linarith
  have hsub : t - a = a := by dsimp [a]; ring
  let f : S.generatorDomain := ⟨S a.toNNReal x,
    u5_symmetric_semigroup_positive_time_mem_generatorDomain S hsym a.toNNReal
      (Real.toNNReal_pos.mpr ha) x⟩
  refine ⟨S a.toNNReal (S.generator f), ?_, ?_⟩
  · have hd := (S.hasDerivAt_operator_toNNReal f (show 0 < t - a by linarith)).scomp
      t ((hasDerivAt_id t).sub_const a)
    have heq : (fun r : ℝ => S r.toNNReal x) =ᶠ[𝓝 t]
        (fun r : ℝ => S (r - a).toNNReal f) := by
      filter_upwards [Ioi_mem_nhds hat] with r hr
      have hsum : (r - a).toNNReal + a.toNNReal = r.toNNReal := by
        rw [← Real.toNNReal_add (sub_nonneg.mpr hr.le) ha.le]
        congr 1
        ring
      change S r.toNNReal x = S (r - a).toNNReal (S a.toNNReal x)
      rw [← hsum, S.add_apply]
    simpa only [hsub, mul_one, one_smul] using hd.congr_of_eventuallyEq heq
  · calc
      ‖S a.toNNReal (S.generator f)‖ ≤ a⁻¹ * ‖(f : E)‖ :=
        (u5_symmetric_semigroup_domain_orbit_derivative S hsym a ha f).2
      _ ≤ a⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left (S.norm_apply_le _ x)
        (inv_nonneg.mpr ha.le)


/-- The bounded extension equals the generator of the positive-time image. -/
theorem u5_semigroup_generator_image_eq_extension
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (t : ℝ≥0) (A : E →L[ℝ] E)
    (hA : ∀ f : S.generatorDomain, A f = S t (S.generator f)) (x : E)
    (hx : S t x ∈ S.generatorDomain) :
    S.generator ⟨S t x, hx⟩ = A x := by
  exact S.generator_eq_of_tendsto _
    (u5_semigroup_extension_differenceQuotient_tendsto S t A hA x)

/-- A fixed positive-time extension represents every later orbit derivative. -/
theorem u5_symmetric_semigroup_orbit_derivative_after
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (a r : ℝ) (ha : 0 < a) (har : a < r)
    (A : E →L[ℝ] E)
    (hA : ∀ f : S.generatorDomain, A f = S a.toNNReal (S.generator f)) (x : E) :
    HasDerivAt (fun z : ℝ => S z.toNNReal x)
      (S (r - a).toNNReal (A x)) r := by
  let f : S.generatorDomain := ⟨S a.toNNReal x,
    u5_symmetric_semigroup_positive_time_mem_generatorDomain S hsym a.toNNReal
      (Real.toNNReal_pos.mpr ha) x⟩
  have hf : S.generator f = A x :=
    u5_semigroup_generator_image_eq_extension S a.toNNReal A hA x f.property
  have hd := (S.hasDerivAt_operator_toNNReal f (show 0 < r - a by linarith)).scomp
    r ((hasDerivAt_id r).sub_const a)
  have heq : (fun z : ℝ => S z.toNNReal x) =ᶠ[𝓝 r]
      (fun z : ℝ => S (z - a).toNNReal f) := by
    filter_upwards [Ioi_mem_nhds har] with z hz
    have hsum : (z - a).toNNReal + a.toNNReal = z.toNNReal := by
      rw [← Real.toNNReal_add (sub_nonneg.mpr hz.le) ha.le]
      congr 1
      ring
    change S z.toNNReal x = S (z - a).toNNReal (S a.toNNReal x)
    rw [← hsum, S.add_apply]
  simpa only [hf, mul_one, one_smul] using hd.congr_of_eventuallyEq heq

/-- Iterated derivatives represented by a fixed positive-time generator extension. -/
theorem u5_symmetric_semigroup_iterated_derivative_after
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (a : ℝ) (ha : 0 < a) (A : E →L[ℝ] E)
    (hA : ∀ f : S.generatorDomain, A f = S a.toNNReal (S.generator f))
    (x : E) (n : ℕ) (r : ℝ) (hr : (n : ℝ) * a < r) :
    iteratedDeriv n (fun z : ℝ => S z.toNNReal x) r =
      S (r - (n : ℝ) * a).toNNReal ((fun y => A y)^[n] x) := by
  induction n generalizing r with
  | zero => simp only [iteratedDeriv_zero, Nat.cast_zero, zero_mul, sub_zero,
      Function.iterate_zero, id_eq]
  | succ n ih =>
    have hnr : (n : ℝ) * a < r := by
      rw [Nat.cast_succ] at hr
      nlinarith
    have heq : iteratedDeriv n (fun z : ℝ => S z.toNNReal x) =ᶠ[𝓝 r]
        (fun z : ℝ => S (z - (n : ℝ) * a).toNNReal ((fun y => A y)^[n] x)) := by
      filter_upwards [Ioi_mem_nhds hnr] with z hz
      exact ih z hz
    have hshift : a < r - (n : ℝ) * a := by
      rw [Nat.cast_succ] at hr
      nlinarith
    have hd := (u5_symmetric_semigroup_orbit_derivative_after S hsym a
      (r - (n : ℝ) * a) ha hshift A hA ((fun y => A y)^[n] x)).scomp
      r ((hasDerivAt_id r).sub_const ((n : ℝ) * a))
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have harg : r - (n : ℝ) * a - a = r - (↑(n + 1) : ℝ) * a := by
      push_cast
      ring
    simpa only [harg, mul_one, one_smul, Function.iterate_succ_apply', Function.comp_def, id_eq] using hd.deriv

/-- The fixed-extension formula yields a geometric bound for each derivative. -/
theorem u5_symmetric_semigroup_iterated_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (a : ℝ) (ha : 0 < a) (A : E →L[ℝ] E)
    (hA : ∀ f : S.generatorDomain, A f = S a.toNNReal (S.generator f))
    (hbound : ‖A‖ ≤ a⁻¹) (x : E) (n : ℕ) (r : ℝ)
    (hr : (n : ℝ) * a < r) :
    ‖iteratedDeriv n (fun z : ℝ => S z.toNNReal x) r‖ ≤ (a⁻¹)^n * ‖x‖ := by
  rw [u5_symmetric_semigroup_iterated_derivative_after S hsym a ha A hA x n r hr]
  calc
    ‖S (r - (n : ℝ) * a).toNNReal ((fun y => A y)^[n] x)‖ ≤
        ‖(fun y => A y)^[n] x‖ := S.norm_apply_le _ _
    _ ≤ (a⁻¹)^n * ‖x‖ := by
      clear hr
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        calc
          ‖A ((fun y => A y)^[n] x)‖ ≤ ‖A‖ * ‖(fun y => A y)^[n] x‖ := A.le_opNorm _
          _ ≤ a⁻¹ * ((a⁻¹)^n * ‖x‖) :=
            mul_le_mul hbound ih (norm_nonneg _) (inv_nonneg.mpr ha.le)
          _ = (a⁻¹)^(n + 1) * ‖x‖ := by rw [pow_succ]; ring

/-- The subdivision cost is controlled by a factorial times an exponential. -/
theorem u5_nat_pow_self_le_factorial_exp (n : ℕ) :
    (n : ℝ)^n ≤ (n.factorial : ℝ) * Real.exp 1 ^ n := by
  have h := Real.pow_div_factorial_le_exp (n : ℝ) (show (0 : ℝ) ≤ n by positivity) n
  have hp : (0 : ℝ) < n.factorial := by positivity
  rw [div_le_iff₀ hp] at h
  have he : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    simpa only [mul_one] using Real.exp_nat_mul 1 n
  rw [he] at h
  simpa only [mul_comm] using h

/-- A uniform factorial estimate holds on every positive half-line. -/
theorem u5_symmetric_semigroup_iterated_derivative_factorial_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (t : ℝ) (ht : 0 < t) (x : E) (n : ℕ) (r : ℝ) (hr : t ≤ r) :
    ‖iteratedDeriv n (fun z : ℝ => S z.toNNReal x) r‖ ≤
      (n.factorial : ℝ) * (2 * Real.exp 1 / t)^n * ‖x‖ := by
  by_cases hn : n = 0
  · subst n
    simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul]
      using S.norm_apply_le r.toNNReal x
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    let a : ℝ := t / (2 * n)
    have ha : 0 < a := by dsimp [a]; positivity
    have ha_lt : (n : ℝ) * a < r := by
      dsimp [a]
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      field_simp [hnne]
      nlinarith
    obtain ⟨A, hA_bound, hA⟩ :=
      u5_symmetric_semigroup_generator_bounded_extension S hsym a.toNNReal
        (Real.toNNReal_pos.mpr ha)
    have hA_bound' : ‖A‖ ≤ a⁻¹ := by
      simpa only [Real.coe_toNNReal a ha.le] using hA_bound
    have hd := u5_symmetric_semigroup_iterated_derivative_bound S hsym a ha A hA
      hA_bound' x n r ha_lt
    have hinv : a⁻¹ = (2 / t) * n := by
      dsimp [a]
      field_simp [ne_of_gt ht, ne_of_gt hnpos]
    have hnum := u5_nat_pow_self_le_factorial_exp n
    have hc : 0 ≤ (2 / t)^n := by positivity
    have hnorm : 0 ≤ ‖x‖ := norm_nonneg x
    calc
      ‖iteratedDeriv n (fun z : ℝ => S z.toNNReal x) r‖ ≤
          a⁻¹ ^ n * ‖x‖ := hd
      _ = ((2 / t)^n * (n : ℝ)^n) * ‖x‖ := by rw [hinv, mul_pow]
      _ ≤ ((2 / t)^n * ((n.factorial : ℝ) * Real.exp 1 ^ n)) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hc) hnorm
      _ = (n.factorial : ℝ) * (2 * Real.exp 1 / t)^n * ‖x‖ := by
        rw [show 2 * Real.exp 1 / t = (2 / t) * Real.exp 1 by ring, mul_pow]
        ring

universe u

/-- Every iterated derivative of an orbit is differentiable at positive time. -/
theorem u5_symmetric_semigroup_iterated_derivative_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (x : E) (n : ℕ) (r : ℝ) (hr : 0 < r) :
    DifferentiableAt ℝ (iteratedDeriv n (fun z : ℝ => S z.toNNReal x)) r := by
  let a : ℝ := r / (2 * ((n : ℝ) + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have hnra : (n : ℝ) * a < r := by
    dsimp [a]
    have hp : 0 < 2 * ((n : ℝ) + 1) := by positivity
    rw [← mul_div_assoc, div_lt_iff₀ hp]
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hshift : a < r - (n : ℝ) * a := by
    dsimp [a]
    have hp : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
    have hn : (0 : ℝ) ≤ n := by positivity
    have h : (1 + (n : ℝ)) * (r / (2 * ((n : ℝ) + 1))) < r := by
      rw [← mul_div_assoc, div_lt_iff₀ hp]
      nlinarith
    nlinarith
  obtain ⟨A, _, hA⟩ := u5_symmetric_semigroup_generator_bounded_extension S hsym
    a.toNNReal (Real.toNNReal_pos.mpr ha)
  have heq : iteratedDeriv n (fun z : ℝ => S z.toNNReal x) =ᶠ[𝓝 r]
      (fun z : ℝ => S (z - (n : ℝ) * a).toNNReal ((fun y => A y)^[n] x)) := by
    filter_upwards [Ioi_mem_nhds hnra] with z hz
    exact u5_symmetric_semigroup_iterated_derivative_after S hsym a ha A hA x n z hz
  have hd := (u5_symmetric_semigroup_orbit_derivative_after S hsym a
    (r - (n : ℝ) * a) ha hshift A hA ((fun y => A y)^[n] x)).scomp
    r ((hasDerivAt_id r).sub_const ((n : ℝ) * a))
  exact (hd.congr_of_eventuallyEq heq).differentiableAt

/-- A symmetric contraction semigroup orbit is smooth for positive time. -/
theorem u5_symmetric_semigroup_orbit_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (x : E) (n : ℕ∞) :
    ContDiffOn ℝ n (fun z : ℝ => S z.toNNReal x) (Set.Ioi 0) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro m hm r hr
  have hd := u5_symmetric_semigroup_iterated_derivative_differentiableAt S hsym x m r hr
  have heq : iteratedDerivWithin m (fun z : ℝ => S z.toNNReal x) (Set.Ioi 0) =ᶠ[𝓝 r]
      iteratedDeriv m (fun z : ℝ => S z.toNNReal x) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with z hz
    exact iteratedDerivWithin_of_isOpen isOpen_Ioi hz
  exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt

/-- Scalar orbit derivatives are inner products with the vector derivatives. -/
theorem u5_symmetric_semigroup_scalar_iterated_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (x v : E) (n : ℕ) (r : ℝ) (hr : 0 < r) :
    iteratedDeriv n (fun z : ℝ => inner ℝ v (S z.toNNReal x)) r =
      inner ℝ v (iteratedDeriv n (fun z : ℝ => S z.toNNReal x) r) := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    have heq : iteratedDeriv n (fun z : ℝ => inner ℝ v (S z.toNNReal x)) =ᶠ[𝓝 r]
        (fun z : ℝ => inner ℝ v (iteratedDeriv n (fun z : ℝ => S z.toNNReal x) z)) := by
      filter_upwards [Ioi_mem_nhds hr] with z hz
      exact ih z hz
    have hd := u5_symmetric_semigroup_iterated_derivative_differentiableAt S hsym x n r hr
    rw [iteratedDeriv_succ, heq.deriv_eq, iteratedDeriv_succ]
    simpa using ((hasDerivAt_const r v).inner ℝ hd.hasDerivAt).deriv

/-- Scalar pairings are smooth on the positive half-line. -/
theorem u5_symmetric_semigroup_scalar_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (x v : E) (n : ℕ∞) :
    ContDiffOn ℝ n (fun z : ℝ => inner ℝ v (S z.toNNReal x)) (Set.Ioi 0) := by
  exact contDiffOn_const.inner ℝ (u5_symmetric_semigroup_orbit_contDiffOn S hsym x n)

/-- Scalar derivatives obey the same uniform factorial estimate. -/
theorem u5_symmetric_semigroup_scalar_derivative_factorial_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (hsym : ∀ t u v, inner ℝ u (S t v) = inner ℝ (S t u) v)
    (t : ℝ) (ht : 0 < t) (x v : E) (n : ℕ) (r : ℝ) (hr : t ≤ r) :
    ‖iteratedDeriv n (fun z : ℝ => inner ℝ v (S z.toNNReal x)) r‖ ≤
      ‖v‖ * ((n.factorial : ℝ) * (2 * Real.exp 1 / t)^n * ‖x‖) := by
  rw [u5_symmetric_semigroup_scalar_iterated_derivative S hsym x v n r (lt_of_lt_of_le ht hr)]
  exact (norm_inner_le_norm v _).trans
    (mul_le_mul_of_nonneg_left
      (u5_symmetric_semigroup_iterated_derivative_factorial_bound S hsym t ht x n r hr)
      (norm_nonneg v))

/-- Factorial derivative bounds give a lower bound on the Taylor series radius. -/
theorem u5_taylor_radius_of_factorial_bound
    (f : ℝ → ℝ) (x C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hderiv : ∀ n : ℕ, ‖iteratedDeriv n f x‖ ≤ C * (n.factorial : ℝ) * K ^ n)
    (a : ℝ≥0) (ha : K * (a : ℝ) ≤ 1) :
    (a : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℝ
      (fun n => iteratedDeriv n f x / (n.factorial : ℝ))).radius := by
  apply FormalMultilinearSeries.le_radius_of_bound _ C
  intro n
  rw [FormalMultilinearSeries.ofScalars_norm, norm_div,
    show ‖(n.factorial : ℝ)‖ = (n.factorial : ℝ) from
      Real.norm_of_nonneg (by positivity)]
  have hp : 0 < (n.factorial : ℝ) := by positivity
  have hc : ‖iteratedDeriv n f x‖ / (n.factorial : ℝ) ≤ C * K ^ n := by
    apply (div_le_iff₀ hp).2
    calc
      ‖iteratedDeriv n f x‖ ≤ C * (n.factorial : ℝ) * K ^ n := hderiv n
      _ = C * K ^ n * (n.factorial : ℝ) := by ring
  calc
    ‖iteratedDeriv n f x‖ / (n.factorial : ℝ) * (a : ℝ) ^ n ≤
        (C * K ^ n) * (a : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg a.coe_nonneg _)
    _ = C * (K * (a : ℝ)) ^ n := by rw [mul_pow]; ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (mul_nonneg hK a.coe_nonneg) ha) hC
    _ = C := mul_one C

/-- Taylor polynomials within a unique-differentiability set have the usual coefficients. -/
theorem u5_taylorWithinEval_eq_scalar_derivative_sum
    (f : ℝ → ℝ) (s : Set ℝ) (x y : ℝ) (n : ℕ)
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s)
    (hf : ∀ k : ℕ, ContDiffAt ℝ k f x) :
    taylorWithinEval f n s x y =
      ∑ k ∈ Finset.range (n + 1),
        (iteratedDeriv k f x / (k.factorial : ℝ)) * (y - x) ^ k := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_eq_iteratedDeriv hs (hf k) hx]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- A factorial estimate makes the two-sided Taylor remainder geometrically small. -/
theorem u5_taylor_remainder_geometric_bound
    (f : ℝ → ℝ) (x y C K : ℝ) (n : ℕ) (hxy : x ≠ y)
    (hf : ContDiffOn ℝ (n + 1) f (Set.uIcc x y))
    (hfx : ∀ k : ℕ, ContDiffAt ℝ k f x)
    (hderiv : ∀ z ∈ Set.uIcc x y,
      ‖iteratedDeriv (n + 1) f z‖ ≤ C * ((n + 1).factorial : ℝ) * K ^ (n + 1)) :
    ‖f y - ∑ k ∈ Finset.range (n + 1),
      (iteratedDeriv k f x / (k.factorial : ℝ)) * (y - x) ^ k‖ ≤
        C * (K * ‖y - x‖) ^ (n + 1) := by
  obtain ⟨z, hz, hzval⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hxy hf
  have hpoly := u5_taylorWithinEval_eq_scalar_derivative_sum f (Set.uIcc x y) x y n
    (uniqueDiffOn_uIcc hxy) Set.left_mem_uIcc hfx
  rw [← hpoly, hzval, norm_div, norm_mul, norm_pow,
    show ‖((n + 1).factorial : ℝ)‖ = ((n + 1).factorial : ℝ) from
      Real.norm_of_nonneg (by positivity)]
  have hp : 0 < ((n + 1).factorial : ℝ) := by positivity
  have hb := hderiv z (Set.uIoo_subset_uIcc_self hz)
  calc
    ‖iteratedDeriv (n + 1) f z‖ * ‖y - x‖ ^ (n + 1) /
        ((n + 1).factorial : ℝ) ≤
      (C * ((n + 1).factorial : ℝ) * K ^ (n + 1)) * ‖y - x‖ ^ (n + 1) /
        ((n + 1).factorial : ℝ) := by
      gcongr
    _ = C * (K * ‖y - x‖) ^ (n + 1) := by
      rw [mul_pow]
      field_simp [ne_of_gt hp]

/-- Geometrically small remainders identify the sum of a convergent scalar series. -/
theorem u5_hasSum_of_geometric_remainder
    (a : ℕ → ℝ) (b C q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsum : Summable a)
    (hrem : ∀ n : ℕ, ‖b - ∑ k ∈ Finset.range (n + 1), a k‖ ≤ C * q ^ (n + 1)) :
    HasSum a b := by
  apply (Summable.hasSum_iff_tendsto_nat hsum).2
  apply (Filter.tendsto_add_atTop_iff_nat 1).1
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (a := fun n : ℕ => C * q ^ (n + 1)) ?_ ?_
  · intro n
    simpa only [norm_sub_rev] using hrem n
  · have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
    have hp' := (Filter.tendsto_add_atTop_iff_nat 1).2 hp
    simpa using hp'

/-- Smooth functions with locally uniform factorial bounds are analytic. -/
theorem u5_analyticAt_of_factorial_bound
    (f : ℝ → ℝ) (x C K d : ℝ) (hC : 0 ≤ C) (hK : 0 < K) (hd : 0 < d)
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n f (Set.Ioo (x - d) (x + d)))
    (hderiv : ∀ n : ℕ, ∀ z ∈ Set.Ioo (x - d) (x + d),
      ‖iteratedDeriv n f z‖ ≤ C * (n.factorial : ℝ) * K ^ n) :
    AnalyticAt ℝ f x := by
  let a : ℝ≥0 := ⟨1 / (2 * K), by positivity⟩
  have ha : 0 < (a : ℝ) := by
    change 0 < 1 / (2 * K)
    positivity
  have haK : K * (a : ℝ) ≤ 1 := by
    change K * (1 / (2 * K)) ≤ 1
    field_simp [ne_of_gt hK]
    norm_num
  let p := FormalMultilinearSeries.ofScalars ℝ
    (fun n => iteratedDeriv n f x / (n.factorial : ℝ))
  have hx : x ∈ Set.Ioo (x - d) (x + d) := by constructor <;> linarith
  have hradius : (a : ℝ≥0∞) ≤ p.radius :=
    u5_taylor_radius_of_factorial_bound f x C K hC hK.le (fun n => hderiv n x hx) a haK
  have hfx : ∀ n : ℕ, ContDiffAt ℝ n f x := fun n =>
    (hsmooth n).contDiffAt (isOpen_Ioo.mem_nhds hx)
  refine ⟨p, hasFPowerSeriesAt_iff.mpr ?_⟩
  have hsmall : Set.Ioo (-min d (a : ℝ)) (min d (a : ℝ)) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by have := lt_min hd ha; linarith) (lt_min hd ha)
  filter_upwards [hsmall] with z hz
  have hzabs : ‖z‖ < min d (a : ℝ) := by rw [Real.norm_eq_abs, abs_lt]; exact hz
  have hzd : ‖z‖ < d := lt_of_lt_of_le hzabs (min_le_left _ _)
  have hza : ‖z‖ < (a : ℝ) := lt_of_lt_of_le hzabs (min_le_right _ _)
  have hzmem : z ∈ Metric.eball (0 : ℝ) p.radius := by
    apply mem_eball_zero_iff.2
    exact lt_of_lt_of_le (by exact_mod_cast hza) hradius
  have hsum : Summable (fun n : ℕ => (iteratedDeriv n f x / (n.factorial : ℝ)) * z ^ n) := by
    simpa only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using p.summable hzmem
  have hq0 : 0 ≤ K * ‖z‖ := mul_nonneg hK.le (norm_nonneg _)
  have hq1 : K * ‖z‖ < 1 := by
    have := mul_lt_mul_of_pos_left hza hK
    linarith
  have hsegment : Set.uIcc x (x + z) ⊆ Set.Ioo (x - d) (x + d) := by
    intro y hy
    rw [Set.mem_uIcc] at hy
    rcases hy with hy | hy <;> constructor <;> rw [Real.norm_eq_abs, abs_lt] at hzd <;> linarith
  have hrem : ∀ n : ℕ, ‖f (x + z) - ∑ k ∈ Finset.range (n + 1),
      (iteratedDeriv k f x / (k.factorial : ℝ)) * z ^ k‖ ≤ C * (K * ‖z‖) ^ (n + 1) := by
    intro n
    by_cases hz0 : z = 0
    · subst z
      simp [Finset.sum_range_succ']
    · have hxy : x ≠ x + z := by intro h; apply hz0; linarith
      have h := u5_taylor_remainder_geometric_bound f x (x + z) C K n hxy
        ((hsmooth (n + 1)).mono hsegment) hfx (fun y hy => hderiv (n + 1) y (hsegment hy))
      simpa using h
  have hs := u5_hasSum_of_geometric_remainder _ (f (x + z)) C (K * ‖z‖) hq0 hq1 hsum hrem
  simpa only [p, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using hs

/-- Scalar pairings of symmetric strongly continuous contraction semigroups are analytic. -/
theorem u5_symmetric_contraction_semigroup_scalar_analytic
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hzero : T 0 = ContinuousLinearMap.id ℝ E)
    (hadd : ∀ s t, T (s+t) = (T s).comp (T t))
    (hcont : ∀ f, Continuous (fun t : ℝ≥0 => T t f))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (hbound : ∀ t, ‖T t‖ ≤ 1) (g v : E) :
    AnalyticOnNhd ℝ (fun t : ℝ => inner ℝ v (T t.toNNReal g)) (Set.Ioi 0) := by
  intro x hx
  let S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E :=
    { operator := T
      operator_zero := hzero
      operator_add := hadd
      opNorm_le_one := hbound
      continuous_orbit := hcont }
  let C : ℝ := ‖v‖ * ‖g‖
  let K : ℝ := 2 * Real.exp 1 / (x / 2)
  have hxpos : 0 < x := hx
  have hx2 : 0 < x / 2 := by linarith
  have hK : 0 < K := by dsimp [K]; positivity
  apply u5_analyticAt_of_factorial_bound _ x C K (x / 2) (by dsimp [C]; positivity) hK hx2
  · intro n
    exact (u5_symmetric_semigroup_scalar_contDiffOn S hsym g v n).mono (by
      intro z hz; simp only [Set.mem_Ioo, Set.mem_Ioi] at *; linarith)
  · intro n z hz
    have hz' : x / 2 ≤ z := by simp only [Set.mem_Ioo] at hz; linarith
    have h := u5_symmetric_semigroup_scalar_derivative_factorial_bound S hsym
      (x / 2) hx2 g v n z hz'
    dsimp [C, K]
    convert h using 1
    all_goals ring

end EinsteinFull
