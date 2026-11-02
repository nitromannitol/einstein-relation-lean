import EinsteinRelation.Mobility.VelocityRateFromSteps
import EinsteinRelation.Mobility.DriftWeakDivergence
import EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinRelation.Environment.EuclideanLipschitz
import EinsteinRelation.Carriers.DensityAnnealedTwins
import EinsteinRelation.Probability.ReductionLocality
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod

/-! # Pointwise drift bounds under the reduced reference law

Source: `paper/main.tex` 1124 and 1144-1146. For a coefficient pair `w`, the column divergence
`cdiv i w = ∑ⱼ ∂ⱼ (w.1 · )_{ji}(0)` is the classical divergence of the `i`-th column at the origin.
For the reduced reference law `reducedReferenceLaw Q` this file proves:

* `reduced_entry_bound_ae`: the entry `(w.1 0)_{p i}` is bounded by `sourceReducedBound Λ₀`;
* `measurable_cdiv`: the column divergence is Borel measurable;
* `ae_differentiableAt_zero_reducedLaw`: the coefficient is differentiable at the origin, almost
  surely;
* `ae_abs_cdiv_le_reduced`: `|cdiv i w| ≤ d · reducedLipschitzConstant Λ₀`, almost surely.

Entries of a continuous matrix-valued field are read through `Continuous.matrix_elem`, and
differentiability of a matrix-valued map through `differentiableAt_pi`.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace EinsteinRelation

open Carriers

/-! ### Euclidean and matrix algebra -/

/-- Each coordinate unit vector has Euclidean norm one. -/
theorem euclideanNorm_unitVector_eq_one {d : ℕ} (j : Fin d) :
    euclideanNorm (unitVector j) = 1 := by
  change Real.sqrt (dotProduct (Pi.single j (1 : ℝ)) (Pi.single j 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

/-- The squared Euclidean norm is nonnegative. -/
theorem euclideanSq_nonneg_coords {d : ℕ} (x : Vec d) : 0 ≤ euclideanSq x := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- Polarization of the quadratic form of a matrix on `u + v` and `u - v`. -/
theorem polarization_mulVec {d : ℕ} (M : Mat d) (u v : Vec d) :
    dotProduct (u + v) (M.mulVec (u + v)) - dotProduct (u - v) (M.mulVec (u - v)) =
      2 * (dotProduct u (M.mulVec v) + dotProduct v (M.mulVec u)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub]
  ring

/-- The `p`-th coordinate of `M` applied to the `q`-th unit vector is the entry `M p q`. -/
theorem mulVec_single_apply_entry {d : ℕ} (M : Mat d) (q p : Fin d) :
    (M.mulVec (Pi.single q (1 : ℝ))) p = M p q := by
  change dotProduct (fun k => M p k) (Pi.single q (1 : ℝ)) = M p q
  rw [dotProduct_single, mul_one]

/-- A symmetric matrix whose quadratic form lies in `[0, Λ |ξ|²]` has all entries bounded by `Λ`.
The bound comes from the polarization identity on `e_p + e_q` and `e_p - e_q`. -/
theorem abs_entry_le_of_quadratic_bounds {d : ℕ} {Λ : ℝ} (hΛ : 0 ≤ Λ) (M : Mat d)
    (hsymm : M.transpose = M) (hlow : ∀ ξ : Vec d, 0 ≤ dotProduct ξ (M.mulVec ξ))
    (hup : ∀ ξ : Vec d, dotProduct ξ (M.mulVec ξ) ≤ Λ * euclideanSq ξ) (p q : Fin d) :
    |M p q| ≤ Λ := by
  have hMsym : M q p = M p q := by
    have h := congrFun (congrFun hsymm p) q
    rwa [Matrix.transpose_apply] at h
  have h1 : dotProduct (Pi.single p (1 : ℝ) : Vec d) (M.mulVec (Pi.single q (1 : ℝ))) = M p q := by
    rw [single_dotProduct, one_mul, mulVec_single_apply_entry]
  have h2 : dotProduct (Pi.single q (1 : ℝ) : Vec d) (M.mulVec (Pi.single p (1 : ℝ))) = M p q := by
    rw [single_dotProduct, one_mul, mulVec_single_apply_entry, hMsym]
  have hpol := polarization_mulVec M (Pi.single p (1 : ℝ)) (Pi.single q (1 : ℝ))
  rw [h1, h2] at hpol
  have hnp : euclideanNorm (Pi.single p (1 : ℝ) : Vec d) = 1 := euclideanNorm_unitVector_eq_one p
  have hnq : euclideanNorm (Pi.single q (1 : ℝ) : Vec d) = 1 := euclideanNorm_unitVector_eq_one q
  have hsq_le : ∀ ξ : Vec d, euclideanNorm ξ ≤ 2 → euclideanSq ξ ≤ 4 := by
    intro ξ hξ
    have hn0 : 0 ≤ euclideanNorm ξ := Real.sqrt_nonneg _
    have hsq : euclideanSq ξ = euclideanNorm ξ ^ 2 := by
      unfold euclideanNorm
      rw [Real.sq_sqrt (euclideanSq_nonneg_coords ξ)]
    rw [hsq]
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hξ)]
  have hplus : euclideanNorm (Pi.single p (1 : ℝ) + Pi.single q (1 : ℝ) : Vec d) ≤ 2 := by
    have h := TimeChange.euclideanNorm_add_le (Pi.single p (1 : ℝ) : Vec d) (Pi.single q (1 : ℝ))
    linarith
  have hminus : euclideanNorm (Pi.single p (1 : ℝ) - Pi.single q (1 : ℝ) : Vec d) ≤ 2 := by
    have hsub : (Pi.single p (1 : ℝ) - Pi.single q (1 : ℝ) : Vec d) =
        (Pi.single p (1 : ℝ) : Vec d) + (-1 : ℝ) • (Pi.single q (1 : ℝ) : Vec d) := by
      rw [neg_one_smul, sub_eq_add_neg]
    have h := TimeChange.euclideanNorm_add_le (Pi.single p (1 : ℝ) : Vec d)
      ((-1 : ℝ) • (Pi.single q (1 : ℝ) : Vec d))
    rw [TimeChange.euclideanNorm_smul, abs_neg, abs_one, one_mul] at h
    rw [hsub]
    linarith
  have hEplus := mul_le_mul_of_nonneg_left (hsq_le _ hplus) hΛ
  have hEminus := mul_le_mul_of_nonneg_left (hsq_le _ hminus) hΛ
  have hupPlus := hup ((Pi.single p (1 : ℝ) : Vec d) + (Pi.single q (1 : ℝ) : Vec d))
  have hupMinus := hup ((Pi.single p (1 : ℝ) : Vec d) - (Pi.single q (1 : ℝ) : Vec d))
  have hlowPlus := hlow ((Pi.single p (1 : ℝ) : Vec d) + (Pi.single q (1 : ℝ) : Vec d))
  have hlowMinus := hlow ((Pi.single p (1 : ℝ) : Vec d) - (Pi.single q (1 : ℝ) : Vec d))
  rw [abs_le]
  constructor <;> linarith

/-- The entries of a matrix are differentiable exactly when the matrix is. -/
theorem differentiableAt_matrix_iff {d : ℕ} (M : Vec d → Mat d) (x : Vec d) :
    DifferentiableAt ℝ M x ↔ ∀ i j : Fin d, DifferentiableAt ℝ (fun y => M y i j) x := by
  constructor
  · intro h i j
    exact differentiableAt_pi.mp (differentiableAt_pi.mp h i) j
  · intro h
    change DifferentiableAt ℝ (fun y i j => M y i j) x
    exact differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j => h i j

/-- Differentiability at `0` of the translate `y ↦ f (x + y)` of a real function is
differentiability of `f` at `x`. -/
theorem differentiableAt_zero_translate_real_iff {d : ℕ} (f : Vec d → ℝ) (x : Vec d) :
    DifferentiableAt ℝ (fun y => f (x + y)) 0 ↔ DifferentiableAt ℝ f x := by
  have h := differentiableAt_comp_add_left (𝕜 := ℝ) (f := f) (x := (0 : Vec d)) x
  rw [add_zero] at h
  exact h

/-- Differentiability at `x` of `g` is differentiability at `0` of its translate `y ↦ g (x + y)`.
The proof goes entrywise, because `differentiableAt_comp_add_left` needs a normed codomain and
`Mat d` carries no normed structure in this development. -/
theorem differentiableAt_zero_translate_iff {d : ℕ} (g : Vec d → Mat d) (x : Vec d) :
    DifferentiableAt ℝ (fun y => g (x + y)) 0 ↔ DifferentiableAt ℝ g x := by
  rw [differentiableAt_matrix_iff (fun y => g (x + y)) 0, differentiableAt_matrix_iff g x]
  constructor
  · intro h i j
    exact (differentiableAt_zero_translate_real_iff (fun y => g y i j) x).mp (h i j)
  · intro h i j
    exact (differentiableAt_zero_translate_real_iff (fun y => g y i j) x).mpr (h i j)

/-! ### Measurability of differentiability sets -/

/-- For a jointly continuous matrix field `M`, the set of pairs `(a, y)` at which `M a` is not
differentiable at `y` is measurable. -/
theorem measurableSet_not_differentiableAt_matrix {d : ℕ} {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] {M : α → Vec d → Mat d}
    (hM : Continuous fun p : α × Vec d => M p.1 p.2) :
    MeasurableSet {p : α × Vec d | ¬DifferentiableAt ℝ (fun y => M p.1 y) p.2} := by
  have hset : {p : α × Vec d | ¬DifferentiableAt ℝ (fun y => M p.1 y) p.2} =
      ⋃ i : Fin d, ⋃ j : Fin d,
        {p : α × Vec d | ¬DifferentiableAt ℝ (fun y => M p.1 y i j) p.2} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, differentiableAt_matrix_iff, not_forall]
  rw [hset]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => ?_
  have hc : Continuous fun p : α × Vec d => M p.1 p.2 i j := hM.matrix_elem i j
  exact (measurableSet_of_differentiableAt_with_param ℝ
    (f := fun (a : α) (y : Vec d) => M a y i j) hc).compl

/-- Joint continuity of `(w, x) ↦ w.1 x`. -/
theorem continuous_coeff_eval {d : ℕ} :
    Continuous fun p : FieldPair d × Vec d => p.1.1 p.2 :=
  continuous_eval.comp ((continuous_fst.fst).prodMk continuous_snd)

/-- Joint continuity of `(ω, x) ↦ (reduce ω).1 x`. -/
theorem continuous_reduced_coeff_eval {d : ℕ} :
    Continuous fun p : FieldPair d × Vec d => (reduce p.1).1 p.2 :=
  continuous_eval.comp
    ((((Probability.continuous_reduce (d := d)).comp continuous_fst).fst).prodMk continuous_snd)

/-- Sublevel sets `{a | |f a| ≤ K}` of a measurable real function are measurable. The absolute
value bound is split into the two inequalities `-K ≤ f a` and `f a ≤ K`. -/
theorem measurableSet_abs_le {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f)
    (K : ℝ) : MeasurableSet {a | |f a| ≤ K} := by
  have hset : {a | |f a| ≤ K} = {a | -K ≤ f a} ∩ {a | f a ≤ K} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_le]
  have hlo : MeasurableSet {a | -K ≤ f a} := measurableSet_le measurable_const hf
  have hhi : MeasurableSet {a | f a ≤ K} := measurableSet_le hf measurable_const
  rw [hset]
  exact hlo.inter hhi

/-! ### Entry bound -/

/-- The entry `(w.1 0)_{p i}` of a reduced coefficient is bounded by the source constant
`sourceReducedBound Λ₀`, for almost every reduced coefficient. -/
theorem reduced_entry_bound_ae {d : ℕ} {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) :
    ∀ᵐ w ∂reducedReferenceLaw Q, |(w.1 0) (firstIdx hd) i| ≤ sourceReducedBound Λ₀ := by
  have hK0 : 0 ≤ sourceReducedBound Λ₀ := by
    unfold sourceReducedBound
    exact mul_nonneg (Real.exp_pos _).le
      (by nlinarith [sq_nonneg Λ₀, Q.ellipticity_parameter])
  have hQ : ∀ᵐ ω ∂Q.measure, |(reduce ω).1 0 (firstIdx hd) i| ≤ sourceReducedBound Λ₀ := by
    filter_upwards [Q.regular] with ω hω
    obtain ⟨hsymm, hbd⟩ := (sourceReducedBound_support Q.ellipticity_parameter hω).2.1 0
    have hlow : ∀ ξ : Vec d, 0 ≤ dotProduct ξ ((reducedCoefficient ω 0).mulVec ξ) := fun ξ =>
      (mul_nonneg (inv_nonneg.mpr hK0) (euclideanSq_nonneg_coords ξ)).trans (hbd ξ).1
    have hup : ∀ ξ : Vec d,
        dotProduct ξ ((reducedCoefficient ω 0).mulVec ξ) ≤
          sourceReducedBound Λ₀ * euclideanSq ξ :=
      fun ξ => (hbd ξ).2
    exact abs_entry_le_of_quadratic_bounds hK0 (reducedCoefficient ω 0) hsymm hlow hup
      (firstIdx hd) i
  have hw0 : Continuous fun w : FieldPair d => w.1 0 :=
    (continuous_eval_const (0 : Vec d)).comp continuous_fst
  have hentry : Continuous fun w : FieldPair d => (w.1 0) (firstIdx hd) i :=
    hw0.matrix_elem (firstIdx hd) i
  have hmeas : MeasurableSet
      {w : FieldPair d | |(w.1 0) (firstIdx hd) i| ≤ sourceReducedBound Λ₀} :=
    measurableSet_abs_le hentry.measurable (sourceReducedBound Λ₀)
  exact (MeasureTheory.ae_map_iff (Probability.measurable_reduce (d := d)).aemeasurable
    hmeas).mpr hQ

/-- Existential form of `reduced_entry_bound_ae`. -/
theorem exists_reduced_entry_bound {d : ℕ} {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) : ∃ K : ℝ, ∀ᵐ w ∂reducedReferenceLaw Q, |(w.1 0) (firstIdx hd) i| ≤ K :=
  ⟨sourceReducedBound Λ₀, reduced_entry_bound_ae hd Q i⟩

/-! ### The column divergence and its pointwise bound -/

-- The classical column divergence `∑ⱼ ∂ⱼ a_{ji}(0)` is `DriftH5.cdiv`, whose weak-divergence
-- identity is proved in `EinsteinRelation.Mobility.DriftWeakDivergence`.
open DriftH5 (cdiv)

/-- Measurability of the column divergence on coefficient pairs. The derivative is measurable as a
function of the parameter by Mathlib's parametric derivative theorem. -/
theorem measurable_cdiv {d : ℕ} (i : Fin d) : Measurable (cdiv i) := by
  have hmeas : ∀ j : Fin d, Measurable fun w : FieldPair d =>
      fderiv ℝ (fun x => (w.1 x) j i) 0 (unitVector j) := by
    intro j
    have hc : Continuous fun p : FieldPair d × Vec d => (p.1.1 p.2) j i :=
      (continuous_coeff_eval (d := d)).matrix_elem j i
    have hm := measurable_fderiv_apply_const_with_param ℝ
      (f := fun (w : FieldPair d) (x : Vec d) => (w.1 x) j i) hc (unitVector j)
    have hpt : Measurable fun w : FieldPair d => (w, (0 : Vec d)) :=
      measurable_id.prodMk measurable_const
    exact hm.comp hpt
  show Measurable fun w : FieldPair d => ∑ j, fderiv ℝ (fun x => (w.1 x) j i) 0 (unitVector j)
  exact Finset.measurable_sum Finset.univ fun j _ => hmeas j

/-- The derivative of a Euclidean-Lipschitz function along a coordinate direction is bounded by the
Lipschitz constant. -/
theorem abs_fderiv_unitVector_le_of_lipschitz {d : ℕ} {g : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y : Vec d, |g x - g y| ≤ L * euclideanNorm (x - y)) (j : Fin d) :
    |fderiv ℝ g 0 (unitVector j)| ≤ L := by
  by_cases hdiff : DifferentiableAt ℝ g 0
  · have hline : HasDerivAt (fun t : ℝ => t • unitVector j) (unitVector j) 0 :=
      ((hasDerivAt_id' (0 : ℝ)).smul_const (unitVector j)).congr_deriv (by simp)
    have hcomp : HasDerivAt (fun t : ℝ => g (t • unitVector j)) (fderiv ℝ g 0 (unitVector j)) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) (hl := hdiff.hasFDerivAt) (hf := hline)
        (hy := by simp)
    have hlip : ∀ t : ℝ, ‖g (t • unitVector j) - g ((0 : ℝ) • unitVector j)‖ ≤
        L * ‖t - 0‖ := by
      intro t
      have hE : euclideanNorm (t • unitVector j) = |t| := by
        rw [TimeChange.euclideanNorm_smul, euclideanNorm_unitVector_eq_one, mul_one]
      have h := hg (t • unitVector j) 0
      rw [sub_zero, hE] at h
      simpa only [zero_smul, Real.norm_eq_abs, sub_zero] using h
    have hbound := hcomp.le_of_lip' hL (Filter.Eventually.of_forall hlip)
    rw [Real.norm_eq_abs] at hbound
    exact hbound
  · rw [fderiv_zero_of_not_differentiableAt hdiff, ContinuousLinearMap.zero_apply, abs_zero]
    exact hL

/-- A coefficient with Euclidean-Lipschitz entries has column divergence at most `d` times the
Lipschitz constant. -/
theorem abs_cdiv_le_of_lipschitz {d : ℕ} {L : ℝ} (hL : 0 ≤ L) (i : Fin d) (w : FieldPair d)
    (hw : IsOperatorLipschitz L (w.1 : Vec d → Mat d)) : |cdiv i w| ≤ (d : ℝ) * L := by
  unfold cdiv
  calc |∑ j, fderiv ℝ (fun x => (w.1 x) j i) 0 (unitVector j)|
      ≤ ∑ j, |fderiv ℝ (fun x => (w.1 x) j i) 0 (unitVector j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, L := Finset.sum_le_sum fun j _ =>
        abs_fderiv_unitVector_le_of_lipschitz hL (fun x y => hw.entry_bound j i x y) j
    _ = (d : ℝ) * L := by simp

/-- The reduced Lipschitz constant `exp(2Λ₀)(Λ₀ + 2Λ₀²)` of `sourceReducedBound_support`. -/
noncomputable def reducedLipschitzConstant (Λ₀ : ℝ) : ℝ :=
  Real.exp (2 * Λ₀) * (Λ₀ + 2 * Λ₀ ^ 2)

/-- Almost surely under the reduced reference law, the column divergence is bounded by
`d` times the reduced Lipschitz constant. -/
theorem ae_abs_cdiv_le_reduced {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    ∀ᵐ w ∂reducedReferenceLaw Q, |cdiv i w| ≤ (d : ℝ) * reducedLipschitzConstant Λ₀ := by
  have hL : 0 ≤ reducedLipschitzConstant Λ₀ := by
    unfold reducedLipschitzConstant
    have h1 : 0 ≤ Λ₀ + 2 * Λ₀ ^ 2 := by
      nlinarith [Q.ellipticity_parameter, sq_nonneg Λ₀]
    exact mul_nonneg (Real.exp_pos _).le h1
  have hQ : ∀ᵐ ω ∂Q.measure, |cdiv i (reduce ω)| ≤ (d : ℝ) * reducedLipschitzConstant Λ₀ := by
    filter_upwards [Q.regular] with ω hω
    exact abs_cdiv_le_of_lipschitz hL i (reduce ω)
      (sourceReducedBound_support Q.ellipticity_parameter hω).2.2.2.1
  have hmeas : MeasurableSet
      {w : FieldPair d | |cdiv i w| ≤ (d : ℝ) * reducedLipschitzConstant Λ₀} :=
    measurableSet_abs_le (measurable_cdiv i) ((d : ℝ) * reducedLipschitzConstant Λ₀)
  exact (MeasureTheory.ae_map_iff (Probability.measurable_reduce (d := d)).aemeasurable
    hmeas).mpr hQ

/-! ### Almost-sure differentiability at the origin -/

/-- The coefficient pairs whose coefficient is not differentiable at the origin. -/
def nonDiffZeroSet (d : ℕ) : Set (FieldPair d) :=
  {w | ¬DifferentiableAt ℝ (fun x => w.1 x) 0}

/-- The pairs `(ω, y)` at which the reduced coefficient of `ω` is not differentiable at `y`. -/
def nonDiffSet (d : ℕ) : Set (FieldPair d × Vec d) :=
  {p | ¬DifferentiableAt ℝ (fun y => (reduce p.1).1 y) p.2}

/-- Under the reduced reference law, the coefficient is differentiable at the origin almost surely.
The bad set has reduced-law mass zero: its product with Lebesgue measure is null by Fubini, its
`x`-sections all have mass `reducedReferenceLaw Q (nonDiffZeroSet d)` by stationarity, and
Lebesgue measure of `Vec d` is nonzero. -/
theorem ae_differentiableAt_zero_reducedLaw {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ w ∂reducedReferenceLaw Q, DifferentiableAt ℝ (fun x => w.1 x) 0 := by
  haveI : IsProbabilityMeasure Q.measure := Q.probability
  have hN : MeasurableSet (nonDiffZeroSet d) := by
    have hS := measurableSet_not_differentiableAt_matrix (α := FieldPair d)
      (M := fun (w : FieldPair d) (y : Vec d) => w.1 y) (continuous_coeff_eval (d := d))
    have hpt : Measurable fun w : FieldPair d => (w, (0 : Vec d)) :=
      measurable_id.prodMk measurable_const
    exact hS.preimage hpt
  have hB : MeasurableSet (nonDiffSet d) :=
    measurableSet_not_differentiableAt_matrix (α := FieldPair d)
      (M := fun (w : FieldPair d) (y : Vec d) => (reduce w).1 y)
      (continuous_reduced_coeff_eval (d := d))
  -- For almost every environment, the reduced coefficient is differentiable at almost every point.
  have hfib : ∀ᵐ ω ∂Q.measure, (volume : Measure (Vec d)) (Prod.mk ω ⁻¹' nonDiffSet d) = 0 := by
    filter_upwards [Q.ae_ae_differentiableAt_reduction] with ω hω
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [hω] with x hx hmem
    exact (show ¬DifferentiableAt ℝ (fun y => (reduce ω).1 y) x from hmem) hx.2
  -- Sections in the environment variable have mass `reducedReferenceLaw Q (nonDiffZeroSet d)`.
  have hsec : ∀ x : Vec d, Q.measure ((fun ω : FieldPair d => (ω, x)) ⁻¹' nonDiffSet d) =
      reducedReferenceLaw Q (nonDiffZeroSet d) := by
    intro x
    have hpre : (fun ω : FieldPair d => (ω, x)) ⁻¹' nonDiffSet d =
        translate x ⁻¹' (reduce ⁻¹' nonDiffZeroSet d) := by
      ext ω
      show ¬DifferentiableAt ℝ (fun y => (reduce ω).1 y) x ↔
        ¬DifferentiableAt ℝ (fun y => (reduce (translate x ω)).1 y) 0
      rw [reduce_translate]
      exact (differentiableAt_zero_translate_iff (fun z => (reduce ω).1 z) x).symm.not
    rw [hpre]
    have hS : MeasurableSet (reduce ⁻¹' nonDiffZeroSet d) :=
      (Probability.measurable_reduce (d := d)) hN
    calc Q.measure (translate x ⁻¹' (reduce ⁻¹' nonDiffZeroSet d))
        = Measure.map (translate x) Q.measure (reduce ⁻¹' nonDiffZeroSet d) :=
          (Measure.map_apply (Probability.measurable_translate x) hS).symm
      _ = Q.measure (reduce ⁻¹' nonDiffZeroSet d) := by rw [Q.stationary x]
      _ = Measure.map reduce Q.measure (nonDiffZeroSet d) :=
          (Measure.map_apply (Probability.measurable_reduce (d := d)) hN).symm
      _ = reducedReferenceLaw Q (nonDiffZeroSet d) := rfl
  -- Fubini in both orders for the product of the environment law with Lebesgue measure.
  have hprod0 : (Q.measure.prod volume) (nonDiffSet d) = 0 := by
    rw [Measure.prod_apply hB]
    calc ∫⁻ ω, (volume : Measure (Vec d)) (Prod.mk ω ⁻¹' nonDiffSet d) ∂Q.measure
        = ∫⁻ _ω, 0 ∂Q.measure := lintegral_congr_ae hfib
      _ = 0 := lintegral_zero
  have hprod1 : (Q.measure.prod volume) (nonDiffSet d) =
      reducedReferenceLaw Q (nonDiffZeroSet d) * (volume : Measure (Vec d)) Set.univ := by
    rw [Measure.prod_apply_symm hB]
    calc ∫⁻ x, Q.measure ((fun ω : FieldPair d => (ω, x)) ⁻¹' nonDiffSet d) ∂volume
        = ∫⁻ _x, reducedReferenceLaw Q (nonDiffZeroSet d) ∂volume :=
          lintegral_congr fun x => hsec x
      _ = reducedReferenceLaw Q (nonDiffZeroSet d) * (volume : Measure (Vec d)) Set.univ :=
          lintegral_const _
  have hvol : (volume : Measure (Vec d)) Set.univ ≠ 0 :=
    isOpen_univ.measure_ne_zero volume Set.univ_nonempty
  have hμ0 : reducedReferenceLaw Q (nonDiffZeroSet d) = 0 := by
    have h : reducedReferenceLaw Q (nonDiffZeroSet d) *
        (volume : Measure (Vec d)) Set.univ = 0 := by
      rw [← hprod1, hprod0]
    exact (mul_eq_zero.mp h).resolve_right hvol
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμ0] with w hw
  have hw' : ¬¬DifferentiableAt ℝ (fun x => w.1 x) 0 := hw
  exact Classical.not_not.mp hw'

end EinsteinRelation
