import EinsteinRelation.Probability.HoeffdingMoments
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Filter
import Mathlib.Logic.Equiv.List
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Colour-class Hoeffding bound for countable sums

Let `X i`, `i ∈ ι`, be random variables coloured by `col : ι → Fin K`. Within one colour class
the variables are independent, centred and bounded by `c i`. The moment form of Hoeffding's
inequality (`lintegral_abs_sum_rpow_le_of_iIndepFun`) then bounds every finite partial sum
inside one class. The triangle inequality for `eLpNorm` adds the `K` classes of a finite sum.
A Fatou-type limit along the finite subsets of a countable `ι` passes the bound to the
countable sum, which is pointwise summable.

This is the bound for the clock spatial averages in `paper/main.tex` (lines 1159–1163).
-/

open MeasureTheory ProbabilityTheory Filter

namespace EinsteinRelation.Probability

/-- The Hoeffding moment constant is nonnegative for `m > 0`. -/
private lemma hoeffdingMomentConst_nonneg {m : ℝ} (hm : 0 < m) :
    0 ≤ hoeffdingMomentConst m := by
  unfold hoeffdingMomentConst
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    (Real.rpow_nonneg (div_nonneg hm.le (Real.exp_pos 1).le) m)

/-- The `m`-th root of the Hoeffding moment bound `C * V ^ (m / 2)` equals
`C ^ (1 / m) * V ^ (1 / 2)`. -/
private lemma rpow_hoeffding_bound {C V m : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V) (hm : 0 < m) :
    (C * V ^ (m / 2)) ^ (1 / m) = C ^ (1 / m) * V ^ (1 / 2 : ℝ) := by
  have hmne : m ≠ 0 := hm.ne'
  have h : m / 2 * (1 / m) = 1 / 2 := by
    calc m / 2 * (1 / m) = m * m⁻¹ / 2 := by ring
      _ = 1 / 2 := by rw [mul_inv_cancel₀ hmne]
  rw [Real.mul_rpow hC (Real.rpow_nonneg hV (m / 2)), ← Real.rpow_mul hV, h]

/-- The `eLpNorm` form of the Hoeffding moment bound for one finite sum of independent centred
variables, indexed by the elements of `t`. -/
private lemma eLpNorm_sum_le_of_iIndepFun_subtype {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (t : Finset ι) (X : ι → Ω → ℝ)
    (hindep : iIndepFun (fun i : t => X i) μ) (hmeas : ∀ i, Measurable (X i))
    (c : ι → ℝ) (hc : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ c i) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (m : ℝ) (hm : 1 ≤ m) :
    eLpNorm (fun ω => ∑ i ∈ t, X i ω) (ENNReal.ofReal m) μ ≤
      ENNReal.ofReal (hoeffdingMomentConst m ^ (1 / m) * (∑ i ∈ t, c i ^ 2) ^ (1 / 2 : ℝ)) := by
  have hm0 : 0 < m := by linarith
  have hC : 0 ≤ hoeffdingMomentConst m := hoeffdingMomentConst_nonneg hm0
  have hV : 0 ≤ ∑ i ∈ t, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (c i)
  have hsub := lintegral_abs_sum_rpow_le_of_iIndepFun (μ := μ) (Finset.univ : Finset t)
    (fun i : t => X i) hindep (fun i : t => hmeas i.1) (fun i : t => c i) (fun i : t => hc i.1)
    (fun i : t => hmean i.1) m hm
  have e1 : ∀ ω, ∑ i : t, X i ω = ∑ i ∈ t, X i ω := fun ω =>
    Finset.sum_coe_sort t (fun i => X i ω)
  have e2 : ∑ i : t, c i ^ 2 = ∑ i ∈ t, c i ^ 2 := Finset.sum_coe_sort t (fun i => c i ^ 2)
  simp only [e1, e2] at hsub
  have hnorm : ∀ ω, ‖(∑ i ∈ t, X i ω)‖ₑ ^ m = ENNReal.ofReal (|∑ i ∈ t, X i ω| ^ m) := fun ω => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hm0.le]
  have hL : (∫⁻ ω, ‖(∑ i ∈ t, X i ω)‖ₑ ^ m ∂μ) ≤
      ENNReal.ofReal (hoeffdingMomentConst m * (∑ i ∈ t, c i ^ 2) ^ (m / 2)) :=
    (lintegral_congr hnorm).trans_le hsub
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hm0).ne'
      ENNReal.ofReal_ne_top
      (Finset.measurable_sum t fun i _ => hmeas i).aestronglyMeasurable,
    ENNReal.toReal_ofReal hm0.le]
  calc (∫⁻ ω, ‖(∑ i ∈ t, X i ω)‖ₑ ^ m ∂μ) ^ (1 / m)
      ≤ (ENNReal.ofReal (hoeffdingMomentConst m * (∑ i ∈ t, c i ^ 2) ^ (m / 2))) ^ (1 / m) :=
        ENNReal.rpow_le_rpow hL (one_div_nonneg.mpr hm0.le)
    _ = ENNReal.ofReal ((hoeffdingMomentConst m * (∑ i ∈ t, c i ^ 2) ^ (m / 2)) ^ (1 / m)) :=
        ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC (Real.rpow_nonneg hV (m / 2)))
          (one_div_nonneg.mpr hm0.le)
    _ = ENNReal.ofReal (hoeffdingMomentConst m ^ (1 / m) * (∑ i ∈ t, c i ^ 2) ^ (1 / 2 : ℝ)) := by
        rw [rpow_hoeffding_bound hC hV hm0]

/-- Finite sums over an arbitrary finite set of indices. The set is split along the colour
classes, each class is bounded by the Hoeffding moment bound, and the `K` class bounds are added
with the triangle inequality for `eLpNorm`. -/
private lemma eLpNorm_sum_colored_le {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : ℕ} (col : ι → Fin K) (X : ι → Ω → ℝ)
    (hindep : ∀ (k : Fin K) (s : Finset ι), (∀ i ∈ s, col i = k) →
      iIndepFun (fun i : s => X i) μ)
    (hmeas : ∀ i, Measurable (X i)) (c : ι → ℝ) (hc : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ c i)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (m : ℝ) (hm : 1 ≤ m) (s : Finset ι) :
    eLpNorm (fun ω => ∑ i ∈ s, X i ω) (ENNReal.ofReal m) μ ≤
      ENNReal.ofReal ((K : ℝ) * hoeffdingMomentConst m ^ (1 / m) *
        (∑ i ∈ s, c i ^ 2) ^ (1 / 2 : ℝ)) := by
  have hm0 : 0 < m := by linarith
  have hC : 0 ≤ hoeffdingMomentConst m := hoeffdingMomentConst_nonneg hm0
  have hsplit : (fun ω => ∑ i ∈ s, X i ω) =
      ∑ j : Fin K, (fun ω => ∑ i ∈ s.filter (fun i => col i = j), X i ω) := by
    rw [Finset.sum_fn]
    funext ω
    exact (Finset.sum_fiberwise s col (fun i => X i ω)).symm
  have hclass : ∀ j : Fin K,
      eLpNorm (fun ω => ∑ i ∈ s.filter (fun i => col i = j), X i ω) (ENNReal.ofReal m) μ ≤
        ENNReal.ofReal (hoeffdingMomentConst m ^ (1 / m) * (∑ i ∈ s, c i ^ 2) ^ (1 / 2 : ℝ)) := by
    intro j
    refine (eLpNorm_sum_le_of_iIndepFun_subtype (s.filter (fun i => col i = j)) X
      (hindep j (s.filter (fun i => col i = j)) fun i hi => (Finset.mem_filter.mp hi).2)
      hmeas c hc hmean m hm).trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hC _)
    exact Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => sq_nonneg (c i))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun i _ _ => sq_nonneg (c i)) (by norm_num)
  have hmeasJ : ∀ j : Fin K, AEStronglyMeasurable
      (fun ω => ∑ i ∈ s.filter (fun i => col i = j), X i ω) μ := fun j =>
    (Finset.measurable_sum (s.filter (fun i => col i = j)) fun i _ => hmeas i).aestronglyMeasurable
  calc eLpNorm (fun ω => ∑ i ∈ s, X i ω) (ENNReal.ofReal m) μ
      = eLpNorm (∑ j : Fin K, (fun ω => ∑ i ∈ s.filter (fun i => col i = j), X i ω))
          (ENNReal.ofReal m) μ :=
        congrArg (fun f : Ω → ℝ => eLpNorm f (ENNReal.ofReal m) μ) hsplit
    _ ≤ ∑ j : Fin K, eLpNorm (fun ω => ∑ i ∈ s.filter (fun i => col i = j), X i ω)
          (ENNReal.ofReal m) μ :=
        eLpNorm_sum_le (ENNReal.one_le_ofReal.mpr hm)
    _ ≤ ∑ j : Fin K, ENNReal.ofReal (hoeffdingMomentConst m ^ (1 / m) *
          (∑ i ∈ s, c i ^ 2) ^ (1 / 2 : ℝ)) :=
        Finset.sum_le_sum fun j _ => hclass j
    _ = ENNReal.ofReal ((K : ℝ) * (hoeffdingMomentConst m ^ (1 / m) *
          (∑ i ∈ s, c i ^ 2) ^ (1 / 2 : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg K : (0 : ℝ) ≤ K), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal ((K : ℝ) * hoeffdingMomentConst m ^ (1 / m) *
          (∑ i ∈ s, c i ^ 2) ^ (1 / 2 : ℝ)) := by
        rw [mul_assoc]

/-- **Colour-class Hoeffding bound for a countable sum.** For a countable index type `ι`, a
probability measure `μ`, and a colouring `col : ι → Fin K` such that the variables of each colour
class are independent, centred and bounded by `c i` almost surely, the `L^m` norm of the pointwise
sum `∑' i, X i` is at most `K * hoeffdingMomentConst m ^ (1 / m) * (∑' i, c i ^ 2) ^ (1 / 2)`,
for every `m ≥ 1`. -/
theorem eLpNorm_tsum_le_colored {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Countable ι] {K : ℕ} (col : ι → Fin K) (X : ι → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (c : ι → ℝ)
    (hindep : ∀ (k : Fin K) (s : Finset ι), (∀ i ∈ s, col i = k) →
      iIndepFun (fun i : s => X i) μ)
    (hc : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ c i) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hc2 : Summable (fun i => c i ^ 2)) (hpt : ∀ ω, Summable (fun i => X i ω))
    (m : ℝ) (hm : 1 ≤ m) :
    eLpNorm (fun ω => ∑' i, X i ω) (ENNReal.ofReal m) μ
      ≤ ENNReal.ofReal ((K : ℝ) * hoeffdingMomentConst m ^ (1 / m) *
        (∑' i, c i ^ 2) ^ (1 / 2 : ℝ)) := by
  have hm0 : 0 < m := by linarith
  have hC : 0 ≤ hoeffdingMomentConst m := hoeffdingMomentConst_nonneg hm0
  have hf : ∀ s : Finset ι, AEStronglyMeasurable (fun ω => ∑ i ∈ s, X i ω) μ :=
    fun s => (Finset.measurable_sum s fun i _ => hmeas i).aestronglyMeasurable
  have htend : ∀ᵐ ω ∂μ, Filter.Tendsto (fun s : Finset ι => ∑ i ∈ s, X i ω) Filter.atTop
      (nhds (∑' i, X i ω)) :=
    ae_of_all μ fun ω => (hpt ω).hasSum
  refine MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (u := (Filter.atTop : Filter (Finset ι)))
    (f := fun s ω => ∑ i ∈ s, X i ω) ?_ hf
    (aestronglyMeasurable_of_tendsto_ae Filter.atTop hf htend) htend
  refine Filter.Eventually.of_forall fun s => ?_
  refine (eLpNorm_sum_colored_le col X hindep hmeas c hc hmean m hm s).trans
    (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K) (Real.rpow_nonneg hC _))
  exact Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => sq_nonneg (c i))
    (sum_le_hasSum s (fun i _ => sq_nonneg (c i)) hc2.hasSum) (by norm_num)

end EinsteinRelation.Probability
