import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Euclidean `L^p` moment bound from coordinatewise bounds.

Source anchors: paper/main.tex:834-838 (Minkowski's inequality in probability applied to the
Euclidean norm of a vector-valued moment) and paper/main.tex:857-859 (the `L^m` norm of the
Euclidean-valued gradient difference). The Euclidean norm of a vector is bounded by
`sqrt(dimension)` times its largest coordinate in `L^p`. The proof is Minkowski's inequality in
`L^(p/2)` applied to the squared coordinates, which is available since `p / 2 ≥ 1`:

`‖‖f‖‖_p^2 = ‖ ∑_i f_i^2 ‖_{p/2} ≤ ∑_i ‖f_i‖_p^2 ≤ card ι * C^2`.

No vector integrability premise is needed, and the empty index type is covered.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- If every Euclidean coordinate of `f` has `L^p(Q)` norm at most `C` for a probability measure
`Q` and `p ≥ 2`, then `f` is `L^p(Q)` and its Euclidean `L^p` norm is at most
`sqrt(card ι) * C`. -/
theorem eLpNorm_euclidean_le_sqrt_card {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (p C : ℝ) (hp : 2 ≤ p) (hC : 0 ≤ C)
    (f : Ω → EuclideanSpace ℝ ι) (hf : Measurable f)
    (hb : ∀ i : ι, eLpNorm (fun ω => f ω i) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C) :
    MemLp f (ENNReal.ofReal p) Q ∧
    eLpNorm f (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (Real.sqrt (Fintype.card ι)*C) := by
  -- Measurability of `f` and of its squared coordinates.
  have hfA : AEStronglyMeasurable f Q := hf.aestronglyMeasurable
  have hsqA : ∀ i : ι, AEStronglyMeasurable (fun ω => ‖f ω i‖ ^ (2 : ℝ)) Q := by
    intro i
    simp only [Real.rpow_two]
    have hcont : Continuous (fun x : EuclideanSpace ℝ ι => ‖x i‖ ^ 2) := by fun_prop
    exact hcont.comp_aestronglyMeasurable hfA
  -- Exponent bookkeeping: `p / 2 ≥ 1` and `(p / 2) * 2 = p`.
  have hq1 : (1 : ℝ) ≤ p / 2 := by linarith
  have hexp : ENNReal.ofReal (p / 2) * ENNReal.ofReal 2 = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ p / 2 by linarith)]
    congr 1
    ring
  -- Pointwise: the squared Euclidean norm is the sum of the squared coordinates.
  have hpt : ∀ ω, ‖f ω‖ ^ (2 : ℝ) = ∑ i : ι, ‖f ω i‖ ^ (2 : ℝ) := by
    intro ω
    simp only [Real.rpow_two]
    exact EuclideanSpace.norm_sq_eq (f ω)
  have hfun : (∑ i : ι, (fun ω => ‖f ω i‖ ^ (2 : ℝ))) = fun ω => ‖f ω‖ ^ (2 : ℝ) := by
    funext ω
    simp only [Finset.sum_apply]
    exact (hpt ω).symm
  -- Minkowski's inequality in `L^(p/2)` for the sum of squared coordinates.
  have hMink : eLpNorm (∑ i : ι, (fun ω => ‖f ω i‖ ^ (2 : ℝ))) (ENNReal.ofReal (p / 2)) Q
      ≤ ∑ i : ι, eLpNorm (fun ω => ‖f ω i‖ ^ (2 : ℝ)) (ENNReal.ofReal (p / 2)) Q :=
    eLpNorm_sum_le (ENNReal.one_le_ofReal.mpr hq1)
  rw [hfun] at hMink
  -- The `L^(p/2)` norm of the squared Euclidean norm is the square of the `L^p` norm.
  have hnorm2 : eLpNorm (fun ω => ‖f ω‖ ^ (2 : ℝ)) (ENNReal.ofReal (p / 2)) Q
      = eLpNorm f (ENNReal.ofReal p) Q ^ (2 : ℝ) := by
    rw [eLpNorm_norm_rpow f hfA (by norm_num : (0 : ℝ) < 2), hexp]
  have hcoord : ∀ i : ι, eLpNorm (fun ω => ‖f ω i‖ ^ (2 : ℝ)) (ENNReal.ofReal (p / 2)) Q
      = eLpNorm (fun ω => f ω i) (ENNReal.ofReal p) Q ^ (2 : ℝ) := by
    intro i
    have hcont : Continuous (fun x : EuclideanSpace ℝ ι => x i) := by fun_prop
    have hci : AEStronglyMeasurable (fun ω => f ω i) Q := hcont.comp_aestronglyMeasurable hfA
    rw [eLpNorm_norm_rpow (fun ω => f ω i) hci (by norm_num : (0 : ℝ) < 2), hexp]
  -- Each squared coordinate has `L^(p/2)` norm at most `C^2`.
  have hCsq : ENNReal.ofReal C ^ (2 : ℝ) = ENNReal.ofReal (C ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hC (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
  have hcoordBound : ∀ i : ι, eLpNorm (fun ω => ‖f ω i‖ ^ (2 : ℝ)) (ENNReal.ofReal (p / 2)) Q
      ≤ ENNReal.ofReal (C ^ 2) := by
    intro i
    rw [hcoord i, ← hCsq]
    exact ENNReal.rpow_le_rpow (hb i) (by norm_num)
  have hsum : ∑ i : ι, eLpNorm (fun ω => ‖f ω i‖ ^ (2 : ℝ)) (ENNReal.ofReal (p / 2)) Q
      ≤ ∑ _i : ι, ENNReal.ofReal (C ^ 2) :=
    Finset.sum_le_sum fun i _ => hcoordBound i
  have hsumEq : ∑ _i : ι, ENNReal.ofReal (C ^ 2)
      = ENNReal.ofReal ((Fintype.card ι : ℝ) * C ^ 2) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hE2 : eLpNorm f (ENNReal.ofReal p) Q ^ (2 : ℝ)
      ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * C ^ 2) := by
    rw [← hnorm2]
    exact hMink.trans (hsum.trans hsumEq.le)
  -- Take square roots: `(sqrt card * C)^2 = card * C^2`.
  have hX : ENNReal.ofReal (Real.sqrt (Fintype.card ι) * C) ^ (2 : ℝ)
      = ENNReal.ofReal ((Fintype.card ι : ℝ) * C ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC)
        (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hE : eLpNorm f (ENNReal.ofReal p) Q
      ≤ ENNReal.ofReal (Real.sqrt (Fintype.card ι) * C) := by
    refine (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp ?_
    rw [hX]
    exact hE2
  exact ⟨hE.trans_lt ENNReal.ofReal_lt_top, hE⟩

end EinsteinRelation.Correctors
