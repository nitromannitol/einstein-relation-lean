import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds_u23_derivatives
import EinsteinRelation.Correctors.EllipticOperatorBound
import EinsteinRelation.Environment.EuclideanLipschitz
import EinsteinRelation.Regeneration.HalfSpaces
import EinsteinRelation.Environment.ReductionEmbedding
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory
open scoped BigOperators
noncomputable section

namespace EinsteinFull.Blueprint
open EinsteinRelation

private lemma euclidean_unit {d : ℕ} (j : Fin d) :
    euclideanNorm (unitVector j) = 1 := by
  change Real.sqrt (dotProduct (Pi.single j (1 : ℝ)) (Pi.single j 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

private lemma matrix_unit_entry {d : ℕ} (A : Mat d) (j i : Fin d) :
    (A.mulVec (unitVector j)) i = A i j := by
  change dotProduct (fun k => A i k) (Pi.single j 1) = _
  rw [dotProduct_single, mul_one]

private lemma norm_le_euclidean {d : ℕ} (v : Vec d) : ‖v‖ ≤ euclideanNorm v := by
  apply pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr
  intro i
  exact Regeneration.coordinate_abs_le_euclideanNorm v i

private lemma scalar_derivative_bound {d k : ℕ} {f : Vec d → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x v, |iteratedFDeriv ℝ k f x v| ≤ C * ∏ j, euclideanNorm (v j))
    (x : Vec d) : ‖iteratedFDeriv ℝ k f x‖ ≤ C * ((d : ℝ) + 1) ^ k := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  calc
    ‖iteratedFDeriv ℝ k f x v‖ ≤ C * ∏ j, euclideanNorm (v j) := h x v
    _ ≤ C * ∏ j, (((d : ℝ) + 1) * ‖v j‖) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) (fun j _ =>
        euclideanNorm_le_dimension_mul_norm (v j))
    _ = (C * ((d : ℝ) + 1) ^ k) * ∏ j, ‖v j‖ := by
      rw [Finset.prod_mul_distrib]; simp [mul_assoc]

private lemma entry_derivative_bound {d k : ℕ} {ω : FieldPair d} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x v ξ, euclideanNorm (Matrix.mulVec (fun i j =>
      iteratedFDeriv ℝ k (fun y => ω.1 y i j) x v) ξ) ≤
        C * (∏ j, euclideanNorm (v j)) * euclideanNorm ξ)
    (x : Vec d) (i j : Fin d) :
    ‖iteratedFDeriv ℝ k (fun y => ω.1 y i j) x‖ ≤ C * ((d : ℝ) + 1) ^ k := by
  apply scalar_derivative_bound hC
  intro x v
  have hc := Regeneration.coordinate_abs_le_euclideanNorm
    (Matrix.mulVec (fun i j => iteratedFDeriv ℝ k (fun y => ω.1 y i j) x v) (unitVector j)) i
  have hb := h x v (unitVector j)
  rw [euclidean_unit, mul_one] at hb
  refine le_trans (le_of_eq ?_) (hc.trans hb)
  congr 1
  exact (matrix_unit_entry
    (fun i j => iteratedFDeriv ℝ k (fun y => ω.1 y i j) x v) j i).symm

private def physicalBound {d : ℕ} (D : StructuralData d) (n : ℕ) : ℝ :=
  if n = 0 then D.ellipticity else D.derivativeBound n * ((d : ℝ) + 1) ^ n

private lemma physicalBound_nonneg {d : ℕ} (D : StructuralData d) (n : ℕ) :
    0 ≤ physicalBound D n := by
  unfold physicalBound
  split_ifs with hn
  · linarith [D.one_le_ellipticity]
  · exact mul_nonneg (D.derivativeBound_pos n (by omega)).le (by positivity)

private lemma physical_derivatives {d : ℕ} (D : StructuralData d) (ω : FieldPair d)
    (hr : IsRegular D.ellipticity ω) (hs : IsSmoothWithBounds D.derivativeBound ω)
    (n : ℕ) (x : Vec d) :
    ‖iteratedFDeriv ℝ n (fun y => ω.2 y) x‖ ≤ physicalBound D n ∧
    ∀ i j, ‖iteratedFDeriv ℝ n (fun y => ω.1 y i j) x‖ ≤ physicalBound D n := by
  by_cases hn : n = 0
  · subst n
    simp only [physicalBound, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    refine ⟨hr.2.1 x, fun i j => ?_⟩
    have hc := Regeneration.coordinate_abs_le_euclideanNorm
      ((ω.1 x).mulVec (unitVector j)) i
    rw [matrix_unit_entry] at hc
    have hb := Correctors.isElliptic_mulVec_euclideanNorm_le
      (by linarith [D.one_le_ellipticity]) hr.1 x (unitVector j)
    rw [euclidean_unit, mul_one] at hb
    exact hc.trans hb
  · obtain ⟨A, B, hA, hB, hAB, ha, hb⟩ := hs.2 n (by omega)
    rw [physicalBound, if_neg hn]
    constructor
    · exact (scalar_derivative_bound hB hb x).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · intro i j
      exact (entry_derivative_bound hA ha x i j).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

private def jetBound {d : ℕ} (D : StructuralData d) (n : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range (n + 1), physicalBound D j

private lemma jetBound_ge_one {d : ℕ} (D : StructuralData d) (n : ℕ) :
    1 ≤ jetBound D n := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => physicalBound_nonneg D j)

private lemma physicalBound_le_jetBound {d : ℕ} (D : StructuralData d) {i n : ℕ}
    (hi : i ≤ n) : physicalBound D i ≤ jetBound D n := by
  have h := Finset.single_le_sum (fun j _ => physicalBound_nonneg D j)
    (Finset.mem_range.mpr (by omega : i < n + 1))
  exact h.trans (le_add_of_nonneg_left zero_le_one)

private def clockBound {d : ℕ} (D : StructuralData d) (n : ℕ) : ℝ :=
  n.factorial * (2 ^ n * Real.exp (2 * D.ellipticity)) * jetBound D n ^ n

private lemma clockBound_nonneg {d : ℕ} (D : StructuralData d) (n : ℕ) :
    0 ≤ clockBound D n := by
  unfold clockBound
  exact mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans (jetBound_ge_one D n)) _)

private lemma clock_derivatives {d : ℕ} (D : StructuralData d) (ω : FieldPair d)
    (hr : IsRegular D.ellipticity ω) (hs : IsSmoothWithBounds D.derivativeBound ω)
    (n : ℕ) (x : Vec d) :
    ‖iteratedFDeriv ℝ n (clockDensity ω) x‖ ≤ clockBound D n := by
  apply norm_iteratedFDeriv_comp_le
    (g := fun t : ℝ => Real.exp (-2 * t)) (f := fun y => ω.2 y)
    ((contDiff_const.mul contDiff_id).exp) hs.1.2
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)) x
  · intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul]
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-2 * ω.2 x) ≤ Real.exp (2 * D.ellipticity) := by
      apply Real.exp_le_exp.mpr
      have := (abs_le.mp (hr.2.1 x)).1
      linarith
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hi) he (Real.exp_pos _).le
      (by positivity)
  · intro i hi hin
    exact ((physical_derivatives D ω hr hs i x).1.trans
      (physicalBound_le_jetBound D hin)).trans (le_self_pow₀ (jetBound_ge_one D n) (by omega))

private def matrixBound {d : ℕ} (D : StructuralData d) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * clockBound D j * physicalBound D (n - j)

private lemma matrixBound_nonneg {d : ℕ} (D : StructuralData d) (n : ℕ) :
    0 ≤ matrixBound D n := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (clockBound_nonneg D j)) (physicalBound_nonneg D _)

private lemma reduced_entry_derivatives {d : ℕ} (D : StructuralData d) (ω : FieldPair d)
    (hr : IsRegular D.ellipticity ω) (hs : IsSmoothWithBounds D.derivativeBound ω)
    (n : ℕ) (x : Vec d) (i j : Fin d) :
    ‖iteratedFDeriv ℝ n (fun y => (reduce ω).1 y i j) x‖ ≤ matrixBound D n := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (clockDensity ω) :=
    (contDiff_const.mul hs.1.2).exp
  apply (norm_iteratedFDeriv_mul_le hc (hs.1.1 i j) x
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).trans
  exact Finset.sum_le_sum fun k _ => mul_le_mul
    (mul_le_mul_of_nonneg_left (clock_derivatives D ω hr hs k x) (Nat.cast_nonneg _))
    ((physical_derivatives D ω hr hs (n - k) x).2 i j) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (clockBound_nonneg D k))

private lemma euclidean_matrix_bound {d : ℕ} (A : Mat d) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i j, |A i j| ≤ C) (ξ : Vec d) :
    euclideanNorm (A.mulVec ξ) ≤ ((d : ℝ) + 1) * (d * C) * euclideanNorm ξ := by
  apply (euclideanNorm_le_dimension_mul_norm _).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) (Real.sqrt_nonneg _)) |>.mpr
  intro i
  calc
    ‖(A.mulVec ξ) i‖ ≤ ∑ j, |A i j| * |ξ j| := by
      simpa only [Matrix.mulVec, dotProduct, Real.norm_eq_abs, abs_mul] using
        (norm_sum_le (s := Finset.univ) (f := fun j => A i j * ξ j))
    _ ≤ ∑ _ : Fin d, C * euclideanNorm ξ := Finset.sum_le_sum fun j _ =>
      mul_le_mul (hA i j) (Regeneration.coordinate_abs_le_euclideanNorm ξ j)
        (abs_nonneg _) hC
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact (mul_assoc (d : ℝ) C (euclideanNorm ξ)).symm

private lemma multilinear_euclidean_bound {d k : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin k => Vec d) ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hL : ‖L‖ ≤ C) (v : Fin k → Vec d) :
    |L v| ≤ C * ∏ j, euclideanNorm (v j) := by
  exact (L.le_opNorm v).trans (mul_le_mul hL
    (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => norm_le_euclidean _))
    (Finset.prod_nonneg fun j _ => norm_nonneg _) hC)

private lemma reduced_smooth_bounds {d : ℕ} (D : StructuralData d) (ω : FieldPair d)
    (hr : IsRegular D.ellipticity ω) (hs : IsSmoothWithBounds D.derivativeBound ω) :
    IsSmoothWithBounds (fun k => ((d : ℝ) + 1) * (d * matrixBound D k) +
      clockBound D k + 1) (reduce ω) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (clockDensity ω) :=
    (contDiff_const.mul hs.1.2).exp
  refine ⟨⟨fun i j => hc.mul (hs.1.1 i j), hc⟩, ?_⟩
  intro k _hk
  refine ⟨((d : ℝ) + 1) * (d * matrixBound D k), clockBound D k,
    mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (matrixBound_nonneg D k)),
    clockBound_nonneg D k, by linarith, ?_, ?_⟩
  · intro x v ξ
    have hp : 0 ≤ ∏ j, euclideanNorm (v j) :=
      Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
    have he (i j : Fin d) :
        |iteratedFDeriv ℝ k (fun y => (reduce ω).1 y i j) x v| ≤
          matrixBound D k * ∏ j, euclideanNorm (v j) := by
      exact multilinear_euclidean_bound
        (iteratedFDeriv ℝ k (fun y => (reduce ω).1 y i j) x)
        (matrixBound_nonneg D k) (reduced_entry_derivatives D ω hr hs k x i j) v
    have hm := euclidean_matrix_bound
      (fun i j => iteratedFDeriv ℝ k (fun y => (reduce ω).1 y i j) x v)
      (mul_nonneg (matrixBound_nonneg D k) hp) he ξ
    simpa only [mul_assoc] using hm
  · intro x v
    exact multilinear_euclidean_bound (iteratedFDeriv ℝ k (clockDensity ω) x)
      (clockBound_nonneg D k) (clock_derivatives D ω hr hs k x) v

/-- The actual time change preserves uniform bounds at every derivative order,
with a deterministic sequence chosen before the environment law.
The graph interface retains its prescribed dependency; this deterministic proof
already follows from regularity and smoothness of the physical fields. -/
@[nolint unusedArguments]
theorem node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    (_hdeps : node_eq_u2E_reduced_u2D_boundsStmt) :
    node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt := by
  intro d D
  refine ⟨fun k => ((d : ℝ) + 1) * (d * matrixBound D k) + clockBound D k + 1,
    ?_, ?_⟩
  · intro k _hk
    have hm := matrixBound_nonneg D k
    have hc := clockBound_nonneg D k
    positivity
  · intro Q hs
    apply (Probability.measurableEmbedding_reduce d).ae_map_iff.mpr
    filter_upwards [Q.regular, hs] with ω hr hω
    exact reduced_smooth_bounds D ω hr hω

end EinsteinFull.Blueprint
