import EinsteinRelation.Environment.Basic
import EinsteinRelation.Environment.Reduction
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Euclidean Lipschitz fields and their actual almost-everywhere derivatives

Source `paper/main.tex:68–80,194–207,240–252`. The source Lipschitz bounds use the
explicit Euclidean norm. A proved dimension-dependent comparison transports those
bounds to the ambient coordinate topology, solely to apply pinned Rademacher.
The original matrix operator bound controls each actual entry. Differentiability
of the literal physical and reduced fields is then proved Lebesgue-almost
everywhere, and exercised under the actual environment law.

No norm instance, coefficient symmetry or dimension assumption is changed.
This is the classical almost-everywhere side of the generator bridge; the weak
representative/occupation and horizontal-generator identifications remain separate.
-/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation

/-- Explicit comparison with the ambient coordinate norm, leaving the source norm intact. -/
theorem euclideanNorm_le_dimension_mul_norm {d : ℕ} (x : Vec d) :
    euclideanNorm x ≤ ((d : ℝ) + 1) * ‖x‖ := by
  unfold euclideanNorm euclideanSq dot
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hi (i : Fin d) : x i * x i ≤ ‖x‖ ^ 2 := by
    have hs := (sq_le_sq₀ (norm_nonneg (x i)) (norm_nonneg x)).mpr (norm_le_pi_norm x i)
    rw [Real.norm_eq_abs, sq_abs] at hs
    simpa only [pow_two] using hs
  have hd : (d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
    nlinarith only [Nat.cast_nonneg (α := ℝ) d]
  calc
    (∑ i, x i * x i) ≤ ∑ _ : Fin d, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = (d : ℝ) * ‖x‖ ^ 2 := by simp
    _ ≤ ((d : ℝ) + 1) ^ 2 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hd (sq_nonneg _)
    _ = (((d : ℝ) + 1) * ‖x‖) ^ 2 := by ring

/-- A Euclidean Lipschitz bound yields a topological Lipschitz constant depending only on d and L. -/
theorem lipschitzWith_of_euclidean_bound {d : ℕ} {F : Vec d → ℝ} (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ x y, |F x - F y| ≤ L * euclideanNorm (x - y)) :
    LipschitzWith ⟨L * ((d : ℝ) + 1), by positivity⟩ F := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  exact (hF x y).trans (by
    change L * euclideanNorm (x-y) ≤ (L * ((d : ℝ) + 1)) * ‖x-y‖
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (euclideanNorm_le_dimension_mul_norm (x-y)) hL)

 private theorem coordinate_abs_le_euclidean {d : ℕ} (x : Vec d) (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  have hsq : x i * x i ≤ ∑ j, x j * x j :=
    Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
      (Finset.mem_univ i)
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact hsq

 private theorem euclideanNorm_unitVector {d : ℕ} (i : Fin d) :
    euclideanNorm (unitVector i) = 1 := by
  change Real.sqrt (dotProduct (Pi.single i (1 : ℝ)) (Pi.single i 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

/-- Each matrix entry obeys the given Euclidean operator Lipschitz constant. -/
theorem IsOperatorLipschitz.entry_bound {d : ℕ} {a : Vec d → Mat d} {L : ℝ}
    (ha : IsOperatorLipschitz L a) (i j : Fin d) (x y : Vec d) :
    |a x i j - a y i j| ≤ L * euclideanNorm (x-y) := by
  have hc := coordinate_abs_le_euclidean ((a x - a y).mulVec (unitVector j)) i
  have hv : ((a x-a y).mulVec (unitVector j)) i = a x i j-a y i j := by
    change dotProduct (fun k => (a x-a y) i k) (Pi.single j 1) = _
    rw [dotProduct_single, mul_one]
    rfl
  simpa only [hv, euclideanNorm_unitVector, mul_one] using (hc.trans (ha x y (unitVector j)))

/-- Actual entrywise Rademacher derivatives assemble to the matrix derivative almost everywhere. -/
theorem IsOperatorLipschitz.ae_differentiableAt {d : ℕ} {a : Vec d → Mat d} {L : ℝ}
    (hL : 0 ≤ L) (ha : IsOperatorLipschitz L a) :
    ∀ᵐ x : Vec d ∂volume, DifferentiableAt ℝ a x := by
  have he : ∀ i j : Fin d, ∀ᵐ x : Vec d ∂volume,
      DifferentiableAt ℝ (fun y => a y i j) x := fun i j =>
    (lipschitzWith_of_euclidean_bound L hL (ha.entry_bound i j)).ae_differentiableAt
  filter_upwards [ae_all_iff.2 (fun i => ae_all_iff.2 (he i))] with x hx
  exact differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j => hx i j

/-- The physical coefficient and potential are differentiable at almost every spatial point. -/
theorem IsRegular.ae_differentiableAt_fields {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hL : 0 ≤ L) (hω : IsRegular L ω) :
    ∀ᵐ x : Vec d ∂volume, DifferentiableAt ℝ (fun y => ω.1 y) x ∧
      DifferentiableAt ℝ (fun y => ω.2 y) x := by
  filter_upwards [hω.2.2.1.ae_differentiableAt hL,
    (lipschitzWith_of_euclidean_bound L hL hω.2.2.2).ae_differentiableAt] with x ha hV
  exact ⟨ha, hV⟩

/-- The actual exponential clock and scalar-multiplied matrix share a full-measure differentiability set. -/
theorem IsRegular.ae_differentiableAt_reduction {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hL : 0 ≤ L) (hω : IsRegular L ω) :
    ∀ᵐ x : Vec d ∂volume, DifferentiableAt ℝ (clockDensity ω) x ∧
      DifferentiableAt ℝ (reducedCoefficient ω) x := by
  filter_upwards [hω.ae_differentiableAt_fields hL] with x hx
  have hμ : DifferentiableAt ℝ (clockDensity ω) x := by
    exact (hx.2.const_mul (-2)).exp
  refine ⟨hμ, ?_⟩
  change DifferentiableAt ℝ (fun y i j => clockDensity ω y * ω.1 y i j) x
  refine differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j => ?_
  exact hμ.mul ((differentiableAt_pi.mp ((differentiableAt_pi.mp hx.1) i)) j)

/-- Real consumer for the physical law, retaining both environment and spatial almost-everywhere qualifiers. -/
theorem EnvironmentLaw.ae_ae_differentiableAt_reduction {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ x : Vec d ∂volume,
      DifferentiableAt ℝ (clockDensity ω) x ∧ DifferentiableAt ℝ (reducedCoefficient ω) x := by
  filter_upwards [Q.regular] with ω hω
  exact hω.ae_differentiableAt_reduction (le_trans zero_le_one Q.ellipticity_parameter)

end EinsteinRelation
