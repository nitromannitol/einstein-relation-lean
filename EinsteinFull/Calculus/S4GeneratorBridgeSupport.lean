import EinsteinFull.External.Draft.StroockVaradhanWellPosed
import EinsteinRelation.Calculus.Generator
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Divergence-form generators versus the second-order operator `½ Σ aᵢⱼ ∂ᵢ∂ⱼ + Σ bᵢ ∂ᵢ`

Support for the bridge between the vendor generators `physicalGenerator`, `reducedGenerator`
(written with the divergence of the flux `A ∇ f`, with `fderiv`-junk at non-differentiability
points of the coefficient) and the textbook operator `svGenerator`.

The identity `generator = svGenerator` holds exactly at the points where all entries of the
coefficient are differentiable (for a Lipschitz coefficient: Lebesgue-almost every point),
and not everywhere: at a non-differentiability point the vendor generator contains the junk
value `0` of `fderiv`.
-/

open scoped BigOperators NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The first-order part `½ Σₖ ∂ₖ Aₖⱼ` produced by expanding `div (A ∇ f)`. -/
noncomputable def matrixDivDrift {d : ℕ} (A : Vec d → Mat d) (y : Vec d) : Vec d :=
  fun j => (1 / 2 : ℝ) * ∑ k, coordinateDerivative k (fun z => A z k j) y

/-- The drift `½ Σₖ ∂ₖ Aₖⱼ + lam (A e_i)ⱼ` of `½ div (A ∇ ·) + lam ⟨A e_i, ∇ ·⟩`. -/
noncomputable def forcedDrift {d : ℕ} (A : Vec d → Mat d) (i : Fin d) (lam : ℝ)
    (y : Vec d) : Vec d :=
  fun j => matrixDivDrift A y j + lam * (A y).mulVec (unitVector i) j

theorem sum_forcedDrift_aux {d : ℕ} (C m g : Fin d → ℝ) (lam : ℝ) :
    ∑ j, ((1 / 2 : ℝ) * C j + lam * m j) * g j =
      (1 / 2 : ℝ) * ∑ j, C j * g j + lam * ∑ j, m j * g j := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Product rule: at a point where all entries of `A` are differentiable, the divergence-form
generator is the second-order operator with drift `forcedDrift`. -/
theorem generator_eq_svGenerator_of_differentiableAt {d : ℕ} (A : Vec d → Mat d)
    (i : Fin d) (lam : ℝ) {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) {x : Vec d}
    (hA : ∀ k j, DifferentiableAt ℝ (fun z => A z k j) x) :
    (1 / 2 : ℝ) * divergence (fun y => (A y).mulVec (gradient f y)) x +
        lam * dot ((A x).mulVec (unitVector i)) (gradient f x) =
      External.Draft.svGenerator A (forcedDrift A i lam) f x := by
  have hf1 : ∀ j : Fin d,
      DifferentiableAt ℝ (fun y => fderiv ℝ f y (unitVector j)) x := by
    intro j
    have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (le_of_eq one_add_one_eq_two)
    have h2 : ContDiff ℝ 1 (fun y => fderiv ℝ f y (unitVector j)) :=
      h1.clm_apply contDiff_const
    exact (h2.differentiable one_ne_zero) x
  have hdiv : ∀ k : Fin d,
      coordinateDerivative k (fun y => (A y).mulVec (gradient f y) k) x =
        ∑ j, (A x k j * fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector k) +
          fderiv ℝ f x (unitVector j) * fderiv ℝ (fun z => A z k j) x (unitVector k)) := by
    intro k
    have h : HasFDerivAt (fun y => ∑ j, A y k j * fderiv ℝ f y (unitVector j))
        (∑ j, (A x k j • fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x +
          fderiv ℝ f x (unitVector j) • fderiv ℝ (fun z => A z k j) x)) x := by
      refine HasFDerivAt.fun_sum fun j _ => ?_
      exact (hA k j).hasFDerivAt.fun_mul (hf1 j).hasFDerivAt
    have e : (fun y => (A y).mulVec (gradient f y) k) =
        fun y => ∑ j, A y k j * fderiv ℝ f y (unitVector j) := rfl
    unfold coordinateDerivative
    rw [e, h.fderiv]
    simp only [sum_apply, add_apply, smul_apply, smul_eq_mul]
  have hS2 : ∑ k, ∑ j, fderiv ℝ f x (unitVector j) *
        fderiv ℝ (fun z => A z k j) x (unitVector k) =
      ∑ j, (∑ k, fderiv ℝ (fun z => A z k j) x (unitVector k)) *
        fderiv ℝ f x (unitVector j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hd2 : divergence (fun y => (A y).mulVec (gradient f y)) x =
      (∑ k, ∑ j, A x k j *
          fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector k)) +
        ∑ j, (∑ k, fderiv ℝ (fun z => A z k j) x (unitVector k)) *
          fderiv ℝ f x (unitVector j) := by
    rw [← hS2, ← Finset.sum_add_distrib]
    unfold divergence
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hdiv k, Finset.sum_add_distrib]
  simp only [External.Draft.svGenerator, forcedDrift, matrixDivDrift]
  rw [hd2, sum_forcedDrift_aux]
  simp only [coordinateDerivative, gradient, dot]
  ring

theorem measurable_matrixDivDrift {d : ℕ} (A : Vec d → Mat d) :
    Measurable (matrixDivDrift A) := by
  refine measurable_pi_iff.2 fun j => ?_
  unfold matrixDivDrift coordinateDerivative
  exact (Finset.measurable_sum _ fun k _ =>
    measurable_fderiv_apply_const ℝ (fun z => A z k j) (unitVector k)).const_mul _

theorem measurable_forcedDrift {d : ℕ} (A : Vec d → Mat d) (hA : Continuous A)
    (i : Fin d) (lam : ℝ) : Measurable (forcedDrift A i lam) := by
  refine measurable_pi_iff.2 fun j => ?_
  have h1 : Measurable fun y => matrixDivDrift A y j :=
    (measurable_pi_apply j).comp (measurable_matrixDivDrift A)
  have h2 : Measurable fun y => (A y).mulVec (unitVector i) j := by
    have e : (fun y => (A y).mulVec (unitVector i) j) = fun y => A y j i := by
      funext y
      simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
    rw [e]
    exact (hA.matrix_elem j i).measurable
  exact h1.add (h2.const_mul lam)

theorem abs_matrixDivDrift_le {d : ℕ} (A : Vec d → Mat d) {L : ℝ≥0}
    (hL : ∀ k j, LipschitzWith L (fun z => A z k j)) (y : Vec d) (j : Fin d) :
    |matrixDivDrift A y j| ≤ (1 / 2 : ℝ) * (d * L) := by
  have hk : ∀ k : Fin d, |coordinateDerivative k (fun z => A z k j) y| ≤ L := by
    intro k
    have h1 : ‖fderiv ℝ (fun z => A z k j) y‖ ≤ L := norm_fderiv_le_of_lipschitz ℝ (hL k j)
    have h2 : ‖unitVector (d := d) k‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => ?_
      by_cases h : l = k <;> simp [unitVector, Pi.single_apply, h]
    calc |coordinateDerivative k (fun z => A z k j) y|
        = ‖fderiv ℝ (fun z => A z k j) y (unitVector k)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (fun z => A z k j) y‖ * ‖unitVector (d := d) k‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L : ℝ) * 1 := mul_le_mul h1 h2 (norm_nonneg _) L.coe_nonneg
      _ = L := mul_one _
  unfold matrixDivDrift
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc |∑ k, coordinateDerivative k (fun z => A z k j) y|
      ≤ ∑ k, |coordinateDerivative k (fun z => A z k j) y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, (L : ℝ) := Finset.sum_le_sum fun k _ => hk k
    _ = d * L := by simp

theorem abs_forcedDrift_le {d : ℕ} (A : Vec d → Mat d) {L : ℝ≥0}
    (hL : ∀ k j, LipschitzWith L (fun z => A z k j)) {M : ℝ}
    (hM : ∀ y k j, |A y k j| ≤ M) (i : Fin d) (lam : ℝ) (y : Vec d) (j : Fin d) :
    |forcedDrift A i lam y j| ≤ (1 / 2 : ℝ) * (d * L) + |lam| * M := by
  have h1 := abs_matrixDivDrift_le A hL y j
  have e : (A y).mulVec (unitVector i) j = A y j i := by
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
  unfold forcedDrift
  calc |matrixDivDrift A y j + lam * (A y).mulVec (unitVector i) j|
      ≤ |matrixDivDrift A y j| + |lam * (A y).mulVec (unitVector i) j| := abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) * (d * L) + |lam| * M := by
        rw [abs_mul, e]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left (hM y j i) (abs_nonneg _))

end EinsteinFull
