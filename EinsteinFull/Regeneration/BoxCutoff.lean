import PDEFoundation.Sobolev.Cutoff.Cube

/-!
# Cutoffs for coordinate boxes

A product of one-dimensional transitions gives a smooth cutoff with an
independent transition width in every coordinate.
-/

open Filter Set PDE

namespace EinsteinFull.Regeneration

/-- The closed inset of a coordinate box by specified positive widths. -/
def boxCutoffInset {d : ℕ} (a b δ : PDE.Vec d) : Set (PDE.Vec d) :=
  Set.pi Set.univ (fun j => Icc (a j + δ j) (b j - δ j))

/-- The closed box containing the support of the product cutoff. -/
def boxCutoffSupport {d : ℕ} (a b δ : PDE.Vec d) : Set (PDE.Vec d) :=
  Set.pi Set.univ (fun j => Icc (a j + δ j / 2) (b j - δ j / 2))

/-- The transition in one coordinate. -/
noncomputable def boxCutoffFactor {d : ℕ} (a b δ : PDE.Vec d) (j : Fin d)
    (x : PDE.Vec d) : ℝ := PDE.cubeCutoffScalarFactor (a j) (b j) (δ j) (x j)

/-- The product of one-dimensional box transitions. -/
noncomputable def boxCutoff {d : ℕ} (a b δ : PDE.Vec d) (x : PDE.Vec d) : ℝ :=
  ∏ j : Fin d, boxCutoffFactor a b δ j x

private theorem boxCutoffFactor_smooth {d : ℕ} (a b δ : PDE.Vec d) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (boxCutoffFactor a b δ j) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (PDE.cubeCutoffScalarFactor (a j) (b j) (δ j) ∘ fun x : PDE.Vec d => x j)
  exact (PDE.cubeCutoffScalarFactor_smooth _ _ _).comp (contDiff_apply ℝ ℝ j)

/-- The box cutoff is smooth. -/
theorem boxCutoff_smooth {d : ℕ} (a b δ : PDE.Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (boxCutoff a b δ) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∏ j ∈ Finset.univ, boxCutoffFactor a b δ j x)
  exact contDiff_prod fun j _ => boxCutoffFactor_smooth a b δ j

/-- The product cutoff takes values between zero and one. -/
theorem boxCutoff_mem_Icc {d : ℕ} (a b δ : PDE.Vec d) (x : PDE.Vec d) :
    boxCutoff a b δ x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg fun j _ => PDE.cubeCutoffScalarFactor_nonneg _ _ _ _
  · exact Finset.prod_le_one₀
      (fun j _ => PDE.cubeCutoffScalarFactor_nonneg _ _ _ _)
      (fun j _ => PDE.cubeCutoffScalarFactor_le_one _ _ _ _)

/-- The support of the product cutoff lies inside its closed support box. -/
theorem boxCutoff_support_subset {d : ℕ} {a b δ : PDE.Vec d}
    (hδ : ∀ j, 0 < δ j) : Function.support (boxCutoff a b δ) ⊆ boxCutoffSupport a b δ := by
  intro x hx j _
  have hprod : (∏ k : Fin d, PDE.cubeCutoffScalarFactor (a k) (b k) (δ k) (x k)) ≠ 0 := hx
  have hj : PDE.cubeCutoffScalarFactor (a j) (b j) (δ j) (x j) ≠ 0 := by
    intro hz
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ j) hz)
  constructor
  · by_contra hn
    have h := PDE.axisBoxLowerTransition_eq_zero_of_le_add_half_delta
      (a := a j) (δ := δ j) (t := x j) (hδ j) (le_of_not_ge hn)
    exact hj (by simp [PDE.cubeCutoffScalarFactor, h])
  · by_contra hn
    have h := PDE.axisBoxUpperTransition_eq_zero_of_sub_half_delta_le
      (b := b j) (δ := δ j) (t := x j) (hδ j) (le_of_not_ge hn)
    exact hj (by simp [PDE.cubeCutoffScalarFactor, h])

/-- The support box is compact. -/
theorem boxCutoffSupport_isCompact {d : ℕ} (a b δ : PDE.Vec d) :
    IsCompact (boxCutoffSupport a b δ) := by
  exact isCompact_univ_pi fun _ => isCompact_Icc

/-- The topological support of the cutoff is inside the open box. -/
theorem boxCutoff_tsupport_subset {d : ℕ} {a b δ : PDE.Vec d}
    (hδ : ∀ j, 0 < δ j) : tsupport (boxCutoff a b δ) ⊆ PDE.axisBox a b := by
  have hclosed : IsClosed (boxCutoffSupport a b δ) := (boxCutoffSupport_isCompact a b δ).isClosed
  have htsub : tsupport (boxCutoff a b δ) ⊆ boxCutoffSupport a b δ :=
    closure_minimal (boxCutoff_support_subset hδ) hclosed
  intro x hx j _
  have hj := htsub hx j (Set.mem_univ j)
  change a j + δ j / 2 ≤ x j ∧ x j ≤ b j - δ j / 2 at hj
  change a j < x j ∧ x j < b j
  constructor <;> linarith [hδ j, hj.1, hj.2]

/-- The cutoff is one throughout the closed inset. -/
theorem boxCutoff_eq_one {d : ℕ} {a b δ : PDE.Vec d} (hδ : ∀ j, 0 < δ j)
    {x : PDE.Vec d} (hx : x ∈ boxCutoffInset a b δ) : boxCutoff a b δ x = 1 := by
  unfold boxCutoff
  apply Finset.prod_eq_one
  intro j _
  have hj := hx j (Set.mem_univ j)
  change a j + δ j ≤ x j ∧ x j ≤ b j - δ j at hj
  have hl := PDE.axisBoxLowerTransition_eq_one_of_add_delta_le (hδ j) hj.1
  have hu := PDE.axisBoxUpperTransition_eq_one_of_add_delta_le
    (b := b j) (δ := δ j) (t := x j) (hδ j) (by linarith [hj.2])
  simp [boxCutoffFactor, PDE.cubeCutoffScalarFactor, hl, hu]

private theorem boxCutoffFactor_fderiv {d : ℕ} (a b δ : PDE.Vec d)
    (i j : Fin d) (x : PDE.Vec d) :
    (fderiv ℝ (boxCutoffFactor a b δ i) x)
        (PDE.basisVec j) =
      deriv (PDE.cubeCutoffScalarFactor (a i) (b i) (δ i)) (x i) * PDE.basisVec j i := by
  have hsmooth := PDE.cubeCutoffScalarFactor_smooth (a i) (b i) (δ i)
  have hdiff := (hsmooth.differentiable (by simp)).differentiableAt (x := x i)
  have hcoord : HasFDerivAt (fun y : PDE.Vec d => y i)
      ((ContinuousLinearMap.proj i) : PDE.Vec d →L[ℝ] ℝ) x := hasFDerivAt_apply (𝕜 := ℝ) i x
  have hcomp := hdiff.hasDerivAt.comp_hasFDerivAt x hcoord
  change (fderiv ℝ (PDE.cubeCutoffScalarFactor (a i) (b i) (δ i) ∘
    fun y : PDE.Vec d => y i) x) (PDE.basisVec j) = _
  rw [hcomp.fderiv]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- Each gradient coordinate is controlled by its own transition width. -/
theorem boxCutoff_gradient_coord_le {d : ℕ} {a b δ : PDE.Vec d}
    (hδ : ∀ j, 0 < δ j) (j : Fin d) (x : PDE.Vec d) :
    |PDE.classicalGradient (boxCutoff a b δ) x j| ≤ 32 / δ j := by
  rw [PDE.classicalGradient_apply]
  change |(fderiv ℝ (fun y : PDE.Vec d =>
    ∏ i ∈ Finset.univ, boxCutoffFactor a b δ i y) x)
      (PDE.basisVec j)| ≤ 32 / δ j
  rw [fderiv_finsetProd (fun i _ =>
    ((boxCutoffFactor_smooth a b δ i).differentiable (by simp) x))]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp only [boxCutoffFactor_fderiv, PDE.basisVec_apply, ite_true, mul_one]
    rw [abs_mul, abs_of_nonneg]
    · calc
        (∏ i ∈ Finset.univ.erase j, PDE.cubeCutoffScalarFactor (a i) (b i) (δ i) (x i)) *
            |deriv (PDE.cubeCutoffScalarFactor (a j) (b j) (δ j)) (x j)| ≤
          1 * (32 / δ j) := by
            apply mul_le_mul
            · exact Finset.prod_le_one₀
                (fun i _ => PDE.cubeCutoffScalarFactor_nonneg _ _ _ _)
                (fun i _ => PDE.cubeCutoffScalarFactor_le_one _ _ _ _)
            · exact PDE.abs_deriv_cubeCutoffScalarFactor_le (hδ j)
            · exact abs_nonneg _
            · norm_num
      _ = 32 / δ j := one_mul _
    · exact Finset.prod_nonneg fun i _ => PDE.cubeCutoffScalarFactor_nonneg _ _ _ _
  · intro i hi hij
    rw [boxCutoffFactor_fderiv]
    simp [PDE.basisVec_apply, hij]
  · simp

/-- A coordinate derivative vanishes inside that coordinate's inset. -/
theorem boxCutoff_gradient_coord_eq_zero_of_interior {d : ℕ} {a b δ : PDE.Vec d}
    (hδ : ∀ j, 0 < δ j) (j : Fin d) (x : PDE.Vec d)
    (hx : a j + δ j < x j ∧ x j < b j - δ j) :
    PDE.classicalGradient (boxCutoff a b δ) x j = 0 := by
  have hevent : PDE.cubeCutoffScalarFactor (a j) (b j) (δ j) =ᶠ[nhds (x j)]
      fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    have hl := PDE.axisBoxLowerTransition_eq_one_of_add_delta_le
      (a := a j) (δ := δ j) (t := t) (hδ j) ht.1.le
    have hu := PDE.axisBoxUpperTransition_eq_one_of_add_delta_le
      (b := b j) (δ := δ j) (t := t) (hδ j) (by linarith [ht.2])
    simp [PDE.cubeCutoffScalarFactor, hl, hu]
  have hderiv : deriv (PDE.cubeCutoffScalarFactor (a j) (b j) (δ j)) (x j) = 0 := by
    rw [hevent.deriv_eq, deriv_const]
  rw [PDE.classicalGradient_apply]
  change (fderiv ℝ (fun y : PDE.Vec d =>
    ∏ i ∈ Finset.univ, boxCutoffFactor a b δ i y) x) (PDE.basisVec j) = 0
  rw [fderiv_finsetProd (fun i _ =>
    ((boxCutoffFactor_smooth a b δ i).differentiable (by simp) x))]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp only [boxCutoffFactor_fderiv, PDE.basisVec_apply, ite_true, mul_one, hderiv, mul_zero]
  · intro i hi hij
    rw [boxCutoffFactor_fderiv]
    simp [PDE.basisVec_apply, hij]
  · simp

/-- A smooth coordinate-box cutoff with a separate scale in each direction. -/
noncomputable def quantitativeBoxCutoff {d : ℕ} (a b δ : PDE.Vec d) (hδ : ∀ j, 0 < δ j) :
    PDE.QuantitativeSmoothCutoff (boxCutoffInset a b δ) (PDE.axisBox a b)
      (∑ j : Fin d, 32 / δ j) where
  toFun := boxCutoff a b δ
  smooth := boxCutoff_smooth a b δ
  hasCompactSupport := HasCompactSupport.of_support_subset_isCompact
    (boxCutoffSupport_isCompact a b δ) (boxCutoff_support_subset hδ)
  tsupport_subset := boxCutoff_tsupport_subset hδ
  nonneg := fun x => (boxCutoff_mem_Icc a b δ x).1
  le_one := fun x => (boxCutoff_mem_Icc a b δ x).2
  eq_one_on_inner := fun _ hx => boxCutoff_eq_one hδ hx
  gradient_bound := fun x => (PDE.vecEuclideanNorm_le_sum_abs _).trans
    (Finset.sum_le_sum fun j _ => boxCutoff_gradient_coord_le hδ j x)

end EinsteinFull.Regeneration
