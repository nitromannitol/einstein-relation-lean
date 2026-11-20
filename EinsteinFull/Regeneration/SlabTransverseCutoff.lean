import EinsteinFull.Regeneration.BoxTransverseCollar

/-!
# Transverse cutoffs for slabs

The force interval is enlarged before applying a box cutoff. On the original
slab the cutoff only varies in transverse directions.
-/

open Set PDE

namespace EinsteinFull.Regeneration

/-- The lower endpoint is enlarged only in the force coordinate. -/
def slabCutoffLower {d : ℕ} (i : Fin d) (a : PDE.Vec d) : PDE.Vec d :=
  fun j => if j = i then a j - 2 else a j

/-- The upper endpoint is enlarged only in the force coordinate. -/
def slabCutoffUpper {d : ℕ} (i : Fin d) (b : PDE.Vec d) : PDE.Vec d :=
  fun j => if j = i then b j + 2 else b j

/-- Unit force width and prescribed transverse width for the cutoff. -/
def slabCutoffWidths {d : ℕ} (i : Fin d) (w : ℝ) : PDE.Vec d :=
  fun j => if j = i then 1 else w

/-- The force-extended, compactly supported product cutoff. -/
noncomputable def slabTransverseCutoff {d : ℕ} (i : Fin d) (a b : PDE.Vec d)
    (w : ℝ) (hw : 0 < w) :
    PDE.QuantitativeSmoothCutoff
      (boxCutoffInset (slabCutoffLower i a) (slabCutoffUpper i b) (slabCutoffWidths i w))
      (PDE.axisBox (slabCutoffLower i a) (slabCutoffUpper i b))
      (∑ j : Fin d, 32 / slabCutoffWidths i w j) :=
  quantitativeBoxCutoff _ _ _ (fun j => by
    by_cases h : j = i <;> simp [slabCutoffWidths, h, hw])

/-- The force derivative vanishes throughout the original slab box. -/
theorem slabTransverseCutoff_force_grad_zero {d : ℕ} (i : Fin d) (a b : PDE.Vec d)
    (w : ℝ) (hw : 0 < w) {x : PDE.Vec d} (hx : x ∈ PDE.axisBox a b) :
    PDE.classicalGradient (slabTransverseCutoff i a b w hw).toFun x i = 0 := by
  have hi := hx i (Set.mem_univ i)
  change PDE.classicalGradient
    (boxCutoff (slabCutoffLower i a) (slabCutoffUpper i b) (slabCutoffWidths i w)) x i = 0
  have hwidth : ∀ j, 0 < slabCutoffWidths i w j := by
    intro j
    by_cases h : j = i <;> simp [slabCutoffWidths, h, hw]
  apply boxCutoff_gradient_coord_eq_zero_of_interior hwidth i x
  simp only [slabCutoffLower, slabCutoffUpper, slabCutoffWidths, ite_true]
  constructor <;> linarith [hi.1, hi.2]

/-- The cutoff vanishes near every transverse face. -/
theorem slabTransverseCutoff_lateral_zero {d : ℕ} (i : Fin d) (a b : PDE.Vec d)
    (w : ℝ) (hw : 0 < w) (j : Fin d) (hji : j ≠ i) (x : PDE.Vec d)
    (hx : x ∈ boxFaceCollars a b j (w / 2)) : slabTransverseCutoff i a b w hw x = 0 := by
  change boxCutoff (slabCutoffLower i a) (slabCutoffUpper i b) (slabCutoffWidths i w) x = 0
  have hwidth : ∀ k, 0 < slabCutoffWidths i w k := by
    intro k
    by_cases h : k = i <;> simp [slabCutoffWidths, h, hw]
  apply boxCutoff_eq_zero_of_near_face hwidth j x
  simpa [boxFaceCollars, slabCutoffLower, slabCutoffUpper, slabCutoffWidths, hji] using hx

/-- On the original box, the cutoff is one on the transverse inset. -/
theorem slabTransverseCutoff_eq_one {d : ℕ} (i : Fin d) (a b : PDE.Vec d)
    (w : ℝ) (hw : 0 < w) {x : PDE.Vec d} (hx : x ∈ PDE.axisBox a b)
    (hinset : ∀ j : Fin d, j ≠ i → a j + w ≤ x j ∧ x j ≤ b j - w) :
    slabTransverseCutoff i a b w hw x = 1 := by
  apply (slabTransverseCutoff i a b w hw).eq_one_on_inner
  intro j _
  by_cases hji : j = i
  · subst j
    have hi := hx i (Set.mem_univ i)
    simp only [slabCutoffLower, slabCutoffUpper, slabCutoffWidths, ite_true]
    constructor <;> linarith [hi.1, hi.2]
  · simpa [slabCutoffLower, slabCutoffUpper, slabCutoffWidths, hji] using hinset j hji

/-- The cutoff gradient on the original box has the transverse-width scale. -/
theorem slabTransverseCutoff_gradient_le {d : ℕ} (i : Fin d) (a b : PDE.Vec d)
    (w : ℝ) (hw : 0 < w) {x : PDE.Vec d} (hx : x ∈ PDE.axisBox a b) :
    PDE.vecEuclideanNorm (PDE.classicalGradient (slabTransverseCutoff i a b w hw).toFun x) ≤
      (32 * (d : ℝ)) / w := by
  have hcoord (j : Fin d) :
      |PDE.classicalGradient (slabTransverseCutoff i a b w hw).toFun x j| ≤ 32 / w := by
    by_cases hji : j = i
    · subst j
      rw [slabTransverseCutoff_force_grad_zero i a b w hw hx, abs_zero]
      positivity
    · have h := boxCutoff_gradient_coord_le (a := slabCutoffLower i a)
        (b := slabCutoffUpper i b) (δ := slabCutoffWidths i w)
        (fun k => by by_cases h : k = i <;> simp [slabCutoffWidths, h, hw]) j x
      change |PDE.classicalGradient
        (boxCutoff (slabCutoffLower i a) (slabCutoffUpper i b) (slabCutoffWidths i w)) x j| ≤ 32 / w
      simpa only [slabCutoffWidths, hji, ite_false] using h
  calc
    _ ≤ ∑ j : Fin d, |PDE.classicalGradient (slabTransverseCutoff i a b w hw).toFun x j| :=
      PDE.vecEuclideanNorm_le_sum_abs _
    _ ≤ ∑ _j : Fin d, 32 / w := Finset.sum_le_sum (fun j _ => hcoord j)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end EinsteinFull.Regeneration
