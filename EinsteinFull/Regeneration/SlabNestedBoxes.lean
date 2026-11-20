import EinsteinFull.Regeneration.SlabCutoffPointwise

/-!
# Nested boxes for a slab cutoff

Shrinking only the transverse sides gives the box on which the comparison
cutoff is identically one.
-/

open Set PDE

namespace EinsteinFull.Regeneration

/-- The lower endpoint of the transverse inset. -/
def slabInsetLower {d : ℕ} (i : Fin d) (a : PDE.Vec d) (w : ℝ) : PDE.Vec d :=
  fun j => if j = i then a j else a j + w

/-- The upper endpoint of the transverse inset. -/
def slabInsetUpper {d : ℕ} (i : Fin d) (b : PDE.Vec d) (w : ℝ) : PDE.Vec d :=
  fun j => if j = i then b j else b j - w

/-- Shrinking the transverse sides gives a subset of the outer box. -/
theorem slabInsetBox_subset {d : ℕ} (i : Fin d) (a b : PDE.Vec d)
    (w : ℝ) (hw : 0 ≤ w) :
    PDE.axisBox (slabInsetLower i a w) (slabInsetUpper i b w) ⊆ PDE.axisBox a b := by
  intro x hx j hj
  have h := hx j hj
  by_cases hji : j = i
  · simpa [slabInsetLower, slabInsetUpper, hji] using h
  · simp only [slabInsetLower, slabInsetUpper, hji, ite_false] at h
    constructor <;> linarith [h.1, h.2]

/-- The transverse cutoff is one everywhere on the inset box. -/
theorem slabTransverseCutoff_eq_one_on_inset {d : ℕ} (i : Fin d) (a b : PDE.Vec d)
    (w : ℝ) (hw : 0 < w) {x : PDE.Vec d}
    (hx : x ∈ PDE.axisBox (slabInsetLower i a w) (slabInsetUpper i b w)) :
    slabTransverseCutoff i a b w hw x = 1 := by
  apply slabTransverseCutoff_eq_one i a b w hw (slabInsetBox_subset i a b w hw.le hx)
  intro j hji
  have hj := hx j (Set.mem_univ j)
  simp only [slabInsetLower, slabInsetUpper, hji, ite_false] at hj
  exact ⟨hj.1.le, hj.2.le⟩

end EinsteinFull.Regeneration
