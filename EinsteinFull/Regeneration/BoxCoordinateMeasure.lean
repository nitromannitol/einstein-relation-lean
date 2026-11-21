import EinsteinFull.Regeneration.CoordinateIntervalIncrement

/-!
# Coordinate sections of boxes

Separating one coordinate identifies a closed box section with a product of
an interval and a transverse box, preserving Lebesgue measure.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The closed transverse section of a coordinate box. -/
def transverseClosedBox {n : ℕ} (i : Fin (n + 1)) (a b : PDE.Vec (n + 1)) :
    Set (Fin n → ℝ) :=
  Icc (fun j => a (i.succAbove j)) (fun j => b (i.succAbove j))

/-- A closed interval section with the transverse sides of a box. -/
def closedCoordinateBox {n : ℕ} (i : Fin (n + 1)) (a b : PDE.Vec (n + 1)) (l r : ℝ) :
    Set (PDE.Vec (n + 1)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i) ⁻¹'
    (Icc l r ×ˢ transverseClosedBox i a b)

/-- Closed coordinate sections are measurable. -/
theorem measurableSet_closedCoordinateBox {n : ℕ} (i : Fin (n + 1))
    (a b : PDE.Vec (n + 1)) (l r : ℝ) :
    MeasurableSet (closedCoordinateBox i a b l r) :=
  (measurableSet_Icc.prod measurableSet_Icc).preimage
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).measurable

/-- A half-open coordinate section is contained in the corresponding closed section. -/
theorem coordinateIntervalBox_subset_closedCoordinateBox {n : ℕ} (i : Fin (n + 1))
    (a b : PDE.Vec (n + 1)) (l r : ℝ) :
    coordinateIntervalBox n i l r (transverseClosedBox i a b) ⊆
      closedCoordinateBox i a b l r := by
  intro x hx
  exact ⟨⟨hx.1.1.le, hx.1.2⟩, hx.2⟩

/-- Closed coordinate section integrals equal the corresponding product integrals. -/
theorem integral_closedCoordinateBox {n : ℕ} (i : Fin (n + 1))
    (a b : PDE.Vec (n + 1)) (l r : ℝ) (f : PDE.Vec (n + 1) → ℝ) :
    (∫ x in closedCoordinateBox i a b l r, f x) =
      ∫ p, f (centralSlabPoint n i p)
        ∂((volume.restrict (Icc l r)).prod (volume.restrict (transverseClosedBox i a b))) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  let W := closedCoordinateBox i a b l r
  let V := Icc l r ×ˢ transverseClosedBox i a b
  have hpres : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have hpre : e ⁻¹' W = V := by
    ext p
    simp [e, W, V, closedCoordinateBox]
  have hpresW := hpres.restrict_preimage (measurableSet_closedCoordinateBox i a b l r)
  rw [hpre, Measure.volume_eq_prod, ← Measure.prod_restrict] at hpresW
  change (∫ x in W, f x) = ∫ p, f (e p) ∂_
  rw [← hpresW.map_eq]
  exact integral_map_equiv e f

/-- Any point of the open box belongs to its full closed coordinate section. -/
theorem axisBox_subset_closedCoordinateBox {n : ℕ} (i : Fin (n + 1))
    (a b : PDE.Vec (n + 1)) : PDE.axisBox a b ⊆ closedCoordinateBox i a b (a i) (b i) := by
  intro x hx
  change ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x).1 ∈ Icc (a i) (b i)) ∧
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x).2 ∈ transverseClosedBox i a b)
  have hi := hx i (Set.mem_univ i)
  constructor
  · simpa [MeasurableEquiv.piFinSuccAbove_apply] using ⟨hi.1.le, hi.2.le⟩
  · change (∀ j, a (i.succAbove j) ≤
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x).2 j) ∧
      (∀ j, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x).2 j ≤
        b (i.succAbove j))
    constructor <;> intro j
    · simpa [MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth] using (hx (i.succAbove j) (Set.mem_univ _)).1.le
    · simpa [MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth] using (hx (i.succAbove j) (Set.mem_univ _)).2.le

end EinsteinFull.Regeneration
