import EinsteinFull.Regeneration.SlabNestedBoxes
import EinsteinFull.Regeneration.BoxCoordinateMeasure

/-!
# Product structure of a transverse slab shell

Splitting the force coordinate identifies the outer-minus-inner box shell
with an interval times a transverse shell.
-/

open MeasureTheory Set PDE

namespace EinsteinFull.Regeneration

/-- The open transverse section of a box. -/
def transverseOpenBox {n : ℕ} (i : Fin (n + 1)) (a b : PDE.Vec (n + 1)) :
    Set (Fin n → ℝ) :=
  PDE.axisBox (fun j => a (i.succAbove j)) (fun j => b (i.succAbove j))

/-- The transverse section of the outer-minus-inset shell. -/
def slabShellSection {n : ℕ} (i : Fin (n + 1)) (a b : PDE.Vec (n + 1)) (w : ℝ) :
    Set (Fin n → ℝ) :=
  transverseOpenBox i a b \ transverseOpenBox i (slabInsetLower i a w) (slabInsetUpper i b w)

/-- The transverse shell is measurable and has finite volume. -/
theorem slabShellSection_measurable_finite {n : ℕ} (i : Fin (n + 1))
    (a b : PDE.Vec (n + 1)) (w : ℝ) :
    MeasurableSet (slabShellSection i a b w) ∧ volume (slabShellSection i a b w) ≠ ⊤ := by
  have hm : MeasurableSet (slabShellSection i a b w) :=
    (PDE.isOpen_axisBox _ _).measurableSet.diff (PDE.isOpen_axisBox _ _).measurableSet
  have hsub : slabShellSection i a b w ⊆ transverseClosedBox i a b := by
    intro z hz
    have houter := hz.1
    constructor <;> intro j
    · exact (houter j (Set.mem_univ j)).1.le
    · exact (houter j (Set.mem_univ j)).2.le
  exact ⟨hm, ne_top_of_le_ne_top isCompact_Icc.measure_lt_top.ne (measure_mono hsub)⟩

/-- The force-coordinate splitting sends an open box to an interval product. -/
theorem centralSlabPoint_mem_axisBox_iff {n : ℕ} (i : Fin (n + 1))
    (a b : PDE.Vec (n + 1)) (t : ℝ) (z : Fin n → ℝ) :
    centralSlabPoint n i (t, z) ∈ PDE.axisBox a b ↔
      t ∈ Ioo (a i) (b i) ∧ z ∈ transverseOpenBox i a b := by
  simp only [PDE.axisBox, transverseOpenBox, mem_pi, mem_univ, forall_true_left, mem_Ioo]
  rw [Fin.forall_iff_succAbove i]
  have hc := centralSlabPoint_coord n i t z
  simp only [hc.1, hc.2]

/-- Integrals on the physical slab shell equal product integrals over its
transverse section. -/
theorem integral_slab_shell_eq_product {n : ℕ} (i : Fin (n + 1))
    (a b : PDE.Vec (n + 1)) (w : ℝ) (f : PDE.Vec (n + 1) → ℝ) :
    (∫ x in PDE.axisBox a b \ PDE.axisBox (slabInsetLower i a w) (slabInsetUpper i b w), f x) =
      ∫ p, f (centralSlabPoint n i p)
        ∂((volume.restrict (Icc (a i) (b i))).prod (volume.restrict (slabShellSection i a b w))) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  let W := PDE.axisBox a b \ PDE.axisBox (slabInsetLower i a w) (slabInsetUpper i b w)
  let V := Ioo (a i) (b i) ×ˢ slabShellSection i a b w
  have hpres : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have hpre : e ⁻¹' W = V := by
    ext p
    change centralSlabPoint n i p ∈ W ↔ p ∈ V
    rcases p with ⟨t, z⟩
    simp only [W, V, mem_sdiff, mem_prod, centralSlabPoint_mem_axisBox_iff,
      slabInsetLower, slabInsetUpper, ite_true, slabShellSection]
    tauto
  have hWmeas : MeasurableSet W :=
    (PDE.isOpen_axisBox _ _).measurableSet.diff (PDE.isOpen_axisBox _ _).measurableSet
  have hpresW := hpres.restrict_preimage hWmeas
  rw [hpre, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_congr_set Ioo_ae_eq_Icc] at hpresW
  change (∫ x in W, f x) = ∫ p, f (e p) ∂_
  rw [← hpresW.map_eq]
  exact integral_map_equiv e f

end EinsteinFull.Regeneration
