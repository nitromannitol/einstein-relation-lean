import EinsteinFull.Regeneration.SlabShellProduct
import EinsteinFull.Regeneration.SlabProfileIntegrated

/-!
# Geometry of geometrically nested slab boxes

The force interval is fixed while every transverse side is halved at each
step of the energy iteration.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- Lower endpoints of a slab with transverse half-side `R`. -/
def centeredSlabLower {d : ℕ} (i : Fin d) (L R : ℝ) : PDE.Vec d :=
  fun j => if j = i then -L else -R

/-- Upper endpoints of a slab with transverse half-side `R`. -/
def centeredSlabUpper {d : ℕ} (i : Fin d) (L R : ℝ) : PDE.Vec d :=
  fun j => if j = i then L else R

/-- A half-width transverse inset halves the slab's transverse side. -/
theorem slabInset_centeredSlab {d : ℕ} (i : Fin d) (L R : ℝ) :
    PDE.axisBox (slabInsetLower i (centeredSlabLower i L R) (R / 2))
      (slabInsetUpper i (centeredSlabUpper i L R) (R / 2)) =
    PDE.axisBox (centeredSlabLower i L (R / 2)) (centeredSlabUpper i L (R / 2)) := by
  have hlo : slabInsetLower i (centeredSlabLower i L R) (R / 2) =
      centeredSlabLower i L (R / 2) := by
    funext j
    by_cases h : j = i
    · simp [slabInsetLower, centeredSlabLower, h]
    · simp [slabInsetLower, centeredSlabLower, h]
      ring
  have hhi : slabInsetUpper i (centeredSlabUpper i L R) (R / 2) =
      centeredSlabUpper i L (R / 2) := by
    funext j
    by_cases h : j = i
    · simp [slabInsetUpper, centeredSlabUpper, h]
    · simp [slabInsetUpper, centeredSlabUpper, h]
      ring
  rw [hlo, hhi]

/-- Every closed section of a smaller centered slab lies in the source box. -/
theorem centeredSlab_closed_subset_source {n : ℕ} (i : Fin (n + 1))
    (s L R : ℝ) (hRmax : R ≤ Real.exp (s * L / (n + 1))) :
    closedCoordinateBox i (centeredSlabLower i L R) (centeredSlabUpper i L R) (-L) L ⊆
      coordinateSlabBox n i s L := by
  intro x hx
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  change (e x).1 ∈ Icc (-L) L ∧ (e x).2 ∈
    transverseClosedBox i (centeredSlabLower i L R) (centeredSlabUpper i L R) at hx
  change (e x).1 ∈ Icc (-L) L ∧ (e x).2 ∈
    Icc (fun _ => -Real.exp (s * L / (n + 1)))
      (fun _ => Real.exp (s * L / (n + 1)))
  refine ⟨hx.1, ?_⟩
  constructor <;> intro j
  · have hj := hx.2.1 j
    simp only [centeredSlabLower, Fin.succAbove_ne, ite_false] at hj
    linarith
  · have hj := hx.2.2 j
    simp only [centeredSlabUpper, Fin.succAbove_ne, ite_false] at hj
    linarith

/-- The transverse shell of a smaller centered slab lies in the source cube. -/
theorem centeredSlab_shell_subset_source_cube {n : ℕ} (i : Fin (n + 1))
    (s L R w : ℝ) (hRmax : R ≤ Real.exp (s * L / (n + 1))) :
    slabShellSection i (centeredSlabLower i L R) (centeredSlabUpper i L R) w ⊆
      Icc (fun _ => -Real.exp (s * L / (n + 1)))
        (fun _ => Real.exp (s * L / (n + 1))) := by
  intro z hz
  have hclosed := slabShellSection_subset_closed i (centeredSlabLower i L R)
    (centeredSlabUpper i L R) w hz
  constructor <;> intro j
  · have hj := hclosed.1 j
    simp only [centeredSlabLower, Fin.succAbove_ne, ite_false] at hj
    linarith
  · have hj := hclosed.2 j
    simp only [centeredSlabUpper, Fin.succAbove_ne, ite_false] at hj
    linarith

end EinsteinFull.Regeneration
