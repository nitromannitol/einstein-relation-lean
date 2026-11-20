import EinsteinFull.Regeneration.SlabCentralCubeTransfer
import EinsteinFull.Regeneration.GMPForceHarnack

/-!
# Harnack and central-slab energy

The local comparison estimate supplies the central gap needed for the
Gantert–Mathieu–Piatnitski energy argument.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- An `L²` weak solution restricts to an open subdomain. -/
theorem weak_divergence_form_l2_solution_restrict {d : ℕ}
    {a : PDE.CoeffField d} {U V : Set (PDE.Vec d)} {u : PDE.H1Function U}
    {f : PDE.Vec d → ℝ} {F : PDE.Vec d → PDE.Vec d}
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn a U u f F)
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U) :
    PDE.IsWeakDivergenceFormL2SolutionOn a V (u.restrict hV hVU) f F where
  flux_memL2 := fun j => (hsol.flux_memL2 j).mono_measure
    (Measure.restrict_mono hVU le_rfl)
  source_memL2 := hsol.source_memL2.mono_measure (Measure.restrict_mono hVU le_rfl)
  forcing_memL2 := fun j => (hsol.forcing_memL2 j).mono_measure
    (Measure.restrict_mono hVU le_rfl)
  identity := fun φ => (hsol.toIsWeakDivergenceFormSolutionOn.restrict hU hV hVU φ).2

/-- A central slice point has zero force coordinate and the transverse coordinates supplied. -/
theorem centralSlabPoint_coord (n : ℕ) (i : Fin (n + 1)) (t : ℝ) (z : Fin n → ℝ) :
    centralSlabPoint n i (t, z) i = t ∧
      ∀ j, centralSlabPoint n i (t, z) (i.succAbove j) = z j := by
  constructor
  · simp [centralSlabPoint, MeasurableEquiv.piFinSuccAbove_symm_apply]
  · intro j
    simp [centralSlabPoint, MeasurableEquiv.piFinSuccAbove_symm_apply]

/-- A transverse unit-cube point gives a central vector in the unit cube. -/
theorem centralSlabPoint_abs_le_one (n : ℕ) (i : Fin (n + 1)) (z : Fin n → ℝ)
    (hz : z ∈ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1)) :
    ∀ j, |centralSlabPoint n i (0, z) j| ≤ 1 := by
  intro j
  refine i.succAboveCases ?_ (fun k => ?_) j
  · simp [centralSlabPoint_coord]
  · rw [(centralSlabPoint_coord n i 0 z).2 k]
    exact abs_le.mpr ⟨hz.1 k, hz.2 k⟩

end EinsteinFull.Regeneration
