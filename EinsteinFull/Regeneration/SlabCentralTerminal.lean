import EinsteinFull.Regeneration.SlabGeometricRecurrence
import EinsteinFull.Regeneration.SlabHarnackSobolev

/-!
# Central energy inside the terminal slab

The central Harnack box embeds in a sufficiently wide transverse slab after
removing a null force-face endpoint.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The central slab with its right force endpoint omitted. -/
noncomputable def coordinateOpenCentralSlab (n : ℕ) (i : Fin (n + 1)) (L : ℝ) :
    Set (PDE.Vec (n + 1)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i) ⁻¹'
    (Ioo 0 L ×ˢ Icc (fun _ => (-1 : ℝ)) (fun _ => 1))

/-- Removing the force-face endpoint leaves central slab integrals unchanged. -/
theorem integral_centralSlab_eq_open (n : ℕ) (i : Fin (n + 1)) (L : ℝ)
    (f : PDE.Vec (n + 1) → ℝ) :
    (∫ x in coordinateCentralSlab n i L, f x) =
      ∫ x in coordinateOpenCentralSlab n i L, f x := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hpres : MeasurePreserving e := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hprod : (Ioc (0 : ℝ) L ×ˢ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1)) =ᵐ[
      (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))]
      (Ioo (0 : ℝ) L ×ˢ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1)) :=
    Measure.set_prod_ae_eq Ioo_ae_eq_Ioc.symm (Filter.EventuallyEq.rfl)
  have hpre : coordinateCentralSlab n i L =ᵐ[volume] coordinateOpenCentralSlab n i L := by
    filter_upwards [hpres.quasiMeasurePreserving.ae hprod] with x hx
    exact hx
  exact setIntegral_congr_set hpre

/-- The open central slab lies in every centered slab of transverse radius
strictly greater than one. -/
theorem openCentralSlab_subset_centered {n : ℕ} (i : Fin (n + 1))
    (L R : ℝ) (hL : 0 < L) (hR : 1 < R) :
    coordinateOpenCentralSlab n i L ⊆ centeredSlabBox i L R := by
  intro x hx
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hx' : (e x).1 ∈ Ioo 0 L ∧ (e x).2 ∈
      Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1) := hx
  have he : centralSlabPoint n i (e x) = x := e.symm_apply_apply x
  rw [← he]
  change centralSlabPoint n i (e x) ∈
    PDE.axisBox (centeredSlabLower i L R) (centeredSlabUpper i L R)
  apply (centralSlabPoint_mem_axisBox_iff i _ _ (e x).1 (e x).2).2
  constructor
  · simp only [centeredSlabLower, centeredSlabUpper, ite_true, mem_Ioo]
    constructor <;> linarith [hx'.1.1, hx'.1.2]
  · intro j _
    have hl := hx'.2.1 j
    have hu := hx'.2.2 j
    simp only [centeredSlabLower, centeredSlabUpper, Fin.succAbove_ne, ite_false, mem_Ioo]
    constructor <;> linarith

/-- A central slab energy is bounded by any enclosing centered slab energy. -/
theorem central_slab_energy_le_centered
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (i : Fin (n + 1)) (L R s : ℝ) (hL : 0 < L) (hR : 1 < R)
    (u : PDE.H1Function U) (A : PDE.CoeffField (n + 1)) (lam' Λ' : ℝ)
    (hsub : centeredSlabBox i L R ⊆ U)
    (hEll : PDE.IsEllipticFieldOn lam' Λ' U (fun x => Real.exp (s * x i) • A x)) :
    (∫ x in coordinateCentralSlab n i L, slabWeightedEnergy A s i u.grad x) ≤
      ∫ x in centeredSlabBox i L R, slabWeightedEnergy A s i u.grad x := by
  rw [integral_centralSlab_eq_open]
  have hintU : IntegrableOn (slabWeightedEnergy A s i u.grad) U := by
    have h := PDE.integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll u.gradMemL2
    have heq : slabWeightedEnergy A s i u.grad = fun x =>
        PDE.vecDot (u.grad x) (PDE.matVecMul (Real.exp (s * x i) • A x) (u.grad x)) := by
      funext x
      dsimp [slabWeightedEnergy, matrixEnergy]
      rw [PDE.vecDot_comm]
    rw [heq]
    exact h
  have hnonneg : ∀ᵐ x ∂(volume.restrict (centeredSlabBox i L R)),
      0 ≤ slabWeightedEnergy A s i u.grad x := by
    filter_upwards [ae_restrict_mem (PDE.isOpen_axisBox _ _).measurableSet] with x hx
    have hell := hEll.elliptic (hsub hx)
    have h := hell.coercive (u.grad x)
    have h0 := mul_nonneg hell.lam_pos.le (PDE.vecNormSq_nonneg (u.grad x))
    exact h0.trans (by simpa only [slabWeightedEnergy, matrixEnergy, PDE.vecDot_comm] using h)
  exact setIntegral_mono_set (hintU.mono_set hsub) hnonneg
    (Filter.Eventually.of_forall fun _ hx => openCentralSlab_subset_centered i L R hL hR hx)

end EinsteinFull.Regeneration
