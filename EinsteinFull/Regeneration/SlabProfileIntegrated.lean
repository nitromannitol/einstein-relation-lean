import EinsteinFull.Regeneration.SlabBoundaryProfile
import Mathlib.MeasureTheory.Constructions.Pi
import PDEFoundation.PDE.CoefficientL2

/-!
# Integrated energy of the slab boundary profile

Splitting the force coordinate identifies the weighted transition strip with
the product boundary layer.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The coordinate boundary layer in the original vector space. -/
noncomputable def coordinateBoundaryLayer (n : ℕ) (i : Fin (n + 1)) (s L : ℝ) :
    Set (PDE.Vec (n + 1)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i) ⁻¹'
    (Ioc (-L) (-L + 1) ×ˢ
      Icc (fun _ => -Real.exp (s * L / (n + 1)))
        (fun _ => Real.exp (s * L / (n + 1))))

/-- The profile energy on the coordinate boundary layer has the source decay. -/
theorem slabBoundaryProfile_integrated_energy_le (n : ℕ) (i : Fin (n + 1))
    (s L : ℝ) (hs : 0 ≤ s) {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (a : PDE.CoeffField (n + 1)) (lam Λ : ℝ)
    (hint : IntegrableOn (fun x => PDE.vecDot
      (PDE.matVecMul (Real.exp (s * x i) • a x) ((slabBoundaryProfile hU i L).grad x))
      ((slabBoundaryProfile hU i L).grad x)) (coordinateBoundaryLayer n i s L))
    (hell : ∀ᵐ x ∂(volume.restrict (coordinateBoundaryLayer n i s L)),
      PDE.IsEllipticMatrix lam Λ (a x)) (hΛ : 0 ≤ Λ) :
    (∫ x in coordinateBoundaryLayer n i s L, PDE.vecDot
      (PDE.matVecMul (Real.exp (s * x i) • a x) ((slabBoundaryProfile hU i L).grad x))
      ((slabBoundaryProfile hU i L).grad x)) ≤
      Λ * (Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1)))) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  let V : Set (ℝ × (Fin n → ℝ)) := Ioc (-L) (-L + 1) ×ˢ
    Icc (fun _ => -Real.exp (s * L / (n + 1)))
      (fun _ => Real.exp (s * L / (n + 1)))
  let W := coordinateBoundaryLayer n i s L
  let f : PDE.Vec (n + 1) → ℝ := fun x => PDE.vecDot
    (PDE.matVecMul (Real.exp (s * x i) • a x) ((slabBoundaryProfile hU i L).grad x))
    ((slabBoundaryProfile hU i L).grad x)
  have hpres : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have hpre : e ⁻¹' W = V := by
    ext p
    simp [W, coordinateBoundaryLayer, e, V]
  have hWmeas : MeasurableSet W := by
    exact (measurableSet_Ioc.prod measurableSet_Icc).preimage
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).measurable
  have hm : (volume : Measure (ℝ × (Fin n → ℝ))).restrict V = boundaryLayerMeasure n s L := by
    dsimp only [V, boundaryLayerMeasure]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hi : Integrable (fun p => f (e p)) (boundaryLayerMeasure n s L) := by
    rw [← hm, ← hpre]
    exact (hpres.integrableOn_comp_preimage e.measurableEmbedding).2 hint
  have hpresW := hpres.restrict_preimage hWmeas
  rw [hpre, hm] at hpresW
  have hp : ∀ᵐ p ∂(boundaryLayerMeasure n s L), PDE.IsEllipticMatrix lam Λ (a (e p)) :=
    hpresW.quasiMeasurePreserving.ae hell
  have hpoint : ∀ᵐ p ∂(boundaryLayerMeasure n s L), f (e p) ≤ Λ * Real.exp (s * p.1) := by
    filter_upwards [hp] with p hpA
    have hb := slabBoundaryProfile_energy_le hU i L s a lam Λ (e p) hpA
    have he : (e p) i = p.1 := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    by_cases hh : e p ∈ {x : PDE.Vec (n + 1) | -L < x i ∧ x i < -L + 1}
    · simpa only [Set.indicator_of_mem hh, he, f] using hb
    · rw [Set.indicator_of_notMem hh] at hb
      exact hb.trans (mul_nonneg hΛ (Real.exp_pos _).le)
  have hbound := boundary_layer_energy_le n s L Λ hs hΛ (fun p => f (e p)) hi hpoint
  have heq : (∫ x in W, f x) = ∫ p, f (e p) ∂boundaryLayerMeasure n s L := by
    rw [← hpresW.map_eq]
    exact integral_map_equiv e f
  rw [heq]
  exact hbound

/-- Local weighted ellipticity supplies integrability of the actual profile energy. -/
theorem slabBoundaryProfile_integrated_energy_of_ellipticity (n : ℕ) (i : Fin (n + 1))
    (s L : ℝ) (hs : 0 ≤ s) {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (a : PDE.CoeffField (n + 1))
    (lam Λ lam' Λ' : ℝ) (hΛ : 0 ≤ Λ)
    (hsub : coordinateBoundaryLayer n i s L ⊆ U)
    (hEll : PDE.IsEllipticFieldOn lam' Λ' U (fun x => Real.exp (s * x i) • a x))
    (hell : ∀ᵐ x ∂(volume.restrict (coordinateBoundaryLayer n i s L)),
      PDE.IsEllipticMatrix lam Λ (a x)) :
    (∫ x in coordinateBoundaryLayer n i s L, PDE.vecDot
      (PDE.matVecMul (Real.exp (s * x i) • a x) ((slabBoundaryProfile hU i L).grad x))
      ((slabBoundaryProfile hU i L).grad x)) ≤
      Λ * (Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1)))) := by
  have hint := (PDE.integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll
    (slabBoundaryProfile hU i L).gradMemL2).mono_set hsub
  apply slabBoundaryProfile_integrated_energy_le n i s L hs hU a lam Λ _ hell hΛ
  simpa only [PDE.vecDot_comm] using hint

/-- The force-aligned slab box with exponentially large transverse sides. -/
noncomputable def coordinateSlabBox (n : ℕ) (i : Fin (n + 1)) (s L : ℝ) :
    Set (PDE.Vec (n + 1)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i) ⁻¹'
    (Icc (-L) L ×ˢ
      Icc (fun _ => -Real.exp (s * L / (n + 1)))
        (fun _ => Real.exp (s * L / (n + 1))))

/-- The whole slab-box profile energy equals the transition-layer energy. -/
theorem slabBoundaryProfile_box_energy_le (n : ℕ) (i : Fin (n + 1))
    (s L : ℝ) (hs : 0 ≤ s) (hL : 1 ≤ L) {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (a : PDE.CoeffField (n + 1))
    (lam Λ lam' Λ' : ℝ) (hΛ : 0 ≤ Λ)
    (hsub : coordinateSlabBox n i s L ⊆ U)
    (hEll : PDE.IsEllipticFieldOn lam' Λ' U (fun x => Real.exp (s * x i) • a x))
    (hell : ∀ᵐ x ∂(volume.restrict (coordinateBoundaryLayer n i s L)),
      PDE.IsEllipticMatrix lam Λ (a x)) :
    (∫ x in coordinateSlabBox n i s L, PDE.vecDot
      (PDE.matVecMul (Real.exp (s * x i) • a x) ((slabBoundaryProfile hU i L).grad x))
      ((slabBoundaryProfile hU i L).grad x)) ≤
      Λ * (Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1)))) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hcoord (x : PDE.Vec (n + 1)) : (e x).1 = x i := by
    simp [e, MeasurableEquiv.piFinSuccAbove_apply]
  have hboxmeas : MeasurableSet (coordinateSlabBox n i s L) :=
    (measurableSet_Icc.prod measurableSet_Icc).preimage e.measurable
  have hlayer : coordinateBoundaryLayer n i s L ⊆ coordinateSlabBox n i s L := by
    intro x hx
    change (e x).1 ∈ Ioc (-L) (-L + 1) ∧ _ at hx
    change (e x).1 ∈ Icc (-L) L ∧ _
    exact ⟨⟨hx.1.1.le, by linarith [hx.1.2]⟩, hx.2⟩
  have hzero : ∀ x ∈ coordinateSlabBox n i s L \ coordinateBoundaryLayer n i s L,
      PDE.vecDot (PDE.matVecMul (Real.exp (s * x i) • a x)
        ((slabBoundaryProfile hU i L).grad x)) ((slabBoundaryProfile hU i L).grad x) = 0 := by
    intro x hx
    have hstrip : x ∉ {x : PDE.Vec (n + 1) | -L < x i ∧ x i < -L + 1} := by
      intro hstrip
      apply hx.2
      change (e x).1 ∈ Ioc (-L) (-L + 1) ∧ _
      have hbox := hx.1
      change (e x).1 ∈ Icc (-L) L ∧ _ at hbox
      exact ⟨⟨by simpa only [hcoord] using hstrip.1,
        by simpa only [hcoord] using hstrip.2.le⟩, hbox.2⟩
    rw [slabBoundaryProfile_grad, Set.indicator_of_notMem hstrip]
    simp [PDE.matVecMul, PDE.vecDot]
  have heq := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume) hboxmeas hlayer hzero
  rw [heq]
  exact slabBoundaryProfile_integrated_energy_of_ellipticity n i s L hs hU a
    lam Λ lam' Λ' hΛ (hlayer.trans hsub) hEll hell

end EinsteinFull.Regeneration
