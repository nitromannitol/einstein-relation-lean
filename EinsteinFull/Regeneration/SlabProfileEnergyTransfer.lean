import EinsteinFull.Regeneration.SlabShellEstimate
import EinsteinFull.Regeneration.SlabProfileIntegrated

/-!
# Profile energy on slab subboxes

The energy of the comparison profile on any subbox of the source box is
bounded by the weighted mass of its left boundary layer.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- Any subbox of the source slab inherits the profile's exponential energy bound. -/
theorem slab_profile_energy_on_subbox_le
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (i : Fin (n + 1))
    (L s lam Λ lam' Λ' : ℝ) (hL : 1 ≤ L) (hs : 0 ≤ s) (hΛ : 0 ≤ Λ)
    (a b : PDE.Vec (n + 1))
    (hQ : PDE.axisBox a b ⊆ coordinateSlabBox n i s L)
    (hfull : coordinateSlabBox n i s L ⊆ U) (A : PDE.CoeffField (n + 1))
    (hEll : PDE.IsEllipticFieldOn lam' Λ' U (fun x => Real.exp (s * x i) • A x))
    (hA : ∀ᵐ x ∂(PDE.volumeOn U), PDE.IsEllipticMatrix lam Λ (A x)) :
    IntegrableOn (slabWeightedEnergy A s i (slabBoundaryProfile hU i L).grad) (PDE.axisBox a b) ∧
    (∫ x in PDE.axisBox a b, slabWeightedEnergy A s i (slabBoundaryProfile hU i L).grad x) ≤
      Λ * (Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1)))) := by
  let Q := PDE.axisBox a b
  let W := coordinateSlabBox n i s L
  let J := coordinateBoundaryLayer n i s L
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hJU : J ⊆ U := by
    apply Set.Subset.trans _ hfull
    intro x hx
    change (e x).1 ∈ Ioc (-L) (-L + 1) ∧ _ at hx
    change (e x).1 ∈ Icc (-L) L ∧ _
    exact ⟨⟨hx.1.1.le, by linarith [hx.1.2]⟩, hx.2⟩
  have hAJ : ∀ᵐ x ∂(volume.restrict J), PDE.IsEllipticMatrix lam Λ (A x) :=
    ae_restrict_of_ae_restrict_of_subset hJU hA
  have hbound := slabBoundaryProfile_box_energy_le n i s L hs hL hU A lam Λ lam' Λ'
    hΛ hfull hEll hAJ
  have henergyU : IntegrableOn (slabWeightedEnergy A s i (slabBoundaryProfile hU i L).grad) U := by
    have h := PDE.integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll
      (slabBoundaryProfile hU i L).gradMemL2
    have heq : slabWeightedEnergy A s i (slabBoundaryProfile hU i L).grad = fun x =>
        PDE.vecDot ((slabBoundaryProfile hU i L).grad x)
          (PDE.matVecMul (Real.exp (s * x i) • A x) ((slabBoundaryProfile hU i L).grad x)) := by
      funext x
      dsimp [slabWeightedEnergy, matrixEnergy]
      rw [PDE.vecDot_comm]
    rw [heq]
    exact h
  have hnonneg : ∀ᵐ x ∂(volume.restrict W),
      0 ≤ slabWeightedEnergy A s i (slabBoundaryProfile hU i L).grad x := by
    have hm : MeasurableSet W := (measurableSet_Icc.prod measurableSet_Icc).preimage e.measurable
    filter_upwards [ae_restrict_mem hm] with x hx
    have hell := hEll.elliptic (hfull hx)
    have hcoercive := hell.coercive ((slabBoundaryProfile hU i L).grad x)
    have hp := mul_nonneg hell.lam_pos.le
      (PDE.vecNormSq_nonneg ((slabBoundaryProfile hU i L).grad x))
    exact hp.trans (by simpa only [slabWeightedEnergy, matrixEnergy, PDE.vecDot_comm] using hcoercive)
  have hmono : (∫ x in Q, slabWeightedEnergy A s i (slabBoundaryProfile hU i L).grad x) ≤
      ∫ x in W, slabWeightedEnergy A s i (slabBoundaryProfile hU i L).grad x :=
    setIntegral_mono_set (henergyU.mono_set hfull) hnonneg
      (Filter.Eventually.of_forall fun _ hx => hQ hx)
  refine ⟨henergyU.mono_set (hQ.trans hfull), hmono.trans ?_⟩
  simpa only [W, slabWeightedEnergy, matrixEnergy] using hbound

end EinsteinFull.Regeneration
