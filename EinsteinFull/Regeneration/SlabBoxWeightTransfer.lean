import EinsteinFull.Regeneration.SlabBoxWeight
import EinsteinFull.Regeneration.SlabProfileIntegrated

/-!
# Weighted volume in physical slab coordinates

Splitting off the force coordinate transfers the full-box exponential mass
estimate to the original Euclidean coordinate space.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- An integrable density bounded by the force weight has the full-box bound. -/
theorem coordinate_slab_integral_le_weight (n : ℕ) (i : Fin (n + 1))
    (s L : ℝ) (hs : 0 < s) (ρ : PDE.Vec (n + 1) → ℝ)
    (hint : IntegrableOn ρ (coordinateSlabBox n i s L))
    (hbound : ∀ᵐ x ∂(volume.restrict (coordinateSlabBox n i s L)),
      ρ x ≤ Real.exp (s * x i)) :
    (∫ x in coordinateSlabBox n i s L, ρ x) ≤
      ((2 : ℝ) ^ n / s) * Real.exp ((s * (2 * (n + 1 : ℝ) - 1) / (n + 1)) * L) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  let K : Set (Fin n → ℝ) := Icc (fun _ => -Real.exp (s * L / (n + 1)))
    (fun _ => Real.exp (s * L / (n + 1)))
  let V : Set (ℝ × (Fin n → ℝ)) := Icc (-L) L ×ˢ K
  let W := coordinateSlabBox n i s L
  let ν : Measure (Fin n → ℝ) := volume.restrict K
  let μ : Measure (ℝ × (Fin n → ℝ)) := (volume.restrict (Icc (-L) L)).prod ν
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hpres : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have hpre : e ⁻¹' W = V := by
    ext p
    simp [W, coordinateSlabBox, e, V, K]
  have hWmeas : MeasurableSet W := (measurableSet_Icc.prod measurableSet_Icc).preimage
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).measurable
  have hm : (volume : Measure (ℝ × (Fin n → ℝ))).restrict V = μ := by
    dsimp only [V, μ, ν]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hpresW := hpres.restrict_preimage hWmeas
  rw [hpre, hm] at hpresW
  have hρ : Integrable (fun p => ρ (e p)) μ := by
    rw [← hm, ← hpre]
    exact (hpres.integrableOn_comp_preimage e.measurableEmbedding).2 hint
  have ht : Integrable (fun t : ℝ => Real.exp (s * t)) (volume.restrict (Icc (-L) L)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).integrableOn_Icc
  have hw : Integrable (fun p : ℝ × (Fin n → ℝ) => Real.exp (s * p.1)) μ := ht.comp_fst ν
  have hpoint : ∀ᵐ p ∂μ, ρ (e p) ≤ Real.exp (s * p.1) := by
    have h := hpresW.quasiMeasurePreserving.ae hbound
    filter_upwards [h] with p hp
    have he : (e p) i = p.1 := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    simpa only [he] using hp
  have hcalc : (∫ p : ℝ × (Fin n → ℝ), Real.exp (s * p.1) ∂μ) =
      (∫ t in Icc (-L) L, Real.exp (s * t)) * (volume : Measure (Fin n → ℝ)).real K := by
    rw [integral_prod _ hw]
    simp [ν, measureReal_def, mul_comm, integral_mul_const]
  have heq : (∫ x in W, ρ x) = ∫ p, ρ (e p) ∂μ := by
    rw [← hpresW.map_eq]
    exact integral_map_equiv e ρ
  calc
    _ = ∫ p, ρ (e p) ∂μ := heq
    _ ≤ ∫ p : ℝ × (Fin n → ℝ), Real.exp (s * p.1) ∂μ := integral_mono_ae hρ hw hpoint
    _ = _ := hcalc
    _ ≤ _ := weighted_slab_product_volume_le n s L hs

end EinsteinFull.Regeneration
