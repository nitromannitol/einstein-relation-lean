import EinsteinFull.Regeneration.SlabBoundaryProfile
import EinsteinFull.Regeneration.SlabProfileError
import EinsteinFull.Regeneration.SlabHarnackEnergy

/-!
# Weighted gradient of the slab comparison profile

The gradient of the clamped profile is a unit vector in the left boundary
layer and vanishes elsewhere.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The weighted gradient energy of the clamped profile on a transverse
section is bounded by the weighted volume of the full left boundary layer. -/
theorem slab_profile_gradient_product_le
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (i : Fin (n + 1))
    (s L : ℝ) (hs : 0 ≤ s) (hL : 1 ≤ L)
    (K : Set (Fin n → ℝ)) (hKfinite : volume K ≠ ∞)
    (hKsub : K ⊆ Icc (fun _ => -Real.exp (s * L / (n + 1)))
      (fun _ => Real.exp (s * L / (n + 1)))) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => Real.exp (s * p.1) *
      PDE.vecNormSq ((slabBoundaryProfile hU i L).grad (centralSlabPoint n i p)))
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict K)) ∧
    (∫ p : ℝ × (Fin n → ℝ), Real.exp (s * p.1) *
      PDE.vecNormSq ((slabBoundaryProfile hU i L).grad (centralSlabPoint n i p))
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict K))) ≤
      Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1))) := by
  let ν : Measure (Fin n → ℝ) := volume.restrict K
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hKfinite
  let g : ℝ → ℝ := (Ioo (-L) (-L + 1)).indicator (fun t => Real.exp (s * t))
  have hw : IntegrableOn (fun t : ℝ => Real.exp (s * t)) (Icc (-L) L) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).integrableOn_Icc
  have hg : IntegrableOn g (Icc (-L) L) := hw.indicator measurableSet_Ioo
  have hprod : Integrable (fun p : ℝ × (Fin n → ℝ) => g p.1)
      ((volume.restrict (Icc (-L) L)).prod ν) := hg.comp_fst ν
  have heq : (∫ p : ℝ × (Fin n → ℝ), g p.1
      ∂((volume.restrict (Icc (-L) L)).prod ν)) =
      (∫ t in Icc (-L) L, g t) * (volume : Measure (Fin n → ℝ)).real K := by
    rw [integral_prod _ hprod]
    simp [ν, measureReal_def, mul_comm, integral_mul_const]
  have hsub : Ioc (-L) (-L + 1) ⊆ Ioc (-L) L := by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  have hzero : ∀ t ∈ Ioc (-L) L \ Ioc (-L) (-L + 1), g t = 0 := by
    intro t ht
    have hnot : t ∉ Ioo (-L) (-L + 1) := by
      intro hh
      exact ht.2 ⟨hh.1, hh.2.le⟩
    exact indicator_of_notMem hnot _
  have hrestrict : (∫ t in Icc (-L) L, g t) = ∫ t in Ioc (-L) (-L + 1), g t := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub hzero
  have hgbound : (∫ t in Icc (-L) L, g t) ≤ Real.exp s * Real.exp (-(s * L)) := by
    rw [hrestrict]
    have hwlayer : IntegrableOn (fun t : ℝ => Real.exp (s * t)) (Ioc (-L) (-L + 1)) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).integrableOn_Ioc
    have hglayer : IntegrableOn g (Ioc (-L) (-L + 1)) := hwlayer.indicator measurableSet_Ioo
    calc
      _ ≤ ∫ t in Ioc (-L) (-L + 1), Real.exp (s * t) := by
        apply setIntegral_mono_on hglayer hwlayer measurableSet_Ioc
        intro t _
        by_cases ht : t ∈ Ioo (-L) (-L + 1)
        · simp [g, ht]
        · simp only [g, indicator_of_notMem ht]
          exact (Real.exp_pos _).le
      _ ≤ _ := integral_exp_boundary_layer_le s L hs
  have hvol : (volume : Measure (Fin n → ℝ)).real K ≤
      (2 * Real.exp (s * L / (n + 1))) ^ n := by
    have h := measureReal_mono (μ := (volume : Measure (Fin n → ℝ))) hKsub
      isCompact_Icc.measure_lt_top.ne
    rw [volume_transverse_cube n _ (Real.exp_pos _).le] at h
    exact h
  have hvol0 : 0 ≤ (volume : Measure (Fin n → ℝ)).real K := measureReal_nonneg
  have hpoint (p : ℝ × (Fin n → ℝ)) : Real.exp (s * p.1) *
      PDE.vecNormSq ((slabBoundaryProfile hU i L).grad (centralSlabPoint n i p)) = g p.1 := by
    rw [slabBoundaryProfile_grad]
    have hc := (centralSlabPoint_coord n i p.1 p.2).1
    by_cases ht : p.1 ∈ Ioo (-L) (-L + 1)
    · have hx : centralSlabPoint n i p ∈
          {x : PDE.Vec (n + 1) | -L < x i ∧ x i < -L + 1} := by
        simpa only [mem_ofPred_eq, hc, mem_Ioo] using ht
      rw [indicator_of_mem hx, PDE.vecNormSq_basisVec]
      simp [g, ht]
    · have hx : centralSlabPoint n i p ∉
          {x : PDE.Vec (n + 1) | -L < x i ∧ x i < -L + 1} := by
        simpa only [mem_ofPred_eq, hc, mem_Ioo] using ht
      rw [indicator_of_notMem hx]
      simp [g, ht, PDE.vecNormSq, PDE.vecDot]
  have hintegral : (∫ p : ℝ × (Fin n → ℝ), Real.exp (s * p.1) *
      PDE.vecNormSq ((slabBoundaryProfile hU i L).grad (centralSlabPoint n i p))
      ∂((volume.restrict (Icc (-L) L)).prod ν)) =
      ∫ p, g p.1 ∂((volume.restrict (Icc (-L) L)).prod ν) := by
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  refine ⟨hprod.congr (Filter.Eventually.of_forall (fun p => (hpoint p).symm)), ?_⟩
  change (∫ p : ℝ × (Fin n → ℝ), Real.exp (s * p.1) *
      PDE.vecNormSq ((slabBoundaryProfile hU i L).grad (centralSlabPoint n i p))
      ∂((volume.restrict (Icc (-L) L)).prod ν)) ≤ _
  rw [hintegral, heq]
  calc
    _ ≤ (Real.exp s * Real.exp (-(s * L))) *
        (2 * Real.exp (s * L / (n + 1))) ^ n :=
      mul_le_mul hgbound hvol hvol0 (by positivity)
    _ = Real.exp s * ((2 * Real.exp (s * L / (n + 1))) ^ n *
        Real.exp (-(s * L))) := by ring
    _ = _ := by rw [boundary_layer_transverse_factor]; ring

end EinsteinFull.Regeneration
