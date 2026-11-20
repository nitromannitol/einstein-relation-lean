import EinsteinFull.Regeneration.SlabProfileEnergy

/-!
# Weighted error of the slab comparison profile

The clamped width-one profile differs from one only in the left boundary
layer. Its weighted squared error has the same decay as that layer.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The weighted squared error of the clamped profile is bounded by the
weighted mass of the left boundary layer. -/
theorem slab_profile_error_integral_le (s L : ℝ) (hs : 0 ≤ s) (hL : 1 ≤ L) :
    (∫ t in Icc (-L) L, Real.exp (s * t) *
      (1 - min (max (t + L) 0) 1) ^ 2) ≤
      Real.exp s * Real.exp (-(s * L)) := by
  let f : ℝ → ℝ := fun t => Real.exp (s * t) * (1 - min (max (t + L) 0) 1) ^ 2
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hsub : Ioc (-L) (-L + 1) ⊆ Ioc (-L) L := by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  have hzero : ∀ t ∈ Ioc (-L) L \ Ioc (-L) (-L + 1), f t = 0 := by
    intro t ht
    have ht' : -L + 1 ≤ t := by
      have := ht.2
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at this
      rcases this with h | h
      · linarith [ht.1.1]
      · linarith
    have hmin : min (max (t + L) 0) 1 = 1 :=
      min_eq_right (le_trans (by linarith) (le_max_left _ _))
    simp [f, hmin]
  have heq : (∫ t in Icc (-L) L, f t) = ∫ t in Ioc (-L) (-L + 1), f t := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub hzero
  rw [heq]
  have hf : IntegrableOn f (Ioc (-L) (-L + 1)) := hcont.integrableOn_Ioc
  have hw : IntegrableOn (fun t : ℝ => Real.exp (s * t)) (Ioc (-L) (-L + 1)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).integrableOn_Ioc
  calc
    _ ≤ ∫ t in Ioc (-L) (-L + 1), Real.exp (s * t) := by
      apply setIntegral_mono_on hf hw measurableSet_Ioc
      intro t _
      have h0 : 0 ≤ min (max (t + L) 0) 1 := le_min (le_max_right _ _) zero_le_one
      have h1 : min (max (t + L) 0) 1 ≤ 1 := min_le_right _ _
      have hsq : (1 - min (max (t + L) 0) 1) ^ 2 ≤ 1 := by nlinarith
      have := mul_le_mul_of_nonneg_left hsq (Real.exp_pos (s * t)).le
      simpa [f] using this
    _ ≤ _ := integral_exp_boundary_layer_le s L hs


/-- On every transverse subset of the source cube, the profile error has
inverse-dimensional exponential decay. -/
theorem slab_profile_error_product_le (n : ℕ) (s L : ℝ) (hs : 0 ≤ s) (hL : 1 ≤ L)
    (K : Set (Fin n → ℝ)) (hKfinite : volume K ≠ ∞)
    (hKsub : K ⊆ Icc (fun _ => -Real.exp (s * L / (n + 1)))
      (fun _ => Real.exp (s * L / (n + 1)))) :
    (∫ p : ℝ × (Fin n → ℝ), Real.exp (s * p.1) *
      (1 - min (max (p.1 + L) 0) 1) ^ 2
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict K))) ≤
      Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1))) := by
  let ν : Measure (Fin n → ℝ) := volume.restrict K
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hKfinite
  let f : ℝ → ℝ := fun t => Real.exp (s * t) * (1 - min (max (t + L) 0) 1) ^ 2
  have hf : Integrable f (volume.restrict (Icc (-L) L)) := by
    have hc : Continuous f := by dsimp [f]; fun_prop
    exact hc.integrableOn_Icc
  have hp : Integrable (fun p : ℝ × (Fin n → ℝ) => f p.1)
      ((volume.restrict (Icc (-L) L)).prod ν) := hf.comp_fst ν
  have heq : (∫ p : ℝ × (Fin n → ℝ), f p.1
      ∂((volume.restrict (Icc (-L) L)).prod ν)) =
      (∫ t in Icc (-L) L, f t) * (volume : Measure (Fin n → ℝ)).real K := by
    rw [integral_prod _ hp]
    simp [ν, measureReal_def, mul_comm, integral_mul_const]
  have hvol : (volume : Measure (Fin n → ℝ)).real K ≤
      (2 * Real.exp (s * L / (n + 1))) ^ n := by
    have h := measureReal_mono (μ := (volume : Measure (Fin n → ℝ))) hKsub
      isCompact_Icc.measure_lt_top.ne
    rw [volume_transverse_cube n _ (Real.exp_pos _).le] at h
    exact h
  have hvol0 : 0 ≤ (volume : Measure (Fin n → ℝ)).real K := measureReal_nonneg
  change (∫ p : ℝ × (Fin n → ℝ), f p.1
    ∂((volume.restrict (Icc (-L) L)).prod ν)) ≤ _
  rw [heq]
  calc
    _ ≤ (Real.exp s * Real.exp (-(s * L))) *
        (2 * Real.exp (s * L / (n + 1))) ^ n :=
      mul_le_mul (slab_profile_error_integral_le s L hs hL) hvol hvol0
        (by positivity)
    _ = Real.exp s * ((2 * Real.exp (s * L / (n + 1))) ^ n *
        Real.exp (-(s * L))) := by ring
    _ = _ := by rw [boundary_layer_transverse_factor]; ring

end EinsteinFull.Regeneration
