import EinsteinFull.External.Source.GMPDirichletKernel
import PDEFoundation.Measure.BallVolume

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- The actual Euclidean gradient energy of a smooth cutoff is controlled by
its pointwise derivative bound and the Euclidean volume of its support ball. -/
theorem sbxB_cutoff_energy_volume {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Vec d) (r : ℝ), 0 < r →
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ sourceBall x (2 * r) →
      (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) →
      (∀ y, euclideanSq (fun i => fderiv ℝ φ y (Pi.single i 1)) ≤ 1024 / r ^ 2) →
      Integrable (fun y => euclideanSq (fun i => fderiv ℝ φ y (Pi.single i 1))) volume ∧
      (∫ y, euclideanSq (fun i => fderiv ℝ φ y (Pi.single i 1))) ≤ C * r ^ (d - 2) := by
  let v : ℝ := (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal
  have hv : 0 < v := PDE.volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num)
  refine ⟨1024 * 2 ^ d * v, by positivity, ?_⟩
  intro x r hr φ hφ hsupp hφbound hgrad
  let B := sourceBall x (2 * r)
  let F : Vec d → ℝ := fun y => euclideanSq (fun i => fderiv ℝ φ y (Pi.single i 1))
  have hr2 : 0 < 2 * r := by positivity
  have heq : B = PDE.euclideanBall x (2 * r) := by
    ext y
    change Real.sqrt (euclideanSq (y - x)) < 2 * r ↔ PDE.vecNormSq (y - x) < (2 * r) ^ 2
    rw [Real.sqrt_lt' hr2]
    rfl
  have hB : MeasurableSet B := heq ▸ (PDE.isOpen_euclideanBall x (2 * r)).measurableSet
  have hfin : volume B ≠ ⊤ := heq ▸ PDE.volume_euclideanBall_ne_top x hr2.le
  have hvol : (volume B).toReal = (2 * r) ^ d * v := by
    rw [heq]
    exact PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos x hr2
  have hcont : Continuous F := by
    dsimp [F, euclideanSq, dot, dotProduct]
    apply continuous_finsetSum
    intro i hi
    exact ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).mul
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hnonneg : ∀ y, 0 ≤ F y := by
    intro y
    dsimp [F, euclideanSq, dot, dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hzero : ∀ y, y ∉ B → F y = 0 := by
    intro y hy
    have hnot : y ∉ tsupport φ := fun h => hy (hsupp h)
    have hz : fderiv ℝ φ y = 0 := fderiv_of_notMem_tsupport ℝ hnot
    simp [F, hz, euclideanSq, dot]
  have hintB : IntegrableOn F B volume := by
    apply IntegrableOn.of_bound (lt_top_iff_ne_top.mpr hfin) hcont.aestronglyMeasurable.restrict (1024 / r ^ 2)
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg y)]
    exact hgrad y
  have hind : B.indicator F = F := by
    funext y
    by_cases hy : y ∈ B
    · simp [hy]
    · simp [hy, hzero y hy]
  have hint : Integrable F volume := by
    rw [← hind]
    exact (integrable_indicator_iff hB).2 hintB
  refine ⟨hint, ?_⟩
  have hle : (∫ y in B, F y) ≤ (1024 / r ^ 2) * (volume B).toReal := by
    let : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hfin.lt_top⟩
    have h := integral_mono_ae hintB (integrable_const (1024 / r ^ 2))
      (Filter.Eventually.of_forall hgrad)
    simpa [integral_const, Measure.real, mul_comm] using h
  have hwhole : (∫ y, F y) = ∫ y in B, F y := by
    rw [← integral_indicator hB, hind]
  rw [hwhole]
  calc
    (∫ y in B, F y) ≤ (1024 / r ^ 2) * (volume B).toReal := hle
    _ = (1024 * 2 ^ d * v) * r ^ (d - 2) := by
      rw [hvol, mul_pow]
      have hp : r ^ d = r ^ (d - 2) * r ^ 2 := by
        rw [← pow_add, Nat.sub_add_cancel hd]
      rw [hp]
      field_simp

/-- Density weighting costs only the upper ellipticity factor. -/
theorem sbxB_cutoff_weighted_energy_volume {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (x : Vec d) (r : ℝ), 0 < r →
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ sourceBall x (2 * r) →
      (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) →
      (∀ y, euclideanSq (fun i => fderiv ℝ φ y (Pi.single i 1)) ≤ 1024 / r ^ 2) →
      Integrable (fun y => ρ y * euclideanSq (fun i => fderiv ℝ φ y (Pi.single i 1))) volume ∧
      (∫ y, ρ y * euclideanSq (fun i => fderiv ℝ φ y (Pi.single i 1))) ≤
        κ⁻¹ * (C * r ^ (d - 2)) := by
  obtain ⟨C, hC, hbound⟩ := sbxB_cutoff_energy_volume hd
  refine ⟨C, hC, ?_⟩
  intro ρ α hell x r hr φ hφ hsupp hφbound hgrad
  obtain ⟨hint, hestimate⟩ := hbound x r hr φ hφ hsupp hφbound hgrad
  let F : Vec d → ℝ := fun y => euclideanSq (fun i => fderiv ℝ φ y (Pi.single i 1))
  have hF : ∀ y, 0 ≤ F y := by
    intro y
    dsimp [F, euclideanSq, dot, dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hρ (y : Vec d) : 0 ≤ ρ y := hκ.le.trans (hell.2.2 y).1
  have hmajor : Integrable (fun y => κ⁻¹ * F y) volume := hint.const_mul _
  have hw : Integrable (fun y => ρ y * F y) volume := by
    apply hmajor.mono' (hell.1.aestronglyMeasurable.mul hint.aestronglyMeasurable)
    filter_upwards with y
    change ‖ρ y * F y‖ ≤ κ⁻¹ * F y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ y) (hF y))]
    exact mul_le_mul_of_nonneg_right (hell.2.2 y).2.1 (hF y)
  refine ⟨hw, ?_⟩
  calc
    (∫ y, ρ y * F y) ≤ ∫ y, κ⁻¹ * F y :=
      integral_mono_ae hw hmajor (Filter.Eventually.of_forall fun y =>
        mul_le_mul_of_nonneg_right (hell.2.2 y).2.1 (hF y))
    _ = κ⁻¹ * ∫ y, F y := integral_const_mul _ _
    _ ≤ κ⁻¹ * (C * r ^ (d - 2)) :=
      mul_le_mul_of_nonneg_left hestimate (inv_nonneg.mpr hκ.le)

end EinsteinFull.Calculus
