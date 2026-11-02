import EinsteinFull.Calculus.SbxBPrescribedStartSurvivalR06

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology NNReal ENNReal

namespace EinsteinFull.Calculus

/-- The actual Hilbert orbit minus the cutoff is the literal spectral kernel
    action minus the cutoff, in the weighted Dirichlet space. -/
theorem br12_native_cutoff_orbit_ae {d : ℕ} {κ R : ℝ}
    (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
    let orbit := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ
    (orbit : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] fun x =>
      (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - φ x := by
  dsimp only
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  let f := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ)
  have ha := c16_supplied_spectral_heat_operator_ae_kernel_action s hspec t ht (hp.toLp φ)
  filter_upwards [Lp.coeFn_sub f (hp.toLp φ), ha, hp.coeFn_toLp] with x hx ha' hp'
  rw [hx]
  change f x - (hp.toLp φ) x = _
  rw [ha', hp']
  congr 1
  apply integral_congr_ae
  filter_upwards [hp.coeFn_toLp] with y hy
  rw [hy]

/-- Positivity of the native density also gives the identity almost
    everywhere for Lebesgue measure on the interior ball. -/
theorem br12_native_cutoff_orbit_ae_volume {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
    let orbit := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ
    (orbit : Vec d → ℝ) =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] fun x =>
      (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - φ x := by
  have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
    change volume.restrict (sourceBall (0 : Vec d) R) ≪
      (volume.restrict (sourceBall (0 : Vec d) R)).withDensity (fun x => ENNReal.ofReal (ρ x))
    apply withDensity_absolutelyContinuous' hell.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (hκ.trans_le (hell.2.2 x).1))
  exact hac.ae_eq (br12_native_cutoff_orbit_ae hR hell s hspec φ hφ t ht)

/-- The literal spectral kernel defect represents the same element of the
    actual weighted Hilbert space as the spectral orbit defect. -/
theorem br12_native_cutoff_orbit_L2 {d : ℕ} {κ R : ℝ}
    (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
    let orbit := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ
    let defect : Vec d → ℝ := fun x =>
      (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - φ x
    ∃ h : MemLp defect 2 (dirichletVolume ρ R), orbit = h.toLp defect := by
  dsimp only
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  let orbit := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ
  let defect : Vec d → ℝ := fun x =>
    (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - φ x
  have ha : (orbit : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] defect :=
    br12_native_cutoff_orbit_ae hR hell s hspec φ hφ t ht
  have hm : MemLp defect 2 (dirichletVolume ρ R) := (memLp_congr_ae ha).mp (Lp.memLp orbit)
  refine ⟨hm, ?_⟩
  apply Lp.ext
  exact ha.trans hm.coeFn_toLp.symm

/-- For the supplied native kernel, the same orbit has the literal
    Lebesgue-kernel cutoff action as its representative. -/
theorem br12_native_kernel_cutoff_orbit_ae {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) ∧
        K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
    let orbit := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ
    (orbit : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] fun x =>
      (∫ y in sourceBall (0 : Vec d) R, K t x y * φ y) - φ x := by
  dsimp only
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  let f := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ)
  have ha := b_supplied_spectral_cutoff_action hκ hR hell K s hspec φ hφ t ht
  filter_upwards [Lp.coeFn_sub f (hp.toLp φ), ha, hp.coeFn_toLp] with x hx ha' hp'
  rw [hx]
  change f x - (hp.toLp φ) x = _
  rw [ha', hp']

/-- Restricting the genuine Hilbert orbit to an interior plateau gives exactly
    the weighted integral of the squared literal spectral cutoff defect. -/
theorem br12_native_cutoff_orbit_restricted_norm_sq {d : ℕ} {κ R : ℝ}
    (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (V : Set (Vec d)) (hV : MeasurableSet V)
    (hplateau : ∀ x ∈ V, φ x = 1) :
    let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
    let orbit := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ
    let hr := (Lp.memLp orbit).mono_measure (Measure.restrict_le_self :
      (dirichletVolume ρ R).restrict V ≤ dirichletVolume ρ R)
    ‖hr.toLp orbit‖ ^ 2 = ∫ x in V, |(∫ y,
      (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1|^2
        ∂dirichletVolume ρ R := by
  dsimp only
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  let orbit := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ
  let hr := (Lp.memLp orbit).mono_measure (Measure.restrict_le_self :
    (dirichletVolume ρ R).restrict V ≤ dirichletVolume ρ R)
  have ha := (br12_native_cutoff_orbit_ae hR hell s hspec φ hφ t ht).filter_mono
    (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self :
      (dirichletVolume ρ R).restrict V ≤ dirichletVolume ρ R)).ae_le
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hr.coeFn_toLp, ha, ae_restrict_mem hV] with x hx hx' hxV
  rw [hx, hx', hplateau x hxV]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs]

#print axioms br12_native_cutoff_orbit_ae_volume
#print axioms br12_native_cutoff_orbit_L2
#print axioms br12_native_kernel_cutoff_orbit_ae
#print axioms br12_native_cutoff_orbit_ae
#print axioms br12_native_cutoff_orbit_restricted_norm_sq

end EinsteinFull.Calculus
