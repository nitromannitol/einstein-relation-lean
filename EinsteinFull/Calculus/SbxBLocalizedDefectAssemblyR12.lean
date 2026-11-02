import EinsteinFull.Calculus.SbxBPrescribedStartSurvivalR06
import EinsteinFull.Calculus.SbxBLocalizedL2DualityR12
import EinsteinFull.Calculus.SbxBNativeCutoffOrbitR12
import EinsteinFull.Calculus.SbxBCutoffEnergyVolumeR12
import EinsteinFull.Calculus.SbxBIntegratedAnnularForceR12

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology NNReal ENNReal

namespace EinsteinFull.Calculus

/-- The supported-test pairing estimate gives the actual weighted cutoff
energy through localized Hilbert-space duality. The pairing estimate and the
abstract duality are displayed separately. -/
theorem br12_weighted_defect_of_supported_pairing {d : ℕ} (C : ℝ) (hC : 0 ≤ C)
    {κ R : ℝ} (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (V : Set (Vec d)) (hV : MeasurableSet V)
    (hplateau : ∀ x ∈ V, φ x = 1)
    (hdual : ∀ (g : Lp ℝ 2 (dirichletVolume ρ R)) (A : ℝ), 0 ≤ A →
      (∀ f : Lp ℝ 2 (dirichletVolume ρ R),
        (∀ᵐ x ∂(dirichletVolume ρ R), x ∉ V → f x = 0) →
        |inner ℝ g f| ≤ A * ‖f‖) →
      (∫ x in V, |g x|^2 ∂dirichletVolume ρ R) ≤ A^2)
    (hpair : let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
      let g := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ
      ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
        (∀ᵐ x ∂(dirichletVolume ρ R), x ∉ V → f x = 0) →
        |inner ℝ g f| ≤ C * ‖f‖) :
    (∫ x in V, |(∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1|^2
        ∂dirichletVolume ρ R) ≤ C^2 := by
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  let p := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ)
  let g := p - hp.toLp φ
  have ha := c16_supplied_spectral_heat_operator_ae_kernel_action s hspec t ht (hp.toLp φ)
  have hg : (g : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] fun x =>
      (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - φ x := by
    filter_upwards [Lp.coeFn_sub p (hp.toLp φ), ha, hp.coeFn_toLp] with x hx hx' hxφ
    rw [hx]
    change p x - (hp.toLp φ) x = _
    rw [hx', hxφ]
    congr 1
    apply integral_congr_ae
    filter_upwards [hp.coeFn_toLp] with y hy
    rw [hy]
  have heq : (∫ x in V, |g x|^2 ∂dirichletVolume ρ R) =
      ∫ x in V, |(∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1|^2
        ∂dirichletVolume ρ R := by
    apply integral_congr_ae
    filter_upwards [hg.filter_mono (Measure.absolutelyContinuous_of_le
      (Measure.restrict_le_self : (dirichletVolume ρ R).restrict V ≤ _)).ae_le,
      ae_restrict_mem hV] with x hx hxV
    rw [hx, hplateau x hxV]
  rw [← heq]
  exact hdual g C hC hpair

/-- The literal slice estimate for the supplied native cutoff action implies the
spacetime estimate. The slice estimate remains an explicit input. -/
theorem br12_native_defect_spacetime_of_slice {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hφbounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (x : Vec d) (r T D : ℝ) (hr : 0 < r) (hT : 0 < T) (hD : 0 < D)
    (hinside : sourceBall x (r/2) ⊆ sourceBall 0 R)
    (hslice : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      (∫ z in sourceBall x (r/2), |(∫ y,
        (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n z *
          s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1|^2) ≤
        D * t * r^(d-2) * Real.exp (-(r^2 / (D*t)))) :
    (∫ z in Set.Ioo (0 : ℝ) T ×ˢ sourceBall x (r/2), |(∫ y,
      (∑' n, Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2 *
        s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1|^2) ≤
      D * T^2 * r^(d-2) * Real.exp (-(r^2 / (D*T))) := by
  let V := sourceBall x (r/2)
  let F : ℝ × Vec d → ℝ := fun z => (∫ y,
    (∑' n, Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2 *
      s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1
  let hp := c9_cutoff_memLp_dirichletVolume hR hell φ hφ hφbounds
  obtain ⟨u, hb, hv⟩ := b_supplied_modes_have_dirichlet_carriers hκ hR hell s
  have hs := br06_native_spectral_eigenvalue_tendsto_atTop hd hκ hR hell s
  have hmem := c9_native_kernel_action_memLp hd hκ hR hell s u hs hb hv (hp.toLp φ) T
  have heq : (fun z : ℝ × Vec d => ∫ y,
      (∑' n, Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2 *
        s.eigenfunction n y) * (hp.toLp φ) y ∂dirichletVolume ρ R) =
      (fun z => ∫ y, (∑' n, Real.exp (-s.eigenvalue n * z.1) *
        s.eigenfunction n z.2 * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) := by
    funext z
    apply integral_congr_ae
    filter_upwards [hp.coeFn_toLp] with y hy
    rw [hy]
  rw [heq] at hmem
  have hsub : Set.Ioo (0 : ℝ) T ×ˢ V ⊆ Set.Ioo 0 T ×ˢ sourceBall (0 : Vec d) R :=
    Set.prod_mono Set.Subset.rfl hinside
  haveI : IsFiniteMeasure (volume.restrict V) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hinside).trans_lt (lt_top_iff_ne_top.mpr
      (c18_sourceBall_measure_ne_top (0 : Vec d) R))).ne
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) T ×ˢ V)) := by
    have hfinite : IsFiniteMeasure ((volume.restrict (Set.Ioo (0 : ℝ) T)).prod
        (volume.restrict V)) := inferInstance
    rwa [Measure.prod_restrict] at hfinite
  have hF : MemLp F 2 (volume.restrict (Set.Ioo 0 T ×ˢ V)) := by
    change MemLp ((fun z : ℝ × Vec d => ∫ y,
      (∑' n, Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2 *
        s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - (fun _ => 1)) 2 _
    exact (hmem.mono_measure (Measure.restrict_mono_set volume hsub)).sub (memLp_const (1 : ℝ))
  let E := D * r^(d-2) * Real.exp (-(r^2 / (D*T)))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlin : ∀ t ∈ Set.Ioo (0 : ℝ) T, (∫ z in V, |F (t,z)|^2) ≤ E*t := by
    intro t ht
    have hden : D*t ≤ D*T := mul_le_mul_of_nonneg_left ht.2.le hD.le
    have hfrac : r^2 / (D*T) ≤ r^2 / (D*t) :=
      div_le_div_of_nonneg_left (sq_nonneg r) (mul_pos hD ht.1) hden
    have hexp : Real.exp (-(r^2 / (D*t))) ≤ Real.exp (-(r^2 / (D*T))) :=
      Real.exp_le_exp.mpr (neg_le_neg hfrac)
    have hmul := mul_le_mul_of_nonneg_left hexp
      (mul_nonneg (mul_nonneg hD.le ht.1.le) (pow_nonneg hr.le (d-2)))
    exact (hslice t ht).trans (by simpa only [E, mul_assoc, mul_comm, mul_left_comm] using hmul)
  have hresult := b_spacetime_L2_of_slice_linear_bound hT hE V F hF hlin
  simpa only [F, V, E, mul_assoc, mul_comm, mul_left_comm] using hresult

/-- Parabolic scaling converts the sharper spacetime bound to the form used
by the normalized local defect estimate. -/
theorem br12_parabolic_defect_scale {d : ℕ} (hd : 2 ≤ d)
    {D T r : ℝ} (hD : 0 ≤ D) (hT : 0 ≤ T) (hr : 0 ≤ r)
    (hTr : T ≤ r^2) :
    D * T^2 * r^(d-2) * Real.exp (-(r^2 / (D*T))) ≤
      D * T * r^d * Real.exp (-(r^2 / (D*T))) := by
  have hp : r^(d-2) * r^2 = r^d := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  calc
    D * T^2 * r^(d-2) * Real.exp (-(r^2 / (D*T))) =
        (D*T*r^(d-2)*Real.exp (-(r^2 / (D*T))))*T := by ring
    _ ≤ (D*T*r^(d-2)*Real.exp (-(r^2 / (D*T))))*r^2 :=
      mul_le_mul_of_nonneg_left hTr (by positivity)
    _ = D * T * r^d * Real.exp (-(r^2 / (D*T))) := by rw [← hp]; ring

/-- The parabolic spacetime estimate, conditional on the displayed native slice estimate. -/
theorem br12_native_defect_parabolic_spacetime_of_slice {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hφbounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (x : Vec d) (r T D : ℝ) (hr : 0 < r) (hT : 0 < T) (hD : 0 < D)
    (hinside : sourceBall x (r/2) ⊆ sourceBall 0 R) (hTr : T ≤ r^2)
    (hslice : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      (∫ z in sourceBall x (r/2), |(∫ y,
        (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n z *
          s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1|^2) ≤
        D * t * r^(d-2) * Real.exp (-(r^2 / (D*t)))) :
    (∫ z in Set.Ioo (0 : ℝ) T ×ˢ sourceBall x (r/2), |(∫ y,
      (∑' n, Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2 *
        s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1|^2) ≤
      D * T * r^d * Real.exp (-(r^2 / (D*T))) := by
  exact (br12_native_defect_spacetime_of_slice hd hκ hR hell s φ hφ hφbounds
    x r T D hr hT hD hinside hslice).trans
    (br12_parabolic_defect_scale hd hD.le hT.le hr.le hTr)

/-- Local unweighted energy is controlled by the actual density-weighted energy. -/
theorem br12_local_unweighted_energy_le {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (V : Set (Vec d))
    (hinside : V ⊆ sourceBall (0 : Vec d) R)
    (g : Lp ℝ 2 (dirichletVolume ρ R)) :
    (∫ x in V, |g x| ^ 2) ≤ κ⁻¹ *
      (∫ x in V, |g x| ^ 2 ∂dirichletVolume ρ R) := by
  have hle : volume.restrict V ≤ ENNReal.ofReal κ⁻¹ • (dirichletVolume ρ R).restrict V := by
    have h := Measure.restrict_mono (μ := volume.restrict (sourceBall (0 : Vec d) R))
      (ν := ENNReal.ofReal κ⁻¹ • dirichletVolume ρ R) (Set.Subset.rfl : V ⊆ V)
      (c9_native_lebesgue_measure_le hκ hell)
    simpa only [Measure.restrict_restrict_of_subset hinside, Measure.restrict_smul] using h
  have hint : Integrable (fun x => |g x| ^ 2) ((dirichletVolume ρ R).restrict V) := by
    have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
    simpa only [Real.norm_eq_abs] using h.mono_measure
      (Measure.restrict_le_self : (dirichletVolume ρ R).restrict V ≤ _)
  have hs := hint.smul_measure (ENNReal.ofReal_ne_top : ENNReal.ofReal κ⁻¹ ≠ ⊤)
  have h := integral_mono_measure hle (ae_of_all _ fun x => sq_nonneg |g x|) hs
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hκ.le),
    smul_eq_mul] using h

#print axioms br12_local_unweighted_energy_le

/-- A supported spectral pairing bound controls the weighted cutoff defect. -/
theorem br12_weighted_defect_of_pairing {d : ℕ} (C : ℝ) (hC : 0 ≤ C)
    {κ R : ℝ} (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (V : Set (Vec d)) (hV : MeasurableSet V)
    (hplateau : ∀ x ∈ V, φ x = 1)
    (hpair : let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
      let g := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ
      ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
        (∀ᵐ x ∂(dirichletVolume ρ R), x ∉ V → f x = 0) →
        |inner ℝ g f| ≤ C * ‖f‖) :
    (∫ x in V, |(∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1|^2
        ∂dirichletVolume ρ R) ≤ C^2 := by
  exact br12_weighted_defect_of_supported_pairing C hC hR hell s hspec φ hφ t ht
    V hV hplateau (fun g A hA htest =>
      EinsteinFull.sbxB_localized_l2_duality ρ R V hV g A hA htest) hpair

#print axioms br12_weighted_defect_of_pairing

/-- A supported pairing bound controls the literal unweighted cutoff defect. -/
theorem br12_unweighted_defect_of_pairing {d : ℕ} (C : ℝ) (hC : 0 ≤ C)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (V : Set (Vec d)) (hV : MeasurableSet V)
    (hinside : V ⊆ sourceBall (0 : Vec d) R) (hplateau : ∀ x ∈ V, φ x = 1)
    (hpair : let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
      let g := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ
      ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
        (∀ᵐ x ∂(dirichletVolume ρ R), x ∉ V → f x = 0) →
        |inner ℝ g f| ≤ C * ‖f‖) :
    (∫ x in V, |(∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1|^2)
        ≤ κ⁻¹ * C^2 := by
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  let g := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ
  have hw : (∫ x in V, |g x| ^ 2 ∂dirichletVolume ρ R) ≤ C ^ 2 :=
    EinsteinFull.sbxB_localized_l2_duality ρ R V hV g C hC hpair
  have ha := (br12_native_cutoff_orbit_ae_volume hκ hR hell s hspec φ hφ t ht).filter_mono
    (Measure.absolutelyContinuous_of_le (Measure.restrict_mono_set volume hinside)).ae_le
  have heq : (∫ x in V, |g x| ^ 2) =
      ∫ x in V, |(∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1|^2 := by
    apply integral_congr_ae
    filter_upwards [ha, ae_restrict_mem hV] with x hx hxV
    rw [hx, hplateau x hxV]
  rw [← heq]
  exact (br12_local_unweighted_energy_le hκ hell V hinside g).trans
    (mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hκ.le))

#print axioms br12_unweighted_defect_of_pairing

/-- A squared supported pairing estimate gives the literal unweighted defect. -/
theorem br12_unweighted_defect_of_squared_pairing {d : ℕ} (K : ℝ) (hK : 0 ≤ K)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (V : Set (Vec d)) (hV : MeasurableSet V)
    (hinside : V ⊆ sourceBall (0 : Vec d) R) (hplateau : ∀ x ∈ V, φ x = 1)
    (hpair : let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
      let g := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ
      ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
        (∀ᵐ x ∂(dirichletVolume ρ R), x ∉ V → f x = 0) →
        |inner ℝ g f| ^ 2 ≤ K * ‖f‖ ^ 2) :
    (∫ x in V, |(∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1|^2)
        ≤ κ⁻¹ * K := by
  have hlinear : let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
      let g := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ
      ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
        (∀ᵐ x ∂(dirichletVolume ρ R), x ∉ V → f x = 0) →
        |inner ℝ g f| ≤ Real.sqrt K * ‖f‖ := by
    dsimp only at hpair ⊢
    intro f hf
    have h := hpair f hf
    have hs := Real.sq_sqrt hK
    have hn : 0 ≤ Real.sqrt K * ‖f‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have heq : (Real.sqrt K * ‖f‖) ^ 2 = K * ‖f‖ ^ 2 := by rw [mul_pow, hs]
    rw [← heq] at h
    have hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
    have habs := abs_nonneg (inner ℝ (SpectralHeat.heatOperator (spectralHeatBasis s)
      s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ) f)
    nlinarith
  have h := br12_unweighted_defect_of_pairing (Real.sqrt K) (Real.sqrt_nonneg K)
    hκ hR hell s hspec φ hφ t ht V hV hinside hplateau hlinear
  simpa only [Real.sq_sqrt hK] using h

#print axioms br12_unweighted_defect_of_squared_pairing

/-- Absorb positive prefactors and Gaussian denominators into one constant. -/
@[nolint unusedArguments]
theorem br12_absorb_gaussian_constants (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) :
    ∃ D : ℝ, 0 < D ∧ ∀ q z : ℝ, 0 ≤ q → 0 ≤ z →
      A * z * Real.exp (-q / B) ≤ D * z * Real.exp (-q / D) := by
  let D := max A B + 1
  have hAD : A ≤ D := le_trans (le_max_left A B) (by dsimp [D]; linarith)
  have hBD : B ≤ D := le_trans (le_max_right A B) (by dsimp [D]; linarith)
  have hD : 0 < D := lt_of_lt_of_le hB hBD
  refine ⟨D, hD, ?_⟩
  intro q z hq hz
  have hdiv : q / D ≤ q / B := div_le_div_of_nonneg_left hq hB hBD
  have hexp : Real.exp (-q / B) ≤ Real.exp (-q / D) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hdiv
  calc
    A * z * Real.exp (-q / B) ≤ D * z * Real.exp (-q / B) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAD hz) (Real.exp_pos _).le
    _ ≤ D * z * Real.exp (-q / D) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hD.le hz)

#print axioms br12_absorb_gaussian_constants

/-- The cutoff gradient vanishes on its open plateau, while the half-radius
ball is separated from the complement of that plateau. -/
@[nolint unusedArguments]
theorem br12_cutoff_plateau_separation {d : ℕ} (x : Vec d) (r : ℝ)
    (hr : 0 < r) (φ : Vec d → ℝ)
    (hplateau : ∀ z ∈ sourceBall x r, φ z = 1) :
    (∀ z ∈ sourceBall x r, fderiv ℝ φ z = 0) ∧
    (∀ z ∉ sourceBall x r, ∀ y ∈ sourceBall x (r/2),
      r/2 ≤ euclideanNorm (z-y)) := by
  constructor
  · intro z hz
    have hloc : φ =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
      filter_upwards [(c17_isOpen_sourceBall x r).mem_nhds hz] with w hw
      exact hplateau w hw
    simpa using hloc.fderiv_eq (𝕜 := ℝ)
  · intro z hz y hy
    have hz' : r ≤ euclideanNorm (z-x) := le_of_not_gt hz
    have hy' : euclideanNorm (y-x) < r/2 := hy
    have heq : z-x = (z-y)+(y-x) := by abel
    have htri := TimeChange.euclideanNorm_add_le (z-y) (y-x)
    rw [← heq] at htri
    linarith

#print axioms br12_cutoff_plateau_separation

/-- A native cutoff carrier has gradient supported off the plateau and its
actual gradient energy is bounded uniformly by the cutoff scale. -/
@[nolint unusedArguments]
theorem br12_cutoff_carrier_annular_energy {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (hell : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
      (x : Vec d) (r : ℝ), 0 < r →
      ∀ φ : Vec d → ℝ, ∀ hφ : IsSpatialTest (sourceBall 0 R) φ,
      ∀ hφbounds : (∀ z, 0 ≤ φ z ∧ φ z ≤ 1),
      (∀ z ∈ sourceBall x r, φ z = 1) →
      tsupport φ ⊆ sourceBall x (2*r) →
      (∀ z, euclideanSq (fun i => fderiv ℝ φ z (Pi.single i 1)) ≤ 1024 / r^2) →
      ∃ v : DirichletHilbertSpace (d := d) R hR,
        dirichletHilbertInclusion ρ R hR κ⁻¹ (fun z _ => (hell.2.2 z).2.1) v =
          (c9_cutoff_memLp_dirichletVolume hR hell φ hφ hφbounds).toLp φ ∧
        (∀ᵐ z ∂volume.restrict (sourceBall (0 : Vec d) R),
          z ∉ (sourceBall x r)ᶜ → ∀ i : Fin d, v.val (some i) z = 0) ∧
        (∫ z in (sourceBall x r)ᶜ, euclideanSq (fun i => v.val (some i) z)
          ∂(volume.restrict (sourceBall (0 : Vec d) R))) ≤ C * r^(d-2) := by
  obtain ⟨C, hC, henergy⟩ := sbxB_cutoff_energy_volume hd
  refine ⟨C, hC, ?_⟩
  intro ρ α hell R hR x r hr φ hφ hφbounds hplateau hsupp hgrad
  obtain ⟨v, hv, hvg⟩ := c9_cutoff_native_dirichlet_datum hR hell φ hφ hφbounds
  have hvg' : ∀ᵐ z ∂volume.restrict (sourceBall (0 : Vec d) R),
      ∀ i : Fin d, v.val (some i) z = fderiv ℝ φ z (unitVector i) := ae_all_iff.mpr hvg
  have hsupport : ∀ᵐ z ∂volume.restrict (sourceBall (0 : Vec d) R),
      z ∉ (sourceBall x r)ᶜ → ∀ i : Fin d, v.val (some i) z = 0 := by
    filter_upwards [hvg'] with z hz hzA i
    have hzB : z ∈ sourceBall x r := by simpa using hzA
    rw [hz i, (br12_cutoff_plateau_separation x r hr φ hplateau).1 z hzB]
    rfl
  obtain ⟨hint, hbound⟩ := henergy x r hr φ hφ.1 hsupp hφbounds hgrad
  have heq : (∫ z in (sourceBall x r)ᶜ, euclideanSq (fun i => v.val (some i) z)
      ∂(volume.restrict (sourceBall (0 : Vec d) R))) =
      ∫ z in (sourceBall x r)ᶜ, euclideanSq (fun i => fderiv ℝ φ z (Pi.single i 1))
        ∂(volume.restrict (sourceBall (0 : Vec d) R)) := by
    apply integral_congr_ae
    filter_upwards [hvg'.filter_mono (Measure.absolutelyContinuous_of_le
      (Measure.restrict_le_self : (volume.restrict (sourceBall (0 : Vec d) R)).restrict
        (sourceBall x r)ᶜ ≤ _)).ae_le] with z hz
    congr 1
    funext i
    simpa only [unitVector] using hz i
  have hle : (volume.restrict (sourceBall (0 : Vec d) R)).restrict (sourceBall x r)ᶜ ≤ volume :=
    Measure.restrict_le_self.trans Measure.restrict_le_self
  have hnonneg : ∀ᵐ z ∂volume,
      0 ≤ euclideanSq (fun i => fderiv ℝ φ z (Pi.single i 1)) := by
    filter_upwards with z
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  refine ⟨v, hv, hsupport, ?_⟩
  rw [heq]
  exact (integral_mono_measure hle hnonneg hint).trans hbound

#print axioms br12_cutoff_carrier_annular_energy

/-- The annular weak forcing controls supported native cutoff pairings. -/
theorem br12_native_cutoff_pairing_squared {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (hell : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
      (s : DirichletSpectralResolution ρ α R) (x : Vec d) (r : ℝ), 0 < r →
      ∀ φ : Vec d → ℝ, ∀ hφ : IsSpatialTest (sourceBall 0 R) φ,
      ∀ hφbounds : (∀ z, 0 ≤ φ z ∧ φ z ≤ 1),
      (∀ z ∈ sourceBall x r, φ z = 1) →
      tsupport φ ⊆ sourceBall x (2*r) →
      (∀ z, euclideanSq (fun i => fderiv ℝ φ z (Pi.single i 1)) ≤ 1024 / r^2) →
      ∀ (T : ℝ), 0 < T → ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
      (∀ᵐ z ∂dirichletVolume ρ R, z ∉ sourceBall x (r/2) → f z = 0) →
      let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
      |inner ℝ (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) T.toNNReal (hp.toLp φ) - hp.toLp φ) f|^2 ≤
      4 * κ⁻¹ ^ 3 * C * T * r^(d-2) *
        Real.exp (-(r/2)^2 / (8 * (4 * κ⁻¹^2) * T)) * ‖f‖^2 := by
  obtain ⟨C, hC, hcarrier⟩ := br12_cutoff_carrier_annular_energy hd hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell R hR s x r hr φ hφ hφbounds hplateau hsupp hgrad T hT f hf
  obtain ⟨v, hv, hvsupp, hvenergy⟩ := hcarrier ρ α hell R hR x r hr φ hφ
    hφbounds hplateau hsupp hgrad
  have hne : (sourceBall x (r/2)).Nonempty := by
    refine ⟨x, ?_⟩
    simp [sourceBall, euclideanNorm, euclideanSq, dot, hr]
  obtain ⟨Q, hQ, hdecay, hforce⟩ := br12_integrated_annular_force_squared hd hκ hell R hR s
    (sourceBall x r)ᶜ (sourceBall x (r/2)) (c17_isOpen_sourceBall x r).measurableSet.compl
    hne (r/2) (by linarith) (br12_cutoff_plateau_separation x r hr φ hplateau).2 f hf v hvsupp T hT
  let X := ∫ t in 0..T, br07_native_restricted_gradient R hR (sourceBall x r)ᶜ Q f t
  let E := ∫ z in (sourceBall x r)ᶜ, euclideanSq (fun i => v.val (some i) z)
    ∂(volume.restrict (sourceBall (0 : Vec d) R))
  have hX : 0 ≤ X := by
    apply intervalIntegral.integral_nonneg_of_forall hT.le
    intro t
    unfold br07_native_restricted_gradient
    split
    · apply integral_nonneg
      intro z
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    · exact le_refl _
  have hE : 0 ≤ E := by
    apply integral_nonneg
    intro z
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hboundX : X ≤ κ⁻¹ * (Real.exp (-(r/2)^2 / (8 * (4 * κ⁻¹^2) * T)) * ‖f‖^2) := by
    apply (le_inv_mul_iff₀ hκ).2
    exact hdecay
  have hEbound : E ≤ C * r^(d-2) := hvenergy
  have hk : 0 ≤ 4 * κ⁻¹^2 * T := by positivity
  have hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  have heq : inner ℝ (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) T.toNNReal (hp.toLp φ) - hp.toLp φ) f =
      inner ℝ (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) T.toNNReal f)
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun z _ => (hell.2.2 z).2.1) v) -
      inner ℝ f (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun z _ => (hell.2.2 z).2.1) v) := by
    rw [hv, inner_sub_left, SpectralHeat.heatOperator_symmetric]
    rw [real_inner_comm (hp.toLp φ) _, real_inner_comm (hp.toLp φ) f]
  dsimp only
  rw [heq]
  calc
    _ ≤ (4 * κ⁻¹^2 * T) * X * E := hforce
    _ ≤ (4 * κ⁻¹^2 * T) *
        (κ⁻¹ * (Real.exp (-(r/2)^2 / (8 * (4 * κ⁻¹^2) * T)) * ‖f‖^2)) *
        (C * r^(d-2)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hboundX hk) hEbound hE
        (mul_nonneg hk (mul_nonneg (inv_nonneg.mpr hκ.le)
          (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))))
    _ = _ := by ring

#print axioms br12_native_cutoff_pairing_squared

/-- The supplied native spectral cutoff has exponentially small local defect. -/
theorem br12_native_cutoff_localized_defect {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (hell : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
      (s : DirichletSpectralResolution ρ α R),
      (∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          Summable (fun n => Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y)) →
      ∀ (x : Vec d) (r : ℝ), 0 < r →
      sourceBall x (r/2) ⊆ sourceBall 0 R →
      ∀ φ : Vec d → ℝ, IsSpatialTest (sourceBall 0 R) φ →
      (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) →
      (∀ z ∈ sourceBall x r, φ z = 1) →
      tsupport φ ⊆ sourceBall x (2*r) →
      (∀ z, euclideanSq (fun i => fderiv ℝ φ z (Pi.single i 1)) ≤ 1024 / r^2) →
      ∀ T : ℝ, 0 < T →
      (∫ z in sourceBall x (r/2), |(∫ y,
        (∑' n, Real.exp (-s.eigenvalue n * T) * s.eigenfunction n z *
          s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1|^2) ≤
        D * T * r^(d-2) * Real.exp (-(r^2 / (D*T))) := by
  obtain ⟨C, hC, hpair⟩ := br12_native_cutoff_pairing_squared hd hκ
  obtain ⟨D, hD, habsorb⟩ := br12_absorb_gaussian_constants
    (4 * κ⁻¹^4 * C) (128 * κ⁻¹^2) (by positivity) (by positivity)
  refine ⟨D, hD, ?_⟩
  intro ρ α hell R hR s hspec x r hr hinside φ hφ hφbounds hplateau hsupp hgrad T hT
  let K := 4 * κ⁻¹ ^ 3 * C * T * r^(d-2) *
    Real.exp (-(r/2)^2 / (8 * (4 * κ⁻¹^2) * T))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hplateau' : ∀ z ∈ sourceBall x (r/2), φ z = 1 := by
    intro z hz
    apply hplateau
    change euclideanNorm (z-x) < r at ⊢
    change euclideanNorm (z-x) < r/2 at hz
    linarith
  have hp : let hmem := c16_spatial_test_memLp_dirichlet hR hell φ hφ
      let g := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) T.toNNReal (hmem.toLp φ) - hmem.toLp φ
      ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
        (∀ᵐ z ∂dirichletVolume ρ R, z ∉ sourceBall x (r/2) → f z = 0) →
        |inner ℝ g f|^2 ≤ K * ‖f‖^2 := by
    dsimp only
    intro f hf
    exact hpair ρ α hell R hR s x r hr φ hφ hφbounds hplateau hsupp hgrad T hT f hf
  have hslice := br12_unweighted_defect_of_squared_pairing K hK hκ hR hell s hspec φ hφ
    T.toNNReal (by simpa using hT) (sourceBall x (r/2))
    (c17_isOpen_sourceBall x (r/2)).measurableSet hinside hplateau' hp
  have hexp : -(r/2)^2 / (8 * (4 * κ⁻¹^2) * T) = -(r^2/T) / (128 * κ⁻¹^2) := by
    field_simp
    <;> ring
  have hexp' : -(r^2/T) / D = -(r^2 / (D*T)) := by field_simp <;> ring
  have hs := habsorb (r^2/T) (T * r^(d-2)) (by positivity) (by positivity)
  rw [hexp'] at hs
  have heq : κ⁻¹ * K = (4 * κ⁻¹^4 * C) * (T * r^(d-2)) *
      Real.exp (-(r^2/T) / (128 * κ⁻¹^2)) := by
    dsimp [K]
    rw [hexp]
    ring
  rw [heq] at hslice
  have hfinal := hslice.trans hs
  simpa only [Real.coe_toNNReal _ hT.le, mul_assoc] using hfinal

#print axioms br12_native_cutoff_localized_defect

/-- The native localized defect obeys the parabolic spacetime estimate. -/
theorem br12_native_cutoff_localized_spacetime {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (hell : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
      (s : DirichletSpectralResolution ρ α R),
      (∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          Summable (fun n => Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y)) →
      ∀ (x : Vec d) (r : ℝ), 0 < r →
      sourceBall x (r/2) ⊆ sourceBall 0 R →
      ∀ φ : Vec d → ℝ, IsSpatialTest (sourceBall 0 R) φ →
      (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) →
      (∀ z ∈ sourceBall x r, φ z = 1) →
      tsupport φ ⊆ sourceBall x (2*r) →
      (∀ z, euclideanSq (fun i => fderiv ℝ φ z (Pi.single i 1)) ≤ 1024 / r^2) →
      ∀ T : ℝ, 0 < T → T ≤ r^2 →
      (∫ z in Set.Ioo (0 : ℝ) T ×ˢ sourceBall x (r/2), |(∫ y,
        (∑' n, Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2 *
          s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1|^2) ≤
        D * T * r^d * Real.exp (-(r^2 / (D*T))) := by
  obtain ⟨D, hD, hslice⟩ := br12_native_cutoff_localized_defect hd hκ
  refine ⟨D, hD, ?_⟩
  intro ρ α hell R hR s hspec x r hr hinside φ hφ hφbounds hplateau hsupp hgrad T hT hTr
  apply br12_native_defect_parabolic_spacetime_of_slice hd hκ hR hell s φ hφ hφbounds
    x r T D hr hT hD hinside hTr
  intro t ht
  exact hslice ρ α hell R hR s hspec x r hr hinside φ hφ hφbounds hplateau hsupp hgrad t ht.1

#print axioms br12_native_cutoff_localized_spacetime

#print axioms br12_weighted_defect_of_supported_pairing
#print axioms br12_native_defect_spacetime_of_slice
#print axioms br12_parabolic_defect_scale
#print axioms br12_native_defect_parabolic_spacetime_of_slice

end EinsteinFull.Calculus
