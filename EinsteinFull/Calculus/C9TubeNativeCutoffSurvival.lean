import EinsteinFull.Calculus.C9TubeNativeCutoffGluing
import EinsteinFull.Calculus.C9TubeWeightedZeroPast
import EinsteinFull.Calculus.C11TubeWeightedZeroPastRepresentative

open EinsteinRelation MeasureTheory PDE Filter EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology NNReal ENNReal

namespace EinsteinFull.Calculus

/-- The native spectral kernel action is a weighted caloric function. -/
theorem c9_native_kernel_action_weighted_caloric {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ) (hT : 0 < T) :
    ∃ G : ℝ × PDE.Vec d → PDE.Vec d,
      IsWeightedCaloric ρ α (Set.Ioo 0 T) (sourceBall 0 R)
        (fun z => ∫ y, (∑' n, Real.exp (-s.eigenvalue n * z.1) *
          s.eigenfunction n z.2 * s.eigenfunction n y) * f y ∂dirichletVolume ρ R) G := by
  let I := Set.Ioo (0 : ℝ) T
  let B := sourceBall (0 : PDE.Vec d) R
  let C := ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R)
    (mul_pos two_pos hR)) : Set (PDE.Vec d))
  let F : ℝ × PDE.Vec d → ℝ := fun z => ∫ y,
    (∑' n, Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2 *
      s.eigenfunction n y) * f y ∂dirichletVolume ρ R
  have hsub : B ⊆ C := sourceBall_subset_cube R hR
  have hprod : (volume.restrict I).prod (volume.restrict B) ≤
      (volume.restrict I).prod (volume.restrict C) :=
    Measure.prod_mono le_rfl (Measure.restrict_mono_set volume hsub)
  obtain ⟨V, G, hJ, hVc, hV, hGm, hGl, hslice, htest⟩ :=
    c9_native_heat_all_strips_iterated_test hd hκ hR h s u hb hv f T
  have hF : MemLp F 2 (volume.restrict (I ×ˢ B)) :=
    c9_native_kernel_action_memLp hd hκ hR h s u hs hb hv f T
  have hGm' : AEStronglyMeasurable G (volume.restrict (I ×ˢ B)) := by
    have hh := hGm.mono_measure hprod
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using hh
  have hGl' : MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (I ×ˢ B)) := by
    have hh := hGl.mono_measure hprod
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using hh
  have hw := c9_native_kernel_action_joint_weakGradient hd hκ hR h s f T V G hJ hslice
  refine ⟨G, hF, hGm', hGl', hw, ?_⟩
  intro ψ hψ hc hsupport
  have hsupp : tsupport ψ ⊆ I ×ˢ B := by simpa only [I, interior_Ioo] using hsupport
  obtain ⟨a, b, ha, hab, hbT, hstrip⟩ := c9_compact_test_positive_strip hT ψ hc hsupp
  let S := Set.Ioo a b ×ˢ B
  have hS : S ⊆ I ×ˢ B := by
    intro z hz
    exact ⟨⟨ha.trans hz.1.1, hz.1.2.trans_le hbT⟩, hz.2⟩
  have hmeas : MeasurableSet (I ×ˢ B) :=
    measurableSet_Ioo.prod (dirichletBall (d := d) R).isOpen.measurableSet
  have hz (z : ℝ × PDE.Vec d) (hz : z ∈ (I ×ˢ B) \ S) : fderiv ℝ ψ z = 0 := by
    apply fderiv_of_notMem_tsupport ℝ
    intro hz'
    exact hz.2 (hstrip hz')
  obtain ⟨ht, hx⟩ := c9_weighted_pairings_integrable hκ h I B F G hF hGm' hGl' ψ hψ hc
  let A : ℝ × PDE.Vec d → ℝ := fun z => (ρ z.2 * F z) * fderiv ℝ ψ z (1, 0)
  let D : ℝ × PDE.Vec d → ℝ := fun z => dot ((α z.2).mulVec (G z))
    (fun i => fderiv ℝ ψ z (0, unitVector i))
  have hA : (∫ z in I ×ˢ B, A z) = ∫ z in S, A z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hS
    intro z hz'
    simp [A, hz z hz']
  have hD : (∫ z in I ×ˢ B, D z) = ∫ z in S, D z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hS
    intro z hz'
    simp [D, hz z hz', dot]
  have ht' : Integrable A ((volume.restrict (Set.Ioo a b)).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact ht.mono_measure (Measure.restrict_mono_set volume hS)
  have hx' : Integrable D ((volume.restrict (Set.Ioo a b)).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hx.mono_measure (Measure.restrict_mono_set volume hS)
  have hstripEq : (∫ z in S, A z) = ∫ z in S, D z := by
    rw [show (∫ z in S, A z) = ∫ z, A z ∂((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict B)) by rw [Measure.prod_restrict, Measure.volume_eq_prod]]
    rw [show (∫ z in S, D z) = ∫ z, D z ∂((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict B)) by rw [Measure.prod_restrict, Measure.volume_eq_prod]]
    rw [integral_prod _ ht', integral_prod _ hx']
    simpa only [A, D, F, B, unitVector] using htest a b ha hab hbT ψ hψ hc hstrip
  have hi : (∫ z in I ×ˢ B, -(ρ z.2 * F z) * fderiv ℝ ψ z (1, 0) + D z) =
      ∫ z in I ×ˢ B, -A z + D z := by
    apply integral_congr_ae
    filter_upwards with z
    simp only [A, neg_mul]
  change (∫ z in I ×ˢ B, -(ρ z.2 * F z) * fderiv ℝ ψ z (1, 0) + D z) = 0
  have hneg : Integrable (fun z => -A z) (volume.restrict (I ×ˢ B)) := ht.neg
  have hpos : Integrable D (volume.restrict (I ×ˢ B)) := hx
  rw [hi, integral_add hneg hpos, integral_neg, hA, hD, hstripEq, neg_add_cancel]



/-- Weighted caloricity restricts to any smaller spatial domain. -/
theorem c9_weighted_caloric_spatial_mono {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {I : Set ℝ}
    {U V : Set (PDE.Vec d)} (hI : MeasurableSet I) (hU : MeasurableSet U)
    (hVU : V ⊆ U) {u : ℝ × PDE.Vec d → ℝ} {G : ℝ × PDE.Vec d → PDE.Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) : IsWeightedCaloric ρ α I V u G := by
  have hsub : I ×ˢ V ⊆ I ×ˢ U := Set.prod_mono Set.Subset.rfl hVU
  have hmeasure := Measure.restrict_mono_set (volume : Measure (ℝ × PDE.Vec d)) hsub
  refine ⟨hu.1.mono_measure hmeasure, hu.2.1.mono_measure hmeasure,
    hu.2.2.1.mono_measure hmeasure, ?_, ?_⟩
  · filter_upwards [hu.2.2.2.1] with t ht
    exact EinsteinRelation.Correctors.hasWeakGradient_mono hVU ht
  · intro ψ hψ hc hs
    have hs' : tsupport ψ ⊆ interior I ×ˢ U := hs.trans (Set.prod_mono Set.Subset.rfl hVU)
    have hz (z : ℝ × PDE.Vec d) (hz : z ∈ (I ×ˢ U) \ (I ×ˢ V)) :
        fderiv ℝ ψ z = 0 := by
      apply fderiv_of_notMem_tsupport ℝ
      intro hz'
      have hh := hs hz'
      exact hz.2 ⟨interior_subset hh.1, hh.2⟩
    have heq : (∫ z in I ×ˢ U, -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j))) =
      ∫ z in I ×ˢ V, -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hI.prod hU) hsub
      intro z hz'
      simp [hz z hz', dot]
    rw [← heq]
    exact hu.2.2.2.2 ψ hψ hc hs'

/-- A continuous representative of a zero-past field vanishes on the initial slice. -/
theorem c9_zero_past_representative_at_zero {d : ℕ} {T : ℝ} (hT : 0 < T)
    (B : Set (PDE.Vec d)) (hB : IsOpen B) (u v : ℝ × PDE.Vec d → ℝ)
    (hv : ContinuousOn v (Set.Ioo (-T) T ×ˢ B))
    (heq : v =ᵐ[volume.restrict (Set.Ioo (-T) T ×ˢ B)] u)
    (hz : ∀ᵐ z ∂volume.restrict (Set.Ioo (-T) 0 ×ˢ B), u z = 0) :
    ∀ y ∈ B, v (0, y) = 0 := by
  let S := Set.Ioo (-T) 0 ×ˢ B
  let E := Set.Ioc (-T) 0 ×ˢ B
  have hsub : S ⊆ Set.Ioo (-T) T ×ˢ B := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨ht.1, lt_trans ht.2 hT⟩, hx⟩
  have hae : v =ᵐ[volume.restrict S] (fun _ => 0) := by
    have h₁ := ae_restrict_of_ae_restrict_of_subset hsub heq
    filter_upwards [h₁, hz] with z hz₁ hz₂
    exact hz₁.trans hz₂
  have hpoint : Set.EqOn v (fun _ => 0) S :=
    Measure.eqOn_open_of_ae_eq hae (isOpen_Ioo.prod hB) (hv.mono hsub)
      continuousOn_const
  have hEsub : E ⊆ Set.Ioo (-T) T ×ˢ B := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨ht.1, lt_of_le_of_lt ht.2 hT⟩, hx⟩
  have hSE : S ⊆ E := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨ht.1, ht.2.le⟩, hx⟩
  have hES : E ⊆ closure S := by
    rw [show closure S = closure (Set.Ioo (-T) 0) ×ˢ closure B from closure_prod_eq]
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    rw [closure_Ioo (by linarith : -T ≠ 0)]
    exact ⟨⟨ht.1.le, ht.2⟩, subset_closure hx⟩
  have hzero := hpoint.of_subset_closure (hv.mono hEsub) continuousOn_const hSE hES
  intro y hy
  exact hzero (show ((0 : ℝ), y) ∈ E from ⟨⟨by linarith, le_rfl⟩, hy⟩)

/-- The actual cutoff action minus one extends calorically to the zero past. -/
theorem c9_native_cutoff_zero_past_caloric {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (φ : PDE.Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hφbounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (y : PDE.Vec d) (r T : ℝ) (hr : 0 < r) (hT : 0 < T)
    (hinside : closure (sourceBall y (2*r)) ⊆ sourceBall 0 R)
    (hplateau : ∀ x ∈ sourceBall y (2*r), φ x = 1) :
    ∃ G : ℝ × PDE.Vec d → PDE.Vec d,
      IsWeightedCaloric ρ α (Set.Ioo (-T) T) (sourceBall y r)
        (fun z => if 0 < z.1 then
          (∫ x, (∑' n, Real.exp (-s.eigenvalue n*z.1) * s.eigenfunction n z.2 *
            s.eigenfunction n x) * φ x ∂dirichletVolume ρ R) - 1 else 0)
        (fun z => if 0 < z.1 then G z else 0) := by
  let f := (c9_cutoff_memLp_dirichletVolume hR h φ hφ hφbounds).toLp φ
  let F : ℝ × PDE.Vec d → ℝ := fun z => ∫ x,
    (∑' n, Real.exp (-s.eigenvalue n*z.1) * s.eigenfunction n z.2 *
      s.eigenfunction n x) * φ x ∂dirichletVolume ρ R
  have heq : (fun z : ℝ × PDE.Vec d => ∫ x,
      (∑' n, Real.exp (-s.eigenvalue n*z.1) * s.eigenfunction n z.2 *
        s.eigenfunction n x) * f x ∂dirichletVolume ρ R) = F := by
    funext z
    apply integral_congr_ae
    filter_upwards [(c9_cutoff_memLp_dirichletVolume hR h φ hφ hφbounds).coeFn_toLp] with x hx
    simp only [f, hx]
  obtain ⟨G, hcal⟩ := c9_native_kernel_action_weighted_caloric hd hκ hR h s u hs hb hv f T hT
  rw [heq] at hcal
  have hsmall : sourceBall y r ⊆ sourceBall y (2*r) := by
    intro x hx
    change euclideanNorm (x-y) < r at hx
    change euclideanNorm (x-y) < 2*r
    linarith
  have hsub : sourceBall y r ⊆ sourceBall 0 R :=
    hsmall.trans (subset_closure.trans hinside)
  have hbdd : Bornology.IsBounded (sourceBall y r) :=
    (SubdiffusiveProcess.centeredCube_isBounded (0 : PDE.Vec d)
      (mul_pos two_pos hR)).subset (hsub.trans (sourceBall_subset_cube R hR))
  have hfinite : volume (Set.Ioo (0 : ℝ) T ×ˢ sourceBall y r) ≠ ⊤ :=
    ((Metric.isBounded_Ioo (0 : ℝ) T).prod hbdd).measure_lt_top.ne
  have hlocal := c9_weighted_caloric_spatial_mono measurableSet_Ioo
    (dirichletBall (d := d) R).isOpen.measurableSet hsub hcal
  have hsubone := c11_weighted_caloric_sub_const hκ h hfinite hlocal 1
  have htrace := c9_cutoff_kernel_zero_trace hd hκ hR h s φ hφ hφbounds y r hr hinside hplateau
  refine ⟨G, ?_⟩
  exact c9_weighted_caloric_zero_past_gluing hκ hT h y (fun z => F z - 1) G hsubone htrace

/-- The native spectral heat row is jointly continuous for positive time. -/
theorem c9_native_heat_row_joint_continuous {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) :
    ContinuousOn (fun z : ℝ × PDE.Vec d => spectralHeatRow s z.1 z.2)
      (Set.Ioi 0 ×ˢ sourceBall 0 R) := by
  let K : ℝ × PDE.Vec d × PDE.Vec d → ℝ := fun z =>
    ∑' i, Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2.1 *
      s.eigenfunction i z.2.2
  have hk : ContinuousOn K {z | 0 < z.1 ∧ z.2.1 ∈ sourceBall 0 R ∧
      z.2.2 ∈ sourceBall 0 R} := spectral_heat_continuousOn hd hκ h hR s hs
  intro z hz
  have hdiag : ContinuousOn (fun w : ℝ × PDE.Vec d => K (w.1+w.1,w.2,w.2))
      (Set.Ioi 0 ×ˢ sourceBall 0 R) := by
    apply hk.comp ((continuous_fst.add continuous_fst).prodMk
      (continuous_snd.prodMk continuous_snd)).continuousOn
    intro w hw
    exact ⟨by change 0 < w.1 + w.1; exact add_pos hw.1 hw.1, hw.2, hw.2⟩
  have hcross : ContinuousOn (fun w : ℝ × PDE.Vec d => K (w.1+z.1,w.2,z.2))
      (Set.Ioi 0 ×ˢ sourceBall 0 R) := by
    apply hk.comp ((continuous_fst.add continuous_const).prodMk
      (continuous_snd.prodMk continuous_const)).continuousOn
    intro w hw
    exact ⟨by change 0 < w.1 + z.1; exact add_pos hw.1 hz.1, hw.2, hz.2⟩
  have hc : ContinuousOn (fun w : ℝ × PDE.Vec d => K (w.1+w.1,w.2,w.2) -
      2 * K (w.1+z.1,w.2,z.2) + K (z.1+z.1,z.2,z.2))
      (Set.Ioi 0 ×ˢ sourceBall 0 R) :=
    (hdiag.sub (continuousOn_const.mul hcross)).add continuousOn_const
  have hlim := hc z hz
  change Tendsto (fun w : ℝ × PDE.Vec d => K (w.1+w.1,w.2,w.2) -
      2 * K (w.1+z.1,w.2,z.2) + K (z.1+z.1,z.2,z.2))
      (nhdsWithin z (Set.Ioi 0 ×ˢ sourceBall 0 R))
      (nhds (K (z.1+z.1,z.2,z.2) - 2 * K (z.1+z.1,z.2,z.2) +
        K (z.1+z.1,z.2,z.2))) at hlim
  have hzero : K (z.1+z.1,z.2,z.2) - 2 * K (z.1+z.1,z.2,z.2) +
      K (z.1+z.1,z.2,z.2) = 0 := by ring
  rw [hzero] at hlim
  have hsq : Tendsto (fun w : ℝ × PDE.Vec d =>
      ‖spectralHeatRow s w.1 w.2 - spectralHeatRow s z.1 z.2‖ ^ 2)
      (nhdsWithin z (Set.Ioi 0 ×ˢ sourceBall 0 R)) (nhds 0) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      spectral_heat_row_inner hd hκ h hR s w.1 w.1 hw.1 hw.1 w.2 w.2 hw.2 hw.2,
      spectral_heat_row_inner hd hκ h hR s w.1 z.1 hw.1 hz.1 w.2 z.2 hw.2 hz.2,
      spectral_heat_row_inner hd hκ h hR s z.1 z.1 hz.1 hz.1 z.2 z.2 hz.2 hz.2]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun w : ℝ × PDE.Vec d =>
    Real.sqrt (‖spectralHeatRow s w.1 w.2 - spectralHeatRow s z.1 z.2‖ ^ 2))
    (nhdsWithin z (Set.Ioi 0 ×ˢ sourceBall 0 R)) (nhds (Real.sqrt 0)) at hsqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

/-- Integrating a native spectral heat row against L² data is jointly continuous. -/
theorem c9_native_heat_action_joint_continuous {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    ContinuousOn (fun z : ℝ × PDE.Vec d => ∫ y,
      (∑' i, Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 *
        s.eigenfunction i y) * f y ∂dirichletVolume ρ R)
      (Set.Ioi 0 ×ˢ sourceBall 0 R) := by
  apply ((c9_native_heat_row_joint_continuous hd hκ hR h s hs).inner
    continuousOn_const).congr
  intro z hz
  symm
  change inner ℝ (spectralHeatRow s z.1 z.2) f = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spectral_heat_row_Lp_ae_eq hd hκ h hR s z.1 hz.1 z.2 hz.2] with y hy
  change spectralHeatRow s z.1 z.2 y = _ at hy
  simp only [RCLike.inner_apply, conj_trivial, hy, mul_comm]

/-- The literal cutoff action is jointly continuous at positive times. -/
theorem c9_native_cutoff_action_joint_continuous {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (φ : PDE.Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hφbounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    ContinuousOn (fun z : ℝ × PDE.Vec d => ∫ x,
      (∑' n, Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2 *
        s.eigenfunction n x) * φ x ∂dirichletVolume ρ R)
      (Set.Ioi 0 ×ˢ sourceBall 0 R) := by
  let hp := c9_cutoff_memLp_dirichletVolume hR h φ hφ hφbounds
  have hc := c9_native_heat_action_joint_continuous hd hκ hR h s hs (hp.toLp φ)
  apply hc.congr
  intro z hz
  apply integral_congr_ae
  filter_upwards [hp.coeFn_toLp] with x hx
  rw [hx]

/-- The zero-past cutoff defect stays in the interval [-1, 0] on its
local cylinder, pointwise for every time and position. -/
theorem c9_native_cutoff_zero_past_bounds {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (φ : PDE.Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hφbounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    ∀ z : ℝ × PDE.Vec d, z.2 ∈ sourceBall 0 R →
      -1 ≤ (if 0 < z.1 then
        (∫ x, (∑' n, Real.exp (-s.eigenvalue n*z.1) * s.eigenfunction n z.2 *
          s.eigenfunction n x) * φ x ∂dirichletVolume ρ R) - 1 else 0) ∧
      (if 0 < z.1 then
        (∫ x, (∑' n, Real.exp (-s.eigenvalue n*z.1) * s.eigenfunction n z.2 *
          s.eigenfunction n x) * φ x ∂dirichletVolume ρ R) - 1 else 0) ≤ 0 := by
  let hp := c9_cutoff_memLp_dirichletVolume hR h φ hφ hφbounds
  have hf : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ hp.toLp φ x ∧ hp.toLp φ x ≤ 1 := by
    filter_upwards [hp.coeFn_toLp] with x hx
    rw [hx]
    exact hφbounds x
  intro z hz
  by_cases ht : 0 < z.1
  · let t : ℝ≥0 := ⟨z.1, ht.le⟩
    have horder := spectral_heat_action_order_of_variational hd hκ h R hR s hs u hb hv
      t ht (hp.toLp φ) hf z.2 hz
    have heq : (∫ x, (∑' n, Real.exp (-s.eigenvalue n*z.1) * s.eigenfunction n z.2 *
        s.eigenfunction n x) * hp.toLp φ x ∂dirichletVolume ρ R) =
        ∫ x, (∑' n, Real.exp (-s.eigenvalue n*z.1) * s.eigenfunction n z.2 *
          s.eigenfunction n x) * φ x ∂dirichletVolume ρ R := by
      apply integral_congr_ae
      filter_upwards [hp.coeFn_toLp] with x hx
      rw [hx]
    change (0 ≤ (∫ x, (∑' n, Real.exp (-s.eigenvalue n*z.1) * s.eigenfunction n z.2 *
        s.eigenfunction n x) * hp.toLp φ x ∂dirichletVolume ρ R)) ∧
      (∫ x, (∑' n, Real.exp (-s.eigenvalue n*z.1) * s.eigenfunction n z.2 *
        s.eigenfunction n x) * hp.toLp φ x ∂dirichletVolume ρ R) ≤ 1 at horder
    rw [heq] at horder
    simp only [ht, if_true]
    constructor <;> linarith [horder.1, horder.2]
  · simp [ht]

end EinsteinFull.Calculus
