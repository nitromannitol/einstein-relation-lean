import EinsteinFull.Calculus.C13TubeWeightedEnergyTrace

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- The spatial affine map takes the unit source ball to the source ball of radius r. -/
theorem c17_mem_sourceBall_affine_iff {d : ℕ} (y x : Vec d) {r : ℝ} (hr : 0 < r) :
    y + r • x ∈ sourceBall y r ↔ x ∈ sourceBall (0 : Vec d) 1 := by
  simp only [sourceBall, Set.mem_ofPred_eq, add_sub_cancel_left, sub_zero,
    TimeChange.euclideanNorm_smul, abs_of_pos hr]
  constructor <;> intro h <;> nlinarith

/-- The spatial affine map is a measurable embedding. -/
theorem c17_spatial_affine_embedding {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (fun x : Vec d => y + r • x) := by
  have h := ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft y)).measurableEmbedding
  exact h

/-- The Jacobian of the spatial affine change of variables on Lebesgue measure. -/
theorem c17_spatial_affine_map_volume {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r) :
    Measure.map (fun x : Vec d => y + r • x) volume =
      ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹) • (volume : Measure (Vec d)) := by
  rw [show (fun x : Vec d => y + r • x) =
    (fun x : Vec d => y + x) ∘ (fun x : Vec d => r • x) from rfl]
  rw [← Measure.map_map (measurable_const_add y) (measurable_const_smul r)]
  rw [Measure.map_addHaar_smul volume hr.ne']
  rw [Measure.map_smul, (measurePreserving_add_left volume y).map_eq, abs_inv]
  exact (measurable_const_add y).aemeasurable

/-- Source balls are open in the coordinate topology. -/
theorem c17_isOpen_sourceBall {d : ℕ} (y : Vec d) (r : ℝ) : IsOpen (sourceBall y r) := by
  have hsum : Continuous (fun v : Vec d => ∑ j, v j * v j) :=
    continuous_finset_sum Finset.univ fun j _ => (continuous_apply j).mul (continuous_apply j)
  have hn : Continuous (fun v : Vec d => euclideanNorm v) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp hsum
  exact isOpen_lt (hn.comp (continuous_id.sub continuous_const)) continuous_const

/-- Spatial affine pullback preserves local integrability on source balls. -/
theorem c17_locallyIntegrableOn_spatial_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {f : Vec d → ℝ} (hf : LocallyIntegrableOn f (sourceBall y r) volume) :
    LocallyIntegrableOn (fun x => f (y + r • x)) (sourceBall (0 : Vec d) 1) volume := by
  let T : Vec d ≃ₜ Vec d := (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft y)
  have hmap : Measure.map T volume =
      ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹) • (volume : Measure (Vec d)) :=
    c17_spatial_affine_map_volume y hr
  rw [locallyIntegrableOn_iff (c17_isOpen_sourceBall 0 1).isLocallyClosed]
  rw [locallyIntegrableOn_iff (c17_isOpen_sourceBall y r).isLocallyClosed] at hf
  intro K hK hKc
  have hTK : IsCompact (T '' K) := hKc.image T.continuous
  have hTKsub : T '' K ⊆ sourceBall y r := by
    rintro _ ⟨x, hx, rfl⟩
    exact (c17_mem_sourceBall_affine_iff y x hr).2 (hK hx)
  have hint : IntegrableOn f (T '' K) (Measure.map T volume) := by
    rw [hmap, IntegrableOn, Measure.restrict_smul]
    exact (hf _ hTKsub hTK).smul_measure ENNReal.ofReal_ne_top
  have h := (T.measurableEmbedding.integrableOn_map_iff).1 hint
  rwa [T.injective.preimage_image] at h

/-- The spatial Jacobian restricted to the source ball. -/
theorem c17_spatial_affine_map_sourceBall {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r) :
    Measure.map (fun x : Vec d => y + r • x)
      (volume.restrict (sourceBall (0 : Vec d) 1)) =
      ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹) •
        (volume : Measure (Vec d)).restrict (sourceBall y r) := by
  have hp : (fun x : Vec d => y + r • x) ⁻¹' sourceBall y r = sourceBall (0 : Vec d) 1 := by
    ext x
    exact c17_mem_sourceBall_affine_iff y x hr
  rw [← hp, ← Measure.restrict_map (c17_spatial_affine_embedding y hr).measurable
    (c17_isOpen_sourceBall y r).measurableSet, c17_spatial_affine_map_volume y hr,
    Measure.restrict_smul]

/-- Change of variables for integrals on spatial source balls. -/
theorem c17_integral_sourceBall_spatial_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (f : Vec d → ℝ) :
    (∫ x in sourceBall (0 : Vec d) 1, f (y + r • x)) =
      (r ^ d)⁻¹ * ∫ x in sourceBall y r, f x := by
  have h := PDE.Parabolic.Rescale.integral_comp_of_map_eq_smul
    (c17_spatial_affine_embedding y hr) (c17_spatial_affine_map_sourceBall y hr) f
  have hp : 0 ≤ (r ^ d)⁻¹ := inv_nonneg.mpr (pow_nonneg hr.le d)
  simpa only [Module.finrank_fin_fun, abs_of_pos (pow_pos hr d), ENNReal.toReal_ofReal hp,
    smul_eq_mul] using h

/-- The inverse affine map cancels the forward spatial scaling. -/
theorem c17_spatial_affine_inverse {d : ℕ} (y x : Vec d) {r : ℝ} (hr : 0 < r) :
    r⁻¹ • ((y + r • x) - y) = x := by
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- A smooth compactly supported unit-ball test pulls back to the source ball. -/
theorem c17_spatial_test_affine_inverse {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest (sourceBall (0 : Vec d) 1) φ) :
    IsSpatialTest (sourceBall y r) (fun z => φ (r⁻¹ • (z - y))) := by
  let T : Vec d ≃ₜ Vec d := (Homeomorph.addRight (-y)).trans
    (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have hT : (fun z : Vec d => r⁻¹ • (z - y)) = T := by
    funext z
    simp [T, sub_eq_add_neg]
  have hdiff : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec d => r⁻¹ • (z - y)) :=
    (contDiff_const_smul r⁻¹).comp (contDiff_id.sub contDiff_const)
  refine ⟨hφ.1.comp hdiff, ?_, ?_⟩
  · change HasCompactSupport (φ ∘ (fun z : Vec d => r⁻¹ • (z - y)))
    rw [hT]
    exact hφ.2.1.comp_homeomorph T
  · intro z hz
    have hz' := hφ.2.2 (tsupport_comp_subset_preimage φ hdiff.continuous hz)
    have hforward : y + r • (r⁻¹ • (z - y)) = z := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
    rw [← hforward]
    exact (c17_mem_sourceBall_affine_iff y _ hr).2 hz'

/-- Chain rule for coordinate derivatives of inverse-affine tests. -/
theorem c17_coordinateDerivative_spatial_inverse {d : ℕ} (y : Vec d) (r : ℝ)
    {φ : Vec d → ℝ} (hφ : Differentiable ℝ φ) (i : Fin d) (z : Vec d) :
    coordinateDerivative i (fun z => φ (r⁻¹ • (z - y))) z =
      r⁻¹ * coordinateDerivative i φ (r⁻¹ • (z - y)) := by
  have hT : HasFDerivAt (fun z : Vec d => r⁻¹ • (z - y))
      (r⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) z := by
    exact (hasFDerivAt_sub_const y).const_smul r⁻¹
  have hcomp := (hφ (r⁻¹ • (z - y))).hasFDerivAt.comp z hT
  unfold coordinateDerivative
  change (fderiv ℝ (φ ∘ (fun z : Vec d => r⁻¹ • (z - y))) z) (unitVector i) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- The actual weak gradient pulls back with the chain-rule factor. -/
theorem c17_hasWeakGradient_spatial_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (h : HasWeakGradient (sourceBall y r) u G) :
    HasWeakGradient (sourceBall (0 : Vec d) 1)
      (fun x => u (y + r • x)) (fun x => r • G (y + r • x)) := by
  intro i
  refine ⟨c17_locallyIntegrableOn_spatial_affine y hr (h i).1, ?_, fun φ hφ => ?_⟩
  · have hl := c17_locallyIntegrableOn_spatial_affine y hr (h i).2.1
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (show LocallyIntegrableOn (fun x => r * G (y + r • x) i)
        (sourceBall (0 : Vec d) 1) volume from fun x hx => (hl x hx).smul r)
  have hψ := c17_spatial_test_affine_inverse y hr hφ
  have hdiff : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have key := (h i).2.2 _ hψ
  have hcd : ∀ x, coordinateDerivative i φ x =
      r * coordinateDerivative i (fun z => φ (r⁻¹ • (z - y))) (y + r • x) := by
    intro x
    rw [c17_coordinateDerivative_spatial_inverse y r hdiff i,
      c17_spatial_affine_inverse y x hr, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  have hL : ∫ x in sourceBall (0 : Vec d) 1, u (y + r • x) * coordinateDerivative i φ x =
      r * ((r ^ d)⁻¹ * ∫ z in sourceBall y r,
        u z * coordinateDerivative i (fun z => φ (r⁻¹ • (z - y))) z) := by
    simp_rw [hcd]
    rw [← c17_integral_sourceBall_spatial_affine y hr, ← integral_const_mul]
    congr 1; ext x; ring
  have hR : ∫ x in sourceBall (0 : Vec d) 1, (r • G (y + r • x)) i * φ x =
      r * ((r ^ d)⁻¹ * ∫ z in sourceBall y r, G z i * φ (r⁻¹ • (z - y))) := by
    rw [← c17_integral_sourceBall_spatial_affine y hr, ← integral_const_mul]
    congr 1; ext x
    rw [c17_spatial_affine_inverse y x hr, Pi.smul_apply, smul_eq_mul]; ring
  rw [hL, hR, key]
  ring

/-- Spatial affine pullback transports weak gradients on almost every time slice. -/
theorem c17_spatial_affine_caloric_gradients {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {a b : ℝ} {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient (sourceBall (0 : Vec d) 1)
        (fun x => u (t, y + r • x)) (fun x => r • G (t, y + r • x)) := by
  filter_upwards [h.2.2.2.1] with t ht
  exact c17_hasWeakGradient_spatial_affine y hr ht

/-- Spatial scaling changes space-time Lebesgue measure by its spatial Jacobian. -/
theorem c17_spacetime_affine_map_volume {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r) :
    Measure.map (fun z : ℝ × Vec d => (z.1, y + r • z.2)) volume =
      ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹) •
        (volume : Measure (ℝ × Vec d)) := by
  have hf : Measurable (fun x : Vec d => y + r • x) :=
    (measurable_const_add y).comp (measurable_const_smul r)
  change Measure.map (Prod.map id (fun x : Vec d => y + r • x)) volume = _
  rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_id hf, Measure.map_id,
    c17_spatial_affine_map_volume y hr, Measure.prod_smul_right]

/-- The space-time map which scales only the spatial variable is an embedding. -/
theorem c17_spacetime_affine_embedding {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (fun z : ℝ × Vec d => (z.1, y + r • z.2)) := by
  exact ((Homeomorph.refl ℝ).prodCongr
    ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft y))).measurableEmbedding

/-- The spatial affine Jacobian restricted to the actual source cylinder. -/
theorem c17_spacetime_affine_map_cylinder {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (a b : ℝ) :
    Measure.map (fun z : ℝ × Vec d => (z.1, y + r • z.2))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) 1)) =
      ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹) •
        (volume : Measure (ℝ × Vec d)).restrict (Set.Ioo a b ×ˢ sourceBall y r) := by
  let F : ℝ × Vec d → ℝ × Vec d := fun z => (z.1, y + r • z.2)
  have hp : F ⁻¹' (Set.Ioo a b ×ˢ sourceBall y r) =
      Set.Ioo a b ×ˢ sourceBall (0 : Vec d) 1 := by
    ext z
    simp only [F, Set.mem_preimage, Set.mem_prod, c17_mem_sourceBall_affine_iff y _ hr]
  have hb : MeasurableSet (sourceBall y r) := by
    have hsum : Continuous (fun v : Vec d => ∑ j, v j * v j) :=
      continuous_finset_sum Finset.univ fun j _ => (continuous_apply j).mul (continuous_apply j)
    have hn : Continuous (fun v : Vec d => euclideanNorm v) := by
      unfold euclideanNorm euclideanSq dot
      exact Real.continuous_sqrt.comp hsum
    exact (isOpen_lt (hn.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet
  have hF : Measurable F := (c17_spacetime_affine_embedding y hr).measurable
  change Measure.map F (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) 1)) = _
  rw [← hp, ← Measure.restrict_map hF (measurableSet_Ioo.prod hb),
    c17_spacetime_affine_map_volume y hr, Measure.restrict_smul]

/-- Spatial affine pullback preserves the caloric energy fields. -/
theorem c17_spatial_affine_caloric_energy {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {a b : ℝ} {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G) :
    MemLp (fun z => u (z.1, y + r • z.2)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) 1)) ∧
    AEStronglyMeasurable (fun z => r • G (z.1, y + r • z.2))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) 1)) ∧
    MemLp (fun z => euclideanNorm (r • G (z.1, y + r • z.2))) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) 1)) := by
  have hmap := c17_spacetime_affine_map_cylinder y hr a b
  have hF := c17_spacetime_affine_embedding y hr
  refine ⟨?_, ?_, ?_⟩
  · exact PDE.Parabolic.Rescale.memLp_comp_of_map_eq_smul hF ENNReal.ofReal_ne_top hmap h.1
  · have hg : AEStronglyMeasurable (fun z => G (z.1, y + r • z.2))
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) 1)) := by
      apply hF.aestronglyMeasurable_map_iff.mp
      rw [hmap]
      exact h.2.1.smul_measure _
    exact hg.const_smul r
  · have hg : MemLp (fun z => euclideanNorm (G (z.1, y + r • z.2))) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) 1)) :=
      PDE.Parabolic.Rescale.memLp_comp_of_map_eq_smul hF ENNReal.ofReal_ne_top hmap h.2.2.1
    simpa only [TimeChange.euclideanNorm_smul, abs_of_pos hr] using hg.const_mul r

/-- Inverse spatial affine map on space-time. -/
noncomputable def c17InverseSpatialMap {d : ℕ} (y : Vec d) (r : ℝ) (z : ℝ × Vec d) : ℝ × Vec d :=
  (z.1, r⁻¹ • (z.2 - y))

/-- The inverse spatial affine map is smooth. -/
theorem c17_contDiff_inverseSpatialMap {d : ℕ} (y : Vec d) (r : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (c17InverseSpatialMap y r) := by
  exact contDiff_fst.prodMk ((contDiff_const_smul r⁻¹).comp (contDiff_snd.sub contDiff_const))

/-- The inverse map agrees with the inverse of the spatial affine homeomorphism. -/
theorem c17_inverseSpatialMap_eq_homeomorph {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r) :
    c17InverseSpatialMap y r =
      ⇑(((Homeomorph.refl ℝ).prodCongr
        ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft y))).symm) := by
  funext z
  symm
  apply (Homeomorph.symm_apply_eq _).2
  ext <;> simp [c17InverseSpatialMap, smul_smul, hr.ne']

/-- Inverse spatial affine transport preserves compact test support. -/
theorem c17_inverseSpatialMap_compactSupport {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {ψ : ℝ × Vec d → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (ψ ∘ c17InverseSpatialMap y r) := by
  rw [c17_inverseSpatialMap_eq_homeomorph y hr]
  exact hψ.comp_homeomorph _

/-- The inverse test map sends unit-cylinder support into the source cylinder. -/
theorem c17_inverseSpatialMap_tsupport {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {I : Set ℝ} {ψ : ℝ × Vec d → ℝ}
    (hψ : tsupport ψ ⊆ I ×ˢ sourceBall (0 : Vec d) 1) :
    tsupport (ψ ∘ c17InverseSpatialMap y r) ⊆ I ×ˢ sourceBall y r := by
  intro z hz
  have hz' := hψ (tsupport_comp_subset_preimage ψ
    (c17_contDiff_inverseSpatialMap y r (n := ⊤)).continuous hz)
  have hx : y + r • (r⁻¹ • (z.2 - y)) = z.2 := by
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  refine ⟨hz'.1, ?_⟩
  rw [← hx]
  exact (c17_mem_sourceBall_affine_iff y _ hr).2 hz'.2

/-- Derivative of the inverse spatial affine map. -/
theorem c17_hasFDerivAt_inverseSpatialMap {d : ℕ} (y : Vec d) (r : ℝ) (z : ℝ × Vec d) :
    HasFDerivAt (c17InverseSpatialMap y r)
      ((ContinuousLinearMap.fst ℝ ℝ (Vec d)).prod
        (r⁻¹ • ContinuousLinearMap.snd ℝ ℝ (Vec d))) z := by
  exact (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).prodMk
    (((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).sub_const y).const_smul r⁻¹)

/-- Time and space derivatives of an inverse-affine space-time test. -/
theorem c17_inverseSpatialMap_derivatives {d : ℕ} (y : Vec d) (r : ℝ)
    {ψ : ℝ × Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : ℝ × Vec d) :
    fderiv ℝ (ψ ∘ c17InverseSpatialMap y r) z (1, 0) =
        fderiv ℝ ψ (c17InverseSpatialMap y r z) (1, 0) ∧
    ∀ j : Fin d, fderiv ℝ (ψ ∘ c17InverseSpatialMap y r) z (0, unitVector j) =
        r⁻¹ * fderiv ℝ ψ (c17InverseSpatialMap y r z) (0, unitVector j) := by
  have hd : DifferentiableAt ℝ ψ (c17InverseSpatialMap y r z) :=
    (hψ.differentiable (by norm_num)).differentiableAt
  rw [fderiv_comp z hd (c17_hasFDerivAt_inverseSpatialMap y r z).differentiableAt,
    (c17_hasFDerivAt_inverseSpatialMap y r z).fderiv]
  constructor
  · simp [ContinuousLinearMap.comp_apply]
  · intro j
    have he : ((ContinuousLinearMap.fst ℝ ℝ (Vec d)).prod
        (r⁻¹ • ContinuousLinearMap.snd ℝ ℝ (Vec d))) (0, unitVector j) =
          r⁻¹ • (0, unitVector j) := by ext <;> simp
    simp only [ContinuousLinearMap.comp_apply, he, map_smul, smul_eq_mul]

/-- Spatial affine scaling transports the weighted weak identity. -/
theorem c17_spatial_affine_weak_identity {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {a b : ℝ} {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsWeightedCaloric ρ (fun x => r^2 • α x) (Set.Ioo a b) (sourceBall y r) u G)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : Vec d) 1) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall (0 : Vec d) 1,
      -(ρ (y + r • z.2) * u (z.1, y + r • z.2)) * fderiv ℝ ψ z (1, 0) +
        dot ((α (y + r • z.2)).mulVec (r • G (z.1, y + r • z.2)))
          (fun j => fderiv ℝ ψ z (0, unitVector j))) = 0 := by
  let φ := ψ ∘ c17InverseSpatialMap y r
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (c17_contDiff_inverseSpatialMap y r)
  have hφc : HasCompactSupport φ := c17_inverseSpatialMap_compactSupport y hr hc
  have hφs : tsupport φ ⊆ interior (Set.Ioo a b) ×ˢ sourceBall y r := by
    simpa only [interior_Ioo] using c17_inverseSpatialMap_tsupport y hr hs
  have hz := h.2.2.2.2 φ hφ hφc hφs
  let F : ℝ × Vec d → ℝ := fun z =>
    -(ρ z.2 * u z) * fderiv ℝ φ z (1, 0) +
      dot (((r^2 • α z.2) : Mat d).mulVec (G z))
        (fun j => fderiv ℝ φ z (0, unitVector j))
  have hF : ∀ z : ℝ × Vec d,
      -(ρ (y + r • z.2) * u (z.1, y + r • z.2)) * fderiv ℝ ψ z (1, 0) +
        dot ((α (y + r • z.2)).mulVec (r • G (z.1, y + r • z.2)))
          (fun j => fderiv ℝ ψ z (0, unitVector j)) = F (z.1, y + r • z.2) := by
    intro z
    have hi : c17InverseSpatialMap y r (z.1, y + r • z.2) = z := by
      change (z.1, r⁻¹ • ((y + r • z.2) - y)) = z
      rw [c17_spatial_affine_inverse y z.2 hr]
    have hd := c17_inverseSpatialMap_derivatives y r hψ (z.1, y + r • z.2)
    rw [hi] at hd
    dsimp only [F, φ]
    rw [hd.1]
    simp only [hd.2]
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul]
    simp only [dot, Pi.smul_apply, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    field_simp
    <;> ring
  simp_rw [hF]
  have hm := PDE.Parabolic.Rescale.integral_comp_of_map_eq_smul
    (c17_spacetime_affine_embedding y hr) (c17_spacetime_affine_map_cylinder y hr a b) F
  rw [hm]
  change (∫ z in Set.Ioo a b ×ˢ sourceBall y r, F z) = 0 at hz
  rw [hz]
  simp

/-- Normalize the time component of a parabolic cylinder, retaining the actual density. -/
theorem c17_weighted_caloric_parabolic_time {d : ℕ}
    (t₀ : ℝ) (y : Vec d) {r : ℝ} (hr : 0 < r)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (t₀-r^2) (t₀+r^2))
      (sourceBall y r) u G) :
    IsWeightedCaloric ρ (fun x => r^2 • α x) (Set.Ioo (-1) 1) (sourceBall y r)
      (fun z => u (t₀+r^2*z.1, z.2)) (fun z => G (t₀+r^2*z.1, z.2)) := by
  have hpos : 0 < r^2 := sq_pos_of_pos hr
  have hab : t₀-r^2 < t₀+r^2 := by linarith
  have h := c13_weighted_caloric_normalize_time hab (sourceBall y r) ρ α u G hu
  have hc : (t₀-r^2 + (t₀+r^2))/2 = t₀ := by ring
  have ht : (t₀+r^2 - (t₀-r^2))/2 = r^2 := by ring
  simpa only [hc, ht] using h

/-- Parabolic rescaling preserves the actual weighted caloric equation. -/
theorem c17_weighted_caloric_parabolic_rescale {d : ℕ}
    (t₀ : ℝ) (y : Vec d) {r : ℝ} (hr : 0 < r)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (t₀-r^2) (t₀+r^2))
      (sourceBall y r) u G) :
    IsWeightedCaloric (fun x => ρ (y + r • x)) (fun x => α (y + r • x))
      (Set.Ioo (-1) 1) (sourceBall (0 : Vec d) 1)
      (fun z => u (t₀+r^2*z.1, y+r • z.2))
      (fun z => r • G (t₀+r^2*z.1, y+r • z.2)) := by
  have h := c17_weighted_caloric_parabolic_time t₀ y hr ρ α u G hu
  have he := c17_spatial_affine_caloric_energy y hr h
  refine ⟨he.1, he.2.1, he.2.2, c17_spatial_affine_caloric_gradients y hr h, ?_⟩
  intro ψ hψ hc hs
  apply c17_spatial_affine_weak_identity y hr h ψ hψ hc
  simpa only [interior_Ioo] using hs

end EinsteinFull.Calculus
