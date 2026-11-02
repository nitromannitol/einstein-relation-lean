import EinsteinFull.Calculus.C5TubeGMPFixedTimeConsumer
import EllipticRegularity.Parabolic.Rescale.AffineMeasure

open MeasureTheory Filter
open EinsteinRelation
open EinsteinFull.External.Source.GMP

noncomputable section
namespace EinsteinFull

/-- Scaling the diffusion matrix scales the eigenvalues, preserving the
weighted eigenfunctions, their weak gradients and their completeness. -/
@[nolint defsWithUnderscore]
def c5_scaledDirichletSpectralResolution {d : ℕ} {ρ : Vec d → ℝ}
    {α : Vec d → Mat d} {R τ : ℝ} (hτ : 0 < τ)
    (s : DirichletSpectralResolution ρ α R) :
    DirichletSpectralResolution ρ (fun x => τ • α x) R where
  eigenvalue n := τ * s.eigenvalue n
  eigenfunction := s.eigenfunction
  gradient := s.gradient
  eigenvalue_pos n := mul_pos hτ (s.eigenvalue_pos n)
  continuous := s.continuous
  boundary_zero := s.boundary_zero
  square_integrable := s.square_integrable
  gradient_square_integrable := s.gradient_square_integrable
  zero_extension_gradient := s.zero_extension_gradient
  eigenfunction_equation n ψ hψ := by
    have heq : (fun x => dot (((τ • α x) : Mat d).mulVec (s.gradient n x))
        (fun j => fderiv ℝ ψ x (unitVector j))) =
        (fun x => τ * dot ((α x).mulVec (s.gradient n x))
          (fun j => fderiv ℝ ψ x (unitVector j))) := by
      funext x
      rw [Matrix.smul_mulVec]
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq, integral_const_mul, s.eigenfunction_equation n ψ hψ]
    ring
  orthonormal := s.orthonormal
  complete := s.complete

/-- The time-scaled kernel has the spectral series for the scaled resolution. -/
theorem c5_scaled_spectral_series {d : ℕ} {ρ : Vec d → ℝ}
    {α : Vec d → Mat d} {R τ : ℝ} (hτ : 0 < τ)
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G) :
    ∃ s : DirichletSpectralResolution ρ (fun x => τ • α x) R,
      ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          Summable (fun n => Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y) ∧
          K (τ * t) x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y := by
  obtain ⟨s, hs⟩ := hK.2
  refine ⟨c5_scaledDirichletSpectralResolution hτ s, ?_⟩
  intro t ht x hx y hy
  have h := hs (τ * t) (mul_pos hτ ht) x hx y hy
  have he : ∀ n, -(τ * s.eigenvalue n) * t = -s.eigenvalue n * (τ * t) := by
    intro n
    ring
  simpa only [c5_scaledDirichletSpectralResolution, he] using h

/-- Positive time scaling preserves the Lebesgue-normalized initial delta. -/
theorem c5_scaled_initial_delta {d : ℕ} {ρ : Vec d → ℝ}
    {α : Vec d → Mat d} {R τ : ℝ} (hτ : 0 < τ)
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsDirichletFundamentalSolution ρ α R K G)
    {y : Vec d} (hy : y ∈ sourceBall (0 : Vec d) R)
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest (sourceBall (0 : Vec d) R) ψ) :
    Filter.Tendsto (fun t : ℝ => ∫ x in sourceBall (0 : Vec d) R, K (τ * t) x y * ψ x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ψ y)) := by
  have ht : Filter.Tendsto (fun t : ℝ => τ * t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => τ * t) := continuous_const.mul continuous_id
      simpa only [mul_zero] using (hc.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hτ ht
  exact (hK.initial_delta hy hψ).comp ht

/-- Positive time scaling is a measurable embedding of space-time. -/
theorem c5_time_scale_embedding {d : ℕ} {τ : ℝ} (hτ : 0 < τ) :
    MeasurableEmbedding (fun z : ℝ × Vec d => (τ * z.1, z.2)) := by
  exact ((Homeomorph.mulLeft₀ τ hτ.ne').prodCongr (Homeomorph.refl (Vec d))).measurableEmbedding

/-- The pushforward of space-time Lebesgue measure under time scaling. -/
theorem c5_time_scale_map_volume {d : ℕ} {τ : ℝ} (hτ : 0 < τ) :
    (volume : Measure (ℝ × Vec d)).map (fun z => (τ * z.1, z.2)) =
      ENNReal.ofReal τ⁻¹ • volume := by
  have ht := Real.map_volume_mul_left hτ.ne'
  rw [abs_of_pos (inv_pos.mpr hτ)] at ht
  change (volume : Measure (ℝ × Vec d)).map (Prod.map (fun t : ℝ => τ * t) id) = _
  rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ (measurable_const_mul τ) measurable_id,
    ht, Measure.map_id, Measure.prod_smul_left]

/-- The time-scale Jacobian on an arbitrary restricted space-time set. -/
theorem c5_time_scale_map_restrict {d : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (S : Set (ℝ × Vec d)) :
    ((volume : Measure (ℝ × Vec d)).restrict S).map (fun z => (τ * z.1, z.2)) =
      ENNReal.ofReal τ⁻¹ • (volume : Measure (ℝ × Vec d)).restrict
        ((fun z : ℝ × Vec d => (τ * z.1, z.2)) '' S) := by
  rw [PDE.Parabolic.Rescale.map_restrict_of_embedding (c5_time_scale_embedding hτ),
    c5_time_scale_map_volume hτ, Measure.restrict_smul]

/-- A positive time dilation sends an open cylinder onto the dilated cylinder. -/
theorem c5_time_scale_image_cylinder {d : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (a b : ℝ) (U : Set (Vec d)) :
    (fun z : ℝ × Vec d => (τ * z.1, z.2)) '' (Set.Ioo a b ×ˢ U) =
      Set.Ioo (τ * a) (τ * b) ×ˢ U := by
  ext ⟨t, x⟩
  constructor
  · rintro ⟨⟨s, y⟩, ⟨hs, hy⟩, he⟩
    cases he
    exact ⟨⟨mul_lt_mul_of_pos_left hs.1 hτ, mul_lt_mul_of_pos_left hs.2 hτ⟩, hy⟩
  · rintro ⟨⟨ht1, ht2⟩, hx⟩
    refine ⟨(t / τ, x), ⟨⟨?_, ?_⟩, hx⟩, ?_⟩
    · exact (lt_div_iff₀ hτ).2 (by simpa [mul_comm] using ht1)
    · exact (div_lt_iff₀ hτ).2 (by simpa [mul_comm] using ht2)
    · simp [mul_div_cancel₀ _ hτ.ne']

/-- The time-scale Jacobian on open cylinders. -/
theorem c5_time_scale_map_cylinder {d : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (a b : ℝ) (U : Set (Vec d)) :
    ((volume : Measure (ℝ × Vec d)).restrict (Set.Ioo a b ×ˢ U)).map
      (fun z => (τ * z.1, z.2)) =
      ENNReal.ofReal τ⁻¹ • (volume : Measure (ℝ × Vec d)).restrict
        (Set.Ioo (τ * a) (τ * b) ×ˢ U) := by
  rw [c5_time_scale_map_restrict hτ, c5_time_scale_image_cylinder hτ]

/-- The three integrability and measurability fields of weighted caloricity
survive the change of time variable on an open cylinder. -/
theorem c5_time_scale_caloric_energy {d : ℕ} {τ a b : ℝ} (hτ : 0 < τ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsWeightedCaloric ρ α (Set.Ioo (τ * a) (τ * b)) U u G) :
    MemLp (fun z => u (τ * z.1, z.2)) 2 (volume.restrict (Set.Ioo a b ×ˢ U)) ∧
    AEStronglyMeasurable (fun z => G (τ * z.1, z.2))
      (volume.restrict (Set.Ioo a b ×ˢ U)) ∧
    MemLp (fun z => euclideanNorm (G (τ * z.1, z.2))) 2
      (volume.restrict (Set.Ioo a b ×ˢ U)) := by
  have hmap := c5_time_scale_map_cylinder (d := d) hτ a b U
  have hF := c5_time_scale_embedding (d := d) hτ
  refine ⟨?_, ?_, ?_⟩
  · exact PDE.Parabolic.Rescale.memLp_comp_of_map_eq_smul hF ENNReal.ofReal_ne_top hmap h.1
  · apply hF.aestronglyMeasurable_map_iff.mp
    rw [hmap]
    exact h.2.1.smul_measure _
  · exact PDE.Parabolic.Rescale.memLp_comp_of_map_eq_smul hF ENNReal.ofReal_ne_top hmap h.2.2.1

/-- Almost-everywhere time-slice properties pull back under positive scaling. -/
theorem c5_time_scale_ae {τ a b : ℝ} (hτ : 0 < τ) {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂volume.restrict (Set.Ioo (τ * a) (τ * b)), P t) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), P (τ * t) := by
  have hF : MeasurableEmbedding (fun t : ℝ => τ * t) :=
    (Homeomorph.mulLeft₀ τ hτ.ne').measurableEmbedding
  have hmap : ((volume : Measure ℝ).restrict (Set.Ioo a b)).map (fun t => τ * t) =
      ENNReal.ofReal τ⁻¹ • (volume : Measure ℝ).restrict (Set.Ioo (τ * a) (τ * b)) := by
    rw [PDE.Parabolic.Rescale.map_restrict_of_embedding hF,
      Real.map_volume_mul_left hτ.ne', abs_of_pos (inv_pos.mpr hτ),
      Set.image_mul_left_Ioo hτ, Measure.restrict_smul]
  exact PDE.Parabolic.Rescale.ae_comp_of_map_eq_smul hF hmap hP

/-- The actual spatial weak gradients remain valid on almost every time slice. -/
theorem c5_time_scale_caloric_gradients {d : ℕ} {τ a b : ℝ} (hτ : 0 < τ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsWeightedCaloric ρ α (Set.Ioo (τ * a) (τ * b)) U u G) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient U (fun x => u (τ * t, x)) (fun x => G (τ * t, x)) :=
  c5_time_scale_ae hτ h.2.2.2.1

/-- The same pullback preserves the actual zero-extension weak gradient. -/
theorem c5_time_scale_zero_extension {d : ℕ} {τ a b : ℝ} (hτ : 0 < τ)
    {U : Set (Vec d)} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : ∀ᵐ t ∂volume.restrict (Set.Ioo (τ * a) (τ * b)),
      HasWeakGradient Set.univ (Set.indicator U (fun x => u (t, x)))
        (Set.indicator U (fun x => G (t, x)))) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient Set.univ (Set.indicator U (fun x => u (τ * t, x)))
        (Set.indicator U (fun x => G (τ * t, x))) :=
  c5_time_scale_ae hτ h

/-- Inverse time dilation used to transport test functions. -/
@[nolint defsWithUnderscore]
def c5_inverseTimeMap {d : ℕ} (τ : ℝ) (z : ℝ × Vec d) : ℝ × Vec d :=
  (τ⁻¹ * z.1, z.2)

/-- Inverse time dilation is smooth. -/
theorem c5_contDiff_inverseTimeMap {d : ℕ} (τ : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (c5_inverseTimeMap (d := d) τ) := by
  exact (contDiff_const.mul contDiff_fst).prodMk contDiff_snd

/-- Inverse time dilation is the inverse of the time-scale homeomorphism. -/
theorem c5_inverseTimeMap_eq_homeomorph {d : ℕ} {τ : ℝ} (hτ : 0 < τ) :
    c5_inverseTimeMap (d := d) τ =
      ⇑(((Homeomorph.mulLeft₀ τ hτ.ne').prodCongr (Homeomorph.refl (Vec d))).symm) := by
  funext z
  symm
  apply (Homeomorph.symm_apply_eq _).2
  ext <;> simp [c5_inverseTimeMap, hτ.ne']

/-- Inverse dilation sends a compactly supported test to a compactly supported test. -/
theorem c5_inverseTimeMap_compactSupport {d : ℕ} {τ : ℝ} (hτ : 0 < τ)
    {ψ : ℝ × Vec d → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (ψ ∘ c5_inverseTimeMap τ) := by
  rw [c5_inverseTimeMap_eq_homeomorph hτ]
  exact hψ.comp_homeomorph _

/-- The transformed test is supported in the dilated open cylinder. -/
theorem c5_inverseTimeMap_tsupport {d : ℕ} {τ a b : ℝ} (hτ : 0 < τ)
    {U : Set (Vec d)} {ψ : ℝ × Vec d → ℝ}
    (hψ : tsupport ψ ⊆ Set.Ioo a b ×ˢ U) :
    tsupport (ψ ∘ c5_inverseTimeMap τ) ⊆ Set.Ioo (τ * a) (τ * b) ×ˢ U := by
  rw [c5_inverseTimeMap_eq_homeomorph hτ, tsupport_comp_eq_preimage]
  intro z hz
  have hz' := hψ hz
  change τ⁻¹ * z.1 ∈ Set.Ioo a b ∧ z.2 ∈ U at hz'
  refine ⟨⟨?_, ?_⟩, hz'.2⟩
  · have hh := mul_lt_mul_of_pos_left hz'.1.1 hτ
    simpa [mul_assoc, hτ.ne'] using hh
  · have hh := mul_lt_mul_of_pos_left hz'.1.2 hτ
    simpa [mul_assoc, hτ.ne'] using hh

/-- Derivative of the inverse time dilation. -/
theorem c5_hasFDerivAt_inverseTimeMap {d : ℕ} (τ : ℝ) (z : ℝ × Vec d) :
    HasFDerivAt (c5_inverseTimeMap τ)
      ((τ⁻¹ • ContinuousLinearMap.fst ℝ ℝ (Vec d)).prod
        (ContinuousLinearMap.snd ℝ ℝ (Vec d))) z := by
  exact ((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).const_smul τ⁻¹).prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := z))

/-- Time and space derivatives of a test composed with inverse time dilation. -/
theorem c5_inverseTimeMap_derivatives {d : ℕ} (τ : ℝ)
    {ψ : ℝ × Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : ℝ × Vec d) :
    fderiv ℝ (ψ ∘ c5_inverseTimeMap τ) z (1, 0) =
        τ⁻¹ * fderiv ℝ ψ (c5_inverseTimeMap τ z) (1, 0) ∧
    (∀ j : Fin d, fderiv ℝ (ψ ∘ c5_inverseTimeMap τ) z (0, unitVector j) =
        fderiv ℝ ψ (c5_inverseTimeMap τ z) (0, unitVector j)) := by
  have hd : DifferentiableAt ℝ ψ (c5_inverseTimeMap τ z) :=
    (hψ.differentiable (by norm_num)).differentiableAt
  rw [fderiv_comp z hd (c5_hasFDerivAt_inverseTimeMap τ z).differentiableAt,
    (c5_hasFDerivAt_inverseTimeMap τ z).fderiv]
  constructor
  · have he : ((τ⁻¹ • ContinuousLinearMap.fst ℝ ℝ (Vec d)).prod
        (ContinuousLinearMap.snd ℝ ℝ (Vec d))) (1, 0) = τ⁻¹ • (1, (0 : Vec d)) := by
      ext <;> simp
    simp only [ContinuousLinearMap.comp_apply, he, map_smul, smul_eq_mul]
  · intro j
    simp [ContinuousLinearMap.comp_apply]

/-- Positive time dilation transports the weighted weak equation itself. -/
theorem c5_time_scale_weak_identity {d : ℕ} {τ a b : ℝ} (hτ : 0 < τ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsWeightedCaloric ρ α (Set.Ioo (τ * a) (τ * b)) U u G)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ U) :
    (∫ z in Set.Ioo a b ×ˢ U,
      -(ρ z.2 * u (τ * z.1, z.2)) * fderiv ℝ ψ z (1, 0) +
        dot (((τ • α z.2) : Mat d).mulVec (G (τ * z.1, z.2)))
          (fun j => fderiv ℝ ψ z (0, unitVector j))) = 0 := by
  let φ := ψ ∘ c5_inverseTimeMap τ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (c5_contDiff_inverseTimeMap τ)
  have hφc : HasCompactSupport φ := c5_inverseTimeMap_compactSupport hτ hc
  have hφs : tsupport φ ⊆ interior (Set.Ioo (τ * a) (τ * b)) ×ˢ U := by
    simpa only [interior_Ioo] using c5_inverseTimeMap_tsupport hτ hs
  have hz := h.2.2.2.2 φ hφ hφc hφs
  let F : ℝ × Vec d → ℝ := fun z =>
    -(ρ z.2 * u z) * fderiv ℝ φ z (1, 0) +
      dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ φ z (0, unitVector j))
  have hF : ∀ z : ℝ × Vec d,
      -(ρ z.2 * u (τ * z.1, z.2)) * fderiv ℝ ψ z (1, 0) +
        dot (((τ • α z.2) : Mat d).mulVec (G (τ * z.1, z.2)))
          (fun j => fderiv ℝ ψ z (0, unitVector j)) = τ * F (τ * z.1, z.2) := by
    intro z
    have hi : c5_inverseTimeMap τ (τ * z.1, z.2) = z := by
      ext <;> simp [c5_inverseTimeMap, mul_assoc, hτ.ne']
    have hd := c5_inverseTimeMap_derivatives τ hψ (τ * z.1, z.2)
    rw [hi] at hd
    have hm : dot (((τ • α z.2) : Mat d).mulVec (G (τ * z.1, z.2)))
        (fun j => fderiv ℝ ψ z (0, unitVector j)) =
        τ * dot ((α z.2).mulVec (G (τ * z.1, z.2)))
          (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
      rw [Matrix.smul_mulVec]
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hm]
    dsimp only [F, φ]
    rw [hd.1]
    simp only [hd.2]
    field_simp
    <;> ring
  simp_rw [hF, integral_const_mul]
  have hm := PDE.Parabolic.Rescale.integral_comp_of_map_eq_smul
    (c5_time_scale_embedding (d := d) hτ) (c5_time_scale_map_cylinder hτ a b U) F
  rw [hm]
  change (∫ z in Set.Ioo (τ * a) (τ * b) ×ˢ U, F z) = 0 at hz
  rw [hz]
  simp

/-- The complete weighted caloric predicate is preserved by time dilation. -/
theorem c5_time_scale_weighted_caloric {d : ℕ} {τ a b : ℝ} (hτ : 0 < τ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsWeightedCaloric ρ α (Set.Ioo (τ * a) (τ * b)) U u G) :
    IsWeightedCaloric ρ (fun x => τ • α x) (Set.Ioo a b) U
      (fun z => u (τ * z.1, z.2)) (fun z => G (τ * z.1, z.2)) := by
  obtain ⟨h1, h2, h3⟩ := c5_time_scale_caloric_energy hτ h
  refine ⟨h1, h2, h3, c5_time_scale_caloric_gradients hτ h, ?_⟩
  intro ψ hψ hc hs
  apply c5_time_scale_weak_identity hτ h ψ hψ hc
  simpa only [interior_Ioo] using hs

/-- Positive time dilation preserves the source Dirichlet fundamental solution. -/
theorem c5_time_scale_dirichlet_solution {d : ℕ} {τ R : ℝ} (hτ : 0 < τ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsDirichletFundamentalSolution ρ α R K G) :
    IsDirichletFundamentalSolution ρ (fun x => τ • α x) R
      (fun t x y => K (τ * t) x y) (fun t x y => G (τ * t) x y) := by
  intro y hy
  obtain ⟨hcont, hnonneg, hboundary, hcal, hdelta⟩ := hK y hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change ContinuousOn ((fun z : ℝ × Vec d => K z.1 z.2 y) ∘
        (fun z : ℝ × Vec d => (τ * z.1, z.2))) _
    apply hcont.comp
    · exact ((continuous_const.mul continuous_fst).prodMk continuous_snd).continuousOn
    · intro z hz
      exact ⟨mul_pos hτ hz.1, hz.2⟩
  · intro t ht x hx
    exact hnonneg (τ * t) (mul_pos hτ ht) x hx
  · intro t ht x hx
    exact hboundary (τ * t) (mul_pos hτ ht) x hx
  · intro a b ha hab
    obtain ⟨hw, hg⟩ := hcal (τ * a) (τ * b) (mul_pos hτ ha)
      (mul_lt_mul_of_pos_left hab hτ)
    refine ⟨c5_time_scale_weighted_caloric hτ hw, ?_⟩
    exact c5_time_scale_zero_extension (U := sourceBall (0 : Vec d) R)
      (u := fun z => K z.1 z.2 y) (G := fun z => G z.1 z.2 y) hτ hg
  · intro ψ hψ
    exact c5_scaled_initial_delta hτ hK hy hψ

/-- A genuine spectral Dirichlet kernel remains genuine after time dilation. -/
theorem c5_time_scale_spectral_solution {d : ℕ} {τ R : ℝ} (hτ : 0 < τ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G) :
    IsSpectralDirichletFundamentalSolution ρ (fun x => τ • α x) R
      (fun t x y => K (τ * t) x y) (fun t x y => G (τ * t) x y) :=
  ⟨c5_time_scale_dirichlet_solution hτ hK.1, c5_scaled_spectral_series hτ hK⟩

/-- The fixed-time GMP lower bound applies to a genuine translated source
kernel at each time in a compact positive window. -/
theorem c5_gmp_original_time_translated_coeff_consumer
    (d : ℕ) (hd : 0 < d) (κ R : ℝ) (hκ : 0 < κ) (hR : 0 < R)
    (center : Vec d) (radius : ℝ) (hradius : 0 < radius)
    (hball : euclideanNorm center + radius < R)
    (τlo τhi : ℝ) (hlo : 0 < τlo) (hwindow : τlo ≤ τhi) :
    ∃ C : ℝ, 0 < C ∧
      ∀ τ ∈ Set.Icc τlo τhi, ∀ (z₀ : Vec d) (ρ : Vec d → ℝ) (α : Vec d → Mat d),
        IsUniformlyElliptic κ ρ α →
        ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
          IsSpectralDirichletFundamentalSolution (fun z => ρ (z + z₀))
            (fun z => α (z + z₀)) R K G →
          ∀ z ∈ sourceBall center radius, C ≤ K τ z 0 := by
  obtain ⟨k, C, hk, hC, hbound⟩ :=
    c5_gmp_fixed_time_translated_coeff_consumer d hd κ R hκ hR center radius
      hradius hball τlo τhi hlo hwindow
  refine ⟨C, hC, ?_⟩
  intro τ hτ z₀ ρ α hell K G hK z hz
  have ht : 0 < τ := lt_of_lt_of_le hlo hτ.1
  have h := (hbound τ hτ z₀ ρ α hell).2
    (fun t x y => K (τ * t) x y) (fun t x y => G (τ * t) x y)
    (c5_time_scale_spectral_solution ht hK) z hz
  simpa only [mul_one] using h

end EinsteinFull
