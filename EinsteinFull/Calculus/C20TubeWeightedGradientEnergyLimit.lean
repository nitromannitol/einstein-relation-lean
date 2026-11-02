import EinsteinFull.Calculus.C20TubeWeightedNonlinearFluxLimit

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- The nonlinear weighted gradient energy converges in L¹ under forward averaging. -/
theorem c20_weighted_forward_nonlinear_gradient_energy_limit
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ)
    (hψm : AEStronglyMeasurable ψ
      (volume.restrict (Set.Ioo (-1/2 : ℝ) (1/2) ×ˢ sourceBall y r)))
    (hψb : ∀ᵐ z ∂volume.restrict
      (Set.Ioo (-1/2 : ℝ) (1/2) ×ˢ sourceBall y r), |ψ z| ≤ 1) :
    let uh := fun h : ℝ => fun z : ℝ × Vec d =>
      h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)
    let Gh := fun h : ℝ => fun z : ℝ × Vec d =>
      h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)
    Tendsto (fun h : ℝ => ∫ z in
      Set.Ioo (-1/2 : ℝ) (1/2) ×ˢ sourceBall y r,
      |deriv (deriv F) (uh h z) * dot ((α z.2).mulVec (Gh h z)) (Gh h z) * ψ z -
       deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  dsimp only
  let U := sourceBall y r
  let T := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U
  have hT : Set.Ioo (-1 / 2 : ℝ) (1 / 2) ×ˢ sourceBall y r = T := by
    dsimp [T, U]
    congr 2
    norm_num
  rw [hT] at hψb hψm ⊢
  let μ := volume.restrict T
  let q : ℝ → ℝ × Vec d → ℝ := fun h z =>
    euclideanNorm (h⁻¹ • (∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) - G z)
  let g : ℝ × Vec d → ℝ := fun z => euclideanNorm (G z)
  let e : ℝ × Vec d → ℝ := fun z => dot ((α z.2).mulVec (G z)) (G z)
  let a : ℝ → ℝ × Vec d → ℝ := fun h z =>
    deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) - deriv (deriv F) (u z)
  have hμ : μ ≤ volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U) := by
    apply Measure.restrict_mono_set
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hgs : MemLp g 2 μ := hG.mono_measure hμ
  have hq : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (q h) 2 μ :=
    c20_vector_forward_error_eventually_memLp y r G hGm hG
  have hq0 (h : ℝ) (z : ℝ × Vec d) : 0 ≤ q h z := Real.sqrt_nonneg _
  have hqlim : Tendsto (fun h : ℝ => ∫ z, |q h z| ^ 2 ∂μ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [abs_of_nonneg (hq0 _ _), q, μ, T, U] using
      (c20_weighted_forward_average_L2_limit hκ ρ α hell y u G hu hGm hG).2
  have hl := c20_integral_abs_mul_fixed_L2_tendsto_zero q g hq hgs hqlim
  have hfixed := c20_scalar_forward_average_fixed_energy_abs_limit hκ ρ α hell y u G hu hGm hG F hF M hF2
  have hupper : Tendsto (fun h : ℝ => M * κ⁻¹ *
      (2 * (∫ z, |q h z| * |g z| ∂μ) + ∫ z, |q h z| ^ 2 ∂μ) +
      ∫ z, |a h z| * |e z| ∂μ) (𝓝[>] 0) (𝓝 0) := by
    have hh := (((hl.const_mul 2).add hqlim).const_mul (M * κ⁻¹)).add hfixed
    simpa only [add_zero, mul_zero, a, e, μ, T, U] using hh
  have hem : Integrable e μ := c20_elliptic_gradient_energy_integrable hκ ρ α hell μ G
    (hGm.mono_measure hμ) (hG.mono_measure hμ)
  have ha : ∀ᶠ h : ℝ in 𝓝[>] 0, AEStronglyMeasurable (a h) μ := by
    filter_upwards [c20_scalar_forward_average_slab_eventually_aestronglyMeasurable U
      (c20_sourceBall_measurable y r) u hu] with h hh
    exact (hF.deriv'.continuous_deriv_one.comp_aestronglyMeasurable hh).sub
      (hF.deriv'.continuous_deriv_one.comp_aestronglyMeasurable (hu.mono_measure hμ).aestronglyMeasurable)
  apply squeeze_zero' _ _ hupper
  · exact Filter.Eventually.of_forall fun h => integral_nonneg fun z => abs_nonneg _
  · filter_upwards [hq, ha] with h hqh hah
    have hi₁ : Integrable (fun z => |q h z| * |g z|) μ := by
      convert hqh.norm.integrable_mul hgs.norm using 1
    have hi₂ : Integrable (fun z => |q h z| ^ 2) μ := by
      simpa only [Real.norm_eq_abs] using hqh.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hi₃ : Integrable (fun z => |a h z| * |e z|) μ := by
      apply (hem.abs.const_mul (2 * M)).mono' ((continuous_abs.comp_aestronglyMeasurable hah).mul hem.abs.aestronglyMeasurable)
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact (abs_sub _ _).trans (by linarith [hF2 (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)), hF2 (u z)])
    calc
      (∫ z in T, |deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z -
        deriv (deriv F) (u z) * e z * ψ z|) ≤
        ∫ z, M * κ⁻¹ * (2 * (|q h z| * |g z|) + |q h z| ^ 2) + |a h z| * |e z| ∂μ := by
          apply integral_mono_of_nonneg (ae_of_all μ fun z => abs_nonneg _)
            (((hi₁.const_mul 2 |>.add hi₂).const_mul _).add hi₃)
          filter_upwards [hψb, hψm.ae_eq_mk] with z hz hzm
          have hb := c20_elliptic_quadratic_difference_bound hκ ρ α hell z.2
            (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) (G z)
          have hc := hF2 (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))
          have hp : 0 ≤ κ⁻¹ := inv_nonneg.mpr (le_of_lt hκ)
          have halg : ∀ A B C D P : ℝ, |P| ≤ 1 → |A * B * P - C * D * P| ≤
              |A| * |B-D| + |A-C| * |D| := by
            intro A B C D P hp
            have ht := abs_add_le (A * (B-D) * P) ((A-C)*D*P)
            have hid : A * B * P - C * D * P = A * (B-D) * P + (A-C)*D*P := by ring
            rw [hid]
            have hp' : |P| ≤ 1 := hp
            rw [abs_mul, abs_mul, abs_mul, abs_mul] at ht
            have hn₁ : 0 ≤ |A| * |B-D| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
            have hn₂ : 0 ≤ |A-C| * |D| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
            nlinarith [mul_le_mul_of_nonneg_left hp' hn₁, mul_le_mul_of_nonneg_left hp' hn₂]
          have hbase := halg (deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)))
            (dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
              (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
            (deriv (deriv F) (u z)) (e z) (ψ z) hz
          have hb' : |dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
                (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) - e z| ≤
              κ⁻¹ * (2 * (|q h z| * |g z|) + |q h z| ^ 2) := by
            simpa only [q, g, e, euclideanNorm, abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc] using hb
          have hm := mul_le_mul hc hb' (abs_nonneg _) hM
          dsimp only [a, e, Pi.add_apply] at hbase hm ⊢
          nlinarith [hm]
      _ = M * κ⁻¹ * (2 * (∫ z, |q h z| * |g z| ∂μ) + ∫ z, |q h z| ^ 2 ∂μ) +
          ∫ z, |a h z| * |e z| ∂μ := by
        let f₁ : ℝ × Vec d → ℝ := fun z => M * κ⁻¹ * (2 * (|q h z| * |g z|) + |q h z| ^ 2)
        let f₂ : ℝ × Vec d → ℝ := fun z => |a h z| * |e z|
        change (∫ z, (f₁ + f₂) z ∂μ) = _
        have hf₁ : Integrable f₁ μ := by
          simpa only [f₁, Pi.add_apply] using ((hi₁.const_mul 2 |>.add hi₂).const_mul (M * κ⁻¹))
        have hf₂ : Integrable f₂ μ := hi₃
        have hsum : (∫ z, (f₁ + f₂) z ∂μ) = (∫ z, f₁ z ∂μ) + ∫ z, f₂ z ∂μ := by
          simpa only [Pi.add_apply] using integral_add hf₁ hf₂
        rw [hsum]
        congr 1
        let f₃ : ℝ × Vec d → ℝ := fun z => 2 * (|q h z| * |g z|)
        let f₄ : ℝ × Vec d → ℝ := fun z => |q h z| ^ 2
        change (∫ z, M * κ⁻¹ * (f₃ + f₄) z ∂μ) = _
        have hf₃ : Integrable f₃ μ := hi₁.const_mul 2
        have hf₄ : Integrable f₄ μ := hi₂
        rw [integral_const_mul]
        have hsum : (∫ z, (f₃ + f₄) z ∂μ) = (∫ z, f₃ z ∂μ) + ∫ z, f₄ z ∂μ := by
          simpa only [Pi.add_apply] using integral_add hf₃ hf₄
        rw [hsum]
        simp only [f₃, f₄, integral_const_mul]

/-- The gradient-energy limit also holds for a test with any finite bound. -/
theorem c20_weighted_forward_nonlinear_gradient_energy_limit_bounded
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hψm : AEStronglyMeasurable ψ
      (volume.restrict (Set.Ioo (-1/2 : ℝ) (1/2) ×ˢ sourceBall y r)))
    (hψb : ∀ᵐ z ∂volume.restrict
      (Set.Ioo (-1/2 : ℝ) (1/2) ×ˢ sourceBall y r), |ψ z| ≤ C) :
    Tendsto (fun h : ℝ => ∫ z in
      Set.Ioo (-1/2 : ℝ) (1/2) ×ˢ sourceBall y r,
      |deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z -
       deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hpos : 0 < C + 1 := by linarith
  have hb : ∀ᵐ z ∂volume.restrict
      (Set.Ioo (-1/2 : ℝ) (1/2) ×ˢ sourceBall y r), |(C + 1)⁻¹ * ψ z| ≤ 1 := by
    filter_upwards [hψb] with z hz
    rw [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
    rw [← div_eq_inv_mul]
    exact (div_le_one hpos).2 (by linarith)
  have ht := c20_weighted_forward_nonlinear_gradient_energy_limit hκ ρ α hell y u G
    hu hGm hG F hF M hM hF2 (fun z => (C + 1)⁻¹ * ψ z)
    (hψm.const_mul _) hb
  have ht' := ht.const_mul (C + 1)
  simp only [mul_zero] at ht'
  convert ht' using 1
  funext h
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  have hid (A B P : ℝ) : A * ((C + 1)⁻¹ * P) - B * ((C + 1)⁻¹ * P) =
      (C + 1)⁻¹ * (A * P - B * P) := by ring
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]

/-- A smooth compactly supported test is bounded, so the gradient-energy limit applies. -/
theorem c20_weighted_forward_nonlinear_gradient_energy_limit_compact
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Tendsto (fun h : ℝ => ∫ z in
      Set.Ioo (-1/2 : ℝ) (1/2) ×ˢ sourceBall y r,
      |deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z -
       deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  apply c20_weighted_forward_nonlinear_gradient_energy_limit_bounded hκ ρ α hell y u G
    hu hGm hG F hF M hM hF2 ψ (max C 0) (le_max_right _ _)
    hψ.continuous.aestronglyMeasurable
  filter_upwards with z
  have hz : |ψ z| ≤ C := by simpa only [Real.norm_eq_abs] using hC z
  exact hz.trans (le_max_left _ _)

/-- Forward averaging commutes with a nonzero affine rescaling of time. -/
theorem c20_forward_average_affine_time {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (t k h : ℝ) (hk : k ≠ 0) :
    h⁻¹ • (∫ s in (0 : ℝ)..h, f (t + k * s)) =
      (k * h)⁻¹ • (∫ s in (0 : ℝ)..(k * h), f (t + s)) := by
  rw [intervalIntegral.integral_comp_mul_left (fun s => f (t + s)) hk]
  simp only [mul_zero, smul_smul, mul_inv_rev, mul_comm]

/-- The affine time change carries Lebesgue measure with its Jacobian. -/
theorem c20_map_volume_affine_time (t k : ℝ) (hk : k ≠ 0) :
    Measure.map (fun s : ℝ => t + k * s) volume =
      ENNReal.ofReal |k⁻¹| • (volume : Measure ℝ) := by
  calc
    Measure.map (fun s : ℝ => t + k * s) volume =
        Measure.map (fun s : ℝ => t + s) (Measure.map (fun s : ℝ => k * s) volume) := by
          rw [Measure.map_map (measurable_const_add t) (measurable_const_mul k)]
          rfl
    _ = ENNReal.ofReal |k⁻¹| • (volume : Measure ℝ) := by
      rw [Real.map_volume_mul_left hk,
        Measure.map_smul _ (measurable_const_add t).aemeasurable, map_add_left_eq_self]

/-- The same time change has the same Jacobian on space-time. -/
theorem c20_map_volume_affine_time_prod {d : ℕ} (t k : ℝ) (hk : k ≠ 0) :
    Measure.map (fun z : ℝ × Vec d => (t + k * z.1, z.2)) volume =
      ENNReal.ofReal |k⁻¹| • (volume : Measure (ℝ × Vec d)) := by
  change Measure.map (Prod.map (fun s : ℝ => t + k * s) id) volume = _
  rw [Measure.volume_eq_prod ℝ (Vec d), ← Measure.map_prod_map
    (volume : Measure ℝ) (volume : Measure (Vec d))
    ((measurable_const_mul k).const_add t) measurable_id,
    c20_map_volume_affine_time t k hk, Measure.map_id, Measure.prod_smul_left,
    ← Measure.volume_eq_prod]

/-- Restricted space-time measure transforms under the affine time change. -/
theorem c20_map_restrict_volume_affine_time_prod {d : ℕ} (t k : ℝ) (hk : k ≠ 0)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S) :
    Measure.map (fun z : ℝ × Vec d => (t + k * z.1, z.2))
      (volume.restrict ((fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S)) =
      ENNReal.ofReal |k⁻¹| • (volume.restrict S) := by
  have hm : Measurable (fun z : ℝ × Vec d => (t + k * z.1, z.2)) :=
    ((measurable_const_mul k).comp measurable_fst |>.const_add t).prodMk measurable_snd
  rw [← Measure.restrict_map hm hS, c20_map_volume_affine_time_prod t k hk,
    Measure.restrict_smul]

/-- Pulling a function back by an affine time change preserves its local Lᵖ class. -/
theorem c20_memLp_affine_time_pullback {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (t k : ℝ) (hk : k ≠ 0)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S) (p : ENNReal)
    (f : ℝ × Vec d → E) (hf : MemLp f p (volume.restrict S)) :
    MemLp (fun z => f (t + k * z.1, z.2)) p
      (volume.restrict ((fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S)) := by
  have hm : Measurable (fun z : ℝ × Vec d => (t + k * z.1, z.2)) :=
    ((measurable_const_mul k).comp measurable_fst |>.const_add t).prodMk measurable_snd
  have hf' : MemLp f p (ENNReal.ofReal |k⁻¹| • volume.restrict S) :=
    hf.smul_measure (by simp)
  rw [← c20_map_restrict_volume_affine_time_prod t k hk S hS] at hf'
  exact hf'.comp_of_map hm.aemeasurable

/-- Almost-everywhere strong measurability also pulls back under the time change. -/
theorem c20_aestronglyMeasurable_affine_time_pullback {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (t k : ℝ) (hk : k ≠ 0)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S)
    (f : ℝ × Vec d → E) (hf : AEStronglyMeasurable f (volume.restrict S)) :
    AEStronglyMeasurable (fun z => f (t + k * z.1, z.2))
      (volume.restrict ((fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S)) := by
  have hm : Measurable (fun z : ℝ × Vec d => (t + k * z.1, z.2)) :=
    ((measurable_const_mul k).comp measurable_fst |>.const_add t).prodMk measurable_snd
  have hf' := hf.smul_measure (ENNReal.ofReal |k⁻¹|)
  rw [← c20_map_restrict_volume_affine_time_prod t k hk S hS] at hf'
  exact hf'.comp_measurable hm

/-- Positive affine time changes pull a time-space slab back to its source slab. -/
theorem c20_affine_time_preimage_slab {d : ℕ} (t k a b : ℝ) (hk : 0 < k)
    (U : Set (Vec d)) :
    (fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹'
      (Set.Ioo (t + k * a) (t + k * b) ×ˢ U) = Set.Ioo a b ×ˢ U := by
  ext z
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨ha, hb⟩, hz⟩
    refine ⟨⟨?_, ?_⟩, hz⟩
    · have h : k * a < k * z.1 := by linarith
      by_contra! hn
      have hle := mul_le_mul_of_nonneg_left hn hk.le
      linarith
    · have h : k * z.1 < k * b := by linarith
      by_contra! hn
      have hle := mul_le_mul_of_nonneg_left hn hk.le
      linarith
  · rintro ⟨⟨ha, hb⟩, hz⟩
    exact ⟨⟨by linarith [mul_lt_mul_of_pos_left ha hk],
      by linarith [mul_lt_mul_of_pos_left hb hk]⟩, hz⟩

/-- Integrals on a measurable set transform with the time Jacobian. -/
theorem c20_integral_affine_time_pullback {d : ℕ} (t k : ℝ) (hk : 0 < k)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S)
    (f : ℝ × Vec d → ℝ) (hf : AEStronglyMeasurable f (volume.restrict S)) :
    (∫ z in ((fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S),
      f (t + k * z.1, z.2)) = k⁻¹ * ∫ z in S, f z := by
  have hm : Measurable (fun z : ℝ × Vec d => (t + k * z.1, z.2)) :=
    ((measurable_const_mul k).comp measurable_fst |>.const_add t).prodMk measurable_snd
  have hfm : AEStronglyMeasurable f
      (Measure.map (fun z : ℝ × Vec d => (t + k * z.1, z.2))
        (volume.restrict ((fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S))) := by
    rw [c20_map_restrict_volume_affine_time_prod t k (ne_of_gt hk) S hS]
    exact hf.smul_measure (ENNReal.ofReal |k⁻¹|)
  have hi := integral_map hm.aemeasurable hfm
  rw [c20_map_restrict_volume_affine_time_prod t k (ne_of_gt hk) S hS,
    integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos (inv_pos.mpr hk), smul_eq_mul] at hi
  exact hi.symm

/-- A compact test support stays inside the time interval under sufficiently short
forward shifts, uniformly over the support. -/
theorem c20_compact_support_forward_shift {d : ℕ} {a b : ℝ} {U : Set (Vec d)}
    (ψ : ℝ × Vec d → ℝ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ tsupport ψ, ∀ s ∈ Set.Icc (0 : ℝ) δ,
      (z.1 + s, z.2) ∈ Set.Ioo a b ×ˢ U := by
  let K : Set ℝ := Prod.fst '' tsupport ψ
  have hK : IsCompact K := hψc.image continuous_fst
  have hKU : K ⊆ Set.Ioo a b := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hψs hz).1
  obtain ⟨ε, hε, hεK⟩ := hK.exists_thickening_subset_open isOpen_Ioo hKU
  refine ⟨ε / 2, by linarith, ?_⟩
  intro z hz s hs
  have hmem : z.1 + s ∈ Metric.thickening ε K := by
    apply Metric.mem_thickening_iff.mpr
    refine ⟨z.1, ⟨z, hz, rfl⟩, ?_⟩
    rw [Real.dist_eq, show z.1 + s - z.1 = s by ring, abs_of_nonneg hs.1]
    have hsδ : s ≤ ε / 2 := hs.2
    linarith
  exact ⟨hεK hmem, (hψs hz).2⟩

/-- Zero extension does not change the short forward integrals on a compact test support. -/
theorem c20_compact_support_forward_indicator_integral {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} {U : Set (Vec d)}
    (ψ : ℝ × Vec d → ℝ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ U) (f : ℝ × Vec d → E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ tsupport ψ, ∀ h ∈ Set.Icc (0 : ℝ) δ,
      (∫ s in (0 : ℝ)..h, (Set.Ioo a b ×ˢ U).indicator f (z.1 + s, z.2)) =
      ∫ s in (0 : ℝ)..h, f (z.1 + s, z.2) := by
  obtain ⟨δ, hδ, hshift⟩ := c20_compact_support_forward_shift ψ hψc hψs
  refine ⟨δ, hδ, ?_⟩
  intro z hz h hh
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hh.1] at hs
  exact Set.indicator_of_mem (hshift z hz s ⟨hs.1, le_trans hs.2 hh.2⟩) f


/-- Zero extension preserves the scalar and gradient hypotheses on a measurable set. -/
theorem c20_memLp_zero_extension {d : ℕ} (S : Set (ℝ × Vec d))
    (hS : MeasurableSet S) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict S))
    (hGm : AEStronglyMeasurable G (volume.restrict S))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict S)) :
    MemLp (S.indicator u) 2 volume ∧
    AEStronglyMeasurable (S.indicator G) volume ∧
    MemLp (fun z => euclideanNorm (S.indicator G z)) 2 volume := by
  refine ⟨(memLp_indicator_iff_restrict hS).2 hu,
    (aestronglyMeasurable_indicator_iff hS).2 hGm, ?_⟩
  have heq : (fun z => euclideanNorm (S.indicator G z)) =
      S.indicator (fun z => euclideanNorm (G z)) := by
    funext z
    by_cases hz : z ∈ S
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz, euclideanNorm, euclideanSq, dot]
  rw [heq]
  exact (memLp_indicator_iff_restrict hS).2 hG


/-- The affine integral formula holds for arbitrary integrands, by measurable equivalence. -/
theorem c20_integral_affine_time_pullback_unconditional {d : ℕ} (t k : ℝ) (hk : 0 < k)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S) (f : ℝ × Vec d → ℝ) :
    (∫ z in ((fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S),
      f (t + k * z.1, z.2)) = k⁻¹ * ∫ z in S, f z := by
  let e : (ℝ × Vec d) ≃ᵐ (ℝ × Vec d) :=
    { toFun := fun z => (t + k * z.1, z.2)
      invFun := fun z => ((z.1 - t) / k, z.2)
      left_inv := by
        intro z
        simp [add_sub_cancel_left, mul_div_cancel_left₀ _ (ne_of_gt hk)]
      right_inv := by
        intro z
        simp [mul_div_cancel₀ _ (ne_of_gt hk)]
      measurable_toFun :=
        ((measurable_const_mul k).comp measurable_fst |>.const_add t).prodMk measurable_snd
      measurable_invFun :=
        ((measurable_fst.sub measurable_const).div_const k).prodMk measurable_snd }
  have hi := integral_map_equiv e f
    (μ := volume.restrict ((fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S))
  change (∫ z, f z ∂Measure.map (fun z : ℝ × Vec d => (t + k * z.1, z.2))
    (volume.restrict ((fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S))) = _ at hi
  rw [c20_map_restrict_volume_affine_time_prod t k (ne_of_gt hk) S hS,
    integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos (inv_pos.mpr hk), smul_eq_mul] at hi
  exact hi.symm


/-- The tested nonlinear energy is unchanged by zero extension for short forward shifts. -/
theorem c20_compact_support_zero_extension_energy {d : ℕ} {a b : ℝ}
    {U : Set (Vec d)} (ψ : ℝ × Vec d → ℝ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ U)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (α : Vec d → Mat d) (D : ℝ → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h ∈ Set.Icc (0 : ℝ) δ, ∀ z : ℝ × Vec d,
      let S := Set.Ioo a b ×ˢ U
      |D (h⁻¹ * ∫ s in (0 : ℝ)..h, S.indicator u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, S.indicator G (z.1+s,z.2)))
          (h⁻¹ • ∫ s in (0 : ℝ)..h, S.indicator G (z.1+s,z.2)) * ψ z -
       D (S.indicator u z) * dot ((α z.2).mulVec (S.indicator G z))
         (S.indicator G z) * ψ z| =
      |D (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z -
       D (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z| := by
  obtain ⟨δu, hδu, hu⟩ := c20_compact_support_forward_indicator_integral ψ hψc hψs u
  obtain ⟨δG, hδG, hG⟩ := c20_compact_support_forward_indicator_integral ψ hψc hψs G
  refine ⟨min δu δG, lt_min hδu hδG, ?_⟩
  intro h hh z
  by_cases hz : z ∈ tsupport ψ
  · have hhu : h ∈ Set.Icc (0 : ℝ) δu := ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    have hhG : h ∈ Set.Icc (0 : ℝ) δG := ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
    dsimp only
    rw [hu z hz h hhu, hG z hz h hhG,
      Set.indicator_of_mem (hψs hz), Set.indicator_of_mem (hψs hz)]
  · simp [image_eq_zero_of_notMem_tsupport hz]


/-- A test-supported integrand has the same integral over any set containing its support. -/
theorem c20_integral_eq_of_test_support_subset {d : ℕ} (ψ f : ℝ × Vec d → ℝ)
    (S : Set (ℝ × Vec d)) (hS : tsupport ψ ⊆ S)
    (hf : ∀ z, ψ z = 0 → f z = 0) :
    (∫ z in S, f z) = ∫ z, f z := by
  have heq : (∫ z in Set.univ, f z) = ∫ z in S, f z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
      (Set.subset_univ S)
    intro z hz
    apply hf z
    exact image_eq_zero_of_notMem_tsupport (fun h => hz.2 (hS h))
  simpa only [setIntegral_univ] using heq.symm


/-- Forward averages of an affine time pullback use the correspondingly scaled time. -/
theorem c20_forward_average_affine_spacetime {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × Vec d → E) (t k h : ℝ) (hk : k ≠ 0) (z : ℝ × Vec d) :
    h⁻¹ • (∫ s in (0 : ℝ)..h, f (t + k * (z.1 + s), z.2)) =
      (k * h)⁻¹ • (∫ s in (0 : ℝ)..(k * h), f (t + k * z.1 + s, z.2)) := by
  convert c20_forward_average_affine_time (fun q => f (q, z.2)) (t + k * z.1) k h hk using 1 <;>
    congr 2 <;> funext s <;> congr 1 <;> ring

/-- Positive constant time rescaling preserves the right-hand neighborhood of zero. -/
theorem c20_tendsto_positive_time_div (k : ℝ) (hk : 0 < k) :
    Tendsto (fun h : ℝ => h / k) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using ((continuous_id.div_const k).tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact div_pos hh hk


/-- The nonlinear gradient-energy limit on any interval for globally L² data. -/
theorem c20_weighted_forward_nonlinear_gradient_energy_limit_global
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 volume) (hGm : AEStronglyMeasurable G volume)
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 volume)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      |deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z -
       deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z|)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  let t : ℝ := (a + b) / 2
  let k : ℝ := b - a
  have hk : 0 < k := by dsimp [k]; linarith
  let A : ℝ × Vec d → ℝ × Vec d := fun z => (t + k * z.1, z.2)
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  let I : Set (ℝ × Vec d) := Set.Ioo (-1/2 : ℝ) (1/2) ×ˢ sourceBall y r
  let J : Set (ℝ × Vec d) := Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r
  have ha : t + k * (-1/2) = a := by dsimp [t, k]; ring
  have hb : t + k * (1/2) = b := by dsimp [t, k]; ring
  have hpre : A ⁻¹' S = I := by
    simpa only [A, S, I, ha, hb] using
      c20_affine_time_preimage_slab t k (-1/2) (1/2) hk (sourceBall y r)
  have hS : MeasurableSet S := measurableSet_Ioo.prod (c20_sourceBall_measurable y r)
  have huA : MemLp (fun z => u (A z)) 2 (volume.restrict J) := by
    have h := c20_memLp_affine_time_pullback t k (ne_of_gt hk) Set.univ
      MeasurableSet.univ 2 u (by simpa using hu)
    have h' : MemLp (fun z => u (A z)) 2 volume := by simpa [A] using h
    exact h'.mono_measure Measure.restrict_le_self
  have hGA : AEStronglyMeasurable (fun z => G (A z)) (volume.restrict J) := by
    have h := c20_aestronglyMeasurable_affine_time_pullback t k (ne_of_gt hk) Set.univ
      MeasurableSet.univ G (by simpa using hGm)
    have h' : AEStronglyMeasurable (fun z => G (A z)) volume := by simpa [A] using h
    exact h'.mono_measure Measure.restrict_le_self
  have hG2A : MemLp (fun z => euclideanNorm (G (A z))) 2 (volume.restrict J) := by
    have h := c20_memLp_affine_time_pullback t k (ne_of_gt hk) Set.univ
      MeasurableSet.univ 2 (fun z => euclideanNorm (G z)) (by simpa using hG)
    have h' : MemLp (fun z => euclideanNorm (G (A z))) 2 volume := by simpa [A] using h
    exact h'.mono_measure Measure.restrict_le_self
  have hAc : Continuous A :=
    (continuous_const.add (continuous_const.mul continuous_fst)).prodMk continuous_snd
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hnorm := c20_weighted_forward_nonlinear_gradient_energy_limit_bounded
    hκ ρ α hell y (fun z => u (A z)) (fun z => G (A z)) huA hGA hG2A
    F hF M hM hF2 (fun z => ψ (A z)) (max C 0) (le_max_right _ _)
    ((hψ.continuous.comp hAc).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun z =>
      (show |ψ (A z)| ≤ C by simpa only [Real.norm_eq_abs] using hC (A z)).trans
        (le_max_left _ _)))
  have ht := (hnorm.comp (c20_tendsto_positive_time_div k hk)).const_mul k
  simp only [mul_zero] at ht
  convert ht using 1
  funext h
  have hI := c20_integral_affine_time_pullback_unconditional t k hk S hS
    (fun z => |deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
        (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z -
     deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z|)
  rw [hpre] at hI
  have heq : (∫ z in I,
      |deriv (deriv F) ((h / k)⁻¹ * ∫ s in (0 : ℝ)..(h / k), u (A (z.1+s,z.2))) *
        dot ((α (A z).2).mulVec ((h / k)⁻¹ • ∫ s in (0 : ℝ)..(h / k), G (A (z.1+s,z.2))))
          ((h / k)⁻¹ • ∫ s in (0 : ℝ)..(h / k), G (A (z.1+s,z.2))) * ψ (A z) -
       deriv (deriv F) (u (A z)) * dot ((α (A z).2).mulVec (G (A z))) (G (A z)) * ψ (A z)|) =
      k⁻¹ * ∫ z in S,
      |deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z -
       deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z| := by
    rw [← hI]
    apply integral_congr_ae
    filter_upwards with z
    have huavg := c20_forward_average_affine_spacetime u t k (h/k) (ne_of_gt hk) z
    have hGavg := c20_forward_average_affine_spacetime G t k (h/k) (ne_of_gt hk) z
    simp only [mul_div_cancel₀ h (ne_of_gt hk), smul_eq_mul] at huavg
    simp only [mul_div_cancel₀ h (ne_of_gt hk)] at hGavg
    simpa only [A, huavg, hGavg]
  change (∫ z in S, _) = k * (∫ z in I, _)
  rw [heq, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hk), one_mul]


/-- Compactly supported tests permit the nonlinear energy limit on any time interval. -/
@[nolint unusedArguments]
theorem c20_weighted_forward_nonlinear_gradient_energy_limit_compact_interval
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r) :
    let uh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)
    let Gh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      |deriv (deriv F) (uh h z) * dot ((α z.2).mulVec (Gh h z)) (Gh h z) * ψ z -
       deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z|)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  have hS : MeasurableSet S := measurableSet_Ioo.prod (c20_sourceBall_measurable y r)
  obtain ⟨hu0, hGm0, hG0⟩ := c20_memLp_zero_extension S hS u G hu hGm hG
  have ht := c20_weighted_forward_nonlinear_gradient_energy_limit_global (r := r)
    hκ hab ρ α hell y (S.indicator u) (S.indicator G) hu0 hGm0 hG0 F hF M hM hF2
    ψ hψ hψc
  obtain ⟨δ, hδ, heq⟩ := c20_compact_support_zero_extension_energy ψ hψc hψs u G α
    (deriv (deriv F))
  have hsmall : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), h < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  dsimp only
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhδ
  apply integral_congr_ae
  filter_upwards with z
  exact heq h ⟨le_of_lt hh, le_of_lt hhδ⟩ z

/-- On a compact test support, zero extension preserves both forward averages and
both original fields for all sufficiently small positive averaging parameters. -/
theorem c20_compact_support_zero_extension_fields {d : ℕ} {a b : ℝ}
    {U : Set (Vec d)} (ψ : ℝ × Vec d → ℝ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ U)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h ∈ Set.Icc (0 : ℝ) δ, ∀ z ∈ tsupport ψ,
      let S := Set.Ioo a b ×ˢ U
      (h⁻¹ * ∫ s in (0 : ℝ)..h, S.indicator u (z.1+s,z.2)) =
        (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) ∧
      (h⁻¹ • ∫ s in (0 : ℝ)..h, S.indicator G (z.1+s,z.2)) =
        (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) ∧
      S.indicator u z = u z ∧ S.indicator G z = G z := by
  obtain ⟨δu, hδu, hu⟩ := c20_compact_support_forward_indicator_integral ψ hψc hψs u
  obtain ⟨δG, hδG, hG⟩ := c20_compact_support_forward_indicator_integral ψ hψc hψs G
  refine ⟨min δu δG, lt_min hδu hδG, ?_⟩
  intro h hh z hz
  have hhu : h ∈ Set.Icc (0 : ℝ) δu := ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  have hhG : h ∈ Set.Icc (0 : ℝ) δG := ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
  dsimp only
  rw [hu z hz h hhu, hG z hz h hhG,
    Set.indicator_of_mem (hψs hz), Set.indicator_of_mem (hψs hz)]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A bounded second derivative and bounded test preserve integrability of the
elliptic gradient energy. -/
theorem c20_nonlinear_gradient_energy_integrable
    {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (μ : Measure (ℝ × Vec d))
    (u : ℝ × Vec d → ℝ) (hum : AEStronglyMeasurable u μ)
    (G : ℝ × Vec d → Vec d) (hGm : AEStronglyMeasurable G μ)
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 μ)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψm : AEStronglyMeasurable ψ μ)
    (C : ℝ) (hψb : ∀ᵐ z ∂μ, |ψ z| ≤ C) :
    Integrable (fun z => deriv (deriv F) (u z) *
      dot ((α z.2).mulVec (G z)) (G z) * ψ z) μ := by
  have he := c20_elliptic_gradient_energy_integrable hκ ρ α hell μ G hGm hG
  have hd : AEStronglyMeasurable (fun z => deriv (deriv F) (u z)) μ :=
    hF.deriv'.continuous_deriv_one.comp_aestronglyMeasurable hum
  have hb : ∀ᵐ z ∂μ, ‖deriv (deriv F) (u z)‖ ≤ M := by
    filter_upwards with z
    simpa only [Real.norm_eq_abs] using hF2 (u z)
  have hdb := he.bdd_mul hd hb
  have hp : ∀ᵐ z ∂μ, ‖ψ z‖ ≤ C := by
    filter_upwards [hψb] with z hz
    simpa only [Real.norm_eq_abs] using hz
  simpa only [Pi.mul_apply] using hdb.mul_bdd hψm hp

/-- The forward-averaged nonlinear energy is integrable on the smaller cylinder
for all sufficiently small positive averaging parameters. -/
theorem c20_nonlinear_forward_gradient_energy_eventually_integrable
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (C : ℝ)
    (hψm : AEStronglyMeasurable ψ (volume.restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)))
    (hψb : ∀ᵐ z ∂volume.restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r), |ψ z| ≤ C) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (fun z =>
      deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
        (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z)
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)) := by
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hvec := c20_vector_memLp_of_euclidean G hGm hG
  have hc : Continuous (fun v : Vec d => euclideanNorm v) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).mul (continuous_apply i))
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 / 4 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hs
  have huavg := c18_memLp_forward_average (c20_sourceBall_measurable y r) hh
    (le_of_lt hs) hu
  have hGavg := c18_memLp_forward_average (c20_sourceBall_measurable y r) hh
    (le_of_lt hs) hvec
  have hGnorm : MemLp (fun z => euclideanNorm
      (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)) := by
    apply (hGavg.norm.const_mul ((d : ℝ) + 1)).mono'
      (hc.comp_aestronglyMeasurable hGavg.aestronglyMeasurable)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ euclideanNorm
      (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) from Real.sqrt_nonneg _)]
    exact euclideanNorm_le_dimension_mul_norm _
  apply c20_nonlinear_gradient_energy_integrable hκ ρ α hell _ _ ?_ _
    hGavg.aestronglyMeasurable hGnorm F hF M hF2 ψ hψm C hψb
  simpa only [smul_eq_mul] using huavg.aestronglyMeasurable

/-- Integrability is invariant under a nondegenerate affine change of time. -/
theorem c20_integrable_affine_time_pullback_iff {d : ℕ} (t k : ℝ) (hk : 0 < k)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S) (f : ℝ × Vec d → ℝ) :
    Integrable (fun z => f (t + k * z.1, z.2))
      (volume.restrict ((fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S)) ↔
    Integrable f (volume.restrict S) := by
  let e : (ℝ × Vec d) ≃ᵐ (ℝ × Vec d) :=
    { toFun := fun z => (t + k * z.1, z.2)
      invFun := fun z => ((z.1 - t) / k, z.2)
      left_inv := by
        intro z
        simp [add_sub_cancel_left, mul_div_cancel_left₀ _ (ne_of_gt hk)]
      right_inv := by
        intro z
        simp [mul_div_cancel₀ _ (ne_of_gt hk)]
      measurable_toFun :=
        ((measurable_const_mul k).comp measurable_fst |>.const_add t).prodMk measurable_snd
      measurable_invFun :=
        ((measurable_fst.sub measurable_const).div_const k).prodMk measurable_snd }
  have he := integrable_map_equiv e f
    (μ := volume.restrict ((fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S))
  change Integrable f (Measure.map (fun z : ℝ × Vec d => (t + k * z.1, z.2))
    (volume.restrict ((fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S))) ↔ _ at he
  rw [c20_map_restrict_volume_affine_time_prod t k (ne_of_gt hk) S hS,
    integrable_smul_measure (by simp [ne_of_gt hk]) ENNReal.ofReal_ne_top] at he
  exact he.symm

/-- Averaged energy for global L² fields is integrable on any bounded time cylinder. -/
theorem c20_nonlinear_forward_gradient_energy_eventually_integrable_global
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 volume) (hGm : AEStronglyMeasurable G volume)
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 volume)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (fun z =>
      deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
        (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z)
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
  let t : ℝ := (a + b) / 2
  let k : ℝ := b - a
  have hk : 0 < k := by dsimp [k]; linarith
  let A : ℝ × Vec d → ℝ × Vec d := fun z => (t + k * z.1, z.2)
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  let I : Set (ℝ × Vec d) := Set.Ioo (-1/2 : ℝ) (1/2) ×ˢ sourceBall y r
  let J : Set (ℝ × Vec d) := Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r
  have ha : t + k * (-1/2) = a := by dsimp [t, k]; ring
  have hb : t + k * (1/2) = b := by dsimp [t, k]; ring
  have hpre : A ⁻¹' S = I := by
    simpa only [A, S, I, ha, hb] using
      c20_affine_time_preimage_slab t k (-1/2) (1/2) hk (sourceBall y r)
  have hS : MeasurableSet S := measurableSet_Ioo.prod (c20_sourceBall_measurable y r)
  have huA : MemLp (fun z => u (A z)) 2 (volume.restrict J) := by
    have h := c20_memLp_affine_time_pullback t k (ne_of_gt hk) Set.univ
      MeasurableSet.univ 2 u (by simpa using hu)
    have h' : MemLp (fun z => u (A z)) 2 volume := by simpa [A] using h
    exact h'.mono_measure Measure.restrict_le_self
  have hGA : AEStronglyMeasurable (fun z => G (A z)) (volume.restrict J) := by
    have h := c20_aestronglyMeasurable_affine_time_pullback t k (ne_of_gt hk) Set.univ
      MeasurableSet.univ G (by simpa using hGm)
    have h' : AEStronglyMeasurable (fun z => G (A z)) volume := by simpa [A] using h
    exact h'.mono_measure Measure.restrict_le_self
  have hG2A : MemLp (fun z => euclideanNorm (G (A z))) 2 (volume.restrict J) := by
    have h := c20_memLp_affine_time_pullback t k (ne_of_gt hk) Set.univ
      MeasurableSet.univ 2 (fun z => euclideanNorm (G z)) (by simpa using hG)
    have h' : MemLp (fun z => euclideanNorm (G (A z))) 2 volume := by simpa [A] using h
    exact h'.mono_measure Measure.restrict_le_self
  have hAc : Continuous A :=
    (continuous_const.add (continuous_const.mul continuous_fst)).prodMk continuous_snd
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have ht := c20_nonlinear_forward_gradient_energy_eventually_integrable
    hκ ρ α hell y (fun z => u (A z)) (fun z => G (A z)) huA hGA hG2A
    F hF M hF2 (fun z => ψ (A z)) C
    ((hψ.continuous.comp hAc).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hC (A z)))
  have ht' := (c20_tendsto_positive_time_div k hk).eventually ht
  filter_upwards [ht'] with h hh
  apply (c20_integrable_affine_time_pullback_iff t k hk S hS _).mp
  rw [show (fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S = I from hpre]
  convert hh using 1
  funext z
  have huavg := c20_forward_average_affine_spacetime u t k (h/k) (ne_of_gt hk) z
  have hGavg := c20_forward_average_affine_spacetime G t k (h/k) (ne_of_gt hk) z
  simp only [mul_div_cancel₀ h (ne_of_gt hk), smul_eq_mul] at huavg
  simp only [mul_div_cancel₀ h (ne_of_gt hk)] at hGavg
  simpa only [A, huavg, hGavg]
  dsimp [I]
  congr 2 <;> norm_num

/-- Compactly supported tests localize integrability of the averaged energy. -/
theorem c20_nonlinear_forward_gradient_energy_eventually_integrable_compact
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (fun z =>
      deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
        (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z)
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  have hS : MeasurableSet S := measurableSet_Ioo.prod (c20_sourceBall_measurable y r)
  obtain ⟨hu0, hGm0, hG0⟩ := c20_memLp_zero_extension S hS u G hu hGm hG
  have ht := c20_nonlinear_forward_gradient_energy_eventually_integrable_global (r := r)
    hκ hab ρ α hell y (S.indicator u) (S.indicator G) hu0 hGm0 hG0 F hF M hF2 ψ hψ hψc
  obtain ⟨δ, hδ, heq⟩ := c20_compact_support_zero_extension_fields ψ hψc hψs u G
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [ht, self_mem_nhdsWithin, hsmall] with h hh hp hd
  apply hh.congr
  filter_upwards with z
  by_cases hz : z ∈ tsupport ψ
  · obtain ⟨hu', hG', _, _⟩ := heq h ⟨le_of_lt hp, le_of_lt hd⟩ z hz
    rw [hu', hG']
  · simp [image_eq_zero_of_notMem_tsupport hz]

/-- The nonlinear quadratic energy itself converges on a compactly tested cylinder. -/
theorem c20_weighted_forward_nonlinear_gradient_energy_integral_limit_compact
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r) :
    let uh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)
    let Gh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      deriv (deriv F) (uh h z) * dot ((α z.2).mulVec (Gh h z)) (Gh h z) * ψ z)
      (𝓝[>] 0) (𝓝 (∫ z in Set.Ioo a b ×ˢ sourceBall y r,
        deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z)) := by
  dsimp only
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hu' := c20_nonlinear_gradient_energy_integrable hκ ρ α hell _ u
    hu.aestronglyMeasurable G hGm hG F hF M hF2 ψ hψ.continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hC z))
  have hf := c20_nonlinear_forward_gradient_energy_eventually_integrable_compact
    hκ hab ρ α hell y u G hu hGm hG F hF M hF2 ψ hψ hψc hψs
  have hl := c20_weighted_forward_nonlinear_gradient_energy_limit_compact_interval
    hκ hr hab ρ α hell y u G hu hGm hG F hF M hM hF2 ψ hψ hψc hψs
  have ht := c20_weighted_integral_of_L1_limit
    (fun h z => deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
        (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z)
    (fun z => deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z)
    (fun _ => 1) 1 (by fun_prop) (by simp) hf hu' hl
  simpa only [one_mul] using ht

end EinsteinFull.Calculus
