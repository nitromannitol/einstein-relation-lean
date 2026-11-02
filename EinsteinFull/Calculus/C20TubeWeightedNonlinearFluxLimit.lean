import EinsteinFull.Calculus.C20TubeWeightedNonlinearEnergyLimit

open EinsteinRelation MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace EinsteinFull.Calculus

/-- A bounded second derivative makes the first derivative globally Lipschitz. -/
theorem c20_deriv_lipschitz_bound (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (M : ℝ) (hF2 : ∀ s, |deriv (deriv F) s| ≤ M) (x y : ℝ) :
    |deriv F y - deriv F x| ≤ M * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (f := deriv F) (C := M)
    (fun t _ => hF.differentiable_deriv_two t)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hF2 t)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa only [Real.norm_eq_abs] using h

/-- A linearly growing derivative maps L² data to L² on a finite measure space. -/
theorem c20_deriv_comp_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (u : Ω → ℝ) (hu : MemLp u 2 μ)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M) :
    MemLp (fun x => deriv F (u x)) 2 μ := by
  have hc : MemLp (fun _ : Ω => |deriv F 0|) 2 μ := memLp_const _
  have hm : MemLp (fun x => M * |u x|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hu.norm.const_mul M
  have hb : MemLp (fun x => |deriv F 0| + M * |u x|) 2 μ := hc.add hm
  have hF' : ContDiff ℝ 1 (deriv F) := hF.deriv'
  apply hb.mono' (hF'.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable)
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using c20_deriv_linear_growth F hF M hF2 (u x)

/-- Derivative compositions inherit strong L² convergence from their arguments. -/
theorem c20_deriv_comp_L2_limit
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    (f : ι → Ω → ℝ) (u : Ω → ℝ)
    (he : ∀ᶠ n in l, MemLp (f n - u) 2 μ)
    (hlim : Tendsto (fun n => ∫ x, |f n x - u x| ^ 2 ∂μ) l (𝓝 0))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M) :
    Tendsto (fun n => ∫ x, |deriv F (f n x) - deriv F (u x)| ^ 2 ∂μ) l (𝓝 0) := by
  have hupper : Tendsto (fun n => M ^ 2 * ∫ x, |f n x - u x| ^ 2 ∂μ) l (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul (M ^ 2)
  apply squeeze_zero' _ _ hupper
  · exact Filter.Eventually.of_forall fun n => integral_nonneg fun x => sq_nonneg _
  · filter_upwards [he] with n hn
    have hi : Integrable (fun x => M ^ 2 * |f n x - u x| ^ 2) μ := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        (hn.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul (M ^ 2)
    calc
      (∫ x, |deriv F (f n x) - deriv F (u x)| ^ 2 ∂μ) ≤
          ∫ x, M ^ 2 * |f n x - u x| ^ 2 ∂μ := by
        apply integral_mono_of_nonneg (ae_of_all μ fun x => sq_nonneg _) hi
        filter_upwards with x
        have h := c20_deriv_lipschitz_bound F hF M hF2 (u x) (f n x)
        have hp : 0 ≤ M * |f n x - u x| := mul_nonneg hM (abs_nonneg _)
        have hs := (sq_le_sq₀ (abs_nonneg _) hp).2 h
        simpa only [mul_pow] using hs
      _ = M ^ 2 * ∫ x, |f n x - u x| ^ 2 ∂μ := integral_const_mul _ _

/-- Products of two strong L² errors converge to zero in L¹. -/
theorem c20_integral_abs_mul_errors_tendsto_zero
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    (e g : ι → Ω → ℝ)
    (he : ∀ᶠ n in l, MemLp (e n) 2 μ)
    (hg : ∀ᶠ n in l, MemLp (g n) 2 μ)
    (helim : Tendsto (fun n => ∫ x, |e n x| ^ 2 ∂μ) l (𝓝 0))
    (hglim : Tendsto (fun n => ∫ x, |g n x| ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun n => ∫ x, |e n x| * |g n x| ∂μ) l (𝓝 0) := by
  have hupper : Tendsto (fun n => (1 / 2 : ℝ) *
      ((∫ x, |e n x| ^ 2 ∂μ) + ∫ x, |g n x| ^ 2 ∂μ)) l (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (helim.add hglim).const_mul (1 / 2 : ℝ)
  apply squeeze_zero' _ _ hupper
  · exact Filter.Eventually.of_forall fun n => integral_nonneg fun x =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · filter_upwards [he, hg] with n hen hgn
    have hei : Integrable (fun x => |e n x| ^ 2) μ := by
      simpa only [Real.norm_eq_abs] using hen.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hgi : Integrable (fun x => |g n x| ^ 2) μ := by
      simpa only [Real.norm_eq_abs] using hgn.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    calc
      (∫ x, |e n x| * |g n x| ∂μ) ≤
          ∫ x, (1 / 2 : ℝ) * (|e n x| ^ 2 + |g n x| ^ 2) ∂μ := by
        apply integral_mono_of_nonneg
          (ae_of_all μ fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
          ((hei.add hgi).const_mul _)
        filter_upwards with x
        simp only [Pi.add_apply]
        nlinarith [sq_nonneg (|e n x| - |g n x|)]
      _ = (1 / 2 : ℝ) * ((∫ x, |e n x| ^ 2 ∂μ) +
          ∫ x, |g n x| ^ 2 ∂μ) := by rw [integral_const_mul, integral_add hei hgi]

/-- Derivatives of scalar forward averages converge in L² on the source cylinder. -/
theorem c20_scalar_forward_deriv_L2_limit {d : ℕ} (y : Vec d) (r : ℝ)
    (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r,
      |deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) - deriv F (u z)| ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let U := EinsteinFull.External.Source.GMP.sourceBall y r
  have hU : MeasurableSet U := c20_sourceBall_measurable y r
  apply c20_deriv_comp_L2_limit
    (fun h z => h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) u
  · have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 / 2 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhsmall
    exact c20_scalar_forward_average_slab_memLp U hU u hu (le_of_lt hh) (le_of_lt hhsmall)
  · exact c20_scalar_forward_average_slab_L2 U hU u hu
  · exact hF
  · exact hM
  · exact hF2

/-- The derivative error of the scalar forward average is eventually L². -/
theorem c20_scalar_forward_deriv_error_eventually_memLp {d : ℕ} (y : Vec d) (r : ℝ)
    (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp
      (fun z => deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) - deriv F (u z)) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r)) := by
  let U := EinsteinFull.External.Source.GMP.sourceBall y r
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hus : MemLp u 2 (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) := by
    apply MemLp.mono_measure (Measure.restrict_mono_set volume ?_) hu
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hdu := c20_deriv_comp_memLp u hus F hF M hF2
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhsmall
  have he := c20_scalar_forward_average_slab_memLp U (c20_sourceBall_measurable y r)
    u hu (le_of_lt hh) (le_of_lt hhsmall)
  have havg : MemLp (fun z => h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) := by
    convert he.add hus using 1 <;> ext z <;> simp
  exact (c20_deriv_comp_memLp _ havg F hF M hF2).sub hdu

/-- The Euclidean norm of the vector averaging error is eventually in L². -/
theorem c20_vector_forward_error_eventually_memLp {d : ℕ} (y : Vec d) (r : ℝ)
    (G : ℝ × Vec d → Vec d)
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r))) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp
      (fun z => euclideanNorm (h⁻¹ • (∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) - G z)) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r)) := by
  let U := EinsteinFull.External.Source.GMP.sourceBall y r
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hvec := c20_vector_memLp_of_euclidean G hGm hG
  have hvecs : MemLp G 2 (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) := by
    apply MemLp.mono_measure (Measure.restrict_mono_set volume ?_) hvec
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hnorm : Continuous (fun v : Vec d => euclideanNorm v) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).mul (continuous_apply i))
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 / 4 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhsmall
  have havg := c18_memLp_forward_average (c20_sourceBall_measurable y r) hh
    (le_of_lt hhsmall) hvec
  have he := havg.sub hvecs
  apply (he.norm.const_mul ((d : ℝ) + 1)).mono'
    (hnorm.comp_aestronglyMeasurable he.aestronglyMeasurable)
  filter_upwards with z
  simp only [Pi.sub_apply] 
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ euclideanNorm
    (h⁻¹ • (∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) - G z) from Real.sqrt_nonneg _)]
  exact euclideanNorm_le_dimension_mul_norm _

/-- An elliptic flux tested against a Euclidean unit vector is bounded. -/
theorem c20_elliptic_flux_unit_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (x g v : Vec d) (hv : euclideanNorm v ≤ 1) :
    |dot ((α x).mulVec g) v| ≤ κ⁻¹ * euclideanNorm g := by
  have hcomm : dot ((α x).mulVec g) v = dot v ((α x).mulVec g) := by
    simp only [dot, mul_comm]
  rw [hcomm]
  have hb := c20_elliptic_bilinear_bound hκ ρ α hell x v g
  have hk : 0 ≤ κ⁻¹ := le_of_lt (inv_pos.mpr hκ)
  have hg : 0 ≤ euclideanNorm g := Real.sqrt_nonneg _
  calc
    |dot v ((α x).mulVec g)| ≤ κ⁻¹ * euclideanNorm v * euclideanNorm g := hb
    _ ≤ κ⁻¹ * 1 * euclideanNorm g := by gcongr
    _ = κ⁻¹ * euclideanNorm g := by ring

/-- Pointwise decomposition of a nonlinear elliptic flux difference. -/
theorem c20_elliptic_flux_difference_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (x g g₀ v : Vec d) (hv : euclideanNorm v ≤ 1) (a b : ℝ) :
    |a * dot ((α x).mulVec g) v - b * dot ((α x).mulVec g₀) v| ≤
      κ⁻¹ * (|a - b| * euclideanNorm g₀ + |b| * euclideanNorm (g - g₀) +
        |a - b| * euclideanNorm (g - g₀)) := by
  let A := dot ((α x).mulVec g) v
  let B := dot ((α x).mulVec g₀) v
  have hsub : A - B = dot ((α x).mulVec (g - g₀)) v := by
    dsimp [A, B]
    simp only [Matrix.mulVec_sub, dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hb := c20_elliptic_flux_unit_bound hκ ρ α hell x g₀ v hv
  have hd := c20_elliptic_flux_unit_bound hκ ρ α hell x (g - g₀) v hv
  change |B| ≤ _ at hb
  rw [← hsub] at hd
  have ha : |a| ≤ |a - b| + |b| := by
    have h := abs_add_le (a - b) b
    have he : a - b + b = a := by ring
    simpa only [he] using h
  have ht := abs_add_le ((a - b) * B) (a * (A - B))
  have he : (a - b) * B + a * (A - B) = a * A - b * B := by ring
  rw [he, abs_mul, abs_mul] at ht
  have hk : 0 ≤ κ⁻¹ := le_of_lt (inv_pos.mpr hκ)
  have hg : 0 ≤ euclideanNorm g₀ := Real.sqrt_nonneg _
  have hdg : 0 ≤ euclideanNorm (g - g₀) := Real.sqrt_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hb (abs_nonneg (a - b))
  have h2 := mul_le_mul_of_nonneg_left hd (abs_nonneg a)
  have h3 := mul_le_mul_of_nonneg_right ha (mul_nonneg hk hdg)
  calc
    |a * A - b * B| ≤ |a - b| * |B| + |a| * |A - B| := ht
    _ ≤ |a - b| * (κ⁻¹ * euclideanNorm g₀) +
        (|a - b| + |b|) * (κ⁻¹ * euclideanNorm (g - g₀)) := by linarith
    _ = κ⁻¹ * (|a - b| * euclideanNorm g₀ + |b| * euclideanNorm (g - g₀) +
        |a - b| * euclideanNorm (g - g₀)) := by ring

/-- Changing the gradient changes its elliptic quadratic energy by an L² product. -/
theorem c20_elliptic_quadratic_difference_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (x g g₀ : Vec d) :
    |dot ((α x).mulVec g) g - dot ((α x).mulVec g₀) g₀| ≤
      κ⁻¹ * (2 * euclideanNorm (g - g₀) * euclideanNorm g₀ +
        euclideanNorm (g - g₀) ^ 2) := by
  let e := g - g₀
  have hs₁ : dot ((α x).mulVec g) g - dot ((α x).mulVec g₀) g₀ =
      dot ((α x).mulVec e) g + dot ((α x).mulVec g₀) e := by
    dsimp [e]
    simp only [Matrix.mulVec_sub, dot, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have hs₂ : dot ((α x).mulVec e) g =
      dot ((α x).mulVec e) g₀ + dot ((α x).mulVec e) e := by
    dsimp [e]
    simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hb₁ := c20_elliptic_bilinear_bound hκ ρ α hell x g₀ e
  have hb₂ := c20_elliptic_bilinear_bound hκ ρ α hell x e g₀
  have hb₃ := c20_elliptic_bilinear_bound hκ ρ α hell x e e
  have hc₁ : dot ((α x).mulVec e) g₀ = dot g₀ ((α x).mulVec e) := by
    simp only [dot, mul_comm]
  have hc₂ : dot ((α x).mulVec g₀) e = dot e ((α x).mulVec g₀) := by
    simp only [dot, mul_comm]
  have hc₃ : dot ((α x).mulVec e) e = dot e ((α x).mulVec e) := by
    simp only [dot, mul_comm]
  rw [hs₁, hs₂]
  have ht₁ := abs_add_le (dot ((α x).mulVec e) g₀ + dot ((α x).mulVec e) e)
    (dot ((α x).mulVec g₀) e)
  have ht₂ := abs_add_le (dot ((α x).mulVec e) g₀) (dot ((α x).mulVec e) e)
  simp only [hc₁, hc₂, hc₃] at ht₁ ht₂ ⊢
  dsimp only [e] at *
  nlinarith [sq_nonneg (euclideanNorm (g - g₀))]

/-- The nonlinear elliptic flux of forward averages converges in L¹. -/
theorem c20_weighted_forward_nonlinear_flux_limit
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (V : ℝ × Vec d → Vec d)
    (hVm : AEStronglyMeasurable V (volume.restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hVb : ∀ᵐ z ∂volume.restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r),
      euclideanNorm (V z) ≤ 1) :
    let I := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
    let U := EinsteinFull.External.Source.GMP.sourceBall y r
    let uh := fun (h : ℝ) (z : ℝ × Vec d) =>
      h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
    let Gh := fun (h : ℝ) (z : ℝ × Vec d) =>
      h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
    Tendsto (fun h : ℝ => ∫ z in I ×ˢ U,
      |deriv F (uh h z) * dot ((α z.2).mulVec (Gh h z)) (V z) -
        deriv F (u z) * dot ((α z.2).mulVec (G z)) (V z)|)
      (𝓝[>] 0) (𝓝 0) := by
  dsimp only
  let U := EinsteinFull.External.Source.GMP.sourceBall y r
  let T := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U
  let μ := volume.restrict T
  letI : IsFiniteMeasure μ := c18_smallSourceCylinder_isFiniteMeasure y r
  let e : ℝ → ℝ × Vec d → ℝ := fun h z =>
    deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) - deriv F (u z)
  let q : ℝ → ℝ × Vec d → ℝ := fun h z =>
    euclideanNorm (h⁻¹ • (∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) - G z)
  let f : ℝ × Vec d → ℝ := fun z => deriv F (u z)
  let g : ℝ × Vec d → ℝ := fun z => euclideanNorm (G z)
  have hus : MemLp u 2 μ := by
    apply MemLp.mono_measure (Measure.restrict_mono_set volume ?_) hu
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hgs : MemLp g 2 μ := by
    apply MemLp.mono_measure (Measure.restrict_mono_set volume ?_) hG
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hfs : MemLp f 2 μ := c20_deriv_comp_memLp u hus F hF M hF2
  have he : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (e h) 2 μ :=
    c20_scalar_forward_deriv_error_eventually_memLp y r u hu F hF M hF2
  have hq : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (q h) 2 μ :=
    c20_vector_forward_error_eventually_memLp y r G hGm hG
  have helim : Tendsto (fun h : ℝ => ∫ z, |e h z| ^ 2 ∂μ) (𝓝[>] 0) (𝓝 0) :=
    c20_scalar_forward_deriv_L2_limit y r u hu F hF M hM hF2
  have hq0 (h : ℝ) (z : ℝ × Vec d) : 0 ≤ q h z := Real.sqrt_nonneg _
  have hqlim : Tendsto (fun h : ℝ => ∫ z, |q h z| ^ 2 ∂μ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [abs_of_nonneg (hq0 _ _), q, μ, T, U] using
      (c20_weighted_forward_average_L2_limit hκ ρ α hell y u G hu hGm hG).2
  have hl1 := c20_integral_abs_mul_fixed_L2_tendsto_zero e g he hgs helim
  have hl2 := c20_integral_abs_mul_fixed_L2_tendsto_zero q f hq hfs hqlim
  have hl3 := c20_integral_abs_mul_errors_tendsto_zero e q he hq helim hqlim
  have hupper : Tendsto (fun h : ℝ => κ⁻¹ *
      ((∫ z, |e h z| * |g z| ∂μ) + (∫ z, |q h z| * |f z| ∂μ) +
        ∫ z, |e h z| * |q h z| ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [add_zero, mul_zero] using ((hl1.add hl2).add hl3).const_mul κ⁻¹
  apply squeeze_zero' _ _ hupper
  · exact Filter.Eventually.of_forall fun h => integral_nonneg fun z => abs_nonneg _
  · filter_upwards [he, hq] with h heh hqh
    have hi1 : Integrable (fun z => |e h z| * |g z|) μ := by
      convert heh.norm.integrable_mul hgs.norm using 1 <;> ext z <;> simp [Real.norm_eq_abs]
    have hi2 : Integrable (fun z => |q h z| * |f z|) μ := by
      convert hqh.norm.integrable_mul hfs.norm using 1 <;> ext z <;> simp [Real.norm_eq_abs]
    have hi3 : Integrable (fun z => |e h z| * |q h z|) μ := by
      convert heh.norm.integrable_mul hqh.norm using 1 <;> ext z <;> simp [Real.norm_eq_abs]
    calc
      (∫ z in T, |deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) *
          dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2))) (V z) -
          deriv F (u z) * dot ((α z.2).mulVec (G z)) (V z)|) ≤
        ∫ z, κ⁻¹ * (|e h z| * |g z| + |q h z| * |f z| + |e h z| * |q h z|) ∂μ := by
        apply integral_mono_of_nonneg (ae_of_all μ fun z => abs_nonneg _)
          (((hi1.add hi2).add hi3).const_mul _)
        filter_upwards [hVb, hVm.ae_eq_mk] with z hz hzm
        have hb := c20_elliptic_flux_difference_bound hκ ρ α hell z.2
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) (G z) (V z) hz
          (deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) (deriv F (u z))
        simpa only [Pi.add_apply, e, q, f, g, euclideanNorm,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_comm] using hb
      _ = κ⁻¹ * ((∫ z, |e h z| * |g z| ∂μ) + (∫ z, |q h z| * |f z| ∂μ) +
          ∫ z, |e h z| * |q h z| ∂μ) := by
        have hs := (integral_add (hi1.add hi2) hi3).trans
          (congrArg (fun t => t + ∫ z, |e h z| * |q h z| ∂μ) (integral_add hi1 hi2))
        simpa only [Pi.add_apply, integral_const_mul] using congrArg (fun t => κ⁻¹ * t) hs

/-- Forward averaging preserves the elliptic gradient energy in L¹. -/
@[nolint unusedArguments]
theorem c20_weighted_forward_gradient_energy_L1_limit
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r))) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r,
      |dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)))
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) -
        dot ((α z.2).mulVec (G z)) (G z)|) (𝓝[>] 0) (𝓝 0) := by
  let U := EinsteinFull.External.Source.GMP.sourceBall y r
  let T := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U
  let μ := volume.restrict T
  let q : ℝ → ℝ × Vec d → ℝ := fun h z =>
    euclideanNorm (h⁻¹ • (∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) - G z)
  let g : ℝ × Vec d → ℝ := fun z => euclideanNorm (G z)
  have hgs : MemLp g 2 μ := by
    apply MemLp.mono_measure (Measure.restrict_mono_set volume ?_) hG
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hq : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (q h) 2 μ :=
    c20_vector_forward_error_eventually_memLp y r G hGm hG
  have hq0 (h : ℝ) (z : ℝ × Vec d) : 0 ≤ q h z := Real.sqrt_nonneg _
  have hqlim : Tendsto (fun h : ℝ => ∫ z, |q h z| ^ 2 ∂μ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [abs_of_nonneg (hq0 _ _), q, μ, T, U] using
      (c20_weighted_forward_average_L2_limit hκ ρ α hell y u G hu hGm hG).2
  have hl := c20_integral_abs_mul_fixed_L2_tendsto_zero q g hq hgs hqlim
  have hupper : Tendsto (fun h : ℝ => κ⁻¹ *
      (2 * (∫ z, |q h z| * |g z| ∂μ) + ∫ z, |q h z| ^ 2 ∂μ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [add_zero, mul_zero] using ((hl.const_mul 2).add hqlim).const_mul κ⁻¹
  apply squeeze_zero' _ _ hupper
  · exact Filter.Eventually.of_forall fun h => integral_nonneg fun z => abs_nonneg _
  · filter_upwards [hq] with h hqh
    have hi₁ : Integrable (fun z => |q h z| * |g z|) μ := by
      convert hqh.norm.integrable_mul hgs.norm using 1 <;> ext z <;> simp [Real.norm_eq_abs]
    have hi₂ : Integrable (fun z => |q h z| ^ 2) μ := by
      simpa only [Real.norm_eq_abs] using hqh.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    calc
      (∫ z in T, |dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)))
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) - dot ((α z.2).mulVec (G z)) (G z)|) ≤
          ∫ z, κ⁻¹ * (2 * (|q h z| * |g z|) + |q h z| ^ 2) ∂μ := by
        apply integral_mono_of_nonneg (ae_of_all μ fun z => abs_nonneg _)
          ((hi₁.const_mul 2 |>.add hi₂).const_mul _)
        filter_upwards with z
        have hb := c20_elliptic_quadratic_difference_bound hκ ρ α hell z.2
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) (G z)
        simpa only [Pi.add_apply, q, g, euclideanNorm, abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc] using hb
      _ = κ⁻¹ * (2 * (∫ z, |q h z| * |g z| ∂μ) + ∫ z, |q h z| ^ 2 ∂μ) := by
        simp only [integral_const_mul, integral_add (hi₁.const_mul 2) hi₂]

end EinsteinFull.Calculus
