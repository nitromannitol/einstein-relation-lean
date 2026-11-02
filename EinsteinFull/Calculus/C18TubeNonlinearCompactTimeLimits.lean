import EinsteinFull.Calculus.C20TubeWeightedGradientEnergyLimit
import EinsteinRelation.TimeChange.EuclideanTransport

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- Bounded weights preserve the nonlinear forward-average scalar limit on an
arbitrary time interval when the original field is globally square integrable. -/
theorem c18_scalar_forward_average_weighted_comp_limit_global
    {d : ℕ} {a b r : ℝ} (hab : a < b) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (hu : MemLp u 2 volume)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (w : ℝ × Vec d → ℝ) (C : ℝ)
    (hw : Measurable w) (hwb : ∀ z, |w z| ≤ C) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      w z * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)))
      (𝓝[>] 0) (𝓝 (∫ z in Set.Ioo a b ×ˢ sourceBall y r, w z * F (u z))) := by
  let t : ℝ := (a + b) / 2
  let k : ℝ := b - a
  have hk : 0 < k := by dsimp [k]; linarith
  let A : ℝ × Vec d → ℝ × Vec d := fun z => (t + k * z.1, z.2)
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  let I : Set (ℝ × Vec d) := Set.Ioo (-(1/2 : ℝ)) (1/2) ×ˢ sourceBall y r
  let J : Set (ℝ × Vec d) := Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r
  have ha : t + k * (-(1/2)) = a := by dsimp [t, k]; ring
  have hb : t + k * (1/2) = b := by dsimp [t, k]; ring
  have hpre : A ⁻¹' S = I := by
    simpa only [A, S, I, ha, hb] using
      c20_affine_time_preimage_slab t k (-(1/2)) (1/2) hk (sourceBall y r)
  have hS : MeasurableSet S := measurableSet_Ioo.prod (c20_sourceBall_measurable y r)
  have huA : MemLp (fun z => u (A z)) 2 (volume.restrict J) := by
    have h := c20_memLp_affine_time_pullback t k (ne_of_gt hk) Set.univ
      MeasurableSet.univ 2 u (by simpa using hu)
    have h' : MemLp (fun z => u (A z)) 2 volume := by simpa [A] using h
    exact h'.mono_measure Measure.restrict_le_self
  letI : IsFiniteMeasure ((volume : Measure (ℝ × Vec d)).restrict I) :=
    c18_smallSourceCylinder_isFiniteMeasure y r
  have hAc : Measurable A :=
    ((measurable_const_mul k).comp measurable_fst |>.const_add t).prodMk measurable_snd
  have hnorm := c20_scalar_forward_average_weighted_comp_limit (sourceBall y r)
    (c20_sourceBall_measurable y r) (fun z => u (A z)) huA F hF M hM hF2
    (fun z => w (A z)) C ((hw.comp hAc).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => hwb (A z))
  have ht := (hnorm.comp (c20_tendsto_positive_time_div k hk)).const_mul k
  have hI (f : ℝ × Vec d → ℝ) : (∫ z in I, f (A z)) = k⁻¹ * ∫ z in S, f z := by
    have hh := c20_integral_affine_time_pullback_unconditional t k hk S hS f
    simpa only [hpre, A] using hh
  have htarget : k * (∫ z in I, w (A z) * F (u (A z))) =
      ∫ z in S, w z * F (u z) := by
    change k * (∫ z in I, (fun z => w z * F (u z)) (A z)) = _
    rw [hI (fun z => w z * F (u z))]
    simp [ne_of_gt hk]
  rw [htarget] at ht
  convert ht using 1
  funext h
  have htransport := hI (fun z => w z * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)))
  have heq : (∫ z in I, w (A z) * F ((h / k)⁻¹ *
      ∫ s in (0 : ℝ)..(h / k), u (A (z.1+s,z.2)))) =
      k⁻¹ * ∫ z in S, w z * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) := by
    rw [← htransport]
    apply integral_congr_ae
    filter_upwards with z
    have hh := c20_forward_average_affine_spacetime u t k (h/k) (ne_of_gt hk) z
    simp only [mul_div_cancel₀ h (ne_of_gt hk), smul_eq_mul] at hh
    simpa only [A, hh]
  change (∫ z in S, w z * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) =
    k * (∫ z in I, w (A z) * F ((h / k)⁻¹ *
      ∫ s in (0 : ℝ)..(h / k), u (A (z.1+s,z.2))))
  rw [heq]
  simp [ne_of_gt hk]


/-- Compactly supported bounded weights localize the scalar limit to the
original cylinder, using only local square integrability. -/
theorem c18_scalar_forward_average_weighted_comp_limit_compact
    {d : ℕ} {a b r : ℝ} (hab : a < b) (y : Vec d)
    (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (w ψ : ℝ × Vec d → ℝ) (C : ℝ)
    (hw : Measurable w) (hwb : ∀ z, |w z| ≤ C)
    (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r)
    (hwzero : ∀ z, ψ z = 0 → w z = 0) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      w z * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)))
      (𝓝[>] 0) (𝓝 (∫ z in Set.Ioo a b ×ˢ sourceBall y r, w z * F (u z))) := by
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  have hS : MeasurableSet S := measurableSet_Ioo.prod (c20_sourceBall_measurable y r)
  have hu0 : MemLp (S.indicator u) 2 volume := (memLp_indicator_iff_restrict hS).2 hu
  have ht := c18_scalar_forward_average_weighted_comp_limit_global (r := r) hab y
    (S.indicator u) hu0 F hF M hM hF2 w C hw hwb
  have htarget : (∫ z in S, w z * F (S.indicator u z)) =
      ∫ z in S, w z * F (u z) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hS] with z hz
    rw [Set.indicator_of_mem hz]
  rw [htarget] at ht
  obtain ⟨δ, hδ, heq⟩ := c20_compact_support_forward_indicator_integral ψ hψc hψs u
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhδ
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ tsupport ψ
  · rw [heq z hz h ⟨le_of_lt hh, le_of_lt hhδ⟩]
  · have hwz := hwzero z (image_eq_zero_of_notMem_tsupport hz)
    simp [hwz]


/-- The nonlinear flux limit holds for any finite bound on the vector test. -/
@[nolint unusedArguments]
theorem c18_weighted_forward_nonlinear_flux_limit_bounded
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (V : ℝ × Vec d → Vec d) (C : ℝ) (hC : 0 ≤ C)
    (hVm : AEStronglyMeasurable V (volume.restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)))
    (hVb : ∀ᵐ z ∂volume.restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r), euclideanNorm (V z) ≤ C) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      |deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) (V z) -
       deriv F (u z) * dot ((α z.2).mulVec (G z)) (V z)|)
      (𝓝[>] 0) (𝓝 0) := by
  have hpos : 0 < C + 1 := by linarith
  have hb : ∀ᵐ z ∂volume.restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r),
      euclideanNorm ((C + 1)⁻¹ • V z) ≤ 1 := by
    filter_upwards [hVb] with z hz
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hpos), ← div_eq_inv_mul]
    exact (div_le_one hpos).2 (by linarith)
  have ht := c20_weighted_forward_nonlinear_flux_limit hκ ρ α hell y u G hu hGm hG
    F hF M hM hF2 (fun z => (C + 1)⁻¹ • V z) (by
      convert hVm.const_smul ((C + 1)⁻¹) using 1) hb
  have ht' := ht.const_mul (C + 1)
  simp only [mul_zero] at ht'
  convert ht' using 1
  funext h
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  have hd (x v : Vec d) : dot x ((C + 1)⁻¹ • v) = (C + 1)⁻¹ * dot x v := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hd, hd]
  have hid (A B P Q R : ℝ) : A * (P * Q) - B * (P * R) = P * (A * Q - B * R) := by ring
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]

/-- Affine time transport of the bounded nonlinear flux limit. -/
theorem c18_weighted_forward_nonlinear_flux_limit_global
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 volume) (hGm : AEStronglyMeasurable G volume)
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 volume)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (V : ℝ × Vec d → Vec d) (C : ℝ) (hC : 0 ≤ C)
    (hVm : Measurable V) (hVb : ∀ z, euclideanNorm (V z) ≤ C) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      |deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) (V z) -
       deriv F (u z) * dot ((α z.2).mulVec (G z)) (V z)|)
      (𝓝[>] 0) (𝓝 0) := by
  let t : ℝ := (a + b) / 2
  let k : ℝ := b - a
  have hk : 0 < k := by dsimp [k]; linarith
  let A : ℝ × Vec d → ℝ × Vec d := fun z => (t + k * z.1, z.2)
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  let I : Set (ℝ × Vec d) := Set.Ioo (-(1/2 : ℝ)) (1/2) ×ˢ sourceBall y r
  let J : Set (ℝ × Vec d) := Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r
  have ha : t + k * (-(1/2)) = a := by dsimp [t, k]; ring
  have hb : t + k * (1/2) = b := by dsimp [t, k]; ring
  have hpre : A ⁻¹' S = I := by
    simpa only [A, S, I, ha, hb] using
      c20_affine_time_preimage_slab t k (-(1/2)) (1/2) hk (sourceBall y r)
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
  have hAc : Measurable A :=
    ((measurable_const_mul k).comp measurable_fst |>.const_add t).prodMk measurable_snd
  have hnorm := c18_weighted_forward_nonlinear_flux_limit_bounded
    hκ hr ρ α hell y (fun z => u (A z)) (fun z => G (A z)) huA hGA hG2A
    F hF M hM hF2 (fun z => V (A z)) C hC
    ((hVm.comp hAc).aestronglyMeasurable) (Filter.Eventually.of_forall fun z => hVb (A z))
  have ht := (hnorm.comp (c20_tendsto_positive_time_div k hk)).const_mul k
  simp only [mul_zero] at ht
  convert ht using 1
  funext h
  have hI := c20_integral_affine_time_pullback_unconditional t k hk S hS
    (fun z => |deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) (V z) -
     deriv F (u z) * dot ((α z.2).mulVec (G z)) (V z)|)
  rw [hpre] at hI
  have heq : (∫ z in I,
      |deriv F ((h / k)⁻¹ * ∫ s in (0 : ℝ)..(h / k), u (A (z.1+s,z.2))) *
        dot ((α (A z).2).mulVec ((h / k)⁻¹ • ∫ s in (0 : ℝ)..(h / k), G (A (z.1+s,z.2)))) (V (A z)) -
       deriv F (u (A z)) * dot ((α (A z).2).mulVec (G (A z))) (V (A z))|) =
      k⁻¹ * ∫ z in S,
      |deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) (V z) -
       deriv F (u z) * dot ((α z.2).mulVec (G z)) (V z)| := by
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

/-- Compactly supported vector tests localize the flux limit to the cylinder. -/
theorem c18_weighted_forward_nonlinear_flux_limit_compact
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
    (V : ℝ × Vec d → Vec d) (C : ℝ) (hC : 0 ≤ C)
    (hVm : Measurable V) (hVb : ∀ z, euclideanNorm (V z) ≤ C)
    (ψ : ℝ × Vec d → ℝ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r)
    (hVzero : ∀ z, z ∉ tsupport ψ → V z = 0) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      |deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) (V z) -
       deriv F (u z) * dot ((α z.2).mulVec (G z)) (V z)|)
      (𝓝[>] 0) (𝓝 0) := by
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  have hS : MeasurableSet S := measurableSet_Ioo.prod (c20_sourceBall_measurable y r)
  obtain ⟨hu0, hGm0, hG0⟩ := c20_memLp_zero_extension S hS u G hu hGm hG
  have ht := c18_weighted_forward_nonlinear_flux_limit_global
    hκ hr hab ρ α hell y (S.indicator u) (S.indicator G) hu0 hGm0 hG0 F hF M hM hF2
    V C hC hVm hVb
  obtain ⟨δ, hδ, heq⟩ := c20_compact_support_zero_extension_fields ψ hψc hψs u G
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhδ
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ tsupport ψ
  · obtain ⟨huavg, hGavg, huz, hGz⟩ := heq h ⟨le_of_lt hh, le_of_lt hhδ⟩ z hz
    rw [huavg, hGavg, huz, hGz]
  · rw [hVzero z hz]
    simp [dot]

/-- The spatial derivative of a smooth compactly supported test is a bounded
measurable vector field supported in the original test support. -/
theorem c18_compact_test_spatial_derivative_bounded {d : ℕ}
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    let V : ℝ × Vec d → Vec d := fun z j => fderiv ℝ ψ z (0, unitVector j)
    Measurable V ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ z, euclideanNorm (V z) ≤ C) ∧
      ∀ z, z ∉ tsupport ψ → V z = 0 := by
  dsimp only
  let V : ℝ × Vec d → Vec d := fun z j => fderiv ℝ ψ z (0, unitVector j)
  have hd : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  have hV : Continuous V := by
    apply continuous_pi
    intro j
    exact hd.clm_apply continuous_const
  have hz : ∀ z, z ∉ tsupport ψ → V z = 0 := by
    intro z hz
    funext j
    simp [V, fderiv_of_notMem_tsupport ℝ hz]
  have hVc : HasCompactSupport V := by
    apply HasCompactSupport.of_support_subset_isCompact hψc
    intro z hz'
    by_contra hz''
    exact hz' (hz z hz'')
  obtain ⟨C, hC⟩ := hV.bounded_above_of_compact_support hVc
  refine ⟨hV.measurable, ⟨((d : ℝ) + 1) * max C 0, by positivity, ?_⟩, hz⟩
  intro z
  calc
    euclideanNorm (V z) ≤ ((d : ℝ) + 1) * ‖V z‖ := euclideanNorm_le_dimension_mul_norm _
    _ ≤ ((d : ℝ) + 1) * max C 0 := by
      gcongr
      exact (hC z).trans (le_max_left _ _)

/-- The density-weighted time derivative of the test yields the scalar limit. -/
theorem c18_weighted_forward_nonlinear_scalar_limit_compact
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * fderiv ℝ ψ z (1,0))
      (𝓝[>] 0) (𝓝 (∫ z in Set.Ioo a b ×ˢ sourceBall y r,
        -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0))) := by
  let χ : ℝ × Vec d → ℝ := fun z => fderiv ℝ ψ z (1,0)
  let w : ℝ × Vec d → ℝ := fun z => -ρ z.2 * χ z
  have hχ : Continuous χ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχc : HasCompactSupport χ := hψc.fderiv_apply ℝ (1,0)
  have hχs : tsupport χ ⊆ Set.Ioo a b ×ˢ sourceBall y r :=
    (tsupport_fderiv_apply_subset ℝ (1,0)).trans hψs
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hχc
  have hρ : ∀ x, |ρ x| ≤ κ⁻¹ := by
    intro x
    rw [abs_of_nonneg (le_trans (le_of_lt hκ) (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  have hw : Measurable w := ((hell.1.comp measurable_snd).neg).mul hχ.measurable
  have hwb : ∀ z, |w z| ≤ κ⁻¹ * max C 0 := by
    intro z
    dsimp only [w]
    rw [abs_mul, abs_neg]
    have hc : |χ z| ≤ max C 0 := by
      simpa only [Real.norm_eq_abs] using (hC z).trans (le_max_left C 0)
    exact mul_le_mul (hρ z.2) hc (abs_nonneg _) (le_of_lt (inv_pos.mpr hκ))
  have ht := c18_scalar_forward_average_weighted_comp_limit_compact hab y u hu F hF M hM hF2
    w χ (κ⁻¹ * max C 0) hw hwb hχc hχs (by intro z hz; simp [w, hz])
  convert ht using 1
  all_goals first
    | (funext h; apply integral_congr_ae; filter_upwards with z; dsimp [w, χ]; ring)
    | (apply integral_congr_ae; filter_upwards with z; dsimp [w, χ]; ring)
    | (congr 1; apply integral_congr_ae; filter_upwards with z; dsimp [w, χ]; ring)

/-- The linear nonlinear flux converges against the spatial test derivative. -/
theorem c18_weighted_forward_nonlinear_flux_derivative_limit_compact
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
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      |deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
          (fun j => fderiv ℝ ψ z (0, unitVector j)) -
       deriv F (u z) * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0, unitVector j))|)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hVm, ⟨C, hC, hVb⟩, hVz⟩ := c18_compact_test_spatial_derivative_bounded ψ hψ hψc
  exact c18_weighted_forward_nonlinear_flux_limit_compact hκ hr hab ρ α hell y u G hu hGm hG
    F hF M hM hF2 _ C hC hVm hVb ψ hψc hψs hVz

/-- Integrable functions whose absolute difference tends to zero in integral
have convergent integrals. -/
theorem c18_tendsto_integral_of_integral_abs_sub {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (l : Filter ι) (f : ι → Ω → ℝ) (g : Ω → ℝ)
    (hg : Integrable g μ) (hf : ∀ᶠ i in l, Integrable (f i) μ)
    (h : Tendsto (fun i => ∫ x, |f i x - g x| ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, f i x ∂μ) l (𝓝 (∫ x, g x ∂μ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' _ _ h
  · exact Filter.Eventually.of_forall fun i => norm_nonneg _
  · filter_upwards [hf] with i hi
    rw [← integral_sub hi hg]
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_integral_le_integral_norm (f i - g)

/-- The compactly tested nonlinear scalar is integrable on the cylinder. -/
theorem c18_nonlinear_scalar_test_integrable
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun z => -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
  haveI : IsFiniteMeasure (volume.restrict (sourceBall y r)) :=
    isFiniteMeasure_restrict.mpr (c18_sourceBall_measure_ne_top y r)
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
    have hh : IsFiniteMeasure ((volume.restrict (Set.Ioo a b)).prod
        (volume.restrict (sourceBall y r))) := inferInstance
    rwa [Measure.prod_restrict] at hh
  let χ : ℝ × Vec d → ℝ := fun z => fderiv ℝ ψ z (1,0)
  let w : ℝ × Vec d → ℝ := fun z => -ρ z.2 * χ z
  have hχ : Continuous χ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support (hψc.fderiv_apply ℝ (1,0))
  have hρ : ∀ x, |ρ x| ≤ κ⁻¹ := by
    intro x
    rw [abs_of_nonneg (le_trans (le_of_lt hκ) (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  have hw : Measurable w := ((hell.1.comp measurable_snd).neg).mul hχ.measurable
  have hwb : ∀ z, |w z| ≤ κ⁻¹ * max C 0 := by
    intro z
    dsimp only [w]
    rw [abs_mul, abs_neg]
    have hc : |χ z| ≤ max C 0 := by
      simpa only [Real.norm_eq_abs] using (hC z).trans (le_max_left C 0)
    exact mul_le_mul (hρ z.2) hc (abs_nonneg _) (le_of_lt (inv_pos.mpr hκ))
  have hi := (c20_nonlinear_comp_integrable u hu F hF M hM hF2).bdd_mul
    hw.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hwb z)
  convert hi using 1 <;> funext z <;> dsimp [w, χ] <;> ring

/-- Lᵖ membership is invariant under a nondegenerate affine change of time. -/
theorem c18_memLp_affine_time_pullback_iff {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (t k : ℝ) (hk : 0 < k)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S) (p : ENNReal)
    (f : ℝ × Vec d → E) :
    MemLp (fun z => f (t + k * z.1, z.2)) p
      (volume.restrict ((fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S)) ↔
    MemLp f p (volume.restrict S) := by
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
  constructor
  · intro hf
    have hm : MemLp f p (ENNReal.ofReal |k⁻¹| • volume.restrict S) := by
      rw [← c20_map_restrict_volume_affine_time_prod t k (ne_of_gt hk) S hS]
      exact (e.memLp_map_measure_iff).2 hf
    have hn : ENNReal.ofReal |k⁻¹| ≠ 0 := by simp [ne_of_gt hk]
    have ht := hm.smul_measure (c := (ENNReal.ofReal |k⁻¹|)⁻¹)
      (ENNReal.inv_ne_top.mpr hn)
    rw [smul_smul, ENNReal.inv_mul_cancel hn ENNReal.ofReal_ne_top, one_smul] at ht
    exact ht
  · exact c20_memLp_affine_time_pullback t k (ne_of_gt hk) S hS p f

/-- A global L² field has L² forward averages on a bounded time cylinder. -/
theorem c18_forward_average_eventually_memLp_global
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r a b : ℝ} (hab : a < b) (y : Vec d)
    (u : ℝ × Vec d → E) (hu : MemLp u 2 volume) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp
      (fun z => h⁻¹ • ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) 2
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
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h / k < 1 / 4 :=
    (c20_tendsto_positive_time_div k hk).eventually
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hs
  have havg := c18_memLp_forward_average (c20_sourceBall_measurable y r)
    (div_pos hh hk) (le_of_lt hs) huA
  apply (c18_memLp_affine_time_pullback_iff t k hk S hS 2 _).mp
  rw [show (fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S = I from hpre]
  convert havg using 1
  funext z
  have hav := c20_forward_average_affine_spacetime u t k (h/k) (ne_of_gt hk) z
  simp only [mul_div_cancel₀ h (ne_of_gt hk)] at hav
  simpa only [A, hav]
  dsimp [I]
  congr 2 <;> norm_num

/-- A bounded vector test turns an elliptic flux of an L² vector field into an L² scalar. -/
theorem c18_elliptic_flux_test_memLp
    {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (μ : Measure (ℝ × Vec d))
    (G V : ℝ × Vec d → Vec d) (hGm : AEStronglyMeasurable G μ)
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 μ)
    (hVm : AEStronglyMeasurable V μ) (C : ℝ)
    (hVb : ∀ᵐ z ∂μ, euclideanNorm (V z) ≤ C) :
    MemLp (fun z => dot ((α z.2).mulVec (G z)) (V z)) 2 μ := by
  have hm : AEStronglyMeasurable (fun z => dot ((α z.2).mulVec (G z)) (V z)) μ := by
    change AEStronglyMeasurable (fun z => ∑ i : Fin d, (∑ j : Fin d,
      α z.2 i j * G z j) * V z i) μ
    have hm' : AEStronglyMeasurable (∑ i : Fin d, fun z => (∑ j : Fin d,
        α z.2 i j * G z j) * V z i) μ := by
      apply Finset.aestronglyMeasurable_sum
      intro i hi
      apply AEStronglyMeasurable.mul _ ((continuous_apply i).comp_aestronglyMeasurable hVm)
      have hjm : AEStronglyMeasurable (∑ j : Fin d, fun z => α z.2 i j * G z j) μ := by
        apply Finset.aestronglyMeasurable_sum
        intro j hj
        apply AEStronglyMeasurable.mul _ ((continuous_apply j).comp_aestronglyMeasurable hGm)
        let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
        let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
        exact ((((continuous_id : Continuous (id : Mat d → Mat d)).matrix_elem i j).measurable.comp
          hell.2.1).comp measurable_snd).aestronglyMeasurable
      convert hjm using 1
      ext z
      simp only [Finset.sum_apply]
    convert hm' using 1
    ext z
    simp only [Finset.sum_apply]
  apply (hG.const_mul (κ⁻¹ * C)).mono' hm
  filter_upwards [hVb] with z hz
  rw [Real.norm_eq_abs]
  have hcomm : dot ((α z.2).mulVec (G z)) (V z) =
      dot (V z) ((α z.2).mulVec (G z)) := by simp only [dot, mul_comm]
  rw [hcomm]
  have hb := c20_elliptic_bilinear_bound hκ ρ α hell z.2 (V z) (G z)
  have hv : 0 ≤ euclideanNorm (V z) := Real.sqrt_nonneg _
  have hg : 0 ≤ euclideanNorm (G z) := Real.sqrt_nonneg _
  have hC : 0 ≤ C := hv.trans hz
  have hk : 0 ≤ κ⁻¹ := le_of_lt (inv_pos.mpr hκ)
  exact hb.trans (by gcongr)

/-- A nonlinear derivative and an elliptic L² flux have an integrable pairing. -/
theorem c18_nonlinear_flux_test_integrable
    {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (μ : Measure (ℝ × Vec d)) [IsFiniteMeasure μ]
    (u : ℝ × Vec d → ℝ) (hu : MemLp u 2 μ)
    (G V : ℝ × Vec d → Vec d) (hGm : AEStronglyMeasurable G μ)
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 μ)
    (hVm : AEStronglyMeasurable V μ) (C : ℝ)
    (hVb : ∀ᵐ z ∂μ, euclideanNorm (V z) ≤ C)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M) :
    Integrable (fun z => deriv F (u z) * dot ((α z.2).mulVec (G z)) (V z)) μ := by
  exact (c20_deriv_comp_memLp u hu F hF M hF2).integrable_mul
    (c18_elliptic_flux_test_memLp hκ ρ α hell μ G V hGm hG hVm C hVb)

/-- Any bounded source cylinder has finite Lebesgue measure. -/
theorem c18_intervalSourceCylinder_isFiniteMeasure {d : ℕ} (a b r : ℝ) (y : Vec d) :
    IsFiniteMeasure (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
  haveI : IsFiniteMeasure (volume.restrict (sourceBall y r)) :=
    isFiniteMeasure_restrict.mpr (c18_sourceBall_measure_ne_top y r)
  have hf : IsFiniteMeasure ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall y r))) := inferInstance
  rwa [Measure.prod_restrict] at hf

/-- Compactly supported bounded weights make the nonlinear forward scalar integrable. -/
theorem c18_nonlinear_scalar_eventually_integrable_compact
    {d : ℕ} {r a b : ℝ} (hab : a < b) (y : Vec d)
    (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (w ψ : ℝ × Vec d → ℝ) (C : ℝ) (hw : Measurable w)
    (hwb : ∀ z, |w z| ≤ C) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r)
    (hwzero : ∀ z, z ∉ tsupport ψ → w z = 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (fun z =>
      w z * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  have hS : MeasurableSet S := measurableSet_Ioo.prod (c20_sourceBall_measurable y r)
  have hu0 : MemLp (S.indicator u) 2 volume := (memLp_indicator_iff_restrict hS).2 hu
  letI := c18_intervalSourceCylinder_isFiniteMeasure a b r y
  have havg := c18_forward_average_eventually_memLp_global (r := r) hab y (S.indicator u) hu0
  obtain ⟨δ, hδ, heq⟩ := c20_compact_support_forward_indicator_integral ψ hψc hψs u
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [havg, self_mem_nhdsWithin, hsmall] with h hav hp hd
  have hint := (c20_nonlinear_comp_integrable _ (by simpa only [smul_eq_mul] using hav)
    F hF M hM hF2).bdd_mul hw.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hwb z))
  apply hint.congr
  filter_upwards with z
  by_cases hz : z ∈ tsupport ψ
  · rw [heq z hz h ⟨le_of_lt hp, le_of_lt hd⟩]
  · simp [hwzero z hz]

/-- Compactly tested nonlinear fluxes of forward averages are integrable. -/
theorem c18_nonlinear_flux_eventually_integrable_compact
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (V : ℝ × Vec d → Vec d) (C : ℝ) (hVm : Measurable V)
    (hVb : ∀ z, euclideanNorm (V z) ≤ C)
    (ψ : ℝ × Vec d → ℝ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r)
    (hVzero : ∀ z, z ∉ tsupport ψ → V z = 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (fun z =>
      deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) (V z))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  have hS : MeasurableSet S := measurableSet_Ioo.prod (c20_sourceBall_measurable y r)
  obtain ⟨hu0, hGm0, hG0⟩ := c20_memLp_zero_extension S hS u G hu hGm hG
  have hvec := c20_vector_memLp_of_euclidean (S.indicator G) hGm0 hG0
  letI := c18_intervalSourceCylinder_isFiniteMeasure a b r y
  have huavg := c18_forward_average_eventually_memLp_global (r := r) hab y (S.indicator u) hu0
  have hGavg := c18_forward_average_eventually_memLp_global (r := r) hab y (S.indicator G) hvec
  obtain ⟨δ, hδ, heq⟩ := c20_compact_support_zero_extension_fields ψ hψc hψs u G
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  have hc : Continuous (fun v : Vec d => euclideanNorm v) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).mul (continuous_apply i))
  filter_upwards [huavg, hGavg, self_mem_nhdsWithin, hsmall] with h hu' hG' hp hd
  have hGnorm : MemLp (fun z => euclideanNorm
      (h⁻¹ • ∫ s in (0 : ℝ)..h, S.indicator G (z.1+s,z.2))) 2 (volume.restrict S) := by
    apply (hG'.norm.const_mul ((d : ℝ) + 1)).mono'
      (hc.comp_aestronglyMeasurable hG'.aestronglyMeasurable)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ euclideanNorm
      (h⁻¹ • ∫ s in (0 : ℝ)..h, S.indicator G (z.1+s,z.2)) from Real.sqrt_nonneg _)]
    exact euclideanNorm_le_dimension_mul_norm _
  have hint := c18_nonlinear_flux_test_integrable hκ ρ α hell (volume.restrict S)
    _ (by simpa only [smul_eq_mul] using hu') _ V hG'.aestronglyMeasurable hGnorm
    hVm.aestronglyMeasurable C (Filter.Eventually.of_forall hVb) F hF M hF2
  apply hint.congr
  filter_upwards with z
  by_cases hz : z ∈ tsupport ψ
  · obtain ⟨hu'', hG'', _, _⟩ := heq h ⟨le_of_lt hp, le_of_lt hd⟩ z hz
    rw [hu'', hG'']
  · rw [hVzero z hz]
    simp [dot]

/-- Integrability allows the scalar and flux limits to be combined under one integral. -/
theorem c18_weighted_forward_nonlinear_scalar_flux_limit_of_integrable
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r)
    (hsi : Integrable (fun z => -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hfi : Integrable (fun z => deriv F (u z) * dot ((α z.2).mulVec (G z))
      (fun j => fderiv ℝ ψ z (0,unitVector j)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (havg : ∀ᶠ h : ℝ in 𝓝[>] 0,
      Integrable (fun z => -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) *
        fderiv ℝ ψ z (1,0)) (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) ∧
      Integrable (fun z => deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
          (fun j => fderiv ℝ ψ z (0,unitVector j)))
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r))) :
    let uh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)
    let Gh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      -(ρ z.2 * F (uh h z)) * fderiv ℝ ψ z (1,0) +
        deriv F (uh h z) * dot ((α z.2).mulVec (Gh h z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)))
      (𝓝[>] 0) (𝓝 (∫ z in Set.Ioo a b ×ˢ sourceBall y r,
        -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
        deriv F (u z) * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)))) := by
  dsimp only
  let S := Set.Ioo a b ×ˢ sourceBall y r
  have hs := c18_weighted_forward_nonlinear_scalar_limit_compact hκ hab ρ α hell y u hu
    F hF M hM hder ψ hψ hψc hψs
  have hf := c18_tendsto_integral_of_integral_abs_sub (volume.restrict S) (𝓝[>] 0)
    (fun h z => deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
        (fun j => fderiv ℝ ψ z (0,unitVector j)))
    (fun z => deriv F (u z) * dot ((α z.2).mulVec (G z))
      (fun j => fderiv ℝ ψ z (0,unitVector j))) hfi (havg.mono fun h hh => hh.2)
    (c18_weighted_forward_nonlinear_flux_derivative_limit_compact hκ hr hab ρ α hell y u G
      hu hGm hG F hF M hM hder ψ hψ hψc hψs)
  have hh := hs.add hf
  rw [← integral_add hsi hfi] at hh
  apply hh.congr'
  filter_upwards [havg] with h hh
  exact (integral_add hh.1 hh.2).symm

/-- Compactly tested scalar and linear flux terms converge together. -/
theorem c18_weighted_forward_nonlinear_scalar_flux_limit_compact
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r) :
    let uh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)
    let Gh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      -(ρ z.2 * F (uh h z)) * fderiv ℝ ψ z (1,0) +
        deriv F (uh h z) * dot ((α z.2).mulVec (Gh h z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) )
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (∫ z in Set.Ioo a b ×ˢ sourceBall y r,
        -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
        deriv F (u z) * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) )) := by
  dsimp only
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  let μ := volume.restrict S
  let χ : ℝ × Vec d → ℝ := fun z => fderiv ℝ ψ z (1,0)
  let w : ℝ × Vec d → ℝ := fun z => -ρ z.2 * χ z
  let V : ℝ × Vec d → Vec d := fun z j => fderiv ℝ ψ z (0,unitVector j)
  letI : IsFiniteMeasure μ := c18_intervalSourceCylinder_isFiniteMeasure a b r y
  have hχ : Continuous χ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχc : HasCompactSupport χ := hψc.fderiv_apply ℝ (1,0)
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hχc
  have hρ : ∀ x, |ρ x| ≤ κ⁻¹ := by
    intro x
    rw [abs_of_nonneg (le_trans (le_of_lt hκ) (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  have hw : Measurable w := ((hell.1.comp measurable_snd).neg).mul hχ.measurable
  have hwb : ∀ z, |w z| ≤ κ⁻¹ * max C 0 := by
    intro z
    dsimp only [w]
    rw [abs_mul, abs_neg]
    have hc : |χ z| ≤ max C 0 := by
      simpa only [Real.norm_eq_abs] using (hC z).trans (le_max_left C 0)
    exact mul_le_mul (hρ z.2) hc (abs_nonneg _) (le_of_lt (inv_pos.mpr hκ))
  have hwzero : ∀ z, z ∉ tsupport ψ → w z = 0 := by
    intro z hz
    simp [w, χ, fderiv_of_notMem_tsupport ℝ hz]
  obtain ⟨hVm, ⟨D, hD, hVb⟩, hVz⟩ := c18_compact_test_spatial_derivative_bounded ψ hψ hψc
  have hs0 : Integrable (fun z => -(ρ z.2 * F (u z)) * χ z) μ := by
    have hi := (c20_nonlinear_comp_integrable u hu F hF M hM hder).bdd_mul
      hw.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hwb z)
    convert hi using 1 <;> funext z <;> dsimp [w, χ] <;> ring
  have hse : ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (fun z =>
      -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * χ z) μ := by
    have hi := c18_nonlinear_scalar_eventually_integrable_compact hab y u hu F hF M hM hder
      w ψ (κ⁻¹ * max C 0) hw hwb hψc hψs hwzero
    filter_upwards [hi] with h hh
    convert hh using 1 <;> funext z <;> dsimp [w, χ] <;> ring
  have hf0 := c18_nonlinear_flux_test_integrable hκ ρ α hell μ u hu G V hGm hG
    hVm.aestronglyMeasurable D (Filter.Eventually.of_forall hVb) F hF M hder
  have hfe := c18_nonlinear_flux_eventually_integrable_compact hκ hab ρ α hell y u G hu hGm hG
    F hF M hder V D hVm hVb ψ hψc hψs hVz
  apply c18_weighted_forward_nonlinear_scalar_flux_limit_of_integrable hκ hr hab ρ α hell y u G hu hGm hG F hF M hM hder ψ hψ hψc hψs
  · exact hs0
  · exact hf0
  · filter_upwards [hse, hfe] with h hsi hfi
    exact ⟨hsi, hfi⟩

end EinsteinFull.Calculus
