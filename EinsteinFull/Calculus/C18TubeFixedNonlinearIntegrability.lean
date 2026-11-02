import EinsteinFull.Calculus.C18TubeNonlinearCompactTimeLimits

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- The three terms in the compactly tested nonlinear equation are integrable. -/
theorem c18_tested_nonlinear_pairing_integrable
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (_hr : 0 < r) (_hab : a < b)
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
    (hψc : HasCompactSupport ψ) (_hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r) :
    Integrable (fun z : ℝ × Vec d =>
      -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z)
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)
  let : IsFiniteMeasure μ := c18_intervalSourceCylinder_isFiniteMeasure a b r y
  obtain ⟨hVm, ⟨C, _, hVb⟩, _⟩ := c18_compact_test_spatial_derivative_bounded ψ hψ hψc
  have hs := c18_nonlinear_scalar_test_integrable hκ ρ α hell y u hu F hF M hM hder ψ hψ hψc
  have hf := c18_nonlinear_flux_test_integrable hκ ρ α hell μ u hu G
    (fun z j => fderiv ℝ ψ z (0, unitVector j)) hGm hG hVm.aestronglyMeasurable C
    (Filter.Eventually.of_forall hVb) F hF M hder
  obtain ⟨D, hD⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have he := c20_nonlinear_gradient_energy_integrable hκ ρ α hell μ u hu.aestronglyMeasurable
    G hGm hG F hF M hder ψ hψ.continuous.aestronglyMeasurable D
    (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hD z)
  exact (hs.add hf).add he


/-- The nonlinear pairing stays integrable after subtracting the value at zero. -/
theorem c18_normalized_nonlinear_pairing_integrable
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
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r) :
    Integrable (fun z : ℝ × Vec d =>
      -(ρ z.2 * (F (u z) - F 0)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z)
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)
  let D : ℝ × Vec d → ℝ := fun z => fderiv ℝ ψ z (1, 0)
  have hD : Continuous D := ((hψ.of_le (by simp)).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDi : Integrable D volume := hD.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (1, 0))
  have hρbound (x : Vec d) : ‖ρ x‖ ≤ κ⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hκ.le (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  have hi : Integrable (fun z : ℝ × Vec d => (ρ z.2 * F 0) * D z) μ := by
    have h := hDi.mul_bdd (c := κ⁻¹) (hell.1.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hρbound z.2)
    have h' : Integrable (fun z : ℝ × Vec d => F 0 * (D z * ρ z.2)) μ :=
      (h.const_mul (F 0)).integrableOn
    convert h' using 1 <;> ext z <;> simp [D, μ] <;> ring
  have hbase := c18_tested_nonlinear_pairing_integrable hκ hr hab ρ α hell y u G hu hGm hG F hF M hM hder ψ hψ hc hs
  convert hbase.add hi using 1 <;> ext z <;> simp only [D, Pi.add_apply] <;> ring


/-- A time-independent density annihilates a compactly supported time derivative. -/
theorem c18_density_time_test_integral_zero {d : ℕ} {κ r a b : ℝ}
    (hκ : 0 < κ) (hab : a < b) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r) :
    ∫ z in Set.Ioo a b ×ˢ sourceBall y r, ρ z.2 * fderiv ℝ ψ z (1, 0) = 0 := by
  let D : ℝ × Vec d → ℝ := fun z => fderiv ℝ ψ z (1, 0)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hD : Continuous D := (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDi : Integrable D volume := hD.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (1, 0))
  have hρbound (x : Vec d) : ‖ρ x‖ ≤ κ⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hκ.le (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  have hmul : Integrable (fun z : ℝ × Vec d => ρ z.2 * D z) volume := by
    have h := hDi.mul_bdd (c := κ⁻¹) (hell.1.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hρbound z.2)
    simpa only [Function.comp_apply, mul_comm] using h
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · change ∫ z, ρ z.2 * D z = 0
    rw [Measure.volume_eq_prod] at hmul ⊢
    rw [integral_prod_symm _ hmul]
    have hzero (x : Vec d) : (∫ t : ℝ, ρ x * D (t, x)) = 0 := by
      rw [integral_const_mul]
      have he (t : ℝ) : deriv (fun s : ℝ => ψ (s, x)) t = D (t, x) := by
        have hp : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) t := by
          simpa using (((hasDerivAt_id t).hasFDerivAt.prodMk
            (hasDerivAt_const t x).hasFDerivAt).hasDerivAt)
        exact (((hψ1.differentiable (by norm_num)) (t, x)).hasFDerivAt.comp_hasDerivAt t hp).deriv
      have hsm : ContDiff ℝ 1 (fun t : ℝ => ψ (t, x)) :=
        hψ1.comp (contDiff_id.prodMk contDiff_const)
      have houtside (t : ℝ) (ht : t ∉ Set.Ioo a b) : (t, x) ∉ tsupport ψ := by
        intro hz
        exact ht (hs hz).1
      have heq : (∫ t : ℝ, D (t, x)) = ∫ t in a..b, D (t, x) := by
        rw [intervalIntegral.integral_of_le hab.le, setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro t ht
        have ht' : t ∉ Set.Ioo a b := fun ht' => ht ⟨ht'.1, ht'.2.le⟩
        simp only [D, fderiv_of_notMem_tsupport (𝕜 := ℝ) (houtside t ht'),
          ContinuousLinearMap.zero_apply]
      rw [heq]
      have hderiv : (fun t => deriv (fun s : ℝ => ψ (s, x)) t) = (fun t => D (t, x)) := funext he
      have hz := intervalIntegral.integral_deriv_eq_sub' (a := a) (b := b) (fun t => ψ (t, x)) hderiv
        (fun t _ => (hsm.differentiable (by norm_num)).differentiableAt)
        ((hD.comp (continuous_id.prodMk continuous_const)).continuousOn)
      have ha : ψ (a, x) = 0 := image_eq_zero_of_notMem_tsupport (houtside a (by simp))
      have hb : ψ (b, x) = 0 := image_eq_zero_of_notMem_tsupport (houtside b (by simp))
      rw [hz, ha, hb, sub_zero, mul_zero]
    simp only [hzero, integral_zero]
  · intro z hz
    have hzs : z ∉ tsupport ψ := fun hz' => hz (hs hz')
    simp only [fderiv_of_notMem_tsupport (𝕜 := ℝ) hzs, ContinuousLinearMap.zero_apply, mul_zero]


/-- Subtracting the value at zero leaves the full tested pairing unchanged. -/
theorem c18_nonlinear_pairing_sub_value_zero
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
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      -(ρ z.2 * (F (u z) - F 0)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) =
    ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)
  let D : ℝ × Vec d → ℝ := fun z => fderiv ℝ ψ z (1, 0)
  have hD : Continuous D := ((hψ.of_le (by simp)).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDi : Integrable D volume := hD.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (1, 0))
  have hρbound (x : Vec d) : ‖ρ x‖ ≤ κ⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hκ.le (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  have hi : Integrable (fun z : ℝ × Vec d => F 0 * (ρ z.2 * D z)) μ := by
    have h := hDi.mul_bdd (c := κ⁻¹) (hell.1.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hρbound z.2)
    have h' : Integrable (fun z : ℝ × Vec d => F 0 * (D z * ρ z.2)) μ :=
      (h.const_mul (F 0)).integrableOn
    simpa only [mul_comm (ρ _)] using h'
  have hz : (∫ z, F 0 * (ρ z.2 * D z) ∂μ) = 0 := by
    rw [integral_const_mul]
    change F 0 * (∫ z in Set.Ioo a b ×ˢ sourceBall y r, ρ z.2 * fderiv ℝ ψ z (1,0)) = 0
    rw [c18_density_time_test_integral_zero hκ hab ρ α hell y ψ hψ hc hs, mul_zero]
  have hbase := c18_tested_nonlinear_pairing_integrable hκ hr hab ρ α hell y u G hu hGm hG F hF M hM hder ψ hψ hc hs
  have heq : (fun z : ℝ × Vec d =>
      -(ρ z.2 * (F (u z) - F 0)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) =
    (fun z => (-(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) + F 0 * (ρ z.2 * D z)) := by
    funext z
    dsimp only [D]
    ring
  rw [heq, integral_add hbase hi, hz, add_zero]

end EinsteinFull.Calculus
