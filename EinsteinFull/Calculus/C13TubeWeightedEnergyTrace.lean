import EinsteinFull.Calculus.C5TubeWeightedCaccioppoli
import EinsteinFull.Calculus.C11TubeForwardNonlinearTest
import EinsteinFull.Calculus.C11TubeC2TimeIntegrationByParts
import EinsteinFull.Calculus.C5TubeGMPSpectralTimeTransport

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The two terms in the weighted cutoff energy flux are integrable on the
original caloric cylinder, for any smooth compactly supported cutoff. -/
theorem c13_weighted_cutoff_energy_flux_integrable {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (I : Set ℝ) (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α I U u G) (χ : Vec d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z => χ z.2 ^ 2 * dot ((α z.2).mulVec (G z)) (G z) +
      2 * χ z.2 * u z * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ χ z.2 (unitVector j)))
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  obtain ⟨C, hC, hbound⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
  have hχtop : MemLp (fun z : ℝ × Vec d => χ z.2) ∞ μ := by
    apply memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable C
    exact ae_of_all μ (fun z => hbound _ ⟨z.2, rfl⟩)
  have hDtop (i : Fin d) : MemLp (fun z : ℝ × Vec d =>
      fderiv ℝ χ z.2 (unitVector i)) ∞ μ := by
    have hd : Continuous (fun x : Vec d => fderiv ℝ χ x (unitVector i)) :=
      (hχ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
    obtain ⟨B, hB, hb⟩ :=
      ((hχc.fderiv_apply ℝ (unitVector i)).isCompact_range hd).isBounded.exists_pos_norm_le
    apply memLp_top_of_bound (hd.comp continuous_snd).aestronglyMeasurable B
    exact ae_of_all μ (fun z => hb _ ⟨z.2, rfl⟩)
  have henergy := (c5_weighted_caloric_mass_flux_energy_integrable hκ hell hu).2
  have hsq : MemLp (fun z : ℝ × Vec d => χ z.2 ^ 2) ∞ μ := by
    have hp : MemLp (fun z : ℝ × Vec d => χ z.2 * χ z.2) ∞ μ := hχtop.mul hχtop
    simpa only [pow_two] using hp
  have hfirst : Integrable (fun z => χ z.2 ^ 2 *
      dot ((α z.2).mulVec (G z)) (G z)) μ := by
    exact henergy.mul_of_top_right hsq
  have hflux := c5_weighted_caloric_flux_memLp hκ hell hu
  have hχu : MemLp (fun z : ℝ × Vec d => χ z.2 * u z) 2 μ := hχtop.mul hu.1
  have hterm (i : Fin d) : Integrable (fun z : ℝ × Vec d =>
      (χ z.2 * u z * fderiv ℝ χ z.2 (unitVector i)) *
        ((α z.2).mulVec (G z)) i) μ := by
    have hχuD : MemLp (fun z : ℝ × Vec d =>
        χ z.2 * u z * fderiv ℝ χ z.2 (unitVector i)) 2 μ := hχu.mul (hDtop i)
    exact hχuD.integrable_mul (hflux i)
  have hcross : Integrable (fun z : ℝ × Vec d => χ z.2 * u z *
      dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ χ z.2 (unitVector j))) μ := by
    convert integrable_finsetSum Finset.univ (fun i _ => hterm i) using 1
    funext z
    simp only [dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  convert hfirst.add (hcross.const_mul 2) using 1
  funext z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The spatially integrated cutoff flux is integrable in time. -/
theorem c13_weighted_cutoff_energy_flux_time_integrable {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (I : Set ℝ) (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α I U u G) (χ : Vec d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun t => ∫ x in U, χ x ^ 2 * dot ((α x).mulVec (G (t, x))) (G (t, x)) +
      2 * χ x * u (t, x) * dot ((α x).mulVec (G (t, x)))
        (fun j => fderiv ℝ χ x (unitVector j))) (volume.restrict I) := by
  have h := c13_weighted_cutoff_energy_flux_integrable hκ ρ α hell I U u G hu χ hχ hχc
  have h' : Integrable (fun z : ℝ × Vec d => χ z.2 ^ 2 *
      dot ((α z.2).mulVec (G z)) (G z) + 2 * χ z.2 * u z *
      dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ χ z.2 (unitVector j)))
      ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact h
  exact h'.integral_prod_left

/-- The weighted cutoff mass is integrable on the caloric cylinder. -/
theorem c13_weighted_cutoff_mass_integrable {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (I : Set ℝ) (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α I U u G) (χ : Vec d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z => ρ z.2 * χ z.2 ^ 2 * u z ^ 2)
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  obtain ⟨C, hC, hbound⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
  have hχtop : MemLp (fun z : ℝ × Vec d => χ z.2) ∞ μ := by
    apply memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable C
    exact ae_of_all μ (fun z => hbound _ ⟨z.2, rfl⟩)
  have hsq : MemLp (fun z : ℝ × Vec d => χ z.2 ^ 2) ∞ μ := by
    have hp : MemLp (fun z : ℝ × Vec d => χ z.2 * χ z.2) ∞ μ := hχtop.mul hχtop
    simpa only [pow_two] using hp
  have hm := (c5_weighted_caloric_mass_flux_energy_integrable hκ hell hu).1
  convert hm.mul_of_top_right hsq using 1
  funext z
  simp only [Pi.mul_apply]
  ring

/-- Spatial integration of the weighted cutoff mass is integrable in time. -/
theorem c13_weighted_cutoff_mass_time_integrable {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (I : Set ℝ) (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α I U u G) (χ : Vec d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun t => ∫ x in U, ρ x * χ x ^ 2 * u (t, x) ^ 2)
      (volume.restrict I) := by
  have h := c13_weighted_cutoff_mass_integrable hκ ρ α hell I U u G hu χ hχ hχc
  have h' : Integrable (fun z : ℝ × Vec d => ρ z.2 * χ z.2 ^ 2 * u z ^ 2)
      ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact h
  exact h'.integral_prod_left

/-- The actual cutoff mass and signed flux have integrable spatial slices
almost everywhere, and the cutoff mass is nonnegative on every slice. -/
theorem c13_weighted_cutoff_mass_flux_slices {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (I : Set ℝ) (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α I U u G) (χ : Vec d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    (∀ᵐ t ∂volume.restrict I,
      Integrable (fun x => ρ x * χ x ^ 2 * u (t, x) ^ 2) (volume.restrict U) ∧
      Integrable (fun x => χ x ^ 2 * dot ((α x).mulVec (G (t, x))) (G (t, x)) +
        2 * χ x * u (t, x) * dot ((α x).mulVec (G (t, x)))
          (fun j => fderiv ℝ χ x (unitVector j))) (volume.restrict U)) ∧
    (∀ t, 0 ≤ ∫ x in U, ρ x * χ x ^ 2 * u (t, x) ^ 2) := by
  have hm := c13_weighted_cutoff_mass_integrable hκ ρ α hell I U u G hu χ hχ hχc
  have hf := c13_weighted_cutoff_energy_flux_integrable hκ ρ α hell I U u G hu χ hχ hχc
  have hp : (volume.restrict I).prod (volume.restrict U) =
      volume.restrict (I ×ˢ U) := by rw [Measure.prod_restrict]; rfl
  rw [← hp] at hm hf
  constructor
  · filter_upwards [hm.prod_right_ae, hf.prod_right_ae] with t hmt hft
    exact ⟨hmt, hft⟩
  · intro t
    apply integral_nonneg
    intro x
    exact mul_nonneg (mul_nonneg (hκ.le.trans (hell.2.2 x).1) (sq_nonneg _)) (sq_nonneg _)

/-- The actual cutoff flux has a continuous primitive with the signed
interval increments appearing in the energy balance. -/
theorem c13_weighted_cutoff_flux_continuous_primitive {d : ℕ} {κ a b : ℝ}
    (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) U u G) (χ : Vec d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    ∃ P : ℝ → ℝ, Continuous P ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
        P t - P s = -2 * ∫ r in s..t, ∫ x in U,
          χ x ^ 2 * dot ((α x).mulVec (G (r, x))) (G (r, x)) +
          2 * χ x * u (r, x) * dot ((α x).mulVec (G (r, x)))
            (fun j => fderiv ℝ χ x (unitVector j)) := by
  let f : ℝ → ℝ := fun r => ∫ x in U,
    χ x ^ 2 * dot ((α x).mulVec (G (r, x))) (G (r, x)) +
    2 * χ x * u (r, x) * dot ((α x).mulVec (G (r, x)))
      (fun j => fderiv ℝ χ x (unitVector j))
  let g := (Set.Ioo a b).indicator f
  have hf : IntegrableOn f (Set.Ioo a b) volume :=
    c13_weighted_cutoff_energy_flux_time_integrable hκ ρ α hell (Set.Ioo a b) U u G hu χ hχ hχc
  have hg : Integrable g volume := hf.integrable_indicator measurableSet_Ioo
  refine ⟨fun t => -2 * ∫ r in (0 : ℝ)..t, g r, ?_, ?_⟩
  · exact continuous_const.mul (intervalIntegral.continuous_primitive
      (fun s t => hg.intervalIntegrable) 0)
  · intro s hs t ht
    have heq : (∫ r in s..t, g r) = ∫ r in s..t, f r := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Set.Ioo a b := by
        by_cases hst : s ≤ t
        · rw [Set.uIcc_of_le hst] at hr
          exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
        · rw [Set.uIcc_of_ge (le_of_not_ge hst)] at hr
          exact ⟨lt_of_lt_of_le ht.1 hr.1, lt_of_le_of_lt hr.2 hs.2⟩
      exact Set.indicator_of_mem hr' f
    rw [← heq, ← intervalIntegral.integral_interval_sub_left
      (hg.intervalIntegrable) (hg.intervalIntegrable)]
    ring

/-- The forward-averaged nonlinear weak equation after integration by parts
in time, with the density retained in the time term. -/
theorem c13_weighted_forward_nonlinear_renormalized_identity
    {d : ℕ} {κ r h : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ q, |deriv F q| ≤ M ∧ |deriv (deriv F) q| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r) :
    let U := fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
    let V := fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
    (-(∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      ρ z.2 * F (U z) * fderiv ℝ ψ z (1, 0))) +
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      dot ((α z.2).mulVec (V z))
        (ψ z • (deriv (deriv F) (U z) • V z) +
          deriv F (U z) • (fun j => fderiv ℝ ψ z (0, unitVector j)))) = 0 := by
  have ht := c13_weighted_forward_nonlinear_spacetime_integration_by_parts
    hκ hh hhsmall ρ α hell y u G hu F hF M M hM hM
    (fun q => (hder q).1) (fun q => (hder q).2) ψ hψ hψc hsp
  have hw := c11_weighted_forward_nonlinear_spacetime_test hκ hr hh hhsmall
    y ρ α hell u G hu F hF M hM (fun q => (hder q).2) ψ hψ hψc hsp
  have heq : (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      ρ z.2 * ((u (z.1+h,z.2) - u z) / h) *
        (ψ z * deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)))) =
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      ρ z.2 * (deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        (h⁻¹ * (u (z.1+h,z.2) - u z))) * ψ z) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [div_eq_mul_inv]
    ring
  dsimp only at hw ⊢
  rw [heq] at hw
  linarith

/-- The spacetime time chain holds for C² nonlinearities with bounded second derivative. -/
theorem c13_weighted_forward_C2_spacetime_integration_by_parts
    {d : ℕ} {κ r h : ℝ} (hκ : 0 < κ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (N : ℝ) (hN : 0 ≤ N)
    (hF2 : ∀ q, |deriv (deriv F) q| ≤ N)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      ρ z.2 * F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) *
        fderiv ℝ ψ z (1, 0)) =
    -(∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      ρ z.2 * (deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) *
        (h⁻¹ * (u (z.1+h,z.2) - u z))) * ψ z) := by
  let μ := (volume : Measure ℝ).restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
  let ν := (volume : Measure (Vec d)).restrict (sourceBall y r)
  let A : ℝ × Vec d → ℝ := fun z => ρ z.2 * F (h⁻¹ *
    (∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * fderiv ℝ ψ z (1, 0)
  let B : ℝ × Vec d → ℝ := fun z => ρ z.2 * (deriv F (h⁻¹ *
    (∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) *
      (h⁻¹ * (u (z.1+h,z.2) - u z))) * ψ z
  have hA : Integrable A (μ.prod ν) := by
    rw [Measure.prod_restrict]
    exact c13_weighted_forward_nonlinear_time_term_integrable hκ (le_of_lt hh)
      (by linarith) ρ α hell y u G hu F hF N hN hF2 ψ hψ hψc
  have hB : Integrable B (μ.prod ν) := by
    rw [Measure.prod_restrict]
    exact c13_weighted_forward_nonlinear_difference_integrable hκ hh hhsmall
      ρ α hell y u G hu F hF N hN hF2 ψ hψ hψc
  have hs := c11_weighted_caloric_spacetime_C2_set_integration_by_parts_ae
    (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)) (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)
    (by linarith : (1 / 2 : ℝ) + h < 1) (le_of_lt hh)
    ρ α y u G hu F hF ψ hψ hsp
  have hslice : ∀ᵐ x ∂ν, (∫ t, A (t, x) ∂μ) = -(∫ t, B (t, x) ∂μ) := by
    filter_upwards [hs] with x hx
    simpa only [A, B, μ, c13_spacetime_test_time_slice_deriv ψ (hψ.of_le (by simp))] using hx
  change (∫ z, A z ∂(volume.restrict (_ ×ˢ _))) =
    -(∫ z, B z ∂(volume.restrict (_ ×ˢ _)))
  have hμν : μ.prod ν = (volume : Measure (ℝ × Vec d)).restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r) := by
    rw [Measure.prod_restrict]
    rfl
  rw [← hμν, integral_prod_symm _ hA, integral_prod_symm _ hB, ← integral_neg]
  exact integral_congr_ae hslice

/-- The forward-averaged C² nonlinear weak equation with bounded second derivative. -/
theorem c13_weighted_forward_C2_renormalized_identity
    {d : ℕ} {κ r h : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ q, |deriv (deriv F) q| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r) :
    let U := fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
    let V := fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
    (-(∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      ρ z.2 * F (U z) * fderiv ℝ ψ z (1, 0))) +
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      dot ((α z.2).mulVec (V z))
        (ψ z • (deriv (deriv F) (U z) • V z) +
          deriv F (U z) • (fun j => fderiv ℝ ψ z (0, unitVector j)))) = 0 := by
  have ht := c13_weighted_forward_C2_spacetime_integration_by_parts
    hκ hh hhsmall ρ α hell y u G hu F hF M hM hder ψ hψ hψc hsp
  have hw := c11_weighted_forward_nonlinear_spacetime_test hκ hr hh hhsmall
    y ρ α hell u G hu F hF M hM hder ψ hψ hψc hsp
  have heq : (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      ρ z.2 * ((u (z.1+h,z.2) - u z) / h) *
        (ψ z * deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)))) =
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      ρ z.2 * (deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        (h⁻¹ * (u (z.1+h,z.2) - u z))) * ψ z) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [div_eq_mul_inv]
    ring
  dsimp only at hw ⊢
  rw [heq] at hw
  linarith


/-- Translation of time preserves Lebesgue measure on translated cylinders. -/
theorem c13_time_translation_measurePreserving {d : ℕ} (c a b : ℝ)
    (U : Set (Vec d)) :
    MeasurePreserving (fun z : ℝ × Vec d => (z.1 + c, z.2))
      (volume.restrict (Set.Ioo (a-c) (b-c) ×ˢ U))
      (volume.restrict (Set.Ioo a b ×ˢ U)) := by
  let v : ℝ × Vec d := (c, 0)
  have hp : MeasurePreserving (fun z : ℝ × Vec d => z + v)
      (volume : Measure (ℝ × Vec d)) volume := by
    rw [Measure.volume_eq_prod]
    have he : (fun z : ℝ × Vec d => z + v) = Prod.map (fun t : ℝ => t+c) id := by
      funext z
      rcases z with ⟨t, x⟩
      simp [v]
    rw [he]
    exact (measurePreserving_add_right (volume : Measure ℝ) c).prod
      (MeasurePreserving.id (volume : Measure (Vec d)))
  have h := hp.restrict_preimage_emb (Homeomorph.addRight v).measurableEmbedding
    (Set.Ioo a b ×ˢ U)
  have heq : (fun z : ℝ × Vec d => z + v) ⁻¹' (Set.Ioo a b ×ˢ U) =
      Set.Ioo (a-c) (b-c) ×ˢ U := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioo, Prod.fst_add,
      Prod.snd_add, v, add_zero]
    constructor <;> rintro ⟨⟨h1, h2⟩, hx⟩ <;> exact ⟨⟨by linarith, by linarith⟩, hx⟩
  rw [heq] at h
  have he : (fun z : ℝ × Vec d => z + v) = (fun z => (z.1 + c, z.2)) := by
    funext z
    rcases z with ⟨t, x⟩
    simp [v]
  rwa [he] at h

/-- The weighted caloric predicate is invariant under translation of time. -/
theorem c13_weighted_caloric_time_translation {d : ℕ} (c a b : ℝ)
    (U : Set (Vec d)) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) U u G) :
    IsWeightedCaloric ρ α (Set.Ioo (a-c) (b-c)) U
      (fun z => u (z.1+c, z.2)) (fun z => G (z.1+c, z.2)) := by
  rcases hu with ⟨hu, hg, hn, hw, he⟩
  have hm := c13_time_translation_measurePreserving c a b U
  refine ⟨hu.comp_measurePreserving hm, hg.comp_measurePreserving hm,
    hn.comp_measurePreserving hm, ?_, ?_⟩
  · have ht := (measurePreserving_add_right (volume : Measure ℝ) c).restrict_preimage_emb
      (Homeomorph.addRight c).measurableEmbedding (Set.Ioo a b)
    have hp : (fun t : ℝ => t+c) ⁻¹' Set.Ioo a b = Set.Ioo (a-c) (b-c) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ioo]
      constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
    rw [hp] at ht
    exact ht.quasiMeasurePreserving.ae hw
  · intro ψ hψ hc hs
    let v : ℝ × Vec d := (-c, 0)
    let φ : ℝ × Vec d → ℝ := fun z => ψ (z + v)
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (contDiff_id.add contDiff_const)
    have hφc : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.addRight v)
    have hφs : tsupport φ ⊆ interior (Set.Ioo a b) ×ˢ U := by
      intro z hz
      have h := hs (tsupport_comp_subset_preimage ψ (continuous_id.add continuous_const) hz)
      simp only [interior_Ioo, Set.mem_prod, Set.mem_Ioo] at h ⊢
      have h1 : a-c < z.1-c := by simpa [v] using h.1.1
      have h2 : z.1-c < b-c := by simpa [v] using h.1.2
      exact ⟨⟨by linarith, by linarith⟩, by simpa [v] using h.2⟩
    have hweak := he φ hφ hφc hφs
    let F : ℝ × Vec d → ℝ := fun z =>
      -(ρ z.2 * u z) * fderiv ℝ φ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ φ z (0, unitVector j))
    have hme : MeasurableEmbedding (fun z : ℝ × Vec d => (z.1+c, z.2)) := by
      convert (Homeomorph.addRight (c, (0 : Vec d))).measurableEmbedding using 1
      funext z
      rcases z with ⟨t,x⟩
      simp
    have hi := hm.integral_comp hme F
    have hd (z : ℝ × Vec d) : fderiv ℝ φ (z.1+c, z.2) = fderiv ℝ ψ z := by
      have h := fderiv_comp_add_right (𝕜 := ℝ) (f := ψ) v (x := (z.1+c, z.2))
      simpa [φ, v, Prod.ext_iff] using h
    simpa only [F, hd] using hi.trans hweak


/-- Centering and dilating time puts a weighted caloric field on the unit interval. -/
theorem c13_weighted_caloric_normalize_time {d : ℕ} {a b : ℝ} (hab : a < b)
    (U : Set (Vec d)) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) U u G) :
    let c := (a+b)/2
    let τ := (b-a)/2
    IsWeightedCaloric ρ (fun x => τ • α x) (Set.Ioo (-1) 1) U
      (fun z => u (c + τ * z.1, z.2)) (fun z => G (c + τ * z.1, z.2)) := by
  let c : ℝ := (a+b)/2
  let τ : ℝ := (b-a)/2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hleft : a-c = τ * (-1) := by dsimp [c, τ]; ring
  have hright : b-c = τ * 1 := by dsimp [c, τ]; ring
  have ht := c13_weighted_caloric_time_translation c a b U ρ α u G hu
  rw [hleft, hright] at ht
  have hs := EinsteinFull.c5_time_scale_weighted_caloric hτ ht
  simpa only [c, τ, add_comm] using hs

/-- A test on an arbitrary time slab pulls back to the normalized slab. -/
theorem c13_normalized_time_test {d : ℕ} {a b : ℝ} (hab : a < b)
    {U : Set (Vec d)} (ψ : ℝ × Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ U) :
    let c := (a+b)/2
    let τ := (b-a)/2
    let φ : ℝ × Vec d → ℝ := fun z => ψ (c + τ*z.1, z.2)
    ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Set.Ioo (-1) 1 ×ˢ U ∧
      (∀ z, fderiv ℝ φ z (1, 0) = τ * fderiv ℝ ψ (c + τ*z.1, z.2) (1, 0)) ∧
      (∀ z j, fderiv ℝ φ z (0, unitVector j) =
        fderiv ℝ ψ (c + τ*z.1, z.2) (0, unitVector j)) := by
  let c : ℝ := (a+b)/2
  let τ : ℝ := (b-a)/2
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec d => ψ (c + τ*z.1, z.2)) ∧
    HasCompactSupport (fun z : ℝ × Vec d => ψ (c + τ*z.1, z.2)) ∧
    tsupport (fun z : ℝ × Vec d => ψ (c + τ*z.1, z.2)) ⊆ Set.Ioo (-1) 1 ×ˢ U ∧
    (∀ z, fderiv ℝ (fun z : ℝ × Vec d => ψ (c + τ*z.1, z.2)) z (1, 0) = τ * fderiv ℝ ψ (c + τ*z.1, z.2) (1, 0)) ∧
    (∀ z j, fderiv ℝ (fun z : ℝ × Vec d => ψ (c + τ*z.1, z.2)) z (0, unitVector j) = fderiv ℝ ψ (c + τ*z.1, z.2) (0, unitVector j))
  have hτ : 0 < τ := by dsimp [τ]; linarith
  let v : ℝ × Vec d := (c, 0)
  let θ : ℝ × Vec d → ℝ := fun z => ψ (z + v)
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := hψ.comp (contDiff_id.add contDiff_const)
  have hθc : HasCompactSupport θ := hc.comp_homeomorph (Homeomorph.addRight v)
  have hθs : tsupport θ ⊆ Set.Ioo (a-c) (b-c) ×ˢ U := by
    intro z hz
    have h := hs (tsupport_comp_subset_preimage ψ (continuous_id.add continuous_const) hz)
    change (z + v).1 ∈ Set.Ioo a b ∧ (z + v).2 ∈ U at h
    simp only [Set.mem_prod, Set.mem_Ioo, Prod.fst_add,
      Prod.snd_add, v, add_zero] at h ⊢
    exact ⟨⟨by linarith, by linarith⟩, h.2⟩
  have hl' : a-c = τ * (-1) := by dsimp [c, τ]; ring
  have hr' : b-c = τ * 1 := by dsimp [c, τ]; ring
  have hl : τ⁻¹ * (a-c) = -1 := by rw [hl', ← mul_assoc, inv_mul_cancel₀ hτ.ne']; norm_num
  have hr : τ⁻¹ * (b-c) = 1 := by rw [hr', ← mul_assoc, inv_mul_cancel₀ hτ.ne']; norm_num
  have hp := EinsteinFull.c5_inverseTimeMap_tsupport (inv_pos.mpr hτ) hθs
  rw [hl, hr] at hp
  have he : θ ∘ EinsteinFull.c5_inverseTimeMap τ⁻¹ =
      (fun z : ℝ × Vec d => ψ (c + τ*z.1, z.2)) := by
    funext z
    simp [θ, v, EinsteinFull.c5_inverseTimeMap, add_comm]
  rw [he] at hp
  refine ⟨?_, ?_, hp, ?_, ?_⟩
  · rw [← he]
    exact hθ.comp (EinsteinFull.c5_contDiff_inverseTimeMap τ⁻¹)
  · rw [← he]
    exact EinsteinFull.c5_inverseTimeMap_compactSupport (inv_pos.mpr hτ) hθc
  · intro z
    have hd := EinsteinFull.c5_inverseTimeMap_derivatives τ⁻¹ hθ z
    rw [he] at hd
    have ht := fderiv_comp_add_right (𝕜 := ℝ) (f := ψ) v
      (x := EinsteinFull.c5_inverseTimeMap τ⁻¹ z)
    have hθd : fderiv ℝ θ (EinsteinFull.c5_inverseTimeMap τ⁻¹ z) =
        fderiv ℝ ψ (EinsteinFull.c5_inverseTimeMap τ⁻¹ z + v) := by simpa only [θ] using ht
    rw [hθd] at hd
    simpa only [inv_inv, EinsteinFull.c5_inverseTimeMap, Prod.mk_add_mk, v,
      add_zero, add_comm] using hd.1
  · intro z j
    have hd := EinsteinFull.c5_inverseTimeMap_derivatives τ⁻¹ hθ z
    rw [he] at hd
    have ht := fderiv_comp_add_right (𝕜 := ℝ) (f := ψ) v
      (x := EinsteinFull.c5_inverseTimeMap τ⁻¹ z)
    simpa [θ, v, EinsteinFull.c5_inverseTimeMap, add_comm] using (hd.2 j).trans
      (congrArg (fun L => L (0, unitVector j)) ht)

/-- The affine normalization of an open time slab has the expected Jacobian. -/
theorem c13_normalized_time_integral {d : ℕ} {a b : ℝ} (hab : a < b)
    (U : Set (Vec d)) (f : ℝ × Vec d → ℝ) :
    let c := (a+b)/2
    let τ := (b-a)/2
    τ * (∫ z in Set.Ioo (-1) 1 ×ˢ U, f (c + τ*z.1, z.2)) =
      ∫ z in Set.Ioo a b ×ˢ U, f z := by
  let c : ℝ := (a+b)/2
  let τ : ℝ := (b-a)/2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hl : a-c = τ * (-1) := by dsimp [c, τ]; ring
  have hr : b-c = τ * 1 := by dsimp [c, τ]; ring
  have ht := c13_time_translation_measurePreserving (d := d) c a b U
  have he : MeasurableEmbedding (fun z : ℝ × Vec d => (z.1+c, z.2)) := by
    convert (Homeomorph.addRight (c, (0 : Vec d))).measurableEmbedding using 1
    funext z
    rcases z with ⟨t,x⟩
    simp
  have hi := ht.integral_comp he f
  rw [hl, hr] at hi
  have hs := PDE.Parabolic.Rescale.integral_comp_of_map_eq_smul
    (EinsteinFull.c5_time_scale_embedding (d := d) hτ)
    (EinsteinFull.c5_time_scale_map_cylinder hτ (-1) 1 U)
    (fun z => f (z.1+c, z.2))
  rw [hi] at hs
  simp only [ENNReal.toReal_ofReal (inv_pos.mpr hτ).le, smul_eq_mul] at hs
  change τ * (∫ z in Set.Ioo (-1) 1 ×ˢ U, f (c + τ*z.1, z.2)) = _
  have hs' : (∫ z in Set.Ioo (-1) 1 ×ˢ U, f (c + τ*z.1, z.2)) =
      τ⁻¹ * ∫ z in Set.Ioo a b ×ˢ U, f z := by simpa only [add_comm] using hs
  rw [hs', ← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul]

end EinsteinFull.Calculus
