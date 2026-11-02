import EinsteinFull.Calculus.C13TubeSmallPositivePower
import EinsteinFull.Calculus.C13TubeNativeC2Energy
import EinsteinFull.Calculus.C13TubeSmallPowerCoercivity
import EinsteinFull.Calculus.C13TubeMoserEssentialBound

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The actual caloric small-positive-power extension has a continuous cutoff energy trace. -/
theorem c13_positive_power_continuous_cutoff_energy {d : ℕ}
    {κ R a b ε p : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ (F : ℝ → ℝ) (c : ℝ) (E : ℝ → ℝ),
      (∀ x, ε ≤ x → F x = Real.rpow x p - c) ∧
      (∀ x, ε ≤ x → deriv F x = p * Real.rpow x (p - 1)) ∧
      (∀ x, ε ≤ x → deriv (deriv F) x = p * (p - 1) * Real.rpow x (p - 2)) ∧
      ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * F (u (t,x))) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
        E t - E s = -(∫ r in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * deriv (deriv F) (u (r,x)) *
            dot ((α x).mulVec (G (r,x))) (G (r,x)) +
          2 * χ x * deriv F (u (r,x)) * dot ((α x).mulVec (G (r,x)))
            (fun j => fderiv ℝ χ x (unitVector j))) := by
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hfirst, hsecond⟩ :=
    c13_small_positive_power_normalized_extension ε p hε hp hp1
  obtain ⟨E, hcont, hrep, hbalance⟩ :=
    c13_actual_weighted_C2_continuous_energy hκ hR hab ρ α hell u G hcal
      F hF hF0 M hM (fun x => (hb x).2) χ hχ hχc hχU
  exact ⟨F, c, E, hval, hfirst, hsecond, hcont, hrep, hbalance⟩

/-- The continuous cutoff trace represents the literal positive power mass. -/
theorem c13_positive_power_literal_continuous_energy {d : ℕ}
    {κ R a b ε p : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ (F : ℝ → ℝ) (c : ℝ),
      (∀ x, ε ≤ x → F x = Real.rpow x p - c) ∧
      (∀ x, ε ≤ x → deriv F x = p * Real.rpow x (p - 1)) ∧
      (∀ x, ε ≤ x → deriv (deriv F) x = p * (p - 1) * Real.rpow x (p - 2)) ∧
      ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
        (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
          E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p) ∧
        ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
          E t - E s = -(∫ r in s..t, ∫ x in sourceBall 0 R,
            χ x ^ 2 * deriv (deriv F) (u (r,x)) *
              dot ((α x).mulVec (G (r,x))) (G (r,x)) +
            2 * χ x * deriv F (u (r,x)) * dot ((α x).mulVec (G (r,x)))
              (fun j => fderiv ℝ χ x (unitVector j))) := by
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hfirst, hsecond⟩ :=
    c13_small_positive_power_normalized_extension ε p hε hp hp1
  obtain ⟨E, hEcont, hEae, hEdiff⟩ :=
    c13_actual_weighted_C2_continuous_energy hκ hR hab ρ α hell u G hcal
      F hF hF0 M hM (fun x => (hb x).2) χ hχ hχc hχU
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  haveI : IsFiniteMeasure μ := c20_sourceCylinder_isFiniteMeasure a b R 0
  have hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) < ∞ := by
    simpa [μ] using (measure_lt_top μ Set.univ)
  have hmF := c13_C2_cutoff_mass_integrable hκ ρ α hell _ _ u G hcal hfinite
    F hF M hM (fun x => (hb x).2) χ hχ hχc
  have hm : Integrable (fun z : ℝ × Vec d => ρ z.2 * χ z.2 ^ 2 *
      (Real.rpow (u z) p - c)) μ := by
    apply hmF.congr
    filter_upwards [hu] with z hz
    rw [hval (u z) hz]
  have hk := c16_density_cutoff_integrable (a := a) (b := b) (R := R)
    hκ ρ α hell χ hχ hχc
  dsimp only [μ] at hm
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hm hk hu
  refine ⟨F, c, hval, hfirst, hsecond, fun t => E t + c *
    (∫ x in sourceBall 0 R, ρ x * χ x ^ 2), ?_, ?_, ?_⟩
  · exact hEcont.add continuousOn_const
  · filter_upwards [hEae, hm.prod_right_ae, hk.prod_right_ae,
      Measure.ae_ae_of_ae_prod hu] with t ht hmt hkt hut
    have heq : (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * F (u (t,x))) =
        ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * (Real.rpow (u (t,x)) p - c) := by
      apply integral_congr_ae
      filter_upwards [hut] with x hx
      rw [hval (u (t,x)) hx]
    rw [ht, heq, ← integral_const_mul, ← integral_add hmt (hkt.const_mul c)]
    apply integral_congr_ae
    filter_upwards with x
    ring
  · intro s hs t ht
    have h := hEdiff s hs t ht
    linarith

/-- The literal positive-power trace satisfies the balance on every interior interval. -/
theorem c13_positive_power_literal_energy_identity {d : ℕ}
    {κ R a b ε p : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
        E t - E s = -(∫ r in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * (p * (p - 1) * Real.rpow (u (r,x)) (p - 2)) *
            dot ((α x).mulVec (G (r,x))) (G (r,x)) +
          2 * χ x * (p * Real.rpow (u (r,x)) (p - 1)) *
            dot ((α x).mulVec (G (r,x)))
              (fun j => fderiv ℝ χ x (unitVector j))) := by
  obtain ⟨F, c, hval, hfirst, hsecond, E, hEcont, hEae, hEdiff⟩ :=
    c13_positive_power_literal_continuous_energy hκ hR hab hε hp hp1
      ρ α hell u G hcal hu χ hχ hχc hχU
  have hu' := hu
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu'
  have hslices := Measure.ae_ae_of_ae_prod hu'
  refine ⟨E, hEcont, hEae, ?_⟩
  intro s hs t ht
  have hsub : Set.uIoc s t ⊆ Set.Ioo a b := by
    intro r hr
    have hr' := Set.uIoc_subset_uIcc hr
    rcases le_total s t with hst | hts
    · rw [Set.uIcc_of_le hst] at hr'
      exact ⟨lt_of_lt_of_le hs.1 hr'.1, lt_of_le_of_lt hr'.2 ht.2⟩
    · rw [Set.uIcc_of_ge hts] at hr'
      exact ⟨lt_of_lt_of_le ht.1 hr'.1, lt_of_le_of_lt hr'.2 hs.2⟩
  have heq : (∫ r in s..t, ∫ x in sourceBall 0 R,
      χ x ^ 2 * deriv (deriv F) (u (r,x)) *
        dot ((α x).mulVec (G (r,x))) (G (r,x)) +
      2 * χ x * deriv F (u (r,x)) * dot ((α x).mulVec (G (r,x)))
        (fun j => fderiv ℝ χ x (unitVector j))) =
      ∫ r in s..t, ∫ x in sourceBall 0 R,
      χ x ^ 2 * (p * (p - 1) * Real.rpow (u (r,x)) (p - 2)) *
        dot ((α x).mulVec (G (r,x))) (G (r,x)) +
      2 * χ x * (p * Real.rpow (u (r,x)) (p - 1)) *
        dot ((α x).mulVec (G (r,x)))
          (fun j => fderiv ℝ χ x (unitVector j)) := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hslices] with r hr
    apply integral_congr_ae
    filter_upwards [hr] with x hx
    rw [hfirst (u (r,x)) hx, hsecond (u (r,x)) hx]
  rw [← heq]
  exact hEdiff s hs t ht


/-- The literal positive-power cutoff flux is integrable on the cylinder. -/
theorem c13_positive_power_literal_flux_integrable {d : ℕ}
    {κ R a b ε p : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z : ℝ × Vec d =>
      χ z.2 ^ 2 * (p * (p - 1) * Real.rpow (u z) (p - 2)) *
        dot ((α z.2).mulVec (G z)) (G z) +
      2 * χ z.2 * (p * Real.rpow (u z) (p - 1)) *
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ χ z.2 (unitVector j)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  haveI : IsFiniteMeasure μ := c20_sourceCylinder_isFiniteMeasure a b R 0
  have hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) < ∞ := by
    simpa [μ] using (measure_lt_top μ Set.univ)
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hfirst, hsecond⟩ :=
    c13_small_positive_power_normalized_extension ε p hε hp hp1
  have hf := c13_C2_cutoff_flux_integrable hκ ρ α hell _ _ u G hcal hfinite
    F hF M hM (fun x => (hb x).2) χ hχ hχc
  apply hf.congr
  filter_upwards [hu] with z hz
  rw [hfirst (u z) hz, hsecond (u z) hz]

/-- The spatial integral of the literal flux is integrable in time. -/
theorem c13_positive_power_flux_time_integrable {d : ℕ}
    {κ R a b ε p : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun t => ∫ x in sourceBall 0 R,
      χ x ^ 2 * (p * (p - 1) * Real.rpow (u (t,x)) (p - 2)) *
        dot ((α x).mulVec (G (t,x))) (G (t,x)) +
      2 * χ x * (p * Real.rpow (u (t,x)) (p - 1)) *
        dot ((α x).mulVec (G (t,x))) (fun j => fderiv ℝ χ x (unitVector j)))
      (volume.restrict (Set.Ioo a b)) := by
  have hf := c13_positive_power_literal_flux_integrable hκ hε hp hp1 ρ α hell u G hcal hu χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  exact hf.integral_prod_left


/-- The cutoff positive-power gradient energy is integrable. -/
theorem c13_positive_power_cutoff_gradient_integrable {d : ℕ} {R a b ε p : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z => χ z.2 ^ 2 *
      (Real.rpow (u z) (p - 2) * euclideanSq (G z)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have hg := c13_positive_power_gradient_integrable hε hp hp1 ρ α u G hcal hu
  obtain ⟨C, hC, hbound⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
  have hχtop : MemLp (fun z : ℝ × Vec d => χ z.2) ∞ μ := by
    apply memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable C
    exact ae_of_all μ (fun z => hbound _ ⟨z.2, rfl⟩)
  have hsq : MemLp (fun z : ℝ × Vec d => χ z.2 ^ 2) ∞ μ := by
    have ht : MemLp (fun z : ℝ × Vec d => χ z.2 * χ z.2) ∞ μ := hχtop.mul hχtop
    simpa only [pow_two] using ht
  have hh := hg.mul_of_top_right hsq
  apply hh.congr
  filter_upwards with z
  simp only [Pi.mul_apply]


/-- The absorbed positive-power flux estimate holds on almost every time slice. -/
theorem c13_positive_power_spatial_energy_bound {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      (κ * p * (1-p) / 2) * (∫ x in sourceBall 0 R,
        χ x^2 * (Real.rpow (u (t,x)) (p-2) * euclideanSq (G (t,x)))) ≤
      -(∫ x in sourceBall 0 R,
        χ x^2 * (p*(p-1)*Real.rpow (u (t,x)) (p-2)) *
          dot ((α x).mulVec (G (t,x))) (G (t,x)) +
        2 * χ x * (p*Real.rpow (u (t,x)) (p-1)) *
          dot ((α x).mulVec (G (t,x))) (fun j => fderiv ℝ χ x (unitVector j))) +
      (2*p/(κ^3*(1-p))) * (∫ x in sourceBall 0 R,
        Real.rpow (u (t,x)) p * euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  have hd := c13_positive_power_cutoff_gradient_integrable hε hp hp1 ρ α u G hcal hu χ hχ hχc
  have hf := c13_positive_power_literal_flux_integrable hκ hε hp hp1 ρ α hell u G hcal hu χ hχ hχc
  have he := c13_positive_power_cutoff_error_integrable hε hp hp1 ρ α u G hcal hu χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hd hf he hu
  have hslices := Measure.ae_ae_of_ae_prod hu
  filter_upwards [hd.prod_right_ae, hf.prod_right_ae, he.prod_right_ae, hslices] with t ht hf' he' hu'
  have hm := integral_mono_ae (ht.const_mul (κ * p * (1-p) / 2))
    (hf'.neg.add (he'.const_mul (2*p/(κ^3*(1-p))))) (by
      filter_upwards [hu'] with x hx
      simpa only [Pi.add_apply, Pi.neg_apply, mul_assoc] using
        (c13_positive_power_flux_coercive hκ ρ α hell x (u (t,x)) p
          (lt_of_lt_of_le hε hx) hp hp1 (G (t,x)) (χ x)
          (fun j => fderiv ℝ χ x (unitVector j))))
  let F : Vec d → ℝ := fun x => χ x^2 * (p*(p-1)*Real.rpow (u (t,x)) (p-2)) *
      dot ((α x).mulVec (G (t,x))) (G (t,x)) +
      2 * χ x * (p*Real.rpow (u (t,x)) (p-1)) *
      dot ((α x).mulVec (G (t,x))) (fun j => fderiv ℝ χ x (unitVector j))
  let H : Vec d → ℝ := fun x => Real.rpow (u (t,x)) p *
      euclideanSq (fun j => fderiv ℝ χ x (unitVector j))
  have hFi : Integrable F (volume.restrict (sourceBall 0 R)) := hf'
  have hHi : Integrable H (volume.restrict (sourceBall 0 R)) := he'
  let J : Vec d → ℝ := fun x => (2*p/(κ^3*(1-p))) * H x
  have hJi : Integrable J (volume.restrict (sourceBall 0 R)) :=
    hHi.const_mul (2*p/(κ^3*(1-p)))
  rw [integral_const_mul] at hm
  change (κ * p * (1-p) / 2) * _ ≤ ∫ x in sourceBall 0 R,
    ((-F) + J) x at hm
  simp only [Pi.add_apply] at hm
  rw [integral_add hFi.neg hJi] at hm
  simp only [Pi.neg_apply, integral_neg] at hm
  change _ ≤ -_ + ∫ x in sourceBall 0 R, (2*p/(κ^3*(1-p))) * H x at hm
  rw [integral_const_mul] at hm
  exact hm


/-- The literal mass trace controls the positive-power gradient on interior intervals. -/
theorem c13_positive_power_interval_energy_bound {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, s ≤ t →
        (κ * p * (1-p) / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * (Real.rpow (u (q,x)) (p-2) * euclideanSq (G (q,x)))) ≤
        E t - E s + (2*p/(κ^3*(1-p))) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          Real.rpow (u (q,x)) p * euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  obtain ⟨E, hEc, hEae, hEdiff⟩ :=
    c13_positive_power_literal_energy_identity hκ hR hab hε hp hp1 ρ α hell u G hcal hu χ hχ hχc hχU
  refine ⟨E, hEc, hEae, ?_⟩
  intro s hs t ht hst
  let D : ℝ → ℝ := fun q => ∫ x in sourceBall 0 R,
    χ x ^ 2 * (Real.rpow (u (q,x)) (p-2) * euclideanSq (G (q,x)))
  let Q : ℝ → ℝ := fun q => ∫ x in sourceBall 0 R,
    χ x ^ 2 * (p*(p-1)*Real.rpow (u (q,x)) (p-2)) *
      dot ((α x).mulVec (G (q,x))) (G (q,x)) +
    2 * χ x * (p*Real.rpow (u (q,x)) (p-1)) *
      dot ((α x).mulVec (G (q,x))) (fun j => fderiv ℝ χ x (unitVector j))
  let C : ℝ → ℝ := fun q => ∫ x in sourceBall 0 R,
    Real.rpow (u (q,x)) p * euclideanSq (fun j => fderiv ℝ χ x (unitVector j))
  have hsub : Set.Icc s t ⊆ Set.Ioo a b := by
    intro q hq
    exact ⟨lt_of_lt_of_le hs.1 hq.1, lt_of_le_of_lt hq.2 ht.2⟩
  have hd := c13_positive_power_cutoff_gradient_integrable hε hp hp1 ρ α u G hcal hu χ hχ hχc
  have hc := c13_positive_power_cutoff_error_integrable hε hp hp1 ρ α u G hcal hu χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hd hc
  have hD : IntegrableOn D (Set.Ioo a b) volume := hd.integral_prod_left
  have hC : IntegrableOn C (Set.Ioo a b) volume := hc.integral_prod_left
  have hQ : IntegrableOn Q (Set.Ioo a b) volume :=
    c13_positive_power_flux_time_integrable hκ hε hp hp1 ρ α hell u G hcal hu χ hχ hχc
  have hdi : IntervalIntegrable D volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact hD.mono_set (Set.Ioc_subset_Icc_self.trans hsub)
  have hqi : IntervalIntegrable Q volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact hQ.mono_set (Set.Ioc_subset_Icc_self.trans hsub)
  have hci : IntervalIntegrable C volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact hC.mono_set (Set.Ioc_subset_Icc_self.trans hsub)
  have hbound : ∀ᵐ q ∂volume.restrict (Set.Icc s t),
      (κ * p * (1-p) / 2) * D q ≤ -Q q + (2*p/(κ^3*(1-p))) * C q :=
    (c13_positive_power_spatial_energy_bound hκ hε hp hp1 ρ α hell u G hcal hu χ hχ hχc).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hm := intervalIntegral.integral_mono_ae_restrict hst
    (hdi.const_mul (κ * p * (1-p) / 2))
    (hqi.neg.add (hci.const_mul (2*p/(κ^3*(1-p))))) hbound
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hqi.neg (hci.const_mul (2*p/(κ^3*(1-p))))] at hm
  change _ ≤ (∫ q in s..t, -Q q) +
    (∫ q in s..t, (2*p/(κ^3*(1-p))) * C q) at hm
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hm
  have hdiff := hEdiff s hs t ht
  change E t - E s = -(∫ q in s..t, Q q) at hdiff
  change (κ * p * (1-p) / 2) * (∫ q in s..t, D q) ≤
    E t - E s + (2*p/(κ^3*(1-p))) * (∫ q in s..t, C q)
  linarith


/-- The interval gradient retains its coefficient in the cutoff estimate. -/
theorem c13_positive_power_interval_gradient_control {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L ^ 2)
    (E : ℝ → ℝ) (s t : ℝ) (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b)
    (hst : s < t)
    (hE : (κ * p * (1-p) / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * (Real.rpow (u (q,x)) (p-2) * euclideanSq (G (q,x)))) ≤
        E t - E s + (2*p/(κ^3*(1-p))) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          Real.rpow (u (q,x)) p * euclideanSq (fun j => fderiv ℝ χ x (unitVector j)))) :
    (κ * p * (1-p) / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
      χ x ^ 2 * (Real.rpow (u (q,x)) (p-2) * euclideanSq (G (q,x)))) ≤
    E t - E s + ((2*p/(κ^3*(1-p))) * (L^2 * κ⁻¹)) *
      (∫ z in Set.Ioo s t ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p) := by
  have hU : MeasurableSet (sourceBall (0 : Vec d) R) := by
    rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) hR]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hsub : Set.Ioo s t ⊆ Set.Ioo a b := by
    intro q hq
    exact ⟨lt_trans hs.1 hq.1, lt_trans hq.2 ht.2⟩
  have hcal' := c5_weighted_caloric_time_mono measurableSet_Ioo hU hsub hcal
  have hu' := ae_restrict_of_ae_restrict_of_subset
    (Set.prod_mono hsub (Set.Subset.rfl)) hu
  have hb := c13_positive_power_cutoff_error_le_mass hκ hε hp hp1 ρ α hell u G hcal' hu' χ hχ hχc L hL
  have hi := c13_positive_power_cutoff_error_integrable hε hp hp1 ρ α u G hcal' hu' χ hχ hχc
  have hprod : (volume.restrict (Set.Ioo s t)).prod (volume.restrict (sourceBall (0 : Vec d) R)) =
      (volume : Measure (ℝ × Vec d)).restrict (Set.Ioo s t ×ˢ sourceBall 0 R) := by
    rw [Measure.prod_restrict]
    rfl
  rw [← hprod] at hi hb
  rw [integral_prod _ hi, hprod] at hb
  simp only [intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo] at hE ⊢
  have hp1' : 0 < 1-p := by linarith
  have hA : 0 ≤ 2*p/(κ^3*(1-p)) := by positivity
  have := mul_le_mul_of_nonneg_left hb hA
  nlinarith



/-- Uniform positive-power gradient energy for an actual weighted caloric field. -/
theorem c13_native_positive_small_power_gradient_energy
    (d : ℕ) (_hd : 2 ≤ d) (κ p : ℝ) (hκ : 0 < κ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ ε : ℝ, 0 < ε →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
    Integrable (fun z => (u z) ^ (p - 2) * euclideanSq (G z))
      (volume.restrict (Set.Ioo (-(1/4 : ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ∧
    (∫ z in Set.Ioo (-(1/4 : ℝ)) (1/4) ×ˢ sourceBall 0 (1/2),
      (u z) ^ (p - 2) * euclideanSq (G z)) ≤
      C * (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1, ρ z.2 * (u z) ^ p) := by
  let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : PDE.Vec d) (1/2) 1
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ :=
    PDE.canonicalBallCutoff_smooth _ (by norm_num) (by norm_num)
  have hχc : HasCompactSupport χ := PDE.canonicalBallCutoff_hasCompactSupport (by norm_num) (by norm_num)
  have hχU : tsupport χ ⊆ sourceBall 0 1 := by
    rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1)]
    exact PDE.canonicalBallCutoff_tsupport_subset_outer (by norm_num) (by norm_num)
  have hχ0 : ∀ x, 0 ≤ χ x := PDE.canonicalBallCutoff_nonneg _ _ _
  have hχ1 : ∀ x, χ x ≤ 1 := PDE.canonicalBallCutoff_le_one _ _ _
  have hone : ∀ x ∈ sourceBall 0 (1/2), χ x = 1 := by
    intro x hx
    apply PDE.canonicalBallCutoff_eq_one_on_inner (by norm_num) (by norm_num)
    rwa [EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1/2)]
  have hgrad : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ (64 : ℝ)^2 := by
    intro x
    have h := PDE.canonicalBallCutoff_gradient_bound (x₀ := (0 : PDE.Vec d))
      (r := (1/2 : ℝ)) (R := 1) (by norm_num) (by norm_num) x
    have hs := pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg _) h 2
    rw [PDE.vecEuclideanNorm_sq] at hs
    convert hs using 1 <;> norm_num [χ, PDE.vecNormSq_eq_sum_sq, euclideanSq, dot, pow_two,
      PDE.classicalGradient_apply, coordinateDerivative, PDE.basisVec, unitVector]
  let A : ℝ := (2*p/(κ^3*(1-p))) * ((64 : ℝ)^2 * κ⁻¹)
  let B : ℝ := κ * p * (1-p) / 2
  have hp1' : 0 < 1-p := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨(4+A)/B + 1, by positivity, ?_⟩
  intro ρ α hell ε hε u G hcal hu
  let M : ℝ := ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
    ρ z.2 * Real.rpow (u z) p
  have hM : 0 ≤ M := by
    apply integral_nonneg_of_ae
    filter_upwards [hu] with z hz
    exact mul_nonneg (hκ.le.trans (hell.2.2 z.2).1)
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
  obtain ⟨E, hEcont, hErep, hEbound⟩ := c13_positive_power_interval_energy_bound hκ
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 1) hε hp hp1
    ρ α hell u G hcal hu χ hχ hχc hχU
  obtain ⟨hEint, hEavg⟩ := c13_positive_power_future_average_le_mass hκ hε hp hp1
    ρ α hell u G hcal hu χ hχ hχc hχ0 hχ1 E hErep
  obtain ⟨t, ht, _, htE⟩ := c13_exists_future_energy_le_average E (fun _ => True)
    hEint (ae_of_all _ fun _ => trivial)
  obtain ⟨s, hs, hsE⟩ := c13_positive_power_exists_early_nonnegative hκ hε ρ α hell u hu χ E hErep
  have hsI : s ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have htI : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hst : s < t := by linarith [hs.2, ht.1]
  have hb := c13_positive_power_interval_gradient_control hκ (by norm_num : (0 : ℝ) < 1) hε hp hp1
    ρ α hell u G hcal hu χ hχ hχc 64 hgrad E s t hsI htI hst (hEbound s hsI t htI hst.le)
  have hm := c13_positive_power_mass_subinterval_le hκ hε hp hp1 ρ α hell u G hcal hu
    (Set.Ioo s t) (by intro q hq; exact ⟨lt_trans hsI.1 hq.1, lt_trans hq.2 htI.2⟩)
  have hm' := mul_le_mul_of_nonneg_left hm hA
  let Q : ℝ × Vec d → ℝ := fun z =>
    χ z.2 ^ 2 * (Real.rpow (u z) (p-2) * euclideanSq (G z))
  let small : Set (ℝ × Vec d) := Set.Ioo (-(1/4 : ℝ)) (1/4) ×ˢ sourceBall 0 (1/2)
  let large : Set (ℝ × Vec d) := Set.Ioo s t ×ˢ sourceBall 0 1
  have hsub : small ⊆ large := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    refine ⟨⟨by linarith [hs.2, hq.1], by linarith [hq.2, ht.1]⟩, ?_⟩
    change euclideanNorm (x - 0) < 1/2 at hx
    change euclideanNorm (x - 0) < 1
    linarith
  have hlarge : large ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1 := by
    intro z hz
    exact ⟨⟨lt_trans hsI.1 hz.1.1, lt_trans hz.1.2 htI.2⟩, hz.2⟩
  have hsmall : MeasurableSet small := by
    apply measurableSet_Ioo.prod
    rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1/2)]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hi : IntegrableOn Q (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1) :=
    c13_positive_power_cutoff_gradient_integrable hε hp hp1 ρ α u G hcal hu χ hχ hχc
  have hi' : IntegrableOn Q large := hi.mono_set hlarge
  have hraw : IntegrableOn (fun z => Real.rpow (u z) (p-2) * euclideanSq (G z))
      (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1) :=
    c13_positive_power_gradient_integrable hε hp hp1 ρ α u G hcal hu
  refine ⟨hraw.mono_set (hsub.trans hlarge), ?_⟩
  have hprod : (volume.restrict (Set.Ioo s t)).prod (volume.restrict (sourceBall (0 : Vec d) 1)) =
      (volume : Measure (ℝ × Vec d)).restrict large := by
    rw [Measure.prod_restrict]
    rfl
  have hQ : (∫ z in small, Real.rpow (u z) (p-2) * euclideanSq (G z)) ≤
      ∫ q in s..t, ∫ x in sourceBall 0 1,
        χ x ^ 2 * (Real.rpow (u (q,x)) (p-2) * euclideanSq (G (q,x))) := by
    calc
      _ = ∫ z in small, Q z := by
        apply setIntegral_congr_fun hsmall
        intro z hz
        dsimp [Q]
        rw [hone z.2 hz.2]
        ring
      _ ≤ ∫ z in large, Q z := integral_mono_measure (Measure.restrict_mono hsub le_rfl)
        (by
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hlarge hu] with z hz
          exact mul_nonneg (sq_nonneg _) (mul_nonneg
            (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _) (PDE.vecNormSq_nonneg _))) hi'
      _ = _ := by
        rw [intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo, ← hprod]
        exact integral_prod _ (by rw [hprod]; exact hi')
  have hQB := mul_le_mul_of_nonneg_left hQ hB.le
  have hbound : B * (∫ z in small, Real.rpow (u z) (p-2) * euclideanSq (G z)) ≤ (4+A)*M := by
    dsimp [A, B, M] at *
    nlinarith
  have hdiv : (∫ z in small, Real.rpow (u z) (p-2) * euclideanSq (G z)) ≤ ((4+A)*M)/B :=
    (le_div_iff₀ hB).2 (by nlinarith [hbound])
  have hr : ((4+A)*M)/B = ((4+A)/B)*M := by ring
  rw [hr] at hdiv
  change (∫ z in small, Real.rpow (u z) (p-2) * euclideanSq (G z)) ≤ ((4+A)/B + 1)*M
  nlinarith

#lint
end EinsteinFull.Calculus
