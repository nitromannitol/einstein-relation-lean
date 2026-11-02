import EinsteinFull.Calculus.C13TubeGeneralChainAssembly
import EinsteinFull.Calculus.C13TubeNativeC2Energy
import EinsteinFull.Calculus.C16TubeWeightedLogEnergy
import EinsteinFull.Calculus.C20TubeNegativePowerExtension
import EinsteinFull.Calculus.C20TubeNegativePowerCoercivity

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The actual caloric renormalization with a negative-power extension, with its
normalizing constant retained in the time term. -/
theorem c16_negative_power_normalized_renormalization {d : ℕ}
    {κ R a b ε p : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (F : ℝ → ℝ) (c M : ℝ) (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0)
    (hM : 0 ≤ M) (hder : ∀ x, |deriv (deriv F) x| ≤ M)
    (hval : ∀ x, ε ≤ x → F x = Real.rpow x (-p) - c)
    (hfirst : ∀ x, ε ≤ x → deriv F x = -p * Real.rpow x (-p-1))
    (hsecond : ∀ x, ε ≤ x → deriv (deriv F) x = p*(p+1)*Real.rpow x (-p-2))
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * (Real.rpow (u z) (-p) - c)) * fderiv ℝ ψ z (1,0) +
      (-p * Real.rpow (u z) (-p-1)) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      (p*(p+1)*Real.rpow (u z) (-p-2)) *
        dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0 := by
  have h := c13_actual_weighted_caloric_renormalization hκ hR hab ρ α hell u G hcal
    F hF hF0 M hM hder ψ hψ hψc hψs
  apply Eq.trans _ h
  apply integral_congr_ae
  filter_upwards [hu] with z hz
  symm
  rw [hval (u z) hz, hfirst (u z) hz, hsecond (u z) hz]

/-- The normalized negative-power identity with separate time and spatial cutoffs. -/
theorem c16_negative_power_separated_balance {d : ℕ}
    {κ R a b ε p : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (F : ℝ → ℝ) (c M : ℝ) (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0)
    (hM : 0 ≤ M) (hder : ∀ x, |deriv (deriv F) x| ≤ M)
    (hval : ∀ x, ε ≤ x → F x = Real.rpow x (-p) - c)
    (hfirst : ∀ x, ε ≤ x → deriv F x = -p * Real.rpow x (-p-1))
    (hsecond : ∀ x, ε ≤ x → deriv (deriv F) x = p*(p+1)*Real.rpow x (-p-2))
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηI : tsupport η ⊆ Set.Ioo a b) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * (Real.rpow (u z) (-p) - c)) * (deriv η z.1 * χ z.2 ^ 2) +
      (-p * Real.rpow (u z) (-p-1)) * dot ((α z.2).mulVec (G z))
        (fun j => η z.1 * (2 * χ z.2 * fderiv ℝ χ z.2 (unitVector j))) +
      (p*(p+1)*Real.rpow (u z) (-p-2)) *
        dot ((α z.2).mulVec (G z)) (G z) * (η z.1 * χ z.2 ^ 2)) = 0 := by
  let ψ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
  have hψ := c5_separated_square_cutoff η hη hηc hηI χ hχ hχc hχU
  have h := c16_negative_power_normalized_renormalization hκ hR hab ρ α hell u G hcal hu
    F c M hF hF0 hM hder hval hfirst hsecond ψ hψ.1 hψ.2.1 hψ.2.2
  apply Eq.trans _ h
  apply integral_congr_ae
  filter_upwards with z
  dsimp only [ψ]
  rw [c5_separated_square_cutoff_time_fderiv η (hη.differentiable (by norm_cast))
    χ (hχ.differentiable (by norm_cast)) z]
  simp_rw [c5_separated_square_cutoff_fderiv η (hη.differentiable (by norm_cast))
    χ (hχ.differentiable (by norm_cast)) z]

/-- The normalized negative-power mass and cutoff flux are integrable. -/
@[nolint unusedArguments]
theorem c16_negative_power_cutoff_integrable {d : ℕ}
    {κ R a b ε p : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (F : ℝ → ℝ) (c M : ℝ) (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0)
    (hM : 0 ≤ M) (hder : ∀ x, |deriv (deriv F) x| ≤ M)
    (hval : ∀ x, ε ≤ x → F x = Real.rpow x (-p) - c)
    (hfirst : ∀ x, ε ≤ x → deriv F x = -p * Real.rpow x (-p-1))
    (hsecond : ∀ x, ε ≤ x → deriv (deriv F) x = p*(p+1)*Real.rpow x (-p-2))
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z : ℝ × Vec d => ρ z.2 * χ z.2 ^ 2 * (Real.rpow (u z) (-p) - c))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) ∧
    Integrable (fun z : ℝ × Vec d => χ z.2 ^ 2 * (p*(p+1)*Real.rpow (u z) (-p-2)) *
        dot ((α z.2).mulVec (G z)) (G z) +
      2 * χ z.2 * (-p * Real.rpow (u z) (-p-1)) *
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ χ z.2 (unitVector j)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have : IsFiniteMeasure μ := c20_sourceCylinder_isFiniteMeasure a b R 0
  have hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) < ∞ := by
    simpa [μ] using (measure_lt_top μ Set.univ)
  have hm := c13_C2_cutoff_mass_integrable hκ ρ α hell _ _ u G hcal hfinite F hF M hM hder χ hχ hχc
  have hf := c13_C2_cutoff_flux_integrable hκ ρ α hell _ _ u G hcal hfinite F hF M hM hder χ hχ hχc
  constructor
  · apply hm.congr
    filter_upwards [hu] with z hz
    rw [hval (u z) hz]
  · apply hf.congr
    filter_upwards [hu] with z hz
    rw [hfirst (u z) hz, hsecond (u z) hz]

/-- The literal negative-power cutoff mass is integrable. -/
theorem c16_negative_power_literal_mass_integrable {d : ℕ}
    {κ R a b ε p : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z : ℝ × Vec d => ρ z.2 * χ z.2 ^ 2 * Real.rpow (u z) (-p))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hfirst, hsecond⟩ :=
    c20_negative_power_normalized_extension ε p hε hp
  have hm := (c16_negative_power_cutoff_integrable hκ ρ α hell u G hcal hu F c M
    hF hF0 hM (fun x => (hb x).2) hval hfirst hsecond χ hχ hχc).1
  have hk := c16_density_cutoff_integrable (a := a) (b := b) (R := R)
    hκ ρ α hell χ hχ hχc
  convert hm.add (hk.const_mul c) using 1
  ext z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The literal cutoff mass has a continuous representative, obtained by
restoring the constant removed in the smooth negative-power extension. -/
theorem c16_negative_power_literal_continuous_energy {d : ℕ}
    {κ R a b ε p : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ F : ℝ → ℝ, ∃ c : ℝ,
      (∀ x, ε ≤ x → F x = Real.rpow x (-p) - c) ∧
      (∀ x, ε ≤ x → deriv F x = -p * Real.rpow x (-p-1)) ∧
      (∀ x, ε ≤ x → deriv (deriv F) x = p*(p+1)*Real.rpow x (-p-2)) ∧
      ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
        (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
          E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) (-p)) ∧
        ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
          E t - E s = -(∫ r in s..t, ∫ x in sourceBall 0 R,
            χ x ^ 2 * deriv (deriv F) (u (r,x)) *
              dot ((α x).mulVec (G (r,x))) (G (r,x)) +
            2 * χ x * deriv F (u (r,x)) * dot ((α x).mulVec (G (r,x)))
              (fun j => fderiv ℝ χ x (unitVector j))) := by
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hfirst, hsecond⟩ :=
    c20_negative_power_normalized_extension ε p hε hp
  obtain ⟨E, hEcont, hEae, hEdiff⟩ :=
    c13_actual_weighted_C2_continuous_energy hκ hR hab ρ α hell u G hcal
      F hF hF0 M hM (fun x => (hb x).2) χ hχ hχc hχU
  have hm := (c16_negative_power_cutoff_integrable hκ ρ α hell u G hcal hu F c M
    hF hF0 hM (fun x => (hb x).2) hval hfirst hsecond χ hχ hχc).1
  have hk := c16_density_cutoff_integrable (a := a) (b := b) (R := R)
    hκ ρ α hell χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hm hk hu
  refine ⟨F, c, hval, hfirst, hsecond, fun t => E t + c *
    (∫ x in sourceBall 0 R, ρ x * χ x ^ 2), ?_, ?_, ?_⟩
  · exact hEcont.add continuousOn_const
  · filter_upwards [hEae, hm.prod_right_ae, hk.prod_right_ae,
      Measure.ae_ae_of_ae_prod hu] with t ht hmt hkt hut
    have heq : (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * F (u (t,x))) =
        ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * (Real.rpow (u (t,x)) (-p) - c) := by
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

/-- The continuous literal mass satisfies the energy identity with the actual
negative-power derivatives on every interior time interval. -/
theorem c16_negative_power_literal_energy_identity {d : ℕ}
    {κ R a b ε p : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) (-p)) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
        E t - E s = -(∫ r in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * (p*(p+1)*Real.rpow (u (r,x)) (-p-2)) *
            dot ((α x).mulVec (G (r,x))) (G (r,x)) +
          2 * χ x * (-p * Real.rpow (u (r,x)) (-p-1)) *
            dot ((α x).mulVec (G (r,x)))
              (fun j => fderiv ℝ χ x (unitVector j))) := by
  obtain ⟨F, c, hval, hfirst, hsecond, E, hEcont, hEae, hEdiff⟩ :=
    c16_negative_power_literal_continuous_energy hκ hR hab hε hp ρ α hell u G hcal hu χ hχ hχc hχU
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
      χ x ^ 2 * (p*(p+1)*Real.rpow (u (r,x)) (-p-2)) *
        dot ((α x).mulVec (G (r,x))) (G (r,x)) +
      2 * χ x * (-p * Real.rpow (u (r,x)) (-p-1)) *
        dot ((α x).mulVec (G (r,x)))
          (fun j => fderiv ℝ χ x (unitVector j)) := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hslices] with r hr
    apply integral_congr_ae
    filter_upwards [hr] with x hx
    rw [hfirst (u (r,x)) hx, hsecond (u (r,x)) hx]
  rw [← heq]
  exact hEdiff s hs t ht

/-- The literal negative-power flux controls the half-power gradient, with
only the spatial cutoff error on the right. -/
theorem c16_negative_power_flux_coercive {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (x : Vec d) (v p : ℝ) (hv : 0 < v) (hp : 0 < p)
    (g : Vec d) (chi : ℝ) (z : Vec d) :
    (2 * κ * (p+1) / p) * chi^2 *
        euclideanSq ((-p/2 * Real.rpow v (-p/2-1)) • g) ≤
      chi^2 * (p*(p+1)*Real.rpow v (-p-2)) * dot ((α x).mulVec g) g +
      2 * chi * (-p * Real.rpow v (-p-1)) * dot ((α x).mulVec g) z +
      (2*p/(κ^3*(p+1))) * Real.rpow v (-p) * euclideanSq z := by
  have hg := c20_negative_power_coercive_gradient hκ ρ α hell x v p hv hp g
  have hg' := mul_le_mul_of_nonneg_left hg (show 0 ≤ chi^2 / 2 by positivity)
  have hm := c20_negative_power_mixed_cutoff hκ ρ α hell x v p hv hp g chi z
  have hm' := (le_abs_self _).trans hm
  calc
    _ = chi^2 / 2 * (4 * κ * (p+1) / p *
        euclideanSq ((-p/2 * Real.rpow v (-p/2-1)) • g)) := by ring
    _ ≤ chi^2 / 2 * (p*(p+1)*Real.rpow v (-p-2) *
        dot ((α x).mulVec g) g) := hg'
    _ ≤ _ := by nlinarith only [hm']

/-- The literal flux in the negative-power energy identity is integrable. -/
theorem c16_negative_power_literal_flux_integrable {d : ℕ}
    {κ R a b ε p : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z : ℝ × Vec d =>
      χ z.2 ^ 2 * (p*(p+1)*Real.rpow (u z) (-p-2)) *
        dot ((α z.2).mulVec (G z)) (G z) +
      2 * χ z.2 * (-p * Real.rpow (u z) (-p-1)) *
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ χ z.2 (unitVector j)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hfirst, hsecond⟩ :=
    c20_negative_power_normalized_extension ε p hε hp
  exact (c16_negative_power_cutoff_integrable hκ ρ α hell u G hcal hu F c M
    hF hF0 hM (fun x => (hb x).2) hval hfirst hsecond χ hχ hχc).2

/-- Spatial integration of the literal flux is integrable in time. -/
theorem c16_negative_power_flux_time_integrable {d : ℕ}
    {κ R a b ε p : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun t => ∫ x in sourceBall 0 R,
      χ x ^ 2 * (p*(p+1)*Real.rpow (u (t,x)) (-p-2)) *
        dot ((α x).mulVec (G (t,x))) (G (t,x)) +
      2 * χ x * (-p * Real.rpow (u (t,x)) (-p-1)) *
        dot ((α x).mulVec (G (t,x))) (fun j => fderiv ℝ χ x (unitVector j)))
      (volume.restrict (Set.Ioo a b)) := by
  have hf := c16_negative_power_literal_flux_integrable hκ hε hp ρ α hell u G hcal hu χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  exact hf.integral_prod_left

/-- The literal negative power is integrable on the finite cylinder. -/
theorem c16_negative_power_integrable {d : ℕ} {R a b ε p : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z) :
    Integrable (fun z => Real.rpow (u z) (-p))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  haveI : IsFiniteMeasure μ := c20_sourceCylinder_isFiniteMeasure a b R 0
  have hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) < ∞ := by
    simpa [μ] using (measure_lt_top μ Set.univ)
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hfirst, hsecond⟩ :=
    c20_negative_power_normalized_extension ε p hε hp
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hm := (c11_weighted_caloric_spacetime_chain_memLp_finite hcal hfinite
    F hF1 M hM (fun x => (hb x).1)).1
  have hm' := hm.add (memLp_const c)
  have heq : (fun z => F (u z) + c) =ᵐ[μ] (fun z => Real.rpow (u z) (-p)) := by
    filter_upwards [hu] with z hz
    rw [hval (u z) hz]
    ring
  exact ((memLp_congr_ae heq).mp hm').integrable (by norm_num)


/-- The negative-power cutoff error is integrable on the cylinder. -/
theorem c16_negative_power_cutoff_error_integrable {d : ℕ} {R a b ε p : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z => Real.rpow (u z) (-p) *
      euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have hpow := c16_negative_power_integrable hε hp ρ α u G hcal hu
  have hDtop (i : Fin d) : MemLp (fun z : ℝ × Vec d =>
      fderiv ℝ χ z.2 (unitVector i)) ∞ μ := by
    have hd : Continuous (fun x : Vec d => fderiv ℝ χ x (unitVector i)) :=
      (hχ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
    obtain ⟨B, hB, hb⟩ :=
      ((hχc.fderiv_apply ℝ (unitVector i)).isCompact_range hd).isBounded.exists_pos_norm_le
    apply memLp_top_of_bound (hd.comp continuous_snd).aestronglyMeasurable B
    exact ae_of_all μ (fun z => hb _ ⟨z.2, rfl⟩)
  have hs : Integrable (fun z : ℝ × Vec d => ∑ i : Fin d,
      Real.rpow (u z) (-p) * (fderiv ℝ χ z.2 (unitVector i)) ^ 2) μ := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    have ht := hpow.mul_of_top_right ((hDtop i).mul (hDtop i))
    convert ht using 1 <;> ext z <;> simp only [Pi.mul_apply, pow_two] <;> ring
  simpa only [euclideanSq, dot, Finset.mul_sum, pow_two] using hs


/-- The cutoff half-power gradient has finite energy on the cylinder. -/
theorem c16_negative_power_gradient_integrable {d : ℕ} {R a b ε p : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z => χ z.2 ^ 2 *
      euclideanSq ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  haveI : IsFiniteMeasure μ := c20_sourceCylinder_isFiniteMeasure a b R 0
  have hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) < ∞ := by
    simpa [μ] using (measure_lt_top μ Set.univ)
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hfirst, hsecond⟩ :=
    c20_negative_power_normalized_extension ε (p/2) hε (by positivity)
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hg := (c11_weighted_caloric_spacetime_chain_memLp_finite hcal hfinite
    F hF1 M hM (fun x => (hb x).1)).2
  have heq : (fun z => euclideanNorm (deriv F (u z) • G z)) =ᵐ[μ]
      (fun z => euclideanNorm ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z)) := by
    filter_upwards [hu] with z hz
    rw [hfirst (u z) hz]
    congr 2 <;> ring
  have hg' := (memLp_congr_ae heq).mp hg
  have henergy : Integrable (fun z => euclideanSq
      ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z)) μ := by
    simpa only [TimeChange.euclideanSq_eq_sq_euclideanNorm] using hg'.integrable_sq
  obtain ⟨C, hC, hbound⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
  have hχtop : MemLp (fun z : ℝ × Vec d => χ z.2) ⊤ μ := by
    apply memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable C
    exact ae_of_all μ (fun z => hbound _ ⟨z.2, rfl⟩)
  have hsq : MemLp (fun z : ℝ × Vec d => χ z.2 ^ 2) ⊤ μ := by
    have ht : MemLp (fun z : ℝ × Vec d => χ z.2 * χ z.2) ⊤ μ := hχtop.mul hχtop
    simpa only [pow_two] using ht
  exact henergy.mul_of_top_right hsq


/-- The coercive negative-power flux estimate holds on almost every time slice. -/
theorem c16_negative_power_spatial_energy_bound {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      (2 * κ * (p+1) / p) * (∫ x in sourceBall 0 R, χ x^2 *
        euclideanSq ((-p/2 * Real.rpow (u (t,x)) (-p/2-1)) • G (t,x))) ≤
      (∫ x in sourceBall 0 R,
        χ x^2 * (p*(p+1)*Real.rpow (u (t,x)) (-p-2)) *
          dot ((α x).mulVec (G (t,x))) (G (t,x)) +
        2 * χ x * (-p * Real.rpow (u (t,x)) (-p-1)) *
          dot ((α x).mulVec (G (t,x))) (fun j => fderiv ℝ χ x (unitVector j))) +
      (2*p/(κ^3*(p+1))) * (∫ x in sourceBall 0 R,
        Real.rpow (u (t,x)) (-p) * euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  have hd := c16_negative_power_gradient_integrable hε hp ρ α u G hcal hu χ hχ hχc
  have hf := c16_negative_power_literal_flux_integrable hκ hε hp ρ α hell u G hcal hu χ hχ hχc
  have he := c16_negative_power_cutoff_error_integrable hε hp ρ α u G hcal hu χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hd hf he hu
  have hslices := Measure.ae_ae_of_ae_prod hu
  filter_upwards [hd.prod_right_ae, hf.prod_right_ae, he.prod_right_ae, hslices] with t ht hf' he' hu'
  have hm := integral_mono_ae (ht.const_mul (2 * κ * (p+1) / p))
    (hf'.add (he'.const_mul (2*p/(κ^3*(p+1))))) (by
      filter_upwards [hu'] with x hx
      simpa only [Pi.add_apply, mul_assoc] using
        (c16_negative_power_flux_coercive hκ ρ α hell x (u (t,x)) p
          (lt_of_lt_of_le hε hx) hp (G (t,x)) (χ x)
          (fun j => fderiv ℝ χ x (unitVector j))))
  simpa only [Pi.add_apply, Pi.mul_apply, integral_const_mul,
    integral_add hf' (he'.const_mul (2*p/(κ^3*(p+1))))] using hm


/-- The continuous negative-power mass controls its half-power gradient on
interior time intervals, up to the cutoff error. -/
theorem c16_negative_power_interval_energy_bound {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) (-p)) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, s ≤ t →
        (2 * κ * (p+1) / p) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * euclideanSq ((-p/2 * Real.rpow (u (q,x)) (-p/2-1)) • G (q,x))) ≤
        E s - E t + (2*p/(κ^3*(p+1))) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          Real.rpow (u (q,x)) (-p) * euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  obtain ⟨E, hEc, hEae, hEdiff⟩ :=
    c16_negative_power_literal_energy_identity hκ hR hab hε hp ρ α hell u G hcal hu χ hχ hχc hχU
  refine ⟨E, hEc, hEae, ?_⟩
  intro s hs t ht hst
  let D : ℝ → ℝ := fun q => ∫ x in sourceBall 0 R,
    χ x ^ 2 * euclideanSq ((-p/2 * Real.rpow (u (q,x)) (-p/2-1)) • G (q,x))
  let Q : ℝ → ℝ := fun q => ∫ x in sourceBall 0 R,
    χ x ^ 2 * (p*(p+1)*Real.rpow (u (q,x)) (-p-2)) *
      dot ((α x).mulVec (G (q,x))) (G (q,x)) +
    2 * χ x * (-p * Real.rpow (u (q,x)) (-p-1)) *
      dot ((α x).mulVec (G (q,x))) (fun j => fderiv ℝ χ x (unitVector j))
  let C : ℝ → ℝ := fun q => ∫ x in sourceBall 0 R,
    Real.rpow (u (q,x)) (-p) * euclideanSq (fun j => fderiv ℝ χ x (unitVector j))
  have hsub : Set.Icc s t ⊆ Set.Ioo a b := by
    intro q hq
    exact ⟨lt_of_lt_of_le hs.1 hq.1, lt_of_le_of_lt hq.2 ht.2⟩
  have hd := c16_negative_power_gradient_integrable hε hp ρ α u G hcal hu χ hχ hχc
  have hc := c16_negative_power_cutoff_error_integrable hε hp ρ α u G hcal hu χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hd hc
  have hD : IntegrableOn D (Set.Ioo a b) volume := hd.integral_prod_left
  have hC : IntegrableOn C (Set.Ioo a b) volume := hc.integral_prod_left
  have hQ : IntegrableOn Q (Set.Ioo a b) volume :=
    c16_negative_power_flux_time_integrable hκ hε hp ρ α hell u G hcal hu χ hχ hχc
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
      (2 * κ * (p+1) / p) * D q ≤ Q q + (2*p/(κ^3*(p+1))) * C q :=
    (c16_negative_power_spatial_energy_bound hκ hε hp ρ α hell u G hcal hu χ hχ hχc).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hm := intervalIntegral.integral_mono_ae_restrict hst
    (hdi.const_mul (2 * κ * (p+1) / p))
    (hqi.add (hci.const_mul (2*p/(κ^3*(p+1))))) hbound
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hqi (hci.const_mul (2*p/(κ^3*(p+1)))),
    intervalIntegral.integral_const_mul] at hm
  have hdiff := hEdiff s hs t ht
  change E t - E s = -(∫ q in s..t, Q q) at hdiff
  change (2 * κ * (p+1) / p) * (∫ q in s..t, D q) ≤
    E s - E t + (2*p/(κ^3*(p+1))) * (∫ q in s..t, C q)
  linarith


/-- The weighted negative-power mass is integrable on the cylinder. -/
theorem c16_weighted_negative_power_integrable {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z) :
    Integrable (fun z => ρ z.2 * Real.rpow (u z) (-p))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have hρ : MemLp (fun z : ℝ × Vec d => ρ z.2) ∞ μ := by
    apply memLp_top_of_bound (hell.1.comp measurable_snd).aestronglyMeasurable κ⁻¹
    filter_upwards with z
    change |ρ z.2| ≤ κ⁻¹
    rw [abs_of_nonneg (hκ.le.trans (hell.2.2 z.2).1)]
    exact (hell.2.2 z.2).2.1
  exact (c16_negative_power_integrable hε hp ρ α u G hcal hu).mul_of_top_right hρ


/-- A bounded cutoff gradient is controlled by the weighted negative-power mass. -/
theorem c16_negative_power_cutoff_error_le_mass {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L ^ 2) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, Real.rpow (u z) (-p) *
      euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j))) ≤
    (L^2 * κ⁻¹) * (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) (-p)) := by
  have he := c16_negative_power_cutoff_error_integrable hε hp ρ α u G hcal hu χ hχ hχc
  have hm := c16_weighted_negative_power_integrable hκ hε hp ρ α hell u G hcal hu
  have hi := integral_mono_ae he (hm.const_mul (L^2 * κ⁻¹)) (by
    filter_upwards [hu] with z hz
    have hq : 0 ≤ Real.rpow (u z) (-p) := Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _
    have hρ : 1 ≤ κ⁻¹ * ρ z.2 := by
      have h := mul_le_mul_of_nonneg_left (hell.2.2 z.2).1 (inv_nonneg.mpr hκ.le)
      simpa only [inv_mul_cancel₀ (ne_of_gt hκ)] using h
    have hg : euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j)) ≤ L^2 * (κ⁻¹ * ρ z.2) :=
      (hL z.2).trans (le_mul_of_one_le_right (sq_nonneg L) hρ)
    have ht := mul_le_mul_of_nonneg_left hg hq
    nlinarith)
  simpa only [integral_const_mul] using hi


/-- The early average of the continuous cutoff mass is bounded by the full mass. -/
theorem c16_negative_power_early_average_le_mass {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (E : ℝ → ℝ) (hrep : ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
      E t = ∫ x in sourceBall 0 1, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) (-p)) :
    IntegrableOn E (Set.Ioo (-1 : ℝ) (-1/2)) ∧
    (∫ t in Set.Ioo (-1 : ℝ) (-1/2), E t) ≤
      ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1, ρ z.2 * Real.rpow (u z) (-p) := by
  let I : Set ℝ := Set.Ioo (-1 : ℝ) 1
  let J : Set ℝ := Set.Ioo (-1 : ℝ) (-1/2)
  let U : Set (Vec d) := sourceBall 0 1
  let F : ℝ → ℝ := fun t => ∫ x in U, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) (-p)
  let Q : ℝ × Vec d → ℝ := fun z => ρ z.2 * χ z.2 ^ 2 * Real.rpow (u z) (-p)
  let M : ℝ × Vec d → ℝ := fun z => ρ z.2 * Real.rpow (u z) (-p)
  have hJI : J ⊆ I := by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  have hQ : IntegrableOn Q (I ×ˢ U) :=
    c16_negative_power_literal_mass_integrable hκ hε hp ρ α hell u G hcal hu χ hχ hχc
  have hM : IntegrableOn M (I ×ˢ U) :=
    c16_weighted_negative_power_integrable hκ hε hp ρ α hell u G hcal hu
  have hQprod := hQ
  change Integrable Q ((volume : Measure (ℝ × Vec d)).restrict (I ×ˢ U)) at hQprod
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hQprod
  have hF : IntegrableOn F I := hQprod.integral_prod_left
  have hrepJ : ∀ᵐ t ∂volume.restrict J, E t = F t :=
    ae_restrict_of_ae_restrict_of_subset hJI hrep
  refine ⟨(hF.mono_set hJI).congr (hrepJ.mono fun _ h => h.symm), ?_⟩
  have hu' := hu
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu'
  have hslices := Measure.ae_ae_of_ae_prod hu'
  have hFpos : ∀ᵐ t ∂volume.restrict I, 0 ≤ F t := by
    filter_upwards [hslices] with t ht
    apply integral_nonneg_of_ae
    filter_upwards [ht] with x hx
    exact mul_nonneg (mul_nonneg (hκ.le.trans (hell.2.2 x).1) (sq_nonneg _))
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hx)) _)
  have hQle : ∀ᵐ z ∂volume.restrict (I ×ˢ U), Q z ≤ M z := by
    filter_upwards [hu] with z hz
    have hc : χ z.2 ^ 2 ≤ 1 := by nlinarith [hχ0 z.2, hχ1 z.2, sq_nonneg (χ z.2)]
    have hp' : 0 ≤ ρ z.2 * Real.rpow (u z) (-p) :=
      mul_nonneg (hκ.le.trans (hell.2.2 z.2).1)
        (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
    have hh := mul_le_mul_of_nonneg_right hc hp'
    dsimp [Q, M]
    calc
      ρ z.2 * χ z.2 ^ 2 * Real.rpow (u z) (-p) =
          χ z.2 ^ 2 * (ρ z.2 * Real.rpow (u z) (-p)) := by ring
      _ ≤ 1 * (ρ z.2 * Real.rpow (u z) (-p)) := hh
      _ = ρ z.2 * Real.rpow (u z) (-p) := by ring
  have hprod : (volume.restrict I).prod (volume.restrict U) =
      (volume : Measure (ℝ × Vec d)).restrict (I ×ˢ U) := by
    rw [Measure.prod_restrict]
    rfl
  calc
    (∫ t in J, E t) = ∫ t in J, F t := integral_congr_ae hrepJ
    _ ≤ ∫ t in I, F t := integral_mono_measure (Measure.restrict_mono hJI le_rfl) hFpos hF
    _ = ∫ z in I ×ˢ U, Q z := by
      rw [← hprod]
      exact (integral_prod _ hQprod).symm
    _ ≤ ∫ z in I ×ˢ U, M z := integral_mono_ae hQ hM hQle


/-- On an interior interval, the cutoff error and the half-power gradient
are controlled by the initial mass and the mass on that interval. -/
theorem c16_negative_power_interval_control {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L ^ 2)
    (E : ℝ → ℝ) (s t : ℝ) (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b)
    (hst : s < t)
    (hE : (2 * κ * (p+1) / p) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * euclideanSq ((-p/2 * Real.rpow (u (q,x)) (-p/2-1)) • G (q,x))) ≤
        E s - E t + (2*p/(κ^3*(p+1))) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          Real.rpow (u (q,x)) (-p) * euclideanSq (fun j => fderiv ℝ χ x (unitVector j)))) :
    E t ≤ E s + ((2*p/(κ^3*(p+1))) * (L^2 * κ⁻¹)) *
      (∫ z in Set.Ioo s t ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) (-p)) := by
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
  have hb := c16_negative_power_cutoff_error_le_mass hκ hε hp ρ α hell u G hcal' hu' χ hχ hχc L hL
  have hi := c16_negative_power_cutoff_error_integrable hε hp ρ α u G hcal' hu' χ hχ hχc
  have hprod : (volume.restrict (Set.Ioo s t)).prod (volume.restrict (sourceBall (0 : Vec d) R)) =
      (volume : Measure (ℝ × Vec d)).restrict (Set.Ioo s t ×ˢ sourceBall 0 R) := by
    rw [Measure.prod_restrict]
    rfl
  rw [← hprod] at hi hb
  rw [integral_prod _ hi, hprod] at hb
  simp only [intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo] at hE
  have hD : 0 ≤ ∫ q in Set.Ioo s t, ∫ x in sourceBall 0 R,
      χ x ^ 2 * euclideanSq ((-p/2 * Real.rpow (u (q,x)) (-p/2-1)) • G (q,x)) := by
    apply integral_nonneg
    intro q
    apply integral_nonneg
    intro x
    exact mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _)
  have hA : 0 ≤ 2*p/(κ^3*(p+1)) := by positivity
  have hB : 0 ≤ 2*κ*(p+1)/p := by positivity
  have := mul_le_mul_of_nonneg_left hb hA
  nlinarith


/-- Restricting the time interval cannot increase the weighted negative-power mass. -/
theorem c16_negative_power_mass_subinterval_le {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (J : Set ℝ) (hJ : J ⊆ Set.Ioo a b) :
    (∫ z in J ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) (-p)) ≤
      ∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) (-p) := by
  apply integral_mono_measure (Measure.restrict_mono (Set.prod_mono hJ (Set.Subset.rfl)) le_rfl)
  · filter_upwards [hu] with z hz
    exact mul_nonneg (hκ.le.trans (hell.2.2 z.2).1)
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
  · exact c16_weighted_negative_power_integrable hκ hε hp ρ α hell u G hcal hu


/-- On almost every time slice, the inner negative-power mass is bounded by
its cutoff mass on the outer ball. -/
theorem c16_negative_power_inner_mass_le_cutoff_slices {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hone : ∀ x ∈ sourceBall 0 (1/2), χ x = 1) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-1/4 : ℝ) (1/4)),
      (∫ x in sourceBall 0 (1/2), ρ x * Real.rpow (u (t,x)) (-p)) ≤
      ∫ x in sourceBall 0 1, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) (-p) := by
  have hsub : sourceBall (0 : Vec d) (1/2) ⊆ sourceBall 0 1 := by
    intro x hx
    change euclideanNorm (x - 0) < 1/2 at hx
    change euclideanNorm (x - 0) < 1
    linarith
  have hsmall : MeasurableSet (sourceBall (0 : Vec d) (1/2)) := by
    rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1/2)]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hi := c16_negative_power_literal_mass_integrable hκ hε hp ρ α hell u G hcal hu χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hi hu
  have hslices := Measure.ae_ae_of_ae_prod hu
  have htime : Set.Ioo (-1/4 : ℝ) (1/4) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset htime hi.prod_right_ae,
    ae_restrict_of_ae_restrict_of_subset htime hslices] with t htint htpos
  calc
    (∫ x in sourceBall 0 (1/2), ρ x * Real.rpow (u (t,x)) (-p)) =
        ∫ x in sourceBall 0 (1/2), ρ x * χ x ^ 2 * Real.rpow (u (t,x)) (-p) := by
      apply setIntegral_congr_fun hsmall
      intro x hx
      dsimp only
      rw [hone x hx]
      ring
    _ ≤ ∫ x in sourceBall 0 1, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) (-p) := by
      apply integral_mono_measure (Measure.restrict_mono hsub le_rfl) ?_ htint
      filter_upwards [htpos] with x hx
      exact mul_nonneg (mul_nonneg (hκ.le.trans (hell.2.2 x).1) (sq_nonneg _))
        (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hx)) _)


/-- Uniform later-time control of the weighted negative-power mass. -/
theorem c16_native_negative_power_energy (d : ℕ) (κ p : ℝ) (hκ : 0 < κ) (hp : 0 < p) :
 ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
 IsUniformlyElliptic κ ρ α → ∀ (ε : ℝ), 0 < ε →
 ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
 IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
 (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
 essSup (fun t : ℝ => ENNReal.ofReal (∫ x in sourceBall 0 (1/2),
   ρ x * Real.rpow (u (t,x)) (-p)))
  (volume.restrict (Set.Ioo (-1/4 : ℝ) (1/4))) ≤
 ENNReal.ofReal (C * ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
   ρ z.2 * Real.rpow (u z) (-p)) := by
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
  let A : ℝ := (2*p/(κ^3*(p+1))) * ((64 : ℝ)^2 * κ⁻¹)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨2 + A, by linarith, ?_⟩
  intro ρ α hell ε hε u G hcal hu
  let M : ℝ := ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
    ρ z.2 * Real.rpow (u z) (-p)
  obtain ⟨E, hEcont, hErep, hEincr⟩ := c16_negative_power_interval_energy_bound hκ
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 1) hε hp
    ρ α hell u G hcal hu χ hχ hχc hχU
  obtain ⟨hEint, hEavg⟩ := c16_negative_power_early_average_le_mass hκ hε hp
    ρ α hell u G hcal hu χ hχ hχc hχ0 hχ1 E hErep
  have hinc : ∀ s ∈ Set.Ioo (-1 : ℝ) (-1/2), ∀ t ∈ Set.Ioo (-1/4 : ℝ) (1/4),
      E t ≤ E s + A * M := by
    intro s hs t ht
    have hsI : s ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
    have htI : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hst : s < t := by linarith [hs.2, ht.1]
    have hb := c16_negative_power_interval_control hκ (by norm_num : (0 : ℝ) < 1) hε hp
      ρ α hell u G hcal hu χ hχ hχc 64 hgrad E s t hsI htI hst (hEincr s hsI t htI hst.le)
    have hm := c16_negative_power_mass_subinterval_le hκ hε hp ρ α hell u G hcal hu
      (Set.Ioo s t) (by intro q hq; exact ⟨lt_trans hsI.1 hq.1, lt_trans hq.2 htI.2⟩)
    have := mul_le_mul_of_nonneg_left hm hA
    dsimp [A, M] at *
    linarith
  have hinner := c16_negative_power_inner_mass_le_cutoff_slices hκ hε hp
    ρ α hell u G hcal hu χ hχ hχc hone
  have hsub : Set.Ioo (-1/4 : ℝ) (1/4) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hrep : ∀ᵐ t ∂volume.restrict (Set.Ioo (-1/4 : ℝ) (1/4)),
      (∫ x in sourceBall 0 (1/2), ρ x * Real.rpow (u (t,x)) (-p)) ≤ E t := by
    filter_upwards [hinner, ae_restrict_of_ae_restrict_of_subset hsub hErep] with t hi he
    rw [he]
    exact hi
  exact c5_later_energy_essSup_le_of_early_average E _ M A hEint hEavg hinc hrep


/-- The interval gradient retains its coefficient in the cutoff estimate. -/
theorem c16_negative_power_interval_gradient_control {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L ^ 2)
    (E : ℝ → ℝ) (s t : ℝ) (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b)
    (hst : s < t)
    (hE : (2 * κ * (p+1) / p) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * euclideanSq ((-p/2 * Real.rpow (u (q,x)) (-p/2-1)) • G (q,x))) ≤
        E s - E t + (2*p/(κ^3*(p+1))) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          Real.rpow (u (q,x)) (-p) * euclideanSq (fun j => fderiv ℝ χ x (unitVector j)))) :
    (2 * κ * (p+1) / p) * (∫ q in s..t, ∫ x in sourceBall 0 R,
      χ x ^ 2 * euclideanSq ((-p/2 * Real.rpow (u (q,x)) (-p/2-1)) • G (q,x))) ≤
    E s - E t + ((2*p/(κ^3*(p+1))) * (L^2 * κ⁻¹)) *
      (∫ z in Set.Ioo s t ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) (-p)) := by
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
  have hb := c16_negative_power_cutoff_error_le_mass hκ hε hp ρ α hell u G hcal' hu' χ hχ hχc L hL
  have hi := c16_negative_power_cutoff_error_integrable hε hp ρ α u G hcal' hu' χ hχ hχc
  have hprod : (volume.restrict (Set.Ioo s t)).prod (volume.restrict (sourceBall (0 : Vec d) R)) =
      (volume : Measure (ℝ × Vec d)).restrict (Set.Ioo s t ×ˢ sourceBall 0 R) := by
    rw [Measure.prod_restrict]
    rfl
  rw [← hprod] at hi hb
  rw [integral_prod _ hi, hprod] at hb
  simp only [intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo] at hE ⊢
  have hA : 0 ≤ 2*p/(κ^3*(p+1)) := by positivity
  have := mul_le_mul_of_nonneg_left hb hA
  nlinarith


/-- The continuous cutoff mass has a nonnegative representative at a late time. -/
theorem c16_negative_power_exists_late_nonnegative {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (E : ℝ → ℝ)
    (hrep : ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
      E t = ∫ x in sourceBall 0 1, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) (-p)) :
    ∃ t ∈ Set.Ioo (1/4 : ℝ) (1/2), 0 ≤ E t := by
  have hsub : Set.Ioo (1/4 : ℝ) (1/2) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu
  have hslices := Measure.ae_ae_of_ae_prod hu
  letI : (ae (volume.restrict (Set.Ioo (1/4 : ℝ) (1/2)))).NeBot :=
    ae_restrict_neBot.mpr (by norm_num [Real.volume_Ioo])
  have hgood : ∀ᵐ t ∂volume.restrict (Set.Ioo (1/4 : ℝ) (1/2)),
      t ∈ Set.Ioo (1/4 : ℝ) (1/2) ∧ 0 ≤ E t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hrep,
      ae_restrict_of_ae_restrict_of_subset hsub hslices] with t ht hEt hpos
    refine ⟨ht, ?_⟩
    rw [hEt]
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with x hx
    exact mul_nonneg (mul_nonneg (hκ.le.trans (hell.2.2 x).1) (sq_nonneg _))
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hx)) _)
  exact hgood.exists


/-- Uniform integrated inner-cylinder control of the gradient of the negative half-power. -/
theorem c16_native_negative_power_gradient_energy (d : ℕ) (κ p : ℝ)
    (hκ : 0 < κ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (ε : ℝ), 0 < ε →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
    (∫ z in Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 (1/2),
      euclideanSq ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z)) ≤
    C * ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
      ρ z.2 * Real.rpow (u z) (-p) := by
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
  let A : ℝ := (2*p/(κ^3*(p+1))) * ((64 : ℝ)^2 * κ⁻¹)
  let B : ℝ := 2 * κ * (p+1) / p
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨(2+A)/B + 1, by positivity, ?_⟩
  intro ρ α hell ε hε u G hcal hu
  let M : ℝ := ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
    ρ z.2 * Real.rpow (u z) (-p)
  have hM : 0 ≤ M := by
    apply integral_nonneg_of_ae
    filter_upwards [hu] with z hz
    exact mul_nonneg (hκ.le.trans (hell.2.2 z.2).1)
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
  obtain ⟨E, hEcont, hErep, hEincr⟩ := c16_negative_power_interval_energy_bound hκ
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 1) hε hp
    ρ α hell u G hcal hu χ hχ hχc hχU
  obtain ⟨hEint, hEavg⟩ := c16_negative_power_early_average_le_mass hκ hε hp
    ρ α hell u G hcal hu χ hχ hχc hχ0 hχ1 E hErep
  obtain ⟨s, hs, _, hsE⟩ := c5_exists_early_energy_le_average E (fun _ => True)
    hEint (ae_of_all _ fun _ => trivial)
  obtain ⟨t, ht, htE⟩ := c16_negative_power_exists_late_nonnegative hκ hε ρ α hell u hu χ E hErep
  have hsI : s ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
  have htI : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hst : s < t := by linarith [hs.2, ht.1]
  have hb := c16_negative_power_interval_gradient_control hκ (by norm_num : (0 : ℝ) < 1) hε hp
    ρ α hell u G hcal hu χ hχ hχc 64 hgrad E s t hsI htI hst (hEincr s hsI t htI hst.le)
  have hm := c16_negative_power_mass_subinterval_le hκ hε hp ρ α hell u G hcal hu
    (Set.Ioo s t) (by intro q hq; exact ⟨lt_trans hsI.1 hq.1, lt_trans hq.2 htI.2⟩)
  have hm' := mul_le_mul_of_nonneg_left hm hA
  let Q : ℝ × Vec d → ℝ := fun z =>
    χ z.2 ^ 2 * euclideanSq ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z)
  let small : Set (ℝ × Vec d) := Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 (1/2)
  let large : Set (ℝ × Vec d) := Set.Ioo s t ×ˢ sourceBall 0 1
  have hsub : small ⊆ large := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    refine ⟨⟨by linarith [hs.2, hq.1], by linarith [hq.2, ht.1]⟩, ?_⟩
    change euclideanNorm (x - 0) < 1/2 at hx
    change euclideanNorm (x - 0) < 1
    linarith
  have hsmall : MeasurableSet small := by
    apply measurableSet_Ioo.prod
    rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1/2)]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hi : IntegrableOn Q (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1) :=
    c16_negative_power_gradient_integrable hε hp ρ α u G hcal hu χ hχ hχc
  have hlarge : large ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1 := by
    intro z hz
    exact ⟨⟨lt_trans hsI.1 hz.1.1, lt_trans hz.1.2 htI.2⟩, hz.2⟩
  have hi' : IntegrableOn Q large := hi.mono_set hlarge
  have hprod : (volume.restrict (Set.Ioo s t)).prod (volume.restrict (sourceBall (0 : Vec d) 1)) =
      (volume : Measure (ℝ × Vec d)).restrict large := by
    rw [Measure.prod_restrict]
    rfl
  have hQ : (∫ z in small, euclideanSq ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z)) ≤
      ∫ q in s..t, ∫ x in sourceBall 0 1,
        χ x ^ 2 * euclideanSq ((-p/2 * Real.rpow (u (q,x)) (-p/2-1)) • G (q,x)) := by
    calc
      _ = ∫ z in small, Q z := by
        apply setIntegral_congr_fun hsmall
        intro z hz
        dsimp [Q]
        rw [hone z.2 hz.2]
        ring
      _ ≤ ∫ z in large, Q z := integral_mono_measure (Measure.restrict_mono hsub le_rfl)
        (ae_of_all _ fun z => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _)) hi'
      _ = _ := by
        rw [intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo, ← hprod]
        exact integral_prod _ (by rw [hprod]; exact hi')
  have hQB := mul_le_mul_of_nonneg_left hQ hB.le
  have hbound : B * (∫ z in small, euclideanSq
      ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z)) ≤ (2+A)*M := by
    dsimp [A, B, M] at *
    nlinarith
  have hdiv : (∫ z in small, euclideanSq
      ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z)) ≤ ((2+A)*M)/B :=
    (le_div_iff₀ hB).2 (by nlinarith [hbound])
  have hr : ((2+A)*M)/B = ((2+A)/B)*M := by ring
  rw [hr] at hdiv
  change (∫ z in small, euclideanSq
    ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z)) ≤ ((2+A)/B + 1)*M
  nlinarith

end EinsteinFull.Calculus
