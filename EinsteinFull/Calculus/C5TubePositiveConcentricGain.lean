import EinsteinFull.Calculus.C8TubeWeightedWeakHarnack
import EinsteinFull.Calculus.C5TubeNestedCutoffs
import EinsteinFull.Calculus.C13TubePositiveSmallPowerGradientEnergy
import EinsteinFull.Calculus.C20TubePositiveSmallPowerSliceMass

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- A positive-power cutoff trace has a nonnegative value on every nonempty
    subinterval of the caloric cylinder. -/
theorem c5_positive_power_exists_nonnegative {d : ℕ} {κ R a b ε p s t : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hst : s < t)
    (hsub : Set.Ioo s t ⊆ Set.Ioo a b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (E : ℝ → ℝ)
    (hrep : ∀ᵐ q ∂volume.restrict (Set.Ioo a b),
      E q = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (q,x)) p) :
    ∃ q ∈ Set.Ioo s t, 0 ≤ E q := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu
  have hslices := Measure.ae_ae_of_ae_prod hu
  letI : (ae (volume.restrict (Set.Ioo s t))).NeBot :=
    ae_restrict_neBot.mpr (by
      rw [Real.volume_Ioo]
      exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hst)).ne')
  have hgood : ∀ᵐ q ∂volume.restrict (Set.Ioo s t),
      q ∈ Set.Ioo s t ∧ 0 ≤ E q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hrep,
      ae_restrict_of_ae_restrict_of_subset hsub hslices] with q hq hEq hpos
    refine ⟨hq, ?_⟩
    rw [hEq]
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with x hx
    exact mul_nonneg (mul_nonneg (hκ.le.trans (hell.2.2 x).1) (sq_nonneg _))
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hx)) _)
  exact hgood.exists

/-- A cutoff positive-power energy is controlled by the mass on any larger cylinder. -/
theorem c5_positive_power_cutoff_average_le_mass {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (E : ℝ → ℝ) (hrep : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p)
    (J : Set ℝ) (hJI : J ⊆ Set.Ioo a b) :
    IntegrableOn E J ∧ (∫ t in J, E t) ≤
      ∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p := by
  let I : Set ℝ := Set.Ioo a b
  let U : Set (Vec d) := sourceBall 0 R
  let F : ℝ → ℝ := fun t => ∫ x in U, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p
  let Q : ℝ × Vec d → ℝ := fun z => ρ z.2 * χ z.2 ^ 2 * Real.rpow (u z) p
  let M : ℝ × Vec d → ℝ := fun z => ρ z.2 * Real.rpow (u z) p
  have hQ : IntegrableOn Q (I ×ˢ U) :=
    c13_positive_power_literal_mass_integrable hκ hε hp hp1 ρ α hell u G hcal hu χ hχ hχc
  have hM : IntegrableOn M (I ×ˢ U) :=
    c13_weighted_positive_power_integrable hκ hε hp hp1 ρ α hell u G hcal hu
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
    have hp' : 0 ≤ ρ z.2 * Real.rpow (u z) p :=
      mul_nonneg (hκ.le.trans (hell.2.2 z.2).1)
        (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
    have hh := mul_le_mul_of_nonneg_right hc hp'
    dsimp [Q, M]
    calc
      ρ z.2 * χ z.2 ^ 2 * Real.rpow (u z) p =
          χ z.2 ^ 2 * (ρ z.2 * Real.rpow (u z) p) := by ring
      _ ≤ 1 * (ρ z.2 * Real.rpow (u z) p) := hh
      _ = ρ z.2 * Real.rpow (u z) p := by ring
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


/-- The actual concave-power energy gives backward cutoff-trace control. -/
theorem c5_positive_power_interval_control {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L ^ 2)
    (E : ℝ → ℝ) (s t : ℝ) (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) (hst : s < t)
    (hE : (κ * p * (1-p) / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * (Real.rpow (u (q,x)) (p-2) * euclideanSq (G (q,x)))) ≤
        E t - E s + (2*p/(κ^3*(1-p))) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          Real.rpow (u (q,x)) p * euclideanSq (fun j => fderiv ℝ χ x (unitVector j)))) :
    E s ≤ E t + ((2*p/(κ^3*(1-p))) * (L^2 * κ⁻¹)) *
      (∫ z in Set.Ioo s t ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p) := by
  exact c20_positive_power_interval_control c13_positive_power_cutoff_error_le_mass
    c13_positive_power_cutoff_error_integrable hκ hR hε hp hp1 ρ α hell u G hcal hu
    χ hχ hχc L hL E s t hs ht hst hE

/-- The actual caloric field supplies a cutoff trace, its future average,
    and the backward trace estimate on an arbitrary cylinder. -/
theorem c5_positive_power_cutoff_trace_and_average {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ sourceBall 0 R) (hχ0 : ∀ x, 0 ≤ χ x)
    (hχ1 : ∀ x, χ x ≤ 1)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L ^ 2)
    (J : Set ℝ) (hJI : J ⊆ Set.Ioo a b) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p) ∧
      (∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, s ≤ t →
        (κ * p * (1-p) / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * (Real.rpow (u (q,x)) (p-2) * euclideanSq (G (q,x)))) ≤
        E t - E s + (2*p/(κ^3*(1-p))) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          Real.rpow (u (q,x)) p * euclideanSq (fun j => fderiv ℝ χ x (unitVector j)))) ∧
      IntegrableOn E J ∧
      (∫ t in J, E t) ≤ (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        ρ z.2 * Real.rpow (u z) p) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, s < t →
        E s ≤ E t + ((2*p/(κ^3*(1-p))) * (L^2 * κ⁻¹)) *
          (∫ z in Set.Ioo s t ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p) := by
  obtain ⟨E, hEc, hrep, hbalance⟩ := c13_positive_power_interval_energy_bound
    hκ hR hab hε hp hp1 ρ α hell u G hcal hu χ hχ hχc hχU
  obtain ⟨hEJ, havg⟩ := c5_positive_power_cutoff_average_le_mass hκ hε hp hp1
    ρ α hell u G hcal hu χ hχ hχc hχ0 hχ1 E hrep J hJI
  refine ⟨E, hEc, hrep, hbalance, hEJ, havg, ?_⟩
  intro s hs t ht hst
  exact c5_positive_power_interval_control hκ hR hε hp hp1 ρ α hell u G hcal hu
    χ hχ hχc L hL E s t hs ht hst (hbalance s hs t ht hst.le)

/-- Early nonnegative and late averaged traces for the actual positive-power
    energy on a cylinder. -/
theorem c5_positive_power_cutoff_selected_traces {d : ℕ} {κ R a b ε p : ℝ}
    {s₀ s₁ t₀ t₁ : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (hs : s₀ < s₁) (ht : t₀ < t₁) (hsep : s₁ ≤ t₀)
    (hsI : Set.Ioo s₀ s₁ ⊆ Set.Ioo a b) (htI : Set.Ioo t₀ t₁ ⊆ Set.Ioo a b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ sourceBall 0 R) (hχ0 : ∀ x, 0 ≤ χ x)
    (hχ1 : ∀ x, χ x ≤ 1)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L ^ 2) :
    ∃ (E : ℝ → ℝ) (s t : ℝ), s ∈ Set.Ioo s₀ s₁ ∧ t ∈ Set.Ioo t₀ t₁ ∧
      0 ≤ E s ∧ E t ≤ (t₁ - t₀)⁻¹ *
        (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p) ∧
      (∀ᵐ q ∂volume.restrict (Set.Ioo a b),
        E q = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (q,x)) p) ∧
      (∀ q ∈ Set.Ioo a b, ∀ r ∈ Set.Ioo a b, q ≤ r →
        (κ * p * (1-p) / 2) * (∫ v in q..r, ∫ x in sourceBall 0 R,
          χ x ^ 2 * (Real.rpow (u (v,x)) (p-2) * euclideanSq (G (v,x)))) ≤
        E r - E q + (2*p/(κ^3*(1-p))) * (∫ v in q..r, ∫ x in sourceBall 0 R,
          Real.rpow (u (v,x)) p * euclideanSq (fun j => fderiv ℝ χ x (unitVector j)))) ∧
      (∀ q ∈ Set.Ioo a b, ∀ r ∈ Set.Ioo a b, q < r →
        E q ≤ E r + ((2*p/(κ^3*(1-p))) * (L^2 * κ⁻¹)) *
          (∫ z in Set.Ioo q r ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p)) ∧
      (∀ q ∈ Set.Ioo a b, q < t → E q ≤
        ((t₁ - t₀)⁻¹ + (2*p/(κ^3*(1-p))) * (L^2 * κ⁻¹)) *
          (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p)) ∧
      s < t ∧
      (κ * p * (1-p) / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
        χ x ^ 2 * (Real.rpow (u (q,x)) (p-2) * euclideanSq (G (q,x)))) ≤
      ((t₁ - t₀)⁻¹ + (2*p/(κ^3*(1-p))) * (L^2 * κ⁻¹)) *
        (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p) := by
  obtain ⟨E, _, hrep, hbalance, hEint, havg, hback⟩ :=
    c5_positive_power_cutoff_trace_and_average hκ hR hab hε hp hp1 ρ α hell u G hcal hu
      χ hχ hχc hχU hχ0 hχ1 L hL (Set.Ioo t₀ t₁) htI
  obtain ⟨s, hs', hsE⟩ := c5_positive_power_exists_nonnegative hκ hε hs hsI ρ α hell u hu χ E hrep
  obtain ⟨t, ht', _, htE⟩ := c5_exists_interval_energy_le_average ht E (fun _ => True)
    hEint (ae_of_all _ fun _ => trivial)
  have hbound := mul_le_mul_of_nonneg_left havg (inv_nonneg.mpr (sub_nonneg.mpr ht.le))
  have hst : s < t := lt_of_lt_of_le hs'.2 (le_trans hsep ht'.1.le)
  have hsI' := hsI hs'
  have htI' := htI ht'
  have hgrad := c13_positive_power_interval_gradient_control hκ hR hε hp hp1
    ρ α hell u G hcal hu χ hχ hχc L hL E s t hsI' htI' hst
    (hbalance s hsI' t htI' hst.le)
  have hmass := c13_positive_power_mass_subinterval_le hκ hε hp hp1 ρ α hell u G hcal hu
    (Set.Ioo s t) (by intro q hq; exact ⟨lt_trans hsI'.1 hq.1, lt_trans hq.2 htI'.2⟩)
  have hp1' : 0 < 1 - p := by linarith
  have hA : 0 ≤ (2*p/(κ^3*(1-p))) * (L^2 * κ⁻¹) := by positivity
  have hmass' := mul_le_mul_of_nonneg_left hmass hA
  have htrace : ∀ q ∈ Set.Ioo a b, q < t → E q ≤
      ((t₁ - t₀)⁻¹ + (2*p/(κ^3*(1-p))) * (L^2 * κ⁻¹)) *
        (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p) := by
    intro q hq hqt
    have hback' := hback q hq t htI' hqt
    have hmq := c13_positive_power_mass_subinterval_le hκ hε hp hp1 ρ α hell u G hcal hu
      (Set.Ioo q t) (by intro v hv; exact ⟨lt_trans hq.1 hv.1, lt_trans hv.2 htI'.2⟩)
    have hmq' := mul_le_mul_of_nonneg_left hmq hA
    nlinarith
  refine ⟨E, s, t, hs', ht', hsE, le_trans htE hbound, hrep, hbalance, hback, htrace, hst, ?_⟩
  nlinarith

/-- The actual positive shift has a cutoff norm gain whenever the stated mass
and coefficient-energy bounds hold. The bounds are retained explicitly. -/
theorem c5_shifted_cutoff_norm_gain (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
    ∀ ε : ℝ, 0 < ε →
    ∀ (η : ℝ × Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
    ∀ K : Set (Vec d), IsCompact K → K ⊆ sourceBall 0 1 →
    (∀ t x, x ∉ K → η (t,x) = 0) →
    ∀ S T : Set (ℝ × Vec d), MeasurableSet S →
    S ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1 →
    T ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1 →
    (∀ z ∈ S, η z = 1) →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ D : ℝ≥0∞,
    let w : ℝ × Vec d → ℝ := fun z => u z + ε
    let v : ℝ × Vec d → ℝ := fun z => η z * (w z) ^ (p / 2)
    let J : ℝ × Vec d → Vec d := fun z =>
      η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) +
        (w z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j))
    (∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
      (∫⁻ x in sourceBall (0 : Vec d) 1, ENNReal.ofReal (ρ x) * ‖v (t,x)‖ₑ ^ (2 : ℝ)) ≤
        D * ∫⁻ z in T, ENNReal.ofReal (w z) ^ p) →
    AEMeasurable (fun z => ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z)))
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1)) →
    (∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
      ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z))) ≤
        D * ∫⁻ z in T, ENNReal.ofReal (w z) ^ p →
    eLpNorm w (ENNReal.ofReal (p * (((d : ℝ) + 2) / d))) (volume.restrict S) ≤
      (C ^ ((p * (((d : ℝ) + 2) / d))⁻¹) * D ^ p⁻¹) *
        eLpNorm w (ENNReal.ofReal p) (volume.restrict T) := by
  obtain ⟨C, hC, hsob⟩ := c8_actual_small_positive_power_integral_gain d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal hu0 ε hε η hη hcη K hK hKU hzero S T hS hSI hTI hηone p hp hp1 D w v J hmass hJm henergy
  obtain ⟨hshift, hpos⟩ := c8_weighted_caloric_positive_shift hκ hell hcal hu0 hε
  have hfinite : volume (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1) < ∞ := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioo (-1 : ℝ) 1)) :=
      isFiniteMeasure_restrict.mpr (by simp)
    have : IsFiniteMeasure (volume.restrict (sourceBall (0 : Vec d) 1)) :=
      isFiniteMeasure_restrict.mpr (by
        rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
        exact PDE.volume_euclideanBall_ne_top 0 (by norm_num))
    have : IsFiniteMeasure (volume.restrict
        (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      infer_instance
    exact lt_top_iff_ne_top.mpr (by
      simpa only [Measure.restrict_apply_univ] using
        (measure_ne_top (volume.restrict
          (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)) Set.univ))
  have hgain := hsob ρ α hell (Set.Ioo (-1) 1) (sourceBall 0 1)
    measurableSet_Ioo (c17_isOpen_sourceBall 0 1) hfinite w G hshift η hη hcη K hK hKU hzero
    S T hS hSI hηone p ε hp hp1 hε hpos D hmass hJm henergy
  have hSmeas : AEStronglyMeasurable w (volume.restrict S) :=
    hshift.1.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume hSI)
  have hTmeas : AEStronglyMeasurable w (volume.restrict T) :=
    hshift.1.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume hTI)
  have hSpos : ∀ᵐ z ∂volume.restrict S, 0 ≤ w z :=
    (hpos.filter_mono (ae_mono (Measure.restrict_mono_set volume hSI))).mono (fun _ h => le_trans hε.le h)
  have hTpos : ∀ᵐ z ∂volume.restrict T, 0 ≤ w z :=
    (hpos.filter_mono (ae_mono (Measure.restrict_mono_set volume hTI))).mono (fun _ h => le_trans hε.le h)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  exact c8_positive_integral_gain_to_eLpNorm _ _ w hp (by positivity : 0 < ((d : ℝ) + 2) / d)
    hSmeas hTmeas hSpos hTpos C D hgain


/-- The shifted field's normalized positive-cylinder norm is its time-first norm. -/
theorem c5_shifted_posCyl_norm_swap (d : ℕ) (σ : ℝ)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (q : ℝ≥0∞)
    (u : ℝ × Vec d → ℝ) (ε : ℝ) :
    eLpNorm (fun z : Vec d × ℝ => u (z.2, z.1) + ε) q
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.posCyl d σ)) =
    eLpNorm (fun z : ℝ × Vec d => u z + ε) q
      ((volume (PDE.Parabolic.WeakHarnack.posCyl d 1))⁻¹ • volume.restrict
        (Set.Ioo (-3 / 4 - (σ - 1 / 2) / 4) (-1 / 2 + (σ - 1 / 2) / 4) ×ˢ
          sourceBall 0 (1 / 2 + (σ - 1 / 2) / 2))) := by
  rw [PDE.Parabolic.WeakHarnack.cylMeasure_restrict
    (PDE.Parabolic.WeakHarnack.measurableSet_posCyl σ)
    (PDE.Parabolic.WeakHarnack.posCyl_mono hσ hσ1)]
  exact c8_posCyl_swap_eLpNorm d σ hσ _ q (fun z => u z + ε)


/-- Nested iteration radii have a positive gap bounded by one half. -/
theorem c5_positive_concentric_gap_bounds (σ' σ : ℝ)
    (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1) :
    0 < σ - σ' ∧ σ - σ' ≤ 1 / 2 := by
  constructor <;> linarith

/-- The spatial radii of nested positive cylinders stay inside the unit ball. -/
theorem c5_positive_concentric_radius_bounds (σ' σ : ℝ)
    (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1) :
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    0 < r ∧ r < R ∧ R < 1 := by
  dsimp only
  constructor
  · linarith
  constructor <;> linarith

/-- The time ramps can be placed strictly inside the outer cylinder while
remaining equal to one on the inner cylinder. -/
theorem c5_positive_concentric_time_gaps (σ' σ : ℝ)
    (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1) :
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let b' : ℝ := -1 / 2 + (σ' - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    0 < δ ∧ -1 < a + δ ∧ a + δ < a' ∧ b' ≤ (b - δ) - δ ∧ b - δ < 1 := by
  dsimp only
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Smooth spatial cutoffs for the positive iteration cylinders, with a
squared gradient bound controlled by the gap between the iteration radii. -/
theorem c5_positive_concentric_spatial_cutoffs (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ →
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    ∃ χ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ sourceBall 0 R ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ sourceBall (0 : Vec d) r, χ x = 1) ∧
      (∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ C / (σ - σ') ^ 2) := by
  obtain ⟨C, hC, hcut⟩ := c5_source_ball_cutoffs d
  refine ⟨4 * C, by positivity, ?_⟩
  intro σ' σ hσ' hσ
  dsimp only
  have hr : 0 ≤ 1 / 2 + (σ' - 1 / 2) / 2 := by linarith
  have hrR : 1 / 2 + (σ' - 1 / 2) / 2 < 1 / 2 + (σ - 1 / 2) / 2 := by
    linarith
  obtain ⟨χ, hs, hc, hsupport, hbound, hone, hgrad⟩ := hcut _ _ hr hrR
  refine ⟨χ, hs, hc, hsupport, hbound, hone, ?_⟩
  intro x
  have hdiff : (1 / 2 + (σ - 1 / 2) / 2) -
      (1 / 2 + (σ' - 1 / 2) / 2) = (σ - σ') / 2 := by ring
  have hgap : σ - σ' ≠ 0 := ne_of_gt (sub_pos.mpr hσ)
  have heq : C / ((1 / 2 + (σ - 1 / 2) / 2) -
      (1 / 2 + (σ' - 1 / 2) / 2)) ^ 2 = 4 * C / (σ - σ') ^ 2 := by
    rw [hdiff]
    field_simp [hgap]
    ring
  exact (hgrad x).trans_eq heq

/-- A compact smooth cutoff equals one on the inner positive cylinder and
is supported within the original caloric domain. -/
theorem c5_positive_concentric_compact_cutoff (d : ℕ) (σ' σ : ℝ)
    (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1) :
    ∃ η : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1 ∧
      (∀ z, 0 ≤ η z ∧ η z ≤ 1) ∧
      (∀ z ∈ Set.Ioo (-3 / 4 - (σ' - 1 / 2) / 4)
          (-1 / 2 + (σ' - 1 / 2) / 4) ×ˢ
          sourceBall (0 : Vec d) (1 / 2 + (σ' - 1 / 2) / 2), η z = 1) := by
  let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
  let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
  let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
  let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
  let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
  let b' : ℝ := -1 / 2 + (σ' - 1 / 2) / 4
  let δ : ℝ := (σ - σ') / 8
  have hr : 0 < r ∧ r < R ∧ R < 1 := c5_positive_concentric_radius_bounds σ' σ hσ' hσ hσ1
  have ht : 0 < δ ∧ -1 < a + δ ∧ a + δ < a' ∧
      b' ≤ (b - δ) - δ ∧ b - δ < 1 := c5_positive_concentric_time_gaps σ' σ hσ' hσ hσ1
  let ξ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
  let η : ℝ × Vec d → ℝ := fun z =>
    (PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
      PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1) * ξ z.2
  have hc := c11_compact_cylinder_cutoff (d := d) (r := r) (R := R)
    (T := a + δ) (T' := a') (b := b - δ) (h := δ) hr.1.le hr.2.1 ht.2.2.1 ht.1
  refine ⟨η, hc.1, hc.2.1, ?_, hc.2.2.2.2.1, ?_⟩
  · intro z hz
    have h := hc.2.2.1 hz
    have hx := hc.2.2.2.1 h.2
    rw [← c8_sourceBall_eq_euclideanBall (0 : Vec d) (lt_trans hr.1 hr.2.1)] at hx
    refine ⟨⟨lt_of_lt_of_le ht.2.1 h.1.1, lt_of_le_of_lt h.1.2 ht.2.2.2.2⟩, ?_⟩
    change euclideanNorm (z.2 - 0) < 1
    change euclideanNorm (z.2 - 0) < R at hx
    exact lt_trans hx hr.2.2
  · intro z hz
    apply hc.2.2.2.2.2 z (le_of_lt hz.1.1) (le_trans (le_of_lt hz.1.2) ht.2.2.2.1)
    rw [← c8_sourceBall_eq_euclideanBall (0 : Vec d) hr.1]
    exact hz.2

/-- The shifted caloric field has a literal interval energy trace for the
    spatial cutoff of any two positive iteration cylinders. -/
theorem c5_positive_concentric_interval_energy (d : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
    ∀ ε p : ℝ, 0 < ε → 0 < p → p < 1 →
    ∃ (χ : Vec d → ℝ) (E : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ sourceBall 0 (1 / 2 + (σ - 1 / 2) / 2) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ sourceBall (0 : Vec d) (1 / 2 + (σ' - 1 / 2) / 2), χ x = 1) ∧
      (∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ C / (σ - σ') ^ 2) ∧
      ContinuousOn E (Set.Ioo (-1) 1) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
        E t = ∫ x in sourceBall 0 1, ρ x * χ x ^ 2 * Real.rpow (u (t,x) + ε) p) ∧
      ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, s ≤ t →
        (κ * p * (1-p) / 2) * (∫ q in s..t, ∫ x in sourceBall 0 1,
          χ x ^ 2 * (Real.rpow (u (q,x) + ε) (p-2) * euclideanSq (G (q,x)))) ≤
        E t - E s + (2*p/(κ^3*(1-p))) * (∫ q in s..t, ∫ x in sourceBall 0 1,
          Real.rpow (u (q,x) + ε) p * euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  obtain ⟨C, hC, hcut⟩ := c5_positive_concentric_spatial_cutoffs d
  refine ⟨C, hC, ?_⟩
  intro σ' σ hσ' hσ hσ1 ρ α hell u G hcal hu ε p hε hp hp1
  obtain ⟨χ, hχ, hχc, hχs, hχbound, hχone, hχgrad⟩ := hcut σ' σ hσ' hσ
  have hR := (c5_positive_concentric_radius_bounds σ' σ hσ' hσ hσ1).2.2
  have hχU : tsupport χ ⊆ sourceBall 0 1 := by
    intro x hx
    have hx' := hχs hx
    change euclideanNorm (x - 0) < 1
    change euclideanNorm (x - 0) < 1 / 2 + (σ - 1 / 2) / 2 at hx'
    exact lt_trans hx' hR
  obtain ⟨hshift, hpos⟩ := c8_weighted_caloric_positive_shift hκ hell hcal hu hε
  obtain ⟨E, hEc, hEae, hE⟩ := c13_positive_power_interval_energy_bound hκ
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 1) hε hp hp1
    ρ α hell (fun z => u z + ε) G hshift hpos χ hχ hχc hχU
  exact ⟨χ, E, hχ, hχc, hχs, hχbound, hχone, hχgrad, hEc, hEae, hE⟩

/-- The canonical spatial cutoff has the actual positive-power interval
    energy inequality on the outer iteration cylinder. -/
theorem c5_positive_concentric_outer_interval_energy (d : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (σ' σ : ℝ) (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z)
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1) :
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x) + ε) p) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, s ≤ t →
        (κ * p * (1-p) / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * (Real.rpow (u (q,x) + ε) (p-2) * euclideanSq (G (q,x)))) ≤
        E t - E s + (2*p/(κ^3*(1-p))) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          Real.rpow (u (q,x) + ε) p * euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  dsimp only
  let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
  let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
  let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
  let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
  let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
  have hr : 0 < r ∧ r < R ∧ R < 1 := c5_positive_concentric_radius_bounds σ' σ hσ' hσ hσ1
  have hR : 0 < R := lt_trans hr.1 hr.2.1
  have hab : a < b := by dsimp [a, b]; linarith
  have htime : Set.Ioo a b ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    rcases ht with ⟨ht1, ht2⟩
    dsimp [a, b] at ht1 ht2
    constructor <;> linarith
  have hspace : sourceBall (0 : Vec d) R ⊆ sourceBall 0 1 := by
    intro x hx
    change euclideanNorm (x - 0) < R at hx
    change euclideanNorm (x - 0) < 1
    exact lt_trans hx hr.2.2
  have hχs : tsupport χ ⊆ sourceBall (0 : Vec d) R := by
    rw [c8_sourceBall_eq_euclideanBall (0 : Vec d) hR]
    exact PDE.canonicalBallCutoff_tsupport_subset_outer hr.1.le hr.2.1
  obtain ⟨hshift, hpos⟩ := c8_weighted_caloric_positive_shift hκ hell hcal hu hε
  have hcal' := c11_weighted_caloric_cylinder_mono measurableSet_Ioo measurableSet_Ioo
    (c17_isOpen_sourceBall (0 : Vec d) 1).measurableSet htime hspace hshift
  have hpos' := ae_restrict_of_ae_restrict_of_subset (Set.prod_mono htime hspace) hpos
  exact c13_positive_power_interval_energy_bound hκ hR hab hε hp hp1 ρ α hell
    (fun z => u z + ε) G hcal' hpos' χ
    (PDE.canonicalBallCutoff_smooth 0 hr.1.le hr.2.1)
    (PDE.canonicalBallCutoff_hasCompactSupport hr.1.le hr.2.1) hχs

/-- The canonical space-time cutoff has derivative bounds depending only on
    the gap between the two iteration radii. -/
theorem c5_positive_concentric_cutoff_derivatives :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (σ' σ : ℝ), 1 / 2 ≤ σ' → σ' < σ →
      let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
      let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
      let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
      let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
      let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
      let δ : ℝ := (σ - σ') / 8
      let η : ℝ × Vec d → ℝ := fun z =>
        (PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
          PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1) *
            PDE.canonicalBallCutoff (0 : Vec d) r R z.2
      (∀ z, |fderiv ℝ η z (1, 0)| ≤ C / (σ - σ')) ∧
      (∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤
        (64 / (σ - σ')) ^ 2) := by
  obtain ⟨B, hB, hderiv⟩ := PDE.Parabolic.LocalMax.exists_abs_deriv_smoothTransition_le
  obtain ⟨Q, hQ, hbounds⟩ := c11_compact_cylinder_cutoff_gap_bounds
  refine ⟨16 * B + 8 * Q + 1, by positivity, ?_⟩
  intro d σ' σ hσ' hσ
  dsimp only
  have hr : 0 ≤ 1 / 2 + (σ' - 1 / 2) / 2 := by linarith
  have hrR : 1 / 2 + (σ' - 1 / 2) / 2 < 1 / 2 + (σ - 1 / 2) / 2 := by linarith
  have htime : -3 / 4 - (σ - 1 / 2) / 4 + (σ - σ') / 8 <
      -3 / 4 - (σ' - 1 / 2) / 4 := by linarith
  have hδ : 0 < (σ - σ') / 8 := by linarith
  have hgap : 0 < σ - σ' := sub_pos.mpr hσ
  have hh := hbounds (d := d)
    (b := -1 / 2 + (σ - 1 / 2) / 4 - (σ - σ') / 8) hr hrR htime hδ hderiv
  dsimp only at hh
  constructor
  · intro z
    refine (hh.1 z).trans ?_
    have heq : (-3 / 4 - (σ' - 1 / 2) / 4) -
        (-3 / 4 - (σ - 1 / 2) / 4 + (σ - σ') / 8) = (σ - σ') / 8 := by ring
    rw [heq, ← add_div]
    apply (div_le_div_iff₀ (by positivity : 0 < (σ - σ') / 8) hgap).2
    nlinarith
  · intro z
    refine (hh.2 z).trans_eq ?_
    have heq : (1 / 2 + (σ - 1 / 2) / 2) -
        (1 / 2 + (σ' - 1 / 2) / 2) = (σ - σ') / 2 := by ring
    rw [heq]
    congr 1
    field_simp [ne_of_gt hgap]
    <;> norm_num

/-- The requested iteration exponents stay below the small-power threshold. -/
theorem c5_positive_gain_exponent_lt_half (d : ℕ) (hd : 2 ≤ d) (p : ℝ)
    (hp : p ≤ (d : ℝ) / (2 * ((d : ℝ) + 2))) : p < 1 / 2 := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hden : 0 < 2 * ((d : ℝ) + 2) := by positivity
  have hbound : (d : ℝ) / (2 * ((d : ℝ) + 2)) < 1 / 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  exact hp.trans_lt hbound


/-- The boosted exponent remains at most one half in the prescribed range. -/
theorem c5_positive_gain_boosted_exponent_le_half (d : ℕ) (hd : 2 ≤ d) (p : ℝ)
    (hp : p ≤ (d : ℝ) / (2 * ((d : ℝ) + 2))) :
    (((d : ℝ) + 2) / d) * p ≤ 1 / 2 := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hbound := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ ((d : ℝ) + 2) / d by positivity)
  have heq : (((d : ℝ) + 2) / d) *
      ((d : ℝ) / (2 * ((d : ℝ) + 2))) = 1 / 2 := by
    field_simp
  linarith

/-- The normalized shifted-cylinder norm carries the explicit volume factor. -/
theorem c5_shifted_posCyl_norm_volume_factor (d : ℕ) (σ : ℝ)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (q : ℝ≥0∞)
    (hq0 : q ≠ 0) (hqtop : q ≠ ⊤) (u : ℝ × Vec d → ℝ) (ε : ℝ) :
    eLpNorm (fun z : Vec d × ℝ => u (z.2, z.1) + ε) q
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.posCyl d σ)) =
    (volume (PDE.Parabolic.WeakHarnack.posCyl d 1))⁻¹ ^ (1 / q).toReal *
      eLpNorm (fun z : ℝ × Vec d => u z + ε) q
        (volume.restrict
          (Set.Ioo (-3 / 4 - (σ - 1 / 2) / 4) (-1 / 2 + (σ - 1 / 2) / 4) ×ˢ
            sourceBall 0 (1 / 2 + (σ - 1 / 2) / 2))) := by
  rw [c5_shifted_posCyl_norm_swap d σ hσ hσ1 q u ε]
  simpa only [smul_eq_mul] using
    (eLpNorm_smul_measure_of_ne_zero_of_ne_top hq0 hqtop
      (f := fun z : ℝ × Vec d => u z + ε)
      (volume (PDE.Parabolic.WeakHarnack.posCyl d 1))⁻¹)

#lint
end EinsteinFull.Calculus
