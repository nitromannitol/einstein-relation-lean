import EinsteinFull.Calculus.C16TubeNegativePowerEnergy
import EinsteinFull.Calculus.C20TubeNegativePowerWeakGradient
import EinsteinFull.Calculus.C13TubeNativeCutoffProduct
import EinsteinFull.Calculus.C9TubeCutoffCoefficientEnergy
import EinsteinFull.Calculus.C20TubeNegativeHalfPowerGradientL2
import EinsteinFull.Calculus.C8TubeWeightedParabolicSobolev

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open scoped Topology NNReal ENNReal

namespace EinsteinFull.Calculus

/-- The explicit cutoff-error coefficient in the negative-power energy estimate is
uniformly bounded in the exponent. -/
theorem c17_negative_power_cutoff_coefficient_le (κ p L : ℝ) (hκ : 0 < κ)
    (hp : 0 < p) :
    (2*p/(κ^3*(p+1))) * (L^2 * κ⁻¹) ≤
      2 / κ^3 * (L^2 * κ⁻¹) := by
  have hp1 : 0 < p + 1 := by linarith
  have hquot : p / (p + 1) ≤ 1 := (div_le_one₀ hp1).2 (by linarith)
  have hk : 0 ≤ 2 / κ^3 := by positivity
  have hm : 0 ≤ L^2 * κ⁻¹ := by positivity
  calc
    (2*p/(κ^3*(p+1))) * (L^2 * κ⁻¹) =
        ((2 / κ^3) * (p / (p+1))) * (L^2 * κ⁻¹) := by field_simp [hκ.ne', hp1.ne']
    _ ≤ (2 / κ^3) * 1 * (L^2 * κ⁻¹) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hquot hk) hm
    _ = _ := by ring


/-- The reciprocal gradient coercivity coefficient is uniformly bounded in p. -/
theorem c17_negative_power_gradient_coefficient_le (κ p : ℝ)
    (hκ : 0 < κ) (hp : 0 < p) :
    (2 * κ * (p + 1) / p)⁻¹ ≤ (2 * κ)⁻¹ := by
  have hp1 : 0 < p + 1 := by linarith
  have hquot : p / (p + 1) ≤ 1 := (div_le_one₀ hp1).2 (by linarith)
  have hk : 0 ≤ (2 * κ)⁻¹ := by positivity
  calc
    (2 * κ * (p + 1) / p)⁻¹ = (2 * κ)⁻¹ * (p / (p + 1)) := by
      field_simp [hκ.ne', hp.ne', hp1.ne']
    _ ≤ (2 * κ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hquot hk
    _ = _ := mul_one _

/-- The coefficient in the native gradient estimate is uniformly bounded in p. -/
theorem c17_negative_power_native_gradient_constant_le (κ p L : ℝ)
    (hκ : 0 < κ) (hp : 0 < p) :
    (2 + (2*p/(κ^3*(p+1))) * (L^2 * κ⁻¹)) /
        (2 * κ * (p+1) / p) ≤
      (2 + (2 / κ^3) * (L^2 * κ⁻¹)) * (2 * κ)⁻¹ := by
  have ha := c17_negative_power_cutoff_coefficient_le κ p L hκ hp
  have hb := c17_negative_power_gradient_coefficient_le κ p hκ hp
  have ha0 : 0 ≤ 2 + (2*p/(κ^3*(p+1))) * (L^2 * κ⁻¹) := by positivity
  have hc0 : 0 ≤ (2 * κ)⁻¹ := by positivity
  rw [div_eq_mul_inv]
  calc
    _ ≤ (2 + (2*p/(κ^3*(p+1))) * (L^2 * κ⁻¹)) * (2 * κ)⁻¹ :=
      mul_le_mul_of_nonneg_left hb ha0
    _ ≤ (2 + (2 / κ^3) * (L^2 * κ⁻¹)) * (2 * κ)⁻¹ :=
      mul_le_mul_of_nonneg_right (add_le_add_right ha 2) hc0

/-- The explicit witness in the native gradient estimate is bounded uniformly in p. -/
theorem c17_negative_power_native_gradient_witness_le (κ p L : ℝ)
    (hκ : 0 < κ) (hp : 0 < p) :
    (2 + (2*p/(κ^3*(p+1))) * (L^2 * κ⁻¹)) /
        (2 * κ * (p+1) / p) + 1 ≤
      (2 + (2 / κ^3) * (L^2 * κ⁻¹)) * (2 * κ)⁻¹ + 1 :=
  by simpa only [add_comm] using
    add_le_add_right (c17_negative_power_native_gradient_constant_le κ p L hκ hp) 1

/-- Uniform later-time cutoff mass with an explicit exponent-independent constant. -/
theorem c17_negative_power_cutoff_mass_bound {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 1)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L^2) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo (-1 : ℝ) 1) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
        E t = ∫ x in sourceBall 0 1, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) (-p)) ∧
      ∀ t ∈ Set.Ioo (-1/4 : ℝ) (1/4),
        E t ≤ (2 + (2 / κ^3) * (L^2 * κ⁻¹)) *
          (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
            ρ z.2 * Real.rpow (u z) (-p)) := by
  let M : ℝ := ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
    ρ z.2 * Real.rpow (u z) (-p)
  let A : ℝ := (2*p/(κ^3*(p+1))) * (L^2 * κ⁻¹)
  let B : ℝ := (2 / κ^3) * (L^2 * κ⁻¹)
  have hM : 0 ≤ M := by
    apply integral_nonneg_of_ae
    filter_upwards [hu] with z hz
    exact mul_nonneg (hκ.le.trans (hell.2.2 z.2).1)
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAB : A ≤ B := c17_negative_power_cutoff_coefficient_le κ p L hκ hp
  obtain ⟨E, hEcont, hErep, hEincr⟩ := c16_negative_power_interval_energy_bound hκ
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 1) hε hp
    ρ α hell u G hcal hu χ hχ hχc hχU
  obtain ⟨hEint, hEavg⟩ := c16_negative_power_early_average_le_mass hκ hε hp
    ρ α hell u G hcal hu χ hχ hχc hχ0 hχ1 E hErep
  obtain ⟨s, hs, _, hsE⟩ := c5_exists_early_energy_le_average E (fun _ => True)
    hEint (ae_of_all _ fun _ => trivial)
  have hsI : s ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
  refine ⟨E, hEcont, hErep, ?_⟩
  intro t ht
  have htI : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hst : s < t := by linarith [hs.2, ht.1]
  have hb := c16_negative_power_interval_control hκ (by norm_num : (0 : ℝ) < 1) hε hp
    ρ α hell u G hcal hu χ hχ hχc L hL E s t hsI htI hst (hEincr s hsI t htI hst.le)
  have hm := c16_negative_power_mass_subinterval_le hκ hε hp ρ α hell u G hcal hu
    (Set.Ioo s t) (by intro q hq; exact ⟨lt_trans hsI.1 hq.1, lt_trans hq.2 htI.2⟩)
  have hmA := mul_le_mul_of_nonneg_left hm hA
  have hAM := mul_le_mul_of_nonneg_right hAB hM
  change E t ≤ (2 + B) * M
  change E t ≤ E s + A * _ at hb
  change A * _ ≤ A * M at hmA
  change _ ≤ M at hEavg
  nlinarith

/-- An early and a late time bracket the inner interval and control the cutoff
negative-half-power gradient with an exponent-independent coefficient. -/
theorem c17_negative_power_cutoff_gradient_interval_bound {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 1)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L^2) :
    ∃ s ∈ Set.Ioo (-1 : ℝ) (-1/2), ∃ t ∈ Set.Ioo (1/4 : ℝ) (1/2),
      (∫ q in s..t, ∫ x in sourceBall 0 1,
        χ x ^ 2 * euclideanSq ((-p/2 * Real.rpow (u (q,x)) (-p/2-1)) • G (q,x))) ≤
      ((2 + (2 / κ^3) * (L^2 * κ⁻¹)) * (2 * κ)⁻¹) *
        (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1, ρ z.2 * Real.rpow (u z) (-p)) := by
  let M : ℝ := ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
    ρ z.2 * Real.rpow (u z) (-p)
  let A : ℝ := (2*p/(κ^3*(p+1))) * (L^2 * κ⁻¹)
  let B : ℝ := 2 * κ * (p+1) / p
  have hM : 0 ≤ M := by
    apply integral_nonneg_of_ae
    filter_upwards [hu] with z hz
    exact mul_nonneg (hκ.le.trans (hell.2.2 z.2).1)
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
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
    ρ α hell u G hcal hu χ hχ hχc L hL E s t hsI htI hst (hEincr s hsI t htI hst.le)
  have hm := c16_negative_power_mass_subinterval_le hκ hε hp ρ α hell u G hcal hu
    (Set.Ioo s t) (by intro q hq; exact ⟨lt_trans hsI.1 hq.1, lt_trans hq.2 htI.2⟩)
  have hm' := mul_le_mul_of_nonneg_left hm hA
  have hbound : B * (∫ q in s..t, ∫ x in sourceBall 0 1,
      χ x ^ 2 * euclideanSq ((-p/2 * Real.rpow (u (q,x)) (-p/2-1)) • G (q,x))) ≤
      (2+A)*M := by
    dsimp [A, B, M] at *
    nlinarith
  have hdiv : (∫ q in s..t, ∫ x in sourceBall 0 1,
      χ x ^ 2 * euclideanSq ((-p/2 * Real.rpow (u (q,x)) (-p/2-1)) • G (q,x))) ≤
      ((2+A)*M)/B := by
    apply (le_div_iff₀ hB).2
    rw [mul_comm]
    exact hbound
  have hc := c17_negative_power_native_gradient_constant_le κ p L hκ hp
  refine ⟨s, hs, t, ht, ?_⟩
  change _ ≤ ((2 + (2 / κ^3) * (L^2 * κ⁻¹)) * (2 * κ)⁻¹) * M
  have hcoef : (2+A)/B ≤ (2 + (2 / κ^3) * (L^2 * κ⁻¹)) * (2 * κ)⁻¹ := hc
  calc
    _ ≤ ((2+A)*M)/B := hdiv
    _ = ((2+A)/B)*M := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hM

/-- The cutoff negative-half-power gradient is controlled on the later time slab. -/
theorem c17_negative_power_cutoff_gradient_slab_bound {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 1)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L^2) :
    (∫ z in Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 1,
      χ z.2 ^ 2 * euclideanSq ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z)) ≤
    ((2 + (2 / κ^3) * (L^2 * κ⁻¹)) * (2 * κ)⁻¹) *
      (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1, ρ z.2 * Real.rpow (u z) (-p)) := by
  obtain ⟨s, hs, t, ht, hb⟩ := c17_negative_power_cutoff_gradient_interval_bound
    hκ hε hp ρ α hell u G hcal hu χ hχ hχc hχU hχ0 hχ1 L hL
  have hst : s < t := by linarith [hs.2, ht.1]
  let Q : ℝ × Vec d → ℝ := fun z =>
    χ z.2 ^ 2 * euclideanSq ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z)
  let small : Set (ℝ × Vec d) := Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 1
  let large : Set (ℝ × Vec d) := Set.Ioo s t ×ˢ sourceBall 0 1
  have hsub : small ⊆ large := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    exact ⟨⟨by linarith [hs.2, hq.1], by linarith [hq.2, ht.1]⟩, hx⟩
  have hlarge : large ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1 := by
    intro z hz
    exact ⟨⟨lt_trans hs.1 hz.1.1, lt_trans hz.1.2 (lt_trans ht.2 (by norm_num))⟩, hz.2⟩
  have hi : IntegrableOn Q (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1) :=
    c16_negative_power_gradient_integrable hε hp ρ α u G hcal hu χ hχ hχc
  have hi' : IntegrableOn Q large := hi.mono_set hlarge
  have hprod : (volume.restrict (Set.Ioo s t)).prod (volume.restrict (sourceBall (0 : Vec d) 1)) =
      (volume : Measure (ℝ × Vec d)).restrict large := by
    rw [Measure.prod_restrict]
    rfl
  have hQ : (∫ z in small, Q z) ≤ ∫ q in s..t, ∫ x in sourceBall 0 1,
      χ x ^ 2 * euclideanSq ((-p/2 * Real.rpow (u (q,x)) (-p/2-1)) • G (q,x)) := by
    calc
      _ ≤ ∫ z in large, Q z := integral_mono_measure (Measure.restrict_mono hsub le_rfl)
        (ae_of_all _ fun z => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _)) hi'
      _ = _ := by
        rw [intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo, ← hprod]
        exact integral_prod _ (by rw [hprod]; exact hi')
  exact hQ.trans hb

/-- The cutoff-derivative error on the later slab is controlled by the full mass. -/
theorem c17_negative_power_cutoff_error_slab_bound {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L^2) :
    (∫ z in Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 1,
      Real.rpow (u z) (-p) * euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j))) ≤
    (L^2 * κ⁻¹) *
      (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1, ρ z.2 * Real.rpow (u z) (-p)) := by
  let small : Set (ℝ × Vec d) := Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 1
  let large : Set (ℝ × Vec d) := Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1
  let Q : ℝ × Vec d → ℝ := fun z => Real.rpow (u z) (-p) *
    euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j))
  have hsub : small ⊆ large := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    exact ⟨⟨by linarith [hq.1], by linarith [hq.2]⟩, hx⟩
  have hi : IntegrableOn Q large :=
    c16_negative_power_cutoff_error_integrable hε hp ρ α u G hcal hu χ hχ hχc
  have hQ : ∀ᵐ z ∂volume.restrict large, 0 ≤ Q z := by
    filter_upwards [hu] with z hz
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
      (PDE.vecNormSq_nonneg _)
  have hb := c16_negative_power_cutoff_error_le_mass hκ hε hp ρ α hell u G hcal hu χ hχ hχc L hL
  exact (integral_mono_measure (Measure.restrict_mono hsub le_rfl) hQ hi).trans hb

/-- A spatial cutoff preserves the literal negative-power weak gradient on
almost every caloric time slice. -/
theorem c17_negative_power_cutoff_gradient_slices
    {d : ℕ} {I : Set ℝ} {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (hU : IsOpen U) {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (hpos : ∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : IsSpatialTest U χ) :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => χ x * Real.rpow (u (t,x)) (-p))
        (fun x => χ x • ((-p * Real.rpow (u (t,x)) (-p-1)) • G (t,x)) +
          Real.rpow (u (t,x)) (-p) • (fun j => fderiv ℝ χ x (unitVector j))) ∧
      MemLp (fun x => χ x * Real.rpow (u (t,x)) (-p)) 2 (volume.restrict U) ∧
      MemLp (fun x => euclideanNorm (χ x • ((-p * Real.rpow (u (t,x)) (-p-1)) • G (t,x)) +
        Real.rpow (u (t,x)) (-p) • (fun j => fderiv ℝ χ x (unitVector j))))
        2 (volume.restrict U) := by
  obtain ⟨c, _, _, hslices⟩ := c20_weighted_caloric_negative_power_receipt
    hU hε hp ρ α u G hcal hpos
  filter_upwards [hslices] with t ht
  have hc : MemLp (fun _ : Vec d => c) 2 (volume.restrict U) := memLp_const c
  have hu : MemLp (fun x => Real.rpow (u (t,x)) (-p)) 2 (volume.restrict U) := by
    convert ht.1.add hc using 1
    ext x
    simp
  exact c13_native_cutoff_weak_gradient hU _ _ ht.2.2 hu ht.2.1 χ hχ

/-- The two cutoff energy terms have finite nonnegative-integral bounds on the
inner time slab, with constants independent of the power. -/
theorem c17_negative_power_cutoff_lintegral_bounds {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 1)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L^2) :
    let M := ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
      ρ z.2 * Real.rpow (u z) (-p)
    (∫⁻ z in Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 1,
      ENNReal.ofReal (χ z.2 ^ 2 * euclideanSq
        ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z))) ≤
      ENNReal.ofReal (((2 + (2 / κ^3) * (L^2 * κ⁻¹)) * (2 * κ)⁻¹) * M) ∧
    (∫⁻ z in Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 1,
      ENNReal.ofReal (Real.rpow (u z) (-p) *
        euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j)))) ≤
      ENNReal.ofReal ((L^2 * κ⁻¹) * M) := by
  let small : Set (ℝ × Vec d) := Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 1
  let large : Set (ℝ × Vec d) := Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1
  have hsub : small ⊆ large := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    exact ⟨⟨by linarith [hq.1], by linarith [hq.2]⟩, hx⟩
  have hpos := hu.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hiAfull : IntegrableOn (fun z => χ z.2 ^ 2 * euclideanSq
      ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z)) large :=
    c16_negative_power_gradient_integrable hε hp ρ α u G hcal hu χ hχ hχc
  have hiBfull : IntegrableOn (fun z => Real.rpow (u z) (-p) *
      euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j))) large :=
    c16_negative_power_cutoff_error_integrable hε hp ρ α u G hcal hu χ hχ hχc
  have hiA := hiAfull.mono_set hsub
  have hiB := hiBfull.mono_set hsub
  have hnA : ∀ᵐ z ∂volume.restrict small, 0 ≤ χ z.2 ^ 2 * euclideanSq
      ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z) :=
    ae_of_all _ fun z => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _)
  have hnB : ∀ᵐ z ∂volume.restrict small, 0 ≤ Real.rpow (u z) (-p) *
      euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j)) := by
    filter_upwards [hpos] with z hz
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
      (PDE.vecNormSq_nonneg _)
  constructor
  · rw [← ofReal_integral_eq_lintegral_ofReal hiA hnA]
    exact ENNReal.ofReal_le_ofReal (c17_negative_power_cutoff_gradient_slab_bound
      hκ hε hp ρ α hell u G hcal hu χ hχ hχc hχU hχ0 hχ1 L hL)
  · rw [← ofReal_integral_eq_lintegral_ofReal hiB hnB]
    exact ENNReal.ofReal_le_ofReal (c17_negative_power_cutoff_error_slab_bound
      hκ hε hp ρ α hell u G hcal hu χ hχ hχc L hL)

/-- The cutoff half-power has uniformly controlled weighted slice mass. -/
theorem c17_negative_power_cutoff_slice_lintegral_bound {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 1)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L^2) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-1/4 : ℝ) (1/4)),
      (∫⁻ x in sourceBall 0 1, ENNReal.ofReal (ρ x) *
        ‖χ x * Real.rpow (u (t,x)) (-p/2)‖ₑ ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((2 + (2 / κ^3) * (L^2 * κ⁻¹)) *
        (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
          ρ z.2 * Real.rpow (u z) (-p))) := by
  obtain ⟨E, _, hErep, hEbound⟩ := c17_negative_power_cutoff_mass_bound hκ hε hp
    ρ α hell u G hcal hu χ hχ hχc hχU hχ0 hχ1 L hL
  have hi := c16_negative_power_literal_mass_integrable hκ hε hp ρ α hell u G hcal hu χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hi hu
  have htime : Set.Ioo (-1/4 : ℝ) (1/4) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset htime hi.prod_right_ae,
    ae_restrict_of_ae_restrict_of_subset htime (Measure.ae_ae_of_ae_prod hu),
    ae_restrict_of_ae_restrict_of_subset htime hErep,
    ae_restrict_mem measurableSet_Ioo] with t htint htpos htrep ht
  have hn : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) 1),
      0 ≤ ρ x * χ x ^ 2 * Real.rpow (u (t,x)) (-p) := by
    filter_upwards [htpos] with x hx
    exact mul_nonneg (mul_nonneg (hκ.le.trans (hell.2.2 x).1) (sq_nonneg _))
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hx)) _)
  calc
    _ = ∫⁻ x in sourceBall 0 1, ENNReal.ofReal
        (ρ x * χ x ^ 2 * Real.rpow (u (t,x)) (-p)) := by
      apply lintegral_congr_ae
      filter_upwards [htpos] with x hx
      rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
        ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs,
        ← ENNReal.ofReal_mul (hκ.le.trans (hell.2.2 x).1)]
      congr 1
      have hpow : (Real.rpow (u (t,x)) (-p/2)) ^ 2 = Real.rpow (u (t,x)) (-p) := by
        change (u (t,x) ^ (-p/2 : ℝ)) ^ (2 : ℕ) = u (t,x) ^ (-p : ℝ)
        rw [← Real.rpow_mul_natCast (le_of_lt (lt_of_lt_of_le hε hx))]
        congr 1
        ring
      rw [mul_pow, hpow]
      ring
    _ = ENNReal.ofReal (∫ x in sourceBall 0 1,
        ρ x * χ x ^ 2 * Real.rpow (u (t,x)) (-p)) :=
      (ofReal_integral_eq_lintegral_ofReal htint hn).symm
    _ ≤ _ := by rw [← htrep]; exact ENNReal.ofReal_le_ofReal (hEbound t ht)

/-- The literal cutoff half-power gradient has uniformly bounded coefficient
energy on the inner time slab. -/
theorem c17_negative_power_cutoff_coefficient_energy {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 1)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L^2) :
    let M := ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
      ρ z.2 * Real.rpow (u z) (-p)
    let J : ℝ × Vec d → Vec d := fun z =>
      χ z.2 • ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z) +
        Real.rpow (u z) (-p/2) • (fun j => fderiv ℝ χ z.2 (unitVector j))
    (∫⁻ z in Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 1,
      ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z))) ≤
      ENNReal.ofReal (2 * κ⁻¹) *
        (ENNReal.ofReal (((2 + (2 / κ^3) * (L^2 * κ⁻¹)) * (2 * κ)⁻¹) * M) +
          ENNReal.ofReal ((L^2 * κ⁻¹) * M)) := by
  let small : Set (ℝ × Vec d) := Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 1
  let large : Set (ℝ × Vec d) := Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1
  have hsub : small ⊆ large := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    exact ⟨⟨by linarith [hq.1], by linarith [hq.2]⟩, hx⟩
  have hpos := hu.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hiAfull : IntegrableOn (fun z => χ z.2 ^ 2 * euclideanSq
      ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z)) large :=
    c16_negative_power_gradient_integrable hε hp ρ α u G hcal hu χ hχ hχc
  have hiBfull : IntegrableOn (fun z => Real.rpow (u z) (-p) *
      euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j))) large :=
    c16_negative_power_cutoff_error_integrable hε hp ρ α u G hcal hu χ hχ hχc
  have hiA := hiAfull.mono_set hsub
  have hiB := hiBfull.mono_set hsub
  have heq : ∀ᵐ z ∂volume.restrict small,
      (Real.rpow (u z) (-p/2)) ^ 2 *
          euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j)) =
        Real.rpow (u z) (-p) *
          euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j)) := by
    filter_upwards [hpos] with z hz
    congr 1
    change (u z ^ (-p/2 : ℝ)) ^ (2 : ℕ) = u z ^ (-p : ℝ)
    rw [← Real.rpow_mul_natCast (le_of_lt (lt_of_lt_of_le hε hz))]
    congr 1
    ring
  obtain ⟨hA, hB⟩ := c17_negative_power_cutoff_lintegral_bounds hκ hε hp
    ρ α hell u G hcal hu χ hχ hχc hχU hχ0 hχ1 L hL
  have hmB := hiB.aestronglyMeasurable.aemeasurable.ennreal_ofReal.congr
    (heq.mono fun _ h => congrArg ENNReal.ofReal h.symm)
  have hb' : (∫⁻ z in small, ENNReal.ofReal ((Real.rpow (u z) (-p/2)) ^ 2 *
      euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j)))) ≤
      ENNReal.ofReal ((L^2 * κ⁻¹) *
        (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
          ρ z.2 * Real.rpow (u z) (-p))) := by
    rw [lintegral_congr_ae (heq.mono fun _ h => congrArg ENNReal.ofReal h)]
    exact hB
  exact c9_cutoff_coefficient_energy_lintegral κ hκ ρ α hell (volume.restrict small)
    (fun z => χ z.2) (fun z => Real.rpow (u z) (-p/2))
    (fun z => (-p/2 * Real.rpow (u z) (-p/2-1)) • G z)
    (fun z j => fderiv ℝ χ z.2 (unitVector j)) _ _
    hiA.aestronglyMeasurable.aemeasurable.ennreal_ofReal hmB hA hb'

/-- The literal cutoff half-power and its Euclidean gradient have spacetime
quadratic regularity on the full caloric cylinder. -/
theorem c17_negative_half_power_cutoff_spacetime_memLp {d : ℕ} {ε p : ℝ}
    (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    let μ := volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)
    let V : ℝ × Vec d → ℝ := fun z => χ z.2 * Real.rpow (u z) (-p/2)
    let J : ℝ × Vec d → Vec d := fun z =>
      χ z.2 • ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z) +
        Real.rpow (u z) (-p/2) • (fun j => fderiv ℝ χ z.2 (unitVector j))
    MemLp V 2 μ ∧ AEStronglyMeasurable J μ ∧
      MemLp (fun z => euclideanNorm (J z)) 2 μ := by
  let μ := volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)
  let H : ℝ × Vec d → Vec d := fun z => (-p/2 * Real.rpow (u z) (-p/2-1)) • G z
  have hHm : AEStronglyMeasurable H μ :=
    ((hcal.1.aestronglyMeasurable.aemeasurable.pow_const (-p/2-1)).aestronglyMeasurable.const_mul (-p/2)).smul hcal.2.1
  have hH : MemLp (fun z => euclideanNorm (H z)) 2 μ :=
    c20_weighted_caloric_negative_half_power_gradient_memLp ρ α u G hcal ε p hε hp hu
  have hpowm : AEStronglyMeasurable (fun z => Real.rpow (u z) (-p/2)) μ :=
    (hcal.1.aestronglyMeasurable.aemeasurable.pow_const (-p/2)).aestronglyMeasurable
  have hpowsq := c16_negative_power_integrable hε hp ρ α u G hcal hu
  have hpow : MemLp (fun z => Real.rpow (u z) (-p/2)) 2 μ := by
    apply (memLp_two_iff_integrable_sq hpowm).2
    apply hpowsq.congr
    filter_upwards [hu] with z hz
    change u z ^ (-p : ℝ) = (u z ^ (-p/2 : ℝ)) ^ (2 : ℕ)
    rw [← Real.rpow_mul_natCast (le_of_lt (lt_of_lt_of_le hε hz))]
    congr 1
    ring
  have hχtop : MemLp (fun z : ℝ × Vec d => χ z.2) ⊤ μ := by
    obtain ⟨B, hB, hb⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
    exact memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable B
      (ae_of_all _ fun z => hb _ ⟨z.2, rfl⟩)
  have hDtop (j : Fin d) : MemLp (fun z : ℝ × Vec d =>
      fderiv ℝ χ z.2 (unitVector j)) ⊤ μ := by
    have hd : Continuous (fun x : Vec d => fderiv ℝ χ x (unitVector j)) :=
      (hχ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
    obtain ⟨B, hB, hb⟩ := ((hχc.fderiv_apply ℝ (unitVector j)).isCompact_range hd).isBounded.exists_pos_norm_le
    exact memLp_top_of_bound (hd.comp continuous_snd).aestronglyMeasurable B
      (ae_of_all _ fun z => hb _ ⟨z.2, rfl⟩)
  have hcoord (j : Fin d) : MemLp (fun z => H z j) 2 μ := by
    apply hH.mono' ((continuous_apply j).comp_aestronglyMeasurable hHm)
    apply ae_of_all
    intro z
    simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
      (PiLp.norm_apply_le (WithLp.toLp 2 (H z)) j)
  have hJcoord (j : Fin d) : MemLp (fun z => χ z.2 * H z j +
      Real.rpow (u z) (-p/2) * fderiv ℝ χ z.2 (unitVector j)) 2 μ := by
    have ha : MemLp (fun z => χ z.2 * H z j) 2 μ := by
      simpa only [mul_comm] using (hcoord j).fun_mul hχtop
    exact ha.add (hpow.fun_mul (hDtop j))
  have hJm : AEStronglyMeasurable (fun z => χ z.2 • H z +
      Real.rpow (u z) (-p/2) • (fun j => fderiv ℝ χ z.2 (unitVector j))) μ :=
    ((hχ.continuous.comp continuous_snd).aestronglyMeasurable.smul hHm).add
      (hpowm.smul ((continuous_pi fun j =>
        ((hχ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)).comp
          continuous_snd).aestronglyMeasurable))
  have hJ : MemLp (fun z => (WithLp.toLp 2 (χ z.2 • H z +
      Real.rpow (u z) (-p/2) • (fun j => fderiv ℝ χ z.2 (unitVector j))) :
      EuclideanSpace ℝ (Fin d))) 2 μ := by
    apply memLp_piLp_iff.mpr
    intro j
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hJcoord j
  refine ⟨?_, hJm, ?_⟩
  · simpa only [mul_comm] using hpow.fun_mul hχtop
  · simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using hJ.norm

/-- Native weighted Sobolev applied to the literal cutoff half-power. -/
theorem c17_negative_half_power_cutoff_native_sobolev (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    ∀ ε p : ℝ, 0 < ε → 0 < p →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
    ∀ (χ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
    tsupport χ ⊆ sourceBall 0 1 → (∀ x, 0 ≤ χ x) → (∀ x, χ x ≤ 1) →
    ∀ L : ℝ, (∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L^2) →
    let V : ℝ × Vec d → ℝ := fun z => χ z.2 * Real.rpow (u z) (-p/2)
    let J : ℝ × Vec d → Vec d := fun z =>
      χ z.2 • ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z) +
        Real.rpow (u z) (-p/2) • (fun j => fderiv ℝ χ z.2 (unitVector j))
    (∫⁻ t in Set.Ioo (-1/4 : ℝ) (1/4), ∫⁻ x in sourceBall 0 1,
      ENNReal.ofReal (ρ x) * ‖V (t,x)‖ₑ ^ (2 * ((d : ℝ)+2) / d)) ≤
    C * (ENNReal.ofReal ((2 + (2 / κ^3) * (L^2 * κ⁻¹)) *
      (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
        ρ z.2 * Real.rpow (u z) (-p)))) ^ (2 / (d : ℝ)) *
      (∫⁻ t in Set.Ioo (-1/4 : ℝ) (1/4), ∫⁻ x in sourceBall 0 1,
        ENNReal.ofReal (dot ((α x).mulVec (J (t,x))) (J (t,x)))) := by
  obtain ⟨C, hC, hsob⟩ := c8_native_weighted_parabolic_sobolev d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal ε p hε hp hpos χ hχ hχc hχU hχ0 hχ1 L hL
  let U : Set (Vec d) := sourceBall 0 1
  let I : Set ℝ := Set.Ioo (-1/4 : ℝ) (1/4)
  let V : ℝ × Vec d → ℝ := fun z => χ z.2 * Real.rpow (u z) (-p/2)
  let J : ℝ × Vec d → Vec d := fun z =>
    χ z.2 • ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z) +
      Real.rpow (u z) (-p/2) • (fun j => fderiv ℝ χ z.2 (unitVector j))
  have hI : I ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsub : I ×ˢ U ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ U := Set.prod_mono hI (Set.Subset.refl U)
  have hμ := Measure.restrict_mono hsub (le_rfl : volume ≤ volume)
  obtain ⟨hV, hJm, hJ⟩ := c17_negative_half_power_cutoff_spacetime_memLp
    hε hp ρ α u G hcal hpos χ hχ hχc
  have hU : IsOpen U := c17_isOpen_sourceBall 0 1
  letI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr (c18_sourceBall_measure_ne_top 0 1)
  have hweak := c17_negative_power_cutoff_gradient_slices hU hε (by linarith : 0 < p/2)
    ρ α u G hcal hpos χ ⟨hχ, hχc, hχU⟩
  have hweak' : ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => V (t,x)) (fun x => J (t,x)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hI hweak] with t ht
    have he : -(p/2) = -p/2 := by ring
    simpa only [V, J, he] using ht.1
  have hsupp : ∀ᵐ t ∂volume.restrict I, ∀ x ∈ U, x ∉ tsupport χ → V (t,x) = 0 := by
    exact ae_of_all _ fun t x hx hxs => by simp [V, image_eq_zero_of_notMem_tsupport hxs]
  have hmass := c17_negative_power_cutoff_slice_lintegral_bound hκ hε hp
    ρ α hell u G hcal hpos χ hχ hχc hχU hχ0 hχ1 L hL
  exact hsob ρ α hell I U measurableSet_Ioo hU V J
    (hV.mono_measure hμ) (hJm.mono_measure hμ) (hJ.mono_measure hμ) hweak'
    (tsupport χ) hχc hχU hsupp _ hmass

/-- The measurable coefficient energy admits the product-space Tonelli identity. -/
theorem c17_coefficient_energy_tonelli {d : ℕ} (I : Set ℝ) (U : Set (Vec d))
    (α : Vec d → Mat d) (hα : Measurable α) (J : ℝ × Vec d → Vec d)
    (hJ : AEStronglyMeasurable J (volume.restrict (I ×ˢ U))) :
    (∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (dot ((α x).mulVec (J (t,x))) (J (t,x)))) =
    ∫⁻ z in I ×ˢ U, ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z)) := by
  have hd : Continuous (fun s : Vec d × Vec d => dot s.1 s.2) :=
    continuous_fst.dotProduct continuous_snd
  have hf : Continuous (fun s : Mat d × Vec d => s.1.mulVec s.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hF : Continuous (fun s : Mat d × Vec d => dot (s.1.mulVec s.2) s.2) :=
    hd.comp (hf.prodMk continuous_snd)
  have hm : AEMeasurable (fun z : ℝ × Vec d =>
      ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z)))
      (volume.restrict (I ×ˢ U)) :=
    (hF.measurable.comp_aemeasurable
      (((hα.comp measurable_snd).aemeasurable).prodMk hJ.aemeasurable)).ennreal_ofReal
  rw [Measure.volume_eq_prod] at hm ⊢
  exact (setLIntegral_prod _ hm).symm

/-- The native Sobolev coefficient-energy term obeys the actual cutoff estimate. -/
theorem c17_negative_half_power_cutoff_iterated_energy_bound {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 1)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L^2) :
    let M := ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
      ρ z.2 * Real.rpow (u z) (-p)
    let J : ℝ × Vec d → Vec d := fun z =>
      χ z.2 • ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z) +
        Real.rpow (u z) (-p/2) • (fun j => fderiv ℝ χ z.2 (unitVector j))
    (∫⁻ t in Set.Ioo (-1/4 : ℝ) (1/4), ∫⁻ x in sourceBall 0 1,
      ENNReal.ofReal (dot ((α x).mulVec (J (t,x))) (J (t,x)))) ≤
      ENNReal.ofReal (2 * κ⁻¹) *
        (ENNReal.ofReal (((2 + (2 / κ^3) * (L^2 * κ⁻¹)) * (2 * κ)⁻¹) * M) +
          ENNReal.ofReal ((L^2 * κ⁻¹) * M)) := by
  let I : Set ℝ := Set.Ioo (-1/4 : ℝ) (1/4)
  let U : Set (Vec d) := sourceBall 0 1
  let J : ℝ × Vec d → Vec d := fun z =>
    χ z.2 • ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z) +
      Real.rpow (u z) (-p/2) • (fun j => fderiv ℝ χ z.2 (unitVector j))
  have hI : I ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsub : I ×ˢ U ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ U := Set.prod_mono hI (Set.Subset.refl U)
  obtain ⟨_, hJm, _⟩ := c17_negative_half_power_cutoff_spacetime_memLp
    hε hp ρ α u G hcal hu χ hχ hχc
  have hα : Measurable α := by
    convert hell.2.1 using 1 <;> exact BorelSpace.measurable_eq.trans BorelSpace.measurable_eq.symm
  change (∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal
    (dot ((α x).mulVec (J (t,x))) (J (t,x)))) ≤ _
  rw [c17_coefficient_energy_tonelli I U α hα J
    (hJm.mono_measure (Measure.restrict_mono hsub le_rfl))]
  exact c17_negative_power_cutoff_coefficient_energy hκ hε hp
    ρ α hell u G hcal hu χ hχ hχc hχU hχ0 hχ1 L hL

/-- Uniform density control converts the negative-power mass to the inverse moment. -/
theorem c17_negative_power_weighted_mass_le_inverse_moment
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (κ p : ℝ)
    (hκ : 0 < κ) (hp : 0 < p) (ρ u : X → ℝ)
    (hρ : ∀ x, κ ≤ ρ x ∧ ρ x ≤ κ⁻¹) (hu : ∀ᵐ x ∂μ, 0 ≤ u x) :
    ENNReal.ofReal (∫ x, ρ x * Real.rpow (u x) (-p) ∂μ) ≤
      ENNReal.ofReal κ⁻¹ * ∫⁻ x, ‖(u x)⁻¹‖ₑ ^ p ∂μ := by
  by_cases hi : Integrable (fun x => ρ x * Real.rpow (u x) (-p)) μ
  · have hn : ∀ᵐ x ∂μ, 0 ≤ ρ x * Real.rpow (u x) (-p) := by
      filter_upwards [hu] with x hx
      exact mul_nonneg (hκ.le.trans (hρ x).1) (Real.rpow_nonneg hx _)
    rw [ofReal_integral_eq_lintegral_ofReal hi hn]
    calc
      _ = ∫⁻ x, ENNReal.ofReal (ρ x) * ‖(u x)⁻¹‖ₑ ^ p ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hu] with x hx
        have heq : Real.rpow (u x) (-p) = Real.rpow ((u x)⁻¹) p := by
          change (u x) ^ (-p : ℝ) = ((u x)⁻¹) ^ p
          exact Real.rpow_neg_eq_inv_rpow _ _
        rw [ENNReal.ofReal_mul (hκ.le.trans (hρ x).1), heq]
        change ENNReal.ofReal (ρ x) * ENNReal.ofReal (((u x)⁻¹) ^ p) = _
        rw [← ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hx) hp.le,
          Real.enorm_eq_ofReal (inv_nonneg.mpr hx)]
      _ ≤ _ := (c8_density_lintegral_bounds μ κ hκ ρ hρ _).1
  · change ¬ Integrable (fun x => ρ x * (u x) ^ (-p : ℝ)) μ at hi
    change ENNReal.ofReal (∫ x, ρ x * (u x) ^ (-p : ℝ) ∂μ) ≤ _
    rw [integral_undef hi, ENNReal.ofReal_zero]
    exact zero_le

/-- The actual inverse-power moment on the inner cylinder is controlled by the
native Sobolev estimate and the actual cutoff energy. -/
theorem c17_negative_power_cutoff_moment_gain (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    ∀ ε p : ℝ, 0 < ε → 0 < p →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
    ∀ (χ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
    tsupport χ ⊆ sourceBall 0 1 → (∀ x, 0 ≤ χ x) → (∀ x, χ x ≤ 1) →
    (∀ x ∈ sourceBall 0 (1/2), χ x = 1) →
    ∀ L : ℝ, (∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L^2) →
    let M := ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
      ρ z.2 * Real.rpow (u z) (-p)
    (∫⁻ z in Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 (1/2),
      ENNReal.ofReal ((u z)⁻¹) ^ (p * (((d : ℝ)+2)/d))) ≤
    ENNReal.ofReal κ⁻¹ * (C *
      (ENNReal.ofReal ((2 + (2 / κ^3) * (L^2 * κ⁻¹)) * M)) ^ (2 / (d : ℝ)) *
      (ENNReal.ofReal (2 * κ⁻¹) *
        (ENNReal.ofReal (((2 + (2 / κ^3) * (L^2 * κ⁻¹)) * (2 * κ)⁻¹) * M) +
          ENNReal.ofReal ((L^2 * κ⁻¹) * M)))) := by
  obtain ⟨C, hC, hsob⟩ := c17_negative_half_power_cutoff_native_sobolev d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal ε p hε hp hu χ hχ hχc hχU hχ0 hχ1 hone L hL
  let I : Set ℝ := Set.Ioo (-1/4 : ℝ) (1/4)
  let U : Set (Vec d) := sourceBall 0 1
  let S : Set (ℝ × Vec d) := I ×ˢ sourceBall 0 (1/2)
  let V : ℝ × Vec d → ℝ := fun z => χ z.2 * Real.rpow (u z) (-p/2)
  have hball : sourceBall (0 : Vec d) (1/2) ⊆ U := by
    intro x hx
    change euclideanNorm (x - 0) < 1/2 at hx
    change euclideanNorm (x - 0) < 1
    linarith
  have hSI : S ⊆ I ×ˢ U := Set.prod_mono (Set.Subset.refl I) hball
  have hI : I ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlarge : S ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ U := Set.prod_mono hI hball
  have hs : MeasurableSet S := measurableSet_Ioo.prod (c17_isOpen_sourceBall 0 (1/2)).measurableSet
  have hpos := hu.filter_mono (ae_mono (Measure.restrict_mono hlarge le_rfl))
  have hV := (c17_negative_half_power_cutoff_spacetime_memLp hε hp ρ α u G hcal hu χ hχ hχc).1
  have hsub : I ×ˢ U ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ U := Set.prod_mono hI (Set.Subset.refl U)
  have hVm := (hV.mono_measure (Measure.restrict_mono hsub le_rfl)).aestronglyMeasurable
  have hm : AEMeasurable (fun z : ℝ × Vec d => ENNReal.ofReal (ρ z.2) *
      ‖V z‖ₑ ^ (2 * ((d : ℝ)+2) / d)) (volume.restrict (I ×ˢ U)) :=
    (ENNReal.measurable_ofReal.comp (hell.1.comp measurable_snd)).aemeasurable.mul
      (hVm.aemeasurable.enorm.pow_const _)
  have hprod : volume.restrict (I ×ˢ U) = (volume.restrict I).prod (volume.restrict U) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hmain := hsob ρ α hell u G hcal ε p hε hp hu χ hχ hχc hχU hχ0 hχ1 L hL
  have henergy := c17_negative_half_power_cutoff_iterated_energy_bound hκ hε hp
    ρ α hell u G hcal hu χ hχ hχc hχU hχ0 hχ1 L hL
  let M : ℝ := ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
    ρ z.2 * Real.rpow (u z) (-p)
  let A : ℝ≥0∞ := ENNReal.ofReal ((2 + (2 / κ^3) * (L^2 * κ⁻¹)) * M)
  let E : ℝ≥0∞ := ENNReal.ofReal (2 * κ⁻¹) *
    (ENNReal.ofReal (((2 + (2 / κ^3) * (L^2 * κ⁻¹)) * (2 * κ)⁻¹) * M) +
      ENNReal.ofReal ((L^2 * κ⁻¹) * M))
  have hweighted : (∫⁻ z in I ×ˢ U, ENNReal.ofReal (ρ z.2) *
      ‖V z‖ₑ ^ (2 * ((d : ℝ)+2) / d)) ≤ C * A ^ (2 / (d : ℝ)) * E := by
    rw [hprod] at hm ⊢
    rw [lintegral_prod _ hm]
    exact hmain.trans (by gcongr)
  calc
    (∫⁻ z in S, ENNReal.ofReal ((u z)⁻¹) ^ (p * (((d : ℝ)+2)/d))) =
        ∫⁻ z in S, ‖V z‖ₑ ^ (2 * ((d : ℝ)+2) / d) := by
      apply lintegral_congr_ae
      filter_upwards [hpos, ae_restrict_mem hs] with z hz hzS
      have hnonneg : 0 ≤ u z := (lt_of_lt_of_le hε hz).le
      have heq : Real.rpow (u z) (-p/2) = Real.rpow ((u z)⁻¹) (p/2) := by
        change (u z) ^ (-p/2 : ℝ) = ((u z)⁻¹) ^ (p/2 : ℝ)
        rw [← Real.rpow_neg_eq_inv_rpow]
        congr 1
        ring
      dsimp only [V]
      rw [hone z.2 hzS.2, one_mul, heq, Real.enorm_eq_ofReal_abs]
      exact (PDE.Parabolic.LocalMax.ofReal_half_pow_rpow (d := d) (inv_nonneg.mpr hnonneg) hp.le).symm
    _ ≤ ∫⁻ z in I ×ˢ U, ‖V z‖ₑ ^ (2 * ((d : ℝ)+2) / d) := lintegral_mono_set hSI
    _ ≤ ENNReal.ofReal κ⁻¹ * ∫⁻ z in I ×ˢ U, ENNReal.ofReal (ρ z.2) *
        ‖V z‖ₑ ^ (2 * ((d : ℝ)+2) / d) :=
      (c8_density_lintegral_bounds (volume.restrict (I ×ˢ U)) κ hκ (fun z => ρ z.2)
        (fun z => ⟨(hell.2.2 z.2).1, (hell.2.2 z.2).2.1⟩) _).2
    _ ≤ _ := by
      change ENNReal.ofReal κ⁻¹ * _ ≤ ENNReal.ofReal κ⁻¹ * (C * A ^ (2 / (d : ℝ)) * E)
      gcongr


/-- The fixed cutoff turns the energy estimate into a homogeneous inverse-moment gain. -/
theorem c17_negative_power_unit_moment_gain (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ K A E : ℝ≥0∞, K ≠ ⊤ ∧ A ≠ ⊤ ∧ E ≠ ⊤ ∧
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    ∀ ε p : ℝ, 0 < ε → 0 < p →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
    (∫⁻ z in Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 (1/2),
      ENNReal.ofReal ((u z)⁻¹) ^ (p * (((d : ℝ)+2)/d))) ≤
    K * (A * (∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
      ‖(u z)⁻¹‖ₑ ^ p)) ^ (2 / (d : ℝ)) *
      (E * (∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
      ‖(u z)⁻¹‖ₑ ^ p)) := by
  obtain ⟨C, hC, hgain⟩ := c17_negative_power_cutoff_moment_gain d hd κ hκ
  let a : ℝ := 2 + (2 / κ^3) * ((64 : ℝ)^2 * κ⁻¹)
  let b : ℝ := a * (2 * κ)⁻¹
  let c : ℝ := (64 : ℝ)^2 * κ⁻¹
  let D : ℝ≥0∞ := ENNReal.ofReal κ⁻¹
  let B : ℝ≥0∞ := ENNReal.ofReal (2 * κ⁻¹)
  let K : ℝ≥0∞ := D * C
  let A : ℝ≥0∞ := ENNReal.ofReal a * D
  let E : ℝ≥0∞ := B * (ENNReal.ofReal b + ENNReal.ofReal c) * D
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨K, A, E, ?_, ?_, ?_, ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)) ENNReal.ofReal_ne_top
  intro ρ α hell u G hcal ε p hε hp hu
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
  let M : ℝ := ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
    ρ z.2 * Real.rpow (u z) (-p)
  let N : ℝ≥0∞ := ∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1, ‖(u z)⁻¹‖ₑ ^ p
  have hmass : ENNReal.ofReal M ≤ D * N := by
    apply c17_negative_power_weighted_mass_le_inverse_moment _ κ p hκ hp
    · intro z
      exact ⟨(hell.2.2 z.2).1, (hell.2.2 z.2).2.1⟩
    · filter_upwards [hu] with z hz
      exact hε.le.trans hz
  have h := hgain ρ α hell u G hcal ε p hε hp hu χ hχ hχc hχU hχ0 hχ1 hone 64 hgrad
  change _ ≤ D * (C * ENNReal.ofReal (a * M) ^ (2 / (d : ℝ)) *
    (B * (ENNReal.ofReal (b * M) + ENNReal.ofReal (c * M)))) at h
  rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb, ENNReal.ofReal_mul hc] at h
  calc
    _ ≤ D * (C * (ENNReal.ofReal a * (D * N)) ^ (2 / (d : ℝ)) *
      (B * (ENNReal.ofReal b * (D * N) + ENNReal.ofReal c * (D * N)))) :=
      h.trans (by gcongr)
    _ = K * (A * N) ^ (2 / (d : ℝ)) * (E * N) := by
      dsimp [K, A, E]
      rw [← add_mul]
      ac_rfl


/-- Unit-scale negative-power Sobolev gain from the actual caloric energy. -/
theorem c17_negative_power_sobolev_gain_from_energy
 (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
 ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
 IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
 IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
 ∀ ε p : ℝ, 0 < ε → 0 < p →
 (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
 eLpNorm (fun z => (u z)⁻¹) (ENNReal.ofReal (p * (((d : ℝ)+2)/d)))
  (volume.restrict (Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
 (C * ENNReal.ofReal ((1+p)^2)) ^ (1/p) *
 eLpNorm (fun z => (u z)⁻¹) (ENNReal.ofReal p)
  (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1)) := by
  obtain ⟨K, A, E, hK, hA, hE, hgain⟩ := c17_negative_power_unit_moment_gain d hd κ hκ
  let s : ℝ := 2 / (d : ℝ)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hq : ((d : ℝ)+2)/d = 1+s := by dsimp [s]; field_simp
  let T : ℝ≥0∞ := K * A ^ s * E
  let C : ℝ≥0∞ := max 1 T
  have hT : T ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top hK (ENNReal.rpow_ne_top_of_nonneg hs hA)) hE
  have hC : C ≠ ⊤ := (max_lt_iff.mpr ⟨by simp, lt_top_iff_ne_top.mpr hT⟩).ne
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal ε p hε hp hu
  let μ := volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)
  let ν := volume.restrict (Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall (0 : Vec d) (1/2))
  have hI : Set.Ioo (-1/4 : ℝ) (1/4) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hU : sourceBall (0 : Vec d) (1/2) ⊆ sourceBall 0 1 := by
    intro x hx
    change euclideanNorm (x - 0) < 1/2 at hx
    change euclideanNorm (x - 0) < 1
    linarith
  have hposν : ∀ᵐ z ∂ν, ε ≤ u z :=
    hu.filter_mono (ae_mono (Measure.restrict_mono (Set.prod_mono hI hU) le_rfl))
  have hvμ : AEStronglyMeasurable (fun z => (u z)⁻¹) μ :=
    hcal.1.aestronglyMeasurable.aemeasurable.inv.aestronglyMeasurable
  have hvν : AEStronglyMeasurable (fun z => (u z)⁻¹) ν :=
    hvμ.mono_measure (Measure.restrict_mono_set volume (Set.prod_mono hI hU))
  have hvμ0 : ∀ᵐ z ∂μ, 0 ≤ (u z)⁻¹ := by
    filter_upwards [hu] with z hz
    exact inv_nonneg.mpr (hε.le.trans hz)
  have hvν0 : ∀ᵐ z ∂ν, 0 ≤ (u z)⁻¹ := by
    filter_upwards [hposν] with z hz
    exact inv_nonneg.mpr (hε.le.trans hz)
  have hmomentμ : (∫⁻ z, ENNReal.ofReal ((u z)⁻¹) ^ p ∂μ) =
      ∫⁻ z, ‖(u z)⁻¹‖ₑ ^ p ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hvμ0] with z hz
    rw [Real.enorm_eq_ofReal hz]
  have hmom : (∫⁻ z, ENNReal.ofReal ((u z)⁻¹) ^ (p * (1+s)) ∂ν) ≤
      K * (A * (∫⁻ z, ENNReal.ofReal ((u z)⁻¹) ^ p ∂μ)) ^ s *
        (E * (∫⁻ z, ENNReal.ofReal ((u z)⁻¹) ^ p ∂μ)) := by
    rw [hmomentμ, ← hq]
    exact hgain ρ α hell u G hcal ε p hε hp hu
  have hnorm := c11_moser_norm_step_of_nonnegative_moment_gain μ ν (fun z => (u z)⁻¹)
    hvμ hvν hvμ0 hvν0 p s hp hs K A E hmom
  have hr : 0 ≤ 1 / (p * (1+s)) := by positivity
  have hrle : 1 / (p * (1+s)) ≤ 1/p := by
    apply one_div_le_one_div_of_le hp
    nlinarith
  have hc1 : 1 ≤ C := le_max_left _ _
  have hTC : T ≤ C := le_max_right _ _
  have hpp : 1 ≤ ENNReal.ofReal ((1+p)^2) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg p]
  have hmul : C ≤ C * ENNReal.ofReal ((1+p)^2) := by
    calc
      C = C * 1 := by simp
      _ ≤ _ := by gcongr
  have hconst : T ^ (1 / (p * (1+s))) ≤
      (C * ENNReal.ofReal ((1+p)^2)) ^ (1/p) := by
    calc
      _ ≤ C ^ (1 / (p * (1+s))) := ENNReal.rpow_le_rpow hTC hr
      _ ≤ C ^ (1/p) := ENNReal.rpow_le_rpow_of_exponent_le hc1 hrle
      _ ≤ _ := ENNReal.rpow_le_rpow hmul (by positivity)
  rw [hq]
  exact hnorm.trans (by change T ^ _ * _ ≤ _; gcongr)

end EinsteinFull.Calculus
