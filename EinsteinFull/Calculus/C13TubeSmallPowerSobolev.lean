import EinsteinFull.Calculus.C11TubeWeightedLocalMax

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- Conditional small-power gain from the literal cutoff power and its weak gradient.
The slice mass, coefficient energy, and functional regularity are separate inputs. -/
theorem c13_small_power_cutoff_sobolev_gain (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (I : Set ℝ) (U : Set (Vec d)),
    MeasurableSet I → IsOpen U →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    ∀ (η : ℝ × Vec d → ℝ),
    ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
    (∀ t x, x ∉ K → η (t,x) = 0) →
    ∀ S : Set (ℝ × Vec d), MeasurableSet S → S ⊆ I ×ˢ U →
    (∀ z ∈ S, η z = 1) →
    ∀ p ε : ℝ, 0 < p → 0 < ε →
    (∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) →
    ∀ A E : ℝ≥0∞,
    let v : ℝ × Vec d → ℝ := fun z => η z * (u z) ^ (p / 2)
    let J : ℝ × Vec d → Vec d := fun z =>
      η z • ((p / 2 * (u z) ^ (p / 2 - 1)) • G z) +
        (u z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j))
    MemLp v 2 (volume.restrict (I ×ˢ U)) →
    AEStronglyMeasurable J (volume.restrict (I ×ˢ U)) →
    MemLp (fun z => euclideanNorm (J z)) 2 (volume.restrict (I ×ˢ U)) →
    (∀ᵐ t ∂volume.restrict I, HasWeakGradient U (fun x => v (t,x)) (fun x => J (t,x))) →
    (∀ᵐ t ∂volume.restrict I, (∫⁻ x in U, ENNReal.ofReal (ρ x) * ‖v (t,x)‖ₑ ^ (2 : ℝ)) ≤ A) →
    AEMeasurable (fun z => ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z)))
      (volume.restrict (I ×ˢ U)) →
    (∫⁻ z in I ×ˢ U, ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z))) ≤ E →
    (∫⁻ z in S, ENNReal.ofReal (u z) ^ (p * (((d : ℝ) + 2) / d))) ≤
      ENNReal.ofReal κ⁻¹ * (C * A ^ (2 / (d : ℝ)) * E) := by
  obtain ⟨C, hC, hsob⟩ := c8_native_weighted_parabolic_sobolev d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hcoeff I U hI hU u G η K hK hKU hzero S hS hSI hηone p ε hp hε hpos A E v J hv hJm hJ hw hmass hEm henergy
  have hs : ∀ᵐ t ∂volume.restrict I, ∀ x ∈ U, x ∉ K → v (t,x) = 0 := by
    filter_upwards with t
    intro x hx hnot
    simp only [v, hzero t x hnot, zero_mul]
  have hprod : volume.restrict (I ×ˢ U) = (volume.restrict I).prod (volume.restrict U) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hEm' := hEm
  rw [hprod] at hEm'
  have henergy' : (∫⁻ t in I, ∫⁻ x in U,
      ENNReal.ofReal (dot ((α x).mulVec (J (t,x))) (J (t,x)))) ≤ E := by
    rw [hprod, lintegral_prod _ hEm'] at henergy
    exact henergy
  have hmain := hsob ρ α hcoeff I U hI hU v J hv hJm hJ hw K hK hKU hs A hmass
  have hm : AEMeasurable (fun z : ℝ × Vec d => ENNReal.ofReal (ρ z.2) *
      ‖v z‖ₑ ^ (2 * ((d : ℝ) + 2) / d)) (volume.restrict (I ×ˢ U)) :=
    (ENNReal.measurable_ofReal.comp (hcoeff.1.comp measurable_snd)).aemeasurable.mul
      (hv.aestronglyMeasurable.aemeasurable.enorm.pow_const _)
  rw [hprod] at hm
  have hweighted : (∫⁻ z in I ×ˢ U, ENNReal.ofReal (ρ z.2) *
      ‖v z‖ₑ ^ (2 * ((d : ℝ) + 2) / d)) ≤ C * A ^ (2 / (d : ℝ)) * E := by
    rw [hprod, lintegral_prod _ hm]
    exact hmain.trans (by gcongr)
  have hposS := hpos.filter_mono (ae_mono (Measure.restrict_mono hSI le_rfl))
  calc
    (∫⁻ z in S, ENNReal.ofReal (u z) ^ (p * (((d : ℝ) + 2) / d))) =
        ∫⁻ z in S, ‖v z‖ₑ ^ (2 * ((d : ℝ) + 2) / d) := by
      apply lintegral_congr_ae
      filter_upwards [hposS, ae_restrict_mem hS] with z hz hzS
      rw [Real.enorm_eq_ofReal_abs]
      dsimp only [v]
      rw [hηone z hzS, one_mul]
      exact (PDE.Parabolic.LocalMax.ofReal_half_pow_rpow (d := d) (by linarith) hp.le).symm
    _ ≤ ∫⁻ z in I ×ˢ U, ‖v z‖ₑ ^ (2 * ((d : ℝ) + 2) / d) := lintegral_mono_set hSI
    _ ≤ ENNReal.ofReal κ⁻¹ * ∫⁻ z in I ×ˢ U, ENNReal.ofReal (ρ z.2) *
        ‖v z‖ₑ ^ (2 * ((d : ℝ) + 2) / d) :=
      (c8_density_lintegral_bounds (volume.restrict (I ×ˢ U)) κ hκ (fun z => ρ z.2)
        (fun z => ⟨(hcoeff.2.2 z.2).1, (hcoeff.2.2 z.2).2.1⟩) _).2
    _ ≤ _ := by gcongr

/-- Functional small-power gain with a supplied weak gradient and energy. -/
theorem c13_small_power_parabolic_sobolev_gain (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (I : Set ℝ) (U : Set (Vec d)),
    MeasurableSet I → IsOpen U →
    ∀ (u η : ℝ × Vec d → ℝ) (J : ℝ × Vec d → Vec d) (p : ℝ),
    0 < p →
    let v := fun z : ℝ × Vec d => η z * Real.rpow (u z) (p/2)
    MemLp v 2 (volume.restrict (I ×ˢ U)) →
    AEStronglyMeasurable J (volume.restrict (I ×ˢ U)) →
    MemLp (fun z => euclideanNorm (J z)) 2 (volume.restrict (I ×ˢ U)) →
    (∀ᵐ t ∂volume.restrict I, HasWeakGradient U (fun x => v (t,x)) (fun x => J (t,x))) →
    ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
    (∀ᵐ t ∂volume.restrict I, ∀ x ∈ U, x ∉ K → v (t,x) = 0) →
    ∀ S : Set (ℝ × Vec d), MeasurableSet S → S ⊆ I ×ˢ U →
    (∀ z ∈ S, η z = 1 ∧ 0 ≤ u z) → ∀ A E : ℝ≥0∞,
    (∀ᵐ t ∂volume.restrict I,
      (∫⁻ x in U, ENNReal.ofReal (ρ x) * ‖v (t,x)‖ₑ ^ (2 : ℝ)) ≤ A) →
    ((∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal
      (dot ((α x).mulVec (J (t,x))) (J (t,x)))) ≤ E) →
    (∫⁻ z in S, ENNReal.ofReal (u z) ^ (p * (((d : ℝ)+2)/d))) ≤
      ENNReal.ofReal κ⁻¹ * (C * A ^ (2/(d : ℝ)) * E) := by
  obtain ⟨C, hC, hsob⟩ := c8_native_weighted_parabolic_sobolev d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hcoeff I U hI hU u η J p hp v hv hJm hJ hw K hK hKU hs S hS hSI hinner A E hmass henergy
  have hmain := hsob ρ α hcoeff I U hI hU v J hv hJm hJ hw K hK hKU hs A hmass
  have hprod : volume.restrict (I ×ˢ U) = (volume.restrict I).prod (volume.restrict U) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hm : AEMeasurable (fun z : ℝ × Vec d => ENNReal.ofReal (ρ z.2) *
      ‖v z‖ₑ ^ (2 * ((d : ℝ) + 2) / d)) (volume.restrict (I ×ˢ U)) :=
    (ENNReal.measurable_ofReal.comp (hcoeff.1.comp measurable_snd)).aemeasurable.mul
      (hv.aestronglyMeasurable.aemeasurable.enorm.pow_const _)
  rw [hprod] at hm
  have hweighted : (∫⁻ z in I ×ˢ U, ENNReal.ofReal (ρ z.2) *
      ‖v z‖ₑ ^ (2 * ((d : ℝ) + 2) / d)) ≤ C * A ^ (2 / (d : ℝ)) * E := by
    rw [hprod, lintegral_prod _ hm]
    exact hmain.trans (by gcongr)
  calc
    (∫⁻ z in S, ENNReal.ofReal (u z) ^ (p * (((d : ℝ) + 2) / d))) =
        ∫⁻ z in S, ‖v z‖ₑ ^ (2 * ((d : ℝ) + 2) / d) := by
      apply setLIntegral_congr_fun hS
      intro z hz
      dsimp only
      rw [Real.enorm_eq_ofReal_abs]
      dsimp only [v]
      rw [(hinner z hz).1, one_mul]
      exact (PDE.Parabolic.LocalMax.ofReal_half_pow_rpow (d := d) (hinner z hz).2 hp.le).symm
    _ ≤ ∫⁻ z in I ×ˢ U, ‖v z‖ₑ ^ (2 * ((d : ℝ) + 2) / d) := lintegral_mono_set hSI
    _ ≤ ENNReal.ofReal κ⁻¹ * ∫⁻ z in I ×ˢ U, ENNReal.ofReal (ρ z.2) *
        ‖v z‖ₑ ^ (2 * ((d : ℝ) + 2) / d) :=
      (c8_density_lintegral_bounds (volume.restrict (I ×ˢ U)) κ hκ (fun z => ρ z.2)
        (fun z => ⟨(hcoeff.2.2 z.2).1, (hcoeff.2.2 z.2).2.1⟩) _).2
    _ ≤ _ := by gcongr

/-- The Sobolev gain remains below one in the weak-Harnack range. -/
theorem c13_small_power_sobolev_exponent_range {d : ℕ} (hd : 2 ≤ d)
    {p : ℝ} (hp : 0 < p) (hp_small : p < (d : ℝ) / ((d : ℝ) + 2)) :
    0 < p * (((d : ℝ) + 2) / d) ∧
      p * (((d : ℝ) + 2) / d) < 1 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsum : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  constructor
  · positivity
  · have h := (lt_div_iff₀ hsum).mp hp_small
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hdpos).mpr
    nlinarith

#lint
end EinsteinFull.Calculus
