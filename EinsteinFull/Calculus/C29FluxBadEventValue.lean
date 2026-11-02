import EinsteinFull.Calculus.CarverSFluxBlockGain
import EinsteinFull.Calculus.CarverSFluxBlockMoments
import EinsteinFull.Calculus.C15FluxBlockBadEventEnergy
import EinsteinFull.Calculus.C6FluxGrowthAbsorption
import EinsteinFull.Frozen.ReducedLawProbability
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open scoped NNReal
open MeasureTheory
open EinsteinRelation EinsteinFull.Blueprint

namespace EinsteinFull.Calculus

/-- The bad-event local endpoint value gains the corresponding probability power. -/
theorem c29_flux_endpoint_local_value_bad_event {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (U : Lp ℂ 2 (reducedLaw Q))
    (p : ℝ) (hp : 1 ≤ p) (hU : MemLp U (ENNReal.ofReal (2*p)) (reducedLaw Q))
    (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (E : Set (FieldPair d)) (hE : MeasurableSet E) :
    let L := fun ω : FieldPair d => Real.sqrt
      (⨍ x in {x : Vec d | euclideanNorm (x-z) ≤ ρ}, ‖U (translate x ω)‖ ^ 2)
    MemLp (Eᶜ.indicator L) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (Eᶜ.indicator L) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (reducedLaw Q Eᶜ).toReal ^ (1/(2*p)) *
          (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal (2*p)) (reducedLaw Q)).toReal := by
  letI := reducedLaw_probability Q
  let L := fun ω : FieldPair d => Real.sqrt
    (⨍ x in {x : Vec d | euclideanNorm (x-z) ≤ ρ}, ‖U (translate x ω)‖ ^ 2)
  have hp0 : 0 < p := by linarith
  have h2p : 0 < 2 * p := by positivity
  have hpq : ENNReal.ofReal p ≤ ENNReal.ofReal (2 * p) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨hL, hLnorm⟩ := carverS_flux_block_closed_local_value_moment Q U (2 * p)
    (by linarith) hU ρ hρ z
  change MemLp L (ENNReal.ofReal (2 * p)) (reducedLaw Q) at hL
  change (eLpNorm L (ENNReal.ofReal (2 * p)) (reducedLaw Q)).toReal ≤ _ at hLnorm
  have hm : MemLp (Eᶜ.indicator L) (ENNReal.ofReal p) (reducedLaw Q) :=
    (hL.mono_exponent hpq).indicator hE.compl
  refine ⟨hm, ?_⟩
  have hexp : 1 / p - 1 / (2 * p) = 1 / (2 * p) := by
    field_simp [hp0.ne']
    <;> ring
  have hbound := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq
    (μ := (reducedLaw Q).restrict Eᶜ) hL.aestronglyMeasurable.restrict
  rw [ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal h2p.le, hexp,
    Measure.restrict_apply_univ] at hbound
  have hle : eLpNorm (Eᶜ.indicator L) (ENNReal.ofReal p) (reducedLaw Q) ≤
      eLpNorm L (ENNReal.ofReal (2 * p)) (reducedLaw Q) *
        (reducedLaw Q Eᶜ) ^ (1 / (2 * p)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hE.compl]
    refine hbound.trans ?_
    gcongr
    exact Measure.restrict_le_self
  have hfin : eLpNorm L (ENNReal.ofReal (2 * p)) (reducedLaw Q) *
      (reducedLaw Q Eᶜ) ^ (1 / (2 * p)) ≠ ⊤ :=
    ENNReal.mul_ne_top hL.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _))
  have hr := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hr
  have hreal : (eLpNorm (Eᶜ.indicator L) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      (reducedLaw Q Eᶜ).toReal ^ (1 / (2 * p)) *
        (eLpNorm L (ENNReal.ofReal (2 * p)) (reducedLaw Q)).toReal := by
    simpa [mul_comm] using hr
  exact hreal.trans
    (mul_le_mul_of_nonneg_left hLnorm (Real.rpow_nonneg ENNReal.toReal_nonneg _))

/-- A stretched-exponential event bound controls the local endpoint value. -/
theorem c29_flux_endpoint_local_value_bad_event_tail {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (U : Lp ℂ 2 (reducedLaw Q))
    (p : ℝ) (hp : 1 ≤ p) (hU : MemLp U (ENNReal.ofReal (2*p)) (reducedLaw Q))
    (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (E : Set (FieldPair d)) (hE : MeasurableSet E)
    (A b α r : ℝ) (hA : 0 ≤ A)
    (htail : (reducedLaw Q Eᶜ).toReal ≤ A * Real.exp (-b * r ^ α)) :
    let L := fun ω : FieldPair d => Real.sqrt
      (⨍ x in {x : Vec d | euclideanNorm (x-z) ≤ ρ}, ‖U (translate x ω)‖ ^ 2)
    MemLp (Eᶜ.indicator L) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (Eᶜ.indicator L) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        A ^ (1/(2*p)) * Real.exp (-b * r ^ α / (2*p)) *
          (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal (2*p)) (reducedLaw Q)).toReal := by
  have hp0 : 0 < p := by linarith
  have hpow := Real.rpow_le_rpow (ENNReal.toReal_nonneg) htail
    (show 0 ≤ 1 / (2 * p) by positivity)
  have hfactor : (A * Real.exp (-b * r ^ α)) ^ (1 / (2 * p)) =
      A ^ (1 / (2 * p)) * Real.exp (-b * r ^ α / (2 * p)) := by
    rw [Real.mul_rpow hA (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  rw [hfactor] at hpow
  obtain ⟨hm, hbound⟩ := c29_flux_endpoint_local_value_bad_event Q U p hp hU ρ hρ z E hE
  exact ⟨hm, hbound.trans (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg)⟩

/-- Two bad events contribute the sum of their probability gains. -/
theorem c29_flux_endpoint_local_value_two_bad_events {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (U : Lp ℂ 2 (reducedLaw Q))
    (p : ℝ) (hp : 1 ≤ p) (hU : MemLp U (ENNReal.ofReal (2*p)) (reducedLaw Q))
    (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (E : Set (FieldPair d)) (hE : MeasurableSet E)
    (F : Set (FieldPair d)) (hF : MeasurableSet F) :
    let L := fun ω : FieldPair d => Real.sqrt
      (⨍ x in {x : Vec d | euclideanNorm (x-z) ≤ ρ}, ‖U (translate x ω)‖ ^ 2)
    MemLp ((E ∩ F)ᶜ.indicator L) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm ((E ∩ F)ᶜ.indicator L) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        ((reducedLaw Q Eᶜ).toReal ^ (1/(2*p)) + (reducedLaw Q Fᶜ).toReal ^ (1/(2*p))) *
          (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal (2*p)) (reducedLaw Q)).toReal := by
  let L := fun ω : FieldPair d => Real.sqrt
    (⨍ x in {x : Vec d | euclideanNorm (x-z) ≤ ρ}, ‖U (translate x ω)‖ ^ 2)
  obtain ⟨hE_mem, hE_bound⟩ := c29_flux_endpoint_local_value_bad_event Q U p hp hU ρ hρ z E hE
  obtain ⟨hF_mem, hF_bound⟩ := c29_flux_endpoint_local_value_bad_event Q U p hp hU ρ hρ z F hF
  change MemLp (Eᶜ.indicator L) _ _ at hE_mem
  change MemLp (Fᶜ.indicator L) _ _ at hF_mem
  have hpart : MemLp (E.indicator (Fᶜ.indicator L)) (ENNReal.ofReal p) (reducedLaw Q) :=
    hF_mem.indicator hE
  have hsplit : (E ∩ F)ᶜ.indicator L = Eᶜ.indicator L + E.indicator (Fᶜ.indicator L) := by
    ext ω
    by_cases he : ω ∈ E <;> by_cases hf : ω ∈ F <;>
      simp [Set.indicator, he, hf]
  have hmem : MemLp ((E ∩ F)ᶜ.indicator L) (ENNReal.ofReal p) (reducedLaw Q) := by
    rw [hsplit]
    exact hE_mem.add hpart
  refine ⟨hmem, ?_⟩
  have hp' : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have htriangle := eLpNorm_add_le (f := Eᶜ.indicator L)
    (g := E.indicator (Fᶜ.indicator L)) (μ := reducedLaw Q) hp'
  have hfin := ENNReal.add_ne_top.mpr ⟨hE_mem.eLpNorm_ne_top, hpart.eLpNorm_ne_top⟩
  have hreal := ENNReal.toReal_mono hfin htriangle
  rw [ENNReal.toReal_add hE_mem.eLpNorm_ne_top hpart.eLpNorm_ne_top] at hreal
  have hpart_le := eLpNorm_indicator_le (Fᶜ.indicator L) hE
    (p := ENNReal.ofReal p) (μ := reducedLaw Q)
  have hpart_real := ENNReal.toReal_mono hF_mem.eLpNorm_ne_top hpart_le
  rw [hsplit]
  exact hreal.trans (by nlinarith [hE_bound, hF_bound, hpart_real])

/-- A complex kernel average has at most twice the kernel mass times the field moment. -/
theorem c29_complex_kernel_moment {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (p : ℝ) (hp : 1 ≤ p)
    (c : Vec d → ℂ) (hc : Integrable c) (hcc : Continuous c)
    (U : Lp ℂ 2 Q) (hU : MemLp (U : FieldPair d → ℂ) (ENNReal.ofReal p) Q) :
    let B : Lp ℂ 2 Q := ∫ y : Vec d, c y • complexTranslation Q hQ y U
    MemLp (B : FieldPair d → ℂ) (ENNReal.ofReal p) Q ∧
      (eLpNorm (B : FieldPair d → ℂ) (ENNReal.ofReal p) Q).toReal ≤
        2 * (∫ y : Vec d, ‖c y‖) *
          (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) Q).toReal := by
  let A : Lp ℂ 2 Q := ∫ y : Vec d, (c y).re • complexTranslation Q hQ y U
  let D : Lp ℂ 2 Q := ∫ y : Vec d, (c y).im • complexTranslation Q hQ y U
  have ht : Continuous fun y : Vec d => complexTranslation Q hQ y U :=
    (continuous_complexTranslation Q hQ).comp (continuous_id.prodMk continuous_const)
  have hint : ∀ r : Vec d → ℝ, Integrable r → Continuous r →
      Integrable (fun y => r y • complexTranslation Q hQ y U) := by
    intro r hr hrc
    refine (hr.norm.mul_const ‖U‖).mono' (hrc.smul ht).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_smul, norm_complexTranslation]
  have hre := hint (fun y => (c y).re) hc.re (Complex.continuous_re.comp hcc)
  have him := hint (fun y => (c y).im) hc.im (Complex.continuous_im.comp hcc)
  have hsplit : (∫ y : Vec d, c y • complexTranslation Q hQ y U : Lp ℂ 2 Q) = A + Complex.I • D := by
    have heq : ∀ y, c y • complexTranslation Q hQ y U =
        (c y).re • complexTranslation Q hQ y U +
          Complex.I • ((c y).im • complexTranslation Q hQ y U) := by
      intro y
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, ← add_smul]
      congr 1
      apply Complex.ext <;> simp
    simp_rw [heq]
    rw [integral_add hre (him.fun_smul Complex.I), integral_smul]
  obtain ⟨hA, hAb⟩ := K6.memLp_integral_smul_complexTranslation Q hQ hp
    (fun y => (c y).re) hc.re (Complex.continuous_re.comp hcc) U hU
  obtain ⟨hD, hDb⟩ := K6.memLp_integral_smul_complexTranslation Q hQ hp
    (fun y => (c y).im) hc.im (Complex.continuous_im.comp hcc) U hU
  change MemLp (A : FieldPair d → ℂ) _ _ at hA
  change MemLp (D : FieldPair d → ℂ) _ _ at hD
  have hID : MemLp (Complex.I • (D : FieldPair d → ℂ)) (ENNReal.ofReal p) Q := hD.const_smul _
  have hsum := hA.add hID
  have hq : (1 : ENNReal) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have htri := eLpNorm_add_le (f := (A : FieldPair d → ℂ))
    (g := Complex.I • (D : FieldPair d → ℂ)) (μ := Q) hq
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA.eLpNorm_ne_top, hID.eLpNorm_ne_top⟩) htri
  rw [ENNReal.toReal_add hA.eLpNorm_ne_top hID.eLpNorm_ne_top, eLpNorm_const_smul,
    ← ofReal_norm, Complex.norm_I, ENNReal.ofReal_one, one_mul] at hreal
  have hBae : ((A + Complex.I • D : Lp ℂ 2 Q) : FieldPair d → ℂ) =ᵐ[Q]
      (A : FieldPair d → ℂ) + Complex.I • (D : FieldPair d → ℂ) := by
    filter_upwards [Lp.coeFn_add A (Complex.I • D), Lp.coeFn_smul Complex.I D] with ω h1 h2
    simp only [Pi.add_apply, Pi.smul_apply] at *
    rw [h1, h2]
  have hR : (∫ y : Vec d, |(c y).re|) ≤ ∫ y : Vec d, ‖c y‖ :=
    integral_mono hc.re.abs hc.norm (fun y => Complex.abs_re_le_norm (c y))
  have hI : (∫ y : Vec d, |(c y).im|) ≤ ∫ y : Vec d, ‖c y‖ :=
    integral_mono hc.im.abs hc.norm (fun y => Complex.abs_im_le_norm (c y))
  dsimp only
  rw [hsplit]
  refine ⟨hsum.ae_eq hBae.symm, ?_⟩
  rw [eLpNorm_congr_ae hBae]
  change (eLpNorm (A : FieldPair d → ℂ) _ _).toReal ≤ _ at hAb
  change (eLpNorm (D : FieldPair d → ℂ) _ _).toReal ≤ _ at hDb
  have hn := ENNReal.toReal_nonneg (a := eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) Q)
  nlinarith [mul_le_mul_of_nonneg_right hR hn, mul_le_mul_of_nonneg_right hI hn]

theorem c29_actual_flux_block_crude_moment
    (hlt : node_e_u3A_local_u2D_timeStmt)
    (hcr : node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) →
    ∀ t : ℝ≥0, 1 ≤ (t : ℝ) →
    ∀ (p : ℝ), 1 ≤ p → ∀ (ψ : Vec d → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → ∀ j : Fin d,
      let B : Lp ℂ 2 (reducedLaw Q) := ∫ y : Vec d,
        ψ y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)
      MemLp (B : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (B : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (∫ y : Vec d, ‖ψ y‖ ∂volume) * (C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) := by
  obtain ⟨C₀, N, hC₀, hflux⟩ := c15_actual_weak_flux_all_finite_moments_of_crude hlt hcr d hd D
  refine ⟨2 * C₀, N, by linarith, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν G J hGJ t ht p hp ψ hψ hψc j
  letI := reducedLaw_probability Q
  let M : ℝ := C₀ * (2 + (t : ℝ)) ^ N * Real.exp (C₀ * ‖ζ‖ ^ 2 * (t : ℝ))
  obtain ⟨hmem, hn⟩ := hflux Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν G J hGJ t ht p hp j
  change (eLpNorm (J t j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ M at hn
  have hc : Continuous ψ := hψ.continuous
  have hi : Integrable ψ := hc.integrable_of_hasCompactSupport hψc
  obtain ⟨hm, hbound⟩ := c29_complex_kernel_moment (reducedLaw Q) (reducedLaw_stationary Q) p hp ψ hi hc (J t j) hmem
  refine ⟨hm, ?_⟩
  have hk : 0 ≤ ∫ y : Vec d, ‖ψ y‖ := integral_nonneg (fun _ => norm_nonneg _)
  have he : Real.exp (C₀ * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
      Real.exp ((2 * C₀) * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ ‖ζ‖ ^ 2 * (t : ℝ) := by positivity
    nlinarith
  have hpow : 0 ≤ (2 + (t : ℝ)) ^ N := by positivity
  have hbig : 2 * M ≤ (2 * C₀) * (2 + (t : ℝ)) ^ N *
      Real.exp ((2 * C₀) * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    dsimp [M]
    nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * C₀ * (2 + (t : ℝ)) ^ N by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hn (show 0 ≤ 2 * (∫ y : Vec d, ‖ψ y‖) by positivity),
    mul_le_mul_of_nonneg_left hbig hk]


theorem c29_actual_flux_block_bad_event_crude_moment
    (hlt : node_e_u3A_local_u2D_timeStmt)
    (hcr : node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) →
    ∀ t : ℝ≥0, 1 ≤ (t : ℝ) →
    ∀ (p : ℝ), 1 ≤ p → ∀ (ψ : Vec d → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → ∀ j : Fin d,
      let B : Lp ℂ 2 (reducedLaw Q) := ∫ y : Vec d,
        ψ y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)
      ∀ E : Set (FieldPair d), MeasurableSet E →
      MemLp (Eᶜ.indicator (B : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (Eᶜ.indicator (B : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (reducedLaw Q Eᶜ).toReal ^ (1 / (2 * p)) *
        ((∫ y : Vec d, ‖ψ y‖ ∂volume) * (C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)))) := by
  obtain ⟨C, N, hC, hbound⟩ := c29_actual_flux_block_crude_moment hlt hcr d hd D
  refine ⟨C, N, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν G J hGJ t ht p hp ψ hψ hψc j
  dsimp only
  intro E hE
  letI := reducedLaw_probability Q
  let B : Lp ℂ 2 (reducedLaw Q) := ∫ y : Vec d,
    ψ y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)
  obtain ⟨hB, hBn⟩ := hbound Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν G J hGJ t ht (2*p) (by linarith) ψ hψ hψc j
  change MemLp (B : FieldPair d → ℂ) _ _ at hB
  change (eLpNorm (B : FieldPair d → ℂ) _ _).toReal ≤ _ at hBn
  have hp0 : 0 < p := by linarith
  have h2p : 0 < 2 * p := by positivity
  have hpq : ENNReal.ofReal p ≤ ENNReal.ofReal (2 * p) := ENNReal.ofReal_le_ofReal (by linarith)
  have hm : MemLp (Eᶜ.indicator (B : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) :=
    (hB.mono_exponent hpq).indicator hE.compl
  have hexp : 1 / p - 1 / (2 * p) = 1 / (2 * p) := by field_simp [hp0.ne']; ring
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq
    (μ := (reducedLaw Q).restrict Eᶜ) hB.aestronglyMeasurable.restrict
  rw [ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal h2p.le, hexp,
    Measure.restrict_apply_univ] at h
  have hle : eLpNorm (Eᶜ.indicator (B : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) ≤
      eLpNorm (B : FieldPair d → ℂ) (ENNReal.ofReal (2 * p)) (reducedLaw Q) *
        (reducedLaw Q Eᶜ) ^ (1 / (2 * p)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hE.compl]
    refine h.trans ?_
    gcongr
    exact Measure.restrict_le_self
  have hfin : eLpNorm (B : FieldPair d → ℂ) (ENNReal.ofReal (2 * p)) (reducedLaw Q) *
      (reducedLaw Q Eᶜ) ^ (1 / (2 * p)) ≠ ⊤ :=
    ENNReal.mul_ne_top hB.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top (reducedLaw Q) Eᶜ))
  have hr := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hr
  refine ⟨hm, ?_⟩
  have hpnon : 0 ≤ (reducedLaw Q Eᶜ).toReal ^ (1 / (2 * p)) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hBn hpnon]


theorem c29_actual_flux_block_bad_event_polynomial_decay
    (hlt : node_e_u3A_local_u2D_timeStmt)
    (hcr : node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (p A Ctail c η₀ m : ℝ) (hp : 2 ≤ p) (hA : 0 ≤ A)
    (hCt : 1 ≤ Ctail) (hc : 0 < c) (hη : 0 < η₀)
    (hηhalf : η₀ ≤ 1 / 2) (hsmall : 2 * η₀ < (d : ℝ) / 4) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) →
    ∀ t : ℝ≥0, t₀ ≤ (t : ℝ) →
      ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ →
    ∀ r : ℝ, Real.sqrt (t : ℝ) ≤ r →
    ∀ H : ℝ, 0 ≤ H →
    ∀ ψ : Vec d → ℂ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ y : Vec d, ‖ψ y‖ ∂volume) ≤ H * (A * (1 + r) ^ d) → ∀ j : Fin d,
    ∀ E : Set (FieldPair d), MeasurableSet E →
      reducedLaw Q Eᶜ ≤ ENNReal.ofReal (Ctail * Real.exp (-c * r ^ ((d : ℝ) / 2))) →
      let B : Lp ℂ 2 (reducedLaw Q) := ∫ y : Vec d,
        ψ y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)
      MemLp (Eᶜ.indicator (B : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (Eᶜ.indicator (B : FieldPair d → ℂ)) (ENNReal.ofReal p)
        (reducedLaw Q)).toReal ≤ H * (t : ℝ) ^ (-m) := by
  obtain ⟨C, N, hC, hmoment⟩ := c29_actual_flux_block_bad_event_crude_moment hlt hcr d hd D
  obtain ⟨T, hT, htail⟩ := c6_flux_bad_event_tail_absorption d hd N C c p (m + 1) η₀
    hC hc hp hsmall
  let K := A * C * Ctail ^ (1 / (2 * p))
  refine ⟨max T K, le_trans hT (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hGJ t ht hf r hr H hH ψ hψ hψc hψbound j E hE hprob
  have htT : T ≤ (t : ℝ) := le_trans (le_max_left _ _) ht
  have ht1 : 1 ≤ (t : ℝ) := le_trans hT htT
  have htpos : 0 < (t : ℝ) := by linarith
  have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 htpos
  have hpow : (t : ℝ) ^ η₀ ≤ Real.sqrt (t : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le ht1 hηhalf
  have hζ : ‖ζ‖ ≤ 4 := by nlinarith [norm_nonneg ζ]
  obtain ⟨hmem, hnorm⟩ := hmoment Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν G J hGJ t ht1 p (by linarith) ψ hψ hψc j E hE
  refine ⟨hmem, ?_⟩
  let tail : ℝ := Ctail * Real.exp (-c * r ^ ((d : ℝ) / 2))
  have htail0 : 0 ≤ tail := by dsimp [tail]; positivity
  have hmeasure : (reducedLaw Q Eᶜ).toReal ≤ tail := by
    change (reducedLaw Q Eᶜ) ≤ ENNReal.ofReal tail at hprob
    have hh : (reducedLaw Q Eᶜ).toReal ≤ (ENNReal.ofReal tail).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob
    simpa only [ENNReal.toReal_ofReal htail0] using hh
  have hprobpow : (reducedLaw Q Eᶜ).toReal ^ (1 / (2 * p)) ≤ tail ^ (1 / (2 * p)) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hmeasure (by positivity)
  have hkernel : 0 ≤ ∫ y : Vec d, ‖ψ y‖ ∂volume := integral_nonneg (fun _ => norm_nonneg _)
  have hpoly : 0 ≤ (1 + r) ^ d := by
    have hr0 : 0 ≤ r := le_trans (Real.sqrt_nonneg _) hr
    positivity
  have htime : 0 ≤ (2 + (t : ℝ)) ^ N := by positivity
  have hexp : 0 ≤ Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := (Real.exp_pos _).le
  have hconst : 0 ≤ K := by dsimp [K]; positivity
  have hk : K ≤ (t : ℝ) := le_trans (le_max_right _ _) ht
  have hbudget := htail (t : ℝ) r ζ htT hr hf
  have hbudget' : K * ((1 + r) ^ d * (2 + (t : ℝ)) ^ N *
      Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * r ^ ((d : ℝ) / 2) / (2 * p))) ≤ (t : ℝ) ^ (-m) := by
    have hmul := mul_le_mul_of_nonneg_left hbudget hconst
    have hpoweq : (t : ℝ) * (t : ℝ) ^ (-(m + 1)) = (t : ℝ) ^ (-m) := by
      calc
        _ = (t : ℝ) ^ (1 : ℝ) * (t : ℝ) ^ (-(m + 1)) := by rw [Real.rpow_one]
        _ = (t : ℝ) ^ ((1 : ℝ) + (-(m + 1))) := (Real.rpow_add htpos _ _).symm
        _ = _ := by congr 1; ring
    exact hmul.trans ((mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg htpos.le _)).trans_eq hpoweq)
  have heq : tail ^ (1 / (2 * p)) = Ctail ^ (1 / (2 * p)) *
      Real.exp (-c * r ^ ((d : ℝ) / 2) / (2 * p)) := by
    dsimp [tail]
    rw [Real.mul_rpow (by linarith : 0 ≤ Ctail) (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  have hcombined : tail ^ (1 / (2 * p)) * ((H * (A * (1 + r) ^ d)) *
      (C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)))) ≤ H * (t : ℝ) ^ (-m) := by
    have h := mul_le_mul_of_nonneg_left hbudget' hH
    convert h using 1
    rw [heq, show C * ‖ζ‖ ^ 2 * (t : ℝ) - c * r ^ ((d : ℝ) / 2) / (2 * p) =
      C * ‖ζ‖ ^ 2 * (t : ℝ) + (-c * r ^ ((d : ℝ) / 2) / (2 * p)) by ring, Real.exp_add]
    dsimp [K]
    ring
  calc
    _ ≤ (reducedLaw Q Eᶜ).toReal ^ (1 / (2 * p)) *
        ((∫ y : Vec d, ‖ψ y‖ ∂volume) * (C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)))) := hnorm
    _ ≤ tail ^ (1 / (2 * p)) * ((H * (A * (1 + r) ^ d)) *
        (C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)))) := by
          gcongr
    _ ≤ _ := hcombined

end EinsteinFull.Calculus
