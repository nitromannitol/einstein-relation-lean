import EinsteinFull.Calculus.CarverSFluxBlockGain
import EinsteinFull.Calculus.C6FluxBlockGlobalGradientMoment
import EinsteinFull.Calculus.K8EndpointFluxMemLp
import EinsteinFull.Frozen.LocalSpatialEnergy
import EinsteinFull.Frozen.ReducedLawProbability
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open scoped NNReal
open MeasureTheory
open EinsteinRelation EinsteinFull.Blueprint

namespace EinsteinFull.Calculus

/-- Restricting the actual local energy to a bad event gains the square root of
its probability at the corresponding moment exponent. -/
theorem c15_flux_block_energy_bad_event {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q))
    (E : Set (FieldPair d)) (hE : MeasurableSet E) (p : ℝ) (hp : 1 ≤ p)
    (henergy : MemLp (localSpatialEnergy Q t ρ hρ z G V)
      (ENNReal.ofReal (2 * p)) (reducedLaw Q)) :
    MemLp (Eᶜ.indicator (localSpatialEnergy Q t ρ hρ z G V))
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (Eᶜ.indicator (localSpatialEnergy Q t ρ hρ z G V))
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      (reducedLaw Q Eᶜ).toReal ^ (1 / (2 * p)) *
      (eLpNorm (localSpatialEnergy Q t ρ hρ z G V)
        (ENNReal.ofReal (2 * p)) (reducedLaw Q)).toReal := by
  letI := reducedLaw_probability Q
  have hp0 : 0 < p := by linarith
  have h2p : 0 < 2 * p := by positivity
  have hpq : ENNReal.ofReal p ≤ ENNReal.ofReal (2 * p) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hm : MemLp (Eᶜ.indicator (localSpatialEnergy Q t ρ hρ z G V))
      (ENNReal.ofReal p) (reducedLaw Q) :=
    (henergy.mono_exponent hpq).indicator hE.compl
  refine ⟨hm, ?_⟩
  have hexp : 1 / p - 1 / (2 * p) = 1 / (2 * p) := by
    field_simp [hp0.ne']
    <;> ring
  have hbound := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq
    (μ := (reducedLaw Q).restrict Eᶜ) henergy.aestronglyMeasurable.restrict
  rw [ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal h2p.le, hexp,
    Measure.restrict_apply_univ] at hbound
  have hle : eLpNorm (Eᶜ.indicator (localSpatialEnergy Q t ρ hρ z G V))
      (ENNReal.ofReal p) (reducedLaw Q) ≤
      eLpNorm (localSpatialEnergy Q t ρ hρ z G V) (ENNReal.ofReal (2 * p))
        (reducedLaw Q) * (reducedLaw Q Eᶜ) ^ (1 / (2 * p)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hE.compl]
    refine hbound.trans ?_
    gcongr
    exact Measure.restrict_le_self
  have hfin : eLpNorm (localSpatialEnergy Q t ρ hρ z G V)
      (ENNReal.ofReal (2 * p)) (reducedLaw Q) *
      (reducedLaw Q Eᶜ) ^ (1 / (2 * p)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top henergy.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _))
  have hr := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hr
  simpa [mul_comm] using hr


/-- A stretched-exponential tail yields the corresponding bad-event energy bound. -/
theorem c15_flux_block_energy_bad_event_tail {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q))
    (E : Set (FieldPair d)) (hE : MeasurableSet E) (p : ℝ) (hp : 1 ≤ p)
    (A b α r : ℝ) (hA : 0 ≤ A)
    (htail : (reducedLaw Q Eᶜ).toReal ≤ A * Real.exp (-b * r ^ α))
    (henergy : MemLp (localSpatialEnergy Q t ρ hρ z G V)
      (ENNReal.ofReal (2 * p)) (reducedLaw Q)) :
    (eLpNorm (Eᶜ.indicator (localSpatialEnergy Q t ρ hρ z G V))
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      A ^ (1 / (2 * p)) * Real.exp (-b * r ^ α / (2 * p)) *
      (eLpNorm (localSpatialEnergy Q t ρ hρ z G V)
        (ENNReal.ofReal (2 * p)) (reducedLaw Q)).toReal := by
  have hp0 : 0 < p := by linarith
  have hpow := Real.rpow_le_rpow (ENNReal.toReal_nonneg) htail
    (show 0 ≤ 1 / (2 * p) by positivity)
  have hfactor : (A * Real.exp (-b * r ^ α)) ^ (1 / (2 * p)) =
      A ^ (1 / (2 * p)) * Real.exp (-b * r ^ α / (2 * p)) := by
    rw [Real.mul_rpow hA (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  rw [hfactor] at hpow
  exact (c15_flux_block_energy_bad_event Q t ρ hρ z G V E hE p hp henergy).2.trans
    (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg)


/-- The local-time estimate gives the bad-event bound for the actual flux energy. -/
theorem c15_flux_block_actual_energy_bad_event_moment
    (hlt : node_e_u3A_local_u2D_timeStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 1 ≤ p) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
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
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
      let V := deriv (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (t : ℝ)
      ∀ (ρ : ℝ) (z : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ)
        (E : Set (FieldPair d)) (hE : MeasurableSet E)
        (A b α r : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b) (hr : 0 < r),
        (reducedLaw Q Eᶜ).toReal ≤ A * Real.exp (-b * r ^ α) →
        MemLp (Eᶜ.indicator (localSpatialEnergy Q t ρ
          (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) z (G t) V))
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (Eᶜ.indicator (localSpatialEnergy Q t ρ
          (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) z (G t) V))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        A ^ (1 / (2 * p)) * Real.exp (-b * r ^ α / (2 * p)) *
          (C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
            (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
            (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
              FieldPair d → ℂ) (ENNReal.ofReal (2 * p)) (reducedLaw Q)).toReal) := by
  obtain ⟨C, Cp, hC, hCp, hlocal⟩ :=
    EinsteinFull.Blueprint.carverS_flux_block_local_time_on_flux_witness hlt d hd D (2 * p) (by linarith)
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
  dsimp only
  intro ρ z hρ E hE A b α r hA hb hr htail
  obtain ⟨hmem, hbound⟩ := hlocal Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht ρ z hρ
  refine ⟨(c15_flux_block_energy_bad_event Q t ρ _ z (G t) _ E hE p hp hmem).1, ?_⟩
  exact (c15_flux_block_energy_bad_event_tail Q t ρ _ z (G t) _ E hE p hp
    A b α r hA htail hmem).trans
      (mul_le_mul_of_nonneg_left hbound (mul_nonneg (Real.rpow_nonneg hA _) (Real.exp_pos _).le))

/-- The bad-event energy bound with the actual deterministic flux center. -/
theorem c15_flux_block_energy_and_center_bad_event {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q))
    (i : Fin d) (ζ : ℂ) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (E : Set (FieldPair d)) (hE : MeasurableSet E) (p : ℝ) (hp : 1 ≤ p)
    (henergy : MemLp (localSpatialEnergy Q t ρ hρ z G V)
      (ENNReal.ofReal (2 * p)) (reducedLaw Q)) :
    let c := ζ * ∫ ω, ∑ j : Fin d, a j i ω * G j ω ∂reducedLaw Q
    MemLp (Eᶜ.indicator (fun ω => localSpatialEnergy Q t ρ hρ z G V ω + ‖c‖))
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (Eᶜ.indicator (fun ω => localSpatialEnergy Q t ρ hρ z G V ω + ‖c‖))
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      (reducedLaw Q Eᶜ).toReal ^ (1 / (2 * p)) *
      (eLpNorm (localSpatialEnergy Q t ρ hρ z G V)
        (ENNReal.ofReal (2 * p)) (reducedLaw Q)).toReal + ‖c‖ * (reducedLaw Q Eᶜ).toReal ^ (1 / p) := by
  letI := reducedLaw_probability Q
  let c := ζ * ∫ ω, ∑ j : Fin d, a j i ω * G j ω ∂reducedLaw Q
  let f := Eᶜ.indicator (localSpatialEnergy Q t ρ hρ z G V)
  let g := Eᶜ.indicator (fun _ : FieldPair d => ‖c‖)
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hf := c15_flux_block_energy_bad_event Q t ρ hρ z G V E hE p hp henergy
  have hg : MemLp g (ENNReal.ofReal p) (reducedLaw Q) :=
    (memLp_const ‖c‖).indicator hE.compl
  have heq : Eᶜ.indicator (fun ω => localSpatialEnergy Q t ρ hρ z G V ω + ‖c‖) = f + g := by
    ext ω
    by_cases hω : ω ∈ Eᶜ <;> simp [f, g, hω]
  change MemLp _ _ _ ∧ (eLpNorm _ _ _).toReal ≤ _
  rw [heq]
  refine ⟨hf.1.add hg, ?_⟩
  have htri := eLpNorm_add_le (f := f) (g := g) (μ := reducedLaw Q) hp1
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.1.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩) htri
  rw [ENNReal.toReal_add hf.1.eLpNorm_ne_top hg.eLpNorm_ne_top] at hreal
  have hg_norm : (eLpNorm g (ENNReal.ofReal p) (reducedLaw Q)).toReal =
      ‖c‖ * (reducedLaw Q Eᶜ).toReal ^ (1 / p) := by
    rw [show g = Eᶜ.indicator (fun _ : FieldPair d => ‖c‖) by rfl,
      eLpNorm_indicator_const hE.compl.nullMeasurableSet
        (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top,
      ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hp0.le]
    simp
  rw [hg_norm] at hreal
  exact hreal.trans (add_le_add hf.2 (le_refl _))

/-- The actual flux energy and its deterministic center on the bad event. -/
theorem c15_flux_block_actual_energy_center_bad_event_moment
    (hlt : node_e_u3A_local_u2D_timeStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 1 ≤ p) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
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
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
      let V := deriv (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (t : ℝ)
      let c := ζ * ∫ ω, ∑ j : Fin d, a j ⟨0, by omega⟩ ω * G t j ω ∂reducedLaw Q
      ∀ (ρ : ℝ) (z : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ)
        (E : Set (FieldPair d)) (hE : MeasurableSet E)
        (A b α r : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b) (hr : 0 < r),
        (reducedLaw Q Eᶜ).toReal ≤ A * Real.exp (-b * r ^ α) →
        MemLp (Eᶜ.indicator (fun ω => localSpatialEnergy Q t ρ
          (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) z (G t) V ω + ‖c‖))
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (Eᶜ.indicator (fun ω => localSpatialEnergy Q t ρ
          (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) z (G t) V ω + ‖c‖))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        A ^ (1 / (2 * p)) * Real.exp (-b * r ^ α / (2 * p)) *
          (C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
            (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
            (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
              FieldPair d → ℂ) (ENNReal.ofReal (2 * p)) (reducedLaw Q)).toReal) +
          ‖c‖ * (reducedLaw Q Eᶜ).toReal ^ (1 / p) := by
  obtain ⟨C, Cp, hC, hCp, hactual⟩ :=
    c15_flux_block_actual_energy_bad_event_moment hlt d hd D p hp
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
  dsimp only
  intro ρ z hρ E hE A b α r hA hb hr htail
  letI := reducedLaw_probability Q
  let c := ζ * ∫ ω, ∑ j : Fin d, a j ⟨0, by omega⟩ ω * G t j ω ∂reducedLaw Q
  let f := Eᶜ.indicator (localSpatialEnergy Q t ρ
    (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) z (G t)
    (deriv (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal) (t : ℝ)))
  let g := Eᶜ.indicator (fun _ : FieldPair d => ‖c‖)
  have hf := hactual Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
    ρ z hρ E hE A b α r hA hb hr htail
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hg : MemLp g (ENNReal.ofReal p) (reducedLaw Q) :=
    (memLp_const ‖c‖).indicator hE.compl
  have heq : Eᶜ.indicator (fun ω => localSpatialEnergy Q t ρ
      (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) z (G t)
      (deriv (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal) (t : ℝ)) ω + ‖c‖) = f + g := by
    ext ω
    by_cases hω : ω ∈ Eᶜ <;> simp [f, g, hω]
  change MemLp _ _ _ ∧ (eLpNorm _ _ _).toReal ≤ _
  rw [heq]
  refine ⟨hf.1.add hg, ?_⟩
  have htri := eLpNorm_add_le (f := f) (g := g) (μ := reducedLaw Q) hp1
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.1.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩) htri
  rw [ENNReal.toReal_add hf.1.eLpNorm_ne_top hg.eLpNorm_ne_top] at hreal
  have hg_norm : (eLpNorm g (ENNReal.ofReal p) (reducedLaw Q)).toReal =
      ‖c‖ * (reducedLaw Q Eᶜ).toReal ^ (1 / p) := by
    rw [show g = Eᶜ.indicator (fun _ : FieldPair d => ‖c‖) by rfl,
      eLpNorm_indicator_const hE.compl.nullMeasurableSet
        (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top,
      ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hp0.le]
    simp
  rw [hg_norm] at hreal
  exact hreal.trans (add_le_add hf.2 (le_refl _))

theorem c15_flux_block_actual_energy_center_bad_event_absorbed_moment
    (hlt : node_e_u3A_local_u2D_timeStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 1 ≤ p) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
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
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (ht1 : 1 ≤ (t : ℝ)),
      let V := deriv (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (t : ℝ)
      let c := ζ * ∫ ω, ∑ j : Fin d, a j ⟨0, by omega⟩ ω * G t j ω ∂reducedLaw Q
      ∀ (ρ : ℝ) (z : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ)
        (E : Set (FieldPair d)) (hE : MeasurableSet E)
        (A b α r : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b) (hr : 0 < r),
        (reducedLaw Q Eᶜ).toReal ≤ A * Real.exp (-b * r ^ α) →
        MemLp (Eᶜ.indicator (fun ω => localSpatialEnergy Q t ρ
          (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) z (G t) V ω + ‖c‖))
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (Eᶜ.indicator (fun ω => localSpatialEnergy Q t ρ
          (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) z (G t) V ω + ‖c‖))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        A ^ (1 / (2 * p)) * Real.exp (-b * r ^ α / (2 * p)) *
          (C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
            (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
            (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
              FieldPair d → ℂ) (ENNReal.ofReal (2 * p)) (reducedLaw Q)).toReal) := by
  obtain ⟨C₁, K₁, hC₁, hK₁, henergy⟩ :=
    c15_flux_block_actual_energy_center_bad_event_moment hlt d hd D p hp
  obtain ⟨C₂, K₂, hC₂, hK₂, hcenter⟩ :=
    c6_flux_block_centering_time_moment hlt d hd D (2 * p) (by linarith)
  let C := C₁ + C₂ + 1
  let K := max K₁ K₂
  refine ⟨C, K, by dsimp [C]; linarith, lt_of_lt_of_le hK₁ (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht ht1
  dsimp only
  intro ρ z hρ E hE A b α r hA hb hr htail
  have he := henergy Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
    ρ z hρ E hE A b α r hA hb hr htail
  refine ⟨he.1, ?_⟩
  have hc := hcenter Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
  let x := 1 + ‖ζ‖ * Real.sqrt (t : ℝ)
  let q := (reducedLaw Q Eᶜ).toReal
  let F := A ^ (1 / (2 * p)) * Real.exp (-b * r ^ α / (2 * p))
  let N := (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
    FieldPair d → ℂ) (ENNReal.ofReal (2 * p)) (reducedLaw Q)).toReal
  have hp0 : 0 < p := by linarith
  have hx : 1 ≤ x := by
    dsimp [x]
    exact le_add_of_nonneg_right (mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg _))
  have hsqrt : 1 ≤ Real.sqrt (t : ℝ) := by
    exact (Real.le_sqrt (by positivity) ht.le).2 (by nlinarith)
  have hz : ‖ζ‖ ≤ x := by dsimp [x]; nlinarith [norm_nonneg ζ]
  letI := reducedLaw_probability Q
  have hq1 : q ≤ 1 := by
    exact measureReal_le_one (μ := reducedLaw Q) (s := Eᶜ)
  have hqp : q ^ (1 / p) ≤ q ^ (1 / (2 * p)) := by
    apply Real.rpow_le_rpow_of_exponent_ge' ENNReal.toReal_nonneg hq1 (by positivity)
    field_simp
    linarith
  have hqF : q ^ (1 / (2 * p)) ≤ F := by
    have h := Real.rpow_le_rpow (show 0 ≤ q from ENNReal.toReal_nonneg) htail
      (show 0 ≤ 1 / (2 * p) by positivity)
    dsimp [F]
    rw [Real.mul_rpow hA (Real.exp_pos _).le, ← Real.exp_mul] at h
    convert h using 1 <;> congr 1 <;> ring
  have hC₁C : C₁ ≤ C := by dsimp [C]; linarith
  have hC₂C : C₂ + 1 ≤ C := by dsimp [C]; linarith
  have hp₁ := Real.rpow_le_rpow_of_exponent_le hx hC₁C
  have hp₂ := Real.rpow_le_rpow_of_exponent_le hx hC₂C
  have hexp₁ : Real.exp (K₁ * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    gcongr
    exact le_max_left _ _
  have hexp₂ : Real.exp (K₂ * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    gcongr
    exact le_max_right _ _
  have hpow : ‖ζ‖ * x ^ C₂ ≤ x ^ C := by
    calc
      _ ≤ x * x ^ C₂ := mul_le_mul_of_nonneg_right hz (Real.rpow_nonneg (by linarith) _)
      _ = x ^ (C₂ + 1) := by rw [Real.rpow_add (by linarith : 0 < x), Real.rpow_one]; ring
      _ ≤ _ := hp₂
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have htime : 0 ≤ (t : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
  have hq : 0 ≤ q ^ (1 / p) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hqpF : q ^ (1 / p) ≤ F := hqp.trans hqF
  have hbig : 0 ≤ x ^ C := Real.rpow_nonneg (by linarith) _
  have he1 : C₁ * x ^ C₁ ≤ C₁ * x ^ C := mul_le_mul_of_nonneg_left hp₁ (by linarith)
  have he2 : ‖ζ‖ * C₂ * x ^ C₂ ≤ C₂ * x ^ C := by nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ C₂ by linarith)]
  have hsum : C₁ * x ^ C₁ + ‖ζ‖ * C₂ * x ^ C₂ ≤ C * x ^ C := by
    dsimp [C]; nlinarith
  have hterm :
      F * (C₁ * x ^ C₁ * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (K₁ * ‖ζ‖ ^ 2 * (t : ℝ)) * N) +
      (‖ζ‖ * C₂ * x ^ C₂ * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (K₂ * ‖ζ‖ ^ 2 * (t : ℝ)) * N) * q ^ (1 / p) ≤
      F * (C * x ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) * N) := by
    have hpos₁ : 0 ≤ C₁ * x ^ C₁ := by positivity
    have hpos₂ : 0 ≤ ‖ζ‖ * C₂ * x ^ C₂ := by positivity
    have h₁ := mul_le_mul_of_nonneg_left hexp₁ (mul_nonneg hpos₁ htime)
    have h₂ := mul_le_mul_of_nonneg_left hexp₂ (mul_nonneg hpos₂ htime)
    have h₁ := mul_le_mul_of_nonneg_right h₁ hN
    have h₂ := mul_le_mul_of_nonneg_right h₂ hN
    have h₂pos : 0 ≤ ‖ζ‖ * C₂ * x ^ C₂ * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) * N := by positivity
    have hh₁ := mul_le_mul_of_nonneg_left h₁ hF
    have hh₂ := (mul_le_mul_of_nonneg_right h₂ hq).trans
      (mul_le_mul_of_nonneg_left hqpF h₂pos)
    have hs := mul_le_mul_of_nonneg_right hsum htime
    have hs := mul_le_mul_of_nonneg_right hs (Real.exp_pos (K * ‖ζ‖ ^ 2 * (t : ℝ))).le
    have hs := mul_le_mul_of_nonneg_right hs hN
    have hs := mul_le_mul_of_nonneg_left hs hF
    calc
      _ ≤ F * (C₁ * x ^ C₁ * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) * N) +
          (‖ζ‖ * C₂ * x ^ C₂ * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) * N) * F := add_le_add hh₁ hh₂
      _ ≤ _ := by convert hs using 1 <;> ring

  apply he.2.trans
  change F * (C₁ * x ^ C₁ * _ * _ * N) + _ * q ^ (1 / p) ≤ _
  exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hc hq)).trans hterm


theorem c15_flux_block_actual_energy_center_bad_event_probability_moment
    (hlt : node_e_u3A_local_u2D_timeStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 1 ≤ p) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
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
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (ht1 : 1 ≤ (t : ℝ)),
      let V := deriv (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (t : ℝ)
      let c := ζ * ∫ ω, ∑ j : Fin d, a j ⟨0, by omega⟩ ω * G t j ω ∂reducedLaw Q
      ∀ (ρ : ℝ) (z : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ)
        (E : Set (FieldPair d)) (hE : MeasurableSet E),
        MemLp (Eᶜ.indicator (fun ω => localSpatialEnergy Q t ρ
          (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) z (G t) V ω + ‖c‖))
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (Eᶜ.indicator (fun ω => localSpatialEnergy Q t ρ
          (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) z (G t) V ω + ‖c‖))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (reducedLaw Q Eᶜ).toReal ^ (1 / (2 * p)) *
          (C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
            (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
            (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
              FieldPair d → ℂ) (ENNReal.ofReal (2 * p)) (reducedLaw Q)).toReal) := by
  obtain ⟨C₁, K₁, hC₁, hK₁, henergy⟩ :=
    EinsteinFull.Blueprint.carverS_flux_block_local_time_on_flux_witness hlt d hd D (2 * p) (by linarith)
  obtain ⟨C₂, K₂, hC₂, hK₂, hcenter⟩ :=
    c6_flux_block_centering_time_moment hlt d hd D (2 * p) (by linarith)
  let C := C₁ + C₂ + 1
  let K := max K₁ K₂
  refine ⟨C, K, by dsimp [C]; linarith, lt_of_lt_of_le hK₁ (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht ht1
  dsimp only
  intro ρ z hρ E hE
  obtain ⟨hmem, hbound⟩ := henergy Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht ρ z hρ
  have he := c15_flux_block_energy_and_center_bad_event Q t ρ _ z (G t) _
    ⟨0, by omega⟩ ζ a E hE p hp hmem
  refine ⟨he.1, ?_⟩
  have hc := hcenter Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
  let x := 1 + ‖ζ‖ * Real.sqrt (t : ℝ)
  let q := (reducedLaw Q Eᶜ).toReal
  let F := q ^ (1 / (2 * p))
  let N := (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
    FieldPair d → ℂ) (ENNReal.ofReal (2 * p)) (reducedLaw Q)).toReal
  have hp0 : 0 < p := by linarith
  have hx : 1 ≤ x := by
    dsimp [x]
    exact le_add_of_nonneg_right (mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg _))
  have hsqrt : 1 ≤ Real.sqrt (t : ℝ) := by
    exact (Real.le_sqrt (by positivity) ht.le).2 (by nlinarith)
  have hz : ‖ζ‖ ≤ x := by dsimp [x]; nlinarith [norm_nonneg ζ]
  letI := reducedLaw_probability Q
  have hq1 : q ≤ 1 := by
    exact measureReal_le_one (μ := reducedLaw Q) (s := Eᶜ)
  have hqp : q ^ (1 / p) ≤ q ^ (1 / (2 * p)) := by
    apply Real.rpow_le_rpow_of_exponent_ge' ENNReal.toReal_nonneg hq1 (by positivity)
    field_simp
    linarith
  have hC₁C : C₁ ≤ C := by dsimp [C]; linarith
  have hC₂C : C₂ + 1 ≤ C := by dsimp [C]; linarith
  have hp₁ := Real.rpow_le_rpow_of_exponent_le hx hC₁C
  have hp₂ := Real.rpow_le_rpow_of_exponent_le hx hC₂C
  have hexp₁ : Real.exp (K₁ * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    gcongr
    exact le_max_left _ _
  have hexp₂ : Real.exp (K₂ * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    gcongr
    exact le_max_right _ _
  have hpow : ‖ζ‖ * x ^ C₂ ≤ x ^ C := by
    calc
      _ ≤ x * x ^ C₂ := mul_le_mul_of_nonneg_right hz (Real.rpow_nonneg (by linarith) _)
      _ = x ^ (C₂ + 1) := by rw [Real.rpow_add (by linarith : 0 < x), Real.rpow_one]; ring
      _ ≤ _ := hp₂
  have hF : 0 ≤ F := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have htime : 0 ≤ (t : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
  have hq : 0 ≤ q ^ (1 / p) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hqpF : q ^ (1 / p) ≤ F := hqp
  have hbig : 0 ≤ x ^ C := Real.rpow_nonneg (by linarith) _
  have he1 : C₁ * x ^ C₁ ≤ C₁ * x ^ C := mul_le_mul_of_nonneg_left hp₁ (by linarith)
  have he2 : ‖ζ‖ * C₂ * x ^ C₂ ≤ C₂ * x ^ C := by nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ C₂ by linarith)]
  have hsum : C₁ * x ^ C₁ + ‖ζ‖ * C₂ * x ^ C₂ ≤ C * x ^ C := by
    dsimp [C]; nlinarith
  have hterm :
      F * (C₁ * x ^ C₁ * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (K₁ * ‖ζ‖ ^ 2 * (t : ℝ)) * N) +
      (‖ζ‖ * C₂ * x ^ C₂ * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (K₂ * ‖ζ‖ ^ 2 * (t : ℝ)) * N) * q ^ (1 / p) ≤
      F * (C * x ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) * N) := by
    have hpos₁ : 0 ≤ C₁ * x ^ C₁ := by positivity
    have hpos₂ : 0 ≤ ‖ζ‖ * C₂ * x ^ C₂ := by positivity
    have h₁ := mul_le_mul_of_nonneg_left hexp₁ (mul_nonneg hpos₁ htime)
    have h₂ := mul_le_mul_of_nonneg_left hexp₂ (mul_nonneg hpos₂ htime)
    have h₁ := mul_le_mul_of_nonneg_right h₁ hN
    have h₂ := mul_le_mul_of_nonneg_right h₂ hN
    have h₂pos : 0 ≤ ‖ζ‖ * C₂ * x ^ C₂ * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) * N := by positivity
    have hh₁ := mul_le_mul_of_nonneg_left h₁ hF
    have hh₂ := (mul_le_mul_of_nonneg_right h₂ hq).trans
      (mul_le_mul_of_nonneg_left hqpF h₂pos)
    have hs := mul_le_mul_of_nonneg_right hsum htime
    have hs := mul_le_mul_of_nonneg_right hs (Real.exp_pos (K * ‖ζ‖ ^ 2 * (t : ℝ))).le
    have hs := mul_le_mul_of_nonneg_right hs hN
    have hs := mul_le_mul_of_nonneg_left hs hF
    calc
      _ ≤ F * (C₁ * x ^ C₁ * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) * N) +
          (‖ζ‖ * C₂ * x ^ C₂ * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) * N) * F := add_le_add hh₁ hh₂
      _ ≤ _ := by convert hs using 1 <;> ring

  apply he.2.trans
  exact (add_le_add (mul_le_mul_of_nonneg_left hbound hF)
    (mul_le_mul_of_nonneg_right hc hq)).trans hterm

private lemma c15_coord_le_euclideanNorm {d : ℕ} (x : Vec d) (j : Fin d) :
    |x j| ≤ euclideanNorm x := by
  rw [TimeChange.euclideanNorm_eq_norm_toLp]
  exact PiLp.norm_apply_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) j

private theorem c15_norm_unitVector_le {d : ℕ} (i k : Fin d) :
    ‖((unitVector i k : ℝ) : ℂ)‖ ≤ 1 := by
  by_cases h : k = i
  · subst h; simp [unitVector]
  · simp [unitVector, Pi.single_apply, h]

/-- Pointwise bound of the flux formula from bounds on its ingredients. -/
private theorem c15_norm_flux_le {d : ℕ} (A B : ℝ) (hA : 0 ≤ A)
    (c a G e : Fin d → ℂ)
    (hc : ∀ k, ‖a k - c k‖ ≤ A) (hG : ∀ k, ‖G k‖ ≤ B)
    (he : ∀ k, ‖e k‖ ≤ 8 * B) :
    ‖∑ k : Fin d, (a k - c k) * (G k - e k)‖ ≤ d * (A * (B + 8 * B)) := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k ∈ (Finset.univ : Finset (Fin d)), ‖(a k - c k) * (G k - e k)‖ ≤ A * (B + 8 * B) := by
    intro k _
    rw [norm_mul]
    exact mul_le_mul (hc k) ((norm_sub_le _ _).trans (add_le_add (hG k) (he k)))
      (norm_nonneg _) hA
  refine (Finset.sum_le_sum this).trans ?_
  simp


theorem c15_actual_weak_flux_ae_bound_of_crude
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
    ∀ j : Fin d, ∀ᵐ ω ∂reducedLaw Q, ‖J t j ω‖ ≤ C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
  obtain ⟨C1, Cp, hC1, hCp, hlt'⟩ := hlt d hd D 2 le_rfl
  obtain ⟨C, N, hC, hcr'⟩ := hcr d hd D
  let K : ℝ := max C (max 1 ((d : ℝ) * (2 * |sourceReducedBound D.ellipticity| * (9 * C))))
  have hKC : C ≤ K := le_max_left _ _
  have hK1 : 1 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKbig : (d : ℝ) * (2 * |sourceReducedBound D.ellipticity| * (9 * C)) ≤ K :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, N, hK1, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν G J hGJ t ht j
  have hGJ := hGJ t (lt_of_lt_of_le one_pos ht)
  letI := EinsteinFull.reducedLaw_probability Q
  have ht0 : 0 < (t : ℝ) := lt_of_lt_of_le one_pos ht
  obtain ⟨Glt, V, hGlt, -⟩ := hlt' Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨Gc, hGc1, hGc2⟩ := hcr' Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨h1, h2, -⟩ := hGlt t ht0
  have hG : G t = Glt t := hGJ.1.unique h1
  have hGc : Gc t = Glt t := (hGc1 t ht).unique h2
  have hcrude := (hGc2 t ht hζ).1
  set B : ℝ := C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) with hBdef
  have hB : 0 ≤ B := by positivity
  have hGb : ∀ᵐ ω ∂reducedLaw Q, ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ≤ B ∧
      ∀ k, ‖G t k ω‖ ≤ B := by
    filter_upwards [hcrude] with ω hω
    refine ⟨(le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hω, fun k => ?_⟩
    have hk : ‖G t k ω‖ ≤ Real.sqrt (∑ j : Fin d, ‖Gc t j ω‖ ^ 2) := by
      rw [hG, ← hGc]
      apply Real.le_sqrt_of_sq_le
      exact Finset.single_le_sum (f := fun j : Fin d => ‖Gc t j ω‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    exact hk.trans ((le_add_of_nonneg_left (norm_nonneg _)).trans hω)
  have hUb : ∀ᵐ ω ∂reducedLaw Q, ν = Sum.inr true →
      ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ≤ B := by
    filter_upwards [hGb] with ω hω hν
    subst hν
    exact hω.1
  have hcoef := EinsteinFull.Calculus.C2TestReplacement.ae_abs_reducedCoefficient_entry_le Q
  have haa : ∀ k, (a j k : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => (ω.1 0 j k : ℂ) :=
    fun k => ha j k
  have haall : ∀ᵐ ω ∂reducedLaw Q, ∀ k, a j k ω = (ω.1 0 j k : ℂ) := by
    rw [ae_all_iff]; exact haa
  have hJj := hGJ.2 j
  set A : ℝ := 2 * |sourceReducedBound D.ellipticity| with hAdef
  have hA : 0 ≤ A := by positivity
  have hbound : ∀ᵐ ω ∂reducedLaw Q, ‖(J t j : FieldPair d → ℂ) ω‖ ≤ d * (A * (B + 8 * B)) := by
    filter_upwards [hJj, hcoef, haall, hGb, hUb] with ω hJω hcω haω hGω hUω
    rw [hJω]
    refine c15_norm_flux_le A B hA _ _ _ _ ?_ ?_ ?_
    swap
    · intro k; exact hGω.2 k
    · intro k
      rw [haω k]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := hcω j k
      have h2 : |homogenizedCoefficient Q j k| ≤ sourceReducedBound D.ellipticity := by
        have hh := (c15_coord_le_euclideanNorm
          ((homogenizedCoefficient Q).mulVec (unitVector k)) j).trans
          (homogenizedCoefficient_column_bound Q k)
        simpa [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply] using hh
      have := add_le_add (h1.trans (le_abs_self _)) (h2.trans (le_abs_self _))
      dsimp [A]; linarith
    · intro k
      cases ν with
      | inl i => simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hB
      | inr b =>
        cases b with
        | false => simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hB
        | true =>
          have hU := hUω rfl
          simp only [norm_mul]
          have hu := c15_norm_unitVector_le (⟨0, by omega⟩ : Fin d) k
          have h2' : ‖(2 : ℂ)‖ = 2 := by simp
          have h2 : ‖(2 : ℂ)‖ * ‖ζ‖ ≤ 8 := by rw [h2']; linarith
          calc _ ≤ (8 : ℝ) * 1 * B := by
                gcongr
            _ = 8 * B := by ring
  filter_upwards [hbound] with ω hω
  refine hω.trans ?_
  have hexp : Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    gcongr
  have hp : 0 ≤ (2 + (t : ℝ)) ^ N := by positivity
  have he : 0 ≤ Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := (Real.exp_pos _).le
  dsimp [A, B]
  calc
    _ = ((d : ℝ) * (2 * |sourceReducedBound D.ellipticity| * (9 * C))) *
        (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by ring
    _ ≤ K * (2 + (t : ℝ)) ^ N * Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) := by
      gcongr


/-- Every finite moment of the actual weak flux obeys the structural bound. -/
theorem c15_actual_weak_flux_all_finite_moments_of_crude
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
    ∀ (p : ℝ), 1 ≤ p → ∀ j : Fin d,
      MemLp (J t j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (J t j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
  obtain ⟨C, N, hC, hb⟩ := c15_actual_weak_flux_ae_bound_of_crude hlt hcr d hd D
  refine ⟨C, N, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν G J hGJ t ht p hp j
  letI := EinsteinFull.reducedLaw_probability Q
  have hbound := hb Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν G J hGJ t ht j
  have hnonneg : 0 ≤ C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    positivity
  exact ⟨MemLp.of_bound (Lp.memLp _).aestronglyMeasurable _ hbound,
    AnnuliSupport.eLpNorm_toReal_le_of_ae_norm_le (Lp.memLp _).aestronglyMeasurable
      hnonneg hbound⟩


/-- The essential supremum of the actual weak flux obeys the structural bound. -/
theorem c15_actual_weak_flux_essential_supremum_of_crude
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
    ∀ j : Fin d,
      MemLp (J t j : FieldPair d → ℂ) (⊤ : ENNReal) (reducedLaw Q) ∧
      (eLpNorm (J t j : FieldPair d → ℂ) (⊤ : ENNReal) (reducedLaw Q)).toReal ≤
        C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
  obtain ⟨C, N, hC, hb⟩ := c15_actual_weak_flux_ae_bound_of_crude hlt hcr d hd D
  refine ⟨C, N, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν G J hGJ t ht j
  letI := EinsteinFull.reducedLaw_probability Q
  have hbound := hb Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν G J hGJ t ht j
  have hnonneg : 0 ≤ C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    positivity
  exact ⟨MemLp.of_bound (Lp.memLp _).aestronglyMeasurable _ hbound,
    AnnuliSupport.eLpNorm_toReal_le_of_ae_norm_le (Lp.memLp _).aestronglyMeasurable
      hnonneg hbound⟩

end EinsteinFull.Calculus
