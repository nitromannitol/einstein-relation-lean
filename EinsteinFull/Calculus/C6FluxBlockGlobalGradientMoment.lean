import EinsteinFull.Calculus.CarverSFluxBlockGain

open MeasureTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- Local-time control bounds the global gradient of the supplied flux. -/
theorem c6_flux_block_global_gradient_moment
    (hlt : node_e_u3A_local_u2D_timeStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p) :
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
    ∀ (t : ℝ≥0), 0 < (t : ℝ) →
      (∑ j : Fin d, ‖G t j‖) ≤
        (d : ℝ) * C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
        (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  obtain ⟨C, Cp, hC, hCp, hlocal⟩ :=
    carverS_flux_block_local_time_on_flux_witness hlt d hd D p hp
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
  let ρ := Real.sqrt (t : ℝ)
  have hρ : 0 < ρ := Real.sqrt_pos.mpr ht
  let V := deriv (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal) (t : ℝ)
  obtain ⟨hE, hbound⟩ := hlocal Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht ρ 0 le_rfl
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hp' : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hLp : Calculus.S1.l2Size (reducedLaw Q)
      (localSpatialEnergy Q t ρ hρ 0 (G t) V) ≤
      (eLpNorm (localSpatialEnergy Q t ρ hρ 0 (G t) V)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
    rw [Calculus.S1.l2Size_eq_norm_toLp (hE.mono_exponent hp'), Lp.norm_toLp]
    exact ENNReal.toReal_mono hE.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hp')
  have hsum : (∑ j : Fin d, ‖G t j‖) ≤ (d : ℝ) *
      (eLpNorm (localSpatialEnergy Q t ρ hρ 0 (G t) V)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      (carverS_flux_block_global_gradient_l2_le_energy Q t ρ hρ 0 (G t) V j).trans hLp)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  calc
    _ ≤ (d : ℝ) * (eLpNorm (localSpatialEnergy Q t ρ hρ 0 (G t) V)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal := hsum
    _ ≤ (d : ℝ) * (C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
        (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) :=
      mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg d)
    _ = _ := by ring


/-- The centering integral inherits the local-time moment of the same flux. -/
theorem c6_flux_block_centering_time_moment
    (hlt : node_e_u3A_local_u2D_timeStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p) :
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
    ∀ (t : ℝ≥0), 0 < (t : ℝ) →
      ‖ζ * ∫ ω, ∑ j : Fin d, a j ⟨0, by omega⟩ ω * G t j ω ∂reducedLaw Q‖ ≤
        ‖ζ‖ * C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
        (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  obtain ⟨A, Cp, hA, hCp, hgrad⟩ := c6_flux_block_global_gradient_moment hlt d hd D p hp
  obtain ⟨M, hM, hcenter⟩ := carverS_flux_block_centering_integral_bound d hd D
  let C := max A (M * (d : ℝ) * A) + 1
  have hAC : A ≤ C := by dsimp [C]; linarith [le_max_left A (M * (d : ℝ) * A)]
  have hMC : M * (d : ℝ) * A ≤ C := by
    dsimp [C]; linarith [le_max_right A (M * (d : ℝ) * A)]
  refine ⟨C, Cp, by linarith, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
  have hbase : 1 ≤ 1 + ‖ζ‖ * Real.sqrt (t : ℝ) :=
    le_add_of_nonneg_right (mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg _))
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase hAC
  have hg := hgrad Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
  calc
    _ ≤ ‖ζ‖ * M * ∑ j : Fin d, ‖G t j‖ := hcenter Q a ha (G t) ζ
    _ ≤ ‖ζ‖ * M * ((d : ℝ) * A * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ A *
        (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) :=
      mul_le_mul_of_nonneg_left hg (mul_nonneg (norm_nonneg ζ) (by linarith))
    _ ≤ _ := by
      have hprod : M * (d : ℝ) * A * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ A ≤
          C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C :=
        mul_le_mul hMC hpow (Real.rpow_nonneg (by positivity) _) (by linarith)
      have hh := mul_le_mul_of_nonneg_left hprod (norm_nonneg ζ)
      have hh := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg ht.le (-(1 / 2 : ℝ)))
      have hh := mul_le_mul_of_nonneg_right hh (Real.exp_pos (Cp * ‖ζ‖ ^ 2 * (t : ℝ))).le
      have hh := mul_le_mul_of_nonneg_right hh (ENNReal.toReal_nonneg (a :=
        eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)))
      convert hh using 1 <;> ring

end EinsteinFull.Blueprint
