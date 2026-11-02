import EinsteinFull.Calculus.C6DyadicIncrementsAssembly
import EinsteinFull.Calculus.C19FirstUnitFluxLocality
import EinsteinFull.Calculus.C8DyadicTransposeFluxSize
import EinsteinFull.Blueprint.G3.node_e_u3A_time_u2D_flux

/-! Actual witnesses and the available estimates for the dyadic-increments root.

The full-window transpose primitive decay is still pending. This file does not
declare the graph root until it is available. The support result keeps the
primitive explicit in a proved bound and retains first-unit flux locality.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The original three graph dependencies give the same actual flux witnesses,
with a structural constant for size, decomposition, locality and the remaining
transpose primitive multiplier. No primitive estimate is assumed. -/
theorem c6_dyadic_increments_data_of_deps
    (henergy : node_e_u3A_energy_u2D_targetStmt)
    (hlocal : node_l_u3A_forced_u2D_localStmt)
    (hflux : node_e_u3A_time_u2D_fluxStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
      ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
        IsComplexTransposeSemigroup Q P Pdag →
      ∃ G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
        IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F ∧
      (‖ζ‖ ≤ 2 → ∀ ν : FluxIndex d,
        Real.sqrt (∑ j : Fin d, ‖F 1 ν j - F 0 ν j‖ ^ 2) ≤ C ∧
        ∀ n : ℕ, 1 ≤ n → ∃ V : Fin d → Lp ℂ 2 (reducedLaw Q),
          (∀ j, IsComplexLocalObservation Q (C * n) (V j)) ∧
          Real.sqrt (∑ j : Fin d, ‖F 1 ν j - F 0 ν j - V j‖ ^ 2) ≤
            C * Real.exp (-c * (n : ℝ) ^ 2)) ∧
      ∀ s u : ℝ≥0, 1 ≤ (s : ℝ) → s ≤ u → u ≤ 2 * s →
        ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) ≤ 2 → ∀ ν : FluxIndex d,
      ∃ Y B : Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ j, (Y j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          fun ω => ∑ k : Fin d, a j k ω *
            (∫ r in Set.Icc (s : ℝ) (u : ℝ), G r.toNNReal ν k) ω) ∧
        (∀ j, (B j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          fun ω => ν.elim (fun _ => 0) (fun _ =>
            -2 * ζ * a j ⟨0, by omega⟩ ω *
              (∫ r in Set.Icc (s : ℝ) (u : ℝ),
                transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal) ω)) ∧
        (∀ j, F u ν j - F s ν j = Y j + B j) ∧
        Real.sqrt (∑ j : Fin d, ‖Y j‖ ^ 2) ≤ C * (s : ℝ) ^ (-(d : ℝ) / 4) ∧
        (∀ j, B j = ν.elim (fun _ => 0) (fun _ => (-2 * ζ) •
          complexCoefficientMul Q j ⟨0, by omega⟩
            (∫ r in Set.Icc (s : ℝ) (u : ℝ),
              transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal))) ∧
        Real.sqrt (∑ j : Fin d, ‖B j‖ ^ 2) ≤
          C * ‖∫ r in Set.Icc (s : ℝ) (u : ℝ),
            transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal‖ /
              Real.sqrt (s : ℝ) ∧
        ∀ n : ℕ, 1 ≤ n → ∃ V : Fin d → Lp ℂ 2 (reducedLaw Q),
          (∀ j, IsComplexLocalObservation Q (C * n * Real.sqrt (s : ℝ)) (V j)) ∧
          Real.sqrt (∑ j : Fin d, ‖F u ν j - F s ν j - V j‖ ^ 2) ≤
            C * (2 + (s : ℝ)) ^ N * Real.exp (-c * (n : ℝ) ^ 2) := by
  intro d hd D
  obtain ⟨C₀, c₀, N, hC₀, hc₀, hdata⟩ :=
    c6_dyadic_gradient_flux_decomposition_and_locality henergy hlocal d hd D
  obtain ⟨C₁, c₁, hC₁, hc₁, hunit⟩ :=
    c19_first_unit_flux_locality hlocal d hd D
  let A : ℝ := 4 * (d : ℝ) * (Real.exp (2 * D.ellipticity) * D.ellipticity)
  let C := max C₀ (max C₁ A)
  let c := min c₀ c₁
  have h₀ : C₀ ≤ C := le_max_left _ _
  have h₁ : C₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hA : A ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hC : 1 ≤ C := hC₀.trans h₀
  have hc : 0 < c := lt_min hc₀ hc₁
  have he₀ (x : ℝ) : Real.exp (-c₀ * x ^ 2) ≤ Real.exp (-c * x ^ 2) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left c₀ c₁)) (sq_nonneg x))
  have he₁ (x : ℝ) : Real.exp (-c₁ * x ^ 2) ≤ Real.exp (-c * x ^ 2) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right c₀ c₁)) (sq_nonneg x))
  refine ⟨C, c, N, hC, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd
  obtain ⟨G, F, hF, _hweak⟩ := hflux d hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd
  obtain ⟨_hfirst, hdyadic⟩ := hdata Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF
  refine ⟨G, F, hF, ?_, ?_⟩
  · intro hζ ν
    obtain ⟨hsize, hlocality⟩ :=
      hunit Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF hζ ν
    refine ⟨hsize.trans h₁, ?_⟩
    intro n hn
    obtain ⟨V, hV, herror⟩ := hlocality n hn
    refine ⟨V, ?_, herror.trans ?_⟩
    · intro j
      obtain ⟨v, hv, hveq⟩ := hV j
      refine ⟨v, hv.mono (Probability.localSigma_mono ?_) le_rfl, hveq⟩
      intro x hx
      exact lt_of_lt_of_le hx (mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg n))
    · exact (mul_le_mul_of_nonneg_right h₁ (Real.exp_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (he₁ n) (zero_le_one.trans hC))
  intro s u hs hsu hus hζ ν
  obtain ⟨Y, B, hY, hB, hsplit, hsize, hBeq, hlocality⟩ :=
    hdyadic s u hs hsu hus hζ ν
  refine ⟨Y, B, hY, hB, hsplit, hsize.trans ?_, hBeq, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right h₀ (Real.rpow_nonneg s.coe_nonneg _)
  · simp_rw [hBeq]
    cases ν with
    | inl ν =>
      simp only [Sum.elim_inl, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
        Finset.sum_const_zero, Real.sqrt_zero]
      exact div_nonneg (mul_nonneg (zero_le_one.trans hC) (norm_nonneg _))
        (Real.sqrt_nonneg _)
    | inr ν =>
      simp only [Sum.elim_inr]
      exact (dyadic_transpose_flux_primitive_reduction Q ⟨0, by omega⟩ β ζ Pdag
        s u hs hζ).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
          (Real.sqrt_nonneg _))
  · intro n hn
    obtain ⟨V, hV, herror⟩ := hlocality n hn
    have hR : C₀ * n * Real.sqrt (s : ℝ) ≤ C * n * Real.sqrt (s : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₀ (Nat.cast_nonneg n))
        (Real.sqrt_nonneg _)
    refine ⟨V, ?_, herror.trans ?_⟩
    · intro j
      obtain ⟨v, hv, hveq⟩ := hV j
      refine ⟨v, hv.mono (Probability.localSigma_mono ?_) le_rfl, hveq⟩
      intro x hx
      exact lt_of_lt_of_le hx hR
    · exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h₀ (pow_nonneg (by positivity) N))
        (Real.exp_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (he₀ n)
          (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (by positivity) N)))

end EinsteinFull.Blueprint
