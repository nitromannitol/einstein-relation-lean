import EinsteinFull.Calculus.C9ShortTimeLocality
import EinsteinFull.Calculus.ComplexForceDriftSupport

/-! Internal support for the actual first-unit flux approximation.
The Gaussian cutoff comparison remains a separate, unproved obligation. -/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.C9DyadicIncrements
open EinsteinRelation

variable {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)

/-- Actual anisotropic coefficient multiplication preserves locality in every
positive-radius joint coefficient/clock ball. -/
theorem complexCoefficientMul_isLocal {ρ : ℝ} (hρ : 0 < ρ)
    (j k : Fin d) {f : Lp ℂ 2 (reducedLaw Q)}
    (hf : IsComplexLocalObservation Q ρ f) :
    IsComplexLocalObservation Q ρ (complexCoefficientMul Q j k f) := by
  obtain ⟨g, hg, hgf⟩ := hf
  have h0 : (0 : Vec d) ∈ {x : Vec d | euclideanNorm x < ρ} := by
    simpa only [Set.mem_setOf_eq, euclideanNorm, euclideanSq, dot,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, Real.sqrt_zero] using hρ
  have heval : Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}]
      (fun ω : FieldPair d => (ω.1 0, ω.2 0)) := by
    rw [measurable_iff_comap_le]
    exact le_iSup (fun y : {x : Vec d | euclideanNorm x < ρ} => MeasurableSpace.comap
      (fun ω : FieldPair d => (ω.1 y, ω.2 y)) inferInstance) ⟨0, h0⟩
  have hentry : Measurable (fun p : Mat d × ℝ => (p.1 j k : ℂ)) :=
    Complex.measurable_ofReal.comp (continuous_fst.matrix_elem j k).measurable
  refine ⟨fun ω => (ω.1 0 j k : ℂ) * g ω, (hentry.comp heval).mul hg, ?_⟩
  filter_upwards [complexCoefficientMul_coe Q j k f, hgf] with ω hmul hgf
  rw [hmul, hgf]

/-- The coefficient error is controlled by its structural operator norm. -/
theorem norm_complexCoefficientMul_sub_le (j k : Fin d)
    (f v : Lp ℂ 2 (reducedLaw Q)) :
    ‖complexCoefficientMul Q j k f - complexCoefficientMul Q j k v‖ ≤
      (Real.exp (2 * Λ) * Λ) * ‖f - v‖ := by
  rw [← map_sub]
  exact ((complexCoefficientMul Q j k).le_opNorm (f - v)).trans
    (mul_le_mul_of_nonneg_right (norm_complexCoefficientMul_le Q j k) (norm_nonneg _))

/-- A time-integrated projected gradient stays local after multiplication by
the actual coefficient. This uses the joint sigma algebra at the same radius. -/
theorem complexCoefficientMul_integral_projection_isLocal
    {ρ : ℝ} (hρ : 0 < ρ) (j k : Fin d)
    {f : ℝ → Lp ℂ 2 (reducedLaw Q)}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) 1)) :
    IsComplexLocalObservation Q ρ
      (complexCoefficientMul Q j k
        (∫ t in Set.Icc (0 : ℝ) 1, C9ShortTimeLocality.localProjection Q ρ (f t))) :=
  complexCoefficientMul_isLocal Q hρ j k
    (C9ShortTimeLocality.integral_localProjection_isLocal Q ρ hf)

/-- Assemble local gradient and transpose inputs with the actual coefficient
row and the exact signed-force transpose correction from the flux formula. -/
theorem fluxCombination_isLocal
    (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) (ζ : ℂ) (ν : FluxIndex d)
    (j : Fin d) (g : Fin d → Lp ℂ 2 (reducedLaw Q))
    (u : Lp ℂ 2 (reducedLaw Q))
    (hg : ∀ k, IsComplexLocalObservation Q ρ (g k))
    (hu : IsComplexLocalObservation Q ρ u) :
    IsComplexLocalObservation Q ρ
      ((∑ k : Fin d, complexCoefficientMul Q j k (g k)) -
        ν.elim (fun _ => 0) (fun _ => (2 * ζ) •
          complexCoefficientMul Q j ⟨0, by omega⟩ u)) := by
  have hsum : C9ShortTimeLocality.localProjection Q ρ
      (∑ k : Fin d, complexCoefficientMul Q j k (g k)) =
        ∑ k : Fin d, complexCoefficientMul Q j k (g k) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact C9ShortTimeLocality.localProjection_of_isLocal Q ρ
      (complexCoefficientMul_isLocal Q hρ j k (hg k))
  have htranspose : C9ShortTimeLocality.localProjection Q ρ
      (ν.elim (fun _ => 0) (fun _ => (2 * ζ) •
        complexCoefficientMul Q j ⟨0, by omega⟩ u)) =
      ν.elim (fun _ => 0) (fun _ => (2 * ζ) •
        complexCoefficientMul Q j ⟨0, by omega⟩ u) := by
    cases ν with
    | inl i => simp only [Sum.elim_inl, map_zero]
    | inr b =>
      simp only [Sum.elim_inr, map_smul]
      rw [C9ShortTimeLocality.localProjection_of_isLocal Q ρ
        (complexCoefficientMul_isLocal Q hρ j ⟨0, by omega⟩ hu)]
  have he := C9ShortTimeLocality.localProjection_isLocal Q ρ
    ((∑ k : Fin d, complexCoefficientMul Q j k (g k)) -
      ν.elim (fun _ => 0) (fun _ => (2 * ζ) •
        complexCoefficientMul Q j ⟨0, by omega⟩ u))
  rwa [map_sub, hsum, htranspose] at he

/-- Subtracting the initial flux cancels exactly the coefficient column.
Both the integrated gradient and the signed transpose correction are retained. -/
theorem finiteTimeFlux_sub_zero_coe
    (hd : 2 ≤ d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (τ : ℝ≥0) (ν : FluxIndex d) (j : Fin d) :
    (F τ ν j - F 0 ν j : Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
      fun ω => (∑ k : Fin d, a j k ω *
        (∫ r in Set.Icc (0 : ℝ) (τ : ℝ), G r.toNNReal ν k) ω) -
        ν.elim (fun _ => 0) (fun _ => 2 * ζ * a j ⟨0, by omega⟩ ω *
          (∫ r in Set.Icc (0 : ℝ) (τ : ℝ),
            transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal) ω) := by
  obtain ⟨hG, hU, _, hF⟩ := hF
  filter_upwards [hF τ ν j, hF 0 ν j, Lp.coeFn_sub (F τ ν j) (F 0 ν j),
    Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω ht h0 hsub hz
  change (0 : Lp ℂ 2 (reducedLaw Q)) ω = 0 at hz
  simp only [finiteTimeFluxObservation, NNReal.coe_zero, Set.Icc_self,
    integral_singleton, measureReal_def, measure_singleton, ENNReal.toReal_zero,
    zero_smul] at h0
  have hinit : (F 0 ν j) ω = a j (ν.elim id (fun _ => ⟨0, by omega⟩)) ω := by
    cases ν <;> simpa only [Sum.elim_inl, Sum.elim_inr, hz, mul_zero,
      Finset.sum_const_zero, add_zero, sub_zero] using h0
  rw [hsub]
  change (F τ ν j) ω - (F 0 ν j) ω = _
  rw [ht, hinit]
  simp only [finiteTimeFluxObservation]
  ring

end EinsteinFull.C9DyadicIncrements
