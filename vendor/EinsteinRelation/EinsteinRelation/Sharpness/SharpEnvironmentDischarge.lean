import EinsteinRelation.Sharpness.SharpOrbitPotential
import EinsteinRelation.Sharpness.SharpEnvironmentMeans

/-! # Environment identities for the white-noise sharpness example

Source: `paper/main.tex` 1212–1238 and 1259–1265. The bounded orbit potential identifies the
canonical corrector, and nondegeneracy of the white-noise seed makes its mean energy positive.
The white-noise law is retained explicitly: `IsSharpLaw` alone does not assert that property.
-/

open MeasureTheory
open EinsteinRelation.Correctors

namespace EinsteinRelation.Sharpness

/-- The constant harmonic flux identifies the homogenized column of the sharp physical law.
Source: `paper/main.tex` 1234–1238. -/
theorem sharp_abar_mulVec_unitVector {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (P : Measure (NoiseSample d)) (hε : 0 < ε) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : Q.measure = P.map (sharpPhysicalPair i δ ε hgrad hμ)) :
    (abar Q).mulVec (unitVector i) = unitVector i := by
  have heq : clippedSharpGradient i =ᵐ[Q.measure] sharpGradientField i := by
    rw [hQ]
    exact clippedSharpGradient_ae_eq i δ ε hgrad hμ P
  have horbit : ∀ᵐ ω ∂Q.measure, ∃ φ : Vec d → ℝ,
      ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ 2 * ε) ∧
        ∀ x, gradient φ x = clippedSharpGradient i (translate x ω) := by
    rw [hQ]
    exact ae_clippedSharpGradient_orbit i δ ε hgrad hμ P hε
  have hharm : ∀ᵐ ω ∂Q.measure,
      (reducedCoefficient ω 0).mulVec (unitVector i + clippedSharpGradient i ω) =
        unitVector i := by
    filter_upwards [heq, ae_sharpGradientField_harmonic_zero Q i] with ω hω hωharm
    rw [hω]
    exact hωharm
  have hflux := (gradient_field_corrector_identification_of_orbit Q i
    (clippedSharpGradient i) (2 * ε) (measurable_clippedSharpGradient i)
    (clippedSharpGradient_norm_le i) horbit hharm).2
  ext j
  simpa [abar, Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, correctorUnitVector]
    using congrArg (fun v : EuclideanSpace ℝ (Fin d) => v j) hflux

/-- All environment-level identities of Proposition 7.1 for a physical pair driven by a genuine
white-noise law. Source: `paper/main.tex` 1231, 1234–1238 and 1259–1265. -/
theorem sharpEnvironmentInput_of_whiteNoise {d : ℕ} (hd : 2 ≤ d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField ⟨0, by omega⟩ δ (fun y => ε * seedField d W y) x ∧
      densityField ⟨0, by omega⟩ δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P)
    (hδ : 0 < δ) (hε : 0 < ε) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : Q.measure = P.map (sharpPhysicalPair ⟨0, by omega⟩ δ ε hgrad hμ)) :
    SharpEnvironmentInput hd Q := by
  have hsharp : IsSharpLaw hd δ Q := ⟨hδ, ε, P, hgrad, hμ, hε, hQ⟩
  apply sharpEnvironmentInput_of_corrector hd δ Q hsharp
  · exact measurable_sharpGradientField ⟨0, by omega⟩
  · change ∀ᵐ ω ∂Q.measure, euclideanNorm (sharpGradientField ⟨0, by omega⟩ ω) ≤ 1 / 4
    rw [hQ]
    exact ae_sharpGradientField_norm_le ⟨0, by omega⟩ δ ε hgrad hμ P
  · change 0 < ∫ ω, sharpEnergy ⟨0, by omega⟩ (sharpGradientField ⟨0, by omega⟩ ω) ∂Q.measure
    rw [hQ]
    exact integral_sharpGradientField_energy_pos ⟨0, by omega⟩ δ ε hgrad hμ hP hε
  · exact sharp_abar_mulVec_unitVector ⟨0, by omega⟩ δ ε hgrad hμ P hε Q hQ

/-- A smooth sharp environment with all its environment identities, retaining the white-noise
witness needed for strict positivity. Source: `paper/main.tex` 1202–1238 and 1259–1265. -/
theorem exists_sharp_environmentLaw_with_input (d : ℕ) (hd : 2 ≤ d)
    (hW : External.WhiteNoiseExistence d) :
    ∃ (Λ₀ r₀ δ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
      IsSharpLaw hd δ Q ∧ (∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω) ∧
        SharpEnvironmentInput hd Q := by
  obtain ⟨P, hP⟩ := hW
  obtain ⟨ε, δ, Λ, hgrad, hμ, hε, hδ, hΛ, hsmooth, hreg, -, -, -⟩ :=
    exists_sharp_physical_seed_step1 d ⟨0, by omega⟩ P hP
  letI : IsProbabilityMeasure P := hP.1
  have hF := measurable_sharpPhysicalPair ⟨0, by omega⟩ δ ε hgrad hμ
  let Q : EnvironmentLaw d Λ 4 :=
    { measure := P.map (sharpPhysicalPair ⟨0, by omega⟩ δ ε hgrad hμ)
      probability := inferInstance
      ellipticity_parameter := by linarith
      range_parameter := by norm_num
      regular := (ae_map_iff hF.aemeasurable (measurableSet_isRegular_fieldPair Λ)).mpr
        (ae_of_all P hreg)
      stationary := sharpPhysicalPair_isStationary ⟨0, by omega⟩ δ ε hgrad hμ hP
      finiteRange := sharpPhysicalPair_hasFiniteRange ⟨0, by omega⟩ δ ε hgrad hμ hP }
  refine ⟨Λ, 4, δ, Q, ⟨hδ, ε, P, hgrad, hμ, hε, rfl⟩, ?_, ?_⟩
  · exact (ae_map_iff hF.aemeasurable measurableSet_isSmoothFieldPair_fieldPair).mpr
      (ae_of_all P hsmooth)
  · exact sharpEnvironmentInput_of_whiteNoise hd δ ε hgrad hμ hP hδ hε Q rfl

end EinsteinRelation.Sharpness
