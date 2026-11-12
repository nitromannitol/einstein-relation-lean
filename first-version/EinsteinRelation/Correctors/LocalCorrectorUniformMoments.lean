import EinsteinRelation.Correctors.LocalCorrectorCoordinateBounds

/-! # Uniform scalar moments extracted from local corrector estimates

Source: `paper/main.tex:1070–1082`. Lemma 5.1 and the genuine geometric
estimates in Proposition 5.3 give a single scalar-coordinate constant,
chosen before the environment law, localization scale and direction.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- Normalize Proposition 5.3's geometric estimates and combine them with
Lemma 5.1, uniformly over all local correctors (`paper/main.tex:1070–1082`). -/
theorem localCorrector_uniform_coordinate_bounds (H51 : CorrectorGradientMoments)
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) {m : ℝ} (hm : 2 ≤ m)
    (φ : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → ℝ)
    (S : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → Mat d)
    (F W : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → Vec d)
    (hW : ∀ Q r, 1 ≤ r → ∀ j, Measurable (W Q r j))
    (hbound : ∃ C : ℝ, ∀ (Q : EnvironmentLaw d Λ₀ r₀) (r : ℝ), 1 ≤ r → ∀ j : Fin d,
      (eLpNorm (φ Q r j) (ENNReal.ofReal m) (reducedEnvironmentLaw Q) +
        eLpNorm (fun ω => frobeniusNorm (S Q r j ω)) (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * correctorAmplitude d r)) ∧
      (eLpNorm (fun ω => euclideanNorm (F Q r j ω)) (ENNReal.ofReal m) (reducedEnvironmentLaw Q) +
        eLpNorm (fun ω => euclideanNorm (W Q r j ω -
          (StationarySpatialRealization.spatialRealization (canonicalCorrectorGradient Q j :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ((0 : Vec d), ω)).ofLp))
          (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (C * r⁻¹))) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (Q : EnvironmentLaw d Λ₀ r₀) (r : ℝ), 1 ≤ r → ∀ j : Fin d,
      eLpNorm (φ Q r j) (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (A * correctorAmplitude d r) ∧
      (∀ i k, eLpNorm (fun ω => S Q r j ω i k) (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (A * correctorAmplitude d r)) ∧
      (∀ i, eLpNorm (fun ω => F Q r j ω i) (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (A / r)) ∧
      (∀ i, eLpNorm (fun ω => W Q r j ω i) (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal A) := by
  obtain ⟨C, hC⟩ := hbound
  obtain ⟨G, hG, hGb⟩ := exists_canonicalGradient_moment_bound H51 hd Λ₀ r₀ hm
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hCB : C ≤ B := le_max_left _ _
  refine ⟨G + B, add_nonneg hG hB, fun Q r hr j => ?_⟩
  have ha : 0 ≤ correctorAmplitude d r := by
    unfold correctorAmplitude
    split <;> positivity
  have hV : Measurable (fun ω =>
      (StationarySpatialRealization.spatialRealization (canonicalCorrectorGradient Q j :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ((0 : Vec d), ω)).ofLp) :=
    (PiLp.continuous_ofLp 2 _).measurable.comp
      ((StationarySpatialRealization.measurable_spatialRealization _).comp
        (measurable_const.prodMk measurable_id))
  have hc := hC Q r hr j
  have hcφ := hc.1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCB ha))
  have hcF := hc.2.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCB (inv_nonneg.mpr (by linarith : 0 ≤ r))))
  have ht := localCorrector_coordinate_moments
    (ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ m)) hB hG hr hV (hW Q r hr j)
    hcφ hcF (hGb Q j)
  refine ⟨ht.1.trans ?_, fun i k => (ht.2.1 i k).trans ?_,
    fun i => (ht.2.2.1 i).trans ?_, ht.2.2.2⟩
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) ha)
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) ha)
  · apply ENNReal.ofReal_le_ofReal
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right (show B ≤ G + B by linarith)
        (inv_nonneg.mpr (by linarith : 0 ≤ r))

end EinsteinRelation.Correctors
