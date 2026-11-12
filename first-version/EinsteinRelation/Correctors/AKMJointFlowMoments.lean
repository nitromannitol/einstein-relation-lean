import EinsteinRelation.Correctors.AKMStretchedExponentialMoments

/-! # One actual AKM flow for all finite moments

Source: `paper/main.tex:789–816`. The source stretched-exponential estimate
provides one joint pair of scalar flow and PDE gradient. Every finite-moment
bound below uses that same pair; choosing the exponent does not choose a new
flow. Constants stay before the environment law and initial field.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The actual source flow simultaneously satisfies all positive finite
moment estimates. Source: `paper/main.tex:789–816`. -/
theorem parabolicSemigroupDecay_all_moments (hAKM : ParabolicSemigroupDecay)
    (d : ℕ) (hd : 2 ≤ d) (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) :
    ∃ C : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < C m) ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
        ∀ g : Coefficient d K → Vec d → Vec d,
          IsStationaryField P g →
          (∀ᵐ A ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)), euclideanNorm (g A x) ≤ 1) →
          (∀ x : Vec d, Measurable[Environment.AKMTestIntegralSupport.localSigma
            {y | euclideanNorm (y - x) < 1}] (fun A => g A x)) →
          ∃ (u : Coefficient d K → ℝ × Vec d → ℝ)
            (G : Coefficient d K → ℝ × Vec d → Vec d),
            Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) ∧
            (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) ∧
            ∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
              MemLp (fun A => u A (t, x)) (ENNReal.ofReal m) P ∧
                eLpNorm (fun A => u A (t, x)) (ENNReal.ofReal m) P ≤
                  ENNReal.ofReal (C m * t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4)) := by
  obtain ⟨C₀, hC₀, hdecay⟩ := hAKM d hd K s hK hs hs2
  let C : ℝ → ℝ := fun m => (2 * (m / s) ^ (m / s)) ^ (1 / m) * C₀
  refine ⟨C, ?_, ?_⟩
  · intro m hm
    dsimp only [C]
    positivity
  · intro P hP g hg hgb hgl
    obtain ⟨u, G, hu, hsol, hstoch⟩ := hdecay P hP g hg hgb hgl
    refine ⟨u, G, hu, hsol, ?_⟩
    intro m hm t ht x
    have hθ : 0 < C₀ * t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4) :=
      mul_pos hC₀ (Real.rpow_pos_of_pos (by linarith) _)
    have hbound := eLpNorm_le_of_stretchedExponential P hs hθ hm
      (Filter.Eventually.of_forall fun A => abs_nonneg (u A (t, x))) (hstoch t ht x)
    have hnorm : eLpNorm (fun A => u A (t, x)) (ENNReal.ofReal m) P ≤
        ENNReal.ofReal (C m * t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4)) := by
      simpa only [C, ← Real.norm_eq_abs, eLpNorm_norm, mul_assoc] using hbound
    exact ⟨⟨(hu.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable,
      hnorm.trans_lt ENNReal.ofReal_lt_top⟩, hnorm⟩

end EinsteinRelation.Correctors
