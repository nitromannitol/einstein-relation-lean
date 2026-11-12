import EinsteinRelation.Correctors.AKMJointFlowMoments
import EinsteinRelation.Correctors.AKMJointGradientVersion

/-! # One jointly measurable source flow for every finite moment

Source: `paper/main.tex:789–816`. Recover the actual PDE gradient from the
source's scalar witness. The same scalar values keep every source decay
estimate, and changing only the gradient representative preserves all local
energy equations and the initial distribution.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- All positive finite moments and all positive-time local energy equations
hold for one jointly measurable scalar/gradient pair. This does not assert
spatial covariance or identify a separately constructed flow.
Source: `paper/main.tex:789–816`. -/
theorem parabolicSemigroupDecay_jointMeasurable_flow (hAKM : ParabolicSemigroupDecay)
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
            Measurable (fun z : Coefficient d K × (ℝ × Vec d) => G z.1 z.2) ∧
            (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) ∧
            ∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
              MemLp (fun A => u A (t, x)) (ENNReal.ofReal m) P ∧
                eLpNorm (fun A => u A (t, x)) (ENNReal.ofReal m) P ≤
                  ENNReal.ofReal (C m * t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4)) := by
  obtain ⟨C, hC, hdecay⟩ := parabolicSemigroupDecay_all_moments hAKM d hd K s hK hs hs2
  refine ⟨C, hC, ?_⟩
  intro P hP g hg hgb hgl
  obtain ⟨u, G, hum, hsol, hval⟩ := hdecay P hP g hg hgb hgl
  obtain ⟨H, hHm, hHsol, _⟩ :=
    exists_measurable_semigroupGradient_solution P g u G hum hsol
  exact ⟨u, H, hum, hHm, hHsol, hval⟩

end EinsteinRelation.Correctors
