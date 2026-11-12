import EinsteinRelation.Correctors.AKMJointMeasurableFlow
import EinsteinRelation.Correctors.AKMInitialFluxObservation
import EinsteinRelation.Correctors.AKMFlowScaling
import EinsteinRelation.Correctors.AKMLocalCorrectorSpecialization

/-! # Apply the source semigroup estimate to actual coefficient columns

Source: `paper/main.tex:789–816`. Local coefficient-test observations give
an admissible source initial field. Its spatial almost-everywhere agreement
with the actual normalized column identifies the initial distribution of
the same measurable scalar flow and its actual weak PDE gradient.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- One source flow for the actual normalized coefficient column, retaining
all moment estimates. No raw point-evaluation measurability premise is used.
Source: `paper/main.tex:789–816`. -/
theorem parabolicSemigroupDecay_coefficient_column (hAKM : ParabolicSemigroupDecay)
    (d : ℕ) (hd : 2 ≤ d) (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) :
    ∃ C : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < C m) ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P → ∀ i : Fin d,
        ∃ (u : Coefficient d K → ℝ × Vec d → ℝ)
          (G : Coefficient d K → ℝ × Vec d → Vec d),
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) ∧
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => G z.1 z.2) ∧
          (∀ᵐ A ∂P, IsSemigroupSolution A
            (fun x => (((d : ℝ) + 1) * K)⁻¹ • (A x).mulVec (unitVector i)) (u A) (G A)) ∧
          ∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
            MemLp (fun A => u A (t, x)) (ENNReal.ofReal m) P ∧
              eLpNorm (fun A => u A (t, x)) (ENNReal.ofReal m) P ≤
                ENNReal.ofReal (C m * t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4)) := by
  obtain ⟨C, hC, hflow⟩ := parabolicSemigroupDecay_jointMeasurable_flow
    hAKM d hd K s hK hs hs2
  refine ⟨C, hC, ?_⟩
  intro P hP i
  obtain ⟨u, G, hum, hGm, hsol, hval⟩ := hflow P hP (initialFluxObservation i)
    (initialFluxObservation_stationary P i)
    (Filter.Eventually.of_forall fun A => initialFluxObservation_norm_le_ae
      (zero_lt_one.trans hK) i A)
    (measurable_initialFluxObservation_local i)
  refine ⟨u, G, hum, hGm, ?_, hval⟩
  filter_upwards [hsol] with A hA
  exact semigroupSolution_initialFlux_congr_ae hA (initialFluxObservation_eq_column_ae i A)

/-- Source: `paper/main.tex:789–816`. Removing the harmless initial
normalization retains one measurable flow, the actual coefficient-column
initial datum and all positive finite-moment estimates. -/
theorem parabolicSemigroupDecay_actual_column (hAKM : ParabolicSemigroupDecay)
    (d : ℕ) (hd : 2 ≤ d) (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) :
    ∃ C : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < C m) ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P → ∀ i : Fin d,
        ∃ (u : Coefficient d K → ℝ × Vec d → ℝ)
          (G : Coefficient d K → ℝ × Vec d → Vec d),
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) ∧
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => G z.1 z.2) ∧
          (∀ᵐ A ∂P, IsSemigroupSolution A
            (fun x => (A x).mulVec (unitVector i)) (u A) (G A)) ∧
          ∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
            MemLp (fun A => u A (t, x)) (ENNReal.ofReal m) P ∧
              eLpNorm (fun A => u A (t, x)) (ENNReal.ofReal m) P ≤
                ENNReal.ofReal (C m * t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4)) := by
  let c : ℝ := ((d : ℝ) + 1) * K
  have hc : 0 < c := mul_pos (by positivity) (zero_lt_one.trans hK)
  obtain ⟨C, hC, hflow⟩ := parabolicSemigroupDecay_coefficient_column
    hAKM d hd K s hK hs hs2
  refine ⟨fun m => c * C m, fun m hm => mul_pos hc (hC m hm), ?_⟩
  intro P hP i
  obtain ⟨u, G, hum, hGm, hsol, hval⟩ := hflow P hP i
  refine ⟨fun A z => c * u A z, fun A z => c • G A z,
    measurable_const.mul hum, measurable_const.smul hGm, ?_, ?_⟩
  · filter_upwards [hsol] with A hA
    have hscaled : IsSemigroupSolution A
        (fun x => c • (c⁻¹ • (A x).mulVec (unitVector i)))
        (fun z => c * u A z) (fun z => c • G A z) :=
      semigroupSolution_const_mul hA hc.le
    simpa only [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] using hscaled
  · intro m hm t ht x
    obtain ⟨hmem, hbound⟩ := hval m hm t ht x
    refine ⟨hmem.const_mul c, ?_⟩
    change eLpNorm (c • (fun A => u A (t, x))) _ P ≤ _
    rw [eLpNorm_const_smul]
    calc
      _ ≤ ‖c‖ₑ * ENNReal.ofReal (C m * t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4)) :=
        mul_le_mul_right hbound _
      _ = ENNReal.ofReal ((c * C m) * t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4)) := by
        rw [Real.enorm_eq_ofReal hc.le, ← ENNReal.ofReal_mul hc.le]
        congr 1
        dsimp [c]
        ring


/-- Source: `paper/main.tex:789–816`. The source flow estimate is
exercised on the actual normalized environment law, with the constant
chosen before the range and environment law. The spatial and time variables
here remain in AKM's normalized coordinates. -/
theorem parabolicSemigroupDecay_actualCoefficientLaw_column
    (hAKM : ParabolicSemigroupDecay) (d : ℕ) (hd : 2 ≤ d)
    (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < C m) ∧
      ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀) (i : Fin d),
        ∃ (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
          (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
          Measurable (fun z : Coefficient d (AKMUpperEllipticity L) × (ℝ × Vec d) =>
            u z.1 z.2) ∧
          Measurable (fun z : Coefficient d (AKMUpperEllipticity L) × (ℝ × Vec d) =>
            G z.1 z.2) ∧
          (∀ᵐ A ∂actualCoefficientLaw Q, IsSemigroupSolution A
            (fun x => (A x).mulVec (unitVector i)) (u A) (G A)) ∧
          ∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
            MemLp (fun A => u A (t, x)) (ENNReal.ofReal m) (actualCoefficientLaw Q) ∧
              eLpNorm (fun A => u A (t, x)) (ENNReal.ofReal m) (actualCoefficientLaw Q) ≤
                ENNReal.ofReal (C m * t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4)) := by
  obtain ⟨C, hC, hflow⟩ := parabolicSemigroupDecay_actual_column hAKM d hd
    (AKMUpperEllipticity L) 1 (one_lt_AKMUpperEllipticity hL)
    (by norm_num) (by norm_num)
  exact ⟨C, hC, fun _ Q => hflow (actualCoefficientLaw Q)
    (isAdmissibleLaw_actualCoefficientLaw Q)⟩

end EinsteinRelation.Correctors
