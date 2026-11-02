import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.Tactic.Linarith

/-! # The AKM hypotheses for the rescaled reduced coefficient law

Source: `paper/main.tex:779–800,850–858`. The map to AKM's coefficient space
uses `x ↦ r₀ x` and multiplication by `exp(2Λ₀)Λ₀`. The probability,
lattice stationarity and unit dependence range of this map's law were proved
in `Environment.AKMTestIntegralSupport`; here they discharge the hypotheses
of the literature contracts. No source corrector is identified with the
canonical variational corrector in these results.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

open Environment.AKMTestIntegralSupport
open External.AKM

/-- The rescaled reduced law satisfies AKM (0.6)--(0.11).
Source: `paper/main.tex:779–800`. -/
theorem isAdmissibleLaw_actualCoefficientLaw {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) : IsAdmissibleLaw (actualCoefficientLaw Q) :=
  ⟨actualCoefficientLaw_probability Q, actualCoefficientLaw_translation_invariant Q,
    actualCoefficientLaw_finiteRange Q⟩

/-- The upper ellipticity constant of the normalized reduced coefficient
is at least one. Source: `paper/main.tex:779–800`. -/
theorem one_le_AKMUpperEllipticity {L : ℝ} (hL : 1 ≤ L) :
    1 ≤ AKMUpperEllipticity L := by
  have hexp : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
  have hscale : 1 ≤ ellipticityScale L :=
    one_le_mul_of_one_le_of_one_le hexp hL
  exact one_le_mul_of_one_le_of_one_le hscale hscale

/-- The actual normalized law is in AKM's strict ellipticity-parameter
range. No endpoint extension is needed. Source: `paper/main.tex:779–800`. -/
theorem one_lt_AKMUpperEllipticity {L : ℝ} (hL : 1 ≤ L) :
    1 < AKMUpperEllipticity L := by
  have hexp : 1 < Real.exp (2 * L) := Real.one_lt_exp_iff.mpr (by linarith)
  have hscale : 1 < ellipticityScale L :=
    calc
      1 < Real.exp (2 * L) := hexp
      _ ≤ Real.exp (2 * L) * L := le_mul_of_one_le_right (Real.exp_pos _).le hL
  calc
    1 < ellipticityScale L := hscale
    _ ≤ ellipticityScale L * ellipticityScale L :=
      le_mul_of_one_le_right (zero_lt_one.trans hscale).le hscale.le

/-- First actual-law consumer of Theorem 3.3, p. 75: its one random radius
and the three estimates, with the law and ellipticity hypotheses discharged.
Source: `paper/main.tex:850–858`. The coefficient is still in AKM coordinates;
transport of the PDE and spatial averages back to physical coordinates is a
separate analytic step. -/
theorem ellipticLargeScale_actualCoefficientLaw (hAKM : EllipticLargeScale)
    (d : ℕ) (hd : 2 ≤ d) (L r₀ s : ℝ) (hL : 1 ≤ L) (hs : 0 < s) (hsd : s < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d L r₀,
      ∃ X : Coefficient d (AKMUpperEllipticity L) → ℝ, Measurable X ∧
        (∀ A, 1 ≤ X A) ∧ StretchedExponentialBound (actualCoefficientLaw Q) s C X ∧
        ∀ᵐ A ∂actualCoefficientLaw Q, ∀ R : ℝ, X A ≤ R →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d), IsHarmonic A R u G →
            ∀ r : ℝ, X A ≤ r → r ≤ R →
              scalarRms volume (originBall d r) (fun x => u x - ⨍ y in originBall d r, u y) / r ≤
                C * scalarRms volume (originBall d R)
                  (fun x => u x - ⨍ y in originBall d R, u y) / R ∧
              scalarRms volume (originBall d r) u ≤ C * scalarRms volume (originBall d R) u ∧
              vectorRms volume (originBall d r) G ≤ C * vectorRms volume (originBall d R) G := by
  obtain ⟨C, hC, h⟩ := hAKM d hd (AKMUpperEllipticity L) s
    (one_lt_AKMUpperEllipticity hL) hs hsd
  exact ⟨C, hC, fun Q => h (actualCoefficientLaw Q) (isAdmissibleLaw_actualCoefficientLaw Q)⟩

end EinsteinRelation.Correctors
