import EinsteinFull.Calculus.ComplexForceApproximationSupport
import EinsteinFull.Calculus.ComplexTransposeResolventSupport

/-!
# Normalized resolvent approximation of the full transpose domain

The actual bilinear transposes of the normalized forward resolvents are
contractions. Conjugation transports the Hilbert adjoint increment estimate,
so forward strong convergence supplies strong convergence on every L2 datum.
Their full weak graph specifications then give constructive domain density.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Conjugating the adjoint increment estimate gives the bilinear transpose estimate. -/
theorem norm_complexL2Transpose_sub_sq_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hA : ‖A‖ ≤ 1)
    (f : Lp ℂ 2 μ) :
    ‖complexL2Transpose μ A f - f‖ ^ 2 ≤
      2 * ‖f‖ * ‖A (complexL2Conjugation μ f) - complexL2Conjugation μ f‖ := by
  have he : complexL2Transpose μ A f - f = complexL2Conjugation μ
      (ContinuousLinearMap.adjoint A (complexL2Conjugation μ f) -
        complexL2Conjugation μ f) := by
    simp only [map_sub, complexL2Conjugation_involutive]
    rfl
  rw [he, norm_complexL2Conjugation]
  simpa only [norm_complexL2Conjugation] using
    norm_complexL2Adjoint_sub_sq_le μ A hA (complexL2Conjugation μ f)

/-- Actual normalized transpose resolvents at the adopted forward spectral parameters. -/
def complexTransposeResolventApproximation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  complexL2Transpose (reducedLaw Q) (forcedComplexResolventApproximation Q i ζ n)

/-- The normalization is exactly the distance of the spectral parameter above the force shift. -/
theorem complexTransposeResolventApproximation_eq {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) :
    complexTransposeResolventApproximation Q i ζ n =
      (((n : ℝ) + 1 : ℝ) : ℂ) • complexL2Transpose (reducedLaw Q)
        (forcedComplexResolvent Q i ζ (complexForceShift d Λ₀ ζ + ((n : ℝ) + 1))
          (by exact lt_add_of_pos_right _ (by positivity))) :=
  complexL2Transpose_smul _ _ _

/-- Each normalized transpose resolvent has operator norm at most one. -/
theorem norm_complexTransposeResolventApproximation_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) :
    ‖complexTransposeResolventApproximation Q i ζ n‖ ≤ 1 := by
  rw [complexTransposeResolventApproximation, norm_complexL2Transpose]
  exact (forcedComplexResolventApproximation Q i ζ n).opNorm_le_bound zero_le_one
    (fun f => by simpa only [one_mul] using
      norm_forcedComplexResolventApproximation_le Q i ζ n f)

/-- Every normalized transpose resolvent contracts the actual L2 norm. -/
theorem norm_complexTransposeResolventApproximation_apply_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖complexTransposeResolventApproximation Q i ζ n f‖ ≤ ‖f‖ := by
  exact ((complexTransposeResolventApproximation Q i ζ n).le_opNorm f).trans
    (by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right
        (norm_complexTransposeResolventApproximation_le Q i ζ n) (norm_nonneg f)))

/-- Each approximant lies in the full H1 transpose graph, with its literal output. -/
theorem complexTransposeResolventApproximation_graph {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexTransposeGeneratorPair Q i ζ (complexTransposeResolventApproximation Q i ζ n f)
      (((complexForceShift d Λ₀ ζ + ((n : ℝ) + 1) : ℝ) : ℂ) •
        complexTransposeResolventApproximation Q i ζ n f - (((n : ℝ) + 1 : ℝ) : ℂ) • f) := by
  have h := complexL2Transpose_forcedComplexResolvent_spec Q i ζ
    (complexForceShift d Λ₀ ζ + ((n : ℝ) + 1))
    (by exact lt_add_of_pos_right _ (by positivity)) ((((n : ℝ) + 1 : ℝ) : ℂ) • f)
  simpa only [map_smul, complexTransposeResolventApproximation_eq,
    ContinuousLinearMap.smul_apply] using h

/-- The normalized actual transpose resolvents converge strongly on every complex L2 datum. -/
theorem tendsto_complexTransposeResolventApproximation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun n => complexTransposeResolventApproximation Q i ζ n f) atTop (𝓝 f) := by
  have hb (n : ℕ) : ‖forcedComplexResolventApproximation Q i ζ n‖ ≤ 1 := by
    rw [← norm_complexL2Transpose (reducedLaw Q)]
    exact norm_complexTransposeResolventApproximation_le Q i ζ n
  have hz : Tendsto (fun n => 2 * ‖f‖ *
      ‖forcedComplexResolventApproximation Q i ζ n (complexL2Conjugation (reducedLaw Q) f) -
        complexL2Conjugation (reducedLaw Q) f‖) atTop (𝓝 0) := by
    have h := ((tendsto_forcedComplexResolventApproximation Q i ζ
      (complexL2Conjugation (reducedLaw Q) f)).sub_const
        (complexL2Conjugation (reducedLaw Q) f)).norm.const_mul (2 * ‖f‖)
    simpa only [sub_self, norm_zero, mul_zero] using h
  have hs := squeeze_zero (fun n => sq_nonneg
    ‖complexTransposeResolventApproximation Q i ζ n f - f‖)
    (fun n => norm_complexL2Transpose_sub_sq_le (reducedLaw Q)
      (forcedComplexResolventApproximation Q i ζ n) (hb n) f) hz
  have hn := hs.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- The literal full transpose generator domain is dense in actual complex L2. -/
theorem dense_complexTransposeGenerator_domain {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) :
    Dense {f : Lp ℂ 2 (reducedLaw Q) | ∃ g, IsComplexTransposeGeneratorPair Q i ζ f g} := by
  intro f
  exact mem_closure_of_tendsto (tendsto_complexTransposeResolventApproximation Q i ζ f)
    (Eventually.of_forall fun n => ⟨_, complexTransposeResolventApproximation_graph Q i ζ n f⟩)

end EinsteinFull
