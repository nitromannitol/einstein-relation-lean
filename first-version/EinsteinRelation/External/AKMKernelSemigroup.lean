import EinsteinRelation.External.AKMHeatKernel

/-! # Decay of the AKM source semigroup

Source: AKM (2019), (9.1)–(9.2), printed p. 347, Theorem 9.1 and the
following paragraph, p. 349. Formula (9.2) uses the Green function of
Proposition E.1, pp. 500–501. Application: `paper/main.tex:787–792,850`.

The chapter defines its chosen flow by the kernel formula. The proposition
below concludes only decay for a specified flow with that representation.
Kernel existence is the separate Proposition E.1; measurable construction
of the represented flow remains an internal obligation.
Absolute convergence is part of the Lebesgue integral in (9.2); its
Gaussian-gradient justification is given in (9.9), printed p. 350.
-/

open MeasureTheory

namespace EinsteinRelation.External.AKM
open Environment.AKMTestIntegralSupport

/-- The kernel formula (9.2) for the same Green function as Proposition E.1.
All kernels and weak derivatives are chosen together. This is a predicate
on a specified flow, not an assertion that every PDE solution has this form. -/
def HasCanonicalKernelRepresentation {d : ℕ} {K : ℝ} (A : Coefficient d K)
    (g : Vec d → Vec d) (u : ℝ × Vec d → ℝ) : Prop :=
  ∃ (C : ℝ → ℝ) (P : ℝ → Vec d → Vec d → ℝ)
    (X Y : ℝ → Vec d → Vec d → Vec d) (H : ℝ → Vec d → Vec d → Mat d),
    (∀ α, 0 < α → α < K⁻¹ → 0 < C α) ∧
    HeatKernelProperties A P X Y H C ∧
    ∀ t : ℝ, 0 < t → ∀ x : Vec d,
      Integrable (fun y => dot (g y) (Y t x y)) volume ∧
      u (t,x) = -(∫ y, dot (g y) (Y t x y) ∂volume)

/-- Transcription of Theorem 9.1 for the specified flow (9.2).
Only decay is concluded. The fundamental solution and its representation
are supplied as data describing that flow, rather than returned alongside
the estimate. No uniqueness of arbitrary distributional solutions is assumed.

Proposition E.1 does not explicitly assert uniqueness. Kernels satisfying
`HeatKernelProperties` are unique; this is proved in this development
(`Correctors.akm_heatKernel_unique`) by the duality argument on printed p. 510.
Source: AKM (9.2), p. 347, Theorem 9.1, p. 349. -/
def ParabolicSemigroupKernelDecay : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (K s : ℝ), 1 < K → 0 < s → s < 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
      ∀ g : Coefficient d K → Vec d → Vec d, IsStationaryField P g →
        (∀ᵐ A ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)), euclideanNorm (g A x) ≤ 1) →
        (∀ x : Vec d, Measurable[Environment.AKMTestIntegralSupport.localSigma
            {y | euclideanNorm (y - x) < 1}]
          (fun A => g A x)) →
        ∀ (u : Coefficient d K → ℝ × Vec d → ℝ)
          (G : Coefficient d K → ℝ × Vec d → Vec d),
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) →
          (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A) ∧
            HasCanonicalKernelRepresentation A (g A) (u A)) →
          ∀ (t : ℝ), 1 ≤ t → ∀ x : Vec d,
            StretchedExponentialBound P s (C * t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4))
              (fun A => |u A (t, x)|)

end EinsteinRelation.External.AKM
