import EinsteinFull.Calculus.C3CanonicalCorrectorSupport
import EinsteinFull.Calculus.C4HalfDirectionCorrector
import EinsteinFull.Calculus.C2SublinearSourceSupport

/-!
Source witnesses for the sublinear-pair construction. The scalar corrector is
the normalized actual global producer, and the flux potential is selected for
that same scalar corrector. These are source-law estimates; smooth reduced-law
representatives and the column-divergence identity remain separate obligations.
-/

open MeasureTheory

noncomputable section
namespace EinsteinFull.Calculus.C3SublinearPair

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport ReductionImageV3
open C4HalfDirectionCorrector

/-- Normalize the actual global producer to a unit coordinate direction. -/
theorem exists_unitCorrector_global_identification
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp,
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        (correctorUnitVector i).ofLp +
          φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp := by
  obtain ⟨φ, hφ⟩ := exists_akmCorrector_global_gradient_identification_from_pde Q i
  refine ⟨doubledCorrector Q i φ, ?_⟩
  filter_upwards [hφ] with ω hω
  filter_upwards [hω] with y hy
  simpa only [smul_add, two_smul_halfDirection, doubledCorrector_grad] using hy

/-- The admitted estimate supplies one source pair for every coordinate of the
actual gradient, with uniform constants chosen before the environment law.
The stochastic exponent is exactly `d / 2`; no smoothness or divergence
property is inferred from the source oscillation bound. -/
theorem exists_sourcePairs
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) :
    ∃ β C Cs : ℝ, 0 < β ∧ 0 < C ∧ 0 < Cs ∧
      ∀ {r₀ : ℝ} (Q : EnvironmentLaw d L r₀),
        ∃ φ : (i : Fin d) →
            Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp,
          (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ i : Fin d,
            ∀ᵐ y ∂(volume : Measure (Vec d)),
              (correctorUnitVector i).ofLp +
                (φ i).grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
              (correctorUnitVector i + (canonicalCorrectorGradient Q i :
                Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                  (translate (r₀ • y) (reduce ω.1))).ofLp) ∧
          ∃ S : (i : Fin d) → FluxCorrector (φ i),
            ∃ X : Fin d → Coefficient d (AKMUpperEllipticity L) → ℝ,
              ∀ i : Fin d, Measurable (X i) ∧
                OsBound (actualCoefficientLaw Q) (X i) ((d : ℝ) / 2) Cs ∧
                ∀ᵐ a ∂actualCoefficientLaw Q, 1 ≤ X i a ∧
                  ∀ r : ℝ, X i a ≤ r →
                    Real.sqrt (⨍ x in ball 0 r,
                      |(φ i).potential a x - (⨍ y in ball 0 r, (φ i).potential a y)| ^ 2) +
                    Real.sqrt (⨍ x in ball 0 r,
                      frobeniusNorm ((S i).potential a x -
                        (Matrix.of fun j k => ⨍ y in ball 0 r,
                          (S i).potential a y j k)) ^ 2) ≤
                      C * r ^ (1 - β * ((d : ℝ) - (d : ℝ) / 2)) ∧
                    Real.sqrt (⨍ x in ball 0 r, euclideanSq ((φ i).grad a x)) ≤ C := by
  classical
  have hK : 1 < AKMUpperEllipticity L := by
    have he : 1 < Real.exp (2 * L) := Real.one_lt_exp_iff.mpr (by linarith)
    have hscale : 1 < ellipticityScale L := by
      unfold ellipticityScale
      nlinarith
    unfold AKMUpperEllipticity
    nlinarith
  obtain ⟨β, C, hβ, hC, h⟩ := C2SublinearSource.sublinearCorrectors d hd _ hK
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨Cs, hCs, h⟩ := h ((d : ℝ) / 2) (by linarith) (by linarith)
  refine ⟨β, C, Cs, hβ, hC, hCs, ?_⟩
  intro r₀ Q
  have : Fact (2 ≤ d) := ⟨hd⟩
  choose φ hφ using exists_unitCorrector_global_identification Q
  have hsource := fun i : Fin d => h (actualCoefficientLaw Q)
    (lawHypotheses_actualCoefficientLaw Q) (correctorUnitVector i).ofLp
      (euclideanNorm_correctorUnitVector i) (φ i)
  let S := fun i => Classical.choice (hsource i).1
  choose X hX using fun i => (hsource i).2 (S i)
  exact ⟨φ, ae_all_iff.mpr hφ, S, X, hX⟩

end EinsteinFull.Calculus.C3SublinearPair
