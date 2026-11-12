import EinsteinRelation.Correctors.CanonicalFlowIdentification
import EinsteinRelation.Correctors.StationarySpatialDivergenceFull
import EinsteinRelation.Correctors.HorizontalH1DivergencePairing

/-! # Identifying flow-gradient limits from spatial PDEs

Source: `paper/main.tex:808–816`. The finite-time spatial divergence
identity supplies the horizontal variational equation used in canonical
identification. The flow, its integrated H¹ potentials, and their decay
and convergence must still be constructed and estimated.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors

/-- A stationary L² spatial divergence equation pairs against every actual
horizontal H¹ test, with the Euclidean L² gradient.
Source: `paper/main.tex:808–816`. -/
theorem horizontalH1_gradient_pairing_of_spatial_divergence {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (W : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) (h : Lp ℝ 2 Q)
    (hspatial : ∀ᵐ ω ∂Q, HasWeakDivergence Set.univ
      (fun x i => W (translate x ω) i) (orbit h ω))
    (f : horizontalH1 Q hQ) :
    inner ℝ (horizontalEuclideanGradient Q hQ f) W =
      -inner ℝ (f : Lp ℝ 2 Q) h := by
  have hWm : Measurable (fun ω i => W ω i) := measurable_pi_lambda _ fun i =>
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).continuous.measurable.comp
      (Lp.stronglyMeasurable W).measurable
  have hW2 : ∀ i, MemLp (fun ω => W ω i) 2 Q := fun i =>
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).comp_memLp'
      (Lp.memLp W)
  exact horizontalH1_gradient_pairing_of_divergence Q hQ f W h
    (weakHorizontalDivergence_of_spatial Q hQ hWm (Lp.stronglyMeasurable h).measurable
      hW2 (Lp.memLp h) hspatial)

/-- The genuine finite-time spatial PDE and residual decay identify a strong
limit of integrated gradients with the canonical corrector. The horizontal
variational equation is derived, rather than supplied as a premise.
Source: `paper/main.tex:808–816`. -/
theorem flowGradient_limit_eq_canonical_of_spatial {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (v : ℕ → horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q))
    (u : ℕ → Lp ℝ 2 (reducedEnvironmentLaw Q))
    {G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)}
    (hG : Tendsto (fun n => horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) (v n)) atTop (𝓝 G))
    (hu : Tendsto u atTop (𝓝 0))
    (hspatial : ∀ n, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakDivergence Set.univ
        (fun x j => correctorFluxOfGradient Q i (horizontalEuclideanGradient
          (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) (v n))
          (translate x ω) j) (orbit (u n) ω)) :
    G = (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) := by
  apply flowGradient_limit_eq_canonical Q i v u hG hu
  intro n f
  exact horizontalH1_gradient_pairing_of_spatial_divergence
    (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) _ _ (hspatial n) f

/-- The spatial PDE identifies the limit supplied by a Cauchy estimate on
integrated gradients. Source: `paper/main.tex:808–816`. -/
theorem tendsto_flowGradient_canonical_of_spatial_cauchy {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (v : ℕ → horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q))
    (u : ℕ → Lp ℝ 2 (reducedEnvironmentLaw Q))
    (hC : CauchySeq (fun n => horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) (v n)))
    (hu : Tendsto u atTop (𝓝 0))
    (hspatial : ∀ n, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakDivergence Set.univ
        (fun x j => correctorFluxOfGradient Q i (horizontalEuclideanGradient
          (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) (v n))
          (translate x ω) j) (orbit (u n) ω)) :
    Tendsto (fun n => horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) (v n)) atTop
      (𝓝 (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) := by
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hC
  rw [flowGradient_limit_eq_canonical_of_spatial Q i v u hG hu hspatial] at hG
  exact hG

end EinsteinRelation.Correctors
