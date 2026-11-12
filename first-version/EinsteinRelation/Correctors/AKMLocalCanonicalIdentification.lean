import EinsteinRelation.Correctors.AKMLocalCanonicalIdentificationPotential
import EinsteinRelation.Correctors.AKMLocalCanonicalIdentificationFlux
import EinsteinRelation.Correctors.CanonicalFlowSpatialIdentification
import EinsteinRelation.Calculus.WeakRepresentativeOperations

/-! # Canonical identification from finite-time spatial potentials

Source: `paper/main.tex:808-816`. Finite-time spatial potentials yield
actual horizontal H¹ vectors. Their literal coefficient-flux equations
and residual decay identify a strong gradient limit with the repository's
canonical variational gradient. The potentials and their spatial equations
remain concrete hypotheses to instantiate for the AKM flow.
-/
open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors

/-- Spatial finite-time potentials and flux equations suffice for canonical
identification; horizontal H¹ membership is derived from the spatial gradients. -/
theorem akmLocal_gradient_limit_eq_canonical_of_spatial_potentials
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (v : ℕ → Lp ℝ 2 (reducedEnvironmentLaw Q))
    (Y : ℕ → Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (u : ℕ → Lp ℝ 2 (reducedEnvironmentLaw Q))
    (hpotential : ∀ n, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient Set.univ (orbit (v n) ω)
        (fun x => (Y n (translate x ω)).ofLp))
    (hflux : ∀ n, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakDivergence Set.univ
        (fun x => (ω.1 x).mulVec (unitVector i + (Y n (translate x ω)).ofLp))
        (orbit (u n) ω))
    (hu : Tendsto u atTop (𝓝 0))
    {G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)}
    (hY : Tendsto Y atTop (𝓝 G)) :
    G = (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) := by
  choose w _ hw using fun n => exists_horizontalH1_of_stationary_spatial_potential
    (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) (v n) (Y n) (hpotential n)
  apply flowGradient_limit_eq_canonical_of_spatial Q i w u
    (by simpa only [hw] using hY) hu
  intro n
  filter_upwards [hflux n, ae_spatial_correctorFluxOfGradient Q i (Y n)] with ω hω hrep
  rw [hw n]
  apply hω.congr_ae
  · rw [Measure.restrict_univ]
    filter_upwards [hrep] with x hx
    exact hx.symm
  · exact ae_eq_refl _

/-- A Cauchy bound for the actual finite-time gradients supplies their canonical limit. -/
theorem akmLocal_tendsto_gradient_canonical_of_spatial_potentials
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (v : ℕ → Lp ℝ 2 (reducedEnvironmentLaw Q))
    (Y : ℕ → Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (u : ℕ → Lp ℝ 2 (reducedEnvironmentLaw Q))
    (hpotential : ∀ n, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient Set.univ (orbit (v n) ω)
        (fun x => (Y n (translate x ω)).ofLp))
    (hflux : ∀ n, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakDivergence Set.univ
        (fun x => (ω.1 x).mulVec (unitVector i + (Y n (translate x ω)).ofLp))
        (orbit (u n) ω))
    (hu : Tendsto u atTop (𝓝 0)) (hY : CauchySeq Y) :
    Tendsto Y atTop (𝓝 (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) := by
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hY
  rwa [akmLocal_gradient_limit_eq_canonical_of_spatial_potentials
    Q i v Y u hpotential hflux hu hG] at hG

end EinsteinRelation.Correctors
