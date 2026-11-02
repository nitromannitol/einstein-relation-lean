import EinsteinFull.Calculus.C4ResponseObservationBounds
import EinsteinFull.Calculus.C5ResponseObservationMeanBound
import EinsteinFull.Calculus.C9ComplexCesaroAbel

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- For the actual forced drift and clock observations, the explicit Cesaro
limits imply the corresponding Abel limits with the same velocity and clock
rate. This holds at every real force, hence at every signed nonzero force.
It does not produce the Cesaro limits or the pathwise witnesses. -/
theorem response_observation_abel_of_cesaro
    (hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (velocity : Vec d) (η : ℝ)
    (hvelocity : ∀ i : Fin d,
      Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
        ∫ t in (0 : ℝ)..T, ∫ ω,
          (P t.toNNReal (β i + (lam : ℂ) • a (⟨0, by omega⟩ : Fin d) i)) ω
            ∂reducedLaw Q) atTop (𝓝 (velocity i : ℂ)))
    (hclock : Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..T, ∫ ω, (P t.toNNReal μ) ω ∂reducedLaw Q)
        atTop (𝓝 (η : ℂ))) :
    (∀ i : Fin d,
      Tendsto (fun s : ℝ => (s : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-s * t) : ℂ) * (∫ ω,
          (P t.toNNReal (β i + (lam : ℂ) • a (⟨0, by omega⟩ : Fin d) i)) ω
            ∂reducedLaw Q)) (𝓝[>] (0 : ℝ)) (𝓝 (velocity i : ℂ))) ∧
    Tendsto (fun s : ℝ => (s : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
      (Real.exp (-s * t) : ℂ) * (∫ ω, (P t.toNNReal μ) ω ∂reducedLaw Q))
        (𝓝[>] (0 : ℝ)) (𝓝 (η : ℂ)) := by
  obtain ⟨C, hC, hobs⟩ := response_observations_uniform_bounds d hd D
  obtain ⟨hμbound, hβbound⟩ := hobs Q hQ β a μ hβ ha hμ
  constructor
  · intro i
    have hK : 0 ≤ C * (1 + |lam|) :=
      mul_nonneg hC.le (by positivity)
    obtain ⟨hcont, hbound⟩ := response_observation_mean_bounded_continuous
      hreal d hd D Q hQ lam P hP Y hY
      (β i + (lam : ℂ) • a (⟨0, by omega⟩ : Fin d) i)
      (C * (1 + |lam|)) hK (hβbound lam i)
    exact complex_abel_limit_of_cesaro _ hcont _ hK hbound _ (hvelocity i)
  · obtain ⟨hcont, hbound⟩ := response_observation_mean_bounded_continuous
      hreal d hd D Q hQ lam P hP Y hY μ C hC.le hμbound
    exact complex_abel_limit_of_cesaro _ hcont C hC.le hbound _ hclock

end EinsteinFull.Blueprint
