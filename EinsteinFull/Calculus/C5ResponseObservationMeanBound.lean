import EinsteinFull.Calculus.C5ResponseRealForceBound
import EinsteinFull.Calculus.C9ResponseObservationMean

open MeasureTheory
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The mean of an essentially bounded observation stays bounded along the actual
real-force semigroup and is continuous under the real-time extension.
The prescribed source contract retains `hreal` and `hY`; the analytic estimate
uses the stronger semigroup bound directly, independently of these inputs. -/
@[nolint unusedArguments]
theorem response_observation_mean_bounded_continuous
    (hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (f : Lp ℂ 2 (reducedLaw Q)) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ K) :
    Continuous (fun t : ℝ => ∫ ω, (P t.toNNReal f) ω ∂reducedLaw Q) ∧
      ∀ t : ℝ, 0 ≤ t → ‖∫ ω, (P t.toNNReal f) ω ∂reducedLaw Q‖ ≤ K := by
  clear hreal hY
  let := reducedLaw_probability Q
  refine ⟨response_observation_mean_continuous hP f, ?_⟩
  intro t _ht
  have hbound := response_real_force_semigroup_bound d hd D Q hQ lam P hP
    f K hK hf t.toNNReal
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const hbound

end EinsteinFull.Blueprint
