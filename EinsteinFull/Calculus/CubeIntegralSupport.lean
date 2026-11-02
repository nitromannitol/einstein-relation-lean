import EinsteinFull.Frozen.CubeIntegralObservation
import EinsteinFull.Calculus.ComplexTranslationSupport
import EinsteinFull.Frozen.ReducedLawProbability
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

theorem integrableOn_cubeIntegralObservation_integrand {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ρ : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    IntegrableOn (fun x : Vec d =>
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x U)
      (Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-ρ / 2) (ρ / 2))) := by
  letI := reducedLaw_probability Q
  have hc : Continuous (fun x : Vec d =>
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x U) :=
    (continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const)
  have hi : IntegrableOn (fun x : Vec d =>
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x U)
      (Set.Icc (fun _ => -ρ / 2) (fun _ => ρ / 2)) := hc.integrableOn_Icc
  apply hi.mono_set
  intro x hx
  constructor
  · intro j
    exact ((Set.mem_pi.mp hx) j (Set.mem_univ j)).1.le
  · intro j
    exact ((Set.mem_pi.mp hx) j (Set.mem_univ j)).2.le

end EinsteinFull
