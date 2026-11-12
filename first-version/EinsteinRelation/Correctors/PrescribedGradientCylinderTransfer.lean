import EinsteinRelation.Correctors.SemigroupPrescribedGradient
import EinsteinRelation.Correctors.EuclideanRmsNorm

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A prescribed whole-space gradient has the endpoint energy bound of
any localized recovery of the same scalar solution.
Source: `paper/main.tex:798–806`. -/
theorem prescribed_gradient_energy_le {d : ℕ} {K c b : ℝ}
    (hK : 0 < K) (hc : 0 < c) (hcb : c < b)
    {A : Coefficient d K} {U V : Set (Vec d)} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (hVc : IsCompact (closure V))
    [IsFiniteMeasure (volume.restrict U)] [IsFiniteMeasure (volume.restrict V)]
    {v : Vec d → Vec d} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsem : IsSemigroupSolution A v u G)
    (hsol : IsParabolicSolution A (Set.Ioo c b) U u G)
    {H : Vec d → Vec d} (hH : HasWeakGradient Set.univ (fun x => u (b,x)) H)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ) (hχb : ∀ x, |χ x| ≤ 1)
    (hχV : ∀ x ∈ V, χ x = 1)
    {L : ℝ} (hL : 0 ≤ L) (hχD : ∀ x, euclideanNorm (gradient χ x) ≤ L) :
    MemLp (fun x => euclideanNorm (H x)) 2 (volume.restrict V) ∧
      (eLpNorm (fun x => euclideanNorm (H x)) 2 (volume.restrict V)).toReal ≤
        Real.sqrt d * Real.sqrt ((2*K/(b-c) + 2*K^2*L^2) *
          (∫ z in Set.Ioo c b ×ˢ U, euclideanSq (G z))) := by
  obtain ⟨J,hw,hJL,hJb⟩ := parabolicSolution_prescribed_gradient_energy hK hc hcb
    hU hVU hV.measurableSet hsem.1 hsol
    (semigroupSolution_scalar_memLp_on_precompact hsem hVc (hc.trans hcb))
    hχ hχb hχV hL hχD
  have heq : J =ᵐ[volume.restrict V] H := by
    filter_upwards [ae_all_iff.mpr fun j => weakPartialDerivative_ae_eq_on_open hV
      (hw j) (hasWeakGradient_mono (Set.subset_univ V) hH j)] with x hx
    exact funext hx
  have heqn := heq.mono fun x hx => congrArg euclideanNorm hx
  exact ⟨(memLp_congr_ae heqn).mp hJL, (eLpNorm_congr_ae heqn).symm ▸ hJb⟩

end EinsteinRelation.Correctors
