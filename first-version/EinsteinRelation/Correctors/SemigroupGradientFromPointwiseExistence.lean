import EinsteinRelation.Correctors.SemigroupPrescribedGradientRecovery
import EinsteinRelation.Correctors.SemigroupPrescribedVersion

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Recover joint gradients directly from the measurable scalar formula. Source: `paper/main.tex:787–806`. -/
theorem exists_measurable_semigroupGradient_of_pointwise_existence
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {K : ℝ} (hK : 0 < K)
    (μ : Measure Ω) (A : Ω → Coefficient d K) (g : Ω → Vec d → Vec d)
    (u : Ω → ℝ × Vec d → ℝ)
    (hum : Measurable (fun z : Ω × (ℝ × Vec d) => u z.1 z.2))
    (hsol : ∀ᵐ ω ∂μ, ∃ G : ℝ × Vec d → Vec d,
      IsSemigroupSolution (A ω) (g ω) (u ω) G) :
    ∃ H : Ω → ℝ × Vec d → Vec d,
      Measurable (fun z : Ω × (ℝ × Vec d) => H z.1 z.2) ∧
      ∀ᵐ ω ∂μ, IsSemigroupSolution (A ω) (g ω) (u ω) (H ω) ∧
        ∀ t : ℝ, 0 < t → HasWeakGradient Set.univ
          (fun x => u ω (t,x)) (fun x => H ω (t,x)) := by
  obtain ⟨H, hHm, hrec⟩ := exists_measurable_prescribed_gradient_recovery u hum
  refine ⟨H, hHm, ?_⟩
  filter_upwards [hsol] with ω hω
  obtain ⟨G, hG⟩ := hω
  have hH : ∀ t : ℝ, 0 < t → HasWeakGradient Set.univ
      (fun x => u ω (t,x)) (fun x => H ω (t,x)) := by
    intro t ht
    obtain ⟨J, hJ⟩ := semigroupSolution_exists_positive_time_gradient hK hG ht
    apply hasWeakGradient_congr_ae isOpen_univ hJ Filter.EventuallyEq.rfl
    simpa only [Measure.restrict_univ] using (hrec ω t J hJ).symm
  exact ⟨semigroupSolution_prescribed_gradient_version hG
    (hHm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable hH, hH⟩

end EinsteinRelation.Correctors
