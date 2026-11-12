import EinsteinRelation.Correctors.AKMHeatKernelPrescribedGaussian
import EinsteinRelation.Correctors.TranslatedGaussianIntegrability

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Every positive-time actual weak kernel gradient is integrable on the
whole spatial carrier. The assertion holds at each initial point.
Source: AKM E.1 (E.7); `paper/main.tex:787–806,850`. -/
theorem akm_heatKernel_prescribed_gradient_integrable
    {d : ℕ} {K : ℝ} (hK : 0 < K) {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y Z : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C)
    (hZm : Measurable (fun z : ℝ × (Vec d × Vec d) => Z z.1 z.2.1 z.2.2))
    (hZsol : ∀ y, IsFundamentalSolution A y
      (fun z => P z.1 z.2 y) (fun z => Z z.1 z.2 y))
    (hZw : ∀ y t, 0 < t → HasWeakGradient Set.univ
      (fun x => P t x y) (fun x => Z t x y))
    (y : Vec d) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x => Z t x y) volume := by
  obtain ⟨D,κ,hD,hκ,he⟩ := akm_heatKernel_prescribed_translated_gradient_energy
    hK hP hZsol hZw ht zero_lt_one
  apply integrable_of_translated_gaussian_energy
    (hZm.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))) hD hκ y
  · exact fun v => (he v y).1
  · exact fun v => (he v y).2

end EinsteinRelation.Correctors
