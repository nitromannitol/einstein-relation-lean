import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Joint measurability of the scalar kernel formula with parameter-dependent
data. Source: AKM (9.2), p. 347; `paper/main.tex:787–792`. -/
theorem measurable_kernel_data_average
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (ν : Measure E) [SFinite ν]
    {p : Ω → ℝ × E → E → ℝ} {f : Ω → E → ℝ}
    (hp : Measurable (fun z : (Ω × (ℝ × E)) × E => p z.1.1 z.1.2 z.2))
    (hf : Measurable (fun z : Ω × E => f z.1 z.2)) :
    Measurable (fun z : Ω × (ℝ × E) => ∫ y, p z.1 z.2 y * f z.1 y ∂ν) := by
  let F : (Ω × (ℝ × E)) × E → ℝ := fun z => p z.1.1 z.1.2 z.2 * f z.1.1 z.2
  have hF_meas : Measurable F := by
    have hF1 : Measurable (fun (z : (Ω × (ℝ × E)) × E) => p z.1.1 z.1.2 z.2) := hp
    have hF2 : Measurable (fun (z : (Ω × (ℝ × E)) × E) => f z.1.1 z.2) :=
      hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact hF1.mul hF2
  have hF_strongly : StronglyMeasurable F := hF_meas.stronglyMeasurable
  have h_int_strongly : StronglyMeasurable (fun (z : Ω × (ℝ × E)) => ∫ y, F (z, y) ∂ν) :=
    hF_strongly.integral_prod_right'
  simpa [F] using h_int_strongly.measurable

end EinsteinRelation.Correctors
