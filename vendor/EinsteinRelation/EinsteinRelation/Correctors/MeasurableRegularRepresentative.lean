import EinsteinRelation.Correctors.NormalizedScalarPhysicalLawTransportSupport
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# A measurable selection of regular spatial representatives

Source: `paper/main.tex:688-702,754-758`. Shrinking spatial averages give
a measurable choice determined by the spatial volume class. Wherever a
continuous local version exists, the choice recovers its point values.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace EinsteinRelation.Correctors

/-- Shrinking-ball averages of a random spatial field. -/
def spatialRegularAverage {d : ℕ} {Ω : Type*}
    (f : Ω → Vec d → ℝ) (n : ℕ) (ω : Ω) (x : Vec d) : ℝ :=
  ⨍ z in Metric.ball (0 : Vec d) (((n : ℝ) + 1)⁻¹), f ω (x + z) ∂volume

/-- The limit of shrinking-ball averages, determined by the volume class. -/
def spatialRegularRepresentative {d : ℕ} {Ω : Type*}
    (f : Ω → Vec d → ℝ) (ω : Ω) (x : Vec d) : ℝ :=
  limUnder atTop (fun n : ℕ => spatialRegularAverage f n ω x)

/-- Taking spatial averages preserves joint Borel measurability. -/
theorem measurable_spatialRegularAverage {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → Vec d → ℝ)
    (hf : Measurable (fun p : Vec d × Ω => f p.2 p.1)) (n : ℕ) :
    Measurable (fun p : Vec d × Ω => spatialRegularAverage f n p.2 p.1) := by
  have hm : Measurable (fun p : (Vec d × Ω) × Vec d => f p.1.2 (p.1.1 + p.2)) :=
    hf.comp ((measurable_fst.fst.add measurable_snd).prodMk measurable_fst.snd)
  unfold spatialRegularAverage
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  exact measurable_const.mul hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Limits of the measurable spatial averages remain jointly measurable,
including on the exceptional samples where no continuous version is known. -/
theorem measurable_spatialRegularRepresentative {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → Vec d → ℝ)
    (hf : Measurable (fun p : Vec d × Ω => f p.2 p.1)) :
    Measurable (fun p : Vec d × Ω => spatialRegularRepresentative f p.2 p.1) := by
  exact (StronglyMeasurable.limUnder (l := atTop)
    (fun n => (measurable_spatialRegularAverage f hf n).stronglyMeasurable)).measurable

end EinsteinRelation.Correctors
