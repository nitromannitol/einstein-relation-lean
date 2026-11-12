import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.MeasureTheory.Integral.Prod

/-! Joint measurability of the literal integrated-gradient spatial RMS,
used in `paper/main.tex:843–849`. -/

open MeasureTheory Set
namespace EinsteinRelation.Correctors
open External.AKM

/-- Parameter measurability for the time integral followed by its spatial
Euclidean energy. Source: `paper/main.tex:843–849`. -/
theorem measurable_integrated_gradient_rms {d : ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (T : ℝ) (G : Ω → ℝ × X → Vec d)
    (hG : Measurable (fun z : Ω × (ℝ × X) => G z.1 z.2)) :
    Measurable (fun ω => Real.sqrt (∫ x, euclideanSq
      (∫ t in Icc (0 : ℝ) T, G ω (t,x)) ∂ν)) := by
  have hs : Measurable (fun z : (Ω × X) × ℝ => G z.1.1 (z.2,z.1.2)) :=
    hG.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))
  have hi : Measurable (fun z : Ω × X => ∫ t in Icc (0 : ℝ) T, G z.1 (t,z.2)) :=
    hs.stronglyMeasurable.integral_prod_right'.measurable
  have hsq : Measurable (fun z : Ω × X => euclideanSq
      (∫ t in Icc (0 : ℝ) T, G z.1 (t,z.2))) := by
    unfold euclideanSq dot
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp hi).mul ((measurable_pi_apply j).comp hi)
  exact hsq.stronglyMeasurable.integral_prod_right'.measurable.sqrt

end EinsteinRelation.Correctors
