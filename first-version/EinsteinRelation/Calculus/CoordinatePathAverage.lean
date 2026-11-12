import EinsteinRelation.Calculus.CoordinatePathMomentBounds
import EinsteinRelation.Correctors.ProbabilityAverageMoments
import EinsteinRelation.Correctors.CoordinateMomentProjections

/-! # Concrete small-scale path flux averages

Source: `paper/main.tex:1021–1029`. Averaging the literal coordinate
primitive against a normalized compact kernel gives a small-scale flux
whose moments cost only the support radius.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation

/-- The small-scale path flux, with the sign for `f - K*f`
(`paper/main.tex:1021–1029`). -/
def coordinatePathAverage {d : ℕ} (K : Vec d → ℝ) (f : FieldPair d → ℝ)
    (ω : FieldPair d) : Vec d :=
  fun i => -(∫ z : Vec d, K z * coordinatePathFlux f z ω i)

/-- The concrete averaged flux has measurable representatives
(`paper/main.tex:1021–1029`). -/
theorem measurable_coordinatePathAverage {d : ℕ} {K : Vec d → ℝ}
    (hK : Measurable K) {f : FieldPair d → ℝ} (hf : Measurable f) :
    Measurable (coordinatePathAverage K f) := by
  apply measurable_pi_lambda
  intro i
  have hm : Measurable (fun q : FieldPair d × Vec d => K q.2 * coordinatePathFlux f q.2 q.1 i) :=
    (hK.comp measurable_snd).mul
      ((measurable_pi_apply i).comp ((measurable_coordinatePathFlux hf).comp measurable_swap))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.neg

/-- Every coordinate of the small-scale flux has moment bounded by the
kernel support radius times the initial moment (`paper/main.tex:1028–1029`). -/
theorem eLpNorm_coordinatePathAverage_coordinate_le {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {L C : ℝ} (hL : 0 ≤ L)
    {K : Vec d → ℝ} (hK : Measurable K) (hKi : Integrable K volume)
    (hKn : ∀ z, 0 ≤ K z) (hKm : (∫ z, K z) = 1)
    (hKt : ∀ z, L ≤ euclideanNorm z → K z = 0)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfb : eLpNorm f p Q ≤ ENNReal.ofReal C) (i : Fin d) :
    eLpNorm (fun ω => coordinatePathAverage K f ω i) p Q ≤ ENNReal.ofReal (L * C) := by
  let ν : Measure (Vec d) := volume.withDensity (fun z => ENNReal.ofReal (K z))
  haveI : IsProbabilityMeasure ν := by
    constructor
    rw [show ν = volume.withDensity (fun z => ENNReal.ofReal (K z)) from rfl,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hKi (ae_of_all _ hKn), hKm, ENNReal.ofReal_one]
  have hbound : ∀ᵐ z ∂ν, eLpNorm (fun ω => coordinatePathFlux f z ω i) p Q ≤
      ENNReal.ofReal (L * C) := by
    apply (ae_withDensity_iff hK.ennreal_ofReal).mpr
    filter_upwards with z hz
    have hzn : euclideanNorm z < L := by
      by_contra h
      exact hz (by rw [hKt z (le_of_not_gt h)]; simp)
    have hzi : |z i| ≤ L := (Correctors.abs_coord_le_euclideanNorm z i).trans hzn.le
    calc
      _ ≤ ENNReal.ofReal |z i| * eLpNorm f p Q := eLpNorm_coordinatePathFlux_bound hQ hp hpt hf z i
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal C := mul_le_mul' (ENNReal.ofReal_le_ofReal hzi) hfb
      _ = _ := (ENNReal.ofReal_mul hL).symm
  have hm : Measurable (fun q : FieldPair d × Vec d => coordinatePathFlux f q.2 q.1 i) :=
    (measurable_pi_apply i).comp ((measurable_coordinatePathFlux hf).comp measurable_swap)
  have hb := Correctors.eLpNorm_integral_probability_le_ae_bound ν hp hpt hm hbound
  have heq : (fun ω => coordinatePathAverage K f ω i) =
      fun ω => -(∫ z, coordinatePathFlux f z ω i ∂ν) := by
    funext ω
    unfold coordinatePathAverage
    congr 1
    rw [integral_withDensity_eq_integral_toReal_smul hK.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards with z
    simp only [ENNReal.toReal_ofReal (hKn z), smul_eq_mul]
  rw [heq]
  change eLpNorm (-(fun ω => ∫ z, coordinatePathFlux f z ω i ∂ν)) p Q ≤ _
  rw [eLpNorm_neg]
  exact hb

end EinsteinRelation
