import EinsteinRelation.Calculus.CoordinatePathIntegratedDivergence
import EinsteinRelation.Calculus.CoordinatePathAverage

/-! # The actual small-scale residual flux identity

Source: `paper/main.tex:1021–1029`. The concrete compactly averaged path
flux has divergence equal to the scalar field minus its spatial average.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation

/-- The literal small-scale flux solves its residual divergence equation
(`paper/main.tex:1021–1029`). -/
theorem hasWeakHorizontalDivergence_coordinatePathAverage
    {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {L : ℝ} (hL : 0 ≤ L)
    {K : Vec d → ℝ} (hK : Measurable K) (hKi : Integrable K volume)
    (hKn : ∀ z, 0 ≤ K z) (hKm : (∫ z, K z) = 1)
    (hKt : ∀ z, L ≤ euclideanNorm z → K z = 0)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 Q) :
    HasWeakHorizontalDivergence Q hQ (coordinatePathAverage K f)
      (fun ω => f ω - horizontalMollify K f ω) := by
  let ν : Measure (Vec d) := volume.withDensity (fun z => ENNReal.ofReal (K z))
  haveI : IsProbabilityMeasure ν := by
    constructor
    rw [show ν = volume.withDensity (fun z => ENNReal.ofReal (K z)) from rfl,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hKi (ae_of_all _ hKn), hKm, ENNReal.ofReal_one]
  have hν : ∀ᵐ z ∂ν, euclideanNorm z < L := by
    apply (ae_withDensity_iff hK.ennreal_ofReal).mpr
    filter_upwards with z hz
    by_contra h
    exact hz (by rw [hKt z (le_of_not_gt h)]; simp)
  have hi (i : Fin d) : Integrable (fun z : Vec d => |z i|) ν := by
    apply (integrable_const L).mono'
      ((measurable_pi_apply i).abs.aestronglyMeasurable)
    filter_upwards [hν] with z hz
    rw [Real.norm_eq_abs, abs_abs]
    exact (Correctors.abs_coord_le_euclideanNorm z i).trans hz.le
  have h := (hasWeakHorizontalDivergence_coordinatePath_integral hQ ν hf hf2 hi).smul (-1)
  have he (g : Vec d → ℝ) : (∫ z, g z ∂ν) = ∫ z, K z * g z := by
    rw [show ν = volume.withDensity (fun z => ENNReal.ofReal (K z)) from rfl,
      integral_withDensity_eq_integral_toReal_smul hK.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards with z
    simp only [ENNReal.toReal_ofReal (hKn z), smul_eq_mul]
  convert h using 1
  · funext ω i
    simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul, he, coordinatePathAverage]
  · funext ω
    simp only [he, horizontalMollify]
    ring

end EinsteinRelation
