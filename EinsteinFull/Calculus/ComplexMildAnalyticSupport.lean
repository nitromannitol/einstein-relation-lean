import EinsteinFull.Calculus.ComplexWeightedVolterraSupport

/-!
# Operator-norm force analyticity via the actual mild Duhamel integral

The unforced propagation of the coefficient drift defines a bounded complex
linear map from square-root-weighted continuous gradient orbits to L2.
Its value on the actual orbit is the mild convolution. Composition transfers
the proved weighted-gradient analyticity to the actual semigroup at zero force.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

local notation "Grad" => PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))

/-- The unforced drift integrand evaluated on a square-root-weighted orbit. -/
def weightedDuhamelIntegrand (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0)
    (g : Ioc (0 : ℝ) (t : ℝ) →ᵇ
      PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) (s : ℝ) : Lp ℂ 2 (reducedLaw Q) :=
  if hs : s ∈ Ioc (0 : ℝ) (t : ℝ) then
    (Real.sqrt s)⁻¹ • R (Real.toNNReal (t-s)) (complexForceDrift Q i (g ⟨s, hs⟩))
  else 0

private theorem continuousOn_weighted_drift
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (t : ℝ≥0)
    (g : Ioc (0 : ℝ) (t : ℝ) →ᵇ Grad) :
    ContinuousOn (weightedDuhamelIntegrand Q i R t g) (Ioc (0 : ℝ) (t : ℝ)) := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun s : Ioc (0 : ℝ) (t : ℝ) => weightedDuhamelIntegrand Q i R t g s.1)
  have hc : Continuous (fun s : Ioc (0 : ℝ) (t : ℝ) =>
      R (Real.toNNReal (t-s.1)) (complexForceDrift Q i (g s))) :=
    hR.continuous_unforced_apply
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_subtype_val))
      ((complexForceDrift Q i).continuous.comp g.continuous)
  have hi : Continuous (fun s : Ioc (0 : ℝ) (t : ℝ) => (Real.sqrt s.1)⁻¹) :=
    (Real.continuous_sqrt.comp continuous_subtype_val).inv₀
      (fun s => ne_of_gt (Real.sqrt_pos.mpr s.2.1))
  apply Continuous.congr (hi.fun_smul hc)
  intro s
  simp only [weightedDuhamelIntegrand, dif_pos s.2]

/-- A single inverse-square-root majorant controls every bounded weighted orbit. -/
theorem IsComplexEnvironmentSemigroup.norm_weightedDuhamelIntegrand_le
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (t : ℝ≥0)
    (g : Ioc (0 : ℝ) (t : ℝ) →ᵇ Grad) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (t : ℝ)) :
    ‖weightedDuhamelIntegrand Q i R t g s‖ ≤
      (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * ‖g‖) * (Real.sqrt s)⁻¹ := by
  have hΛ : 0 ≤ Λ₀ := zero_le_one.trans Q.ellipticity_parameter
  rw [weightedDuhamelIntegrand, dif_pos hs,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (Real.sqrt s)⁻¹ * (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * ‖g‖) := by
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (hR.norm_unforced_apply_le _ _).trans
        ((norm_complexForceDrift_apply_le Q i _).trans
          (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (by positivity)))
    _ = _ := mul_comm _ _

/-- Every bounded weighted orbit gives a Bochner-integrable Duhamel drift. -/
theorem IsComplexEnvironmentSemigroup.intervalIntegrable_weightedDuhamelIntegrand
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (t : ℝ≥0)
    (g : Ioc (0 : ℝ) (t : ℝ) →ᵇ Grad) :
    IntervalIntegrable (weightedDuhamelIntegrand Q i R t g) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)]
  apply ((intervalIntegrable_inv_sqrt t.property).const_mul
    (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * ‖g‖)).1.mono'
  · letI : SecondCountableTopologyEither ℝ (Lp ℂ 2 (reducedLaw Q)) :=
      secondCountableTopologyEither_of_left ℝ _
    exact (continuousOn_weighted_drift hR t g).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hR.norm_weightedDuhamelIntegrand_le t g hs

private theorem integral_bound
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (t : ℝ≥0)
    (g : Ioc (0 : ℝ) (t : ℝ) →ᵇ Grad) :
    ‖∫ s in (0 : ℝ)..(t : ℝ), weightedDuhamelIntegrand Q i R t g s‖ ≤
      (2 * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * Real.sqrt (t : ℝ)) * ‖g‖ := by
  calc
    _ ≤ ∫ s in (0 : ℝ)..(t : ℝ),
        (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * ‖g‖) * (Real.sqrt s)⁻¹ :=
      intervalIntegral.norm_integral_le_of_norm_le t.property
        (Eventually.of_forall fun s hs => hR.norm_weightedDuhamelIntegrand_le t g hs)
        ((intervalIntegrable_inv_sqrt t.property).const_mul _)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_inv_sqrt (t := (t : ℝ)) t.property]
      ring

/-- The unforced Duhamel integral is a bounded complex linear map on weighted orbits. -/
def IsComplexEnvironmentSemigroup.weightedDuhamel
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (t : ℝ≥0) :
    (Ioc (0 : ℝ) (t : ℝ) →ᵇ Grad) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  let L : (Ioc (0 : ℝ) (t : ℝ) →ᵇ Grad) →ₗ[ℂ] Lp ℂ 2 (reducedLaw Q) :=
    { toFun := fun g => ∫ s in (0 : ℝ)..(t : ℝ), weightedDuhamelIntegrand Q i R t g s
      map_add' := fun g h => by
        have he : weightedDuhamelIntegrand Q i R t (g+h) = fun s =>
            weightedDuhamelIntegrand Q i R t g s + weightedDuhamelIntegrand Q i R t h s := by
          funext s
          by_cases hs : s ∈ Ioc (0 : ℝ) (t : ℝ)
          · simp only [weightedDuhamelIntegrand, dif_pos hs,
              BoundedContinuousFunction.coe_add, Pi.add_apply, map_add, smul_add]
          · simp only [weightedDuhamelIntegrand, dif_neg hs,
              add_zero]
        rw [he, intervalIntegral.integral_add
          (hR.intervalIntegrable_weightedDuhamelIntegrand t g)
          (hR.intervalIntegrable_weightedDuhamelIntegrand t h)]
      map_smul' := fun c g => by
        have he : weightedDuhamelIntegrand Q i R t (c • g) = fun s =>
            c • weightedDuhamelIntegrand Q i R t g s := by
          funext s
          by_cases hs : s ∈ Ioc (0 : ℝ) (t : ℝ)
          · simp only [weightedDuhamelIntegrand, dif_pos hs,
              BoundedContinuousFunction.coe_smul, map_smul]
            exact smul_comm _ _ _
          · simp only [weightedDuhamelIntegrand, dif_neg hs,
              smul_zero]
        change _ = c • _
        rw [he, intervalIntegral.integral_smul] }
  L.mkContinuous (2 * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * Real.sqrt (t : ℝ))
    (integral_bound hR t)

/-- Evaluation of the bounded integral map is the actual unforced Duhamel integral. -/
theorem IsComplexEnvironmentSemigroup.weightedDuhamel_apply
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (t : ℝ≥0)
    (g : Ioc (0 : ℝ) (t : ℝ) →ᵇ Grad) :
    hR.weightedDuhamel t g = ∫ s in (0 : ℝ)..(t : ℝ), weightedDuhamelIntegrand Q i R t g s := rfl

/-- The integral map has the explicit square-root-time operator norm bound. -/
theorem IsComplexEnvironmentSemigroup.norm_weightedDuhamel_le
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (t : ℝ≥0) :
    ‖hR.weightedDuhamel t‖ ≤
      2 * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * Real.sqrt (t : ℝ) := by
  have hΛ : 0 ≤ Λ₀ := zero_le_one.trans Q.ellipticity_parameter
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (integral_bound hR t)

/-- On the actual weighted orbit, the bounded map recovers the original mild convolution. -/
theorem IsComplexEnvironmentSemigroup.weightedDuhamel_actual
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    hR.weightedDuhamel t (hP.weightedGradientOrbit t f) =
      ∫ s in (0 : ℝ)..(t : ℝ), R (Real.toNNReal (t-s))
        (complexForceDrift Q i (hP.gradientOrbit f s)) := by
  rw [hR.weightedDuhamel_apply]
  apply intervalIntegral.integral_congr_ae
  apply Eventually.of_forall
  intro s hs
  rw [uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hs
  rw [weightedDuhamelIntegrand, dif_pos hs,
    hP.weightedGradientOrbit_apply, (complexForceDrift Q i).map_smul_of_tower,
    (R _).map_smul_of_tower, smul_smul,
    inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hs.1)), one_smul]

/-- Mild Duhamel is a bounded linear composition with the actual weighted gradient orbit. -/
theorem IsComplexEnvironmentSemigroup.eq_add_weightedDuhamel
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (t : ℝ≥0) :
    P t = R t + ζ • (hR.weightedDuhamel t).comp (hP.weightedGradientOrbit t) := by
  apply ContinuousLinearMap.ext
  intro f
  change P t f = R t f + ζ • hR.weightedDuhamel t (hP.weightedGradientOrbit t f)
  rw [hP.weightedDuhamel_actual hR t f]
  exact hP.mild_duhamel hR f t

/-- The actual complex-force semigroup is analytic at zero force in operator norm. -/
theorem analyticAt_complexEnvironmentSemigroup_zero
    {F : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z)) (t : ℝ≥0) :
    AnalyticAt ℂ (fun z => F z t) 0 := by
  have hg := analyticAt_weightedGradientOrbit hF (t : ℝ)
  have hc := (((ContinuousLinearMap.compL ℂ _ _ _) ((hF 0).weightedDuhamel t)).analyticAt _).comp hg
  have ha := (analyticAt_const (v := F 0 t)).add
    ((analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))).fun_smul hc)
  apply ha.congr
  apply Eventually.of_forall
  intro z
  exact ((hF z).eq_add_weightedDuhamel (hF 0) t).symm

/-- The internally constructed stationary complex-force evolution has operator-norm analyticity at zero. -/
theorem analyticAt_forcedComplexEvolution_zero (t : ℝ≥0) :
    AnalyticAt ℂ (fun z => forcedComplexEvolution Q i z t) 0 :=
  analyticAt_complexEnvironmentSemigroup_zero
    (fun z => isComplexEnvironmentSemigroup_forcedComplexEvolution Q i z) t

end EinsteinFull
