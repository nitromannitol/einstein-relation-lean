import EinsteinFull.Calculus.ComplexMildGradientSupport
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import EinsteinFull.Calculus.VolterraSeriesSupport

/-!
# Weighted gradient Volterra convolution and a convergent force series

The actual gradient embeds into bounded continuous square-root-weighted orbits
on `(0,T]`. Rescaling time to `(0,1)` gives a single integrable majorant and
proves continuity of the unforced convolution. Its explicit norm bound and
the actual Volterra identity identify the Neumann series and give operator
norm analyticity of the weighted gradient at zero force.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

/-- The actual unforced positive-time gradient is jointly strongly continuous in time and datum. -/
theorem IsComplexEnvironmentSemigroup.continuous_unforcedGradient
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    {α : Type*} [TopologicalSpace α] (t : α → {s : ℝ≥0 // 0 < s})
    (f : α → Lp ℂ 2 (reducedLaw Q)) (ht : Continuous t) (hf : Continuous f) :
    Continuous (fun x => hR.unforcedGradient (t x).1 (t x).2 (f x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let δ : ℝ≥0 := (t x).1 / 2
  have hδ : 0 < δ := half_pos (t x).2
  have hδt : δ < (t x).1 := half_lt_self (t x).2
  have hv : Continuous (fun y => hR.unforcedGradient δ hδ (R ((t y).1-δ) (f y))) :=
    (hR.unforcedGradient δ hδ).continuous.comp
      (hR.continuous_unforced_apply ((continuous_subtype_val.comp ht).fun_sub continuous_const) hf)
  apply hv.continuousAt.congr_of_eventuallyEq
  filter_upwards [((continuous_subtype_val.comp ht).tendsto x).eventually
    (eventually_gt_nhds hδt)] with y hy
  have he := congrArg (fun A => A (f y)) (hR.unforcedGradient_add δ hδ ((t y).1-δ))
  have hy' : δ ≤ (t y).1 := hy.le
  have heq : δ + ((t y).1-δ) = (t y).1 := add_tsub_cancel_of_le hy'
  simpa only [heq, ContinuousLinearMap.comp_apply] using he

private theorem weighted_bound (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (T : ℝ) (f : Lp ℂ 2 (reducedLaw Q)) (t : Ioc (0 : ℝ) T) :
    ‖Real.sqrt t.1 • hP.gradientOrbit f t.1‖ ≤
      (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
        Real.exp (65 * complexForceShift d Λ₀ ζ * T)) * ‖f‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := mul_le_mul_of_nonneg_left (hP.norm_gradientOrbit_le f t.2.1 t.2.2)
    (Real.sqrt_nonneg t.1)
  have hs : Real.sqrt t.1 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 t.2.1)
  simpa only [← mul_assoc, mul_comm (Real.sqrt t.1), mul_assoc,
    inv_mul_cancel₀ hs, mul_one] using h

private theorem weighted_continuous (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (T : ℝ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t : Ioc (0 : ℝ) T => Real.sqrt t.1 • hP.gradientOrbit f t.1) :=
  (Real.continuous_sqrt.comp continuous_subtype_val).fun_smul
    ((hP.continuousOn_gradientOrbit f).comp_continuous continuous_subtype_val fun t => t.2.1)

/-- The actual gradient orbit in the complete space of square-root-weighted continuous orbits. -/
def IsComplexEnvironmentSemigroup.weightedGradientOrbit
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (T : ℝ) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ]
      (Ioc (0 : ℝ) T →ᵇ PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) :=
  let L : Lp ℂ 2 (reducedLaw Q) →ₗ[ℂ]
      (Ioc (0 : ℝ) T →ᵇ PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) :=
    { toFun := fun f => BoundedContinuousFunction.ofNormedAddCommGroup _
        (weighted_continuous hP T f)
        ((2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
          Real.exp (65 * complexForceShift d Λ₀ ζ * T)) * ‖f‖)
        (weighted_bound hP T f)
      map_add' := fun f g => by
        apply BoundedContinuousFunction.ext
        intro t
        simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup,
          BoundedContinuousFunction.coe_add, Pi.add_apply,
          IsComplexEnvironmentSemigroup.gradientOrbit, dif_pos t.2.1, map_add, smul_add]
      map_smul' := fun c f => by
        apply BoundedContinuousFunction.ext
        intro t
        simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup,
          BoundedContinuousFunction.coe_smul,
          IsComplexEnvironmentSemigroup.gradientOrbit, dif_pos t.2.1, map_smul]
        exact smul_comm _ _ _ }
  L.mkContinuous (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
    Real.exp (65 * complexForceShift d Λ₀ ζ * T)) fun f =>
      (BoundedContinuousFunction.norm_le (by positivity)).2 (weighted_bound hP T f)

/-- Evaluation of the weighted orbit recovers the actual positive-time gradient. -/
theorem IsComplexEnvironmentSemigroup.weightedGradientOrbit_apply
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (T : ℝ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : Ioc (0 : ℝ) T) :
    hP.weightedGradientOrbit T f t = Real.sqrt t.1 • hP.gradientOrbit f t.1 := rfl

/-- The weighted actual gradient is uniformly bounded on each finite time interval. -/
theorem IsComplexEnvironmentSemigroup.norm_weightedGradientOrbit_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (T : ℝ) :
    ‖hP.weightedGradientOrbit T‖ ≤ 2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      Real.exp (65 * complexForceShift d Λ₀ ζ * T) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f =>
    (BoundedContinuousFunction.norm_le (by positivity)).2 (weighted_bound hP T f)


local notation "Grad" => PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))

private def driftTime {T : ℝ} (t : Ioc (0 : ℝ) T) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    {s : ℝ≥0 // 0 < s} :=
  ⟨(t.1*(1-r)).toNNReal, Real.toNNReal_pos.mpr (mul_pos t.2.1 (sub_pos.mpr hr.2))⟩

private def inputTime {T : ℝ} (t : Ioc (0 : ℝ) T) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Ioc (0 : ℝ) T :=
  ⟨t.1*r, mul_pos t.2.1 hr.1,
    (mul_le_of_le_one_right t.2.1.le hr.2.le).trans t.2.2⟩

/-- The fixed-unit-interval integrand of the square-root-weighted gradient convolution. -/
def IsComplexEnvironmentSemigroup.weightedVolterraIntegrand
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) {T : ℝ}
    (g : Ioc (0 : ℝ) T →ᵇ Grad) (t : Ioc (0 : ℝ) T) (r : ℝ) : Grad :=
  if hr : r ∈ Ioo (0 : ℝ) 1 then
    (t.1 * (Real.sqrt r)⁻¹) • hR.unforcedGradient (driftTime t hr).1 (driftTime t hr).2
      (complexForceDrift Q i (g (inputTime t hr)))
  else 0

private theorem continuous_integrand_time
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) {T : ℝ}
    (g : Ioc (0 : ℝ) T →ᵇ Grad) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Continuous (fun t : Ioc (0 : ℝ) T => hR.weightedVolterraIntegrand g t r) := by
  have hc : Continuous (fun t : Ioc (0 : ℝ) T =>
      hR.unforcedGradient (driftTime t hr).1 (driftTime t hr).2
        (complexForceDrift Q i (g (inputTime t hr)))) :=
    hR.continuous_unforcedGradient _ _
      ((continuous_real_toNNReal.comp (continuous_subtype_val.fun_mul continuous_const)).subtype_mk _)
      ((complexForceDrift Q i).continuous.comp
        (g.continuous.comp ((continuous_subtype_val.fun_mul continuous_const).subtype_mk _)))
  simpa only [IsComplexEnvironmentSemigroup.weightedVolterraIntegrand, dif_pos hr] using
    (continuous_subtype_val.fun_mul continuous_const).fun_smul hc

private theorem continuousOn_integrand_space
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) {T : ℝ}
    (g : Ioc (0 : ℝ) T →ᵇ Grad) (t : Ioc (0 : ℝ) T) :
    ContinuousOn (hR.weightedVolterraIntegrand g t) (Ioo (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun r : Ioo (0 : ℝ) 1 => hR.weightedVolterraIntegrand g t r.1)
  have hc : Continuous (fun r : Ioo (0 : ℝ) 1 =>
      hR.unforcedGradient (driftTime t r.2).1 (driftTime t r.2).2
        (complexForceDrift Q i (g (inputTime t r.2)))) :=
    hR.continuous_unforcedGradient _ _
      ((continuous_real_toNNReal.comp
        (continuous_const.fun_mul (continuous_const.fun_sub continuous_subtype_val))).subtype_mk _)
      ((complexForceDrift Q i).continuous.comp
        (g.continuous.comp ((continuous_const.fun_mul continuous_subtype_val).subtype_mk _)))
  have hi : Continuous (fun r : Ioo (0 : ℝ) 1 => (Real.sqrt r.1)⁻¹) :=
    (Real.continuous_sqrt.comp continuous_subtype_val).inv₀
      (fun r => ne_of_gt (Real.sqrt_pos.mpr r.2.1))
  apply Continuous.congr (((continuous_const (y := t.1)).fun_mul hi).fun_smul hc)
  intro r
  simp only [IsComplexEnvironmentSemigroup.weightedVolterraIntegrand, dif_pos r.2]

private theorem scalar_kernel_identity {t r K B N : ℝ} (ht : 0 < t)
    (hK : 0 ≤ K) :
    (t * (Real.sqrt r)⁻¹) * (Real.sqrt (K/(t*(1-r))) * (B*N)) =
      (Real.sqrt K * B * Real.sqrt t * N) *
        ((Real.sqrt r)⁻¹ * (Real.sqrt (1-r))⁻¹) := by
  rw [Real.sqrt_div hK, Real.sqrt_mul ht.le, div_eq_mul_inv, mul_inv_rev]
  have he : t * (Real.sqrt t)⁻¹ = Real.sqrt t := by
    calc
      _ = (Real.sqrt t * Real.sqrt t) * (Real.sqrt t)⁻¹ := by rw [Real.mul_self_sqrt ht.le]
      _ = _ := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.2 ht)), mul_one]
  calc
    _ = (t * (Real.sqrt t)⁻¹) *
        (Real.sqrt K * B * N * (Real.sqrt r)⁻¹ * (Real.sqrt (1-r))⁻¹) := by ring
    _ = _ := by rw [he]; ring

/-- The unit-interval gradient kernel has a single integrable bound, uniformly in time. -/
theorem IsComplexEnvironmentSemigroup.norm_weightedVolterraIntegrand_le
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) {T : ℝ}
    (g : Ioc (0 : ℝ) T →ᵇ Grad) (t : Ioc (0 : ℝ) T) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    ‖hR.weightedVolterraIntegrand g t r‖ ≤
      (Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
        Real.sqrt T * ‖g‖) * ((Real.sqrt r)⁻¹ * (Real.sqrt (1-r))⁻¹) := by
  have hΛ : 0 ≤ Λ₀ := zero_le_one.trans Q.ellipticity_parameter
  have hK : 0 ≤ Real.exp (2 * Λ₀) * Λ₀ := by positivity
  have htr : 0 < t.1*(1-r) := mul_pos t.2.1 (sub_pos.2 hr.2)
  have hcoef : 0 ≤ t.1 * (Real.sqrt r)⁻¹ :=
    mul_nonneg t.2.1.le (inv_nonneg.mpr (Real.sqrt_nonneg r))
  rw [IsComplexEnvironmentSemigroup.weightedVolterraIntegrand, dif_pos hr,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef]
  have hn := (hR.unforcedGradient (driftTime t hr).1 (driftTime t hr).2).le_opNorm
    (complexForceDrift Q i (g (inputTime t hr)))
  have hg := norm_complexForceDrift_apply_le Q i (g (inputTime t hr))
  have hb := hR.norm_unforcedGradient_le (driftTime t hr).1 (driftTime t hr).2
  dsimp only [driftTime] at hb
  rw [Real.coe_toNNReal _ htr.le] at hb
  calc
    _ ≤ (t.1 * (Real.sqrt r)⁻¹) *
        (Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀)/(t.1*(1-r))) *
          (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * ‖g‖)) := by
      exact mul_le_mul_of_nonneg_left (hn.trans (mul_le_mul hb
        (hg.trans (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (by positivity)))
        (norm_nonneg _) (Real.sqrt_nonneg _))) hcoef
    _ = (Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
        Real.sqrt t.1 * ‖g‖) * ((Real.sqrt r)⁻¹ * (Real.sqrt (1-r))⁻¹) :=
      scalar_kernel_identity t.2.1 hK
    _ ≤ _ := by gcongr; exact t.2.2

private theorem integrable_weighted_integrand
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) {T : ℝ}
    (g : Ioc (0 : ℝ) T →ᵇ Grad) (t : Ioc (0 : ℝ) T) :
    IntervalIntegrable (hR.weightedVolterraIntegrand g t) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply (((intervalIntegrable_inv_sqrt_mul_inv_sqrt_sub (by norm_num : (0 : ℝ) < 1)).const_mul
    (Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
      Real.sqrt T * ‖g‖)).1.mono_set Ioo_subset_Ioc_self).mono'
  · letI : SecondCountableTopologyEither ℝ Grad :=
      secondCountableTopologyEither_of_left ℝ Grad
    exact (continuousOn_integrand_space hR g t).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hR.norm_weightedVolterraIntegrand_le g t hr

private theorem continuous_integral
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) {T : ℝ}
    (g : Ioc (0 : ℝ) T →ᵇ Grad) :
    Continuous (fun t : Ioc (0 : ℝ) T => ∫ r in (0 : ℝ)..1,
      hR.weightedVolterraIntegrand g t r) := by
  apply intervalIntegral.continuous_of_dominated_interval
    (bound := fun r : ℝ => (Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * Real.sqrt T * ‖g‖) *
      ((Real.sqrt r)⁻¹ * (Real.sqrt (1-r))⁻¹))
  · intro t
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (integrable_weighted_integrand hR g t).aestronglyMeasurable
  · intro t
    filter_upwards [volume.ae_ne (1 : ℝ)] with r hr hr'
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr'
    exact hR.norm_weightedVolterraIntegrand_le g t ⟨hr'.1, lt_of_le_of_ne hr'.2 hr⟩
  · exact (intervalIntegrable_inv_sqrt_mul_inv_sqrt_sub (by norm_num : (0 : ℝ) < 1)).const_mul _
  · filter_upwards [volume.ae_ne (1 : ℝ)] with r hr hr'
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr'
    exact continuous_integrand_time hR g ⟨hr'.1, lt_of_le_of_ne hr'.2 hr⟩

private theorem integral_bound
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) {T : ℝ}
    (g : Ioc (0 : ℝ) T →ᵇ Grad) (t : Ioc (0 : ℝ) T) :
    ‖∫ r in (0 : ℝ)..1, hR.weightedVolterraIntegrand g t r‖ ≤
      (4 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
        Real.sqrt T) * ‖g‖ := by
  have hΛ : 0 ≤ Λ₀ := zero_le_one.trans Q.ellipticity_parameter
  let C := Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
    Real.sqrt T * ‖g‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∫ r in (0 : ℝ)..1, C * ((Real.sqrt r)⁻¹ * (Real.sqrt (1-r))⁻¹) := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1) ?_
        ((intervalIntegrable_inv_sqrt_mul_inv_sqrt_sub (by norm_num : (0 : ℝ) < 1)).const_mul C)
      filter_upwards [volume.ae_ne (1 : ℝ)] with r hr hr'
      exact hR.norm_weightedVolterraIntegrand_le g t ⟨hr'.1, lt_of_le_of_ne hr'.2 hr⟩
    _ ≤ 4*C := by
      rw [intervalIntegral.integral_const_mul]
      exact (mul_le_mul_of_nonneg_left (integral_inv_sqrt_mul_inv_sqrt_sub_le
        (by norm_num : (0 : ℝ) < 1)) hC).trans_eq (mul_comm C 4)
    _ = _ := by dsimp [C]; ring


/-- The actual unforced-gradient Volterra convolution on square-root-weighted continuous orbits. -/
def IsComplexEnvironmentSemigroup.weightedVolterra
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (T : ℝ) :
    (Ioc (0 : ℝ) T →ᵇ Grad) →L[ℂ] (Ioc (0 : ℝ) T →ᵇ Grad) :=
  let L : (Ioc (0 : ℝ) T →ᵇ Grad) →ₗ[ℂ] (Ioc (0 : ℝ) T →ᵇ Grad) :=
    { toFun := fun g => BoundedContinuousFunction.ofNormedAddCommGroup _
        (continuous_integral hR g)
        ((4 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
          Real.sqrt T) * ‖g‖) (integral_bound hR g)
      map_add' := fun g h => by
        apply BoundedContinuousFunction.ext
        intro t
        change (∫ r in (0 : ℝ)..1, hR.weightedVolterraIntegrand (g+h) t r) =
          (∫ r in (0 : ℝ)..1, hR.weightedVolterraIntegrand g t r) +
          (∫ r in (0 : ℝ)..1, hR.weightedVolterraIntegrand h t r)
        have he : hR.weightedVolterraIntegrand (g+h) t = fun r =>
            hR.weightedVolterraIntegrand g t r + hR.weightedVolterraIntegrand h t r := by
          funext r
          by_cases hr : r ∈ Ioo (0 : ℝ) 1
          · simp only [IsComplexEnvironmentSemigroup.weightedVolterraIntegrand, dif_pos hr,
              BoundedContinuousFunction.coe_add, Pi.add_apply, map_add, smul_add]
          · simp only [IsComplexEnvironmentSemigroup.weightedVolterraIntegrand, dif_neg hr,
              add_zero]
        rw [he, intervalIntegral.integral_add (integrable_weighted_integrand hR g t)
          (integrable_weighted_integrand hR h t)]
      map_smul' := fun c g => by
        apply BoundedContinuousFunction.ext
        intro t
        change (∫ r in (0 : ℝ)..1, hR.weightedVolterraIntegrand (c • g) t r) =
          c • (∫ r in (0 : ℝ)..1, hR.weightedVolterraIntegrand g t r)
        have he : hR.weightedVolterraIntegrand (c • g) t = fun r =>
            c • hR.weightedVolterraIntegrand g t r := by
          funext r
          by_cases hr : r ∈ Ioo (0 : ℝ) 1
          · simp only [IsComplexEnvironmentSemigroup.weightedVolterraIntegrand, dif_pos hr,
              BoundedContinuousFunction.coe_smul, map_smul]
            exact smul_comm _ _ _
          · simp only [IsComplexEnvironmentSemigroup.weightedVolterraIntegrand, dif_neg hr,
              smul_zero]
        rw [he, intervalIntegral.integral_smul] }
  L.mkContinuous (4 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
    ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * Real.sqrt T) fun g =>
      (BoundedContinuousFunction.norm_le (by
        have hΛ : 0 ≤ Λ₀ := zero_le_one.trans Q.ellipticity_parameter
        positivity)).2 (integral_bound hR g)

/-- Evaluation of the bounded Volterra operator is its actual fixed-interval Bochner integral. -/
theorem IsComplexEnvironmentSemigroup.weightedVolterra_apply
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (T : ℝ)
    (g : Ioc (0 : ℝ) T →ᵇ Grad) (t : Ioc (0 : ℝ) T) :
    hR.weightedVolterra T g t = ∫ r in (0 : ℝ)..1, hR.weightedVolterraIntegrand g t r := rfl

/-- The Volterra operator becomes a contraction after multiplication by a sufficiently small force. -/
theorem IsComplexEnvironmentSemigroup.norm_weightedVolterra_le
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (T : ℝ) :
    ‖hR.weightedVolterra T‖ ≤ 4 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * Real.sqrt T := by
  have hΛ : 0 ≤ Λ₀ := zero_le_one.trans Q.ellipticity_parameter
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro g
  exact (BoundedContinuousFunction.norm_le (by positivity)).2 (integral_bound hR g)


private theorem integrand_on_actual_orbit
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) {T : ℝ}
    (f : Lp ℂ 2 (reducedLaw Q)) (t : Ioc (0 : ℝ) T) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    hR.weightedVolterraIntegrand (hP.weightedGradientOrbit T f) t r =
      t.1 • (Real.sqrt t.1 • hP.gradientDuhamelIntegrand hR f t.1 (t.1*r)) := by
  have htau : 0 < t.1*(1-r) := mul_pos t.2.1 (sub_pos.2 hr.2)
  have heG (x : Lp ℂ 2 (reducedLaw Q)) :
      hR.unforcedGradient (driftTime t hr).1 (driftTime t hr).2 x =
        hR.gradientOrbit x (t.1*(1-r)) := by
    apply hR.unforcedGradient_eq
    simpa only [driftTime] using hR.gradientOrbit_spec x htau
  rw [IsComplexEnvironmentSemigroup.weightedVolterraIntegrand, dif_pos hr,
    hP.weightedGradientOrbit_apply]
  dsimp only [inputTime]
  rw [(complexForceDrift Q i).map_smul_of_tower,
    (hR.unforcedGradient (driftTime t hr).1 (driftTime t hr).2).map_smul_of_tower,
    heG, smul_smul, smul_smul]
  have hs : t.1 * (Real.sqrt r)⁻¹ * Real.sqrt (t.1*r) = t.1 * Real.sqrt t.1 := by
    rw [Real.sqrt_mul t.2.1.le]
    calc
      _ = (t.1 * Real.sqrt t.1) * ((Real.sqrt r)⁻¹ * Real.sqrt r) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 hr.1)), mul_one]
  rw [hs]
  congr 1
  dsimp only [IsComplexEnvironmentSemigroup.gradientDuhamelIntegrand]
  congr 1
  ring

/-- The fixed-interval operator on the actual weighted orbit equals the original time convolution. -/
theorem IsComplexEnvironmentSemigroup.weightedVolterra_actual
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) {T : ℝ}
    (f : Lp ℂ 2 (reducedLaw Q)) (t : Ioc (0 : ℝ) T) :
    hR.weightedVolterra T (hP.weightedGradientOrbit T f) t =
      Real.sqrt t.1 • (∫ s in (0 : ℝ)..t.1, hP.gradientDuhamelIntegrand hR f t.1 s) := by
  rw [hR.weightedVolterra_apply]
  calc
    _ = ∫ r in (0 : ℝ)..1,
        t.1 • (Real.sqrt t.1 • hP.gradientDuhamelIntegrand hR f t.1 (t.1*r)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne (1 : ℝ)] with r hr hr'
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr'
      exact integrand_on_actual_orbit hP hR f t ⟨hr'.1, lt_of_le_of_ne hr'.2 hr⟩
    _ = Real.sqrt t.1 • (t.1 • ∫ r in (0 : ℝ)..1,
        hP.gradientDuhamelIntegrand hR f t.1 (t.1*r)) := by
      rw [intervalIntegral.integral_smul, intervalIntegral.integral_smul, smul_comm]
    _ = _ := by rw [intervalIntegral.smul_integral_comp_mul_left, mul_zero, mul_one]

/-- The actual weighted gradient solves the bounded Volterra equation on the complete orbit space. -/
theorem IsComplexEnvironmentSemigroup.weightedGradientOrbit_eq
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (T : ℝ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    hP.weightedGradientOrbit T f = hR.weightedGradientOrbit T f +
      ζ • hR.weightedVolterra T (hP.weightedGradientOrbit T f) := by
  apply BoundedContinuousFunction.ext
  intro t
  change hP.weightedGradientOrbit T f t = hR.weightedGradientOrbit T f t +
    ζ • hR.weightedVolterra T (hP.weightedGradientOrbit T f) t
  rw [hP.weightedGradientOrbit_apply, hR.weightedGradientOrbit_apply,
    hP.weightedVolterra_actual hR f t]
  have ht : 0 < t.1.toNNReal := Real.toNNReal_pos.mpr t.2.1
  have he := hP.gradient_mild_duhamel hR f t.1.toNNReal ht
  rw [Real.coe_toNNReal _ t.2.1.le] at he
  rw [he, smul_add, smul_comm (Real.sqrt t.1) ζ]


/-- A short-time convergent force power series equals the actual weighted gradient orbit. -/
theorem IsComplexEnvironmentSemigroup.hasSum_weightedGradientOrbit
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (T : ℝ)
    (f : Lp ℂ 2 (reducedLaw Q))
    (hs : ‖ζ‖ * (4 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * Real.sqrt T) < 1) :
    HasSum (fun n : ℕ => ζ^n • ((hR.weightedVolterra T)^n) (hR.weightedGradientOrbit T f))
      (hP.weightedGradientOrbit T f) := by
  have hsmall : ‖ζ • hR.weightedVolterra T‖ < 1 := by
    exact (ContinuousLinearMap.opNorm_smul_le ζ _).trans_lt
      ((mul_le_mul_of_nonneg_left (hR.norm_weightedVolterra_le T) (norm_nonneg ζ)).trans_lt hs)
  exact hasSum_pow_smul_of_eq_add _ _ _ _ (hP.weightedGradientOrbit_eq hR T f) hsmall

/-- Any complete actual complex-force family has an operator-norm analytic weighted gradient at zero. -/
theorem analyticAt_weightedGradientOrbit
    {F : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z)) (T : ℝ) :
    AnalyticAt ℂ (fun z => (hF z).weightedGradientOrbit T) 0 := by
  apply analyticAt_clm_of_eq_add_comp_smul ((hF 0).weightedVolterra T)
    ((hF 0).weightedGradientOrbit T)
  intro z
  apply ContinuousLinearMap.ext
  intro f
  exact (hF z).weightedGradientOrbit_eq (hF 0) T f

end EinsteinFull
