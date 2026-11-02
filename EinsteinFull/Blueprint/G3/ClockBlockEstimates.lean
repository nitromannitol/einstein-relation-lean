import EinsteinFull.Work.W7.ClockFiniteRangeSupport

/-! Actual Gaussian clock blocks: integrability, normalization and boundary estimates.
These estimates assemble the adopted finite-range covariance and deterministic
Gaussian APIs without any new probabilistic or analytic input. -/

noncomputable section
namespace EinsteinFull.Blueprint.ClockBlocks
open EinsteinRelation MeasureTheory
open scoped ENNReal

variable {d : ℕ} {Λ R : ℝ}

/-- The literal, unrenormalized truncated Gaussian clock average. -/
def average (Q : EnvironmentLaw d Λ R) (r : ℝ) (T : Set (Vec d))
    (y : Vec d) (ω : FieldPair d) : ℝ :=
  ∫ z in T, anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
    centeredClockField Q (y - z) ω

/-- The source normalization is by the square root of cube volume. -/
def block (Q : EnvironmentLaw d Λ R) (r L : ℝ) (T : Set (Vec d))
    (x : Vec d) (f : Vec d → ℝ) (ω : FieldPair d) : ℝ :=
  L ^ (-(d : ℝ) / 2) * ∫ y in clockBlockCube x L, f y * average Q r T y ω

lemma gaussian_nonneg (Q : EnvironmentLaw d Λ R) (r : ℝ) (z : Vec d) :
    0 ≤ anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z := by
  unfold anisotropicGaussian
  positivity

lemma bounded_test_integrable {S : Set (Vec d)} (hS : MeasurableSet S)
    (hSf : volume S < ∞) {f : Vec d → ℝ} (hfm : Measurable f)
    {b : ℝ} (hb : 0 ≤ b) (hf : ∀ y ∈ S, |f y| ≤ b) :
    Integrable (S.indicator f) ∧ Integrable (fun y => (S.indicator f y) ^ 2) := by
  have hbound : ∀ᵐ y ∂(volume.restrict S), ‖f y‖ ≤ b := by
    filter_upwards [ae_restrict_mem hS] with y hy
    simpa only [Real.norm_eq_abs] using hf y hy
  have hi := (IntegrableOn.of_bound hSf hfm.aestronglyMeasurable.restrict b hbound).integrable_indicator hS
  refine ⟨hi, ?_⟩
  have hi2 : IntegrableOn (fun y => f y ^ 2) S volume := by
    apply IntegrableOn.of_bound hSf (hfm.pow_const 2).aestronglyMeasurable.restrict (b ^ 2)
    filter_upwards [ae_restrict_mem hS] with y hy
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hb).mpr (hf y hy)
  convert hi2.integrable_indicator hS using 1
  funext y
  by_cases hy : y ∈ S <;> simp [hy]

lemma integral_indicator_mul (S : Set (Vec d)) (hS : MeasurableSet S)
    (f g : Vec d → ℝ) :
    (∫ y, S.indicator f y * g y) = ∫ y in S, f y * g y := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by by_cases hy : y ∈ S <;> simp [hy]

lemma memLp_block (Q : EnvironmentLaw d Λ R) {r L : ℝ} (hr : 0 < r)
    {T : Set (Vec d)} (hT : MeasurableSet T) (x : Vec d) (hL : 0 ≤ L)
    {f : Vec d → ℝ} (hfm : Measurable f) {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ y ∈ clockBlockCube x L, |f y| ≤ b) :
    MemLp (block Q r L T x f) 2 (reducedLaw Q) := by
  let k := anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2)
  have hkm : Measurable k := (contDiff_anisotropicGaussian _ _).continuous.measurable
  letI := clockAveragingMeasure_probability
    (integrable_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) _ (sq_pos_of_pos hr))
    (gaussian_nonneg Q r)
    (integral_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) _ (sq_pos_of_pos hr))
  have hfi := (bounded_test_integrable (measurableSet_clockBlockCube x L)
    (by rw [volume_clockBlockCube x hL]; finiteness) hfm hb hf).1
  have h := memLp_clockTest_truncatedAverage Q (clockAveragingMeasure k) hT
    (hfm.indicator (measurableSet_clockBlockCube x L)) hfi
  simp_rw [truncatedClockAverage_eq_kernel Q hkm (gaussian_nonneg Q r) hT,
    integral_indicator_mul _ (measurableSet_clockBlockCube x L)] at h
  exact h.const_mul _

lemma normalized_power {L : ℝ} (hL : 0 < L) (k : ℕ) :
    (L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ k = L ^ ((k : ℝ) - d) := by
  rw [← Real.rpow_natCast (L ^ (-(d : ℝ) / 2)) 2,
    ← Real.rpow_mul hL.le, ← Real.rpow_natCast L k, ← Real.rpow_add hL]
  congr 1
  norm_num
  ring

lemma normalized_volume {L : ℝ} (hL : 0 < L) :
    (L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ d = 1 := by
  rw [normalized_power hL, sub_self, Real.rpow_zero]

lemma normalized_surface {L : ℝ} (hL : 0 < L) (hd : 1 ≤ d) :
    (L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ (d - 1) = L ^ (-1 : ℝ) := by
  rw [normalized_power hL, Nat.cast_sub hd]
  congr 1
  push_cast
  ring

lemma variance_block_le (Q : EnvironmentLaw d Λ R) {r L : ℝ} (hr : 0 < r)
    {T : Set (Vec d)} (hT : MeasurableSet T) (x : Vec d) (hL : 0 < L)
    {f : Vec d → ℝ} (hfm : Measurable f) {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ y ∈ clockBlockCube x L, |f y| ≤ b) :
    (∫ ω, (block Q r L T x f ω) ^ 2 ∂reducedLaw Q) ≤
      clockVarianceConstant d Λ R * b ^ 2 := by
  have h := clockCube_anisotropicGaussian_variance_le Q _
    (posDef_homogenizedCoefficient Q) _ (sq_pos_of_pos hr) hT x hL.le hfm hb hf
  simp only [block, mul_pow, integral_const_mul]
  apply (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq
  rw [show (L ^ (-(d : ℝ) / 2)) ^ 2 *
    (clockVarianceConstant d Λ R * b ^ 2 * L ^ d) =
      (clockVarianceConstant d Λ R * b ^ 2) *
        ((L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ d) by ring,
    normalized_volume hL, mul_one]

lemma variance_boundary_le (Q : EnvironmentLaw d Λ R) {r L w : ℝ} (hr : 0 < r)
    {T : Set (Vec d)} (hT : MeasurableSet T) (x : Vec d) (hw : 0 ≤ w) (hwL : w ≤ L)
    (hL : 0 < L) (hd : 1 ≤ d) {f : Vec d → ℝ} (hfm : Measurable f)
    {b : ℝ} (hb : 0 ≤ b) (hf : ∀ y ∈ clockBlockCube x L, |f y| ≤ b)
    (hf0 : ∀ y ∈ clockBlockCube x (L - w), f y = 0) :
    (∫ ω, (block Q r L T x f ω) ^ 2 ∂reducedLaw Q) ≤
      clockVarianceConstant d Λ R * b ^ 2 * d * L ^ (-1 : ℝ) * w := by
  have he (ω : FieldPair d) :
      (∫ y in clockBlockCube x L, f y * average Q r T y ω) =
      ∫ y in clockBlockCube x L \ clockBlockCube x (L - w), f y * average Q r T y ω := by
    rw [← integral_indicator (measurableSet_clockBlockCube x L),
      ← integral_indicator ((measurableSet_clockBlockCube x L).diff
        (measurableSet_clockBlockCube x (L - w)))]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      by_cases hy : y ∈ clockBlockCube x (L - w)
      · simp [hy, hf0 y hy]
      · by_cases hx : y ∈ clockBlockCube x L <;> simp [hx, hy]
  have h := clockCube_strip_anisotropicGaussian_variance_le Q _
    (posDef_homogenizedCoefficient Q) _ (sq_pos_of_pos hr) hT x hw hwL hfm hb
    (fun y hy => hf y hy.1)
  simp only [block, he, mul_pow, integral_const_mul]
  apply (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq
  calc
    _ = clockVarianceConstant d Λ R * b ^ 2 * d *
      ((L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ (d - 1)) * w := by ring
    _ = _ := by rw [normalized_surface hL hd]

lemma smoothing_L2 (Q : EnvironmentLaw d Λ R) {r L : ℝ} (hr : 0 < r)
    (x : Vec d) (hL : 0 ≤ L) {f : Vec d → ℝ} (hfm : Measurable f)
    {b : ℝ} (hb : 0 ≤ b) (hf : ∀ y ∈ clockBlockCube x L, |f y| ≤ b) :
    MemLp (fun y => ∫ z : Vec d,
      anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
        (clockBlockCube x L).indicator f (y + z)) 2 volume ∧
    (∫ y : Vec d, (∫ z : Vec d,
      anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
        (clockBlockCube x L).indicator f (y + z)) ^ 2) ≤
      ∫ y in clockBlockCube x L, (f y) ^ 2 := by
  let k := anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2)
  have hkm : Measurable k := (contDiff_anisotropicGaussian _ _).continuous.measurable
  letI := clockAveragingMeasure_probability
    (integrable_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) _ (sq_pos_of_pos hr))
    (gaussian_nonneg Q r)
    (integral_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) _ (sq_pos_of_pos hr))
  have hfi := (bounded_test_integrable (measurableSet_clockBlockCube x L)
    (by rw [volume_clockBlockCube x hL]; finiteness) hfm hb hf).2
  have h := truncatedClockTestFunction_L2 (clockAveragingMeasure k)
    MeasurableSet.univ (hfm.indicator (measurableSet_clockBlockCube x L)) hfi
  have he : truncatedClockTestFunction (clockAveragingMeasure k) Set.univ
      ((clockBlockCube x L).indicator f) = fun y => ∫ z, k z *
        (clockBlockCube x L).indicator f (y + z) := by
    funext y
    rw [truncatedClockTestFunction_eq_kernel hkm (gaussian_nonneg Q r)
      MeasurableSet.univ, Measure.restrict_univ]
  rw [he] at h
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [← integral_indicator (measurableSet_clockBlockCube x L)]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    by_cases hy : y ∈ clockBlockCube x L <;> simp [hy]

lemma smoothing_error_memLp (Q : EnvironmentLaw d Λ R) {r L : ℝ} (hr : 0 < r)
    (x : Vec d) (hL : 0 ≤ L) :
    MemLp (fun y => (∫ z : Vec d,
      anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
        (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) (y + z)) -
          (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) y) 2 volume := by
  have h := (smoothing_L2 Q hr x hL (f := fun _ => (1 : ℝ)) measurable_const (b := 1) (by norm_num)
    (fun _ _ => by norm_num)).1
  have hi := memLp_indicator_const 2 (measurableSet_clockBlockCube x L) (1 : ℝ)
    (Or.inr (by rw [volume_clockBlockCube x hL]; finiteness))
  exact h.sub hi

lemma measurable_average (Q : EnvironmentLaw d Λ R) (r : ℝ)
    {T : Set (Vec d)} (hT : MeasurableSet T) :
    Measurable (fun p : Vec d × FieldPair d => average Q r T p.1 p.2) := by
  have hF : Measurable (fun p : (Vec d × FieldPair d) × Vec d =>
      T.indicator (fun z => anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
        centeredClockField Q (p.1.1 - z) p.1.2) p.2) := by
    convert (((contDiff_anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2)).continuous.measurable.comp measurable_snd).mul
      ((continuous_centeredClockField Q).measurable.comp
        ((measurable_fst.fst.sub measurable_snd).prodMk measurable_fst.snd))).indicator
          (measurable_snd hT) using 1
    funext p
    by_cases hp : p.2 ∈ T <;> simp [hp]
  convert (hF.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Vec d)))).measurable using 1
  funext p
  unfold average
  rw [← integral_indicator hT]

lemma average_bound (Q : EnvironmentLaw d Λ R) {r : ℝ} (hr : 0 < r)
    {T : Set (Vec d)} (hT : MeasurableSet T) {ω : FieldPair d}
    (hω : ∀ y, |centeredClockField Q y ω| ≤ 2 * sourceReducedBound Λ)
    (y : Vec d) : ‖average Q r T y ω‖ ≤ 2 * sourceReducedBound Λ := by
  let k := anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2)
  have hkm : Measurable k := (contDiff_anisotropicGaussian _ _).continuous.measurable
  letI := clockAveragingMeasure_probability
    (integrable_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) _ (sq_pos_of_pos hr))
    (gaussian_nonneg Q r)
    (integral_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) _ (sq_pos_of_pos hr))
  have hM : 0 ≤ 2 * sourceReducedBound Λ := (abs_nonneg _).trans (hω 0)
  change ‖∫ z in T, k z * centeredClockField Q (y - z) ω‖ ≤ _
  rw [← truncatedClockAverage_eq_kernel Q hkm (gaussian_nonneg Q r) hT]
  change ‖∫ z, T.indicator (fun z => centeredClockField Q (y - z) ω) z
    ∂clockAveragingMeasure k‖ ≤ _
  have hb : ∀ᵐ z ∂clockAveragingMeasure k,
      ‖T.indicator (fun z => centeredClockField Q (y - z) ω) z‖ ≤
        2 * sourceReducedBound Λ := ae_of_all _ fun z => by
    by_cases hz : z ∈ T
    · simpa [hz, Real.norm_eq_abs] using hω (y - z)
    · simpa [hz] using hM
  simpa using norm_integral_le_of_norm_le_const hb

lemma integrableOn_average (Q : EnvironmentLaw d Λ R) {r L : ℝ} (hr : 0 < r)
    {T : Set (Vec d)} (hT : MeasurableSet T) {ω : FieldPair d}
    (hω : ∀ y, |centeredClockField Q y ω| ≤ 2 * sourceReducedBound Λ)
    (x : Vec d) (hL : 0 ≤ L) :
    IntegrableOn (fun y => average Q r T y ω) (clockBlockCube x L) volume := by
  apply IntegrableOn.of_bound (by rw [volume_clockBlockCube x hL]; finiteness)
    ((measurable_average Q r hT).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable.restrict
    (2 * sourceReducedBound Λ)
  exact ae_of_all _ (average_bound Q hr hT hω)

lemma normalized_difference_variance (Q : EnvironmentLaw d Λ R) {r t L : ℝ}
    (hr : 0 < r) (ht : 0 < t) (x : Vec d) (hL : 0 < L) (hd : 1 ≤ d) :
    (∫ ω, (block Q r L Set.univ x (fun _ => 1) ω -
      block Q t L Set.univ x (fun _ => 1) ω) ^ 2 ∂reducedLaw Q) ≤
      8 * clockVarianceConstant d Λ R * (d : ℝ) ^ 2 *
        Real.sqrt (sourceReducedBound Λ) * L ^ (-1 : ℝ) * (r + t) := by
  have h := clockCube_homogenizedGaussian_scaleChange_variance_le Q hr ht x hL.le
  simp only [block, average, Measure.restrict_univ, one_mul, ← mul_sub,
    mul_pow, integral_const_mul]
  apply (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq
  calc
    _ = 8 * clockVarianceConstant d Λ R * (d : ℝ) ^ 2 *
      Real.sqrt (sourceReducedBound Λ) *
        ((L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ (d - 1)) * (r + t) := by ring
    _ = _ := by rw [normalized_surface hL hd]

lemma normalized_truncation_variance (Q : EnvironmentLaw d Λ R) {r L δ : ℝ}
    (hr : 0 < r) (x : Vec d) (hL : 0 < L) {E p : ℝ}
    (hb : (∫ ω, (∫ y in clockBlockCube x L,
      ((∫ z : Vec d, anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
        centeredClockField Q (y - z) ω) -
        ∫ z in {z : Vec d | euclideanNorm z < r ^ (1 + δ)},
          anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
            centeredClockField Q (y - z) ω)) ^ 2 ∂reducedLaw Q) ≤
      (E * L ^ d * r ^ (-p)) ^ 2) :
    (∫ ω, (block Q r L Set.univ x (fun _ => 1) ω -
      block Q r L {z : Vec d | euclideanNorm z < r ^ (1 + δ)} x
        (fun _ => 1) ω) ^ 2 ∂reducedLaw Q) ≤
      E ^ 2 * L ^ d * (r ^ (-p)) ^ 2 := by
  have hT : MeasurableSet {z : Vec d | euclideanNorm z < r ^ (1 + δ)} := by
    apply measurableSet_lt _ measurable_const
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have he : (fun ω => block Q r L Set.univ x (fun _ => 1) ω -
      block Q r L {z : Vec d | euclideanNorm z < r ^ (1 + δ)} x (fun _ => 1) ω) =ᵐ[reducedLaw Q]
      fun ω => L ^ (-(d : ℝ) / 2) * ∫ y in clockBlockCube x L,
        ((∫ z : Vec d, anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
          centeredClockField Q (y - z) ω) -
          ∫ z in {z : Vec d | euclideanNorm z < r ^ (1 + δ)},
            anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
              centeredClockField Q (y - z) ω) := by
    filter_upwards [ae_forall_abs_centeredClockField_le Q] with ω hω
    have hu := integrableOn_average Q hr MeasurableSet.univ hω x hL.le
    have ht := integrableOn_average Q hr hT hω x hL.le
    simp only [block, one_mul, ← mul_sub]
    rw [← integral_sub hu ht]
    simp only [average, Measure.restrict_univ]
  rw [integral_congr_ae (he.mono fun _ h => congrArg (fun a : ℝ => a ^ 2) h)]
  simp only [mul_pow, integral_const_mul]
  apply (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans_eq
  calc
    _ = E ^ 2 * ((L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ d) * L ^ d * (r ^ (-p)) ^ 2 := by ring
    _ = _ := by rw [normalized_volume hL, mul_one]

/-- A deterministic three-piece comparison in an actual L2 space. -/
lemma variance_three_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X Y U V : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) :
    (∫ ω, (X ω - Y ω) ^ 2 ∂μ) ≤
      3 * (∫ ω, (U ω - X ω) ^ 2 ∂μ) +
      3 * (∫ ω, (U ω - V ω) ^ 2 ∂μ) +
      3 * (∫ ω, (V ω - Y ω) ^ 2 ∂μ) := by
  have h1 := (hU.sub hX).integrable_sq
  have h2 := (hU.sub hV).integrable_sq
  have h3 := (hV.sub hY).integrable_sq
  change Integrable (fun ω => (U ω - X ω) ^ 2) μ at h1
  change Integrable (fun ω => (U ω - V ω) ^ 2) μ at h2
  change Integrable (fun ω => (V ω - Y ω) ^ 2) μ at h3
  have h12 : Integrable (fun ω => 3 * (U ω - X ω) ^ 2 + 3 * (U ω - V ω) ^ 2) μ :=
    (h1.const_mul 3).add (h2.const_mul 3)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (h1.const_mul 3) (h2.const_mul 3),
    ← integral_add h12 (h3.const_mul 3)]
  apply integral_mono (hX.sub hY).integrable_sq
    (((h1.const_mul 3).add (h2.const_mul 3)).add (h3.const_mul 3))
  intro ω
  dsimp only [Pi.add_apply, Pi.sub_apply]
  nlinarith [sq_nonneg (2 * U ω - X ω - V ω),
    sq_nonneg (U ω - X ω + V ω - Y ω),
    sq_nonneg (U ω - 2 * V ω + Y ω)]

/-- A structural inverse power beats the normalized block volume uniformly
throughout the allowed smoothing-scale interval. -/
lemma truncation_power_le {L r η β : ℝ} (hL : 1 ≤ L) (hη : 0 < η)
    (hβ : 0 ≤ β) (hr : L ^ η ≤ r) :
    L ^ d * (r ^ (-((d : ℝ) + 1) / η)) ^ 2 ≤ L ^ (β - 1) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hrp : 0 < r := (Real.rpow_pos_of_pos hLp η).trans_le hr
  have he : η * (-((d : ℝ) + 1) / η * 2) = -2 * ((d : ℝ) + 1) := by
    field_simp
  calc
    _ = L ^ d * r ^ (-((d : ℝ) + 1) / η * 2) := by
      rw [← Real.rpow_natCast (r ^ (-((d : ℝ) + 1) / η)) 2,
        ← Real.rpow_mul hrp.le]
      norm_num
    _ ≤ L ^ d * (L ^ η) ^ (-((d : ℝ) + 1) / η * 2) := by
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hLp η) hr ?_)
        (pow_nonneg hLp.le _)
      exact mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) d]) hη.le) (by norm_num)
    _ = L ^ (-(d : ℝ) - 2) := by
      rw [← Real.rpow_mul hLp.le, he, ← Real.rpow_natCast L d, ← Real.rpow_add hLp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith [Nat.cast_nonneg (α := ℝ) d])

lemma surface_power {L β : ℝ} (hL : 0 < L) :
    L ^ (-1 : ℝ) * L ^ β = (L ^ (-(1 - β) / 2)) ^ 2 := by
  rw [← Real.rpow_add hL, ← Real.rpow_natCast (L ^ (-(1 - β) / 2)) 2,
    ← Real.rpow_mul hL.le]
  congr 1
  norm_num
  ring

end EinsteinFull.Blueprint.ClockBlocks
