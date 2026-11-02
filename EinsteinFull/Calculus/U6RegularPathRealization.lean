import EinsteinFull.Calculus.U2GMPRegularRealization
import EinsteinFull.Calculus.U8RegularKernelMoments
import EinsteinFull.Calculus.U2GMPHeatDensity

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal Topology BigOperators

noncomputable section
namespace EinsteinFull
open Blueprint

/-- A clipped Euclidean fourth-moment bound transfers to the exhaustion metric
on the one-point compactification of the actual regular resolvent. -/
theorem u6_regular_onePoint_localMoments_of_euclidean_fourth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ (x : Vec d) (h : ℝ≥0), (h : ℝ) ≤ 1 →
      (∫⁻ y, ENNReal.ofReal (min (euclideanNorm (y - x) ^ 4) 1) ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω h x)) ≤
          ENNReal.ofReal (C * (h : ℝ) ^ 2)) :
    letI := OnePoint.exhaustionMetricSpace (gmpPhysicalExhaustion (d := d))
      gmpPhysicalExhaustion_continuous gmpPhysicalExhaustion_pos
      gmpPhysicalExhaustion_lipschitz gmpPhysicalExhaustion_superlevel_compact
    ∃ M : ℝ≥0, (u2RegularPositiveC0Resolvent hd ω lam Λ hΛ hω).onePointKernelSemigroup.HasLocalKolmogorovMoments 4 2 M 16 := by
  let := OnePoint.exhaustionMetricSpace (gmpPhysicalExhaustion (d := d))
    gmpPhysicalExhaustion_continuous gmpPhysicalExhaustion_pos
    gmpPhysicalExhaustion_lipschitz gmpPhysicalExhaustion_superlevel_compact
  refine ⟨Real.toNNReal (16 * C), by norm_num, by norm_num, ?_, ?_⟩
  · intro h hh z
    have hh' : (h : ℝ) ≤ 1 := by exact_mod_cast hh
    have hrhs : ((Real.toNNReal (16 * C) : ℝ≥0) : ℝ≥0∞) * (h : ℝ≥0∞) ^ (2 : ℝ) =
        16 * ENNReal.ofReal (C * (h : ℝ) ^ 2) := by
      rw [ENNReal.rpow_two, ENNReal.ofReal_mul hC, ENNReal.ofReal_pow h.coe_nonneg,
        ENNReal.ofReal_coe_nnreal, ← mul_assoc]
      congr 1
      rw [show ((Real.toNNReal (16 * C) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (16 * C) from rfl,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [hrhs]
    induction z using OnePoint.rec with
    | infty =>
        rw [(u2RegularPositiveC0Resolvent hd ω lam Λ hΛ hω).onePointKernelSemigroup_absorbing,
          lintegral_dirac]
        simp
    | coe x =>
        have hlaw : (u2RegularPositiveC0Resolvent hd ω lam Λ hΛ hω).onePointKernelSemigroup h
            (x : OnePoint (Vec d)) =
            (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω h x).map
              ((↑) : Vec d → OnePoint (Vec d)) := by
          rw [(u2RegularPositiveC0Resolvent hd ω lam Λ hΛ hω).onePointKernelSemigroup_apply_coe h x]
          change _ + (1 - (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω h x) Set.univ) • _ = _
          rw [u2_regular_kernel_conservative hd ω lam Λ hΛ hω h x, tsub_self,
            zero_smul, add_zero]
          rfl
        have hmeas : Measurable fun z : OnePoint (Vec d) => edist z (x : OnePoint (Vec d)) ^ (4 : ℝ) :=
          (measurable_edist_left (x := (x : OnePoint (Vec d)))).pow_const 4
        rw [hlaw, lintegral_map hmeas OnePoint.continuous_coe.measurable]
        calc
          (∫⁻ y, edist (y : OnePoint (Vec d)) (x : OnePoint (Vec d)) ^ (4 : ℝ) ∂
              (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω h x)) ≤
              ∫⁻ y, 16 * ENNReal.ofReal (min (euclideanNorm (y - x) ^ 4) 1) ∂
                (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω h x) := by
            refine lintegral_mono fun y => ?_
            have hb := gmpPhysicalExhaustion_live_euclidean_fourth_le x y
            rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num),
              show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            calc
              ENNReal.ofReal (dist (y : OnePoint (Vec d)) (x : OnePoint (Vec d)) ^ 4) ≤
                  ENNReal.ofReal (16 * min (euclideanNorm (y - x) ^ 4) 1) :=
                ENNReal.ofReal_le_ofReal hb
              _ = 16 * ENNReal.ofReal (min (euclideanNorm (y - x) ^ 4) 1) := by
                rw [ENNReal.ofReal_mul (by norm_num)]
                norm_num
          _ = 16 * ∫⁻ y, ENNReal.ofReal (min (euclideanNorm (y - x) ^ 4) 1) ∂
                (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω h x) :=
            lintegral_const_mul' _ _ (by norm_num)
          _ ≤ 16 * ENNReal.ofReal (C * (h : ℝ) ^ 2) := by
            gcongr
            exact hm x h hh'
  · intro y z
    have hdist : edist z y ≤ 2 := by
      rw [edist_dist]
      calc ENNReal.ofReal (dist z y) ≤ ENNReal.ofReal 2 :=
            ENNReal.ofReal_le_ofReal (gmpPhysicalExhaustion_dist_le_two z y)
        _ = 2 := by
            rw [show (2 : ℝ) = ((2 : ℝ≥0) : ℝ) by norm_num, ENNReal.ofReal_coe_nnreal]
            rfl
    calc edist z y ^ (4 : ℝ) ≤ (2 : ℝ≥0∞) ^ (4 : ℝ) :=
          ENNReal.rpow_le_rpow hdist (by norm_num)
      _ = 16 := by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
          norm_num
      _ = ((16 : ℝ≥0) : ℝ≥0∞) := by norm_num

/-- A clipped Euclidean fourth-moment estimate for the regular semigroup
produces a measurable continuous-path law with its actual finite-dimensional
marginals, simultaneously for all starting points. -/
theorem u6_regular_continuous_kernel_of_euclidean_fourth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ (x : Vec d) (h : ℝ≥0), (h : ℝ) ≤ 1 →
      (∫⁻ y, ENNReal.ofReal (min (euclideanNorm (y - x) ^ 4) 1) ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω h x)) ≤
          ENNReal.ofReal (C * (h : ℝ) ^ 2)) :
    ∃ K : Kernel (Vec d) (Path d), IsMarkovKernel K ∧
      ∀ I : Finset ℝ≥0,
        K.map (ContinuousPath.finsetEvaluation I) =
          finiteSetKernel (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I := by
  let hreg : (u2RegularPositiveC0Resolvent hd ω lam Λ hΛ hω).OnePointRegular := {
    rho := gmpPhysicalExhaustion
    continuous_rho := gmpPhysicalExhaustion_continuous
    rho_pos := gmpPhysicalExhaustion_pos
    lipschitz_rho := gmpPhysicalExhaustion_lipschitz
    isCompact_superlevel := gmpPhysicalExhaustion_superlevel_compact
    kolmogorovRegular := by
      let := OnePoint.exhaustionMetricSpace (gmpPhysicalExhaustion (d := d))
        gmpPhysicalExhaustion_continuous gmpPhysicalExhaustion_pos
        gmpPhysicalExhaustion_lipschitz gmpPhysicalExhaustion_superlevel_compact
      let : CompleteSpace (OnePoint (Vec d)) :=
        completeSpace_of_isComplete_univ isCompact_univ.isComplete
      obtain ⟨M, hM⟩ :=
        u6_regular_onePoint_localMoments_of_euclidean_fourth hd ω lam Λ hΛ hω C hC hm
      exact SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
        (u2RegularPositiveC0Resolvent hd ω lam Λ hΛ hω).isConservative_onePointKernelSemigroup
        (hM.toHasKolmogorovMoments
          (u2RegularPositiveC0Resolvent hd ω lam Λ hΛ hω).isConservative_onePointKernelSemigroup)
  }
  exact (gmpExistsUnique_livePath_of_onePointRegular hreg
    (u2_regular_kernel_conservative hd ω lam Λ hΛ hω)).exists

/-- Coordinate fourth bounds yield a local Euclidean fourth bound. -/
theorem u6_regular_euclideanFourth_of_coordinate_local
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hcoord : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      (t : ℝ) ≤ δ →
      Integrable (fun y => (y k - x k) ^ 4)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (y k - x k) ^ 4 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        C * (t : ℝ) ^ 2) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (t : ℝ≥0), (t : ℝ) ≤ δ →
      Integrable (fun y => (∑ k : Fin d, (y k - x k) ^ 2) ^ 2)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (∑ k : Fin d, (y k - x k) ^ 2) ^ 2 ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤ C * (t : ℝ) ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hm⟩ :=
    hcoord
  refine ⟨(d : ℝ) ^ 2 * C, δ, by positivity, hδ, ?_⟩
  intro x t ht
  let μ := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  have hi (k : Fin d) : Integrable (fun y => (y k - x k) ^ 4) μ := (hm x k t ht).1
  have hsum : Integrable (fun y => ∑ k : Fin d, (y k - x k) ^ 4) μ :=
    integrable_finsetSum _ (fun k _ => hi k)
  have hcont : Continuous (fun y : Vec d => (∑ k : Fin d, (y k - x k) ^ 2) ^ 2) := by fun_prop
  have hdom : Integrable (fun y => (d : ℝ) * ∑ k : Fin d, (y k - x k) ^ 4) μ :=
    hsum.const_mul (d : ℝ)
  have htarget : Integrable (fun y => (∑ k : Fin d, (y k - x k) ^ 2) ^ 2) μ :=
    hdom.mono_nonneg hcont.aestronglyMeasurable (ae_of_all _ (fun y => sq_nonneg _))
      (ae_of_all _ (gmpPhysical_sum_coordinateSquares_sq_le x))
  refine ⟨htarget, ?_⟩
  have h := integral_mono htarget hdom (gmpPhysical_sum_coordinateSquares_sq_le x)
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => hi k)] at h
  have hsumle : (∑ k : Fin d, ∫ y, (y k - x k) ^ 4 ∂μ) ≤
      (d : ℝ) * (C * (t : ℝ) ^ 2) := by
    calc
      _ ≤ ∑ _k : Fin d, C * (t : ℝ) ^ 2 := Finset.sum_le_sum (fun k _ => (hm x k t ht).2)
      _ = _ := by simp
  have hh := mul_le_mul_of_nonneg_left hsumle (show (0 : ℝ) ≤ d by positivity)
  nlinarith [h, hh]


/-- Translate the coordinate bound to the explicit Euclidean norm. -/
theorem u6_regular_euclideanNormFourth_of_coordinate_local
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hcoord : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      (t : ℝ) ≤ δ →
      Integrable (fun y => (y k - x k) ^ 4)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (y k - x k) ^ 4 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        C * (t : ℝ) ^ 2) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (t : ℝ≥0), (t : ℝ) ≤ δ →
      Integrable (fun y => euclideanNorm (y - x) ^ 4)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, euclideanNorm (y - x) ^ 4 ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤ C * (t : ℝ) ^ 2 := by
  have heq (x y : Vec d) : euclideanNorm (y - x) ^ 4 =
      (∑ k : Fin d, (y k - x k) ^ 2) ^ 2 := by
    have hs : euclideanNorm (y - x) ^ 2 = ∑ k : Fin d, (y k - x k) ^ 2 := by
      unfold euclideanNorm euclideanSq dot
      rw [Real.sq_sqrt]
      · simp only [Pi.sub_apply, pow_two]
      · exact Finset.sum_nonneg (fun k _ => mul_self_nonneg _)
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hs]
  obtain ⟨C, δ, hC, hδ, hm⟩ :=
    u6_regular_euclideanFourth_of_coordinate_local hd ω lam Λ hΛ hω hcoord
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro x t ht
  simpa only [heq] using hm x t ht


/-- A local coordinate bound controls clipped Euclidean displacement for unit times. -/
theorem u6_regular_clippedFourth_of_coordinate_local
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hcoord : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      (t : ℝ) ≤ δ →
      Integrable (fun y => (y k - x k) ^ 4)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (y k - x k) ^ 4 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        C * (t : ℝ) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec d) (t : ℝ≥0), (t : ℝ) ≤ 1 →
      Integrable (fun y => min (euclideanNorm (y - x) ^ 4) 1)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, min (euclideanNorm (y - x) ^ 4) 1 ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤ C * (t : ℝ) ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hm⟩ :=
    u6_regular_euclideanNormFourth_of_coordinate_local hd ω lam Λ hΛ hω hcoord
  refine ⟨C + (δ ^ 2)⁻¹, by positivity, ?_⟩
  intro x t _ht
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let μ := P t x
  letI : IsProbabilityMeasure μ := ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
  have hcont : Continuous (fun y : Vec d => min (euclideanNorm (y - x) ^ 4) 1) := by
    have he : Continuous (fun y : Vec d => euclideanNorm (y - x)) := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    exact (he.pow 4).min continuous_const
  have h0 (y : Vec d) : 0 ≤ min (euclideanNorm (y - x) ^ 4) 1 :=
    le_min (by positivity) (by norm_num)
  have hbound (y : Vec d) : min (euclideanNorm (y - x) ^ 4) 1 ≤ 1 := min_le_right _ _
  have hi : Integrable (fun y => min (euclideanNorm (y - x) ^ 4) 1) μ :=
    (integrable_const (1 : ℝ)).mono_nonneg hcont.aestronglyMeasurable
      (ae_of_all _ h0) (ae_of_all _ hbound)
  refine ⟨hi, ?_⟩
  by_cases hsmall : (t : ℝ) ≤ δ
  · have h := integral_mono hi (hm x t hsmall).1 (fun y => min_le_left _ _)
    have hh := (hm x t hsmall).2
    have hpos : 0 ≤ (δ ^ 2)⁻¹ * (t : ℝ) ^ 2 := by positivity
    nlinarith
  · have hb := integral_mono hi (integrable_const (1 : ℝ)) hbound
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hb
    have hδt : δ ≤ (t : ℝ) := le_of_not_ge hsmall
    have hs : δ ^ 2 ≤ (t : ℝ) ^ 2 := by nlinarith [t.coe_nonneg]
    have hδsq : 0 < δ ^ 2 := by positivity
    have hinv : 1 ≤ (δ ^ 2)⁻¹ * (t : ℝ) ^ 2 := by
      rw [inv_mul_eq_div, one_le_div hδsq]
      exact hs
    have hp : 0 ≤ C * (t : ℝ) ^ 2 := by positivity
    nlinarith


/-- Extended nonnegative form of the clipped fourth-moment estimate. -/
theorem u6_regular_clippedFourth_lintegral_of_coordinate_local
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hcoord : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      (t : ℝ) ≤ δ →
      Integrable (fun y => (y k - x k) ^ 4)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (y k - x k) ^ 4 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        C * (t : ℝ) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec d) (t : ℝ≥0), (t : ℝ) ≤ 1 →
      (∫⁻ y, ENNReal.ofReal (min (euclideanNorm (y - x) ^ 4) 1) ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
          ENNReal.ofReal (C * (t : ℝ) ^ 2) := by
  obtain ⟨C, hC, hm⟩ :=
    u6_regular_clippedFourth_of_coordinate_local hd ω lam Λ hΛ hω hcoord
  refine ⟨C, hC, ?_⟩
  intro x t ht
  rw [← ofReal_integral_eq_lintegral_ofReal (hm x t ht).1
    (ae_of_all _ (fun y => le_min (by positivity) (by norm_num)))]
  exact ENNReal.ofReal_le_ofReal (hm x t ht).2

/-- Local coordinate fourth moments yield the continuous-path realization
of the actual regular semigroup. -/
theorem u6_regular_continuous_kernel_of_coordinate_fourth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hcoord : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      (t : ℝ) ≤ δ →
      Integrable (fun y => (y k - x k) ^ 4)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (y k - x k) ^ 4 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        C * (t : ℝ) ^ 2) :
    ∃ K : Kernel (Vec d) (Path d), IsMarkovKernel K ∧
      ∀ I : Finset ℝ≥0,
        K.map (ContinuousPath.finsetEvaluation I) =
          finiteSetKernel (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I := by
  obtain ⟨C, hC, hm⟩ :=
    u6_regular_clippedFourth_lintegral_of_coordinate_local hd ω lam Λ hΛ hω hcoord
  exact u6_regular_continuous_kernel_of_euclidean_fourth hd ω lam Λ hΛ hω C hC hm

/-- The regular fourth-cutoff generator obeys a common almost-everywhere growth bound. -/
theorem u6_regular_squaredSquareCutoff_generator_ae_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, ∀ (z : Vec d) (k : Fin d) (a : ℝ), 0 < a →
      let f := gmpPhysicalCoordinateMomentCutoff z k 1 a
      |physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => (f y) ^ 2) x| ≤
        A * (x k - z k) ^ 2 + B * (f x) ^ 2 := by
  obtain ⟨D, hD, hderiv⟩ := gmpPhysical_squaredSquareCutoff_derivative_bounds (d := d)
  obtain ⟨C₁, C₂, hC₁, hC₂, hg⟩ :=
    u2_regular_generator_ae_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω
  refine ⟨C₁ * D + C₂ * (2 * D + 2 * D ^ 2), C₁ * D, by positivity, by positivity, ?_⟩
  filter_upwards [(gmpPhysical_ae_iff_volume hd ω lam _).mpr hg] with x hx
  intro z k a ha
  let f := gmpPhysicalCoordinateMomentCutoff z k 1 a
  let q : ℝ := x k - z k
  have hs : ContDiff ℝ 2 (fun y => (f y) ^ 2) :=
    ((gmpPhysical_coordinateMomentCutoff_properties z k 1 a ha).1.pow 2).of_le (by simp)
  have hfirst (i : Fin d) :
      |fderiv ℝ (fun y => (f y) ^ 2) x (unitVector i)| ≤ D * (q ^ 2 + (f x) ^ 2) := by
    have h := (hderiv z x k i i a ha).1
    have hq : |q| ^ 2 = q ^ 2 := sq_abs q
    nlinarith [sq_nonneg (|q| - f x), mul_nonneg hD (sq_nonneg (|q| - f x))]
  have hsecond (i j : Fin d) :
      |fderiv ℝ (fun y => fderiv ℝ (fun v => (f v) ^ 2) y (unitVector j)) x (unitVector i)| ≤
        (2 * D + 2 * D ^ 2) * q ^ 2 := (hderiv z x k i j a ha).2
  have h := hx _ hs (D * (q ^ 2 + (f x) ^ 2)) ((2 * D + 2 * D ^ 2) * q ^ 2)
    (by positivity) (by positivity) hfirst hsecond
  convert h using 1 <;> dsimp [q] <;> ring

/-- Positive-time absolute continuity and square-moment integrability transfer the
fourth-cutoff generator bound to every starting point. -/
theorem u6_regular_squaredSquareCutoff_generator_integral_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
        physicalReversibleMeasure ω hd lam)
    (hsecond : ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0), 0 < t →
      Integrable (fun y => (y k - x k) ^ 2)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0, 0 < t →
      let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
      (∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam (fun v => (f v) ^ 2) y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      A * (∫ y, (y k - x k) ^ 2 ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) +
      B * (∫ y, (f y) ^ 2 ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) := by
  obtain ⟨A, B, hA, hB, hgen⟩ :=
    u6_regular_squaredSquareCutoff_generator_ae_bound hd ω lam Λ hΛ hω
  refine ⟨A, B, hA, hB, ?_⟩
  intro x k a ha t ht
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let μ := P t x
  let : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
  have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  have hfs : ContDiff ℝ (⊤ : ℕ∞) (fun y => (f y) ^ 2) := hp.1.pow 2
  have hfc : HasCompactSupport (fun y => (f y) ^ 2) := by
    have hh : HasCompactSupport (fun y => f y * f y) := hp.2.1.mul_right
    simpa only [pow_two] using hh
  have hf : Integrable (fun y => (f y) ^ 2) μ :=
    hfs.continuous.integrable_of_hasCompactSupport hfc
  obtain ⟨D, _, hgD⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hfs hfc
  have hg : Integrable (physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => (f y) ^ 2)) μ :=
    Integrable.of_bound
      (measurable_physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => (f y) ^ 2)).aestronglyMeasurable D
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hgD y)
  have hq := hsecond x k t ht
  have hh : Integrable (fun y => A * (y k - x k) ^ 2 + B * (f y) ^ 2) μ :=
    (hq.const_mul A).add (hf.const_mul B)
  have hae : ∀ᵐ y ∂μ, physicalGenerator (firstCoordinateIndex hd) ω lam (fun v => (f v) ^ 2) y ≤
      A * (y k - x k) ^ 2 + B * (f y) ^ 2 := by
    filter_upwards [(hac t ht x).ae_le hgen] with y hy
    exact (abs_le.mp (hy x k a ha)).2
  have h := integral_mono_ae hg hh hae
  rw [integral_add (hq.const_mul A) (hf.const_mul B), integral_const_mul, integral_const_mul] at h
  exact h

/-- A fourth-cutoff integral inequality yields the local quadratic estimate. -/
theorem u6_regular_squaredSquareCutoff_local_of_integral_inequality
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hineq0 : ∃ A B D : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ D ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0,
      let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
      (∫ y, (f y) ^ 2 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        (A + B * (t : ℝ)) * (t : ℝ) ^ 2 + D * ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ y, (f y) ^ 2 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x)) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a →
      ∀ t : ℝ≥0, (t : ℝ) ≤ δ →
      (∫ y, (gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2 ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤ C * (t : ℝ) ^ 2 := by
  obtain ⟨A, B, D, hA, hB, hD, hineq⟩ :=
    hineq0
  refine ⟨2 * (A + B), (2 * (D + 1))⁻¹, by positivity, by positivity, ?_⟩
  intro x k a ha t ht
  let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
  let φ : Vec d → ℝ := fun y => (f y) ^ 2
  have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  have hs : ContDiff ℝ (⊤ : ℕ∞) φ := hp.1.pow 2
  have hcompact : HasCompactSupport φ := by
    have h : HasCompactSupport (fun y => f y * f y) := hp.2.1.mul_right
    simpa only [φ, pow_two] using h
  let S := u2RegularC0Semigroup hd ω lam Λ hΛ hω
  let F := gmpPhysicalCompactC0 φ hs.continuous hcompact
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun g => g x
        map_add' := by intro g h; rfl
        map_smul' := by intro c g; rfl } 1 (by
          intro g
          simpa using BoundedContinuousFunction.norm_coe_le_norm g.toBCF x)
  let m : ℝ → ℝ := fun s => ∫ y, φ y ∂
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x)
  have hc : Continuous m := by
    have heq (s : ℝ) : m s = ev (S (Real.toNNReal s) F) :=
      u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω (Real.toNNReal s) F x
    rw [funext heq]
    exact ev.continuous.comp (S.continuous_operator_toNNReal F)
  have hnonneg (s : ℝ) (_ : 0 ≤ s) : 0 ≤ m s := by
    apply integral_nonneg
    intro y
    exact sq_nonneg _
  have hi (s : ℝ) (hs0 : 0 ≤ s) :
      m s ≤ (A + B * s) * s ^ 2 + D * ∫ r in (0 : ℝ)..s, m r := by
    have h := hineq x k a ha (Real.toNNReal s)
    rw [Real.coe_toNNReal' s, max_eq_left hs0] at h
    exact h
  have h := gmpPhysical_quadratic_bound_of_integral_inequality m hc A B D hA hB hD hnonneg hi t t.coe_nonneg ht
  simpa [m, φ, f] using h


/-- Uniform local fourth-cutoff estimates pass to the actual coordinate moment. -/
theorem u6_regular_coordinateFourth_of_cutoff_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hcutoff : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0, (t : ℝ) ≤ δ →
      (∫ y, (gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2 ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤ C * (t : ℝ) ^ 2) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      (t : ℝ) ≤ δ →
      Integrable (fun y => (y k - x k) ^ 4)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (y k - x k) ^ 4 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        C * (t : ℝ) ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hcut⟩ :=
    hcutoff
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro x k t ht
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let μ := P t x
  letI : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  let D : ℝ := C * (t : ℝ) ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb (m : ℕ) :
      (∫⁻ y, ENNReal.ofReal ((gmpPhysicalCoordinateMomentCutoff x k 1 (((m : ℝ) + 1)⁻¹) y) ^ 2) ∂μ) ≤
        ENNReal.ofReal D := by
    let a : ℝ := ((m : ℝ) + 1)⁻¹
    have ha : 0 < a := by dsimp [a]; positivity
    have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
    have hc : HasCompactSupport (fun y => (gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2) := by
      have hh : HasCompactSupport (fun y => gmpPhysicalCoordinateMomentCutoff x k 1 a y *
          gmpPhysicalCoordinateMomentCutoff x k 1 a y) := hp.2.1.mul_right
      simpa only [pow_two] using hh
    have hi : Integrable (fun y => (gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2) μ :=
      (hp.1.pow 2).continuous.integrable_of_hasCompactSupport hc
    change (∫⁻ y, ENNReal.ofReal ((gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2) ∂μ) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun y => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hcut x k a ha t ht)
  have hl : (∫⁻ y, ENNReal.ofReal ((y k - x k) ^ 4) ∂μ) ≤ ENNReal.ofReal D := by
    exact (gmpPhysical_squaredSquareCutoff_fatou x k μ).trans
      (Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hb))
  have hc : Continuous (fun y : Vec d => (y k - x k) ^ 4) := by fun_prop
  have h0 : ∀ y : Vec d, 0 ≤ (y k - x k) ^ 4 := fun y => by positivity
  have hint : Integrable (fun y => (y k - x k) ^ 4) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable (ae_of_all _ h0)).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hl)
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ h0)] at hl
  exact (ENNReal.ofReal_le_ofReal_iff hD).1 hl


/-- A regular compact-test generator orbit is time-integrable on finite intervals. -/
theorem u6_regular_generator_orbit_intervalIntegrable {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (x : Vec d) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) volume 0 t := by
  obtain ⟨D, hD, hm, hb⟩ := u2_regular_kernel_compactTest_generator_orbit hd ω lam Λ hΛ hω φ hφ hc
  have hm' := hm.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ => x)))
  change Measurable (fun s : ℝ => ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
    u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) at hm'
  apply (intervalIntegrable_const (c := D)).mono_fun hm'.aestronglyMeasurable
  filter_upwards with s
  simpa only [Real.norm_eq_abs, Real.norm_of_nonneg hD] using hb (Real.toNNReal s) x

/-- Positive-time comparisons integrate on a finite interval. -/
theorem u6_intervalIntegral_mono_Ioc (F G : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hF : IntervalIntegrable F volume 0 t) (hG : IntervalIntegrable G volume 0 t)
    (h : ∀ s ∈ Set.Ioc (0 : ℝ) t, F s ≤ G s) :
    (∫ s in (0 : ℝ)..t, F s) ≤ ∫ s in (0 : ℝ)..t, G s := by
  rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
  apply integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hF)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hG)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact h s hs

/-- Dynkin's identity, every-start absolute continuity, and square moments give
 the fourth-cutoff integral inequality for the regular kernel. -/
theorem u6_regular_squaredSquareCutoff_integral_inequality_of_dynkin
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪ physicalReversibleMeasure ω hd lam)
    (hsecond : ∃ D E : ℝ, 0 ≤ D ∧ 0 ≤ E ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      Integrable (fun y => (y k - x k) ^ 2) (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (y k - x k) ^ 2 ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        (D + E * (t : ℝ)) * (t : ℝ))
    (hdyn : ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∀ (t : ℝ≥0) (x : Vec d),
      (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) - φ x =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
          u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) :
    ∃ A B C : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0,
      let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
      (∫ y, (f y) ^ 2 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        (A + B * (t : ℝ)) * (t : ℝ) ^ 2 + C * ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ y, (f y) ^ 2 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) := by
  obtain ⟨D, E, hD, hE, hmoment⟩ := hsecond
  have hsi : ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0), 0 < t →
      Integrable (fun y => (y k - x k) ^ 2) (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) :=
    fun x k t _ => (hmoment x k t).1
  obtain ⟨A, B, hA, hB, hgen⟩ :=
    u6_regular_squaredSquareCutoff_generator_integral_le hd ω lam Λ hΛ hω hac hsi
  refine ⟨A * D, A * E, B, by positivity, by positivity, hB, ?_⟩
  intro x k a ha t
  let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
  let φ : Vec d → ℝ := fun y => (f y) ^ 2
  have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  have hs : ContDiff ℝ (⊤ : ℕ∞) φ := hp.1.pow 2
  have hcompact : HasCompactSupport φ := by
    have h : HasCompactSupport (fun y => f y * f y) := hp.2.1.mul_right
    simpa only [φ, pow_two] using h
  let S := u2RegularC0Semigroup hd ω lam Λ hΛ hω
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun g => g x
        map_add' := by intro g h; rfl
        map_smul' := by intro c g; rfl } 1 (by
          intro g
          simpa using BoundedContinuousFunction.norm_coe_le_norm g.toBCF x)
  let F := gmpPhysicalCompactC0 φ hs.continuous hcompact
  have hcF : Continuous (fun s : ℝ => ∫ y, φ y ∂
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) := by
    have heq (s : ℝ) : (∫ y, φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) =
          ev (S (Real.toNNReal s) F) :=
      u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω (Real.toNNReal s) F x
    simp_rw [heq]
    exact ev.continuous.comp (S.continuous_operator_toNNReal F)
  have hiG := u6_regular_generator_orbit_intervalIntegrable hd ω lam Λ hΛ hω φ hs hcompact x t
  have hpoint (s : ℝ) (hsi : s ∈ Set.Ioc 0 (t : ℝ)) :
      (∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) ≤
      A * ((D + E * (t : ℝ)) * (t : ℝ)) + B * (∫ y, φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) := by
    have htpos : 0 < Real.toNNReal s := Real.toNNReal_pos.mpr hsi.1
    have h := hgen x k a ha (Real.toNNReal s) htpos
    have hm := (hmoment x k (Real.toNNReal s)).2
    rw [Real.coe_toNNReal' s, max_eq_left hsi.1.le] at hm
    have hpoly : (D + E * s) * s ≤ (D + E * (t : ℝ)) * (t : ℝ) := by
      nlinarith [mul_nonneg hE hsi.1.le, mul_nonneg hE t.coe_nonneg,
        mul_nonneg (sub_nonneg.mpr hsi.2) hD,
        mul_nonneg (sub_nonneg.mpr hsi.2) (mul_nonneg hE (add_nonneg hsi.1.le t.coe_nonneg))]
    have hh := mul_le_mul_of_nonneg_left (hm.trans hpoly) hA
    dsimp [φ, f] at h ⊢
    linarith
  have hi := u6_intervalIntegral_mono_Ioc _ _ t t.coe_nonneg hiG
    (intervalIntegrable_const.add ((hcF.intervalIntegrable 0 t).const_mul B)) hpoint
  have he := hdyn φ hs hcompact t x
  have hz : φ x = 0 := by simp [φ, f, gmpPhysicalCoordinateMomentCutoff]
  rw [hz, sub_zero] at he
  change (∫ y, φ y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤ _
  rw [he]
  rw [intervalIntegral.integral_add intervalIntegrable_const ((hcF.intervalIntegrable 0 t).const_mul B),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hi
  simp only [smul_eq_mul, sub_zero] at hi
  nlinarith [hi]

#print axioms u6_regular_squaredSquareCutoff_integral_inequality_of_dynkin
/-- The fourth-cutoff integral inequality yields the regular continuous-path kernel. -/
theorem u6_regular_continuous_kernel_of_cutoff_integral_inequality
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hineq : ∃ A B D : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ D ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0,
      let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
      (∫ y, (f y) ^ 2 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        (A + B * (t : ℝ)) * (t : ℝ) ^ 2 + D * ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ y, (f y) ^ 2 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x)) :
    ∃ K : Kernel (Vec d) (Path d), IsMarkovKernel K ∧
      ∀ I : Finset ℝ≥0,
        K.map (ContinuousPath.finsetEvaluation I) =
          finiteSetKernel (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I := by
  apply u6_regular_continuous_kernel_of_coordinate_fourth hd ω lam Λ hΛ hω
  apply u6_regular_coordinateFourth_of_cutoff_bound hd ω lam Λ hΛ hω
  exact u6_regular_squaredSquareCutoff_local_of_integral_inequality hd ω lam Λ hΛ hω hineq

/-- Every-start Dynkin and positive-time absolute continuity give the regular
continuous-path kernel, using the square and fourth cutoff bootstraps. -/
theorem u6_regular_continuous_kernel_of_ac_dynkin
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪ physicalReversibleMeasure ω hd lam)
    (hdyn : ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∀ (t : ℝ≥0) (x : Vec d),
      (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) - φ x =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
          u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) :
    ∃ K : Kernel (Vec d) (Path d), IsMarkovKernel K ∧
      ∀ I : Finset ℝ≥0,
        K.map (ContinuousPath.finsetEvaluation I) =
          finiteSetKernel (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I := by
  obtain ⟨A, B, hA, hB, hcut⟩ :=
    u8_regular_squareCutoff_bound_of_ac_dynkin hd ω lam Λ hΛ hω hac hdyn
  have hsecond := u8_regular_coordinateSquare_of_cutoff_bound hd ω lam Λ hΛ hω A B hA hB hcut
  apply u6_regular_continuous_kernel_of_cutoff_integral_inequality hd ω lam Λ hΛ hω
  exact u6_regular_squaredSquareCutoff_integral_inequality_of_dynkin hd ω lam Λ hΛ hω
    hac ⟨A, B, hA, hB, hsecond⟩ hdyn

/-- Positive-time absolute continuity gives the regular continuous-path kernel. -/
theorem u6_regular_continuous_kernel_of_ac
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪ physicalReversibleMeasure ω hd lam) :
    ∃ K : Kernel (Vec d) (Path d), IsMarkovKernel K ∧
      ∀ I : Finset ℝ≥0,
        K.map (ContinuousPath.finsetEvaluation I) =
          finiteSetKernel (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I := by
  apply u6_regular_continuous_kernel_of_ac_dynkin hd ω lam Λ hΛ hω hac
  exact u8_regular_compactTest_dynkin_of_ac hd ω lam Λ hΛ hω hac

/-- Lebesgue absolute continuity of the regular kernel gives its continuous-path realization. -/
theorem u6_regular_continuous_kernel_of_volume_ac
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪ (volume : Measure (Vec d))) :
    ∃ K : Kernel (Vec d) (Path d), IsMarkovKernel K ∧
      ∀ I : Finset ℝ≥0,
        K.map (ContinuousPath.finsetEvaluation I) =
          finiteSetKernel (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I := by
  apply u6_regular_continuous_kernel_of_ac hd ω lam Λ hΛ hω
  intro t ht x
  exact (hac t ht x).trans (gmpVolume_absolutelyContinuous_physical hd ω lam)

/-- At zero force, the regular kernel has a continuous-path realization. -/
theorem u6_regular_unforced_continuous_kernel_exists
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ K : Kernel (Vec d) (Path d), IsMarkovKernel K ∧
      ∀ I : Finset ℝ≥0,
        K.map (ContinuousPath.finsetEvaluation I) =
          finiteSetKernel (u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω) I := by
  apply u6_regular_continuous_kernel_of_ac hd ω 0 Λ hΛ hω
  intro t ht x
  obtain ⟨M, hM, hdom⟩ := u2_regular_unforced_kernel_domination hd ω Λ hΛ hω t ht
  exact (Measure.absolutelyContinuous_of_le_smul (hdom x)).trans
    (Measure.absolutelyContinuous_of_le_smul
      (u4_unforced_physical_measure_comparable hd ω Λ hω).2)

#print axioms u6_regular_unforced_continuous_kernel_exists
#print axioms u6_regular_continuous_kernel_of_volume_ac
#print axioms u6_regular_continuous_kernel_of_ac
#print axioms u6_regular_continuous_kernel_of_ac_dynkin
#print axioms u6_regular_continuous_kernel_of_cutoff_integral_inequality
#print axioms u6_regular_squaredSquareCutoff_generator_ae_bound
#print axioms u6_regular_squaredSquareCutoff_generator_integral_le
#print axioms u6_regular_squaredSquareCutoff_local_of_integral_inequality
#print axioms u6_regular_coordinateFourth_of_cutoff_bound
#print axioms u6_regular_continuous_kernel_of_coordinate_fourth
#print axioms u6_regular_clippedFourth_lintegral_of_coordinate_local
#print axioms u6_regular_onePoint_localMoments_of_euclidean_fourth
#print axioms u6_regular_continuous_kernel_of_euclidean_fourth
end EinsteinFull
