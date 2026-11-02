import EinsteinFull.Calculus.C16ReducedGeneratorAE
import EinsteinFull.Calculus.S4CountableBasicSupport
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Inverse-clock transport for regular environments

The pointwise clock identity is used directly, so the time substitution keeps the actual
Fréchet-derivative values of both generators, including at nondifferentiability points.
-/

open MeasureTheory
open scoped NNReal BigOperators

namespace EinsteinFull
open EinsteinRelation ProbabilityTheory
open EinsteinRelation.Clock EinsteinRelation.Clock.InverseMeaningV3

private theorem c16_exists_lipschitz_mul {E : Type*} [PseudoMetricSpace E]
    {f g : E → ℝ} {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    {Cf Cg : ℝ} (hCf : ∀ x, |f x| ≤ Cf) (hCg : ∀ x, |g x| ≤ Cg) :
    ∃ K, LipschitzWith K (fun x => f x * g x) := by
  let C := |Cf| * (Kg : ℝ) + |Cg| * (Kf : ℝ)
  have hC : 0 ≤ C := by positivity
  refine ⟨Real.toNNReal C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.coe_toNNReal C hC, Real.dist_eq]
  calc
    |f x * g x - f y * g y| = |f x * (g x - g y) + (f x - f y) * g y| := by ring_nf
    _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
      simpa only [abs_mul] using abs_add_le (f x * (g x - g y)) ((f x - f y) * g y)
    _ ≤ |Cf| * ((Kg : ℝ) * dist x y) + ((Kf : ℝ) * dist x y) * |Cg| := by
      exact add_le_add
        (mul_le_mul ((hCf x).trans (le_abs_self _)) (by simpa only [Real.dist_eq] using hg.dist_le_mul x y)
          (abs_nonneg _) (abs_nonneg _))
        (mul_le_mul (by simpa only [Real.dist_eq] using hf.dist_le_mul x y)
          ((hCg y).trans (le_abs_self _)) (abs_nonneg _) (by positivity))
    _ = C * dist x y := by dsimp [C]; ring

private theorem c16_flux_lipschitz {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (k : Fin d) :
    ∃ K, LipschitzWith K (fun y => (reducedCoefficient ω y).mulVec (gradient f y) k) := by
  have hg : ∀ j : Fin d, ContDiff ℝ 1 (fun y => fderiv ℝ f y (unitVector j)) := fun j =>
    ((contDiff_two_of_top hf).fderiv_right (le_of_eq one_add_one_eq_two)).clm_apply contDiff_const
  have hprod : ∀ j : Fin d, ∃ K, LipschitzWith K
      (fun y => reducedCoefficient ω y k j * fderiv ℝ f y (unitVector j)) := by
    intro j
    obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
      (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (unitVector j)) (hg j) one_ne_zero
    obtain ⟨B, hB⟩ := (hg j).continuous.bounded_above_of_compact_support
      (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (unitVector j))
    exact c16_exists_lipschitz_mul (reducedCoefficient_lipschitz hΛ hω k j) hK
      (fun y => abs_reducedCoefficient_le hΛ hω y k j)
      (fun y => by simpa only [Real.norm_eq_abs] using hB y)
  choose K hK using hprod
  refine ⟨∑ j, K j, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  change ‖(∑ j, reducedCoefficient ω x k j * fderiv ℝ f x (unitVector j)) -
      (∑ j, reducedCoefficient ω y k j * fderiv ℝ f y (unitVector j))‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ j, (K j : ℝ) * dist x y :=
      Finset.sum_le_sum fun j _ => (hK j).norm_sub_le x y
    _ = _ := by rw [← Finset.sum_mul]; simp only [NNReal.coe_sum]

private theorem c16_measurable_reduced_generator {d : ℕ} (ω : FieldPair d)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) :
    Measurable (reducedGenerator i ω lam f) := by
  unfold reducedGenerator divergence coordinateDerivative dot
  refine Measurable.add (measurable_const.mul ?_) (measurable_const.mul ?_)
  · exact Finset.measurable_sum _ fun k _ => measurable_fderiv_apply_const ℝ _ _
  · refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
    · simpa only [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
        ((continuous_reducedCoefficient ω).matrix_elem k i).measurable
    · exact measurable_fderiv_apply_const ℝ f (unitVector k)

private theorem c16_bounded_reduced_generator {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ x, |reducedGenerator i ω lam f x| ≤ C := by
  choose K hK using fun k => c16_flux_lipschitz hΛ hω hf hc k
  have hfirst : ∀ j : Fin d, ∃ B : ℝ, ∀ x, |coordinateDerivative j f x| ≤ B := by
    intro j
    obtain ⟨B, hB⟩ := (continuous_fderiv_apply_first (contDiff_two_of_top hf) j).bounded_above_of_compact_support
      (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (unitVector j))
    exact ⟨B, fun x => by simpa only [coordinateDerivative, Real.norm_eq_abs] using hB x⟩
  choose B hB using hfirst
  have hdiv : ∀ x, |divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x| ≤
      ∑ k, (K k : ℝ) * ‖unitVector k‖ := by
    intro x
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    change |fderiv ℝ _ x (unitVector k)| ≤ _
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ _ x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hK k)) (norm_nonneg _))
  refine ⟨(1 / 2 : ℝ) * (∑ k, (K k : ℝ) * ‖unitVector k‖) +
      |lam| * (∑ k, (Real.exp (2 * Λ₀) * Λ₀) * B k), fun x => ?_⟩
  unfold reducedGenerator
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left (hdiv x) (by norm_num)
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg lam)
    unfold dot
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have he : (reducedCoefficient ω x).mulVec (unitVector i) k = reducedCoefficient ω x k i := by
      simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
    rw [he, abs_mul]
    exact mul_le_mul (abs_reducedCoefficient_le hΛ hω x k i) (hB k x) (abs_nonneg _)
      (by positivity)

private theorem c16_measurable_physical_generator {d : ℕ} (ω : FieldPair d)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) :
    Measurable (physicalGenerator i ω lam f) := by
  have he : physicalGenerator i ω lam f =
      fun x => (clockDensity ω x)⁻¹ * reducedGenerator i ω lam f x :=
    funext fun x => physicalGenerator_eq_inv_mul ω i lam f x
  rw [he]
  exact (reduce ω).2.continuous.measurable.inv.mul (c16_measurable_reduced_generator ω i lam f)

private theorem c16_bounded_physical_generator {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ x, |physicalGenerator i ω lam f x| ≤ C := by
  obtain ⟨C, hC⟩ := c16_bounded_reduced_generator hΛ hω i lam hf hc
  refine ⟨Real.exp (2 * Λ₀) * C, fun x => ?_⟩
  rw [physicalGenerator_eq_inv_mul, abs_mul]
  have hinv : (clockDensity ω x)⁻¹ = Real.exp (2 * ω.2 x) := by
    rw [clockDensity, ← Real.exp_neg]
    congr 1
    ring
  have h1 : |(clockDensity ω x)⁻¹| ≤ Real.exp (2 * Λ₀) := by
    rw [hinv, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by have := (abs_le.1 (hω.2.1 x)).2; linarith)
  exact mul_le_mul h1 (hC x) (abs_nonneg _) (Real.exp_pos _).le

private theorem c16_time_change_integral {d : ℕ} {L : ℝ} {ω : FieldPair d} (hω : IsRegular L ω)
    (γ : Path d) (s : ℝ≥0) (G : Vec d → ℝ) :
    ∫ t in (0 : ℝ)..((inversePhysicalPathClock ω γ L hω s : ℝ≥0) : ℝ),
        G (γ t.toNNReal) * clockDensity ω (γ t.toNNReal) =
      ∫ u in (0 : ℝ)..(s : ℝ), G (γ (inversePhysicalPathClock ω γ L hω u.toNNReal)) := by
  have hμ : Continuous (clockDensity ω) := (reduce ω).2.continuous
  have hcont : Continuous (fun u : ℝ => clockDensity ω (γ u.toNNReal)) :=
    hμ.comp (γ.continuous.comp continuous_real_toNNReal)
  have hF : ∀ t : ℝ, 0 ≤ t →
      (∫ u in (0 : ℝ)..t, clockDensity ω (γ u.toNNReal)) =
        ((physicalPathClock ω γ t.toNNReal : ℝ≥0) : ℝ) := by
    intro t ht
    show _ = pathClock (clockDensity ω) γ t.toNNReal
    unfold pathClock
    rw [Real.coe_toNNReal t ht]
  have key := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := 0)
    (b := ((inversePhysicalPathClock ω γ L hω s : ℝ≥0) : ℝ))
    (f := fun t : ℝ => ∫ u in (0 : ℝ)..t, clockDensity ω (γ u.toNNReal))
    (f' := fun t : ℝ => clockDensity ω (γ t.toNNReal))
    (g := fun u : ℝ => G (γ (inversePhysicalPathClock ω γ L hω u.toNNReal)))
    (intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) 0).continuousOn
    (fun x _ => (hcont.integral_hasStrictDerivAt 0 x).hasDerivAt)
    (fun x _ => (clockDensity_pos ω _).le)
  have hF0 : (∫ u in (0 : ℝ)..(0 : ℝ), clockDensity ω (γ u.toNNReal)) = 0 :=
    intervalIntegral.integral_same
  have hFT : (∫ u in (0 : ℝ)..((inversePhysicalPathClock ω γ L hω s : ℝ≥0) : ℝ),
      clockDensity ω (γ u.toNNReal)) = (s : ℝ) := by
    rw [hF _ (NNReal.coe_nonneg _), Real.toNNReal_coe,
      physicalPathClock_inversePhysicalPathClock]
  rw [hF0, hFT] at key
  rw [← key]
  refine intervalIntegral.integral_congr fun x hx => ?_
  have hx0 : 0 ≤ x := by
    rw [Set.uIcc_of_le (NNReal.coe_nonneg _)] at hx
    exact hx.1
  show G (γ x.toNNReal) * clockDensity ω (γ x.toNNReal) =
    G (γ (inversePhysicalPathClock ω γ L hω
      (∫ u in (0 : ℝ)..x, clockDensity ω (γ u.toNNReal)).toNNReal)) *
      clockDensity ω (γ x.toNNReal)
  rw [hF x hx0, Real.toNNReal_coe, inversePhysicalPathClock_physicalPathClock]

private theorem c16_compensated_test_inverse_clock {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hω : IsRegular L ω) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (γ : Path d) (s : ℝ≥0) :
    compensatedTest (physicalGenerator i ω lam) f s (inverseClockPath ω γ L hω) =
      compensatedTest (reducedGenerator i ω lam) f
        (inversePhysicalPathClock ω γ L hω s) γ := by
  unfold compensatedTest
  have h0 : (inverseClockPath ω γ L hω) 0 = γ 0 := inverseClockPath_zero ω γ L hω
  have hcv := c16_time_change_integral hω γ s (physicalGenerator i ω lam f)
  have e1 : (fun t : ℝ => reducedGenerator i ω lam f (γ t.toNNReal)) =
      fun t : ℝ => physicalGenerator i ω lam f (γ t.toNNReal) *
        clockDensity ω (γ t.toNNReal) := by
    funext t
    rw [← clockDensity_mul_physicalGenerator]
    exact mul_comm _ _
  rw [h0, e1, hcv]
  rfl

/-- Inverse-clock transport of the actual reduced martingale problem in a regular environment. -/
theorem c16_time_change_solves_of_regular {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (x : Vec d) {PY : Measure (Path d)}
    (hY : SolvesMartingaleProblem (reducedGenerator i ω lam) x PY) :
    SolvesMartingaleProblem (physicalGenerator i ω lam) x
      (Measure.map
        (Clock.InverseMeaningV3.inverseClockPath ω · Λ₀ hω) PY) := by
  change SolvesMartingaleProblem (physicalGenerator i ω lam) x (PY.map (timeChangeMap hω))
  obtain ⟨hprob, hstart, hf⟩ := hY
  have : IsProbabilityMeasure PY := hprob
  have hΦ : Measurable (timeChangeMap hω) := measurable_timeChangeMap hω
  refine ⟨inferInstance, ?_, ?_⟩
  · have hmeas : MeasurableSet {γ : Path d | γ 0 = x} :=
      (measurable_pathPosition 0) (measurableSet_singleton x)
    rw [ae_map_iff hΦ.aemeasurable hmeas]
    filter_upwards [hstart] with γ hγ
    show (inverseClockPath ω γ Λ₀ hω) 0 = x
    rw [inverseClockPath_zero]
    exact hγ
  · intro f hfs hfc
    obtain ⟨_, _, hmart⟩ := hf f hfs hfc
    have hf0 : Continuous f := hfs.continuous
    obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, ∀ y, |f y| ≤ Cf := by
      obtain ⟨C, hC⟩ := hf0.bounded_above_of_compact_support hfc
      exact ⟨C, fun y => by
        have := hC y
        rwa [Real.norm_eq_abs] at this⟩
    have hLr := c16_measurable_reduced_generator ω i lam f
    have hLp := c16_measurable_physical_generator ω i lam f
    obtain ⟨Cr, hCr⟩ := c16_bounded_reduced_generator hΛ hω i lam hfs hfc
    obtain ⟨Cp, hCp⟩ := c16_bounded_physical_generator hΛ hω i lam hfs hfc
    have hNad := stronglyAdapted_compensatedTest_of_measurable (physicalGenerator i ω lam) f hf0 hLp
    have hNint : ∀ t : ℝ≥0, Integrable (compensatedTest (physicalGenerator i ω lam) f t)
        (PY.map (timeChangeMap hω)) := by
      intro t
      have hm : StronglyMeasurable (compensatedTest (physicalGenerator i ω lam) f t) :=
        (hNad t).mono ((pathFiltration d).le t)
      exact Integrable.of_bound hm.aestronglyMeasurable (2 * Cf + Cp * t)
        (Filter.Eventually.of_forall fun γ => norm_compensatedTest_le _ f hCf hCp t γ)
    refine ⟨fun t => Filter.Eventually.of_forall fun γ => ?_, hNint, ?_⟩
    · refine (intervalIntegrable_const (c := Cp)).mono_fun ?_ ?_
      · exact (hLp.comp (γ.continuous.comp continuous_real_toNNReal).measurable).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun u => by
          simpa only [Real.norm_eq_abs] using (hCp (γ u.toNNReal)).trans (le_abs_self Cp)
    · rw [pathFiltration_eq_canonical] at hmart ⊢
      rw [pathFiltration_eq_canonical] at hNad
      refine ⟨hNad, fun r s hrs => ?_⟩
      have hNm : ∀ t : ℝ≥0, StronglyMeasurable
          (compensatedTest (physicalGenerator i ω lam) f t) := fun t =>
        (hNad t).mono ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le t)
      refine (ae_eq_condExp_of_forall_setIntegral_eq
        ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le r)
        (hNint s) (fun B _ _ => (hNint r).integrableOn) ?_
        (hNad r).aestronglyMeasurable).symm
      intro B hB _
      have hBm : MeasurableSet B :=
        (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le r B hB
      rw [setIntegral_map hBm (hNm r).aestronglyMeasurable hΦ.aemeasurable,
        setIntegral_map hBm (hNm s).aestronglyMeasurable hΦ.aemeasurable]
      have e : ∀ (t : ℝ≥0) (γ : Path d),
          compensatedTest (physicalGenerator i ω lam) f t (timeChangeMap hω γ) =
            compensatedTest (reducedGenerator i ω lam) f
              (inversePhysicalPathClock ω γ Λ₀ hω t) γ := fun t γ =>
        c16_compensated_test_inverse_clock hω i lam γ t
      have hint' : ∀ t : ℝ≥0, Integrable (fun γ : Path d =>
          compensatedTest (reducedGenerator i ω lam) f
            (inversePhysicalPathClock ω γ Λ₀ hω t) γ) PY := by
        intro t
        have h1 := (integrable_map_measure (hNm t).aestronglyMeasurable
          hΦ.aemeasurable).1 (hNint t)
        have e' : (fun γ : Path d => compensatedTest (reducedGenerator i ω lam) f
            (inversePhysicalPathClock ω γ Λ₀ hω t) γ) =
            compensatedTest (physicalGenerator i ω lam) f t ∘ timeChangeMap hω :=
          funext fun γ => (e t γ).symm
        rw [e']
        exact h1
      have hbound : ∀ v : ℝ≥0, ∃ C : ℝ, ∀ t ≤ v, ∀ γ : Path d,
          ‖compensatedTest (reducedGenerator i ω lam) f t γ‖ ≤ C := by
        intro v
        refine ⟨2 * Cf + max Cr 0 * v, fun t ht γ => ?_⟩
        have h := norm_compensatedTest_le (reducedGenerator i ω lam) f (CL := max Cr 0) hCf
          (fun y => (hCr y).trans (le_max_left _ _)) t γ
        have h' : max Cr 0 * (t : ℝ) ≤ max Cr 0 * v :=
          mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 ht) (le_max_right _ _)
        linarith
      have hright : ∀ (γ : Path d) (v : ℝ≥0),
          ContinuousWithinAt (fun t : ℝ≥0 => compensatedTest (reducedGenerator i ω lam) f t γ)
            (Set.Ici v) v := fun γ v =>
        (continuous_compensatedTest_time_of_bounded _ f hf0 hLr hCr γ).continuousWithinAt
      have hmono : ∀ γ : Path d, inversePhysicalPathClock ω γ Λ₀ hω r ≤
          inversePhysicalPathClock ω γ Λ₀ hω s := fun γ =>
        (physicalPathClockOrderIso ω γ Λ₀ hω).symm.monotone hrs
      have hsK : ∀ γ : Path d, inversePhysicalPathClock ω γ Λ₀ hω s ≤
          Real.toNNReal (Real.exp (2 * Λ₀) * s) := fun γ =>
        NNReal.le_toNNReal_of_coe_le (inversePhysicalPathClock_bounds ω γ Λ₀ hω s).2
      have hB' := measurable_timeChangeMap_stopped hω r hB
      have key := setIntegral_stoppedValue_eq (μ := PY) hmart hbound hright
        (isStoppingTime_inversePhysicalPathClock_canonical hω r)
        (isStoppingTime_inversePhysicalPathClock_canonical hω s) hmono
        (fun γ => (hmono γ).trans (hsK γ)) hsK (hint' r) (hint' s) hB'
      have lhs : ∫ x in timeChangeMap hω ⁻¹' B,
          compensatedTest (physicalGenerator i ω lam) f r (timeChangeMap hω x) ∂PY =
          ∫ x in timeChangeMap hω ⁻¹' B, compensatedTest (reducedGenerator i ω lam) f
            (inversePhysicalPathClock ω x Λ₀ hω r) x ∂PY :=
        setIntegral_congr_fun (hΦ hBm) fun γ _ => e r γ
      have rhs : ∫ x in timeChangeMap hω ⁻¹' B,
          compensatedTest (physicalGenerator i ω lam) f s (timeChangeMap hω x) ∂PY =
          ∫ x in timeChangeMap hω ⁻¹' B, compensatedTest (reducedGenerator i ω lam) f
            (inversePhysicalPathClock ω x Λ₀ hω s) x ∂PY :=
        setIntegral_congr_fun (hΦ hBm) fun γ _ => e s γ
      rw [lhs, rhs]
      exact key.symm


end EinsteinFull
