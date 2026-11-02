import EinsteinFull.Calculus.S4TestFamilySupport
import EinsteinFull.Calculus.S4CylinderSupport
import EinsteinFull.Calculus.S4PathClockSupport
import EinsteinFull.Calculus.S4TimeChangeMartingale

/-!
# Bounded measurable coefficients: approximation lemmas for the martingale problem

For a diffusion matrix `A` and a drift `b` with bounded measurable entries, the textbook operator
`svGenerator A b` is measurable and bounded on test functions with controlled derivatives, and
the compensated tests of an approximating sequence converge boundedly.
-/

open MeasureTheory Topology Filter
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- Bounded measurable coefficients. -/
structure BddCoef {d : ℕ} (A : Vec d → Mat d) (b : Vec d → Vec d) (M : ℝ) : Prop where
  Am : ∀ i j, Measurable fun y => A y i j
  bm : ∀ k, Measurable fun y => b y k
  Ab : ∀ y i j, |A y i j| ≤ M
  bb : ∀ y k, |b y k| ≤ M

theorem BddCoef.measurable_gen {d : ℕ} {A : Vec d → Mat d} {b : Vec d → Vec d} {M : ℝ}
    (h : BddCoef A b M) (f : Vec d → ℝ) : Measurable (External.Draft.svGenerator A b f) := by
  unfold External.Draft.svGenerator
  refine Measurable.add ?_ ?_
  · refine measurable_const.mul ?_
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact (h.Am i j).mul (measurable_fderiv_apply_const ℝ
      (fun y => fderiv ℝ f y (unitVector j)) (unitVector i))
  · refine Finset.measurable_sum _ fun i _ => ?_
    exact (h.bm i).mul (measurable_fderiv_apply_const ℝ f (unitVector i))

theorem BddCoef.gen_bound {d : ℕ} {A : Vec d → Mat d} {b : Vec d → Vec d} {M : ℝ}
    (h : BddCoef A b M) {m : ℝ} {u : Vec d → ℝ} (hu : InH m u) (y : Vec d) :
    |External.Draft.svGenerator A b u y| ≤
      (1 / 2 : ℝ) * (d * (d * (M * m))) + d * (M * m) := by
  unfold External.Draft.svGenerator
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j, A y i j *
          fderiv ℝ (fun z => fderiv ℝ u z (unitVector j)) y (unitVector i)|
        ≤ ∑ _i : Fin d, ((d : ℝ) * (M * m)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ j, |A y i j * fderiv ℝ (fun z => fderiv ℝ u z (unitVector j)) y (unitVector i)|
              ≤ ∑ _j : Fin d, (M * m) := by
                refine Finset.sum_le_sum fun j _ => ?_
                rw [abs_mul]
                exact mul_le_mul (h.Ab y i j) ((hu.2.2.2 i j).1 y) (abs_nonneg _)
                  ((abs_nonneg _).trans (h.Ab y i j))
            _ = d * (M * m) := by simp
      _ = d * (d * (M * m)) := by simp
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |b y i * fderiv ℝ u y (unitVector i)| ≤ ∑ _i : Fin d, (M * m) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (h.bb y i) ((hu.2.2.1 i).1 y) (abs_nonneg _)
            ((abs_nonneg _).trans (h.bb y i))
      _ = d * (M * m) := by simp

theorem BddCoef.gen_tendsto {d : ℕ} {A : Vec d → Mat d} {b : Vec d → Vec d} {M : ℝ}
    (_h : BddCoef A b M) {u : ℕ → Vec d → ℝ} {f : Vec d → ℝ}
    (h1 : ∀ j y, Tendsto (fun k => D1 (u k) j y) atTop (𝓝 (D1 f j y)))
    (h2 : ∀ i j y, Tendsto (fun k => D2 (u k) i j y) atTop (𝓝 (D2 f i j y))) (y : Vec d) :
    Tendsto (fun k => External.Draft.svGenerator A b (u k) y) atTop
      (𝓝 (External.Draft.svGenerator A b f y)) := by
  unfold External.Draft.svGenerator
  refine Tendsto.add ?_ ?_
  · refine tendsto_const_nhds.mul ?_
    exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      tendsto_const_nhds.mul (h2 i j y)
  · exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul (h1 i y)

theorem stronglyMeasurable_pathIntegral_of_measurable {d : ℕ} (g : Vec d → ℝ)
    (hg : Measurable g) (t : ℝ≥0) :
    StronglyMeasurable[MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) t]
      (fun γ : Path d => ∫ s in (0 : ℝ)..t, g (γ s.toNNReal)) := by
  have hcl := MarkovProcess.ContinuousPath.measurable_clampedCoordinate (alpha := Vec d) t
  have hphi : StronglyMeasurable[(borel ℝ).prod
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) t)]
      (fun p : ℝ × Path d => g (p.2 (min (Real.toNNReal p.1) t))) :=
    hg.stronglyMeasurable.comp_measurable hcl
  have hprod : StronglyMeasurable[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) t] (fun γ : Path d =>
        ∫ s, g (γ (min (Real.toNNReal s) t)) ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) :=
    stronglyMeasurable_integral_prod' (volume.restrict (Set.Ioc (0 : ℝ) t)) hphi
  have hfun : (fun γ : Path d => ∫ s in (0 : ℝ)..t, g (γ s.toNNReal)) =
      fun γ : Path d => ∫ s, g (γ (min (Real.toNNReal s) t))
        ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    funext γ
    rw [intervalIntegral.integral_of_le t.coe_nonneg]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hs.2)]
  rw [hfun]
  exact hprod

theorem stronglyAdapted_compensatedTest_of_measurable {d : ℕ}
    (L : (Vec d → ℝ) → Vec d → ℝ) (f : Vec d → ℝ) (hf : Continuous f)
    (hLf : Measurable (L f)) :
    StronglyAdapted (pathFiltration d) (compensatedTest L f) := by
  intro t
  rw [pathFiltration_eq_canonical]
  have h1 : StronglyMeasurable[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) t] (fun γ : Path d => f (γ t)) :=
    hf.comp_stronglyMeasurable
      (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := Vec d) t).stronglyMeasurable
  have h0 : StronglyMeasurable[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) t] (fun γ : Path d => f (γ 0)) :=
    hf.comp_stronglyMeasurable
      (((MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := Vec d) 0).mono
        ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).mono zero_le)
        le_rfl).stronglyMeasurable)
  have hint := stronglyMeasurable_pathIntegral_of_measurable (L f) hLf t
  exact (h1.sub h0).sub hint

theorem continuous_compensatedTest_time_of_bounded {d : ℕ}
    (L : (Vec d → ℝ) → Vec d → ℝ) (f : Vec d → ℝ) (hf : Continuous f)
    (hLm : Measurable (L f)) {C : ℝ} (hC : ∀ y, |L f y| ≤ C) (γ : Path d) :
    Continuous fun t : ℝ≥0 => compensatedTest L f t γ := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => L f (γ u.toNNReal)) volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := C)).mono_fun ?_ ?_
    · exact (hLm.comp (γ.continuous.comp continuous_real_toNNReal).measurable).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun u => ?_
      simp only [Real.norm_eq_abs]
      exact (hC _).trans (le_abs_self C)
  unfold compensatedTest
  have hI : Continuous fun t : ℝ≥0 => ∫ u in (0 : ℝ)..(t : ℝ), L f (γ u.toNNReal) :=
    (intervalIntegral.continuous_primitive (fun a b => hint a b) 0).comp NNReal.continuous_coe
  have hγ : Continuous fun t : ℝ≥0 => f (γ t) := hf.comp γ.continuous
  first
    | exact (hγ.sub continuous_const).sub hI
    | fun_prop

theorem setIntegral_eq_zero_of_piSystem {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {F : MeasurableSpace Ω} (hF : F ≤ m0) {C : Set (Set Ω)}
    (hgen : F = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C) (hu : Set.univ ∈ C)
    {Δ : Ω → ℝ} (hΔ : Integrable Δ μ) (h : ∀ B ∈ C, ∫ ω in B, Δ ω ∂μ = 0) :
    ∀ B, MeasurableSet[F] B → ∫ ω in B, Δ ω ∂μ = 0 := by
  intro B hB
  refine MeasurableSpace.induction_on_inter (C := fun s _ => ∫ ω in s, Δ ω ∂μ = 0)
    hgen hpi ?_ ?_ ?_ ?_ B hB
  · simp
  · intro s hs
    exact h s hs
  · intro t htm ih
    letI : MeasurableSpace Ω := m0
    have htm' : MeasurableSet t := hF _ htm
    have ih' : ∫ ω in t, Δ ω ∂μ = 0 := ih
    have h1 := integral_add_compl htm' hΔ
    have hU := h Set.univ hu
    rw [Measure.restrict_univ] at hU
    show ∫ ω in tᶜ, Δ ω ∂μ = 0
    linarith
  · intro f hfd hfm ih
    letI : MeasurableSpace Ω := m0
    have hfm' : ∀ i, MeasurableSet (f i) := fun i => hF _ (hfm i)
    have ih' : ∀ i, ∫ ω in f i, Δ ω ∂μ = 0 := ih
    show ∫ ω in ⋃ i, f i, Δ ω ∂μ = 0
    rw [integral_iUnion hfm' hfd hΔ.integrableOn]
    simp [ih']

end EinsteinFull
