import EinsteinFull.Calculus.S4ReducedCoefficientSupport
import EinsteinFull.External.Draft.BassFoundation
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.ODE.Gronwall
import MarkovProcess.Path.StoppedValueMeasurability

/-! Continuity of the coordinate maximum used in the source-law exponential estimate. -/

namespace EinsteinFull

open EinsteinRelation MeasureTheory ProbabilityTheory
open scoped NNReal Topology

/-- The absolute coordinate maximum over a compact time interval is continuous in the path. -/
theorem c16_continuous_coordinate_max {d : ℕ} (i : Fin d) (x : Vec d) (T : ℝ≥0) :
    Continuous (fun γ : Path d =>
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T)) := by
  apply IsCompact.continuous_sSup isCompact_Icc
  have heval : Continuous (fun p : Path d × ℝ≥0 => (p.1 p.2) i) :=
    (continuous_apply i).comp (continuous_eval : Continuous
      (fun p : Path d × ℝ≥0 => p.1 p.2))
  exact (heval.sub continuous_const).abs


open EinsteinRelation

/-- Truncating a fixed exit time varies continuously with the time horizon. -/
theorem c16_continuous_exitTimeTrunc {d : ℕ} (U : Set (Vec d)) (γ : Path d) :
    Continuous (fun t : ℝ≥0 => MarkovProcess.ContinuousPath.exitTimeTrunc U t γ) := by
  have hm : Continuous (fun t : ℝ≥0 =>
      min (MarkovProcess.ContinuousPath.exitTimeTop U γ) (t : WithTop ℝ≥0)) :=
    continuous_const.min WithTop.continuous_coe
  have hc := WithTop.continuousOn_untopA.comp_continuous hm (fun t =>
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ (t : WithTop ℝ≥0)))
  simpa only [MarkovProcess.ContinuousPath.exitTimeTrunc, Function.comp_def] using hc

/-- The coordinate exponential along a ball-stopped path is continuous in time. -/
theorem c16_continuous_stopped_coordinate_exp {d : ℕ} (U : Set (Vec d))
    (γ : Path d) (i : Fin d) (q : ℝ) :
    Continuous (fun t : ℝ≥0 => Real.exp (q *
      (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ)) i)) := by
  exact Real.continuous_exp.comp (continuous_const.mul ((continuous_apply i).comp
    (γ.continuous.comp (c16_continuous_exitTimeTrunc U γ))))

/-- A stopped coordinate exponential is jointly measurable in time and path. -/
theorem c16_measurable_stopped_coordinate_exp {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (i : Fin d) (q : ℝ) :
    Measurable (fun p : ℝ≥0 × Path d => Real.exp (q *
      (p.2 (MarkovProcess.ContinuousPath.exitTimeTrunc U p.1 p.2)) i)) := by
  change Measurable (Function.uncurry (fun (t : ℝ≥0) (γ : Path d) =>
    Real.exp (q * (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ)) i)))
  apply measurable_uncurry_of_continuous_of_measurable
  · intro γ
    exact c16_continuous_stopped_coordinate_exp U γ i q
  · intro t
    have ht := MarkovProcess.ContinuousPath.isStoppingTime_exitTimeTrunc U hU t
    have he := (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime _ ht).mono
      ht.measurableSpace_le le_rfl
    exact Real.continuous_exp.measurable.comp
      (measurable_const.mul ((measurable_pi_apply i).comp he))

theorem c16_norm_path_before_ball_exit {d : ℕ} (R : ℝ) (γ : EinsteinRelation.Path d)
    (h0 : euclideanNorm (γ 0) < R) (t u : ℝ≥0)
    (hu : u ≤ MarkovProcess.ContinuousPath.exitTimeTrunc {y : Vec d | euclideanNorm y < R} t γ) :
    euclideanNorm (γ u) ≤ R := by
  let U := {y : Vec d | euclideanNorm y < R}
  have hU : IsOpen U := isOpen_lt (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  have hue : (u : ENNReal) ≤ MarkovProcess.ContinuousPath.exitTime U γ := by
    change (u : WithTop ℝ≥0) ≤ MarkovProcess.ContinuousPath.exitTimeTop U γ
    calc
      (u : WithTop ℝ≥0) ≤ (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ : WithTop ℝ≥0) :=
        WithTop.coe_le_coe.mpr hu
      _ = min (MarkovProcess.ContinuousPath.exitTimeTop U γ) t :=
        MarkovProcess.ContinuousPath.coe_exitTimeTrunc U t γ
      _ ≤ MarkovProcess.ContinuousPath.exitTimeTop U γ := min_le_left _ _
  have hcl : γ u ∈ closure U := by
    rcases lt_or_eq_of_le hue with hlt | heq
    · exact subset_closure (MarkovProcess.ContinuousPath.mem_of_lt_exitTime U γ u hlt)
    · have hfin : MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤ := by
        rw [← heq]
        exact ENNReal.coe_ne_top
      have hf := MarkovProcess.ContinuousPath.coordinate_exitTime_mem_frontier U hU γ h0 hfin
      rw [← heq, ENNReal.toNNReal_coe] at hf
      exact frontier_subset_closure hf
  have heuc : euclideanNorm (γ u) ≤ R :=
    closure_minimal (fun y hy => le_of_lt hy)
      (isClosed_le (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const) hcl
  exact heuc


/-- The coordinate exponential is uniformly bounded before ball exit. -/
theorem c16_exp_coordinate_before_ball_exit {d : ℕ} (R q : ℝ)
    (γ : EinsteinRelation.Path d) (i : Fin d)
    (h0 : euclideanNorm (γ 0) < R) (t u : ℝ≥0)
    (hu : u ≤ MarkovProcess.ContinuousPath.exitTimeTrunc
      {y : Vec d | euclideanNorm y < R} t γ) :
    Real.exp (q * (γ u) i) ≤ Real.exp (|q| * R) := by
  apply Real.exp_le_exp.mpr
  calc
    q * (γ u) i ≤ |q * (γ u) i| := le_abs_self _
    _ = |q| * |(γ u) i| := abs_mul _ _
    _ ≤ |q| * euclideanNorm (γ u) :=
      mul_le_mul_of_nonneg_left (abs_apply_le_euclideanNorm (γ u) i) (abs_nonneg _)
    _ ≤ |q| * R := mul_le_mul_of_nonneg_left
      (c16_norm_path_before_ball_exit R γ h0 t u hu) (abs_nonneg _)

/-- Stopped coordinate-exponential moments are continuous under the solution law. -/
theorem c16_continuous_stopped_exp_moment {d : ℕ}
    {ω : FieldPair d} (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (q R : ℝ) (hR : euclideanNorm x < R) :
    Continuous (fun s : ℝ => ∫ γ : Path d, Real.exp (q *
      (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : Vec d | euclideanNorm y < R} s.toNNReal γ)) i) ∂P) := by
  letI : IsProbabilityMeasure P := hP.1
  let U := {y : Vec d | euclideanNorm y < R}
  have hU : IsOpen U := isOpen_lt
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  apply continuous_of_dominated (bound := fun _ : Path d => Real.exp (|q| * R))
  · intro s
    exact ((c16_measurable_stopped_coordinate_exp U hU i q).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · intro s
    filter_upwards [hP.2.1] with γ hγ
    have h0 : euclideanNorm (γ 0) < R := by rw [hγ]; exact hR
    have hb := c16_exp_coordinate_before_ball_exit R q γ i h0 s.toNNReal
      (MarkovProcess.ContinuousPath.exitTimeTrunc U s.toNNReal γ) le_rfl
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb
  · exact integrable_const _
  · exact ae_of_all _ fun γ =>
      (c16_continuous_stopped_coordinate_exp U γ i q).comp continuous_real_toNNReal

/-- Time and solution-law integration commute for the stopped exponential. -/
theorem c16_stopped_exp_moment_integral_swap {d : ℕ}
    {ω : FieldPair d} (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (q R : ℝ) (hR : euclideanNorm x < R) (t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ), ∫ γ : Path d, Real.exp (q *
      (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : Vec d | euclideanNorm y < R} s.toNNReal γ)) i) ∂P) =
    ∫ γ : Path d, (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (q *
      (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : Vec d | euclideanNorm y < R} s.toNNReal γ)) i)) ∂P := by
  letI : IsProbabilityMeasure P := hP.1
  let U := {y : Vec d | euclideanNorm y < R}
  have hU : IsOpen U := isOpen_lt
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  let F : ℝ × Path d → ℝ := fun p => Real.exp (q *
    (p.2 (MarkovProcess.ContinuousPath.exitTimeTrunc U p.1.toNNReal p.2)) i)
  have hF : Measurable F := (c16_measurable_stopped_coordinate_exp U hU i q).comp
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  letI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) (t : ℝ))) := by
    rw [Set.uIoc_of_le t.coe_nonneg]
    infer_instance
  apply intervalIntegral_integral_swap
  apply Integrable.of_bound hF.aestronglyMeasurable (Real.exp (|q| * R))
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hF.norm measurable_const)).mpr
  filter_upwards [] with s
  filter_upwards [hP.2.1] with γ hγ
  have h0 : euclideanNorm (γ 0) < R := by rw [hγ]; exact hR
  have hb := c16_exp_coordinate_before_ball_exit R q γ i h0 s.toNNReal
    (MarkovProcess.ContinuousPath.exitTimeTrunc U s.toNNReal γ) le_rfl
  simpa only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb


open EinsteinRelation
open scoped BigOperators

/-- Candidate calculation for a coordinate exponential with arbitrary coefficients. -/
theorem c16_svGenerator_coordinate_exp {d : ℕ} (a : Vec d → Mat d)
    (b : Vec d → Vec d) (i : Fin d) (q : ℝ) (x : Vec d) :
    External.Draft.svGenerator a b (fun y => Real.exp (q * y i)) x =
      Real.exp (q * x i) * (q * b x i + (q ^ 2 / 2) * a x i i) := by
  let h : Vec d → ℝ := fun y => Real.exp (q * y i)
  have hh : ContDiff ℝ 2 h := (contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp
  have hderiv (x : Vec d) (j : Fin d) :
      fderiv ℝ h x (unitVector j) = h x * q * unitVector i j := by
    have hd := ((hasFDerivAt_apply (𝕜 := ℝ) i x).const_mul q).exp
    change fderiv ℝ (fun y : Vec d => Real.exp (q * y i)) x (unitVector j) = _
    simp only [hd.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.proj_apply]
    have he : unitVector j i = unitVector i j := by
      simp only [unitVector, Pi.single_apply, eq_comm]
    rw [he]
    ring
  have hsecond (x : Vec d) (j k : Fin d) :
      fderiv ℝ (fun y => fderiv ℝ h y (unitVector k)) x (unitVector j) =
        h x * q * unitVector i j * q * unitVector i k := by
    rw [show (fun y => fderiv ℝ h y (unitVector k)) =
      (fun y => h y * (q * unitVector i k)) from
      funext fun y => by rw [hderiv]; ring]
    rw [show fderiv ℝ (fun y => h y * (q * unitVector i k)) x = _ from
      ((hh.differentiable (by simp) x).hasFDerivAt.mul_const _).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hderiv]
    ring
  change External.Draft.svGenerator a b h x = _
  unfold External.Draft.svGenerator
  simp_rw [hsecond, hderiv]
  simp only [unitVector, Pi.single_apply, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- Uniform coefficient bounds control the coordinate-exponential generator. -/
theorem c16_svGenerator_coordinate_exp_le {d : ℕ} (a : Vec d → Mat d)
    (b : Vec d → Vec d) (i : Fin d) (q : ℝ) (x : Vec d) {Ma Mb : ℝ}
    (ha : |a x i i| ≤ Ma) (hb : |b x i| ≤ Mb) :
    External.Draft.svGenerator a b (fun y => Real.exp (q * y i)) x ≤
      Real.exp (q * x i) * (|q| * Mb + q ^ 2 / 2 * Ma) := by
  rw [c16_svGenerator_coordinate_exp]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  have hb' : q * b x i ≤ |q| * Mb := by
    calc
      q * b x i ≤ |q * b x i| := le_abs_self _
      _ = |q| * |b x i| := abs_mul _ _
      _ ≤ |q| * Mb := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  have ha' : q ^ 2 / 2 * a x i i ≤ q ^ 2 / 2 * Ma := by
    apply mul_le_mul_of_nonneg_left ((le_abs_self _).trans ha)
    positivity
  exact add_le_add hb' ha'

/-- Coefficient bounds also control the absolute coordinate-exponential generator. -/
theorem c16_svGenerator_coordinate_exp_abs_le {d : ℕ} (a : Vec d → Mat d)
    (b : Vec d → Vec d) (i : Fin d) (q : ℝ) (x : Vec d) {Ma Mb : ℝ}
    (ha : |a x i i| ≤ Ma) (hb : |b x i| ≤ Mb) :
    |External.Draft.svGenerator a b (fun y => Real.exp (q * y i)) x| ≤
      Real.exp (q * x i) * (|q| * Mb + q ^ 2 / 2 * Ma) := by
  rw [c16_svGenerator_coordinate_exp, abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  calc
    |q * b x i + q ^ 2 / 2 * a x i i| ≤
        |q * b x i| + |q ^ 2 / 2 * a x i i| := abs_add_le _ _
    _ = |q| * |b x i| + (q ^ 2 / 2) * |a x i i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ q ^ 2 / 2)]
    _ ≤ |q| * Mb + q ^ 2 / 2 * Ma := add_le_add
      (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
      (mul_le_mul_of_nonneg_left ha (by positivity))



/-- Both signed exponentials dominate the exponential of an absolute value. -/
theorem c16_exp_abs_le_signed (q z : ℝ) :
    Real.exp (q * |z|) ≤ Real.exp (q * z) + Real.exp (-q * z) := by
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_nonpos hz]
    have heq : q * -z = -q * z := by ring
    rw [heq]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)


open EinsteinRelation MeasureTheory
open scoped NNReal

theorem c16_integrable_coordinate_max_exp_nonpos {d : ℕ} (i : Fin d) (x : Vec d)
    (T : ℝ≥0) (P : Measure (Path d)) [IsFiniteMeasure P] (a : ℝ) (ha : a ≤ 0) :
    Integrable (fun γ : Path d => Real.exp (a *
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T))) P := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact (Real.continuous_exp.comp ((continuous_const : Continuous (fun _ : Path d => a)).mul
      (c16_continuous_coordinate_max i x T))).aestronglyMeasurable
  · filter_upwards [] with γ
    have hs : 0 ≤ sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T) := by
      apply Real.sSup_nonneg
      rintro y ⟨t, ht, rfl⟩
      exact abs_nonneg _
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa using Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg ha hs)

/-- A nonnegative stopped path dominates its integral up to the stopping time. -/
theorem c16_integral_until_le_stopped (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ t, 0 ≤ f t) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
    (∫ s in (0 : ℝ)..r, f s) ≤ ∫ s in (0 : ℝ)..t, f (min s r) := by
  let g : ℝ → ℝ := fun s => f (min s r)
  have hg : Continuous g := hf.comp (continuous_id.min continuous_const)
  have hgi : IntervalIntegrable g volume 0 t := hg.intervalIntegrable _ _
  have heq : (∫ s in (0 : ℝ)..r, f s) = ∫ s in (0 : ℝ)..r, g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hr] at hs
    have hs' : s ≤ r := hs.2
    simp [g, min_eq_left hs']
  rw [heq]
  apply intervalIntegral.integral_mono_interval le_rfl hr hrt _ hgi
  exact Filter.Eventually.of_forall fun s => hn _

/-- A generator bound integrates to a stopped-path Gronwall bound. -/
theorem c16_integral_generator_le_stopped (f g : ℝ → ℝ)
    (hg : Continuous g) (hgn : ∀ s, 0 ≤ g s) {C r t : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hrt : r ≤ t)
    (hfi : IntervalIntegrable f volume 0 r)
    (hfg : ∀ s ∈ Set.Icc 0 r, f s ≤ C * g s) :
    (∫ s in (0 : ℝ)..r, f s) ≤ C * ∫ s in (0 : ℝ)..t, g (min s r) := by
  calc
    (∫ s in (0 : ℝ)..r, f s) ≤ ∫ s in (0 : ℝ)..r, C * g s :=
      intervalIntegral.integral_mono_on hr hfi
        ((continuous_const.mul hg).intervalIntegrable _ _) hfg
    _ = C * ∫ s in (0 : ℝ)..r, g s := intervalIntegral.integral_const_mul C g
    _ ≤ C * ∫ s in (0 : ℝ)..t, g (min s r) :=
      mul_le_mul_of_nonneg_left (c16_integral_until_le_stopped g hg hgn hr hrt) hC

/-- A single nonnegative constant bounds the reduced coordinate-exponential generator. -/
theorem c16_reduced_coordinate_exp_generator_bound {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Vec d,
      External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i 0)
          (fun z => Real.exp (q * z i)) y ≤ C * Real.exp (q * y i) := by
  obtain ⟨Ma, ha⟩ := (reduced_svHypotheses hΛ hω i 0).2.2.1
  obtain ⟨Mb, hb⟩ := (reduced_svHypotheses hΛ hω i 0).2.2.2.2.2
  refine ⟨|q| * |Mb| + q ^ 2 / 2 * |Ma|, ?_, ?_⟩
  · positivity
  · intro y
    have h := c16_svGenerator_coordinate_exp_le (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i 0) i q y
      ((ha y i i).trans (le_abs_self Ma)) ((hb y i).trans (le_abs_self Mb))
    simpa only [mul_comm] using h

/-- On each ball, the absolute generator has a deterministic pathwise bound. -/
theorem c16_reduced_exp_generator_before_ball_exit_bound {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (q R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : Path d), euclideanNorm (γ 0) < R →
      ∀ t u : ℝ≥0, u ≤ MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : Vec d | euclideanNorm y < R} t γ →
      |External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0)
        (fun y => Real.exp (q * y i)) (γ u)| ≤ C := by
  obtain ⟨Ma, ha⟩ := (reduced_svHypotheses hΛ hω i 0).2.2.1
  obtain ⟨Mb, hb⟩ := (reduced_svHypotheses hΛ hω i 0).2.2.2.2.2
  let K : ℝ := |q| * |Mb| + q ^ 2 / 2 * |Ma|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨Real.exp (|q| * R) * K, mul_nonneg (Real.exp_nonneg _) hK, ?_⟩
  intro γ h0 t u hu
  calc
    |External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0)
        (fun y => Real.exp (q * y i)) (γ u)| ≤ Real.exp (q * (γ u) i) * K :=
      c16_svGenerator_coordinate_exp_abs_le _ _ i q _
        ((ha _ i i).trans (le_abs_self Ma)) ((hb _ i).trans (le_abs_self Mb))
    _ ≤ Real.exp (|q| * R) * K := mul_le_mul_of_nonneg_right
      (c16_exp_coordinate_before_ball_exit R q γ i h0 t u hu) hK

/-- A continuous stopped-moment estimate has an exponential bound. -/
theorem c16_integral_gronwall {E : ℝ → ℝ} {k T : ℝ}
    (hE : Continuous E) (hk : 0 ≤ k)
    (hineq : ∀ s ∈ Set.Icc (0 : ℝ) T,
      E s ≤ E 0 + k * (∫ u in 0..s, E u)) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, E s ≤ E 0 * Real.exp (k * s) := by
  let G := fun s => E 0 + k * (∫ u in 0..s, E u)
  have hd (s : ℝ) : HasDerivAt G (k * E s) s := by
    exact ((intervalIntegral.integral_hasDerivAt_right (hE.intervalIntegrable 0 s)
      (hE.stronglyMeasurableAtFilter _ _) hE.continuousAt).const_mul k).const_add _
  have hG : Continuous G := continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt
  have hb := le_gronwallBound_of_liminf_deriv_right_le
    (f := G) (f' := fun s => k * E s) (δ := E 0) (K := k) (ε := 0)
    (a := 0) (b := T) hG.continuousOn
    (fun s _ _ hr => (hd s).hasDerivWithinAt.liminf_right_slope_le hr)
    (by simp only [G, intervalIntegral.integral_same, mul_zero, add_zero]; exact le_rfl)
    (fun s hs => by
      simpa only [add_zero] using mul_le_mul_of_nonneg_left
        (hineq s ⟨hs.1, hs.2.le⟩) hk)
  intro s hs
  have hgs := hb s hs
  rw [gronwallBound_ε0, sub_zero] at hgs
  exact (hineq s hs).trans hgs

/-- Coordinate exponentials yield true martingales when stopped at a ball exit. -/
theorem c16_reduced_exp_ball_stopped_martingale {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (q R : ℝ) (hR : 0 < R) :
    Martingale (fun (t : ℝ≥0) (γ : External.Bass.Path d) =>
      External.Bass.compensatedTest (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0) (fun y => Real.exp (q * y i))
        (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : Vec d | euclideanNorm y < R} t (External.Bass.pathMeasurableEquiv d γ)) γ)
      (External.Bass.filtration d) (P.map (External.Bass.pathMeasurableEquiv d).symm) := by
  have hs := reduced_svHypotheses hΛ hω i 0
  obtain ⟨Ma, ha⟩ := hs.2.2.1
  obtain ⟨Mb, hb⟩ := hs.2.2.2.2.2
  exact External.Bass.c2_ball_stopped_martingale_map_symm hP hs.1.measurable
    hs.2.2.2.2.1 ha hb ((contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp) R hR

/-- The stopped compensated coordinate exponential has zero expectation. -/
theorem c16_reduced_exp_ball_stopped_expectation_zero {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (q R : ℝ) (hR : 0 < R) (t : ℝ≥0) :
    ∫ γ : External.Bass.Path d, External.Bass.compensatedTest (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i 0) (fun y => Real.exp (q * y i))
      (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : Vec d | euclideanNorm y < R} t (External.Bass.pathMeasurableEquiv d γ)) γ
      ∂(P.map (External.Bass.pathMeasurableEquiv d).symm) = 0 := by
  letI : IsProbabilityMeasure P := hP.1
  have hm := c16_reduced_exp_ball_stopped_martingale hΛ hω i hP q R hR
  have h := hm.setIntegral_eq (show (0 : ℝ≥0) ≤ t from bot_le) MeasurableSet.univ
  have hz (γ : External.Bass.Path d) :
      MarkovProcess.ContinuousPath.exitTimeTrunc {y : Vec d | euclideanNorm y < R}
        0 (External.Bass.pathMeasurableEquiv d γ) = 0 :=
    le_antisymm (MarkovProcess.ContinuousPath.exitTimeTrunc_le _ _ _) bot_le
  simpa [hz, External.Bass.compensatedTest] using h.symm

/-- The stopped compensated exponential is integrable and centered under the solution law. -/
theorem c16_reduced_exp_ball_stopped_centered {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (q R : ℝ) (hR : 0 < R) (t : ℝ≥0) :
    let M := fun γ : Path d => EinsteinRelation.compensatedTest
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0)) (fun y => Real.exp (q * y i))
      (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : Vec d | euclideanNorm y < R} t γ) γ
    Integrable M P ∧ ∫ γ, M γ ∂P = 0 := by
  let M := fun γ : External.Bass.Path d => External.Bass.compensatedTest
    (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)
    (fun y => Real.exp (q * y i))
    (MarkovProcess.ContinuousPath.exitTimeTrunc
      {y : Vec d | euclideanNorm y < R} t (External.Bass.pathMeasurableEquiv d γ)) γ
  have hi : Integrable M (P.map (External.Bass.pathMeasurableEquiv d).symm) :=
    (c16_reduced_exp_ball_stopped_martingale hΛ hω i hP q R hR).integrable t
  have hz : ∫ γ, M γ ∂(P.map (External.Bass.pathMeasurableEquiv d).symm) = 0 :=
    c16_reduced_exp_ball_stopped_expectation_zero hΛ hω i hP q R hR t
  rw [integral_map_equiv] at hz
  have hi' := (integrable_map_equiv (External.Bass.pathMeasurableEquiv d).symm M).mp hi
  constructor
  · simpa [M, Function.comp_def, External.Bass.compensatedTest_eq_frozen] using hi'
  · simpa [M, External.Bass.compensatedTest_eq_frozen] using hz

/-- The stopped moment equals its initial value plus the expected generator integral. -/
theorem c16_reduced_exp_stopped_moment_identity {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (q R : ℝ) (hR : euclideanNorm x < R) (t : ℝ≥0) :
    let U := {y : Vec d | euclideanNorm y < R}
    let F := fun γ : Path d => Real.exp (q *
      (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ)) i)
    let J := fun γ : Path d => ∫ u in (0 : ℝ)..
      (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ : ℝ),
      External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0) (fun y => Real.exp (q * y i))
        (γ u.toNNReal)
    Integrable J P ∧ (∫ γ, F γ ∂P) = Real.exp (q * x i) + ∫ γ, J γ ∂P := by
  letI : IsProbabilityMeasure P := hP.1
  let U := {y : Vec d | euclideanNorm y < R}
  let F := fun γ : Path d => Real.exp (q *
    (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ)) i)
  let J := fun γ : Path d => ∫ u in (0 : ℝ)..
    (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ : ℝ),
    External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i 0) (fun y => Real.exp (q * y i))
      (γ u.toNNReal)
  let M := fun γ : Path d => EinsteinRelation.compensatedTest
    (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i 0)) (fun y => Real.exp (q * y i))
    (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ) γ
  have hU : IsOpen U := isOpen_lt
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  have hF : Integrable F P := by
    have hFm : AEStronglyMeasurable F P := by
      simpa only [F, Function.comp_def, id_eq] using
        ((c16_measurable_stopped_coordinate_exp U hU i q).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    apply Integrable.of_bound hFm (Real.exp (|q| * R))
    filter_upwards [hP.2.1] with γ hγ
    have h0 : euclideanNorm (γ 0) < R := by rw [hγ]; exact hR
    have hb := c16_exp_coordinate_before_ball_exit R q γ i h0 t
      (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ) le_rfl
    simpa only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb
  have hRpos : 0 < R := (Real.sqrt_nonneg _).trans_lt hR
  have hM := c16_reduced_exp_ball_stopped_centered hΛ hω i hP q R hRpos t
  change Integrable M P ∧ (∫ γ, M γ ∂P) = 0 at hM
  have heq : J =ᵐ[P] fun γ => (F γ - Real.exp (q * x i)) - M γ := by
    filter_upwards [hP.2.1] with γ hγ
    simp only [J, F, M, EinsteinRelation.compensatedTest, hγ]
    ring
  have hJ : Integrable J P := ((hF.sub (integrable_const _)).sub hM.1).congr heq.symm
  refine ⟨hJ, ?_⟩
  have hJi : (∫ γ, J γ ∂P) = (∫ γ, F γ ∂P) - Real.exp (q * x i) := by
    calc
      _ = ∫ γ, (F γ - Real.exp (q * x i)) - M γ ∂P := integral_congr_ae heq
      _ = (∫ γ, F γ ∂P) - Real.exp (q * x i) := by
        have hsub := integral_sub (hF.sub (integrable_const (Real.exp (q * x i)))) hM.1
        simp only [Pi.sub_apply] at hsub
        rw [hsub, integral_sub hF (integrable_const _), hM.2]
        simp
  linarith

/-- Stopping at an earlier horizon agrees with truncating the later stopped time. -/
theorem c16_exitTimeTrunc_min {d : ℕ} (U : Set (Vec d)) (γ : Path d)
    (s t : ℝ≥0) :
    MarkovProcess.ContinuousPath.exitTimeTrunc U (min s t) γ =
      min s (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ) := by
  apply WithTop.coe_injective
  simp only [WithTop.coe_min, MarkovProcess.ContinuousPath.coe_exitTimeTrunc]
  exact min_left_comm _ _ _

/-- A pathwise stopped generator integral is dominated by the stopped exponential. -/
theorem c16_reduced_exp_stopped_generator_path_bound {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (Vec d)) (t : ℝ≥0) (γ : Path d),
      (∫ u in (0 : ℝ)..(MarkovProcess.ContinuousPath.exitTimeTrunc U t γ : ℝ),
        External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i 0) (fun y => Real.exp (q * y i))
          (γ u.toNNReal)) ≤ C * ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (q *
        (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U u.toNNReal γ)) i) := by
  obtain ⟨C, hC, hbound⟩ := c16_reduced_coordinate_exp_generator_bound hΛ hω i q
  refine ⟨C, hC, ?_⟩
  intro U t γ
  let r := MarkovProcess.ContinuousPath.exitTimeTrunc U t γ
  let f : ℝ → ℝ := fun u => External.Draft.svGenerator (reducedCoefficient ω)
    (forcedDrift (reducedCoefficient ω) i 0) (fun y => Real.exp (q * y i)) (γ u.toNNReal)
  let g : ℝ → ℝ := fun u => Real.exp (q * (γ u.toNNReal) i)
  have hg : Continuous g := Real.continuous_exp.comp (continuous_const.mul
    ((continuous_apply i).comp (γ.continuous.comp continuous_real_toNNReal)))
  have hs := reduced_svHypotheses hΛ hω i 0
  obtain ⟨Ma, ha⟩ := hs.2.2.1
  obtain ⟨Mb, hb⟩ := hs.2.2.2.2.2
  have hfi : IntervalIntegrable f volume 0 (r : ℝ) := by
    simpa only [f, External.Bass.generator_eq_svGenerator,
      External.Bass.pathMeasurableEquiv_symm_apply] using
      (External.Bass.intervalIntegrable_generator_path hs.1.measurable hs.2.2.2.2.1
        ha hb ((contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp)
        ((External.Bass.pathMeasurableEquiv d).symm γ) r)
  have hr : (r : ℝ) ≤ t := NNReal.coe_le_coe.mpr
    (MarkovProcess.ContinuousPath.exitTimeTrunc_le U t γ)
  have hbound' := c16_integral_generator_le_stopped f g hg (fun u => Real.exp_nonneg _)
    hC r.coe_nonneg hr hfi (fun u _ => hbound (γ u.toNNReal))
  refine hbound'.trans_eq ?_
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le t.coe_nonneg] at hu
  have hut : u.toNNReal ≤ t := by
    exact Real.toNNReal_le_iff_le_coe.2 hu.2
  have he := c16_exitTimeTrunc_min U γ u.toNNReal t
  rw [min_eq_left hut] at he
  have he' : ((MarkovProcess.ContinuousPath.exitTimeTrunc U u.toNNReal γ : ℝ≥0) : ℝ) =
      min u (r : ℝ) := by
    rw [he, NNReal.coe_min, Real.coe_toNNReal u hu.1]
  simp only [g, ← he', Real.toNNReal_coe]


/-- The time integral of the stopped exponential is integrable under the solution law. -/
theorem c16_integrable_stopped_exp_time_integral {d : ℕ}
    {ω : FieldPair d} (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (q R : ℝ) (hR : euclideanNorm x < R) (t : ℝ≥0) :
    Integrable (fun γ : Path d => ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (q *
      (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : Vec d | euclideanNorm y < R} s.toNNReal γ)) i)) P := by
  let : IsProbabilityMeasure P := hP.1
  let U := {y : Vec d | euclideanNorm y < R}
  have hU : IsOpen U := isOpen_lt
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  let F : ℝ × Path d → ℝ := fun p => Real.exp (q *
    (p.2 (MarkovProcess.ContinuousPath.exitTimeTrunc U p.1.toNNReal p.2)) i)
  have hF : Measurable F := (c16_measurable_stopped_coordinate_exp U hU i q).comp
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  letI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) := by infer_instance
  have hi : Integrable F ((volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))).prod P) := by
    apply Integrable.of_bound hF.aestronglyMeasurable (Real.exp (|q| * R))
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hF.norm measurable_const)).mpr
    filter_upwards [] with s
    filter_upwards [hP.2.1] with γ hγ
    have h0 : euclideanNorm (γ 0) < R := by rw [hγ]; exact hR
    have hb := c16_exp_coordinate_before_ball_exit R q γ i h0 s.toNNReal
      (MarkovProcess.ContinuousPath.exitTimeTrunc U s.toNNReal γ) le_rfl
    simpa only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb
  simpa only [F, intervalIntegral.integral_of_le t.coe_nonneg] using hi.integral_prod_right


/-- The stopped coordinate-exponential moment satisfies a uniform Gronwall inequality. -/
theorem c16_reduced_exp_stopped_moment_le {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (q : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, euclideanNorm x < R → ∀ t : ℝ≥0,
      (∫ γ : Path d, Real.exp (q *
        (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : Vec d | euclideanNorm y < R} t γ)) i) ∂P) ≤
        Real.exp (q * x i) * Real.exp (C * (t : ℝ)) := by
  let : IsProbabilityMeasure P := hP.1
  obtain ⟨C, hC, hbound⟩ := c16_reduced_exp_stopped_generator_path_bound hΛ hω i q
  refine ⟨C, hC, ?_⟩
  intro R hR t
  let U := {y : Vec d | euclideanNorm y < R}
  let E : ℝ → ℝ := fun s => ∫ γ : Path d, Real.exp (q *
    (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U s.toNNReal γ)) i) ∂P
  have hE : Continuous E := c16_continuous_stopped_exp_moment i hP q R hR
  have hE0 : E 0 = Real.exp (q * x i) := by
    have heq : (fun γ : Path d => Real.exp (q *
        (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U (0 : ℝ≥0) γ)) i)) =ᵐ[P]
        fun _ => Real.exp (q * x i) := by
      filter_upwards [hP.2.1] with γ hγ
      have hz : MarkovProcess.ContinuousPath.exitTimeTrunc U 0 γ = 0 :=
        le_antisymm (MarkovProcess.ContinuousPath.exitTimeTrunc_le _ _ _) bot_le
      simp [hz, hγ]
    simpa [E] using integral_congr_ae heq
  have hineq : ∀ s ∈ Set.Icc (0 : ℝ) (t : ℝ), E s ≤ E 0 + C * ∫ u in 0..s, E u := by
    intro s hs
    let v := s.toNNReal
    have hv : (v : ℝ) = s := Real.coe_toNNReal s hs.1
    have hid := c16_reduced_exp_stopped_moment_identity hΛ hω i hP q R hR v
    have hi := c16_integrable_stopped_exp_time_integral i hP q R hR v
    have hb := integral_mono_ae hid.1 (hi.const_mul C) (ae_of_all P (hbound U v))
    have hswap := c16_stopped_exp_moment_integral_swap i hP q R hR v
    rw [integral_const_mul, ← hswap] at hb
    have hm := hid.2
    have hh := add_le_add_left hb (Real.exp (q * x i))
    simp only [add_comm] at hh
    rw [← hm] at hh
    simpa only [E, hE0, hv] using hh
  have hg := c16_integral_gronwall hE hC hineq (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  simpa only [E, hE0, Real.toNNReal_coe] using hg


/-- Uniform exponential moments for stopped coordinate increments. -/
theorem c16_reduced_textbook_stopped_coordinate_exp_moment
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), euclideanNorm x < R → ∀ T : ℝ≥0,
      Integrable (fun γ : Path d => Real.exp (q *
        ((γ (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : Vec d | euclideanNorm y < R} T γ)) i - x i))) P ∧
      (∫ γ : Path d, Real.exp (q *
        ((γ (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : Vec d | euclideanNorm y < R} T γ)) i - x i)) ∂P)
        ≤ Real.exp (C * (T : ℝ)) := by
  let : IsProbabilityMeasure P := hP.1
  obtain ⟨C, hC, hb⟩ := c16_reduced_exp_stopped_moment_le hΛ hω i hP q
  refine ⟨C, hC, ?_⟩
  intro R hR T
  let U := {y : Vec d | euclideanNorm y < R}
  let F : Path d → ℝ := fun γ => Real.exp (q *
    (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U T γ)) i)
  have hU : IsOpen U := isOpen_lt
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  have hF : Integrable F P := by
    have hm : AEStronglyMeasurable F P := by
      simpa only [F, Function.comp_def, id_eq] using
        ((c16_measurable_stopped_coordinate_exp U hU i q).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    apply Integrable.of_bound hm (Real.exp (|q| * R))
    filter_upwards [hP.2.1] with γ hγ
    have h0 : euclideanNorm (γ 0) < R := by rw [hγ]; exact hR
    have hh := c16_exp_coordinate_before_ball_exit R q γ i h0 T
      (MarkovProcess.ContinuousPath.exitTimeTrunc U T γ) le_rfl
    simpa only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hh
  have heq (γ : Path d) : Real.exp (q *
      ((γ (MarkovProcess.ContinuousPath.exitTimeTrunc U T γ)) i - x i)) =
      Real.exp (-q * x i) * F γ := by
    dsimp [F]
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · exact (hF.const_mul _).congr (Filter.Eventually.of_forall fun γ => (heq γ).symm)
  · have he : (∫ γ : Path d, Real.exp (q *
        ((γ (MarkovProcess.ContinuousPath.exitTimeTrunc U T γ)) i - x i)) ∂P) =
        Real.exp (-q * x i) * ∫ γ, F γ ∂P := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall heq)
    rw [he]
    have h := mul_le_mul_of_nonneg_left (hb R hR T) (Real.exp_nonneg (-q * x i))
    have hc : Real.exp (-q * x i) * Real.exp (q * x i) = 1 := by
      rw [← Real.exp_add]
      have : -q * x i + q * x i = 0 := by ring
      rw [this, Real.exp_zero]
    simpa only [F, ← mul_assoc, hc, one_mul] using h

end EinsteinFull
