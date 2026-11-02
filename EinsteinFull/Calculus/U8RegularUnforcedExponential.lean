import EinsteinFull.Calculus.U6RegularUnforcedRealization
import EinsteinFull.Calculus.C16SourceExponentialMax
import EinsteinFull.Calculus.C9PhysicalPathBallExitExhaustion
import EinsteinFull.Calculus.U2GMPEnvironmentRealization
import EinsteinFull.Calculus.C16SourceExponentialMaxAssembly

noncomputable section
namespace EinsteinFull

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal Topology

/-- A uniform stopped exponential estimate passes to the endpoint of the same
continuous path law. The estimate is only needed for sufficiently large balls. -/
theorem u8_endpoint_exp_le_of_stopped {d : ℕ} (i : Fin d) (q : ℝ)
    (P : Measure (Path d)) (t : ℝ≥0) (B : ℝ)
    (hbound : ∀ᶠ n : ℕ in Filter.atTop,
      (∫⁻ γ : Path d, ENNReal.ofReal (Real.exp (q *
        (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : Vec d | euclideanNorm y < (n + 1 : ℝ)} t γ)) i)) ∂P) ≤
        ENNReal.ofReal B) :
    (∫⁻ γ : Path d, ENNReal.ofReal (Real.exp (q * (γ t) i)) ∂P) ≤
      ENNReal.ofReal B := by
  let U : ℕ → Set (Vec d) := fun n => {y | euclideanNorm y < (n + 1 : ℝ)}
  let F : ℕ → Path d → ℝ := fun n γ => Real.exp (q *
    (γ (MarkovProcess.ContinuousPath.exitTimeTrunc (U n) t γ)) i)
  let G : Path d → ℝ := fun γ => Real.exp (q * (γ t) i)
  have hU (n : ℕ) : IsOpen (U n) := isOpen_lt
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  have hFm (n : ℕ) : Measurable (F n) := by
    simpa only [F, Function.comp_def, id_eq] using
      (c16_measurable_stopped_coordinate_exp (U n) (hU n) i q).comp
        (measurable_const.prodMk measurable_id)
  have hlim (γ : Path d) : ∀ᶠ n : ℕ in Filter.atTop, F n γ = G γ := by
    filter_upwards [Blueprint.physical_path_euclidean_ball_exit_exhaustion γ t] with n hn
    simp only [F, G, U, hn t le_rfl]
  have hfatou := lintegral_liminf_le' (μ := P) (u := (Filter.atTop : Filter ℕ))
    (fun n => (hFm n).aemeasurable.ennreal_ofReal)
  have hlim' (γ : Path d) : Filter.liminf (fun n => ENNReal.ofReal (F n γ)) Filter.atTop =
      ENNReal.ofReal (G γ) := by
    rw [Filter.liminf_congr ((hlim γ).mono fun n hn => by rw [hn])]
    exact Filter.liminf_const _
  simp only [hlim'] at hfatou
  exact hfatou.trans (by
    calc
      _ ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal B) Filter.atTop :=
        Filter.liminf_le_liminf hbound
      _ = _ := Filter.liminf_const _)

theorem u8_continuous_stopped_exp_moment {d : ℕ}
    {ω : FieldPair d} (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (ω.1) (physicalDrift ω i 0)) x P)
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
theorem u8_stopped_exp_moment_integral_swap {d : ℕ}
    {ω : FieldPair d} (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (ω.1) (physicalDrift ω i 0)) x P)
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


theorem u8_physical_coordinate_exp_generator_bound {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Vec d,
      External.Draft.svGenerator (ω.1)
          (physicalDrift ω i 0)
          (fun z => Real.exp (q * z i)) y ≤ C * Real.exp (q * y i) := by
  obtain ⟨Ma, ha⟩ := (physical_svHypotheses hΛ hω i 0).2.2.1
  obtain ⟨Mb, hb⟩ := (physical_svHypotheses hΛ hω i 0).2.2.2.2.2
  refine ⟨|q| * |Mb| + q ^ 2 / 2 * |Ma|, ?_, ?_⟩
  · positivity
  · intro y
    have h := c16_svGenerator_coordinate_exp_le (ω.1)
      (physicalDrift ω i 0) i q y
      ((ha y i i).trans (le_abs_self Ma)) ((hb y i).trans (le_abs_self Mb))
    simpa only [mul_comm] using h



theorem u8_physical_exp_ball_stopped_martingale {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (ω.1) (physicalDrift ω i 0)) x P)
    (q R : ℝ) (hR : 0 < R) :
    Martingale (fun (t : ℝ≥0) (γ : External.Bass.Path d) =>
      External.Bass.compensatedTest (ω.1)
        (physicalDrift ω i 0) (fun y => Real.exp (q * y i))
        (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : Vec d | euclideanNorm y < R} t (External.Bass.pathMeasurableEquiv d γ)) γ)
      (External.Bass.filtration d) (P.map (External.Bass.pathMeasurableEquiv d).symm) := by
  have hs := physical_svHypotheses hΛ hω i 0
  obtain ⟨Ma, ha⟩ := hs.2.2.1
  obtain ⟨Mb, hb⟩ := hs.2.2.2.2.2
  exact External.Bass.c2_ball_stopped_martingale_map_symm hP (by
      letI : MeasurableSpace (Vec d) := MeasurableSpace.pi
      letI : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
      exact hs.1.measurable)
    hs.2.2.2.2.1 ha hb ((contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp) R hR

/-- The stopped compensated coordinate exponential has zero expectation. -/
theorem u8_physical_exp_ball_stopped_expectation_zero {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (ω.1) (physicalDrift ω i 0)) x P)
    (q R : ℝ) (hR : 0 < R) (t : ℝ≥0) :
    ∫ γ : External.Bass.Path d, External.Bass.compensatedTest (ω.1)
      (physicalDrift ω i 0) (fun y => Real.exp (q * y i))
      (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : Vec d | euclideanNorm y < R} t (External.Bass.pathMeasurableEquiv d γ)) γ
      ∂(P.map (External.Bass.pathMeasurableEquiv d).symm) = 0 := by
  letI : IsProbabilityMeasure P := hP.1
  have hm := u8_physical_exp_ball_stopped_martingale hΛ hω i hP q R hR
  have h := hm.setIntegral_eq (show (0 : ℝ≥0) ≤ t from bot_le) MeasurableSet.univ
  have hz (γ : External.Bass.Path d) :
      MarkovProcess.ContinuousPath.exitTimeTrunc {y : Vec d | euclideanNorm y < R}
        0 (External.Bass.pathMeasurableEquiv d γ) = 0 :=
    le_antisymm (MarkovProcess.ContinuousPath.exitTimeTrunc_le _ _ _) bot_le
  simpa [hz, External.Bass.compensatedTest] using h.symm

/-- The stopped compensated exponential is integrable and centered under the solution law. -/
theorem u8_physical_exp_ball_stopped_centered {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (ω.1) (physicalDrift ω i 0)) x P)
    (q R : ℝ) (hR : 0 < R) (t : ℝ≥0) :
    let M := fun γ : Path d => EinsteinRelation.compensatedTest
      (External.Draft.svGenerator (ω.1)
        (physicalDrift ω i 0)) (fun y => Real.exp (q * y i))
      (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : Vec d | euclideanNorm y < R} t γ) γ
    Integrable M P ∧ ∫ γ, M γ ∂P = 0 := by
  let M := fun γ : External.Bass.Path d => External.Bass.compensatedTest
    (ω.1) (physicalDrift ω i 0)
    (fun y => Real.exp (q * y i))
    (MarkovProcess.ContinuousPath.exitTimeTrunc
      {y : Vec d | euclideanNorm y < R} t (External.Bass.pathMeasurableEquiv d γ)) γ
  have hi : Integrable M (P.map (External.Bass.pathMeasurableEquiv d).symm) :=
    (u8_physical_exp_ball_stopped_martingale hΛ hω i hP q R hR).integrable t
  have hz : ∫ γ, M γ ∂(P.map (External.Bass.pathMeasurableEquiv d).symm) = 0 :=
    u8_physical_exp_ball_stopped_expectation_zero hΛ hω i hP q R hR t
  rw [integral_map_equiv] at hz
  have hi' := (integrable_map_equiv (External.Bass.pathMeasurableEquiv d).symm M).mp hi
  constructor
  · simpa [M, Function.comp_def, External.Bass.compensatedTest_eq_frozen] using hi'
  · simpa [M, External.Bass.compensatedTest_eq_frozen] using hz

/-- The stopped moment equals its initial value plus the expected generator integral. -/
theorem u8_physical_exp_stopped_moment_identity {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (ω.1) (physicalDrift ω i 0)) x P)
    (q R : ℝ) (hR : euclideanNorm x < R) (t : ℝ≥0) :
    let U := {y : Vec d | euclideanNorm y < R}
    let F := fun γ : Path d => Real.exp (q *
      (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ)) i)
    let J := fun γ : Path d => ∫ u in (0 : ℝ)..
      (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ : ℝ),
      External.Draft.svGenerator (ω.1)
        (physicalDrift ω i 0) (fun y => Real.exp (q * y i))
        (γ u.toNNReal)
    Integrable J P ∧ (∫ γ, F γ ∂P) = Real.exp (q * x i) + ∫ γ, J γ ∂P := by
  letI : IsProbabilityMeasure P := hP.1
  let U := {y : Vec d | euclideanNorm y < R}
  let F := fun γ : Path d => Real.exp (q *
    (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ)) i)
  let J := fun γ : Path d => ∫ u in (0 : ℝ)..
    (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ : ℝ),
    External.Draft.svGenerator (ω.1)
      (physicalDrift ω i 0) (fun y => Real.exp (q * y i))
      (γ u.toNNReal)
  let M := fun γ : Path d => EinsteinRelation.compensatedTest
    (External.Draft.svGenerator (ω.1)
      (physicalDrift ω i 0)) (fun y => Real.exp (q * y i))
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
  have hM := u8_physical_exp_ball_stopped_centered hΛ hω i hP q R hRpos t
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



theorem u8_physical_exp_stopped_generator_path_bound {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (Vec d)) (t : ℝ≥0) (γ : Path d),
      (∫ u in (0 : ℝ)..(MarkovProcess.ContinuousPath.exitTimeTrunc U t γ : ℝ),
        External.Draft.svGenerator (ω.1)
          (physicalDrift ω i 0) (fun y => Real.exp (q * y i))
          (γ u.toNNReal)) ≤ C * ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (q *
        (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U u.toNNReal γ)) i) := by
  obtain ⟨C, hC, hbound⟩ := u8_physical_coordinate_exp_generator_bound hΛ hω i q
  refine ⟨C, hC, ?_⟩
  intro U t γ
  let r := MarkovProcess.ContinuousPath.exitTimeTrunc U t γ
  let f : ℝ → ℝ := fun u => External.Draft.svGenerator (ω.1)
    (physicalDrift ω i 0) (fun y => Real.exp (q * y i)) (γ u.toNNReal)
  let g : ℝ → ℝ := fun u => Real.exp (q * (γ u.toNNReal) i)
  have hg : Continuous g := Real.continuous_exp.comp (continuous_const.mul
    ((continuous_apply i).comp (γ.continuous.comp continuous_real_toNNReal)))
  have hs := physical_svHypotheses hΛ hω i 0
  obtain ⟨Ma, ha⟩ := hs.2.2.1
  obtain ⟨Mb, hb⟩ := hs.2.2.2.2.2
  have hfi : IntervalIntegrable f volume 0 (r : ℝ) := by
    simpa only [f, External.Bass.generator_eq_svGenerator,
      External.Bass.pathMeasurableEquiv_symm_apply] using
      (External.Bass.intervalIntegrable_generator_path
        (by
          letI : MeasurableSpace (Vec d) := MeasurableSpace.pi
          letI : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
          exact hs.1.measurable) hs.2.2.2.2.1
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
theorem u8_integrable_stopped_exp_time_integral {d : ℕ}
    {ω : FieldPair d} (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (ω.1) (physicalDrift ω i 0)) x P)
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
theorem u8_physical_exp_stopped_moment_le {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (q : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {x : Vec d} {P : Measure (Path d)},
      SolvesMartingaleProblem (External.Draft.svGenerator
        (ω.1) (physicalDrift ω i 0)) x P → ∀ R : ℝ, euclideanNorm x < R → ∀ t : ℝ≥0,
      (∫ γ : Path d, Real.exp (q *
        (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : Vec d | euclideanNorm y < R} t γ)) i) ∂P) ≤
        Real.exp (q * x i) * Real.exp (C * (t : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := u8_physical_exp_stopped_generator_path_bound hΛ hω i q
  refine ⟨C, hC, ?_⟩
  intro x P hP R hR t
  let : IsProbabilityMeasure P := hP.1
  let U := {y : Vec d | euclideanNorm y < R}
  let E : ℝ → ℝ := fun s => ∫ γ : Path d, Real.exp (q *
    (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U s.toNNReal γ)) i) ∂P
  have hE : Continuous E := u8_continuous_stopped_exp_moment i hP q R hR
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
    have hid := u8_physical_exp_stopped_moment_identity hΛ hω i hP q R hR v
    have hi := u8_integrable_stopped_exp_time_integral i hP q R hR v
    have hb := integral_mono_ae hid.1 (hi.const_mul C) (ae_of_all P (hbound U v))
    have hswap := u8_stopped_exp_moment_integral_swap i hP q R hR v
    rw [integral_const_mul, ← hswap] at hb
    have hm := hid.2
    have hh := add_le_add_left hb (Real.exp (q * x i))
    simp only [add_comm] at hh
    rw [← hm] at hh
    simpa only [E, hE0, hv] using hh
  have hg := c16_integral_gronwall hE hC hineq (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  simpa only [E, hE0, Real.toNNReal_coe] using hg


/-- Uniform exponential moments for stopped coordinate increments. -/
theorem u8_physical_textbook_stopped_coordinate_exp_moment
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d)
    (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x : Vec d} {P : Measure (Path d)},
      SolvesMartingaleProblem (External.Draft.svGenerator
        (ω.1) (physicalDrift ω i 0)) x P → ∀ (R : ℝ), euclideanNorm x < R → ∀ T : ℝ≥0,
      Integrable (fun γ : Path d => Real.exp (q *
        ((γ (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : Vec d | euclideanNorm y < R} T γ)) i - x i))) P ∧
      (∫ γ : Path d, Real.exp (q *
        ((γ (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : Vec d | euclideanNorm y < R} T γ)) i - x i)) ∂P)
        ≤ Real.exp (C * (T : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := u8_physical_exp_stopped_moment_le hΛ hω i q
  refine ⟨C, hC, ?_⟩
  intro x P hP R hR T
  let : IsProbabilityMeasure P := hP.1
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
    have h := mul_le_mul_of_nonneg_left (hb hP R hR T) (Real.exp_nonneg (-q * x i))
    have hc : Real.exp (-q * x i) * Real.exp (q * x i) = 1 := by
      rw [← Real.exp_add]
      have : -q * x i + q * x i = 0 := by ring
      rw [this, Real.exp_zero]
    simpa only [F, ← mul_assoc, hc, one_mul] using h


theorem u8_textbook_coordinate_exp_moment
    {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d}
    (hω : IsRegular Λ ω) (i : Fin d) (q : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x : EinsteinRelation.Vec d} {P : Measure (Path d)},
      SolvesMartingaleProblem (External.Draft.svGenerator (ω.1) (physicalDrift ω i 0)) x P →
      ∀ t : ℝ≥0, Integrable (fun γ : Path d => Real.exp (q * (γ t) i)) P ∧
        (∫ γ : Path d, Real.exp (q * (γ t) i) ∂P) ≤
          Real.exp (q * x i) * Real.exp (C * (t : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ :=
    u8_physical_exp_stopped_moment_le hΛ hω i q
  refine ⟨C, hC, ?_⟩
  intro x P hP t
  let : IsProbabilityMeasure P := hP.1
  let U : ℕ → Set (EinsteinRelation.Vec d) := fun n => {y | euclideanNorm y < (n + 1 : ℝ)}
  let F : ℕ → Path d → ℝ := fun n γ => Real.exp (q *
    (γ (MarkovProcess.ContinuousPath.exitTimeTrunc (U n) t γ)) i)
  let G : Path d → ℝ := fun γ => Real.exp (q * (γ t) i)
  let B := Real.exp (q * x i) * Real.exp (C * (t : ℝ))
  have hU (n : ℕ) : IsOpen (U n) := isOpen_lt
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  have hFm (n : ℕ) : Measurable (F n) := by
    simpa only [F, Function.comp_def, id_eq] using
      (c16_measurable_stopped_coordinate_exp (U n) (hU n) i q).comp
        (measurable_const.prodMk measurable_id)
  have hGm : AEStronglyMeasurable G P := by
    exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_apply i).comp (continuous_eval_const t)))).measurable.aestronglyMeasurable
  have hlim (γ : Path d) : ∀ᶠ n : ℕ in atTop, F n γ = G γ := by
    filter_upwards [Blueprint.physical_path_euclidean_ball_exit_exhaustion γ t] with n hn
    simp only [F, G, U, hn t le_rfl]
  have hlarge : ∀ᶠ n : ℕ in atTop, euclideanNorm x < (n + 1 : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (euclideanNorm x)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hFint (n : ℕ) (hn : euclideanNorm x < (n + 1 : ℝ)) : Integrable (F n) P := by
    apply Integrable.of_bound (hFm n).aestronglyMeasurable (Real.exp (|q| * (n + 1)))
    filter_upwards [hP.2.1] with γ hγ
    have h0 : euclideanNorm (γ 0) < (n + 1 : ℝ) := by rw [hγ]; exact hn
    have hh := c16_exp_coordinate_before_ball_exit (n + 1) q γ i h0 t
      (MarkovProcess.ContinuousPath.exitTimeTrunc (U n) t γ) le_rfl
    simpa only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hh
  have hfatou := lintegral_liminf_le' (μ := P) (u := (atTop : Filter ℕ))
    (fun n => (hFm n).aemeasurable.ennreal_ofReal)
  have hlim' (γ : Path d) : liminf (fun n => ENNReal.ofReal (F n γ)) atTop =
      ENNReal.ofReal (G γ) := by
    rw [Filter.liminf_congr ((hlim γ).mono fun n hn => by rw [hn])]
    exact Filter.liminf_const _
  simp only [hlim'] at hfatou
  have hle : ∀ᶠ n : ℕ in atTop, (∫⁻ γ, ENNReal.ofReal (F n γ) ∂P) ≤ ENNReal.ofReal B := by
    filter_upwards [hlarge] with n hn
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint n hn)
      (ae_of_all _ fun γ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (hbound hP (n + 1) hn t)
  have hL : (∫⁻ γ, ENNReal.ofReal (G γ) ∂P) ≤ ENNReal.ofReal B := hfatou.trans (by
    calc
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal B) atTop := Filter.liminf_le_liminf hle
      _ = _ := Filter.liminf_const _)
  have hGi : Integrable G P := ⟨hGm,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun γ => (Real.exp_pos _).le)).2
      (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hGi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hGi
    (ae_of_all _ fun γ => (Real.exp_pos _).le)] at hL
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le
    (Real.exp_pos _).le)).mp hL

/-- Exponential moments of coordinate displacements, uniformly over starts and laws. -/
theorem u8_textbook_coordinate_increment_exp_moment
    {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d}
    (hω : IsRegular Λ ω) (i : Fin d) (q : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x : EinsteinRelation.Vec d} {P : Measure (Path d)},
      SolvesMartingaleProblem (External.Draft.svGenerator (ω.1) (physicalDrift ω i 0)) x P →
      ∀ t : ℝ≥0, Integrable (fun γ : Path d => Real.exp (q * ((γ t) i - x i))) P ∧
        (∫ γ : Path d, Real.exp (q * ((γ t) i - x i)) ∂P) ≤ Real.exp (C * (t : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := u8_textbook_coordinate_exp_moment hΛ hω i q
  refine ⟨C, hC, ?_⟩
  intro x P hP t
  obtain ⟨hF, hbound⟩ := hb hP t
  have heq (γ : Path d) : Real.exp (q * ((γ t) i - x i)) =
      Real.exp (-q * x i) * Real.exp (q * (γ t) i) := by
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · exact (hF.const_mul _).congr (Filter.Eventually.of_forall fun γ => (heq γ).symm)
  · have he : (∫ γ : Path d, Real.exp (q * ((γ t) i - x i)) ∂P) =
        Real.exp (-q * x i) * ∫ γ : Path d, Real.exp (q * (γ t) i) ∂P := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall heq)
    rw [he]
    have h := mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg (-q * x i))
    have hc : Real.exp (-q * x i) * Real.exp (q * x i) = 1 := by
      rw [← Real.exp_add]
      have : -q * x i + q * x i = 0 := by ring
      rw [this, Real.exp_zero]
    simpa only [← mul_assoc, hc, one_mul] using h



/-- Uniform exponential increments for the actual unforced physical kernel. -/
theorem u8_regular_unforced_kernel_coordinate_exponential_increment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (i : Fin d) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (a * ((y - x) i)))
        ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) ≤
      ENNReal.ofReal (Real.exp (C * (t : ℝ))) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  obtain ⟨C, hC, hb⟩ := u8_textbook_coordinate_increment_exp_moment hΛpos hω i a
  obtain ⟨K, hK, hfdd, hmp⟩ := u6_regular_unforced_continuous_kernel_and_mp hd ω Λ hΛ hω
  letI : IsMarkovKernel K := hK
  refine ⟨C + 1, by linarith, ?_⟩
  intro t x
  have hmarg (s : ℝ≥0) : (K x).map (pathPosition s) =
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω s x := by
    have h := congrArg (fun k => k x)
      (SubdiffusiveProcess.Section10.realization_map_eval
        (u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω)
        (u2_regular_kernel_conservative hd ω 0 Λ hΛ hω) K hfdd s)
    rw [← Kernel.map_apply K (measurable_pathPosition s)]
    exact h
  have hac (s : ℝ≥0) (hs : 0 < s) :
      (K x).map (pathPosition s) ≪ (volume : Measure (Vec d)) := by
    rw [hmarg s]
    obtain ⟨M, p, hM, hp, hpb, hrep⟩ :=
      u2_regular_unforced_kernel_bounded_density hd ω Λ hΛ hω s hs
    rw [hrep x]
    exact withDensity_absolutelyContinuous _ _
  have hocc := u2_averaged_occupation_ac_of_marginals (K x) hac
  have hp0 := c4_textbook_solves_of_physical_and_averaged_occupation
    hΛpos hω (firstCoordinateIndex hd) 0 (hmp x) hocc
  have hdrift : physicalDrift ω i 0 = physicalDrift ω (firstCoordinateIndex hd) 0 := by
    funext y j
    simp [physicalDrift, forcedDrift]
  have hp : SolvesMartingaleProblem (External.Draft.svGenerator (ω.1)
      (physicalDrift ω i 0)) x (K x) := by rw [hdrift]; exact hp0
  obtain ⟨hi, hbound⟩ := hb hp t
  have hf : Continuous (fun y : Vec d => Real.exp (a * (y i - x i))) :=
    Real.continuous_exp.comp (continuous_const.mul ((continuous_apply i).sub continuous_const))
  have hint : Integrable (fun y : Vec d => Real.exp (a * (y i - x i)))
      (u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) := by
    rw [← hmarg t]
    exact (integrable_map_measure hf.aestronglyMeasurable
      (measurable_pathPosition t).aemeasurable).2 hi
  have he : (∫ y : Vec d, Real.exp (a * (y i - x i)) ∂
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) ≤ Real.exp (C * (t : ℝ)) := by
    rw [← hmarg t, integral_map (measurable_pathPosition t).aemeasurable hf.aestronglyMeasurable]
    exact hbound
  have hC' : Real.exp (C * (t : ℝ)) ≤ Real.exp ((C + 1) * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [t.coe_nonneg]
  have hlin := ENNReal.ofReal_le_ofReal (he.trans hC')
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => (Real.exp_pos _).le)] at hlin
  simpa only [Pi.sub_apply] using hlin

/-- Uniform exponential increments for the actual unforced physical kernel. -/
theorem u8_regular_unforced_kernel_exponential_increment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (a * ((y - x) (firstCoordinateIndex hd))))
        ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) ≤
      ENNReal.ofReal (Real.exp (C * (t : ℝ))) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let i := firstCoordinateIndex hd
  obtain ⟨C, hC, hb⟩ := u8_textbook_coordinate_increment_exp_moment hΛpos hω i a
  obtain ⟨K, hK, hfdd, hmp⟩ := u6_regular_unforced_continuous_kernel_and_mp hd ω Λ hΛ hω
  letI : IsMarkovKernel K := hK
  refine ⟨C + 1, by linarith, ?_⟩
  intro t x
  have hmarg (s : ℝ≥0) : (K x).map (pathPosition s) =
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω s x := by
    have h := congrArg (fun k => k x)
      (SubdiffusiveProcess.Section10.realization_map_eval
        (u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω)
        (u2_regular_kernel_conservative hd ω 0 Λ hΛ hω) K hfdd s)
    rw [← Kernel.map_apply K (measurable_pathPosition s)]
    exact h
  have hac (s : ℝ≥0) (hs : 0 < s) :
      (K x).map (pathPosition s) ≪ (volume : Measure (Vec d)) := by
    rw [hmarg s]
    obtain ⟨M, p, hM, hp, hpb, hrep⟩ :=
      u2_regular_unforced_kernel_bounded_density hd ω Λ hΛ hω s hs
    rw [hrep x]
    exact withDensity_absolutelyContinuous _ _
  have hocc := u2_averaged_occupation_ac_of_marginals (K x) hac
  have hp := c4_textbook_solves_of_physical_and_averaged_occupation
    hΛpos hω i 0 (hmp x) hocc
  obtain ⟨hi, hbound⟩ := hb hp t
  have hf : Continuous (fun y : Vec d => Real.exp (a * (y i - x i))) :=
    Real.continuous_exp.comp (continuous_const.mul ((continuous_apply i).sub continuous_const))
  have hint : Integrable (fun y : Vec d => Real.exp (a * (y i - x i)))
      (u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) := by
    rw [← hmarg t]
    exact (integrable_map_measure hf.aestronglyMeasurable
      (measurable_pathPosition t).aemeasurable).2 hi
  have he : (∫ y : Vec d, Real.exp (a * (y i - x i)) ∂
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) ≤ Real.exp (C * (t : ℝ)) := by
    rw [← hmarg t, integral_map (measurable_pathPosition t).aemeasurable hf.aestronglyMeasurable]
    exact hbound
  have hC' : Real.exp (C * (t : ℝ)) ≤ Real.exp ((C + 1) * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [t.coe_nonneg]
  have hlin := ENNReal.ofReal_le_ofReal (he.trans hC')
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => (Real.exp_pos _).le)] at hlin
  simpa only [Pi.sub_apply, i] using hlin

/-- Absolute exponential increments for the actual unforced physical kernel. -/
theorem u8_regular_unforced_kernel_absolute_exponential_increment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (|a| * |(y - x) (firstCoordinateIndex hd)|))
        ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) ≤
      ENNReal.ofReal (2 * Real.exp (C * (t : ℝ))) := by
  obtain ⟨C₁, hC₁, h₁⟩ :=
    u8_regular_unforced_kernel_exponential_increment hd ω Λ hΛ hω |a|
  obtain ⟨C₂, hC₂, h₂⟩ :=
    u8_regular_unforced_kernel_exponential_increment hd ω Λ hΛ hω (-|a|)
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro t x
  let i := firstCoordinateIndex hd
  let μ := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x
  have hm : Measurable (fun y : Vec d =>
      ENNReal.ofReal (Real.exp (|a| * ((y - x) i)))) :=
    (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_apply i).sub continuous_const))).measurable.ennreal_ofReal
  have hpoint (y : Vec d) :
      ENNReal.ofReal (Real.exp (|a| * |(y - x) i|)) ≤
      ENNReal.ofReal (Real.exp (|a| * ((y - x) i))) +
        ENNReal.ofReal (Real.exp (-|a| * ((y - x) i))) := by
    rcases le_total 0 ((y - x) i) with h | h
    · rw [abs_of_nonneg h]
      exact le_add_right le_rfl
    · rw [abs_of_nonpos h]
      have he : |a| * -((y - x) i) = -|a| * ((y - x) i) := by ring
      rw [he]
      exact le_add_left le_rfl
  have hbound₁ : Real.exp (C₁ * (t : ℝ)) ≤ Real.exp (max C₁ C₂ * (t : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) t.coe_nonneg)
  have hbound₂ : Real.exp (C₂ * (t : ℝ)) ≤ Real.exp (max C₁ C₂ * (t : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) t.coe_nonneg)
  calc
    (∫⁻ y, ENNReal.ofReal (Real.exp (|a| * |(y - x) i|)) ∂μ) ≤
        ∫⁻ y, (ENNReal.ofReal (Real.exp (|a| * ((y - x) i))) +
          ENNReal.ofReal (Real.exp (-|a| * ((y - x) i)))) ∂μ :=
      lintegral_mono hpoint
    _ = (∫⁻ y, ENNReal.ofReal (Real.exp (|a| * ((y - x) i))) ∂μ) +
        ∫⁻ y, ENNReal.ofReal (Real.exp (-|a| * ((y - x) i))) ∂μ :=
      lintegral_add_left hm _
    _ ≤ ENNReal.ofReal (Real.exp (max C₁ C₂ * (t : ℝ))) +
        ENNReal.ofReal (Real.exp (max C₁ C₂ * (t : ℝ))) :=
      add_le_add ((h₁ t x).trans (ENNReal.ofReal_le_ofReal hbound₁))
        ((h₂ t x).trans (ENNReal.ofReal_le_ofReal hbound₂))
    _ = ENNReal.ofReal (2 * Real.exp (max C₁ C₂ * (t : ℝ))) := by
      rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
      congr 1 <;> ring

/-- Euclidean exponential increments for the actual unforced kernel. -/
theorem u8_regular_unforced_kernel_euclidean_exponential_increment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (|a| * euclideanNorm (y - x)))
        ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) ≤
      ENNReal.ofReal (C * Real.exp (C * (t : ℝ))) := by
  let q : ℝ := |a| * d
  have hq : 0 ≤ q := mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have hb (i : Fin d) (s : Bool) :=
    u8_regular_unforced_kernel_coordinate_exponential_increment hd ω Λ hΛ hω i
      (if s then q else -q)
  choose B hB hbound using hb
  let D : ℝ := 1 + ∑ i : Fin d, (B i true + B i false)
  let C : ℝ := D + 2 * d
  have hD : 0 < D := by
    dsimp [D]
    have hs : 0 ≤ ∑ i : Fin d, (B i true + B i false) :=
      Finset.sum_nonneg fun i _ => add_nonneg (hB i true).le (hB i false).le
    linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hBD (i : Fin d) (s : Bool) : B i s ≤ D := by
    have hs := Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin d => B i true + B i false)
      (fun j _ => add_nonneg (hB j true).le (hB j false).le) (Finset.mem_univ i)
    have ht := hB i true
    have hf := hB i false
    cases s <;> simp only [D] <;> linarith
  refine ⟨C, hC, ?_⟩
  intro t x
  let μ := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x
  let F : Fin d → Bool → Vec d → ℝ≥0∞ := fun i s y =>
    ENNReal.ofReal (Real.exp ((if s then q else -q) * ((y - x) i)))
  have hm (i : Fin d) (s : Bool) : Measurable (F i s) :=
    (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_apply i).sub continuous_const))).measurable.ennreal_ofReal
  have hpoint (y : Vec d) : ENNReal.ofReal (Real.exp (|a| * euclideanNorm (y - x))) ≤
      ∑ i : Fin d, (F i true y + F i false y) := by
    obtain ⟨i, hi⟩ := c16_max_exists_coord_ge (by omega : 1 ≤ d)
      (y := y - x) (R := euclideanNorm (y - x)) le_rfl
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hnorm : |a| * euclideanNorm (y - x) ≤ q * |(y - x) i| := by
      dsimp [q]
      have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hdpos).mp hi) (abs_nonneg a)
      simpa only [Pi.sub_apply, mul_assoc, mul_comm, mul_left_comm] using h
    have he := (Real.exp_le_exp.mpr hnorm).trans
      (c16_max_exp_ge hq (le_refl |(y - x) i|))
    have he' := ENNReal.ofReal_le_ofReal he
    rw [ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)] at he'
    apply he'.trans
    simpa [F] using
      (Finset.single_le_sum (f := fun j : Fin d => F j true y + F j false y)
        (fun j _ => bot_le) (Finset.mem_univ i))
  have hi (i : Fin d) (s : Bool) : (∫⁻ y, F i s y ∂μ) ≤
      ENNReal.ofReal (Real.exp (C * (t : ℝ))) := by
    apply (hbound i s t x).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (le_trans (hBD i s) (by dsimp [C]; linarith [show (0 : ℝ) ≤ d by positivity])) t.coe_nonneg
  calc
    _ ≤ ∫⁻ y, ∑ i : Fin d, (F i true y + F i false y) ∂μ := lintegral_mono hpoint
    _ = ∑ i : Fin d, ((∫⁻ y, F i true y ∂μ) + (∫⁻ y, F i false y ∂μ)) := by
      rw [lintegral_finsetSum (f := fun i y => F i true y + F i false y)
        Finset.univ (fun i _ => (hm i true).add (hm i false))]
      simp_rw [lintegral_add_left (hm _ true)]
    _ ≤ ∑ _i : Fin d, (ENNReal.ofReal (Real.exp (C * (t : ℝ))) +
        ENNReal.ofReal (Real.exp (C * (t : ℝ)))) :=
      Finset.sum_le_sum fun i _ => add_le_add (hi i true) (hi i false)
    _ = ENNReal.ofReal ((2 * d) * Real.exp (C * (t : ℝ))) := by
      rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (d : ℝ))]
      congr 1 <;> ring
    _ ≤ ENNReal.ofReal (C * Real.exp (C * (t : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      dsimp [C]
      linarith

/-- Exponential Euclidean displacement tail for every starting point. -/
theorem u8_regular_unforced_kernel_exponential_tail
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (q : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d) (R : ℝ), 0 ≤ R →
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x
        {y | R ≤ euclideanNorm (y - x)} ≤
      ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - q * R)) := by
  obtain ⟨C, hC, hbound⟩ :=
    u8_regular_unforced_kernel_euclidean_exponential_increment hd ω Λ hΛ hω q
  refine ⟨C, hC, ?_⟩
  intro t x R _hR
  let μ := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x
  let f : Vec d → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (Real.exp (q * euclideanNorm (y - x)))
  have hf : Measurable f :=
    (Real.continuous_exp.comp (continuous_const.mul
      ((EinsteinFull.Calculus.Feller.continuous_euclideanNorm d).comp
        (continuous_id.sub continuous_const)))).measurable.ennreal_ofReal
  have hsub : {y : Vec d | R ≤ euclideanNorm (y - x)} ⊆
      {y | ENNReal.ofReal (Real.exp (q * R)) ≤ f y} := by
    intro y hy
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hy hq.le))
  calc
    μ {y | R ≤ euclideanNorm (y - x)} ≤
        μ {y | ENNReal.ofReal (Real.exp (q * R)) ≤ f y} := measure_mono hsub
    _ ≤ (∫⁻ y, f y ∂μ) / ENNReal.ofReal (Real.exp (q * R)) :=
      meas_ge_le_lintegral_div hf.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C * Real.exp (C * (t : ℝ))) /
        ENNReal.ofReal (Real.exp (q * R)) := by
      apply ENNReal.div_le_div_right _ _
      simpa only [f, μ, abs_of_pos hq] using hbound t x
    _ = ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - q * R)) := by
      rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
      congr 1
      rw [Real.exp_sub]
      ring

/-- All integer Euclidean displacement moments of the actual unforced kernel. -/
theorem u8_regular_unforced_kernel_all_moments
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ n)
        ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) ≤
        ENNReal.ofReal (C * Real.exp (C * (t : ℝ))) := by
  obtain ⟨B, hB, hbound⟩ :=
    u8_regular_unforced_kernel_euclidean_exponential_increment hd ω Λ hΛ hω 1
  let A : ℝ := n.factorial
  let C : ℝ := 1 + B + A * B
  have hA : 0 < A := by dsimp [A]; exact_mod_cast Nat.factorial_pos n
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; nlinarith
  have hABC : A * B ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro t x
  let μ := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x
  have hpoint (y : Vec d) :
      ENNReal.ofReal (euclideanNorm (y - x) ^ n) ≤
      ENNReal.ofReal A * ENNReal.ofReal (Real.exp (euclideanNorm (y - x))) := by
    have hr : 0 ≤ euclideanNorm (y - x) := Real.sqrt_nonneg _
    have hf := Real.pow_div_factorial_le_exp _ hr n
    have hp : euclideanNorm (y - x) ^ n ≤ A * Real.exp (euclideanNorm (y - x)) := by
      have hf' : euclideanNorm (y - x) ^ n / A ≤ Real.exp (euclideanNorm (y - x)) := hf
      exact (div_le_iff₀ hA).mp hf' |>.trans_eq (mul_comm _ _)
    exact (ENNReal.ofReal_le_ofReal hp).trans_eq (ENNReal.ofReal_mul hA.le)
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal A * ENNReal.ofReal (Real.exp (euclideanNorm (y - x))) ∂μ :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal A * ∫⁻ y, ENNReal.ofReal (Real.exp (euclideanNorm (y - x))) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (B * Real.exp (B * (t : ℝ))) := by
      exact mul_le_mul_right
        (by simpa only [μ, abs_one, one_mul] using hbound t x) (ENNReal.ofReal A)
    _ = ENNReal.ofReal ((A * B) * Real.exp (B * (t : ℝ))) := by
      rw [← ENNReal.ofReal_mul hA.le]
      congr 1 <;> ring
    _ ≤ ENNReal.ofReal (C * Real.exp (C * (t : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul hABC _ (Real.exp_nonneg _) hC.le
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hBC t.coe_nonneg)

#print axioms u8_regular_unforced_kernel_all_moments

#print axioms u8_regular_unforced_kernel_exponential_tail

#print axioms u8_regular_unforced_kernel_euclidean_exponential_increment

#print axioms u8_regular_unforced_kernel_absolute_exponential_increment

#print axioms u8_regular_unforced_kernel_exponential_increment

end EinsteinFull
