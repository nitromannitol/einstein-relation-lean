import EinsteinFull.Calculus.S4CountableSolvesSupport
import MarkovProcess.Path.Polish
import Mathlib.Probability.Kernel.Condexp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Restarting a solution of the martingale problem at a deterministic time

For bounded measurable coefficients, the conditional law of the restarted path `γ (s + ·)` given
the path up to time `s` solves the martingale problem from `γ s` for almost every path. With
uniqueness from every start this is the Markov property at deterministic times.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The path restarted at time `s`. -/
def restartPath {d : ℕ} (s : ℝ≥0) (γ : Path d) : Path d :=
  ⟨fun t => γ (s + t), γ.continuous.comp (continuous_const.add continuous_id)⟩

@[simp] theorem restartPath_apply {d : ℕ} (s t : ℝ≥0) (γ : Path d) :
    restartPath s γ t = γ (s + t) := rfl

theorem continuous_restartPath {d : ℕ} (s : ℝ≥0) : Continuous (restartPath (d := d) s) :=
  ContinuousMap.continuous_precomp
    (⟨fun t => s + t, continuous_const.add continuous_id⟩ : C(ℝ≥0, ℝ≥0))

theorem measurable_restartPath {d : ℕ} (s : ℝ≥0) : Measurable (restartPath (d := d) s) :=
  (continuous_restartPath s).measurable

/-- A past event of the restarted path at time `S` is a past event of the path at `s + S`. -/
theorem measurableSet_restartPath_preimage {d : ℕ} (s S : ℝ≥0) {B : Set (Path d)}
    (hB : MeasurableSet[pathFiltration d S] B) :
    MeasurableSet[pathFiltration d (s + S)] (restartPath s ⁻¹' B) := by
  have hle : MeasurableSpace.comap (restartPath (d := d) s) (pathFiltration d S) ≤
      pathFiltration d (s + S) := by
    change MeasurableSpace.comap _ (⨆ j ≤ S, MeasurableSpace.comap (pathPosition j) _) ≤
      ⨆ j ≤ s + S, MeasurableSpace.comap (pathPosition j) _
    simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    refine iSup₂_le fun j hj => le_iSup₂_of_le (s + j) (add_le_add le_rfl hj) le_rfl
  exact hle _ ⟨B, hB, rfl⟩

/-- Restarting shifts the compensated increments of a test function. -/
theorem compensatedTest_restartPath_sub {d : ℕ} {L : (Vec d → ℝ) → Vec d → ℝ}
    {f : Vec d → ℝ} (hL : Measurable (L f)) {C : ℝ} (hC : ∀ y, |L f y| ≤ C)
    (s S T : ℝ≥0) (γ : Path d) :
    compensatedTest L f T (restartPath s γ) - compensatedTest L f S (restartPath s γ) =
      compensatedTest L f (s + T) γ - compensatedTest L f (s + S) γ := by
  have hint (a c : ℝ) :
      IntervalIntegrable (fun u : ℝ => L f (γ u.toNNReal)) volume a c :=
    intervalIntegrable_path_of_bounded hL hC γ a c
  have hshift (t : ℝ≥0) :
      (∫ u in (0 : ℝ)..(t : ℝ), L f (restartPath s γ u.toNNReal)) =
        ∫ u in (s : ℝ)..((s : ℝ) + t), L f (γ u.toNNReal) := by
    have hc := intervalIntegral.integral_comp_add_right
      (fun u : ℝ => L f (γ u.toNNReal)) (s : ℝ) (a := 0) (b := (t : ℝ))
    rw [zero_add, add_comm (t : ℝ)] at hc
    rw [← hc]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le (NNReal.coe_nonneg t)] at hu
    have hu0 : 0 ≤ u := hu.1
    simp only [restartPath_apply]
    congr 2
    rw [Real.toNNReal_add hu0 (NNReal.coe_nonneg s), Real.toNNReal_coe, add_comm]
  unfold compensatedTest
  rw [hshift T, hshift S]
  simp only [restartPath_apply, add_zero, NNReal.coe_add]
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s (s + T))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s (s + S))
  linarith

/-- An observation measurable for the conditioning sigma-algebra is almost surely constant
under the conditional kernel. -/
theorem ae_condExpKernel_observation_eq {α E : Type*}
    [mα : MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace E] [MeasurableEq E]
    (μ : Measure α) [IsFiniteMeasure μ] (m : MeasurableSpace α) (hm : m ≤ mα)
    (X : α → E) (hX : Measurable[m] X) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂condExpKernel (mΩ := mα) μ m a, X a = X b := by
  let : MeasurableSpace α := mα
  let : MeasurableSpace (α × α) := m.prod mα
  have hp : @MeasurableSet (α × α) (m.prod mα) {p | X p.1 = X p.2} :=
    measurableSet_eq_fun (hX.comp (@measurable_fst α α m mα))
      ((hX.mono hm le_rfl).comp (@measurable_snd α α m mα))
  have hd : @Measurable α (α × α) mα (m.prod mα) (fun a => (a, a)) :=
    (measurable_id.mono le_rfl hm).prodMk measurable_id
  have hprod : ∀ᵐ p ∂(μ.trim hm).compProd (condExpKernel μ m), X p.1 = X p.2 := by
    rw [compProd_trim_condExpKernel hm]
    exact (ae_map_iff hd.aemeasurable hp).mpr (Filter.Eventually.of_forall fun _ => rfl)
  exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_compProd hprod)

section Restart

variable {d : ℕ}

/-- The conditional law of the path restarted at time `s`, given the path up to time `s`. -/
noncomputable def restartLaw (P : Measure (Path d)) [IsFiniteMeasure P] (s : ℝ≥0)
    (γ : Path d) : Measure (Path d) :=
  (condExpKernel P (pathFiltration d s) γ).map (restartPath s)

variable {A : Vec d → Mat d} {b : Vec d → Vec d} {M : ℝ}

/-- For almost every path, the conditional law of the restarted path satisfies the countable
martingale-problem conditions from the current position. -/
theorem ae_countableCond_restartLaw (h : BddCoef A b M) {x : Vec d} {P : Measure (Path d)}
    [IsProbabilityMeasure P]
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator A b) x P) (s : ℝ≥0) :
    ∀ᵐ γ ∂P, CountableCond (External.Draft.svGenerator A b) (γ s) (restartLaw P s γ) := by
  classical
  have hm : pathFiltration d s ≤ (inferInstance : MeasurableSpace (Path d)) :=
    (pathFiltration d).le s
  have hpos : Measurable[pathFiltration d s] (pathPosition (d := d) s) :=
    (Filtration.stronglyAdapted_natural (fun t => (measurable_pathPosition t).stronglyMeasurable)
      s).measurable
  have hstart := ae_condExpKernel_observation_eq P (pathFiltration d s) hm
    (pathPosition (d := d) s) hpos
  have hcond : ∀ u ∈ tfam d, ∀ S T : MarkovProcess.DenseTime, ∀ B ∈ cylSys d S,
      ∀ᵐ γ ∂P, S ≤ T → ∫ η in B,
        (compensatedTest (External.Draft.svGenerator A b) u (MarkovProcess.DenseTime.castOrderEmbedding T) η -
          compensatedTest (External.Draft.svGenerator A b) u (MarkovProcess.DenseTime.castOrderEmbedding S) η)
            ∂restartLaw P s γ = 0 := by
    intro u hu S T B hB
    by_cases hST : S ≤ T
    swap
    · exact ae_of_all _ fun _ h => absurd h hST
    set Sr := MarkovProcess.DenseTime.castOrderEmbedding S
    set Tr := MarkovProcess.DenseTime.castOrderEmbedding T
    obtain ⟨hus, huc⟩ := tfam_test d u hu
    obtain ⟨CL, hCL⟩ := bounded_svGenerator A b h.Ab h.bb (contDiff_two_of_top hus) huc
    have hLm := h.measurable_gen u
    obtain ⟨_, hint, hmart⟩ := hP.2.2 u hus huc
    have hadapt := stronglyAdapted_compensatedTest_of_measurable (External.Draft.svGenerator A b) u hus.continuous hLm
    have hBS : MeasurableSet[pathFiltration d Sr] B := by
      rw [pathFiltration_eq_canonical, ← cylSys_gen d S]
      exact MeasurableSpace.measurableSet_generateFrom hB
    have hB : MeasurableSet B := (pathFiltration d).le Sr _ hBS
    have hE := measurableSet_restartPath_preimage s Sr hBS
    let Z : Path d → ℝ := (restartPath s ⁻¹' B).indicator
      (fun η => compensatedTest (External.Draft.svGenerator A b) u (s + Tr) η - compensatedTest (External.Draft.svGenerator A b) u (s + Sr) η)
    have hZint : Integrable Z P :=
      ((hint _).sub (hint _)).indicator ((pathFiltration d).le _ _ hE)
    have hZ0 : P[Z | pathFiltration d s] =ᵐ[P] 0 := by
      refine (ae_eq_condExp_of_forall_setIntegral_eq hm hZint
        (fun _ _ _ => integrableOn_zero) (fun E hEm _ => ?_)
        stronglyMeasurable_zero.aestronglyMeasurable).symm
      have hEE : MeasurableSet[pathFiltration d (s + Sr)] (E ∩ restartPath s ⁻¹' B) :=
        ((pathFiltration d).mono le_self_add _ hEm).inter hE
      have e := hmart.setIntegral_eq
        (add_le_add le_rfl (MarkovProcess.DenseTime.castOrderEmbedding.monotone hST)) hEE
      rw [integral_zero, setIntegral_indicator ((pathFiltration d).le _ _ hE),
        integral_sub (hint _).integrableOn (hint _).integrableOn, e, sub_self]
    have hker := condExp_ae_eq_integral_condExpKernel hm hZint
    filter_upwards [hZ0, hker] with γ h0 hk _
    have hmeas (t : ℝ≥0) : Measurable (compensatedTest (External.Draft.svGenerator A b) u t) :=
      ((hadapt t).mono ((pathFiltration d).le t)).measurable
    unfold restartLaw
    rw [setIntegral_map (f := fun η => compensatedTest (External.Draft.svGenerator A b) u Tr η - compensatedTest (External.Draft.svGenerator A b) u Sr η) hB
      ((hmeas Tr).sub (hmeas Sr)).aestronglyMeasurable (measurable_restartPath s).aemeasurable]
    simp_rw [compensatedTest_restartPath_sub hLm hCL]
    rw [← integral_indicator (measurable_restartPath s hB)]
    change (∫ η, Z η ∂condExpKernel P (pathFiltration d s) γ) = 0
    rw [← hk, h0, Pi.zero_apply]
  have hall : ∀ᵐ γ ∂P, ∀ u ∈ tfam d, ∀ S T : MarkovProcess.DenseTime, ∀ B ∈ cylSys d S,
      S ≤ T → ∫ η in B,
        (compensatedTest (External.Draft.svGenerator A b) u (MarkovProcess.DenseTime.castOrderEmbedding T) η -
          compensatedTest (External.Draft.svGenerator A b) u (MarkovProcess.DenseTime.castOrderEmbedding S) η)
            ∂restartLaw P s γ = 0 :=
    (ae_ball_iff (tfam_countable d)).2 fun u hu => ae_all_iff.2 fun S => ae_all_iff.2 fun T =>
      (ae_ball_iff (cylSys_countable d S)).2 fun B hB => hcond u hu S T B hB
  filter_upwards [hstart, hall] with γ hγs hγ
  refine ⟨?_, ?_, fun u hu S T hST B hB => hγ u hu S T B hB hST⟩
  · unfold restartLaw
    infer_instance
  · unfold restartLaw
    rw [ae_map_iff (measurable_restartPath s).aemeasurable
      (show MeasurableSet {η : Path d | η 0 = γ s} from
        measurableSet_eq_fun (measurable_pathPosition 0) measurable_const)]
    filter_upwards [hγs] with η hη
    change η (s + 0) = γ s
    rw [add_zero]
    exact hη.symm

/-- For almost every path, the conditional law of the restarted path solves the martingale
problem from the current position. -/
theorem ae_solves_restartLaw (h : BddCoef A b M) {x : Vec d} {P : Measure (Path d)}
    [IsProbabilityMeasure P]
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator A b) x P) (s : ℝ≥0) :
    ∀ᵐ γ ∂P, SolvesMartingaleProblem (External.Draft.svGenerator A b) (γ s)
      (restartLaw P s γ) := by
  filter_upwards [ae_countableCond_restartLaw h hP s] with γ hγ
  exact solves_of_countableCond h hγ

/-- Markov property at a deterministic time. If the martingale problem has the unique solution
`K y` from every start `y`, a bounded past observable and a bounded functional of the restarted
path integrate as if the restarted path were drawn from `K` at the current position. -/
theorem integral_mul_restartPath (h : BddCoef A b M) {x : Vec d} {P : Measure (Path d)}
    [IsProbabilityMeasure P]
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator A b) x P)
    (K : Vec d → Measure (Path d))
    (hK : ∀ (y : Vec d) (P' : Measure (Path d)),
      SolvesMartingaleProblem (External.Draft.svGenerator A b) y P' → P' = K y)
    (s : ℝ≥0) {H G : Path d → ℝ} (hH : StronglyMeasurable[pathFiltration d s] H)
    {CH : ℝ} (hHb : ∀ γ, |H γ| ≤ CH) (hG : Measurable G) {CG : ℝ} (hGb : ∀ γ, |G γ| ≤ CG) :
    ∫ γ, H γ * G (restartPath s γ) ∂P = ∫ γ, H γ * ∫ η, G η ∂K (γ s) ∂P := by
  have hm : pathFiltration d s ≤ (inferInstance : MeasurableSpace (Path d)) :=
    (pathFiltration d).le s
  have hGr : Integrable (fun γ => G (restartPath s γ)) P :=
    Integrable.of_bound (hG.comp (measurable_restartPath s)).aestronglyMeasurable CG
      (ae_of_all _ fun γ => by simpa only [Real.norm_eq_abs] using hGb _)
  have hHm : Measurable H := (hH.mono hm).measurable
  have hHG : Integrable (H * fun γ => G (restartPath s γ)) P :=
    Integrable.of_bound (hHm.mul (hG.comp (measurable_restartPath s))).aestronglyMeasurable
      (CH * CG) (ae_of_all _ fun γ => by
        rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hHb γ) (hGb _) (abs_nonneg _) ((abs_nonneg _).trans (hHb γ)))
  calc
    (∫ γ, H γ * G (restartPath s γ) ∂P) =
        ∫ γ, (P[H * fun γ => G (restartPath s γ) | pathFiltration d s]) γ ∂P :=
      (integral_condExp hm).symm
    _ = ∫ γ, (H * P[fun γ => G (restartPath s γ) | pathFiltration d s]) γ ∂P :=
      integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hH hHG hGr)
    _ = ∫ γ, H γ * ∫ η, G η ∂K (γ s) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [condExp_ae_eq_integral_condExpKernel hm hGr,
        ae_solves_restartLaw h hP s] with γ h1 h2
      rw [Pi.mul_apply, h1, ← hK _ _ h2]
      unfold restartLaw
      rw [integral_map (measurable_restartPath s).aemeasurable hG.aestronglyMeasurable]

end Restart

section Translation

variable {d : ℕ}

/-- The path translated by `y`. -/
def translatePath (y : Vec d) (γ : Path d) : Path d :=
  ⟨fun t => y + γ t, continuous_const.add γ.continuous⟩

@[simp] theorem translatePath_apply (y : Vec d) (γ : Path d) (t : ℝ≥0) :
    translatePath y γ t = y + γ t := rfl

theorem measurable_translatePath (y : Vec d) : Measurable (translatePath y) :=
  (ContinuousMap.continuous_postcomp
    (⟨fun x => y + x, continuous_const.add continuous_id⟩ : C(Vec d, Vec d))).measurable

/-- A past event of the translated path is a past event of the path. -/
theorem measurableSet_translatePath_preimage (y : Vec d) (S : ℝ≥0) {B : Set (Path d)}
    (hB : MeasurableSet[pathFiltration d S] B) :
    MeasurableSet[pathFiltration d S] (translatePath y ⁻¹' B) := by
  have hle : MeasurableSpace.comap (translatePath y) (pathFiltration d S) ≤
      pathFiltration d S := by
    change MeasurableSpace.comap _ (⨆ j ≤ S, MeasurableSpace.comap (pathPosition j) _) ≤
      ⨆ j ≤ S, MeasurableSpace.comap (pathPosition j) _
    simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    refine iSup₂_le fun j hj => le_iSup₂_of_le j hj ?_
    have e : pathPosition j ∘ translatePath (d := d) y = (fun x => y + x) ∘ pathPosition j := rfl
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_const_add y).comap_le
  exact hle _ ⟨B, hB, rfl⟩

/-- The textbook generator commutes with spatial translation. -/
theorem svGenerator_comp_add (A : Vec d → Mat d) (b : Vec d → Vec d) (f : Vec d → ℝ)
    (y z : Vec d) :
    External.Draft.svGenerator (fun w => A (y + w)) (fun w => b (y + w))
        (fun w => f (y + w)) z =
      External.Draft.svGenerator A b f (y + z) := by
  unfold External.Draft.svGenerator
  have h1 : ∀ w, fderiv ℝ (fun w => f (y + w)) w = fderiv ℝ f (y + w) :=
    fun w => fderiv_comp_add_left y
  simp only [h1]
  have h2 : ∀ j : Fin d, fderiv ℝ (fun w => fderiv ℝ f (y + w) (unitVector j)) z =
      fderiv ℝ (fun v => fderiv ℝ f v (unitVector j)) (y + z) :=
    fun j => fderiv_comp_add_left (f := fun v => fderiv ℝ f v (unitVector j)) y
  simp only [h2]

/-- Compensated tests of the translated path are compensated translated tests. -/
theorem compensatedTest_translatePath (A : Vec d → Mat d) (b : Vec d → Vec d)
    (f : Vec d → ℝ) (y : Vec d) (t : ℝ≥0) (γ : Path d) :
    compensatedTest (External.Draft.svGenerator A b) f t (translatePath y γ) =
      compensatedTest (External.Draft.svGenerator (fun w => A (y + w)) (fun w => b (y + w)))
        (fun w => f (y + w)) t γ := by
  unfold compensatedTest
  simp only [translatePath_apply, svGenerator_comp_add]

/-- Translating a solution for the translated coefficients from the origin gives a solution
from `y`. -/
theorem solves_map_translatePath {A : Vec d → Mat d} {b : Vec d → Vec d} {M : ℝ}
    (h : BddCoef A b M) (y : Vec d) {P : Measure (Path d)} [IsProbabilityMeasure P]
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (fun w => A (y + w)) (fun w => b (y + w))) 0 P) :
    SolvesMartingaleProblem (External.Draft.svGenerator A b) y (P.map (translatePath y)) := by
  apply solves_of_countableCond h
  refine ⟨inferInstance, ?_, fun u hu S T hST B hB => ?_⟩
  · rw [ae_map_iff (measurable_translatePath y).aemeasurable
      (show MeasurableSet {η : Path d | η 0 = y} from
        measurableSet_eq_fun (measurable_pathPosition 0) measurable_const)]
    filter_upwards [hP.2.1] with γ hγ
    change y + γ 0 = y
    rw [hγ, add_zero]
  · obtain ⟨hus, huc⟩ := tfam_test d u hu
    have hus' : ContDiff ℝ (⊤ : ℕ∞) (fun w => u (y + w)) :=
      hus.comp (contDiff_const.add contDiff_id)
    have huc' : HasCompactSupport (fun w => u (y + w)) :=
      huc.comp_homeomorph (Homeomorph.addLeft y)
    obtain ⟨_, hint, hmart⟩ := hP.2.2 _ hus' huc'
    set Sr := MarkovProcess.DenseTime.castOrderEmbedding S
    set Tr := MarkovProcess.DenseTime.castOrderEmbedding T
    have hBS : MeasurableSet[pathFiltration d Sr] B := by
      rw [pathFiltration_eq_canonical, ← cylSys_gen d S]
      exact MeasurableSpace.measurableSet_generateFrom hB
    have hB' : MeasurableSet B := (pathFiltration d).le Sr _ hBS
    have hE := measurableSet_translatePath_preimage y Sr hBS
    have hadapt := stronglyAdapted_compensatedTest_of_measurable
      (External.Draft.svGenerator A b) u hus.continuous (h.measurable_gen u)
    have hmeas (t : ℝ≥0) : Measurable (compensatedTest (External.Draft.svGenerator A b) u t) :=
      ((hadapt t).mono ((pathFiltration d).le t)).measurable
    rw [setIntegral_map (f := fun η => compensatedTest (External.Draft.svGenerator A b) u Tr η -
        compensatedTest (External.Draft.svGenerator A b) u Sr η) hB'
      ((hmeas Tr).sub (hmeas Sr)).aestronglyMeasurable (measurable_translatePath y).aemeasurable]
    simp_rw [compensatedTest_translatePath]
    have e := hmart.setIntegral_eq (MarkovProcess.DenseTime.castOrderEmbedding.monotone hST) hE
    rw [integral_sub (hint _).integrableOn (hint _).integrableOn, e, sub_self]

end Translation

end EinsteinFull
