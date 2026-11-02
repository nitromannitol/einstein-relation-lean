import EinsteinFull.Calculus.C10PhysicalMPCompactC2Martingale
import EinsteinFull.Calculus.S4PathClockSupport
import EinsteinFull.Calculus.S4OptionalStoppingSupport
import MarkovProcess.Path.ExitTime
import EinsteinFull.Calculus.S4MartingaleSllnSupport
import EinsteinFull.Calculus.FellerRegularSet
import EinsteinFull.Calculus.S1SharpBoundSupport
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- Bounded continuous martingales remain martingales after stopping. -/
private theorem martingale_stopped_continuous_bounded
    {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P)
    (hc : ∀ γ, Continuous (fun t => M t γ))
    (hb : ∀ v, ∃ C : ℝ, ∀ t ≤ v, ∀ γ, ‖M t γ‖ ≤ C)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Martingale (stoppedProcess M τ) F P := by
  classical
  let N := stoppedProcess M τ
  let T : ℝ≥0 → Ω → ℝ≥0 := fun t γ => (min (t : WithTop ℝ≥0) (τ γ)).untopA
  have hTcoe (t : ℝ≥0) (γ : Ω) : (T t γ : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (τ γ) := by
    have hne : min (t : WithTop ℝ≥0) (τ γ) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    change (((min (t : WithTop ℝ≥0) (τ γ)).untopA : ℝ≥0) : WithTop ℝ≥0) = _
    rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
  have hTle (t : ℝ≥0) (γ : Ω) : T t γ ≤ t := by
    rw [← WithTop.coe_le_coe, hTcoe]
    exact min_le_left _ _
  have hTs (t : ℝ≥0) : IsStoppingTime F (fun γ => (T t γ : WithTop ℝ≥0)) := by
    simp only [hTcoe]
    exact (isStoppingTime_const F t).min hτ
  have had : StronglyAdapted F N := hM.stronglyAdapted.stoppedProcess hc hτ
  have hNi (t : ℝ≥0) : Integrable (N t) P := by
    obtain ⟨C, hC⟩ := hb t
    exact Integrable.of_bound ((had t).mono (F.le t)).aestronglyMeasurable C
      (ae_of_all _ fun γ => hC _ (hTle t γ) γ)
  refine ⟨had, fun s t hst => ?_⟩
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hNi t)
    (fun _ _ _ => (hNi s).integrableOn) (fun B hB _ => ?_) (had s).aestronglyMeasurable
  let A : Set Ω := B ∩ {γ | (s : WithTop ℝ≥0) < τ γ}
  have hA : MeasurableSet[F s] A := hB.inter (hτ.measurableSet_gt s)
  let V : Ω → ℝ≥0 := fun γ => max s (T t γ)
  have hV : IsStoppingTime F (fun γ => (V γ : WithTop ℝ≥0)) := by
    change IsStoppingTime F (fun γ => ((max s (T t γ) : ℝ≥0) : WithTop ℝ≥0))
    simp only [WithTop.coe_max]
    exact (isStoppingTime_const F s).max (hTs t)
  have hVi : Integrable (fun γ => M (V γ) γ) P := by
    obtain ⟨C, hC⟩ := hb t
    have hmeas := stronglyMeasurable_stoppedValue_of_le (hM.stronglyAdapted.isStronglyProgressive_of_continuous hc)
      hV (fun γ => WithTop.coe_le_coe.mpr (max_le hst (hTle t γ)))
    exact Integrable.of_bound (hmeas.mono (F.le t)).aestronglyMeasurable C
      (ae_of_all _ fun γ => by simpa [V] using hC (V γ) (max_le hst (hTle t γ)) γ)
  have hstop := EinsteinFull.setIntegral_stoppedValue_eq hM hb
    (fun γ v => (hc γ).continuousWithinAt)
    (isStoppingTime_const F s) hV (fun γ => le_max_left _ _)
    (fun _ => hst) (fun γ => max_le hst (hTle t γ)) (hM.integrable s) hVi
    (σ := fun _ => s) (τ := V) (K := t)
    (B := A) (by
      change MeasurableSet[(isStoppingTime_const F s).measurableSpace] A
      rw [IsStoppingTime.measurableSpace_const]
      exact hA)
  have heq : ∀ γ, B.indicator (fun γ => N t γ - N s γ) γ =
      A.indicator (fun γ => M (V γ) γ - M s γ) γ := by
    intro γ
    by_cases hγ : γ ∈ B
    · by_cases hsτ : (s : WithTop ℝ≥0) < τ γ
      · have hsT : s ≤ T t γ := by
          rw [← WithTop.coe_le_coe, hTcoe]
          exact le_min (WithTop.coe_le_coe.mpr hst) hsτ.le
        have hTs0 : T s γ = s := by
          apply WithTop.coe_injective
          rw [hTcoe, min_eq_left hsτ.le]
        simp only [Set.indicator_of_mem hγ, Set.indicator_of_mem (show γ ∈ A from ⟨hγ, hsτ⟩)]
        change M (T t γ) γ - M (T s γ) γ = _
        rw [hTs0, show V γ = T t γ from max_eq_right hsT]
      · have hτs : τ γ ≤ (s : WithTop ℝ≥0) := le_of_not_gt hsτ
        have he : T t γ = T s γ := by
          apply WithTop.coe_injective
          rw [hTcoe, hTcoe, min_eq_right (hτs.trans (WithTop.coe_le_coe.mpr hst)), min_eq_right hτs]
        simp only [Set.indicator_of_mem hγ, Set.indicator_of_notMem (show γ ∉ A from fun h => hsτ h.2)]
        change M (T t γ) γ - M (T s γ) γ = 0
        rw [he, sub_self]
    · simp only [Set.indicator_of_notMem hγ, Set.indicator_of_notMem (show γ ∉ A from fun h => hγ h.1)]
  have hi : ∫ γ in B, N t γ - N s γ ∂P = 0 := by
    rw [← integral_indicator (F.le s _ hB)]
    simp_rw [heq]
    rw [integral_indicator (F.le s _ hA), integral_sub hVi.integrableOn (hM.integrable s).integrableOn, hstop, sub_self]
  rw [integral_sub (hNi t).integrableOn (hNi s).integrableOn] at hi
  exact (sub_eq_zero.mp hi).symm
private theorem continuous_physicalGenerator_c2_ball {d : ℕ} (i : Fin d) (ω : FieldPair d)
    (hs : IsSmoothFieldPair ω) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (2 : ℕ∞) f) : Continuous (physicalGenerator i ω lam f) := by
  rw [funext (EinsteinFull.physicalGenerator_eq_svGenerator hs i lam hf)]
  apply EinsteinFull.continuous_svGenerator _ _ (fun j k => (hs.1 j k).continuous) _ hf
  intro j
  exact ((reduce ω).2.continuous.inv₀ (fun y => (clockDensity_pos ω y).ne')).mul
    (EinsteinFull.continuous_forcedDrift_apply hs i lam j)

private theorem norm_path_before_ball_exit {d : ℕ} (R : ℝ) (γ : Path d)
    (h0 : euclideanNorm (γ 0) < R) (t u : ℝ≥0)
    (hu : u ≤ MarkovProcess.ContinuousPath.exitTimeTrunc {y : Vec d | euclideanNorm y < R} t γ) :
    ‖γ u‖ ≤ R := by
  let U := {y : Vec d | euclideanNorm y < R}
  have hU : IsOpen U := isOpen_lt (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  have hue : (u : ℝ≥0∞) ≤ MarkovProcess.ContinuousPath.exitTime U γ := by
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
  exact (EinsteinFull.Calculus.S1.norm_le_euclideanNorm _).trans heuc

/-- Every C² physical martingale test, stopped on a Euclidean ball, is a martingale. -/
theorem physical_mp_c2_ball_stopped_rightCont_martingale :
∀ {d : ℕ} (i : Fin d) (ω : FieldPair d) (hSmooth : IsSmoothFieldPair ω)
  (lam : ℝ) (x : Vec d) (P : Measure (Path d)),
  SolvesMartingaleProblem (physicalGenerator i ω lam) x P →
  ∀ (f : Vec d → ℝ), ContDiff ℝ (2 : ℕ∞) f →
  ∀ R : ℝ, 0 < R →
  Martingale (fun (t : ℝ≥0) (γ : Path d) =>
    compensatedTest (physicalGenerator i ω lam) f
      (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : Vec d | euclideanNorm y < R} t γ) γ)
    (pathFiltration d).rightCont P := by
  intro d i ω hSmooth lam x P hP f hf R hR
  classical
  let _ : IsProbabilityMeasure P := hP.1
  obtain ⟨χ, hχ, _, _, hχ1, hχ0⟩ := EinsteinFull.exists_cutoff d
  let g := EinsteinFull.cutoffFn χ (R + 1) f
  have hRp : 0 < R + 1 := by linarith
  have hg : ContDiff ℝ (2 : ℕ∞) g :=
    ((hχ.of_le (by norm_num)).comp (contDiff_const_smul (R + 1)⁻¹)).mul hf
  have hgc : HasCompactSupport g := EinsteinFull.hasCompactSupport_cutoffFn f hRp hχ0
  have hLgc := continuous_physicalGenerator_c2_ball i ω hSmooth lam hg
  have hM := physical_mp_compact_c2_rightCont_martingale i ω hSmooth lam x P hP g hg hgc
  have hc : ∀ γ : Path d, Continuous (fun t : ℝ≥0 => compensatedTest (physicalGenerator i ω lam) g t γ) := by
    intro γ
    have h := EinsteinFull.continuous_compensatedTest hg.continuous hLgc
    exact (h.comp ((continuous_const : Continuous fun _ : ℝ≥0 => γ).prodMk NNReal.continuous_coe)).congr (fun t => by simp)
  have hb : ∀ v : ℝ≥0, ∃ C : ℝ, ∀ t ≤ v, ∀ γ : Path d,
      ‖compensatedTest (physicalGenerator i ω lam) g t γ‖ ≤ C := by
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    obtain ⟨K, hK⟩ := hLgc.bounded_above_of_compact_support
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator i ω lam hgc)
    have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
    intro v
    refine ⟨2 * C + K * v, fun t ht γ => ?_⟩
    rw [Real.norm_eq_abs]
    exact (EinsteinFull.abs_compensatedTest_le (fun y => by simpa only [Real.norm_eq_abs] using hC y)
      (fun y => by simpa only [Real.norm_eq_abs] using hK y) t γ).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht) hK0) _)
  let U := {y : Vec d | euclideanNorm y < R}
  have hU : IsOpen U := isOpen_lt (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  have hτ : IsStoppingTime (pathFiltration d).rightCont (MarkovProcess.ContinuousPath.exitTimeTop U) := by
    intro t
    have hle := (pathFiltration d).le_rightCont
    rw [EinsteinFull.pathFiltration_eq_canonical] at hle
    rw [EinsteinFull.pathFiltration_eq_canonical]
    exact hle t _ (MarkovProcess.ContinuousPath.isStoppingTime_exitTime U hU t)
  have hstopped := martingale_stopped_continuous_bounded hM hc hb hτ
  have hident : stoppedProcess (compensatedTest (physicalGenerator i ω lam) g)
      (MarkovProcess.ContinuousPath.exitTimeTop U) =
      fun t γ => compensatedTest (physicalGenerator i ω lam) f
        (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ) γ := by
    funext t γ
    change compensatedTest (physicalGenerator i ω lam) g
      ((min (t : WithTop ℝ≥0) (MarkovProcess.ContinuousPath.exitTimeTop U γ)).untopA) γ = _
    rw [min_comm]
    change compensatedTest (physicalGenerator i ω lam) g
      (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ) γ = _
    let T := MarkovProcess.ContinuousPath.exitTimeTrunc U t γ
    by_cases h0 : γ 0 ∈ U
    · have hpath : ∀ u ≤ T, ‖γ u‖ < R + 1 := fun u hu =>
        lt_of_le_of_lt (norm_path_before_ball_exit R γ h0 t u hu) (by linarith)
      have hge : ∀ u ≤ T, g =ᶠ[𝓝 (γ u)] f := fun u hu =>
        EinsteinFull.cutoffFn_eventuallyEq f hRp hχ1 (hpath u hu)
      unfold compensatedTest
      rw [(hge T le_rfl).eq_of_nhds, (hge 0 (bot_le)).eq_of_nhds]
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le T.coe_nonneg] at hu
      have hut : u.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hu.2
      dsimp only
      rw [EinsteinFull.physicalGenerator_eq_svGenerator hSmooth i lam hg,
        EinsteinFull.physicalGenerator_eq_svGenerator hSmooth i lam hf]
      exact EinsteinFull.svGenerator_congr _ _ (hge _ hut)
    · have he0 : MarkovProcess.ContinuousPath.exitTime U γ = 0 :=
        le_antisymm (by simpa using MarkovProcess.ContinuousPath.exitTime_le_of_notMem U γ 0 h0) bot_le
      have hT0 : T = 0 := by
        apply WithTop.coe_injective
        rw [MarkovProcess.ContinuousPath.coe_exitTimeTrunc]
        change min (MarkovProcess.ContinuousPath.exitTime U γ) _ = _
        rw [he0]
        exact min_eq_left (WithTop.coe_le_coe.mpr (bot_le : (0 : ℝ≥0) ≤ t))
      change compensatedTest _ g T γ = compensatedTest _ f T γ
      rw [hT0]
      simp [compensatedTest]
  rw [hident] at hstopped
  exact hstopped
end EinsteinFull.Blueprint
