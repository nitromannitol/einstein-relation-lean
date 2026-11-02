import EinsteinFull.Work.W5.GantertWeightedFormDynkinProof
import EinsteinFull.Calculus.S4MartingaleVarianceSupport
import Mathlib.Probability.Process.Filtration
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.GantertSection7Support EinsteinFull.Work.W5
/-- Continuous, locally uniformly bounded martingales extend to the literal
right-continuation of their filtration. -/
private theorem martingale_rightCont_of_continuous_locallyBounded
    {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hc : ∀ γ, Continuous (fun t => M t γ))
    (hb : ∀ v, ∃ C : ℝ, ∀ t ≤ v, ∀ γ, ‖M t γ‖ ≤ C) :
    Martingale M F.rightCont P := by
  have had : StronglyAdapted F.rightCont M :=
    fun t => (hM.stronglyMeasurable t).mono (F.le_rightCont t)
  refine ⟨had, fun s t hst => ?_⟩
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (F.rightCont.le s) (hM.integrable t)
    (fun B _ _ => (hM.integrable s).integrableOn) (fun B hB _ => ?_)
    (had s).aestronglyMeasurable
  obtain rfl | hst := hst.eq_or_lt
  · rfl
  obtain ⟨u, _huanti, hu, hulim⟩ := exists_seq_strictAnti_tendsto' hst
  obtain ⟨C, hC⟩ := hb t
  have hBu (n : ℕ) : MeasurableSet[F (u n)] B := by
    have hle : F.rightCont s ≤ F (u n) := by
      rw [F.rightCont_eq s]
      exact iInf₂_le_of_le (u n) (hu n).1 le_rfl
    exact hle B hB
  have heq (n : ℕ) : ∫ γ in B, M (u n) γ ∂P = ∫ γ in B, M t γ ∂P :=
    hM.setIntegral_eq (hu n).2.le (hBu n)
  have hlim : Tendsto (fun n => ∫ γ in B, M (u n) γ ∂P) atTop
      (𝓝 (∫ γ in B, M s γ ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · intro n
      exact (hM.integrable (u n)).aestronglyMeasurable.restrict
    · exact integrable_const C
    · intro n
      exact ae_of_all _ fun γ => hC (u n) (hu n).2.le γ
    · exact ae_of_all _ fun γ => (hc γ).continuousAt.tendsto.comp hulim
  exact tendsto_nhds_unique hlim (by simpa only [heq] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ γ in B, M t γ ∂P) atTop
      (𝓝 (∫ γ in B, M t γ ∂P))))

/-- Every compact smooth compensated test of an arbitrary physical martingale
problem solution is a martingale in the right-continuous path filtration. -/
theorem physical_mp_compact_smooth_rightCont_martingale :
∀ {d : ℕ} (i : Fin d) (ω : FieldPair d) (hSmooth : IsSmoothFieldPair ω)
  (lam : ℝ) (x : Vec d) (P : Measure (Path d)),
  SolvesMartingaleProblem (physicalGenerator i ω lam) x P →
  ∀ (f : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
  Martingale (fun (t : ℝ≥0) (γ : Path d) =>
    compensatedTest (physicalGenerator i ω lam) f t γ)
    (pathFiltration d).rightCont P := by
  intro d i ω hSmooth lam x P hP f hf hfc
  have : IsProbabilityMeasure P := hP.1
  have hL := gantert_contDiff_physicalGenerator i ω hSmooth lam hf
  have hLc := gantert_hasCompactSupport_physicalGenerator i ω lam hfc
  have hM := (hP.2.2 f hf hfc).2.2
  apply martingale_rightCont_of_continuous_locallyBounded hM
  · intro γ
    have hc := continuous_compensatedTest hf.continuous hL.continuous
    have he : Continuous (fun t : ℝ≥0 => (γ, (t : ℝ))) :=
      continuous_const.prodMk NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using hc.comp he
  · intro v
    obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hfc
    obtain ⟨K, hK⟩ := hL.continuous.bounded_above_of_compact_support hLc
    refine ⟨2 * C + max K 0 * v, fun t htv γ => ?_⟩
    have hbound := abs_compensatedTest_le
      (fun y => (Real.norm_eq_abs (f y)) ▸ hC y)
      (fun y => (Real.norm_eq_abs (physicalGenerator i ω lam f y)) ▸ hK y) t γ
    rw [Real.norm_eq_abs]
    exact hbound.trans (add_le_add_right
      ((mul_le_mul_of_nonneg_right (le_max_left K 0) t.coe_nonneg).trans
        (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr htv) (le_max_right K 0))) _)

end EinsteinFull.Blueprint
