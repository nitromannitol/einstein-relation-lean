import EinsteinFull.Calculus.C9GMPActualDynkin
import EinsteinFull.Work.W1.GMPFullPastRestartSupport
import EinsteinFull.Calculus.S4PathClockSupport
import EinsteinFull.Calculus.S4MartingaleVarianceSupport
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.GantertSection7Support EinsteinFull.Work.W5
-- The following three restart helpers reuse the checked private proofs in
-- C10SignedVelocityFamily; kept local to avoid importing its downstream assembly.

/-- Restart uses exactly the canonical natural filtration. -/
private theorem pastSigma_eq_pathFiltration {d : ℕ} (s : ℝ≥0) :
    gmpPastSigma (d := d) s = pathFiltration d s := by
  change (⨆ t : Set.Iic s, MeasurableSpace.comap (pathPosition t.val) inferInstance) =
    ⨆ t ≤ s, MeasurableSpace.comap (pathPosition t) inferInstance
  exact iSup_subtype

/-- Compensated-test increments are literal future compensated tests. -/
private theorem compensatedTest_shift {d : ℕ}
    (L : (Vec d → ℝ) → Vec d → ℝ) (f : Vec d → ℝ)
    (hL : Continuous (L f)) (s t : ℝ≥0) (γ : Path d) :
    compensatedTest L f t (gmpShiftPath s γ) =
      compensatedTest L f (s + t) γ - compensatedTest L f s γ := by
  let g : ℝ → ℝ := fun u => L f (γ u.toNNReal)
  have hg : Continuous g := hL.comp (γ.continuous.comp continuous_real_toNNReal)
  have hshift : (∫ u in (0 : ℝ)..(t : ℝ), L f (gmpShiftPath s γ u.toNNReal)) =
      ∫ u in (s : ℝ)..((s : ℝ) + t), g u := by
    calc
      _ = ∫ u in (0 : ℝ)..(t : ℝ), g (u + s) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu0 : 0 ≤ u := (Set.uIcc_of_le t.coe_nonneg ▸ hu).1
        change L f (γ (s + u.toNNReal)) = L f (γ (u + s).toNNReal)
        congr 2
        apply NNReal.eq
        simp only [NNReal.coe_add, Real.coe_toNNReal _ hu0,
          Real.coe_toNNReal _ (add_nonneg hu0 s.coe_nonneg)]
        exact add_comm _ _
      _ = _ := by
        simpa only [zero_add, add_comm (t : ℝ) (s : ℝ)] using
          intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := (t : ℝ)) g (s : ℝ)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (0 : ℝ) (s : ℝ))
    (hg.intervalIntegrable (μ := volume) (s : ℝ) ((s : ℝ) + t))
  simp only [compensatedTest, gmpShiftPath, ContinuousMap.coe_mk, add_zero,
    NNReal.coe_add] at hshift ⊢
  rw [hshift]
  dsimp [g] at hadd
  linarith

open ProbabilityTheory EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Work.W5

/-- Full-past restart integrates any bounded measurable future observable,
retaining the actual endpoint distribution under the past event. -/
private theorem integral_shift_on_past {d : ℕ} {hd : 2 ≤ d} {Λ : ℝ} {hΛ : 1 ≤ Λ}
    {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h₀ h₁)
    (x : Vec d) (s : ℝ≥0) (E : Set (Path d))
    (hE : MeasurableSet[pathFiltration d s] E)
    (F : Path d → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ γ, ‖F γ‖ ≤ B) :
    (∫ γ in E, F (gmpShiftPath s γ) ∂R.pathLaw x) =
      ∫ y, ∫ γ, F γ ∂R.pathLaw y
        ∂(((R.pathLaw x).restrict E).map (pathPosition s)) := by
  let : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  have hpast : MeasurableSet[gmpPastSigma s] E :=
    (pastSigma_eq_pathFiltration s).symm ▸ hE
  let K := R.pathLaw.restrict (gmpPastSigma_le s E hpast)
  have hrestart := congrArg (fun K : Kernel (Vec d) (Path d) => K x)
    (gmpPathLaw_restrict_past_map_shift R s E hpast)
  have hi : Integrable F ((R.pathLaw ∘ₖ K.map (pathPosition s)) x) :=
    (integrable_const B).mono' hF.aestronglyMeasurable (ae_of_all _ hB)
  have he : (∫ γ, F γ ∂(K.map (gmpShiftPath s)) x) =
      ∫ γ in E, F (gmpShiftPath s γ) ∂R.pathLaw x := by
    rw [Kernel.map_apply _ (measurable_gmpShiftPath s)]
    exact integral_map (measurable_gmpShiftPath s).aemeasurable hF.aestronglyMeasurable
  rw [← he, hrestart, Kernel.integral_comp hi,
    Kernel.map_apply _ (measurable_pathPosition s)]
  rfl


/-- The supplied GMP law solves the full compact-test martingale problem at every start. -/
theorem gmp_actual_solves_martingale_problem :
∀ {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
  {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ}
  {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
  (R : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
    hd Λ hΛ ω hω lam h0 h1) (hSmooth : IsSmoothFieldPair ω)
  (x : Vec d),
  SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x (R.pathLaw x) := by
  intro d hd Λ hΛ ω hω lam h0 h1 R hSmooth x
  letI : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  refine ⟨inferInstance, R.pathLaw_starts_at x, ?_⟩
  intro f hf hc
  let L := physicalGenerator (firstCoordinateIndex hd) ω lam
  have hL : Continuous (L f) :=
    (gantert_contDiff_physicalGenerator _ ω hSmooth lam hf).continuous
  have hi := gantert_integrable_compensatedTest hd Λ hΛ ω hω lam h0 h1 R
    hSmooth f hf hc x
  have ha := EinsteinFull.stronglyAdapted_compensatedTest L f hf.continuous hL
  refine ⟨fun t => ae_of_all _ fun γ =>
    (hL.comp (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable 0 t,
    hi, ha, ?_⟩
  intro s u hsu
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (pathFiltration d |>.le s) (hi u)
  · intro E hE hfinite
    exact (hi s).integrableOn
  · intro E hE hfinite
    have hF : Continuous (compensatedTest L f (u - s)) := by
      have h := (continuous_compensatedTest hf.continuous hL).comp
        (continuous_id.prodMk (continuous_const : Continuous fun _ : Path d => ((u - s : ℝ≥0) : ℝ)))
      exact h.congr (fun γ => by
        simp only [Function.comp_apply, id_eq, Real.toNNReal_coe])
    let fB := gantertCompactObservable f hf.continuous hc
    let gB := gantertCompactObservable (L f) hL
      (gantert_hasCompactSupport_physicalGenerator _ ω lam hc)
    have hbound (γ : Path d) :
        ‖compensatedTest L f (u - s) γ‖ ≤ 2 * ‖fB‖ + ‖gB‖ * ((u - s : ℝ≥0) : ℝ) :=
      abs_compensatedTest_le (L := L) (φ := f) (fun y => fB.norm_coe_le_norm y)
        (fun y => gB.norm_coe_le_norm y) (u - s) γ
    have he := integral_shift_on_past R x s E hE
      (compensatedTest L f (u - s)) hF.measurable _ hbound
    simp_rw [compensatedTest_shift L f hL s (u - s), add_tsub_cancel_of_le hsu] at he
    have hz (y : Vec d) : (∫ γ, compensatedTest L f (u - s) γ ∂R.pathLaw y) = 0 :=
      gmp_actual_compensated_test_mean_zero hd hΛ R hSmooth f hf hc y (u - s)
    simp_rw [hz] at he
    rw [integral_zero, integral_sub (hi u).integrableOn (hi s).integrableOn] at he
    exact (sub_eq_zero.mp he).symm
  · exact (ha s).aestronglyMeasurable

end EinsteinFull.Blueprint
