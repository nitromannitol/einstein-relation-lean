import EinsteinFull.Calculus.U6GMPKernelFourthMoment
import EinsteinFull.Calculus.C4FoundationPhysicalLawUniqueness

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.GantertSection7Support

private theorem u6_joint_of_restart {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → A) (Y : Ω → B) (hX : Measurable X) (hY : Measurable Y)
    (κ : Kernel A B) [IsMarkovKernel κ]
    (h : ∀ C : Set A, MeasurableSet C →
      (μ.restrict (X ⁻¹' C)).map Y =
        (Kernel.comap κ X hX) ∘ₘ (μ.restrict (X ⁻¹' C))) :
    μ.map (fun z => (X z, Y z)) = (μ.map X).compProd κ := by
  apply Measure.ext_prod
  intro C D hC hD
  have hh := congrArg (fun m : Measure B => m D) (h C hC)
  rw [Measure.map_apply hY hD, Measure.bind_apply hD (Kernel.aemeasurable _),
    Measure.restrict_apply (hY hD)] at hh
  simp_rw [Kernel.comap_apply] at hh
  rw [Measure.map_apply (hX.prodMk hY) (hC.prod hD), Set.mk_preimage_prod,
    Measure.compProd_apply_prod hC hD,
    setLIntegral_map hC (κ.measurable_coe hD) hX]
  simpa only [Set.inter_comm] using hh

theorem u6_physical_supplied_law_fourth_increment_of_smooth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Vec d) (P : Measure (Path d)),
      SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω lam) x P →
      ∀ s t : ℝ≥0, s ≤ t →
        (∫⁻ γ, ENNReal.ofReal (euclideanNorm (γ t - γ s) ^ 4) ∂P) ≤
          ENNReal.ofReal C *
            ((((t - s : ℝ≥0) : ℝ≥0∞) ^ 2) +
             (((t - s : ℝ≥0) : ℝ≥0∞) ^ 4)) := by
  obtain ⟨C, hC, hmoment⟩ := u6_gmpPhysicalC0KernelSemigroup_fourth_moment
    hd ω lam Λ hΛ hω hSmooth
  obtain ⟨K, ⟨hK, hfdd⟩, _⟩ :=
    gmpPhysicalC0KernelSemigroup_existsUnique_continuous_realization hd ω lam Λ hΛ hω hSmooth
  letI : IsMarkovKernel K := hK
  let S := gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  have hcons := gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth
  have hfeller := gmpPhysicalC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω hSmooth
  refine ⟨C, hC, ?_⟩
  intro x P hP s t hst
  rw [c4_physical_supplied_law_eq_gmp_realization_of_smooth
    hd ω lam Λ hΛ hω hSmooth K hfdd x P hP]
  let X : Path d → Vec d := fun γ => γ s
  let Y : Path d → Path d := ContinuousPath.shift s
  have hX : Measurable X := ContinuousPath.measurable_coordinateProcess s
  have hY : Measurable Y := ContinuousPath.measurable_shift_fixed s
  have hjoint : (K x).map (fun γ => (X γ, Y γ)) = ((K x).map X).compProd K := by
    apply u6_joint_of_restart (K x) X Y hX hY K
    intro A hA
    apply hfeller.realization_restrict_map_shift S hcons
      (ContinuousMap.const ℝ≥0 (0 : Vec d)) K hfdd x s
    exact (ContinuousPath.measurable_coordinateProcess_canonicalFiltration s) hA
  let F : Vec d × Path d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (euclideanNorm (z.2 (t - s) - z.1) ^ 4)
  have hF : Measurable F := by
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    apply EinsteinRelation.Entropy.continuous_euclideanNorm'.measurable.comp
    exact ((ContinuousPath.measurable_coordinateProcess (t - s)).comp measurable_snd).sub measurable_fst
  have hinner (y : Vec d) : ∫⁻ η, F (y, η) ∂K y ≤
      ENNReal.ofReal C * (((t - s : ℝ≥0) : ℝ≥0∞) ^ 2 +
        ((t - s : ℝ≥0) : ℝ≥0∞) ^ 4) := by
    have hmarg := SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation S (K y) y (t - s) (by
      have h := congrArg (fun k => k y) (hfdd {t - s})
      simpa only [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _)] using h)
    have hm := hmoment (t - s) y
    have hf : Measurable (fun z : Vec d => ENNReal.ofReal (euclideanNorm (z - y) ^ 4)) := by
      apply Measurable.ennreal_ofReal
      apply Measurable.pow_const
      exact EinsteinRelation.Entropy.continuous_euclideanNorm'.measurable.comp
        (measurable_id.sub measurable_const)
    rw [← hmarg, lintegral_map hf (show Measurable (fun path : Path d => path (t - s)) from
      ContinuousPath.measurable_coordinateProcess (t - s))] at hm
    exact hm
  calc
    _ = ∫⁻ z, F z ∂((K x).map (fun γ => (X γ, Y γ))) := by
      rw [lintegral_map hF (hX.prodMk hY)]
      congr 1
      funext γ
      simp [F, X, Y, ContinuousPath.shift, add_tsub_cancel_of_le hst]
    _ = ∫⁻ y, ∫⁻ η, F (y, η) ∂K y ∂((K x).map X) := by
      rw [hjoint, Measure.lintegral_compProd hF]
    _ ≤ _ := by
      calc
        _ ≤ ∫⁻ _, ENNReal.ofReal C * (((t - s : ℝ≥0) : ℝ≥0∞) ^ 2 +
            ((t - s : ℝ≥0) : ℝ≥0∞) ^ 4) ∂((K x).map X) := lintegral_mono hinner
        _ = _ := by simp

#print axioms u6_physical_supplied_law_fourth_increment_of_smooth
end EinsteinFull.Blueprint

namespace EinsteinFull
open EinsteinRelation

/-- The physical generator of translated smooth tests is jointly measurable in
translation and evaluation point, even for nonsmooth coefficient fields. -/
theorem u6_measurable_physical_generator_translates
    {d : ℕ} (ω : FieldPair d) (i : Fin d) (lam : ℝ)
    {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) :
    Measurable (fun p : Vec d × Vec d =>
      physicalGenerator i ω lam (fun w => κ (w - p.1)) p.2) := by
  have hg (j : Fin d) : Continuous (fun p : Vec d × Vec d =>
      coordinateDerivative j (fun w => κ (w - p.1)) p.2) := by
    have hc : Continuous (fun p : Vec d × Vec d =>
        fderiv ℝ κ (p.2 - p.1) (unitVector j)) :=
      ((hκ.continuous_fderiv (by simp)).comp (continuous_snd.sub continuous_fst)).clm_apply
        continuous_const
    simpa only [coordinateDerivative, fderiv_comp_sub] using hc
  have hflux (j : Fin d) : Continuous (fun p : Vec d × Vec d =>
      ((reducedCoefficient ω p.2).mulVec
        (gradient (fun w => κ (w - p.1)) p.2)) j) := by
    simp only [Matrix.mulVec, dotProduct, gradient]
    exact continuous_finsetSum _ (fun k _ =>
      (((continuous_reducedCoefficient ω).matrix_elem j k).comp continuous_snd).mul (hg k))
  have hdiv : Measurable (fun p : Vec d × Vec d =>
      divergence (fun w => (reducedCoefficient ω w).mulVec
        (gradient (fun v => κ (v - p.1)) w)) p.2) := by
    unfold divergence coordinateDerivative
    exact Finset.measurable_sum _ fun j _ =>
      measurable_fderiv_apply_const_with_param ℝ
        (f := fun y w => ((reducedCoefficient ω w).mulVec
          (gradient (fun v => κ (v - y)) w)) j) (hflux j) (unitVector j)
  unfold physicalGenerator dot
  refine ((Real.continuous_exp.comp (continuous_const.mul
    (ω.2.continuous.comp continuous_snd))).div_const 2).measurable.mul hdiv |>.add ?_
  refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
  exact (((continuous_apply j).comp
    ((ω.1.continuous.comp continuous_snd).matrix_mulVec continuous_const)).measurable).mul
    (hg j).measurable

end EinsteinFull
