import EinsteinFull.Calculus.U6RegularPathRealization
import EinsteinFull.Calculus.U7RegularKernelDensity

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal

noncomputable section
namespace EinsteinFull

/-- The actual signed regular kernel has one continuous-path realization
that supplies the full fixed-environment fields and the martingale problem. -/
theorem u5_regular_signed_fixed_environment_realization_and_mp
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1,
      R.transitionKernel = (fun t => u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t) ∧
      ∀ x : Vec d, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω lam) x (R.pathLaw x) := by
  have hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪ (volume : Measure (Vec d)) :=
    fun t ht => u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht
  obtain ⟨K, hK, hfdd⟩ := u6_regular_continuous_kernel_of_volume_ac hd ω lam Λ hΛ hω hac
  let : IsMarkovKernel K := hK
  obtain ⟨⟨R, hpath, htransition⟩, hmp⟩ :=
    u2_regular_fixed_environment_realization_and_mp_of_ac_fdd
      hd ω lam Λ hΛ hω h0 h1 K hfdd hac
  refine ⟨R, htransition, ?_⟩
  simpa only [hpath] using hmp

/-- Every regular fixed environment admits the full signed realization. -/
theorem u5_regular_signed_fixed_environment_realization_exists
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Nonempty
      (EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd Λ hΛ ω hω lam h0 h1) := by
  obtain ⟨R, _, _⟩ := u5_regular_signed_fixed_environment_realization_and_mp
    hd hΛ ω hω lam h0 h1
  exact ⟨R⟩

/-- Any supplied continuous-path kernel with the actual signed finite-dimensional
laws solves the physical martingale problem at every starting point. -/
theorem u5_regular_signed_same_FDD_kernel_solves_physical_MP
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∀ x : Vec d, SolvesMartingaleProblem
      (physicalGenerator (firstCoordinateIndex hd) ω lam) x (K x) := by
  exact (u2_regular_fixed_environment_realization_and_mp_of_ac_fdd
    hd ω lam Λ hΛ hω h0 h1 K hfdd
    (fun t ht => u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht)).2

/-- The supplied path law spends zero positive time in every measurable
volume-null set, on each finite horizon. -/
theorem u5_regular_signed_same_FDD_path_occupation_null_sets
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (T : ℝ≥0) (N : Set (Vec d))
    (hN : MeasurableSet N) (hnull : (volume : Measure (Vec d)) N = 0) :
    ∀ᵐ γ ∂K x, ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))),
      γ (Real.toNNReal s) ∉ N := by
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hsection : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)),
      ∀ᵐ γ ∂K x, γ s.toNNReal ∉ N := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have ht : 0 < s.toNNReal := Real.toNNReal_pos.mpr hs.1
    have hmarg : (K x).map (pathPosition s.toNNReal) ≪ (volume : Measure (Vec d)) := by
      rw [Blueprint.k11_endpoint _ K hfdd]
      exact u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω _ ht x
    exact (ae_map_iff (measurable_pathPosition _).aemeasurable hN.compl).mp
      (measure_eq_zero_iff_ae_notMem.mp (hmarg hnull))
  have hprod : ∀ᵐ z ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (K x),
      z.2 z.1.toNNReal ∉ N := by
    apply (Measure.ae_prod_iff_ae_ae ?_).2 hsection
    exact ((hN.preimage heval).compl).preimage measurable_swap
  have hswap : ∀ᵐ z ∂(K x).prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))),
      z.1 z.2.toNNReal ∉ N :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hprod
  exact (Measure.ae_prod_iff_ae_ae (hN.preimage heval).compl).1 hswap

#print axioms u5_regular_signed_same_FDD_path_occupation_null_sets

/-- The joint time and position occupation law is absolutely continuous. -/
theorem u5_regular_signed_same_FDD_joint_occupation_ac
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (T : ℝ≥0) :
    Measure.map (fun z : ℝ × Path d => (z.1, z.2 (Real.toNNReal z.1)))
      ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (K x)) ≪
      ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (volume : Measure (Vec d))) := by
  have heval : Measurable (fun z : ℝ × Path d => (z.1, z.2 z.1.toNNReal)) :=
    measurable_fst.prodMk ((continuous_eval.comp
      (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable)
  refine Measure.AbsolutelyContinuous.mk fun N hN hnull => ?_
  have hsections : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)),
      ∀ᵐ y ∂(volume : Measure (Vec d)), (s, y) ∉ N :=
    (Measure.ae_prod_iff_ae_ae hN.compl).1 (measure_eq_zero_iff_ae_notMem.mp hnull)
  have hpaths : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)),
      ∀ᵐ γ ∂K x, (s, γ s.toNNReal) ∉ N := by
    filter_upwards [hsections, ae_restrict_mem measurableSet_Ioc] with s hs ht
    have hz : (volume : Measure (Vec d)) (Prod.mk s ⁻¹' N) = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr hs
    have hmarg : (K x).map (pathPosition s.toNNReal) ≪ (volume : Measure (Vec d)) := by
      rw [Blueprint.k11_endpoint _ K hfdd]
      exact u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω _
        (Real.toNNReal_pos.mpr ht.1) x
    exact (ae_map_iff (measurable_pathPosition _).aemeasurable
      (measurable_prodMk_left hN).compl).mp
      (measure_eq_zero_iff_ae_notMem.mp (hmarg hz))
  rw [Measure.map_apply heval hN]
  exact measure_eq_zero_iff_ae_notMem.mpr
    ((Measure.ae_prod_iff_ae_ae (hN.preimage heval).compl).2 hpaths)

#print axioms u5_regular_signed_same_FDD_joint_occupation_ac

#print axioms u5_regular_signed_fixed_environment_realization_and_mp
#print axioms u5_regular_signed_fixed_environment_realization_exists
#print axioms u5_regular_signed_same_FDD_kernel_solves_physical_MP

end EinsteinFull
