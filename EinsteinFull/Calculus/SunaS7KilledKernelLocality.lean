import EinsteinFull.Calculus.SunaSuppliedLawIdentification
import MarkovProcess.Killed.Marginals
import MarkovProcess.Trajectory.HarmonicRepresentation
import EinsteinFull.Work.W1.StoppedLawReconstructionSupport

open MeasureTheory ProbabilityTheory
open EinsteinRelation EinsteinRelation.Diffusion
open scoped NNReal ENNReal

namespace EinsteinFull

/-- The physical and Markov-process definitions describe the same exit time. -/
theorem s7_localityExitTime_eq {d : ℕ} (U : Set (Vec d)) (γ : Path d) :
    localityExitTime U γ = MarkovProcess.ContinuousPath.exitTime U γ := by
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨t, rfl, ht⟩
    exact iInf_le_of_le t (iInf_le _ ht)
  · apply le_iInf
    intro t
    apply le_iInf
    intro ht
    exact MarkovProcess.ContinuousPath.exitTime_le_of_notMem U γ t ht

/-- Decode a cemetery observation into the survival flag and position. -/
def s7CemeteryObservation {d : ℕ} (U : Set (Vec d)) :
    MarkovProcess.Cemetery U → ℝ × Vec d :=
  Sum.elim (fun x : U => (1, (x : Vec d))) (fun _ => (0, 0))

theorem s7_measurable_cemeteryObservation {d : ℕ} (U : Set (Vec d)) :
    Measurable (s7CemeteryObservation U) := by
  exact measurable_fun_sum (measurable_const.prodMk measurable_subtype_coe) measurable_const

/-- A decoded observation agrees with the strict-survival record. -/
theorem s7_cemeteryObservation_killAtExit {d : ℕ} (U : Set (Vec d))
    (γ : Path d) (t : ℝ≥0) :
    s7CemeteryObservation U
        (MarkovProcess.LifetimePath.coordinate t
          (MarkovProcess.ContinuousPath.killAtExit U γ)) =
      if (t : ℝ≥0∞) < localityExitTime U γ then (1, γ t) else (0, 0) := by
  rw [s7_localityExitTime_eq]
  rw [MarkovProcess.ContinuousPath.coordinate_killAtExit]
  split_ifs <;> rfl

/-- Decode the cemetery coordinates at the dense times indexed by `I`. -/
noncomputable def s7FiniteTraceDecoder {d : ℕ} (U : Set (Vec d)) (I : Finset ℕ) (x : Vec d) :
    ((I.image (TopologicalSpace.denseSeq ℝ≥0)) → MarkovProcess.Cemetery U) →
      (I → Vec d × ℝ × Vec d) :=
  fun f n => (x, s7CemeteryObservation U
    (f ⟨TopologicalSpace.denseSeq ℝ≥0 n, Finset.mem_image_of_mem _ n.property⟩))

theorem s7_measurable_finiteTraceDecoder {d : ℕ} (U : Set (Vec d))
    (I : Finset ℕ) (x : Vec d) : Measurable (s7FiniteTraceDecoder U I x) := by
  apply Measurable.of_eval
  intro n
  exact measurable_const.prodMk ((s7_measurable_cemeteryObservation U).comp
    (measurable_pi_apply _))

/-- Finite killed traces are decoded cemetery observations at the same dense times. -/
theorem s7_trace_map_eq_decoded {d : ℕ}
    (P : MarkovProcess.SubMarkovKernelSemigroup (Vec d))
    (hP : P.IsConservative) (hK : P.KolmogorovRegular hP)
    (U : Set (Vec d)) (hU : IsOpen U) (x : U) (I : Finset ℕ) :
    ((MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP) x).map
        (fun γ => I.restrict (localityKilledTrace U γ)) =
      (((MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedProcess P hP U hU x).map
        (fun γ => fun t : I.image (TopologicalSpace.denseSeq ℝ≥0) =>
          MarkovProcess.LifetimePath.coordinate (t : ℝ≥0) γ)).map
            (s7FiniteTraceDecoder U I x)) := by
  let J := I.image (TopologicalSpace.denseSeq ℝ≥0)
  have hf : Measurable (fun γ : MarkovProcess.LifetimePath U =>
      fun t : J => MarkovProcess.LifetimePath.coordinate (t : ℝ≥0) γ) :=
    MarkovProcess.LifetimePath.measurable_coordinateFamily (fun t : J => (t : ℝ≥0))
  rw [MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedProcess_apply,
    Measure.map_map (s7_measurable_finiteTraceDecoder U I x) hf,
    Measure.map_map ((s7_measurable_finiteTraceDecoder U I x).comp hf)
      (MarkovProcess.ContinuousPath.measurable_killAtExit U hU)]
  apply Measure.map_congr
  filter_upwards [MarkovProcess.SubMarkovKernelSemigroup.IsConservative.ae_eval_zero_eq hP hK x] with γ hγ
  funext n
  simp only [Function.comp_apply, Finset.restrict, s7FiniteTraceDecoder]
  rw [s7_cemeteryObservation_killAtExit]
  simp [localityKilledTrace, localityKilledRecord, hγ]

/-- Equality of the killed kernels at starts in the domain gives equality of
    their restrictions to the domain. -/
theorem s7_killedKernelOn_eq_of_killedKernel_eq
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (ω ω' : FieldPair d) (hω : IsRegular Λ ω) (hω' : IsRegular Λ ω')
    (lam : ℝ) (U : Set (Vec d)) (hU : IsOpen U)
    (hpart : ∀ t : ℝ≥0, ∀ x ∈ U,
      MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedKernel
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω)
        (u2_regular_kernel_conservative hd ω lam Λ hΛ hω) U hU t x =
      MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedKernel
        (u2RegularC0KernelSemigroup hd ω' lam Λ hΛ hω')
        (u2_regular_kernel_conservative hd ω' lam Λ hΛ hω') U hU t x) :
    ∀ t : ℝ≥0,
      MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedKernelOn
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω)
        (u2_regular_kernel_conservative hd ω lam Λ hΛ hω) U hU t =
      MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedKernelOn
        (u2RegularC0KernelSemigroup hd ω' lam Λ hΛ hω')
        (u2_regular_kernel_conservative hd ω' lam Λ hΛ hω') U hU t := by
  intro t
  apply Kernel.ext
  intro x
  rw [MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedKernelOn_apply_eq,
    MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedKernelOn_apply_eq,
    hpart t x x.property]

/-- A common restricted killed kernel gives the same finite-dimensional
cemetery laws when both canonical continuous processes satisfy the regularity
assumptions of the killed-process theorem. -/
theorem s7_killed_finiteEvaluation_eq_of_kernelOn_eq
    {d : ℕ} (P Q : MarkovProcess.SubMarkovKernelSemigroup (Vec d))
    (hP : P.IsConservative) (hQ : Q.IsConservative)
    (hFP : P.IsFellerKernelSemigroup) (hFQ : Q.IsFellerKernelSemigroup)
    (hKP : P.KolmogorovRegular hP) (hKQ : Q.KolmogorovRegular hQ)
    (U : Set (Vec d)) (hU : IsOpen U)
    (h : ∀ t, MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedKernelOn
        P hP U hU t =
      MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedKernelOn
        Q hQ U hU t) (I : Finset ℝ≥0) (x : U) :
    (MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedProcess P hP U hU x).map
      (fun γ => fun i : I => MarkovProcess.LifetimePath.coordinate (i : ℝ≥0) γ) =
    (MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedProcess Q hQ U hU x).map
      (fun γ => fun i : I => MarkovProcess.LifetimePath.coordinate (i : ℝ≥0) γ) := by
  have heq :
      MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedSemigroup P hP U hU hFP hKP =
      MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedSemigroup Q hQ U hU hFQ hKQ := by
    apply MarkovProcess.SubMarkovKernelSemigroup.ext
    intro t
    exact h t
  rw [MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedProcess_map_finiteEvaluation
      P hP U hU hFP hKP I x,
    MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedProcess_map_finiteEvaluation
      Q hQ U hU hFQ hKQ I x, heq]

/-- Equal killed kernels give equal canonical killed-trace finite-dimensional laws. -/
theorem s7_canonical_killed_kernels_eq_on_open
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (ω ω' : FieldPair d) (hω : IsRegular Λ ω) (hω' : IsRegular Λ ω')
    (lam : ℝ) (U : Set (Vec d)) (hU : IsOpen U)
    (hK : (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω).KolmogorovRegular
      (u2_regular_kernel_conservative hd ω lam Λ hΛ hω))
    (hK' : (u2RegularC0KernelSemigroup hd ω' lam Λ hΛ hω').KolmogorovRegular
      (u2_regular_kernel_conservative hd ω' lam Λ hΛ hω'))
    (hpart : ∀ t : ℝ≥0, ∀ x ∈ U,
      MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedKernel
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω)
        (u2_regular_kernel_conservative hd ω lam Λ hΛ hω) U hU t x =
      MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedKernel
        (u2RegularC0KernelSemigroup hd ω' lam Λ hΛ hω')
        (u2_regular_kernel_conservative hd ω' lam Λ hΛ hω') U hU t x) :
    ∀ x ∈ U, ∀ I : Finset ℕ,
      ((MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousProcess
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) (u2_regular_kernel_conservative hd ω lam Λ hΛ hω)) x).map
        (fun γ => I.restrict (localityKilledTrace U γ)) =
      ((MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousProcess
        (u2RegularC0KernelSemigroup hd ω' lam Λ hΛ hω') (u2_regular_kernel_conservative hd ω' lam Λ hΛ hω')) x).map
        (fun γ => I.restrict (localityKilledTrace U γ)) := by
  intro x hx I
  let xU : U := ⟨x, hx⟩
  have hk := s7_killed_finiteEvaluation_eq_of_kernelOn_eq
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω)
    (u2RegularC0KernelSemigroup hd ω' lam Λ hΛ hω')
    (u2_regular_kernel_conservative hd ω lam Λ hΛ hω)
    (u2_regular_kernel_conservative hd ω' lam Λ hΛ hω')
    (u2RegularC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω)
    (u2RegularC0KernelSemigroup_isFeller hd ω' lam Λ hΛ hω') hK hK' U hU
    (s7_killedKernelOn_eq_of_killedKernel_eq hd Λ hΛ ω ω' hω hω' lam U hU hpart)
    (I.image (TopologicalSpace.denseSeq ℝ≥0)) xU
  calc
    _ = _ := s7_trace_map_eq_decoded _ _ hK U hU xU I
    _ = _ := congrArg (fun μ => μ.map (s7FiniteTraceDecoder U I x)) hk
    _ = _ := (s7_trace_map_eq_decoded _ _ hK' U hU xU I).symm

/-- Strict survival to `s + t` splits into survival to `s` and
survival for the path shifted by `s`. -/
theorem s7_killed_event_add {d : ℕ} (U : Set (Vec d)) (s t : ℝ≥0)
    (A : Set (Vec d)) :
    {γ : Path d | ((s + t : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ ∧ γ (s + t) ∈ A} =
      {γ : Path d | (s : ℝ≥0∞) < localityExitTime U γ ∧
        (t : ℝ≥0∞) < localityExitTime U (MarkovProcess.ContinuousPath.shift s γ) ∧
        (MarkovProcess.ContinuousPath.shift s γ) t ∈ A} := by
  ext γ
  simp only [Set.mem_setOf_eq, s7_localityExitTime_eq,
    MarkovProcess.ContinuousPath.coe_add_lt_exitTime_iff,
    MarkovProcess.ContinuousPath.shift_apply]
  tauto

/-- Killed traces of two supplied realizations in the same environment agree
at every starting point, without a killed-kernel or regularity assumption. -/
theorem s7_same_environment_killed_trace_fdd
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r r' : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1) (U : Set (Vec d)) (x : Vec d) (I : Finset ℕ) :
    (r.pathLaw x).map (fun γ => I.restrict (localityKilledTrace U γ)) =
      (r'.pathLaw x).map (fun γ => I.restrict (localityKilledTrace U γ)) := by
  rw [u6_same_canonical_fdd_path_laws_equal hd Λ hΛ ω hω lam h0 h1 r r']

/-- The complete countable killed-trace law is independent of the supplied
realization in a fixed regular environment. -/
theorem s7_same_environment_killed_trace_law
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r r' : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1) (U : Set (Vec d)) (x : Vec d) :
    (r.pathLaw x).map (localityKilledTrace U) =
      (r'.pathLaw x).map (localityKilledTrace U) := by
  rw [u6_same_canonical_fdd_path_laws_equal hd Λ hΛ ω hω lam h0 h1 r r']

/-- Countably many observations of the actual stopped path have the same joint
law for any two supplied realizations of the same environment. -/
theorem s7_same_environment_stopped_observations_law
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r r' : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1) (U : Set (Vec d)) (x : Vec d) (t : ℕ → ℝ≥0) :
    (r.pathLaw x).map (fun γ => fun n => localityStoppedPath U γ (t n)) =
      (r'.pathLaw x).map (fun γ => fun n => localityStoppedPath U γ (t n)) := by
  rw [u6_same_canonical_fdd_path_laws_equal hd Λ hΛ ω hω lam h0 h1 r r']

/-- The actual strict-survival marginal is independent of the supplied
realization in a fixed regular environment. -/
theorem s7_same_environment_killed_marginals
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r r' : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1) (U : Set (Vec d)) (t : ℝ≥0) (x : Vec d)
    (A : Set (Vec d)) :
    (r.pathLaw x) {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A} =
      (r'.pathLaw x) {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A} := by
  rw [u6_same_canonical_fdd_path_laws_equal hd Λ hΛ ω hω lam h0 h1 r r']


end EinsteinFull
