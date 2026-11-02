import EinsteinFull.Calculus.SunaS5UnforcedIdentification
import EinsteinFull.Work.W2.CorrectorCorrelationSupport
import EinsteinFull.Calculus.U3RealForceBoundedTests
import EinsteinFull.Work.W6.SamplewiseTemporalFubiniProof
import EinsteinFull.Calculus.U2C0ResolventTail

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

noncomputable section
namespace EinsteinFull

/-- Pathwise-only version of the supplied-law helper. -/
theorem u3_pathwise_unforced_supplied_endpoint_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (K ω) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let E : FieldPair d × Path d → FieldPair d :=
    fun z => translate (z.2 t) (reduce z.1)
  have hE : Measurable E := measurable_c2EnvironmentAt t
  have hmap := u2_supplied_annealed_environment_marginal (hpath := hpath) hd Q K hK t
  have hi : Integrable (fun z => f (E z)) (Q.measure ⊗ₘ K) := by
    apply (integrable_map_measure (Lp.stronglyMeasurable f).aestronglyMeasurable
      hE.aemeasurable).1
    rw [hmap]
    exact (Lp.memLp f).integrable (by norm_num)
  exact (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi |>.1


/-- Pathwise-only version of the supplied-law helper. -/
theorem u3_pathwise_unforced_supplied_endpoint_ae_eq
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (t : ℝ≥0) {f g : FieldPair d → ℂ} (hfg : f =ᵐ[reducedLaw Q] g) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂K ω,
      f (translate (γ t) (reduce ω)) = g (translate (γ t) (reduce ω)) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  let E : FieldPair d × Path d → FieldPair d :=
    fun z => translate (z.2 t) (reduce z.1)
  have hE : Measurable E := measurable_c2EnvironmentAt t
  have hmap : ∀ᵐ ρ ∂Measure.map E (Q.measure ⊗ₘ K), f ρ = g ρ := by
    rw [u2_supplied_annealed_environment_marginal (hpath := hpath) hd Q K hK t]
    exact hfg
  exact Measure.ae_ae_of_ae_compProd (ae_of_ae_map hE.aemeasurable hmap)


/-- Pathwise-only version of the supplied-law helper. -/
theorem u3_pathwise_unforced_path_endpoint_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨Y₀, hmarkov, hactual⟩ :=
    foundation_reduced_actual_kernel hd hΛ ⟨0, by omega⟩ 0
  let : IsMarkovKernel Y₀ := hmarkov
  let K : Kernel (FieldPair d) (Path d) :=
    Y₀.comap (fun ω => (0, ω)) (measurable_const.prodMk measurable_id)
  let : IsMarkovKernel K := inferInstance
  have hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y₀ (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact hactual ω hω
  have hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω) := hY₀
  have hu := reducedOriginLaw_ae_unique_of_pathwise (hpath := hpath) Q ⟨0, by omega⟩ 0 Y₀ Y hY₀ hY
  filter_upwards [u3_pathwise_unforced_supplied_endpoint_integrable (hpath := hpath) hd Q K hK t f,
    hu] with ω hi he
  change Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y₀ (0, ω)) at hi
  rw [← he]
  exact hi


/-- Pathwise-only version of the supplied-law helper. -/
theorem u3_pathwise_unforced_supplied_scalar_orbit_of_Laplace
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) :
    ∃ T : ℝ≥0 → Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q),
      (∀ t F, T t F =ᵐ[reducedLaw Q]
        MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) F) ∧
      ∀ (F : Lp ℝ 2 (reducedLaw Q)) (g : Lp ℂ 2 (reducedLaw Q))
        (L : ℂ →L[ℝ] ℝ) (φ : Lp ℝ 2 (reducedLaw Q) →L[ℝ] ℝ),
        (∀ s : ℝ, 0 < s →
          (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * φ (T t.toNNReal F)) =
          ∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
            φ (L.compLpL 2 (reducedLaw Q)
              (unforcedComplexEvolution Q ⟨0, by omega⟩ t.toNNReal g))) →
        ∀ t : ℝ≥0, φ (T t F) =
          φ (L.compLpL 2 (reducedLaw Q)
            (unforcedComplexEvolution Q ⟨0, by omega⟩ t g)) := by
  obtain ⟨T, hn, hr, hz, ha, hc⟩ :=
    u2_unforced_reduced_kernel_L2_strongly_continuous
      (hpath := hpath) hd Q K hK D hD hleft
  refine ⟨T, hr, ?_⟩
  intro F g L φ he t
  let P := L.compLpL 2 (reducedLaw Q)
  have hf : Continuous (fun t : ℝ≥0 => φ (T t F)) := φ.continuous.comp (hc F)
  have hg : Continuous (fun t : ℝ≥0 => φ (P (unforcedComplexEvolution Q ⟨0, by omega⟩ t g))) :=
    φ.continuous.comp (P.continuous.comp (continuous_unforcedComplexEvolution_apply Q ⟨0, by omega⟩ g))
  have hb (t : ℝ≥0) : |φ (T t F)| +
      |φ (P (unforcedComplexEvolution Q ⟨0, by omega⟩ t g))| ≤
        ‖φ‖ * ‖F‖ + ‖φ‖ * (‖P‖ * ‖g‖) := by
    have ht : ‖T t F‖ ≤ ‖F‖ := by
      calc
        ‖T t F‖ ≤ ‖T t‖ * ‖F‖ := (T t).le_opNorm F
        _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right (hn t) (norm_nonneg _)
        _ = ‖F‖ := one_mul _
    have hs : ‖unforcedComplexEvolution Q ⟨0, by omega⟩ t g‖ ≤ ‖g‖ := by
      calc
        ‖unforcedComplexEvolution Q ⟨0, by omega⟩ t g‖ ≤
            ‖unforcedComplexEvolution Q ⟨0, by omega⟩ t‖ * ‖g‖ :=
          (unforcedComplexEvolution Q ⟨0, by omega⟩ t).le_opNorm g
        _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right
          (norm_unforcedComplexEvolution_le Q ⟨0, by omega⟩ t) (norm_nonneg _)
        _ = ‖g‖ := one_mul _
    rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact add_le_add
      ((φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _)))
      ((φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((P.le_opNorm _).trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _))) (norm_nonneg _)))
  have h := s5_continuous_bounded_scalar_Laplace_unique _ _ hf hg _ hb he
  exact congrFun h t


/-- Scalar observations of the analytic unforced orbit have the corresponding
projection of the actual horizontal resolvent as their Laplace transform. -/
theorem u3_unforced_scalar_laplace_eq_resolvent
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (g : Lp ℂ 2 (reducedLaw Q)) (L : ℂ →L[ℝ] ℝ)
    (φ : Lp ℝ 2 (reducedLaw Q) →L[ℝ] ℝ) (s : ℝ) (hs : 0 < s) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
      φ (L.compLpL 2 (reducedLaw Q) (unforcedComplexEvolution Q i t.toNNReal g))) =
      φ (L.compLpL 2 (reducedLaw Q) (unforcedComplexResolvent Q i s hs g)) := by
  let P := isComplexEnvironmentSemigroup_unforcedComplexEvolution Q i
  let A := φ.comp (L.compLpL 2 (reducedLaw Q))
  have h := A.integral_comp_comm (P.integrable_laplace_orbit s hs g)
  rw [P.laplace_orbit_eq_resolvent s hs g] at h
  simpa only [A, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul] using h


/-- The missing discounted weak identification for the actual supplied
kernel and analytic unforced evolution, tested against every real dual vector. -/
def u3UnforcedWeakLaplaceIdentity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) (D : FieldPair d → FieldPair d)
    (hD : Measurable D) : Prop :=
  ∀ (T : ℝ≥0 → Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q)),
    (∀ t F, T t F =ᵐ[reducedLaw Q]
      MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) F) →
    ∀ (g : Lp ℂ 2 (reducedLaw Q)) (L : ℂ →L[ℝ] ℝ)
      (φ : Lp ℝ 2 (reducedLaw Q) →L[ℝ] ℝ) (s : ℝ), 0 < s →
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        φ (T t.toNNReal (L.compLpL 2 (reducedLaw Q) g))) =
      ∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        φ (L.compLpL 2 (reducedLaw Q)
          (unforcedComplexEvolution Q ⟨0, by omega⟩ t.toNNReal g))

/-- The discounted supplied-kernel orbit equals the analytic resolvent,
when tested against arbitrary continuous real dual vectors. -/
def u3UnforcedKernelResolventIdentity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) (D : FieldPair d → FieldPair d)
    (hD : Measurable D) : Prop :=
  ∀ (T : ℝ≥0 → Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q)),
    (∀ t F, T t F =ᵐ[reducedLaw Q]
      MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) F) →
    ∀ (g : Lp ℂ 2 (reducedLaw Q)) (L : ℂ →L[ℝ] ℝ)
      (φ : Lp ℝ 2 (reducedLaw Q) →L[ℝ] ℝ) (s : ℝ) (hs : 0 < s),
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        φ (T t.toNNReal (L.compLpL 2 (reducedLaw Q) g))) =
      φ (L.compLpL 2 (reducedLaw Q)
        (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g))

/-- The actual analytic Laplace formula converts the kernel-resolvent
comparison into the weak Laplace identity. -/
theorem u3_unforced_weak_laplace_of_kernel_resolvent
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) (D : FieldPair d → FieldPair d)
    (hD : Measurable D) (hres : u3UnforcedKernelResolventIdentity hd Q K D hD) :
    u3UnforcedWeakLaplaceIdentity hd Q K D hD := by
  intro T hrep g L φ s hs
  rw [u3_unforced_scalar_laplace_eq_resolvent Q ⟨0, by omega⟩ g L φ s hs]
  exact hres T hrep g L φ s hs

/-- The weak Laplace identity determines the actual supplied real L² action
on every real projection of the complex unforced evolution. -/
theorem u3_unforced_projected_action_of_weak_laplace
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce)
    (hlap : u3UnforcedWeakLaplaceIdentity hd Q K D hD) :
    ∃ T : ℝ≥0 → Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q),
      (∀ t F, T t F =ᵐ[reducedLaw Q]
        MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) F) ∧
      ∀ (g : Lp ℂ 2 (reducedLaw Q)) (L : ℂ →L[ℝ] ℝ) (t : ℝ≥0),
        T t (L.compLpL 2 (reducedLaw Q) g) =
          L.compLpL 2 (reducedLaw Q)
            (unforcedComplexEvolution Q ⟨0, by omega⟩ t g) := by
  obtain ⟨T, hrep, hscalar⟩ :=
    u3_pathwise_unforced_supplied_scalar_orbit_of_Laplace (hpath := hpath) hd Q K hK D hD hleft
  refine ⟨T, hrep, ?_⟩
  intro g L t
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro φ
  exact hscalar (L.compLpL 2 (reducedLaw Q) g) g L φ
    (fun s hs => hlap T hrep g L φ s hs) t


/-- Conditional path identification from the actual kernel's weak Laplace identity. -/
theorem u3_unforced_kernel_endpoint_of_weak_laplace
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce)
    (hlap : u3UnforcedWeakLaplaceIdentity hd Q K D hD)
    (t : ℝ≥0) (F : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      unforcedComplexEvolution Q ⟨0, by omega⟩ t F (reduce ω) =
        ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂K ω := by
  obtain ⟨T, hrep, hproj⟩ :=
    u3_unforced_projected_action_of_weak_laplace (hpath := hpath) hd Q K hK D hD hleft hlap
  let E : FieldPair d × Path d → FieldPair d :=
    fun z => translate (z.2 t) (reduce z.1)
  have hE : Measurable E := measurable_c2EnvironmentAt t
  have htrans (L : ℂ →L[ℝ] ℝ) :
      ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂K ω,
        (L.compLpL 2 (reducedLaw Q) F) (E (ω,γ)) = L (F (E (ω,γ))) := by
    have hm := L.coeFn_compLpL F
    have hmap : ∀ᵐ ρ ∂Measure.map E (Q.measure ⊗ₘ K),
        (L.compLpL 2 (reducedLaw Q) F) ρ = L (F ρ) := by
      rw [u2_supplied_annealed_environment_marginal (hpath := hpath) hd Q K hK t]
      exact hm
    exact Measure.ae_ae_of_ae_compProd (ae_of_ae_map hE.aemeasurable hmap)
  have hpoint (L : ℂ →L[ℝ] ℝ) : ∀ᵐ ω ∂Q.measure,
      (L.compLpL 2 (reducedLaw Q) (unforcedComplexEvolution Q ⟨0, by omega⟩ t F)) (reduce ω) =
        ∫ γ : Path d, (L.compLpL 2 (reducedLaw Q) F) (E (ω,γ)) ∂K ω := by
    have hr := (Probability.measurableEmbedding_reduce d).ae_map_iff.mp
      (hrep t (L.compLpL 2 (reducedLaw Q) F))
    filter_upwards [hr] with ω hω
    rw [← hproj F L t, hω]
    change (∫ ρ, (L.compLpL 2 (reducedLaw Q) F) ρ ∂
      c2ReducedEnvironmentKernel K D hD t (reduce ω)) = _
    rw [c2ReducedEnvironmentKernel_pullback K D hD hleft, c2EnvironmentKernel_apply]
    have hm : Measurable (fun γ : Path d => translate (γ t) (reduce ω)) :=
      hE.comp (measurable_const.prodMk measurable_id)
    exact integral_map hm.aemeasurable
      (Lp.stronglyMeasurable (L.compLpL 2 (reducedLaw Q) F)).aestronglyMeasurable
  have hout (L : ℂ →L[ℝ] ℝ) : ∀ᵐ ω ∂Q.measure,
      (L.compLpL 2 (reducedLaw Q) (unforcedComplexEvolution Q ⟨0, by omega⟩ t F)) (reduce ω) =
        L (unforcedComplexEvolution Q ⟨0, by omega⟩ t F (reduce ω)) :=
    (Probability.measurableEmbedding_reduce d).ae_map_iff.mp (L.coeFn_compLpL _)
  filter_upwards [hpoint Complex.reCLM, hpoint Complex.imCLM,
    htrans Complex.reCLM, htrans Complex.imCLM,
    hout Complex.reCLM, hout Complex.imCLM,
    u3_pathwise_unforced_supplied_endpoint_integrable (hpath := hpath) hd Q K hK t F]
    with ω hpRe hpIm htRe htIm hoRe hoIm hi
  simp only [Complex.reCLM_apply] at hpRe htRe hoRe
  simp only [Complex.imCLM_apply] at hpIm htIm hoIm
  apply Complex.ext
  · rw [← hoRe, hpRe, integral_congr_ae htRe]
    exact integral_re hi
  · rw [← hoIm, hpIm, integral_congr_ae htIm]
    exact integral_im hi

/-- Conditional bounded-test identification for the original supplied law. -/
theorem u3_unforced_bounded_test_identity_of_weak_laplace
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (hKY : ∀ᵐ ω ∂Q.measure, K ω = Y (0,ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce)
    (hlap : u3UnforcedWeakLaplaceIdentity hd Q K D hD)
    (t : ℝ≥0) (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (F : Lp ℂ 2 (reducedLaw Q))
    (hF : F =ᵐ[reducedLaw Q] fun ω => g ω) :
    ∀ᵐ ω ∂Q.measure,
      forcedComplexEvolution Q ⟨0, by omega⟩ 0 t F (reduce ω) =
        ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂Y (0,ω) := by
  have he := u3_pathwise_unforced_supplied_endpoint_ae_eq (hpath := hpath) hd Q K hK t hF
  have ha := u3_unforced_kernel_endpoint_of_weak_laplace
    (hpath := hpath) hd Q K hK D hD hleft hlap t F
  filter_upwards [he, ha, hKY] with ω heω haω hKYω
  rw [← s5_unforced_evolution_eq_zero_force Q ⟨0, by omega⟩, haω, ← hKYω]
  exact integral_congr_ae heω


/-- The bounded-test endpoint follows from the explicit weak Laplace identity
for each Markov kernel representing the supplied origin law. -/
theorem u3_unforced_bounded_test_of_weak_laplace_family
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0,ω)))
    (hlap : ∀ (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K],
      (∀ᵐ ω ∂Q.measure, K ω = Y (0,ω)) →
      ∀ (D : FieldPair d → FieldPair d) (hD : Measurable D),
      Function.LeftInverse D reduce → u3UnforcedWeakLaplaceIdentity hd Q K D hD)
    (t : ℝ≥0) (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (F : Lp ℂ 2 (reducedLaw Q))
    (hF : F =ᵐ[reducedLaw Q] fun ω => g ω) :
    ∀ᵐ ω ∂Q.measure,
      forcedComplexEvolution Q ⟨0, by omega⟩ 0 t F (reduce ω) =
        ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂Y (0,ω) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) :=
    hY.mono fun _ h => h.1
  obtain ⟨K, hKY, hmarkov⟩ := Kernel.exists_ae_eq_isMarkovKernel hprob
    (IsProbabilityMeasure.ne_zero Q.measure)
  let : IsMarkovKernel K := hmarkov
  have hKY' : ∀ᵐ ω ∂Q.measure, K ω = Y (0,ω) := hKY.mono fun _ h => h.symm
  have hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω) := by
    filter_upwards [hKY', hY] with ω he hp
    simpa only [he] using hp
  obtain ⟨D, hD, hleft⟩ := Probability.exists_measurable_leftInverse_reduce d
  exact u3_unforced_bounded_test_identity_of_weak_laplace (hpath := hpath) hd Q Y K
    hK hKY' D hD hleft (hlap K hKY' D hD hleft) t g F hF


#print axioms u3_unforced_weak_laplace_of_kernel_resolvent
#print axioms u3_unforced_scalar_laplace_eq_resolvent
#print axioms u3_unforced_bounded_test_of_weak_laplace_family
#print axioms u3_unforced_projected_action_of_weak_laplace
#print axioms u3_unforced_kernel_endpoint_of_weak_laplace
#print axioms u3_unforced_bounded_test_identity_of_weak_laplace

end EinsteinFull

open Set

namespace EinsteinFull

/-- Finite-time L² occupation for the given unforced law, from its invariant marginal. -/
theorem u3_unforced_finite_time_joint_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (T : ℝ≥0) (r : FieldPair d → ℝ) (hm : Measurable r)
    (hr : MemLp r 2 (reducedLaw Q)) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      (∀ᵐ ω ∂Q.measure, Y (0, ω) = K ω) ∧
      Integrable (fun p : ℝ × (FieldPair d × Path d) =>
        |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|)
        ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (Q.measure ⊗ₘ K)) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) :=
    hY.mono fun _ h => h.1
  obtain ⟨K, hK, hmarkov⟩ := Kernel.exists_ae_eq_isMarkovKernel hprob
    (IsProbabilityMeasure.ne_zero Q.measure)
  let : IsMarkovKernel K := hmarkov
  have hK' : ∀ᵐ ω ∂Q.measure, Y (0, ω) = K ω := hK
  have hKmp : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω) := by
    filter_upwards [hK', hY] with ω he hm
    simpa only [← he] using hm
  refine ⟨K, hmarkov, hK', ?_⟩
  let E : ℝ × (FieldPair d × Path d) → FieldPair d := fun p =>
    translate (p.2.2 p.1.toNNReal) (reduce p.2.1)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp ((continuous_snd.comp continuous_snd).prodMk
        (continuous_real_toNNReal.comp continuous_fst))).prodMk
        (Probability.continuous_reduce.comp (continuous_fst.comp continuous_snd)))).measurable
  have hi := (u2_supplied_discounted_occupation_L2_bound (hpath := hpath) hd Q K hKmp 1
    (by norm_num) r hm hr).1
  have hi' := hi.mono_measure (Measure.prod_mono
    (Measure.restrict_mono_set volume (fun t (ht : t ∈ Set.Ioc (0 : ℝ) (T : ℝ)) => ht.1)) le_rfl)
  apply (hi'.const_mul (Real.exp (T : ℝ))).mono'
    (continuous_abs.measurable.comp (hm.comp hE)).aestronglyMeasurable
  rw [Measure.restrict_prod_eq_prod_univ]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with p hp
  have hexp : (1 : ℝ) ≤ Real.exp (T : ℝ) * Real.exp (-1 * p.1) := by
    have h := Real.exp_le_exp.mpr (show (0 : ℝ) ≤ (T : ℝ) + -p.1 by linarith [hp.1.2])
    simpa only [Real.exp_zero, Real.exp_add, neg_one_mul] using h
  simp only [Real.norm_eq_abs, Function.comp_apply, abs_abs]
  simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right hexp (abs_nonneg (r (E p)))

/-- Generator occupation is pathwise integrable for the same supplied law. -/
theorem u3_unforced_resolvent_generator_path_occupation
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g) G)
    (L : ℂ →L[ℝ] ℝ) (T : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      IntegrableOn (fun t : ℝ => |envGenerator hd 0 (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g v)))
          (translate (γ t.toNNReal) (reduce ω))|) (Set.Ioc 0 (T : ℝ)) volume := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  obtain ⟨a, ham, ha, hae⟩ :=
    s5_unforced_resolvent_generator_representatives hd Q ⟨0, by omega⟩ s hs g hG L
  obtain ⟨K, hmarkov, hK, hi⟩ :=
    u3_unforced_finite_time_joint_integrable (hpath := hpath) hd Q Y hY T (a n) (ham n) (ha n)
  let : IsMarkovKernel K := hmarkov
  have hsections := Measure.ae_ae_of_ae_compProd hi.prod_left_ae
  have heq := u3_supplied_force_ae_eq_occupation_of_pathwise (hpath := hpath) hd Q
    ⟨0, by omega⟩ 0 Y hY (a n) _ (hae n)
  filter_upwards [hK, hsections, heq] with ω hKω hsectionω heqω
  rw [← hKω] at hsectionω
  filter_upwards [hsectionω, heqω] with γ hsectionγ heqγ
  have ht := ae_restrict_of_ae_restrict_of_subset
    (fun t (ht : t ∈ Set.Ioc (0 : ℝ) (T : ℝ)) => ht.1) heqγ
  apply hsectionγ.congr
  filter_upwards [ht] with t ht
  exact congrArg abs ht

/-- The same generator occupation is integrable over each supplied path law. -/
theorem u3_unforced_resolvent_generator_quenched_occupation
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g) G)
    (L : ℂ →L[ℝ] ℝ) (T : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂Q.measure, Integrable (fun γ : Path d =>
      ∫ t in Set.Ioc 0 (T : ℝ), |envGenerator hd 0 (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g v)))
          (translate (γ t.toNNReal) (reduce ω))|) (Y (0, ω)) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  obtain ⟨a, ham, ha, hae⟩ :=
    s5_unforced_resolvent_generator_representatives hd Q ⟨0, by omega⟩ s hs g hG L
  obtain ⟨K, hmarkov, hK, hi⟩ :=
    u3_unforced_finite_time_joint_integrable (hpath := hpath) hd Q Y hY T (a n) (ham n) (ha n)
  let : IsMarkovKernel K := hmarkov
  have hn := hi.integral_norm_prod_right
  have hn' : Integrable (fun p : FieldPair d × Path d =>
      ∫ t in Set.Ioc 0 (T : ℝ), |a n (translate (p.2 t.toNNReal) (reduce p.1))|)
      (Q.measure ⊗ₘ K) := by
    simpa only [Real.norm_eq_abs, abs_abs] using hn
  have hsections := (Measure.integrable_compProd_iff hn'.aestronglyMeasurable).mp hn'
  have heq := u3_supplied_force_ae_eq_occupation_of_pathwise (hpath := hpath) hd Q
    ⟨0, by omega⟩ 0 Y hY (a n) _ (hae n)
  filter_upwards [hK, hsections.1, heq] with ω hKω hsectionω heqω
  rw [← hKω] at hsectionω
  apply hsectionω.congr
  filter_upwards [heqω] with γ heqγ
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) heqγ] with t ht
  exact congrArg abs ht



/-- The unforced resolvent generator compensator is quenched integrable. -/
theorem u3_unforced_resolvent_generator_compensator_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g) G)
    (L : ℂ →L[ℝ] ℝ) (T : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂Q.measure, Integrable (fun γ : Path d =>
      ∫ t in Set.Ioc 0 (T : ℝ), envGenerator hd 0 (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g v)))
          (translate (γ t.toNNReal) (reduce ω))) (Y (0, ω)) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  obtain ⟨a, ham, ha, hae⟩ :=
    s5_unforced_resolvent_generator_representatives hd Q ⟨0, by omega⟩ s hs g hG L
  obtain ⟨K, hmarkov, hK, hi⟩ :=
    u3_unforced_finite_time_joint_integrable
      (hpath := hpath) hd Q Y hY T (a n) (ham n) (ha n)
  let : IsMarkovKernel K := hmarkov
  let E : ℝ × (FieldPair d × Path d) → FieldPair d := fun p =>
    translate (p.2.2 p.1.toNNReal) (reduce p.2.1)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp ((continuous_snd.comp continuous_snd).prodMk
        (continuous_real_toNNReal.comp continuous_fst))).prodMk
        (Probability.continuous_reduce.comp (continuous_fst.comp continuous_snd)))).measurable
  have hj : Integrable (fun p : ℝ × (FieldPair d × Path d) => a n (E p))
      ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod (Q.measure ⊗ₘ K)) := by
    apply hi.mono' ((ham n).comp hE).aestronglyMeasurable
    filter_upwards [] with p
    simp only [Real.norm_eq_abs, Function.comp_apply, E, le_refl]
  have hn := hj.integral_prod_right
  have hsections := (Measure.integrable_compProd_iff hn.aestronglyMeasurable).mp hn
  have heq := u3_supplied_force_ae_eq_occupation_of_pathwise (hpath := hpath) hd Q
    ⟨0, by omega⟩ 0 Y hY (a n) _ (hae n)
  filter_upwards [hK, hsections.1, heq] with ω hKω hsectionω heqω
  rw [← hKω] at hsectionω
  apply hsectionω.congr
  filter_upwards [heqω] with γ heqγ
  apply integral_congr_ae
  exact ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) heqγ



/-- The unforced supplied law integrates real L² observations at fixed times. -/
theorem u3_unforced_real_endpoint_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (t : ℝ≥0) (a : FieldPair d → ℝ)
    (ha : MemLp a 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure, Integrable
      (fun γ : Path d => a (translate (γ t) (reduce ω))) (Y (0, ω)) := by
  let A : FieldPair d → ℂ := fun w => (a w : ℂ)
  have hA : MemLp A 2 (reducedLaw Q) := ha.ofReal
  let F : Lp ℂ 2 (reducedLaw Q) := hA.toLp A
  have hi := u3_pathwise_unforced_path_endpoint_integrable (hpath := hpath) hd Q Y hY t F
  have he := s5_unforced_path_endpoint_ae_eq (hpath := hpath) hd Q Y hY t hA.coeFn_toLp
  filter_upwards [hi, he] with ω hiω heω
  have hr := Complex.reCLM.integrable_comp hiω
  apply hr.congr
  filter_upwards [heω] with γ hγ
  simpa only [A, Complex.ofReal_re, Complex.reCLM_apply] using congrArg Complex.re hγ

/-- Each unforced mollified resolvent orbit is a true supplied-law martingale. -/
theorem u3_unforced_resolvent_orbit_martingale
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (rhs : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs) G)
    (L : ℂ →L[ℝ] ℝ) (n : ℕ) :
    ∀ᵐ ω ∂Q.measure,
      Martingale (External.Bass.compensatedTest (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ 0)
        (orbit (horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs v))) (reduce ω)))
        (External.Bass.filtration d)
        ((Y (0, ω)).map (External.Bass.pathMeasurableEquiv d).symm) := by
  let lam : ℝ := 0
  let f := unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs
  let g := (s : ℂ) • f - rhs
  have hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g := by
    simpa [lam, f, g] using unforcedComplexResolvent_spec Q ⟨0, by omega⟩ s hs rhs
  let V : FieldPair d → ℝ := fun v => L (f v)
  let M := horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
  have hVm : Measurable V := L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable
  have hV : MemLp V 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp f)
  have hb := fun N : ℕ => u3_supplied_force_mollified_orbit_integrable_horizon_bound_of_deps
    (hpath := hpath) hd Q ⟨0, by omega⟩ lam Y hY _
    (Entropy.contDiff_unitMassScaledMollifier _).continuous
    (Entropy.hasCompactSupport_unitMassScaledMollifier (Entropy.scaleSeq_pos n))
    V hVm hV (N : ℝ≥0)
  have ho := fun N : ℕ => u3_unforced_resolvent_generator_quenched_occupation
    (hpath := hpath) hd Q Y hY s hs rhs hG L (N : ℝ≥0) n
  have hp := fun N : ℕ => u3_unforced_resolvent_generator_path_occupation
    (hpath := hpath) hd Q Y hY s hs rhs hG L (N : ℝ≥0) n
  filter_upwards [Q.regular, hY, ae_all_iff.mpr hb, ae_all_iff.mpr ho,
    ae_all_iff.mpr hp, u3_signed_graph_mollified_orbit_local_martingale_of_pathwise
      (hpath := hpath) hd Q lam s hs Y hY f g hfg hG L (Entropy.scaleSeq_pos n)]
    with ω hω hP hbω hoω hpω hlocal
  let : IsProbabilityMeasure (Y (0, ω)) := hP.1
  let e := External.Bass.pathMeasurableEquiv d
  let P := (Y (0, ω)).map e.symm
  let : IsProbabilityMeasure P := inferInstance
  have hsymmetric : ∀ x j k, (reduce ω).1 x j k = (reduce ω).1 x k j := by
    intro x j k
    have he := congrArg (fun A : Mat d => A j k) (reducedCoefficient_symm hω x)
    exact he.symm
  have he (x : Vec d) : envGenerator hd lam M (translate x (reduce ω)) =
      External.Bass.generator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ lam) (orbit M (reduce ω)) x := by
    exact u3_signed_envGenerator_eq_svGenerator hd (reduce ω) M lam hsymmetric x
  apply u3_compensated_local_martingale_of_natural_occupation_bound hlocal.2
  · intro N
    obtain ⟨H, hH, hbH⟩ := hbω N
    refine ⟨H ∘ e, ?_, ?_⟩
    · apply (integrable_map_equiv e.symm (H ∘ e)).2
      simpa [Function.comp_def] using hH
    · exact Filter.Eventually.of_forall fun γ t ht => hbH (e γ) t ht
  · intro N
    apply (integrable_map_equiv e.symm _).2
    change Integrable (fun γ : Path d => ∫ u in Set.Ioc (0 : ℝ) (N : ℝ),
      |External.Bass.generator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ lam)
        (orbit M (reduce ω)) (γ u.toNNReal)|) (Y (0, ω))
    simpa only [← he, NNReal.coe_natCast] using hoω N
  · intro N
    have hmap : ∀ᵐ γ ∂P.map e, IntegrableOn
        (fun u : ℝ => |External.Bass.generator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ lam)
          (orbit M (reduce ω)) (e.symm γ u.toNNReal)|) (Set.Ioc 0 (N : ℝ)) volume := by
      simpa only [P, e, External.Bass.map_pathMeasurableEquiv_symm_roundtrip,
        External.Bass.pathMeasurableEquiv_symm_apply, ← he,
        NNReal.coe_natCast] using hpω N
    have hh := ae_of_ae_map e.measurable.aemeasurable hmap
    simpa only [e, MeasurableEquiv.symm_apply_apply] using hh


/-- Finite-time Dynkin identity for mollified unforced resolvent orbits. -/
theorem u3_unforced_resolvent_mollified_dynkin
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (rhs : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs) G)
    (L : ℂ →L[ℝ] ℝ) (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs v))
          (translate (γ T) (reduce ω)) ∂Y (0, ω)) -
      horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs v)) (reduce ω) =
      ∫ γ : Path d, (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd 0 (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs v)))
          (translate (γ u.toNNReal) (reduce ω))) ∂Y (0, ω) := by
  let lam : ℝ := 0
  let f := unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs
  let V : FieldPair d → ℝ := fun v => L (f v)
  let M := horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
  have hVm : Measurable V := L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable
  have hV : MemLp V 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp f)
  have hM : MemLp M 2 (reducedLaw Q) :=
    Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q)
      (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top hVm hV
  filter_upwards [Q.regular, hY,
    u3_unforced_resolvent_orbit_martingale (hpath := hpath) hd Q s hs Y hY rhs hG L n,
    u3_unforced_real_endpoint_integrable (hpath := hpath) hd Q Y hY T M hM,
    u3_unforced_real_endpoint_integrable (hpath := hpath) hd Q Y hY 0 M hM,
    u3_unforced_resolvent_generator_compensator_integrable (hpath := hpath) hd Q Y hY s hs rhs hG L T n]
    with ω hω hP hmart ht h0 hc
  let : IsProbabilityMeasure (Y (0, ω)) := hP.1
  have hsymmetric : ∀ x j k, (reduce ω).1 x j k = (reduce ω).1 x k j := by
    intro x j k
    have he := congrArg (fun A : Mat d => A j k) (reducedCoefficient_symm hω x)
    exact he.symm
  have he (x : Vec d) : envGenerator hd lam M (translate x (reduce ω)) =
      External.Bass.generator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ lam) (orbit M (reduce ω)) x := by
    exact u3_signed_envGenerator_eq_svGenerator hd (reduce ω) M lam hsymmetric x
  have hz := hmart.setIntegral_eq (show (0 : ℝ≥0) ≤ T from bot_le) MeasurableSet.univ
  have hz' : (∫ γ : External.Bass.Path d, External.Bass.compensatedTest
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ lam)
      (orbit M (reduce ω)) T γ ∂(Y (0, ω)).map (External.Bass.pathMeasurableEquiv d).symm) = 0 := by
    simpa [External.Bass.compensatedTest] using hz.symm
  rw [integral_map_equiv] at hz'
  have hz'' : (∫ γ : Path d, M (translate (γ T) (reduce ω)) -
      M (translate (γ 0) (reduce ω)) - (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd lam M (translate (γ u.toNNReal) (reduce ω))) ∂Y (0, ω)) = 0 := by
    have hzinterval : (∫ γ : Path d, M (translate (γ T) (reduce ω)) -
        M (translate (γ 0) (reduce ω)) - (∫ u in (0 : ℝ)..(T : ℝ),
          envGenerator hd lam M (translate (γ u.toNNReal) (reduce ω))) ∂Y (0, ω)) = 0 := by
      simpa only [External.Bass.compensatedTest, External.Bass.pathMeasurableEquiv_symm_apply,
        orbit, ← he] using hz'
    convert hzinterval using 1
    apply integral_congr_ae
    filter_upwards [] with γ
    have hi : (∫ u in (0 : ℝ)..(T : ℝ), envGenerator hd lam M
        (translate (γ u.toNNReal) (reduce ω))) =
        ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), envGenerator hd lam M
          (translate (γ u.toNNReal) (reduce ω)) := intervalIntegral.integral_of_le T.property
    rw [hi]
  have hstart : (∫ γ : Path d, M (translate (γ 0) (reduce ω)) ∂Y (0, ω)) = M (reduce ω) := by
    calc
      _ = ∫ _ : Path d, M (reduce ω) ∂Y (0, ω) := integral_congr_ae
        (hP.2.1.mono fun _ h => by simp only [h, translate_zero])
      _ = M (reduce ω) := by simp
  change (∫ γ : Path d, M (translate (γ T) (reduce ω)) ∂Y (0, ω)) - M (reduce ω) = _
  have hc' : Integrable (fun γ : Path d => ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      envGenerator hd lam M (translate (γ u.toNNReal) (reduce ω))) (Y (0, ω)) := hc
  change (∫ γ : Path d, ((fun γ : Path d => M (translate (γ T) (reduce ω))) -
    (fun γ : Path d => M (translate (γ 0) (reduce ω)))) γ -
      (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), envGenerator hd lam M
        (translate (γ u.toNNReal) (reduce ω))) ∂Y (0, ω)) = 0 at hz''
  rw [integral_sub (ht.sub h0) hc'] at hz''
  simp only [Pi.sub_apply] at hz''
  rw [integral_sub ht h0, hstart] at hz''
  exact sub_eq_zero.mp hz''



/-- For an L² observable, finite-horizon path and time integration may be
interchanged for almost every supplied unforced law. -/
theorem u3_unforced_occupation_fubini
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (T : ℝ≥0) (r : FieldPair d → ℝ) (hm : Measurable r)
    (hr : MemLp r 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun p : Path d × ℝ =>
        r (translate (p.1 p.2.toNNReal) (reduce ω)))
          ((Y (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) ∧
      (∫ γ : Path d, (∫ t in Set.Ioc 0 (T : ℝ),
        r (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω)) =
      ∫ t in Set.Ioc 0 (T : ℝ), ∫ γ : Path d,
        r (translate (γ t.toNNReal) (reduce ω)) ∂Y (0, ω) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  obtain ⟨K, hmarkov, hK, hi⟩ :=
    u3_unforced_finite_time_joint_integrable
      (hpath := hpath) hd Q Y hY T r hm hr
  let : IsMarkovKernel K := hmarkov
  let E : ℝ × (FieldPair d × Path d) → FieldPair d := fun p =>
    translate (p.2.2 p.1.toNNReal) (reduce p.2.1)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp ((continuous_snd.comp continuous_snd).prodMk
        (continuous_real_toNNReal.comp continuous_fst))).prodMk
        (Probability.continuous_reduce.comp (continuous_fst.comp continuous_snd)))).measurable
  have hi' : Integrable (fun p : ℝ × (FieldPair d × Path d) => r (E p))
      ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod (Q.measure ⊗ₘ K)) := by
    apply hi.mono' (hm.comp hE).aestronglyMeasurable
    filter_upwards [] with p
    simp only [Real.norm_eq_abs, Function.comp_apply, E, le_refl]
  have htime := Measure.ae_ae_of_ae_compProd hi'.prod_left_ae
  have hn := hi'.integral_norm_prod_right
  have hsections := (Measure.integrable_compProd_iff hn.aestronglyMeasurable).mp hn
  filter_upwards [hK, htime, hsections.1] with ω hKω htimeω hnormω
  let : IsProbabilityMeasure (Y (0, ω)) := by rw [hKω]; infer_instance
  rw [← hKω] at htimeω hnormω
  have hmeas : Measurable (fun p : Path d × ℝ =>
      r (translate (p.1 p.2.toNNReal) (reduce ω))) := by
    apply hm.comp
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_fst.prodMk
        (continuous_real_toNNReal.comp continuous_snd))).prodMk continuous_const)).measurable
  have hp : Integrable (fun p : Path d × ℝ =>
      r (translate (p.1 p.2.toNNReal) (reduce ω)))
      ((Y (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    exact ⟨htimeω, hnormω⟩
  exact ⟨hp, (integral_prod _ hp).symm.trans (integral_prod_symm _ hp)⟩



/-- Finite-time Dynkin identity with time integrated after path expectation. -/
theorem u3_unforced_resolvent_mollified_dynkin_time_first
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (rhs : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs) G)
    (L : ℂ →L[ℝ] ℝ) (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs v))
          (translate (γ T) (reduce ω)) ∂Y (0, ω)) -
      horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs v)) (reduce ω) =
      ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        envGenerator hd 0 (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs v)))
          (translate (γ u.toNNReal) (reduce ω)) ∂Y (0, ω) := by
  obtain ⟨a, ham, ha, hae⟩ :=
    s5_unforced_resolvent_generator_representatives hd Q ⟨0, by omega⟩ s hs rhs hG L
  filter_upwards [u3_unforced_resolvent_mollified_dynkin (hpath := hpath) hd Q s hs Y hY rhs hG L n T,
    u3_unforced_occupation_fubini (hpath := hpath) hd Q Y hY T (a n) (ham n) (ha n),
    u3_supplied_force_ae_eq_occupation_of_pathwise (hpath := hpath) hd Q ⟨0, by omega⟩ 0 Y hY (a n) _ (hae n),
    u3_supplied_force_ae_eq_time_first_occupation_of_pathwise (hpath := hpath) hd Q ⟨0, by omega⟩ 0 Y hY T (a n) _ (hae n)]
    with ω hdyn hfub hpathEq htimeEq
  rw [hdyn]
  calc
    _ = ∫ γ : Path d, (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        a n (translate (γ u.toNNReal) (reduce ω))) ∂Y (0, ω) := by
      apply integral_congr_ae
      filter_upwards [hpathEq] with γ hγ
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) hγ] with u hu
      exact hu.symm
    _ = ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        a n (translate (γ u.toNNReal) (reduce ω)) ∂Y (0, ω) := hfub.2
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [htimeEq] with u hu
      exact integral_congr_ae hu


/-- Laplace integration of a measurable primitive with discounted integrability. -/
theorem u3_laplace_integral_primitive_of_integrable {g : ℝ → ℝ} (hg : Measurable g)
    (s : ℝ) (hs : 0 < s)
    (hgi : Integrable (fun u => Real.exp (-s * u) * g u)
      (volume.restrict (Set.Ioi 0))) :
    (∫ T : ℝ in Set.Ioi 0, Real.exp (-s * T) * (∫ u in (0 : ℝ)..T, g u)) =
      (∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g u) / s := by
  let H : ℝ × ℝ → ℝ := fun z =>
    if z.2 < z.1 then Real.exp (-s * z.1) * g z.2 else 0
  have hexp := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) (0 : ℝ)
  have hslice (u a : ℝ) (hu : 0 < u) :
      (∫ T : ℝ in Set.Ioi 0, if u < T then Real.exp (-s * T) * a else 0) =
        Real.exp (-s * u) / s * a := by
    change (∫ T : ℝ in Set.Ioi 0,
      (Set.Ioi u).indicator (fun T => Real.exp (-s * T) * a) T) = _
    rw [setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hu.le), integral_mul_const,
      integral_exp_mul_Ioi (neg_lt_zero.mpr hs) u, neg_div_neg_eq]
  have hm : Measurable H :=
    Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
      ((Real.continuous_exp.measurable.comp
        (measurable_const.mul measurable_fst)).mul (hg.comp measurable_snd)) measurable_const
  have hi : Integrable H
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun u => by
        change Integrable ((Set.Ioi u).indicator
          (fun T => Real.exp (-s * T) * g u)) _
        exact (hexp.mul_const (g u)).indicator measurableSet_Ioi
    · have heq : (fun u => ∫ T : ℝ in Set.Ioi 0, ‖H (T, u)‖) =ᵐ[
          volume.restrict (Set.Ioi 0)] fun u => Real.exp (-s * u) / s * ‖g u‖ := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hn (T : ℝ) : ‖H (T, u)‖ =
            if u < T then Real.exp (-s * T) * ‖g u‖ else 0 := by
          dsimp only [H]
          split_ifs <;> simp only [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), norm_zero]
        simp_rw [hn]
        exact hslice u ‖g u‖ hu
      apply Integrable.congr _ heq.symm
      have hn := hgi.norm.div_const s
      convert hn using 1
      ext u
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      ring

  calc
    _ = ∫ T : ℝ in Set.Ioi 0, ∫ u : ℝ in Set.Ioi 0, H (T, u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro T hT
      change _ = ∫ u : ℝ in Set.Ioi 0,
        (Set.Iio T).indicator (fun u => Real.exp (-s * T) * g u) u
      dsimp only
      rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio,
        integral_const_mul, intervalIntegral.integral_of_le hT.le,
        integral_Ioc_eq_integral_Ioo]
    _ = ∫ u : ℝ in Set.Ioi 0, ∫ T : ℝ in Set.Ioi 0, H (T, u) :=
      integral_integral_swap hi
    _ = ∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) / s * g u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact hslice u (g u) hu
    _ = _ := by simp only [div_mul_eq_mul_div, integral_div]


/-- A finite-time Dynkin identity yields its discounted form under L¹ bounds. -/
theorem u3_discounted_dynkin_of_integrable
    (F G : ℝ → ℝ) (hG : Measurable G) (F₀ s : ℝ) (hs : 0 < s)
    (hFint : Integrable (fun t => Real.exp (-s * t) * F t)
      (volume.restrict (Set.Ioi 0)))
    (hGint : Integrable (fun t => Real.exp (-s * t) * G t)
      (volume.restrict (Set.Ioi 0)))
    (hfinite : ∀ᵐ T ∂volume.restrict (Set.Ioi 0),
      (∫ u in (0 : ℝ)..T, G u) = F T - F₀) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * G t) =
      s * (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * F t) - F₀ := by
  have hexp := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) (0 : ℝ)
  have heq : (∫ T : ℝ in Set.Ioi 0, Real.exp (-s * T) * (F T - F₀)) =
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * G t) / s := by
    calc
      _ = ∫ T : ℝ in Set.Ioi 0, Real.exp (-s * T) * (∫ u in (0 : ℝ)..T, G u) := by
        apply integral_congr_ae
        filter_upwards [hfinite] with T hT
        rw [hT]
      _ = _ := u3_laplace_integral_primitive_of_integrable hG s hs hGint
  simp_rw [mul_sub] at heq
  rw [integral_sub hFint (hexp.mul_const F₀), integral_mul_const,
    integral_exp_mul_Ioi (neg_lt_zero.mpr hs) 0] at heq
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at heq
  have h := (eq_div_iff hs.ne').mp heq
  have hcancel : (1 / s * F₀) * s = F₀ := by field_simp
  rw [sub_mul, hcancel] at h
  linarith only [h]

/-- Exchange fixed-time exceptional sets in a supplied-kernel Dynkin identity. -/
theorem u3_supplied_finite_dynkin_ae_time
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (m a : FieldPair d → ℝ) (hm : Measurable m) (ha : Measurable a)
    (hdyn : ∀ T : ℝ≥0, ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, m (translate (γ T) (reduce ω)) ∂K ω) - m (reduce ω) =
      ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        a (translate (γ u.toNNReal) (reduce ω)) ∂K ω) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ T ∂volume.restrict (Set.Ioi (0 : ℝ)),
      (∫ γ : Path d, m (translate (γ T.toNNReal) (reduce ω)) ∂K ω) - m (reduce ω) =
      ∫ u in (0 : ℝ)..T, ∫ γ : Path d,
        a (translate (γ u.toNNReal) (reduce ω)) ∂K ω := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  let R : Kernel (ℝ × FieldPair d) (Path d) := K.comap Prod.snd measurable_snd
  let E : (ℝ × FieldPair d) × Path d → FieldPair d := fun z =>
    translate (z.2 z.1.1.toNNReal) (reduce z.1.2)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_snd.prodMk
        (continuous_real_toNNReal.comp (continuous_fst.comp continuous_fst)))).prodMk
        (Probability.continuous_reduce.comp (continuous_snd.comp continuous_fst)))).measurable
  have hM : Measurable (fun z : ℝ × FieldPair d =>
      ∫ γ : Path d, m (translate (γ z.1.toNNReal) (reduce z.2)) ∂K z.2) := by
    simpa only [E, R, Kernel.comap_apply, Function.comp_apply] using
      ((hm.comp hE).stronglyMeasurable.integral_kernel_prod_right' (κ := R)).measurable
  have hA : Measurable (fun z : ℝ × FieldPair d =>
      ∫ γ : Path d, a (translate (γ z.1.toNNReal) (reduce z.2)) ∂K z.2) := by
    simpa only [E, R, Kernel.comap_apply, Function.comp_apply] using
      ((ha.comp hE).stronglyMeasurable.integral_kernel_prod_right' (κ := R)).measurable
  let A : ℝ × FieldPair d → ℝ := fun z =>
    ∫ γ : Path d, a (translate (γ z.1.toNNReal) (reduce z.2)) ∂K z.2
  have hprim : Measurable (fun z : ℝ × FieldPair d =>
      ∫ u in Set.Ioc (0 : ℝ) z.1, A (u, z.2)) := by
    have hi : Measurable (fun z : (ℝ × FieldPair d) × ℝ =>
        if 0 < z.2 ∧ z.2 ≤ z.1.1 then A (z.2, z.1.2) else 0) :=
      (hA.comp (measurable_snd.prodMk measurable_fst.snd)).ite
        ((measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_fst.fst)) measurable_const
    have hj := (hi.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
    simpa only [← integral_indicator measurableSet_Ioc, Set.indicator, mem_Ioc] using hj
  have he : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, m (translate (γ t.toNNReal) (reduce ω)) ∂K ω) - m (reduce ω) =
      ∫ u in Set.Ioc (0 : ℝ) t, A (u, ω) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Real.coe_toNNReal _ ht.le] using hdyn t.toNNReal
  have hswap := (Measure.ae_ae_comm (p := fun t ω =>
      (∫ γ : Path d, m (translate (γ t.toNNReal) (reduce ω)) ∂K ω) - m (reduce ω) =
      ∫ u in Set.Ioc (0 : ℝ) t, A (u, ω))
    (measurableSet_eq_fun (hM.sub (hm.comp (Probability.measurable_reduce.comp measurable_snd))) hprim)).mp he
  filter_upwards [hswap] with ω hω
  filter_upwards [hω, ae_restrict_mem measurableSet_Ioi] with t ht hpos
  simpa only [intervalIntegral.integral_of_le hpos.le] using ht


/-- The supplied discounted L² occupation bound gives time integrability of
expected observations for almost every environment. -/
theorem u3_unforced_expected_discounted_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (s : ℝ) (hs : 0 < s) (a : FieldPair d → ℝ) (ha : Measurable a)
    (halp : MemLp a 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun t : ℝ => Real.exp (-s * t) * ∫ γ : Path d,
        a (translate (γ t.toNNReal) (reduce ω)) ∂K ω)
        (volume.restrict (Set.Ioi 0)) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  let E : (ℝ × FieldPair d) × Path d → FieldPair d := fun z =>
    translate (z.2 z.1.1.toNNReal) (reduce z.1.2)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_snd.prodMk
        (continuous_real_toNNReal.comp (continuous_fst.comp continuous_fst)))).prodMk
        (Probability.continuous_reduce.comp (continuous_snd.comp continuous_fst)))).measurable
  let R : Kernel (ℝ × FieldPair d) (Path d) := K.comap Prod.snd measurable_snd
  have hA : Measurable (fun z : ℝ × FieldPair d =>
      ∫ γ : Path d, a (translate (γ z.1.toNNReal) (reduce z.2)) ∂K z.2) := by
    simpa only [E, R, Kernel.comap_apply, Function.comp_apply] using
      ((ha.comp hE).stronglyMeasurable.integral_kernel_prod_right' (κ := R)).measurable
  have hj := (u2_supplied_discounted_occupation_L2_bound (hpath := hpath) hd Q K hK s hs a ha halp).1
  have ht := c17_integrable_time_expected_norm (volume.restrict (Set.Ioi (0 : ℝ)))
    Q.measure K (fun p => Real.exp (-s * p.1) *
      |a (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|) hj
  filter_upwards [ht] with ω hω
  have hb : Integrable (fun t : ℝ => Real.exp (-s*t) *
      ∫ γ : Path d, |a (translate (γ t.toNNReal) (reduce ω))| ∂K ω)
      (volume.restrict (Set.Ioi 0)) := by
    convert hω using 1
    ext t
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _), integral_const_mul]
  apply hb.mono' ((Real.continuous_exp.measurable.comp
    (measurable_const.mul measurable_id)).mul
    (hA.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  filter_upwards [] with t
  change |Real.exp (-s*t) * (∫ γ : Path d, a (translate (γ t.toNNReal) (reduce ω)) ∂K ω)| ≤ _
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (Real.exp_nonneg _)

/-- Discounted Dynkin from finite-time supplied-kernel identities for L² tests. -/
theorem u3_unforced_discounted_dynkin_of_finite
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (m a : FieldPair d → ℝ) (hm : Measurable m) (ha : Measurable a)
    (hmlp : MemLp m 2 (reducedLaw Q)) (halp : MemLp a 2 (reducedLaw Q))
    (hdyn : ∀ T : ℝ≥0, ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, m (translate (γ T) (reduce ω)) ∂K ω) - m (reduce ω) =
      ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        a (translate (γ u.toNNReal) (reduce ω)) ∂K ω)
    (s : ℝ) (hs : 0 < s) :
    ∀ᵐ ω ∂Q.measure,
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        (∫ γ : Path d, a (translate (γ t.toNNReal) (reduce ω)) ∂K ω)) =
      s * (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        (∫ γ : Path d, m (translate (γ t.toNNReal) (reduce ω)) ∂K ω)) - m (reduce ω) := by
  have hfinite := u3_supplied_finite_dynkin_ae_time Q K m a hm ha hdyn
  have hiM := u3_unforced_expected_discounted_integrable (hpath := hpath) hd Q K hK s hs m hm hmlp
  have hiA := u3_unforced_expected_discounted_integrable (hpath := hpath) hd Q K hK s hs a ha halp
  filter_upwards [hfinite, hiM, hiA] with ω hf hmi hai
  have hE : Measurable (fun p : ℝ × Path d =>
      translate (p.2 p.1.toNNReal) (reduce ω)) := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_snd.prodMk
        (continuous_real_toNNReal.comp continuous_fst))).prodMk continuous_const)).measurable
  have hg : Measurable (fun t : ℝ => ∫ γ : Path d,
      a (translate (γ t.toNNReal) (reduce ω)) ∂K ω) :=
    ((ha.comp hE).stronglyMeasurable.integral_prod_right' (ν := K ω)).measurable
  exact u3_discounted_dynkin_of_integrable _ _ hg _ s hs hmi hai
    (hf.mono fun _ h => h.symm)

/-- Discounted Dynkin for each actual unforced resolvent mollification. -/
theorem u3_unforced_mollified_discounted_dynkin
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (s : ℝ) (hs : 0 < s) (rhs : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs) G)
    (L : ℂ →L[ℝ] ℝ) (n : ℕ) :
    ∃ a : FieldPair d → ℝ, Measurable a ∧ MemLp a 2 (reducedLaw Q) ∧
      (a =ᵐ[reducedLaw Q] fun w => envGenerator hd 0 (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs v))) w) ∧
      ∀ᵐ ω ∂Q.measure,
        (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * ∫ γ : Path d,
          a (translate (γ t.toNNReal) (reduce ω)) ∂K ω) =
        s * (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * ∫ γ : Path d,
          horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
            (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs v))
            (translate (γ t.toNNReal) (reduce ω)) ∂K ω) -
        horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs v)) (reduce ω) := by
  let Y : QuenchedPathLaws d := K.comap Prod.snd measurable_snd
  have hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0,ω)) := hK
  let f : FieldPair d → ℝ := fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs v)
  let m := horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) f
  have hf : Measurable f := L.continuous.measurable.comp
    (Lp.stronglyMeasurable (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs rhs)).measurable
  have hflp : MemLp f 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp _)
  have hm : Measurable m := measurable_horizontalMollify _
    (Entropy.contDiff_unitMassScaledMollifier _).continuous.measurable hf
  have hmlp : MemLp m 2 (reducedLaw Q) := Entropy.memLp_horizontalMollify_unitMass
    (reducedLaw_stationary Q) (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top hf hflp
  obtain ⟨a, ham, ha, hae⟩ :=
    s5_unforced_resolvent_generator_representatives hd Q ⟨0, by omega⟩ s hs rhs hG L
  have hfin : ∀ T : ℝ≥0, ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, m (translate (γ T) (reduce ω)) ∂K ω) - m (reduce ω) =
      ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        a n (translate (γ u.toNNReal) (reduce ω)) ∂K ω := by
    intro T
    have hdyn := u3_unforced_resolvent_mollified_dynkin_time_first
      (hpath := hpath) hd Q s hs Y hY rhs hG L n T
    have heq := u3_supplied_force_ae_eq_time_first_occupation_of_pathwise
      (hpath := hpath) hd Q ⟨0, by omega⟩ 0 Y hY T (a n) _ (hae n)
    filter_upwards [hdyn, heq] with ω hdynω heqω
    change (∫ γ : Path d, m (translate (γ T) (reduce ω)) ∂K ω) - m (reduce ω) = _ at hdynω
    rw [hdynω]
    apply integral_congr_ae
    filter_upwards [heqω] with t ht
    exact integral_congr_ae (ht.mono fun _ h => h.symm)
  refine ⟨a n, ham n, ha n, hae n, ?_⟩
  exact u3_unforced_discounted_dynkin_of_finite (hpath := hpath) hd Q K hK
    m (a n) hm (ham n) hmlp (ha n) hfin s hs

/-- Refine an existing residual subsequence until the initial mollified
observation also converges for almost every original environment. -/
theorem u3_unforced_initial_mollification_subsequence
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (f : FieldPair d → ℝ) (hf : Measurable f) (hflp : MemLp f 2 (reducedLaw Q))
    (idx : ℕ → ℕ) (hidx : StrictMono idx) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Tendsto (fun n => horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq (idx (ns n)))) f (reduce ω))
        atTop (𝓝 (f (reduce ω))) := by
  have ht := (Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier
    (reducedLaw Q) (reducedLaw_stationary Q) 2 ENNReal.ofNat_ne_top hf hflp).comp
      (Entropy.tendsto_scaleSeq.comp hidx.tendsto_atTop)
  obtain ⟨ns, hns, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) ht).exists_seq_tendsto_ae
  exact ⟨ns, hns, (Probability.measurableEmbedding_reduce d).ae_map_iff.mp hpoint⟩

/-- The residual form of discounted Dynkin identifies the limiting initial
value once the absolute discounted residual tends to zero. -/
theorem u3_discounted_residual_limit
    (q u : ℝ) (initial residual bound : ℕ → ℝ)
    (hidentity : ∀ n, q = initial n - residual n)
    (hinitial : Tendsto initial atTop (𝓝 u))
    (hbound : ∀ n, |residual n| ≤ bound n)
    (hvanish : Tendsto bound atTop (𝓝 0)) : q = u := by
  have hres : Tendsto residual atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := bound)
    · intro n
      simpa only [Real.norm_eq_abs] using hbound n
    · exact hvanish
  have hq : Tendsto (fun _ : ℕ => q) atTop (𝓝 u) := by
    have h := hinitial.sub hres
    simpa only [sub_zero, ← hidentity] using h
  exact tendsto_nhds_unique tendsto_const_nhds hq


/-- Choose residual representatives together with one subsequence controlling
both their discounted occupation and the resolvent's initial mollification. -/
theorem u3_unforced_residual_and_initial_subsequence
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g) G) (L : ℂ →L[ℝ] ℝ) :
    ∃ (r : ℕ → FieldPair d → ℝ) (ns : ℕ → ℕ), StrictMono ns ∧
      (∀ n, Measurable (r n)) ∧ (∀ n, MemLp (r n) 2 (reducedLaw Q)) ∧
      (∀ n, r n =ᵐ[reducedLaw Q] fun w =>
        s * horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g v)) w -
        envGenerator hd 0 (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g v))) w - L (g w)) ∧
      ∀ᵐ ω ∂Q.measure,
        Tendsto (fun n => horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq (ns n)))
          (fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g v)) (reduce ω))
          atTop (𝓝 (L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g (reduce ω)))) ∧
        Tendsto (fun n => ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) *
          (∫ γ : Path d, |r (ns n) (translate (γ t.toNNReal) (reduce ω))| ∂K ω))
          atTop (𝓝 0) := by
  let f : FieldPair d → ℝ := fun v => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g v)
  have hf : Measurable f := L.continuous.measurable.comp
    (Lp.stronglyMeasurable (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g)).measurable
  have hflp : MemLp f 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp _)
  obtain ⟨r, hr, hm, he, hlim⟩ :=
    c17_resolvent_residual_representatives hd Q ⟨0, by omega⟩ s hs g hG L
  obtain ⟨ns, hns, hocc⟩ := c17_residual_quenched_subsequence Q K s s⁻¹
    (u2_supplied_discounted_occupation_L2_bound (hpath := hpath) hd Q K hK s hs)
    r hm hr hlim
  obtain ⟨ks, hks, hpoint⟩ :=
    u3_unforced_initial_mollification_subsequence Q f hf hflp ns hns
  refine ⟨r, ns ∘ ks, hns.comp hks, hm, hr, he, ?_⟩
  filter_upwards [hpoint, hocc] with ω hp ho
  exact ⟨hp, ho.comp hks.tendsto_atTop⟩


/-- Absolute discounted occupation bounds the signed occupation, provided
both time integrals are integrable. -/
theorem u3_discounted_occupation_abs_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : ℝ)
    (r : ℝ → Ω → ℝ)
    (hi : Integrable (fun t : ℝ => Real.exp (-s * t) * ∫ x, r t x ∂μ)
      (volume.restrict (Set.Ioi 0)))
    (ha : Integrable (fun t : ℝ => Real.exp (-s * t) * ∫ x, |r t x| ∂μ)
      (volume.restrict (Set.Ioi 0))) :
    |∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * ∫ x, r t x ∂μ| ≤
      ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * ∫ x, |r t x| ∂μ := by
  calc
    _ ≤ ∫ t : ℝ in Set.Ioi 0, |Real.exp (-s * t) * ∫ x, r t x ∂μ| :=
      abs_integral_le_integral_abs
    _ ≤ _ := by
      apply integral_mono_ae hi.norm ha
      filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (Real.exp_nonneg _)

/-- Reduced-law representatives agree along the discounted occupation of
almost every supplied path, in environment-time-path order. -/
theorem u3_unforced_discounted_occupation_ae_eq
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (s : ℝ) (hs : 0 < s) (f g : FieldPair d → ℝ)
    (hfg : f =ᵐ[reducedLaw Q] g) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ∀ᵐ γ ∂K ω,
        f (translate (γ t.toNNReal) (reduce ω)) =
          g (translate (γ t.toNNReal) (reduce ω)) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  obtain ⟨N, hsub, hNm, hN⟩ := exists_measurable_superset_of_null (ae_iff.mp hfg)
  have havoid := c17_occupation_avoids_null_set Q K s s⁻¹
    (u2_supplied_discounted_occupation_L2_bound (hpath := hpath) hd Q K hK s hs) N hNm hN
  have h := c17_occupation_ae_quenched (volume.restrict (Set.Ioi (0 : ℝ)))
    Q.measure K (fun t ω γ => translate (γ t.toNNReal) (reduce ω) ∉ N) havoid
  filter_upwards [h] with ω hω
  filter_upwards [hω] with t ht
  filter_upwards [ht] with γ hγ
  by_contra hne
  exact hγ (hsub hne)


/-- Transport a pointwise residual graph through path and time integration. -/
theorem u3_discounted_integrated_graph
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : ℝ)
    (m a q r : ℝ → Ω → ℝ)
    (hgraph : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ᵐ x ∂μ,
      r t x = s * m t x - a t x - q t x)
    (hm : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), Integrable (m t) μ)
    (ha : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), Integrable (a t) μ)
    (hq : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), Integrable (q t) μ)
    (hmi : Integrable (fun t : ℝ => Real.exp (-s * t) * ∫ x, m t x ∂μ)
      (volume.restrict (Set.Ioi 0)))
    (hai : Integrable (fun t : ℝ => Real.exp (-s * t) * ∫ x, a t x ∂μ)
      (volume.restrict (Set.Ioi 0)))
    (hqi : Integrable (fun t : ℝ => Real.exp (-s * t) * ∫ x, q t x ∂μ)
      (volume.restrict (Set.Ioi 0))) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * ∫ x, r t x ∂μ) =
      s * (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * ∫ x, m t x ∂μ) -
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * ∫ x, a t x ∂μ) -
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * ∫ x, q t x ∂μ) := by
  have he : (fun t : ℝ => Real.exp (-s * t) * ∫ x, r t x ∂μ) =ᵐ[
      volume.restrict (Set.Ioi 0)] fun t =>
      s * (Real.exp (-s * t) * ∫ x, m t x ∂μ) -
        (Real.exp (-s * t) * ∫ x, a t x ∂μ) -
        (Real.exp (-s * t) * ∫ x, q t x ∂μ) := by
    filter_upwards [hgraph, hm, ha, hq] with t ht hmt hat hqt
    rw [integral_congr_ae ht]
    change Real.exp (-s * t) * (∫ x, (s * m t x - a t x) - q t x ∂μ) = _
    have h₁ := integral_sub ((hmt.const_mul s).sub hat) hqt
    have h₂ := integral_sub (hmt.const_mul s) hat
    simp only [Pi.sub_apply] at h₁ h₂
    rw [h₁, h₂, integral_const_mul]
    ring
  rw [integral_congr_ae he]
  change (∫ t : ℝ in Set.Ioi 0,
    (s * (Real.exp (-s * t) * ∫ x, m t x ∂μ) -
      (Real.exp (-s * t) * ∫ x, a t x ∂μ)) -
      (Real.exp (-s * t) * ∫ x, q t x ∂μ)) = _
  have h₁ := integral_sub ((hmi.const_mul s).sub hai) hqi
  have h₂ := integral_sub (hmi.const_mul s) hai
  simp only [Pi.sub_apply] at h₁ h₂
  rw [h₁, h₂, integral_const_mul]


/-- Every measurable L² observation is integrable under almost every supplied
path law at almost every positive time. -/
theorem u3_unforced_discounted_path_slices
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (s : ℝ) (hs : 0 < s) (f : FieldPair d → ℝ) (hf : Measurable f)
    (hflp : MemLp f 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Integrable (fun γ : Path d => f (translate (γ t.toNNReal) (reduce ω))) (K ω) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  let E : ℝ × (FieldPair d × Path d) → FieldPair d := fun p =>
    translate (p.2.2 p.1.toNNReal) (reduce p.2.1)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp ((continuous_snd.comp continuous_snd).prodMk
        (continuous_real_toNNReal.comp continuous_fst))).prodMk
        (Probability.continuous_reduce.comp (continuous_fst.comp continuous_snd)))).measurable
  have hi := (u2_supplied_discounted_occupation_L2_bound (hpath := hpath) hd Q K hK s hs f hf hflp).1
  have hi' : Integrable (fun p : ℝ × (FieldPair d × Path d) =>
      Real.exp (-s * p.1) * f (E p))
      ((volume.restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K)) := by
    apply hi.mono' ((Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_fst)).mul (hf.comp hE)).aestronglyMeasurable
    filter_upwards [] with p
    change |Real.exp (-s * p.1) * f (E p)| ≤ Real.exp (-s * p.1) * |f (E p)|
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hslice := c17_integrable_path_slices (volume.restrict (Set.Ioi (0 : ℝ)))
    Q.measure K (fun p : ℝ × (FieldPair d × Path d) =>
      Real.exp (-s * p.1) * f (E p)) hi'
  filter_upwards [hslice] with ω hω
  filter_upwards [hω] with t ht
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero _)) _).mp ht


/-- Residual form of discounted Dynkin for L² representatives of the graph. -/
theorem u3_unforced_discounted_graph_identity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (s : ℝ) (hs : 0 < s) (m a q r : FieldPair d → ℝ)
    (hm : Measurable m) (ha : Measurable a) (hq : Measurable q)
    (hmlp : MemLp m 2 (reducedLaw Q)) (halp : MemLp a 2 (reducedLaw Q))
    (hqlp : MemLp q 2 (reducedLaw Q))
    (hgraph : r =ᵐ[reducedLaw Q] fun w => s * m w - a w - q w)
    (hdyn : ∀ᵐ ω ∂Q.measure,
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * ∫ γ : Path d,
        a (translate (γ t.toNNReal) (reduce ω)) ∂K ω) =
      s * (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * ∫ γ : Path d,
        m (translate (γ t.toNNReal) (reduce ω)) ∂K ω) - m (reduce ω)) :
    ∀ᵐ ω ∂Q.measure,
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * ∫ γ : Path d,
        q (translate (γ t.toNNReal) (reduce ω)) ∂K ω) =
      m (reduce ω) -
        (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * ∫ γ : Path d,
          r (translate (γ t.toNNReal) (reduce ω)) ∂K ω) := by
  have he := u3_unforced_discounted_occupation_ae_eq (hpath := hpath) hd Q K hK s hs r _ hgraph
  have hmsec := u3_unforced_discounted_path_slices (hpath := hpath) hd Q K hK s hs m hm hmlp
  have hasec := u3_unforced_discounted_path_slices (hpath := hpath) hd Q K hK s hs a ha halp
  have hqsec := u3_unforced_discounted_path_slices (hpath := hpath) hd Q K hK s hs q hq hqlp
  have hmi := u3_unforced_expected_discounted_integrable (hpath := hpath) hd Q K hK s hs m hm hmlp
  have hai := u3_unforced_expected_discounted_integrable (hpath := hpath) hd Q K hK s hs a ha halp
  have hqi := u3_unforced_expected_discounted_integrable (hpath := hpath) hd Q K hK s hs q hq hqlp
  filter_upwards [he, hmsec, hasec, hqsec, hmi, hai, hqi, hdyn] with ω heω hmω haω hqω hmiω haiω hqiω hdynω
  let E : ℝ → Path d → FieldPair d := fun t γ => translate (γ t.toNNReal) (reduce ω)
  have hg := u3_discounted_integrated_graph (K ω) s
    (fun t γ => m (E t γ)) (fun t γ => a (E t γ))
    (fun t γ => q (E t γ)) (fun t γ => r (E t γ))
    heω hmω haω hqω hmiω haiω hqiω
  dsimp [E] at hg
  linarith


/-- The supplied discounted occupation of each real resolvent projection
identifies the corresponding analytic resolvent at the initial environment. -/
theorem u3_unforced_quenched_resolvent_identity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g) G) (L : ℂ →L[ℝ] ℝ) :
    ∀ᵐ ω ∂Q.measure,
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * ∫ γ : Path d,
        L (g (translate (γ t.toNNReal) (reduce ω))) ∂K ω) =
      L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g (reduce ω)) := by
  let f : FieldPair d → ℝ := fun w => L (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g w)
  let q : FieldPair d → ℝ := fun w => L (g w)
  let m (n : ℕ) := horizontalMollify
    (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) f
  have hf : Measurable f := L.continuous.measurable.comp
    (Lp.stronglyMeasurable (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g)).measurable
  have hflp : MemLp f 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp _)
  have hq : Measurable q := L.continuous.measurable.comp (Lp.stronglyMeasurable g).measurable
  have hqlp : MemLp q 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp g)
  have hm (n : ℕ) : Measurable (m n) := measurable_horizontalMollify _
    (Entropy.contDiff_unitMassScaledMollifier _).continuous.measurable hf
  have hmlp (n : ℕ) : MemLp (m n) 2 (reducedLaw Q) :=
    Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q)
      (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top hf hflp
  obtain ⟨r, ns, _, hrm, hrlp, he, hlim⟩ :=
    u3_unforced_residual_and_initial_subsequence (hpath := hpath) hd Q K hK s hs g hG L
  choose a ham halp hae hdyn using fun n : ℕ =>
    u3_unforced_mollified_discounted_dynkin (hpath := hpath) hd Q K hK s hs g hG L n
  have hgraph (n : ℕ) : r n =ᵐ[reducedLaw Q] fun w => s * m n w - a n w - q w := by
    filter_upwards [he n, hae n] with w hrw haw
    dsimp [m, f, q] at *
    linarith
  have hid (n : ℕ) := u3_unforced_discounted_graph_identity (hpath := hpath) hd Q K hK
    s hs (m n) (a n) q (r n) (hm n) (ham n) hq (hmlp n) (halp n) hqlp (hgraph n) (hdyn n)
  have hbound (n : ℕ) : ∀ᵐ ω ∂Q.measure,
      |∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * ∫ γ : Path d,
        r n (translate (γ t.toNNReal) (reduce ω)) ∂K ω| ≤
      ∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * ∫ γ : Path d,
        |r n (translate (γ t.toNNReal) (reduce ω))| ∂K ω := by
    have hi := u3_unforced_expected_discounted_integrable (hpath := hpath) hd Q K hK s hs
      (r n) (hrm n) (hrlp n)
    have hiabs := u3_unforced_expected_discounted_integrable (hpath := hpath) hd Q K hK s hs
      (fun w => |r n w|) (hrm n).abs (by simpa only [Real.norm_eq_abs] using (hrlp n).norm)
    filter_upwards [hi, hiabs] with ω hiω haω
    exact u3_discounted_occupation_abs_bound (K ω) s
      (fun t γ => r n (translate (γ t.toNNReal) (reduce ω))) hiω haω
  filter_upwards [hlim, ae_all_iff.mpr hid, ae_all_iff.mpr hbound] with ω hlimω hidω hbω
  apply u3_discounted_residual_limit
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * ∫ γ : Path d,
      q (translate (γ t.toNNReal) (reduce ω)) ∂K ω) (f (reduce ω))
    (fun n => m (ns n) (reduce ω))
    (fun n => ∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * ∫ γ : Path d,
      r (ns n) (translate (γ t.toNNReal) (reduce ω)) ∂K ω)
    (fun n => ∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * ∫ γ : Path d,
      |r (ns n) (translate (γ t.toNNReal) (reduce ω))| ∂K ω)
  · exact fun n => hidω (ns n)
  · exact hlimω.1
  · exact fun n => hbω (ns n)
  · exact hlimω.2

/-- Real-valued version of the probability-space L²-to-L¹ estimate. -/
private theorem u3_real_integral_norm_le_l2 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    (∫ ω, ‖f ω‖ ∂μ) ≤ ‖f‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f), Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

/-- A jointly measurable real representative of an integrable L² orbit is
jointly integrable. -/
theorem u3_integrable_joint_real_l2 {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure T} {u : T → Lp ℝ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℝ} (hU : Measurable U)
    (heq : ∀ t, (fun ω => U (t, ω)) =ᵐ[μ] u t) :
    Integrable U (ν.prod μ) := by
  apply (integrable_prod_iff hU.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun t => ((Lp.memLp (u t)).integrable (by norm_num)).congr
    (heq t).symm), ?_⟩
  apply hu.norm.mono' (hU.stronglyMeasurable.norm.integral_prod_right.aestronglyMeasurable)
  filter_upwards with t
  rw [Real.norm_of_nonneg (integral_nonneg (fun ω => norm_nonneg _)),
    integral_congr_ae ((heq t).mono (fun ω h => congrArg norm h))]
  exact u3_real_integral_norm_le_l2 (u t)

/-- The Bochner integral of the real L² orbit has the literal time-integral
representative, with no uncountable intersection of full-measure events. -/
theorem u3_coeFn_integral_joint_real_l2 {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure T} [SFinite ν] {u : T → Lp ℝ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℝ} (hU : Measurable U)
    (heq : ∀ t, (fun ω => U (t, ω)) =ᵐ[μ] u t) :
    (fun ω => (∫ t, u t ∂ν) ω) =ᵐ[μ] fun ω => ∫ t, U (t, ω) ∂ν := by
  have hi := u3_integrable_joint_real_l2 hu hU heq
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp _).integrable (by norm_num)) hi.integral_prod_right
  intro A hA hμA
  have ht := integral_inner (𝕜 := ℝ) hu (indicatorConstLp 2 hA hμA.ne (1 : ℝ))
  rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  simp_rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  rw [← ht]
  have hir : Integrable U (ν.prod (μ.restrict A)) := by
    have h := hi.integrableOn (s := Set.univ ×ˢ A)
    rwa [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h
  rw [← integral_integral_swap (f := fun t ω => U (t, ω)) hir]
  apply integral_congr_ae
  filter_upwards with t
  exact integral_congr_ae (ae_restrict_of_ae (heq t).symm)

/-- A samplewise identification of a discounted orbit transfers to every
continuous linear functional on L². -/
theorem u3_real_dual_of_samplewise_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : ℝ≥0 → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hbound : ∀ t, ‖T t‖ ≤ 1)
    (hcont : ∀ f, Continuous (fun t : ℝ≥0 => T t f))
    (f v : Lp ℝ 2 μ) (s : ℝ) (hs : 0 < s)
    (hpoint : (fun ω => (∫ t : ℝ in Set.Ioi 0,
      Real.exp (-s*t) • T t.toNNReal f) ω) =ᵐ[μ] v) :
    ∀ φ : Lp ℝ 2 μ →L[ℝ] ℝ,
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * φ (T t.toNNReal f)) = φ v := by
  intro φ
  have hi := u2_discounted_C0_orbit_integrableOn_Ioi T hbound hcont f 0 s hs
  have he : (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) • T t.toNNReal f) = v :=
    Lp.ext hpoint
  have h := φ.integral_comp_comm hi
  rw [he] at h
  simpa only [map_smul, smul_eq_mul] using h


/-- Two L² actions representing the same supplied kernel agree pointwise in
operator time and input; the representative events may depend on both. -/
theorem u3_supplied_kernel_actions_eq
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) (D : FieldPair d → FieldPair d)
    (hD : Measurable D)
    (T S : ℝ≥0 → Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q))
    (hT : ∀ t F, T t F =ᵐ[reducedLaw Q]
      MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) F)
    (hS : ∀ t F, S t F =ᵐ[reducedLaw Q]
      MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) F) :
    ∀ t F, T t F = S t F := by
  intro t F
  exact Lp.ext ((hT t F).trans (hS t F).symm)

/-- The actual supplied kernel orbit has a jointly measurable time/environment
representative, including the exponential discount. -/
theorem u3_supplied_discounted_joint_orbit_measurable
    {d : ℕ} (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (f : FieldPair d → ℝ) (hf : Measurable f) (s : ℝ) :
    Measurable (fun p : ℝ × FieldPair d => Real.exp (-s * p.1) *
      ∫ γ : Path d, f (translate (γ p.1.toNNReal) (reduce (D p.2))) ∂K (D p.2)) := by
  let κ : Kernel (ℝ × FieldPair d) (Path d) := K.comap (fun p => D p.2)
    (hD.comp measurable_snd)
  let : IsMarkovKernel κ := inferInstance
  have hE : Measurable (fun p : (ℝ × FieldPair d) × Path d =>
      translate (p.2 p.1.1.toNNReal) (reduce (D p.1.2))) := by
    exact Probability.continuous_translate.measurable.comp
      ((continuous_eval.measurable.comp (measurable_snd.prodMk
        (continuous_real_toNNReal.measurable.comp measurable_fst.fst))).prodMk
        (Probability.measurable_reduce.comp (hD.comp measurable_fst.snd)))
  have hI : Measurable (fun p : ℝ × FieldPair d =>
      ∫ γ : Path d, f (translate (γ p.1.toNNReal) (reduce (D p.2))) ∂κ p) :=
    ((hf.comp hE).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  exact (Real.continuous_exp.measurable.comp
    (measurable_const.mul measurable_fst)).mul hI

/-- The joint representative agrees at every time with the discounted L²
orbit, up to the time-dependent reduced-law null set. -/
theorem u3_supplied_discounted_joint_orbit_rep
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (T : ℝ≥0 → Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q))
    (hrep : ∀ t F, T t F =ᵐ[reducedLaw Q]
      MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) F)
    (f : Lp ℝ 2 (reducedLaw Q)) (s t : ℝ) :
    (fun ρ => Real.exp (-s*t) * ∫ γ : Path d,
      f (translate (γ t.toNNReal) (reduce (D ρ))) ∂K (D ρ)) =ᵐ[reducedLaw Q]
      Real.exp (-s*t) • T t.toNNReal f := by
  filter_upwards [hrep t.toNNReal f] with ρ hρ
  have hm : Measurable (fun γ : Path d => translate (γ t.toNNReal) (reduce (D ρ))) :=
    (measurable_c2EnvironmentAt t.toNNReal).comp (measurable_const.prodMk measurable_id)
  have hi : (∫ η, f η ∂c2ReducedEnvironmentKernel K D hD t.toNNReal ρ) =
      ∫ γ : Path d, f (translate (γ t.toNNReal) (reduce (D ρ))) ∂K (D ρ) := by
    change (∫ η, f η ∂c2EnvironmentKernel K t.toNNReal (D ρ)) = _
    rw [c2EnvironmentKernel_apply]
    exact integral_map hm.aemeasurable (Lp.stronglyMeasurable f).aestronglyMeasurable
  change Real.exp (-s*t) * _ = Real.exp (-s*t) * (T t.toNNReal f) ρ
  rw [hρ]
  exact congrArg (fun x : ℝ => Real.exp (-s*t) * x) hi.symm

/-- The actual supplied kernel has the analytic weak resolvent identity. -/
theorem u3_unforced_kernel_resolvent_identity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) :
    u3UnforcedKernelResolventIdentity hd Q K D hD := by
  intro T hrep g L φ s hs
  obtain ⟨S, hn, hr, _, _, hc⟩ :=
    u2_unforced_reduced_kernel_L2_strongly_continuous (hpath := hpath) hd Q K hK D hD hleft
  have hST := u3_supplied_kernel_actions_eq Q K D hD S T hr hrep
  let f := L.compLpL 2 (reducedLaw Q) g
  let v := L.compLpL 2 (reducedLaw Q) (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g)
  let U : ℝ × FieldPair d → ℝ := fun p => Real.exp (-s*p.1) *
    ∫ γ : Path d, f (translate (γ p.1.toNNReal) (reduce (D p.2))) ∂K (D p.2)
  let u : ℝ → Lp ℝ 2 (reducedLaw Q) := fun t => Real.exp (-s*t) • S t.toNNReal f
  have hu : Integrable u (volume.restrict (Set.Ioi 0)) :=
    u2_discounted_C0_orbit_integrableOn_Ioi S hn hc f 0 s hs
  have hU : Measurable U := u3_supplied_discounted_joint_orbit_measurable K D hD f
    (Lp.stronglyMeasurable f).measurable s
  have hrepU : ∀ t, (fun ρ => U (t,ρ)) =ᵐ[reducedLaw Q] u t := fun t => by
    exact (u3_supplied_discounted_joint_orbit_rep Q K D hD S hr f s t).trans
      (Lp.coeFn_smul _ _).symm
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hcoe := u3_coeFn_integral_joint_real_l2 hu hU hrepU
  have hG := hasComplexHorizontalGradient_unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g
  have hq := u3_unforced_quenched_resolvent_identity (hpath := hpath) hd Q K hK s hs g hG L
  have hf := u3_unforced_discounted_occupation_ae_eq (hpath := hpath) hd Q K hK s hs
    f (fun ρ => L (g ρ)) (L.coeFn_compLpL g)
  have hv := (Probability.measurableEmbedding_reduce d).ae_map_iff.mp
    (L.coeFn_compLpL (unforcedComplexResolvent Q ⟨0, by omega⟩ s hs g))
  have hcoep := (Probability.measurableEmbedding_reduce d).ae_map_iff.mp hcoe
  have hp : ∀ᵐ ω ∂Q.measure, (∫ t, u t ∂volume.restrict (Set.Ioi 0)) (reduce ω) = v (reduce ω) := by
    filter_upwards [hcoep, hq, hf, hv] with ω hcoepω hqω hfω hvω
    rw [hcoepω, hvω, ← hqω]
    apply integral_congr_ae
    filter_upwards [hfω] with t ht
    dsimp [U]
    rw [hleft ω]
    exact congrArg (fun x : ℝ => Real.exp (-s*t) * x) (integral_congr_ae ht)
  have hpoint : ∀ᵐ ρ ∂reducedLaw Q,
      (∫ t, u t ∂volume.restrict (Set.Ioi 0)) ρ = v ρ := by
    apply (Probability.measurableEmbedding_reduce d).ae_map_iff.mpr
    exact hp
  have hdual := u3_real_dual_of_samplewise_integral (reducedLaw Q) S hn hc f v s hs hpoint φ
  simpa only [hST, f, v] using hdual

/-- The supplied Markov kernel satisfies the bounded-test hypothesis used by
    the unforced-process assembler. -/
theorem u3_unforced_markov_kernel_bounded_test_identity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (t : ℝ≥0) (g : FieldPair d →ᵇ ℂ)
    (F : Lp ℂ 2 (reducedLaw Q))
    (hF : F =ᵐ[reducedLaw Q] fun ω => g ω) :
    (fun ω => forcedComplexEvolution Q ⟨0, by omega⟩ 0 t F (reduce ω)) =ᵐ[Q.measure]
      fun ω => ∫ η, g η ∂c2EnvironmentKernel K t ω := by
  obtain ⟨D, hD, hleft⟩ := Probability.exists_measurable_leftInverse_reduce d
  have hlap := u3_unforced_weak_laplace_of_kernel_resolvent hd Q K D hD
    (u3_unforced_kernel_resolvent_identity (hpath := hpath) hd Q K hK D hD hleft)
  have ha := u3_unforced_kernel_endpoint_of_weak_laplace
    (hpath := hpath) hd Q K hK D hD hleft hlap t F
  have he := u3_pathwise_unforced_supplied_endpoint_ae_eq (hpath := hpath) hd Q K hK t hF
  filter_upwards [ha, he] with ω haω heω
  rw [← s5_unforced_evolution_eq_zero_force Q ⟨0, by omega⟩, haω]
  rw [c2EnvironmentKernel_apply]
  have hm : Measurable (fun γ : Path d => translate (γ t) (reduce ω)) :=
    (measurable_c2EnvironmentAt t).comp (measurable_const.prodMk measurable_id)
  rw [integral_map hm.aemeasurable g.continuous.measurable.aestronglyMeasurable]
  exact integral_congr_ae heω

/-- The required unforced bounded-test identity for the supplied path law. -/
theorem u3_unforced_bounded_test_identity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0,ω)))
    (t : ℝ≥0) (g : FieldPair d →ᵇ ℂ)
    (F : Lp ℂ 2 (reducedLaw Q))
    (hF : F =ᵐ[reducedLaw Q] fun ω => g ω) :
    ∀ᵐ ω ∂Q.measure,
      forcedComplexEvolution Q ⟨0, by omega⟩ 0 t F (reduce ω) =
        ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂Y (0,ω) := by
  refine u3_unforced_bounded_test_of_weak_laplace_family (hpath := hpath) hd Q Y hY ?_ t g F hF
  intro K inst hKY D hD hleft
  let : IsMarkovKernel K := inst
  have hK : ∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω) := by
      filter_upwards [hKY, hY] with ω he hp
      simpa only [he] using hp
  exact u3_unforced_weak_laplace_of_kernel_resolvent hd Q K D hD
      (u3_unforced_kernel_resolvent_identity (hpath := hpath) hd Q K hK D hD hleft)

#print axioms u3_unforced_quenched_resolvent_identity
#print axioms u3_unforced_kernel_resolvent_identity
#print axioms u3_unforced_markov_kernel_bounded_test_identity
#print axioms u3_unforced_bounded_test_identity

end EinsteinFull
