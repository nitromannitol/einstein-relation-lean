import EinsteinFull.Calculus.U2RegularKernelCovariance
import SubdiffusiveProcess.Processes.E7.FellerFromResolvent
import EinsteinFull.Calculus.C17UnforcedIdentification
import EinsteinFull.Calculus.C17UnforcedBoundedTests
import EinsteinFull.Calculus.ComplexEvolutionGeneratorSupport
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BoundedContinuousFunction

noncomputable section
namespace EinsteinFull

/-- The unforced and zero-force constructions have the same evolution. -/
theorem s5_unforced_evolution_eq_zero_force
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    unforcedComplexEvolution Q i = forcedComplexEvolution Q i 0 :=
  (isComplexEnvironmentSemigroup_unforcedComplexEvolution Q i).eq_forcedComplexEvolution

/-- The actual supplied law admits a quenched subsequence along which the
mollified resolvent graph residual has vanishing discounted occupation. -/
theorem s5_unforced_resolvent_residual_quenched_subsequence
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (i : Fin d) (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q i s hs g) G) (L : ℂ →L[ℝ] ℝ) :
    ∃ (r : ℕ → FieldPair d → ℝ) (ns : ℕ → ℕ), StrictMono ns ∧
      (∀ n, r n =ᵐ[reducedLaw Q] fun w =>
        s * horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (unforcedComplexResolvent Q i s hs g v)) w -
        envGenerator hd 0 (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (unforcedComplexResolvent Q i s hs g v))) w - L (g w)) ∧
      ∀ᵐ ω ∂Q.measure,
        Tendsto (fun n => ∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) *
          (∫ γ : Path d, |r (ns n) (translate (γ u.toNNReal) (reduce ω))| ∂K ω))
          atTop (𝓝 0) := by
  obtain ⟨r, hr, hm, he, hlim⟩ :=
    c17_resolvent_residual_representatives hd Q i s hs g hG L
  obtain ⟨ns, hns, hocc⟩ := c17_residual_quenched_subsequence Q K s s⁻¹
    (u2_supplied_discounted_occupation_L2_bound (hpath := hpath) hd Q K hK s hs)
    r hm hr hlim
  exact ⟨r, ns, hns, he, hocc⟩

/-- Every square-integrable observation is integrable along the same supplied
unforced path law at each fixed time, for almost every initial environment. -/
theorem s5_unforced_supplied_endpoint_integrable
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

#print axioms s5_unforced_supplied_endpoint_integrable

/-- Reduced-law almost-everywhere equality is preserved at fixed times under
the same supplied unforced path law. -/
theorem s5_unforced_supplied_endpoint_ae_eq
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

#print axioms s5_unforced_supplied_endpoint_ae_eq

/-- The endpoint integrability holds for every supplied reduced martingale
solution, including kernels that are Markov only on almost every fiber. -/
theorem s5_unforced_path_endpoint_integrable
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
  filter_upwards [s5_unforced_supplied_endpoint_integrable (hpath := hpath) hd Q K hK t f,
    hu] with ω hi he
  change Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y₀ (0, ω)) at hi
  rw [← he]
  exact hi

#print axioms s5_unforced_path_endpoint_integrable

/-- Reduced-law representatives agree along every supplied unforced solution
at each fixed time, almost surely in the initial environment and path. -/
theorem s5_unforced_path_endpoint_ae_eq
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (t : ℝ≥0) {f g : FieldPair d → ℂ} (hfg : f =ᵐ[reducedLaw Q] g) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      f (translate (γ t) (reduce ω)) = g (translate (γ t) (reduce ω)) := by
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
  filter_upwards [s5_unforced_supplied_endpoint_ae_eq (hpath := hpath) hd Q K hK t hfg,
    hu] with ω heq he
  change ∀ᵐ γ ∂Y₀ (0, ω),
    f (translate (γ t) (reduce ω)) = g (translate (γ t) (reduce ω)) at heq
  rw [← he]
  exact heq

#print axioms s5_unforced_path_endpoint_ae_eq

/-- A measurable L² representative of each mollified resolvent generator. -/
theorem s5_unforced_resolvent_generator_representatives
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q))
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q i s hs g) G) (L : ℂ →L[ℝ] ℝ) :
    ∃ a : ℕ → FieldPair d → ℝ, (∀ n, Measurable (a n)) ∧
      (∀ n, MemLp (a n) 2 (reducedLaw Q)) ∧
      ∀ n, a n =ᵐ[reducedLaw Q] fun w =>
        envGenerator hd 0 (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (unforcedComplexResolvent Q i s hs g v))) w := by
  let f : FieldPair d → ℝ := fun v => L (unforcedComplexResolvent Q i s hs g v)
  let q : FieldPair d → ℝ := fun v => L (g v)
  have hfm : Measurable f := L.continuous.measurable.comp
    (Lp.stronglyMeasurable (unforcedComplexResolvent Q i s hs g)).measurable
  have hf : MemLp f 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp _)
  have hqm : Measurable q := L.continuous.measurable.comp (Lp.stronglyMeasurable g).measurable
  have hq : MemLp q 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp g)
  obtain ⟨r, hr, hm, he, _⟩ := c17_resolvent_residual_representatives hd Q i s hs g hG L
  let m (n : ℕ) := horizontalMollify
    (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) f
  have hmm (n : ℕ) : Measurable (m n) := measurable_horizontalMollify _
    (Entropy.contDiff_unitMassScaledMollifier _).continuous.measurable hfm
  have hml (n : ℕ) : MemLp (m n) 2 (reducedLaw Q) :=
    Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q)
      (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top hfm hf
  refine ⟨fun n w => s * m n w - q w - r n w,
    fun n => ((hmm n).const_mul s).sub hqm |>.sub (hm n),
    fun n => ((hml n).const_mul s).sub hq |>.sub (hr n), ?_⟩
  intro n
  filter_upwards [he n] with w hw
  dsimp [m, f, q] at *
  linarith

#print axioms s5_unforced_resolvent_generator_representatives

/-- Discounted Dynkin identity on the horizontal core for the supplied law. -/
theorem s5_unforced_horizontal_core_discounted_dynkin
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (F : FieldPair d → ℝ) (hF : IsHorizontalTest F) (s : ℝ) (hs : 0 < s) :
    ∀ᵐ ω ∂Q.measure,
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        (∫ γ : Path d, envGenerator hd 0 F
          (translate (γ t.toNNReal) (reduce ω)) ∂K ω)) =
      s * (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        (∫ γ : Path d, F (translate (γ t.toNNReal) (reduce ω)) ∂K ω)) -
        F (reduce ω) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  let i : Fin d := ⟨0, by omega⟩
  obtain ⟨Y, _, hY⟩ := foundation_reduced_textbook_kernel hΛ i 0
  have hred : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact c16_reduced_solves_of_textbook_and_averaged_occupation hΛ hω i 0
      (hY ω hω)
      (foundation_reduced_textbook_averaged_occupation_ac_of_two_le hd hΛ hω i 0 (hY ω hω))
  let X : QuenchedPathLaws d := K.comap Prod.snd measurable_snd
  have huniq := reducedOriginLaw_ae_unique_of_pathwise (hpath := hpath) Q i 0 X Y hK hred
  filter_upwards [huniq, Q.regular] with ω hωeq hω
  change K ω = Y (0, ω) at hωeq
  have hP' : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) 0 (K ω) := by
    rw [hωeq]
    exact hY ω hω
  have hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) 0 (K ω) :=
    ⟨inferInstance, hP'.2⟩
  have hsym : ∀ x j k, (reduce ω).1 x j k = (reduce ω).1 x k j := fun x j k => by
    have := congrFun (congrFun (reducedCoefficient_symm hω x) k) j
    exact (by simpa [Matrix.transpose_apply] using this : reducedCoefficient ω x j k = reducedCoefficient ω x k j)
  have hdyn := c17_discounted_horizontal_test_dynkin hΛ hω i hP F hF s hs
  have hcongr : ∀ (γ : Path d) (u : ℝ), External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i 0) (orbit F (reduce ω)) (γ u.toNNReal) =
      envGenerator hd 0 F (translate (γ u.toNNReal) (reduce ω)) := fun γ u =>
    (c17_envGenerator_eq_svGenerator hd (reduce ω) F i hsym _).symm
  simp_rw [hcongr] at hdyn
  simpa [orbit] using hdyn

#print axioms s5_unforced_resolvent_residual_quenched_subsequence
#print axioms s5_unforced_horizontal_core_discounted_dynkin
#print axioms s5_unforced_evolution_eq_zero_force
/-- Bounded continuous scalar orbits are determined by their Laplace transforms. -/
theorem s5_continuous_bounded_scalar_Laplace_unique
    (f g : ℝ≥0 → ℝ) (hf : Continuous f) (hg : Continuous g)
    (M : ℝ) (hbound : ∀ t, |f t| + |g t| ≤ M)
    (he : ∀ s : ℝ, 0 < s →
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t)*f t.toNNReal) =
      ∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t)*g t.toNNReal) : f = g := by
  have hc (u : ℝ≥0 → ℝ) (hu : Continuous u)
      (hbu : ∀ t, |u t| ≤ M) (s : ℝ) (hs : 0 < s) :
      Integrable (fun t : ℝ => Real.exp (-s*t) * u t.toNNReal)
        (volume.restrict (Set.Ioi 0)) := by
    apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const M).mono'
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (hu.comp continuous_real_toNNReal)).aestronglyMeasurable)
    exact ae_of_all _ fun t => by
      change |Real.exp (-s*t) * u t.toNNReal| ≤ _
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hbu _) (Real.exp_nonneg _)
  have hbf : ∀ t, |f t| ≤ M := fun t =>
    (le_add_of_nonneg_right (abs_nonneg (g t))).trans (hbound t)
  have hbg : ∀ t, |g t| ≤ M := fun t =>
    (le_add_of_nonneg_left (abs_nonneg (f t))).trans (hbound t)
  have hz := SubdiffusiveProcess.E7.laplace_unique
    ((hf.sub hg).comp continuous_real_toNNReal) (C := M)
    (fun t => (abs_sub _ _).trans (hbound t.toNNReal)) (by
      intro n hn
      have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      change (∫ t : ℝ in Set.Ioi 0, Real.exp (-(n : ℝ)*t) *
        (f t.toNNReal - g t.toNNReal)) = 0
      simp_rw [mul_sub]
      rw [integral_sub (hc f hf hbf n hn') (hc g hg hbg n hn'), he n hn', sub_self])
  funext t
  have h := hz t t.property
  simpa using sub_eq_zero.mp h

#print axioms s5_continuous_bounded_scalar_Laplace_unique

/-- A Laplace identity for scalar observations identifies the actual supplied
kernel orbit with the projected analytic orbit. The identity is an explicit
conditional input, and the kernel representation retains the supplied law. -/
theorem s5_unforced_supplied_scalar_orbit_of_Laplace
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

#print axioms s5_unforced_supplied_scalar_orbit_of_Laplace

/-- Bounded observations of a Markov kernel on continuous paths have
continuous time orbits at each initial environment. -/
theorem s5_unforced_kernel_bounded_orbit_continuous
    {d : ℕ} (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (ω : FieldPair d) (g : FieldPair d →ᵇ ℂ) :
    Continuous (fun t : ℝ≥0 => ∫ γ : Path d,
      g (translate (γ t) (reduce ω)) ∂K ω) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  exact tendsto_integral_filter_of_dominated_convergence (μ := K ω)
    (fun _ : Path d => ‖g‖)
    (Filter.Eventually.of_forall fun t : ℝ≥0 =>
      (g.continuous.comp (Probability.continuous_translate.comp
        ((continuous_eval_const t).prodMk (continuous_const (y := reduce ω))))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ : ℝ≥0 =>
      Filter.Eventually.of_forall fun _ : Path d => g.norm_coe_le_norm _)
    (integrable_const ‖g‖)
    (Filter.Eventually.of_forall fun γ : Path d =>
      (g.continuous.comp (Probability.continuous_translate.comp
        (γ.continuous.prodMk (continuous_const (y := reduce ω))))).tendsto s)

#print axioms s5_unforced_kernel_bounded_orbit_continuous

/-- Countably many continuous scalar observations agree at every time on one
common full event when they agree at every nonnegative rational time. -/
theorem s5_unforced_scalar_orbits_common_conull
    {d : ℕ} (μ : Measure (FieldPair d)) (F G : ℕ → ℝ≥0 → FieldPair d → ℂ)
    (hcont : ∀ᵐ ω ∂μ, ∀ n, Continuous (fun t => F n t ω) ∧ Continuous (fun t => G n t ω))
    (hdense : ∀ (n : ℕ) (q : ℚ≥0), F n (q : ℝ≥0) =ᵐ[μ] G n (q : ℝ≥0)) :
    ∀ᵐ ω ∂μ, ∀ n t, F n t ω = G n t ω := by
  filter_upwards [hcont, ae_all_iff.mpr (fun n => ae_all_iff.mpr (hdense n))] with ω hc he
  intro n t
  have h : (fun x : ℝ => F n x.toNNReal ω) = fun x : ℝ => G n x.toNNReal ω := by
    apply Rat.denseRange_cast.equalizer
      ((hc n).1.comp continuous_real_toNNReal) ((hc n).2.comp continuous_real_toNNReal)
    funext q
    change F n (q : ℝ).toNNReal ω = G n (q : ℝ).toNNReal ω
    by_cases hq : 0 ≤ q
    · have hcast : (q : ℝ).toNNReal = (q.toNNRat : ℝ≥0) := by
        apply Subtype.ext
        change ((q : ℝ).toNNReal : ℝ) = ((q.toNNRat : ℝ≥0) : ℝ)
        simp only [Real.coe_toNNReal', max_eq_left (Rat.cast_nonneg.mpr hq)]
        exact congrArg (fun r : ℚ => (r : ℝ)) (Rat.coe_toNNRat q hq).symm
      rw [hcast]
      exact he n q.toNNRat
    · have hcast : (q : ℝ).toNNReal = 0 := by
        apply Subtype.ext
        change ((q : ℝ).toNNReal : ℝ) = (0 : ℝ≥0)
        simp only [Real.coe_toNNReal', max_eq_right (Rat.cast_nonpos.mpr (le_of_not_ge hq)),
          NNReal.coe_zero]
      rw [hcast]
      simpa only [NNRat.cast_zero] using he n 0
  have ht := congrFun h (t : ℝ)
  simpa only [Real.toNNReal_coe] using ht

/-- Rational-time identification for the same supplied origin kernel extends
simultaneously to every time and every test in a countable family, provided
the actual scalar representatives have pointwise continuous time orbits. -/
theorem s5_unforced_supplied_bounded_orbits_common_conull
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (K : Kernel (FieldPair d) (Path d))
    (g : ℕ → FieldPair d →ᵇ ℂ) (F : ℕ → Lp ℂ 2 (reducedLaw Q))
    (hcont : ∀ᵐ ω ∂Q.measure, ∀ n,
      Continuous (fun t => forcedComplexEvolution Q i 0 t (F n) (reduce ω)) ∧
      Continuous (fun t => ∫ γ : Path d, g n (translate (γ t) (reduce ω)) ∂K ω))
    (hid : ∀ n (q : ℚ≥0),
      (fun ω => forcedComplexEvolution Q i 0 (q : ℝ≥0) (F n) (reduce ω)) =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, g n (translate (γ (q : ℝ≥0)) (reduce ω)) ∂K ω) :
    ∀ᵐ ω ∂Q.measure, ∀ n t,
      forcedComplexEvolution Q i 0 t (F n) (reduce ω) =
        ∫ γ : Path d, g n (translate (γ t) (reduce ω)) ∂K ω :=
  s5_unforced_scalar_orbits_common_conull Q.measure _ _ hcont hid

/-- For a Markov kernel, only continuity of the analytic representatives is
needed to extend rational-time bounded-observation identities. -/
theorem s5_unforced_markov_bounded_orbits_common_conull
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (g : ℕ → FieldPair d →ᵇ ℂ) (F : ℕ → Lp ℂ 2 (reducedLaw Q))
    (hcont : ∀ᵐ ω ∂Q.measure, ∀ n,
      Continuous (fun t => forcedComplexEvolution Q i 0 t (F n) (reduce ω)))
    (hid : ∀ n (q : ℚ≥0),
      (fun ω => forcedComplexEvolution Q i 0 (q : ℝ≥0) (F n) (reduce ω)) =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, g n (translate (γ (q : ℝ≥0)) (reduce ω)) ∂K ω) :
    ∀ᵐ ω ∂Q.measure, ∀ n t,
      forcedComplexEvolution Q i 0 t (F n) (reduce ω) =
        ∫ γ : Path d, g n (translate (γ t) (reduce ω)) ∂K ω := by
  apply s5_unforced_supplied_bounded_orbits_common_conull Q i K g F ?_ hid
  filter_upwards [hcont] with ω hω
  exact fun n => ⟨hω n, s5_unforced_kernel_bounded_orbit_continuous K ω (g n)⟩

#print axioms s5_unforced_scalar_orbits_common_conull
#print axioms s5_unforced_supplied_bounded_orbits_common_conull
#print axioms s5_unforced_markov_bounded_orbits_common_conull

end EinsteinFull
