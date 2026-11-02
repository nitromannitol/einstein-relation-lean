import EinsteinFull.Calculus.CLMarkovRestart
import EinsteinFull.Calculus.U5ReducedAllStartKernel
import EinsteinFull.Calculus.U3RealForceQuenchedAction
import EinsteinFull.Calculus.C12ClockCocycleIdentity
import EinsteinFull.Calculus.S4SmoothGeneratorSupport
import EinsteinFull.Calculus.S4PolishSupport

/-!
# Stationarity of the unit clock shift for the unforced environment process

On smooth environments the textbook reduced martingale problem is well posed from every start,
so its solutions are Markov at deterministic times and covariant under spatial translation.
With the stationarity of the environment marginal, the unit shift of the environment–path pair
preserves the annealed unforced law.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

/-- The reduction of a coefficient pair determines the pair. -/
theorem reduce_injective : Function.Injective (reduce (d := d)) := by
  intro ω ω' h
  have h2 : clockDensity ω = clockDensity ω' := congrArg (fun ρ : FieldPair d => ⇑ρ.2) h
  have h1 : reducedCoefficient ω = reducedCoefficient ω' :=
    congrArg (fun ρ : FieldPair d => ⇑ρ.1) h
  have hV : ⇑ω.2 = ⇑ω'.2 := by
    funext x
    have hx : Real.exp (-2 * ω.2 x) = Real.exp (-2 * ω'.2 x) := congrFun h2 x
    have := Real.exp_injective hx
    linarith
  have ha : ⇑ω.1 = ⇑ω'.1 := by
    funext x
    have hx : clockDensity ω x • ω.1 x = clockDensity ω' x • ω'.1 x := congrFun h1 x
    rw [congrFun h2 x] at hx
    exact smul_right_injective (Mat d) (clockDensity_pos ω' x).ne' hx
  exact Prod.ext (ContinuousMap.ext (congrFun ha)) (ContinuousMap.ext (congrFun hV))

/-- The reduction is a measurable embedding. -/
theorem measurableEmbedding_reduce : MeasurableEmbedding (reduce (d := d)) := by
  let : PolishSpace (FieldPair d) := fieldPair_polish d
  exact Probability.continuous_reduce.measurableEmbedding reduce_injective

/-- If the reduced environment seen from the particle has the reduced law at time `t`, the
physical environment seen from the particle has the environment law. -/
theorem map_translate_eq_of_reduced {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (μ : Measure (FieldPair d × Path d)) (t : ℝ≥0)
    (h : Measure.map (fun z : FieldPair d × Path d => translate (z.2 t) (reduce z.1)) μ =
      reducedLaw Q) :
    Measure.map (fun z : FieldPair d × Path d => translate (z.2 t) z.1) μ = Q.measure := by
  have hE : Measurable (fun z : FieldPair d × Path d => translate (z.2 t) z.1) :=
    (Probability.continuous_translate.comp
      ((continuous_snd.eval continuous_const).prodMk continuous_fst)).measurable
  apply measurableEmbedding_reduce.map_injective
  rw [Measure.map_map Probability.continuous_reduce.measurable hE]
  exact h

/-- Translation by a point read off the path is jointly continuous. -/
theorem continuous_translatePath_joint :
    Continuous (fun p : Vec d × Path d => translatePath p.1 p.2) := by
  have e : (fun p : Vec d × Path d => translatePath p.1 p.2) =
      fun p => ContinuousMap.const ℝ≥0 p.1 + p.2 := rfl
  rw [e]
  exact (ContinuousMap.continuous_const'.comp continuous_fst).add continuous_snd

section Kernel

variable {Λ : ℝ} (hΛ : 0 < Λ) (i : Fin d) (lam : ℝ)

include hΛ in
/-- The textbook reduced coefficients of a regular environment are bounded and measurable. -/
theorem reduced_bddCoef {ω : FieldPair d} (hω : IsRegular Λ ω) :
    ∃ M, BddCoef (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam) M := by
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  exact ⟨max Ma Mb, ⟨fun k j => (hA.matrix_elem k j).measurable,
    fun k => (measurable_pi_apply k).comp hb,
    fun y k j => (hAb y k j).trans (le_max_left _ _),
    fun y k => (hbb y k).trans (le_max_right _ _)⟩⟩

omit hΛ in
/-- The forced drift of the translated environment is the translated forced drift. -/
theorem forcedDrift_reduced_translate (y : Vec d) (ω : FieldPair d) :
    forcedDrift (reducedCoefficient (translate y ω)) i lam =
      fun w => forcedDrift (reducedCoefficient ω) i lam (y + w) := by
  funext w j
  have hk : ∀ k : Fin d,
      coordinateDerivative k (fun z => reducedCoefficient (translate y ω) z k j) w =
        coordinateDerivative k (fun z => reducedCoefficient ω z k j) (y + w) := fun k => by
    unfold coordinateDerivative
    exact congrArg (fun L => L (unitVector k))
      (fderiv_comp_add_left (𝕜 := ℝ) (f := fun z => reducedCoefficient ω z k j) y (x := w))
  simp only [forcedDrift, matrixDivDrift, hk]
  rfl

variable {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular Λ ω → ∀ x : Vec d,
    SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam))
      x (K (ω, x)))

omit [IsMarkovKernel K] in
include hΛ hK in
/-- Every textbook reduced solution is the kernel law at its start. -/
theorem reducedKernel_eq_of_solves (hd : 1 ≤ d) {ω : FieldPair d} (hω : IsRegular Λ ω)
    (y : Vec d) {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam))
      y P) :
    P = K (ω, y) :=
  (foundation_reduced_textbook_well_posed hd hΛ hω i lam y).unique hP (hK ω hω y)

include hΛ hK in
/-- Spatial covariance of the textbook reduced kernel. -/
theorem reducedKernel_translate (hd : 1 ≤ d) {ω : FieldPair d} (hω : IsRegular Λ ω)
    (y : Vec d) :
    K (ω, y) = (K (translate y ω, 0)).map (translatePath y) := by
  have hω' : IsRegular Λ (translate y ω) :=
    (ActualImageLpStateTransport.isRegular_translate_iff y ω).mpr hω
  obtain ⟨M, hM⟩ := reduced_bddCoef hΛ i lam hω
  have h0 := hK _ hω' 0
  rw [forcedDrift_reduced_translate] at h0
  exact (reducedKernel_eq_of_solves hΛ i lam hK hd hω y (solves_map_translatePath hM y h0)).symm

end Kernel

/-- The annealed coordinate law is the composition of the environment law with the probability
parts of the quenched laws. -/
theorem annealedCoordinateJoint_eq_compProd
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (Y : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw Y ω)) :
    Carriers.annealedCoordinateJoint Q Y op =
      Q.compProd (Probability.probabilityPart (originLaw Y)) := by
  have hae := Probability.probabilityPart_ae_eq Q (originLaw Y) op
  ext S hS
  have h := Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_lintegral
    Q (originLaw Y) op (S.indicator 1) (measurable_one.indicator hS)
  unfold Carriers.annealedCoordinateJoint
  rw [← lintegral_indicator_one hS, h, Measure.compProd_apply hS]
  refine lintegral_congr_ae (hae.mono fun ω hω => ?_)
  dsimp only
  rw [hω, ← lintegral_indicator_one (measurable_prodMk_left hS)]
  rfl

/-- On smooth environments the supplied unforced annealed law is the environment law composed with
the textbook reduced kernel started at the origin; that kernel solves the textbook problem from
every start on every regular environment. -/
theorem exists_unforced_reduced_kernel (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0 (Y (0, ω)))
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω)) :
    ∃ K : Kernel (FieldPair d × Vec d) (Path d), IsMarkovKernel K ∧
      (∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
        SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x))) ∧
      Carriers.annealedCoordinateJoint Q.measure Y hprob =
        Q.measure ⊗ₘ K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const) := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  let i : Fin d := ⟨0, by omega⟩
  have hΛ : 0 < D.ellipticity := zero_lt_one.trans_le D.one_le_ellipticity
  obtain ⟨K, hKm, hK⟩ := u5_reduced_textbook_kernel_all_starts (by omega) hΛ i 0
  refine ⟨K, hKm, hK, ?_⟩
  rw [annealedCoordinateJoint_eq_compProd]
  refine Measure.compProd_congr ?_
  filter_upwards [Probability.probabilityPart_ae_eq Q.measure (originLaw Y) hprob, hY,
    Q.regular, hQ] with ω h1 hYω hω hsm
  rw [h1]
  exact reducedKernel_eq_of_solves hΛ i 0 hK (by omega) hω 0
    ((reducedGenerator_solves_iff hsm.1 i 0 0 _).1 hYω)

/-- The unit shift of the environment–path pair preserves the annealed unforced law on smooth
environments. -/
theorem measurePreserving_c12ClockShift_one (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0 (Y (0, ω)))
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω)) :
    MeasurePreserving (c12ClockShift 1) (Carriers.annealedCoordinateJoint Q.measure Y hprob)
      (Carriers.annealedCoordinateJoint Q.measure Y hprob) := by
  classical
  have : IsProbabilityMeasure Q.measure := Q.probability
  let i : Fin d := ⟨0, by omega⟩
  have hΛ : 0 < D.ellipticity := zero_lt_one.trans_le D.one_le_ellipticity
  have hd1 : 1 ≤ d := by omega
  obtain ⟨K, hKm, hK, hJ⟩ := exists_unforced_reduced_kernel hd D Q hQ Y hY hprob
  let K0 : Kernel (FieldPair d) (Path d) :=
    K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const)
  have : IsMarkovKernel K0 := by unfold K0; infer_instance
  have hK0 : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (K0 ω) := by
    filter_upwards [Q.regular, hQ] with ω hω hsm
    exact (reducedGenerator_solves_iff hsm.1 i 0 0 _).2 (hK ω hω 0)
  have hmarg (t : ℝ≥0) : Measure.map (fun z : FieldPair d × Path d => translate (z.2 t) z.1)
      (Q.measure ⊗ₘ K0) = Q.measure :=
    map_translate_eq_of_reduced Q _ t (u3_unforced_annealed_marginal_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q K0 hK0 t)
  have hθ : Measurable (c12ClockShift (d := d) 1) := (continuous_c12ClockShift 1).measurable
  rw [hJ]
  refine ⟨hθ, Measure.ext fun S hS => ?_⟩
  rw [Measure.map_apply hθ hS]
  let one : FieldPair d × Path d → ℝ := S.indicator fun _ => 1
  have hone : Measurable one := measurable_const.indicator hS
  have hone_b (z : FieldPair d × Path d) : |one z| ≤ 1 := by
    by_cases hz : z ∈ S <;> simp [one, hz]
  have hint (F : FieldPair d × Path d → ℝ) (hF : Measurable F) (hFb : ∀ z, |F z| ≤ 1) :
      Integrable F (Q.measure ⊗ₘ K0) :=
    Integrable.of_bound hF.aestronglyMeasurable 1
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hFb z)
  let g : FieldPair d → ℝ := fun ω' => ∫ η, one (ω', η) ∂K0 ω'
  have hg : Measurable g :=
    (StronglyMeasurable.integral_kernel_prod_right (κ := K0) (f := fun ω' η => one (ω', η))
      hone.stronglyMeasurable).measurable
  have hgb (ω' : FieldPair d) : |g ω'| ≤ 1 := by
    have h := norm_integral_le_of_norm_le_const (μ := K0 ω') (C := 1)
      (f := fun η => one (ω', η)) (ae_of_all _ fun η => by
        simpa only [Real.norm_eq_abs] using hone_b (ω', η))
    have h1 : (K0 ω').real Set.univ = 1 := by simp [Measure.real]
    simpa only [Real.norm_eq_abs, h1, mul_one] using h
  have hE : Measurable (fun z : FieldPair d × Path d => translate (z.2 1) z.1) :=
    (Probability.continuous_translate.comp
      ((continuous_snd.eval continuous_const).prodMk continuous_fst)).measurable
  have hinner : ∀ᵐ ω ∂Q.measure,
      (∫ γ, one (c12ClockShift 1 (ω, γ)) ∂K0 ω) = ∫ γ, g (translate (γ 1) ω) ∂K0 ω := by
    filter_upwards [Q.regular] with ω hω
    obtain ⟨M, hM⟩ := reduced_bddCoef hΛ i 0 hω
    let G : Path d → ℝ := fun η => one (translate (η 0) ω, translatePath (-(η 0)) η)
    have hG : Measurable G := hone.comp
      ((Probability.continuous_translate.comp
        ((continuous_eval_const 0).prodMk continuous_const)).prodMk
        (continuous_translatePath_joint.comp
          ((continuous_eval_const 0).neg.prodMk continuous_id))).measurable
    have hGb (η : Path d) : |G η| ≤ 1 := hone_b _
    have hshift (γ : Path d) : one (c12ClockShift 1 (ω, γ)) = G (restartPath 1 γ) := by
      change one _ = one _
      congr 1
      refine Prod.ext ?_ (ContinuousMap.ext fun t => ?_)
      · change translate (γ 1) ω = translate (γ (1 + 0)) ω
        rw [add_zero]
      change γ (1 + t) - γ 1 = -γ (1 + 0) + γ (1 + t)
      rw [add_zero, neg_add_eq_sub]
    have hcond (y : Vec d) : (∫ η, G η ∂K (ω, y)) = g (translate y ω) := by
      have hω' : IsRegular D.ellipticity (translate y ω) :=
        (ActualImageLpStateTransport.isRegular_translate_iff y ω).mpr hω
      rw [reducedKernel_translate hΛ i 0 hK hd1 hω y,
        integral_map (measurable_translatePath y).aemeasurable hG.aestronglyMeasurable]
      refine integral_congr_ae ?_
      filter_upwards [(hK _ hω' 0).2.1] with η hη
      have hpath0 : translatePath (-(y + η 0)) (translatePath y η) = η := by
        ext t k
        simp [hη]
      change one (translate (y + η 0) ω, translatePath (-(y + η 0)) (translatePath y η)) =
        one (translate y ω, η)
      rw [hpath0, hη, add_zero]
    have hmk := integral_mul_restartPath hM (hK ω hω 0) (fun y => K (ω, y))
      (fun y P' hP' => reducedKernel_eq_of_solves hΛ i 0 hK hd1 hω y hP') 1
      (H := fun _ => 1) stronglyMeasurable_const (CH := 1) (fun _ => by simp) hG hGb
    simp only [one_mul] at hmk
    change (∫ γ, one (c12ClockShift 1 (ω, γ)) ∂K (ω, 0)) = ∫ γ, g (translate (γ 1) ω) ∂K (ω, 0)
    simp_rw [hshift, hmk, hcond]
  have key : (Q.measure ⊗ₘ K0).real (c12ClockShift 1 ⁻¹' S) = (Q.measure ⊗ₘ K0).real S := by
    have hpre : (c12ClockShift 1 ⁻¹' S).indicator (fun _ => (1 : ℝ)) = one ∘ c12ClockShift 1 :=
      rfl
    rw [← integral_indicator_one (hθ hS), ← integral_indicator_one hS]
    change (∫ z, (c12ClockShift 1 ⁻¹' S).indicator (fun _ => (1 : ℝ)) z ∂(Q.measure ⊗ₘ K0)) =
      ∫ z, one z ∂(Q.measure ⊗ₘ K0)
    rw [hpre]
    calc
      (∫ z, (one ∘ c12ClockShift 1) z ∂(Q.measure ⊗ₘ K0)) =
          ∫ ω, ∫ γ, one (c12ClockShift 1 (ω, γ)) ∂K0 ω ∂Q.measure :=
        Measure.integral_compProd (hint _ (hone.comp hθ) fun z => hone_b _)
      _ = ∫ ω, ∫ γ, g (translate (γ 1) ω) ∂K0 ω ∂Q.measure := integral_congr_ae hinner
      _ = ∫ z, g (translate (z.2 1) z.1) ∂(Q.measure ⊗ₘ K0) :=
        (Measure.integral_compProd (hint _ (hg.comp hE) fun z => hgb _)).symm
      _ = ∫ ω, g ω ∂Q.measure := by
        rw [← integral_map hE.aemeasurable hg.aestronglyMeasurable, hmarg 1]
      _ = ∫ z, one z ∂(Q.measure ⊗ₘ K0) :=
        (Measure.integral_compProd (hint _ hone hone_b)).symm
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 key

end EinsteinFull.Blueprint
