import EinsteinFull.Calculus.C16ReducedMPExistence
import EinsteinFull.Calculus.C16PhysicalMPExistence
import EinsteinFull.Calculus.C4TextbookFoundation
import EinsteinFull.Calculus.S4PathwiseV2Support
import EinsteinFull.Calculus.S4PhysicalWellPosedSupport
import EinsteinFull.Calculus.C8FoundationGMPAssociation
import SubdiffusiveProcess.Section10.TorsionExitDynkinMartingale
import SubdiffusiveProcess.MultiplicativeChaos.TimeMarginal
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Generator transfer for arbitrary physical martingale-problem laws

The physical and textbook generators agree on one spatial full-measure set,
simultaneously for every signed force and C² test. Transferring that identity
to an arbitrary supplied physical law requires occupation control for that
same law. Occupation control for a textbook solution alone does not supply it.

This module proves the transfer under the explicit measure-theoretic condition;
it does not assert the unconditional `physical_mp_ae_unique` foundation target.
-/

open scoped BigOperators NNReal Topology

namespace EinsteinFull

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support

/-- One spatial event identifies the physical generator with its actual anisotropic
textbook operator, for every force direction, signed force, and C² test. -/
theorem c4_physical_generator_ae_textbook {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ (i : Fin d) (lam : ℝ)
      (f : Vec d → ℝ), ContDiff ℝ 2 f →
      physicalGenerator i ω lam f x =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) f x := by
  have hA : (⇑ω.1 : Vec d → Mat d) =
      fun y => (clockDensity ω y)⁻¹ • reducedCoefficient ω y := by
    funext y
    rw [reducedCoefficient, inv_smul_smul₀ (clockDensity_pos ω y).ne']
  filter_upwards [c16_reduced_generator_ae_textbook hΛ hω] with x hx
  intro i lam f hf
  rw [physicalGenerator_eq_inv_mul, hx i lam f hf, hA]
  exact (svGenerator_smul (reducedCoefficient ω)
    (forcedDrift (reducedCoefficient ω) i lam)
    (fun y => (clockDensity ω y)⁻¹) f x).symm

/-- The textbook operator of the physical coefficient is measurable even when the
regular environment is only Lipschitz. -/
theorem c4_measurable_physical_textbook_generator {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) :
    Measurable (External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) f) := by
  obtain ⟨hA, _, _, _, hb, _⟩ := physical_svHypotheses hΛ hω i lam
  unfold External.Draft.svGenerator
  refine (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
    Finset.measurable_sum _ fun j _ => ?_)).add
    (Finset.measurable_sum _ fun k _ => ?_)
  · exact ((hA.matrix_elem k j).measurable).mul
      (measurable_fderiv_apply_const ℝ _ _)
  · exact ((measurable_pi_apply k).comp hb).mul
      (measurable_fderiv_apply_const ℝ f (unitVector k))

/-- Occupation control for the supplied physical law transports the common spatial
generator identity along almost every path, before the force/test/time quantifiers. -/
theorem c4_ae_physical_path_generator_eq_of_averaged_occupation
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (P : Measure (Path d))
    (hocc : Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) :
    ∀ᵐ γ ∂P, ∀ (i : Fin d) (lam : ℝ) (f : Vec d → ℝ),
      ContDiff ℝ 2 f → ∀ T : ℝ≥0,
      ∀ᵐ u ∂volume.restrict (Set.uIoc 0 (T : ℝ)),
        physicalGenerator i ω lam f (γ u.toNNReal) =
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
            f (γ u.toNNReal) := by
  filter_upwards [c16_ae_path_of_averaged_occupation P hocc
    (c4_physical_generator_ae_textbook hΛ hω)] with γ hγ
  intro i lam f hf T
  have hs : Set.uIoc (0 : ℝ) (T : ℝ) ⊆ Set.Ioi 0 := by
    rw [Set.uIoc_of_le T.coe_nonneg]
    exact fun _ hu => hu.1
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hγ] with u hu
  exact hu i lam f hf

/-- An arbitrary supplied physical law with absolutely continuous averaged occupation
solves the textbook problem for the physical coefficient and physical drift.
All martingale and integrability clauses are transported for this same law. -/
theorem c4_textbook_solves_of_physical_and_averaged_occupation
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (hocc : Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) :
    SolvesMartingaleProblem
      (External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)) x P := by
  refine c16_solves_of_ae_path_generator hP
    (fun f _ _ => c4_measurable_physical_textbook_generator hΛ hω i lam f) ?_
  intro f hf _ t
  filter_upwards [c4_ae_physical_path_generator_eq_of_averaged_occupation
    hΛ hω P hocc] with γ hγ
  exact hγ i lam f (contDiff_two_of_top hf) t

/-- The literal physical generator, including the default derivative values, is
measurable for every continuous environment and every test function. -/
theorem c4_measurable_physical_generator {d : ℕ} (ω : FieldPair d)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) :
    Measurable (physicalGenerator i ω lam f) := by
  have hpref : Measurable (fun x => Real.exp (2 * ω.2 x) / 2) :=
    (Real.measurable_exp.comp
      (measurable_const.mul ω.2.continuous.measurable)).div_const 2
  unfold physicalGenerator divergence coordinateDerivative dot
  refine (hpref.mul (Finset.measurable_sum _ fun k _ =>
    measurable_fderiv_apply_const ℝ _ _)).add
    (measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_))
  refine Measurable.mul ?_ (measurable_fderiv_apply_const ℝ f (unitVector k))
  simpa only [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
    ((ω.1.continuous.matrix_elem k i).measurable)

/-- Conversely, occupation control transports a textbook physical law to the
literal divergence-form physical problem for the same path measure. -/
theorem c4_physical_solves_of_textbook_and_averaged_occupation
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)) x P)
    (hocc : Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) :
    SolvesMartingaleProblem (physicalGenerator i ω lam) x P := by
  refine c16_solves_of_ae_path_generator hP
    (fun f _ _ => c4_measurable_physical_generator ω i lam f) ?_
  intro f hf _ t
  filter_upwards [c4_ae_physical_path_generator_eq_of_averaged_occupation
    hΛ hω P hocc] with γ hγ
  filter_upwards [hγ i lam f (contDiff_two_of_top hf) t] with u hu
  exact hu.symm

/-- Under averaged occupation control of one fixed law, its physical and textbook
martingale-problem predicates are equivalent, with the same starting point. -/
theorem c4_physical_solves_iff_textbook_of_averaged_occupation
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    (x : Vec d) (P : Measure (Path d))
    (hocc : Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) :
    SolvesMartingaleProblem (physicalGenerator i ω lam) x P ↔
      SolvesMartingaleProblem
        (External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)) x P :=
  ⟨fun hP => c4_textbook_solves_of_physical_and_averaged_occupation
    hΛ hω i lam hP hocc,
   fun hP => c4_physical_solves_of_textbook_and_averaged_occupation
    hΛ hω i lam hP hocc⟩

/-- Null occupation at natural finite horizons suffices for the infinite-time
averaged occupation contract. No density or probability hypothesis is required;
the path measure only needs to be s-finite. -/
theorem c4_averaged_occupation_ac_of_finite_horizon_null {d : ℕ}
    (P : Measure (Path d)) [SFinite P]
    (hfinite : ∀ (N : Set (Vec d)), MeasurableSet N →
      (volume : Measure (Vec d)) N = 0 → ∀ n : ℕ,
      (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (n : ℝ))))
        {z : Path d × ℝ | z.1 z.2.toNNReal ∈ N} = 0) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hprod (S : Set ℝ) : P.prod (volume.restrict S) =
      (P.prod volume).restrict (Set.univ ×ˢ S) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := P) (ν := volume) Set.univ S)
  have hcover : (Set.univ : Set (Path d)) ×ˢ Set.Ioi (0 : ℝ) =
      ⋃ n : ℕ, (Set.univ : Set (Path d)) ×ˢ Set.Ioc (0 : ℝ) (n : ℝ) := by
    ext z
    simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_Ioi,
      Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_ge z.2
      exact ⟨n, hz, hn⟩
    · rintro ⟨n, hn, _⟩
      exact hn
  intro N hN
  apply measure_mono_null (subset_toMeasurable (volume : Measure (Vec d)) N)
  rw [Measure.map_apply heval (measurableSet_toMeasurable _ _)]
  rw [hprod, hcover, measure_eq_zero_iff_ae_notMem,
    ae_restrict_iUnion_iff]
  intro n
  rw [← hprod, ← measure_eq_zero_iff_ae_notMem]
  exact hfinite _ (measurableSet_toMeasurable _ _)
    (by simpa only [measure_toMeasurable] using hN) n

/-- Assembly of physical-law uniqueness from the two exact announced FOUNDATION
contracts. The occupation contract concerns each supplied physical law itself;
it is not inferred from occupation control of a separately constructed law.
Both contracts remain explicit helper hypotheses until their producers close. -/
theorem c4_physical_mp_ae_unique_of_foundation_contracts
    (foundation_textbook_well_posed : External.Draft.svWellPosedStmt)
    (foundation_physical_averaged_occupation_ac :
      ∀ {d : ℕ}, 1 ≤ d → ∀ {Λ₀ : ℝ}, 0 < Λ₀ →
        ∀ {ω : FieldPair d}, IsRegular Λ₀ ω → ∀ (i : Fin d) (lam : ℝ)
          {x : Vec d} {P : Measure (Path d)},
        SolvesMartingaleProblem (physicalGenerator i ω lam) x P →
        Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)))
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (lam : ℝ) (PX PX' : QuenchedPathLaws d)
    (hX : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω)))
    (hX' : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω))) :
    ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω) := by
  have hd1 : 1 ≤ d := (by decide : 1 ≤ 2).trans hd
  have hΛ : 0 < Λ₀ := zero_lt_one.trans_le Q.ellipticity_parameter
  filter_upwards [Q.regular, hX, hX'] with ω hω hPX hPX'
  have hocc := foundation_physical_averaged_occupation_ac hd1 hΛ hω i lam hPX
  have hocc' := foundation_physical_averaged_occupation_ac hd1 hΛ hω i lam hPX'
  have htext := c4_textbook_solves_of_physical_and_averaged_occupation
    hΛ hω i lam hPX hocc
  have htext' := c4_textbook_solves_of_physical_and_averaged_occupation
    hΛ hω i lam hPX' hocc'
  obtain ⟨hc, hs, hb, he, hm, hbd⟩ := physical_svHypotheses hΛ hω i lam
  obtain ⟨P, _, huniq⟩ := foundation_textbook_well_posed d hd1
    (⇑ω.1) (physicalDrift ω i lam) hc hs hb he hm hbd 0
  exact (huniq _ htext).trans (huniq _ htext').symm

/-- A continuous coefficient has the usual product derivative when the other
factor vanishes at the evaluation point. No derivative of the coefficient is
needed, including at a point where its default `fderiv` is zero. -/
private theorem c4_hasFDerivAt_mul_zero {d : ℕ} {c g : Vec d → ℝ}
    {g' : Vec d →L[ℝ] ℝ} {x : Vec d} (hc : ContinuousAt c x)
    (hg : HasFDerivAt g g' x) (hzero : g x = 0) :
    HasFDerivAt (fun y => c y * g y) (c x • g') x := by
  have hsmall : (fun y => c y - c x) =o[𝓝 x] (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 (by
      simpa only [sub_self] using hc.tendsto.sub_const (c x))
  have hbig : g =O[𝓝 x] (fun y => y - x) := by
    simpa only [hzero, sub_zero] using hg.isBigO_sub
  have hprod : (fun y => (c y - c x) * g y) =o[𝓝 x] (fun y => y - x) := by
    simpa only [smul_eq_mul, one_smul] using hsmall.smul_isBigO hbig
  apply HasFDerivAt.of_isLittleO
  convert hprod.add (hg.isLittleO.const_mul_left (c x)) using 1
  funext y
  simp only [smul_apply, smul_eq_mul, hzero]
  ring

/-- At a critical point of a C² test, continuous coefficients suffice for the
literal divergence-form operator to equal its textbook expression. -/
theorem c4_generator_eq_svGenerator_of_gradient_eq_zero {d : ℕ}
    (A : Vec d → Mat d) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 2 f) {x : Vec d}
    (hA : ∀ k j, ContinuousAt (fun y => A y k j) x)
    (hzero : gradient f x = 0) :
    (1 / 2 : ℝ) * divergence (fun y => (A y).mulVec (gradient f y)) x +
        lam * dot ((A x).mulVec (unitVector i)) (gradient f x) =
      External.Draft.svGenerator A (forcedDrift A i lam) f x := by
  have hz (j : Fin d) : fderiv ℝ f x (unitVector j) = 0 :=
    congrFun hzero j
  have hf1 (j : Fin d) :
      DifferentiableAt ℝ (fun y => fderiv ℝ f y (unitVector j)) x := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (le_of_eq one_add_one_eq_two)
    exact ((h1.clm_apply contDiff_const).differentiable one_ne_zero) x
  have hdiv (k : Fin d) :
      coordinateDerivative k (fun y => (A y).mulVec (gradient f y) k) x =
        ∑ j, A x k j *
          fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector k) := by
    have h : HasFDerivAt (fun y => ∑ j, A y k j * fderiv ℝ f y (unitVector j))
        (∑ j, A x k j • fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x) x := by
      refine HasFDerivAt.fun_sum fun j _ => ?_
      exact c4_hasFDerivAt_mul_zero (hA k j) (hf1 j).hasFDerivAt (hz j)
    change fderiv ℝ (fun y => ∑ j, A y k j * fderiv ℝ f y (unitVector j)) x
      (unitVector k) = _
    rw [h.fderiv]
    simp only [sum_apply, smul_apply, smul_eq_mul]
  simp only [External.Draft.svGenerator, hz, mul_zero,
    Finset.sum_const_zero, add_zero]
  rw [hzero]
  simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  congr 1
  exact Finset.sum_congr rfl fun k _ => hdiv k

/-- The actual physical generator has its textbook value at every critical point
of a C² test, without requiring a smooth or regular environment. -/
theorem c4_physical_generator_eq_textbook_of_gradient_eq_zero {d : ℕ}
    (ω : FieldPair d) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 2 f) {x : Vec d} (hzero : gradient f x = 0) :
    physicalGenerator i ω lam f x =
      External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) f x := by
  have hA : (⇑ω.1 : Vec d → Mat d) =
      fun y => (clockDensity ω y)⁻¹ • reducedCoefficient ω y := by
    funext y
    rw [reducedCoefficient, inv_smul_smul₀ (clockDensity_pos ω y).ne']
  rw [physicalGenerator_eq_inv_mul]
  change (clockDensity ω x)⁻¹ *
    ((1 / 2 : ℝ) * divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x +
      lam * dot ((reducedCoefficient ω x).mulVec (unitVector i)) (gradient f x)) = _
  rw [c4_generator_eq_svGenerator_of_gradient_eq_zero _ i lam hf
    (fun k j => ((continuous_reducedCoefficient ω).matrix_elem k j).continuousAt) hzero,
    hA]
  exact (svGenerator_smul (reducedCoefficient ω)
    (forcedDrift (reducedCoefficient ω) i lam)
    (fun y => (clockDensity ω y)⁻¹) f x).symm

/-- At a critical point the physical generator agrees with the textbook generator. -/
theorem c4_physicalGenerator_eq_svGenerator_of_gradient_eq_zero
    {d : ℕ} {ω : FieldPair d} (i : Fin d) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) (x : Vec d)
    (hgrad : ∀ j : Fin d, coordinateDerivative j f x = 0) :
    physicalGenerator i ω lam f x =
      External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) f x := by
  apply c4_physical_generator_eq_textbook_of_gradient_eq_zero ω i lam hf
  funext j
  exact hgrad j

/-- The textbook operator is additive on twice continuously differentiable tests. -/
theorem c4_svGenerator_add {d : ℕ} (a : Vec d → Mat d) (b : Vec d → Vec d)
    {f g : Vec d → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : Vec d) :
    External.Draft.svGenerator a b (fun y => f y + g y) x =
      External.Draft.svGenerator a b f x + External.Draft.svGenerator a b g x := by
  have hf1 (j : Fin d) : DifferentiableAt ℝ
      (fun y => fderiv ℝ f y (unitVector j)) x := by
    exact (((hf.fderiv_right (le_of_eq one_add_one_eq_two)).clm_apply
      contDiff_const).differentiable one_ne_zero) x
  have hg1 (j : Fin d) : DifferentiableAt ℝ
      (fun y => fderiv ℝ g y (unitVector j)) x := by
    exact (((hg.fderiv_right (le_of_eq one_add_one_eq_two)).clm_apply
      contDiff_const).differentiable one_ne_zero) x
  have hfirst (y : Vec d) : fderiv ℝ (fun z => f z + g z) y =
      fderiv ℝ f y + fderiv ℝ g y :=
    fderiv_fun_add (hf.differentiable (by norm_num) y)
      (hg.differentiable (by norm_num) y)
  have hsecond (j : Fin d) :
      fderiv ℝ (fun y => fderiv ℝ (fun z => f z + g z) y (unitVector j)) x =
        fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x +
          fderiv ℝ (fun y => fderiv ℝ g y (unitVector j)) x := by
    simp only [hfirst, ContinuousLinearMap.add_apply]
    exact fderiv_fun_add (hf1 j) (hg1 j)
  simp only [External.Draft.svGenerator, hsecond]
  simp only [hfirst, ContinuousLinearMap.add_apply, mul_add, Finset.sum_add_distrib]
  ring

/-- A single coordinate test has the textbook generator even at points where
the coefficient entries are not differentiable. -/
theorem c4_generator_coordinate_eq_svGenerator {d : ℕ}
    (A : Vec d → Mat d) (i j : Fin d) (lam : ℝ) (x : Vec d) :
    (1 / 2 : ℝ) * divergence (fun y => (A y).mulVec (gradient (fun z => z j) y)) x +
        lam * dot ((A x).mulVec (unitVector i)) (gradient (fun z => z j) x) =
      External.Draft.svGenerator A (forcedDrift A i lam) (fun z => z j) x := by
  have hderiv (y : Vec d) : fderiv ℝ (fun z : Vec d => z j) y =
      (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) :=
    (hasFDerivAt_apply j y).fderiv
  simp [External.Draft.svGenerator, forcedDrift, matrixDivDrift, divergence,
    dot, gradient, coordinateDerivative, Matrix.mulVec, dotProduct, hderiv,
    unitVector, Pi.single_apply]

/-- Each coordinate test identifies the physical and textbook generators at
every point of an arbitrary continuous field pair. -/
theorem c4_physical_generator_coordinate_eq_textbook {d : ℕ}
    (ω : FieldPair d) (i j : Fin d) (lam : ℝ) (x : Vec d) :
    physicalGenerator i ω lam (fun z => z j) x =
      External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) (fun z => z j) x := by
  have hA : (⇑ω.1 : Vec d → Mat d) =
      fun y => (clockDensity ω y)⁻¹ • reducedCoefficient ω y := by
    funext y
    rw [reducedCoefficient, inv_smul_smul₀ (clockDensity_pos ω y).ne']
  rw [physicalGenerator_eq_inv_mul]
  change (clockDensity ω x)⁻¹ *
    ((1 / 2 : ℝ) * divergence (fun y => (reducedCoefficient ω y).mulVec
      (gradient (fun z => z j) y)) x +
      lam * dot ((reducedCoefficient ω x).mulVec (unitVector i))
        (gradient (fun z => z j) x)) = _
  rw [c4_generator_coordinate_eq_svGenerator, hA]
  exact (svGenerator_smul (reducedCoefficient ω)
    (forcedDrift (reducedCoefficient ω) i lam)
    (fun y => (clockDensity ω y)⁻¹) (fun z => z j) x).symm

/-- The literal physical generator is homogeneous even where fluxes are not
 differentiable: the default derivative commutes with scalar multiplication. -/
theorem c4_physical_generator_const_mul {d : ℕ} (ω : FieldPair d)
    (i : Fin d) (lam c : ℝ) (f : Vec d → ℝ) (x : Vec d) :
    physicalGenerator i ω lam (fun y => c * f y) x =
      c * physicalGenerator i ω lam f x := by
  have hD (y : Vec d) : fderiv ℝ (fun z => c * f z) y =
      c • fderiv ℝ f y := by
    simpa only [Pi.smul_def, smul_eq_mul] using
      congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := f) c) y
  have hg (y : Vec d) : gradient (fun z => c * f z) y = c • gradient f y := by
    funext j
    simp [gradient, coordinateDerivative, hD, smul_eq_mul]
  have hdiv : divergence (fun y => (reducedCoefficient ω y).mulVec
      (gradient (fun z => c * f z) y)) x =
      c * divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x := by
    unfold divergence coordinateDerivative
    simp only [hg, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    simp_rw [show ∀ (k : Fin d), fderiv ℝ
      (fun y => c * (reducedCoefficient ω y).mulVec (gradient f y) k) x =
        c • fderiv ℝ (fun y => (reducedCoefficient ω y).mulVec (gradient f y) k) x by
      intro k
      simpa only [Pi.smul_def, smul_eq_mul] using congrFun
        (fderiv_const_smul_field (𝕜 := ℝ)
          (f := fun y => (reducedCoefficient ω y).mulVec (gradient f y) k) c) x]
    simp [Finset.mul_sum, smul_eq_mul]
  rw [physicalGenerator_eq_inv_mul, physicalGenerator_eq_inv_mul]
  change (clockDensity ω x)⁻¹ * ((1 / 2 : ℝ) *
    divergence (fun y => (reducedCoefficient ω y).mulVec
      (gradient (fun z => c * f z) y)) x +
    lam * dot ((reducedCoefficient ω x).mulVec (unitVector i))
      (gradient (fun z => c * f z) x)) = _
  rw [hdiv, hg]
  simp only [reducedGenerator, dot, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ a b : ℝ, a * (c * b) = c * (a * b) by intros; ring]
  rw [← Finset.mul_sum]
  ring

/-- The textbook generator is homogeneous for arbitrary real scalars. -/
theorem c4_svGenerator_const_mul {d : ℕ} (a : Vec d → Mat d)
    (b : Vec d → Vec d) (c : ℝ) (f : Vec d → ℝ) (x : Vec d) :
    External.Draft.svGenerator a b (fun y => c * f y) x =
      c * External.Draft.svGenerator a b f x := by
  have hD (y : Vec d) : fderiv ℝ (fun z => c * f z) y = c • fderiv ℝ f y := by
    simpa only [Pi.smul_def, smul_eq_mul] using
      congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := f) c) y
  have hD2 (j : Fin d) : fderiv ℝ
      (fun y => fderiv ℝ (fun z => c * f z) y (unitVector j)) x =
      c • fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x := by
    simp only [hD, ContinuousLinearMap.smul_apply, smul_eq_mul]
    simpa only [Pi.smul_def, smul_eq_mul] using congrFun
      (fderiv_const_smul_field (𝕜 := ℝ)
        (f := fun y => fderiv ℝ f y (unitVector j)) c) x
  simp only [External.Draft.svGenerator]
  simp_rw [hD2]
  simp only [hD, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp_rw [show ∀ a b : ℝ, a * (c * b) = c * (a * b) by intros; ring]
  simp only [← Finset.mul_sum]
  ring

/-- Both operators depend only on the germ of their test function. -/
theorem c4_generator_eq_of_eventuallyEq {d : ℕ} (ω : FieldPair d)
    (i : Fin d) (lam : ℝ) {f g : Vec d → ℝ} {x : Vec d}
    (hfg : f =ᶠ[𝓝 x] g) :
    physicalGenerator i ω lam f x = physicalGenerator i ω lam g x ∧
      External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) f x =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) g x := by
  have hD : fderiv ℝ f =ᶠ[𝓝 x] fderiv ℝ g := hfg.fderiv
  have hgrad : gradient f =ᶠ[𝓝 x] gradient g := by
    filter_upwards [hD] with y hy
    funext j
    simp only [gradient, coordinateDerivative, hy]
  have hdiv : divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x =
      divergence (fun y => (reducedCoefficient ω y).mulVec (gradient g y)) x := by
    unfold divergence coordinateDerivative
    apply Finset.sum_congr rfl
    intro k _
    have he : (fun y => ((reducedCoefficient ω y).mulVec (gradient f y)) k) =ᶠ[𝓝 x]
        (fun y => ((reducedCoefficient ω y).mulVec (gradient g y)) k) := by
      filter_upwards [hgrad] with y hy
      rw [hy]
    rw [he.fderiv_eq]
  have hD2 (j : Fin d) :
      fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x =
        fderiv ℝ (fun y => fderiv ℝ g y (unitVector j)) x :=
    (hD.fun_comp (fun z => z (unitVector j))).fderiv_eq
  constructor
  · rw [physicalGenerator_eq_inv_mul, physicalGenerator_eq_inv_mul]
    change (clockDensity ω x)⁻¹ * ((1 / 2 : ℝ) *
      divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x +
      lam * dot ((reducedCoefficient ω x).mulVec (unitVector i)) (gradient f x)) = _
    rw [hdiv, hgrad.self_of_nhds]
    rfl
  · simp only [External.Draft.svGenerator, hD2, hD.self_of_nhds]

/-- A compactly supported coordinate cutoff agrees with the textbook
generator wherever the cutoff is locally equal to the coordinate. -/
theorem c4_physical_generator_local_coordinate_eq_textbook {d : ℕ}
    (ω : FieldPair d) (i j : Fin d) (lam : ℝ) {f : Vec d → ℝ} {x : Vec d}
    (hf : f =ᶠ[𝓝 x] fun z => z j) :
    physicalGenerator i ω lam f x =
      External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) f x := by
  obtain ⟨hp, ht⟩ := c4_generator_eq_of_eventuallyEq ω i lam hf
  rw [hp, ht]
  exact c4_physical_generator_coordinate_eq_textbook ω i j lam x

/-- Additivity transfers the generator discrepancy between two tests whose
difference has zero gradient at the point. -/
theorem c4_physical_generator_discrepancy_of_add_and_critical
    {d : ℕ} (ω : FieldPair d) (i : Fin d) (lam : ℝ)
    {f g : Vec d → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : Vec d) (hgrad : gradient f x = 0)
    (hadd : physicalGenerator i ω lam (fun y => f y + g y) x =
      physicalGenerator i ω lam f x + physicalGenerator i ω lam g x) :
    physicalGenerator i ω lam (fun y => f y + g y) x -
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
          (fun y => f y + g y) x =
      physicalGenerator i ω lam g x -
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) g x := by
  rw [hadd, c4_svGenerator_add _ _ hf hg,
    c4_physical_generator_eq_textbook_of_gradient_eq_zero ω i lam hf hgrad]
  ring

/-- A centered quadratic test recovers the diffusion matrix at its center. -/
theorem c4_physicalGenerator_centered_quadratic
    {d : ℕ} {Λ₀ : ℝ} {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    (x : Vec d) (j k : Fin d) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hχone : χ =ᶠ[𝓝 x] fun _ => 1) :
    physicalGenerator i ω lam
      (fun y => χ y * (y j - x j) * (y k - x k)) x = ω.1 x j k := by
  classical
  let q : Vec d → ℝ := fun y => (y j - x j) * (y k - x k)
  let f : Vec d → ℝ := fun y => χ y * (y j - x j) * (y k - x k)
  have he : f =ᶠ[𝓝 x] q := by
    filter_upwards [hχone] with y hy
    simp [f, q, hy]
  have hD (y : Vec d) : fderiv ℝ q y =
      (y j - x j) • (ContinuousLinearMap.proj k : Vec d →L[ℝ] ℝ) +
        (y k - x k) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) :=
    (((hasFDerivAt_apply j y).sub_const (x j)).mul
      ((hasFDerivAt_apply k y).sub_const (x k))).fderiv
  have hDD (l : Fin d) :
      fderiv ℝ (fun y => fderiv ℝ f y (unitVector l)) x =
        unitVector l k • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) +
          unitVector l j • (ContinuousLinearMap.proj k : Vec d →L[ℝ] ℝ) := by
    have heD : (fun y => fderiv ℝ f y (unitVector l)) =ᶠ[𝓝 x]
        (fun y => fderiv ℝ q y (unitVector l)) := by
      simpa only [Function.comp_def] using
        (he.fderiv (𝕜 := ℝ)).fun_comp (fun z => z (unitVector l))
    rw [heD.fderiv_eq]
    simp only [hD, add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    exact (((((hasFDerivAt_apply j x).sub_const (x j)).mul_const (unitVector l k)).add
      (((hasFDerivAt_apply k x).sub_const (x k)).mul_const (unitVector l j)))).fderiv
  have hf : ContDiff ℝ 2 f := by
    dsimp [f]
    exact (hχ.mul ((contDiff_apply ℝ ℝ j).sub contDiff_const)).mul
      ((contDiff_apply ℝ ℝ k).sub contDiff_const)
  have hg (l : Fin d) : coordinateDerivative l f x = 0 := by
    rw [coordinateDerivative, he.fderiv_eq, hD]
    simp
  change physicalGenerator i ω lam f x = _
  rw [c4_physicalGenerator_eq_svGenerator_of_gradient_eq_zero i lam hf x hg]
  have hsym : ω.1 x k j = ω.1 x j k :=
    congrArg (fun A : Mat d => A j k) (hω.1 x).1
  simp only [External.Draft.svGenerator, hDD, he.fderiv_eq, hD,
    add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp [unitVector, Pi.single_apply, eq_comm, mul_add, Finset.sum_add_distrib, hsym]
  ring

/-- For two fixed compact smooth tests of the same supplied martingale law,
the integrated additivity defect of the literal generator is represented by a
martingale. This does not assert that the defect is zero, or choose tests from
the random path position. -/
theorem c4_finite_test_additivity_defect_martingale {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P) {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    Martingale (fun t γ => compensatedTest L f t γ + compensatedTest L g t γ -
      compensatedTest L (fun y => f y + g y) t γ) (pathFiltration d) P ∧
    ∀ t : ℝ≥0, ∀ᵐ γ ∂P,
      compensatedTest L f t γ + compensatedTest L g t γ -
        compensatedTest L (fun y => f y + g y) t γ =
      ∫ u in (0 : ℝ)..(t : ℝ),
        (L (fun y => f y + g y) (γ u.toNNReal) -
          L f (γ u.toNNReal) - L g (γ u.toNNReal)) := by
  obtain ⟨hif, _, hmf⟩ := hP.2.2 f hf hfc
  obtain ⟨hig, _, hmg⟩ := hP.2.2 g hg hgc
  obtain ⟨his, _, hms⟩ := hP.2.2 (fun y => f y + g y) (hf.add hg) (hfc.add hgc)
  constructor
  · exact (hmf.add hmg).sub hms
  · intro t
    filter_upwards [hif t, hig t, his t] with γ hfγ hgγ hsγ
    rw [intervalIntegral.integral_sub (hsγ.sub hfγ) hgγ,
      intervalIntegral.integral_sub hsγ hfγ]
    simp only [compensatedTest]
    ring

/-- The finite-test defect martingale for the actual physical generator. -/
theorem c4_physical_finite_test_additivity_defect_martingale {d : ℕ}
    (ω : FieldPair d) (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P) {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    Martingale (fun t γ => compensatedTest (physicalGenerator i ω lam) f t γ +
      compensatedTest (physicalGenerator i ω lam) g t γ -
      compensatedTest (physicalGenerator i ω lam) (fun y => f y + g y) t γ)
      (pathFiltration d) P ∧
    ∀ t : ℝ≥0, ∀ᵐ γ ∂P,
      compensatedTest (physicalGenerator i ω lam) f t γ +
        compensatedTest (physicalGenerator i ω lam) g t γ -
        compensatedTest (physicalGenerator i ω lam) (fun y => f y + g y) t γ =
      ∫ u in (0 : ℝ)..(t : ℝ),
        (physicalGenerator i ω lam (fun y => f y + g y) (γ u.toNNReal) -
          physicalGenerator i ω lam f (γ u.toNNReal) -
          physicalGenerator i ω lam g (γ u.toNNReal)) :=
  c4_finite_test_additivity_defect_martingale hP hf hfc hg hgc

/-- The fixed-test defect is integrable on every finite time interval on one
full-measure set of paths. -/
theorem c4_finite_test_additivity_defect_intervalIntegrable {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P) {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∀ᵐ γ ∂P, ∀ t : ℝ≥0,
      IntervalIntegrable (fun u : ℝ =>
        L (fun y => f y + g y) (γ u.toNNReal) -
          L f (γ u.toNNReal) - L g (γ u.toNNReal)) volume 0 (t : ℝ) := by
  obtain ⟨hif, _, _⟩ := hP.2.2 f hf hfc
  obtain ⟨hig, _, _⟩ := hP.2.2 g hg hgc
  obtain ⟨his, _, _⟩ := hP.2.2 (fun y => f y + g y) (hf.add hg) (hfc.add hgc)
  filter_upwards [ae_all_iff.2 (fun n : ℕ => hif (n : ℝ≥0)),
    ae_all_iff.2 (fun n : ℕ => hig (n : ℝ≥0)),
    ae_all_iff.2 (fun n : ℕ => his (n : ℝ≥0))] with γ hF hG hS
  intro t
  obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
  have hsub : Set.uIcc (0 : ℝ) (t : ℝ) ⊆ Set.uIcc 0 (n : ℝ) := by
    rw [Set.uIcc_of_le t.coe_nonneg, Set.uIcc_of_le (Nat.cast_nonneg n)]
    exact Set.Icc_subset_Icc le_rfl hn
  exact (((hS n).mono_set hsub).sub ((hF n).mono_set hsub)).sub
    ((hG n).mono_set hsub)

/-- The fixed-test martingale and its integral representation agree at all
times on one full-measure set, for the same supplied law. -/
theorem c4_finite_test_additivity_defect_ae_all {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P) {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∀ᵐ γ ∂P, ∀ t : ℝ≥0,
      compensatedTest L f t γ + compensatedTest L g t γ -
        compensatedTest L (fun y => f y + g y) t γ =
      ∫ u in (0 : ℝ)..(t : ℝ),
        (L (fun y => f y + g y) (γ u.toNNReal) -
          L f (γ u.toNNReal) - L g (γ u.toNNReal)) := by
  obtain ⟨hif, _, _⟩ := hP.2.2 f hf hfc
  obtain ⟨hig, _, _⟩ := hP.2.2 g hg hgc
  obtain ⟨his, _, _⟩ := hP.2.2 (fun y => f y + g y) (hf.add hg) (hfc.add hgc)
  filter_upwards [ae_all_iff.2 (fun n : ℕ => hif (n : ℝ≥0)),
    ae_all_iff.2 (fun n : ℕ => hig (n : ℝ≥0)),
    ae_all_iff.2 (fun n : ℕ => his (n : ℝ≥0))] with γ hF hG hS
  intro t
  obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
  have hsub : Set.uIcc (0 : ℝ) (t : ℝ) ⊆ Set.uIcc 0 (n : ℝ) := by
    rw [Set.uIcc_of_le t.coe_nonneg, Set.uIcc_of_le (Nat.cast_nonneg n)]
    exact Set.Icc_subset_Icc le_rfl hn
  have hF' := (hF n).mono_set hsub
  have hG' := (hG n).mono_set hsub
  have hS' := (hS n).mono_set hsub
  rw [intervalIntegral.integral_sub (hS'.sub hF') hG',
    intervalIntegral.integral_sub hS' hF']
  simp only [compensatedTest]
  ring

/-- On one full-measure set, the integrated fixed-test defect is continuous
on every finite nonnegative time interval. -/
theorem c4_finite_test_additivity_defect_continuousOn {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P) {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∀ᵐ γ ∂P, ∀ T : ℝ≥0,
      ContinuousOn (fun t : ℝ =>
        ∫ u in (0 : ℝ)..t,
          (L (fun y => f y + g y) (γ u.toNNReal) -
            L f (γ u.toNNReal) - L g (γ u.toNNReal))) (Set.Icc 0 (T : ℝ)) := by
  filter_upwards [c4_finite_test_additivity_defect_intervalIntegrable hP hf hfc hg hgc]
    with γ hγ
  intro T
  simpa only [Set.uIcc_of_le T.coe_nonneg] using
    (intervalIntegral.continuousOn_primitive_interval' (hγ T) Set.left_mem_uIcc)

/-- The integrated fixed-test defect has bounded variation on every finite
nonnegative time interval on one full-measure set. -/
theorem c4_finite_test_additivity_defect_boundedVariationOn {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P) {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∀ᵐ γ ∂P, ∀ T : ℝ≥0,
      BoundedVariationOn (fun t : ℝ =>
        ∫ u in (0 : ℝ)..t,
          (L (fun y => f y + g y) (γ u.toNNReal) -
            L f (γ u.toNNReal) - L g (γ u.toNNReal))) (Set.Icc 0 (T : ℝ)) := by
  filter_upwards [c4_finite_test_additivity_defect_intervalIntegrable hP hf hfc hg hgc]
    with γ hγ
  intro T
  simpa only [Set.uIcc_of_le T.coe_nonneg] using
    ((hγ T).absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc).boundedVariationOn

/-- The fixed-test defect martingale itself has continuous paths of bounded
variation on every compact nonnegative time interval, almost surely. -/
theorem c4_finite_test_additivity_defect_martingale_path_regular {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P) {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∀ᵐ γ ∂P, ∀ T : ℝ≥0,
      ContinuousOn (fun t : ℝ =>
        compensatedTest L f t.toNNReal γ + compensatedTest L g t.toNNReal γ -
          compensatedTest L (fun y => f y + g y) t.toNNReal γ) (Set.Icc 0 (T : ℝ)) ∧
      BoundedVariationOn (fun t : ℝ =>
        compensatedTest L f t.toNNReal γ + compensatedTest L g t.toNNReal γ -
          compensatedTest L (fun y => f y + g y) t.toNNReal γ) (Set.Icc 0 (T : ℝ)) := by
  filter_upwards [c4_finite_test_additivity_defect_ae_all hP hf hfc hg hgc,
    c4_finite_test_additivity_defect_continuousOn hP hf hfc hg hgc,
    c4_finite_test_additivity_defect_boundedVariationOn hP hf hfc hg hgc]
    with γ hrep hcont hvar
  intro T
  have heq : Set.EqOn (fun t : ℝ =>
      compensatedTest L f t.toNNReal γ + compensatedTest L g t.toNNReal γ -
        compensatedTest L (fun y => f y + g y) t.toNNReal γ)
      (fun t : ℝ => ∫ u in (0 : ℝ)..t,
        (L (fun y => f y + g y) (γ u.toNNReal) -
          L f (γ u.toNNReal) - L g (γ u.toNNReal))) (Set.Icc 0 (T : ℝ)) := by
    intro t ht
    simpa only [Real.coe_toNNReal _ ht.1] using hrep t.toNNReal
  refine ⟨(hcont T).congr heq, ?_⟩
  change eVariationOn _ _ ≠ ⊤
  rw [eVariationOn.congr heq]
  exact hvar T

/-- Squared increments along a partition are bounded by the largest increment
times total variation. This is the pathwise estimate used for vanishing quadratic
variation. -/
theorem c4_partition_squared_increments_le_variation
    (f : ℝ → ℝ) (s : Set ℝ) (u : ℕ → ℝ) (n : ℕ) (δ : ENNReal)
    (hu : MonotoneOn u (Set.Iic n)) (hus : ∀ i ≤ n, u i ∈ s)
    (hδ : ∀ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ≤ δ) :
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ 2) ≤
      δ * eVariationOn f s := by
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ 2) ≤
        ∑ i ∈ Finset.range n, δ * edist (f (u (i + 1))) (f (u i)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [pow_two]
          gcongr
          exact hδ i hi
    _ = δ * ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) := by
      rw [Finset.mul_sum]
    _ ≤ δ * eVariationOn f s := by
      gcongr
      exact eVariationOn.sum_le_of_monotoneOn_Iic hu hus

/-- Uniform continuity controls every increment of a sequence of partitions whose
mesh tends to zero. -/
theorem c4_uniform_continuous_partition_increments
    (f : ℝ → ℝ) (s : Set ℝ) (u : ℕ → ℕ → ℝ) (N : ℕ → ℕ)
    (mesh : ℕ → ℝ) (hf : UniformContinuousOn f s)
    (hu : ∀ n i, i ≤ N n → u n i ∈ s)
    (hmesh : Filter.Tendsto mesh Filter.atTop (𝓝 0))
    (hstep : ∀ n i, i < N n → dist (u n (i + 1)) (u n i) ≤ mesh n) :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop, ∀ i < N n,
      dist (f (u n (i + 1))) (f (u n i)) < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.mp hf ε hε
  filter_upwards [hmesh.eventually (Iio_mem_nhds hδ)] with n hn
  intro i hi
  exact hδf _ (hu n (i + 1) (Nat.succ_le_of_lt hi)) _
    (hu n i (Nat.le_of_lt hi)) (lt_of_le_of_lt (hstep n i hi) hn)

/-- The length of a dyadic subinterval of a fixed interval tends to zero. -/
theorem c4_dyadic_mesh_tendsto_zero (T : ℝ) :
    Filter.Tendsto (fun n : ℕ => T / (2 : ℝ) ^ n) Filter.atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 2⁻¹ by norm_num) (show (2 : ℝ)⁻¹ < 1 by norm_num)).const_mul T
  simpa only [← inv_pow, div_eq_mul_inv, mul_zero] using h

/-- The dyadic grid on a nonnegative interval is ordered, remains in the
interval, and has the stated mesh length. -/
theorem c4_dyadic_partition_geometry (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    Monotone (fun k : ℕ => (k : ℝ) * T / (2 : ℝ) ^ n) ∧
    (∀ k : ℕ, k ≤ 2 ^ n → (k : ℝ) * T / (2 : ℝ) ^ n ∈ Set.Icc 0 T) ∧
    (∀ k : ℕ, dist (((k + 1 : ℕ) : ℝ) * T / (2 : ℝ) ^ n)
      ((k : ℝ) * T / (2 : ℝ) ^ n) = T / (2 : ℝ) ^ n) := by
  have hden : 0 < (2 : ℝ) ^ n := by positivity
  constructor
  · intro a b hab
    apply div_le_div_of_nonneg_right _ (le_of_lt hden)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hT
  constructor
  · intro k hk
    have hk' : (k : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hk
    constructor
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg k) hT) (le_of_lt hden)
    · apply (div_le_iff₀ hden).2
      nlinarith
  · intro k
    rw [Real.dist_eq]
    have heq : ((↑(k + 1) : ℝ) * T / (2 : ℝ) ^ n) -
        ((k : ℝ) * T / (2 : ℝ) ^ n) = T / (2 : ℝ) ^ n := by
      push_cast
      ring
    rw [heq, abs_of_nonneg (div_nonneg hT (le_of_lt hden))]

/-- A real-valued form of the squared-increment bound for a bounded-variation path. -/
theorem c4_partition_real_squared_increments_le_variation
    (f : ℝ → ℝ) (s : Set ℝ) (u : ℕ → ℝ) (n : ℕ) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hf : BoundedVariationOn f s)
    (hu : MonotoneOn u (Set.Iic n)) (hus : ∀ i ≤ n, u i ∈ s)
    (hδ : ∀ i ∈ Finset.range n, dist (f (u (i + 1))) (f (u i)) ≤ δ) :
    (∑ i ∈ Finset.range n, dist (f (u (i + 1))) (f (u i)) ^ 2) ≤
      δ * (eVariationOn f s).toReal := by
  have h := c4_partition_squared_increments_le_variation f s u n (ENNReal.ofReal δ)
    hu hus (by
      intro i hi
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hδ i hi))
  have hfin : ENNReal.ofReal δ * eVariationOn f s ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf
  have hreal := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hfin h) hfin).2 h
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.pow_ne_top (edist_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ0] at hreal
  simpa only [ENNReal.toReal_pow, dist_edist] using hreal

/-- The variation along any finite ordered partition is bounded by total variation. -/
theorem c4_partition_real_variation_le (f : ℝ → ℝ) (s : Set ℝ)
    (u : ℕ → ℝ) (n : ℕ) (hf : BoundedVariationOn f s)
    (hu : MonotoneOn u (Set.Iic n)) (hus : ∀ i ≤ n, u i ∈ s) :
    (∑ i ∈ Finset.range n, |f (u (i + 1)) - f (u i)|) ≤
      (eVariationOn f s).toReal := by
  have h := eVariationOn.sum_le_of_monotoneOn_Iic (f := f) (s := s) hu hus
  have hreal := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hf h) hf).2 h
  rw [ENNReal.toReal_sum (fun _ _ => edist_ne_top _ _)] at hreal
  simpa only [← dist_edist, Real.dist_eq] using hreal

/-- A continuous bounded-variation path has vanishing dyadic quadratic variation. -/
theorem c4_dyadic_quadratic_variation_tendsto_zero
    (f : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hc : ContinuousOn f (Set.Icc 0 T))
    (hv : BoundedVariationOn f (Set.Icc 0 T)) :
    Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (2 ^ n),
      |f (((k + 1 : ℕ) : ℝ) * T / (2 : ℝ) ^ n) -
        f ((k : ℝ) * T / (2 : ℝ) ^ n)| ^ 2) Filter.atTop (𝓝 0) := by
  let u : ℕ → ℕ → ℝ := fun n k => (k : ℝ) * T / (2 : ℝ) ^ n
  have huc : UniformContinuousOn f (Set.Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc
  have hinc := c4_uniform_continuous_partition_increments f (Set.Icc 0 T)
    u (fun n => 2 ^ n) (fun n => T / (2 : ℝ) ^ n) huc
    (fun n k hk => (c4_dyadic_partition_geometry T hT n).2.1 k hk)
    (c4_dyadic_mesh_tendsto_zero T)
    (fun n k _ => le_of_eq ((c4_dyadic_partition_geometry T hT n).2.2 k))
  apply Metric.tendsto_nhds.2
  intro ε hε
  let V := (eVariationOn f (Set.Icc 0 T)).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  let δ := ε / (V + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδV : δ * (V + 1) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ ε (by linarith)
  filter_upwards [hinc δ hδ] with n hn
  have hbound := c4_partition_real_squared_increments_le_variation f (Set.Icc 0 T)
    (u n) (2 ^ n) δ hδ.le hv
    ((c4_dyadic_partition_geometry T hT n).1.monotoneOn _)
    ((c4_dyadic_partition_geometry T hT n).2.1)
    (fun k hk => (hn k (Finset.mem_range.mp hk)).le)
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range (2 ^ n),
      |f (u n (k + 1)) - f (u n k)| ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbound' : (∑ k ∈ Finset.range (2 ^ n),
      |f (u n (k + 1)) - f (u n k)| ^ 2) ≤ δ * V := by
    simpa only [Real.dist_eq] using hbound
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  change (∑ k ∈ Finset.range (2 ^ n), |f (u n (k + 1)) - f (u n k)| ^ 2) < ε
  nlinarith

/-- The actual fixed-test defect paths have vanishing dyadic quadratic variation. -/
theorem c4_defect_dyadic_quadratic_variation_tendsto_zero {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P)
    {f g : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    let M : ℝ≥0 → Path d → ℝ := fun t γ =>
      compensatedTest L f t γ +
      compensatedTest L g t γ -
      compensatedTest L (fun y => f y + g y) t γ
    ∀ᵐ γ ∂P, ∀ T : ℝ≥0,
      Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (2 ^ n),
        |M ((((k + 1 : ℕ) : ℝ) * (T : ℝ) / (2 : ℝ) ^ n).toNNReal) γ -
          M (((k : ℝ) * (T : ℝ) / (2 : ℝ) ^ n).toNNReal) γ| ^ 2)
        Filter.atTop (𝓝 0) := by
  filter_upwards [c4_finite_test_additivity_defect_martingale_path_regular (L := L) (P := P) (f := f) (g := g) hP hf hfc hg hgc]
    with γ hγ
  intro T
  exact c4_dyadic_quadratic_variation_tendsto_zero
    (fun t : ℝ => compensatedTest L f t.toNNReal γ + compensatedTest L g t.toNNReal γ -
      compensatedTest L (fun y => f y + g y) t.toNNReal γ)
    (T : ℝ) T.coe_nonneg (hγ T).1 (hγ T).2

/-- The actual fixed-test defect paths have vanishing dyadic quadratic variation. -/
theorem c4_physical_defect_dyadic_quadratic_variation_tendsto_zero {d : ℕ}
    (ω : FieldPair d) (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    {f g : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    let M : ℝ≥0 → Path d → ℝ := fun t γ =>
      compensatedTest (physicalGenerator i ω lam) f t γ +
      compensatedTest (physicalGenerator i ω lam) g t γ -
      compensatedTest (physicalGenerator i ω lam) (fun y => f y + g y) t γ
    ∀ᵐ γ ∂P, ∀ T : ℝ≥0,
      Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (2 ^ n),
        |M ((((k + 1 : ℕ) : ℝ) * (T : ℝ) / (2 : ℝ) ^ n).toNNReal) γ -
          M (((k : ℝ) * (T : ℝ) / (2 : ℝ) ^ n).toNNReal) γ| ^ 2)
        Filter.atTop (𝓝 0) := by
  exact c4_defect_dyadic_quadratic_variation_tendsto_zero
    (L := physicalGenerator i ω lam) (P := P) (f := f) (g := g) hP hf hfc hg hgc

/-- Stopping an ordered partition preserves the variation bound for squared increments. -/
theorem c4_stopped_partition_real_squared_increments_le_variation
    (f : ℝ → ℝ) (s : Set ℝ) (u : ℕ → ℝ) (n m : ℕ) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hf : BoundedVariationOn f s)
    (hu : MonotoneOn u (Set.Iic n)) (hus : ∀ i ≤ n, u i ∈ s)
    (hδ : ∀ i ∈ Finset.range n, dist (f (u (i + 1))) (f (u i)) ≤ δ) :
    (∑ i ∈ Finset.range n, dist (f (u (min (i + 1) m))) (f (u (min i m))) ^ 2) ≤
      δ * (eVariationOn f s).toReal := by
  apply c4_partition_real_squared_increments_le_variation f s (fun i => u (min i m)) n δ hδ0 hf
  · intro a ha b hb hab
    apply hu (by simp only [Set.mem_Iic] at ha ⊢; omega)
      (by simp only [Set.mem_Iic] at hb ⊢; omega)
    exact min_le_min_right m hab
  · intro i hi
    exact hus _ (le_trans (Nat.min_le_left _ _) hi)
  · intro i hi
    by_cases him : i < m
    · simpa only [Nat.min_eq_left (Nat.succ_le_of_lt him), Nat.min_eq_left (Nat.le_of_lt him)]
        using hδ i hi
    · have hm : m ≤ i := Nat.le_of_not_gt him
      simp only [Nat.min_eq_right hm, Nat.min_eq_right (le_trans hm (Nat.le_succ i)), dist_self]
      exact hδ0

/-- Stopping a discrete path cannot increase its quadratic variation. -/
theorem c4_stopped_squared_increments_le (v : ℕ → ℝ) (n m : ℕ) :
    (∑ k ∈ Finset.range n, |v (min (k + 1) m) - v (min k m)| ^ 2) ≤
      ∑ k ∈ Finset.range n, |v (k + 1) - v k| ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  by_cases h : k < m
  · simp only [Nat.min_eq_left (Nat.succ_le_of_lt h), Nat.min_eq_left (Nat.le_of_lt h)]
    exact le_rfl
  · have hm : m ≤ k := Nat.le_of_not_gt h
    simp only [Nat.min_eq_right hm, Nat.min_eq_right (le_trans hm (Nat.le_succ k)),
      sub_self, abs_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact sq_nonneg _

/-- Vanishing quadratic variation is preserved by arbitrary discrete stopping. -/
theorem c4_stopped_quadratic_variation_tendsto_zero
    (v : ℕ → ℕ → ℝ) (N τ : ℕ → ℕ)
    (h : Filter.Tendsto (fun n => ∑ k ∈ Finset.range (N n),
      |v n (k + 1) - v n k| ^ 2) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∑ k ∈ Finset.range (N n),
      |v n (min (k + 1) (τ n)) - v n (min k (τ n))| ^ 2)
      Filter.atTop (𝓝 0) := by
  exact squeeze_zero (fun n => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (fun n => c4_stopped_squared_increments_le (v n) (N n) (τ n)) h

/-- The physical defect retains vanishing dyadic quadratic variation under
any path-dependent choice of stopping indices. -/
theorem c4_physical_defect_stopped_dyadic_quadratic_variation_tendsto_zero {d : ℕ}
    (ω : FieldPair d) (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    {f g : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    let M : ℝ≥0 → Path d → ℝ := fun t γ =>
      compensatedTest (physicalGenerator i ω lam) f t γ +
      compensatedTest (physicalGenerator i ω lam) g t γ -
      compensatedTest (physicalGenerator i ω lam) (fun y => f y + g y) t γ
    ∀ᵐ γ ∂P, ∀ (T : ℝ≥0) (τ : ℕ → ℕ),
      Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (2 ^ n),
        |M ((((min (k + 1) (τ n) : ℕ) : ℝ) * (T : ℝ) / (2 : ℝ) ^ n).toNNReal) γ -
          M ((((min k (τ n) : ℕ) : ℝ) * (T : ℝ) / (2 : ℝ) ^ n).toNNReal) γ| ^ 2)
        Filter.atTop (𝓝 0) := by
  filter_upwards [c4_physical_defect_dyadic_quadratic_variation_tendsto_zero
    ω i lam hP hf hfc hg hgc] with γ hγ
  intro T τ
  let v : ℕ → ℕ → ℝ := fun n k =>
    compensatedTest (physicalGenerator i ω lam) f
        (((k : ℝ) * (T : ℝ) / (2 : ℝ) ^ n).toNNReal) γ +
      compensatedTest (physicalGenerator i ω lam) g
        (((k : ℝ) * (T : ℝ) / (2 : ℝ) ^ n).toNNReal) γ -
      compensatedTest (physicalGenerator i ω lam) (fun y => f y + g y)
        (((k : ℝ) * (T : ℝ) / (2 : ℝ) ^ n).toNNReal) γ
  exact c4_stopped_quadratic_variation_tendsto_zero v (fun n => 2 ^ n) τ (hγ T)

/-- The discrete quadratic increment identity underlying the martingale square estimate. -/
theorem c4_sum_squared_increments_identity (v : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (v (k + 1) - v k) ^ 2) +
      2 * (∑ k ∈ Finset.range n, v k * (v (k + 1) - v k)) = v n ^ 2 - v 0 ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    nlinarith [ih, sq_nonneg (v (n + 1) - v n)]

/-- If the total discrete variation is below the threshold, stopping reaches the end. -/
theorem c4_discrete_variation_hitting_eq_end_of_bound (v : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (h : (∑ k ∈ Finset.range n, |v (k + 1) - v k|) ≤ B) :
    let V : ℕ → Unit → ℝ := fun j _ => ∑ k ∈ Finset.range j, |v (k + 1) - v k|
    hittingBtwn V (Set.Ioi B) 0 n () = n := by
  dsimp only
  apply hittingBtwn_eq_end_iff.mpr
  rintro ⟨j, hj, hjB⟩
  have hjbound : (∑ k ∈ Finset.range j, |v (k + 1) - v k|) ≤
      ∑ k ∈ Finset.range n, |v (k + 1) - v k| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj.2)
      (fun _ _ _ => abs_nonneg _)
  simp only [Set.mem_Ioi] at hjB
  exact False.elim ((not_lt_of_ge (le_trans hjbound h)) hjB)

/-- A variation threshold above the path's total variation is never crossed
on any ordered partition of the interval. -/
theorem c4_partition_variation_hitting_eq_end (f : ℝ → ℝ) (s : Set ℝ)
    (u : ℕ → ℝ) (n : ℕ) (B : ℝ) (hf : BoundedVariationOn f s)
    (hu : MonotoneOn u (Set.Iic n)) (hus : ∀ i ≤ n, u i ∈ s)
    (hB : (eVariationOn f s).toReal ≤ B) :
    let V : ℕ → Unit → ℝ := fun j _ =>
      ∑ k ∈ Finset.range j, |f (u (k + 1)) - f (u k)|
    hittingBtwn V (Set.Ioi B) 0 n () = n := by
  exact c4_discrete_variation_hitting_eq_end_of_bound (fun k => f (u k)) n B
    (le_trans (c4_partition_real_variation_le f s u n hf hu hus) hB)

/-- The accumulated variation at its first threshold crossing overshoots by at
most one increment; the same bound holds when the terminal index is reached. -/
theorem c4_discrete_variation_hitting_overshoot (v : ℕ → ℝ) (n : ℕ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hstep : ∀ k < n, |v (k + 1) - v k| ≤ δ) :
    let V : ℕ → Unit → ℝ := fun j _ => ∑ k ∈ Finset.range j, |v (k + 1) - v k|
    let τ := hittingBtwn V (Set.Ioi B) 0 n ()
    τ ≤ n ∧ (∑ k ∈ Finset.range τ, |v (k + 1) - v k|) ≤ B + δ := by
  dsimp only
  let V : ℕ → Unit → ℝ := fun j _ => ∑ k ∈ Finset.range j, |v (k + 1) - v k|
  let τ := hittingBtwn V (Set.Ioi B) 0 n ()
  have hτ : τ ≤ n := hittingBtwn_le ()
  constructor
  · exact hτ
  · change V τ () ≤ B + δ
    cases h : τ with
    | zero =>
      simp only [V, Finset.range_zero, Finset.sum_empty]
      linarith
    | succ k =>
      have hprev : V k () ≤ B := by
        have hnot := notMem_of_lt_hittingBtwn (u := V) (s := Set.Ioi B)
          (n := 0) (m := n) (ω := ()) (by omega : k < τ) (Nat.zero_le k)
        simpa only [Set.mem_Ioi, not_lt] using hnot
      have hk : k < n := by omega
      change (∑ i ∈ Finset.range (k + 1), |v (i + 1) - v i|) ≤ B + δ
      rw [Finset.sum_range_succ]
      change V k () + |v (k + 1) - v k| ≤ B + δ
      exact add_le_add hprev (hstep k hk)

/-- Before the variation-threshold stop, the squared increments admit a
bound depending only on the threshold and the largest grid increment. -/
theorem c4_discrete_variation_hitting_squared_bound (v : ℕ → ℝ) (n : ℕ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hstep : ∀ k < n, |v (k + 1) - v k| ≤ δ) :
    let V : ℕ → Unit → ℝ := fun j _ => ∑ k ∈ Finset.range j, |v (k + 1) - v k|
    let τ := hittingBtwn V (Set.Ioi B) 0 n ()
    (∑ k ∈ Finset.range τ, |v (k + 1) - v k| ^ 2) ≤ δ * (B + δ) := by
  dsimp only
  let V : ℕ → Unit → ℝ := fun j _ => ∑ k ∈ Finset.range j, |v (k + 1) - v k|
  let τ := hittingBtwn V (Set.Ioi B) 0 n ()
  have hτ : τ ≤ n := hittingBtwn_le ()
  have hvar : (∑ k ∈ Finset.range τ, |v (k + 1) - v k|) ≤ B + δ :=
    (c4_discrete_variation_hitting_overshoot v n B δ hB hδ hstep).2
  calc
    (∑ k ∈ Finset.range τ, |v (k + 1) - v k| ^ 2) ≤
        ∑ k ∈ Finset.range τ, δ * |v (k + 1) - v k| := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' : k < n := lt_of_lt_of_le (Finset.mem_range.mp hk) hτ
      nlinarith [abs_nonneg (v (k + 1) - v k), hstep k hk']
    _ = δ * ∑ k ∈ Finset.range τ, |v (k + 1) - v k| := by rw [Finset.mul_sum]
    _ ≤ δ * (B + δ) := mul_le_mul_of_nonneg_left hvar hδ

/-- The quadratic variation of the stopped grid has the same deterministic
bound as the increments through the variation threshold. -/
theorem c4_discrete_variation_stopped_squared_bound (v : ℕ → ℝ) (n : ℕ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hstep : ∀ k < n, |v (k + 1) - v k| ≤ δ) :
    let V : ℕ → Unit → ℝ := fun j _ => ∑ k ∈ Finset.range j, |v (k + 1) - v k|
    let τ := hittingBtwn V (Set.Ioi B) 0 n ()
    (∑ k ∈ Finset.range n, |v (min (k + 1) τ) - v (min k τ)| ^ 2) ≤ δ * (B + δ) := by
  dsimp only
  let V : ℕ → Unit → ℝ := fun j _ => ∑ k ∈ Finset.range j, |v (k + 1) - v k|
  let τ := hittingBtwn V (Set.Ioi B) 0 n ()
  have hτ : τ ≤ n := hittingBtwn_le ()
  have heq : (∑ k ∈ Finset.range n, |v (min (k + 1) τ) - v (min k τ)| ^ 2) =
      ∑ k ∈ Finset.range τ, |v (k + 1) - v k| ^ 2 := by
    calc
      _ = ∑ k ∈ Finset.range τ, |v (min (k + 1) τ) - v (min k τ)| ^ 2 := by
        symm
        apply Finset.sum_subset (Finset.range_mono hτ)
        intro k hk hkn
        have h : τ ≤ k := Nat.le_of_not_gt (fun h => hkn (Finset.mem_range.mpr h))
        simp [Nat.min_eq_right h, Nat.min_eq_right (le_trans h (Nat.le_succ k))]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        have h : k < τ := Finset.mem_range.mp hk
        simp [Nat.min_eq_left (Nat.succ_le_of_lt h), Nat.min_eq_left (Nat.le_of_lt h)]
  rw [heq]
  exact c4_discrete_variation_hitting_squared_bound v n B δ hB hδ hstep

/-- Every value up to the variation stop stays within the threshold plus one
grid increment of the initial value. -/
theorem c4_discrete_variation_hitting_value_bound (v : ℕ → ℝ) (n : ℕ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hstep : ∀ k < n, |v (k + 1) - v k| ≤ δ) :
    let V : ℕ → Unit → ℝ := fun j _ => ∑ k ∈ Finset.range j, |v (k + 1) - v k|
    let τ := hittingBtwn V (Set.Ioi B) 0 n ()
    ∀ j ≤ τ, |v j - v 0| ≤ B + δ := by
  dsimp only
  let V : ℕ → Unit → ℝ := fun j _ => ∑ k ∈ Finset.range j, |v (k + 1) - v k|
  let τ := hittingBtwn V (Set.Ioi B) 0 n ()
  intro j hj
  have hvar : (∑ k ∈ Finset.range τ, |v (k + 1) - v k|) ≤ B + δ :=
    (c4_discrete_variation_hitting_overshoot v n B δ hB hδ hstep).2
  calc
    |v j - v 0| = |∑ k ∈ Finset.range j, (v (k + 1) - v k)| := by
      rw [Finset.sum_range_sub]
    _ ≤ ∑ k ∈ Finset.range j, |v (k + 1) - v k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range τ, |v (k + 1) - v k| := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
        (fun _ _ _ => abs_nonneg _)
    _ ≤ B + δ := hvar

/-- Accumulated variation on a discrete grid is adapted whenever the original
process is adapted. -/
theorem c4_discrete_variation_adapted {Ω : Type*} {m : MeasurableSpace Ω}
    {ℱ : Filtration ℕ m} {X : ℕ → Ω → ℝ} (hX : Adapted ℱ X) :
    Adapted ℱ (fun j ω => ∑ k ∈ Finset.range j, |X (k + 1) ω - X k ω|) := by
  intro j
  refine Finset.measurable_sum _ fun k hk => ?_
  have hk' : k + 1 ≤ j := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
  exact continuous_abs.measurable.comp
    ((hX.measurable_le hk').sub (hX.measurable_le (by omega : k ≤ j)))

/-- The first discrete crossing of a variation threshold is a stopping time. -/
theorem c4_discrete_variation_isStoppingTime {Ω : Type*} {m : MeasurableSpace Ω}
    {ℱ : Filtration ℕ m} {X : ℕ → Ω → ℝ} (hX : Adapted ℱ X) (B : ℝ) (n : ℕ) :
    IsStoppingTime ℱ (fun ω => (hittingBtwn
      (fun j ω => ∑ k ∈ Finset.range j, |X (k + 1) ω - X k ω|) (Set.Ioi B) 0 n ω : ℕ)) := by
  exact c4_discrete_variation_adapted hX |>.isStoppingTime_hittingBtwn measurableSet_Ioi

/-- Stopping a discrete martingale at its variation threshold preserves the
martingale property. -/
theorem c4_discrete_variation_stopped_martingale {Ω : Type*} {m : MeasurableSpace Ω}
    {ℱ : Filtration ℕ m} {μ : Measure Ω} [SigmaFiniteFiltration μ ℱ]
    {X : ℕ → Ω → ℝ} (hX : Martingale X ℱ μ) (B : ℝ) (n : ℕ) :
    let τ : Ω → WithTop ℕ := fun ω => (hittingBtwn
      (fun j ω => ∑ k ∈ Finset.range j, |X (k + 1) ω - X k ω|) (Set.Ioi B) 0 n ω : ℕ)
    Martingale (stoppedProcess X τ) ℱ μ := by
  dsimp only
  let τ : Ω → WithTop ℕ := fun ω => (hittingBtwn
    (fun j ω => ∑ k ∈ Finset.range j, |X (k + 1) ω - X k ω|) (Set.Ioi B) 0 n ω : ℕ)
  have hτ : IsStoppingTime ℱ τ := c4_discrete_variation_isStoppingTime hX.stronglyAdapted.adapted B n
  apply martingale_iff.mpr
  constructor
  · change Supermartingale (stoppedProcess X τ) ℱ μ
    have heq : -stoppedProcess (-X) τ = stoppedProcess X τ := by
      funext j ω
      simp [stoppedProcess, stoppedValue]
    rw [← heq]
    exact ((hX.neg.submartingale).stoppedProcess hτ).neg
  · exact hX.submartingale.stoppedProcess hτ

/-- Sample a filtration at an increasing sequence of times. -/
def c4SampledFiltration {Ω ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    (ℱ : Filtration ι m) (q : ℕ → ι) (hq : Monotone q) : Filtration ℕ m where
  seq := fun k => ℱ (q k)
  mono' := fun _ _ hab => ℱ.mono (hq hab)
  le' := fun k => ℱ.le (q k)

/-- Deterministic monotone sampling preserves the martingale property. -/
theorem c4_martingale_sampled {Ω ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    {ℱ : Filtration ι m} {μ : Measure Ω} {X : ι → Ω → ℝ}
    (hX : Martingale X ℱ μ) (q : ℕ → ι) (hq : Monotone q) :
    Martingale (fun k => X (q k)) (c4SampledFiltration ℱ q hq) μ := by
  constructor
  · intro k
    exact hX.stronglyAdapted (q k)
  · intro k l hkl
    exact hX.2 (q k) (q l) (hq hkl)

/-- An integrable product of a martingale value and its next increment has
zero expectation. -/
theorem c4_martingale_increment_orthogonal {Ω : Type*} {m : MeasurableSpace Ω}
    {ℱ : Filtration ℕ m} {μ : Measure Ω} [SigmaFiniteFiltration μ ℱ]
    {X : ℕ → Ω → ℝ} (hX : Martingale X ℱ μ) (k : ℕ)
    (hnext : Integrable (X (k + 1)) μ) (hcurr : Integrable (X k) μ)
    (hprod : Integrable (X k * (X (k + 1) - X k)) μ) :
    ∫ ω, X k ω * (X (k + 1) ω - X k ω) ∂μ = 0 := by
  have hinc : Integrable (X (k + 1) - X k) μ := hnext.sub hcurr
  have hzero : μ[X (k + 1) - X k | ℱ k] =ᵐ[μ] 0 := by
    have hc := condExp_of_stronglyMeasurable (ℱ.le k) (hX.stronglyAdapted k) hcurr
    filter_upwards [condExp_sub hnext hcurr (ℱ k), hX.2 k (k + 1) (Nat.le_succ k)] with ω ha hb
    simp only [Pi.sub_apply, Pi.zero_apply] at ha ⊢
    rw [ha, hb, hc, sub_self]
  have hpull := condExp_mul_of_stronglyMeasurable_left (hX.stronglyAdapted k) hprod hinc
  calc
    (∫ ω, X k ω * (X (k + 1) ω - X k ω) ∂μ) =
        ∫ ω, μ[X k * (X (k + 1) - X k) | ℱ k] ω ∂μ :=
      (integral_condExp (ℱ.le k)).symm
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hpull, hzero] with ω hp hz
      simp only [Pi.mul_apply, Pi.zero_apply] at hp hz
      change μ[X k * (X (k + 1) - X k) | ℱ k] ω = (0 : ℝ)
      rw [hp, hz, mul_zero]

/-- A square-integrable martingale has the discrete square-increment identity
in expectation. -/
theorem c4_martingale_expected_square_increments {Ω : Type*} {m : MeasurableSpace Ω}
    {ℱ : Filtration ℕ m} {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : Martingale X ℱ μ)
    (hL2 : ∀ k, MemLp (X k) 2 μ) (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ ω, (X (k + 1) ω - X k ω) ^ 2 ∂μ) =
      (∫ ω, X n ω ^ 2 ∂μ) - ∫ ω, X 0 ω ^ 2 ∂μ := by
  have hstep (k : ℕ) :
      (∫ ω, (X (k + 1) ω - X k ω) ^ 2 ∂μ) =
        (∫ ω, X (k + 1) ω ^ 2 ∂μ) - ∫ ω, X k ω ^ 2 ∂μ := by
    have hinc : MemLp (X (k + 1) - X k) 2 μ := (hL2 (k + 1)).sub (hL2 k)
    have hprod : Integrable (X k * (X (k + 1) - X k)) μ := (hL2 k).integrable_mul hinc
    have hortho := c4_martingale_increment_orthogonal hX k
      ((hL2 (k + 1)).integrable (by norm_num)) ((hL2 k).integrable (by norm_num)) hprod
    have heq : (fun ω => X (k + 1) ω ^ 2) =
        (fun ω => X k ω ^ 2) + (fun ω => (X (k + 1) ω - X k ω) ^ 2) +
          (fun ω => 2 * (X k ω * (X (k + 1) ω - X k ω))) := by
      funext ω
      simp only [Pi.add_apply]
      ring
    have hi := congrArg (fun z : Ω → ℝ => ∫ ω, z ω ∂μ) heq
    simp only [Pi.add_apply] at hi
    have hincsq : Integrable (fun ω => (X (k + 1) ω - X k ω) ^ 2) μ := by
      simpa only [Pi.sub_apply] using hinc.integrable_sq
    have hcross : Integrable (fun ω => 2 * (X k ω * (X (k + 1) ω - X k ω))) μ := by
      simpa only [Pi.mul_apply, Pi.sub_apply] using hprod.const_mul 2
    have hleft : Integrable (fun ω => X k ω ^ 2 + (X (k + 1) ω - X k ω) ^ 2) μ := by
      exact (hL2 k).integrable_sq.add hincsq
    rw [integral_add hleft hcross,
      integral_add (hL2 k).integrable_sq hincsq, integral_const_mul, hortho] at hi
    linarith
  simp_rw [hstep]
  exact Finset.sum_range_sub (fun j => ∫ ω, X j ω ^ 2 ∂μ) n

/-- Uniformly bounded grid increments make the variation-stopped martingale
square-integrable when it starts at zero. -/
theorem c4_discrete_variation_stopped_memLp {Ω : Type*} {m : MeasurableSpace Ω}
    {ℱ : Filtration ℕ m} {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : Martingale X ℱ μ) (n : ℕ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hzero : X 0 =ᵐ[μ] 0)
    (hstep : ∀ᵐ ω ∂μ, ∀ k < n, |X (k + 1) ω - X k ω| ≤ δ) :
    let τ : Ω → WithTop ℕ := fun ω => (hittingBtwn
      (fun j ω => ∑ k ∈ Finset.range j, |X (k + 1) ω - X k ω|)
      (Set.Ioi B) 0 n ω : ℕ)
    ∀ k, MemLp (stoppedProcess X τ k) 2 μ := by
  dsimp only
  let τ : Ω → WithTop ℕ := fun ω => (hittingBtwn
    (fun j ω => ∑ k ∈ Finset.range j, |X (k + 1) ω - X k ω|)
    (Set.Ioi B) 0 n ω : ℕ)
  have hstop : Martingale (stoppedProcess X τ) ℱ μ :=
    c4_discrete_variation_stopped_martingale hX B n
  intro k
  apply MemLp.of_bound ((hstop.stronglyAdapted k).mono (ℱ.le k)).aestronglyMeasurable (B + δ)
  filter_upwards [hzero, hstep] with ω hω0 hωstep
  let v : ℕ → ℝ := fun j => X j ω
  let t : ℕ := hittingBtwn (fun (j : ℕ) (_ : Unit) =>
    ∑ k ∈ Finset.range j, |v (k + 1) - v k|) (Set.Ioi B) 0 n ()
  have ht := c4_discrete_variation_hitting_value_bound v n B δ hB hδ hωstep
    (min k t) (min_le_right _ _)
  have hz : v 0 = 0 := hω0
  simp only [hz, sub_zero] at ht
  have heq : τ ω = (t : WithTop ℕ) := by
    simp [τ, t, v, hittingBtwn]
  change ‖stoppedProcess X τ k ω‖ ≤ B + δ
  simp only [stoppedProcess, heq, Real.norm_eq_abs]
  change |X (((min k t : ℕ) : WithTop ℕ).untopA) ω| ≤ B + δ
  change |X (min k t) ω| ≤ B + δ
  exact ht

/-- Under a uniform grid-increment bound, the variation-stopped martingale
satisfies the square-increment identity in expectation. -/
theorem c4_discrete_variation_stopped_expected_square_increments
    {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℕ m}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : Martingale X ℱ μ) (n : ℕ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hzero : X 0 =ᵐ[μ] 0)
    (hstep : ∀ᵐ ω ∂μ, ∀ k < n, |X (k + 1) ω - X k ω| ≤ δ) :
    let τ : Ω → WithTop ℕ := fun ω => (hittingBtwn
      (fun j ω => ∑ k ∈ Finset.range j, |X (k + 1) ω - X k ω|)
      (Set.Ioi B) 0 n ω : ℕ)
    let Y := stoppedProcess X τ
    (∑ k ∈ Finset.range n, ∫ ω, (Y (k + 1) ω - Y k ω) ^ 2 ∂μ) =
      (∫ ω, Y n ω ^ 2 ∂μ) - ∫ ω, Y 0 ω ^ 2 ∂μ := by
  exact c4_martingale_expected_square_increments
    (c4_discrete_variation_stopped_martingale hX B n)
    (c4_discrete_variation_stopped_memLp hX n B δ hB hδ hzero hstep) n

/-- Bounded stopping on any family of discrete grids gives uniformly
integrable stopped values when all grids share the same terminal variable. -/
theorem c4_uniformIntegrable_stopped_grids {Ω ι : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (ℱ : ι → Filtration ℕ m) (X : ι → ℕ → Ω → ℝ) (N : ι → ℕ)
    (τ : ι → Ω → WithTop ℕ) (Z : Ω → ℝ)
    (hX : ∀ j, Martingale (X j) (ℱ j) μ)
    (hτ : ∀ j, IsStoppingTime (ℱ j) (τ j))
    (hτN : ∀ j ω, τ j ω ≤ N j)
    (hZ : Integrable Z μ) (hterminal : ∀ j, X j (N j) =ᵐ[μ] Z) :
    UniformIntegrable (fun j => stoppedValue (X j) (τ j)) 1 μ := by
  have hui := hZ.uniformIntegrable_condExp
    (ℱ := fun j => (hτ j).measurableSpace) (fun j => (hτ j).measurableSpace_le)
  apply hui.ae_eq
  intro j
  have hoptional := (hX j).stoppedValue_ae_eq_condExp_of_le_const (hτ j) (hτN j)
  exact ((condExp_congr_ae (hterminal j)).symm.trans hoptional.symm)

/-- Variation-stopped dyadic samples of the actual defect are uniformly
integrable as the grid is refined, for each fixed horizon and threshold. -/
theorem c4_physical_defect_stopped_dyadic_uniformIntegrable {d : ℕ}
    (ω : FieldPair d) (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    {f g : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (T : ℝ≥0) (B : ℝ) :
    let q : ℕ → ℕ → ℝ≥0 := fun n k => ((k : ℝ) * (T : ℝ) / (2 : ℝ) ^ n).toNNReal
    let X : ℕ → ℕ → Path d → ℝ := fun n k γ =>
      compensatedTest (physicalGenerator i ω lam) f (q n k) γ +
      compensatedTest (physicalGenerator i ω lam) g (q n k) γ -
      compensatedTest (physicalGenerator i ω lam) (fun y => f y + g y) (q n k) γ
    let τ : ℕ → Path d → WithTop ℕ := fun n γ => (hittingBtwn
      (fun j γ => ∑ k ∈ Finset.range j, |X n (k + 1) γ - X n k γ|)
      (Set.Ioi B) 0 (2 ^ n) γ : ℕ)
    UniformIntegrable (fun n => stoppedValue (X n) (τ n)) 1 P := by
  dsimp only
  letI : IsProbabilityMeasure P := hP.1
  let q : ℕ → ℕ → ℝ≥0 := fun n k => ((k : ℝ) * (T : ℝ) / (2 : ℝ) ^ n).toNNReal
  let hq (n : ℕ) : Monotone (q n) := fun a b hab => Real.toNNReal_mono
    ((c4_dyadic_partition_geometry T T.coe_nonneg n).1 hab)
  let F : ℕ → Filtration ℕ _ := fun n => c4SampledFiltration (pathFiltration d) (q n) (hq n)
  let M : ℝ≥0 → Path d → ℝ := fun t γ =>
    compensatedTest (physicalGenerator i ω lam) f t γ +
    compensatedTest (physicalGenerator i ω lam) g t γ -
    compensatedTest (physicalGenerator i ω lam) (fun y => f y + g y) t γ
  let X : ℕ → ℕ → Path d → ℝ := fun n k => M (q n k)
  let τ : ℕ → Path d → WithTop ℕ := fun n γ => (hittingBtwn
    (fun j γ => ∑ k ∈ Finset.range j, |X n (k + 1) γ - X n k γ|)
    (Set.Ioi B) 0 (2 ^ n) γ : ℕ)
  have hM : Martingale M (pathFiltration d) P :=
    (c4_physical_finite_test_additivity_defect_martingale ω i lam hP hf hfc hg hgc).1
  have hX (n : ℕ) : Martingale (X n) (F n) P := c4_martingale_sampled hM (q n) (hq n)
  have hτ (n : ℕ) : IsStoppingTime (F n) (τ n) :=
    c4_discrete_variation_isStoppingTime (hX n).stronglyAdapted.adapted B (2 ^ n)
  apply c4_uniformIntegrable_stopped_grids F X (fun n => 2 ^ n) τ (M T) hX hτ
  · intro n γ
    dsimp only [τ]
    exact_mod_cast (hittingBtwn_le γ : hittingBtwn _ _ _ (2 ^ n) γ ≤ 2 ^ n)
  · exact hM.integrable T
  · intro n
    have hqend : q n (2 ^ n) = T := by
      simp [q, Nat.cast_pow, mul_div_cancel_left₀, (show (2 : ℝ) ^ n ≠ 0 by positivity)]
    exact Filter.Eventually.of_forall (fun γ => by simp [X, hqend])

/-- The physical defect martingale sampled on a dyadic grid remains a
martingale after stopping at a discrete variation threshold. -/
theorem c4_physical_defect_dyadic_stopped_martingale {d : ℕ}
    (ω : FieldPair d) (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    {f g : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (T : ℝ≥0) (n : ℕ) (B : ℝ) :
    let q : ℕ → ℝ≥0 := fun k => ((k : ℝ) * (T : ℝ) / (2 : ℝ) ^ n).toNNReal
    let hq : Monotone q := fun a b hab => Real.toNNReal_mono
      ((c4_dyadic_partition_geometry T T.coe_nonneg n).1 hab)
    let ℱ := c4SampledFiltration (pathFiltration d) q hq
    let X : ℕ → Path d → ℝ := fun k γ =>
      compensatedTest (physicalGenerator i ω lam) f (q k) γ +
      compensatedTest (physicalGenerator i ω lam) g (q k) γ -
      compensatedTest (physicalGenerator i ω lam) (fun y => f y + g y) (q k) γ
    let τ : Path d → WithTop ℕ := fun γ => (hittingBtwn
      (fun j γ => ∑ k ∈ Finset.range j, |X (k + 1) γ - X k γ|)
      (Set.Ioi B) 0 (2 ^ n) γ : ℕ)
    Martingale (stoppedProcess X τ) ℱ P := by
  dsimp only
  letI : IsProbabilityMeasure P := hP.1
  apply c4_discrete_variation_stopped_martingale
  exact c4_martingale_sampled
    (c4_physical_finite_test_additivity_defect_martingale ω i lam hP hf hfc hg hgc).1 _ _

/-- A fixed affine copy of the ternary Cantor set, contained in `(1,2)`. -/
noncomputable def c4CantorTrapSet : Set ℝ :=
  (fun z : ℝ => 5 / 4 + z / 2) '' cantorSet

/-- The proposed trap coefficient is globally bounded even away from the set. -/
noncomputable def c4CantorTrapCoefficient (z : ℝ) : ℝ :=
  1 + min (Metric.infDist z c4CantorTrapSet) 1

theorem c4_cantorTrapSet_geometry : c4CantorTrapSet.Nonempty ∧
    IsCompact c4CantorTrapSet ∧ c4CantorTrapSet ⊆ Set.Icc (5 / 4) (7 / 4) := by
  constructor
  · refine ⟨5 / 4, 0, zero_mem_cantorSet, ?_⟩
    norm_num
  constructor
  · exact isCompact_cantorSet.image (continuous_const.add (continuous_id.div_const 2))
  · rintro _ ⟨z, hz, rfl⟩
    have hz' := cantorSet_subset_unitInterval hz
    constructor <;> linarith [hz'.1, hz'.2]

theorem c4_cantorTrapCoefficient_of_mem {z : ℝ} (hz : z ∈ c4CantorTrapSet) :
    c4CantorTrapCoefficient z = 1 := by
  simp [c4CantorTrapCoefficient, Metric.infDist_zero_of_mem hz]

theorem c4_cantorTrapCoefficient_bounds (z : ℝ) :
    1 ≤ c4CantorTrapCoefficient z ∧ c4CantorTrapCoefficient z ≤ 2 := by
  have hlo : (0 : ℝ) ≤ min (Metric.infDist z c4CantorTrapSet) 1 :=
    le_min (Metric.infDist_nonneg (x := z) (s := c4CantorTrapSet)) (by norm_num)
  have hhi := min_le_right (Metric.infDist z c4CantorTrapSet) (1 : ℝ)
  unfold c4CantorTrapCoefficient
  constructor <;> linarith

theorem c4_cantorTrapCoefficient_lipschitz : LipschitzWith 1 c4CantorTrapCoefficient := by
  have h := (Metric.lipschitz_infDist_pt c4CantorTrapSet).min_const 1
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  change dist (1 + min (Metric.infDist x c4CantorTrapSet) 1)
    (1 + min (Metric.infDist y c4CantorTrapSet) 1) ≤ _
  rw [dist_add_left]
  exact h.dist_le_mul x y

/-- This is an actual zero-potential `FieldPair`, with one coordinate. -/
noncomputable def c4CantorTrapField : FieldPair 1 :=
  (⟨fun x _ _ => c4CantorTrapCoefficient (x 0),
    continuous_pi fun _ => continuous_pi fun _ =>
      c4_cantorTrapCoefficient_lipschitz.continuous.comp (continuous_apply 0)⟩,
    ⟨fun _ => 0, continuous_const⟩)

private theorem c4_euclideanNorm_one (x : Vec 1) : euclideanNorm x = |x 0| := by
  simp [euclideanNorm, euclideanSq, dot, ← pow_two, Real.sqrt_sq_eq_abs]

/-- The concrete proposed obstruction has the actual project regularity bounds.
This coefficient check makes no assertion about a martingale-problem law. -/
theorem c4_cantorTrapField_isRegular : IsRegular 2 c4CantorTrapField := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨rfl, fun ξ => ?_⟩
    have hb := c4_cantorTrapCoefficient_bounds (x 0)
    have hlo := mul_nonneg (sub_nonneg.mpr hb.1) (mul_self_nonneg (ξ 0))
    have hhi := mul_nonneg (sub_nonneg.mpr hb.2) (mul_self_nonneg (ξ 0))
    simp [c4CantorTrapField, euclideanSq, dot, Matrix.mulVec, dotProduct]
    change (2 : ℝ)⁻¹ * (ξ 0 * ξ 0) ≤
        ξ 0 * (c4CantorTrapCoefficient (x 0) * ξ 0) ∧
      ξ 0 * (c4CantorTrapCoefficient (x 0) * ξ 0) ≤ 2 * (ξ 0 * ξ 0)
    constructor <;> nlinarith [mul_self_nonneg (ξ 0)]
  · intro x
    norm_num [c4CantorTrapField]
  · intro x y ξ
    rw [c4_euclideanNorm_one, c4_euclideanNorm_one, c4_euclideanNorm_one]
    have hl := c4_cantorTrapCoefficient_lipschitz.norm_sub_le (x 0) (y 0)
    simp only [Real.norm_eq_abs, NNReal.coe_one, one_mul] at hl
    have hmul := mul_le_mul_of_nonneg_right hl (abs_nonneg (ξ 0))
    simp [c4CantorTrapField, Matrix.mulVec, dotProduct, abs_mul]
    change |c4CantorTrapCoefficient (x 0) - c4CantorTrapCoefficient (y 0)| * |ξ 0| ≤
      2 * |x 0 - y 0| * |ξ 0|
    nlinarith [mul_nonneg (abs_nonneg (x 0 - y 0)) (abs_nonneg (ξ 0))]
  · intro x y
    change |(0 : ℝ) - 0| ≤ 2 * euclideanNorm (x - y)
    rw [sub_self, abs_zero]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- A fixed real test has only countably many nonflat zeros. This is the
exceptional-set calculation needed for the proposed random-level trap. -/
theorem c4_countable_nonflat_zeros (g : ℝ → ℝ) :
    {r | g r = 0 ∧ DifferentiableAt ℝ g r ∧ deriv g r ≠ 0}.Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  apply Filter.eventually_false_iff_eq_bot.mp
  rw [Filter.eventually_inf_principal]
  have hne : ∀ᶠ y in 𝓝[≠] x, g y ≠ 0 :=
    hx.2.1.hasDerivAt.eventually_ne hx.2.2
  filter_upwards [hne] with y hy hz
  exact hy hz.1

/-- For a fixed test and a measure with null singletons, its differentiable
zeros are flat almost everywhere. The exceptional event may depend on the test. -/
theorem c4_ae_deriv_eq_zero_of_eq_zero (μ : Measure ℝ) [NullSingletonClass μ]
    (g : ℝ → ℝ) :
    ∀ᵐ r ∂μ, g r = 0 → DifferentiableAt ℝ g r → deriv g r = 0 := by
  have h : ∀ᵐ r ∂μ,
      r ∉ {r | g r = 0 ∧ DifferentiableAt ℝ g r ∧ deriv g r ≠ 0} :=
    measure_eq_zero_iff_ae_notMem.mp ((c4_countable_nonflat_zeros g).measure_zero μ)
  filter_upwards [h] with r hr hz hd
  by_contra hne
  exact hr ⟨hz, hd, hne⟩

/-- Scalar nondifferentiability persists under the project's one-dimensional
coordinate identification. -/
theorem c4_cantorTrapCoefficient_not_differentiableAt_vec {r : ℝ}
    (hr : ¬ DifferentiableAt ℝ c4CantorTrapCoefficient r) :
    ¬ DifferentiableAt ℝ (fun x : Vec 1 => c4CantorTrapCoefficient (x 0))
      (fun _ => r) := by
  intro h
  apply hr
  have hline : DifferentiableAt ℝ (fun t : ℝ => fun _ : Fin 1 => t) r :=
    differentiableAt_pi.mpr fun _ => differentiableAt_id
  have hcomp := h.comp r hline
  exact hcomp

private theorem c4_not_differentiableAt_mul_of_nonzero {d : ℕ}
    {c g : Vec d → ℝ} {x : Vec d} (hc : ¬ DifferentiableAt ℝ c x)
    (hg : DifferentiableAt ℝ g x) (hne : g x ≠ 0) :
    ¬ DifferentiableAt ℝ (fun y => c y * g y) x := by
  intro hprod
  apply hc
  refine (hprod.mul (hg.inv hne)).congr_of_eventuallyEq ?_
  filter_upwards [hg.continuousAt.eventually_ne hne] with y hy
  simp [hy]

/-- At a nondifferentiability point of this actual scalar coefficient, every
noncritical smooth test has literal generator zero. The nondifferentiability
of the Cantor distance itself is a separate obligation. -/
theorem c4_cantorTrapField_generator_eq_zero {f : Vec 1 → ℝ}
    (hf : ContDiff ℝ 2 f) {x : Vec 1}
    (ha : ¬ DifferentiableAt ℝ (fun y : Vec 1 => c4CantorTrapCoefficient (y 0)) x)
    (hne : coordinateDerivative 0 f x ≠ 0) :
    physicalGenerator 0 c4CantorTrapField 0 f x = 0 := by
  have hg : DifferentiableAt ℝ (fun y => coordinateDerivative 0 f y) x := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (le_of_eq one_add_one_eq_two)
    exact ((h1.clm_apply contDiff_const).differentiable one_ne_zero) x
  have hd := fderiv_zero_of_not_differentiableAt
    (c4_not_differentiableAt_mul_of_nonzero ha hg hne)
  have hflux :
      (fun y : Vec 1 => (reducedCoefficient c4CantorTrapField y).mulVec (gradient f y) 0) =
        fun y => c4CantorTrapCoefficient (y 0) * coordinateDerivative 0 f y := by
    funext y
    simp [reducedCoefficient, clockDensity, c4CantorTrapField, ContinuousMap.coe_mk,
      Matrix.mulVec, dotProduct, gradient]
    exact Or.inl rfl
  simp only [physicalGenerator, zero_mul, add_zero, divergence, Fin.sum_univ_one]
  rw [hflux]
  change _ * (fderiv ℝ (fun y => c4CantorTrapCoefficient (y 0) *
    coordinateDerivative 0 f y) x) (unitVector 0) = 0
  rw [hd]
  simp


/-- For each fixed C² test, a measure with null singletons concentrated at
nondifferentiability points sees the actual trap-field generator vanish. The
full-measure event depends on this fixed test; no common event is asserted. -/
theorem c4_cantorTrapField_generator_ae_eq_zero
    (μ : Measure ℝ) [NullSingletonClass μ] {f : Vec 1 → ℝ}
    (hf : ContDiff ℝ 2 f)
    (ha : ∀ᵐ r ∂μ, ¬ DifferentiableAt ℝ c4CantorTrapCoefficient r) :
    ∀ᵐ r ∂μ, physicalGenerator 0 c4CantorTrapField 0 f (fun _ => r) = 0 := by
  let g : Vec 1 → ℝ := fun y => coordinateDerivative 0 f y
  have hgc : ContDiff ℝ 1 g := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (le_of_eq one_add_one_eq_two)
    exact h1.clm_apply contDiff_const
  have hline (r : ℝ) :
      HasDerivAt (fun t : ℝ => fun _ : Fin 1 => t) (unitVector 0) r := by
    have heq : (fun t : ℝ => t • unitVector (d := 1) 0) =
        (fun t : ℝ => fun _ : Fin 1 => t) := by
      funext t j
      fin_cases j
      simp [unitVector]
    simpa only [id_eq, one_smul, heq] using
      (hasDerivAt_id r).smul_const (unitVector (d := 1) 0)
  have hscalar (r : ℝ) : HasDerivAt (fun t => g (fun _ => t))
      (fderiv ℝ g (fun _ => r) (unitVector 0)) r := by
    simpa only [Function.comp_def] using
      (hgc.differentiable one_ne_zero (fun _ => r)).hasFDerivAt.comp_hasDerivAt r (hline r)
  filter_upwards [ha, c4_ae_deriv_eq_zero_of_eq_zero μ (fun t => g (fun _ => t))]
    with r har hflat
  by_cases hz : g (fun _ => r) = 0
  · have hderiv : fderiv ℝ g (fun _ => r) (unitVector 0) = 0 := by
      rw [← (hscalar r).deriv]
      exact hflat hz (hscalar r).differentiableAt
    have hp := c4_hasFDerivAt_mul_zero
      (c4_cantorTrapCoefficient_lipschitz.continuous.comp (continuous_apply 0)).continuousAt
      (hgc.differentiable one_ne_zero (fun _ => r)).hasFDerivAt hz
    have hflux :
        (fun y : Vec 1 => (reducedCoefficient c4CantorTrapField y).mulVec (gradient f y) 0) =
          fun y => c4CantorTrapCoefficient (y 0) * g y := by
      funext y
      simp [reducedCoefficient, clockDensity, c4CantorTrapField, ContinuousMap.coe_mk,
        Matrix.mulVec, dotProduct, gradient, g]
      exact Or.inl rfl
    simp only [physicalGenerator, zero_mul, add_zero, divergence, Fin.sum_univ_one]
    rw [hflux]
    change _ * (fderiv ℝ (fun y => c4CantorTrapCoefficient (y 0) * g y)
      (fun _ => r)) (unitVector 0) = 0
    have hp' : fderiv ℝ (fun y : Vec 1 => c4CantorTrapCoefficient (y 0) * g y)
        (fun _ => r) = c4CantorTrapCoefficient r • fderiv ℝ g (fun _ => r) := by
      simpa only [Function.comp_def] using hp.fderiv
    rw [hp']
    change _ * (c4CantorTrapCoefficient r * fderiv ℝ g (fun _ => r) (unitVector 0)) = 0
    rw [hderiv]
    simp
  · exact c4_cantorTrapField_generator_eq_zero hf
      (c4_cantorTrapCoefficient_not_differentiableAt_vec har) hz





/-- A quadratic bound on every increment forces a scalar time function to be constant.
The proof refines an interval into halves and takes the resulting geometric limit. -/
private theorem c4_eq_of_quadratic_increment_bound {V : ℝ≥0 → ℝ} {C : ℝ}
    (hV : ∀ s t : ℝ≥0, s ≤ t → V t - V s ≤ C * ((t : ℝ) - s) ^ 2)
    (s t : ℝ≥0) (hst : s ≤ t) : V t ≤ V s := by
  have hbound : ∀ n : ℕ, ∀ u v : ℝ≥0, u ≤ v →
      V v - V u ≤ C * ((v : ℝ) - u) ^ 2 * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simpa only [pow_zero, mul_one] using hV
    | succ n ih =>
      intro u v huv
      let m : ℝ≥0 := (u + v) / 2
      have hreal : (m : ℝ) = ((u : ℝ) + v) / 2 := by
        simp only [m, NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat]
      have huv' : (u : ℝ) ≤ v := huv
      have hum : u ≤ m := by
        change (u : ℝ) ≤ (m : ℝ)
        rw [hreal]
        linarith
      have hmv : m ≤ v := by
        change (m : ℝ) ≤ v
        rw [hreal]
        linarith
      calc V v - V u = (V v - V m) + (V m - V u) := by ring
        _ ≤ C * ((v : ℝ) - m) ^ 2 * (1 / 2 : ℝ) ^ n +
            C * ((m : ℝ) - u) ^ 2 * (1 / 2 : ℝ) ^ n :=
          add_le_add (ih m v hmv) (ih u m hum)
        _ = C * ((v : ℝ) - u) ^ 2 * (1 / 2 : ℝ) ^ (n + 1) := by
          rw [hreal, pow_succ]
          ring
  have hlim : Filter.Tendsto (fun n : ℕ =>
      C * ((t : ℝ) - s) ^ 2 * (1 / 2 : ℝ) ^ n) Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
        (C * ((t : ℝ) - s) ^ 2)
  exact sub_nonpos.mp (ge_of_tendsto' hlim fun n => hbound n s t hst)

/-- A martingale starting at zero with a deterministic Lipschitz bound for each
fixed pair of times vanishes at each fixed time. -/
theorem c4_martingale_eq_zero_of_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ P) {K : ℝ} (hK : 0 ≤ K)
    (hzero : ∀ᵐ γ ∂P, M 0 γ = 0)
    (hinc : ∀ s t : ℝ≥0, ∀ᵐ γ ∂P,
      |M t γ - M s γ| ≤ K * |(t : ℝ) - s|)
    (t : ℝ≥0) : ∀ᵐ γ ∂P, M t γ = 0 := by
  have hbd : ∀ s : ℝ≥0, ∀ᵐ γ ∂P, |M s γ| ≤ K * s := by
    intro s
    filter_upwards [hzero, hinc 0 s] with γ hγ hγs
    simpa only [hγ, sub_zero, NNReal.coe_zero, abs_of_nonneg s.coe_nonneg]
      using hγs
  have hmeas : ∀ s, StronglyMeasurable (M s) := fun s =>
    (hM.stronglyMeasurable s).mono (ℱ.le s)
  have hprod : ∀ s v, Integrable (fun γ => M s γ * M v γ) P := by
    intro s v
    exact (hM.integrable v).bdd_mul (hmeas s).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hbd s)
  have hsq : ∀ s, Integrable (fun γ => M s γ ^ 2) P := by
    intro s
    simpa only [pow_two] using hprod s s
  have hcross : ∀ s v, s ≤ v →
      (∫ γ, M s γ * M v γ ∂P) = ∫ γ, M s γ ^ 2 ∂P := by
    intro s v hsv
    calc (∫ γ, M s γ * M v γ ∂P)
        = ∫ γ, (P[(fun γ => M s γ * M v γ) | ℱ s]) γ ∂P :=
          (integral_condExp (ℱ.le s)).symm
      _ = ∫ γ, M s γ * (P[M v | ℱ s]) γ ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left
          (hM.stronglyMeasurable s) (hprod s v) (hM.integrable v))
      _ = ∫ γ, M s γ ^ 2 ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hM.condExp_ae_eq hsv] with γ hγ
        rw [hγ, pow_two]
  let V : ℝ≥0 → ℝ := fun s => ∫ γ, M s γ ^ 2 ∂P
  have hV : ∀ s v : ℝ≥0, s ≤ v →
      V v - V s ≤ K ^ 2 * ((v : ℝ) - s) ^ 2 := by
    intro s v hsv
    have hsv' : (s : ℝ) ≤ v := hsv
    have hD : Integrable (fun γ => (M v γ - M s γ) ^ 2) P := by
      have h := ((hM.integrable v).sub (hM.integrable s)).bdd_mul
        ((hmeas v).sub (hmeas s)).aestronglyMeasurable
        (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using hinc s v)
      simpa only [pow_two, Pi.sub_apply] using h
    have heq : (∫ γ, (M v γ - M s γ) ^ 2 ∂P) = V v - V s := by
      have halg : (fun γ => (M v γ - M s γ) ^ 2) =
          (fun γ => M v γ ^ 2 + M s γ ^ 2 - 2 * (M s γ * M v γ)) := by
        funext γ
        ring
      rw [halg, integral_sub (f := fun γ => M v γ ^ 2 + M s γ ^ 2)
          (g := fun γ => 2 * (M s γ * M v γ))
          ((hsq v).add (hsq s)) ((hprod s v).const_mul 2),
        integral_add (f := fun γ => M v γ ^ 2) (g := fun γ => M s γ ^ 2)
          (hsq v) (hsq s), integral_const_mul, hcross s v hsv]
      dsimp only [V]
      ring
    rw [← heq]
    calc (∫ γ, (M v γ - M s γ) ^ 2 ∂P)
        ≤ ∫ _γ : Ω, K ^ 2 * ((v : ℝ) - s) ^ 2 ∂P := by
          refine integral_mono_ae hD (integrable_const _) ?_
          filter_upwards [hinc s v] with γ hb
          rw [abs_of_nonneg (sub_nonneg.mpr hsv')] at hb
          have hsquare := (sq_le_sq₀ (abs_nonneg (M v γ - M s γ))
            (mul_nonneg hK (sub_nonneg.mpr hsv'))).2 hb
          simpa only [sq_abs, mul_pow] using hsquare
      _ = K ^ 2 * ((v : ℝ) - s) ^ 2 := by simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hVt : V t = 0 := by
    have hle := c4_eq_of_quadratic_increment_bound hV 0 t (by positivity)
    have hV0 : V 0 = 0 := by
      calc V 0 = ∫ _γ : Ω, (0 : ℝ) ∂P := by
            refine integral_congr_ae ?_
            filter_upwards [hzero] with γ hγ
            rw [hγ, zero_pow (by decide : 2 ≠ 0)]
        _ = 0 := integral_zero _ _
    have hnonneg : 0 ≤ V t := integral_nonneg fun γ => sq_nonneg _
    rw [hV0] at hle
    exact le_antisymm hle hnonneg
  have hae : ∀ᵐ γ ∂P, M t γ ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun γ => sq_nonneg _) (hsq t)).mp hVt
  filter_upwards [hae] with γ hγ
  exact sq_eq_zero_iff.mp hγ

/-- For two fixed tests with bounded generator values, the supplied martingale
problem forces the integral of the additivity defect to vanish. This conclusion
is for each fixed test pair and time, without a path-dependent choice of test. -/
theorem c4_finite_test_additivity_defect_integral_eq_zero {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P) {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    {Cf Cg Cs : ℝ} (hLf : ∀ y, |L f y| ≤ Cf) (hLg : ∀ y, |L g y| ≤ Cg)
    (hLs : ∀ y, |L (fun z => f z + g z) y| ≤ Cs) (t : ℝ≥0) :
    ∀ᵐ γ ∂P, (∫ u in (0 : ℝ)..(t : ℝ),
      (L (fun y => f y + g y) (γ u.toNNReal) -
        L f (γ u.toNNReal) - L g (γ u.toNNReal))) = 0 := by
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨hM, hrepr⟩ := c4_finite_test_additivity_defect_martingale hP hf hfc hg hgc
  let M : ℝ≥0 → Path d → ℝ := fun s γ =>
    compensatedTest L f s γ + compensatedTest L g s γ -
      compensatedTest L (fun y => f y + g y) s γ
  let D : Vec d → ℝ := fun y => L (fun z => f z + g z) y - L f y - L g y
  have hD : ∀ y, |D y| ≤ Cs + Cf + Cg := by
    intro y
    exact (abs_sub _ _).trans (add_le_add
      ((abs_sub _ _).trans (add_le_add (hLs y) (hLf y))) (hLg y))
  have hK : 0 ≤ Cs + Cf + Cg :=
    (abs_nonneg (D 0)).trans (hD 0)
  have hzero : ∀ᵐ γ ∂P, M 0 γ = 0 := by
    refine ae_of_all _ fun γ => ?_
    dsimp only [M, compensatedTest]
    simp only [NNReal.coe_zero, intervalIntegral.integral_same, sub_self,
      add_zero]
  have hinc : ∀ s v : ℝ≥0, ∀ᵐ γ ∂P,
      |M v γ - M s γ| ≤ (Cs + Cf + Cg) * |(v : ℝ) - s| := by
    intro s v
    obtain ⟨hif, _, _⟩ := hP.2.2 f hf hfc
    obtain ⟨hig, _, _⟩ := hP.2.2 g hg hgc
    obtain ⟨his, _, _⟩ := hP.2.2 (fun y => f y + g y) (hf.add hg) (hfc.add hgc)
    filter_upwards [hrepr s, hrepr v, hif s, hif v, hig s, hig v, his s, his v]
      with γ hs hv hfs hfv hgs hgv hss hsv
    change |(compensatedTest L f v γ + compensatedTest L g v γ -
      compensatedTest L (fun y => f y + g y) v γ) -
      (compensatedTest L f s γ + compensatedTest L g s γ -
      compensatedTest L (fun y => f y + g y) s γ)| ≤ _
    rw [hs, hv, intervalIntegral.integral_interval_sub_left
      ((hsv.sub hfv).sub hgv) ((hss.sub hfs).sub hgs)]
    simpa only [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (s : ℝ)) (b := (v : ℝ)) (C := Cs + Cf + Cg)
        (f := fun u : ℝ => D (γ u.toNNReal)) (fun u _ => by
          simpa only [Real.norm_eq_abs] using hD (γ u.toNNReal)))
  have hMt : ∀ᵐ γ ∂P, M t γ = 0 :=
    c4_martingale_eq_zero_of_lipschitz hM hK hzero hinc t
  filter_upwards [hMt, hrepr t] with γ hγ hreprγ
  exact hreprγ.symm.trans hγ

/- The bounds below reuse the regular-field argument of
C16RegularTimeChange:19–64,78–111,122–136, whose helpers are private. -/
private theorem c4_exists_lipschitz_mul {E : Type*} [PseudoMetricSpace E]
    {f g : E → ℝ} {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    {Cf Cg : ℝ} (hCf : ∀ x, |f x| ≤ Cf) (hCg : ∀ x, |g x| ≤ Cg) :
    ∃ K, LipschitzWith K (fun x => f x * g x) := by
  let C := |Cf| * (Kg : ℝ) + |Cg| * (Kf : ℝ)
  have hC : 0 ≤ C := by positivity
  refine ⟨Real.toNNReal C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.coe_toNNReal C hC, Real.dist_eq]
  calc
    |f x * g x - f y * g y| = |f x * (g x - g y) + (f x - f y) * g y| := by ring_nf
    _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
      simpa only [abs_mul] using abs_add_le (f x * (g x - g y)) ((f x - f y) * g y)
    _ ≤ |Cf| * ((Kg : ℝ) * dist x y) + ((Kf : ℝ) * dist x y) * |Cg| := by
      exact add_le_add
        (mul_le_mul ((hCf x).trans (le_abs_self _)) (by simpa only [Real.dist_eq] using hg.dist_le_mul x y)
          (abs_nonneg _) (abs_nonneg _))
        (mul_le_mul (by simpa only [Real.dist_eq] using hf.dist_le_mul x y)
          ((hCg y).trans (le_abs_self _)) (abs_nonneg _) (by positivity))
    _ = C * dist x y := by dsimp [C]; ring

/-- A quantitative product estimate, keeping the dependence on both factors. -/
private theorem c4_lipschitz_mul_bound {E : Type*} [PseudoMetricSpace E]
    {f g : E → ℝ} {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    {Cf Cg : ℝ} (hCf : ∀ x, |f x| ≤ Cf) (hCg : ∀ x, |g x| ≤ Cg) :
    LipschitzWith (Real.toNNReal (|Cf| * (Kg : ℝ) + |Cg| * (Kf : ℝ)))
      (fun x => f x * g x) := by
  let C := |Cf| * (Kg : ℝ) + |Cg| * (Kf : ℝ)
  have hC : 0 ≤ C := by positivity
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal C hC, Real.dist_eq]
  calc
    |f x * g x - f y * g y| = |f x * (g x - g y) + (f x - f y) * g y| := by ring_nf
    _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
      simpa only [abs_mul] using abs_add_le (f x * (g x - g y)) ((f x - f y) * g y)
    _ ≤ |Cf| * ((Kg : ℝ) * dist x y) + ((Kf : ℝ) * dist x y) * |Cg| := by
      exact add_le_add
        (mul_le_mul ((hCf x).trans (le_abs_self _)) (by simpa only [Real.dist_eq] using hg.dist_le_mul x y)
          (abs_nonneg _) (abs_nonneg _))
        (mul_le_mul (by simpa only [Real.dist_eq] using hf.dist_le_mul x y)
          ((hCg y).trans (le_abs_self _)) (abs_nonneg _) (by positivity))
    _ = C * dist x y := by dsimp [C]; ring

private theorem c4_reduced_flux_lipschitz {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (k : Fin d) :
    ∃ K, LipschitzWith K (fun y => (reducedCoefficient ω y).mulVec (gradient f y) k) := by
  have hg : ∀ j : Fin d, ContDiff ℝ 1 (fun y => fderiv ℝ f y (unitVector j)) := fun j =>
    ((contDiff_two_of_top hf).fderiv_right (le_of_eq one_add_one_eq_two)).clm_apply contDiff_const
  have hprod : ∀ j : Fin d, ∃ K, LipschitzWith K
      (fun y => reducedCoefficient ω y k j * fderiv ℝ f y (unitVector j)) := by
    intro j
    obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
      (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (unitVector j)) (hg j) one_ne_zero
    obtain ⟨B, hB⟩ := (hg j).continuous.bounded_above_of_compact_support
      (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (unitVector j))
    exact c4_exists_lipschitz_mul (reducedCoefficient_lipschitz hΛ hω k j) hK
      (fun y => abs_reducedCoefficient_le hΛ hω y k j)
      (fun y => by simpa only [Real.norm_eq_abs] using hB y)
  choose K hK using hprod
  refine ⟨∑ j, K j, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  change ‖(∑ j, reducedCoefficient ω x k j * fderiv ℝ f x (unitVector j)) -
      (∑ j, reducedCoefficient ω y k j * fderiv ℝ f y (unitVector j))‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ j, (K j : ℝ) * dist x y :=
      Finset.sum_le_sum fun j _ => (hK j).norm_sub_le x y
    _ = _ := by rw [← Finset.sum_mul]; simp only [NNReal.coe_sum]

/-- Uniform flux bound in terms of the gradient and its Lipschitz constant. -/
private theorem c4_reduced_flux_quantitative {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (f : Vec d → ℝ)
    (G : ℝ) (H : ℝ≥0) (hG : ∀ y j, |coordinateDerivative j f y| ≤ G)
    (hH : ∀ j, LipschitzWith H (fun y => coordinateDerivative j f y)) (k : Fin d) :
    LipschitzWith (∑ _j : Fin d, Real.toNNReal
      (|Real.exp (2 * Λ₀) * Λ₀| * (H : ℝ) + |G| *
        (Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d) : ℝ)))
      (fun y => (reducedCoefficient ω y).mulVec (gradient f y) k) := by
  let K := Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d)
  let C := Real.exp (2 * Λ₀) * Λ₀
  let L := Real.toNNReal (|C| * (H : ℝ) + |G| * (K : ℝ))
  have hprod (j : Fin d) : LipschitzWith L
      (fun y => reducedCoefficient ω y k j * fderiv ℝ f y (unitVector j)) := by
    exact c4_lipschitz_mul_bound (reducedCoefficient_lipschitz hΛ hω k j) (hH j)
      (fun y => abs_reducedCoefficient_le hΛ hω y k j) (fun y => hG y j)
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  change ‖(∑ j, reducedCoefficient ω x k j * fderiv ℝ f x (unitVector j)) -
      (∑ j, reducedCoefficient ω y k j * fderiv ℝ f y (unitVector j))‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ j : Fin d, (L : ℝ) * dist x y :=
      Finset.sum_le_sum fun j _ => (hprod j).norm_sub_le x y
    _ = _ := by rw [← Finset.sum_mul]; simp only [NNReal.coe_sum, L, C, K]

private theorem c4_bounded_reduced_generator {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ x, |reducedGenerator i ω lam f x| ≤ C := by
  choose K hK using fun k => c4_reduced_flux_lipschitz hΛ hω hf hc k
  have hfirst : ∀ j : Fin d, ∃ B : ℝ, ∀ x, |coordinateDerivative j f x| ≤ B := by
    intro j
    obtain ⟨B, hB⟩ := (continuous_fderiv_apply_first (contDiff_two_of_top hf) j).bounded_above_of_compact_support
      (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (unitVector j))
    exact ⟨B, fun x => by simpa only [coordinateDerivative, Real.norm_eq_abs] using hB x⟩
  choose B hB using hfirst
  have hdiv : ∀ x, |divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x| ≤
      ∑ k, (K k : ℝ) * ‖unitVector k‖ := by
    intro x
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    change |fderiv ℝ _ x (unitVector k)| ≤ _
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ _ x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hK k)) (norm_nonneg _))
  refine ⟨(1 / 2 : ℝ) * (∑ k, (K k : ℝ) * ‖unitVector k‖) +
      |lam| * (∑ k, (Real.exp (2 * Λ₀) * Λ₀) * B k), fun x => ?_⟩
  unfold reducedGenerator
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left (hdiv x) (by norm_num)
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg lam)
    unfold dot
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have he : (reducedCoefficient ω x).mulVec (unitVector i) k = reducedCoefficient ω x k i := by
      simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
    rw [he, abs_mul]
    exact mul_le_mul (abs_reducedCoefficient_le hΛ hω x k i) (hB k x) (abs_nonneg _)
      (by positivity)

/-- Quantitative reduced-generator bound, uniform over tests with the same
first-derivative and Lipschitz bounds. -/
theorem c4_reduced_generator_quantitative {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    (f : Vec d → ℝ) (G : ℝ) (H : ℝ≥0)
    (hG : ∀ y j, |coordinateDerivative j f y| ≤ G)
    (hH : ∀ j, LipschitzWith H (fun y => coordinateDerivative j f y)) (x : Vec d) :
    |reducedGenerator i ω lam f x| ≤
      (1 / 2 : ℝ) * (∑ k : Fin d, (∑ _j : Fin d,
        (Real.toNNReal (|Real.exp (2 * Λ₀) * Λ₀| * (H : ℝ) + |G| *
          (Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d) : ℝ)) : ℝ)) *
            ‖unitVector k‖) +
      |lam| * (∑ _k : Fin d, (Real.exp (2 * Λ₀) * Λ₀) * G) := by
  let L := Real.toNNReal (|Real.exp (2 * Λ₀) * Λ₀| * (H : ℝ) + |G| *
    (Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d) : ℝ))
  have hflux (k : Fin d) : LipschitzWith (∑ _j : Fin d, L)
      (fun y => (reducedCoefficient ω y).mulVec (gradient f y) k) :=
    c4_reduced_flux_quantitative hΛ hω f G H hG hH k
  have hdiv : |divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x| ≤
      ∑ k : Fin d, (∑ _j : Fin d, (L : ℝ)) * ‖unitVector k‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    change |fderiv ℝ _ x (unitVector k)| ≤ _
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ _ x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (by
        simpa only [NNReal.coe_sum] using
          (norm_fderiv_le_of_lipschitz ℝ (hflux k) (x₀ := x))) (norm_nonneg _))
  unfold reducedGenerator
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg lam)
    unfold dot
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have he : (reducedCoefficient ω x).mulVec (unitVector i) k = reducedCoefficient ω x k i := by
      simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
    rw [he, abs_mul]
    exact mul_le_mul (abs_reducedCoefficient_le hΛ hω x k i) (hG x k) (abs_nonneg _) (by positivity)

/-- One field-dependent constant controls the physical generator in terms of
uniform bounds for the gradient and its Lipschitz constant. -/
theorem c4_physical_generator_quantitative {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Vec d → ℝ) (G : ℝ) (H : ℝ≥0),
      0 ≤ G → (∀ y j, |coordinateDerivative j f y| ≤ G) →
      (∀ j, LipschitzWith H (fun y => coordinateDerivative j f y)) →
      ∀ x, |physicalGenerator i ω lam f x| ≤ C * (G + H) := by
  let A := Real.exp (2 * Λ₀) * Λ₀
  let K := Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d
  let D : ℝ := d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C := Real.exp (2 * Λ₀) * ((1 / 2 : ℝ) * D * D * (A + K) + |lam| * D * A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f G H hG0 hG hH x
  have hb := c4_reduced_generator_quantitative hΛ hω i lam f G H hG hH x
  have hh : 0 ≤ (H : ℝ) := H.coe_nonneg
  have hAK : 0 ≤ A * (H : ℝ) + G * K := by positivity
  change |reducedGenerator i ω lam f x| ≤
    (1 / 2 : ℝ) * (∑ k : Fin d, (∑ _j : Fin d,
      (Real.toNNReal (|A| * (H : ℝ) + |G| * (Real.toNNReal K : ℝ)) : ℝ)) *
      ‖unitVector k‖) + |lam| * (∑ _k : Fin d, A * G) at hb
  simp only [abs_of_nonneg hA, abs_of_nonneg hG0, Real.coe_toNNReal K hK,
    Real.coe_toNNReal _ hAK, unitVector, Pi.norm_single, norm_one, le_refl,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one] at hb
  have hb' : |reducedGenerator i ω lam f x| ≤
      ((1 / 2 : ℝ) * D * D * (A + K) + |lam| * D * A) * (G + H) := by
    dsimp [D] at *
    nlinarith [mul_nonneg hA hG0, mul_nonneg hK hh,
      mul_nonneg (mul_nonneg hD hD) (add_nonneg (mul_nonneg hA hG0) (mul_nonneg hK hh)),
      mul_nonneg (mul_nonneg (abs_nonneg lam) hD) (mul_nonneg hA hh)]
  rw [physicalGenerator_eq_inv_mul, abs_mul]
  have hinv : (clockDensity ω x)⁻¹ = Real.exp (2 * ω.2 x) := by
    rw [clockDensity, ← Real.exp_neg]
    congr 1
    ring
  have h1 : |(clockDensity ω x)⁻¹| ≤ Real.exp (2 * Λ₀) := by
    rw [hinv, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by have := (abs_le.1 (hω.2.1 x)).2; linarith)
  calc
    _ ≤ Real.exp (2 * Λ₀) * (((1 / 2 : ℝ) * D * D * (A + K) + |lam| * D * A) * (G + H)) :=
      mul_le_mul h1 hb' (abs_nonneg _) (Real.exp_pos _).le
    _ = C * (G + H) := by dsimp [C]; ring

/-- On an event where the relevant additivity identities hold, controlled
approximations converge under the literal physical generator. -/
theorem c4_physical_generator_tendsto_of_additive_approximation
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) (F : ℕ → Vec d → ℝ) (x : Vec d)
    (G : ℕ → ℝ) (H : ℕ → ℝ≥0)
    (hG0 : ∀ n, 0 ≤ G n)
    (hG : ∀ n y j, |coordinateDerivative j (fun z => f z - F n z) y| ≤ G n)
    (hH : ∀ n j, LipschitzWith (H n)
      (fun y => coordinateDerivative j (fun z => f z - F n z) y))
    (hGlim : Filter.Tendsto G Filter.atTop (𝓝 0))
    (hHlim : Filter.Tendsto (fun n => (H n : ℝ)) Filter.atTop (𝓝 0))
    (hadd : ∀ n, physicalGenerator i ω lam f x =
      physicalGenerator i ω lam (F n) x +
        physicalGenerator i ω lam (fun z => f z - F n z) x) :
    Filter.Tendsto (fun n => physicalGenerator i ω lam (F n) x)
      Filter.atTop (𝓝 (physicalGenerator i ω lam f x)) := by
  obtain ⟨C, hC, hbound⟩ := c4_physical_generator_quantitative hΛ hω i lam
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa only [add_zero, mul_zero] using
      (tendsto_const_nhds.mul (hGlim.add hHlim) :
        Filter.Tendsto (fun n => C * (G n + (H n : ℝ))) Filter.atTop (𝓝 (C * (0 + 0)))))
  rw [Real.norm_eq_abs]
  have he : physicalGenerator i ω lam (F n) x - physicalGenerator i ω lam f x =
      -physicalGenerator i ω lam (fun z => f z - F n z) x := by rw [hadd n]; ring
  rw [he, abs_neg]
  exact hbound _ _ _ (hG0 n) (hG n) (hH n) x

/-- The literal generator is bounded for compact smooth tests in a regular field,
including at the default values of derivatives. -/
theorem c4_bounded_physical_generator {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ x, |physicalGenerator i ω lam f x| ≤ C := by
  obtain ⟨C, hC⟩ := c4_bounded_reduced_generator hΛ hω i lam hf hc
  refine ⟨Real.exp (2 * Λ₀) * C, fun x => ?_⟩
  rw [physicalGenerator_eq_inv_mul, abs_mul]
  have hinv : (clockDensity ω x)⁻¹ = Real.exp (2 * ω.2 x) := by
    rw [clockDensity, ← Real.exp_neg]
    congr 1
    ring
  have h1 : |(clockDensity ω x)⁻¹| ≤ Real.exp (2 * Λ₀) := by
    rw [hinv, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by have := (abs_le.1 (hω.2.1 x)).2; linarith)
  exact mul_le_mul h1 (hC x) (abs_nonneg _) (Real.exp_pos _).le

/-- Additivity consistency for two fixed compact smooth tests under the same
supplied physical law. The test pair is chosen before the almost-everywhere event. -/
theorem c4_physical_additivity_defect_integral_eq_zero {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    {f g : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (t : ℝ≥0) :
    ∀ᵐ γ ∂P, (∫ u in (0 : ℝ)..(t : ℝ),
      (physicalGenerator i ω lam (fun y => f y + g y) (γ u.toNNReal) -
        physicalGenerator i ω lam f (γ u.toNNReal) -
          physicalGenerator i ω lam g (γ u.toNNReal))) = 0 := by
  obtain ⟨Cf, hLf⟩ := c4_bounded_physical_generator hΛ hω i lam hf hfc
  obtain ⟨Cg, hLg⟩ := c4_bounded_physical_generator hΛ hω i lam hg hgc
  obtain ⟨Cs, hLs⟩ := c4_bounded_physical_generator hΛ hω i lam
    (hf.add hg) (hfc.add hgc)
  exact c4_finite_test_additivity_defect_integral_eq_zero hP hf hfc hg hgc
    hLf hLg hLs t

/-- The additivity defect vanishes at almost every positive time along almost
every path, for a fixed pair of compact smooth tests. -/
theorem c4_physical_additivity_defect_ae_zero {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      physicalGenerator i ω lam (fun y => f y + g y) (γ u.toNNReal) =
        physicalGenerator i ω lam f (γ u.toNNReal) +
          physicalGenerator i ω lam g (γ u.toNNReal) := by
  obtain ⟨Cf, hLf⟩ := c4_bounded_physical_generator hΛ hω i lam hf hfc
  obtain ⟨Cg, hLg⟩ := c4_bounded_physical_generator hΛ hω i lam hg hgc
  obtain ⟨Cs, hLs⟩ := c4_bounded_physical_generator hΛ hω i lam
    (hf.add hg) (hfc.add hgc)
  let D : Vec d → ℝ := fun y =>
    physicalGenerator i ω lam (fun z => f z + g z) y -
      physicalGenerator i ω lam f y - physicalGenerator i ω lam g y
  have hDm : Measurable D :=
    ((c4_measurable_physical_generator ω i lam _).sub
      (c4_measurable_physical_generator ω i lam f)).sub
        (c4_measurable_physical_generator ω i lam g)
  have hDb : ∀ y, ‖D y‖ ≤ Cs + Cf + Cg := by
    intro y
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add
      ((abs_sub _ _).trans (add_le_add (hLs y) (hLf y))) (hLg y))
  have hq : ∀ᵐ γ ∂P, ∀ q : ℚ,
      (∫ u in (0 : ℝ)..(((q : ℝ).toNNReal : ℝ)), D (γ u.toNNReal)) = 0 := by
    apply ae_all_iff.mpr
    intro q
    simpa only [D] using c4_physical_additivity_defect_integral_eq_zero
      hΛ hω i lam hP hf hfc hg hgc ((q : ℝ).toNNReal)
  filter_upwards [hq] with γ hγ
  let F : ℝ → ℝ := fun u => D (γ u.toNNReal)
  have hFm : Measurable F := hDm.comp (γ.continuous.comp continuous_real_toNNReal).measurable
  have hFloc : LocallyIntegrable F volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    apply Measure.integrableOn_of_bounded hK.measure_lt_top.ne hFm.aestronglyMeasurable
    exact ae_of_all _ (fun u => hDb (γ u.toNNReal))
  have hFi : ∀ a b : ℝ, IntervalIntegrable F volume a b := by
    intro a b
    exact (hFloc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hcont : Continuous (fun t : ℝ => ∫ u in (0 : ℝ)..t, F u) :=
    intervalIntegral.continuous_primitive hFi 0
  have hall : ∀ t : ℝ, (∫ u in (0 : ℝ)..((t.toNNReal : ℝ)), F u) = 0 := by
    intro t
    refine Rat.denseRange_cast.induction_on t ?_ ?_
    · exact isClosed_eq (hcont.comp (NNReal.continuous_coe.comp continuous_real_toNNReal))
        continuous_const
    · intro q
      exact hγ q
  have hpos : ∀ t : ℝ, 0 < t → (∫ u in (0 : ℝ)..t, F u) = 0 := by
    intro t ht
    simpa [Real.coe_toNNReal _ ht.le] using hall t
  filter_upwards [ae_restrict_of_ae (LocallyIntegrable.ae_hasDerivAt_integral hFloc),
    ae_restrict_mem measurableSet_Ioi] with u hu hupos
  have hz : HasDerivAt (fun t : ℝ => ∫ v in (0 : ℝ)..t, F v) 0 u := by
    apply (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hupos] with t ht
    exact hpos t ht
  have hFu : F u = 0 := (hu 0).unique hz
  dsimp [F, D] at hFu
  linarith

/-- A fixed pair of tests has zero integrated additivity defect at every time
on one common event for the supplied physical law. -/
theorem c4_physical_additivity_defect_integral_all_times_eq_zero
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∀ᵐ γ ∂P, ∀ t : ℝ≥0, (∫ u in (0 : ℝ)..(t : ℝ),
      (physicalGenerator i ω lam (fun y => f y + g y) (γ u.toNNReal) -
        physicalGenerator i ω lam f (γ u.toNNReal) -
          physicalGenerator i ω lam g (γ u.toNNReal))) = 0 := by
  filter_upwards [c4_physical_additivity_defect_ae_zero hΛ hω i lam hP
    hf hfc hg hgc] with γ hγ
  intro t
  have ht : (Set.uIoc (0 : ℝ) (t : ℝ)) ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIoc_of_le t.coe_nonneg]
    exact fun _ hu => hu.1
  have hzero := ae_restrict_of_ae_restrict_of_subset ht hγ
  calc
    (∫ u in (0 : ℝ)..(t : ℝ),
      (physicalGenerator i ω lam (fun y => f y + g y) (γ u.toNNReal) -
        physicalGenerator i ω lam f (γ u.toNNReal) -
          physicalGenerator i ω lam g (γ u.toNNReal))) =
        ∫ _u in (0 : ℝ)..(t : ℝ), (0 : ℝ) := by
          apply intervalIntegral.integral_congr_ae_restrict
          filter_upwards [hzero] with u hu
          linarith
    _ = 0 := intervalIntegral.integral_zero

/-- Additivity holds on a common event for a prescribed countable family of tests. -/
theorem c4_physical_additivity_defect_countable_ae_zero
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F G : ℕ → Vec d → ℝ)
    (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n))
    (hcF : ∀ n, HasCompactSupport (F n))
    (hG : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (G n))
    (hcG : ∀ n, HasCompactSupport (G n)) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ n : ℕ,
      physicalGenerator i ω lam (fun y => F n y + G n y) (γ u.toNNReal) =
        physicalGenerator i ω lam (F n) (γ u.toNNReal) +
          physicalGenerator i ω lam (G n) (γ u.toNNReal) := by
  have h : ∀ᵐ γ ∂P, ∀ n : ℕ,
      ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
        physicalGenerator i ω lam (fun y => F n y + G n y) (γ u.toNNReal) =
          physicalGenerator i ω lam (F n) (γ u.toNNReal) +
            physicalGenerator i ω lam (G n) (γ u.toNNReal) := by
    apply ae_all_iff.mpr
    intro n
    exact c4_physical_additivity_defect_ae_zero hΛ hω i lam hP
      (hF n) (hcF n) (hG n) (hcG n)
  filter_upwards [h] with γ hγ
  exact ae_all_iff.mpr hγ

/-- Every controlled prescribed approximation converges under the literal
physical generator along the supplied martingale-problem law. -/
theorem c4_physical_generator_approximation_ae
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)} (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (F : ℕ → Vec d → ℝ) (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n))
    (hcF : ∀ n, HasCompactSupport (F n)) (G : ℕ → ℝ) (H : ℕ → ℝ≥0)
    (hG0 : ∀ n, 0 ≤ G n)
    (hG : ∀ n y j, |coordinateDerivative j (fun z => f z - F n z) y| ≤ G n)
    (hH : ∀ n j, LipschitzWith (H n)
      (fun y => coordinateDerivative j (fun z => f z - F n z) y))
    (hGlim : Filter.Tendsto G Filter.atTop (𝓝 0))
    (hHlim : Filter.Tendsto (fun n => (H n : ℝ)) Filter.atTop (𝓝 0)) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Filter.Tendsto (fun n => physicalGenerator i ω lam (F n) (γ u.toNNReal))
        Filter.atTop (𝓝 (physicalGenerator i ω lam f (γ u.toNNReal))) := by
  have hevent := c4_physical_additivity_defect_countable_ae_zero hΛ hω i lam hP
    F (fun n z => f z - F n z) hF hcF
    (fun n => hf.sub (hF n)) (fun n => hfc.sub (hcF n))
  filter_upwards [hevent] with γ hγ
  filter_upwards [hγ] with u hu
  apply c4_physical_generator_tendsto_of_additive_approximation hΛ hω i lam f F
    (γ u.toNNReal) G H hG0 hG hH hGlim hHlim
  intro n
  have he : (fun y => F n y + (f y - F n y)) = f := by
    funext y
    ring
  simpa only [he] using (hu n)

/-- On the common countable additivity event, a critical test does not change
the discrepancy between the physical and textbook operators. -/
theorem c4_physical_countable_critical_discrepancy_ae
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F G : ℕ → Vec d → ℝ)
    (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n))
    (hcF : ∀ n, HasCompactSupport (F n))
    (hG : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (G n))
    (hcG : ∀ n, HasCompactSupport (G n)) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ n : ℕ,
      gradient (F n) (γ u.toNNReal) = 0 →
      physicalGenerator i ω lam (fun y => F n y + G n y) (γ u.toNNReal) -
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
            (fun y => F n y + G n y) (γ u.toNNReal) =
        physicalGenerator i ω lam (G n) (γ u.toNNReal) -
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
            (G n) (γ u.toNNReal) := by
  filter_upwards [c4_physical_additivity_defect_countable_ae_zero
    hΛ hω i lam hP F G hF hcF hG hcG] with γ hγ
  filter_upwards [hγ] with u hu
  intro n hcrit
  exact c4_physical_generator_discrepancy_of_add_and_critical ω i lam
    (contDiff_two_of_top (hF n)) (contDiff_two_of_top (hG n)) _ hcrit (hu n)

/-- On one event for a prescribed countable family, tests with the same
gradient have the same physical-versus-textbook generator discrepancy. -/
theorem c4_physical_countable_same_gradient_discrepancy_ae
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F G : ℕ → Vec d → ℝ)
    (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n))
    (hcF : ∀ n, HasCompactSupport (F n))
    (hG : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (G n))
    (hcG : ∀ n, HasCompactSupport (G n)) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ n : ℕ,
      gradient (F n) (γ u.toNNReal) = gradient (G n) (γ u.toNNReal) →
      physicalGenerator i ω lam (F n) (γ u.toNNReal) -
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
            (F n) (γ u.toNNReal) =
        physicalGenerator i ω lam (G n) (γ u.toNNReal) -
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
            (G n) (γ u.toNNReal) := by
  let H : ℕ → Vec d → ℝ := fun n y => F n y - G n y
  have hH : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (H n) := fun n => (hF n).sub (hG n)
  have hcH : ∀ n, HasCompactSupport (H n) := fun n => (hcF n).sub (hcG n)
  filter_upwards [c4_physical_countable_critical_discrepancy_ae
    hΛ hω i lam hP H G hH hcH hG hcG] with γ hγ
  filter_upwards [hγ] with u hu
  intro n hgrad
  have hz : gradient (H n) (γ u.toNNReal) = 0 := by
    funext j
    change fderiv ℝ (fun y => F n y - G n y) (γ u.toNNReal) (unitVector j) = 0
    rw [fderiv_fun_sub ((hF n).differentiable (by simp) _)
      ((hG n).differentiable (by simp) _)]
    apply sub_eq_zero.mpr
    simpa [gradient, coordinateDerivative] using congrFun hgrad j
  have he : (fun y => H n y + G n y) = F n := by
    funext y
    dsimp [H]
    ring
  simpa only [he] using hu n hz

/-- The countable same-gradient event transfers the pointwise coordinate
comparison to every test in the prescribed family at matching points. -/
theorem c4_physical_countable_match_coordinate_ae
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F G : ℕ → Vec d → ℝ)
    (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n))
    (hcF : ∀ n, HasCompactSupport (F n))
    (hG : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (G n))
    (hcG : ∀ n, HasCompactSupport (G n)) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ n : ℕ,
      ∀ j : Fin d,
      (G n =ᶠ[𝓝 (γ u.toNNReal)] fun z => z j) →
      gradient (F n) (γ u.toNNReal) = gradient (G n) (γ u.toNNReal) →
      physicalGenerator i ω lam (F n) (γ u.toNNReal) =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
          (F n) (γ u.toNNReal) := by
  filter_upwards [c4_physical_countable_same_gradient_discrepancy_ae
    hΛ hω i lam hP F G hF hcF hG hcG] with γ hγ
  filter_upwards [hγ] with u hu
  intro n j hlocal hgrad
  have h := hu n hgrad
  rw [c4_physical_generator_local_coordinate_eq_textbook ω i j lam hlocal,
    sub_self] at h
  exact sub_eq_zero.mp h

/-- Finite sums of scaled coordinate cutoffs have their textbook value on
one event wherever the cutoffs agree locally with the scaled coordinates. -/
theorem c4_physical_finite_coordinate_sum_ae
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)} (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F : Fin d → Vec d → ℝ) (c : Fin d → ℝ) (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (F j))
    (hcF : ∀ j, HasCompactSupport (F j)) (s : Finset (Fin d)) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      (∀ j ∈ s, F j =ᶠ[𝓝 (γ u.toNNReal)] fun z => c j * z j) →
      physicalGenerator i ω lam (fun y => ∑ j ∈ s, F j y) (γ u.toNNReal) =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
          (fun y => ∑ j ∈ s, F j y) (γ u.toNNReal) := by
  classical
  have hscompact (t : Finset (Fin d)) : HasCompactSupport (fun y => ∑ k ∈ t, F k y) := by
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty, Pi.zero_def] using
        (HasCompactSupport.zero : HasCompactSupport (0 : Vec d → ℝ))
    | @insert k t hk iht =>
        simpa only [Finset.sum_insert hk, Pi.add_def] using (hcF k).add iht
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [] with γ
      filter_upwards [] with u
      intro _
      simp only [Finset.sum_empty]
      apply c4_physical_generator_eq_textbook_of_gradient_eq_zero ω i lam
        (contDiff_const : ContDiff ℝ 2 (fun _ : Vec d => (0 : ℝ)))
      funext k
      simp [gradient, coordinateDerivative]
  | @insert j s hj ih =>
      have hs : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ k ∈ s, F k y) :=
        ContDiff.sum fun k _ => hF k
      have hsc := hscompact s
      have hadd := c4_physical_additivity_defect_ae_zero hΛ hω i lam hP
        (hF j) (hcF j) hs hsc
      filter_upwards [ih, hadd] with γ hγ haddγ
      filter_upwards [hγ, haddγ] with u hu haddu
      intro hloc
      have hjloc := hloc j (Finset.mem_insert_self j s)
      have hsloc : ∀ k ∈ s, F k =ᶠ[𝓝 (γ u.toNNReal)] fun z => c k * z k := by
        intro k hk
        exact hloc k (Finset.mem_insert_of_mem hk)
      have he : (fun y => ∑ k ∈ insert j s, F k y) =
          (fun y => F j y + ∑ k ∈ s, F k y) := by
        funext y
        simp [Finset.sum_insert hj]
      have hjcomp : physicalGenerator i ω lam (F j) (γ u.toNNReal) =
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
            (F j) (γ u.toNNReal) := by
        obtain ⟨hp, ht⟩ := c4_generator_eq_of_eventuallyEq ω i lam hjloc
        rw [hp, ht, c4_physical_generator_const_mul, c4_svGenerator_const_mul,
          c4_physical_generator_coordinate_eq_textbook]
      rw [he, haddu, c4_svGenerator_add _ _ (contDiff_two_of_top (hF j))
        (contDiff_two_of_top hs), hjcomp, hu hsloc]

/-- A prescribed countable family of finite affine coordinate sums has a
common comparison event under the supplied law. -/
theorem c4_physical_countable_coordinate_sum_ae
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)} (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F : ℕ → Fin d → Vec d → ℝ) (c : ℕ → Fin d → ℝ)
    (hF : ∀ n j, ContDiff ℝ (⊤ : ℕ∞) (F n j))
    (hcF : ∀ n j, HasCompactSupport (F n j)) (s : ℕ → Finset (Fin d)) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ n : ℕ,
      (∀ j ∈ s n, F n j =ᶠ[𝓝 (γ u.toNNReal)] fun z => c n j * z j) →
      physicalGenerator i ω lam (fun y => ∑ j ∈ s n, F n j y) (γ u.toNNReal) =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
          (fun y => ∑ j ∈ s n, F n j y) (γ u.toNNReal) := by
  have he : ∀ᵐ γ ∂P, ∀ n : ℕ, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      (∀ j ∈ s n, F n j =ᶠ[𝓝 (γ u.toNNReal)] fun z => c n j * z j) →
      physicalGenerator i ω lam (fun y => ∑ j ∈ s n, F n j y) (γ u.toNNReal) =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
          (fun y => ∑ j ∈ s n, F n j y) (γ u.toNNReal) := by
    apply ae_all_iff.mpr
    intro n
    exact c4_physical_finite_coordinate_sum_ae hΛ hω i lam hP
      (F n) (c n) (hF n) (hcF n) (s n)
  filter_upwards [he] with γ hγ
  exact ae_all_iff.mpr hγ

/-- Every pair in a prescribed countable family has zero integrated defect at
all times on a common event for the supplied physical law. -/
theorem c4_physical_countable_additivity_defect_integral_all_times_eq_zero
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F G : ℕ → Vec d → ℝ)
    (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n))
    (hcF : ∀ n, HasCompactSupport (F n))
    (hG : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (G n))
    (hcG : ∀ n, HasCompactSupport (G n)) :
    ∀ᵐ γ ∂P, ∀ n : ℕ, ∀ t : ℝ≥0, (∫ u in (0 : ℝ)..(t : ℝ),
      (physicalGenerator i ω lam (fun y => F n y + G n y) (γ u.toNNReal) -
        physicalGenerator i ω lam (F n) (γ u.toNNReal) -
          physicalGenerator i ω lam (G n) (γ u.toNNReal))) = 0 := by
  apply ae_all_iff.mpr
  intro n
  exact c4_physical_additivity_defect_integral_all_times_eq_zero
    hΛ hω i lam hP (hF n) (hcF n) (hG n) (hcG n)


/-- A two-dimensional diagonal field with a Cantor-set trap in its first coordinate. -/
noncomputable def c4DiagonalCantorTrapField : FieldPair 2 :=
  (⟨fun x j k => if j = k then
      (if j = 0 then c4CantorTrapCoefficient (x 0) else 1) else 0,
    continuous_pi fun j => continuous_pi fun k => by
      by_cases h : j = k
      · subst k
        by_cases hj : j = 0
        · simpa [hj, Function.comp_def] using
            c4_cantorTrapCoefficient_lipschitz.continuous.comp
              (continuous_apply (0 : Fin 2) : Continuous (fun x : Vec 2 => x 0))
        · simpa [hj] using
            (continuous_const : Continuous (fun _ : Vec 2 => (1 : ℝ)))
      · simpa only [if_neg h] using
          (continuous_const : Continuous (fun _ : Vec 2 => (0 : ℝ)))⟩,
    ⟨fun _ => 0, continuous_const⟩)

private theorem c4_two_coord_le (x : Vec 2) (i : Fin 2) :
    |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  have h := Finset.single_le_sum (f := fun j => x j * x j)
    (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
  exact (sq (x i)).le.trans h

/-- A regular two-dimensional diagonal coefficient field with zero potential. -/
theorem c4_diagonalCantorTrap_regular_environment :
    ∃ ω : FieldPair 2, IsRegular 2 ω ∧
      (∀ x : Vec 2, ω.2 x = 0) ∧
      ∀ (x : Vec 2) (j k : Fin 2),
        ω.1 x j k = if j = k then
          (if j = 0 then c4CantorTrapCoefficient (x 0) else 1) else 0 := by
  have hv (x : Vec 2) (j k : Fin 2) :
      c4DiagonalCantorTrapField.1 x j k = if j = k then
        (if j = 0 then c4CantorTrapCoefficient (x 0) else 1) else 0 := rfl
  refine ⟨c4DiagonalCantorTrapField, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      constructor
      · ext j k
        fin_cases j <;> fin_cases k <;> simp [Matrix.transpose_apply, hv]
      · intro ξ
        have hb := c4_cantorTrapCoefficient_bounds (x 0)
        have hlo := mul_nonneg (sub_nonneg.mpr hb.1) (sq_nonneg (ξ 0))
        have hhi := mul_nonneg (sub_nonneg.mpr hb.2) (sq_nonneg (ξ 0))
        simp [euclideanSq, dot, Matrix.mulVec, dotProduct, hv,
          Fin.sum_univ_two]
        constructor <;> nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1)]
    · intro x
      norm_num [c4DiagonalCantorTrapField]
    · intro x y ξ
      have hl := c4_cantorTrapCoefficient_lipschitz.norm_sub_le (x 0) (y 0)
      simp only [Real.norm_eq_abs, NNReal.coe_one, one_mul] at hl
      have hx := c4_two_coord_le (x - y) 0
      have hξ := c4_two_coord_le ξ 0
      have hm := mul_le_mul hl hξ (abs_nonneg _) (abs_nonneg _)
      have hxy : |x 0 - y 0| ≤ euclideanNorm (x - y) := by simpa using hx
      have hm' := hm.trans (mul_le_mul_of_nonneg_right hxy (Real.sqrt_nonneg _))
      have he : euclideanNorm ((c4DiagonalCantorTrapField.1 x -
          c4DiagonalCantorTrapField.1 y).mulVec ξ) =
          |c4CantorTrapCoefficient (x 0) - c4CantorTrapCoefficient (y 0)| * |ξ 0| := by
        simp [euclideanNorm, euclideanSq, dot, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two, hv, ← pow_two, Real.sqrt_sq_eq_abs, abs_mul]
      rw [he]
      have hn : 0 ≤ euclideanNorm (x - y) * euclideanNorm ξ :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      nlinarith
    · intro x y
      change |(0 : ℝ) - 0| ≤ 2 * euclideanNorm (x - y)
      rw [sub_self, abs_zero]
      exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · intro x; rfl
  · intro x j k; rfl

/-- The left endpoint of the trap is a cusp of the actual coefficient. -/
theorem c4_cantorTrapCoefficient_not_differentiableAt_left :
    ¬ DifferentiableAt ℝ c4CantorTrapCoefficient (5 / 4 : ℝ) := by
  have hmem : (5 / 4 : ℝ) ∈ c4CantorTrapSet := by
    exact ⟨0, zero_mem_cantorSet, by norm_num⟩
  have hbase : c4CantorTrapCoefficient (5 / 4 : ℝ) = 1 :=
    c4_cantorTrapCoefficient_of_mem hmem
  have hmin : IsLocalMin c4CantorTrapCoefficient (5 / 4 : ℝ) := by
    filter_upwards with z
    rw [hbase]
    exact (c4_cantorTrapCoefficient_bounds z).1
  have heq : c4CantorTrapCoefficient =ᶠ[𝓝[Set.Iio (5 / 4 : ℝ)] (5 / 4 : ℝ)]
      (fun z => 1 + (5 / 4 - z)) := by
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [eventually_gt_nhds (show (1 / 4 : ℝ) < 5 / 4 by norm_num)] with z hz hleft
    change z < 5 / 4 at hleft
    have hd : Metric.infDist z c4CantorTrapSet = 5 / 4 - z := by
      apply le_antisymm
      · have h := Metric.infDist_le_dist_of_mem (x := z) hmem
        rw [Real.dist_eq, abs_of_nonpos (by linarith : z - 5 / 4 ≤ 0)] at h
        linarith
      · apply (Metric.le_infDist c4_cantorTrapSet_geometry.1).2
        intro y hy
        have hy' := c4_cantorTrapSet_geometry.2.2 hy
        change z < 5 / 4 at hleft
        change 5 / 4 ≤ y ∧ y ≤ 7 / 4 at hy'
        rw [Real.dist_eq, abs_of_nonpos (by linarith : z - y ≤ 0)]
        linarith [hy'.1]
    simp only [c4CantorTrapCoefficient, hd, min_eq_left (by linarith : 5 / 4 - z ≤ 1)]
  intro hdiff
  have hzero : deriv c4CantorTrapCoefficient (5 / 4 : ℝ) = 0 := hmin.deriv_eq_zero
  have hwithin := heq.derivWithin_eq (by simp [hbase])
  rw [hdiff.derivWithin (uniqueDiffWithinAt_Iio _)] at hwithin
  have ha : HasDerivAt (fun z : ℝ => 1 + (5 / 4 - z)) (-1) (5 / 4) := by
    convert (hasDerivAt_const (5 / 4 : ℝ) (1 : ℝ)).add
      ((hasDerivAt_const (5 / 4 : ℝ) (5 / 4 : ℝ)).sub (hasDerivAt_id (5 / 4 : ℝ))) using 1
    · funext z; rfl
    · norm_num
  rw [ha.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio _)] at hwithin
  linarith

/-- Uniqueness of supplied physical laws under the paper's smoothness assumption. -/
theorem c4_physical_mp_ae_unique_of_smooth_bounds {d : ℕ}
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d) (lam : ℝ)
    (PX PX' : QuenchedPathLaws d)
    (hX : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω)))
    (hX' : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω))) :
    ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω) := by
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one D.one_le_ellipticity
  filter_upwards [Q.regular, hQ, hX, hX'] with ω hreg hs hXω hX'ω
  obtain ⟨P, _, huniq⟩ := exists_unique_physical_solution
    foundation_textbook_well_posed hΛ hreg hs.1 i lam 0
  exact (huniq _ hXω).trans (huniq _ hX'ω).symm

/-- Existence and literal inverse-clock uniqueness under the paper's smoothness assumption. -/
theorem c4_pathwise_of_smooth_bounds {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d) (lam : ℝ) :
    (∃ PX PY : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) ∧
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω)))) ∧
    ∀ PX PY : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) →
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω))) →
      ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular D.ellipticity ω,
        PX (0, ω) = Measure.map
          (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ D.ellipticity hω)
          (PY (0, ω)) ∧
        ∀ᵐ γ ∂PY (0, ω), ∀ t : ℝ≥0,
          Clock.InverseMeaningV3.inverseClockPath ω γ D.ellipticity hω
            (Clock.physicalPathClock ω γ t) = γ t := by
  have hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω := by
    filter_upwards [hQ] with ω hω
    exact hω.1
  refine ⟨?_, ?_⟩
  · obtain ⟨PX, PY, hX, hY, _⟩ :=
      c16_physical_reduced_mp_exists_with_inverse_clock d hd D.ellipticity
        D.dependenceRange Q i lam
    exact ⟨PX, PY, hX, hY⟩
  · intro PX PY hX hY
    exact pathwiseV2_uniqueness_part foundation_textbook_well_posed D Q hsm i lam PX PY hX hY

/-- The supplied smooth physical law is the inverse-clock image of a textbook
reduced law with absolutely continuous averaged occupation, from the same start. -/
theorem c4_physical_eq_inverse_clock_textbook_of_smooth
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (hSmooth : IsSmoothFieldPair ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P) :
    ∃ PY : Measure (Path d),
      SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x PY ∧
      Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
        (PY.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) ∧
      P = Measure.map (Clock.InverseMeaningV3.inverseClockPath ω · Λ₀ hω) PY := by
  obtain ⟨PY, hPY, _⟩ := foundation_reduced_textbook_well_posed
    (by omega) hΛ hω i lam x
  have hocc := foundation_reduced_textbook_averaged_occupation_ac_of_two_le
    hd hΛ hω i lam hPY
  have hred := c16_reduced_solves_of_textbook_and_averaged_occupation
    hΛ hω i lam hPY hocc
  have hphysical := c16_time_change_solves_of_regular hΛ hω i lam x hred
  obtain ⟨P₀, _, huniq⟩ := exists_unique_physical_solution
    foundation_textbook_well_posed hΛ hω hSmooth i lam x
  exact ⟨PY, hPY, hocc, (huniq P hP).trans (huniq _ hphysical).symm⟩

/-- The physical clock maps Lebesgue-null sets of nonnegative times to null sets. -/
theorem c4_physical_clock_image_null {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (N : Set ℝ) (hN : (volume : Measure ℝ) N = 0) :
    (volume : Measure ℝ)
      ((fun t : ℝ => (Clock.physicalPathClock ω γ t.toNNReal : ℝ)) ''
        (N ∩ Set.Ici 0)) = 0 := by
  let f : ℝ → ℝ := fun t => clockDensity ω (γ t.toNNReal)
  let F : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, f u
  have hf : Continuous f :=
    (reduce ω).2.continuous.comp (γ.continuous.comp continuous_real_toNNReal)
  have hF : Differentiable ℝ F := fun t =>
    (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.differentiableAt
  have heq : Set.EqOn (fun t : ℝ => (Clock.physicalPathClock ω γ t.toNNReal : ℝ))
      F (N ∩ Set.Ici 0) := by
    intro t ht
    change (Clock.physicalPathClock ω γ t.toNNReal : ℝ) = F t
    rw [Clock.InverseMeaningV3.coe_physicalPathClock_explicit, Real.coe_toNNReal t ht.2]
    rfl
  rw [heq.image_eq]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    volume hF.differentiableOn (measure_mono_null Set.inter_subset_left hN)

/-- Inverse-clock transport preserves positive-time null occupation of a spatial set. -/
theorem c4_inverse_clock_path_null_occupation {d : ℕ} {Λ₀ : ℝ}
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (γ : Path d)
    {N : Set (Vec d)} (hN : MeasurableSet N)
    (hγ : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), γ t.toNNReal ∉ N) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω t.toNNReal ∉ N := by
  let A : Set ℝ := {t | γ t.toNNReal ∈ N} ∩ Set.Ioi 0
  have hA : (volume : Measure ℝ) A = 0 := by
    have hzero : volume.restrict (Set.Ioi (0 : ℝ)) {t | γ t.toNNReal ∈ N} = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr hγ
    have hm : MeasurableSet {t : ℝ | γ t.toNNReal ∈ N} :=
      (γ.continuous.comp continuous_real_toNNReal).measurable hN
    rw [Measure.restrict_apply hm] at hzero
    exact hzero
  have himage := c4_physical_clock_image_null ω γ A hA
  apply measure_eq_zero_iff_ae_notMem.mp
  have hm : MeasurableSet {t : ℝ |
      Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω t.toNNReal ∈ N} :=
    ((Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω).continuous.comp
      continuous_real_toNNReal).measurable hN
  change (volume.restrict (Set.Ioi (0 : ℝ)))
    {t : ℝ | Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω t.toNNReal ∈ N} = 0
  rw [Measure.restrict_apply hm]
  apply measure_mono_null _ himage
  intro t ht
  have htpos : 0 < t := ht.2
  let s := Clock.InverseMeaningV3.inversePhysicalPathClock ω γ Λ₀ hω t.toNNReal
  have hspos : 0 < (s : ℝ) := by
    have hb := (Clock.InverseMeaningV3.inversePhysicalPathClock_bounds ω γ Λ₀ hω t.toNNReal).1
    have ht' : 0 < (t.toNNReal : ℝ) := by simpa [Real.coe_toNNReal t htpos.le] using htpos
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) ht') hb
  refine ⟨(s : ℝ), ⟨?_, hspos.le⟩, ?_⟩
  · refine ⟨?_, hspos⟩
    simpa [s, Clock.InverseMeaningV3.inverseClockPath] using ht.1
  · simp only [Real.toNNReal_coe]
    change (Clock.physicalPathClock ω γ
      (Clock.InverseMeaningV3.inversePhysicalPathClock ω γ Λ₀ hω t.toNNReal) : ℝ) = t
    rw [Clock.InverseMeaningV3.physicalPathClock_inversePhysicalPathClock,
      Real.coe_toNNReal t htpos.le]

/-- The supplied physical law has absolutely continuous averaged occupation in a
smooth regular environment. -/
theorem c4_physical_averaged_occupation_ac_of_smooth
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (hSmooth : IsSmoothFieldPair ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  obtain ⟨PY, hPY, hocc, heq⟩ :=
    c4_physical_eq_inverse_clock_textbook_of_smooth hd hΛ hω hSmooth i lam hP
  let _ : IsProbabilityMeasure PY := hPY.1
  let _ : IsProbabilityMeasure P := hP.1
  let Φ : Path d → Path d := fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω
  have hΦ : Measurable Φ := measurable_timeChangeMap hω
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  intro N hnull
  let M := toMeasurable (volume : Measure (Vec d)) N
  have hM : MeasurableSet M := measurableSet_toMeasurable _ _
  have hMnull : (volume : Measure (Vec d)) M = 0 := by
    simp [M, hnull]
  have hpaths := c16_ae_path_of_averaged_occupation PY hocc
    (measure_eq_zero_iff_ae_notMem.mp hMnull)
  have htransport : ∀ᵐ γ ∂PY, ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Φ γ t.toNNReal ∉ M := by
    filter_upwards [hpaths] with γ hγ
    exact c4_inverse_clock_path_null_occupation hω γ hM hγ
  let B : Set (Path d × ℝ) := {z | z.1 z.2.toNNReal ∈ M}
  have hB : MeasurableSet B := hM.preimage heval
  have hsection : Measurable (fun γ : Path d =>
      (volume.restrict (Set.Ioi (0 : ℝ))) {t | γ t.toNNReal ∈ M}) :=
    measurable_measure_prodMk_left hB
  have hprop : MeasurableSet {γ : Path d |
      (volume.restrict (Set.Ioi (0 : ℝ))) {t | γ t.toNNReal ∈ M} = 0} :=
    measurableSet_eq_fun hsection measurable_const
  have hmap : ∀ᵐ γ ∂P, ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      γ t.toNNReal ∉ M := by
    rw [heq]
    have h := (ae_map_iff hΦ.aemeasurable hprop).2
      (htransport.mono fun γ hγ => measure_eq_zero_iff_ae_notMem.mpr hγ)
    exact h.mono fun γ hγ => measure_eq_zero_iff_ae_notMem.mp hγ
  have hprod : ∀ᵐ z ∂P.prod (volume.restrict (Set.Ioi (0 : ℝ))),
      z.1 z.2.toNNReal ∉ M :=
    (Measure.ae_prod_iff_ae_ae hB.compl).2 hmap
  apply measure_mono_null (subset_toMeasurable (volume : Measure (Vec d)) N)
  rw [Measure.map_apply heval hM]
  exact measure_eq_zero_iff_ae_notMem.mpr hprod

/-- Under smooth bounds, each supplied physical law has null occupation of
every measurable spatial null set, on one almost-sure environment event. -/
theorem c4_physical_supplied_law_null_occupation_of_smooth_bounds
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d) (lam : ℝ) (PX : QuenchedPathLaws d)
    (hX : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) :
    ∀ᵐ ω ∂Q.measure, ∀ N : Set (Vec d), MeasurableSet N →
      (volume : Measure (Vec d)) N = 0 →
      ∀ᵐ γ ∂PX (0, ω), ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), γ t.toNNReal ∉ N := by
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one D.one_le_ellipticity
  filter_upwards [Q.regular, hQ, hX] with ω hω hs hP
  have hocc := c4_physical_averaged_occupation_ac_of_smooth hd hΛ hω hs.1 i lam hP
  intro N _ hnull
  exact c16_ae_path_of_averaged_occupation _ hocc
    (measure_eq_zero_iff_ae_notMem.mp hnull)

/-- The actual finite-dimensional realization has the physical Dynkin martingale. -/
theorem c4_gmpPhysical_realization_compact_martingale
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (K : ProbabilityTheory.Kernel (Vec d) (Path d)) [ProbabilityTheory.IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) I)
    (x : Vec d) (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) :
    Martingale (fun (t : ℝ≥0) (γ : Path d) => f (γ t) - ∫ u in (0 : ℝ)..(t : ℝ),
      physicalGenerator (firstCoordinateIndex hd) ω lam f (γ u.toNNReal))
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) (K x) := by
  let F := Blueprint.gmpPhysicalC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω hSmooth
  have hsem : F.c0Semigroup = Blueprint.gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth :=
    Blueprint.gmpPhysicalC0KernelSemigroup_c0Semigroup hd ω lam Λ hΛ hω hSmooth
  let u := Blueprint.gmpPhysicalCompactC0 f hf.continuous hc
  have hu : u ∈ F.c0Semigroup.generatorDomain := by
    rw [hsem]
    exact Blueprint.gmpPhysicalC0Semigroup_compactTest_mem_generatorDomain
      hd ω lam Λ hΛ hω hSmooth f hf hc
  have hg : F.c0Semigroup.generator ⟨u, hu⟩ =
      Blueprint.gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam f)
        (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hf).continuous
        (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hc) := by
    generalize hS : F.c0Semigroup = S at hu hsem ⊢
    clear hS
    subst S
    exact Blueprint.gmpPhysicalC0Semigroup_generator_compactTest
      hd ω lam Λ hΛ hω hSmooth f hf hc
  have h := SubdiffusiveProcess.Section10.martingale_dynkinProcess_realization
    (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth)
    (Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth)
    F K hfdd ⟨u, hu⟩ x
  change Martingale (fun (t : ℝ≥0) (γ : Path d) => u (γ t) - ∫ s in (0 : ℝ)..(t : ℝ),
    (F.c0Semigroup.generator ⟨u, hu⟩) (γ s.toNNReal)) _ _ at h
  rw [hg] at h
  exact h

/-- The finite-dimensional realization starts at the specified point. -/
theorem c4_gmpPhysical_realization_ae_initial
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (K : ProbabilityTheory.Kernel (Vec d) (Path d))
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) I)
    (x : Vec d) : ∀ᵐ γ ∂K x, γ 0 = x := by
  let P := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  have hmarg : (K x).map (fun γ : Path d => γ 0) = Measure.dirac x := by
    have h := SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation P (K x) x 0 (by
      have h := congrArg (fun k => k x) (hfdd {0})
      simpa only [ProbabilityTheory.Kernel.map_apply _
        (MarkovProcess.ContinuousPath.measurable_finsetEvaluation _)] using h)
    simpa only [P, MarkovProcess.SubMarkovKernelSemigroup.kernel_zero,
      ProbabilityTheory.Kernel.id_apply] using h
  have hmeas : Measurable (fun γ : Path d => γ 0) := measurable_pathPosition 0
  apply (ae_map_iff hmeas.aemeasurable (measurableSet_singleton x)).mp
  rw [hmarg]
  rw [ae_dirac_eq]
  exact Filter.mem_pure.mpr rfl

/-- Both filtrations are generated by the path coordinates. -/
theorem c4_pathFiltration_eq_canonical (d : ℕ) :
    pathFiltration d = MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) := by
  apply Filtration.ext
  funext t
  change (⨆ s ≤ t, MeasurableSpace.comap (fun γ : Path d => γ s) inferInstance) =
    ⨆ s : Set.Iic t, MeasurableSpace.comap (fun γ : Path d => γ s) inferInstance
  rw [iSup_subtype']
  rfl

/-- The actual smooth physical realization solves the physical martingale problem. -/
theorem c4_gmpPhysical_realization_solves_martingale_problem
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (K : ProbabilityTheory.Kernel (Vec d) (Path d)) [ProbabilityTheory.IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) I)
    (x : Vec d) :
    SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x (K x) := by
  refine ⟨inferInstance, c4_gmpPhysical_realization_ae_initial hd ω lam Λ hΛ hω hSmooth K hfdd x, ?_⟩
  intro f hf hc
  have hcont : Continuous (physicalGenerator (firstCoordinateIndex hd) ω lam f) :=
    (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hf).continuous
  have hM := c4_gmpPhysical_realization_compact_martingale hd ω lam Λ hΛ hω hSmooth K hfdd x f hf hc
  rw [← c4_pathFiltration_eq_canonical d] at hM
  have hM0 := martingale_const_fun (pathFiltration d) (K x)
    (hM.stronglyAdapted 0) (hM.integrable 0)
  have hcomp : Martingale (compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f)
      (pathFiltration d) (K x) := by
    convert hM.sub hM0 using 1
    funext t γ
    simp only [compensatedTest, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero, Pi.sub_apply]
    ring
  refine ⟨?_, fun t => hcomp.integrable t, hcomp⟩
  intro t
  exact Filter.Eventually.of_forall fun γ =>
    (hcont.comp (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable _ _

/-- Every supplied smooth physical law equals the actual finite-dimensional realization. -/
theorem c4_physical_supplied_law_eq_gmp_realization_of_smooth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (K : ProbabilityTheory.Kernel (Vec d) (Path d)) [ProbabilityTheory.IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) I)
    (x : Vec d) (P : Measure (Path d))
    (hP : SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x P) :
    P = K x := by
  obtain ⟨Q, _, huniq⟩ := exists_unique_physical_solution
    foundation_textbook_well_posed (lt_of_lt_of_le zero_lt_one hΛ) hω hSmooth
      (firstCoordinateIndex hd) lam x
  exact (huniq _ hP).trans (huniq _
    (c4_gmpPhysical_realization_solves_martingale_problem hd ω lam Λ hΛ hω hSmooth K hfdd x)).symm

/-- The one-time marginals of a supplied smooth physical law are the GMP kernels. -/
theorem c4_physical_supplied_law_marginal_eq_gmp_kernel_of_smooth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (K : ProbabilityTheory.Kernel (Vec d) (Path d)) [ProbabilityTheory.IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) I)
    (x : Vec d) (P : Measure (Path d))
    (hP : SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x P)
    (t : ℝ≥0) :
    P.map (fun γ : Path d => γ t) =
      Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x := by
  rw [c4_physical_supplied_law_eq_gmp_realization_of_smooth
    hd ω lam Λ hΛ hω hSmooth K hfdd x P hP]
  exact SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation
    (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) (K x) x t (by
      have h := congrArg (fun k => k x) (hfdd {t})
      simpa only [ProbabilityTheory.Kernel.map_apply _
        (MarkovProcess.ContinuousPath.measurable_finsetEvaluation _)] using h)

/-- A supplied smooth physical law restarts at its current position. -/
theorem c4_physical_supplied_law_condExp_restart_of_smooth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (K : ProbabilityTheory.Kernel (Vec d) (Path d)) [ProbabilityTheory.IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) I)
    (x : Vec d) (P : Measure (Path d))
    (hP : SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x P)
    (s : ℝ≥0) (F : Path d → ℝ) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ γ, ‖F γ‖ ≤ C) :
    (P)[fun γ => F (MarkovProcess.ContinuousPath.shift s γ) | (pathFiltration d) s] =ᵐ[P]
      fun γ => ∫ η, F η ∂K (γ s) := by
  rw [c4_physical_supplied_law_eq_gmp_realization_of_smooth
    hd ω lam Λ hΛ hω hSmooth K hfdd x P hP, c4_pathFiltration_eq_canonical]
  exact SubdiffusiveProcess.Section10.condExp_shift_realization
    (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth)
    (Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth)
    (Blueprint.gmpPhysicalC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω hSmooth)
    K hfdd x s F hF C hFC


/-- The discounted occupation of a supplied smooth physical law is the GMP resolvent. -/
theorem c4_physical_supplied_law_laplace_eq_gmp_resolvent_of_smooth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (K : ProbabilityTheory.Kernel (Vec d) (Path d)) [ProbabilityTheory.IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) I)
    (x : Vec d) (P : Measure (Path d))
    (hP : SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x P)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) *
      (∫ γ : Path d, f (γ t.toNNReal) ∂P)) (Set.Ioi 0) ∧
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) *
      (∫ γ : Path d, f (γ t.toNNReal) ∂P)) =
      Blueprint.gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth s hs f x := by
  let S := Blueprint.gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun f => f x
        map_add' := by intro f g; rfl
        map_smul' := by intro c f; rfl } 1 (by
          intro f
          simpa using BoundedContinuousFunction.norm_coe_le_norm f.toBCF x)
  have hm (t : ℝ) : (∫ γ : Path d, f (γ t.toNNReal) ∂P) = S t.toNNReal f x := by
    change (∫ γ : Path d, f (pathPosition t.toNNReal γ) ∂P) = _
    have hmap := integral_map (μ := P) (measurable_pathPosition t.toNNReal).aemeasurable
      (f := fun y => f y) f.continuous.aestronglyMeasurable
    rw [← hmap]
    change (∫ y, f y ∂P.map (fun γ : Path d => γ t.toNNReal)) = _
    rw [c4_physical_supplied_law_marginal_eq_gmp_kernel_of_smooth
        hd ω lam Λ hΛ hω hSmooth K hfdd x P hP]
    exact Blueprint.gmpPhysicalC0KernelSemigroup_integral hd ω lam Λ hΛ hω hSmooth _ f x
  have hi := S.integrableOn_laplaceIntegrand hs f
  have hev : (fun t : ℝ => Real.exp (-s * t) *
      (∫ γ : Path d, f (γ t.toNNReal) ∂P)) =
      fun t => ev (S.laplaceIntegrand s f t) := by
    funext t
    simp [hm, MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, ev]
  rw [hev]
  refine ⟨ev.integrable_comp hi, ?_⟩
  calc
    _ = ev (∫ t in Set.Ioi 0, S.laplaceIntegrand s f t) := by
      simpa only [Function.comp_def] using (ev.integral_comp_comm hi)
    _ = ev (S.resolvent ⟨s, hs⟩ f) := by rw [S.resolvent_apply]
    _ = _ := by rw [show S.resolvent ⟨s, hs⟩ = _ from
      Blueprint.gmpPhysicalC0Semigroup_resolvent hd ω lam Λ hΛ hω hSmooth ⟨s, hs⟩]; rfl


/-- The smooth physical path occupation agrees almost everywhere with the physical L² resolvent. -/
theorem c4_gmpPhysical_path_occupation_resolvent_ae_of_smooth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (K : ProbabilityTheory.Kernel (Vec d) (Path d)) [ProbabilityTheory.IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) I)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (s : ℝ) (hs : 0 < s) :
    (fun x : Vec d => ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) *
      (∫ γ : Path d, f (γ t.toNNReal) ∂K x)) =ᵐ[physicalReversibleMeasure ω hd lam]
        Blueprint.gmpPhysicalResolvent hd ω lam Λ hΛ hω s hs F := by
  filter_upwards [Blueprint.gmpPhysicalC0Resolvent_ae_of_memLp
    hd ω lam Λ hΛ hω hSmooth s hs f F hae] with x hx
  exact (c4_physical_supplied_law_laplace_eq_gmp_resolvent_of_smooth
    hd ω lam Λ hΛ hω hSmooth K hfdd x (K x)
    (c4_gmpPhysical_realization_solves_martingale_problem
      hd ω lam Λ hΛ hω hSmooth K hfdd x) f s hs).2.trans hx

/-- A supplied smooth physical law restarts at every finite canonical stopping time. -/
theorem c4_physical_supplied_law_stopping_restart_of_smooth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (K : ProbabilityTheory.Kernel (Vec d) (Path d)) [ProbabilityTheory.IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) I)
    (x : Vec d) (P : Measure (Path d))
    (hP : SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x P)
    (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0))) :
    ∀ A : Set (Path d), MeasurableSet[hT.measurableSpace] A →
      (P.restrict A).map (fun γ => MarkovProcess.ContinuousPath.shift (T γ) γ) =
        ProbabilityTheory.Kernel.comap K (fun γ => γ (T γ))
          (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
            (P.restrict A) := by
  rw [c4_physical_supplied_law_eq_gmp_realization_of_smooth
    hd ω lam Λ hΛ hω hSmooth K hfdd x P hP]
  exact MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.realization_restrict_map_shift_stoppingTime
    (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth)
    (Blueprint.gmpPhysicalC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω hSmooth)
    (Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth)
    ⟨fun _ => 0, continuous_const⟩ K hfdd x T hT

/-- The discounted occupation of a supplied smooth physical law, started at a finite canonical
stopping time, is the GMP resolvent at the stopping position. -/
theorem c4_physical_supplied_law_stopped_laplace_of_smooth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (K : ProbabilityTheory.Kernel (Vec d) (Path d)) [ProbabilityTheory.IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) I)
    (x : Vec d) (P : Measure (Path d))
    (hP : SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x P)
    (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)))
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) (s : ℝ) (hs : 0 < s) :
    ∀ A : Set (Path d), MeasurableSet[hT.measurableSpace] A →
      (∫ γ in A, (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) *
        f (γ (T γ + t.toNNReal))) ∂P) =
      ∫ γ in A, Blueprint.gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth s hs f
        (γ (T γ)) ∂P := by
  intro A hA
  have hrestart := c4_physical_supplied_law_stopping_restart_of_smooth
    hd ω lam Λ hΛ hω hSmooth K hfdd x P hP T hT A hA
  have hPK := c4_physical_supplied_law_eq_gmp_realization_of_smooth
    hd ω lam Λ hΛ hω hSmooth K hfdd x P hP
  subst hPK
  let Φ : Path d → ℝ := fun η => ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * f (η t.toNNReal)
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hg : Measurable (fun z : Path d × ℝ => Real.exp (-s * z.2) * f (z.1 z.2.toNNReal)) :=
    (by fun_prop : Measurable fun z : Path d × ℝ => Real.exp (-s * z.2)).mul
      (f.continuous.measurable.comp heval)
  have hΦm : Measurable Φ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      hg.stronglyMeasurable).measurable
  have hfn (y : Vec d) : ‖f y‖ ≤ ‖f‖ := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF y
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-s * t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith : -s < 0) 0
  have hexp : IntegrableOn (fun t : ℝ => ‖f‖ * Real.exp (-s * t)) (Set.Ioi 0) := hE.const_mul ‖f‖
  have hbd (η : Path d) : ‖Φ η‖ ≤ ∫ t in Set.Ioi (0 : ℝ), ‖f‖ * Real.exp (-s * t) := by
    refine norm_integral_le_of_norm_le hexp (ae_of_all _ fun t => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hfn _) (Real.exp_nonneg _)
  have hΦi (μ : Measure (Path d)) [IsFiniteMeasure μ] : Integrable Φ μ :=
    Integrable.of_bound hΦm.aestronglyMeasurable _ (ae_of_all _ hbd)
  -- the occupation functional is the Laplace integral of the one-point laws
  have hswap (y : Vec d) :
      (∫ η, Φ η ∂K y) = Blueprint.gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth s hs f y := by
    rw [← (c4_physical_supplied_law_laplace_eq_gmp_resolvent_of_smooth
      hd ω lam Λ hΛ hω hSmooth K hfdd y (K y)
      (c4_gmpPhysical_realization_solves_martingale_problem
        hd ω lam Λ hΛ hω hSmooth K hfdd y) f s hs).2]
    have hint : Integrable (Function.uncurry fun (η : Path d) (t : ℝ) =>
        Real.exp (-s * t) * f (η t.toNNReal)) ((K y).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
      refine Integrable.mono' ((integrable_const ‖f‖).mul_prod hE)
        hg.aestronglyMeasurable (ae_of_all _ fun z => ?_)
      obtain ⟨η, t⟩ := z
      simp only [Function.uncurry_apply_pair]
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hfn _) (Real.exp_nonneg _)
    have h := integral_integral_swap hint
    simp only [Function.uncurry_def, integral_const_mul] at h
    exact h
  have hshift := MarkovProcess.ContinuousPath.measurable_shift_stoppingTime T hT
  calc
    _ = ∫ η, Φ η ∂((K x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift (T γ) γ) := by
      rw [integral_map hshift.aemeasurable hΦm.aestronglyMeasurable]
      rfl
    _ = ∫ η, Φ η ∂(ProbabilityTheory.Kernel.comap K (fun γ => γ (T γ))
          (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
            ((K x).restrict A)) := by rw [hrestart]
    _ = _ := by
      rw [Measure.comp_eq_comp_const_apply, ProbabilityTheory.Kernel.integral_comp]
      · simp only [ProbabilityTheory.Kernel.const_apply, ProbabilityTheory.Kernel.comap_apply, hswap]
      · exact hΦi _

end EinsteinFull
