import EinsteinFull.Calculus.CLConstantEnvironmentBrownian
import EinsteinFull.Work.W2.CorrectorReuseSupport
import EinsteinRelation.Diffusion.TimeChangeCovariance
import MarkovProcess.Main

/-!
# The corrector covariance in a constant environment

A Brownian law is invariant under diffusive rescaling, and a Brownian law is determined by its
covariance (its finite-dimensional characteristic functions determine it). When the environment
law is a point mass at a translation invariant field, the reduced diffusion is the Brownian law
with covariance `a(0)`, the corrector gradient has mean zero so the homogenized coefficient is
`a(0)`, and the annealed invariance principle holds with the homogenized coefficient.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology ENNReal BigOperators

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

theorem dot_smul_right' (ξ y : Vec d) (ε : ℝ) : dot ξ (ε • y) = ε * dot ξ y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem dot_smul_left' (ξ y : Vec d) (ε : ℝ) : dot (ε • ξ) y = ε * dot ξ y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Brownian laws are invariant under diffusive rescaling. -/
theorem IsBrownianLaw.map_rescalePath {A : Mat d} {W : Measure (Path d)}
    (hW : IsBrownianLaw A W) {ε : ℝ} (hε : ε ≠ 0) :
    IsBrownianLaw A (W.map (rescalePath ε)) := by
  obtain ⟨hprob, hsymm, hpsd, hstart, hchar⟩ := hW
  have hm : Measurable (rescalePath (d := d) ε) :=
    (TimeChangeCovariance.continuous_rescalePath ε).measurable
  refine ⟨inferInstance, hsymm, hpsd, ?_, fun n t ξ => ?_⟩
  · rw [ae_map_iff hm.aemeasurable
      (measurableSet_eq_fun (continuous_eval_const (0 : ℝ≥0)).measurable measurable_const)]
    filter_upwards [hstart] with γ hγ
    show ε • γ ((ε⁻¹ ^ 2).toNNReal * 0) = 0
    rw [mul_zero, hγ, smul_zero]
  · set s : ℝ≥0 := (ε⁻¹ ^ 2).toNNReal with hs
    have hint : AEStronglyMeasurable (fun γ : Path d =>
        Complex.exp (Complex.I * ((∑ k, dot (ξ k) (γ (t k))) : ℂ))) (W.map (rescalePath ε)) := by
      refine Continuous.aestronglyMeasurable ?_
      refine Complex.continuous_exp.comp (continuous_const.mul ?_)
      refine continuous_finsetSum _ fun k _ => Complex.continuous_ofReal.comp ?_
      exact (contDiff_dot (ξ k)).continuous.comp (continuous_eval_const (t k))
    rw [integral_map hm.aemeasurable hint]
    have e1 : ∀ γ : Path d, (∑ k, (dot (ξ k) ((rescalePath ε γ) (t k)) : ℂ)) =
        ∑ k, (dot (ε • ξ k) (γ (s * t k)) : ℂ) := by
      intro γ
      refine Finset.sum_congr rfl fun k _ => ?_
      show ((dot (ξ k) (ε • γ ((ε⁻¹ ^ 2).toNNReal * t k)) : ℝ) : ℂ) = _
      rw [dot_smul_right', dot_smul_left']
    simp_rw [e1]
    rw [hchar n (fun k => s * t k) (fun k => ε • ξ k)]
    congr 2
    have hs1 : (s : ℝ) * ε ^ 2 = 1 := by
      rw [hs, Real.coe_toNNReal _ (by positivity)]
      field_simp
    have e2 : ∀ k l, (min ((s * t k : ℝ≥0) : ℝ) ((s * t l : ℝ≥0) : ℝ)) *
        dot (ε • ξ k) (A.mulVec (ε • ξ l)) = (min (t k : ℝ) (t l)) * dot (ξ k) (A.mulVec (ξ l)) := by
      intro k l
      rw [NNReal.coe_mul, NNReal.coe_mul, ← mul_min_of_nonneg _ _ s.coe_nonneg,
        Matrix.mulVec_smul, dot_smul_right', dot_smul_left']
      calc (s : ℝ) * min (t k : ℝ) (t l) * (ε * (ε * dot (ξ k) (A.mulVec (ξ l)))) =
            ((s : ℝ) * ε ^ 2) * (min (t k : ℝ) (t l) * dot (ξ k) (A.mulVec (ξ l))) := by ring
        _ = _ := by rw [hs1, one_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => e2 k l

/-- Path laws agreeing on all finite-time marginals are equal (the argument of
`SubdiffusiveProcess.path_measure_eq_of_finiteEvaluation_map_eq`). -/
theorem path_measure_eq_of_finiteEvaluation_map_eq' (μ ν : Measure (Path d)) [IsFiniteMeasure μ]
    (h : ∀ I : Finset ℝ≥0,
      μ.map (MarkovProcess.ContinuousPath.finiteEvaluation (fun t : I => (t : ℝ≥0))) =
        ν.map (MarkovProcess.ContinuousPath.finiteEvaluation (fun t : I => (t : ℝ≥0)))) :
    μ = ν := by
  rw [← MarkovProcess.Measure.map_denseRestriction_eq_iff]
  apply MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
  intro J
  have key : ∀ ρ : Measure (Path d),
      (ρ.map MarkovProcess.ContinuousPath.denseRestriction).map J.restrict =
        (ρ.map (MarkovProcess.ContinuousPath.finiteEvaluation
            (fun t : MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J =>
              (t : ℝ≥0)))).map (MarkovProcess.DenseTimePath.pullbackPhysicalSet J) := by
    have hEvaluate : Measurable (MarkovProcess.ContinuousPath.finiteEvaluation (α := Vec d)
        (fun t : MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J =>
          (t : ℝ≥0))) := by
      rw [measurable_pi_iff]
      intro t
      exact MarkovProcess.ContinuousPath.measurable_coordinateProcess (alpha := Vec d) (t : ℝ≥0)
    have hfun : J.restrict ∘ MarkovProcess.ContinuousPath.denseRestriction (alpha := Vec d) =
        MarkovProcess.DenseTimePath.pullbackPhysicalSet J ∘
          MarkovProcess.ContinuousPath.finiteEvaluation
          (fun t : MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J =>
            (t : ℝ≥0)) := by
      funext path
      exact (MarkovProcess.DenseTimePath.pullbackPhysicalSet_evaluation J path).symm
    intro ρ
    rw [Measure.map_map (Finset.measurable_restrict J)
        MarkovProcess.ContinuousPath.measurable_denseRestriction,
      hfun, ← Measure.map_map
        (MarkovProcess.DenseTimePath.measurable_pullbackPhysicalSet J) hEvaluate]
  rw [key μ, key ν, h (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)]

/-- A continuous linear functional on finitely many coordinates of `ℝ^d` is a sum of dot
products. -/
theorem strongDual_pi_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : StrongDual ℝ (ι → Vec d)) (x : ι → Vec d) :
    L x = ∑ t, dot (fun j => L (Pi.single t (Pi.single j 1))) (x t) := by
  have hx : x = ∑ t, ∑ j, x t j • (Pi.single t (Pi.single j 1) : ι → Vec d) := by
    funext t' j'
    rw [Finset.sum_apply, Finset.sum_eq_single t']
    · rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single j']
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      simp [Finset.sum_apply, Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul, smul_eq_mul, dot]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A Brownian law is determined by its covariance. -/
theorem IsBrownianLaw.unique {A : Mat d} {W₁ W₂ : Measure (Path d)} (h₁ : IsBrownianLaw A W₁)
    (h₂ : IsBrownianLaw A W₂) : W₁ = W₂ := by
  have := h₁.1
  have := h₂.1
  classical
  refine path_measure_eq_of_finiteEvaluation_map_eq' W₁ W₂ fun I => ?_
  have hev : Continuous (MarkovProcess.ContinuousPath.finiteEvaluation (α := Vec d)
      (fun t : I => (t : ℝ≥0))) := MarkovProcess.ContinuousPath.continuous_finiteEvaluation _
  refine Measure.ext_of_charFunDual ?_
  ext L
  have hL : Continuous fun v : I → Vec d => Complex.exp ((L v : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp L.continuous).mul
      continuous_const)
  rw [charFunDual_apply, charFunDual_apply,
    integral_map hev.measurable.aemeasurable hL.aestronglyMeasurable,
    integral_map hev.measurable.aemeasurable hL.aestronglyMeasurable]
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let ξ : Fin (Fintype.card I) → Vec d := fun k j => L (Pi.single (e k) (Pi.single j 1))
  let τ : Fin (Fintype.card I) → ℝ≥0 := fun k => (e k : ℝ≥0)
  have hrep : ∀ γ : Path d, Complex.exp ((L (MarkovProcess.ContinuousPath.finiteEvaluation
      (α := Vec d) (fun t : I => (t : ℝ≥0)) γ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((∑ k, dot (ξ k) (γ (τ k))) : ℂ)) := by
    intro γ
    rw [strongDual_pi_apply L, mul_comm]
    congr 2
    push_cast
    exact (Equiv.sum_comp e (fun t => ((dot (fun j => L (Pi.single t (Pi.single j 1)))
      (γ t) : ℝ) : ℂ))).symm
  simp_rw [hrep]
  rw [h₁.2.2.2.2 _ τ ξ, h₂.2.2.2.2 _ τ ξ]

/-- For a point mass at a field, the homogenized coefficient is the reduced coefficient at the
origin: the corrector gradient has mean zero. -/
theorem homogenizedCoefficient_of_constant {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {c : FieldPair d} (hQc : ∀ᵐ ω ∂Q.measure, ω = c) :
    homogenizedCoefficient Q = reducedCoefficient c 0 := by
  have : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hmeas : ∀ k l : Fin d, Measurable fun ρ : FieldPair d => ρ.1 0 k l := fun k l =>
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem k l).measurable
  have hset : MeasurableSet {ρ : FieldPair d | ∀ k l, ρ.1 0 k l = reducedCoefficient c 0 k l} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun l =>
      measurableSet_eq_fun (hmeas k l) measurable_const
  have hae : ∀ᵐ ρ ∂reducedLaw Q, ∀ k l, ρ.1 0 k l = reducedCoefficient c 0 k l := by
    rw [reducedLaw, ae_map_iff Probability.measurable_reduce.aemeasurable hset]
    filter_upwards [hQc] with ω hω k l
    rw [hω]
    rfl
  ext i j
  rw [homogenizedCoefficient_eq_integral_flux Q i j]
  have e : (fun ρ : FieldPair d => ∑ k, ρ.1 0 i k * (unitVector j k + correctorGradient Q j ρ k))
      =ᵐ[reducedLaw Q] fun ρ => reducedCoefficient c 0 i j +
        ∑ k, reducedCoefficient c 0 i k * correctorGradient Q j ρ k := by
    filter_upwards [hae] with ρ hρ
    simp only [hρ, mul_add, Finset.sum_add_distrib]
    congr 1
    simp [unitVector, Pi.single_apply]
  rw [integral_congr_ae e, integral_add (integrable_const _)
      (integrable_finsetSum _ fun k _ => (integrable_correctorGradient_coordinate Q j k).const_mul _),
    integral_finsetSum _ fun k _ => (integrable_correctorGradient_coordinate Q j k).const_mul _]
  simp [integral_const_mul, integral_correctorGradient_coordinate]

/-- The corrector covariance for a point mass at a translation invariant field. -/
theorem hasDiffusivity_of_constant (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    {c : FieldPair d} (hc : ∀ x, translate x c = c) (hQc : ∀ᵐ ω ∂Q.measure, ω = c)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0 (Y (0, ω))) :
    HasDiffusivity Q.measure (originLaw Y) (homogenizedCoefficient Q) := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨ω, hωc, hωr, hωs, hωY⟩ := (hQc.and (Q.regular.and (hQ.and hY))).exists
  rw [hωc] at hωr hωs hωY
  have hB := isBrownianLaw_of_constant hc hΛ hωr hωs.1 _ hωY
  rw [homogenizedCoefficient_of_constant Q hQc]
  refine ⟨Y (0, c), hB, fun F => ?_⟩
  have hconst : ∀ ε : ℝ, ε ≠ 0 →
      ∫ ω, ∫ γ, F (rescalePath ε γ) ∂originLaw Y ω ∂Q.measure = ∫ γ, F γ ∂(Y (0, c)) := by
    intro ε hε
    have e : (fun ω => ∫ γ, F (rescalePath ε γ) ∂originLaw Y ω) =ᵐ[Q.measure]
        fun _ => ∫ γ, F (rescalePath ε γ) ∂Y (0, c) := by
      filter_upwards [hQc] with ω hω
      rw [hω, originLaw_apply]
    rw [integral_congr_ae e]
    simp only [integral_const, probReal_univ, one_smul]
    have hm : Measurable (rescalePath (d := d) ε) :=
      (TimeChangeCovariance.continuous_rescalePath ε).measurable
    have hmap := integral_map (μ := Y (0, c)) hm.aemeasurable F.continuous.aestronglyMeasurable
    rw [IsBrownianLaw.unique (IsBrownianLaw.map_rescalePath hB hε) hB] at hmap
    exact hmap.symm
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hconst ε (ne_of_gt hε)).symm

end EinsteinFull.Blueprint
