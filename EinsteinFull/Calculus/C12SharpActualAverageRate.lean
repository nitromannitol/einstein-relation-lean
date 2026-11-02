import EinsteinFull.Proofs.CovarianceScaling
import EinsteinFull.Blueprint.G4.Proofs.W2Queue0145_2
import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_clock_u2D_continuity
import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_replacement_u2D_pair
import EinsteinFull.Blueprint.G4.node_e_u3A_numerator_u2D_clock
import EinsteinFull.Blueprint.G4.node_app_u3A_sharp_u2D_clock
import EinsteinRelation.Environment.ReductionEmbedding
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import EinsteinFull.Calculus.S4DivisionAbstract
import EinsteinFull.Calculus.ComplexForceSemigroupSupport
import EinsteinFull.Calculus.C9ResponseThresholdEnergy
import EinsteinFull.Calculus.C2TestReplacementSupport
import EinsteinFull.Regeneration.GMPVelocityTransfer
import EinsteinFull.Calculus.C9GMPMartingaleProblem
import EinsteinFull.Calculus.C38SharpClockContinuity

open MeasureTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation EinsteinRelation.Sharpness

/-! Quantitative bound for the actual sharp coefficient averages. -/

private theorem sharp_positive_clock_averages
    (h2 : node_app_u3A_sharp_u2D_clockStmt)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map
      (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (Y : DiffusionFamily d)
    (hY : ∀ lam : ℝ, 0 < lam → ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y lam (0, ω))) :
    ∃ avg eta : ℝ → ℝ, ∀ lam : ℝ, 0 < lam →
      HasReducedClockRate Q (Y lam) (eta lam) ∧
      eta lam = 1 - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) *
        lam * (avg lam - 1) ∧
      (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw (Y lam) ω,
        Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
          reducedCoefficient ω (γ u.toNNReal) (⟨0, by omega⟩ : Fin d)
            (⟨0, by omega⟩ : Fin d)) atTop (𝓝 (avg lam))) := by
  classical
  have hex := fun lam : {lam : ℝ // 0 < lam} =>
    (h2 d hd P hP D Q hQ).2 lam.val lam.property.ne' (Y lam.val)
      (hY lam.val lam.property)
  choose eta avg hrate hidentity havg hcorrector using hex
  refine ⟨fun lam => if h : 0 < lam then avg ⟨lam, h⟩ else 0,
    fun lam => if h : 0 < lam then eta ⟨lam, h⟩ else 0, ?_⟩
  intro lam hlam
  simp only [dite_eq_left hlam]
  exact ⟨hrate ⟨lam, hlam⟩, hidentity ⟨lam, hlam⟩, havg ⟨lam, hlam⟩⟩

private theorem sharp_replacement_clock_mean
    {d : ℕ} {L R Ln Rn : ℝ} (first : Fin d)
    (Q : EnvironmentLaw d L R) (Qn : EnvironmentLaw d Ln Rn)
    (F : FieldPair d → FieldPair d) (hF : Measurable F)
    (hQn : Qn.measure = Q.measure.map F)
    (hclock : ∀ᵐ ω ∂Q.measure,
      clockDensity (F ω) 0 = reducedCoefficient ω 0 first first) :
    (∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Qn) =
      ∫ ω, reducedCoefficient ω 0 first first ∂Q.measure := by
  have heval : Continuous fun ω : FieldPair d => ω.2 (0 : Vec d) :=
    (continuous_eval_const (0 : Vec d)).comp continuous_snd
  have hdensity : Continuous fun ω : FieldPair d => clockDensity ω (0 : Vec d) :=
    Real.continuous_exp.comp (continuous_const.mul heval)
  unfold reducedLaw
  rw [integral_map EinsteinRelation.Probability.measurable_reduce.aemeasurable
    heval.aestronglyMeasurable]
  change (∫ ω, clockDensity ω (0 : Vec d) ∂Qn.measure) = _
  rw [hQn, integral_map hF.aemeasurable hdensity.aestronglyMeasurable]
  exact integral_congr_ae hclock

private theorem sharp_measurable_coefficient_divergence {d : ℕ}
    (first : Fin d) (x : Vec d) :
    Measurable fun ω : FieldPair d =>
      divergence (fun y => (reducedCoefficient ω y).mulVec (unitVector first)) x := by
  have hraw (j : Fin d) : Measurable fun ω : FieldPair d =>
      fderiv ℝ (fun y => (ω.1 y) j first) x (unitVector j) := by
    have hc : Continuous fun p : FieldPair d × Vec d => (p.1.1 p.2) j first :=
      (continuous_fst.fst.eval continuous_snd).matrix_elem j first
    have hm := measurable_fderiv_apply_const_with_param ℝ
      (f := fun (ω : FieldPair d) (y : Vec d) => (ω.1 y) j first) hc (unitVector j)
    have hpt : Measurable fun ω : FieldPair d => (ω, x) :=
      measurable_id.prodMk measurable_const
    exact hm.comp hpt
  have hsum : Measurable fun ω : FieldPair d =>
      ∑ j, fderiv ℝ (fun y => (ω.1 y) j first) x (unitVector j) :=
    Finset.measurable_sum Finset.univ fun j _ => hraw j
  have hcol (ω : FieldPair d) (y : Vec d) (j : Fin d) :
      ((reducedCoefficient ω y).mulVec (unitVector first)) j =
        reducedCoefficient ω y j first := by
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
  unfold divergence coordinateDerivative
  simp_rw [hcol]
  exact hsum.comp EinsteinRelation.Probability.measurable_reduce

private theorem sharp_density_from_coefficient_ae {d : ℕ}
    {L R : ℝ} (first : Fin d) (P : Measure (NoiseSample d))
    (Q : EnvironmentLaw d L R)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair first))
    (x : Vec d) :
    ∀ᵐ ω ∂Q.measure, clockDensity ω x =
      1 + EinsteinFull.Work.W8.clockParameter first / 2 *
        divergence (fun y => (reducedCoefficient ω y).mulVec (unitVector first)) x := by
  have heval : Continuous fun ω : FieldPair d => ω.2 x :=
    (continuous_eval_const x).comp continuous_snd
  have hdensity : Measurable fun ω : FieldPair d => clockDensity ω x :=
    (Real.continuous_exp.comp (continuous_const.mul heval)).measurable
  have hm : MeasurableSet {ω : FieldPair d | clockDensity ω x =
      1 + EinsteinFull.Work.W8.clockParameter first / 2 *
        divergence (fun y => (reducedCoefficient ω y).mulVec (unitVector first)) x} :=
    measurableSet_eq_fun hdensity
      (measurable_const.add (measurable_const.mul
        (sharp_measurable_coefficient_divergence first x)))
  rw [hQ]
  apply (ae_map_iff (EinsteinFull.Work.W8.measurable_physicalPair first).aemeasurable hm).mpr
  filter_upwards [] with W
  rw [EinsteinFull.Work.W8.physicalPair_clockDensity]
  simp only [EinsteinFull.Work.W8.physicalPair_reducedCoefficient, densityField]

private theorem sharp_replacement_injective_on_full_set {d : ℕ}
    {L R : ℝ} (first : Fin d) (P : Measure (NoiseSample d))
    (Q : EnvironmentLaw d L R)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair first))
    (F : FieldPair d → FieldPair d)
    (hcoeff : ∀ᵐ ω ∂Q.measure, ∀ x,
      reducedCoefficient (F ω) x = reducedCoefficient ω x) :
    ∃ s : Set (FieldPair d), s ∈ ae Q.measure ∧ MeasurableSet s ∧ Set.InjOn F s := by
  classical
  have hform : ∀ᵐ ω ∂Q.measure, ∀ n : ℕ,
      clockDensity ω (TopologicalSpace.denseSeq (Vec d) n) =
      1 + EinsteinFull.Work.W8.clockParameter first / 2 *
        divergence (fun y => (reducedCoefficient ω y).mulVec (unitVector first))
          (TopologicalSpace.denseSeq (Vec d) n) :=
    ae_all_iff.mpr fun n => sharp_density_from_coefficient_ae first P Q hQ _
  obtain ⟨s, hs, hsm, hsprop⟩ := (hcoeff.and hform).exists_measurable_mem
  refine ⟨s, hs, hsm, ?_⟩
  intro ω hω η hη heq
  have hcoeffeq : reducedCoefficient ω = reducedCoefficient η := by
    funext x
    rw [← (hsprop ω hω).1 x, ← (hsprop η hη).1 x, heq]
  have hdensityeq : clockDensity ω = clockDensity η := by
    apply (TopologicalSpace.denseRange_denseSeq (Vec d)).equalizer
      (Real.continuous_exp.comp (continuous_const.mul ω.2.continuous))
      (Real.continuous_exp.comp (continuous_const.mul η.2.continuous))
    funext n
    change clockDensity ω _ = clockDensity η _
    exact ((hsprop ω hω).2 n).trans (by rw [hcoeffeq]; exact ((hsprop η hη).2 n).symm)
  apply EinsteinRelation.Probability.injective_reduce
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro x
  · exact congrFun hcoeffeq x
  · exact congrFun hdensityeq x

private theorem sharp_replacement_measurable_inverse {d : ℕ}
    {L R : ℝ} (first : Fin d) (P : Measure (NoiseSample d))
    (Q : EnvironmentLaw d L R)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair first))
    (F : FieldPair d → FieldPair d) (hF : Measurable F)
    (hcoeff : ∀ᵐ ω ∂Q.measure, ∀ x,
      reducedCoefficient (F ω) x = reducedCoefficient ω x) :
    ∃ G : FieldPair d → FieldPair d, Measurable G ∧
      (∀ᵐ ω ∂Q.measure, G (F ω) = ω) ∧
      (Q.measure.map F).map G = Q.measure := by
  classical
  obtain ⟨s, hs, hsm, hinj⟩ :=
    sharp_replacement_injective_on_full_set first P Q hQ F hcoeff
  have : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  have : PolishSpace (FieldPair d) := inferInstance
  have : StandardBorelSpace s := hsm.standardBorel
  have hsae : ∀ᵐ ω ∂Q.measure, ω ∈ s := hs
  have : Nonempty s := ⟨⟨hsae.exists.choose, hsae.exists.choose_spec⟩⟩
  have hemb : MeasurableEmbedding (fun ω : s => F ω) :=
    (hF.comp measurable_subtype_coe).measurableEmbedding
      (fun ω η h => Subtype.ext (hinj ω.property η.property h))
  let G : FieldPair d → FieldPair d := fun ω => (hemb.invFun ω).val
  have hG : Measurable G := measurable_subtype_coe.comp hemb.measurable_invFun
  have hleft : ∀ᵐ ω ∂Q.measure, G (F ω) = ω := by
    filter_upwards [hs] with ω hω
    exact congrArg Subtype.val (hemb.leftInverse_invFun ⟨ω, hω⟩)
  refine ⟨G, hG, hleft, ?_⟩
  rw [Measure.map_map hG hF]
  exact (Measure.map_congr hleft).trans Measure.map_id'

private theorem sharp_inverse_ae_transport {d : ℕ} {μ : Measure (FieldPair d)}
    {F G : FieldPair d → FieldPair d} (hF : Measurable F) (hG : Measurable G)
    (hleft : ∀ᵐ ω ∂μ, G (F ω) = ω) (hmap : (μ.map F).map G = μ)
    (p : FieldPair d → FieldPair d → Prop)
    (hp : ∀ᵐ ω ∂μ, p (F ω) ω) :
    ∀ᵐ ω ∂μ.map F, p ω (G ω) := by
  have : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  have : PolishSpace (FieldPair d) := inferInstance
  have hright : ∀ᵐ ω ∂μ.map F, F (G ω) = ω := by
    apply (ae_map_iff hF.aemeasurable
      (measurableSet_eq_fun (hF.comp hG) measurable_id)).mpr
    filter_upwards [hleft] with ω hω
    change F (G (F ω)) = F ω
    rw [hω]
  have hp' : ∀ᵐ ω ∂μ.map F, p (F (G ω)) (G ω) := by
    have hh : ∀ᵐ ω ∂(μ.map F).map G, p (F ω) ω := by rw [hmap]; exact hp
    exact ae_of_ae_map hG.aemeasurable hh
  filter_upwards [hright, hp'] with ω hω hpω
  rwa [hω] at hpω

private theorem sharp_coefficient_average_replacement_rate {d : ℕ}
    (first : Fin d) (ω ωn : FieldPair d) (γ : Path d) (avg : ℝ)
    (hclock : ∀ x : Vec d, clockDensity ωn x = reducedCoefficient ω x first first)
    (havg : Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
      reducedCoefficient ω (γ u.toNNReal) first first) atTop (𝓝 avg)) :
    EinsteinRelation.Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ωn γ avg := by
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hh := havg.comp hcoe
  unfold EinsteinRelation.Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed
  convert hh using 1
  funext t
  change (∫ u in (0 : ℝ)..(t : ℝ), clockDensity ωn (γ u.toNNReal)) / (t : ℝ) =
    (t : ℝ)⁻¹ * ∫ u in (0 : ℝ)..(t : ℝ),
      reducedCoefficient ω (γ u.toNNReal) first first
  simp_rw [hclock]
  exact div_eq_inv_mul _ _

private theorem sharp_replacement_supplied_family {d : ℕ} {L R Ln Rn : ℝ}
    (first : Fin d) (P : Measure (NoiseSample d))
    (Q : EnvironmentLaw d L R) (Qn : EnvironmentLaw d Ln Rn)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair first))
    (F : FieldPair d → FieldPair d) (hF : Measurable F)
    (hQn : Qn.measure = Q.measure.map F)
    (hcoeff : ∀ᵐ ω ∂Q.measure, ∀ x,
      reducedCoefficient (F ω) x = reducedCoefficient ω x)
    (hgen : ∀ᵐ ω ∂Q.measure, ∀ (lam : ℝ) (f : Vec d → ℝ) (x : Vec d),
      reducedGenerator first (F ω) lam f x = reducedGenerator first ω lam f x)
    (hclock : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      clockDensity (F ω) x = reducedCoefficient ω x first first)
    (Y : DiffusionFamily d)
    (hY : ∀ lam : ℝ, 0 < lam → ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator first ω lam) 0 (Y lam (0, ω))) :
    ∃ Yn : DiffusionFamily d,
      (∀ lam : ℝ, ∀ᵐ ω ∂Q.measure, Yn lam (0, F ω) = Y lam (0, ω)) ∧
      (∀ lam : ℝ, 0 < lam → ∀ᵐ ω ∂Qn.measure,
        SolvesMartingaleProblem (reducedGenerator first ω lam) 0 (Yn lam (0, ω))) ∧
      ∀ (lam avg : ℝ),
        (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw (Y lam) ω,
          Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
            reducedCoefficient ω (γ u.toNNReal) first first) atTop (𝓝 avg)) →
        HasReducedClockRate Qn (Yn lam) avg := by
  obtain ⟨G, hG, hleft, hmap⟩ :=
    sharp_replacement_measurable_inverse first P Q hQ F hF hcoeff
  let Yn : DiffusionFamily d := fun lam => (Y lam).comap
    (fun p : Vec d × FieldPair d => (p.1, G p.2))
    (measurable_fst.prodMk (hG.comp measurable_snd))
  have hYn (lam : ℝ) : ∀ᵐ ω ∂Q.measure, Yn lam (0, F ω) = Y lam (0, ω) := by
    filter_upwards [hleft] with ω hω
    change Y lam (0, G (F ω)) = Y lam (0, ω)
    rw [hω]
  refine ⟨Yn, hYn, ?_, ?_⟩
  · intro lam hlam
    rw [hQn]
    have hp : ∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator first (F ω) lam) 0 (Y lam (0, ω)) := by
      filter_upwards [hY lam hlam, hgen] with ω hω hgω
      have hg : reducedGenerator first (F ω) lam = reducedGenerator first ω lam :=
        funext fun f => funext fun x => hgω lam f x
      rwa [hg]
    exact sharp_inverse_ae_transport hF hG hleft hmap
      (fun ω η => SolvesMartingaleProblem (reducedGenerator first ω lam) 0 (Y lam (0, η))) hp
  · intro lam avg havg
    unfold HasReducedClockRate
    rw [hQn]
    apply sharp_inverse_ae_transport hF hG hleft hmap
      (fun ω η => ∀ᵐ γ ∂originLaw (Y lam) η,
        EinsteinRelation.Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ avg)
    filter_upwards [havg, hclock] with ω hω hcω
    filter_upwards [hω] with γ hγ
    exact sharp_coefficient_average_replacement_rate first ω (F ω) γ avg hcω hγ

private theorem sharp_clock_expansion_bound {d : ℕ} (hd : 2 ≤ d)
    (C lam m eta chi : ℝ) (e : Fin d → ℝ)
    (hC : 0 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ Real.exp (-1))
    (he : ∀ j, |e j| ≤ C) (hchi : |chi| ≤ C)
    (hrem : |eta - m - (∑ j : Fin d, e j * lam ^ (j.val + 1)) +
        2 * chi * criticalKernelTerm d lam hlam.ne'| ≤
      C * lam ^ d * expansionModulus lam hlam hsmall) :
    |eta - m| ≤ ((d : ℝ) + 9) * C * lam := by
  have hlam1 : lam ≤ 1 := hsmall.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hpoly : |∑ j : Fin d, e j * lam ^ (j.val + 1)| ≤ (d : ℝ) * C * lam := by
    calc
      _ ≤ ∑ j : Fin d, |e j * lam ^ (j.val + 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, C * lam := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_pow, abs_of_pos hlam]
        exact mul_le_mul (he j) (EinsteinFull.pow_le_self_of_le_one hlam hlam1 (by omega))
          (pow_nonneg hlam.le _) hC
      _ = (d : ℝ) * C * lam := by simp; ring
  have hT : |criticalKernelTerm d lam hlam.ne'| ≤ 4 * lam := by
    apply (T_bounds hd hlam hlam1 (expansionModulus_le_one hlam hsmall)
      (mul_one_add_log_le hlam hsmall) ?_).2
    simpa only [abs_of_pos hlam] using
      abs_criticalKernelTerm_le d hlam.ne' (by simpa only [abs_of_pos hlam] using hsmall)
  have hR : |eta - m - (∑ j : Fin d, e j * lam ^ (j.val + 1)) +
      2 * chi * criticalKernelTerm d lam hlam.ne'| ≤ C * lam := by
    refine hrem.trans ?_
    calc
      _ ≤ C * lam ^ d * 1 := mul_le_mul_of_nonneg_left
        (expansionModulus_le_one hlam hsmall) (mul_nonneg hC (pow_nonneg hlam.le _))
      _ ≤ C * lam := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left
          (EinsteinFull.pow_le_self_of_le_one hlam hlam1 (by omega)) hC
  have hh := eta_sub_m_le hpoly hR hchi hT hC
  convert hh using 1
  congr 1
  ring

/-- The perturbation input is instantiated with the actual reduced fields and
the actual unforced commutator, rather than arbitrary L² observations. -/
private theorem sharp_actual_observations {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) :
    ∃ (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β ∧ IsReducedCoefficientObservation Q a ∧
        IsReducedClockObservation Q μ ∧ IsJointObservation Q Z := by
  classical
  have : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨_, _, hβ⟩ := response_reduced_drift_exists_uniform_bound d D
  obtain ⟨β, hβ, _⟩ := hβ Q hQ
  have ha (j k : Fin d) : MemLp (fun ω : FieldPair d => (ω.1 0 j k : ℂ))
      2 (reducedLaw Q) := (memLp_reduced_coefficient_complex Q j k).mono_exponent le_top
  have hm : MemLp (fun ω : FieldPair d => (ω.2 0 : ℂ)) 2 (reducedLaw Q) := by
    apply MemLp.of_bound
      (Complex.continuous_ofReal.comp
        ((continuous_eval_const (0 : Vec d)).comp continuous_snd)).aestronglyMeasurable
      (sourceReducedBound D.ellipticity)
    simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs,
      reducedLaw, Carriers.reducedReferenceLaw] using
      Clock.ae_abs_clockAtOrigin_le Q
  have hXi (j i : Fin d) : MemLp
      (fun ω => (commutatorObservation Q j i ω : ℂ)) 2 (reducedLaw Q) := by
    have hg := (memLp_const (Correctors.correctorUnitVector i)
      (p := (2 : ℝ≥0∞)) (μ := reducedLaw Q)).add (Lp.memLp (correctorGradient Q i))
    apply hg.of_le_mul (c := (d : ℝ) * (2 * sourceReducedBound D.ellipticity))
      (Complex.measurable_ofReal.comp
        (EinsteinFull.Calculus.C2TestReplacement.commutatorObservation_measurable Q j i)).aestronglyMeasurable
    simpa only [Function.comp_apply, Pi.add_apply, Complex.norm_real, Real.norm_eq_abs] using
      EinsteinFull.Calculus.C2TestReplacement.ae_abs_commutatorObservation_le Q j i
  have hc : MemLp (fun ω => (centeredClockField Q 0 ω : ℂ)) 2 (reducedLaw Q) := by
    apply MemLp.of_bound
      (Complex.continuous_ofReal.comp ((continuous_centeredClockField Q).comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
      (2 * sourceReducedBound D.ellipticity)
    simpa only [Function.comp_apply, id_eq, Complex.norm_real, Real.norm_eq_abs] using
      ae_abs_centeredClockField_le Q 0
  refine ⟨β, (fun j k => (ha j k).toLp _), hm.toLp _,
    (fun z => match z with
      | .inl (j, i) => (hXi j i).toLp _
      | .inr () => hc.toLp _), hβ, (fun j k => (ha j k).coeFn_toLp),
    hm.coeFn_toLp, (fun j i => (hXi j i).coeFn_toLp), ?_⟩
  exact hc.coeFn_toLp

/-- The complete covariance theorem supplies every joint component, including
commutator entries; no restriction to clock-supported tests is used. -/
private theorem sharp_actual_joint_covariance {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (hZ : IsJointObservation Q Z) :
    ∃ covariance, IsJointCovariance Q Z covariance := by
  obtain ⟨ε, C, hε, _hC, h⟩ :=
    EinsteinFull.Proofs.covariance_scaling d hd D (2 * d + 11) (by omega)
  obtain ⟨covariance, _hpos, _hbound, hrate⟩ := h Q hQ
  refine ⟨covariance, w2_jointCovariance_of_rate Q Z covariance
    (2 * d + 11) ε C hε ?_⟩
  intro R hR F G
  rw [jointTestCovariance_eq_integral]
  exact hrate Z hZ R hR F G


/-- A measurable replacement transports the velocity of the actual supplied
origin kernel. The almost-sure inverse avoids an extra measurability premise
on the nested path-law assertion. -/
private theorem sharp_replacement_supplied_velocity {d : ℕ} {L R Ln Rn : ℝ}
    (first : Fin d) (P : Measure (NoiseSample d))
    (Q : EnvironmentLaw d L R) (Qn : EnvironmentLaw d Ln Rn)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair first))
    (F : FieldPair d → FieldPair d) (hF : Measurable F)
    (hQn : Qn.measure = Q.measure.map F)
    (hcoeff : ∀ᵐ ω ∂Q.measure, ∀ x,
      reducedCoefficient (F ω) x = reducedCoefficient ω x)
    (Y Yn : QuenchedPathLaws d)
    (hYn : ∀ᵐ ω ∂Q.measure, Yn (0, F ω) = Y (0, ω))
    (ell : Vec d) (hvelocity : HasQuenchedVelocity Q.measure (originLaw Y) ell) :
    HasQuenchedVelocity Qn.measure (originLaw Yn) ell := by
  obtain ⟨G, hG, hleft, hmap⟩ :=
    sharp_replacement_measurable_inverse first P Q hQ F hF hcoeff
  unfold HasQuenchedVelocity
  rw [hQn]
  apply sharp_inverse_ae_transport hF hG hleft hmap
    (fun ω _ => ∀ᵐ γ ∂originLaw Yn ω, HasPathVelocity γ ell)
  filter_upwards [hYn, hvelocity] with ω heq hω
  change ∀ᵐ γ ∂Yn (0, F ω), HasPathVelocity γ ell
  rw [heq]
  exact hω


/-- The actual sharp coefficient averages obey a uniform linear-force estimate. -/
theorem sharp_actual_coefficient_average_uniform_linear_force_bound
    (hrep : node_sharp_u2E_example_u23_replacement_u2D_pairStmt)
    (hnum : node_e_u3A_numerator_u2D_clockStmt)
    (hclock : node_app_u3A_sharp_u2D_clockStmt)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map
      (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (Y : DiffusionFamily d)
    (hY : ∀ lam : ℝ, 0 < lam → ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y lam (0, ω)))
    (hvelocity : ∃ r : ℝ, 0 < r ∧ ∀ lam : ℝ, 0 < lam → lam ≤ r →
      ∃ ell : Vec d, HasQuenchedVelocity Q.measure (originLaw (Y lam)) ell) :
    ∃ avg : ℝ → ℝ, ∃ C radius : ℝ, 0 ≤ C ∧ 0 < radius ∧
      (∀ lam : ℝ, 0 < lam → ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw (Y lam) ω,
        Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
          reducedCoefficient ω (γ u.toNNReal) (⟨0, by omega⟩ : Fin d)
            (⟨0, by omega⟩ : Fin d)) atTop (𝓝 (avg lam))) ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ radius →
        |avg lam - ∫ ω, reducedCoefficient ω 0 (⟨0, by omega⟩ : Fin d)
          (⟨0, by omega⟩ : Fin d) ∂Q.measure| ≤ C * lam := by
  classical
  obtain ⟨avg, eta, havg⟩ := sharp_positive_clock_averages hclock d hd P hP D Q hQ Y hY
  obtain ⟨Dn, F, hF, hformula, Qn, hQn, hsmooth⟩ := hrep d hd P hP D Q hQ
  have hcoeff : ∀ᵐ ω ∂Q.measure, ∀ x,
      reducedCoefficient (F ω) x = reducedCoefficient ω x := by
    filter_upwards [hformula] with ω hω
    exact fun x => (hω x).2.2.2.2.1
  have hc : ∀ᵐ ω ∂Q.measure, ∀ x,
      clockDensity (F ω) x = reducedCoefficient ω x (⟨0, by omega⟩ : Fin d)
        (⟨0, by omega⟩ : Fin d) := by
    filter_upwards [hformula] with ω hω
    exact fun x => (hω x).2.2.2.1
  have hgen : ∀ᵐ ω ∂Q.measure, ∀ (lam : ℝ) (f : Vec d → ℝ) (x : Vec d),
      reducedGenerator (⟨0, by omega⟩ : Fin d) (F ω) lam f x =
        reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam f x := by
    filter_upwards [hformula] with ω hω
    exact fun lam f x => (hω x).2.2.2.2.2 lam f
  obtain ⟨Yn, hYn, hYnMP, hrate⟩ := sharp_replacement_supplied_family
    (⟨0, by omega⟩ : Fin d) P Q Qn hQ F hF hQn hcoeff hgen hc Y hY
  obtain ⟨r, hr, hvel⟩ := hvelocity
  have hveln (lam : ℝ) (hlam : 0 < lam) (hsmall : lam ≤ r) :
      ∃ ell : Vec d, HasQuenchedVelocity Qn.measure (originLaw (Yn lam)) ell := by
    obtain ⟨ell, hell⟩ := hvel lam hlam hsmall
    exact ⟨ell, sharp_replacement_supplied_velocity (⟨0, by omega⟩ : Fin d)
      P Q Qn hQ F hF hQn hcoeff (Y lam) (Yn lam) (hYn lam) ell hell⟩
  obtain ⟨β, a, μ, Z, hβ, ha, hμ, hZ⟩ := sharp_actual_observations Dn Qn hsmooth
  obtain ⟨covariance, hcovariance⟩ := sharp_actual_joint_covariance hd Dn Qn hsmooth Z hZ
  obtain ⟨C, lamStar, hC, hstar, hsmall, hexpand⟩ := hnum d hd Dn
  obtain ⟨hγ, hK, hR, hI, _hzero, _haCoeff, hetaCoeff, hchi, hrem⟩ :=
    hexpand Qn hsmooth β a μ Z covariance hβ ha hμ hZ hcovariance
      (forcedComplexEvolution Qn (⟨0, by omega⟩ : Fin d))
      (fun ζ => isComplexEnvironmentSemigroup_forcedComplexEvolution Qn _ ζ)
  have hmean := sharp_replacement_clock_mean (⟨0, by omega⟩ : Fin d)
    Q Qn F hF hQn (by filter_upwards [hc] with ω hω; exact hω 0)
  refine ⟨avg, ((d : ℝ) + 9) * C, min lamStar r, ?_, lt_min hstar hr,
    (fun lam hlam => (havg lam hlam).2.2), ?_⟩
  · positivity
  · intro lam hlam hlamSmall
    have hstar' : lam ≤ lamStar := hlamSmall.trans (min_le_left _ _)
    obtain ⟨ell, hell⟩ := hveln lam hlam (hlamSmall.trans (min_le_right _ _))
    have h := (hrem lam (by rwa [abs_of_pos hlam])
      (by rwa [abs_of_pos hlam]) (by rw [abs_of_pos hlam]; exact hstar'.trans hsmall)
      (Yn lam) (hYnMP lam hlam) ell (avg lam) hell
      (hrate lam (avg lam) (havg lam hlam).2.2)).2
    have hb := sharp_clock_expansion_bound hd C lam _ (avg lam) _ _ hC.le hlam
      (hstar'.trans hsmall) hetaCoeff
      ((le_add_of_nonneg_left (by unfold euclideanNorm; positivity)).trans hchi)
      (by simpa only [abs_of_pos hlam] using h)
    rwa [hmean] at hb

/-- The actual sharp clock has the stated quadratic response. -/
theorem sharp_actual_quadratic_response_limit
    (hrep : node_sharp_u2E_example_u23_replacement_u2D_pairStmt)
    (hnum : node_e_u3A_numerator_u2D_clockStmt)
    (hclock : node_app_u3A_sharp_u2D_clockStmt)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map
      (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (Y : DiffusionFamily d)
    (hY : ∀ lam : ℝ, 0 < lam → ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y lam (0, ω)))
    (hvelocity : ∃ r : ℝ, 0 < r ∧ ∀ lam : ℝ, 0 < lam → lam ≤ r →
      ∃ ell : Vec d, HasQuenchedVelocity Q.measure (originLaw (Y lam)) ell) :
    ∃ eta avg : ℝ → ℝ,
      (∀ lam : ℝ, 0 < lam → HasReducedClockRate Q (Y lam) (eta lam) ∧
        eta lam = 1 - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d)
          * lam * (avg lam - 1)) ∧
      (∀ lam : ℝ, 0 < lam → ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw (Y lam) ω,
        Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
          reducedCoefficient ω (γ u.toNNReal) (⟨0, by omega⟩ : Fin d)
            (⟨0, by omega⟩ : Fin d)) atTop (𝓝 (avg lam))) ∧
      Tendsto (fun lam : ℝ => (lam / eta lam - lam) / lam^2)
        (𝓝[>] (0 : ℝ))
        (𝓝 (EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) *
          ((∫ ω, reducedCoefficient ω 0 (⟨0, by omega⟩ : Fin d)
            (⟨0, by omega⟩ : Fin d) ∂Q.measure) - 1))) := by
  classical
  obtain ⟨avg, C, r, hC, hr, havg, hbound⟩ :=
    sharp_actual_coefficient_average_uniform_linear_force_bound hrep hnum hclock d hd P hP D Q hQ Y hY hvelocity
  obtain ⟨avg', eta, hclock'⟩ := sharp_positive_clock_averages hclock d hd P hP D Q hQ Y hY
  have heq (lam : ℝ) (hlam : 0 < lam) : avg lam = avg' lam := by
    letI : IsProbabilityMeasure Q.measure := Q.probability
    obtain ⟨ω, hω, ha, hb⟩ := ((hY lam hlam).and ((havg lam hlam).and (hclock' lam hlam).2.2)).exists
    letI : IsProbabilityMeasure (originLaw (Y lam) ω) := hω.1
    obtain ⟨γ, hγa, hγb⟩ := (ha.and hb).exists
    exact tendsto_nhds_unique hγa hγb
  let m := ∫ ω, reducedCoefficient ω 0 (⟨0, by omega⟩ : Fin d)
    (⟨0, by omega⟩ : Fin d) ∂Q.measure
  have hlim : Tendsto avg (𝓝[>] (0 : ℝ)) (𝓝 m) := by
    have hzero : Tendsto (fun lam : ℝ => C * lam) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun lam : ℝ => lam) (𝓝[>] (0 : ℝ)) (𝓝 0))
    have hdist : Tendsto (fun lam : ℝ => |avg lam - m|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
      · exact Filter.Eventually.of_forall (fun _ => abs_nonneg _)
      · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr)] with lam hp hs
        exact hbound lam hp hs.le
    exact (tendsto_iff_norm_sub_tendsto_zero).2 (by simpa only [Real.norm_eq_abs] using hdist)
  refine ⟨eta, avg, ?_, havg, ?_⟩
  · intro lam hlam
    exact ⟨(hclock' lam hlam).1, by rw [heq lam hlam]; exact (hclock' lam hlam).2.1⟩
  · apply (sharp_right_quadratic_response_of_average_limit (⟨0, by omega⟩ : Fin d) avg m hlim).congr'
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    rw [(hclock' lam hlam).2.1, ← heq lam hlam]

end EinsteinFull.Blueprint
