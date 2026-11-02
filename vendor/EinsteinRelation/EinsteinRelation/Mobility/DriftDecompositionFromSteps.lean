import EinsteinRelation.Mobility.VelocityAbelFromDecomposition

/-! # The drift-martingale decomposition from a drift bound and a quenched second moment bound

Source: `paper/main.tex` 1144-1146 and Gantert, Mathieu and Piatnitski (2012), Section 7, p. 33.
`DriftDecompositionStep` is split into two step propositions:

* `DriftBoundStep`: the drift `b_i^λ = ½ D·(a e_i) + λ e₁·a e_i` is essentially bounded under the
  reduced reference law, for every weak horizontal divergence `D·(a e_i)`;
* `QuenchedDriftMartingaleStep`: for almost every environment, the martingale part
  `M_t = Y_t·e_i - ∫₀ᵗ b(ω_u) du` of the reduced GMP diffusion from the origin is square integrable
  with `E[M_t²] ≤ C t`. This is the Fukushima decomposition of the coordinate function used by GMP
  (p. 33, citing Fukushima, Oshima and Takeda 1994, Theorems 5.5.1 and 5.5.2), with the bracket
  bounded by the ellipticity constant.

`driftDecompositionStep_of_steps` integrates the quenched bound against the environment law.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace EinsteinRelation

open Carriers

/-- Step `DriftBoundStep`: for `0 < λ ≤ 1` and every weak horizontal divergence `D·(a e_i)` of the
`i`-th column of the reduced coefficient, the drift `b_i^λ` is essentially bounded under the
reduced reference law. -/
def DriftBoundStep : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ), 0 < lam → lam ≤ 1 →
    ∀ (hQ : IsStationary (reducedReferenceLaw Q)) (i : Fin d) (divA : FieldPair d → ℝ),
      HasWeakHorizontalDivergence (reducedReferenceLaw Q) hQ
        (fun ω : FieldPair d => (ω.1 0).mulVec (unitVector i)) divA →
      ∃ B : ℝ, ∀ᵐ w ∂reducedReferenceLaw Q, |velocityDrift hd lam i divA w| ≤ B

/-- Step `QuenchedDriftMartingaleStep`: for the reduced GMP family at `0 < λ ≤ 1` and every weak
horizontal divergence `D·(a e_i)`, there is `C` such that for every `t ≥ 0` and almost every
environment `ω`, the martingale part `M_t = Y_t·e_i - ∫₀ᵗ b_i^λ(ω_u) du` of the reduced diffusion from
the origin is square integrable with `E[M_t²] ≤ C t`.

Sources: the reduced form `(a, 0)` with `a = e^{-2V} a₀` is GMP 2012, p. 10, (3.8)-(3.9); its
Dirichlet form is GMP p. 32, (7.1), and Lemma 7.1, p. 33. GMP p. 33 applies Fukushima, Oshima and
Takeda 1994, Theorems 5.5.1 and 5.5.2, to a coordinate function: the coordinate has a Fukushima
decomposition whose martingale part has bracket `∫₀ᵗ a_ii(Y_s) ds ≤ Λ t` (GMP (7.3)), hence is a square
integrable martingale. The zero-energy part is identified with `∫₀ᵗ b_i^λ(Y_s) ds` through FOT
Theorem 5.4.2, applied to the cutoffs `χ_R x_i`, which lie in the generator domain for Lipschitz `a`
with `L^λ x_i = ½ Σ_j ∂_j a_ji + λ a_1i`, followed by localization. GMP pp. 32-33 moves the statement
from almost every starting point to the origin for almost every environment by translation covariance
and stationarity. The constant can be taken `C = Λ₀ e^{2Λ₀}`, uniform in `λ`, `i`, `ω` and the version
of `D·(a e_i)`. The cutoff computation, the identification of the horizontal divergence with the
spatial one and the version independence are standard derivations recorded in the source audit
they are not displayed in GMP. -/
def QuenchedDriftMartingaleStep : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P' : DiffusionFamily d),
    IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      ∀ (hQ : IsStationary (reducedReferenceLaw Q)) (i : Fin d) (divA : FieldPair d → ℝ),
        HasWeakHorizontalDivergence (reducedReferenceLaw Q) hQ
          (fun ω : FieldPair d => (ω.1 0).mulVec (unitVector i)) divA →
        ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂Q.measure,
          MemLp (fun γ => driftMartingalePart (velocityDrift hd lam i divA) i t (ω, γ)) 2
              (P' lam (0, ω)) ∧
            ∫ γ, driftMartingalePart (velocityDrift hd lam i divA) i t (ω, γ) ^ 2
              ∂(P' lam (0, ω)) ≤ C * t

/-- `DriftDecompositionStep` from `DriftBoundStep` and `QuenchedDriftMartingaleStep`: the quenched
second moment bound integrates to the annealed one. -/
theorem driftDecompositionStep_of_steps (hBd : DriftBoundStep)
    (hQM : QuenchedDriftMartingaleStep) : DriftDecompositionStep := by
  intro d hd Λ₀ r₀ Q P' hP' lam hlam hlam1 hQ i divA hdiv origin_probability
  obtain ⟨B, hB⟩ := hBd d hd Λ₀ r₀ Q lam hlam hlam1 hQ i divA hdiv
  obtain ⟨C, hC⟩ := hQM d hd Λ₀ r₀ Q P' hP' lam hlam hlam1 hQ i divA hdiv
  refine ⟨B, C, hB, fun t ht => ?_⟩
  set K := originLaw (P' lam)
  set J := annealedCoordinateJoint Q.measure (P' lam) origin_probability with hJ
  haveI : IsProbabilityMeasure J :=
    Density.isProbabilityMeasure_annealedCoordinateJoint Q.measure (P' lam) origin_probability
  have hGMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hlam.le hlam1 K :=
    hP' lam hlam.le hlam1
  -- A bounded measurable version `bt` of the drift, and the corresponding martingale part.
  have hentry : Continuous fun ω : FieldPair d => (ω.1 0) (firstIdx hd) i :=
    (continuous_apply i).comp ((continuous_apply (firstIdx hd)).comp
      ((continuous_eval_const (0 : Vec d)).comp continuous_fst))
  have hbm : AEStronglyMeasurable (velocityDrift hd lam i divA) (reducedReferenceLaw Q) :=
    (hdiv.2.1.aestronglyMeasurable.const_mul _).add (hentry.aestronglyMeasurable.const_mul lam)
  obtain ⟨bt, hbt, -, hbbt⟩ := exists_bounded_measurable_version hbm hB
  set M := driftMartingalePart (velocityDrift hd lam i divA) i t with hMdef
  set Mt := driftMartingalePart bt i t with hMtdef
  have hMtm : Measurable Mt := by
    have hc : Continuous fun z : FieldPair d × Path d => z.2 t.toNNReal i :=
      (continuous_apply i).comp ((continuous_eval_const t.toNNReal).comp continuous_snd)
    exact hc.measurable.sub (measurable_intervalIntegral_observation hbt t)
  have hMMt : M =ᵐ[J] Mt := by
    filter_upwards [ae_intervalIntegral_observation_eq hd Q hlam.le hlam1 (P' lam)
      origin_probability hGMP hbbt ht] with z hz
    simp only [hMdef, hMtdef, driftMartingalePart]
    rw [hz]
  -- The annealed null set of `{M ≠ Mt}` is quenched null for almost every environment.
  set Kp := Probability.probabilityPart K
  have hKae := Probability.probabilityPart_ae_eq Q.measure K origin_probability
  have hquench : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' lam (0, ω)), M (ω, γ) = Mt (ω, γ) := by
    set N := toMeasurable J {z | M z ≠ Mt z}
    have hN : MeasurableSet N := measurableSet_toMeasurable _ _
    have hN0 : J N = 0 := by rw [measure_toMeasurable]; exact hMMt
    have hmass := Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_lintegral
      Q.measure K origin_probability (N.indicator 1) (measurable_one.indicator hN)
    have hJN : J N = ∫⁻ ω, ∫⁻ γ, N.indicator 1 (ω, γ) ∂Kp ω ∂Q.measure := by
      rw [← lintegral_indicator_one hN, hJ]
      unfold annealedCoordinateJoint
      rw [hmass]
      refine lintegral_congr_ae ?_
      filter_upwards [hKae] with ω hω
      rw [hω]
    have hmeas : Measurable fun ω => ∫⁻ γ, N.indicator 1 (ω, γ) ∂Kp ω :=
      Measurable.lintegral_kernel_prod_right' (κ := Kp) (measurable_one.indicator hN)
    rw [hN0, eq_comm, lintegral_eq_zero_iff hmeas] at hJN
    filter_upwards [hJN, hKae] with ω hω hKω
    have hω' : (∫⁻ γ, N.indicator 1 (ω, γ) ∂K ω) = 0 := by rw [← hKω]; exact hω
    have hω'' : ∫⁻ γ, (Prod.mk ω ⁻¹' N).indicator 1 γ ∂K ω = 0 := hω'
    rw [lintegral_indicator_one (measurable_prodMk_left hN)] at hω''
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hω''] with γ hγ
    by_contra hne
    exact hγ (subset_toMeasurable _ _ hne)
  -- `C t ≥ 0`, since a second moment is nonnegative.
  have hCt : 0 ≤ C * t := by
    obtain ⟨ω, hω⟩ := (hC t ht).exists
    exact (integral_nonneg fun γ => sq_nonneg _).trans hω.2
  -- Quenched lower integrals of `Mt²`.
  have hq : ∀ᵐ ω ∂Q.measure,
      ∫⁻ γ, ENNReal.ofReal (Mt (ω, γ) ^ 2) ∂(P' lam (0, ω)) ≤ ENNReal.ofReal (C * t) := by
    filter_upwards [hC t ht, hquench] with ω hω hωq
    obtain ⟨hmem, hint⟩ := hω
    have hsq : Integrable (fun γ => M (ω, γ) ^ 2) (P' lam (0, ω)) := hmem.integrable_sq
    calc ∫⁻ γ, ENNReal.ofReal (Mt (ω, γ) ^ 2) ∂(P' lam (0, ω))
        = ∫⁻ γ, ENNReal.ofReal (M (ω, γ) ^ 2) ∂(P' lam (0, ω)) :=
          lintegral_congr_ae (hωq.mono fun γ h => by simp only [h])
      _ = ENNReal.ofReal (∫ γ, M (ω, γ) ^ 2 ∂(P' lam (0, ω))) :=
          (ofReal_integral_eq_lintegral_ofReal hsq (ae_of_all _ fun γ => sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal (C * t) := ENNReal.ofReal_le_ofReal hint
  -- The annealed lower integral of `Mt²`.
  have hMt2m : Measurable fun z => Mt z ^ 2 := hMtm.pow_const 2
  have hann : ∫⁻ z, ENNReal.ofReal (Mt z ^ 2) ∂J ≤ ENNReal.ofReal (C * t) := by
    rw [hJ]
    unfold annealedCoordinateJoint
    rw [Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_lintegral
      Q.measure K origin_probability (fun z => ENNReal.ofReal (Mt z ^ 2))
      (ENNReal.measurable_ofReal.comp hMt2m)]
    calc ∫⁻ ω, ∫⁻ γ, ENNReal.ofReal (Mt (ω, γ) ^ 2) ∂K ω ∂Q.measure
        ≤ ∫⁻ _, ENNReal.ofReal (C * t) ∂Q.measure := lintegral_mono_ae hq
      _ = ENNReal.ofReal (C * t) := by simp
  have hMtsq : Integrable (fun z => Mt z ^ 2) J := by
    refine ⟨hMt2m.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg (Mt z))]
    exact hann.trans_lt ENNReal.ofReal_lt_top
  have hMtmem : MemLp Mt 2 J := (memLp_two_iff_integrable_sq hMtm.aestronglyMeasurable).mpr hMtsq
  have hMtint : ∫ z, Mt z ^ 2 ∂J ≤ C * t := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg (Mt z))
      hMt2m.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hCt hann
  refine ⟨hMtmem.ae_eq hMMt.symm, ?_⟩
  have hEq : ∫ z, M z ^ 2 ∂J = ∫ z, Mt z ^ 2 ∂J :=
    integral_congr_ae (hMMt.mono fun z h => by simp only [h])
  rw [hEq]
  exact hMtint

end EinsteinRelation
