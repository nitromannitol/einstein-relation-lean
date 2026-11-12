import EinsteinRelation.Mobility.VelocityRateFromSteps
import EinsteinRelation.Correctors.ScalarDecompositionGlue
import EinsteinRelation.Calculus.WeakCalculusAlgebra
import EinsteinRelation.Mobility.VelocityAbelFromDecomposition
import EinsteinRelation.Mobility.DriftWeakDivergence
import EinsteinRelation.Mobility.DriftBoundStepProof
import EinsteinRelation.Mobility.AKMFluxDecaySplit
import EinsteinRelation.Carriers.RegenerationCorrectorTwins
import EinsteinRelation.Correctors.CorrectorAmplitude
import EinsteinRelation.Environment.MatrixNorm
import EinsteinRelation.Clock.ResolventRateLimit
import EinsteinRelation.Mobility.ClockEstimateFromSteps

/-! # The velocity resolvent rate

Source: `paper/main.tex` 1102-1147, the proof of `eq.velocity-resolvent-rate`.
`velocityResolventRateStep_of_steps` proves `VelocityResolventRateStep` from these premises:
- Proposition 5.3 with the corrector gradient localized (`CorrectorLocalConstruction`);
- Proposition 6.1 (`ScalarDecompositionTwin`);
- Lemma 4.3 (`Entropy.ResolventStatement`);
- the gradient part of Lemma 4.1 (`Correctors.FisherBoundStatement`);
- the AKM flux decay (`AKMFluxDecay`);
- the gradient moments of Lemma 5.1 (`CorrectorGradientMoments`).

The argument follows the paper:

* `satisfiesReducedGeneratorEquation_localCorrector`: the local flux equation of Proposition 5.3,
  a skew-symmetric divergence form, gives `b_i^λ + L^λ φ_{i,R} = λ ā_{1i} + λ f_R + ½ D·F_{i,R}`
  weakly, with `f_R = e₁·a(e_i + Dφ_{i,R}) - ā_{1i}` (`localFluxFirst`).
* `localDiv`: a version of `D·(a e_i)` that depends only on the coefficient near the origin, so that
  Lemma 4.3 applies to the source term; any other version agrees with it almost surely.
* `isScalarAveragingField_localFluxFirst`: `f_R` satisfies the averaging assumption, by the AKM flux
  decay and the local-corrector error.
* Lemma 4.3 bounds `E[ρ_s(-b_i + λ ā + λ f_R)]` by `C s ‖φ_{i,R}‖ + C λ ‖F_{i,R}‖`. The response
  bound of Proposition 6.1 bounds `λ E[ρ_s f_R]`. With `R ≍ λ⁻¹`, both give
  `|E[ρ_s b_i^λ] - λ ā_{1i}| ≤ C λ² + C s K`.

`satisfiesReducedGeneratorEquation_lam_of_zero` is the force-`λ` equation for the corrected function
of Proposition 6.1, from its force-zero equation; the assembly above does not need it.
-/

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace

noncomputable section

namespace EinsteinRelation

variable {d : ℕ}

/-! ## Zero mean of horizontal derivatives -/

/-- The `L²` horizontal derivative of an `L²` function has mean zero under a stationary probability
law. -/
theorem integral_eq_zero_of_hasHorizontalLpDerivative {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} {j : Fin d} {F G : Lp ℝ 2 Q}
    (hG : HasHorizontalLpDerivative Q hQ j F G) : ∫ ω, G ω ∂Q = 0 := by
  set one : Lp ℝ 2 Q := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top Q _) (1 : ℝ)
  have hone : ∀ g : Lp ℝ 2 Q, ⟪one, g⟫_ℝ = ∫ ω, g ω ∂Q := by
    intro g
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := Q) (s := Set.univ)
      (hs := MeasurableSet.univ) (hμs := measure_ne_top Q _) (c := (1 : ℝ))] with ω hω
    simp only [one, hω, Set.indicator_univ]
    simp
  have htrans : ∀ x : Vec d, ∫ ω, translationLp Q hQ x F ω ∂Q = ∫ ω, F ω ∂Q := by
    intro x
    rw [integral_congr_ae (coeFn_translationLp Q hQ x F)]
    have hmp := measurePreserving_translate Q hQ x
    have hF' : AEStronglyMeasurable (fun ω => F ω) (Measure.map (translate x) Q) := by
      rw [hmp.map_eq]
      exact Lp.aestronglyMeasurable F
    rw [← integral_map hmp.measurable.aemeasurable hF', hmp.map_eq]
  have hzero : ∀ t : ℝ, ⟪one, t⁻¹ • (translationLp Q hQ (t • unitVector j) F - F)⟫_ℝ = 0 := by
    intro t
    rw [inner_smul_right, inner_sub_right, hone, hone, htrans, sub_self, mul_zero]
  have hlim : Tendsto (fun t : ℝ => ⟪one, t⁻¹ • (translationLp Q hQ (t • unitVector j) F - F)⟫_ℝ)
      (𝓝[≠] (0 : ℝ)) (𝓝 ⟪one, G⟫_ℝ) :=
    (continuous_const.inner continuous_id).continuousAt.tendsto.comp hG
  simp only [hzero] at hlim
  rw [← hone]
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-! ## The generator equation at force `λ` from force `0` -/

/-- The generator equation `L⁰ψ = h₀ + D·G₀` and the weak divergence `D·P = (a e_{i₁})·Dψ - h` give
`L^λ ψ = (h₀ + λ h) + D·(G₀ + λ P)`. -/
theorem satisfiesReducedGeneratorEquation_lam_of_zero {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} {i₁ : Fin d} (lam : ℝ)
    (hA : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ i j : Fin d, |ω.1 0 i j| ≤ C)
    {ψ h₀ h : FieldPair d → ℝ} {Dψ G₀ P : FieldPair d → Vec d}
    (h0 : SatisfiesReducedGeneratorEquation Q hQ 0 ψ Dψ h₀ G₀ i₁)
    (hP : HasWeakHorizontalDivergence Q hQ P
      (fun ω => dot ((ω.1 0).mulVec (unitVector i₁)) (Dψ ω) - h ω))
    (hh : Integrable h Q) :
    SatisfiesReducedGeneratorEquation Q hQ lam ψ Dψ (fun ω => h₀ ω + lam * h ω)
      (fun ω => G₀ ω + lam • P ω) i₁ := by
  obtain ⟨C, hC⟩ := hA
  obtain ⟨hw, hh₀, hG₀, he₀⟩ := h0
  obtain ⟨hPint, hdint, hPdiv⟩ := hP
  refine ⟨hw, hh₀.add (hh.const_mul lam), fun i => (hG₀ i).add ((hPint i).const_mul lam),
    fun F hF DF hDF => ?_⟩
  obtain ⟨M, hM⟩ := ae_bound_of_isHorizontallySmoothTest hF
  have he := he₀ F hF DF hDF
  have hdv := hPdiv F hF DF hDF
  have hcol : ∀ ω, dot ((ω.1 0).mulVec (unitVector i₁)) (Dψ ω) =
      ∑ j : Fin d, (ω.1 0) j i₁ * Dψ ω j := fun ω => by
    simp [dot, unitVector]
  have hIs : Integrable (fun ω => F ω * ∑ j : Fin d, (ω.1 0) j i₁ * Dψ ω j) Q :=
    integrable_scalar_flux i₁ hC hM hw.2.1
  have hIh : Integrable (fun ω => h ω * F ω) Q := integrable_mul_of_ae_bound hh hM
  have hIh₀ : Integrable (fun ω => h₀ ω * F ω) Q := integrable_mul_of_ae_bound hh₀ hM
  have hIG : Integrable (fun ω => ∑ i : Fin d, G₀ ω i * DF i ω) Q :=
    integrable_sum_mul_derivative hG₀ hF hDF
  have hIP : Integrable (fun ω => ∑ i : Fin d, P ω i * DF i ω) Q :=
    integrable_sum_mul_derivative hPint hF hDF
  -- `∫ F (a e_{i₁})·Dψ = ∫ h F - ∫ P·DF`.
  have hkey : ∫ ω, F ω * (∑ j : Fin d, (ω.1 0) j i₁ * Dψ ω j) ∂Q =
      (∫ ω, h ω * F ω ∂Q) - ∫ ω, (∑ i : Fin d, P ω i * DF i ω) ∂Q := by
    have h1 : ∫ ω, (dot ((ω.1 0).mulVec (unitVector i₁)) (Dψ ω) - h ω) * F ω ∂Q =
        (∫ ω, F ω * (∑ j : Fin d, (ω.1 0) j i₁ * Dψ ω j) ∂Q) - ∫ ω, h ω * F ω ∂Q := by
      rw [← integral_sub hIs hIh]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only [hcol]
      ring
    linarith
  have hsplitH : ∫ ω, (h₀ ω + lam * h ω) * F ω ∂Q =
      (∫ ω, h₀ ω * F ω ∂Q) + lam * ∫ ω, h ω * F ω ∂Q := by
    rw [← integral_const_mul, ← integral_add hIh₀ (hIh.const_mul lam)]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  have hsplitG : ∫ ω, (∑ i : Fin d, (G₀ ω + lam • P ω) i * DF i ω) ∂Q =
      (∫ ω, (∑ i : Fin d, G₀ ω i * DF i ω) ∂Q) + lam * ∫ ω, (∑ i : Fin d, P ω i * DF i ω) ∂Q := by
    rw [← integral_const_mul, ← integral_add hIG (hIP.const_mul lam)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplitH, hsplitG, hkey]
  have he' : -(1 / 2 : ℝ) * (∫ ω, (∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j * Dψ ω j) ∂Q) =
      (∫ ω, h₀ ω * F ω ∂Q) - ∫ ω, (∑ i : Fin d, G₀ ω i * DF i ω) ∂Q := by
    simpa using he
  linarith

/-! ## The generator equation of the local corrector -/

/-- A skew-symmetric matrix paired entrywise with a symmetric one gives zero. -/
theorem sum_sum_skew_mul_symm (S H : Fin d → Fin d → ℝ) (hS : ∀ j k, S j k = -S k j)
    (hH : ∀ j k, H j k = H k j) : ∑ j, ∑ k, S j k * H j k = 0 := by
  have h : ∑ j, ∑ k, S j k * H j k = -∑ j, ∑ k, S j k * H j k := by
    calc ∑ j, ∑ k, S j k * H j k = ∑ j, ∑ k, -(S k j * H k j) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
            rw [hS j k, hH j k]; ring
      _ = -∑ k, ∑ j, S k j * H k j := by
          rw [Finset.sum_comm]; simp only [Finset.sum_neg_distrib]
      _ = -∑ j, ∑ k, S j k * H j k := rfl
  linarith

/-- Second horizontal derivatives of a horizontally smooth test exist. -/
theorem exists_second_hasHorizontalLpDerivative {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {F : Lp ℝ 2 Q} (hF : IsHorizontallySmoothTest Q hQ F) {DF : Fin d → Lp ℝ 2 Q}
    (hDF : ∀ i, HasHorizontalLpDerivative Q hQ i F (DF i)) (j k : Fin d) :
    ∃ H : Lp ℝ 2 Q, HasHorizontalLpDerivative Q hQ k (DF j) H := by
  obtain ⟨G, hG, -⟩ := hF [k, j]
  obtain ⟨h1, hIter, hk⟩ := hG
  obtain ⟨h0, hIter0, hj⟩ := hIter
  have h0F : h0 = F := hIter0
  rw [h0F] at hj
  have h1D : h1 = DF j := HasHorizontalLpDerivative.unique hj (hDF j)
  rw [h1D] at hk
  exact ⟨G, hk⟩

/-- **The generator equation of the local corrector.** If `a(e_i + Dφ) - c - F = D·S` row by row
for a skew-symmetric `S` (the local flux equation of Proposition 5.3, with `c = ā e_i`), and `divA`
is the weak divergence of `a e_i`, then `L^λ φ = h + D·(½ F)` with
`h = -b_i^λ + λ e₁·a(e_i + Dφ)` and `b_i^λ = ½ divA + λ a_{1i}`. -/
theorem satisfiesReducedGeneratorEquation_localCorrector {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} (hd : 2 ≤ d) (lam : ℝ) (i : Fin d)
    (hA : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ j k : Fin d, |ω.1 0 j k| ≤ C)
    (hsym : ∀ᵐ ω ∂Q, ∀ j k : Fin d, ω.1 0 j k = ω.1 0 k j)
    {φ divA : FieldPair d → ℝ} {S : FieldPair d → Mat d} {flux Dφ : FieldPair d → Vec d}
    (c : Vec d) (hskew : ∀ ω, (S ω).transpose = -(S ω))
    (hgrad : HasWeakHorizontalGradient Q hQ φ Dφ)
    (hdivS : ∀ j, HasWeakHorizontalDivergence Q hQ (fun ω k => S ω j k)
      (fun ω => (∑ k, (ω.1 0) j k * (unitVector i k + Dφ ω k)) - c j - flux ω j))
    (hdivA : HasWeakHorizontalDivergence Q hQ (fun ω => (ω.1 0).mulVec (unitVector i)) divA)
    (hflux : ∀ j, Integrable (fun ω => flux ω j) Q) :
    SatisfiesReducedGeneratorEquation Q hQ lam φ Dφ
      (fun ω => -velocityDrift hd lam i divA ω +
        lam * ∑ k, (ω.1 0) (firstIdx hd) k * (unitVector i k + Dφ ω k))
      (fun ω => (1 / 2 : ℝ) • flux ω) (firstIdx hd) := by
  obtain ⟨C, hC⟩ := hA
  have hentry : ∀ j k : Fin d, Integrable (fun ω : FieldPair d => (ω.1 0) j k) Q := fun j k =>
    (integrable_const C).mono' (measurable_coeff_entry j k).aestronglyMeasurable
      (hC.mono fun ω hω => by rw [Real.norm_eq_abs]; exact hω j k)
  have hrowint : ∀ j : Fin d, Integrable
      (fun ω => ∑ k, (ω.1 0) j k * (unitVector i k + Dφ ω k)) Q := fun j =>
    integrable_finset_sum _ fun k _ =>
      ((integrable_const (unitVector i k)).add (hgrad.2.1 k)).bdd_mul
        (measurable_coeff_entry j k).aestronglyMeasurable
        (hC.mono fun ω hω => by rw [Real.norm_eq_abs]; exact hω j k)
  have hhint : Integrable (fun ω => -velocityDrift hd lam i divA ω +
      lam * ∑ k, (ω.1 0) (firstIdx hd) k * (unitVector i k + Dφ ω k)) Q := by
    unfold velocityDrift
    exact (((hdivA.2.1.const_mul (1 / 2)).add ((hentry (firstIdx hd) i).const_mul lam)).neg).add
      ((hrowint (firstIdx hd)).const_mul lam)
  refine ⟨hgrad, hhint, fun j => (hflux j).const_mul (1 / 2), fun F hF DF hDF => ?_⟩
  obtain ⟨M, hM⟩ := ae_bound_of_isHorizontallySmoothTest hF
  have hN : ∀ j, ∃ N : ℝ, ∀ᵐ ω ∂Q, |DF j ω| ≤ N := fun j =>
    ae_bound_of_hasHorizontalLpDerivative hF (hDF j)
  -- Second derivatives and their symmetry.
  choose H hH using exists_second_hasHorizontalLpDerivative hF hDF
  have hHsym : ∀ j k, H j k = H k j := fun j k =>
    horizontal_derivative_comm (hDF j) (hH j k) (hDF k) (hH k j)
  have hHae : ∀ᵐ ω ∂Q, ∀ j k, H j k ω = H k j ω := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro k
    rw [hHsym j k]
    exact ae_of_all _ fun _ => rfl
  -- The skew part vanishes after summing the rows.
  have hrows : ∀ j, ∫ ω, (∑ k, S ω j k * H j k ω) ∂Q =
      -∫ ω, ((∑ k, (ω.1 0) j k * (unitVector i k + Dφ ω k)) - c j - flux ω j) * DF j ω ∂Q :=
    fun j => (hdivS j).2.2 (DF j) (hF.derivative (hDF j)) (H j) (hH j)
  have hSint : ∀ j, Integrable (fun ω => ∑ k, S ω j k * H j k ω) Q := fun j =>
    integrable_finset_sum _ fun k _ => by
      obtain ⟨N, hNk⟩ := ae_bound_of_hasHorizontalLpDerivative (hF.derivative (hDF j)) (hH j k)
      exact integrable_mul_of_ae_bound ((hdivS j).1 k) hNk
  have hskew0 : ∫ ω, (∑ j, ∑ k, S ω j k * H j k ω) ∂Q = 0 := by
    rw [integral_congr_ae (hHae.mono fun ω hω => sum_sum_skew_mul_symm (fun j k => S ω j k)
      (fun j k => H j k ω) (fun j k => by
        have := congrFun (congrFun (hskew ω) k) j
        simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
        exact this) hω)]
    simp
  have hrowsum : ∑ j, ∫ ω, ((∑ k, (ω.1 0) j k * (unitVector i k + Dφ ω k)) - c j - flux ω j) *
      DF j ω ∂Q = 0 := by
    have h1 : ∑ j, ∫ ω, (∑ k, S ω j k * H j k ω) ∂Q = 0 := by
      rw [← integral_finset_sum _ fun j _ => hSint j]
      exact hskew0
    simp only [hrows, Finset.sum_neg_distrib, neg_eq_zero] at h1
    exact h1
  -- Split each row.
  have hDFint : ∀ j, Integrable (fun ω => DF j ω) Q := fun j =>
    (Lp.memLp (DF j)).integrable one_le_two
  have hzero : ∀ j, ∫ ω, DF j ω ∂Q = 0 := fun j =>
    integral_eq_zero_of_hasHorizontalLpDerivative (hDF j)
  set T := ∫ ω, (∑ j : Fin d, ∑ k : Fin d, DF j ω * (ω.1 0) j k * Dφ ω k) ∂Q with hT
  set Φ := ∫ ω, (∑ j : Fin d, flux ω j * DF j ω) ∂Q with hΦ
  have hIA := integrable_sum_mul_derivative (V := fun ω => (ω.1 0).mulVec (unitVector i))
    hdivA.1 hF hDF
  have hIT := integrable_double_sum_flux hC hN hgrad.2.1
  have hIΦ := integrable_sum_mul_derivative hflux hF hDF
  have hIc : Integrable (fun ω => ∑ j, c j * DF j ω) Q :=
    integrable_finset_sum _ fun j _ => (hDFint j).const_mul (c j)
  have hsplit : ∑ j, ∫ ω, ((∑ k, (ω.1 0) j k * (unitVector i k + Dφ ω k)) - c j - flux ω j) *
      DF j ω ∂Q =
      (∫ ω, (∑ j : Fin d, ((ω.1 0).mulVec (unitVector i)) j * DF j ω) ∂Q) + T -
        (∫ ω, (∑ j, c j * DF j ω) ∂Q) - Φ := by
    have hint : ∀ j, Integrable (fun ω =>
        ((∑ k, (ω.1 0) j k * (unitVector i k + Dφ ω k)) - c j - flux ω j) * DF j ω) Q := by
      intro j
      have hr : Integrable (fun ω => (∑ k, (ω.1 0) j k * (unitVector i k + Dφ ω k)) - c j -
          flux ω j) Q := ((hrowint j).sub (integrable_const (c j))).sub (hflux j)
      exact integrable_mul_of_ae_bound hr (hN j).choose_spec
    have hpt : ∀ ω, (∑ j, ((∑ k, (ω.1 0) j k * (unitVector i k + Dφ ω k)) - c j - flux ω j) *
        DF j ω) = (∑ j : Fin d, ((ω.1 0).mulVec (unitVector i)) j * DF j ω) +
          (∑ j : Fin d, ∑ k : Fin d, DF j ω * (ω.1 0) j k * Dφ ω k) - (∑ j, c j * DF j ω) -
          ∑ j : Fin d, flux ω j * DF j ω := by
      intro ω
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hmv : ((ω.1 0).mulVec (unitVector i)) j = ∑ k, (ω.1 0) j k * unitVector i k := rfl
      have e1 : ∑ k, (ω.1 0) j k * (unitVector i k + Dφ ω k) =
          (∑ k, (ω.1 0) j k * unitVector i k) + ∑ k, (ω.1 0) j k * Dφ ω k := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      have e2 : ∑ k, DF j ω * (ω.1 0) j k * Dφ ω k = DF j ω * ∑ k, (ω.1 0) j k * Dφ ω k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hmv, e1, e2]
      ring
    calc ∑ j, ∫ ω, ((∑ k, (ω.1 0) j k * (unitVector i k + Dφ ω k)) - c j - flux ω j) *
          DF j ω ∂Q
        = ∫ ω, (∑ j, ((∑ k, (ω.1 0) j k * (unitVector i k + Dφ ω k)) - c j - flux ω j) *
          DF j ω) ∂Q := (integral_finset_sum _ fun j _ => hint j).symm
      _ = ∫ ω, ((∑ j : Fin d, ((ω.1 0).mulVec (unitVector i)) j * DF j ω) +
          (∑ j : Fin d, ∑ k : Fin d, DF j ω * (ω.1 0) j k * Dφ ω k) - (∑ j, c j * DF j ω) -
          ∑ j : Fin d, flux ω j * DF j ω) ∂Q := integral_congr_ae (ae_of_all _ hpt)
      _ = _ := by
        have e3 : ∫ ω, ((∑ j : Fin d, ((ω.1 0).mulVec (unitVector i)) j * DF j ω) +
            (∑ j : Fin d, ∑ k : Fin d, DF j ω * (ω.1 0) j k * Dφ ω k) - (∑ j, c j * DF j ω) -
            ∑ j : Fin d, flux ω j * DF j ω) ∂Q =
            (∫ ω, ((∑ j : Fin d, ((ω.1 0).mulVec (unitVector i)) j * DF j ω) +
              (∑ j : Fin d, ∑ k : Fin d, DF j ω * (ω.1 0) j k * Dφ ω k) -
              (∑ j, c j * DF j ω)) ∂Q) - Φ :=
          integral_sub ((hIA.add hIT).sub hIc) hIΦ
        have e4 : ∫ ω, ((∑ j : Fin d, ((ω.1 0).mulVec (unitVector i)) j * DF j ω) +
              (∑ j : Fin d, ∑ k : Fin d, DF j ω * (ω.1 0) j k * Dφ ω k) -
              (∑ j, c j * DF j ω)) ∂Q =
            (∫ ω, ((∑ j : Fin d, ((ω.1 0).mulVec (unitVector i)) j * DF j ω) +
              (∑ j : Fin d, ∑ k : Fin d, DF j ω * (ω.1 0) j k * Dφ ω k)) ∂Q) -
              ∫ ω, (∑ j, c j * DF j ω) ∂Q :=
          integral_sub (hIA.add hIT) hIc
        have e5 : ∫ ω, ((∑ j : Fin d, ((ω.1 0).mulVec (unitVector i)) j * DF j ω) +
              (∑ j : Fin d, ∑ k : Fin d, DF j ω * (ω.1 0) j k * Dφ ω k)) ∂Q =
            (∫ ω, (∑ j : Fin d, ((ω.1 0).mulVec (unitVector i)) j * DF j ω) ∂Q) + T :=
          integral_add hIA hIT
        rw [e3, e4, e5]
  have hcz : ∫ ω, (∑ j, c j * DF j ω) ∂Q = 0 := by
    rw [integral_finset_sum _ fun j _ => (hDFint j).const_mul (c j)]
    simp [integral_const_mul, hzero]
  have hA_eq : ∫ ω, (∑ j : Fin d, ((ω.1 0).mulVec (unitVector i)) j * DF j ω) ∂Q =
      -∫ ω, divA ω * F ω ∂Q := hdivA.2.2 F hF DF hDF
  have hTeq : T = Φ + ∫ ω, divA ω * F ω ∂Q := by
    have := hrowsum
    rw [hsplit, hA_eq, hcz] at this
    linarith
  -- The right-hand side of the generator equation.
  have hIdF := integrable_mul_of_ae_bound hdivA.2.1 hM
  have hIB := integrable_scalar_flux (firstIdx hd) hC hM hgrad.2.1
  have hhF : ∫ ω, (-velocityDrift hd lam i divA ω +
      lam * ∑ k, (ω.1 0) (firstIdx hd) k * (unitVector i k + Dφ ω k)) * F ω ∂Q =
      -(1 / 2 : ℝ) * (∫ ω, divA ω * F ω ∂Q) +
        lam * ∫ ω, F ω * (∑ j : Fin d, (ω.1 0) j (firstIdx hd) * Dφ ω j) ∂Q := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hIdF.const_mul _)
      (hIB.const_mul _)]
    refine integral_congr_ae (hsym.mono fun ω hω => ?_)
    unfold velocityDrift
    simp only [mul_add, Finset.sum_add_distrib, unitVector, Pi.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have : ∑ k, (ω.1 0) (firstIdx hd) k * Dφ ω k = ∑ k, (ω.1 0) k (firstIdx hd) * Dφ ω k :=
      Finset.sum_congr rfl fun k _ => by rw [hω]
    rw [this]
    generalize (∑ k, (ω.1 0) k (firstIdx hd) * Dφ ω k) = σ
    ring
  have hGF : ∫ ω, (∑ j : Fin d, ((1 / 2 : ℝ) • flux ω) j * DF j ω) ∂Q = (1 / 2 : ℝ) * Φ := by
    rw [hΦ, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hhF, hGF]
  rw [hTeq]
  ring

/-! ## A local version of the divergence of a coefficient column -/

private theorem vr_euclid_nonneg (x : Vec d) : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _

private theorem qd'_abs_coord_le_euclid (v : Vec d) (j : Fin d) : |v j| ≤ euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  have h := Finset.single_le_sum (f := fun k => v k * v k)
    (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
  simpa only [sq] using h

private theorem vr_euclid_smul (t : ℝ) (v : Vec d) :
    euclideanNorm (t • v) = |t| * euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  have h : ∑ j, (t • v) j * (t • v) j = (t * t) * ∑ j, v j * v j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, Real.sqrt_mul (mul_self_nonneg t), Real.sqrt_mul_self_eq_abs]

private theorem vr_euclid_unitVector (i : Fin d) : euclideanNorm (unitVector i) = 1 := by
  change Real.sqrt (dotProduct (Pi.single i (1 : ℝ)) (Pi.single i 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

/-- Evaluation of a field pair at a point of `U` is measurable for the local σ-algebra of `U`. -/
theorem measurable_eval_localSigma {U : Set (Vec d)} {x : Vec d} (hx : x ∈ U) :
    Measurable[localSigma U] fun ω : FieldPair d => (ω.1 x, ω.2 x) := by
  rw [measurable_iff_comap_le]
  exact le_iSup (fun y : U => MeasurableSpace.comap
    (fun ω : FieldPair d => (ω.1 y, ω.2 y)) inferInstance) ⟨x, hx⟩

theorem measurable_entry_localSigma {U : Set (Vec d)} {x : Vec d} (hx : x ∈ U) (j i : Fin d) :
    Measurable[localSigma U] fun ω : FieldPair d => ω.1 x j i := by
  have hc : Measurable fun p : Mat d × ℝ => p.1 j i :=
    (continuous_fst.matrix_elem j i).measurable
  exact hc.comp (measurable_eval_localSigma hx)

/-- The difference quotient of the divergence of column `i` at the origin with step `r/(n+2)`. -/
def divQuot (i : Fin d) (r : ℝ) (n : ℕ) (w : FieldPair d) : ℝ :=
  ∑ j, (r / ((n : ℝ) + 2))⁻¹ * (w.1 ((r / ((n : ℝ) + 2)) • unitVector j) j i - w.1 0 j i)

/-- The local divergence of column `i`: the upper limit of the difference quotients with steps
inside the ball of radius `r`. -/
def localDiv (i : Fin d) (r : ℝ) (w : FieldPair d) : ℝ :=
  Filter.limsup (fun n : ℕ => divQuot i r n w) atTop

theorem measurable_localDiv (i : Fin d) {r : ℝ} (hr : 0 < r) :
    Measurable[localSigma {y : Vec d | euclideanNorm y < r}] (localDiv i r) := by
  letI : MeasurableSpace (FieldPair d) := localSigma {y : Vec d | euclideanNorm y < r}
  refine Measurable.limsup fun n => ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hpt : (r / ((n : ℝ) + 2)) • unitVector j ∈ {y : Vec d | euclideanNorm y < r} := by
    simp only [Set.mem_setOf_eq]
    rw [vr_euclid_smul, vr_euclid_unitVector, mul_one, abs_of_pos (div_pos hr hn),
      div_lt_iff₀ hn]
    nlinarith
  have h0 : (0 : Vec d) ∈ {y : Vec d | euclideanNorm y < r} := by
    simp only [Set.mem_setOf_eq]
    rw [show (0 : Vec d) = (0 : ℝ) • unitVector j by simp, vr_euclid_smul]
    simpa using hr
  exact measurable_const.mul ((measurable_entry_localSigma hpt j i).sub
    (measurable_entry_localSigma h0 j i))

/-- Where every entry of the column is differentiable at the origin, the difference quotients
converge to the pointwise divergence. -/
theorem tendsto_divQuot (i : Fin d) {r : ℝ} (hr : 0 < r) {w : FieldPair d}
    (hw : ∀ j, DifferentiableAt ℝ (fun y => w.1 y j i) 0) :
    Tendsto (fun n : ℕ => divQuot i r n w) atTop (𝓝 (DriftH5.cdiv i w)) := by
  unfold DriftH5.cdiv divQuot
  refine tendsto_finset_sum _ fun j _ => ?_
  have ht : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      exact tendsto_const_nhds.div_atTop h2
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact (div_pos hr (by positivity)).ne'
  have hl : HasDerivAt (fun t : ℝ => t • unitVector j) (unitVector j) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (unitVector j)
  have hg : HasFDerivAt (fun y => w.1 y j i) (fderiv ℝ (fun y => w.1 y j i) 0)
      ((0 : ℝ) • unitVector j) := by
    rw [zero_smul]
    exact (hw j).hasFDerivAt
  have hd := hg.comp_hasDerivAt (0 : ℝ) hl
  have hs := hasDerivAt_iff_tendsto_slope_zero.mp hd
  refine (hs.comp ht).congr fun n => ?_
  simp only [Function.comp_apply, zero_add, zero_smul, smul_eq_mul]

/-- The local divergence agrees with the pointwise divergence almost surely. -/
theorem localDiv_ae_eq_cdiv {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) (i : Fin d) {r : ℝ} (hr : 0 < r) :
    localDiv i r =ᵐ[Carriers.reducedReferenceLaw Q] DriftH5.cdiv i := by
  have h := ae_all_iff.mpr fun j => DriftH5.ae_differentiableAt_reducedColumn Q hQ j i
  filter_upwards [h] with w hw
  exact (tendsto_divQuot i hr hw).limsup_eq

/-- Weak divergences are stable under almost-everywhere modification of the divergence. -/
theorem HasWeakHorizontalDivergence.congr_ae {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {V : FieldPair d → Vec d} {h h' : FieldPair d → ℝ}
    (hw : HasWeakHorizontalDivergence Q hQ V h) (hh : h =ᵐ[Q] h') :
    HasWeakHorizontalDivergence Q hQ V h' := by
  refine ⟨hw.1, hw.2.1.congr hh, fun F hF DF hDF => ?_⟩
  rw [hw.2.2 F hF DF hDF]
  congr 1
  exact integral_congr_ae (hh.mono fun ω hω => by simp only [hω])

/-- The local divergence is a weak horizontal divergence of the column `a e_i`. -/
theorem hasWeakHorizontalDivergence_localDiv {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) (i : Fin d) {r : ℝ} (hr : 0 < r) :
    HasWeakHorizontalDivergence (Carriers.reducedReferenceLaw Q) hQ
      (fun w : FieldPair d => (w.1 0).mulVec (unitVector i)) (localDiv i r) :=
  (DriftH5.hasWeakHorizontalDivergence_reducedColumn Q hQ i).congr_ae
    (localDiv_ae_eq_cdiv Q hQ i hr).symm

/-! ## Locality helpers -/

/-- The reduced coefficient observation σ-algebra of `U` is contained in the local σ-algebra. -/
theorem reducedCoefficientObservationSigma_le_localSigma (U : Set (Vec d)) :
    Carriers.reducedCoefficientObservationSigma U ≤ localSigma U :=
  iSup_le fun x => (measurable_fst.comp (measurable_eval_localSigma x.2)).comap_le

/-- Local σ-algebras of centred balls are monotone in the radius. -/
theorem localSigma_ball_mono {r r' : ℝ} (h : r ≤ r') :
    localSigma {y : Vec d | euclideanNorm (y - 0) < r} ≤
      localSigma {y : Vec d | euclideanNorm y < r'} :=
  Probability.localSigma_mono fun y hy => by
    simp only [Set.mem_setOf_eq, sub_zero] at hy ⊢
    linarith

/-- The reduced coefficient is symmetric almost surely. -/
theorem ae_symm_reducedReferenceLaw {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ w ∂Carriers.reducedReferenceLaw Q, ∀ j k : Fin d, w.1 0 j k = w.1 0 k j := by
  have hcont : ∀ j k : Fin d, Continuous fun w : FieldPair d => w.1 0 j k := fun j k =>
    ((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k
  have hmeas : MeasurableSet {w : FieldPair d | ∀ j k : Fin d, w.1 0 j k = w.1 0 k j} := by
    simp only [Set.setOf_forall]
    exact (isClosed_iInter fun j => isClosed_iInter fun k =>
      isClosed_eq (hcont j k) (hcont k j)).measurableSet
  unfold Carriers.reducedReferenceLaw
  refine (ae_map_iff (Probability.measurable_reduce (d := d)).aemeasurable hmeas).2 ?_
  filter_upwards [Q.regular] with η hη
  intro j k
  have h := reducedCoefficient_transpose η 0 ((hη.1 0).1)
  exact (congrFun (congrFun h j) k).symm

/-! ## The local flux as an averaging field -/

/-- The first component of the local flux minus its homogenized value,
`f_R = e₁·a(e_i + Dφ_{i,R}) - ā_{1i}` (`eq.velocity-local-flux`). -/
def localFluxFirst (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (grad : FieldPair d → Vec d) (w : FieldPair d) : ℝ :=
  (∑ k, (w.1 0) (firstIdx hd) k * (unitVector i k + grad w k)) -
    (Correctors.expectedCorrectorFlux Q i).ofLp (firstIdx hd)

/-- The canonical centred flux at the origin acts by the coefficient on `e_i + ∇φ_i`. -/
theorem ae_centredFluxFirst_eq (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) :
    ∀ᵐ w ∂Carriers.reducedReferenceLaw Q, centredFluxFirst hd Q i w =
      (∑ k, (w.1 0) (firstIdx hd) k * (unitVector i k +
        (Correctors.StationarySpatialRealization.spatialRealization
          (Correctors.canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
          ((0 : Vec d), w)).ofLp k)) -
        (Correctors.expectedCorrectorFlux Q i).ofLp (firstIdx hd) := by
  set G : Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q) :=
    (Correctors.canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
  filter_upwards [Correctors.reducedOriginCoefficientAction_coeFn Q
      (Correctors.correctorAffineField Q i + G),
    Lp.coeFn_add (Correctors.correctorAffineField Q i) G,
    Lp.coeFn_const (p := 2) (μ := Correctors.reducedEnvironmentLaw Q)
      (Correctors.correctorUnitVector i)] with w h1 h2 h3
  have hflux : Correctors.StationarySpatialRealization.spatialRealization
      (Correctors.canonicalCorrectorFlux Q i) ((0 : Vec d), w) =
      Correctors.reducedOriginCoefficientAction Q (Correctors.correctorAffineField Q i + G) w := by
    simp only [Correctors.StationarySpatialRealization.spatialRealization, translate_zero]
    rfl
  have hG : Correctors.StationarySpatialRealization.spatialRealization G ((0 : Vec d), w) = G w := by
    simp only [Correctors.StationarySpatialRealization.spatialRealization, translate_zero]
  unfold centredFluxFirst
  rw [hflux, h1, hG, h2]
  have haff : (Correctors.correctorAffineField Q i) w = Correctors.correctorUnitVector i := h3
  rw [Pi.add_apply, haff]
  simp only [Matrix.mulVec, dotProduct, Correctors.correctorUnitVector, WithLp.ofLp_add,
    Pi.add_apply, unitVector]

/-- **The local flux is an averaging field** (`paper/main.tex` 1111-1122): the AKM flux decay of
the centred flux and the local-corrector error `‖Dφ_{i,R} - ∇φ_i‖_{L^m} ≤ B_m R⁻¹` give
`IsScalarAveragingField` for `f_R` with constants `A_m + d K B_m`. -/
theorem isScalarAveragingField_localFluxFirst (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hQ : IsStationary (Carriers.reducedReferenceLaw Q))
    (i : Fin d) {R : ℝ} (hR : 0 < R) {grad : FieldPair d → Vec d}
    (hgradL : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 33 * R}] grad)
    {Ka : ℝ} (hKa0 : 0 ≤ Ka)
    (hKa : ∀ᵐ w ∂Carriers.reducedReferenceLaw Q, ∀ j k : Fin d, |w.1 0 j k| ≤ Ka)
    (A B : ℝ → ℝ) (hA0 : ∀ m : ℝ, 2 ≤ m → 0 ≤ A m) (hB0 : ∀ m : ℝ, 2 ≤ m → 0 ≤ B m)
    (hflux : ∀ m : ℝ, 2 ≤ m → ∀ t : ℝ, 0 ≤ t →
      eLpNorm (Correctors.heatSmoothed t (centredFluxFirst hd Q i)) (ENNReal.ofReal m)
        (Carriers.reducedReferenceLaw Q) ≤ ENNReal.ofReal (A m * (Real.sqrt (1 + t))⁻¹))
    (hgm : ∀ m : ℝ, 2 ≤ m →
      MemLp (centredFluxFirst hd Q i) (ENNReal.ofReal m) (Carriers.reducedReferenceLaw Q))
    (hgradm : ∀ m : ℝ, 2 ≤ m → MemLp (fun w => euclideanNorm (grad w)) (ENNReal.ofReal m)
      (Carriers.reducedReferenceLaw Q))
    (hdiff : ∀ m : ℝ, 2 ≤ m →
      eLpNorm (fun w : FieldPair d => euclideanNorm (fun j : Fin d => grad w j -
          (Correctors.StationarySpatialRealization.spatialRealization
            (Correctors.canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
            ((0 : Vec d), w)).ofLp j))
        (ENNReal.ofReal m) (Carriers.reducedReferenceLaw Q) ≤ ENNReal.ofReal (B m * R⁻¹)) :
    Carriers.IsScalarAveragingField Q (fun m => A m + d * Ka * B m) R
      (localFluxFirst hd Q i grad) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    Entropy.reducedReferenceLaw_isProbabilityMeasure Q
  set μ := Carriers.reducedReferenceLaw Q
  set U : Set (Vec d) := {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 33 * R}
  have h0U : (0 : Vec d) ∈ U := by
    simp only [U, Set.mem_setOf_eq, sub_zero]
    rw [show (0 : Vec d) = (0 : ℝ) • unitVector i by simp, vr_euclid_smul]
    simp only [abs_zero, zero_mul]
    positivity
  have hfL : Measurable[localSigma U] (localFluxFirst hd Q i grad) := by
    letI : MeasurableSpace (FieldPair d) := localSigma U
    unfold localFluxFirst
    refine (Finset.measurable_sum _ fun k _ => ?_).sub measurable_const
    exact (measurable_entry_localSigma h0U (firstIdx hd) k).mul
      (measurable_const.add ((measurable_pi_apply k).comp hgradL))
  have hf : Measurable (localFluxFirst hd Q i grad) :=
    hfL.mono (Probability.localSigma_le_borel U) le_rfl
  have hg := measurable_centredFluxFirst hd Q i
  -- `|f_R| ≤ d K (1 + |Dφ|) + |ā_{1i}|`.
  have habs : ∀ v : Vec d, ∀ w : FieldPair d, (∀ j k : Fin d, |w.1 0 j k| ≤ Ka) →
      |∑ k, (w.1 0) (firstIdx hd) k * v k| ≤ d * Ka * euclideanNorm v := by
    intro v w hw
    calc |∑ k, (w.1 0) (firstIdx hd) k * v k| ≤ ∑ k, |(w.1 0) (firstIdx hd) k * v k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin d, Ka * euclideanNorm v := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact mul_le_mul (hw _ k) (qd'_abs_coord_le_euclid v k) (abs_nonneg _) hKa0
      _ = d * Ka * euclideanNorm v := by simp; ring
  have hfm : ∀ m : ℝ, 2 ≤ m → MemLp (localFluxFirst hd Q i grad) (ENNReal.ofReal m) μ := by
    intro m hm
    have h1 : MemLp (fun _ : FieldPair d => (1 : ℝ)) (ENNReal.ofReal m) μ := memLp_const 1
    have h2 : MemLp (fun w => (1 : ℝ) + euclideanNorm (grad w)) (ENNReal.ofReal m) μ :=
      h1.add (hgradm m hm)
    have h3 : MemLp (fun w => (d : ℝ) * Ka * (1 + euclideanNorm (grad w))) (ENNReal.ofReal m) μ :=
      h2.const_mul _
    have h4 : MemLp (fun _ : FieldPair d =>
        |(Correctors.expectedCorrectorFlux Q i).ofLp (firstIdx hd)|) (ENNReal.ofReal m) μ :=
      memLp_const _
    have hbound : MemLp (fun w => (d : ℝ) * Ka * (1 + euclideanNorm (grad w)) +
        |(Correctors.expectedCorrectorFlux Q i).ofLp (firstIdx hd)|) (ENNReal.ofReal m) μ :=
      h3.add h4
    refine hbound.mono hf.aestronglyMeasurable (hKa.mono fun w hw => ?_)
    have hsum : euclideanNorm (fun k => unitVector i k + grad w k) ≤ 1 + euclideanNorm (grad w) := by
      have := TimeChange.euclideanNorm_add_le (unitVector i) (grad w)
      rwa [vr_euclid_unitVector] at this
    have h1 := habs (fun k => unitVector i k + grad w k) w hw
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    unfold localFluxFirst
    have hnn : 0 ≤ d * Ka * (1 + euclideanNorm (grad w)) +
        |(Correctors.expectedCorrectorFlux Q i).ofLp (firstIdx hd)| := by
      have := vr_euclid_nonneg (grad w)
      exact add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hKa0) (by linarith))
        (abs_nonneg _)
    rw [abs_of_nonneg hnn]
    calc |(∑ k, (w.1 0) (firstIdx hd) k * (unitVector i k + grad w k)) -
          (Correctors.expectedCorrectorFlux Q i).ofLp (firstIdx hd)|
        ≤ |∑ k, (w.1 0) (firstIdx hd) k * (unitVector i k + grad w k)| +
          |(Correctors.expectedCorrectorFlux Q i).ofLp (firstIdx hd)| := abs_sub _ _
      _ ≤ d * Ka * (1 + euclideanNorm (grad w)) +
          |(Correctors.expectedCorrectorFlux Q i).ofLp (firstIdx hd)| := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left hsum
            (mul_nonneg (Nat.cast_nonneg _) hKa0))
  have hdK : (0 : ℝ) ≤ d * Ka := mul_nonneg (Nat.cast_nonneg _) hKa0
  have happrox : ∀ m : ℝ, 2 ≤ m → eLpNorm (localFluxFirst hd Q i grad - centredFluxFirst hd Q i)
      (ENNReal.ofReal m) μ ≤ ENNReal.ofReal (d * Ka * B m * R⁻¹) := by
    intro m hm
    set Ev : FieldPair d → ℝ := fun w => euclideanNorm (fun j : Fin d => grad w j -
          (Correctors.StationarySpatialRealization.spatialRealization
            (Correctors.canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
            ((0 : Vec d), w)).ofLp j) with hEv
    have hpt : ∀ᵐ w ∂μ, ‖(localFluxFirst hd Q i grad - centredFluxFirst hd Q i) w‖ ≤
        ‖((d : ℝ) * Ka) • Ev w‖ := by
      filter_upwards [ae_centredFluxFirst_eq hd Q i, hKa] with w hw hK
      have hE0 : 0 ≤ ((d : ℝ) * Ka) • Ev w := mul_nonneg hdK (vr_euclid_nonneg _)
      rw [Pi.sub_apply, hw, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hE0, smul_eq_mul]
      unfold localFluxFirst
      have hdiffsum : (∑ k, (w.1 0) (firstIdx hd) k * (unitVector i k + grad w k)) -
          (Correctors.expectedCorrectorFlux Q i).ofLp (firstIdx hd) -
          ((∑ k, (w.1 0) (firstIdx hd) k * (unitVector i k +
            (Correctors.StationarySpatialRealization.spatialRealization
              (Correctors.canonicalCorrectorGradient Q i :
                Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
              ((0 : Vec d), w)).ofLp k)) -
            (Correctors.expectedCorrectorFlux Q i).ofLp (firstIdx hd)) =
          ∑ k, (w.1 0) (firstIdx hd) k * (grad w k -
            (Correctors.StationarySpatialRealization.spatialRealization
              (Correctors.canonicalCorrectorGradient Q i :
                Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
              ((0 : Vec d), w)).ofLp k) := by
        rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hdiffsum]
      exact habs (fun k => grad w k -
            (Correctors.StationarySpatialRealization.spatialRealization
              (Correctors.canonicalCorrectorGradient Q i :
                Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
              ((0 : Vec d), w)).ofLp k) w hK
    have hc : ‖(d : ℝ) * Ka‖ₑ = ENNReal.ofReal (d * Ka) := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hdK]
    calc eLpNorm (localFluxFirst hd Q i grad - centredFluxFirst hd Q i) (ENNReal.ofReal m) μ
        ≤ eLpNorm (((d : ℝ) * Ka) • Ev) (ENNReal.ofReal m) μ := eLpNorm_mono_ae hpt
      _ ≤ ‖(d : ℝ) * Ka‖ₑ * eLpNorm Ev (ENNReal.ofReal m) μ := eLpNorm_const_smul_le
      _ ≤ ENNReal.ofReal (d * Ka) * ENNReal.ofReal (B m * R⁻¹) := by
          rw [hc]; gcongr; exact hdiff m hm
      _ = ENNReal.ofReal (d * Ka * B m * R⁻¹) := by
          rw [← ENNReal.ofReal_mul hdK]
          ring_nf
  exact isScalarAveragingField_of_flux_approx Q hQ (fun m => A m + d * Ka * B m) A
    (fun m => d * Ka * B m) hR hfL hf hg (fun m _ => rfl) hA0
    (fun m hm => mul_nonneg hdK (hB0 m hm)) hfm hgm hflux happrox

/-! ## Helpers for the assembly -/

/-- A bound `ofReal x ≤ ofReal a * A + ofReal b * B` with finite `A, B` and `a, b ≥ 0` gives the
real bound `x ≤ a A + b B`. -/
theorem le_of_ofReal_le_add_mul {x a b : ℝ} {A B : ℝ≥0∞} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (h : ENNReal.ofReal x ≤ ENNReal.ofReal a * A + ENNReal.ofReal b * B) :
    x ≤ a * A.toReal + b * B.toReal := by
  have hrhs : ENNReal.ofReal a * A + ENNReal.ofReal b * B =
      ENNReal.ofReal (a * A.toReal + b * B.toReal) := by
    rw [ENNReal.ofReal_add (mul_nonneg ha ENNReal.toReal_nonneg)
      (mul_nonneg hb ENNReal.toReal_nonneg), ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb,
      ENNReal.ofReal_toReal hA, ENNReal.ofReal_toReal hB]
  rw [hrhs] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- A reduced Laplace density integrates to one against the reduced law. -/
theorem integral_rho_eq_one {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (P : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)) (s : {r : ℝ // 0 < r})
    {rho : FieldPair d → ℝ} (hrho : Carriers.IsReducedLaplaceDensity Q.measure P hprob s rho) :
    ∫ w, rho w ∂(Carriers.reducedReferenceLaw Q) = 1 ∧
      Integrable rho (Carriers.reducedReferenceLaw Q) := by
  obtain ⟨hm, hnn, hlaw⟩ := hrho
  haveI := laplaceDensity_isProbabilityMeasure_observed Q P hprob s
  have hone : ∫⁻ w, ENNReal.ofReal (rho w) ∂(Carriers.reducedReferenceLaw Q) = 1 := by
    have h := measure_univ (μ := Carriers.reducedLaplaceObservedLaw Q.measure P hprob s)
    rw [hlaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  have hint : Integrable rho (Carriers.reducedReferenceLaw Q) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn), hone]
    exact ENNReal.one_lt_top
  refine ⟨?_, hint⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hm.aestronglyMeasurable, hone]
  simp

/-- The canonical corrector gradient at the origin is in every `L^m`, by Lemma 5.1. -/
theorem memLp_canonicalGradient (H51 : CorrectorGradientMoments) (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) {m : ℝ} (hm : 2 ≤ m) :
    MemLp (fun w : FieldPair d => euclideanNorm
        (Correctors.StationarySpatialRealization.spatialRealization
          (Correctors.canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
          ((0 : Vec d), w)).ofLp)
      (ENNReal.ofReal m) (Carriers.reducedReferenceLaw Q) := by
  obtain ⟨C, hC⟩ := H51 d hd Λ₀ r₀ m hm
  have hm0 : 0 < m := by linarith
  have hmeas : Measurable (fun w : FieldPair d => euclideanNorm
        (Correctors.StationarySpatialRealization.spatialRealization
          (Correctors.canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
          ((0 : Vec d), w)).ofLp) := by
    have h1 := (Correctors.StationarySpatialRealization.measurable_spatialRealization
      (Correctors.canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))).comp
      ((measurable_const (a := (0 : Vec d))).prodMk measurable_id)
    have hc : Continuous fun x : EuclideanSpace ℝ (Fin d) => euclideanNorm x.ofLp := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    exact hc.measurable.comp h1
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_pos.mpr hm0).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hm0.le]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt ?_)
  refine lt_of_le_of_lt (le_of_eq ?_) ((hC Q i).trans_lt ENNReal.ofReal_lt_top)
  refine lintegral_congr fun w => ?_
  rw [Real.enorm_of_nonneg (vr_euclid_nonneg _), ENNReal.ofReal_rpow_of_nonneg
    (vr_euclid_nonneg _) hm0.le]

/-- The final arithmetic of `eq.velocity-resolvent-rate`. -/
theorem abs_sub_le_of_resolvent_response {X Y Z lam s R ab C43 C61 Nφ NG l C0 B : ℝ}
    (hZ : Z = -X + lam * ab + lam * Y) (hZb : |Z| ≤ C43 * s * Nφ + C43 * lam * NG)
    (hY : |Y| ≤ C61 * (s * R + lam + lam ^ 2 * R + R⁻¹)) (hNG : NG ≤ (1 / 2) * B * R⁻¹)
    (hRinv : R⁻¹ ≤ 4 * C0 * lam / l) (hlamR : lam * R ≤ l / (2 * C0))
    (hlam : 0 ≤ lam) (hs : 0 ≤ s) (hC43 : 0 ≤ C43) (hC61 : 0 ≤ C61) (hB : 0 ≤ B) (hl : 0 < l)
    (hC0 : 0 < C0) :
    |X - lam * ab| ≤ (2 * C43 * B * C0 / l + C61 * (1 + l / (2 * C0) + 4 * C0 / l)) * lam ^ 2 +
      s * (C43 * Nφ + C61 * (l / (2 * C0))) := by
  have h1 : |X - lam * ab| ≤ lam * |Y| + |Z| := by
    rw [show X - lam * ab = lam * Y - Z by linarith]
    calc |lam * Y - Z| ≤ |lam * Y| + |Z| := abs_sub _ _
      _ = lam * |Y| + |Z| := by rw [abs_mul, abs_of_nonneg hlam]
  have h2 : lam * |Y| ≤ C61 * (s * (l / (2 * C0)) + lam ^ 2 + lam ^ 2 * (l / (2 * C0)) +
      lam * (4 * C0 * lam / l)) := by
    calc lam * |Y| ≤ lam * (C61 * (s * R + lam + lam ^ 2 * R + R⁻¹)) :=
          mul_le_mul_of_nonneg_left hY hlam
      _ = C61 * (s * (lam * R) + lam ^ 2 + lam ^ 2 * (lam * R) + lam * R⁻¹) := by ring
      _ ≤ _ := by gcongr
  have h3 : |Z| ≤ C43 * s * Nφ + C43 * lam * ((1 / 2) * B * (4 * C0 * lam / l)) := by
    refine hZb.trans ?_
    gcongr
    exact hNG.trans (by gcongr)
  have h4 : C61 * (s * (l / (2 * C0)) + lam ^ 2 + lam ^ 2 * (l / (2 * C0)) +
      lam * (4 * C0 * lam / l)) + (C43 * s * Nφ + C43 * lam * ((1 / 2) * B * (4 * C0 * lam / l))) =
      (2 * C43 * B * C0 / l + C61 * (1 + l / (2 * C0) + 4 * C0 / l)) * lam ^ 2 +
        s * (C43 * Nφ + C61 * (l / (2 * C0))) := by
    field_simp
    ring
  linarith

/-! ## The step -/

open Correctors.StationarySpatialRealization (spatialRealization) in
/-- Proposition 5.3 (`corrector.local`, `paper/main.tex` 895-906) as the existence of a local
corrector, with its gradient localized. This is the statement of `EinsteinRelation.corrector_local` with
the production carriers (`Correctors.expectedCorrectorFlux` for the homogenized column) and one more
conjunct: the gradient `grad Q R i` is measurable for the reduced coefficient observation
σ-algebra of `B_{33R}`, like `phi`, `skew` and `flux`. The paper's construction makes the gradient of
the local corrector a function of the coefficient in `B_{33R}`; the localization is used for
`f_R` (`eq.velocity-local-flux`, "it depends only on the environment in `B_{33R}`") and for Lemma
4.3. This mirrors `Correctors.DecompositionConstruction` for Proposition 6.1. -/
def CorrectorLocalConstruction : Prop :=
  ∀ (d : ℕ) (_ : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ (phi : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → ℝ)
      (skew : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → Mat d)
      (flux : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → Vec d)
      (grad : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → Vec d),
      (∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
        (Measurable[Carriers.reducedCoefficientObservationSigma
              {y : Vec d | euclideanNorm (y - 0) < 33 * R}] (fun ω => phi Q R i ω) ∧
            Measurable[Carriers.reducedCoefficientObservationSigma
              {y : Vec d | euclideanNorm (y - 0) < 33 * R}] (fun ω => skew Q R i ω) ∧
            Measurable[Carriers.reducedCoefficientObservationSigma
              {y : Vec d | euclideanNorm (y - 0) < 33 * R}] (fun ω => flux Q R i ω) ∧
            Measurable[Carriers.reducedCoefficientObservationSigma
              {y : Vec d | euclideanNorm (y - 0) < 33 * R}] (fun ω => grad Q R i ω)) ∧
        (∀ ω, (skew Q R i ω).transpose = -(skew Q R i ω)) ∧
        HasWeakHorizontalGradient (Correctors.reducedEnvironmentLaw Q)
          (Correctors.reducedEnvironmentLaw_stationary Q) (phi Q R i) (grad Q R i) ∧
        (∀ j : Fin d,
          HasWeakHorizontalDivergence (Correctors.reducedEnvironmentLaw Q)
            (Correctors.reducedEnvironmentLaw_stationary Q)
            (fun (ω : FieldPair d) (k : Fin d) => skew Q R i ω j k)
            (fun ω : FieldPair d =>
              (∑ k, (ω.1 0) j k * (unitVector i k + grad Q R i ω k)) -
                (Correctors.expectedCorrectorFlux Q i).ofLp j - flux Q R i ω j))) ∧
      ∀ m : ℝ, 2 ≤ m → ∃ C : ℝ, ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
        (eLpNorm (phi Q R i) (ENNReal.ofReal m) (Correctors.reducedEnvironmentLaw Q) +
            eLpNorm (fun ω => frobeniusNorm (skew Q R i ω)) (ENNReal.ofReal m)
              (Correctors.reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * Correctors.correctorAmplitude d R)) ∧
        (eLpNorm (fun ω => euclideanNorm (flux Q R i ω)) (ENNReal.ofReal m)
              (Correctors.reducedEnvironmentLaw Q) +
            eLpNorm (fun ω : FieldPair d =>
                euclideanNorm (fun j : Fin d =>
                  grad Q R i ω j -
                    (spatialRealization (Correctors.canonicalCorrectorGradient Q i :
                        Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
                      ((0 : Vec d), ω)).ofLp j))
              (ENNReal.ofReal m) (Correctors.reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * R⁻¹))

open Correctors.StationarySpatialRealization (spatialRealization) in
/-- **`VelocityResolventRateStep`** (`eq.velocity-resolvent-rate`, `paper/main.tex` 1102-1147).
With `λ_* = min(1, l/(4C₀'))`, `C₀' = max(C₀, 33)` and the dyadic scale `R ≍ λ⁻¹`, Lemma 4.3 applied
to the local corrector `φ_{i,R}` (with `L^λ φ = (-b_i + λ ā_{1i} + λ f_R) + D·(½F)`) and the
response bound of Proposition 6.1 for `f_R` give
`|E[ρ_s b_i^λ] - λ ā_{1i}| ≤ C λ² + C s K` with `K = ‖φ_{i,R}‖_{L^{2p}} + l/(2C₀')`.

Premises: Proposition 5.3 with the gradient localized (`CorrectorLocalConstruction`), Proposition 6.1
(`ScalarDecompositionTwin`), Lemma 4.3 (`Entropy.ResolventStatement`), the gradient part of Lemma 4.1
(`Correctors.FisherBoundStatement`, for `Dρ_s`), the AKM flux decay (`AKMFluxDecay`) and the gradient
moments of Lemma 5.1 (`CorrectorGradientMoments`). -/
theorem velocityResolventRateStep_of_steps (H53 : CorrectorLocalConstruction)
    (H61 : ScalarDecompositionTwin)
    (H43 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), Entropy.ResolventStatement d hd Λ₀ r₀)
    (H41 : Correctors.FisherBoundStatement) (hAKM : AKMFluxDecay)
    (H51 : CorrectorGradientMoments) : VelocityResolventRateStep := by
  intro d hd Λ₀ r₀
  by_cases hpar : 1 ≤ Λ₀ ∧ 1 ≤ r₀
  swap
  · exact ⟨0, 1, one_pos, le_rfl,
      fun Q => absurd ⟨Q.ellipticity_parameter, Q.range_parameter⟩ hpar⟩
  obtain ⟨hΛ, hr₀⟩ := hpar
  obtain ⟨C₀, hC₀, l₁, -, hD⟩ := H61 d hd Λ₀ r₀ hΛ hr₀
  obtain ⟨l₂, -, hRes⟩ := H43 d hd Λ₀ r₀
  set l : ℝ := max (max l₁ l₂) 1 with hldef
  have hl₁ : l₁ ≤ l := (le_max_left _ _).trans (le_max_left _ _)
  have hl₂ : l₂ ≤ l := (le_max_right _ _).trans (le_max_left _ _)
  have hlpos : 0 < l := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨p₁, hp₁, hD1⟩ := hD l hl₁
  obtain ⟨p₂, hp₂, hRes1⟩ := hRes l hl₂
  set p : ℝ := max p₁ p₂ with hpdef
  have hp1 : 1 < p := lt_of_lt_of_le hp₁ (le_max_left _ _)
  have h2p : (2 : ℝ) ≤ 2 * p := by linarith
  obtain ⟨phi, skew, flux, grad, hstruct, hbounds⟩ := H53 d hd Λ₀ r₀
  obtain ⟨Ka, hKa0, hKa⟩ := DriftH5.exists_ae_abs_entry_le d Λ₀ r₀
  have hAex : ∀ m : ℝ, ∃ A : ℝ, 0 ≤ A ∧ (2 ≤ m → ∀ (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
      (t : ℝ), 0 ≤ t → eLpNorm (Correctors.heatSmoothed t (centredFluxFirst hd Q i))
        (ENNReal.ofReal m) (Carriers.reducedReferenceLaw Q) ≤
          ENNReal.ofReal (A * (Real.sqrt (1 + t))⁻¹)) := by
    intro m
    by_cases hm : 2 ≤ m
    · obtain ⟨C, hC⟩ := hAKM d hd Λ₀ r₀ m hm
      refine ⟨max C 0, le_max_right _ _, fun _ Q i t ht => ?_⟩
      exact (hC Q i t ht).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (le_max_left _ _) (inv_nonneg.mpr (Real.sqrt_nonneg _))))
    · exact ⟨0, le_rfl, fun h => absurd h hm⟩
  choose A hA0 hA using hAex
  have hBex : ∀ m : ℝ, ∃ B : ℝ, 0 ≤ B ∧ (2 ≤ m → ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ),
      1 ≤ R → ∀ i : Fin d,
      eLpNorm (fun ω => euclideanNorm (flux Q R i ω)) (ENNReal.ofReal m)
          (Correctors.reducedEnvironmentLaw Q) +
        eLpNorm (fun ω : FieldPair d => euclideanNorm (fun j : Fin d => grad Q R i ω j -
            (spatialRealization (Correctors.canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
              ((0 : Vec d), ω)).ofLp j)) (ENNReal.ofReal m) (Correctors.reducedEnvironmentLaw Q) ≤
        ENNReal.ofReal (B * R⁻¹)) := by
    intro m
    by_cases hm : 2 ≤ m
    · obtain ⟨C, hC⟩ := hbounds m hm
      refine ⟨max C 0, le_max_right _ _, fun _ Q R hR i => (hC Q R hR i).2.trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (inv_nonneg.mpr (by linarith))))⟩
    · exact ⟨0, le_rfl, fun h => absurd h hm⟩
  choose B hB0 hB using hBex
  set M : ℝ → ℝ := fun m => A m + d * Ka * B m with hMdef
  obtain ⟨C₆₁, hC₆₁, hD2⟩ := hD1 p (le_max_left _ _) (M (4 * p))
  obtain ⟨C₄₃, hC₄₃, hRes2⟩ := hRes1 p (le_max_right _ _)
  obtain ⟨Cφ, hCφ⟩ := hbounds (2 * p) h2p
  set C₀' : ℝ := max C₀ 33 with hC₀'def
  have hC₀'pos : 0 < C₀' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  set C₂ : ℝ := 2 * C₄₃ * B (2 * p) * C₀' / l + C₆₁ * (1 + l / (2 * C₀') + 4 * C₀' / l)
    with hC₂def
  refine ⟨max (max C₄₃ C₆₁) C₂, min 1 (l / (4 * C₀')), lt_min one_pos (by positivity),
    min_le_left _ _, ?_⟩
  intro Q P' hP' lam hl0 hlS hQ i divA hdiv op rhoOf hrho
  have hl1 : lam ≤ 1 := hlS.trans (min_le_left _ _)
  have hlsmall : lam ≤ l / (4 * C₀') := hlS.trans (min_le_right _ _)
  obtain ⟨R, hR2, hRdy, hC₀R, hRlow⟩ :=
    Clock.exists_dyadic_scale C₀' l hC₀'pos hlpos lam hl0 hlsmall
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    Entropy.reducedReferenceLaw_isProbabilityMeasure Q
  set μ := Carriers.reducedReferenceLaw Q with hμ
  have hRpos : 0 < R := by linarith
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hlamR : lam * R ≤ l / (2 * C₀') := by
    have h := hC₀R
    rw [le_div_iff₀ (by positivity)] at h
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hRinv : R⁻¹ ≤ 4 * C₀' * lam / l := by
    rw [inv_le_comm₀ hRpos (by positivity), inv_div]
    exact hRlow
  have h33 : 33 * R ≤ l / (2 * lam) :=
    (mul_le_mul_of_nonneg_right (le_max_right C₀ 33) hRpos.le).trans hC₀R
  have hC₀R' : C₀ * R ≤ l / (2 * lam) :=
    (mul_le_mul_of_nonneg_right (le_max_left C₀ 33) hRpos.le).trans hC₀R
  set r : ℝ := l / (2 * lam) with hrdef
  have hrpos : 0 < r := by positivity
  obtain ⟨⟨hφm, -, hFm, hgm⟩, hskew, hgradW, hdivS⟩ := hstruct Q R hR1 i
  obtain ⟨hφbd, -⟩ := hCφ Q R hR1 i
  set φ := phi Q R i with hφdef
  set Dφ := grad Q R i with hDφdef
  set Fl := flux Q R i with hFldef
  -- Localities.
  have hU : localSigma {y : Vec d | euclideanNorm (y - 0) < 33 * R} ≤
      localSigma {y : Vec d | euclideanNorm y < r} := localSigma_ball_mono h33
  have hφL : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] φ :=
    (hφm.mono (reducedCoefficientObservationSigma_le_localSigma _) le_rfl).mono hU le_rfl
  have hDφ33 : Measurable[localSigma {y : Vec d | euclideanNorm (y - 0) < 33 * R}] Dφ :=
    hgm.mono (reducedCoefficientObservationSigma_le_localSigma _) le_rfl
  have hDφL : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] Dφ := hDφ33.mono hU le_rfl
  have hFL : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] Fl :=
    (hFm.mono (reducedCoefficientObservationSigma_le_localSigma _) le_rfl).mono hU le_rfl
  have hborel := Probability.localSigma_le_borel (d := d) {y : Vec d | euclideanNorm y < r}
  have hφB : Measurable φ := hφL.mono hborel le_rfl
  have hDφB : Measurable Dφ := hDφL.mono hborel le_rfl
  have hFB : Measurable Fl := hFL.mono hborel le_rfl
  have hcontE : Continuous fun v : Vec d => euclideanNorm v := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  -- Gradient moments.
  have hcanV : Measurable fun w : FieldPair d =>
      (spatialRealization (Correctors.canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
        ((0 : Vec d), w)).ofLp := by
    have h1 := (Correctors.StationarySpatialRealization.measurable_spatialRealization
      (Correctors.canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))).comp
      ((measurable_const (a := (0 : Vec d))).prodMk measurable_id)
    exact (PiLp.continuous_ofLp 2 _).measurable.comp h1
  have hdiffm : ∀ m : ℝ, 2 ≤ m → eLpNorm (fun w : FieldPair d => euclideanNorm
      (fun j : Fin d => Dφ w j - (spatialRealization (Correctors.canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
        ((0 : Vec d), w)).ofLp j)) (ENNReal.ofReal m) μ ≤ ENNReal.ofReal (B m * R⁻¹) :=
    fun m hm => le_add_self.trans (hB m hm Q R hR1 i)
  have hgradm : ∀ m : ℝ, 2 ≤ m →
      MemLp (fun w => euclideanNorm (Dφ w)) (ENNReal.ofReal m) μ := by
    intro m hm
    have hdm : MemLp (fun w : FieldPair d => euclideanNorm (fun j : Fin d => Dφ w j -
        (spatialRealization (Correctors.canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
          ((0 : Vec d), w)).ofLp j)) (ENNReal.ofReal m) μ :=
      ⟨(hcontE.measurable.comp (hDφB.sub hcanV)).aestronglyMeasurable,
        lt_of_le_of_lt (hdiffm m hm) ENNReal.ofReal_lt_top⟩
    refine (hdm.add (memLp_canonicalGradient H51 hd Q i hm)).mono
      (hcontE.measurable.comp hDφB).aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (vr_euclid_nonneg _)]
    have htri := TimeChange.euclideanNorm_add_le (fun j : Fin d => Dφ w j -
        (spatialRealization (Correctors.canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
          ((0 : Vec d), w)).ofLp j)
      (spatialRealization (Correctors.canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
          ((0 : Vec d), w)).ofLp
    have hsum : (fun j : Fin d => Dφ w j -
        (spatialRealization (Correctors.canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
          ((0 : Vec d), w)).ofLp j) +
        (spatialRealization (Correctors.canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
          ((0 : Vec d), w)).ofLp = Dφ w := by
      funext j; simp
    rw [hsum] at htri
    refine htri.trans (le_of_eq ?_)
    simp only [Pi.add_apply]
    rw [abs_of_nonneg (add_nonneg (vr_euclid_nonneg _) (vr_euclid_nonneg _))]
  have hgmem : ∀ m : ℝ, 2 ≤ m → MemLp (centredFluxFirst hd Q i) (ENNReal.ofReal m) μ := by
    intro m hm
    obtain ⟨C, hC⟩ := centredFluxMoments_of_correctorGradientMoments H51 d hd Λ₀ r₀ m hm
    exact ⟨(measurable_centredFluxFirst hd Q i).aestronglyMeasurable,
      lt_of_le_of_lt (hC Q i) ENNReal.ofReal_lt_top⟩
  -- The local flux is an averaging field; the response bound of Proposition 6.1.
  have hAvg : Carriers.IsScalarAveragingField Q M R (localFluxFirst hd Q i Dφ) :=
    isScalarAveragingField_localFluxFirst hd Q hQ i hRpos hDφ33 hKa0 (hKa Q) A B
      (fun m _ => hA0 m) (fun m _ => hB0 m) (fun m hm t ht => hA m hm Q i t ht) hgmem hgradm
      hdiffm
  obtain ⟨-, hresp⟩ := hD2 Q hQ M rfl R hR2 hRdy (localFluxFirst hd Q i Dφ) hAvg
  -- The local divergence replaces `divA`.
  have hdivL := hasWeakHorizontalDivergence_localDiv Q hQ i hrpos
  have hdivae : divA =ᵐ[μ] localDiv i r := hdiv.ae_unique hdivL
  obtain ⟨Bc, hBc⟩ := DriftH5.exists_ae_abs_cdiv_le Q hQ i
  have hLDbd : ∀ᵐ w ∂μ, |localDiv i r w| ≤ Bc := by
    filter_upwards [localDiv_ae_eq_cdiv Q hQ i hrpos, hBc] with w h1 h2
    rw [h1]; exact h2
  have hLDL := measurable_localDiv i hrpos
  have hLDB : Measurable (localDiv i r) := hLDL.mono hborel le_rfl
  -- The generator equation of the local corrector.
  have hFlmem : MemLp (fun w => euclideanNorm (Fl w)) (ENNReal.ofReal (2 * p)) μ :=
    ⟨(hcontE.measurable.comp hFB).aestronglyMeasurable,
      lt_of_le_of_lt (le_self_add.trans (hB (2 * p) h2p Q R hR1 i)) ENNReal.ofReal_lt_top⟩
  have h12p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hFlint : ∀ j : Fin d, Integrable (fun ω => Fl ω j) μ := fun j =>
    (hFlmem.integrable h12p).mono' ((measurable_pi_apply j).comp hFB).aestronglyMeasurable
      (ae_of_all _ fun w => by
        rw [Real.norm_eq_abs]; exact qd'_abs_coord_le_euclid (Fl w) j)
  set h₁ : FieldPair d → ℝ := fun ω => -velocityDrift hd lam i (localDiv i r) ω +
    lam * ∑ k, (ω.1 0) (firstIdx hd) k * (unitVector i k + Dφ ω k) with hh₁def
  set G₁ : FieldPair d → Vec d := fun ω => (1 / 2 : ℝ) • Fl ω with hG₁def
  have hgen : SatisfiesReducedGeneratorEquation μ hQ lam φ Dφ h₁ G₁ (firstIdx hd) :=
    satisfiesReducedGeneratorEquation_localCorrector hd lam i ⟨Ka, hKa Q⟩
      (ae_symm_reducedReferenceLaw Q) (Correctors.expectedCorrectorFlux Q i).ofLp hskew hgradW
      hdivS hdivL hFlint
  -- The inputs of Lemma 4.3.
  have hφmem : MemLp φ (ENNReal.ofReal (2 * p)) μ :=
    ⟨hφB.aestronglyMeasurable, lt_of_le_of_lt (le_self_add.trans hφbd) ENNReal.ofReal_lt_top⟩
  have hentryB : ∀ k : Fin d, Measurable fun ω : FieldPair d => (ω.1 0) (firstIdx hd) k :=
    fun k => (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem
      (firstIdx hd) k).measurable
  have hh₁B : Measurable h₁ := by
    simp only [hh₁def, velocityDrift]
    exact ((measurable_const.mul hLDB).add (measurable_const.mul (hentryB i))).neg.add
      (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
        (hentryB k).mul (measurable_const.add ((measurable_pi_apply k).comp hDφB))))
  have hh₁mem : MemLp h₁ (ENNReal.ofReal (2 * p)) μ := by
    have hc1 : MemLp (fun _ : FieldPair d => (1 / 2) * Bc + lam * Ka + lam * (d * Ka))
        (ENNReal.ofReal (2 * p)) μ := memLp_const _
    have hc2 : MemLp (fun w => lam * (d * Ka) * euclideanNorm (Dφ w)) (ENNReal.ofReal (2 * p)) μ :=
      (hgradm (2 * p) h2p).const_mul _
    have hdom : MemLp (fun w => ((1 / 2) * Bc + lam * Ka + lam * (d * Ka)) +
        lam * (d * Ka) * euclideanNorm (Dφ w)) (ENNReal.ofReal (2 * p)) μ := hc1.add hc2
    refine hdom.mono hh₁B.aestronglyMeasurable ?_
    filter_upwards [hLDbd, hKa Q] with w hw hK
    have hE0 := vr_euclid_nonneg (Dφ w)
    have hBc0 : 0 ≤ Bc := (abs_nonneg _).trans hw
    have hdomnn : 0 ≤ (1 / 2) * Bc + lam * Ka + lam * (d * Ka) +
        lam * (d * Ka) * euclideanNorm (Dφ w) := by
      have e1 : 0 ≤ lam * Ka := mul_nonneg hl0.le hKa0
      have e2 : 0 ≤ lam * (d * Ka) := mul_nonneg hl0.le (mul_nonneg (Nat.cast_nonneg _) hKa0)
      have e3 := mul_nonneg e2 hE0
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hdomnn]
    simp only [hh₁def, velocityDrift]
    have hsum : |∑ k, (w.1 0) (firstIdx hd) k * (unitVector i k + Dφ w k)| ≤
        d * Ka * (1 + euclideanNorm (Dφ w)) := by
      calc |∑ k, (w.1 0) (firstIdx hd) k * (unitVector i k + Dφ w k)|
          ≤ ∑ k, |(w.1 0) (firstIdx hd) k * (unitVector i k + Dφ w k)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin d, Ka * (1 + euclideanNorm (Dφ w)) := Finset.sum_le_sum fun k _ => by
            rw [abs_mul]
            refine mul_le_mul (hK _ k) ?_ (abs_nonneg _) hKa0
            refine (abs_add_le _ _).trans (add_le_add ?_ (qd'_abs_coord_le_euclid _ k))
            simp [unitVector, Pi.single_apply]; split_ifs <;> norm_num
        _ = d * Ka * (1 + euclideanNorm (Dφ w)) := by simp; ring
    calc |-((1 / 2) * localDiv i r w + lam * (w.1 0) (firstIdx hd) i) +
          lam * ∑ k, (w.1 0) (firstIdx hd) k * (unitVector i k + Dφ w k)|
        ≤ (1 / 2) * |localDiv i r w| + lam * |(w.1 0) (firstIdx hd) i| +
          lam * |∑ k, (w.1 0) (firstIdx hd) k * (unitVector i k + Dφ w k)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg, abs_mul lam, abs_of_pos hl0]
          refine add_le_add ((abs_add_le _ _).trans ?_) le_rfl
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos hl0]
      _ ≤ (1 / 2) * Bc + lam * Ka + lam * (d * Ka * (1 + euclideanNorm (Dφ w))) := by
          gcongr
          · exact hK _ _
      _ = _ := by ring
  have hG₁eq : (fun w => euclideanNorm (G₁ w)) = fun w => (1 / 2 : ℝ) * euclideanNorm (Fl w) := by
    funext w
    simp only [hG₁def]
    rw [vr_euclid_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hG₁mem : MemLp (fun w => euclideanNorm (G₁ w)) (ENNReal.ofReal (2 * p)) μ := by
    rw [hG₁eq]; exact hFlmem.const_mul _
  have hh₁L : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] h₁ := by
    letI : MeasurableSpace (FieldPair d) := localSigma {y : Vec d | euclideanNorm y < r}
    have h0 : (0 : Vec d) ∈ {y : Vec d | euclideanNorm y < r} := by
      simp only [Set.mem_setOf_eq]
      rw [show (0 : Vec d) = (0 : ℝ) • unitVector i by simp, vr_euclid_smul]
      simpa using hrpos
    simp only [hh₁def, velocityDrift]
    exact ((measurable_const.mul hLDL).add (measurable_const.mul
      (measurable_entry_localSigma h0 _ i))).neg.add (measurable_const.mul
        (Finset.measurable_sum _ fun k _ => (measurable_entry_localSigma h0 _ k).mul
          (measurable_const.add ((measurable_pi_apply k).comp hDφL))))
  have hG₁L : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] G₁ := by
    letI : MeasurableSpace (FieldPair d) := localSigma {y : Vec d | euclideanNorm y < r}
    exact measurable_const.smul hFL
  -- The constant `K`.
  refine ⟨(eLpNorm φ (ENNReal.ofReal (2 * p)) μ).toReal + l / (2 * C₀'), fun s hs0 hs => ?_⟩
  set s' : {r : ℝ // 0 < r} := ⟨s, hs0⟩
  have hρ := hrho s'
  obtain ⟨Drho, hDrho, -, -⟩ := H41 d hd Λ₀ r₀ Q hQ lam hl0 hl1 (P' lam) op
    (hP' lam hl0.le hl1) s' (rhoOf s) hρ
  obtain ⟨⟨-, hintρh, -, -⟩, hL43⟩ := hRes2 Q hQ lam hl0 hl1 Q.measure (P' lam) op
    ⟨rfl, hP' lam hl0.le hl1⟩ s' hs (rhoOf s) hρ Drho hDrho φ Dφ h₁ G₁ hφmem
    (hgradm (2 * p) h2p) hh₁mem hG₁mem hφL hDφL hh₁L hG₁L hgen
  obtain ⟨hintρf, hY⟩ := hresp lam hl0 hl1 hC₀R' Q.measure inferInstance (P' lam) op
    ⟨rfl, hP' lam hl0.le hl1⟩ s' hs (rhoOf s) hρ
  obtain ⟨hρ1, hρint⟩ := integral_rho_eq_one Q (P' lam) op s' hρ
  have hρ1' : ∫ w, rhoOf s w ∂μ = 1 := hρ1
  have hρint' : Integrable (rhoOf s) μ := hρint
  have hintρf' : Integrable (fun w => rhoOf s w * localFluxFirst hd Q i Dφ w) μ := hintρf
  have hY' : |∫ w, rhoOf s w * localFluxFirst hd Q i Dφ w ∂μ| ≤
      C₆₁ * (s * R + lam + lam ^ 2 * R + R⁻¹) := hY
  -- `E[ρ h₁] = -E[ρ b] + λ ā + λ E[ρ f_R]`.
  set ab : ℝ := (Correctors.expectedCorrectorFlux Q i).ofLp (firstIdx hd) with habdef
  have hbB : Measurable (velocityDrift hd lam i (localDiv i r)) := by
    unfold velocityDrift
    exact (measurable_const.mul hLDB).add (measurable_const.mul (hentryB i))
  have hbbd : ∀ᵐ w ∂μ, ‖velocityDrift hd lam i (localDiv i r) w‖ ≤ (1 / 2) * Bc + lam * Ka := by
    filter_upwards [hLDbd, hKa Q] with w hw hK
    rw [Real.norm_eq_abs]
    unfold velocityDrift
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos hl0]
    gcongr
    exact hK _ _
  have hintρb : Integrable (fun w => rhoOf s w * velocityDrift hd lam i (localDiv i r) w) μ :=
    hρint'.mul_bdd hbB.aestronglyMeasurable hbbd
  have hZ : ∫ w, rhoOf s w * h₁ w ∂μ =
      -(∫ w, rhoOf s w * velocityDrift hd lam i (localDiv i r) w ∂μ) + lam * ab +
        lam * ∫ w, rhoOf s w * localFluxFirst hd Q i Dφ w ∂μ := by
    have hpt : ∀ w, rhoOf s w * h₁ w = -(rhoOf s w * velocityDrift hd lam i (localDiv i r) w) +
        lam * ab * rhoOf s w + lam * (rhoOf s w * localFluxFirst hd Q i Dφ w) := by
      intro w
      simp only [hh₁def, localFluxFirst, habdef]
      ring
    rw [integral_congr_ae (ae_of_all _ hpt)]
    have e1 : ∫ w, (-(rhoOf s w * velocityDrift hd lam i (localDiv i r) w) + lam * ab * rhoOf s w +
        lam * (rhoOf s w * localFluxFirst hd Q i Dφ w)) ∂μ =
        (∫ w, (-(rhoOf s w * velocityDrift hd lam i (localDiv i r) w) + lam * ab * rhoOf s w) ∂μ) +
          ∫ w, lam * (rhoOf s w * localFluxFirst hd Q i Dφ w) ∂μ :=
      integral_add (hintρb.neg.add (hρint'.const_mul _)) (hintρf'.const_mul _)
    have e2 : ∫ w, (-(rhoOf s w * velocityDrift hd lam i (localDiv i r) w) +
        lam * ab * rhoOf s w) ∂μ =
        -(∫ w, rhoOf s w * velocityDrift hd lam i (localDiv i r) w ∂μ) +
          lam * ab * ∫ w, rhoOf s w ∂μ := by
      have e2a : ∫ w, (-(rhoOf s w * velocityDrift hd lam i (localDiv i r) w) +
          lam * ab * rhoOf s w) ∂μ =
          (∫ w, -(rhoOf s w * velocityDrift hd lam i (localDiv i r) w) ∂μ) +
            ∫ w, lam * ab * rhoOf s w ∂μ := integral_add hintρb.neg (hρint'.const_mul _)
      rw [e2a, integral_neg, integral_const_mul]
    rw [e1, e2, integral_const_mul, hρ1', mul_one]
  -- `E[ρ b]` for the given divergence.
  have hX : ∫ w, rhoOf s w * ((1 / 2 : ℝ) * divA w + lam * (w.1 0) (firstIdx hd) i) ∂μ =
      ∫ w, rhoOf s w * velocityDrift hd lam i (localDiv i r) w ∂μ := by
    refine integral_congr_ae (hdivae.mono fun w hw => ?_)
    simp only [velocityDrift, hw]
  -- Bounds.
  have hZb : |∫ w, rhoOf s w * h₁ w ∂μ| ≤
      C₄₃ * s * (eLpNorm φ (ENNReal.ofReal (2 * p)) μ).toReal +
        C₄₃ * lam * (eLpNorm (fun w => euclideanNorm (G₁ w)) (ENNReal.ofReal (2 * p)) μ).toReal := by
    have h := le_of_ofReal_le_add_mul (mul_nonneg hC₄₃ hs0.le) (mul_nonneg hC₄₃ hl0.le)
      hφmem.2.ne hG₁mem.2.ne hL43
    linarith
  have hNG : (eLpNorm (fun w => euclideanNorm (G₁ w)) (ENNReal.ofReal (2 * p)) μ).toReal ≤
      (1 / 2) * B (2 * p) * R⁻¹ := by
    have hle : eLpNorm (fun w => euclideanNorm (G₁ w)) (ENNReal.ofReal (2 * p)) μ ≤
        ENNReal.ofReal ((1 / 2) * B (2 * p) * R⁻¹) := by
      rw [hG₁eq]
      have hsm : (fun w => (1 / 2 : ℝ) * euclideanNorm (Fl w)) =
          (1 / 2 : ℝ) • fun w => euclideanNorm (Fl w) := rfl
      rw [hsm, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc,
        ENNReal.ofReal_mul (p := (1 / 2 : ℝ)) (by norm_num)]
      gcongr
      exact le_self_add.trans (hB (2 * p) h2p Q R hR1 i)
    exact ENNReal.toReal_le_of_le_ofReal (by have := hB0 (2 * p); positivity) hle
  have hfin := abs_sub_le_of_resolvent_response (s := s) hZ hZb hY' hNG hRinv hlamR hl0.le
    hs0.le hC₄₃ hC₆₁ (hB0 (2 * p)) hlpos hC₀'pos
  have habar : abar Q (firstIdx hd) i = ab := by simp [abar, habdef]
  rw [hX, habar]
  have hfin' : |(∫ w, rhoOf s w * velocityDrift hd lam i (localDiv i r) w ∂μ) - lam * ab| ≤
      C₂ * lam ^ 2 + s * (C₄₃ * (eLpNorm φ (ENNReal.ofReal (2 * p)) μ).toReal +
        C₆₁ * (l / (2 * C₀'))) := hfin.trans (le_of_eq (by rw [hC₂def]))
  have hNφ : 0 ≤ (eLpNorm φ (ENNReal.ofReal (2 * p)) μ).toReal := ENNReal.toReal_nonneg
  have hlC : 0 ≤ l / (2 * C₀') := by positivity
  have hCmax1 : C₄₃ ≤ max (max C₄₃ C₆₁) C₂ := (le_max_left _ _).trans (le_max_left _ _)
  have hCmax2 : C₆₁ ≤ max (max C₄₃ C₆₁) C₂ := (le_max_right _ _).trans (le_max_left _ _)
  have hCmax3 : C₂ ≤ max (max C₄₃ C₆₁) C₂ := le_max_right _ _
  have h1 : C₂ * lam ^ 2 ≤ max (max C₄₃ C₆₁) C₂ * lam ^ 2 :=
    mul_le_mul_of_nonneg_right hCmax3 (sq_nonneg _)
  have h2 : s * (C₄₃ * (eLpNorm φ (ENNReal.ofReal (2 * p)) μ).toReal + C₆₁ * (l / (2 * C₀'))) ≤
      max (max C₄₃ C₆₁) C₂ * s * ((eLpNorm φ (ENNReal.ofReal (2 * p)) μ).toReal +
        l / (2 * C₀')) := by
    have e1 := mul_le_mul_of_nonneg_right hCmax1 hNφ
    have e2 := mul_le_mul_of_nonneg_right hCmax2 hlC
    have e3 : C₄₃ * (eLpNorm φ (ENNReal.ofReal (2 * p)) μ).toReal + C₆₁ * (l / (2 * C₀')) ≤
        max (max C₄₃ C₆₁) C₂ * ((eLpNorm φ (ENNReal.ofReal (2 * p)) μ).toReal +
          l / (2 * C₀')) := by
      rw [mul_add]; exact add_le_add e1 e2
    calc s * (C₄₃ * (eLpNorm φ (ENNReal.ofReal (2 * p)) μ).toReal + C₆₁ * (l / (2 * C₀')))
        ≤ s * (max (max C₄₃ C₆₁) C₂ * ((eLpNorm φ (ENNReal.ofReal (2 * p)) μ).toReal +
          l / (2 * C₀'))) := mul_le_mul_of_nonneg_left e3 hs0.le
      _ = _ := by ring
  exact hfin'.trans (add_le_add h1 h2)

end EinsteinRelation
