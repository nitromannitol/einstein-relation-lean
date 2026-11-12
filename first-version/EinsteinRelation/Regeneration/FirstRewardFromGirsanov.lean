import EinsteinRelation.Regeneration.FirstRewardSteps
import EinsteinRelation.Density.LaplaceDensityExistence
import EinsteinRelation.Entropy.DivergenceFromFisher
import EinsteinRelation.External.GMPReducedInputs
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # The Girsanov step of Proposition 3.2 from its inputs

Source: `paper/main.tex` 457-480. This file proves `FirstRewardStepFrozen` from four inputs:
`GirsanovEndpointStep`, `UnforcedEnvironmentInvarianceStep`, `External.GMPReducedFamilyExistence`
and `GMPCouplingTailsV2Input`. The steps follow the paper:

* `annealed_sq_le_of_girsanov`: the fixed-time bound
  `E^λ|G(ω_t)|² ≤ exp(½ (q - 1) K λ² t) ‖G‖²_{L^{2q/(q-1)}(Q)}`, from the Girsanov bound in each
  environment, Hölder's inequality over the environment, and the force-zero invariance of `Q`;
* `coupled_indicator_observation_le`: Cauchy–Schwarz against the first regeneration tail;
* `firstReward_le_of_girsanov`: integration in time over `[0, τ₁)`, with `q = p / (p - 2)`;
* `firstRewardStepFrozen_of_girsanov`: the quantifier prefix of Proposition 3.2.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

/-- On a probability space, `∫⁻ f^s ≤ (∫⁻ f)^s` for `0 < s ≤ 1` (Hölder against the constant `1`). -/
theorem lintegral_rpow_le_rpow_lintegral_of_prob {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) : ∫⁻ a, f a ^ s ∂μ ≤ (∫⁻ a, f a ∂μ) ^ s := by
  rcases hs1.lt_or_eq with hs1 | rfl
  · have hpq : (1 / s).HolderConjugate (1 / (1 - s)) :=
      Real.holderConjugate_one_div hs0 (by linarith) (by ring)
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (hf.pow_const s)
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
    have hinner : ∫⁻ a, (f a ^ s) ^ (1 / s) ∂μ = ∫⁻ a, f a ∂μ :=
      lintegral_congr fun a => by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hs0.ne', ENNReal.rpow_one]
    rw [hinner, one_div_one_div] at h
    exact h
  · simp

/-- **The fixed-time bound of Step 1** (`paper/main.tex` 461-468): under the annealed law at force
`λ`, `E|G(ω_t)|² ≤ exp(½ (q - 1) K λ² t) (E_Q |G|^{2q'})^{1/q'}` with `q' = q / (q - 1)` and
`K = sourceReducedBound Λ₀`. Only the origin law of the forced kernel enters. -/
theorem annealed_sq_le_of_girsanov_origin (hGir : GirsanovEndpointStep)
    (hInv : UnforcedEnvironmentInvarianceStep) (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    (hP0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (P' : DiffusionFamily d) (hP' : IsGMPReducedFamily hd Q.ellipticity_parameter Q P')
    (hP'0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω))
    {G : FieldPair d → ℝ} (hG : Measurable G) (t : ℝ≥0) {q : ℝ} (hq : 1 < q) :
    ∫⁻ z, ENNReal.ofReal |G (Carriers.reducedObservationAt t z)| ^ (2 : ℝ)
        ∂(Carriers.annealedCoordinateJoint Q.measure P hP0) ≤
      ENNReal.ofReal (Real.exp ((1 / 2) * (q - 1) * sourceReducedBound Λ₀ * lam ^ 2 * t)) *
        (∫⁻ w, ENNReal.ofReal |G w| ^ (2 * (q / (q - 1))) ∂(Carriers.reducedReferenceLaw Q)) ^
          ((q - 1) / q) := by
  set E := ENNReal.ofReal (Real.exp ((1 / 2) * (q - 1) * sourceReducedBound Λ₀ * lam ^ 2 * t))
  set q' := q / (q - 1) with hq'def
  have hq1 : 0 < q - 1 := by linarith
  have hq'pos : 0 < q' := div_pos (by linarith) hq1
  have hs : (q - 1) / q = 1 / q' := by rw [hq'def, one_div_div]
  -- The observation functional and its measurability.
  set F : FieldPair d × Path d → ℝ≥0∞ :=
    fun z => ENNReal.ofReal |G (Carriers.reducedObservationAt t z)| ^ (2 : ℝ) with hFdef
  have hobs := laplaceDensity_measurable_observation_fixed (d := d) t
  have hF : Measurable F :=
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hG.comp hobs))).pow_const _
  have hFq : Measurable fun z => F z ^ q' := hF.pow_const _
  set φ : FieldPair d → Vec d → ℝ≥0∞ :=
    fun ω y => ENNReal.ofReal |G (translate y (reduce ω))| ^ (2 : ℝ) with hφdef
  have hφ : ∀ ω, Measurable (φ ω) := fun ω =>
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (hG.comp (laplaceDensity_measurable_translate_reduce ω)))).pow_const _
  have hFφ : ∀ ω γ, F (ω, γ) = φ ω (γ t) := fun ω γ => rfl
  -- The force-zero moments, against the probability part of the kernel.
  set Kp0 := Probability.probabilityPart (originLaw (P' 0))
  have hK0ae := Probability.probabilityPart_ae_eq Q.measure (originLaw (P' 0)) hP'0
  set A : FieldPair d → ℝ≥0∞ := fun ω => ∫⁻ γ, F (ω, γ) ^ q' ∂Kp0 ω with hAdef
  have hA : Measurable A := Measurable.lintegral_kernel_prod_right' (κ := Kp0) hFq
  -- Girsanov in each environment.
  have hpt : ∀ᵐ ω ∂Q.measure, ∫⁻ γ, F (ω, γ) ∂originLaw P ω ≤ E * A ω ^ (1 / q') := by
    filter_upwards [hP, hP' 0 le_rfl zero_le_one, hGir d hd Λ₀ r₀ Q lam h0 h1, hK0ae]
      with ω hPω hP'ω hgω hKω
    obtain ⟨hω', r, hr⟩ := hPω
    obtain ⟨_, r0, hr0⟩ := hP'ω
    have hgir := hgω hω' r r0 t q hq (φ ω) (hφ ω)
    have hlhs : ∫⁻ γ, F (ω, γ) ∂originLaw P ω = ∫⁻ γ, φ ω (γ t) ∂r.pathLaw 0 := by
      rw [hr]; rfl
    have hrhs : A ω = ∫⁻ γ, φ ω (γ t) ^ q' ∂r0.pathLaw 0 := by
      simp only [hAdef]
      rw [hKω, originLaw_apply, hr0]; rfl
    rw [hlhs, hrhs, mul_comm, ← hs]
    exact hgir
  -- Integrate over the environment, then Jensen and the force-zero invariance.
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    Entropy.reducedReferenceLaw_isProbabilityMeasure Q
  have hJ0 : ∫⁻ ω, A ω ∂Q.measure =
      ∫⁻ w, ENNReal.ofReal |G w| ^ (2 * q') ∂(Carriers.reducedReferenceLaw Q) := by
    have hψ : Measurable fun w : FieldPair d => ENNReal.ofReal |G w| ^ (2 * q') :=
      (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hG)).pow_const _
    rw [← hInv d hd Λ₀ r₀ Q P' hP' hP'0 t _ hψ]
    unfold Carriers.annealedCoordinateJoint
    rw [Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_lintegral
      Q.measure (originLaw (P' 0)) hP'0
      (fun z => ENNReal.ofReal |G (Carriers.reducedObservationAt t z)| ^ (2 * q')) (hψ.comp hobs)]
    refine lintegral_congr_ae ?_
    filter_upwards [hK0ae] with ω hω
    simp only [hAdef]
    rw [hω]
    refine lintegral_congr fun γ => ?_
    simp only [hFdef]
    rw [← ENNReal.rpow_mul]
  calc ∫⁻ z, F z ∂(Carriers.annealedCoordinateJoint Q.measure P hP0)
      = ∫⁻ ω, ∫⁻ γ, F (ω, γ) ∂originLaw P ω ∂Q.measure := by
        unfold Carriers.annealedCoordinateJoint
        exact Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_lintegral
          Q.measure (originLaw P) hP0 F hF
    _ ≤ ∫⁻ ω, E * A ω ^ (1 / q') ∂Q.measure := lintegral_mono_ae hpt
    _ = E * ∫⁻ ω, A ω ^ (1 / q') ∂Q.measure := lintegral_const_mul _ (hA.pow_const _)
    _ ≤ E * (∫⁻ ω, A ω ∂Q.measure) ^ (1 / q') := by
        gcongr
        exact lintegral_rpow_le_rpow_lintegral_of_prob Q.measure hA.aemeasurable
          (by positivity) (by rw [div_le_one hq'pos, hq'def, le_div_iff₀ hq1]; linarith)
    _ = E * (∫⁻ w, ENNReal.ofReal |G w| ^ (2 * (q / (q - 1)))
          ∂(Carriers.reducedReferenceLaw Q)) ^ ((q - 1) / q) := by rw [hJ0, hs]

/-- `annealed_sq_le_of_girsanov_origin` for a reduced GMP kernel. -/
theorem annealed_sq_le_of_girsanov (hGir : GirsanovEndpointStep)
    (hInv : UnforcedEnvironmentInvarianceStep) (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (hP0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (P' : DiffusionFamily d) (hP' : IsGMPReducedFamily hd Q.ellipticity_parameter Q P')
    (hP'0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω))
    {G : FieldPair d → ℝ} (hG : Measurable G) (t : ℝ≥0) {q : ℝ} (hq : 1 < q) :
    ∫⁻ z, ENNReal.ofReal |G (Carriers.reducedObservationAt t z)| ^ (2 : ℝ)
        ∂(Carriers.annealedCoordinateJoint Q.measure P hP0) ≤
      ENNReal.ofReal (Real.exp ((1 / 2) * (q - 1) * sourceReducedBound Λ₀ * lam ^ 2 * t)) *
        (∫⁻ w, ENNReal.ofReal |G w| ^ (2 * (q / (q - 1))) ∂(Carriers.reducedReferenceLaw Q)) ^
          ((q - 1) / q) :=
  annealed_sq_le_of_girsanov_origin hGir hInv hd Q h0 h1 P
    (hP.mono fun ω ⟨hω', r, hr⟩ => ⟨hω', r, by rw [originLaw_apply, hr 0]⟩) hP0 P' hP' hP'0 hG t hq

/-! ## Cauchy–Schwarz against the first regeneration tail -/

/-- At time zero the sample shift is the identity. -/
theorem sampleTimeShift_zero (Δ : ℝ≥0) (z : Regeneration.CoupledSample d) :
    Regeneration.sampleTimeShift Δ z 0 = z := by
  refine Prod.ext ?_ ?_
  · ext u : 1
    simp [Regeneration.sampleTimeShift, Regeneration.pathTimeShift]
  · funext n
    simp [Regeneration.sampleTimeShift, Regeneration.gridIndex]

/-- The regeneration time of index one is the first regeneration time. -/
theorem regenerationTime_one_eq (Δ : ℝ≥0) (lam R : ℝ) (z : Regeneration.CoupledSample d)
    (i : Fin d) :
    Regeneration.regenerationTime Δ lam R z i 1 = Regeneration.firstRegenerationTime Δ lam R z i := by
  simp [Regeneration.regenerationTime, sampleTimeShift_zero]

/-- **The fixed-time bound before `τ₁`** (`paper/main.tex` 469-474): if the event `S` has coupled
probability at most `C e^{-c λ² t}` and `(q - 1) K ≤ c`, then
`E[|G(ω_t)| 1_S] ≤ √C e^{-c λ² t / 4} (E_Q |G|^{2q'})^{1/(2q')}`, by Cauchy–Schwarz and the
fixed-time Girsanov bound. -/
theorem coupled_indicator_observation_le (hGir : GirsanovEndpointStep)
    (hInv : UnforcedEnvironmentInvarianceStep) (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (Regeneration.originCoupledLaw K ω))
    (hmarg : ∀ᵐ ω ∂Q.measure,
      Measure.map Prod.fst (Regeneration.originCoupledLaw K ω) = originLaw P ω)
    (P' : DiffusionFamily d) (hP' : IsGMPReducedFamily hd Q.ellipticity_parameter Q P')
    {G : FieldPair d → ℝ} (hG : Measurable G) {q c C t : ℝ} (hq : 1 < q)
    (hcq : (q - 1) * sourceReducedBound Λ₀ ≤ c) (hC : 0 ≤ C) (ht : 0 ≤ t)
    {S : Set (FieldPair d × Regeneration.CoupledSample d)} (hS : MeasurableSet S)
    (hSt : Regeneration.annealedCoupledLaw Q.measure K S ≤
      ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t))) :
    ∫⁻ ωz, S.indicator (fun ωz => ENNReal.ofReal
        |G (Carriers.reducedObservationAt t.toNNReal (ωz.1, ωz.2.1))|) ωz
        ∂(Regeneration.annealedCoupledLaw Q.measure K) ≤
      ENNReal.ofReal (Real.sqrt C * Real.exp (-(c / 4) * lam ^ 2 * t)) *
        (∫⁻ w, ENNReal.ofReal |G w| ^ (2 * (q / (q - 1))) ∂(Carriers.reducedReferenceLaw Q)) ^
          ((q - 1) / q * (1 / 2)) := by
  set μ := Regeneration.annealedCoupledLaw Q.measure K
  set f : FieldPair d × Regeneration.CoupledSample d → ℝ≥0∞ := fun ωz =>
    ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal (ωz.1, ωz.2.1))| with hfdef
  have hobs := laplaceDensity_measurable_observation_fixed (d := d) t.toNNReal
  have hpath : Measurable fun p : FieldPair d × Regeneration.CoupledSample d => (p.1, p.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hf : Measurable f :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hG.comp (hobs.comp hpath)))
  -- The origin laws of `P` and of `P' 0` are probability laws.
  have hP0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω) := by
    filter_upwards [hprob, hmarg] with ω hω hm
    haveI := hω
    rw [← hm]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hP'0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω) := by
    filter_upwards [hP' 0 le_rfl zero_le_one] with ω hω
    obtain ⟨_, r0, hr0⟩ := hω
    haveI := r0.pathLaw_isMarkovKernel
    rw [originLaw_apply, hr0]
    infer_instance
  -- Cauchy–Schwarz.
  have hCS : ∫⁻ ωz, S.indicator f ωz ∂μ ≤
      (∫⁻ ωz, f ωz ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (μ S) ^ (1 / (2 : ℝ)) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf.aemeasurable
      (measurable_one.indicator hS).aemeasurable
    have hsq : ∫⁻ ωz, S.indicator (1 : FieldPair d × Regeneration.CoupledSample d → ℝ≥0∞) ωz ^ (2 : ℝ) ∂μ = μ S := by
      rw [← lintegral_indicator_one hS]
      refine lintegral_congr fun ωz => ?_
      by_cases h : ωz ∈ S <;> simp [h]
    simp only [Pi.mul_apply] at h
    rw [hsq] at h
    calc ∫⁻ ωz, S.indicator f ωz ∂μ = ∫⁻ ωz, f ωz * S.indicator 1 ωz ∂μ :=
          lintegral_congr fun ωz => by by_cases h : ωz ∈ S <;> simp [h]
      _ ≤ _ := h
  -- The second moment, by the fixed-time Girsanov bound.
  have htrans : ∫⁻ ωz, f ωz ^ (2 : ℝ) ∂μ = ∫⁻ z, ENNReal.ofReal
      |G (Carriers.reducedObservationAt t.toNNReal z)| ^ (2 : ℝ)
        ∂(Carriers.annealedCoordinateJoint Q.measure P hP0) :=
    lintegral_annealedCoupledLaw_path Q.measure K P hprob hmarg hP0
      (fun z => ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)| ^ (2 : ℝ))
      ((ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hG.comp hobs))).pow_const _)
  have hGir1 := annealed_sq_le_of_girsanov hGir hInv hd Q h0 h1 P hP hP0 P' hP' hP'0 hG
    t.toNNReal hq
  rw [Real.coe_toNNReal t ht] at hGir1
  set N := ∫⁻ w, ENNReal.ofReal |G w| ^ (2 * (q / (q - 1))) ∂(Carriers.reducedReferenceLaw Q)
  set E := ENNReal.ofReal (Real.exp ((1 / 2) * (q - 1) * sourceReducedBound Λ₀ * lam ^ 2 * t))
  have hexp : E * ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t)) ≤
      ENNReal.ofReal (C * Real.exp (-(c / 2) * lam ^ 2 * t)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_left_comm, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
    have hlt : 0 ≤ lam ^ 2 * t := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcq hlt]
  have hsqrt : (ENNReal.ofReal (C * Real.exp (-(c / 2) * lam ^ 2 * t))) ^ (1 / (2 : ℝ)) =
      ENNReal.ofReal (Real.sqrt C * Real.exp (-(c / 4) * lam ^ 2 * t)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      Real.mul_rpow hC (Real.exp_pos _).le, ← Real.sqrt_eq_rpow, ← Real.exp_mul,
      show -(c / 2) * lam ^ 2 * t * (1 / 2) = -(c / 4) * lam ^ 2 * t by ring]
  calc ∫⁻ ωz, S.indicator f ωz ∂μ
      ≤ (∫⁻ ωz, f ωz ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (μ S) ^ (1 / (2 : ℝ)) := hCS
    _ ≤ (E * N ^ ((q - 1) / q)) ^ (1 / (2 : ℝ)) *
          (ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t))) ^ (1 / (2 : ℝ)) :=
        mul_le_mul' (ENNReal.rpow_le_rpow (htrans.trans_le hGir1) (by norm_num))
          (ENNReal.rpow_le_rpow hSt (by norm_num))
    _ = (E * ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t))) ^ (1 / (2 : ℝ)) *
          N ^ ((q - 1) / q * (1 / 2)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ENNReal.rpow_mul]
        ring
    _ ≤ (ENNReal.ofReal (C * Real.exp (-(c / 2) * lam ^ 2 * t))) ^ (1 / (2 : ℝ)) *
          N ^ ((q - 1) / q * (1 / 2)) := by
        gcongr
    _ = ENNReal.ofReal (Real.sqrt C * Real.exp (-(c / 4) * lam ^ 2 * t)) *
          N ^ ((q - 1) / q * (1 / 2)) := by rw [hsqrt]

/-! ## Integration in time -/

/-- `∫_0^∞ a e^{-r t} dt = a / r` for `r > 0` and `a ≥ 0`, as a lower Lebesgue integral. -/
theorem lintegral_Ici_ofReal_mul_exp_neg {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (a * Real.exp (-r * t)) = ENNReal.ofReal (a / r) := by
  haveI := ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  have h1 := lintegral_expMeasure_eq_Ici r (fun _ => (1 : ℝ≥0∞)) measurable_const
  simp only [lintegral_const, measure_univ, mul_one] at h1
  have hm : Measurable fun t : ℝ => ENNReal.ofReal (r * Real.exp (-r * t)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
  calc ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (a * Real.exp (-r * t))
      = ∫⁻ t in Set.Ici (0 : ℝ),
          ENNReal.ofReal (a / r) * ENNReal.ofReal (r * Real.exp (-r * t)) := by
        refine lintegral_congr fun t => ?_
        rw [← ENNReal.ofReal_mul (div_nonneg ha hr.le)]
        congr 1
        field_simp
    _ = ENNReal.ofReal (a / r) *
          ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (r * Real.exp (-r * t)) :=
        lintegral_const_mul _ hm
    _ = ENNReal.ofReal (a / r) := by rw [← h1, mul_one]

/-- **Step 1 of Proposition 3.2 for one realization** (`paper/main.tex` 457-480): with
`q = p / (p - 2)`, so that `2q / (q - 1) = p`, and `(q - 1) K ≤ c`, the first regeneration interval
has coupled occupation at most `(4 √C / c) Δ ‖G‖_{L^p(Q)}`. -/
theorem firstReward_le_of_girsanov (hGir : GirsanovEndpointStep)
    (hInv : UnforcedEnvironmentInvarianceStep) (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam ≤ 1) (l : ℝ) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam hl0.le hl1 P)
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hmarg : ∀ᵐ ω ∂Q.measure,
      Measure.map Prod.fst (Regeneration.originCoupledLaw K ω) = originLaw P ω)
    (P' : DiffusionFamily d) (hP' : IsGMPReducedFamily hd Q.ellipticity_parameter Q P')
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hTail : Regeneration.HasFirstRegenerationTail Q.measure (Regeneration.Renewal.regenDelta lam)
      lam (l / lam) c C (Regeneration.Renewal.forceCoord hd) K)
    {G : FieldPair d → ℝ} (hG : Measurable G) {p : ℝ} (hp : 2 < p)
    (hcp : 2 / (p - 2) * sourceReducedBound Λ₀ ≤ c) :
    FirstRewardStep hd Q lam l p (4 * Real.sqrt C / c) K G := by
  unfold FirstRewardStep
  haveI := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK
  set μ := Regeneration.annealedCoupledLaw Q.measure K
  set τ : FieldPair d × Regeneration.CoupledSample d → ℝ≥0∞ := fun ωz =>
    Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) ωz.2
      (Regeneration.Renewal.forceCoord hd) 1 with hτdef
  have hτ : Measurable τ := measurable_coupledRegenerationTime hd lam l 1
  set g : FieldPair d × Regeneration.CoupledSample d → ℝ → ℝ≥0∞ := fun ωz t =>
    ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal (ωz.1, ωz.2.1))| with hgdef
  have hgm : Measurable fun p : (FieldPair d × Regeneration.CoupledSample d) × ℝ => g p.1 p.2 := by
    have hmap : Measurable fun p : (FieldPair d × Regeneration.CoupledSample d) × ℝ =>
        (p.2, (p.1.1, p.1.2.1)) :=
      measurable_snd.prodMk (measurable_fst.comp measurable_fst |>.prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_fst)))
    have h1 : Measurable fun p : (FieldPair d × Regeneration.CoupledSample d) × ℝ =>
        Carriers.reducedObservationAt p.2.toNNReal (p.1.1, p.1.2.1) :=
      Measurable.comp (g := fun z : ℝ × (FieldPair d × Path d) =>
          Carriers.reducedObservationAt z.1.toNNReal z.2)
        (f := fun p : (FieldPair d × Regeneration.CoupledSample d) × ℝ => (p.2, (p.1.1, p.1.2.1)))
        laplaceDensity_measurable_observation hmap
    have h2 : Measurable fun p : (FieldPair d × Regeneration.CoupledSample d) × ℝ =>
        ENNReal.ofReal |G (Carriers.reducedObservationAt p.2.toNNReal (p.1.1, p.1.2.1))| :=
      ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hG.comp h1))
    exact h2
  set H : FieldPair d × Regeneration.CoupledSample d → ℝ → ℝ≥0∞ := fun ωz t =>
    {x | ENNReal.ofReal t < τ x}.indicator (fun x => g x t) ωz with hHdef
  have hHm : Measurable (Function.uncurry H) := by
    have hset : MeasurableSet {p : (FieldPair d × Regeneration.CoupledSample d) × ℝ |
        ENNReal.ofReal p.2 < τ p.1} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hτ.comp measurable_fst)
    have heq : Function.uncurry H = {p : (FieldPair d × Regeneration.CoupledSample d) × ℝ |
        ENNReal.ofReal p.2 < τ p.1}.indicator fun p => g p.1 p.2 := by
      funext p
      simp only [Function.uncurry, hHdef, Set.indicator_apply, Set.mem_setOf_eq]
    rw [heq]
    exact hgm.indicator hset
  -- The first interval as an integral over `[0, ∞)`.
  have hint : ∀ ωz, ∫⁻ t in regenInterval 0 (τ ωz), g ωz t = ∫⁻ t in Set.Ici (0 : ℝ), H ωz t := by
    intro ωz
    rw [← lintegral_indicator (measurableSet_regenInterval _ _),
      ← lintegral_indicator measurableSet_Ici]
    refine lintegral_congr fun t => ?_
    by_cases h1 : 0 ≤ t
    · have hI : t ∈ Set.Ici (0 : ℝ) := h1
      rw [Set.indicator_of_mem hI]
      by_cases h2 : ENNReal.ofReal t < τ ωz
      · have hm : t ∈ regenInterval 0 (τ ωz) := ⟨h1, zero_le _, h2⟩
        have hx : ωz ∈ {x | ENNReal.ofReal t < τ x} := h2
        rw [Set.indicator_of_mem hm]
        simp only [hHdef]
        rw [Set.indicator_of_mem hx]
      · have hm : t ∉ regenInterval 0 (τ ωz) := fun h => h2 h.2.2
        have hx : ωz ∉ {x | ENNReal.ofReal t < τ x} := h2
        rw [Set.indicator_of_notMem hm]
        simp only [hHdef]
        rw [Set.indicator_of_notMem hx]
    · have hI : t ∉ Set.Ici (0 : ℝ) := h1
      have hm : t ∉ regenInterval 0 (τ ωz) := fun h => h1 h.1
      rw [Set.indicator_of_notMem hI, Set.indicator_of_notMem hm]
  -- Exponents.
  set q : ℝ := p / (p - 2) with hqdef
  have hp2 : 0 < p - 2 := by linarith
  have hq : 1 < q := (one_lt_div hp2).mpr (by linarith)
  have hq1 : q - 1 = 2 / (p - 2) := by rw [hqdef]; field_simp; ring
  have he1 : 2 * (q / (q - 1)) = p := by rw [hq1, hqdef]; field_simp
  have he2 : (q - 1) / q * (1 / 2) = 1 / p := by rw [hq1, hqdef]; field_simp
  have hcq : (q - 1) * sourceReducedBound Λ₀ ≤ c := by rw [hq1]; exact hcp
  set Np := (∫⁻ w, ENNReal.ofReal |G w| ^ p ∂(Carriers.reducedReferenceLaw Q)) ^ (1 / p)
  -- The bound at each time.
  have hpt : ∀ t ∈ Set.Ici (0 : ℝ), ∫⁻ ωz, H ωz t ∂μ ≤
      ENNReal.ofReal (Real.sqrt C * Real.exp (-(c / 4 * lam ^ 2) * t)) * Np := by
    intro t ht
    have hS : MeasurableSet {x : FieldPair d × Regeneration.CoupledSample d |
        ENNReal.ofReal t < τ x} := measurableSet_lt measurable_const hτ
    have hSt : μ {x | ENNReal.ofReal t < τ x} ≤ ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t)) := by
      have h := hTail t ht
      simp only [hτdef, regenerationTime_one_eq]
      exact h
    have hb := coupled_indicator_observation_le hGir hInv hd Q hl0.le hl1 P hP K hK.1 hmarg P' hP'
      hG hq hcq hC ht hS hSt
    rw [he1, he2] at hb
    rw [show -(c / 4 * lam ^ 2) * t = -(c / 4) * lam ^ 2 * t by ring]
    exact hb
  have hr : 0 < c / 4 * lam ^ 2 := by positivity
  have hm : Measurable fun t : ℝ =>
      ENNReal.ofReal (Real.sqrt C * Real.exp (-(c / 4 * lam ^ 2) * t)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
  have hΔ : ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ) = (lam ^ 2)⁻¹ := by
    simp only [Regeneration.Renewal.regenDelta]
    exact Real.coe_toNNReal _ (by positivity)
  have hnorm : eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) = Np := by
    rw [eLpNorm_eq_lintegral_rpow_enorm (by rw [Ne, ENNReal.ofReal_eq_zero]; linarith)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by linarith)]
    simp only [Real.enorm_eq_ofReal_abs]
    rfl
  calc ∫⁻ ωz, (∫⁻ t in regenInterval 0 (τ ωz), g ωz t) ∂μ
      = ∫⁻ ωz, (∫⁻ t in Set.Ici (0 : ℝ), H ωz t) ∂μ := lintegral_congr hint
    _ = ∫⁻ t in Set.Ici (0 : ℝ), ∫⁻ ωz, H ωz t ∂μ :=
        lintegral_lintegral_swap hHm.aemeasurable
    _ ≤ ∫⁻ t in Set.Ici (0 : ℝ),
          ENNReal.ofReal (Real.sqrt C * Real.exp (-(c / 4 * lam ^ 2) * t)) * Np :=
        setLIntegral_mono' measurableSet_Ici hpt
    _ = ENNReal.ofReal (Real.sqrt C / (c / 4 * lam ^ 2)) * Np := by
        rw [lintegral_mul_const _ hm, lintegral_Ici_ofReal_mul_exp_neg hr (Real.sqrt_nonneg C)]
    _ = ENNReal.ofReal (4 * Real.sqrt C / c *
          ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ)) *
          eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) := by
        rw [hΔ, hnorm]
        congr 2
        field_simp

/-- **The Girsanov step of Proposition 3.2** (`regen.first-reward`, `paper/main.tex` 457-480), from
the per-environment Girsanov bound, the force-zero invariance of `Q`, the existence of the reduced
family and the first regeneration tail. The exponent is `p₀ = 2 + 2 max(K, 1) / c` and the constant
`4 √(max C 0) / c`, where `K = sourceReducedBound Λ₀` and `c, C` are the tail constants. -/
theorem firstRewardStepFrozen_of_girsanov (hGir : GirsanovEndpointStep)
    (hInv : UnforcedEnvironmentInvarianceStep) (hFam : External.GMPReducedFamilyExistence)
    (hTail : GMPCouplingTailsV2Input) : FirstRewardStepFrozen := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hT⟩ := hTail d hd Λ₀ r₀
  refine ⟨l₀, hl₀, fun l hl δ hδ0 hδ1 => ?_⟩
  obtain ⟨c, C, hc, hcC⟩ := hT l hl δ hδ0 hδ1
  set M := max (sourceReducedBound Λ₀) 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMc : 0 < 2 * M / c := by positivity
  refine ⟨2 + 2 * M / c, by linarith, fun p hp => ?_⟩
  have hp2 : 2 < p := by linarith
  refine ⟨4 * Real.sqrt (max C 0) / c, by positivity, ?_⟩
  intro Q lam hl0 hl1 P K hK G hGloc _
  obtain ⟨P', hP'⟩ := hFam d hd Λ₀ r₀ Q
  have hcp : 2 / (p - 2) * sourceReducedBound Λ₀ ≤ c := by
    have h1 : 2 / (p - 2) ≤ c / M := by
      rw [div_le_div_iff₀ (by linarith) hM]
      have h2 : 2 * M / c ≤ p - 2 := by linarith
      rw [div_le_iff₀ hc] at h2
      linarith
    calc 2 / (p - 2) * sourceReducedBound Λ₀ ≤ 2 / (p - 2) * M :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (div_nonneg (by norm_num) (by linarith))
      _ ≤ c / M * M := mul_le_mul_of_nonneg_right h1 hM.le
      _ = c := div_mul_cancel₀ c hM.ne'
  have hTl := (hcC lam hl0 hl1 Q P K hK).2
  have hTl' : Regeneration.HasFirstRegenerationTail Q.measure
      (Regeneration.Renewal.regenDelta lam) lam (l / lam) c (max C 0)
      (Regeneration.Renewal.forceCoord hd) K := fun t ht =>
    (hTl t ht).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
  exact firstReward_le_of_girsanov hGir hInv hd Q hl0 hl1 l P hK.2.2.1 K hK.1 hK.2.1.1 P' hP'
    hc (le_max_right _ _) hTl' (Entropy.measurable_of_localSigma_vec hGloc) hp2 hcp

end EinsteinRelation
