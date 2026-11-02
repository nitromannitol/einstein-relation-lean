import EinsteinFull.Blueprint.G1.Proofs.SbxS4RemainderMoment
import EinsteinFull.Blueprint.G1.Proofs.SbxS2KmDecomp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
Actual endpoint support for `rt:km-decomp`.

The endpoint below is evaluated under the supplied annealed coupling. Its law
is absolutely continuous with respect to the literal reduced environment law.
This justifies representative transport without a semigroup realization premise.
The bounded continuous time-continuity results concern these actual path
observations; they do not assert a full stationary L² generator identification.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- The literal environment seen at time `t` in the supplied coupled sample. -/
def sbxS4CoupledEndpoint {d : ℕ} (t : ℝ≥0)
    (w : FieldPair d × Regeneration.CoupledSample d) : FieldPair d :=
  translate (w.2.1 t) (reduce w.1)

/-- Endpoint evaluation is jointly measurable in the environment and sample. -/
theorem sbxS4_measurable_coupledEndpoint {d : ℕ} (t : ℝ≥0) :
    Measurable (sbxS4CoupledEndpoint (d := d) t) := by
  exact Probability.continuous_translate.measurable.comp
    (((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk
      (Probability.measurable_reduce.comp measurable_fst))

/-- Equality of measurable reduced-law representatives survives the actual
annealed endpoint, including the origin-a.e. path marginal qualifier. -/
theorem sbxS4_ae_eq_coupledEndpoint {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (t : ℝ≥0) {f g : FieldPair d → ℂ} (hf : Measurable f) (hg : Measurable g)
    (heq : f =ᵐ[reducedLaw Q] g) :
    (fun w => f (sbxS4CoupledEndpoint t w)) =ᵐ[Regeneration.annealedCoupledLaw Q.measure K]
      (fun w => g (sbxS4CoupledEndpoint t w)) := by
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun (hf.comp (sbxS4_measurable_coupledEndpoint t))
      (hg.comp (sbxS4_measurable_coupledEndpoint t)))
  filter_upwards [Probability.probabilityPart_ae_eq Q.measure
      (Regeneration.originCoupledLaw K) hK.1.1, hK.2.1.1,
    SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q lam h0 h1 P hK.2.2.1 t hf hg heq]
    with ω hκ hpath hω
  change Probability.probabilityPart (Regeneration.originCoupledLaw K) ω = K (0, ω) at hκ
  rw [hκ]
  have he : ∀ᵐ γ ∂(K (0, ω)).map Prod.fst,
      f (translate (γ t) (reduce ω)) = g (translate (γ t) (reduce ω)) := by
    rw [hpath]
    exact hω
  exact ae_of_ae_map measurable_fst.aemeasurable he

/-- The actual coupled endpoint law charges no reduced-law null set.
This is absolute continuity, with no assertion of forced invariance. -/
theorem sbxS4_coupledEndpoint_absolutelyContinuous {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K) (t : ℝ≥0) :
    (Regeneration.annealedCoupledLaw Q.measure K).map (sbxS4CoupledEndpoint t) ≪
      reducedLaw Q := by
  classical
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  have heq : s.indicator (fun _ : FieldPair d => (1 : ℂ)) =ᵐ[reducedLaw Q]
      fun _ => 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hs0] with ω hω
    exact Set.indicator_of_notMem hω _
  have hend := sbxS4_ae_eq_coupledEndpoint hd Q lam l δ h0 h1 P K hK t
    (measurable_const.indicator hs) measurable_const heq
  rw [Measure.map_apply (sbxS4_measurable_coupledEndpoint t) hs,
    measure_eq_zero_iff_ae_notMem]
  filter_upwards [hend] with w hw
  intro hmem
  change sbxS4CoupledEndpoint t w ∈ s at hmem
  have hz : (1 : ℂ) = 0 := by
    simpa only [Set.indicator_of_mem hmem] using hw
  exact one_ne_zero hz

/-- Absolute continuity transports arbitrary a.e. equal functions, without
imposing measurability on the chosen representatives. -/
theorem sbxS4_ae_eq_coupledEndpoint_of_ae_eq {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (t : ℝ≥0) {E : Type*} {f g : FieldPair d → E} (heq : f =ᵐ[reducedLaw Q] g) :
    (fun w => f (sbxS4CoupledEndpoint t w)) =ᵐ[Regeneration.annealedCoupledLaw Q.measure K]
      (fun w => g (sbxS4CoupledEndpoint t w)) :=
  ae_of_ae_map (sbxS4_measurable_coupledEndpoint t).aemeasurable
    ((sbxS4_coupledEndpoint_absolutelyContinuous hd Q lam l δ h0 h1 P K hK t).ae_eq heq)

/-- A reduced-law a.e. measurable observation is a.e. measurable at the
literal coupled endpoint; no pointwise representative assumption is added. -/
theorem sbxS4_aestronglyMeasurable_coupledEndpoint {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (t : ℝ≥0) {f : FieldPair d → ℂ} (hf : AEStronglyMeasurable f (reducedLaw Q)) :
    AEStronglyMeasurable (fun w => f (sbxS4CoupledEndpoint t w))
      (Regeneration.annealedCoupledLaw Q.measure K) := by
  exact (hf.mono_ac
    (sbxS4_coupledEndpoint_absolutelyContinuous hd Q lam l δ h0 h1 P K hK t)).comp_measurable
      (sbxS4_measurable_coupledEndpoint t)

/-- Replacing both observations by their reduced-law representatives preserves
the actual annealed bilinear covariance. No integrability premise is needed
for this equality of literal Bochner integrals. -/
theorem sbxS4_coupled_covariance_congr {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (t : ℝ≥0) {F F' G G' : FieldPair d → ℂ}
    (hF : F =ᵐ[reducedLaw Q] F') (hG : G =ᵐ[reducedLaw Q] G') :
    (∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
      ∂Regeneration.annealedCoupledLaw Q.measure K) =
    ∫ w, F' (reduce w.1) * G' (sbxS4CoupledEndpoint t w)
      ∂Regeneration.annealedCoupledLaw Q.measure K := by
  apply integral_congr_ae
  filter_upwards [(sbxS2_reducedFst_measurePreserving Q K hK.1).quasiMeasurePreserving.ae hF,
    sbxS4_ae_eq_coupledEndpoint_of_ae_eq hd Q lam l δ h0 h1 P K hK t hG]
    with w hFw hGw
  rw [hFw, hGw]

/-- A real local complex L² class has its actual local real representative
with exactly the same higher moment norm. -/
theorem sbxS4_realLocal_representative {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (F : Lp ℂ 2 (reducedLaw Q))
    (hlocal : IsRealLocalObservation Q R F) (p : ℝ≥0∞)
    (hFp : MemLp (F : FieldPair d → ℂ) p (reducedLaw Q)) :
    ∃ f : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < R}] f ∧
      (fun ω => (f ω : ℂ)) =ᵐ[reducedLaw Q] (F : FieldPair d → ℂ) ∧
      MemLp f p (reducedLaw Q) ∧
      eLpNorm f p (reducedLaw Q) = eLpNorm (F : FieldPair d → ℂ) p (reducedLaw Q) := by
  obtain ⟨f, hf, heq⟩ := hlocal
  have hfm : Measurable f := hf.mono (Probability.localSigma_le_borel _) le_rfl
  have hnorm : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ = ‖F ω‖ := by
    filter_upwards [heq] with ω hω
    rw [← Complex.norm_real, hω]
  exact ⟨f, hf, heq,
    (memLp_congr_norm hfm.aestronglyMeasurable hFp.aestronglyMeasurable hnorm).mpr hFp,
    eLpNorm_congr_norm_ae hfm.aestronglyMeasurable hFp.aestronglyMeasurable hnorm⟩

/-- The real representative of a centered complex class is centered. -/
theorem sbxS4_real_representative_centered {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (F : Lp ℂ 2 (reducedLaw Q))
    {f : FieldPair d → ℝ}
    (heq : (fun ω => (f ω : ℂ)) =ᵐ[reducedLaw Q] (F : FieldPair d → ℂ))
    (hzero : (∫ ω, F ω ∂reducedLaw Q) = 0) :
    (∫ ω, f ω ∂reducedLaw Q) = 0 := by
  apply Complex.ofReal_eq_zero.mp
  rw [← integral_complex_ofReal, integral_congr_ae heq, hzero]

/-- The actual path covariance of real local complex L² observations obeys
the positive-force estimate with one structural witness tuple. This uses only
the four prescribed dependency statements, and does not identify the canonical
semigroup with the actual path family. -/
theorem sbxS4_positive_complex_path_covariance_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ), l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
    IsRealLocalObservation Q (A / lam) F →
    IsRealLocalObservation Q (A / lam) G →
    MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
    ‖∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
      ∂Regeneration.annealedCoupledLaw Q.measure K‖ ≤
      C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hsep, hdecay⟩ :=
    sbxS2_covariance_radius_decay_of_deps hfactor hphase hmany hrem d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨p, c, C, hp, hc, hC, hb⟩ := hdecay l hl δ hδ₀ hδ₁
  refine ⟨p, c, C, hp, hc, hC, ?_⟩
  intro Q lam h₀ h₁ P K hK hD A hA F G hFl hGl hFp hGp hzero t
  obtain ⟨f, hf, hfF, hfp, hfnorm⟩ :=
    sbxS4_realLocal_representative Q (A / lam) F hFl (ENNReal.ofReal p) hFp
  obtain ⟨g, hg, hgG, hgp, hgnorm⟩ :=
    sbxS4_realLocal_representative Q (A / lam) G hGl (ENNReal.ofReal p) hGp
  have hfzero := sbxS4_real_representative_centered Q F hfF hzero
  have hcov := sbxS4_coupled_covariance_congr hd Q lam l δ h₀.le h₁ P K hK t
    hfF.symm hgG.symm
  rw [hcov]
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hbound := hb Q lam h₀ h₁ P K hK hD A hA f g hf hg hfp hgp hfzero t
  rw [hfnorm, hgnorm] at hbound
  exact hbound

/-- The literal coupled endpoint at time zero is the reduced starting
environment, on the actual annealed law. -/
theorem sbxS4_coupledEndpoint_zero {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K) :
    sbxS4CoupledEndpoint 0 =ᵐ[Regeneration.annealedCoupledLaw Q.measure K]
      fun w => reduce w.1 := by
  have hstart : ∀ᵐ w : FieldPair d × Regeneration.CoupledSample d
      ∂Regeneration.annealedCoupledLaw Q.measure K, w.2.1 0 = 0 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp measurable_snd.fst)
        measurable_const)
    filter_upwards [Probability.probabilityPart_ae_eq Q.measure
        (Regeneration.originCoupledLaw K) hK.1.1, hK.2.1.1, hK.2.2.1]
      with ω hκ hpath hω
    change Probability.probabilityPart (Regeneration.originCoupledLaw K) ω = K (0, ω) at hκ
    rw [hκ]
    obtain ⟨_, R, hR⟩ := hω
    have hstart : ∀ᵐ γ ∂P (0, ω), γ 0 = 0 := by
      rw [hR 0]
      exact R.pathLaw_starts_at 0
    have he : ∀ᵐ γ ∂(K (0, ω)).map Prod.fst, γ 0 = 0 := by
      rwa [hpath]
    exact ae_of_ae_map measurable_fst.aemeasurable he
  filter_upwards [hstart] with w hw
  change translate (w.2.1 0) (reduce w.1) = reduce w.1
  rw [hw, translate_zero]

/-- Bounded continuous observations along the supplied continuous paths have
continuous annealed expectations, for every actual coupling. -/
theorem sbxS4_continuous_coupled_endpoint_integral {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    {f : FieldPair d → ℂ} (hf : Continuous f) (B : ℝ) (hb : ∀ ω, ‖f ω‖ ≤ B) :
    Continuous (fun t : ℝ≥0 => ∫ w, f (sbxS4CoupledEndpoint t w)
      ∂Regeneration.annealedCoupledLaw Q.measure K) := by
  have := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => B)
    (Filter.Eventually.of_forall fun s =>
      (hf.measurable.comp (sbxS4_measurable_coupledEndpoint s)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => Filter.Eventually.of_forall fun w => hb _)
    (integrable_const B)
  apply Filter.Eventually.of_forall
  intro w
  exact (hf.comp (Probability.continuous_translate.comp
    (w.2.1.continuous.prodMk continuous_const))).continuousAt

/-- Bounded continuous actual path observations converge in mean square to
the reduced starting observation. This establishes time-zero continuity on
this class, without assuming a stationary semigroup realization. -/
theorem sbxS4_coupled_endpoint_mean_square_zero {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    {f : FieldPair d → ℂ} (hf : Continuous f) (B : ℝ) (hb : ∀ ω, ‖f ω‖ ≤ B) :
    Tendsto (fun t : ℝ≥0 => ∫ w,
      ‖f (sbxS4CoupledEndpoint t w) - f (reduce w.1)‖ ^ 2
        ∂Regeneration.annealedCoupledLaw Q.measure K) (𝓝 0) (𝓝 0) := by
  have := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hlim : ∀ᵐ w ∂Regeneration.annealedCoupledLaw Q.measure K,
      Tendsto (fun t : ℝ≥0 => ‖f (sbxS4CoupledEndpoint t w) - f (reduce w.1)‖ ^ 2)
        (𝓝 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [sbxS4_coupledEndpoint_zero hd Q lam l δ h0 h1 P K hK] with w hw
    have hc : Continuous (fun t : ℝ≥0 =>
        ‖f (sbxS4CoupledEndpoint t w) - f (reduce w.1)‖ ^ 2) :=
      ((hf.comp (Probability.continuous_translate.comp
        (w.2.1.continuous.prodMk continuous_const))).sub continuous_const).norm.pow 2
    have ht := hc.continuousAt (x := 0)
    change Tendsto _ _ _ at ht
    simpa only [hw, sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0)] using ht
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ => (2 * B) ^ 2)
    (Filter.Eventually.of_forall fun t =>
      ((((hf.measurable.comp (sbxS4_measurable_coupledEndpoint t)).sub
        (hf.measurable.comp (Probability.measurable_reduce.comp measurable_fst))).norm).pow_const 2
          |>.aestronglyMeasurable))
    (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (norm_sub_le _ _).trans ((add_le_add (hb _) (hb _)).trans_eq (two_mul B).symm))
    (integrable_const ((2 * B) ^ 2)) hlim
  simpa only [integral_zero, Pi.sub_apply, Function.comp_apply] using ht

/-- The actual annealed product integral is the quenched endpoint pairing.
Only the genuine coupling marginal and product integrability enter this
Fubini identity; it contains no canonical semigroup premise. -/
theorem sbxS4_coupled_product_integral_eq_supplied {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (t : ℝ≥0) {F G : FieldPair d → ℂ} (hG : Measurable G)
    (hi : Integrable (fun w => F (reduce w.1) * G (sbxS4CoupledEndpoint t w))
      (Regeneration.annealedCoupledLaw Q.measure K)) :
    (∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
      ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ ω, F (reduce ω) *
        (∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂P (0, ω)) ∂Q.measure := by
  unfold Regeneration.annealedCoupledLaw
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [Probability.probabilityPart_ae_eq Q.measure
      (Regeneration.originCoupledLaw K) hK.1.1, hK.2.1.1] with ω hκ hpath
  change Probability.probabilityPart (Regeneration.originCoupledLaw K) ω = K (0, ω) at hκ
  change (∫ z, F (reduce ω) * G (translate (z.1 t) (reduce ω))
    ∂Probability.probabilityPart (Regeneration.originCoupledLaw K) ω) = _
  rw [hκ, integral_const_mul, ← hpath]
  congr 1
  exact (integral_map (μ := K (0, ω)) (f := fun γ : Path d => G (translate (γ t) (reduce ω)))
    measurable_fst.aemeasurable
    (hG.comp (Probability.continuous_translate.measurable.comp
      ((continuous_eval_const t).measurable.prodMk measurable_const))).aestronglyMeasurable).symm

/-- The remainder-moment dependency on the whole sample space gives actual
complex path-product integrability and higher-moment growth. The threshold,
moment exponent and growth constant precede the environment and the coupling.
This is a higher-moment estimate, not a bound on the full L² path operator. -/
theorem sbxS4_complex_path_product_growth_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (F G : FieldPair d → ℂ),
    Measurable F → Measurable G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    Integrable (fun w => F (reduce w.1) * G (sbxS4CoupledEndpoint t w))
      (Regeneration.annealedCoupledLaw Q.measure K) ∧
    (∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
      ∂Regeneration.annealedCoupledLaw Q.measure K) =
      (∫ ω, F (reduce ω) *
        (∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂P (0, ω)) ∂Q.measure) ∧
    (∫ w, ‖F (reduce w.1) * G (sbxS4CoupledEndpoint t w)‖
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
      C * Real.exp (C * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, hr⟩ :=
    hrem d hd Λ₀ r₀ 1 1 zero_lt_one zero_lt_one
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t
  have := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hwhole : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by
    simp only [one_mul, sub_self, Real.exp_zero, ENNReal.ofReal_one, measure_univ, le_rfl]
  obtain ⟨hprod, hbound⟩ := hr Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    (fun ω => ‖F ω‖) (fun ω => ‖G ω‖) hF.norm hG.norm hFp.norm hGp.norm
    (lam ^ 2 * (t : ℝ)) t Set.univ (by positivity) MeasurableSet.univ hwhole
    (Regeneration.annealedCoupledLaw Q.measure K) (Set.mem_insert _ _)
  have hnorm : Integrable (fun w => ‖F (reduce w.1) * G (sbxS4CoupledEndpoint t w)‖)
      (Regeneration.annealedCoupledLaw Q.measure K) := by
    simpa only [IntegrableOn, Measure.restrict_univ, norm_mul, sbxS4CoupledEndpoint] using hprod
  have hcomplex := (integrable_norm_iff
    (((hF.comp (Probability.measurable_reduce.comp measurable_fst)).mul
      (hG.comp (sbxS4_measurable_coupledEndpoint t))).aestronglyMeasurable)).mp hnorm
  refine ⟨hcomplex, sbxS4_coupled_product_integral_eq_supplied hd Q lam l δ h₀.le h₁
    P K hK t hG hcomplex, ?_⟩
  have hb : |∫ w, ‖F (reduce w.1) * G (sbxS4CoupledEndpoint t w)‖
      ∂Regeneration.annealedCoupledLaw Q.measure K| ≤
      C * Real.exp (C * lam ^ 2 * (t : ℝ) - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
    simpa only [Measure.restrict_univ, norm_mul, sbxS4CoupledEndpoint,
      eLpNorm_norm F hFp.aestronglyMeasurable, eLpNorm_norm G hGp.aestronglyMeasurable,
      mul_assoc] using hbound
  refine (le_abs_self _).trans (hb.trans ?_)
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.exp_le_exp.mpr (sub_le_self _ (by positivity))

/-- Disintegration of actual annealed L² membership gives quenched L²
membership under the supplied path law, on one full-measure environment event.
The probability-part kernel and origin-a.e. path marginal are retained. -/
theorem sbxS4_supplied_endpoint_memLp_two_of_coupled {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (t : ℝ≥0) {F : FieldPair d → ℂ} (hF : Measurable F)
    (hFend : MemLp (fun w => F (sbxS4CoupledEndpoint t w)) 2
      (Regeneration.annealedCoupledLaw Q.measure K)) :
    ∀ᵐ ω ∂Q.measure,
      MemLp (fun γ : Path d => F (translate (γ t) (reduce ω))) 2 (P (0, ω)) := by
  have hsquare := (memLp_two_iff_integrable_sq_norm hFend.aestronglyMeasurable).mp hFend
  have hdata := (Measure.integrable_compProd_iff hsquare.aestronglyMeasurable).mp hsquare
  filter_upwards [hdata.1, Probability.probabilityPart_ae_eq Q.measure
      (Regeneration.originCoupledLaw K) hK.1.1, hK.2.1.1] with ω hω hκ hpath
  change Probability.probabilityPart (Regeneration.originCoupledLaw K) ω = K (0, ω) at hκ
  rw [hκ] at hω
  have hm : Measurable (fun γ : Path d => F (translate (γ t) (reduce ω))) :=
    hF.comp (Probability.continuous_translate.measurable.comp
      ((continuous_eval_const t).measurable.prodMk measurable_const))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  rw [← hpath]
  apply (integrable_map_measure (hm.norm.pow_const 2).aestronglyMeasurable
    measurable_fst.aemeasurable).mpr
  exact hω

/-- Actual coupled endpoints of higher-moment observations lie in L². The
moment exponent is chosen before the environment, and the squared-moment
bound is derived from the literal remainder dependency rather than a path
realization premise. -/
theorem sbxS4_coupled_endpoint_memLp_two_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (F : FieldPair d → ℂ),
    Measurable F → MemLp F (2 * ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    MemLp (fun w => F (sbxS4CoupledEndpoint t w)) 2
      (Regeneration.annealedCoupledLaw Q.measure K) ∧
    (∀ᵐ ω ∂Q.measure,
      MemLp (fun γ : Path d => F (translate (γ t) (reduce ω))) 2 (P (0, ω))) ∧
    (∫ w, ‖F (sbxS4CoupledEndpoint t w)‖ ^ 2
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
      C * Real.exp (C * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (2 * ENNReal.ofReal p) (reducedLaw Q)).toReal ^ 2 := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p, C, hl₀, hsep, hp, hC, hgrowth⟩ :=
    sbxS4_complex_path_product_growth_of_remainder hrem d hd Λ₀ r₀
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F hF hFp t
  have := reducedLaw_probability Q
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hp
  have hsquare : MemLp (fun ω => ‖F ω‖ ^ 2) (ENNReal.ofReal p) (reducedLaw Q) := by
    convert hFp.norm_rpow_div (2 : ℝ≥0∞) using 1
    · ext ω
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    · rw [div_eq_mul_inv, mul_comm (2 : ℝ≥0∞), mul_assoc,
        ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  have hcast : AEStronglyMeasurable
      (fun ω => ((‖F ω‖ ^ 2 : ℝ) : ℂ)) (reducedLaw Q) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hsquare.aestronglyMeasurable
  have hcastnorm : ∀ᵐ ω ∂reducedLaw Q, ‖((‖F ω‖ ^ 2 : ℝ) : ℂ)‖ = ‖‖F ω‖ ^ 2‖ :=
    Filter.Eventually.of_forall fun ω => Complex.norm_real _
  have hcastLp : MemLp (fun ω => ((‖F ω‖ ^ 2 : ℝ) : ℂ))
      (ENNReal.ofReal p) (reducedLaw Q) :=
    (memLp_congr_norm hcast hsquare.aestronglyMeasurable hcastnorm).mpr hsquare
  have hnorm : eLpNorm (fun ω => ((‖F ω‖ ^ 2 : ℝ) : ℂ))
      (ENNReal.ofReal p) (reducedLaw Q) =
      eLpNorm F (2 * ENNReal.ofReal p) (reducedLaw Q) ^ 2 := by
    rw [eLpNorm_congr_norm_ae hcast hsquare.aestronglyMeasurable hcastnorm]
    simpa only [Real.rpow_two, ENNReal.ofReal_ofNat, ENNReal.rpow_two,
      mul_comm] using (eLpNorm_norm_rpow F hFp.aestronglyMeasurable (by norm_num : (0 : ℝ) < 2)
        (p := ENNReal.ofReal p))
  obtain ⟨hprod, _hpair, hb⟩ := hgrowth Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    (fun _ => 1) (fun ω => ((‖F ω‖ ^ 2 : ℝ) : ℂ)) measurable_const
    (Complex.continuous_ofReal.measurable.comp (hF.norm.pow_const 2))
    (memLp_const 1) hcastLp t
  have hsquareEnd : Integrable (fun w => ‖F (sbxS4CoupledEndpoint t w)‖ ^ 2)
      (Regeneration.annealedCoupledLaw Q.measure K) := by
    simpa only [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_sq] using hprod.norm
  have hFend := (memLp_two_iff_integrable_sq_norm
    (hF.comp (sbxS4_measurable_coupledEndpoint t)).aestronglyMeasurable).mpr hsquareEnd
  refine ⟨hFend, sbxS4_supplied_endpoint_memLp_two_of_coupled hd Q lam l δ h₀.le h₁
    P K hK t hF hFend, ?_⟩
  have hone : eLpNorm (fun _ : FieldPair d => (1 : ℂ)) (ENNReal.ofReal p)
      (reducedLaw Q) = 1 := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hp0).ne' (NeZero.ne _), measure_univ,
      ENNReal.one_rpow, mul_one]
    norm_num
  simpa only [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_sq, hone,
    ENNReal.toReal_one, mul_one, hnorm, ENNReal.toReal_pow] using hb

/-- Positive-force actual covariance decay together with genuine product
integrability, for literal real local complex L² classes. One moment exponent
dominates the independently chosen growth and mixing exponents. This leaves
the path/canonical identification as a separate obligation. -/
theorem sbxS4_positive_complex_integrable_covariance_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ), l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
    IsRealLocalObservation Q (A / lam) F →
    IsRealLocalObservation Q (A / lam) G →
    MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
    Integrable (fun w => F (reduce w.1) * G (sbxS4CoupledEndpoint t w))
      (Regeneration.annealedCoupledLaw Q.measure K) ∧
    ‖∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
      ∂Regeneration.annealedCoupledLaw Q.measure K‖ ≤
      C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨lD, hlD, hsepD, hdecay⟩ :=
    sbxS4_positive_complex_path_covariance_of_deps hfactor hphase hmany hrem d hd Λ₀ r₀
  obtain ⟨lR, pR, _CR, _hlR, _hsepR, _hpR, _hCR, hgrowth⟩ :=
    sbxS4_complex_path_product_growth_of_remainder hrem d hd Λ₀ r₀
  refine ⟨max lD lR, hlD.trans_le (le_max_left _ _),
    hsepD.trans_le (by linarith only [le_max_left lD lR]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hlD' : lD ≤ l := (le_max_left _ _).trans hl
  have hlR' : lR ≤ l := (le_max_right _ _).trans hl
  obtain ⟨pD, c, C, hpD, hc, hC, hb⟩ := hdecay l hlD' δ hδ₀ hδ₁
  refine ⟨max pD pR, c, C, hpD.trans (le_max_left _ _), hc, hC, ?_⟩
  intro Q lam h₀ h₁ P K hK hD A hA F G hFl hGl hFp hGp hzero t
  have := reducedLaw_probability Q
  have hpD' : ENNReal.ofReal pD ≤ ENNReal.ofReal (max pD pR) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hpR' : ENNReal.ofReal pR ≤ ENNReal.ofReal (max pD pR) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hint := (hgrowth Q lam h₀ h₁ l δ hlR' hδ₀ hδ₁ P K hK hD F G
    (Lp.stronglyMeasurable F).measurable (Lp.stronglyMeasurable G).measurable
    (hFp.mono_exponent hpR') (hGp.mono_exponent hpR') t).1
  refine ⟨hint, ?_⟩
  have hbound := hb Q lam h₀ h₁ P K hK hD A hA F G hFl hGl
    (hFp.mono_exponent hpD') (hGp.mono_exponent hpD') hzero t
  have hFnorm := ENNReal.toReal_mono hFp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (F : FieldPair d → ℂ)) hpD')
  have hGnorm := ENNReal.toReal_mono hGp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (G : FieldPair d → ℂ)) hpD')
  exact hbound.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hFnorm (mul_nonneg hC.le (Real.exp_pos _).le))
    hGnorm ENNReal.toReal_nonneg (by positivity))

/-- Conditional averaging contracts the squared moment of an actual coupled
observation. Only the literal origin-a.e. probability clause is used. -/
theorem sbxS4_coupled_average_memLp_two {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    {H : FieldPair d × Regeneration.CoupledSample d → ℂ} (hH : StronglyMeasurable H)
    (hHlp : MemLp H 2 (Regeneration.annealedCoupledLaw Q.measure K)) :
    MemLp (fun ω => ∫ z, H (ω, z) ∂K (0, ω)) 2 Q.measure ∧
    (∫ ω, ‖∫ z, H (ω, z) ∂K (0, ω)‖ ^ 2 ∂Q.measure) ≤
      ∫ w, ‖H w‖ ^ 2 ∂Regeneration.annealedCoupledLaw Q.measure K := by
  let κ := Probability.probabilityPart (Regeneration.originCoupledLaw K)
  let M : FieldPair d → ℂ := fun ω => ∫ z, H (ω, z) ∂κ ω
  have hM : StronglyMeasurable M := hH.integral_kernel_prod_right'
  have hsquare := (memLp_two_iff_integrable_sq_norm hHlp.aestronglyMeasurable).mp hHlp
  have hdata := (Measure.integrable_compProd_iff hsquare.aestronglyMeasurable).mp hsquare
  have := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK
  have hint := (Measure.integrable_compProd_iff hHlp.aestronglyMeasurable).mp
    (hHlp.integrable (by norm_num))
  have hupper : Integrable (fun ω => ∫ z, ‖H (ω, z)‖ ^ 2 ∂κ ω) Q.measure := by
    simpa only [Real.norm_eq_abs, abs_sq] using hdata.2
  have hJensen : ∀ᵐ ω ∂Q.measure,
      ‖M ω‖ ^ 2 ≤ ∫ z, ‖H (ω, z)‖ ^ 2 ∂κ ω := by
    filter_upwards [hdata.1, hint.1, hK.1,
      Probability.probabilityPart_ae_eq Q.measure (Regeneration.originCoupledLaw K) hK.1]
      with ω hsq hi hprob hκ
    have : IsProbabilityMeasure (κ ω) := by
      change Probability.probabilityPart (Regeneration.originCoupledLaw K) ω = K (0, ω) at hκ
      change IsProbabilityMeasure (Probability.probabilityPart (Regeneration.originCoupledLaw K) ω)
      rw [hκ]
      exact hprob
    exact (convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2).map_integral_le
      (continuous_norm.pow 2).continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hi hsq
  have hMsquare : Integrable (fun ω => ‖M ω‖ ^ 2) Q.measure :=
    hupper.mono' (hM.norm.pow 2).aestronglyMeasurable
      (hJensen.mono fun _ h => by simpa only [Real.norm_eq_abs, abs_sq] using h)
  have hMLp := (memLp_two_iff_integrable_sq_norm hM.aestronglyMeasurable).mpr hMsquare
  have hM_eq : M =ᵐ[Q.measure] fun ω => ∫ z, H (ω, z) ∂K (0, ω) := by
    filter_upwards [Probability.probabilityPart_ae_eq Q.measure
      (Regeneration.originCoupledLaw K) hK.1] with ω hκ
    change Probability.probabilityPart (Regeneration.originCoupledLaw K) ω = K (0, ω) at hκ
    change (∫ z, H (ω, z)
      ∂Probability.probabilityPart (Regeneration.originCoupledLaw K) ω) = _
    rw [hκ]
  refine ⟨(memLp_congr_ae hM_eq).mp hMLp, ?_⟩
  calc
    _ = ∫ ω, ‖M ω‖ ^ 2 ∂Q.measure :=
      integral_congr_ae (hM_eq.mono fun _ h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h.symm)
    _ ≤ ∫ ω, ∫ z, ‖H (ω, z)‖ ^ 2 ∂κ ω ∂Q.measure :=
      integral_mono_ae hMsquare hupper hJensen
    _ = _ := (Measure.integral_compProd hsquare).symm

/-- Averaging over the genuine supplied paths contracts the annealed squared
moment. The origin-a.e. marginal transfers the conditional coupling average. -/
theorem sbxS4_supplied_average_memLp_two_of_coupled {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (t : ℝ≥0) {F : FieldPair d → ℂ} (hF : Measurable F)
    (hFend : MemLp (fun w => F (sbxS4CoupledEndpoint t w)) 2
      (Regeneration.annealedCoupledLaw Q.measure K)) :
    MemLp (fun ω => ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω)) 2
      Q.measure ∧
    (∫ ω, ‖∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω)‖ ^ 2 ∂Q.measure) ≤
      ∫ w, ‖F (sbxS4CoupledEndpoint t w)‖ ^ 2
        ∂Regeneration.annealedCoupledLaw Q.measure K := by
  obtain ⟨hMLp, hbound⟩ := sbxS4_coupled_average_memLp_two Q K hK.1
    (hF.comp (sbxS4_measurable_coupledEndpoint t)).stronglyMeasurable hFend
  have heq : (fun ω => ∫ z, F (sbxS4CoupledEndpoint t (ω, z)) ∂K (0, ω)) =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω) := by
    filter_upwards [hK.2.1.1] with ω hpath
    rw [← hpath]
    exact (integral_map (μ := K (0, ω))
      (f := fun γ : Path d => F (translate (γ t) (reduce ω)))
      measurable_fst.aemeasurable
      (hF.comp (Probability.continuous_translate.measurable.comp
        ((continuous_eval_const t).measurable.prodMk measurable_const))).aestronglyMeasurable).symm
  refine ⟨(memLp_congr_ae heq).mp hMLp, ?_⟩
  exact (integral_congr_ae (heq.mono fun _ h =>
    congrArg (fun z : ℂ => ‖z‖ ^ 2) h)).symm.le.trans hbound

/-- Actual supplied path averages of bounded continuous observations are
continuous in mean square over environments. This concerns the supplied laws
themselves and does not identify their generator with the frozen generator. -/
theorem sbxS4_supplied_average_mean_square_continuous {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    {f : FieldPair d → ℂ} (hf : Continuous f) (B : ℝ) (hb : ∀ ω, ‖f ω‖ ≤ B)
    (s : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => ∫ ω,
      ‖(∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)) -
        (∫ γ : Path d, f (translate (γ s) (reduce ω)) ∂P (0, ω))‖ ^ 2 ∂Q.measure)
      (𝓝 s) (𝓝 0) := by
  have := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let M : ℝ≥0 → FieldPair d → ℂ := fun t ω =>
    ∫ z, f (sbxS4CoupledEndpoint t (ω, z)) ∂K (0, ω)
  let D : ℝ≥0 → ℝ := fun t => ∫ w,
    ‖f (sbxS4CoupledEndpoint t w) - f (sbxS4CoupledEndpoint s w)‖ ^ 2
      ∂Regeneration.annealedCoupledLaw Q.measure K
  have hmeas (t : ℝ≥0) : Measurable
      (fun w => f (sbxS4CoupledEndpoint t w) - f (sbxS4CoupledEndpoint s w)) :=
    (hf.measurable.comp (sbxS4_measurable_coupledEndpoint t)).sub
      (hf.measurable.comp (sbxS4_measurable_coupledEndpoint s))
  have hnorm (t : ℝ≥0) (w : FieldPair d × Regeneration.CoupledSample d) :
      ‖f (sbxS4CoupledEndpoint t w) - f (sbxS4CoupledEndpoint s w)‖ ≤ 2 * B :=
    (norm_sub_le _ _).trans ((add_le_add (hb _) (hb _)).trans_eq (two_mul B).symm)
  have hD : Tendsto D (𝓝 s) (𝓝 0) := by
    have ht := tendsto_integral_filter_of_dominated_convergence
      (μ := Regeneration.annealedCoupledLaw Q.measure K) (fun _ => (2 * B) ^ 2)
      (Filter.Eventually.of_forall fun t => ((hmeas t).norm.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) (hnorm t w) 2)
      (integrable_const ((2 * B) ^ 2))
      (Filter.Eventually.of_forall fun w => by
        have hc : Continuous (fun t : ℝ≥0 =>
            ‖f (sbxS4CoupledEndpoint t w) - f (sbxS4CoupledEndpoint s w)‖ ^ 2) :=
          (((hf.comp (Probability.continuous_translate.comp
          (w.2.1.continuous.prodMk continuous_const))).sub continuous_const).norm.pow 2)
        have ht := hc.continuousAt (x := s)
        change Tendsto _ _ _ at ht
        simpa only [sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0)] using ht)
    simpa only [D, integral_zero] using ht
  have hbound (t : ℝ≥0) : (∫ ω, ‖M t ω - M s ω‖ ^ 2 ∂Q.measure) ≤ D t := by
    have hdiff := MemLp.of_bound (p := (2 : ℝ≥0∞))
      (μ := Regeneration.annealedCoupledLaw Q.measure K) (hmeas t).aestronglyMeasurable
      (2 * B) (Filter.Eventually.of_forall (hnorm t))
    obtain ⟨_hmean, hmeanbound⟩ := sbxS4_coupled_average_memLp_two Q K hK.1
      (hmeas t).stronglyMeasurable hdiff
    have heq : (fun ω => ∫ z, f (sbxS4CoupledEndpoint t (ω, z)) -
        f (sbxS4CoupledEndpoint s (ω, z)) ∂K (0, ω)) =ᵐ[Q.measure]
        fun ω => M t ω - M s ω := by
      filter_upwards [hK.1.1] with ω hprob
      letI := hprob
      have hi (u : ℝ≥0) : Integrable
          (fun z => f (sbxS4CoupledEndpoint u (ω, z))) (K (0, ω)) :=
        (integrable_const B).mono'
          ((hf.measurable.comp (sbxS4_measurable_coupledEndpoint u)).comp
            measurable_prodMk_left).aestronglyMeasurable
          (Filter.Eventually.of_forall fun _ => hb _)
      exact integral_sub (hi t) (hi s)
    exact (integral_congr_ae (heq.mono fun _ h =>
      congrArg (fun z : ℂ => ‖z‖ ^ 2) h)).symm.le.trans hmeanbound
  have hM : Tendsto (fun t => ∫ ω, ‖M t ω - M s ω‖ ^ 2 ∂Q.measure) (𝓝 s) (𝓝 0) :=
    squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) hbound hD
  have heq (t : ℝ≥0) : M t =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω) := by
    filter_upwards [hK.2.1.1] with ω hpath
    change (∫ z, f (translate (z.1 t) (reduce ω)) ∂K (0, ω)) = _
    rw [← hpath]
    exact (integral_map (μ := K (0, ω))
      (f := fun γ : Path d => f (translate (γ t) (reduce ω)))
      measurable_fst.aemeasurable
      (hf.measurable.comp (Probability.continuous_translate.measurable.comp
        ((continuous_eval_const t).measurable.prodMk measurable_const))).aestronglyMeasurable).symm
  apply hM.congr'
  exact Filter.Eventually.of_forall fun t => integral_congr_ae <| by
    filter_upwards [heq t, heq s] with ω ht hs
    rw [ht, hs]

/-- The literal supplied GMP expectation at time zero is the starting reduced
observation, without any coupling or stationary realization premise. -/
theorem sbxS4_supplied_average_zero {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (f : FieldPair d → ℂ) :
    (fun ω => ∫ γ : Path d, f (translate (γ 0) (reduce ω)) ∂P (0, ω)) =ᵐ[Q.measure]
      fun ω => f (reduce ω) := by
  filter_upwards [hP] with ω hω
  obtain ⟨_, R, hR⟩ := hω
  rw [hR 0]
  have := R.pathLaw_isMarkovKernel.isProbabilityMeasure 0
  calc
    _ = ∫ _ : Path d, f (reduce ω) ∂R.pathLaw 0 := by
      apply integral_congr_ae
      filter_upwards [R.pathLaw_starts_at 0] with γ hγ
      change γ 0 = 0 at hγ
      rw [hγ, translate_zero]
    _ = _ := by simp

/-- The supplied path averaging map has a genuine L² bound on higher-moment
inputs. Its exponent and constants precede all environments and couplings.
This is not a full L²-to-L² operator bound. -/
theorem sbxS4_supplied_average_growth_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (F : FieldPair d → ℂ),
    Measurable F → MemLp F (2 * ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    MemLp (fun ω => ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω)) 2 Q.measure ∧
    (∫ ω, ‖∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω)‖ ^ 2 ∂Q.measure) ≤
      C * Real.exp (C * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (2 * ENNReal.ofReal p) (reducedLaw Q)).toReal ^ 2 := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p, C, hl₀, hsep, hp, hC, hgrowth⟩ :=
    sbxS4_coupled_endpoint_memLp_two_of_remainder hrem d hd Λ₀ r₀
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F hF hFp t
  obtain ⟨hend, _hquenched, hbound⟩ :=
    hgrowth Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F hF hFp t
  obtain ⟨hmean, hmeanbound⟩ :=
    sbxS4_supplied_average_memLp_two_of_coupled hd Q lam l δ h₀.le h₁ P K hK t hF hend
  exact ⟨hmean, hmeanbound.trans hbound⟩

/-- The squared Hilbert norm of an actual complex L² class is its squared
moment. This also applies to the supplied conditional averages constructed here. -/
theorem sbxS4_L2_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : Lp ℂ 2 μ) : ‖u‖ ^ 2 = ∫ ω, ‖u ω‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

/-- An L² starting observation can be paired integrably with any actual
endpoint observation having a finite second moment. This gives the literal
annealed/quenched pairing identity without higher moments on the test function. -/
theorem sbxS4_L2_pairing_eq_supplied {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (t : ℝ≥0) {F G : FieldPair d → ℂ} (hF : MemLp F 2 (reducedLaw Q))
    (hG : Measurable G)
    (hGend : MemLp (fun w => G (sbxS4CoupledEndpoint t w)) 2
      (Regeneration.annealedCoupledLaw Q.measure K)) :
    Integrable (fun w => F (reduce w.1) * G (sbxS4CoupledEndpoint t w))
      (Regeneration.annealedCoupledLaw Q.measure K) ∧
    (∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
      ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ ω, F (reduce ω) *
        (∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂P (0, ω)) ∂Q.measure := by
  have hfirst := hF.comp_measurePreserving (sbxS2_reducedFst_measurePreserving Q K hK.1)
  have hi := hfirst.integrable_mul hGend
  exact ⟨hi, sbxS4_coupled_product_integral_eq_supplied hd Q lam l δ h0 h1 P K hK t hG hi⟩

/-- Actual supplied averaging defines a continuous complex linear map from the
higher-moment reduced-law space to L² of the original environment law. The
representation and bound are derived from the remainder estimate and the
literal coupling, without a semigroup realization assumption. -/
theorem sbxS4_supplied_average_operator_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ ∃ hp : 2 ≤ p, 0 < C ∧
    letI : Fact (1 ≤ 2 * ENNReal.ofReal p) := ⟨by
      have h : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
        simpa only [ENNReal.ofReal_one] using
          (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
      exact h.trans (le_mul_of_one_le_left (by positivity) (by norm_num))⟩
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0) (t : ℝ≥0),
    ∃ T : Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q) →L[ℂ] Lp ℂ 2 Q.measure,
      (∀ F, T F =ᵐ[Q.measure]
        fun ω => ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω)) ∧
      (∀ F, ‖T F‖ ^ 2 ≤ C * Real.exp (C * lam ^ 2 * (t : ℝ)) * ‖F‖ ^ 2) ∧
      ‖T‖ ≤ Real.sqrt (C * Real.exp (C * lam ^ 2 * (t : ℝ))) := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p, C, hl₀, hsep, hp, hC, hgrowth⟩ :=
    sbxS4_coupled_endpoint_memLp_two_of_remainder hrem d hd Λ₀ r₀
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  letI : Fact (1 ≤ 2 * ENNReal.ofReal p) := ⟨by
    have h : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      simpa only [ENNReal.ofReal_one] using
          (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
    exact h.trans (le_mul_of_one_le_left (by positivity) (by norm_num))⟩
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD t
  let M : Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q) → FieldPair d → ℂ :=
    fun F ω => ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω)
  have hdata (F : Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q)) :
      (∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => F (translate (γ t) (reduce ω))) (P (0, ω))) ∧
      MemLp (M F) 2 Q.measure ∧
      (∫ ω, ‖M F ω‖ ^ 2 ∂Q.measure) ≤
        C * Real.exp (C * lam ^ 2 * (t : ℝ)) * ‖F‖ ^ 2 := by
    have hF : Measurable F := (Lp.stronglyMeasurable F).measurable
    obtain ⟨hend, hquenched, hbound⟩ :=
      hgrowth Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F hF (Lp.memLp F) t
    obtain ⟨hmean, hmeanbound⟩ :=
      sbxS4_supplied_average_memLp_two_of_coupled hd Q lam l δ h₀.le h₁ P K hK t hF hend
    have hprob := hK.2.2.1
    have hi : ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => F (translate (γ t) (reduce ω))) (P (0, ω)) := by
      filter_upwards [hquenched, hprob] with ω hω hP
      obtain ⟨_, R, hR⟩ := hP
      have : IsProbabilityMeasure (P (0, ω)) := by
        rw [hR 0]
        exact R.pathLaw_isMarkovKernel.isProbabilityMeasure 0
      exact hω.integrable (by norm_num)
    exact ⟨hi, hmean, by simpa only [Lp.norm_def] using hmeanbound.trans hbound⟩
  let L : Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q) →ₗ[ℂ] Lp ℂ 2 Q.measure :=
    { toFun := fun F => (hdata F).2.1.toLp (M F)
      map_add' := by
        intro F G
        apply Lp.ext
        have he := SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q lam h₀.le h₁ P
          hK.2.2.1 t (Lp.stronglyMeasurable (F + G)).measurable
          ((Lp.stronglyMeasurable F).measurable.add (Lp.stronglyMeasurable G).measurable)
          (Lp.coeFn_add F G)
        filter_upwards [(hdata (F + G)).2.1.coeFn_toLp,
          Lp.coeFn_add ((hdata F).2.1.toLp (M F)) ((hdata G).2.1.toLp (M G)),
          (hdata F).2.1.coeFn_toLp, (hdata G).2.1.coeFn_toLp,
          (hdata F).1, (hdata G).1, he] with ω hsum hadd hF hG hiF hiG he
        rw [hsum, hadd]
        change M (F + G) ω = ((hdata F).2.1.toLp (M F)) ω +
          ((hdata G).2.1.toLp (M G)) ω
        rw [hF, hG]
        exact (integral_congr_ae he).trans (integral_add hiF hiG)
      map_smul' := by
        intro c F
        apply Lp.ext
        have he := SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q lam h₀.le h₁ P
          hK.2.2.1 t (Lp.stronglyMeasurable (c • F)).measurable
          ((Lp.stronglyMeasurable F).measurable.const_smul c) (Lp.coeFn_smul c F)
        filter_upwards [(hdata (c • F)).2.1.coeFn_toLp,
          Lp.coeFn_smul c ((hdata F).2.1.toLp (M F)),
          (hdata F).2.1.coeFn_toLp, he] with ω hsmul hcoe hF he
        rw [hsmul]
        change M (c • F) ω = (c • (hdata F).2.1.toLp (M F)) ω
        rw [hcoe]
        change M (c • F) ω = c • ((hdata F).2.1.toLp (M F)) ω
        rw [hF]
        exact (integral_congr_ae he).trans (integral_smul c _) }
  have hbound (F : Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q)) :
      ‖L F‖ ^ 2 ≤ C * Real.exp (C * lam ^ 2 * (t : ℝ)) * ‖F‖ ^ 2 := by
    rw [sbxS4_L2_norm_sq]
    have he := (hdata F).2.1.coeFn_toLp
    exact (integral_congr_ae (he.mono fun _ h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)).le.trans
      (hdata F).2.2
  let A := C * Real.exp (C * lam ^ 2 * (t : ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hnorm_bound (F : Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q)) :
      ‖L F‖ ≤ Real.sqrt A * ‖F‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hA] using hbound F
  let T := L.mkContinuous (Real.sqrt A) hnorm_bound
  exact ⟨T, fun F => (hdata F).2.1.coeFn_toLp, hbound,
    T.opNorm_le_bound (Real.sqrt_nonneg _) hnorm_bound⟩

/-- Local operator bounds extend time continuity from a dense set of inputs.
This applies to operators between different input and output Banach spaces. -/
theorem sbxS4_continuous_operator_family_of_dense
    {E H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H]
    [NormedSpace ℂ E] [NormedSpace ℂ H]
    (T : ℝ≥0 → E →L[ℂ] H) (B : ℝ≥0 → ℝ) (hB : Continuous B)
    (hbound : ∀ t, ‖T t‖ ≤ B t) {D : Set E} (hD : Dense D)
    (hcont : ∀ F ∈ D, Continuous (fun t => T t F)) :
    ∀ F, Continuous (fun t => T t F) := by
  intro F
  apply continuous_iff_continuousAt.mpr
  intro s
  let A : ℝ := max 1 (max (B s + 1) ‖T s‖)
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hs : ‖T s‖ ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hlocal : ∀ᶠ t in 𝓝 s, ‖T t‖ ≤ A := by
    have h := hB.continuousAt.eventually (gt_mem_nhds (lt_add_one (B s)))
    filter_upwards [h] with t ht
    exact (hbound t).trans (ht.le.trans
      ((le_max_left _ _).trans (le_max_right _ _)))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨G, hG, hFG⟩ := hD.exists_dist_lt F (div_pos hε (by positivity : 0 < 3 * A))
  have hsmall : A * dist F G < ε / 3 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 3 * A)).mp hFG
    nlinarith
  have hg := Metric.tendsto_nhds.mp ((hcont G hG).continuousAt (x := s)) (ε / 3) (by positivity)
  filter_upwards [hlocal, hg] with t ht htg
  have hfirst : dist (T t F) (T t G) ≤ A * dist F G := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((T t).le_opNorm _).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
  have hlast : dist (T s G) (T s F) ≤ A * dist F G := by
    rw [dist_comm, dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((T s).le_opNorm _).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
  calc
    dist (T t F) (T s F) ≤ dist (T t F) (T t G) +
        (dist (T t G) (T s G) + dist (T s G) (T s F)) :=
      (dist_triangle (T t F) (T t G) (T s F)).trans
        (add_le_add le_rfl (dist_triangle (T t G) (T s G) (T s F)))
    _ < ε := by linarith

/-- Any operator family representing the actual supplied averages is continuous
on bounded continuous observations. Only actual GMP and coupling facts enter. -/
theorem sbxS4_supplied_operator_continuous_boundedContinuous
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (T : ℝ≥0 → Lp ℂ q (reducedLaw Q) →L[ℂ] Lp ℂ 2 Q.measure)
    (hrep : ∀ t F, T t F =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω))
    (f : FieldPair d →ᵇ ℂ) :
    letI := reducedLaw_probability Q
    Continuous (fun t => T t (BoundedContinuousFunction.toLp q (reducedLaw Q) ℂ f)) := by
  letI := reducedLaw_probability Q
  let F := BoundedContinuousFunction.toLp q (reducedLaw Q) ℂ f
  have heq (t : ℝ≥0) : T t F =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω) := by
    have he := SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q lam h0 h1 P hK.2.2.1 t
      (Lp.stronglyMeasurable F).measurable f.continuous.measurable
      (BoundedContinuousFunction.coeFn_toLp q (reducedLaw Q) ℂ f)
    filter_upwards [hrep t F, he] with ω ht hω
    exact ht.trans (integral_congr_ae hω)
  apply continuous_iff_continuousAt.mpr
  intro s
  have hmoment := sbxS4_supplied_average_mean_square_continuous hd Q lam l δ h0 h1 P K hK
    f.continuous ‖f‖ (fun ω => f.norm_coe_le_norm ω) s
  have hsq : Tendsto (fun t : ℝ≥0 => ‖T t F - T s F‖ ^ 2) (𝓝 s) (𝓝 0) := by
    apply hmoment.congr'
    exact Filter.Eventually.of_forall fun t => by
      dsimp only
      rw [sbxS4_L2_norm_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (T t F) (T s F), heq t, heq s] with ω hsub ht hs
      simp only [hsub, Pi.sub_apply, ht, hs]
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

/-- The remainder estimate produces an actual supplied averaging family that
is strongly continuous for every higher-moment input. The input and output
spaces remain the literal reduced law and the original environment law. -/
theorem sbxS4_continuous_supplied_average_family_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ ∃ hp : 2 ≤ p, 0 < C ∧
    letI : Fact (1 ≤ 2 * ENNReal.ofReal p) := ⟨by
      have h : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
        simpa only [ENNReal.ofReal_one] using
          (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
      exact h.trans (le_mul_of_one_le_left (by positivity) (by norm_num))⟩
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∃ T : ℝ≥0 → Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q) →L[ℂ] Lp ℂ 2 Q.measure,
      (∀ t F, T t F =ᵐ[Q.measure]
        fun ω => ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω)) ∧
      (∀ t F, ‖T t F‖ ^ 2 ≤ C * Real.exp (C * lam ^ 2 * (t : ℝ)) * ‖F‖ ^ 2) ∧
      (∀ t, ‖T t‖ ≤ Real.sqrt (C * Real.exp (C * lam ^ 2 * (t : ℝ)))) ∧
      (∀ F, Continuous (fun t => T t F)) := by
  classical
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p, C, hl₀, hsep, hp, hC, hops⟩ :=
    sbxS4_supplied_average_operator_of_remainder hrem d hd Λ₀ r₀
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  letI : Fact (1 ≤ 2 * ENNReal.ofReal p) := ⟨by
    have h : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
    exact h.trans (le_mul_of_one_le_left (by positivity) (by norm_num))⟩
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
  choose T hrep hsquared hopnorm using hops Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
  refine ⟨T, hrep, hsquared, hopnorm, ?_⟩
  letI := reducedLaw_probability Q
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  have hfinite : 2 * ENNReal.ofReal p ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hB : Continuous (fun t : ℝ≥0 => Real.sqrt (C * Real.exp (C * lam ^ 2 * (t : ℝ)))) :=
    Real.continuous_sqrt.comp (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)))
  refine sbxS4_continuous_operator_family_of_dense T
    (fun t => Real.sqrt (C * Real.exp (C * lam ^ 2 * (t : ℝ)))) hB hopnorm
    (BoundedContinuousFunction.toLp_denseRange ℂ (reducedLaw Q) ℂ hfinite) ?_
  rintro _ ⟨f, rfl⟩
  exact sbxS4_supplied_operator_continuous_boundedContinuous hd Q lam l δ h₀.le h₁
    P K hK (2 * ENNReal.ofReal p) T hrep f

/-- Pulling back along reduction preserves the literal L² norm. -/
def sbxS4ReducedPullback {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    Lp ℂ 2 (reducedLaw Q) →ₗᵢ[ℂ] Lp ℂ 2 Q.measure :=
  Lp.compMeasurePreservingₗᵢ ℂ reduce ⟨Probability.measurable_reduce, rfl⟩

/-- The adjoint of reduction pullback represents all reduced-observable pairings
on the literal reduced-law space. It does not presume descent of its input. -/
def sbxS4ReducedAverage {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    Lp ℂ 2 Q.measure →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  ContinuousLinearMap.adjoint (sbxS4ReducedPullback Q).toContinuousLinearMap

/-- Passing to reduced-observable pairings cannot increase the L² norm. -/
theorem sbxS4_reducedAverage_norm_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (u : Lp ℂ 2 Q.measure) :
    ‖sbxS4ReducedAverage Q u‖ ≤ ‖u‖ := by
  have hnorm : ‖sbxS4ReducedAverage Q‖ ≤ 1 := by
    unfold sbxS4ReducedAverage
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact (sbxS4ReducedPullback Q).norm_toContinuousLinearMap_le
  exact ((sbxS4ReducedAverage Q).le_opNorm u).trans
    ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg u)).trans_eq (one_mul _))

/-- Averaging a reduced observable after pullback returns its original class. -/
theorem sbxS4_reducedAverage_pullback {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (F : Lp ℂ 2 (reducedLaw Q)) :
    sbxS4ReducedAverage Q (sbxS4ReducedPullback Q F) = F := by
  have h := ContinuousLinearMap.norm_map_iff_adjoint_comp_self
    (sbxS4ReducedPullback Q).toContinuousLinearMap |>.mp
      (sbxS4ReducedPullback Q).norm_map
  exact congrArg (fun A => A F) h

/-- The reduced average has exactly the pairings of the original variable
against every L² observable of the reduced environment. -/
theorem sbxS4_reducedAverage_pairing {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (F : Lp ℂ 2 (reducedLaw Q))
    (u : Lp ℂ 2 Q.measure) :
    inner ℂ F (sbxS4ReducedAverage Q u) =
      ∫ ω, inner ℂ (F (reduce ω)) (u ω) ∂Q.measure := by
  rw [sbxS4ReducedAverage, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving F
    (show MeasurePreserving reduce Q.measure (reducedLaw Q) from
      ⟨Probability.measurable_reduce, rfl⟩)] with ω hω
  exact congrArg (fun z => inner ℂ z (u ω)) hω

/-- The reduced-law representative of an actual supplied path average has the
literal annealed endpoint correlation, for every reduced L² test. -/
theorem sbxS4_reducedAverage_supplied_correlation {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (t : ℝ≥0) (F : Lp ℂ 2 (reducedLaw Q))
    {G : FieldPair d → ℂ} (hG : Measurable G)
    (hGend : MemLp (fun w => G (sbxS4CoupledEndpoint t w)) 2
      (Regeneration.annealedCoupledLaw Q.measure K))
    (u : Lp ℂ 2 Q.measure)
    (hu : u =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂P (0, ω)) :
    inner ℂ F (sbxS4ReducedAverage Q u) =
      ∫ w, inner ℂ (F (reduce w.1)) (G (sbxS4CoupledEndpoint t w))
        ∂Regeneration.annealedCoupledLaw Q.measure K := by
  have hpair := (sbxS4_L2_pairing_eq_supplied hd Q lam l δ h0 h1 P K hK t
    (Lp.memLp F).star hG hGend).2
  rw [sbxS4_reducedAverage_pairing]
  calc
    _ = ∫ ω, star (F (reduce ω)) *
        (∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂P (0, ω)) ∂Q.measure := by
      apply integral_congr_ae
      filter_upwards [hu] with ω hω
      simp only [hω, RCLike.inner_apply', Complex.star_def]
    _ = _ := by
      simpa only [RCLike.inner_apply', Pi.star_apply, Complex.star_def] using hpair.symm

/-- At time zero the reduced average of the actual supplied GMP expectation
is the original reduced L² class, rather than merely a weak initial value. -/
theorem sbxS4_reducedAverage_supplied_zero {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (F : Lp ℂ 2 (reducedLaw Q)) (u : Lp ℂ 2 Q.measure)
    (hu : u =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, F (translate (γ 0) (reduce ω)) ∂P (0, ω)) :
    sbxS4ReducedAverage Q u = F := by
  have huF : u = sbxS4ReducedPullback Q F := by
    apply Lp.ext
    exact (hu.trans (sbxS4_supplied_average_zero hd Q lam h0 h1 P hP F)).trans
      (Lp.coeFn_compMeasurePreserving F
        (show MeasurePreserving reduce Q.measure (reducedLaw Q) from
          ⟨Probability.measurable_reduce, rfl⟩)).symm
  rw [huF, sbxS4_reducedAverage_pullback]

/-- Reduction of a strongly continuous supplied averaging family preserves
strong continuity and its pointwise bounds. This produces a family on the
literal reduced-law output space without asserting a semigroup law. -/
theorem sbxS4_reducedAverage_family {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (P : QuenchedPathLaws d)
    (T : ℝ≥0 → Lp ℂ q (reducedLaw Q) →L[ℂ] Lp ℂ 2 Q.measure)
    (hrep : ∀ t G, T t G =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂P (0, ω))
    (hcont : ∀ G, Continuous (fun t => T t G)) :
    let S : ℝ≥0 → Lp ℂ q (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
      fun t => (sbxS4ReducedAverage Q).comp (T t)
    (∀ G, Continuous (fun t => S t G)) ∧
      (∀ t G, ‖S t G‖ ≤ ‖T t G‖) ∧
      (∀ t G F, inner ℂ F (S t G) =
        ∫ ω, inner ℂ (F (reduce ω))
          (∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂P (0, ω)) ∂Q.measure) := by
  refine ⟨fun G => (sbxS4ReducedAverage Q).continuous.comp (hcont G),
    fun t G => sbxS4_reducedAverage_norm_le Q (T t G), ?_⟩
  intro t G F
  change inner ℂ F (sbxS4ReducedAverage Q (T t G)) = _
  rw [sbxS4_reducedAverage_pairing]
  apply integral_congr_ae
  filter_upwards [hrep t G] with ω hω
  rw [hω]

/-- An exponentially bounded strongly continuous family has a pointwise
Bochner Laplace transform. No semigroup identity is used here. -/
theorem sbxS4_laplace_integrable_and_bound
    {E H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H]
    [NormedSpace ℂ E] [NormedSpace ℂ H]
    (T : ℝ≥0 → E →L[ℂ] H) (M a α : ℝ) (hα : a < α)
    (hcont : ∀ F, Continuous (fun t => T t F))
    (hbound : ∀ t, ‖T t‖ ≤ M * Real.exp (a * (t : ℝ))) (F : E) :
    IntegrableOn (fun t : ℝ => Real.exp (-α * t) • T t.toNNReal F) (Set.Ioi 0) ∧
      ‖∫ t : ℝ in Set.Ioi 0, Real.exp (-α * t) • T t.toNNReal F‖ ≤
        (M / (α - a)) * ‖F‖ := by
  have hdecay : a - α < 0 := sub_neg.mpr hα
  have hg : IntegrableOn (fun t : ℝ =>
      (M * ‖F‖) * Real.exp ((a - α) * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi hdecay 0).const_mul _
  have hnorm : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioi 0),
      ‖Real.exp (-α * t) • T t.toNNReal F‖ ≤
        (M * ‖F‖) * Real.exp ((a - α) * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hb := (T t.toNNReal).le_opNorm F
    have he := hbound t.toNNReal
    rw [Real.coe_toNNReal t ht.le] at he
    calc
      Real.exp (-α * t) * ‖T t.toNNReal F‖ ≤
          Real.exp (-α * t) * ((M * Real.exp (a * t)) * ‖F‖) :=
        mul_le_mul_of_nonneg_left
          (hb.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _)))
          (Real.exp_nonneg _)
      _ = (M * ‖F‖) * (Real.exp (-α * t) * Real.exp (a * t)) := by ring
      _ = (M * ‖F‖) * Real.exp ((a - α) * t) := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hc : Continuous (fun t : ℝ => Real.exp (-α * t) • T t.toNNReal F) := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((hcont F).comp (by fun_prop))
  refine ⟨hg.mono' hc.aestronglyMeasurable hnorm, ?_⟩
  calc
    ‖∫ t : ℝ in Set.Ioi 0, Real.exp (-α * t) • T t.toNNReal F‖ ≤
        ∫ t : ℝ in Set.Ioi 0, (M * ‖F‖) * Real.exp ((a - α) * t) :=
      norm_integral_le_of_norm_le hg hnorm
    _ = (M / (α - a)) * ‖F‖ := by
      rw [integral_const_mul, integral_exp_mul_Ioi hdecay]
      simp only [mul_zero, Real.exp_zero]
      rw [show a - α = -(α - a) by ring, neg_div_neg_eq]
      ring

/-- The Laplace transform is a bounded complex linear operator even when only
strong continuity, rather than operator-norm continuity, is known. -/
def sbxS4LaplaceOperator
    {E H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H]
    [NormedSpace ℂ E] [NormedSpace ℂ H]
    (T : ℝ≥0 → E →L[ℂ] H) (M a α : ℝ) (hα : a < α)
    (hcont : ∀ F, Continuous (fun t => T t F))
    (hbound : ∀ t, ‖T t‖ ≤ M * Real.exp (a * (t : ℝ))) : E →L[ℂ] H :=
  let L : E →ₗ[ℂ] H :=
    { toFun := fun F => ∫ t : ℝ in Set.Ioi 0, Real.exp (-α * t) • T t.toNNReal F
      map_add' := by
        intro F G
        simp only [map_add, smul_add]
        exact integral_add
          (sbxS4_laplace_integrable_and_bound T M a α hα hcont hbound F).1
          (sbxS4_laplace_integrable_and_bound T M a α hα hcont hbound G).1
      map_smul' := by
        intro c F
        simp only [map_smul, RingHom.id_apply]
        simp_rw [smul_comm (Real.exp (-α * _)) c]
        exact integral_smul c _ }
  L.mkContinuous (M / (α - a))
    (fun F => (sbxS4_laplace_integrable_and_bound T M a α hα hcont hbound F).2)

/-- The quantitative Laplace bound is inherited by the operator norm. -/
theorem sbxS4_laplaceOperator_norm_le
    {E H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H]
    [NormedSpace ℂ E] [NormedSpace ℂ H]
    (T : ℝ≥0 → E →L[ℂ] H) (M a α : ℝ) (hM : 0 ≤ M) (hα : a < α)
    (hcont : ∀ F, Continuous (fun t => T t F))
    (hbound : ∀ t, ‖T t‖ ≤ M * Real.exp (a * (t : ℝ))) :
    ‖sbxS4LaplaceOperator T M a α hα hcont hbound‖ ≤ M / (α - a) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM (sub_pos.mpr hα).le)
  intro F
  exact (sbxS4_laplace_integrable_and_bound T M a α hα hcont hbound F).2

/-- The reduced Laplace pairing is the integral of the literal supplied-path
correlations. The reduction is the adjoint of pullback, as above. -/
theorem sbxS4_laplace_supplied_correlation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (P : QuenchedPathLaws d)
    (T : ℝ≥0 → Lp ℂ q (reducedLaw Q) →L[ℂ] Lp ℂ 2 Q.measure)
    (hrep : ∀ t G, T t G =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂P (0, ω))
    (hcont : ∀ G, Continuous (fun t => T t G))
    (M a α : ℝ) (hα : a < α)
    (hbound : ∀ t, ‖T t‖ ≤ M * Real.exp (a * (t : ℝ)))
    (G : Lp ℂ q (reducedLaw Q)) (F : Lp ℂ 2 (reducedLaw Q)) :
    inner ℂ F (sbxS4ReducedAverage Q
        (sbxS4LaplaceOperator T M a α hα hcont hbound G)) =
      ∫ t : ℝ in Set.Ioi 0, Real.exp (-α * t) •
        (∫ ω, inner ℂ (F (reduce ω))
          (∫ γ : Path d, G (translate (γ t.toNNReal) (reduce ω)) ∂P (0, ω))
          ∂Q.measure) := by
  let B := (innerSL ℂ F).comp (sbxS4ReducedAverage Q)
  have hi := (sbxS4_laplace_integrable_and_bound T M a α hα hcont hbound G).1
  change B (∫ t : ℝ in Set.Ioi 0, Real.exp (-α * t) • T t.toNNReal G) = _
  refine (B.integral_comp_comm hi).symm.trans ?_
  apply integral_congr_ae
  filter_upwards [] with t
  change B (Real.exp (-α * t) • T t.toNNReal G) = _
  rw [B.map_smul_of_tower]
  congr 1
  change inner ℂ F (sbxS4ReducedAverage Q (T t.toNNReal G)) = _
  rw [sbxS4_reducedAverage_pairing]
  apply integral_congr_ae
  filter_upwards [hrep t.toNNReal G] with ω hω
  rw [hω]

/-- The remainder estimate produces an actual bounded reduced-law Laplace
operator whose pairings are the supplied path correlations. This construction
requires no canonical semigroup realization premise. -/
theorem sbxS4_supplied_laplace_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ ∃ hp : 2 ≤ p, 0 < C ∧
    letI : Fact (1 ≤ 2 * ENNReal.ofReal p) := ⟨by
      have h : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
        simpa only [ENNReal.ofReal_one] using
          (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
      exact h.trans (le_mul_of_one_le_left (by positivity) (by norm_num))⟩
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (α : ℝ), C * lam ^ 2 < α →
    ∃ L : Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q) →L[ℂ]
        Lp ℂ 2 (reducedLaw Q),
      ‖L‖ ≤ Real.sqrt C / (α - C * lam ^ 2) ∧
      ∀ G F, inner ℂ F (L G) =
        ∫ t : ℝ in Set.Ioi 0, Real.exp (-α * t) •
          (∫ ω, inner ℂ (F (reduce ω))
            (∫ γ : Path d, G (translate (γ t.toNNReal) (reduce ω)) ∂P (0, ω))
            ∂Q.measure) := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p, C, hl₀, hsep, hp, hC, hfamily⟩ :=
    sbxS4_continuous_supplied_average_family_of_remainder hrem d hd Λ₀ r₀
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  letI : Fact (1 ≤ 2 * ENNReal.ofReal p) := ⟨by
    have h : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
    exact h.trans (le_mul_of_one_le_left (by positivity) (by norm_num))⟩
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD α hα
  obtain ⟨T, hrep, _, hnorm, hcont⟩ := hfamily Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
  have hbound (t : ℝ≥0) : ‖T t‖ ≤ Real.sqrt C * Real.exp (C * lam ^ 2 * (t : ℝ)) := by
    have hexp : 1 ≤ Real.exp (C * lam ^ 2 * (t : ℝ)) :=
      Real.one_le_exp_iff.mpr (by positivity)
    have hsqrt : Real.sqrt (Real.exp (C * lam ^ 2 * (t : ℝ))) ≤
        Real.exp (C * lam ^ 2 * (t : ℝ)) := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨Real.exp_nonneg _, by nlinarith⟩
    calc
      ‖T t‖ ≤ Real.sqrt C * Real.sqrt (Real.exp (C * lam ^ 2 * (t : ℝ))) := by
        simpa only [Real.sqrt_mul hC.le] using hnorm t
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
  let A := sbxS4LaplaceOperator T (Real.sqrt C) (C * lam ^ 2) α hα hcont hbound
  let L := (sbxS4ReducedAverage Q).comp A
  refine ⟨L, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _
      (div_nonneg (Real.sqrt_nonneg _) (sub_pos.mpr hα).le)
    intro G
    exact (sbxS4_reducedAverage_norm_le Q (A G)).trans
      (sbxS4_laplace_integrable_and_bound T (Real.sqrt C) (C * lam ^ 2) α
        hα hcont hbound G).2
  · intro G F
    exact sbxS4_laplace_supplied_correlation Q _ P T hrep hcont
      (Real.sqrt C) (C * lam ^ 2) α hα hbound G F

open External.GantertSection7Support ProbabilityTheory

/-- The supplied reduced kernel satisfies the literal backward Dynkin identity
on every compact smooth physical test, at every specified starting point. -/
theorem sbxS4_supplied_compact_dynkin {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (f : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ∀ T : ℝ≥0,
      (∫ γ : Path d, f (γ T) ∂P (x, ω)) - f x =
        ∫ u in (0 : ℝ)..(T : ℝ), ∫ γ : Path d,
          reducedGenerator (firstCoordinateIndex hd) ω lam f (γ u.toNNReal) ∂P (x, ω) := by
  filter_upwards [hP] with ω hω x f hf hc T
  obtain ⟨hω, R, hR⟩ := hω
  rw [hR x, ← SbxS4Dynkin.physicalGenerator_zeroPotentialReducedPair]
  have he (g : Vec d → ℝ) (hg : Measurable g) (t : ℝ≥0) :
      (∫ γ : Path d, g (γ t) ∂R.pathLaw x) = ∫ y, g y ∂R.transitionKernel t x := by
    rw [← R.pathLaw_endpoint t x]
    exact (integral_map (measurable_pathPosition t).aemeasurable
      hg.aestronglyMeasurable).symm
  rw [he f hf.continuous.measurable]
  simp_rw [he _ (measurable_physicalGenerator _ _ _ _)]
  exact SbxS4Dynkin.compact_test_evolution_every_start hd
    (one_le_sourceReducedBound Q.ellipticity_parameter) R f hf hc T x

/-- The generator means in the supplied compact-test Dynkin identity are Borel
in time and uniformly bounded in time and starting point. The bound may depend
on the sampled environment and the compact test. -/
theorem sbxS4_supplied_compact_generator_mean_bounded {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (f : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Vec d,
        Measurable (fun u : ℝ => ∫ γ : Path d,
          reducedGenerator (firstCoordinateIndex hd) ω lam f (γ u.toNNReal) ∂P (x, ω)) ∧
        ∀ u : ℝ, ‖∫ γ : Path d,
          reducedGenerator (firstCoordinateIndex hd) ω lam f (γ u.toNNReal) ∂P (x, ω)‖ ≤ B := by
  filter_upwards [hP] with ω hω f hf hc
  obtain ⟨hω, R, hR⟩ := hω
  obtain ⟨B, hB, hb⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one (one_le_sourceReducedBound Q.ellipticity_parameter))
    hω lam hf hc
  refine ⟨B, hB, fun x => ?_⟩
  rw [hR x, ← SbxS4Dynkin.physicalGenerator_zeroPotentialReducedPair]
  let : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  have hm : Measurable (fun p : ℝ × Path d =>
      physicalGenerator (firstCoordinateIndex hd) (zeroPotentialReducedPair ω) lam f
        (p.2 p.1.toNNReal)) := by
    apply (measurable_physicalGenerator _ _ _ _).comp
    exact (ContinuousEval.continuous_eval (F := Path d) (X := ℝ≥0)
      (Y := Vec d)).measurable.comp
        (measurable_snd.prodMk (measurable_real_toNNReal.comp measurable_fst))
  refine ⟨hm.stronglyMeasurable.integral_prod_right'.measurable, fun u => ?_⟩
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := R.pathLaw x)
      (Eventually.of_forall fun γ => by simpa only [Real.norm_eq_abs] using hb (γ u.toNNReal)))

/-- Compact smooth observations of the actual supplied paths have Lipschitz
quenched means. This follows from their bounded measurable generator means,
without a semigroup realization hypothesis. -/
theorem sbxS4_supplied_compact_mean_lipschitz {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (f : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (x : Vec d) (s t : ℝ≥0),
        ‖(∫ γ : Path d, f (γ t) ∂P (x, ω)) -
          ∫ γ : Path d, f (γ s) ∂P (x, ω)‖ ≤ B * |(t : ℝ) - s| := by
  filter_upwards [sbxS4_supplied_compact_dynkin hd Q lam h0 h1 P hP,
    sbxS4_supplied_compact_generator_mean_bounded hd Q lam h0 h1 P hP]
    with ω he hb f hf hc
  obtain ⟨B, hB, hb⟩ := hb f hf hc
  refine ⟨B, hB, fun x s t => ?_⟩
  let g : ℝ → ℝ := fun u => ∫ γ : Path d,
    reducedGenerator (firstCoordinateIndex hd) ω lam f (γ u.toNNReal) ∂P (x, ω)
  have hi (a b : ℝ) : IntervalIntegrable g volume a b := by
    apply intervalIntegrable_iff.mpr
    let : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) := by
      unfold Set.uIoc
      infer_instance
    exact ⟨(hb x).1.aestronglyMeasurable.restrict,
      HasFiniteIntegral.of_bounded (Eventually.of_forall fun u => (hb x).2 u)⟩
  have hiT := he x f hf hc t
  have hiS := he x f hf hc s
  have hdiff : (∫ γ : Path d, f (γ t) ∂P (x, ω)) -
      ∫ γ : Path d, f (γ s) ∂P (x, ω) = ∫ u in (s : ℝ)..(t : ℝ), g u := by
    calc
      _ = ((∫ γ : Path d, f (γ t) ∂P (x, ω)) - f x) -
          ((∫ γ : Path d, f (γ s) ∂P (x, ω)) - f x) := by ring
      _ = (∫ u in (0 : ℝ)..(t : ℝ), g u) - ∫ u in (0 : ℝ)..(s : ℝ), g u := by
        rw [hiT, hiS]
      _ = _ := intervalIntegral.integral_interval_sub_left (hi 0 t) (hi 0 s)
  rw [hdiff]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun u _ => (hb x).2 u)

/-- The backward equation for a compact smooth test holds at almost every
positive time for the literal supplied quenched endpoint mean. -/
theorem sbxS4_supplied_compact_mean_ae_hasDerivAt {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (f : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        HasDerivAt (fun u : ℝ => ∫ γ : Path d, f (γ u.toNNReal) ∂P (x, ω))
          (∫ γ : Path d,
            reducedGenerator (firstCoordinateIndex hd) ω lam f (γ t.toNNReal) ∂P (x, ω)) t := by
  filter_upwards [sbxS4_supplied_compact_dynkin hd Q lam h0 h1 P hP,
    sbxS4_supplied_compact_generator_mean_bounded hd Q lam h0 h1 P hP]
    with ω he hb x f hf hc
  obtain ⟨B, -, hb⟩ := hb f hf hc
  let g : ℝ → ℝ := fun u => ∫ γ : Path d,
    reducedGenerator (firstCoordinateIndex hd) ω lam f (γ u.toNNReal) ∂P (x, ω)
  have hgi : LocallyIntegrable g volume := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    let : IsFiniteMeasure (volume.restrict K) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
    exact ⟨(hb x).1.aestronglyMeasurable.restrict,
      HasFiniteIntegral.of_bounded (Eventually.of_forall fun u => (hb x).2 u)⟩
  filter_upwards [ae_restrict_of_ae (LocallyIntegrable.ae_hasDerivAt_integral hgi),
    ae_restrict_mem measurableSet_Ioi] with t ht ht0
  apply ((ht 0).add_const (f x)).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht0] with u hu
  have h := he x f hf hc u.toNNReal
  rw [Real.coe_toNNReal u hu.le] at h
  exact sub_eq_iff_eq_add.mp h

/-- Discounted Dynkin identity on a finite time interval for the supplied paths.
The generator need only be measurable; absolute continuity of the endpoint mean
justifies integration by parts. -/
theorem sbxS4_supplied_compact_discounted_dynkin {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (f : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ∀ (α : ℝ) (T : ℝ≥0),
      (∫ u in (0 : ℝ)..(T : ℝ), Real.exp (-α * u) *
        ∫ γ : Path d, reducedGenerator (firstCoordinateIndex hd) ω lam f
          (γ u.toNNReal) ∂P (x, ω)) =
      Real.exp (-α * T) * (∫ γ : Path d, f (γ T) ∂P (x, ω)) - f x +
        α * ∫ u in (0 : ℝ)..(T : ℝ), Real.exp (-α * u) *
          ∫ γ : Path d, f (γ u.toNNReal) ∂P (x, ω) := by
  filter_upwards [sbxS4_supplied_compact_mean_lipschitz hd Q lam h0 h1 P hP,
    sbxS4_supplied_compact_mean_ae_hasDerivAt hd Q lam h0 h1 P hP,
    SbxS4Dynkin.reduced_kernel_solves_martingale_problem hd Q lam h0 h1 P hP]
    with ω hl hd' hmp x f hf hc α T
  obtain ⟨B, hB, hl⟩ := hl f hf hc
  let m : ℝ → ℝ := fun u => ∫ γ : Path d, f (γ u.toNNReal) ∂P (x, ω)
  have hml : LipschitzWith ⟨B, hB⟩
      (fun t : ℝ≥0 => ∫ γ : Path d, f (γ t) ∂P (x, ω)) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro t s
    change dist (∫ γ : Path d, f (γ t) ∂P (x, ω))
      (∫ γ : Path d, f (γ s) ∂P (x, ω)) ≤ _
    rw [dist_eq_norm, NNReal.dist_eq]
    exact hl x s t
  have hmac : AbsolutelyContinuousOnInterval m 0 T :=
    (hml.comp Real.lipschitzWith_toNNReal).lipschitzOnWith.absolutelyContinuousOnInterval
  have heac : AbsolutelyContinuousOnInterval (fun u : ℝ => Real.exp (-α * u)) 0 T :=
    (show ContDiff ℝ 1 (fun u : ℝ => Real.exp (-α * u)) by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hde (u : ℝ) : deriv (fun u : ℝ => Real.exp (-α * u)) u =
      -α * Real.exp (-α * u) := by
    simpa only [id_eq, mul_comm, mul_one] using (((hasDerivAt_id u).const_mul (-α)).exp).deriv
  have hdz := (ae_restrict_iff' measurableSet_Ioi).mp (hd' x f hf hc)
  let : IsProbabilityMeasure (P (x, ω)) := (hmp x).1
  have hmzero : m 0 = f x := by
    dsimp only [m]
    rw [Real.toNNReal_zero]
    calc
      _ = ∫ _ : Path d, f x ∂P (x, ω) := integral_congr_ae
        ((hmp x).2.1.mono fun γ hγ => congrArg f hγ)
      _ = _ := by simp
  calc
    _ = ∫ u in (0 : ℝ)..(T : ℝ), Real.exp (-α * u) * deriv m u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hdz] with u hu huI
      have hu0 : 0 < u := (Set.uIoc_of_le T.coe_nonneg ▸ huI).1
      rw [(hu hu0).deriv]
    _ = Real.exp (-α * T) * m T - Real.exp (-α * 0) * m 0 -
        ∫ u in (0 : ℝ)..(T : ℝ), deriv (fun u : ℝ => Real.exp (-α * u)) u * m u :=
      heac.integral_mul_deriv_eq_deriv_mul hmac
    _ = _ := by
      simp_rw [hde, mul_assoc]
      rw [intervalIntegral.integral_const_mul, hmzero]
      simp only [mul_zero, Real.exp_zero, one_mul, Real.toNNReal_coe, sub_neg_eq_add,
        neg_mul, m]

/-- Exponential discount makes a bounded Borel real function integrable. -/
theorem sbxS4_laplace_integrable_of_bounded (v : ℝ → ℝ) (hv : Measurable v)
    (C α : ℝ) (hvC : ∀ u, ‖v u‖ ≤ C) (hα : 0 < α) :
    IntegrableOn (fun u : ℝ => Real.exp (-α * u) * v u) (Set.Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hα) 0).mul_const C).mono'
    ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul hv).aestronglyMeasurable
  filter_upwards [] with u
  change ‖Real.exp (-α * u) * v u‖ ≤ Real.exp (-α * u) * C
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_left (hvC u) (Real.exp_pos _).le

/-- Passage from a finite discounted identity to its Laplace identity uses only
integrability of the discounted terms and boundedness of the boundary value. -/
theorem sbxS4_laplace_identity_of_discounted (m g : ℝ → ℝ) (M α z : ℝ)
    (hα : 0 < α) (hmb : ∀ u, ‖m u‖ ≤ M)
    (hmi : IntegrableOn (fun u : ℝ => Real.exp (-α * u) * m u) (Set.Ioi 0))
    (hgi : IntegrableOn (fun u : ℝ => Real.exp (-α * u) * g u) (Set.Ioi 0))
    (he : ∀ T : ℝ≥0, (∫ u in (0 : ℝ)..(T : ℝ), Real.exp (-α * u) * g u) =
      Real.exp (-α * T) * m T - z +
        α * ∫ u in (0 : ℝ)..(T : ℝ), Real.exp (-α * u) * m u) :
    (∫ u : ℝ in Set.Ioi 0, Real.exp (-α * u) * g u) =
      α * (∫ u : ℝ in Set.Ioi 0, Real.exp (-α * u) * m u) - z := by
  have hexp : Tendsto (fun u : ℝ => Real.exp (-α * u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (neg_neg_of_pos hα) tendsto_id)
  have htail : Tendsto (fun u : ℝ => Real.exp (-α * u) * m u) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun u => ?_)
      (by simpa using hexp.mul_const M)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    simpa only [neg_mul] using
      mul_le_mul_of_nonneg_left (hmb u) (Real.exp_pos (-α * u)).le
  have hleft := intervalIntegral_tendsto_integral_Ioi 0 hgi tendsto_id
  have hright := (htail.sub_const z).add
    ((intervalIntegral_tendsto_integral_Ioi 0 hmi tendsto_id).const_mul α)
  have heq : (fun T : ℝ => ∫ u in (0 : ℝ)..T, Real.exp (-α * u) * g u) =ᶠ[atTop]
      (fun T : ℝ => Real.exp (-α * T) * m T - z +
        α * ∫ u in (0 : ℝ)..T, Real.exp (-α * u) * m u) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simpa only [Real.coe_toNNReal T hT] using he T.toNNReal
  have hlim := tendsto_nhds_unique hleft (hright.congr' heq.symm)
  simpa only [zero_sub, sub_eq_neg_add, add_comm, add_zero] using hlim

#print axioms sbxS4_laplace_integrable_of_bounded
#print axioms sbxS4_laplace_identity_of_discounted

/-- The supplied path law gives the backward resolvent identity for every
compact smooth physical test. Both discounted means are genuinely integrable;
no stationary semigroup identification is used. -/
theorem sbxS4_supplied_compact_laplace_dynkin {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (f : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ∀ α : ℝ, 0 < α →
      IntegrableOn (fun u : ℝ => Real.exp (-α * u) *
        ∫ γ : Path d, f (γ u.toNNReal) ∂P (x, ω)) (Set.Ioi 0) ∧
      IntegrableOn (fun u : ℝ => Real.exp (-α * u) *
        ∫ γ : Path d, reducedGenerator (firstCoordinateIndex hd) ω lam f
          (γ u.toNNReal) ∂P (x, ω)) (Set.Ioi 0) ∧
      (∫ u : ℝ in Set.Ioi 0, Real.exp (-α * u) *
        ∫ γ : Path d, reducedGenerator (firstCoordinateIndex hd) ω lam f
          (γ u.toNNReal) ∂P (x, ω)) =
        α * (∫ u : ℝ in Set.Ioi 0, Real.exp (-α * u) *
          ∫ γ : Path d, f (γ u.toNNReal) ∂P (x, ω)) - f x := by
  filter_upwards [sbxS4_supplied_compact_discounted_dynkin hd Q lam h0 h1 P hP,
    sbxS4_supplied_compact_generator_mean_bounded hd Q lam h0 h1 P hP,
    sbxS4_supplied_compact_mean_lipschitz hd Q lam h0 h1 P hP,
    SbxS4Dynkin.reduced_kernel_solves_martingale_problem hd Q lam h0 h1 P hP]
    with ω he hg hl hmp x f hf hc α hα
  let : IsProbabilityMeasure (P (x, ω)) := (hmp x).1
  let m : ℝ → ℝ := fun u => ∫ γ : Path d, f (γ u.toNNReal) ∂P (x, ω)
  let g : ℝ → ℝ := fun u => ∫ γ : Path d,
    reducedGenerator (firstCoordinateIndex hd) ω lam f (γ u.toNNReal) ∂P (x, ω)
  obtain ⟨B, -, hg⟩ := hg f hf hc
  obtain ⟨D, hD, hl⟩ := hl f hf hc
  have hml : LipschitzWith ⟨D, hD⟩
      (fun t : ℝ≥0 => ∫ γ : Path d, f (γ t) ∂P (x, ω)) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro t s
    change dist (∫ γ : Path d, f (γ t) ∂P (x, ω))
      (∫ γ : Path d, f (γ s) ∂P (x, ω)) ≤ _
    rw [dist_eq_norm, NNReal.dist_eq]
    exact hl x s t
  have hmm : Measurable m := (hml.continuous.comp continuous_real_toNNReal).measurable
  let fB := Work.W5.gantertCompactObservable f hf.continuous hc
  have hmb (u : ℝ) : ‖m u‖ ≤ ‖fB‖ := by
    have hb : ∀ γ : Path d, ‖f (γ u.toNNReal)‖ ≤ ‖fB‖ :=
      fun γ => fB.norm_coe_le_norm (γ u.toNNReal)
    simpa only [probReal_univ, mul_one, m] using
      (norm_integral_le_of_norm_le_const (μ := P (x, ω)) (Eventually.of_forall hb))
  have hmi := sbxS4_laplace_integrable_of_bounded m hmm ‖fB‖ α hmb hα
  have hgi := sbxS4_laplace_integrable_of_bounded g (hg x).1 B α (hg x).2 hα
  refine ⟨hmi, hgi, ?_⟩
  apply sbxS4_laplace_identity_of_discounted m g ‖fB‖ α (f x) hα hmb hmi hgi
  intro T
  have h := he x f hf hc α T
  simpa only [m, g, Real.toNNReal_coe] using h

#print axioms sbxS4_supplied_compact_laplace_dynkin

#print axioms sbxS4_supplied_compact_discounted_dynkin

#print axioms sbxS4_supplied_compact_mean_ae_hasDerivAt

#print axioms sbxS4_supplied_compact_dynkin
#print axioms sbxS4_supplied_compact_generator_mean_bounded
#print axioms sbxS4_supplied_compact_mean_lipschitz

#print axioms sbxS4_laplace_supplied_correlation
#print axioms sbxS4_supplied_laplace_of_remainder

#print axioms sbxS4_laplace_integrable_and_bound
#print axioms sbxS4LaplaceOperator
#print axioms sbxS4_laplaceOperator_norm_le

#print axioms sbxS4ReducedPullback
#print axioms sbxS4ReducedAverage
#print axioms sbxS4_reducedAverage_norm_le
#print axioms sbxS4_reducedAverage_pullback
#print axioms sbxS4_reducedAverage_pairing
#print axioms sbxS4_reducedAverage_supplied_correlation
#print axioms sbxS4_reducedAverage_family
#print axioms sbxS4_reducedAverage_supplied_zero

#print axioms sbxS4_continuous_supplied_average_family_of_remainder
#print axioms sbxS4_continuous_operator_family_of_dense
#print axioms sbxS4_supplied_operator_continuous_boundedContinuous
#print axioms sbxS4_L2_pairing_eq_supplied
#print axioms sbxS4_L2_norm_sq
#print axioms sbxS4_supplied_average_operator_of_remainder
#print axioms sbxS4_supplied_average_growth_of_remainder
#print axioms sbxS4_supplied_average_zero
#print axioms sbxS4_supplied_average_mean_square_continuous
#print axioms sbxS4_coupled_average_memLp_two
#print axioms sbxS4_supplied_average_memLp_two_of_coupled
#print axioms sbxS4_positive_complex_integrable_covariance_of_deps
#print axioms sbxS4_coupled_endpoint_memLp_two_of_remainder
#print axioms sbxS4_coupled_product_integral_eq_supplied
#print axioms sbxS4_supplied_endpoint_memLp_two_of_coupled
#print axioms sbxS4_complex_path_product_growth_of_remainder
#print axioms sbxS4CoupledEndpoint
#print axioms sbxS4_measurable_coupledEndpoint
#print axioms sbxS4_ae_eq_coupledEndpoint
#print axioms sbxS4_coupledEndpoint_absolutelyContinuous
#print axioms sbxS4_ae_eq_coupledEndpoint_of_ae_eq
#print axioms sbxS4_aestronglyMeasurable_coupledEndpoint
#print axioms sbxS4_coupled_covariance_congr
#print axioms sbxS4_realLocal_representative
#print axioms sbxS4_real_representative_centered
#print axioms sbxS4_positive_complex_path_covariance_of_deps
#print axioms sbxS4_coupledEndpoint_zero
#print axioms sbxS4_continuous_coupled_endpoint_integral
#print axioms sbxS4_coupled_endpoint_mean_square_zero

#lint

end EinsteinFull.Blueprint
