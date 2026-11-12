import EinsteinRelation.Correctors.P53SourceSkewMollifyAlgebra
import EinsteinRelation.Correctors.P53SourceSkewHeatHessianIBP
import EinsteinRelation.Correctors.HeatGradientConvolution
import EinsteinRelation.Correctors.HeatGradientJointMeasurability
import EinsteinRelation.Correctors.HeatHessianUniformL1
import EinsteinRelation.Correctors.HeatHessianUnitIntegrability
import EinsteinRelation.Correctors.StationaryHeatGradientBound
import EinsteinRelation.Correctors.StationaryConvolutionFubini
import EinsteinRelation.Correctors.HeatTransferConvolution
import EinsteinRelation.Correctors.HeatTransferMoments
import EinsteinRelation.Entropy.EllipticRegularity
import EinsteinRelation.External.AKMCorrectorOscillation

/-!
# Pairing the AKM heat truncations with smooth tests

Source: `paper/main.tex:732-748`; AKM (6.7) and Lemma 6.1, Step 4. Tested against
a smooth compactly supported spatial function, the literal truncation of the heat
formula along a stationary orbit becomes a time integral of horizontal
convolutions of the heat-smoothed source with second derivatives of the test.
The two spatial derivatives of the heat kernel are moved onto the test function,
and the time integral is exchanged with the spatial pairing by Fubini's theorem,
with integrability obtained from stationarity.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

variable {d : ℕ}

/-- The heat-kernel Hessian at time `t`, reflected. -/
def reflectedHeatHessian (t : ℝ) (j l : Fin d) (y : Vec d) : ℝ :=
  coordinateDerivative l (coordinateDerivative j (euclideanHeatKernel (d := d) t)) (-y)

theorem contDiff_coordinateDerivative' {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i f) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (unitVector i))
  exact ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const

theorem hasCompactSupport_coordinateDerivative' {f : Vec d → ℝ} (hf : HasCompactSupport f)
    (i : Fin d) : HasCompactSupport (coordinateDerivative i f) := by
  simpa only [coordinateDerivative] using hf.fderiv_apply ℝ (unitVector i)

theorem continuous_reflectedHeatHessian (t : ℝ) (j l : Fin d) :
    Continuous (reflectedHeatHessian (d := d) t j l) :=
  ((contDiff_coordinateDerivative' (contDiff_coordinateDerivative'
    (contDiff_euclideanHeatKernel t) j) l).continuous).comp continuous_neg

theorem integrable_reflectedHeatHessian {t : ℝ} (ht : 0 < t) (j l : Fin d) :
    Integrable (reflectedHeatHessian (d := d) t j l) volume := by
  obtain ⟨C, -, hC⟩ := heatKernel_mixedHessian_uniform_L1_of_unit
    (integrable_unit_heatKernel_mixedHessian (d := d))
  exact (hC t ht j l).1.comp_neg

/-- Convolution against a kernel respects almost-sure equality of stationary
observables. -/
theorem horizontalMollify_congr_ae {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {K : Vec d → ℝ} {f f' : FieldPair d → ℝ} (hf : Measurable f)
    (hf' : Measurable f') (h : f =ᵐ[Q] f') :
    horizontalMollify K f =ᵐ[Q] horizontalMollify K f' := by
  filter_upwards [Entropy.ae_ae_translate_eq hQ hf hf' h] with ρ hρ
  unfold horizontalMollify
  exact integral_congr_ae (hρ.mono fun x hx => by simp only [hx])

/-- Pairing the spatial heat integral at a fixed positive time with a smooth
compactly supported test: both derivatives move onto the test, and the heat
kernel onto the source. -/
theorem ae_horizontalMollify_heatSpaceIntegral_eq (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {g : FieldPair d → Vec d}
    (hg : Measurable g) (hgi : ∀ k, Integrable (fun ω => g ω k) Q)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    {t : ℝ} (ht : 0 < t) (j k l : Fin d) :
    horizontalMollify ψ
        (fun ω => akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) t j k l 0) =ᵐ[Q]
      fun ρ => horizontalMollify (coordinateDerivative j (coordinateDerivative l ψ))
          (heatSmoothed t (fun ω => g ω k)) ρ -
        horizontalMollify (coordinateDerivative k (coordinateDerivative l ψ))
          (heatSmoothed t (fun ω => g ω j)) ρ := by
  have hgk (i : Fin d) : Measurable (fun ω => g ω i) := (measurable_pi_apply i).comp hg
  have hKm (a b : Fin d) : Measurable (reflectedHeatHessian (d := d) t a b) :=
    (continuous_reflectedHeatHessian t a b).measurable
  have hKi (a b : Fin d) := integrable_reflectedHeatHessian (d := d) ht a b
  have hψm : Measurable ψ := hψ.continuous.measurable
  have hψi : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hψc
  -- the spatial heat integral as a difference of two convolutions
  have hS : (fun ω => akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) t j k l 0)
      =ᵐ[Q] fun ω => horizontalMollify (reflectedHeatHessian t j l) (fun ω => g ω k) ω -
        horizontalMollify (reflectedHeatHessian t k l) (fun ω => g ω j) ω := by
    filter_upwards [ae_integrable_kernel_translate hQ (hKm j l) (hKi j l) (hgk k) (hgi k),
      ae_integrable_kernel_translate hQ (hKm k l) (hKi k l) (hgk j) (hgi j)] with ω h1 h2
    exact akmHeatGradientSpaceIntegral_eq_horizontalMollify g ω t ht j k l
      (by simpa only [reflectedHeatHessian, mul_comm] using h1)
      (by simpa only [reflectedHeatHessian, mul_comm] using h2)
  have hSm : Measurable
      (fun ω => akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) t j k l 0) :=
    (measurable_actualHeatGradientSpaceIntegral_stationary g hg j k l).comp
      ((measurable_id.prodMk measurable_const).prodMk measurable_const)
  have hconv (a b c : Fin d) :
      MemLp (horizontalMollify (reflectedHeatHessian t a b) (fun ω => g ω c))
        (ENNReal.ofReal 1) Q := by
    have hn : eLpNorm (fun ω => g ω c) (ENNReal.ofReal 1) Q ≤
        ENNReal.ofReal (eLpNorm (fun ω => g ω c) 1 Q).toReal := by
      rw [ENNReal.ofReal_one, ENNReal.ofReal_toReal
        (memLp_one_iff_integrable.mpr (hgi c)).eLpNorm_ne_top]
    exact (horizontalMollify_moment_le Q hQ le_rfl ENNReal.toReal_nonneg (hKm a b) (hKi a b)
      (hgk c) hn).2.1
  have hconvi (a b c : Fin d) :
      Integrable (horizontalMollify (reflectedHeatHessian t a b) (fun ω => g ω c)) Q := by
    simpa only [ENNReal.ofReal_one, memLp_one_iff_integrable] using hconv a b c
  have hconvm (a b c : Fin d) :
      Measurable (horizontalMollify (reflectedHeatHessian t a b) (fun ω => g ω c)) :=
    measurable_horizontalMollify _ (hKm a b) (hgk c)
  -- the composite kernel is the heat smoothing of the second derivatives of the test
  have hker (a b : Fin d) : (fun y => ∫ x, ψ x * reflectedHeatHessian t a b (y - x)) =
      heatKernelConvolution t (coordinateDerivative a (coordinateDerivative b ψ)) := by
    funext y
    rw [← integral_mul_heatHessian_eq_heatKernelConvolution hψ hψc ht a b y]
    simp only [reflectedHeatHessian, neg_sub]
  have hcomp (a b c : Fin d) :
      horizontalMollify ψ (horizontalMollify (reflectedHeatHessian t a b) (fun ω => g ω c))
        =ᵐ[Q] horizontalMollify (coordinateDerivative a (coordinateDerivative b ψ))
          (heatSmoothed t (fun ω => g ω c)) := by
    have hD : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative a (coordinateDerivative b ψ)) :=
      contDiff_coordinateDerivative' (contDiff_coordinateDerivative' hψ b) a
    have hDc : HasCompactSupport (coordinateDerivative a (coordinateDerivative b ψ)) :=
      hasCompactSupport_coordinateDerivative' (hasCompactSupport_coordinateDerivative' hψc b) a
    filter_upwards [horizontalMollify_comp_ae Q hQ hψm hψi (hKm a b) (hKi a b) (hgk c) (hgi c),
      horizontalMollify_heatSmoothed_ae Q hQ hD.continuous.measurable
        (hD.continuous.integrable_of_hasCompactSupport hDc) (hgk c) (hgi c) ht.le]
      with ρ h1 h2
    rw [h1, hker, h2]
  filter_upwards [horizontalMollify_congr_ae hQ hSm
      ((hconvm j l k).sub (hconvm k l j)) hS,
    horizontalMollify_sub_ae hQ hψm hψi (hconvm j l k) (hconvi j l k) (hconvm k l j)
      (hconvi k l j), hcomp j l k, hcomp k l j] with ρ h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- The positive time window of the `(m, n)` truncation. -/
def truncationWindow (m n : ℕ) : Set ℝ :=
  Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ)

theorem measurableSet_truncationWindow (m n : ℕ) : MeasurableSet (truncationWindow m n) :=
  measurableSet_Icc

theorem truncationWindow_pos {m n : ℕ} {t : ℝ} (ht : t ∈ truncationWindow m n) : 0 < t :=
  lt_of_lt_of_le (by positivity) ht.1

/-- The truncation along an orbit is the time integral of the spatial heat integral. -/
theorem iteratedAKMHeatGradientTruncation_eq_setIntegral (g : Vec d → Vec d) (m n : ℕ)
    (j k l : Fin d) (x : Vec d) :
    iteratedAKMHeatGradientTruncation g m n j k l x =
      ∫ t in truncationWindow m n, akmHeatGradientSpaceIntegral g t j k l x := rfl

/-- Joint measurability of the spatial heat integral at the origin of the orbit. -/
theorem measurable_heatSpaceIntegral_origin {g : FieldPair d → Vec d} (hg : Measurable g)
    (j k l : Fin d) :
    Measurable (fun p : ℝ × FieldPair d =>
      akmHeatGradientSpaceIntegral (fun y => g (translate y p.2)) p.1 j k l 0) :=
  (measurable_actualHeatGradientSpaceIntegral_stationary g hg j k l).comp
    ((measurable_snd.prodMk measurable_fst).prodMk measurable_const)

/-- Pairing a truncation with a test exchanges with the time integral, for almost
every environment. Integrability follows from the stationary `C/t` moment bound. -/
theorem ae_horizontalMollify_truncation_eq_setIntegral (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {g : FieldPair d → Vec d}
    (hg : Measurable g) (hg2 : ∀ k, MemLp (fun ω => g ω k) 2 Q)
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (m n : ℕ)
    (j k l : Fin d) :
    horizontalMollify ψ
        (fun ω => iteratedAKMHeatGradientTruncation (fun y => g (translate y ω)) m n j k l 0)
      =ᵐ[Q] fun ρ => ∫ t in truncationWindow m n, horizontalMollify ψ
        (fun ω => akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) t j k l 0) ρ := by
  set ν : Measure ℝ := volume.restrict (truncationWindow m n) with hνdef
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by
    simp [truncationWindow, Real.volume_Icc])
  set S : ℝ → FieldPair d → ℝ := fun t ω =>
    akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) t j k l 0 with hSdef
  have hSm : Measurable (fun p : ℝ × FieldPair d => S p.1 p.2) :=
    measurable_heatSpaceIntegral_origin hg j k l
  obtain ⟨C, hC, hbound⟩ := exists_stationary_heatGradient_L2_bound hQ g hg hg2
  have ha : (0 : ℝ) < ((m + 1 : ℕ) : ℝ)⁻¹ := by positivity
  -- integrable joint integrand on `(space × time) × environment`
  let Φ : (Vec d × ℝ) × FieldPair d → ℝ := fun q => ψ q.1.1 * S q.1.2 (translate q.1.1 q.2)
  have hΦm : Measurable Φ :=
    (hψ.measurable.comp (measurable_fst.comp measurable_fst)).mul
      (hSm.comp ((measurable_snd.comp measurable_fst).prodMk
        (Probability.continuous_translate.measurable.comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))))
  have hS1 (t : ℝ) (ht : 0 < t) : Integrable (S t) Q := by
    have h2 : MemLp (S t) 2 Q :=
      ⟨(hSm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      (hbound j k l t ht).trans_lt ENNReal.ofReal_lt_top⟩
    exact h2.integrable one_le_two
  have hS1norm (t : ℝ) (ht : 0 < t) : (∫ ω, ‖S t ω‖ ∂Q) ≤ C / t := by
    have h2 : MemLp (S t) 2 Q :=
      ⟨(hSm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      (hbound j k l t ht).trans_lt ENNReal.ofReal_lt_top⟩
    have hle : eLpNorm (S t) 1 Q ≤ eLpNorm (S t) 2 Q :=
      eLpNorm_le_eLpNorm_of_exponent_le one_le_two h2.aestronglyMeasurable
    rw [integral_norm_eq_lintegral_enorm h2.aestronglyMeasurable, ← eLpNorm_one_eq_lintegral_enorm]
    exact ENNReal.toReal_le_of_le_ofReal (div_pos hC ht).le (hle.trans (hbound j k l t ht))
  have hΦi : Integrable Φ (((volume : Measure (Vec d)).prod ν).prod Q) := by
    refine (integrable_prod_iff hΦm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · have hmem : ∀ᵐ p ∂((volume : Measure (Vec d)).prod ν), p.2 ∈ truncationWindow m n := by
        have := (ae_restrict_mem (μ := (volume : Measure ℝ))
          (measurableSet_Icc : MeasurableSet (truncationWindow m n)))
        exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Vec d)))
          (ν := ν)).ae this
      filter_upwards [hmem] with p hp
      exact ((measurePreserving_translate Q hQ p.1).integrable_comp_of_integrable
        (hS1 p.2 (truncationWindow_pos hp))).const_mul (ψ p.1)
    · have hψi : Integrable ψ volume := hψ.integrable_of_hasCompactSupport hψc
      have hdom : Integrable (fun p : Vec d × ℝ => |ψ p.1| * (C / ((m + 1 : ℕ) : ℝ)⁻¹))
          ((volume : Measure (Vec d)).prod ν) :=
        (hψi.abs.mul_const _).comp_fst ν
      refine hdom.mono' (hΦm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) ?_
      have hmem : ∀ᵐ p ∂((volume : Measure (Vec d)).prod ν), p.2 ∈ truncationWindow m n :=
        (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Vec d))) (ν := ν)).ae
          (ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc)
      filter_upwards [hmem] with p hp
      have htpos := truncationWindow_pos hp
      have heq : (∫ ω, ‖Φ (p, ω)‖ ∂Q) = |ψ p.1| * ∫ ω, ‖S p.2 ω‖ ∂Q := by
        simp only [Φ, norm_mul, Real.norm_eq_abs, integral_const_mul]
        congr 1
        exact Probability.integral_translate Q hQ p.1 (fun ω => ‖S p.2 ω‖)
          (hSm.comp (measurable_const.prodMk measurable_id)).norm
      rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _), heq]
      refine mul_le_mul_of_nonneg_left ((hS1norm p.2 htpos).trans ?_) (abs_nonneg _)
      exact div_le_div_of_nonneg_left hC.le ha hp.1
  filter_upwards [hΦi.prod_left_ae] with ρ hρ
  have hρ' : Integrable (Function.uncurry fun (x : Vec d) (t : ℝ) =>
      ψ x * S t (translate x ρ)) ((volume : Measure (Vec d)).prod ν) := hρ
  change (∫ x, ψ x * ∫ t, S t (translate x ρ) ∂ν) = ∫ t, (∫ x, ψ x * S t (translate x ρ)) ∂ν
  simp_rw [← integral_const_mul]
  exact integral_integral_swap hρ'

/-- Tested against a smooth compactly supported function, a literal truncation of
AKM (6.7) along the orbit is the time integral of horizontal convolutions of the
heat-smoothed source with second derivatives of the test.
Source: AKM Lemma 6.1, Step 4, `paper/main.tex:732-748`. -/
theorem ae_horizontalMollify_truncation_eq (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {g : FieldPair d → Vec d}
    (hg : Measurable g) (hg2 : ∀ k, MemLp (fun ω => g ω k) 2 Q)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (m n : ℕ)
    (j k l : Fin d) :
    horizontalMollify ψ
        (fun ω => iteratedAKMHeatGradientTruncation (fun y => g (translate y ω)) m n j k l 0)
      =ᵐ[Q] fun ρ => ∫ t in truncationWindow m n,
        (horizontalMollify (coordinateDerivative j (coordinateDerivative l ψ))
            (heatSmoothed t (fun ω => g ω k)) ρ -
          horizontalMollify (coordinateDerivative k (coordinateDerivative l ψ))
            (heatSmoothed t (fun ω => g ω j)) ρ) := by
  have hgi (i : Fin d) : Integrable (fun ω => g ω i) Q := (hg2 i).integrable one_le_two
  have hgk (i : Fin d) : Measurable (fun ω => g ω i) := (measurable_pi_apply i).comp hg
  have hSm := measurable_heatSpaceIntegral_origin hg j k l
  have hD (a b : Fin d) : Measurable (coordinateDerivative a (coordinateDerivative b ψ)) :=
    (contDiff_coordinateDerivative' (contDiff_coordinateDerivative' hψ b) a).continuous.measurable
  have hL : Measurable (fun p : ℝ × FieldPair d => horizontalMollify ψ
      (fun ω => akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) p.1 j k l 0) p.2) := by
    have h : Measurable (fun q : (ℝ × FieldPair d) × Vec d => ψ q.2 *
        akmHeatGradientSpaceIntegral (fun y => g (translate y (translate q.2 q.1.2)))
          q.1.1 j k l 0) :=
      (hψ.continuous.measurable.comp measurable_snd).mul (hSm.comp
        ((measurable_fst.comp measurable_fst).prodMk
          (Probability.continuous_translate.measurable.comp
            (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))))
    exact h.stronglyMeasurable.integral_prod_right'.measurable
  have hR : Measurable (fun p : ℝ × FieldPair d =>
      horizontalMollify (coordinateDerivative j (coordinateDerivative l ψ))
          (heatSmoothed p.1 (fun ω => g ω k)) p.2 -
        horizontalMollify (coordinateDerivative k (coordinateDerivative l ψ))
          (heatSmoothed p.1 (fun ω => g ω j)) p.2) :=
    (measurable_horizontalMollify_heatSmoothed_joint (hD j l) (hgk k)).sub
      (measurable_horizontalMollify_heatSmoothed_joint (hD k l) (hgk j))
  have htime : ∀ᵐ t ∂(volume.restrict (truncationWindow m n)), ∀ᵐ ρ ∂Q,
      horizontalMollify ψ
          (fun ω => akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) t j k l 0) ρ =
        (horizontalMollify (coordinateDerivative j (coordinateDerivative l ψ))
            (heatSmoothed t (fun ω => g ω k)) ρ -
          horizontalMollify (coordinateDerivative k (coordinateDerivative l ψ))
            (heatSmoothed t (fun ω => g ω j)) ρ) := by
    refine (ae_restrict_iff' (measurableSet_truncationWindow m n)).mpr (ae_of_all _ fun t ht => ?_)
    exact ae_horizontalMollify_heatSpaceIntegral_eq Q hQ hg hgi hψ hψc
      (truncationWindow_pos ht) j k l
  have hswap := (Measure.ae_ae_comm (μ := volume.restrict (truncationWindow m n)) (ν := Q)
    (measurableSet_eq_fun hL hR)).mp htime
  filter_upwards [ae_horizontalMollify_truncation_eq_setIntegral Q hQ hg hg2 hψ.continuous hψc
    m n j k l, hswap] with ρ h1 h2
  rw [h1]
  exact integral_congr_ae h2

end EinsteinRelation.Correctors
