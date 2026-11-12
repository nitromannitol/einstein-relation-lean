import EinsteinRelation.Correctors.ScalarMomentAverage
import EinsteinRelation.Correctors.SpatialGradientTimeMinkowski
import EinsteinRelation.Correctors.PairedPDEBallNormalization
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # Enlarging spatial averages of local energy

Source: `paper/main.tex:800–808,842–849`. A uniform bound for translated
unit-ball RMS moments controls larger-ball RMS moments. The argument
averages translations of the unit ball and retains the volume ratio.
-/

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM

/-- Unit-ball convolution covers the energy on a larger ball, with no
integrability assumption on the nonnegative energy density.
Source: `paper/main.tex:800–808,842–849`. -/
theorem ball_energy_le_translated_unit_energy {d : ℕ} {R : ℝ}
    (hR : 1 ≤ R) (f : Vec d → ℝ≥0∞) (hf : Measurable f) :
    volume (ball (0 : Vec d) 1) * (∫⁻ x in ball (0 : Vec d) R, f x) ≤
      ∫⁻ v in ball (0 : Vec d) (2*R), ∫⁻ z in ball (0 : Vec d) 1, f (v+z) := by
  have hB (r : ℝ) : MeasurableSet (ball (0 : Vec d) r) :=
    (paired_isOpen_ball _ _).measurableSet
  have hcover (z : Vec d) (hz : z ∈ ball (0 : Vec d) 1) :
      (∫⁻ x in ball (0 : Vec d) R, f x) ≤
        ∫⁻ v in ball (0 : Vec d) (2*R), f (v+z) := by
    rw [← lintegral_indicator (hB R),
      ← lintegral_add_right_eq_self ((ball (0 : Vec d) R).indicator f) z,
      ← lintegral_indicator (hB (2*R))]
    apply lintegral_mono
    intro v
    by_cases hv : v+z ∈ ball (0 : Vec d) R
    · have hv' : v ∈ ball (0 : Vec d) (2*R) := by
        have ht := TimeChange.euclideanNorm_add_le (v+z) (-z)
        simp only [add_neg_cancel_right] at ht
        have hn : euclideanNorm (-z) = euclideanNorm z := by
          rw [TimeChange.euclideanNorm_eq_norm_toLp,TimeChange.euclideanNorm_eq_norm_toLp]
          exact norm_neg _
        rw [hn] at ht
        simp only [ball,mem_setOf_eq,sub_zero] at hv hz ⊢
        linarith
      simp only [indicator_of_mem hv,indicator_of_mem hv',le_refl]
    · simp only [indicator_of_notMem hv]
      exact zero_le _
  calc
    _ = ∫⁻ _z in ball (0 : Vec d) 1, ∫⁻ x in ball (0 : Vec d) R, f x := by
      rw [setLIntegral_const,mul_comm]
    _ ≤ ∫⁻ z in ball (0 : Vec d) 1,
        ∫⁻ v in ball (0 : Vec d) (2*R), f (v+z) := by
      apply setLIntegral_mono' (hB 1)
      exact hcover
    _ = _ := lintegral_lintegral_swap (hf.comp (measurable_snd.add measurable_fst)).aemeasurable

/-- The normalized large-ball energy costs at most the doubled-ball
volume ratio relative to averaged translated unit-ball energies.
Source: `paper/main.tex:800–808,842–849`. -/
theorem normalized_ball_energy_le_unit_average {d : ℕ} {R : ℝ}
    (hR : 1 ≤ R) (f : Vec d → ℝ≥0∞) (hf : Measurable f) :
    let ν := fun r : ℝ => (volume (ball (0 : Vec d) r))⁻¹ •
      volume.restrict (ball (0 : Vec d) r)
    (∫⁻ x, f x ∂ν R) ≤ ENNReal.ofReal (2^d : ℝ) *
      ∫⁻ v, ∫⁻ z, f (v+z) ∂ν 1 ∂ν (2*R) := by
  let V := fun r : ℝ => volume (ball (0 : Vec d) r)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hv (r : ℝ) (hr : 0 < r) : V r ≠ 0 ∧ V r ≠ ⊤ := by
    have h := ENNReal.toReal_pos_iff.mp (paired_ball_volume_pos_finite (d := d) hr)
    exact ⟨h.1.ne',h.2.ne⟩
  have hV2 : V (2*R) = ENNReal.ofReal (2^d : ℝ) * V R := by
    apply (ENNReal.toReal_eq_toReal_iff' (hv _ (by positivity)).2
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hv _ hR0).2)).mp
    simp only [V,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2^d)]
    change volume.real (ball (0 : Vec d) (2*R)) =
      2^d * volume.real (ball (0 : Vec d) R)
    rw [paired_ball_volume_real (by positivity), paired_ball_volume_real hR0,mul_pow]
    ring
  have hb := ball_energy_le_translated_unit_energy hR f hf
  dsimp only
  simp only [lintegral_smul_measure,smul_eq_mul]
  rw [lintegral_const_mul' _ _]
  change (V R)⁻¹ * _ ≤ ENNReal.ofReal (2^d : ℝ) *
    ((V (2*R))⁻¹ * ((V 1)⁻¹ * _))
  have hc : ENNReal.ofReal (2^d : ℝ) * (V (2*R))⁻¹ = (V R)⁻¹ := by
    rw [hV2,ENNReal.mul_inv]
    rw [← mul_assoc,ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top,one_mul]
    · exact Or.inl (by positivity)
    · exact Or.inl ENNReal.ofReal_ne_top
  rw [← mul_assoc,hc]
  apply mul_le_mul_right
  apply (ENNReal.mul_le_mul_iff_right (hv 1 zero_lt_one).1 (hv 1 zero_lt_one).2).mp
  simpa only [← mul_assoc,ENNReal.mul_inv_cancel (hv 1 zero_lt_one).1
    (hv 1 zero_lt_one).2,one_mul] using hb

  exact ENNReal.inv_ne_top.mpr (hv 1 zero_lt_one).1

/-- Local energy on the tripled ball controls every translated unit
ball used in the doubled-ball average.
Source: `paper/main.tex:800–808,842–849`. -/
theorem translated_unit_memLp_of_ball
    {E : Type*} [NormedAddCommGroup E] {d : ℕ} {R : ℝ} (hR : 1 ≤ R)
    {F : Vec d → E} (hF : MemLp F 2 (volume.restrict (ball (0 : Vec d) (3*R))))
    {v : Vec d} (hv : v ∈ ball (0 : Vec d) (2*R)) :
    MemLp (fun z => F (v+z)) 2
      ((volume (ball (0 : Vec d) 1))⁻¹ • volume.restrict (ball 0 1)) := by
  have hsub : ball (0 : Vec d) 1 ⊆
      (fun z => v+z) ⁻¹' ball (0 : Vec d) (3*R) := by
    intro z hz
    have ht := TimeChange.euclideanNorm_add_le v z
    simp only [ball,mem_setOf_eq,sub_zero,mem_preimage] at hv hz ⊢
    linarith
  have hmp := (measurePreserving_add_left (volume : Measure (Vec d)) v).restrict_preimage_emb
    (MeasurableEquiv.addLeft v).measurableEmbedding (ball (0 : Vec d) (3*R))
  have h := (hF.comp_measurePreserving hmp).mono_measure
    (Measure.restrict_mono hsub le_rfl)
  have hV := ENNReal.toReal_pos_iff.mp
    (paired_ball_volume_pos_finite (d := d) zero_lt_one)
  exact h.smul_measure (ENNReal.inv_ne_top.mpr hV.1.ne')

/-- Uniform stochastic moments of translated unit-ball RMS norms give
large-ball RMS moments with a dimension-only factor. Local square
integrability is retained as part of the conclusion.
Source: `paper/main.tex:800–808,842–849`. -/
theorem ball_rms_moment_le_of_unit_moments
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {d : ℕ} {R p C : ℝ}
    (hR : 1 ≤ R) (hp : 2 ≤ p) (hC : 0 ≤ C)
    (f : Ω × Vec d → E) (hf : Measurable f)
    (hlocal : let ν := fun r : ℝ => (volume (ball (0 : Vec d) r))⁻¹ •
      volume.restrict (ball (0 : Vec d) r)
      ∀ᵐ ω ∂Q, ∀ᵐ v ∂ν (2*R), MemLp (fun z => f (ω,v+z)) 2 (ν 1))
    (hb : ∀ v : Vec d,
      eLpNorm (fun ω => Real.sqrt (∫ z, ‖f (ω,v+z)‖^2
        ∂((volume (ball (0 : Vec d) 1))⁻¹ • volume.restrict (ball 0 1))))
        (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C) :
    let ν : Measure (Vec d) := (volume (ball (0 : Vec d) R))⁻¹ •
      volume.restrict (ball (0 : Vec d) R)
    (∀ᵐ ω ∂Q, MemLp (fun x => f (ω,x)) 2 ν) ∧
      MemLp (fun ω => Real.sqrt (∫ x, ‖f (ω,x)‖^2 ∂ν)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => Real.sqrt (∫ x, ‖f (ω,x)‖^2 ∂ν)) (ENNReal.ofReal p) Q ≤
        ENNReal.ofReal (Real.sqrt (2^d : ℝ)*C) := by
  let ν := fun r : ℝ => (volume (ball (0 : Vec d) r))⁻¹ •
    volume.restrict (ball (0 : Vec d) r)
  have hprob (r : ℝ) (hr : 0 < r) : IsProbabilityMeasure (ν r) := by
    have hv := ENNReal.toReal_pos_iff.mp (paired_ball_volume_pos_finite (d := d) hr)
    refine ⟨?_⟩
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hv.1.ne' hv.2.ne
  letI : IsProbabilityMeasure (ν 1) := hprob 1 zero_lt_one
  letI : IsProbabilityMeasure (ν (2*R)) := hprob _ (by linarith)
  letI : IsProbabilityMeasure (ν R) := hprob _ (by linarith)
  let h : Ω × Vec d → ℝ := fun z => Real.sqrt (∫ x, ‖f (z.1,z.2+x)‖^2 ∂ν 1)
  have hhm : Measurable h :=
    ((((hf.comp (measurable_fst.fst.prodMk (measurable_fst.snd.add measurable_snd))).norm.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.sqrt)
  obtain ⟨hloc,hMom,hB⟩ := scalarL2_average_moment_le Q (ν (2*R)) hp hC h hhm
    (fun v => ⟨⟨(hhm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable,
      (hb v).trans_lt ENNReal.ofReal_lt_top⟩, hb v⟩)
  have henergy (μ : Measure (Vec d)) {F : Vec d → E}
      (hF : MemLp F 2 μ) : (∫⁻ x, ‖F x‖ₑ^2 ∂μ) =
        ENNReal.ofReal ((Real.sqrt (∫ x, ‖F x‖^2 ∂μ))^2) := by
    have he := eLpNorm_nnreal_pow_eq_lintegral (f := F) (μ := μ)
      (p := (2 : ℝ≥0)) (by norm_num)
    have he' : (eLpNorm F 2 μ)^2 = ∫⁻ x, ‖F x‖ₑ^2 ∂μ := by simpa using he
    rw [← he',eLpNorm_two_eq_ofReal_spatial_rms μ hF,
      ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
  have hpoint : ∀ᵐ ω ∂Q, MemLp (fun x => f (ω,x)) 2 (ν R) ∧
      Real.sqrt (∫ x, ‖f (ω,x)‖^2 ∂ν R) ≤
        Real.sqrt (2^d : ℝ) * Real.sqrt (∫ v, h (ω,v)^2 ∂ν (2*R)) := by
    filter_upwards [hlocal,hloc] with ω hω hlω
    have hi : Integrable (fun v => h (ω,v)^2) (ν (2*R)) := hlω.integrable_sq
    have hdouble : (∫⁻ v, ∫⁻ z, ‖f (ω,v+z)‖ₑ^2 ∂ν 1 ∂ν (2*R)) =
        ENNReal.ofReal (∫ v, h (ω,v)^2 ∂ν (2*R)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _)]
      exact lintegral_congr_ae (hω.mono fun v hv => henergy (ν 1) hv)
    have he := normalized_ball_energy_le_unit_average hR
      (fun x => ‖f (ω,x)‖ₑ^2)
      ((hf.comp measurable_prodMk_left).enorm.pow_const 2)
    change (∫⁻ x, ‖f (ω,x)‖ₑ^2 ∂ν R) ≤ _ at he
    rw [hdouble] at he
    have hfin : (∫⁻ x, ‖f (ω,x)‖ₑ^2 ∂ν R) < ⊤ :=
      he.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    have hmem : MemLp (fun x => f (ω,x)) 2 (ν R) := by
      refine ⟨(hf.comp measurable_prodMk_left).aestronglyMeasurable, ?_⟩
      rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
        (by simpa using hfin.ne)
    refine ⟨hmem,?_⟩
    rw [henergy (ν R) hmem,← ENNReal.ofReal_mul (by positivity)] at he
    have hs : (Real.sqrt (∫ x, ‖f (ω,x)‖^2 ∂ν R))^2 ≤
        (2^d : ℝ) * (∫ v, h (ω,v)^2 ∂ν (2*R)) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he
    have hs' := Real.sqrt_le_sqrt hs
    rw [Real.sqrt_sq (Real.sqrt_nonneg _),Real.sqrt_mul (by positivity)] at hs'
    exact hs'
  have hZ : Measurable (fun ω => Real.sqrt (∫ x, ‖f (ω,x)‖^2 ∂ν R)) :=
    ((hf.norm.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.sqrt
  have hnorm : eLpNorm (fun ω => Real.sqrt (∫ x, ‖f (ω,x)‖^2 ∂ν R))
      (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (Real.sqrt (2^d : ℝ)*C) := by
    calc
      _ ≤ eLpNorm (fun ω => Real.sqrt (2^d : ℝ) *
          Real.sqrt (∫ v, h (ω,v)^2 ∂ν (2*R))) (ENNReal.ofReal p) Q := by
        apply eLpNorm_mono_ae
        filter_upwards [hpoint] with ω hω
        simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _),
          Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
          using hω.2
      _ = ENNReal.ofReal (Real.sqrt (2^d : ℝ)) *
          eLpNorm (fun ω => Real.sqrt (∫ v, h (ω,v)^2 ∂ν (2*R)))
            (ENNReal.ofReal p) Q := by
        simpa only [Pi.smul_apply,smul_eq_mul,Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
          using eLpNorm_const_smul (Real.sqrt (2^d : ℝ))
            (fun ω => Real.sqrt (∫ v, h (ω,v)^2 ∂ν (2*R))) (ENNReal.ofReal p) Q
      _ ≤ _ := by
        simpa only [ENNReal.ofReal_mul (Real.sqrt_nonneg _)] using
          mul_le_mul_right hB (ENNReal.ofReal (Real.sqrt (2^d : ℝ)))
  exact ⟨hpoint.mono fun _ hω => hω.1,
    ⟨hZ.aestronglyMeasurable, hnorm.trans_lt ENNReal.ofReal_lt_top⟩,hnorm⟩

end EinsteinRelation.Correctors
