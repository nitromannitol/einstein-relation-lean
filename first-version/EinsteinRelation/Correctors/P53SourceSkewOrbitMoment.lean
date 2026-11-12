import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Integral.Prod
import EinsteinRelation.Correctors.StationaryLocalL2Square
import EinsteinRelation.Calculus.HorizontalTranslationLp
import EinsteinRelation.Correctors.StationaryGradientDomainSupport
import EinsteinRelation.Correctors.SpatialLocalL2LimitDilation
import EinsteinRelation.External.AKMCorrectorOscillation
import EinsteinRelation.Correctors.SpatialBallVolume

/-!
# Square moments of the stationary flux-corrector gradient

Source: `paper/main.tex:716-723,732-748`; AKM Lemma 6.1, (6.8). The unit-ball
moment of AKM's flux-corrector gradient survives the physical dilation, and
stationarity turns the local square moment of an orbit into the square moment of
the stationary field.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

lemma measurableSet_unitBall (d : ℕ) : MeasurableSet (ball (0 : Vec d) 1) := by
  unfold ball euclideanNorm euclideanSq dot
  exact (isOpen_lt (by fun_prop) continuous_const).measurableSet

/-- The unit ball has positive Lebesgue measure. -/
lemma measure_unitBall_pos (d : ℕ) : 0 < volume (ball (0 : Vec d) 1) := by
  -- The unit ball contains the origin and is open, hence has positive measure
  have h_open : IsOpen (ball (0 : Vec d) 1) := by
    unfold ball euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have h_ne : (ball (0 : Vec d) 1).Nonempty := by
    refine ⟨0, ?_⟩
    unfold ball euclideanNorm euclideanSq dot
    simp
  exact h_open.measure_pos volume h_ne

/-- If the orbit of a measurable observable agrees almost everywhere with a sample
field whose unit-ball `L²` norm has a finite second moment, the observable is in
`L²` of the stationary law. Tonelli and stationarity give
`∫ |F|² = |B₁|⁻¹ E ∫_{B₁} |F(τ_x ·)|²`. -/
theorem memLp_two_of_orbit_lintegral {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {F : FieldPair d → ℝ}
    (hF : Measurable F) {h : FieldPair d → Vec d → ℝ}
    (horbit : ∀ᵐ ρ ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)), F (translate x ρ) = h ρ x)
    (hm : ∫⁻ ρ, eLpNorm (h ρ) 2 (volume.restrict (ball 0 1)) ^ 2 ∂Q < ⊤) :
    MemLp F 2 Q := by
  -- Step 1: Convert `hm` to the lintegral-of-enorm-squared form
  have hm_ball : ∫⁻ ρ, ∫⁻ x in ball (0 : Vec d) 1, ‖h ρ x‖ₑ ^ 2 ∂volume ∂Q < ⊤ := by
    simpa [eLpNorm_two_sq_eq_lintegral_enorm_sq] using hm
  -- Step 2: Use the orbit condition to replace `h` with `F` in the inner integral
  have h_ae_ball : ∀ᵐ ρ ∂Q, ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) 1)),
      F (translate x ρ) = h ρ x := by
    filter_upwards [horbit] with ρ hρ
    exact hρ.filter_mono (ae_mono Measure.restrict_le_self)
  have h_inner_eq : ∀ᵐ ρ ∂Q, ∫⁻ x in ball (0 : Vec d) 1, ‖h ρ x‖ₑ ^ 2 ∂volume =
      ∫⁻ x in ball (0 : Vec d) 1, ‖F (translate x ρ)‖ₑ ^ 2 ∂volume := by
    filter_upwards [h_ae_ball] with ρ hρ
    have h_norm_eq : ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) 1)),
        ‖h ρ x‖ₑ ^ 2 = ‖F (translate x ρ)‖ₑ ^ 2 :=
      hρ.mono fun x hx => by simp [hx]
    have h_norm_eq' : ∀ᵐ x ∂volume, x ∈ ball (0 : Vec d) 1 →
        ‖h ρ x‖ₑ ^ 2 = ‖F (translate x ρ)‖ₑ ^ 2 :=
      (ae_restrict_iff' (measurableSet_unitBall d)).mp h_norm_eq
    exact setLIntegral_congr_fun_ae (measurableSet_unitBall d) h_norm_eq'
  have hm_F : ∫⁻ ρ, ∫⁻ x in ball (0 : Vec d) 1, ‖F (translate x ρ)‖ₑ ^ 2 ∂volume ∂Q < ⊤ := by
    have h_eq : (∫⁻ ρ, ∫⁻ x in ball (0 : Vec d) 1, ‖h ρ x‖ₑ ^ 2 ∂volume ∂Q) =
        (∫⁻ ρ, ∫⁻ x in ball (0 : Vec d) 1, ‖F (translate x ρ)‖ₑ ^ 2 ∂volume ∂Q) := by
      refine lintegral_congr_ae ?_
      filter_upwards [h_inner_eq] with ρ hρ_eq
      exact hρ_eq
    rwa [← h_eq]
  -- Step 3: Define the integrand on the product space and convert to product integral
  let g : Vec d × FieldPair d → ℝ≥0∞ := fun p => ‖F (translate p.1 p.2)‖ₑ ^ 2
  have hg_meas : Measurable g := by
    have h_translate_meas : Measurable (fun (p : Vec d × FieldPair d) => translate p.1 p.2) :=
      Probability.continuous_translate.measurable
    have h_norm_pow_meas : Measurable (fun (ω : FieldPair d) => ‖F ω‖ₑ ^ 2) :=
      (measurable_enorm.comp hF).pow_const 2
    exact h_norm_pow_meas.comp h_translate_meas
  have hg_aemeasurable_restrict : AEMeasurable g
      ((volume.prod Q).restrict (ball (0 : Vec d) 1 ×ˢ (univ : Set (FieldPair d)))) :=
    hg_meas.aemeasurable.restrict
  have h_prod_eq : (∫⁻ ρ, ∫⁻ x in ball (0 : Vec d) 1, g (x, ρ) ∂volume ∂Q) =
      (∫⁻ z in ball (0 : Vec d) 1 ×ˢ (univ : Set (FieldPair d)), g z ∂(volume.prod Q)) := by
    rw [setLIntegral_prod_symm g hg_aemeasurable_restrict, setLIntegral_univ]
  have h_swap : (∫⁻ z in ball (0 : Vec d) 1 ×ˢ (univ : Set (FieldPair d)), g z ∂(volume.prod Q)) =
      (∫⁻ x in ball (0 : Vec d) 1, ∫⁻ ω, g (x, ω) ∂Q ∂volume) := by
    rw [setLIntegral_prod g hg_aemeasurable_restrict]
    refine setLIntegral_congr_fun (measurableSet_unitBall d) fun x hx => ?_
    rw [setLIntegral_univ]
  rw [h_prod_eq, h_swap] at hm_F
  -- Step 4: Use stationarity to simplify the inner integral
  have h_inner_eq' (x : Vec d) : (∫⁻ ω, g (x, ω) ∂Q) = (∫⁻ ω, ‖F ω‖ₑ ^ 2 ∂Q) := by
    dsimp [g]
    have h_meas : Measurable (fun (ω : FieldPair d) => ‖F ω‖ₑ ^ 2) :=
      (measurable_enorm.comp hF).pow_const 2
    rw [← lintegral_map h_meas (Probability.measurable_translate x), hQ x]
  have h_inner_congr : (∫⁻ x in ball (0 : Vec d) 1, ∫⁻ ω, g (x, ω) ∂Q ∂volume) =
      (∫⁻ x in ball (0 : Vec d) 1, (∫⁻ ω, ‖F ω‖ₑ ^ 2 ∂Q) ∂volume) := by
    refine setLIntegral_congr_fun (measurableSet_unitBall d) fun x hx => ?_
    rw [h_inner_eq' x]
  rw [h_inner_congr] at hm_F
  -- Step 5: Factor out the constant volume of the unit ball
  have h_const_factor : (∫⁻ x in ball (0 : Vec d) 1, (∫⁻ ω, ‖F ω‖ₑ ^ 2 ∂Q) ∂volume) =
      (volume (ball (0 : Vec d) 1)) * (∫⁻ ω, ‖F ω‖ₑ ^ 2 ∂Q) := by
    simp [mul_comm, setLIntegral_const (ball (0 : Vec d) 1) (∫⁻ ω, ‖F ω‖ₑ ^ 2 ∂Q)]
  rw [h_const_factor] at hm_F
  -- Step 6: Since volume(ball 0 1) > 0, deduce the single integral is finite
  have hball_pos : 0 < volume (ball (0 : Vec d) 1) := measure_unitBall_pos d
  have h_single_finite : (∫⁻ ω, ‖F ω‖ₑ ^ 2 ∂Q) < ⊤ := by
    by_contra! htop
    have htop_val : (∫⁻ ω, ‖F ω‖ₑ ^ 2 ∂Q) = ⊤ := top_unique htop
    have hvol_ne_zero : volume (ball (0 : Vec d) 1) ≠ 0 := by
      intro hzero
      rw [hzero] at hball_pos
      exact lt_irrefl _ hball_pos
    have htop' : (volume (ball (0 : Vec d) 1)) * (∫⁻ ω, ‖F ω‖ₑ ^ 2 ∂Q) = ⊤ := by
      rw [htop_val]
      exact ENNReal.mul_top hvol_ne_zero
    rw [htop'] at hm_F
    exact lt_irrefl _ hm_F
  -- Step 7: Convert finiteness of lintegral to finiteness of eLpNorm
  have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h_eLpNorm_finite : eLpNorm F (2 : ℝ≥0∞) Q < ∞ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_ne_zero hp_ne_top]
    simpa [show ((2 : ℝ≥0∞).toReal : ℝ) = (2 : ℝ) by norm_num] using h_single_finite
  -- Step 8: Assemble MemLp from AEStronglyMeasurable and finite eLpNorm
  exact ⟨hF.aestronglyMeasurable, h_eLpNorm_finite⟩

/-- A coordinate's unit-ball square integral is at most the ball volume times the
mean square Euclidean norm, in the source's square-root normalization. -/
theorem eLpNorm_coord_sq_le_ball_average {d : ℕ} {f : Vec d → Vec d}
    (hf : MemLp f 2 (volume.restrict (ball (0 : Vec d) 1))) (l : Fin d) :
    eLpNorm (fun y => f y l) 2 (volume.restrict (ball 0 1)) ^ 2 ≤
      volume (ball (0 : Vec d) 1) * ENNReal.ofReal ((Real.sqrt
        (⨍ y in ball 0 1, euclideanSq (f y) ∂volume)) ^ (2 : ℝ)) := by
  set B : Set (Vec d) := ball (0 : Vec d) 1 with hBdef
  have hBm : MeasurableSet B := measurableSet_unitBall d
  have hBfin : volume B ≠ ⊤ := by
    have h := ball_volume_pos_finite d 1 one_pos
    exact (ENNReal.toReal_pos_iff.mp h).2.ne
  have hcoord (i : Fin d) : MemLp (fun y => f y i) 2 (volume.restrict B) :=
    (memLp_pi_iff.mp hf) i
  have hsqi : Integrable (fun y => euclideanSq (f y)) (volume.restrict B) := by
    unfold euclideanSq dot
    exact integrable_finset_sum _ fun i _ => by
      simpa only [sq] using (hcoord i).integrable_sq
  have hsq_nn (v : Vec d) : 0 ≤ euclideanSq v := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hnn : 0 ≤ ⨍ y in B, euclideanSq (f y) ∂volume := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
      (integral_nonneg fun y => hsq_nn (f y))
  rw [Real.rpow_two, Real.sq_sqrt hnn, eLpNorm_two_sq_eq_lintegral_enorm_sq]
  calc (∫⁻ y in B, ‖f y l‖ₑ ^ 2) ≤ ∫⁻ y in B, ENNReal.ofReal (euclideanSq (f y)) := by
        refine lintegral_mono fun y => ?_
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs,
          sq_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        unfold euclideanSq dot
        rw [sq]
        exact Finset.single_le_sum (fun i _ => mul_self_nonneg (f y i)) (Finset.mem_univ l)
    _ = ENNReal.ofReal (∫ y in B, euclideanSq (f y)) :=
        (ofReal_integral_eq_lintegral_ofReal hsqi
          (ae_of_all _ fun y => hsq_nn (f y))).symm
    _ = volume B * ENNReal.ofReal (⨍ y in B, euclideanSq (f y) ∂volume) := by
        have hpos := ball_volume_pos_finite d 1 one_pos
        have hv : ENNReal.ofReal (volume.real B) = volume B := ENNReal.ofReal_toReal hBfin
        have hne : volume B ≠ 0 := (ENNReal.toReal_pos_iff.mp hpos).1.ne'
        rw [setAverage_eq, smul_eq_mul, ENNReal.ofReal_mul (inv_nonneg.mpr measureReal_nonneg),
          ENNReal.ofReal_inv_of_pos hpos, hv, ← mul_assoc, ENNReal.mul_inv_cancel hne hBfin,
          one_mul]

/-- Finite second moment of the unit-ball `L²` norm of the physical heat-selected
flux gradient. Source: AKM Lemma 6.1, (6.8), via `paper/main.tex:716-723`. -/
theorem lintegral_sq_eLpNorm_physical_fluxGradient_lt_top
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    {e : Vec d} {φ : Corrector (actualCoefficientLaw Q) e} (S : FluxCorrector φ)
    {C : ℝ} (hb : ∀ j k : Fin d, (∫⁻ a, ENNReal.ofReal ((Real.sqrt
      (⨍ x in ball 0 1, euclideanSq (S.grad a j k x) ∂volume)) ^ (2 : ℝ))
        ∂actualCoefficientLaw Q) ≤ ENNReal.ofReal C)
    (Ψ : FieldPair d → Coefficient d (AKMUpperEllipticity L))
    (hΨ : MeasurePreserving Ψ (reducedEnvironmentLaw Q) (actualCoefficientLaw Q))
    (κ : ℝ) (hr : 1 ≤ r₀) (j k l : Fin d) :
    ∫⁻ ρ, eLpNorm (fun x => κ⁻¹ * S.grad (Ψ ρ) j k (r₀⁻¹ • x) l) 2
      (volume.restrict (ball 0 1)) ^ 2 ∂reducedEnvironmentLaw Q < ⊤ := by
  have hr0 : 0 < r₀ := zero_lt_one.trans_le hr
  have hrinv : 0 < r₀⁻¹ := inv_pos.mpr hr0
  set K₀ : ℝ≥0∞ := (ENNReal.ofReal |(r₀⁻¹ ^ d)⁻¹|) ^ (1 / (2 : ℝ≥0∞)).toReal with hK₀
  set c : ℝ≥0∞ := (‖κ⁻¹‖ₑ * K₀) ^ 2 * volume (ball (0 : Vec d) 1) with hcdef
  have hc : c ≠ ⊤ := by
    have h1 : volume (ball (0 : Vec d) 1) ≠ ⊤ :=
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d 1 one_pos)).2.ne
    have h2 : K₀ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top enorm_ne_top h2)) h1
  let H : Coefficient d (AKMUpperEllipticity L) → ℝ≥0∞ := fun a =>
    c * ENNReal.ofReal ((Real.sqrt (⨍ x in ball 0 1, euclideanSq (S.grad a j k x) ∂volume)) ^
      (2 : ℝ))
  have hHm : Measurable H := by
    refine Measurable.const_mul (ENNReal.measurable_ofReal.comp ?_) c
    refine (Measurable.pow_const (Real.continuous_sqrt.measurable.comp ?_) _)
    simp only [setAverage_eq, smul_eq_mul]
    refine Measurable.const_mul ?_ _
    have hj : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
        euclideanSq (S.grad p.1 j k p.2)) := by
      have hg := S.measurable_grad j k
      unfold euclideanSq dot
      exact Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp hg).mul ((measurable_pi_apply i).comp hg)
    exact (hj.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (ball (0 : Vec d) 1))).measurable
  have hpoint : ∀ᵐ ρ ∂reducedEnvironmentLaw Q,
      eLpNorm (fun x => κ⁻¹ * S.grad (Ψ ρ) j k (r₀⁻¹ • x) l) 2
        (volume.restrict (ball 0 1)) ^ 2 ≤ H (Ψ ρ) := by
    filter_upwards [hΨ.quasiMeasurePreserving.ae S.locally_square_integrable] with ρ hρ
    set A := Ψ ρ
    have hg1 : MemLp (S.grad A j k) 2 (volume.restrict (ball 0 1)) := (hρ 1 one_pos j k).2
    have hgl : MemLp (fun y => S.grad A j k y l) 2 (volume.restrict (ball 0 (r₀⁻¹ * 1))) := by
      have hsub : ball (0 : Vec d) (r₀⁻¹ * 1) ⊆ ball 0 1 := by
        intro x hx
        change euclideanNorm (x - 0) < 1
        have hx' : euclideanNorm (x - 0) < r₀⁻¹ * 1 := hx
        have : r₀⁻¹ * 1 ≤ 1 := by rw [mul_one]; exact inv_le_one_of_one_le₀ hr
        linarith
      exact ((memLp_pi_iff.mp hg1) l).mono_measure (Measure.restrict_mono_set _ hsub)
    have hdil := eLpNorm_two_dilation_ball (fun y => S.grad A j k y l) r₀⁻¹ 1 hrinv hgl
    have hmono : eLpNorm (fun y => S.grad A j k y l) 2 (volume.restrict (ball 0 (r₀⁻¹ * 1))) ≤
        eLpNorm (fun y => S.grad A j k y l) 2 (volume.restrict (ball 0 1)) := by
      refine eLpNorm_mono_measure _ (Measure.restrict_mono_set _ fun x hx => ?_)
      change euclideanNorm (x - 0) < 1
      have hx' : euclideanNorm (x - 0) < r₀⁻¹ * 1 := hx
      have : r₀⁻¹ * 1 ≤ 1 := by rw [mul_one]; exact inv_le_one_of_one_le₀ hr
      linarith
    have hscale : eLpNorm (fun x => κ⁻¹ * S.grad A j k (r₀⁻¹ • x) l) 2
        (volume.restrict (ball 0 1)) ≤
        ‖κ⁻¹‖ₑ * K₀ * eLpNorm (fun y => S.grad A j k y l) 2 (volume.restrict (ball 0 1)) := by
      rw [show (fun x => κ⁻¹ * S.grad A j k (r₀⁻¹ • x) l) =
          κ⁻¹ • (fun x => S.grad A j k (r₀⁻¹ • x) l) from rfl, eLpNorm_const_smul, mul_assoc]
      refine mul_le_mul_right ?_ _
      rw [hdil]
      exact mul_le_mul_right hmono _
    calc eLpNorm (fun x => κ⁻¹ * S.grad A j k (r₀⁻¹ • x) l) 2 (volume.restrict (ball 0 1)) ^ 2
        ≤ (‖κ⁻¹‖ₑ * K₀ * eLpNorm (fun y => S.grad A j k y l) 2
            (volume.restrict (ball 0 1))) ^ 2 := pow_le_pow_left' hscale 2
      _ = (‖κ⁻¹‖ₑ * K₀) ^ 2 * eLpNorm (fun y => S.grad A j k y l) 2
            (volume.restrict (ball 0 1)) ^ 2 := by rw [mul_pow]
      _ ≤ (‖κ⁻¹‖ₑ * K₀) ^ 2 * (volume (ball (0 : Vec d) 1) * ENNReal.ofReal ((Real.sqrt
            (⨍ x in ball 0 1, euclideanSq (S.grad A j k x) ∂volume)) ^ (2 : ℝ))) :=
          mul_le_mul_right (eLpNorm_coord_sq_le_ball_average hg1 l) _
      _ = H A := by simp only [H, hcdef, mul_assoc]
  calc (∫⁻ ρ, eLpNorm (fun x => κ⁻¹ * S.grad (Ψ ρ) j k (r₀⁻¹ • x) l) 2
        (volume.restrict (ball 0 1)) ^ 2 ∂reducedEnvironmentLaw Q)
      ≤ ∫⁻ ρ, H (Ψ ρ) ∂reducedEnvironmentLaw Q := lintegral_mono_ae hpoint
    _ = ∫⁻ a, H a ∂actualCoefficientLaw Q := hΨ.lintegral_comp hHm
    _ = c * ∫⁻ a, ENNReal.ofReal ((Real.sqrt
          (⨍ x in ball 0 1, euclideanSq (S.grad a j k x) ∂volume)) ^ (2 : ℝ))
            ∂actualCoefficientLaw Q := by
        rw [lintegral_const_mul' _ _ hc]
    _ ≤ c * ENNReal.ofReal C := mul_le_mul_right (hb j k) c
    _ < ⊤ := ENNReal.mul_lt_top hc.lt_top ENNReal.ofReal_lt_top

end EinsteinRelation.Correctors
