import EinsteinRelation.Correctors.StationaryHeatSelectionRescaling
import EinsteinRelation.Correctors.StationaryHeatGradientBound
import EinsteinRelation.Correctors.AKMHeatTimeDilation

/-!
# Environment dilation and dilated heat windows

Source: `paper/main.tex:716,733-748`. The flux corrector of Lemma 5.1 is the
AKM heat formula (6.7) in the coordinates of AKM, which dilate physical space
by the range `r₀`. The heat selection supplied there uses integer time
cutoffs in those coordinates. Dilating the environment itself turns the
dilated source into a stationary orbit, so the stationary cutoff rescaling
applies; the window integrability is transported by the exact heat-kernel
dilation identities. No limit or identity of the heat formula is assumed.
-/

open MeasureTheory Filter Topology Set
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

/-- Spatial dilation `x ↦ s x` of both fields of a coefficient pair. -/
def dilateFieldPair {d : ℕ} (s : ℝ) (ρ : FieldPair d) : FieldPair d :=
  (ρ.1.comp ⟨fun x => s • x, continuous_const_smul s⟩,
    ρ.2.comp ⟨fun x => s • x, continuous_const_smul s⟩)

theorem continuous_dilateFieldPair {d : ℕ} (s : ℝ) :
    Continuous (dilateFieldPair (d := d) s) :=
  ((ContinuousMap.continuous_precomp _).comp continuous_fst).prodMk
    ((ContinuousMap.continuous_precomp _).comp continuous_snd)

/-- Translating a dilated pair is dilating the pair translated by the dilated vector. -/
theorem translate_dilateFieldPair {d : ℕ} (s : ℝ) (y : Vec d) (ρ : FieldPair d) :
    translate y (dilateFieldPair s ρ) = dilateFieldPair s (translate (s • y) ρ) := by
  apply Prod.ext <;> ext x <;> simp [translate, dilateFieldPair, smul_add]

theorem dilateFieldPair_inv_dilateFieldPair {d : ℕ} {s : ℝ} (hs : s ≠ 0)
    (ρ : FieldPair d) : dilateFieldPair s⁻¹ (dilateFieldPair s ρ) = ρ := by
  apply Prod.ext <;> ext x <;> simp [dilateFieldPair, smul_smul, mul_inv_cancel₀ hs]

/-- The image of a stationary law under a dilation is stationary. -/
theorem isStationary_map_dilateFieldPair {d : ℕ} {Q : Measure (FieldPair d)}
    (hQ : IsStationary Q) (s : ℝ) : IsStationary (Measure.map (dilateFieldPair s) Q) := by
  intro y
  have hD := (continuous_dilateFieldPair (d := d) s).measurable
  rw [Measure.map_map (Probability.measurable_translate y) hD]
  have hcomm : translate y ∘ dilateFieldPair s = dilateFieldPair s ∘ translate (s • y) :=
    funext (translate_dilateFieldPair s y)
  rw [hcomm, ← Measure.map_map hD (Probability.measurable_translate _), hQ]

/-- For a stationary square-integrable field, the heat selection of the
dilated orbit `y ↦ b F(τ_{s y} ρ)` persists for the time-rescaled cutoffs,
almost surely, and simultaneously for every selected gradient. -/
theorem ae_dilated_heat_selection_rescaled_local_L2 {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → Vec d) (hF : Measurable F)
    (hF2 : ∀ i, MemLp (fun ω => F ω i) 2 Q) (s b c : ℝ) (hs : s ≠ 0) (hc : 0 < c) :
    ∀ᵐ ρ ∂Q, ∀ G : Fin d → Fin d → Vec d → Vec d,
      IsHeatSelectedFluxGradient (fun y => b • F (translate (s • y) ρ)) G →
      ∀ (j k l : Fin d) (R : ℕ),
        (∀ m n, MemLp (rescaledAKMHeatGradientTruncation
          (fun y => b • F (translate (s • y) ρ)) c m n j k l)
            2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) ∧
        Tendsto (fun mn : ℕ × ℕ => eLpNorm
          (fun x => rescaledAKMHeatGradientTruncation
            (fun y => b • F (translate (s • y) ρ)) c mn.1 mn.2 j k l x - G j k x l)
            2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) atTop (𝓝 0) := by
  have hD := (continuous_dilateFieldPair (d := d) s).measurable
  let Q' : Measure (FieldPair d) := Measure.map (dilateFieldPair s) Q
  haveI : IsProbabilityMeasure Q' := Measure.isProbabilityMeasure_map hD.aemeasurable
  have hQ' : IsStationary Q' := isStationary_map_dilateFieldPair hQ s
  let F' : FieldPair d → Vec d := fun ω => b • F (dilateFieldPair s⁻¹ ω)
  have hF' : Measurable F' :=
    (hF.comp (continuous_dilateFieldPair (d := d) s⁻¹).measurable).const_smul b
  have hF'2 (i : Fin d) : MemLp (fun ω => F' ω i) 2 Q' := by
    have hm : AEStronglyMeasurable (fun ω => F' ω i) Q' :=
      ((measurable_pi_apply i).comp hF').aestronglyMeasurable
    refine (memLp_map_measure_iff hm hD.aemeasurable).mpr ?_
    have heq : ((fun ω => F' ω i) ∘ dilateFieldPair s) = fun ω => b * F ω i := by
      funext ω
      simp [F', dilateFieldPair_inv_dilateFieldPair hs]
    rw [heq]
    exact (hF2 i).const_mul b
  obtain ⟨C, hC, hbound⟩ := exists_stationary_heatGradient_L2_bound hQ' F' hF' hF'2
  have h := ae_heat_selection_rescaled_local_L2 Q' hQ' F' hF' C c hC hc hbound
  filter_upwards [ae_of_ae_map hD.aemeasurable h] with ρ hρ
  have horbit : (fun y => F' (translate y (dilateFieldPair s ρ))) =
      fun y => b • F (translate (s • y) ρ) := by
    funext y
    simp only [F', translate_dilateFieldPair, dilateFieldPair_inv_dilateFieldPair hs]
  rw [horbit] at hρ
  exact hρ

private theorem ae_restrict_ball_of_smul {d : ℕ} {r : ℝ} (hr : 0 < r) {R R' : ℝ}
    (hRR : R ≤ r * R') {P : Vec d → Prop}
    (h : ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) R')), P x) :
    ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) R)), P (r⁻¹ • x) := by
  have hmeas (S : ℝ) : MeasurableSet (ball (0 : Vec d) S) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  rw [ae_restrict_iff' (hmeas R')] at h
  have h' := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
    (inv_ne_zero hr.ne')).ae h
  rw [ae_restrict_iff' (hmeas R)]
  filter_upwards [h'] with x hx hxR
  apply hx
  change euclideanNorm (r⁻¹ • x - 0) < R'
  change euclideanNorm (x - 0) < R at hxR
  rw [sub_zero] at hxR ⊢
  have hn : euclideanNorm (r⁻¹ • x) = r⁻¹ * euclideanNorm x := by
    unfold euclideanNorm euclideanSq dot
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ i, r⁻¹ * x i * (r⁻¹ * x i)) = (r⁻¹) ^ 2 * ∑ i, x i * x i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr hr.le)]
  rw [hn]
  calc r⁻¹ * euclideanNorm x < r⁻¹ * R := mul_lt_mul_of_pos_left hxR (inv_pos.mpr hr)
    _ ≤ r⁻¹ * (r * R') := mul_le_mul_of_nonneg_left hRR (inv_nonneg.mpr hr.le)
    _ = R' := by field_simp

/-- The two genuine integrability clauses of a heat selection survive the
physical dilation `g ↦ b g(r⁻¹ ·)` of its source, on the literal integer
cutoff windows. -/
theorem heat_window_integrability_of_dilated_selection {d : ℕ}
    {g : Vec d → Vec d} {G : Fin d → Fin d → Vec d → Vec d}
    (hselect : IsHeatSelectedFluxGradient g G) (r b : ℝ) (hr : 0 < r)
    (j k l : Fin d) (R m n : ℕ) :
    ∀ᵐ x ∂(volume.restrict (ball 0 ((R : ℝ) + 1))),
      (∀ᵐ t ∂(volume.restrict (Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))),
        Integrable (fun y => akmHeatGradientDensity
          (fun z => b • g (r⁻¹ • z)) t j k l x y) volume) ∧
      Integrable (fun t => akmHeatGradientSpaceIntegral
        (fun z => b • g (r⁻¹ • z)) t j k l x)
        (volume.restrict (Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))) := by
  obtain ⟨R', hR'⟩ := exists_nat_gt (((R : ℝ) + 1) / r)
  have hRR : (R : ℝ) + 1 ≤ r * ((R' : ℝ) + 1) := by
    rw [div_lt_iff₀ hr] at hR'
    nlinarith
  have hr2 : (r ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hr.ne')
  set a : ℝ := (r ^ 2)⁻¹ * ((m + 1 : ℕ) : ℝ)⁻¹ with ha_def
  set h : ℝ := (r ^ 2)⁻¹ * ((n + 1 : ℕ) : ℝ) with hh_def
  have ha : 0 < a := by positivity
  have hlow : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    norm_cast
    omega
  have hhigh : 1 ≤ ((n + 1 : ℕ) : ℝ) := by norm_cast; omega
  have hah : a ≤ h := mul_le_mul_of_nonneg_left (hlow.trans hhigh)
    (inv_nonneg.mpr (sq_nonneg r))
  have hra : r ^ 2 * a = ((m + 1 : ℕ) : ℝ)⁻¹ := by
    rw [ha_def, mul_inv_cancel_left₀ (pow_ne_zero 2 hr.ne')]
  have hrh : r ^ 2 * h = ((n + 1 : ℕ) : ℝ) := by
    rw [hh_def, mul_inv_cancel_left₀ (pow_ne_zero 2 hr.ne')]
  have hwin := heat_selected_integrable_positive_window hselect j k l R' a h ha
  filter_upwards [ae_restrict_ball_of_smul hr hRR hwin] with x hx
  have hxx : r • (r⁻¹ • x) = x := by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  constructor
  · have hmeas : MeasurableSet (Icc a h) := measurableSet_Icc
    have hin := (ae_restrict_iff' hmeas).mp hx.1
    have hT := (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hr2).ae hin
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hT] with t ht htI
    have htI' : (r ^ 2)⁻¹ • t ∈ Icc a h := by
      rw [smul_eq_mul]
      refine ⟨?_, ?_⟩
      · rw [ha_def]
        exact mul_le_mul_of_nonneg_left htI.1 (inv_nonneg.mpr (sq_nonneg r))
      · rw [hh_def]
        exact mul_le_mul_of_nonneg_left htI.2 (inv_nonneg.mpr (sq_nonneg r))
    have hpos : 0 < (r ^ 2)⁻¹ • t := lt_of_lt_of_le ha htI'.1
    have hd := integrable_akmHeatGradientDensity_dilation g r b ((r ^ 2)⁻¹ • t) hr hpos
      j k l (r⁻¹ • x) (ht htI')
    rwa [smul_eq_mul, mul_inv_cancel_left₀ (pow_ne_zero 2 hr.ne'), hxx] at hd
  · have hd := integrableOn_akmHeatGradientSpaceIntegral_dilation g r b a h hr ha hah
      j k l (r⁻¹ • x) hx.2
    rwa [hra, hrh, hxx] at hd

end EinsteinRelation.Correctors
