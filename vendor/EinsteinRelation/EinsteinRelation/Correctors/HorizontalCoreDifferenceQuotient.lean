import EinsteinRelation.Calculus.HorizontalCore
import EinsteinRelation.Calculus.HorizontalTranslationLp

/-! # L² identification of the bounded horizontal core derivative

Source `paper/main.tex:240–248`, generator and horizontal derivative. On the bounded smooth
core `IsHorizontalTest`, the translation difference quotient `t⁻¹ • (T_{t e_i} v - v)` of the
actual L² class `v` converges in `L²(Q)` along the punctured filter `𝓝[≠] 0` to the actual
horizontal derivative. The pointwise slope limit comes from the literal orbit along the
coordinate line, the uniform bound from the mean value inequality on that line, and the Lp
convergence from dominated convergence on the probability space. No continuity of `F` in the
environment, no density, mean-zero or generator-domain premise is assumed. Full generator and
H¹ characterization are separate internal obligations.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors

/-- The literal orbit of a bounded smooth core is differentiable at every point. -/
private theorem differentiableAt_orbit_core {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (ω : FieldPair d) (x : Vec d) :
    DifferentiableAt ℝ (orbit F ω) x :=
  ((hF.2.1 ω).differentiable (by simp)).differentiableAt

/-- Derivative of the coordinate line `u ↦ orbit F ω (u • e_i)` at any parameter `s`. -/
private theorem hasDerivAt_orbit_line_core {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (i : Fin d) (ω : FieldPair d) (s : ℝ) :
    HasDerivAt (fun u : ℝ => orbit F ω (u • unitVector i))
      (coordinateDerivative i (orbit F ω) (s • unitVector i)) s :=
  hasDerivAt_orbit_line i F ω s (differentiableAt_orbit_core hF ω _)

/-- Pointwise two-sided slope limit of the orbit along a coordinate line at the origin. -/
private theorem tendsto_orbit_slope {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (i : Fin d) (ω : FieldPair d) :
    Tendsto (fun t : ℝ => t⁻¹ * (F (translate (t • unitVector i) ω) - F ω)) (𝓝[≠] 0)
      (𝓝 (horizontalDerivative i F ω)) := by
  have hlim := (hasDerivAt_orbit_line_core hF i ω 0).tendsto_slope_zero
  have hderiv : coordinateDerivative i (orbit F ω) ((0 : ℝ) • unitVector i) =
      horizontalDerivative i F ω := by
    simp [horizontalDerivative]
  rw [hderiv] at hlim
  refine hlim.congr (fun t => ?_)
  simp only [orbit, zero_add, zero_smul, translate_zero, smul_eq_mul]

/-- Uniform mean value bound along a coordinate line, from the bounded orbit derivative. -/
private theorem abs_orbit_line_sub_le {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (i : Fin d) {D : ℝ}
    (hD : ∀ (ω : FieldPair d) (x : Vec d), |coordinateDerivative i (orbit F ω) x| ≤ D)
    (ω : FieldPair d) (t : ℝ) :
    |F (translate (t • unitVector i) ω) - F ω| ≤ D * |t| := by
  have hderiv : ∀ u : ℝ, ‖deriv (fun s : ℝ => orbit F ω (s • unitVector i)) u‖ ≤ D := fun u => by
    rw [(hasDerivAt_orbit_line_core hF i ω u).deriv, Real.norm_eq_abs]
    exact hD ω _
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun s : ℝ => orbit F ω (s • unitVector i)) (s := Set.univ) (C := D) (x := 0) (y := t)
    (fun u _ => (hasDerivAt_orbit_line_core hF i ω u).differentiableAt)
    (fun u _ => hderiv u) convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa only [Real.norm_eq_abs, sub_zero, zero_smul, orbit, translate_zero] using h

/-- Dominated convergence in `L²`: pointwise convergence with a uniform bound on the difference
gives `eLpNorm → 0` along any countably generated filter. -/
private theorem tendsto_eLpNorm_two_sub_of_dominated {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hf : ∀ t, Measurable (f t)) (hg : Measurable g)
    (hbd : ∀ t ω, |f t ω - g ω| ≤ C) (hlim : ∀ ω, Tendsto (fun t => f t ω) l (𝓝 (g ω))) :
    Tendsto (fun t => eLpNorm (fun ω => f t ω - g ω) 2 μ) l (𝓝 0) := by
  have hmeas : ∀ t, Measurable (fun ω => ‖f t ω - g ω‖ₑ ^ (2 : ℝ)) := fun t =>
    (((hf t).sub hg).enorm).pow_const _
  have hbound : ∀ t ω, ‖f t ω - g ω‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal C ^ (2 : ℝ) := fun t ω =>
    ENNReal.rpow_le_rpow
      (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (hbd t ω)) (by norm_num)
  have hK : ∫⁻ _ : Ω, ENNReal.ofReal C ^ (2 : ℝ) ∂μ ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      (measure_ne_top μ _)
  have hcont : Continuous fun x : ℝ => ‖x‖ₑ ^ (2 : ℝ) :=
    (ENNReal.continuous_rpow_const (y := 2)).comp continuous_enorm
  have hlim0 : ∀ ω, Tendsto (fun t => ‖f t ω - g ω‖ₑ ^ (2 : ℝ)) l (𝓝 0) := by
    intro ω
    have h1 : Tendsto (fun t => f t ω - g ω) l (𝓝 0) := by
      simpa only [sub_self] using (hlim ω).sub_const (g ω)
    have h2 : Tendsto (fun t => ‖f t ω - g ω‖ₑ ^ (2 : ℝ)) l (𝓝 (‖(0 : ℝ)‖ₑ ^ (2 : ℝ))) :=
      (hcont.tendsto 0).comp h1
    rwa [enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
  have hI : Tendsto (fun t => ∫⁻ ω, ‖f t ω - g ω‖ₑ ^ (2 : ℝ) ∂μ) l (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence (μ := μ)
      (F := fun t ω => ‖f t ω - g ω‖ₑ ^ (2 : ℝ)) (f := fun _ => (0 : ENNReal))
      (fun _ => ENNReal.ofReal C ^ (2 : ℝ)) (Filter.Eventually.of_forall hmeas)
      (Filter.Eventually.of_forall fun t => ae_of_all μ (hbound t)) hK (ae_of_all μ hlim0)
    simpa only [lintegral_zero] using h
  have hrw : ∀ t, eLpNorm (fun ω => f t ω - g ω) 2 μ =
      (∫⁻ ω, ‖f t ω - g ω‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro t
    have hm : AEStronglyMeasurable (fun ω => f t ω - g ω) μ :=
      ((hf t).sub hg).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) two_ne_zero ENNReal.ofNat_ne_top hm]
    simp only [ENNReal.toReal_ofNat]
  have hfin : Tendsto (fun t => (∫⁻ ω, ‖f t ω - g ω‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) l
      (𝓝 0) := by
    have h3 : Tendsto (fun t => (∫⁻ ω, ‖f t ω - g ω‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) l
        (𝓝 ((0 : ENNReal) ^ (1 / (2 : ℝ)))) :=
      ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hI
    rwa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h3
  exact Tendsto.congr (fun t => (hrw t).symm) hfin

/-- Actual horizontal derivative of the bounded smooth core as the `L²` limit of translation
difference quotients along the punctured filter, on the literal Lp action. -/
theorem tendsto_horizontalCore_differenceQuotient : ∀ {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) (i : Fin d),
    let v : Lp ℝ 2 Q := (hF.memLp Q 2).toLp F
    let w : Lp ℝ 2 Q := (hF.memLp_derivative Q 2 i).toLp (horizontalDerivative i F)
    Filter.Tendsto (fun t : ℝ => t⁻¹ • (translationLp Q hQ (t • unitVector i) v - v))
      (nhdsWithin 0 {t : ℝ | t ≠ 0}) (nhds w) := by
  intro d Q _ hQ F hF i
  dsimp only
  obtain ⟨D, hD0, hD⟩ := hF.bound_derivative i
  have hset : {t : ℝ | t ≠ 0} = {0}ᶜ := by
    ext t
    simp
  rw [hset]
  -- uniform bound on the difference quotient
  have hbd : ∀ (t : ℝ) (ω : FieldPair d),
      |t⁻¹ * (F (translate (t • unitVector i) ω) - F ω)| ≤ D := by
    intro t ω
    rcases eq_or_ne t 0 with rfl | ht
    · simpa using hD0
    · have habs : |t| ≠ 0 := abs_ne_zero.mpr ht
      rw [abs_mul, abs_inv]
      calc |t|⁻¹ * |F (translate (t • unitVector i) ω) - F ω|
          ≤ |t|⁻¹ * (D * |t|) :=
            mul_le_mul_of_nonneg_left (abs_orbit_line_sub_le hF i hD ω t)
              (inv_nonneg.mpr (abs_nonneg t))
        _ = D := by rw [mul_comm D (|t|), inv_mul_cancel_left₀ habs]
  -- measurability and bounds of the limit candidate
  have hmeas : ∀ t : ℝ, Measurable
      (fun ω : FieldPair d => t⁻¹ * (F (translate (t • unitVector i) ω) - F ω)) :=
    fun t =>
      ((hF.1.comp (Probability.measurable_translate (t • unitVector i))).sub hF.1).const_mul t⁻¹
  have hgmeas : Measurable (horizontalDerivative i F) := hF.measurable_derivative i
  have hgbd : ∀ ω, |horizontalDerivative i F ω| ≤ D := fun ω => hD ω 0
  have hbd2 : ∀ (t : ℝ) (ω : FieldPair d),
      |t⁻¹ * (F (translate (t • unitVector i) ω) - F ω) - horizontalDerivative i F ω| ≤ 2 * D := by
    intro t ω
    have h1 := abs_le.mp (hbd t ω)
    have h2 := abs_le.mp (hgbd ω)
    exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  -- identification of the Lp difference quotient with the genuine representative
  have hcoef : ∀ t : ℝ, ⇑(t⁻¹ • (translationLp Q hQ (t • unitVector i)
      ((hF.memLp Q 2).toLp F) - (hF.memLp Q 2).toLp F)) =ᵐ[Q]
      fun ω => t⁻¹ * (F (translate (t • unitVector i) ω) - F ω) := by
    intro t
    have hTv : translationLp Q hQ (t • unitVector i) ((hF.memLp Q 2).toLp F) =
        ((hF.memLp Q 2).comp_measurePreserving
          (measurePreserving_translate Q hQ (t • unitVector i))).toLp
          (fun ω => F (translate (t • unitVector i) ω)) :=
      translationLp_toLp Q hQ (t • unitVector i) (hF.memLp Q 2)
    have hT : ⇑(translationLp Q hQ (t • unitVector i) ((hF.memLp Q 2).toLp F)) =ᵐ[Q]
        fun ω => F (translate (t • unitVector i) ω) := by
      rw [hTv]
      exact MemLp.coeFn_toLp _
    filter_upwards [Lp.coeFn_smul t⁻¹ (translationLp Q hQ (t • unitVector i)
        ((hF.memLp Q 2).toLp F) - (hF.memLp Q 2).toLp F),
      Lp.coeFn_sub (translationLp Q hQ (t • unitVector i) ((hF.memLp Q 2).toLp F))
        ((hF.memLp Q 2).toLp F),
      hT, (hF.memLp Q 2).coeFn_toLp] with ω h1 h2 h3 h4
    simp only [h1, h2, h3, h4, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  -- dominated convergence in L² and transfer to the Lp difference quotient
  have hconv := tendsto_eLpNorm_two_sub_of_dominated (μ := Q) (l := 𝓝[≠] (0 : ℝ))
    (f := fun t ω => t⁻¹ * (F (translate (t • unitVector i) ω) - F ω))
    (g := horizontalDerivative i F) (C := 2 * D) hmeas hgmeas hbd2
    (fun ω => tendsto_orbit_slope hF i ω)
  refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr ?_
  refine hconv.congr (fun t => ?_)
  refine eLpNorm_congr_ae ?_
  filter_upwards [hcoef t, (hF.memLp_derivative Q 2 i).coeFn_toLp] with ω h1 h2
  simp only [Pi.sub_apply, h1, h2]

end EinsteinRelation.Correctors
