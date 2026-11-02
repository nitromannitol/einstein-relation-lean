import EinsteinFull.Calculus.LocalEnergySupport
import EinsteinFull.Calculus.LocalEnergyDomainSupport
import Mathlib.MeasureTheory.Integral.Average
import EinsteinFull.Calculus.ComplexLpChainSupport
import EinsteinFull.Calculus.ComplexTranslationSupport
import EinsteinFull.Frozen.ComplexHorizontalGradient

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- A stationary almost-sure upper bound holds on almost every spatial orbit.
The spatial null set may depend on the environment. -/
theorem ae_ae_stationary_orbit_le {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {u : FieldPair d → ℝ}
    (hu : Measurable u) {B : ℝ} (hB : ∀ᵐ ω ∂Q, u ω ≤ B) :
    ∀ᵐ ω ∂Q, ∀ᵐ y : Vec d ∂volume, u (translate y ω) ≤ B := by
  have hm : Measurable (fun p : Vec d × FieldPair d => translate p.1 p.2) :=
    Probability.continuous_translate.measurable
  apply (Measure.ae_ae_comm (μ := volume) (ν := Q)
    (p := fun y ω => u (translate y ω) ≤ B)
    (measurableSet_le (hu.comp hm) measurable_const)).mp
  apply Filter.Eventually.of_forall
  intro y
  apply ae_of_ae_map (μ := Q) (p := fun ω => u ω ≤ B)
    (Probability.measurable_translate y).aemeasurable
  rwa [hQ y]

/-- A bound on the Euclidean gradient controls its literal normalized ball
energy at every positive radius. The gradient representatives are unchanged. -/
theorem localSpatialEnergy_zero_le_of_ae_gradient_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ᵐ ω ∂reducedLaw Q, Real.sqrt (∑ j : Fin d, ‖G j ω‖ ^ 2) ≤ B)
    (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (x : Vec d) :
    ∀ᵐ ω ∂reducedLaw Q, localSpatialEnergy Q t ρ hρ x G 0 ω ≤ B := by
  let := reducedLaw_probability Q
  have hsq : ∀ᵐ ω ∂reducedLaw Q, (∑ j : Fin d, ‖G j ω‖ ^ 2) ≤ B ^ 2 := by
    filter_upwards [hG] with ω hω
    exact (Real.sqrt_le_iff).mp hω |>.2
  have hm : Measurable (fun ω => ∑ j : Fin d, ‖G j ω‖ ^ 2) :=
    Finset.measurable_fun_sum _ fun j _ =>
      (Lp.stronglyMeasurable (G j)).measurable.norm.pow_const 2
  have hv := ENNReal.toReal_pos_iff.mp (localSpatialEnergy_window_volume x ρ hρ)
  have : IsFiniteMeasure (volume.restrict {y : Vec d | euclideanNorm (y - x) < ρ}) :=
    isFiniteMeasure_restrict.mpr hv.2.ne
  have hzero : (0 : Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q] fun _ => 0 :=
    Lp.coeFn_zero _ _ _
  have hzeroNorm : (fun ω => ‖(0 : Lp ℂ 2 (reducedLaw Q)) ω‖) =ᵐ[reducedLaw Q]
      fun _ => (0 : ℝ) := by
    filter_upwards [hzero] with ω hω
    rw [hω, norm_zero]
  have hz := ae_ae_stationary_orbit_eq (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (0 : Lp ℂ 2 (reducedLaw Q))).measurable.norm
    measurable_const hzeroNorm
  filter_upwards [ae_ae_stationary_orbit_le (reducedLaw_stationary Q) hm hsq, hz]
    with ω hω hzω
  have hav : (⨍ y in {y : Vec d | euclideanNorm (y - x) < ρ},
      ∑ j : Fin d, ‖G j (translate y ω)‖ ^ 2) ≤ B ^ 2 := by
    calc
      _ ≤ ⨍ _y in {y : Vec d | euclideanNorm (y - x) < ρ}, B ^ 2 := by
        simp only [setAverage_eq, smul_eq_mul]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (measureReal_nonneg))
        exact integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => Finset.sum_nonneg fun j _ => sq_nonneg _)
          (integrable_const _) (ae_restrict_of_ae hω)
      _ = B ^ 2 := setAverage_const hv.1.ne' hv.2.ne _
  unfold localSpatialEnergy
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hB, ?_⟩
  calc
    _ = ⨍ y in {y : Vec d | euclideanNorm (y - x) < ρ},
        ∑ j : Fin d, ‖G j (translate y ω)‖ ^ 2 := by
      apply average_congr
      filter_upwards [ae_restrict_of_ae hzω] with y hy
      simp only [hy, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    _ ≤ B ^ 2 := hav

/-- The scalar-plus-local estimate uses the same gradient as its pointwise
counterpart. Its constant costs only a factor two, independently of radius. -/
theorem norm_add_localSpatialEnergy_le_of_ae_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℂ 2 (reducedLaw Q))
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ᵐ ω ∂reducedLaw Q,
      ‖f ω‖ + Real.sqrt (∑ j : Fin d, ‖G j ω‖ ^ 2) ≤ B)
    (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (x : Vec d) :
    ∀ᵐ ω ∂reducedLaw Q,
      ‖f ω‖ + localSpatialEnergy Q t ρ hρ x G 0 ω ≤ 2 * B := by
  have hG : ∀ᵐ ω ∂reducedLaw Q, Real.sqrt (∑ j : Fin d, ‖G j ω‖ ^ 2) ≤ B := by
    filter_upwards [h] with ω hω
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans hω
  filter_upwards [h, localSpatialEnergy_zero_le_of_ae_gradient_bound Q G hB hG t ρ hρ x]
    with ω hω he
  have hf : ‖f ω‖ ≤ B :=
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hω
  calc
    _ ≤ B + B := add_le_add hf he
    _ = 2 * B := (two_mul B).symm

/-- Doubling a crude bound is absorbed by doubling its structural constant,
with the same polynomial exponent and no dependence on the force or law. -/
theorem twice_crudeEnergyBound_le {C t z : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) (N : ℕ) :
    2 * (C * (2 + t) ^ N * Real.exp (C * z ^ 2 * t)) ≤
      (2 * C) * (2 + t) ^ N * Real.exp ((2 * C) * z ^ 2 * t) := by
  have he : Real.exp (C * z ^ 2 * t) ≤ Real.exp ((2 * C) * z ^ 2 * t) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ ht
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg z)
  calc
    _ = (2 * C) * (2 + t) ^ N * Real.exp (C * z ^ 2 * t) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he
      (mul_nonneg (mul_nonneg (by norm_num) hC) (pow_nonneg (by linarith) N))

/-- A differentiable, uniformly Lipschitz representative on almost every
translation orbit has the actual strong horizontal L2 derivative. No
measurability premise on the representatives is needed beyond their AE
identification with the supplied L2 classes. -/
theorem hasComplexHorizontalDerivative_of_ae_lipschitz_orbits
    {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (i : Fin d) (f g : Lp ℂ 2 Q)
    {F H : FieldPair d → ℂ} (hf : f =ᵐ[Q] F) (hg : g =ᵐ[Q] H)
    (K : ℝ≥0)
    (hlip : ∀ᵐ ω ∂Q, LipschitzWith K (fun t : ℝ => F (translate (t • unitVector i) ω)))
    (hderiv : ∀ᵐ ω ∂Q, HasDerivAt
      (fun t : ℝ => F (translate (t • unitVector i) ω)) (H ω) 0) :
    HasComplexHorizontalDerivative Q hQ i f g := by
  let q := fun (t : ℝ) ω => t⁻¹ • (F (translate (t • unitVector i) ω) - F ω)
  have hq : ∀ᵐ ω ∂Q, ∀ t : ℝ, ‖q t ω‖ ≤ (K : ℝ) := by
    filter_upwards [hlip] with ω hω
    intro t
    by_cases ht : t = 0
    · simp only [q, ht, inv_zero, zero_smul, norm_zero]
      exact K.coe_nonneg
    · have hb := hω.norm_sub_le t 0
      simp only [zero_smul, translate_zero, sub_zero, Real.norm_eq_abs] at hb
      calc
        ‖q t ω‖ = |t|⁻¹ * ‖F (translate (t • unitVector i) ω) - F ω‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv]
        _ ≤ |t|⁻¹ * ((K : ℝ) * |t|) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg t))
        _ = (K : ℝ) := by rw [mul_left_comm, inv_mul_cancel₀ (abs_ne_zero.mpr ht), mul_one]
  have htend : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (complexTranslation Q hQ (t • unitVector i) f - f))
      (nhdsWithin 0 {0}ᶜ) (nhds g) := by
    apply tendsto_complexLp_of_dominated (F := q) (f := H) _ hg
      (b := fun _ => 2 * (K : ℝ)) (integrable_const _) _ _
    · intro t
      have htrans := (measurePreserving_translate Q hQ (t • unitVector i)).quasiMeasurePreserving.ae hf
      filter_upwards [Lp.coeFn_smul t⁻¹ (complexTranslation Q hQ (t • unitVector i) f - f),
        Lp.coeFn_sub (complexTranslation Q hQ (t • unitVector i) f) f,
        coeFn_complexTranslation Q hQ (t • unitVector i) f, hf, htrans]
        with ω ha hb hc hd he
      simp only [Pi.smul_apply, Pi.sub_apply] at ha hb
      rw [ha, hb, hc, hd, he]
    · apply Filter.Eventually.of_forall
      intro t
      filter_upwards [hq, hlip, hderiv] with ω hω hl hd
      calc
        ‖q t ω - H ω‖ ≤ ‖q t ω‖ + ‖H ω‖ := norm_sub_le _ _
        _ ≤ (K : ℝ) + K := add_le_add (hω t) (hd.le_of_lipschitz hl)
        _ = 2 * (K : ℝ) := by ring
    · filter_upwards [hderiv] with ω hω
      simpa only [q, zero_add, zero_smul, translate_zero] using
        (hasDerivAt_iff_tendsto_slope_zero.mp hω)
  simpa only [HasComplexHorizontalDerivative,
    RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv]
    using! htend

/-- A bounded classical orbit derivative automatically has a measurable L2
class and is the strong horizontal derivative. Measurability of H follows
from pointwise limits of the measurable difference quotients. -/
theorem exists_horizontalDerivative_of_ae_lipschitz_orbits
    {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (i : Fin d) (f : Lp ℂ 2 Q)
    {F H : FieldPair d → ℂ} (hf : f =ᵐ[Q] F) (K : ℝ≥0)
    (hlip : ∀ᵐ ω ∂Q, LipschitzWith K (fun t : ℝ => F (translate (t • unitVector i) ω)))
    (hderiv : ∀ᵐ ω ∂Q, HasDerivAt
      (fun t : ℝ => F (translate (t • unitVector i) ω)) (H ω) 0) :
    ∃ g : Lp ℂ 2 Q, g =ᵐ[Q] H ∧
      HasComplexHorizontalDerivative Q hQ i f g ∧
      (∀ᵐ ω ∂Q, ‖g ω‖ ≤ (K : ℝ)) := by
  let q := fun (t : ℝ) ω => t⁻¹ • (F (translate (t • unitVector i) ω) - F ω)
  have hFm : AEStronglyMeasurable F Q := (Lp.aestronglyMeasurable f).congr hf
  have hqm (t : ℝ) : AEStronglyMeasurable (q t) Q := by
    exact ((hFm.comp_quasiMeasurePreserving
      (measurePreserving_translate Q hQ (t • unitVector i)).quasiMeasurePreserving).sub hFm).const_smul t⁻¹
  have hlim : ∀ᵐ ω ∂Q, Filter.Tendsto (fun t : ℝ => q t ω)
      (nhdsWithin 0 {0}ᶜ) (nhds (H ω)) := by
    filter_upwards [hderiv] with ω hω
    simpa only [q, zero_add, zero_smul, translate_zero] using
      (hasDerivAt_iff_tendsto_slope_zero.mp hω)
  have hHm : AEStronglyMeasurable H Q :=
    aestronglyMeasurable_of_tendsto_ae (nhdsWithin (0 : ℝ) {0}ᶜ) hqm hlim
  have hbound : ∀ᵐ ω ∂Q, ‖H ω‖ ≤ (K : ℝ) := by
    filter_upwards [hlip, hderiv] with ω hl hd
    exact hd.le_of_lipschitz hl
  have hmem : MemLp H 2 Q := MemLp.of_bound hHm K hbound
  refine ⟨hmem.toLp H, hmem.coeFn_toLp, ?_, ?_⟩
  · exact hasComplexHorizontalDerivative_of_ae_lipschitz_orbits hQ i f
      (hmem.toLp H) hf hmem.coeFn_toLp K hlip hderiv
  · filter_upwards [hmem.coeFn_toLp, hbound] with ω he hb
    rwa [he]

/-- Classical bounded orbit derivatives produce one actual horizontal gradient
for both the Euclidean pointwise bound and every normalized spatial ball
energy. This is a representative criterion, not a kernel/semigroup
identification assumption. -/
theorem exists_commonGradient_of_ae_lipschitz_orbits
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (f : Lp ℂ 2 (reducedLaw Q)) {F : FieldPair d → ℂ}
    {H : Fin d → FieldPair d → ℂ} (hf : f =ᵐ[reducedLaw Q] F) (K : ℝ≥0)
    (hlip : ∀ j : Fin d, ∀ᵐ ω ∂reducedLaw Q,
      LipschitzWith K (fun s : ℝ => F (translate (s • unitVector j) ω)))
    (hderiv : ∀ j : Fin d, ∀ᵐ ω ∂reducedLaw Q, HasDerivAt
      (fun s : ℝ => F (translate (s • unitVector j) ω)) (H j ω) 0)
    {B : ℝ} (hB : 0 ≤ B)
    (hpoint : ∀ᵐ ω ∂reducedLaw Q,
      ‖F ω‖ + Real.sqrt (∑ j : Fin d, ‖H j ω‖ ^ 2) ≤ B) :
    ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G ∧
      (∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ + Real.sqrt (∑ j : Fin d, ‖G j ω‖ ^ 2) ≤ B) ∧
      (∀ (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (x : Vec d), ∀ᵐ ω ∂reducedLaw Q,
        ‖f ω‖ + localSpatialEnergy Q t ρ hρ x G 0 ω ≤ 2 * B) := by
  let := reducedLaw_probability Q
  have hex (j : Fin d) := exists_horizontalDerivative_of_ae_lipschitz_orbits
    (reducedLaw_stationary Q) j f hf K (hlip j) (hderiv j)
  choose G hrep hgrad hbound using hex
  have hp : ∀ᵐ ω ∂reducedLaw Q,
      ‖f ω‖ + Real.sqrt (∑ j : Fin d, ‖G j ω‖ ^ 2) ≤ B := by
    filter_upwards [hf, ae_all_iff.mpr hrep, hpoint] with ω he hG hb
    simpa only [he, hG] using hb
  exact ⟨G, hgrad, hp, fun t ρ hρ x =>
    norm_add_localSpatialEnergy_le_of_ae_bound Q f G hB hp t ρ hρ x⟩

end EinsteinFull
