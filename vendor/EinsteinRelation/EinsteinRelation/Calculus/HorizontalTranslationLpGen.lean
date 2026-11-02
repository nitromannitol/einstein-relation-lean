import EinsteinRelation.Calculus.HorizontalMollification
import EinsteinRelation.Calculus.HorizontalTranslationLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Real.ConjExponents
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Translations and horizontal mollification on `L^p(Q)`

Source `paper/main.tex:240–244` (translation group) and `paper/main.tex:548–566`
(horizontal smoothing). For a stationary probability law `Q` on coefficient pairs and
`1 ≤ p < ∞`:

* spatial translations act on `L^p(Q)` by linear isometries, jointly continuous in the
  translation vector and the class (`translationLpGen`);
* for a probability density `ζ`, the horizontal smoothing `horizontalMollify ζ F` is a
  contraction of `L^p(Q)`;
* for a family of nonnegative unit-mass densities whose supports shrink to the origin,
  `horizontalMollify (ζ ε) F → F` in `L^p(Q)` as `ε → 0⁺`. The unit-mass Euclidean
  mollifier of `Calculus/Mollifier.lean`, rescaled to radius `ε`, is a concrete family.

The smoothing estimates use Jensen's inequality for the density `ζ(z) dz` in lintegral
form, Tonelli's theorem, and stationarity. Pointwise identities for the smoothing are
taken almost everywhere, where the translated orbit is integrable.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Calculus

/-- Spatial translation of `L^p(Q)` by `x`, for `1 ≤ p`, as a linear isometry. -/
def translationLpGen {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : Vec d) : Lp ℝ p Q →ₗᵢ[ℝ] Lp ℝ p Q :=
  Lp.compMeasurePreservingₗᵢ ℝ (translate x) (measurePreserving_translate Q hQ x)

theorem coeFn_translationLpGen {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : Vec d) (f : Lp ℝ p Q) :
    translationLpGen Q hQ p x f =ᵐ[Q] fun ω => f (translate x ω) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_translate Q hQ x)

theorem translationLpGen_zero {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp ℝ p Q) : translationLpGen Q hQ p 0 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_translationLpGen Q hQ p 0 f] with ω hω
  simpa only [translate_zero] using hω

/-- Joint continuity of `(x, f) ↦ f ∘ T_x` on `L^p(Q)` for every finite exponent. -/
theorem continuous_translationLpGen {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Continuous (fun q : Vec d × Lp ℝ p Q => translationLpGen Q hQ p q.1 q.2) := by
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  let g : Vec d × Lp ℝ p Q → C(FieldPair d, FieldPair d) :=
    fun q => ⟨translate q.1, Probability.continuous_translate.comp (continuous_const.prodMk continuous_id)⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Probability.continuous_translate.comp ((continuous_fst.fst).prodMk continuous_snd)
  exact continuous_snd.compMeasurePreservingLp hg (fun q => measurePreserving_translate Q hQ q.1) hp

theorem tendsto_translationLpGen_zero {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : Lp ℝ p Q) : Tendsto (fun x : Vec d => translationLpGen Q hQ p x f) (𝓝 0) (𝓝 f) := by
  have h : Continuous (fun x : Vec d => translationLpGen Q hQ p x f) :=
    (continuous_translationLpGen Q hQ p hp).comp (continuous_id.prodMk continuous_const)
  simpa only [translationLpGen_zero] using h.tendsto 0

/-! ### Lintegral Jensen inequality and Tonelli for translations -/

/-- Jensen's inequality in lintegral form: `(∫ G)^m ≤ ∫ G^m` for a probability measure. -/
private theorem lintegral_rpow_le_of_univ {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (hμ : μ Set.univ = 1) {m : ℝ} (hm : 1 ≤ m) {G : α → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ a, G a ∂μ) ^ m ≤ ∫⁻ a, G a ^ m ∂μ := by
  rcases hm.eq_or_lt with h1 | h1
  · rw [← h1]
    simp
  · have hpq := Real.HolderConjugate.conjExponent h1
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hG.aemeasurable
      (measurable_const : Measurable fun _ : α => (1 : ℝ≥0∞)).aemeasurable
    simp only [Pi.mul_apply, mul_one, lintegral_const, hμ, one_mul, ENNReal.one_rpow] at h
    have hm0 : m ≠ 0 := (zero_lt_one.trans h1).ne'
    have hpow := ENNReal.rpow_le_rpow h (zero_le_one.trans hm)
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hm0, ENNReal.rpow_one] at hpow

private theorem lintegral_withDensity_weight {d : ℕ} {ζ : Vec d → ℝ} (hζm : Measurable ζ)
    {G : Vec d → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z, G z ∂((volume : Measure (Vec d)).withDensity fun z => ENNReal.ofReal (ζ z)) =
      ∫⁻ z, ENNReal.ofReal (ζ z) * G z :=
  lintegral_withDensity_eq_lintegral_mul _ hζm.ennreal_ofReal hG

/-- Jensen's inequality for the probability density `ofReal ∘ ζ` of unit total mass. -/
private theorem lintegral_weighted_rpow_le {d : ℕ} {ζ : Vec d → ℝ} (hζm : Measurable ζ)
    (hζl : ∫⁻ z, ENNReal.ofReal (ζ z) = 1) {m : ℝ} (hm : 1 ≤ m) {G : Vec d → ℝ≥0∞}
    (hG : Measurable G) :
    (∫⁻ z, ENNReal.ofReal (ζ z) * G z) ^ m ≤ ∫⁻ z, ENNReal.ofReal (ζ z) * G z ^ m := by
  have hμ : ((volume : Measure (Vec d)).withDensity fun z => ENNReal.ofReal (ζ z)) Set.univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hζl]
  have h := lintegral_rpow_le_of_univ _ hμ hm hG
  rw [lintegral_withDensity_weight hζm hG, lintegral_withDensity_weight hζm (hG.pow_const m)] at h
  exact h

private theorem integrable_of_integral_eq_one {d : ℕ} {ζ : Vec d → ℝ} (hζ1 : ∫ z, ζ z = 1) :
    Integrable ζ (volume : Measure (Vec d)) := by
  by_contra h
  rw [integral_undef h] at hζ1
  exact zero_ne_one hζ1

private theorem lintegral_ofReal_eq_one {d : ℕ} {ζ : Vec d → ℝ} (hζ0 : ∀ z, 0 ≤ ζ z)
    (hζ1 : ∫ z, ζ z = 1) : ∫⁻ z, ENNReal.ofReal (ζ z) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one hζ1)
    (ae_of_all _ hζ0), hζ1, ENNReal.ofReal_one]

private theorem measurable_translate_point {d : ℕ} (ω : FieldPair d) :
    Measurable (fun z : Vec d => translate z ω) := by
  have hc : Continuous (fun z : Vec d => (z, ω)) := continuous_id.prodMk continuous_const
  exact (Probability.continuous_translate.comp hc).measurable

private theorem measurable_translate_swap {d : ℕ} :
    Measurable (fun q : FieldPair d × Vec d => translate q.2 q.1) :=
  Probability.continuous_translate.measurable.comp measurable_swap

/-- Stationarity transports lintegrals of translated `ℝ≥0∞`-valued observables. -/
private theorem lintegral_translate_eq {d : ℕ} {Q : Measure (FieldPair d)} (hQ : IsStationary Q)
    {G : FieldPair d → ℝ≥0∞} (hG : Measurable G) (z : Vec d) :
    ∫⁻ ω, G (translate z ω) ∂Q = ∫⁻ ω, G ω ∂Q := by
  rw [← lintegral_map hG (Probability.measurable_translate z), hQ z]

/-- Tonelli for a weighted translation integral: the weight depends only on the translation. -/
private theorem lintegral_comm_weight {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {W : Vec d → ℝ≥0∞} (hW : Measurable W) (hWfin : ∀ z, W z ≠ ∞)
    {h : FieldPair d → Vec d → ℝ≥0∞} (hh : Measurable fun q : FieldPair d × Vec d => h q.1 q.2) :
    ∫⁻ ω, ∫⁻ z, W z * h ω z ∂(volume : Measure (Vec d)) ∂Q =
      ∫⁻ z, W z * ∫⁻ ω, h ω z ∂Q ∂(volume : Measure (Vec d)) := by
  calc ∫⁻ ω, ∫⁻ z, W z * h ω z ∂(volume : Measure (Vec d)) ∂Q
      = ∫⁻ z, ∫⁻ ω, W z * h ω z ∂Q ∂(volume : Measure (Vec d)) :=
        lintegral_lintegral_swap (f := fun ω z => W z * h ω z)
          ((hW.comp measurable_snd).mul hh).aemeasurable
    _ = ∫⁻ z, W z * ∫⁻ ω, h ω z ∂Q ∂(volume : Measure (Vec d)) :=
        lintegral_congr fun z => lintegral_const_mul' (W z) _ (hWfin z)

/-- A unit-mass weight turns the translated `ℝ≥0∞` integral back into the stationary one. -/
private theorem lintegral_weight_translate {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {ζ : Vec d → ℝ} (hζm : Measurable ζ)
    (hζl : ∫⁻ z, ENNReal.ofReal (ζ z) = 1) {G : FieldPair d → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (ζ z) * G (translate z ω) ∂(volume : Measure (Vec d)) ∂Q =
      ∫⁻ ω, G ω ∂Q := by
  have hh : Measurable fun q : FieldPair d × Vec d => G (translate q.2 q.1) :=
    hG.comp measurable_translate_swap
  rw [lintegral_comm_weight hζm.ennreal_ofReal (fun z => ENNReal.ofReal_ne_top)
    (h := fun ω z => G (translate z ω)) hh]
  simp only [lintegral_translate_eq hQ hG]
  rw [lintegral_mul_const _ hζm.ennreal_ofReal, hζl, one_mul]

/-- The weighted orbit integrand is integrable for `Q`-almost every field. -/
private theorem ae_integrable_weight_translate {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {ζ : Vec d → ℝ} (hζm : Measurable ζ)
    (hζ0 : ∀ z, 0 ≤ ζ z) (hζl : ∫⁻ z, ENNReal.ofReal (ζ z) = 1) {F : FieldPair d → ℝ}
    (hF : Measurable F) (hF1 : ∫⁻ ω, ‖F ω‖ₑ ∂Q ≠ ∞) :
    ∀ᵐ ω ∂Q, Integrable (fun z => ζ z * F (translate z ω)) (volume : Measure (Vec d)) := by
  have hHm : Measurable fun ω : FieldPair d =>
      ∫⁻ z, ENNReal.ofReal (ζ z) * ‖F (translate z ω)‖ₑ ∂(volume : Measure (Vec d)) :=
    ((hζm.ennreal_ofReal.comp measurable_snd).mul
      ((hF.comp measurable_translate_swap).enorm)).lintegral_prod_right'
  have hfin : ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (ζ z) * ‖F (translate z ω)‖ₑ ∂(volume : Measure (Vec d)) ∂Q
      ≠ ∞ := by
    rw [lintegral_weight_translate hQ hζm hζl hF.enorm]
    exact hF1
  filter_upwards [ae_lt_top hHm hfin] with ω hω
  have heq : ∫⁻ z, ‖ζ z * F (translate z ω)‖ₑ ∂(volume : Measure (Vec d)) =
      ∫⁻ z, ENNReal.ofReal (ζ z) * ‖F (translate z ω)‖ₑ ∂(volume : Measure (Vec d)) :=
    lintegral_congr fun z => by rw [enorm_mul, Real.enorm_eq_ofReal (hζ0 z)]
  refine ⟨(hζm.mul (hF.comp (measurable_translate_point ω))).aestronglyMeasurable, ?_⟩
  show ∫⁻ z, ‖ζ z * F (translate z ω)‖ₑ ∂(volume : Measure (Vec d)) < ∞
  rw [heq]
  exact hω

/-- Almost-everywhere smoothing identity and the lintegral bound for the `m`-th moment of
the increment `horizontalMollify ζ F - F`. -/
private theorem lintegral_mollify_sub_le {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {ζ : Vec d → ℝ} (hζm : Measurable ζ)
    (hζ0 : ∀ z, 0 ≤ ζ z) (hζ1 : ∫ z, ζ z = 1) {F : FieldPair d → ℝ} (hF : Measurable F)
    (hF1 : ∫⁻ ω, ‖F ω‖ₑ ∂Q ≠ ∞) {m : ℝ} (hm : 1 ≤ m) :
    ∫⁻ ω, ‖horizontalMollify ζ F ω - F ω‖ₑ ^ m ∂Q ≤
      ∫⁻ z, ENNReal.ofReal (ζ z) * ∫⁻ ω, ‖F (translate z ω) - F ω‖ₑ ^ m ∂Q
        ∂(volume : Measure (Vec d)) := by
  have hm0 : (0 : ℝ) ≤ m := zero_le_one.trans hm
  have hζi : Integrable ζ (volume : Measure (Vec d)) := integrable_of_integral_eq_one hζ1
  have hζl : ∫⁻ z, ENNReal.ofReal (ζ z) = 1 := lintegral_ofReal_eq_one hζ0 hζ1
  have hgood := ae_integrable_weight_translate hQ hζm hζ0 hζl hF hF1
  have hpt : ∀ᵐ ω ∂Q, ‖horizontalMollify ζ F ω - F ω‖ₑ ^ m ≤
      ∫⁻ z, ENNReal.ofReal (ζ z) * ‖F (translate z ω) - F ω‖ₑ ^ m ∂(volume : Measure (Vec d)) := by
    filter_upwards [hgood] with ω hω
    have hconst : Integrable (fun z => ζ z * F ω) (volume : Measure (Vec d)) :=
      hζi.mul_const (F ω)
    have hconst_int : ∫ z, ζ z * F ω = F ω := by
      rw [integral_mul_const, hζ1, one_mul]
    have hsplit : ∫ z, ζ z * (F (translate z ω) - F ω) =
        (∫ z, ζ z * F (translate z ω)) - ∫ z, ζ z * F ω := by
      simp only [mul_sub]
      exact integral_sub hω hconst
    have hid : horizontalMollify ζ F ω - F ω = ∫ z, ζ z * (F (translate z ω) - F ω) := by
      unfold horizontalMollify
      rw [hsplit, hconst_int]
    have hnorm : ‖horizontalMollify ζ F ω - F ω‖ₑ ≤
        ∫⁻ z, ENNReal.ofReal (ζ z) * ‖F (translate z ω) - F ω‖ₑ ∂(volume : Measure (Vec d)) := by
      rw [hid]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun z => ?_))
      rw [enorm_mul, Real.enorm_eq_ofReal (hζ0 z)]
    have hG : Measurable fun z : Vec d => ‖F (translate z ω) - F ω‖ₑ :=
      ((hF.comp (measurable_translate_point ω)).sub (measurable_const : Measurable fun _ : Vec d => F ω)).enorm
    exact (ENNReal.rpow_le_rpow hnorm hm0).trans (lintegral_weighted_rpow_le hζm hζl hm hG)
  have hh : Measurable fun q : FieldPair d × Vec d => ‖F (translate q.2 q.1) - F q.1‖ₑ ^ m :=
    (((hF.comp measurable_translate_swap).sub (hF.comp measurable_fst)).enorm).pow_const m
  calc ∫⁻ ω, ‖horizontalMollify ζ F ω - F ω‖ₑ ^ m ∂Q
      ≤ ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (ζ z) * ‖F (translate z ω) - F ω‖ₑ ^ m
          ∂(volume : Measure (Vec d)) ∂Q := lintegral_mono_ae hpt
    _ = ∫⁻ z, ENNReal.ofReal (ζ z) * ∫⁻ ω, ‖F (translate z ω) - F ω‖ₑ ^ m ∂Q
          ∂(volume : Measure (Vec d)) :=
        lintegral_comm_weight hζm.ennreal_ofReal (fun z => ENNReal.ofReal_ne_top)
          (h := fun ω z => ‖F (translate z ω) - F ω‖ₑ ^ m) hh

/-! ### Elementary real and norm facts -/

private theorem one_le_toReal_of_ge {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) : 1 ≤ p.toReal := by
  simpa using ENNReal.toReal_mono hp hp1

private theorem eLpNorm_rpow_toReal_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) (hg : AEStronglyMeasurable g μ) :
    eLpNorm g p μ ^ p.toReal = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ := by
  have hq0 : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hpt).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hg, ← ENNReal.rpow_mul, one_div_mul_cancel hq0,
    ENNReal.rpow_one]

private theorem norm_le_euclideanNorm_vec {d : ℕ} (x : Vec d) : ‖x‖ ≤ euclideanNorm x := by
  have hr : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  refine (pi_norm_le_iff_of_nonneg hr).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  have hsq : x i ^ 2 ≤ euclideanSq x := by
    unfold euclideanSq dot
    rw [sq]
    exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
      (Finset.mem_univ i)
  exact Real.abs_le_sqrt hsq

/-! ### `L^p` contraction of the horizontal smoothing -/

/-- **Contraction.** For a stationary probability law `Q`, a measurable field `F` and a
probability density `ζ`, the horizontal smoothing does not increase the `L^p(Q)` norm. -/
theorem eLpNorm_horizontalMollify_le {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {ζ : Vec d → ℝ} (hζm : Measurable ζ) (hζ0 : ∀ z, 0 ≤ ζ z) (hζ1 : ∫ z, ζ z = 1)
    {F : FieldPair d → ℝ} (hF : Measurable F) :
    eLpNorm (horizontalMollify ζ F) p Q ≤ eLpNorm F p Q := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hq : 1 ≤ p.toReal := one_le_toReal_of_ge hp1 hp
  have hq0 : 0 ≤ p.toReal := zero_le_one.trans hq
  have hl : ∫⁻ z, ENNReal.ofReal (ζ z) = 1 := lintegral_ofReal_eq_one hζ0 hζ1
  have hnorm : ∀ ω, ‖horizontalMollify ζ F ω‖ₑ ≤
      ∫⁻ z, ENNReal.ofReal (ζ z) * ‖F (translate z ω)‖ₑ ∂(volume : Measure (Vec d)) := by
    intro ω
    unfold horizontalMollify
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun z => ?_))
    rw [enorm_mul, Real.enorm_eq_ofReal (hζ0 z)]
  have hGω : ∀ ω : FieldPair d, Measurable fun z : Vec d => ‖F (translate z ω)‖ₑ :=
    fun ω => (hF.comp (measurable_translate_point ω)).enorm
  have hGF : Measurable fun ω : FieldPair d => ‖F ω‖ₑ ^ p.toReal := hF.enorm.pow_const _
  have hh : Measurable fun q : FieldPair d × Vec d => ‖F (translate q.2 q.1)‖ₑ ^ p.toReal :=
    ((hF.comp measurable_translate_swap).enorm).pow_const _
  have hcore : ∫⁻ ω, ‖horizontalMollify ζ F ω‖ₑ ^ p.toReal ∂Q ≤ ∫⁻ ω, ‖F ω‖ₑ ^ p.toReal ∂Q := by
    calc ∫⁻ ω, ‖horizontalMollify ζ F ω‖ₑ ^ p.toReal ∂Q
        ≤ ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (ζ z) * ‖F (translate z ω)‖ₑ ^ p.toReal
            ∂(volume : Measure (Vec d)) ∂Q :=
          lintegral_mono fun ω =>
            (ENNReal.rpow_le_rpow (hnorm ω) hq0).trans
              (lintegral_weighted_rpow_le hζm hl hq (hGω ω))
      _ = ∫⁻ z, ENNReal.ofReal (ζ z) * ∫⁻ ω, ‖F (translate z ω)‖ₑ ^ p.toReal ∂Q
            ∂(volume : Measure (Vec d)) :=
          lintegral_comm_weight hζm.ennreal_ofReal (fun z => ENNReal.ofReal_ne_top)
            (h := fun ω z => ‖F (translate z ω)‖ₑ ^ p.toReal) hh
      _ = ∫⁻ z, ENNReal.ofReal (ζ z) * ∫⁻ ω, ‖F ω‖ₑ ^ p.toReal ∂Q ∂(volume : Measure (Vec d)) :=
          lintegral_congr fun z => by rw [lintegral_translate_eq hQ hGF z]
      _ = (∫⁻ z, ENNReal.ofReal (ζ z) ∂(volume : Measure (Vec d))) * ∫⁻ ω, ‖F ω‖ₑ ^ p.toReal ∂Q :=
          lintegral_mul_const _ hζm.ennreal_ofReal
      _ = ∫⁻ ω, ‖F ω‖ₑ ^ p.toReal ∂Q := by rw [hl, one_mul]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
      (measurable_horizontalMollify ζ hζm hF).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hF.aestronglyMeasurable]
  exact ENNReal.rpow_le_rpow hcore (one_div_nonneg.mpr hq0)

/-! ### Convergence of the horizontal smoothing in `L^p(Q)` -/

/-- **Convergence.** Let `F` be measurable and in `L^p(Q)`, and let `ζ ε` be nonnegative
unit-mass densities whose supports lie in the Euclidean ball of radius `ε`. Then
`horizontalMollify (ζ ε) F → F` in `L^p(Q)` as `ε → 0⁺`. -/
theorem tendsto_eLpNorm_horizontalMollify_sub {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {F : FieldPair d → ℝ} (hF : Measurable F) (hFp : MemLp F p Q)
    (ζ : ℝ → Vec d → ℝ) (hζm : ∀ ε, 0 < ε → Measurable (ζ ε))
    (hζ0 : ∀ ε, 0 < ε → ∀ z, 0 ≤ ζ ε z) (hζ1 : ∀ ε, 0 < ε → ∫ z, ζ ε z = 1)
    (hζs : ∀ ε, 0 < ε → ∀ z, ζ ε z ≠ 0 → euclideanNorm z < ε) :
    Tendsto (fun ε => eLpNorm (fun ω => horizontalMollify (ζ ε) F ω - F ω) p Q)
      (𝓝[>] 0) (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hq : 1 ≤ p.toReal := one_le_toReal_of_ge hp1 hp
  have hqpos : 0 < p.toReal := zero_lt_one.trans_le hq
  have hF1' : ∫⁻ ω, ‖F ω‖ₑ ∂Q < ∞ := (hFp.integrable hp1).hasFiniteIntegral
  have hF1 : ∫⁻ ω, ‖F ω‖ₑ ∂Q ≠ ∞ := hF1'.ne
  -- Translation increments converge in `L^p(Q)`, hence their `p`-th moments vanish at `0`.
  have hG0 : Tendsto (fun z : Vec d => eLpNorm (fun ω => F (translate z ω) - F ω) p Q)
      (𝓝 0) (𝓝 0) := by
    have hL := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun z : Vec d => translationLpGen Q hQ p z (hFp.toLp F)) (hFp.toLp F)).mp
      (tendsto_translationLpGen_zero Q hQ p hp (hFp.toLp F))
    refine Filter.Tendsto.congr (fun z => ?_) hL
    apply eLpNorm_congr_ae
    filter_upwards [coeFn_translationLpGen Q hQ p z (hFp.toLp F), MemLp.coeFn_toLp hFp,
      (measurePreserving_translate Q hQ z).quasiMeasurePreserving.ae (MemLp.coeFn_toLp hFp)]
      with ω h1 h2 h3
    have h1' : translationLpGen Q hQ p z (hFp.toLp F) ω = (hFp.toLp F) (translate z ω) := h1
    have h3' : (hFp.toLp F) (translate z ω) = F (translate z ω) := h3
    show translationLpGen Q hQ p z (hFp.toLp F) ω - (hFp.toLp F) ω = F (translate z ω) - F ω
    rw [h1', h2, h3']
  have hN : Tendsto (fun z : Vec d => ∫⁻ ω, ‖F (translate z ω) - F ω‖ₑ ^ p.toReal ∂Q)
      (𝓝 0) (𝓝 0) := by
    have hpow : Tendsto (fun z : Vec d => eLpNorm (fun ω => F (translate z ω) - F ω) p Q ^ p.toReal)
        (𝓝 0) (𝓝 0) := by
      have h := (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto (0 : ℝ≥0∞)
      rw [ENNReal.zero_rpow_of_pos hqpos] at h
      exact h.comp hG0
    refine Filter.Tendsto.congr (fun z => ?_) hpow
    exact eLpNorm_rpow_toReal_eq hp0 hp
      ((hF.comp (Probability.measurable_translate z)).sub hF).aestronglyMeasurable
  have hcont : Tendsto (fun x : ℝ≥0∞ => x ^ (1 / p.toReal)) (𝓝 0) (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto (0 : ℝ≥0∞)
    rw [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hqpos)] at h
    exact h
  have hI : Tendsto (fun ε => ∫⁻ ω, ‖horizontalMollify (ζ ε) F ω - F ω‖ₑ ^ p.toReal ∂Q)
      (𝓝[>] 0) (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro η hη
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.eventually_nhds_iff.mp (ENNReal.tendsto_nhds_zero.mp hN η hη)
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεδ : ε < δ := hε.2
    have hζl : ∫⁻ z, ENNReal.ofReal (ζ ε z) = 1 :=
      lintegral_ofReal_eq_one (hζ0 ε hε0) (hζ1 ε hε0)
    have hpt : ∀ z, ENNReal.ofReal (ζ ε z) * (∫⁻ ω, ‖F (translate z ω) - F ω‖ₑ ^ p.toReal ∂Q)
        ≤ ENNReal.ofReal (ζ ε z) * η := by
      intro z
      by_cases hz : ζ ε z = 0
      · simp [hz]
      · have hdist : dist z 0 < δ := by
          rw [dist_zero_right]
          exact lt_of_le_of_lt (norm_le_euclideanNorm_vec z) (lt_trans (hζs ε hε0 z hz) hεδ)
        have hNz : ∫⁻ ω, ‖F (translate z ω) - F ω‖ₑ ^ p.toReal ∂Q ≤ η := hball hdist
        exact mul_le_mul_right hNz _
    calc ∫⁻ ω, ‖horizontalMollify (ζ ε) F ω - F ω‖ₑ ^ p.toReal ∂Q
        ≤ ∫⁻ z, ENNReal.ofReal (ζ ε z) * ∫⁻ ω, ‖F (translate z ω) - F ω‖ₑ ^ p.toReal ∂Q
            ∂(volume : Measure (Vec d)) :=
          lintegral_mollify_sub_le hQ (hζm ε hε0) (hζ0 ε hε0) (hζ1 ε hε0) hF hF1 hq
      _ ≤ ∫⁻ z, ENNReal.ofReal (ζ ε z) * η ∂(volume : Measure (Vec d)) :=
          lintegral_mono fun z => hpt z
      _ = (∫⁻ z, ENNReal.ofReal (ζ ε z) ∂(volume : Measure (Vec d))) * η :=
          lintegral_mul_const η (hζm ε hε0).ennreal_ofReal
      _ = η := by rw [hζl, one_mul]
  have hpow : Tendsto
      (fun ε => (∫⁻ ω, ‖horizontalMollify (ζ ε) F ω - F ω‖ₑ ^ p.toReal ∂Q) ^ (1 / p.toReal))
      (𝓝[>] 0) (𝓝 0) := hcont.comp hI
  refine Filter.Tendsto.congr' ?_ hpow
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
    (((measurable_horizontalMollify (ζ ε) (hζm ε hε) hF).sub hF).aestronglyMeasurable)).symm

/-! ### The unit-mass Euclidean mollifier, rescaled -/

/-- The unit-mass Euclidean mollifier of `Calculus/Mollifier.lean`, rescaled to radius `ε`. -/
noncomputable def unitMassScaledMollifier (d : ℕ) (ε : ℝ) (x : Vec d) : ℝ :=
  (ε ^ d)⁻¹ * mollifier d (ε⁻¹ • x)

private theorem euclideanNorm_smul_vec {d : ℕ} (c : ℝ) (x : Vec d) :
    euclideanNorm (c • x) = |c| * euclideanNorm x := by
  unfold euclideanNorm euclideanSq dot
  have hsum : ∑ i, (c • x) i * (c • x) i = c ^ 2 * ∑ i, x i * x i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

private theorem measurable_unitMassScaledMollifier (d : ℕ) (ε : ℝ) :
    Measurable (unitMassScaledMollifier d ε) := by
  have hs : Continuous (fun x : Vec d => ε⁻¹ • x) := by fun_prop
  exact measurable_const.mul ((contDiff_mollifier d).continuous.comp hs).measurable

private theorem unitMassScaledMollifier_nonneg {d : ℕ} {ε : ℝ} (hε : 0 < ε) (z : Vec d) :
    0 ≤ unitMassScaledMollifier d ε z :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le d)) (mollifier_nonneg d _)

private theorem integral_unitMassScaledMollifier {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∫ z, unitMassScaledMollifier d ε z = 1 := by
  unfold unitMassScaledMollifier
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (μ := volume) (mollifier d) hε.le,
    Module.finrank_fin_fun, integral_mollifier, smul_eq_mul, mul_one,
    inv_mul_cancel₀ (pow_ne_zero d hε.ne')]

private theorem unitMassScaledMollifier_lt_of_ne_zero {d : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Vec d}
    (hz : unitMassScaledMollifier d ε z ≠ 0) : euclideanNorm z < ε := by
  unfold unitMassScaledMollifier at hz
  have hm : mollifier d (ε⁻¹ • z) ≠ 0 := right_ne_zero_of_mul hz
  have hts : ε⁻¹ • z ∈ tsupport (mollifier d) :=
    subset_tsupport _ (Function.mem_support.mpr hm)
  have h1 : euclideanNorm (ε⁻¹ • z) < 1 := tsupport_mollifier_subset d hts
  rw [euclideanNorm_smul_vec, abs_of_pos (inv_pos.mpr hε)] at h1
  have h2 := (inv_mul_lt_iff₀ hε).mp h1
  rwa [mul_one] at h2

/-- **Convergence for the rescaled mollifier.** For `F` measurable and in `L^p(Q)`,
horizontal smoothing by the rescaled unit-mass mollifier converges in `L^p(Q)` as `ε → 0⁺`. -/
theorem tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {F : FieldPair d → ℝ} (hF : Measurable F) (hFp : MemLp F p Q) :
    Tendsto (fun ε => eLpNorm (fun ω => horizontalMollify (unitMassScaledMollifier d ε) F ω - F ω) p Q)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_eLpNorm_horizontalMollify_sub Q hQ p hp hF hFp (unitMassScaledMollifier d)
    (fun _ _ => measurable_unitMassScaledMollifier d _)
    (fun _ hε z => unitMassScaledMollifier_nonneg hε z)
    (fun _ hε => integral_unitMassScaledMollifier hε)
    (fun _ hε z hz => unitMassScaledMollifier_lt_of_ne_zero hε hz)

end EinsteinRelation.Calculus
