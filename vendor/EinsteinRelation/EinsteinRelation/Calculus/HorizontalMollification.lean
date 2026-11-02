import EinsteinRelation.Calculus.HorizontalCore
import EinsteinRelation.Calculus.Mollifier
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Actual horizontal convolution on the physical environment space

Source `paper/main.tex:548–566`, S_delta f = integral kappa_delta(x) f(T_x omega) dx.
The kernel is an arbitrary given compact smooth function here; its dilation to
kappa_delta and full L²/H¹ approximation/commutator estimates are separate steps.
The first consumers prove actual integrability, measurable observations, C∞
orbits and amplitude bounds for bounded Borel observables, without continuity in
the environment. Reflection and translation signs are verified by an exact
convolution identity. Actual invariant-law Fubini gives mean preservation.
The concrete canonical unit-mass kernel exercises the same definitions.
-/

open MeasureTheory
open scoped Convolution
noncomputable section
namespace EinsteinRelation

/-- Literal horizontal convolution against actual spatial translations. -/
def horizontalMollify {d : ℕ} (ζ : Vec d → ℝ) (F : FieldPair d → ℝ)
    (ω : FieldPair d) : ℝ := ∫ x : Vec d, ζ x * F (translate x ω)

theorem measurable_orbit {d : ℕ} {F : FieldPair d → ℝ} (hF : Measurable F)
    (ω : FieldPair d) : Measurable (orbit F ω) :=
  hF.comp (Probability.continuous_translate.measurable.comp
    (measurable_id.prodMk measurable_const))

/-- The literal orbit of a bounded measurable observable is locally integrable. -/
theorem locallyIntegrable_orbit_of_bounded {d : ℕ} {F : FieldPair d → ℝ}
    (hF : Measurable F) (hb : ∃ M : ℝ, ∀ ω, |F ω| ≤ M) (ω : FieldPair d) :
    LocallyIntegrable (orbit F ω) := by
  obtain ⟨M, hM⟩ := hb
  exact (locallyIntegrable_const (μ := volume) M).mono
    (measurable_orbit hF ω).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs]
      exact (hM (translate x ω)).trans (le_abs_self M))

/-- Actual pointwise convolution integrability, without environmental continuity. -/
theorem integrable_horizontalMollify_integrand {d : ℕ} (ζ : Vec d → ℝ)
    (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) {F : FieldPair d → ℝ}
    (hF : Measurable F) (hb : ∃ M : ℝ, ∀ ω, |F ω| ≤ M) (ω : FieldPair d) :
    Integrable (fun x : Vec d => ζ x * F (translate x ω)) := by
  simpa only [smul_eq_mul, orbit] using
    (locallyIntegrable_orbit_of_bounded hF hb ω).integrable_smul_left_of_hasCompactSupport hζ hζc

theorem measurable_horizontalMollify {d : ℕ} (ζ : Vec d → ℝ) (hζ : Measurable ζ)
    {F : FieldPair d → ℝ} (hF : Measurable F) : Measurable (horizontalMollify ζ F) := by
  have ht : Measurable (fun p : FieldPair d × Vec d => translate p.2 p.1) :=
    Probability.continuous_translate.measurable.comp (measurable_snd.prodMk measurable_fst)
  have hm : StronglyMeasurable (fun p : FieldPair d × Vec d => ζ p.2 * F (translate p.2 p.1)) :=
    ((hζ.comp measurable_snd).mul (hF.comp ht)).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

/-- An exact convolution identity, including reflection and the translation sign. -/
theorem orbit_horizontalMollify_eq_convolution {d : ℕ} (ζ : Vec d → ℝ)
    (F : FieldPair d → ℝ) (ω : FieldPair d) (y : Vec d) :
    orbit (horizontalMollify ζ F) ω y =
      (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun x => orbit F ω (-x))) (-y) := by
  simp only [orbit, horizontalMollify, convolution_lsmul, smul_eq_mul, translate_add]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have heq : -(-y - x) = x + y := by abel
    change ζ x * F (translate (x + y) ω) = ζ x * F (translate (-(-y-x)) ω)
    rw [heq]

/-- Horizontal smoothing is C∞ on every actual orbit even for merely measurable F. -/
theorem contDiff_orbit_horizontalMollify {d : ℕ} (ζ : Vec d → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    {F : FieldPair d → ℝ} (hF : Measurable F) (hb : ∃ M : ℝ, ∀ ω, |F ω| ≤ M)
    (ω : FieldPair d) : ContDiff ℝ (⊤ : ℕ∞) (orbit (horizontalMollify ζ F) ω) := by
  obtain ⟨M, hM⟩ := hb
  have hH : LocallyIntegrable (fun x : Vec d => orbit F ω (-x)) :=
    (locallyIntegrable_const (μ := volume) M).mono
      ((measurable_orbit hF ω).comp measurable_neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simp only [Real.norm_eq_abs]
        exact (hM (translate (-x) ω)).trans (le_abs_self M))
  have hc := hζc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hζ hH
  have heq : orbit (horizontalMollify ζ F) ω = fun y : Vec d =>
      (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun x => orbit F ω (-x))) (-y) :=
    funext (orbit_horizontalMollify_eq_convolution ζ F ω)
  rw [heq]
  exact hc.comp contDiff_id.neg

/-- The actual amplitude is controlled by the fixed kernel L1 mass. -/
theorem abs_horizontalMollify_le {d : ℕ} (ζ : Vec d → ℝ)
    (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) {F : FieldPair d → ℝ}
    (hF : Measurable F) (M : ℝ) (hb : ∀ ω, |F ω| ≤ M) (ω : FieldPair d) :
    |horizontalMollify ζ F ω| ≤ (∫ x : Vec d, |ζ x|) * M := by
  have hi := integrable_horizontalMollify_integrand ζ hζ hζc hF ⟨M, hb⟩ ω
  have hζi : Integrable ζ (volume : Measure (Vec d)) := hζ.integrable_of_hasCompactSupport hζc
  calc
    |horizontalMollify ζ F ω| = ‖∫ x : Vec d, ζ x * F (translate x ω)‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∫ x : Vec d, ‖ζ x * F (translate x ω)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : Vec d, |ζ x| * M := integral_mono hi.norm (hζi.abs.mul_const M) (fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _))
    _ = (∫ x : Vec d, |ζ x|) * M := integral_mul_const _ _

/-- Invariant means pass through the literal smoothing integral by genuine Fubini. -/
theorem integral_horizontalMollify {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (ζ : Vec d → ℝ)
    (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) {F : FieldPair d → ℝ}
    (hF : Measurable F) (hb : ∃ M : ℝ, ∀ ω, |F ω| ≤ M) :
    (∫ ω, horizontalMollify ζ F ω ∂Q) = (∫ x : Vec d, ζ x) * ∫ ω, F ω ∂Q := by
  obtain ⟨M, hM⟩ := hb
  have ht : Measurable (fun p : FieldPair d × Vec d => translate p.2 p.1) :=
    Probability.continuous_translate.measurable.comp (measurable_snd.prodMk measurable_fst)
  have hm : Measurable (fun p : FieldPair d × Vec d => ζ p.2 * F (translate p.2 p.1)) :=
    (hζ.measurable.comp measurable_snd).mul (hF.comp ht)
  have hζi : Integrable ζ (volume : Measure (Vec d)) := hζ.integrable_of_hasCompactSupport hζc
  have hdom : Integrable (fun p : FieldPair d × Vec d => |ζ p.2| * M) (Q.prod volume) :=
    (hζi.abs.mul_const M).comp_snd Q
  have hint : Integrable (fun p : FieldPair d × Vec d => ζ p.2 * F (translate p.2 p.1))
      (Q.prod volume) := hdom.mono' hm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _))
  change (∫ ω, (∫ x : Vec d, ζ x * F (translate x ω)) ∂Q) = _
  rw [integral_integral_swap hint]
  simp_rw [integral_const_mul, Probability.integral_translate Q hQ _ F hF]
  exact integral_mul_const _ _

/-- The canonical unit-mass kernel preserves the actual bound of every observable. -/
theorem abs_horizontalMollify_mollifier_le {d : ℕ} {F : FieldPair d → ℝ}
    (hF : Measurable F) (M : ℝ) (hb : ∀ ω, |F ω| ≤ M) (ω : FieldPair d) :
    |horizontalMollify (mollifier d) F ω| ≤ M := by
  have h := abs_horizontalMollify_le (mollifier d) (contDiff_mollifier d).continuous
    (hasCompactSupport_mollifier d) hF M hb ω
  have hm : (∫ x : Vec d, |mollifier d x|) = 1 := by
    simp only [abs_of_nonneg (mollifier_nonneg d _)]
    exact integral_mollifier d
  simpa only [hm, one_mul] using h

/-- The concrete canonical smoothing preserves the law's mean. -/
theorem integral_horizontalMollify_mollifier {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {F : FieldPair d → ℝ}
    (hF : Measurable F) (hb : ∃ M : ℝ, ∀ ω, |F ω| ≤ M) :
    (∫ ω, horizontalMollify (mollifier d) F ω ∂Q) = ∫ ω, F ω ∂Q := by
  simpa only [integral_mollifier, one_mul] using integral_horizontalMollify Q hQ
    (mollifier d) (contDiff_mollifier d).continuous (hasCompactSupport_mollifier d) hF hb

end EinsteinRelation
