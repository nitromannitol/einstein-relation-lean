import EinsteinRelation.Calculus.HorizontalTranslationLp
import EinsteinRelation.Calculus.Mollifier
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual scalar representative of the horizontal `L²` mollifier

Source `paper/main.tex:545–566` (horizontal smoothing `S_δ f = ∫ κ_δ(x) f(T_x ω) dx`) and
`paper/main.tex:240–248` (the actual strongly continuous `L²` translations).

The scalar smoothing `ω ↦ ∫ κ(x) F(T_{εx} ω) dx` of a bounded measurable observable is itself
bounded and measurable, hence a genuine class in `L²(Q)`. Its class is compared with the Bochner
integral in `Lp ℝ 2 Q` of the actual translated classes by pairing with every `L²` class: the
Bochner integral commutes with the inner product, each translated class is evaluated through its
almost-everywhere representative, and genuine Fubini on `volume.prod Q` exchanges the two integrals.
Inner-product separation then gives equality of classes. No continuity or differentiability of `F`
in the environment is used, and `ε = 0` needs no special case.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

private theorem integrable_mollifier_representative (d : ℕ) : Integrable (mollifier d) volume :=
  (contDiff_mollifier d).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_mollifier d)

/-- Joint measurability of the literal translated observable `(x, ω) ↦ F (T_{εx} ω)`. -/
private theorem measurable_scaledOrbit {d : ℕ} {F : FieldPair d → ℝ} (hF : Measurable F)
    (ε : ℝ) : Measurable (fun p : Vec d × FieldPair d => F (translate (ε • p.1) p.2)) := by
  have hc : Continuous (fun p : Vec d × FieldPair d => translate (ε • p.1) p.2) :=
    Probability.continuous_translate.comp ((continuous_fst.const_smul ε).prodMk continuous_snd)
  exact hF.comp hc.measurable

/-- The scalar smoothing is measurable in the environment, by measurability of parametric
integrals of a jointly measurable integrand. -/
private theorem measurable_scalarSmoothing {d : ℕ} {F : FieldPair d → ℝ} (hF : Measurable F)
    (ε : ℝ) :
    Measurable (fun ω : FieldPair d => ∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)) := by
  have hc : Continuous (fun p : FieldPair d × Vec d => translate (ε • p.2) p.1) :=
    Probability.continuous_translate.comp ((continuous_snd.const_smul ε).prodMk continuous_fst)
  have hm : StronglyMeasurable (fun p : FieldPair d × Vec d =>
      mollifier d p.2 * F (translate (ε • p.2) p.1)) :=
    (((contDiff_mollifier d).continuous.measurable.comp measurable_snd).mul
      (hF.comp hc.measurable)).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

/-- The integrand of the scalar smoothing is integrable against the kernel for every `ω`. -/
private theorem integrable_scalarIntegrand {d : ℕ} {F : FieldPair d → ℝ} (hF : Measurable F)
    {M : ℝ} (hM : ∀ ω, |F ω| ≤ M) (ε : ℝ) (ω : FieldPair d) :
    Integrable (fun x : Vec d => mollifier d x * F (translate (ε • x) ω)) := by
  have hsec : Measurable (fun x : Vec d => (x, ω)) := measurable_id.prodMk measurable_const
  have hxm : Measurable (fun x : Vec d => F (translate (ε • x) ω)) :=
    (measurable_scaledOrbit hF ε).comp hsec
  refine Integrable.mono' ((integrable_mollifier_representative d).mul_const M) ?_ ?_
  · exact ((contDiff_mollifier d).continuous.measurable.mul hxm).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    show ‖mollifier d x * F (translate (ε • x) ω)‖ ≤ mollifier d x * M
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollifier_nonneg d x)]
    exact mul_le_mul_of_nonneg_left (hM _) (mollifier_nonneg d x)

/-- The scalar smoothing is bounded by the bound of the observable, since the kernel has unit
mass and is nonnegative. -/
private theorem abs_scalarSmoothing_le {d : ℕ} {F : FieldPair d → ℝ} (hF : Measurable F)
    {M : ℝ} (hM : ∀ ω, |F ω| ≤ M) (ε : ℝ) (ω : FieldPair d) :
    |∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)| ≤ M := by
  have hbd : ∀ x : Vec d, ‖mollifier d x * F (translate (ε • x) ω)‖ ≤ mollifier d x * M :=
    fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollifier_nonneg d x)]
      exact mul_le_mul_of_nonneg_left (hM _) (mollifier_nonneg d x)
  calc |∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)|
      = ‖∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x : Vec d, ‖mollifier d x * F (translate (ε • x) ω)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x : Vec d, mollifier d x * M :=
        integral_mono (integrable_scalarIntegrand hF hM ε ω).norm
          ((integrable_mollifier_representative d).mul_const M) hbd
    _ = (∫ x : Vec d, mollifier d x) * M := integral_mul_const _ _
    _ = M := by rw [integral_mollifier d, one_mul]

/-- The scalar smoothing lies in `L²(Q)` of a probability law, being measurable and bounded. -/
private theorem memLp_scalarSmoothing {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {F : FieldPair d → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ ω, |F ω| ≤ M) (ε : ℝ) :
    MemLp (fun ω : FieldPair d => ∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)) 2 Q :=
  MemLp.of_bound (measurable_scalarSmoothing hF ε).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_scalarSmoothing_le hF hM ε ω)

/-- Pairing with an `L²` class sees its a.e. representative, as a real integral. -/
private theorem inner_memLp_toLp {d : ℕ} {Q : Measure (FieldPair d)} (g : Lp ℝ 2 Q)
    {G : FieldPair d → ℝ} (hG : MemLp G 2 Q) :
    inner ℝ g (hG.toLp G) = ∫ ω, g ω * G ω ∂Q := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hG.coeFn_toLp] with ω hω
  rw [hω, RCLike.inner_apply, conj_trivial, mul_comm]

/-- Actual scalar representative of the horizontal `L²` mollifier, `paper/main.tex:545–566`.
The scalar orbit integral `ω ↦ ∫ κ(x) F(T_{εx} ω) dx` is an `L²` class, and it equals the
Bochner integral `∫ κ(x) • T_{εx} F` of the actual translated `L²` classes. -/
theorem exists_mollifier_representative_eq_translation_integral : ∀ {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {F : FieldPair d → ℝ}, Measurable F → (∃ M : ℝ, ∀ ω, |F ω| ≤ M) →
    ∀ hF : MemLp F 2 Q, ∀ ε : ℝ,
    ∃ hS : MemLp (fun ω => ∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)) 2 Q,
    hS.toLp (fun ω => ∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)) =
      ∫ x : Vec d, mollifier d x • translationLp Q hQ (ε • x) (hF.toLp F) := by
  intro d Q hPr hQ F hFm hb hF ε
  obtain ⟨M, hM⟩ := hb
  have hS : MemLp (fun ω : FieldPair d => ∫ x : Vec d, mollifier d x * F (translate (ε • x) ω))
      2 Q := memLp_scalarSmoothing hFm hM ε
  refine ⟨hS, ?_⟩
  have hcont : Continuous (fun x : Vec d => translationLp Q hQ (ε • x) (hF.toLp F)) :=
    (continuous_translationLp Q hQ).comp ((continuous_id.const_smul ε).prodMk continuous_const)
  have hint : Integrable (fun x : Vec d => mollifier d x • translationLp Q hQ (ε • x) (hF.toLp F))
      volume := by
    refine Integrable.mono' ((integrable_mollifier_representative d).mul_const ‖hF.toLp F‖) ?_ ?_
    · exact ((contDiff_mollifier d).continuous.smul hcont).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      refine le_of_eq ?_
      rw [norm_smul, norm_translationLp, Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg d x)]
  refine ext_inner_left ℝ fun g => ?_
  -- Pairing with one actual translated class, through its a.e. representative.
  have hT : ∀ x : Vec d, inner ℝ g (translationLp Q hQ (ε • x) (hF.toLp F)) =
      ∫ ω, g ω * F (translate (ε • x) ω) ∂Q := by
    intro x
    have hae := (measurePreserving_translate Q hQ (ε • x)).quasiMeasurePreserving.ae
      hF.coeFn_toLp
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_translationLp Q hQ (ε • x) (hF.toLp F), hae] with ω h1 h2
    simp only [h1, h2, RCLike.inner_apply, conj_trivial]
    exact mul_comm _ _
  -- The Bochner integral commutes with the continuous pairing.
  have hB : inner ℝ g (∫ x : Vec d, mollifier d x • translationLp Q hQ (ε • x) (hF.toLp F)) =
      ∫ x : Vec d, mollifier d x * (∫ ω, g ω * F (translate (ε • x) ω) ∂Q) := by
    rw [← integral_inner (𝕜 := ℝ) hint g]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show inner ℝ g (mollifier d x • translationLp Q hQ (ε • x) (hF.toLp F)) =
      mollifier d x * (∫ ω, g ω * F (translate (ε • x) ω) ∂Q)
    rw [real_inner_smul_right, hT x]
  -- Genuine Fubini on `volume.prod Q`, with an integrable dominating product.
  have hgI : Integrable (fun ω : FieldPair d => g ω) Q :=
    (Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hdom : Integrable (fun p : Vec d × FieldPair d => mollifier d p.1 * |g p.2| * M)
      ((volume : Measure (Vec d)).prod Q) :=
    ((integrable_mollifier_representative d).mul_prod hgI.abs).mul_const M
  have hgp : AEStronglyMeasurable (fun p : Vec d × FieldPair d => g p.2)
      ((volume : Measure (Vec d)).prod Q) :=
    (Lp.aestronglyMeasurable g).comp_snd
  have hFp : AEStronglyMeasurable (fun p : Vec d × FieldPair d => F (translate (ε • p.1) p.2))
      ((volume : Measure (Vec d)).prod Q) :=
    (measurable_scaledOrbit hFm ε).aestronglyMeasurable
  have hmp : AEStronglyMeasurable (fun p : Vec d × FieldPair d => mollifier d p.1)
      ((volume : Measure (Vec d)).prod Q) :=
    ((contDiff_mollifier d).continuous.measurable.comp measurable_fst).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun p : Vec d × FieldPair d =>
      mollifier d p.1 * (g p.2 * F (translate (ε • p.1) p.2)))
      ((volume : Measure (Vec d)).prod Q) :=
    hmp.mul (hgp.mul hFp)
  have hint2 : Integrable (fun p : Vec d × FieldPair d =>
      mollifier d p.1 * (g p.2 * F (translate (ε • p.1) p.2)))
      ((volume : Measure (Vec d)).prod Q) := by
    refine hdom.mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (mollifier_nonneg d p.1), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)) (mollifier_nonneg d p.1)
  have hFub : (∫ x : Vec d, mollifier d x * (∫ ω, g ω * F (translate (ε • x) ω) ∂Q)) =
      ∫ ω, g ω * (∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)) ∂Q := by
    calc (∫ x : Vec d, mollifier d x * (∫ ω, g ω * F (translate (ε • x) ω) ∂Q))
        = ∫ x : Vec d, ∫ ω, mollifier d x * (g ω * F (translate (ε • x) ω)) ∂Q :=
          integral_congr_ae (ae_of_all _ fun x => (integral_const_mul _ _).symm)
      _ = ∫ ω, (∫ x : Vec d, mollifier d x * (g ω * F (translate (ε • x) ω))) ∂Q :=
          integral_integral_swap (f := fun x ω => mollifier d x * (g ω * F (translate (ε • x) ω)))
            hint2
      _ = ∫ ω, g ω * (∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)) ∂Q := by
          refine integral_congr_ae (ae_of_all _ fun ω => ?_)
          show (∫ x : Vec d, mollifier d x * (g ω * F (translate (ε • x) ω))) =
            g ω * ∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)
          rw [← integral_const_mul]
          exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [inner_memLp_toLp g hS, hB]
  exact hFub.symm

end EinsteinRelation.Correctors
