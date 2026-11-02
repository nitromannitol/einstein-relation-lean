import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.L2Space
import EinsteinFull.Calculus.ComplexTranslationSupport

/-!
# Complex stationary horizontal integration by parts

The actual strong L2 horizontal derivatives commute with conjugation and are
skew symmetric. The resulting bilinear integration identity retains the actual
complex representatives and proves integrability of both products.

The unitary-group argument adapts the real argument in
`EinsteinRelation/Correctors/HorizontalGeneratorsIbP.lean` at blueprint revision
`7748a8e9000034825873768d309be8915ae53b07`. No probability normalization,
coefficient regularity or analytic estimate is required.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull

open EinsteinRelation

/-- Stationary L2 translation commutes with complex conjugation. -/
theorem complexTranslation_star {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) (f : Lp ℂ 2 Q) :
    complexTranslation Q hQ x (star f) = star (complexTranslation Q hQ x f) := by
  apply Lp.ext
  have hm := measurePreserving_translate Q hQ x
  have hc := hm.quasiMeasurePreserving.ae (Lp.coeFn_star f)
  filter_upwards [coeFn_complexTranslation Q hQ x (star f),
    Lp.coeFn_star (complexTranslation Q hQ x f), coeFn_complexTranslation Q hQ x f,
    hc] with ω ha hb hd he
  change (star f) (translate x ω) = star (f (translate x ω)) at he
  change (star (complexTranslation Q hQ x f)) ω =
    star ((complexTranslation Q hQ x f) ω) at hb
  rw [ha, hb, hd, he]

/-- Conjugation preserves the full strong horizontal derivative domain. -/
theorem HasComplexHorizontalDerivative.star {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {i : Fin d} {f g : Lp ℂ 2 Q}
    (hf : HasComplexHorizontalDerivative Q hQ i f g) :
    HasComplexHorizontalDerivative Q hQ i (star f) (star g) := by
  unfold HasComplexHorizontalDerivative at *
  let C : Lp ℂ 2 Q →L[ℝ] Lp ℂ 2 Q :=
    Complex.conjCLE.toContinuousLinearMap.compLpL 2 Q
  have hC (u : Lp ℂ 2 Q) : C u = Star.star u := by
    apply Lp.ext
    filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL u,
      Lp.coeFn_star u] with ω ha hb
    change (Star.star u) ω = Star.star (u ω) at hb
    refine ha.trans (Eq.trans ?_ hb.symm)
    first
      | rfl
      | simp [Complex.conjCLE_apply]
  have key (t : ℝ) : C ((t : ℂ)⁻¹ • (complexTranslation Q hQ (t • unitVector i) f - f)) =
      (t : ℂ)⁻¹ • (complexTranslation Q hQ (t • unitVector i) (Star.star f) - Star.star f) := by
    have e : ((t : ℂ)⁻¹) = ((t⁻¹ : ℝ) : ℂ) := (Complex.ofReal_inv t).symm
    have h1 : C (((t⁻¹ : ℝ) : ℂ) • (complexTranslation Q hQ (t • unitVector i) f - f)) =
        ((t⁻¹ : ℝ) : ℂ) • C (complexTranslation Q hQ (t • unitVector i) f - f) :=
      C.map_smul t⁻¹ _
    rw [e, h1, map_sub, hC, hC, complexTranslation_star]
  have h3 := (C.continuous.tendsto g).comp hf
  rw [hC g] at h3
  exact Tendsto.congr (fun t => key t) h3

private theorem inner_complexTranslation_eq {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) (u v : Lp ℂ 2 Q) :
    inner ℂ (complexTranslation Q hQ x u) v =
      inner ℂ u (complexTranslation Q hQ (-x) v) := by
  have hc : complexTranslation Q hQ x (complexTranslation Q hQ (-x) v) = v := by
    rw [← complexTranslation_add, add_neg_cancel, complexTranslation_zero]
  have h := (complexTranslation Q hQ x).inner_map_map u (complexTranslation Q hQ (-x) v)
  rw [hc] at h
  exact h

/-- Strong horizontal derivatives are skew symmetric for the Hermitian L2 pairing. -/
theorem HasComplexHorizontalDerivative.inner_eq_neg {d : ℕ}
    {Q : Measure (FieldPair d)} {hQ : IsStationary Q} {i : Fin d}
    {f f' g g' : Lp ℂ 2 Q}
    (hf : HasComplexHorizontalDerivative Q hQ i f f')
    (hg : HasComplexHorizontalDerivative Q hQ i g g') :
    inner ℂ f' g = -inner ℂ f g' := by
  unfold HasComplexHorizontalDerivative at hf hg
  have hadj : ∀ t : ℝ,
      inner ℂ ((t : ℂ)⁻¹ • (complexTranslation Q hQ (t • unitVector i) f - f)) g =
      inner ℂ f ((t : ℂ)⁻¹ • (complexTranslation Q hQ (-(t • unitVector i)) g - g)) := by
    intro t
    rw [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      inner_complexTranslation_eq]
    simp only [map_inv₀, Complex.conj_ofReal]
  have hn : Tendsto (fun t : ℝ => -t) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero] using (continuous_neg.tendsto (0 : ℝ))
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hn.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun t ht => by simpa using ht⟩
  have hlim : Tendsto
      (fun t : ℝ => (t : ℂ)⁻¹ • (complexTranslation Q hQ (-(t • unitVector i)) g - g))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-g')) := by
    have h2 := (hg.comp hneg).neg
    refine Tendsto.congr (fun t => ?_) h2
    simp only [Function.comp_apply, Complex.ofReal_neg, neg_smul, inv_neg, neg_neg]
  have hF := hf.inner (𝕜 := ℂ) (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => g) (𝓝[≠] (0 : ℝ)) (𝓝 g))
  have hG := (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => f) (𝓝[≠] (0 : ℝ)) (𝓝 f)).inner (𝕜 := ℂ) hlim
  rw [inner_neg_right] at hG
  exact tendsto_nhds_unique hF (Tendsto.congr (fun t => (hadj t).symm) hG)

private theorem inner_star_eq_integral_mul {d : ℕ} (Q : Measure (FieldPair d))
    (f g : Lp ℂ 2 Q) : inner ℂ (star f) g = ∫ ω, f ω * g ω ∂Q := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with ω hω
  change (star f) ω = star (f ω) at hω
  simp only [hω, RCLike.inner_apply, Complex.star_def, starRingEnd_self_apply]
  ring

/-- Bilinear horizontal integration by parts on the full complex strong L2 domain. -/
theorem complexHorizontalDerivatives_integration_by_parts {d : ℕ}
    {Q : Measure (FieldPair d)} {hQ : IsStationary Q} {i : Fin d}
    {f f' g g' : Lp ℂ 2 Q}
    (hf : HasComplexHorizontalDerivative Q hQ i f f')
    (hg : HasComplexHorizontalDerivative Q hQ i g g') :
    Integrable (fun ω => f' ω * g ω) Q ∧
      Integrable (fun ω => f ω * g' ω) Q ∧
      (∫ ω, f' ω * g ω ∂Q) = -(∫ ω, f ω * g' ω ∂Q) := by
  refine ⟨(Lp.memLp f').integrable_mul (Lp.memLp g),
    (Lp.memLp f).integrable_mul (Lp.memLp g'), ?_⟩
  simpa only [inner_star_eq_integral_mul] using hf.star.inner_eq_neg hg

end EinsteinFull
