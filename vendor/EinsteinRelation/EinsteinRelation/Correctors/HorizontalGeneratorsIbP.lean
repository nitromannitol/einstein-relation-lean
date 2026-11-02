import EinsteinRelation.Calculus.HorizontalSobolev
import EinsteinRelation.Calculus.HorizontalIntegration
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.L2Space

/-! # Integration by parts between two horizontal L² generators

Source `eq.horizontal-ibp`, `paper/main.tex:240–248`: `E[f D_j g] = -E[g D_j f]` for `f, g` in the
horizontal H¹ domain. Here `f'` and `g'` are the strong L² generators of `f` and `g` in coordinate
`i`, that is, the two-sided limits of the translation difference quotients in `HasHorizontalLpDerivative`.
Translation invariance of the L² action (a linear isometry) moves the quotient of `f` onto the negative
shift of `g`. Passing to the limit along `𝓝[≠] 0` on both sides identifies `⟪f', g⟫ = -⟪f, g'⟫`.
Only the two strong generator limits are used; no smooth-test, core-density or closure premise appears.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors

/-- The L² pairing of two classes is the Bochner integral of their pointwise product. -/
private theorem ibp_inner_eq_integral_mul {d : ℕ} (Q : Measure (FieldPair d))
    (u v : Lp ℝ 2 Q) : inner ℝ u v = ∫ ω, u ω * v ω ∂Q := by
  rw [L2.inner_def]
  apply integral_congr_ae
  refine ae_of_all _ fun ω => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The pointwise product of two L² classes is integrable. -/
private theorem ibp_integrable_mul {d : ℕ} (Q : Measure (FieldPair d)) (u v : Lp ℝ 2 Q) :
    Integrable (fun ω => u ω * v ω) Q := by
  refine Integrable.congr (L2.integrable_inner (𝕜 := ℝ) u v) (ae_of_all _ fun ω => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- Translation is a linear isometry of L², so moving it across the pairing replaces `x` by `-x`. -/
private theorem ibp_inner_translationLp_eq {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) (u h : Lp ℝ 2 Q) :
    inner ℝ (translationLp Q hQ x u) h = inner ℝ u (translationLp Q hQ (-x) h) := by
  have hcancel : translationLp Q hQ x (translationLp Q hQ (-x) h) = h := by
    rw [← translationLp_add, add_neg_cancel, translationLp_zero]
  have h1 := (translationLp Q hQ x).inner_map_map u (translationLp Q hQ (-x) h)
  rw [hcancel] at h1
  exact h1

/-- The pairing of the strong generator limit `f'` of `f` with `v` equals minus the pairing of `f`
with the strong limit `w` of the difference quotient of `v`. Both quotients are taken along
`𝓝[≠] 0`, and the negative-shift quotient of `v` is the reparametrisation `t ↦ -t` of that quotient. -/
private theorem ibp_generator_inner_eq_neg {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (i : Fin d) (f f' v w : Lp ℝ 2 Q)
    (hf : HasHorizontalLpDerivative Q hQ i f f')
    (hv : HasHorizontalLpDerivative Q hQ i v w) :
    inner ℝ f' v = -inner ℝ f w := by
  unfold HasHorizontalLpDerivative at hf hv
  -- the quotient of `f` paired with `v` equals the pairing of `f` with the negative-shift quotient
  have hadj : ∀ t : ℝ, inner ℝ (t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f)) v =
      inner ℝ f (t⁻¹ • (translationLp Q hQ (-(t • unitVector i)) v - v)) := by
    intro t
    rw [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right,
      ibp_inner_translationLp_eq Q hQ (t • unitVector i) f v]
  -- the negative-shift quotient of `v` converges to `-w`, through `t ↦ -t` on the punctured filter
  have hn : Tendsto (fun t : ℝ => -t) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero] using (continuous_neg.tendsto (0 : ℝ))
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hn.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun t ht => by simpa using ht⟩
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • (translationLp Q hQ (-(t • unitVector i)) v - v))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-w)) := by
    have h2 : Tendsto (fun t : ℝ => -((-t)⁻¹ • (translationLp Q hQ ((-t) • unitVector i) v - v)))
        (𝓝[≠] (0 : ℝ)) (𝓝 (-w)) := (hv.comp hneg).neg
    refine Tendsto.congr (fun t => ?_) h2
    simp only [neg_smul, inv_neg, neg_neg]
  -- the two limits of the same pairing along `𝓝[≠] 0`
  have hF : Tendsto (fun t : ℝ => inner ℝ (t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f)) v)
      (𝓝[≠] (0 : ℝ)) (𝓝 (inner ℝ f' v)) :=
    hf.inner (tendsto_const_nhds : Tendsto (fun _ : ℝ => v) (𝓝[≠] (0 : ℝ)) (𝓝 v))
  have hc : Tendsto
      (fun t : ℝ => inner ℝ f (t⁻¹ • (translationLp Q hQ (-(t • unitVector i)) v - v)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (inner ℝ f (-w))) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => f) (𝓝[≠] (0 : ℝ)) (𝓝 f)).inner hlim
  rw [inner_neg_right] at hc
  have hG : Tendsto (fun t : ℝ => inner ℝ (t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f)) v)
      (𝓝[≠] (0 : ℝ)) (𝓝 (-inner ℝ f w)) :=
    Tendsto.congr (fun t => (hadj t).symm) hc
  exact tendsto_nhds_unique hF hG

/-- Source `eq.horizontal-ibp`, `paper/main.tex:240–248`: for actual L² generator pairs `(f, f')` and
`(g, g')` in coordinate `i`, the products `f' g` and `f g'` are integrable and
`E[f' g] = -E[f g']`. -/
theorem horizontalGenerators_integration_by_parts {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (i : Fin d) (f f' g g' : Lp ℝ 2 Q)
    (hf : HasHorizontalLpDerivative Q hQ i f f') (hg : HasHorizontalLpDerivative Q hQ i g g') :
    Integrable (fun ω => f' ω*g ω) Q ∧ Integrable (fun ω => f ω*g' ω) Q ∧
    (∫ ω, f' ω*g ω ∂Q) = -(∫ ω, f ω*g' ω ∂Q) := by
  refine ⟨ibp_integrable_mul Q f' g, ibp_integrable_mul Q f g', ?_⟩
  rw [← ibp_inner_eq_integral_mul Q f' g, ← ibp_inner_eq_integral_mul Q f g']
  exact ibp_generator_inner_eq_neg Q hQ i f f' g g' hf hg

end EinsteinRelation.Correctors
