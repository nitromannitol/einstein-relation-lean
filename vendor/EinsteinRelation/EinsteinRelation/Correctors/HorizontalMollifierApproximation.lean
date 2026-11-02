import EinsteinRelation.Calculus.HorizontalTranslationLp
import EinsteinRelation.Calculus.Mollifier

/-! # Actual L² approximate identity for the horizontal mollifier

Source `paper/main.tex:545–548` and `548–566` (the kernel `κ_δ` and the horizontal smoothing
`S_δ f = ∫ κ_δ(x) f∘T_x dx`, which is the integral below after the substitution `y = δ x`), and
`paper/main.tex:240–248` (the strong `L²` translation group).

The integrand is the genuine Bochner integral in `Lp ℝ 2 Q` of the scalar canonical kernel times
the actual translated classes `translationLp Q hQ (ε • x) f`. Convergence to `f` for arbitrary
`f ∈ L²` is proved by dominated convergence: the dominating function is `mollifier d x * ‖f‖`,
the pointwise limit comes from strong continuity of the translation group, and `∫ mollifier = 1`
gives the limit of the constant integrand. No regularity, boundedness, or density of `f` is used.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

private theorem integrable_mollifierKernel (d : ℕ) : Integrable (mollifier d) volume :=
  (contDiff_mollifier d).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_mollifier d)

theorem tendsto_horizontalMollifier_translation_integral {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (f : Lp ℝ 2 Q) :
    Filter.Tendsto (fun ε : ℝ => ∫ x : Vec d, mollifier d x • translationLp Q hQ (ε • x) f)
      (nhds 0) (nhds f) := by
  have hf_eq : (∫ x : Vec d, mollifier d x • f) = f := by
    rw [integral_smul_const (mollifier d) f, integral_mollifier d, one_smul]
  have hcont : ∀ ε : ℝ, Continuous (fun x : Vec d => translationLp Q hQ (ε • x) f) := fun ε =>
    (continuous_translationLp Q hQ).comp ((continuous_id.const_smul ε).prodMk continuous_const)
  have hb : ∀ (ε : ℝ) (x : Vec d),
      ‖mollifier d x • translationLp Q hQ (ε • x) f‖ ≤ mollifier d x * ‖f‖ := by
    intro ε x
    refine le_of_eq ?_
    rw [norm_smul, norm_translationLp, Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg d x)]
  have hpt : ∀ x : Vec d,
      Filter.Tendsto (fun ε : ℝ => mollifier d x • translationLp Q hQ (ε • x) f)
        (nhds 0) (nhds (mollifier d x • f)) := by
    intro x
    have hc : Continuous fun ε : ℝ => ε • x := by fun_prop
    have hs : Filter.Tendsto (fun ε : ℝ => ε • x) (nhds 0) (nhds 0) := by
      simpa only [zero_smul] using hc.tendsto 0
    exact ((tendsto_translationLp_zero Q hQ f).comp hs).const_smul (mollifier d x)
  have hmeas : Filter.Eventually (fun ε : ℝ => AEStronglyMeasurable
      (fun x : Vec d => mollifier d x • translationLp Q hQ (ε • x) f) volume) (nhds 0) :=
    Filter.Eventually.of_forall fun ε =>
      ((contDiff_mollifier d).continuous.smul (hcont ε)).aestronglyMeasurable
  have hbound : Filter.Eventually (fun ε : ℝ => ∀ᵐ x ∂(volume : Measure (Vec d)),
      ‖mollifier d x • translationLp Q hQ (ε • x) f‖ ≤ mollifier d x * ‖f‖) (nhds 0) :=
    Filter.Eventually.of_forall fun ε => ae_of_all _ (hb ε)
  have hint : Integrable (fun x : Vec d => mollifier d x * ‖f‖) volume :=
    (integrable_mollifierKernel d).mul_const ‖f‖
  have hlimit : ∀ᵐ x ∂(volume : Measure (Vec d)),
      Filter.Tendsto (fun ε : ℝ => mollifier d x • translationLp Q hQ (ε • x) f) (nhds 0)
        (nhds (mollifier d x • f)) :=
    ae_of_all _ hpt
  have key : Filter.Tendsto
      (fun ε : ℝ => ∫ x : Vec d, mollifier d x • translationLp Q hQ (ε • x) f)
      (nhds 0) (nhds (∫ x : Vec d, mollifier d x • f)) :=
    tendsto_integral_filter_of_dominated_convergence (fun x : Vec d => mollifier d x * ‖f‖)
      hmeas hbound hint hlimit
  rw [hf_eq] at key
  exact key

end EinsteinRelation.Correctors
