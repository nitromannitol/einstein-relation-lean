import EinsteinRelation.Calculus.WeakHorizontalFiniteSums
import Mathlib.MeasureTheory.Integral.Prod

/-! # Parameter integration of weak divergences

Source: `paper/main.tex:1021–1029`. Fubini passes the literal integrated
path flux to the full horizontal test domain.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation

private theorem integrable_parameter_pairing
    {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {ν : Measure S} [SFinite ν] {μ : Measure Ω} [SFinite μ]
    {X : S × Ω → ℝ} (hX : Integrable X (ν.prod μ))
    {F : Ω → ℝ} (hF : AEStronglyMeasurable F μ)
    {B : ℝ} (hB : ∀ᵐ ω ∂μ, |F ω| ≤ B) :
    Integrable (fun q : S × Ω => X q * F q.2) (ν.prod μ) := by
  apply hX.mul_bdd hF.comp_snd
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν)).ae hB] with q hq
  simpa only [Real.norm_eq_abs] using hq

private theorem integral_parameter_pairing
    {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {ν : Measure S} [SFinite ν] {μ : Measure Ω} [SFinite μ]
    {X : S × Ω → ℝ} (hX : Integrable X (ν.prod μ))
    {F : Ω → ℝ} (hF : AEStronglyMeasurable F μ)
    {B : ℝ} (hB : ∀ᵐ ω ∂μ, |F ω| ≤ B) :
    (∫ ω, (∫ z, X (z, ω) ∂ν) * F ω ∂μ) =
      ∫ z, (∫ ω, X (z, ω) * F ω ∂μ) ∂ν := by
  have hi := integrable_parameter_pairing hX hF hB
  simp_rw [← integral_mul_const]
  exact integral_integral_swap hi.swap

/-- Integrating jointly integrable fields preserves their full weak
horizontal divergence (`paper/main.tex:1021–1029`). -/
theorem hasWeakHorizontalDivergence_parameter_integral
    {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν]
    {V : S → FieldPair d → Vec d} {g : S → FieldPair d → ℝ}
    (hV : ∀ i, Integrable (fun q : S × FieldPair d => V q.1 q.2 i) (ν.prod Q))
    (hg : Integrable (fun q : S × FieldPair d => g q.1 q.2) (ν.prod Q))
    (hdiv : ∀ᵐ z ∂ν, HasWeakHorizontalDivergence Q hQ (V z) (g z)) :
    HasWeakHorizontalDivergence Q hQ
      (fun ω i => ∫ z, V z ω i ∂ν) (fun ω => ∫ z, g z ω ∂ν) := by
  refine ⟨fun i => (hV i).integral_prod_right, hg.integral_prod_right,
    fun F hF DF hDF => ?_⟩
  obtain ⟨B, hB⟩ := ae_bound_of_isHorizontallySmoothTest hF
  choose C hC using fun i => ae_bound_of_hasHorizontalLpDerivative hF (hDF i)
  have hi (i : Fin d) := integrable_parameter_pairing (hV i)
    (Lp.aestronglyMeasurable (DF i)) (hC i)
  have hi' (i : Fin d) : Integrable
      (fun ω => (∫ z, V z ω i ∂ν) * DF i ω) Q :=
    integrable_mul_of_ae_bound (hV i).integral_prod_right (hC i)
  calc
    _ = ∑ i, ∫ ω, (∫ z, V z ω i ∂ν) * DF i ω ∂Q :=
      integral_finset_sum _ fun i _ => hi' i
    _ = ∑ i, ∫ z, (∫ ω, V z ω i * DF i ω ∂Q) ∂ν := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_parameter_pairing (hV i) (Lp.aestronglyMeasurable (DF i)) (hC i)
    _ = ∫ z, (∑ i, ∫ ω, V z ω i * DF i ω ∂Q) ∂ν :=
      (integral_finset_sum _ fun i _ => (hi i).integral_prod_left).symm
    _ = ∫ z, -(∫ ω, g z ω * F ω ∂Q) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hdiv] with z hz
      rw [← integral_finset_sum _ (fun i _ => integrable_mul_of_ae_bound (hz.1 i) (hC i))]
      exact hz.2.2 F hF DF hDF
    _ = -(∫ ω, (∫ z, g z ω ∂ν) * F ω ∂Q) := by
      rw [integral_neg, integral_parameter_pairing hg (Lp.aestronglyMeasurable F) hB]

end EinsteinRelation
