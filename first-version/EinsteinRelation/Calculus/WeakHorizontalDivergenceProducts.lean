import EinsteinRelation.Calculus.WeakHorizontalLpProducts

/-! # Multiplying a weak horizontal divergence

Source: `paper/main.tex:1044–1069`, Steps 3 and 4 of Proposition 6.1.
The local flux corrector is multiplied by a derivative of the smoothed scalar
field. This file proves the corresponding distributional product rule directly
from the horizontal Sobolev approximation and the existing gradient-divergence
duality.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace EinsteinRelation

variable {d : ℕ}

/-- The divergence product rule for square-integrable fields and derivatives
(`paper/main.tex:1053–1069`). All products in the conclusion are integrable. -/
theorem HasWeakHorizontalDivergence.mul_of_memLp_two {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {V : FieldPair d → Vec d} {h g : FieldPair d → ℝ} {Dg : FieldPair d → Vec d}
    (hV : HasWeakHorizontalDivergence Q hQ V h)
    (hg : HasWeakHorizontalGradient Q hQ g Dg)
    (hgm : Measurable g) (hDgm : Measurable Dg)
    (hV2 : ∀ i, MemLp (fun ω => V ω i) 2 Q) (hh2 : MemLp h 2 Q)
    (hg2 : MemLp g 2 Q) (hDg2 : ∀ i, MemLp (fun ω => Dg ω i) 2 Q) :
    HasWeakHorizontalDivergence Q hQ (fun ω i => g ω * V ω i)
      (fun ω => g ω * h ω + ∑ i, V ω i * Dg ω i) := by
  have hprod : ∀ i, Integrable (fun ω => g ω * V ω i) Q := fun i =>
    hg2.integrable_mul (hV2 i)
  have hcross : ∀ i, Integrable (fun ω => V ω i * Dg ω i) Q := fun i =>
    (hV2 i).integrable_mul (hDg2 i)
  refine ⟨hprod, (hg2.integrable_mul hh2).add (integrable_finset_sum _ fun i _ => hcross i),
    fun F hF DF hDF => ?_⟩
  let Fm := (Lp.aestronglyMeasurable F).mk _
  let Dm : FieldPair d → Vec d := fun ω i => (Lp.aestronglyMeasurable (DF i)).mk _ ω
  have hFmm : Measurable Fm := (Lp.aestronglyMeasurable F).measurable_mk
  have hDmm : Measurable Dm := measurable_pi_lambda _ fun i =>
    (Lp.aestronglyMeasurable (DF i)).measurable_mk
  have hFae : (fun ω => F ω) =ᵐ[Q] Fm := (Lp.aestronglyMeasurable F).ae_eq_mk
  have hDae : (fun ω i => DF i ω) =ᵐ[Q] Dm := by
    filter_upwards [ae_all_iff.mpr fun i => (Lp.aestronglyMeasurable (DF i)).ae_eq_mk]
      with ω hω
    exact funext hω
  have hFm2 : MemLp Fm 2 Q := (Lp.memLp F).ae_eq hFae
  have hDm2 : ∀ i, MemLp (fun ω => Dm ω i) 2 Q := fun i =>
    (Lp.memLp (DF i)).ae_eq (hDae.mono fun ω hω => congrFun hω i)
  obtain ⟨B, hB⟩ := ae_bound_of_isHorizontallySmoothTest hF
  have hBm : ∀ᵐ ω ∂Q, |Fm ω| ≤ B := by
    filter_upwards [hB, hFae] with ω hω hω'
    rwa [← hω']
  have hDb : ∀ i, ∃ C : ℝ, ∀ᵐ ω ∂Q, |DF i ω| ≤ C := fun i =>
    ae_bound_of_hasHorizontalLpDerivative hF (hDF i)
  have hDmb : ∀ i, ∃ C : ℝ, ∀ᵐ ω ∂Q, |Dm ω i| ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := hDb i
    refine ⟨C, ?_⟩
    filter_upwards [hC, hDae] with ω hω hω'
    rwa [← congrFun hω' i]
  have hFgrad := (hasWeakHorizontalGradient_of_generators hQ F DF hDF).congr_ae hFae hDae
  have hpgrad := hg.mul_of_memLp_two hFgrad hgm hFmm hDgm hDmm hg2 hFm2 hDg2 hDm2
  have hp2 : MemLp (fun ω => g ω * Fm ω) 2 Q :=
    memLp_mul_of_ae_bound hg2 hFmm.aestronglyMeasurable hBm
  have hDp2 : ∀ i, MemLp (fun ω => Fm ω * Dg ω i + g ω * Dm ω i) 2 Q := by
    intro i
    obtain ⟨C, hC⟩ := hDmb i
    have h₁ := memLp_mul_of_ae_bound (hDg2 i) hFmm.aestronglyMeasurable hBm
    have h₂ := memLp_mul_of_ae_bound hg2 ((measurable_pi_apply i).comp hDmm).aestronglyMeasurable hC
    have h₁' : MemLp (fun ω => Fm ω * Dg ω i) 2 Q := by
      simpa only [mul_comm] using h₁
    exact h₁'.add h₂
  have hdual := Entropy.sum_integral_mul_eq_neg_of_div hQ (hgm.mul hFmm) hp2
    (measurable_pi_lambda _ fun i =>
      (hFmm.mul ((measurable_pi_apply i).comp hDgm)).add
        (hgm.mul ((measurable_pi_apply i).comp hDmm))) hDp2 hpgrad hV hV2 hh2
  have hleft : ∀ i, Integrable (fun ω => (g ω * V ω i) * DF i ω) Q := by
    intro i
    obtain ⟨C, hC⟩ := hDb i
    exact integrable_mul_of_ae_bound (hprod i) hC
  have hright : ∀ i, Integrable (fun ω => (V ω i * Dg ω i) * F ω) Q := fun i =>
    integrable_mul_of_ae_bound (hcross i) hB
  have hzero : Integrable (fun ω => (g ω * h ω) * F ω) Q :=
    integrable_mul_of_ae_bound (hg2.integrable_mul hh2) hB
  have hsplit : ∑ i, ∫ ω, V ω i * (Fm ω * Dg ω i + g ω * Dm ω i) ∂Q =
      (∫ ω, ∑ i, (g ω * V ω i) * DF i ω ∂Q) +
        ∫ ω, (∑ i, V ω i * Dg ω i) * F ω ∂Q := by
    have heq : ∀ i, (∫ ω, V ω i * (Fm ω * Dg ω i + g ω * Dm ω i) ∂Q) =
        (∫ ω, (g ω * V ω i) * DF i ω ∂Q) + ∫ ω, (V ω i * Dg ω i) * F ω ∂Q := by
      intro i
      calc
        _ = ∫ ω, ((g ω * V ω i) * DF i ω + (V ω i * Dg ω i) * F ω) ∂Q := by
          apply integral_congr_ae
          filter_upwards [hFae, hDae] with ω hω hω'
          rw [← hω, ← congrFun hω' i]
          ring
        _ = _ := integral_add (hleft i) (hright i)
    simp_rw [heq]
    rw [Finset.sum_add_distrib, ← integral_finset_sum _ fun i _ => hleft i,
      ← integral_finset_sum _ fun i _ => hright i]
    congr 1
    congr 1
    funext ω
    exact (Finset.sum_mul _ _ _).symm
  have hsplit' : (∫ ω, h ω * (g ω * Fm ω) ∂Q) = ∫ ω, (g ω * h ω) * F ω ∂Q := by
    apply integral_congr_ae
    filter_upwards [hFae] with ω hω
    rw [← hω]
    ring
  have hsource : (∫ ω, (g ω * h ω + ∑ i, V ω i * Dg ω i) * F ω ∂Q) =
      (∫ ω, (g ω * h ω) * F ω ∂Q) + ∫ ω, (∑ i, V ω i * Dg ω i) * F ω ∂Q := by
    simpa only [add_mul] using integral_add hzero
      (integrable_mul_of_ae_bound (integrable_finset_sum _ fun i _ => hcross i) hB)
  simp only [Function.comp_apply] at hdual
  rw [hsplit, hsplit'] at hdual
  change (∫ ω, ∑ i, (g ω * V ω i) * DF i ω ∂Q) =
    -(∫ ω, (g ω * h ω + ∑ i, V ω i * Dg ω i) * F ω ∂Q)
  rw [hsource]
  linarith only [hdual]

end EinsteinRelation
