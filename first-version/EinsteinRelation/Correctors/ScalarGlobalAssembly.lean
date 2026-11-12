import EinsteinRelation.Correctors.ScalarCorrectedGenerator

/-! # Assembling the weak scalar decomposition over all bands

Source: `paper/main.tex:1044–1069`. The corrected band generator equations
sum on the full horizontal test domain. A small-scale divergence moves into
the error flux, and the band drift divergences sum with their remainders.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation

variable {d : ℕ} {Q : Measure (FieldPair d)} {hQ : IsStationary Q}

/-- Finite sums of generator equations remain generator equations
(`paper/main.tex:1044–1059`). -/
theorem SatisfiesReducedGeneratorEquation.finset_sum [IsProbabilityMeasure Q]
    {ι : Type*} (s : Finset ι) {lam : ℝ} {i₁ : Fin d}
    (hA : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ i j : Fin d, |ω.1 0 i j| ≤ C)
    {u b : ι → FieldPair d → ℝ} {Du B : ι → FieldPair d → Vec d}
    (h : ∀ k ∈ s, SatisfiesReducedGeneratorEquation Q hQ lam (u k) (Du k) (b k) (B k) i₁) :
    SatisfiesReducedGeneratorEquation Q hQ lam
      (fun ω => ∑ k ∈ s, u k ω) (fun ω => ∑ k ∈ s, Du k ω)
      (fun ω => ∑ k ∈ s, b k ω) (fun ω => ∑ k ∈ s, B k ω) i₁ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using SatisfiesReducedGeneratorEquation.zero
  | @insert k s hk ih =>
    simpa only [Finset.sum_insert hk] using
      (h k (Finset.mem_insert_self k s)).add hA
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Moving a weak divergence between the source and the flux preserves
the generator equation (`paper/main.tex:1056–1059`). -/
theorem SatisfiesReducedGeneratorEquation.add_source_divergence
    {lam : ℝ} {i₁ : Fin d} {u b g : FieldPair d → ℝ}
    {Du B V : FieldPair d → Vec d}
    (heq : SatisfiesReducedGeneratorEquation Q hQ lam u Du b B i₁)
    (hV : HasWeakHorizontalDivergence Q hQ V g) :
    SatisfiesReducedGeneratorEquation Q hQ lam u Du (fun ω => b ω + g ω)
      (fun ω => B ω - V ω) i₁ := by
  refine ⟨heq.1, heq.2.1.add hV.2.1, fun i => (heq.2.2.1 i).sub (hV.1 i),
    fun F hF DF hDF => ?_⟩
  obtain ⟨C, hC⟩ := ae_bound_of_isHorizontallySmoothTest hF
  have hb := integrable_mul_of_ae_bound heq.2.1 hC
  have hg := integrable_mul_of_ae_bound hV.2.1 hC
  have hB := integrable_sum_mul_derivative heq.2.2.1 hF hDF
  have hVi := integrable_sum_mul_derivative hV.1 hF hDF
  have hsource : (∫ ω, (b ω + g ω) * F ω ∂Q) =
      (∫ ω, b ω * F ω ∂Q) + ∫ ω, g ω * F ω ∂Q := by
    simpa only [add_mul] using integral_add hb hg
  have hflux : (∫ ω, ∑ i, (B ω - V ω) i * DF i ω ∂Q) =
      (∫ ω, ∑ i, B ω i * DF i ω ∂Q) - ∫ ω, ∑ i, V ω i * DF i ω ∂Q := by
    simpa only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] using integral_sub hB hVi
  rw [hsource, hflux, hV.2.2 F hF DF hDF]
  linarith only [heq.2.2.2 F hF DF hDF]

namespace Correctors

/-- The global source and error flux after summing the corrected bands
(`paper/main.tex:1044–1059`). The small-scale field `E₀` satisfies its
explicit residual divergence identity. -/
theorem satisfiesReducedGeneratorEquation_globalBands [IsProbabilityMeasure Q]
    {ι : Type*} (s : Finset ι) (i₁ : Fin d)
    (hA : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ i j : Fin d, |ω.1 0 i j| ≤ C)
    {u b : ι → FieldPair d → ℝ} {Du B : ι → FieldPair d → Vec d}
    {f e : FieldPair d → ℝ} {E₀ : FieldPair d → Vec d}
    (hband : ∀ k ∈ s, SatisfiesReducedGeneratorEquation Q hQ 0 (u k) (Du k) (b k) (B k) i₁)
    (hsmall : HasWeakHorizontalDivergence Q hQ E₀
      (fun ω => f ω - e ω - ∑ k ∈ s, b k ω)) :
    SatisfiesReducedGeneratorEquation Q hQ 0
      (fun ω => ∑ k ∈ s, u k ω) (fun ω => ∑ k ∈ s, Du k ω)
      (fun ω => f ω - e ω) (fun ω => -(E₀ ω - ∑ k ∈ s, B k ω)) i₁ := by
  have h := (SatisfiesReducedGeneratorEquation.finset_sum s hA hband).add_source_divergence hsmall
  convert h using 1
  · funext ω
    ring
  · funext ω
    abel

/-- The drift equation sums over bands, including its scalar remainder
(`paper/main.tex:1061–1069`). -/
theorem hasWeakHorizontalDivergence_globalDrift {ι : Type*} (s : Finset ι) (i₁ : Fin d)
    {Du P : ι → FieldPair d → Vec d} {h : ι → FieldPair d → ℝ}
    (hband : ∀ k ∈ s, HasWeakHorizontalDivergence Q hQ (P k)
      (fun ω => dot ((ω.1 0).mulVec (unitVector i₁)) (Du k ω) - h k ω)) :
    HasWeakHorizontalDivergence Q hQ (fun ω => ∑ k ∈ s, P k ω)
      (fun ω => dot ((ω.1 0).mulVec (unitVector i₁)) (∑ k ∈ s, Du k ω) - ∑ k ∈ s, h k ω) := by
  have hsum := HasWeakHorizontalDivergence.finset_sum s hband
  refine Entropy.HasWeakHorizontalDivergence.congr_div hsum (ae_of_all _ fun ω => ?_)
  simp only [Finset.sum_sub_distrib, dot, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

end Correctors
end EinsteinRelation
