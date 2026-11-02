import EinsteinFull.Calculus.C22SuppliedLawDiscountedOccupation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Annealed convergence of discounted absolute occupation residuals admits an
almost surely convergent quenched subsequence for the same kernel. -/
theorem c22_discounted_occupation_quenched_subsequence
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (s : ℝ) (r : ℕ → FieldPair d → ℝ)
    (hi : ∀ n, Integrable (fun a : ℝ × (FieldPair d × Path d) =>
      Real.exp (-s * a.1) * |r n (translate (a.2.2 a.1.toNNReal) (reduce a.2.1))|)
      ((volume.restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K)))
    (hlim : Tendsto (fun n => ∫ a : ℝ × (FieldPair d × Path d),
      Real.exp (-s * a.1) * |r n (translate (a.2.2 a.1.toNNReal) (reduce a.2.1))|
      ∂((volume.restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K))) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Tendsto (fun n => ∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) *
        (∫ γ : Path d, |r (ns n) (translate (γ u.toNNReal) (reduce ω))| ∂K ω))
        atTop (𝓝 0) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  let μ := (volume : Measure ℝ).restrict (Set.Ioi 0)
  let F : ℕ → ℝ × (FieldPair d × Path d) → ℝ := fun n a =>
    Real.exp (-s * a.1) * |r n (translate (a.2.2 a.1.toNNReal) (reduce a.2.1))|
  let G : ℕ → (ℝ × FieldPair d) × Path d → ℝ := fun n p => F n (p.1.1, p.1.2, p.2)
  let H : ℕ → ℝ × FieldPair d → ℝ := fun n p => ∫ γ, G n (p, γ) ∂K p.2
  let R : ℕ → FieldPair d → ℝ := fun n ω => ∫ u, H n (u, ω) ∂μ
  have hpos : ∀ n p, 0 ≤ F n p := fun n p => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
  have hG : ∀ n, Integrable (G n) ((μ.prod Q.measure) ⊗ₘ Kernel.prodMkLeft ℝ K) := by
    intro n
    apply (integrable_map_equiv MeasurableEquiv.prodAssoc (F n)).mp
    rw [c22_prod_compProd_assoc]
    exact hi n
  have hH : ∀ n, Integrable (H n) (μ.prod Q.measure) := by
    intro n
    have h := (Measure.integrable_compProd_iff (hG n).aestronglyMeasurable).mp (hG n)
    have hn : ∀ p, ‖G n p‖ = G n p := fun p =>
      (Real.norm_eq_abs _).trans (abs_of_nonneg (hpos n _))
    simpa only [H, Kernel.prodMkLeft_apply, hn] using h.2
  have hHpos : ∀ n p, 0 ≤ H n p := fun n p => integral_nonneg (fun γ => hpos n _)
  have hR : ∀ n, Integrable (R n) Q.measure := by
    intro n
    have h := (hH n).integral_norm_prod_right
    have hn : ∀ p, ‖H n p‖ = H n p := fun p =>
      (Real.norm_eq_abs _).trans (abs_of_nonneg (hHpos n p))
    simpa only [R, hn] using h
  have hRpos : ∀ n ω, 0 ≤ R n ω := fun n ω => integral_nonneg (fun u => hHpos n _)
  have heq : ∀ n, (∫ ω, R n ω ∂Q.measure) = ∫ a, F n a ∂(μ.prod (Q.measure ⊗ₘ K)) := by
    intro n
    exact (c22_integral_prod_compProd_swap μ Q.measure K (F n) (hpos n) (hi n)).symm
  have heLp : Tendsto (fun n => eLpNorm (R n - 0) 1 Q.measure) atTop (𝓝 0) := by
    have heq' : ∀ n, eLpNorm (R n - 0) 1 Q.measure = ENNReal.ofReal (∫ a, F n a ∂(μ.prod (Q.measure ⊗ₘ K))) := by
      intro n
      simp only [sub_zero]
      rw [eLpNorm_one_eq_lintegral_enorm (hR n).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (hR n)]
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (hRpos n _)]
      rw [heq n]
    simp_rw [heq']
    simpa only [F, μ, Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hlim
  obtain ⟨ns, hns, ha⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) heLp).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [ha] with ω hω
  simpa only [R, H, G, F, Pi.zero_apply, integral_const_mul] using hω

