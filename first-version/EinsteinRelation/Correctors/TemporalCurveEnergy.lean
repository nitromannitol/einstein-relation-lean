import EinsteinRelation.Correctors.FiniteTemporalL2Contraction
import EinsteinRelation.Correctors.CoefficientLpEnergy

open MeasureTheory
namespace EinsteinRelation.Correctors

private theorem integral_sq_eq_eLpNorm_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x^2 ∂μ) = (eLpNorm f 2 μ).toReal^2 := by
  rw [← Lp.norm_toLp f hf,← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx,RCLike.inner_apply,conj_trivial,pow_two]

/-- The integrated energy of an actual temporally regularized gradient is
bounded by the original cylinder energy. Source: `paper/main.tex:798–806`. -/
theorem temporal_gradient_curve_energy_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] {d : ℕ} {c e a b : ℝ} (hab : a ≤ b)
    {G : ℝ × X → Fin d → ℝ}
    (hG : ∀ i, MemLp (fun z => G z i) 2 ((volume.restrict (Set.Ioo c e)).prod ν))
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ s, 0 ≤ ρ s) (hρ1 : (∫ s, ρ s) = 1)
    (g : ℝ → Lp (EuclideanSpace ℝ (Fin d)) 2 ν)
    (hrep : ∀ t i, (fun x => g t x i) =ᵐ[ν]
      fun x => ∫ s in Set.Ioo c e, ρ (t-s) * G (s,x) i) :
    (∫ t in a..b, ‖g t‖^2) ≤
      ∫ z, (∑ i : Fin d, (G z i)^2) ∂((volume.restrict (Set.Ioo c e)).prod ν) := by
  let μ := (volume.restrict (Set.Ioo c e)).prod ν
  let H : Fin d → ℝ × X → ℝ := fun i z =>
    ∫ s in Set.Ioo c e, ρ (z.1-s) * G (s,z.2) i
  have hH i := finite_temporal_convolution_L2_contraction ν (hG i) hρ hρc hρ0 hρ1
  have hQ : Integrable (fun z : ℝ × X => ∑ i, (H i z)^2) (volume.prod ν) :=
    integrable_finset_sum Finset.univ fun i _ => (hH i).1.integrable_sq
  have hnorm t : ‖g t‖^2 = ∫ x, ∑ i, (H i (t,x))^2 ∂ν := by
    rw [← integral_euclideanSq_Lp ν (g t)]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (hrep t)] with x hx
    simp only [euclideanSq,dot,← pow_two]
    exact Finset.sum_congr rfl fun i _ => congrArg (fun y : ℝ => y^2) (hx i)
  have hsmall : (∫ t in a..b, ‖g t‖^2) ≤
      ∫ z, ∑ i, (H i z)^2 ∂(volume.prod ν) := by
    simp_rw [hnorm]
    rw [intervalIntegral.integral_of_le hab,integral_prod _ hQ]
    apply setIntegral_le_integral hQ.integral_prod_left
    exact Filter.Eventually.of_forall fun t => integral_nonneg fun x =>
      Finset.sum_nonneg fun i _ => sq_nonneg _
  apply hsmall.trans
  rw [integral_finset_sum Finset.univ (fun i _ => (hH i).1.integrable_sq),
    integral_finset_sum Finset.univ (fun i _ => (hG i).integrable_sq)]
  apply Finset.sum_le_sum
  intro i _
  rw [integral_sq_eq_eLpNorm_sq (hH i).1,integral_sq_eq_eLpNorm_sq (hG i)]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (hG i).2.ne (hH i).2) 2

end EinsteinRelation.Correctors
