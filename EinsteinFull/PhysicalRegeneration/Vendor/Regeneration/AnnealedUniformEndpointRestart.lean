import EinsteinRelation.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets

/-!
# Physical-kernel version of
`EinsteinRelation.Regeneration.AnnealedUniformEndpointRestart`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration
/-- The physical-kernel version of
`EinsteinRelation.Regeneration.integral_annealed_future_eq_uniformEndpointAverage`. -/
theorem integral_annealed_future_eq_uniformEndpointAverage_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (hRestart : HasDeterministicRestart Q.measure Δ K)
    (hUniform : HasUniformSuccessfulEndpoint Q.measure Δ δ R i K)
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H)
    (hbH : BoundedRealTest H)
    (Ψ : (Vec d × FieldPair d) × CoupledSample d → ℝ)
    (hΨ : Measurable Ψ) (hbΨ : BoundedRealTest Ψ)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B)
    (hBeq : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
      B xω = ∫ w, Ψ (xω, w) ∂K xω) :
    (∫ q, H q.2 * (if q.2.2 m = true then (1 : ℝ) else 0) *
      Ψ ((q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ), q.1),
        sampleTimeShift Δ q.2 (((m + 1 : ℕ) : ℝ≥0) * Δ))
      ∂annealedCoupledLaw Q.measure K) =
      ∫ ω, δ * ∫ z, H z * endpointAverage i R (z.1 ((m : ℝ≥0) * Δ))
        (fun y => B (y, ω)) ∂K (0, ω) ∂Q.measure := by
  classical
  let t : ℝ≥0 := ((m + 1 : ℕ) : ℝ≥0) * Δ
  have ht : 0 < t := mul_pos (by positivity) hΔ
  have hprob := ae_quenched_of_annealed Q.measure K hK
    (ae_at_endpoint_of_product_ae_phys hd Q lam h0 h1 P K hK hpath hP t ht _ hK.2)
  have hversion := ae_quenched_of_annealed Q.measure K hK
    (ae_at_endpoint_of_product_ae_phys hd Q lam h0 h1 P K hK hpath hP t ht _ hBeq)
  let F : FieldPair d × CoupledSample d → ℝ := fun q =>
    H q.2 * (if q.2.2 m = true then 1 else 0) *
      Ψ ((q.2.1 t, q.1), sampleTimeShift Δ q.2 t)
  have hHfull := hH.mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hF : Measurable F := by
    exact ((hHfull.comp measurable_snd).mul
      (Measurable.ite (((measurable_pi_apply m).comp measurable_snd.snd)
        (measurableSet_singleton true)) measurable_const measurable_const)).mul
      (hΨ.comp (((((continuous_eval_const t).measurable.comp measurable_snd.fst)).prodMk
        measurable_fst).prodMk ((measurable_sampleTimeShift Δ).comp
          (measurable_const.prodMk measurable_snd))))
  have hbF : BoundedRealTest F := by
    obtain ⟨CH, hCH⟩ := hbH
    obtain ⟨CP, hCP⟩ := hbΨ
    refine ⟨max CH 0 * max CP 0, fun q => ?_⟩
    dsimp [F]
    by_cases hq : q.2.2 m = true
    · simp only [hq, ↓reduceIte, mul_one, abs_mul]
      exact mul_le_mul ((hCH _).trans (le_max_left _ _))
        ((hCP _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    · simpa [hq] using
        (mul_nonneg (le_max_right CH (0 : ℝ)) (le_max_right CP (0 : ℝ)))
  change (∫ q, F q ∂annealedCoupledLaw Q.measure K) = _
  rw [integral_annealedCoupledLaw Q.measure K hK F hF hbF]
  apply integral_congr_ae
  filter_upwards [hK.1, hRestart.1, hUniform.1, hprob, hversion] with ω hω hr hu hp hv
  have := hω
  exact integral_future_eq_uniformEndpointAverage Δ δ R i K (0, ω) hr hu m hp H hH hbH
    (fun q => Ψ ((q.1, ω), q.2))
    (hΨ.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd))
    (by obtain ⟨C, hC⟩ := hbΨ; exact ⟨C, fun q => hC _⟩)
    (fun y => B (y, ω)) (hB.comp measurable_prodMk_right)
    (by obtain ⟨C, hC⟩ := hbB; exact ⟨C, fun y => hC _⟩) hv

end EinsteinRelation.Regeneration
