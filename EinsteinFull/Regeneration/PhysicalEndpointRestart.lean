import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.Regeneration.EndpointJointUniform

/-!
# The annealed uniform endpoint with a factor of the endpoint displacement

For the split coupling of the physical kernel, the restart at the end of a successful interval
and the uniform law of its endpoint hold jointly with a nonnegative factor of the endpoint
displacement over the interval (GMP 2012, Proposition 5.4(ii)–(iii); Shen 2003, Theorem 2.5,
whose cycle variables contain the displacement up to the regeneration time).
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The annealed uniform endpoint formula for a nonnegative bounded future test multiplied by a
nonnegative bounded function of the endpoint displacement over the successful interval. -/
theorem integral_annealed_future_endpoint_eq_uniformEndpointAverage_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d) (hδ : 0 ≤ δ)
    (hR0 : volume (endpointBall i R 0) ≠ ⊤) (hRpos : volume (endpointBall i R 0) ≠ 0)
    (hRestart : HasDeterministicRestart Q.measure Δ K)
    (hUniform : HasUniformSuccessfulEndpoint Q.measure Δ δ R i K)
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H)
    (hbH : BoundedRealTest H) (hH0 : ∀ z, 0 ≤ H z)
    (g : Vec d → ℝ) (hg : Measurable g) (hbg : BoundedRealTest g) (hg0 : ∀ y, 0 ≤ g y)
    (Ψ : (Vec d × FieldPair d) × CoupledSample d → ℝ)
    (hΨ : Measurable Ψ) (hbΨ : BoundedRealTest Ψ)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B)
    (hB0 : ∀ p, 0 ≤ B p)
    (hBeq : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
      B xω = ∫ w, Ψ (xω, w) ∂K xω) :
    (∫ q, H q.2 * (if q.2.2 m = true then (1 : ℝ) else 0) *
      g (q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ) - q.2.1 ((m : ℝ≥0) * Δ)) *
      Ψ ((q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ), q.1),
        sampleTimeShift Δ q.2 (((m + 1 : ℕ) : ℝ≥0) * Δ))
      ∂annealedCoupledLaw Q.measure K) =
      ∫ ω, δ * ∫ z, H z * endpointAverage i R (z.1 ((m : ℝ≥0) * Δ))
        (fun y => g (y - z.1 ((m : ℝ≥0) * Δ)) * B (y, ω)) ∂K (0, ω) ∂Q.measure := by
  classical
  let t : ℝ≥0 := ((m + 1 : ℕ) : ℝ≥0) * Δ
  let s : ℝ≥0 := (m : ℝ≥0) * Δ
  have ht : 0 < t := mul_pos (by positivity) hΔ
  have hprob := ae_quenched_of_annealed Q.measure K hK
    (ae_at_endpoint_of_product_ae_phys hd Q lam h0 h1 P K hK hpath hP t ht _ hK.2)
  have hversion := ae_quenched_of_annealed Q.measure K hK
    (ae_at_endpoint_of_product_ae_phys hd Q lam h0 h1 P K hK hpath hP t ht _ hBeq)
  let F : FieldPair d × CoupledSample d → ℝ := fun q =>
    H q.2 * (if q.2.2 m = true then 1 else 0) * g (q.2.1 t - q.2.1 s) *
      Ψ ((q.2.1 t, q.1), sampleTimeShift Δ q.2 t)
  have hHfull := hH.mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hte : Measurable fun q : FieldPair d × CoupledSample d => q.2.1 t :=
    (continuous_eval_const t).measurable.comp measurable_snd.fst
  have hse : Measurable fun q : FieldPair d × CoupledSample d => q.2.1 s :=
    (continuous_eval_const s).measurable.comp measurable_snd.fst
  have hF : Measurable F := by
    exact (((hHfull.comp measurable_snd).mul
      (Measurable.ite (measurableSet_eq_fun ((measurable_pi_apply m).comp measurable_snd.snd)
        measurable_const) measurable_const measurable_const)).mul (hg.comp (hte.sub hse))).mul
      (hΨ.comp ((hte.prodMk measurable_fst).prodMk ((measurable_sampleTimeShift Δ).comp
          (measurable_const.prodMk measurable_snd))))
  obtain ⟨CH, hCH⟩ := hbH
  obtain ⟨Cg, hCg⟩ := hbg
  obtain ⟨CP, hCP⟩ := hbΨ
  have hbF : BoundedRealTest F := by
    refine ⟨max CH 0 * max Cg 0 * max CP 0, fun q => ?_⟩
    dsimp only [F]
    have hc : |(if q.2.2 m = true then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    rw [abs_mul, abs_mul, abs_mul]
    calc |H q.2| * |(if q.2.2 m = true then (1 : ℝ) else 0)| * |g (q.2.1 t - q.2.1 s)| *
          |Ψ ((q.2.1 t, q.1), sampleTimeShift Δ q.2 t)| ≤
          max CH 0 * 1 * max Cg 0 * max CP 0 := by
          gcongr
          · exact (hCH _).trans (le_max_left _ _)
          · exact (hCg _).trans (le_max_left _ _)
          · exact (hCP _).trans (le_max_left _ _)
      _ = max CH 0 * max Cg 0 * max CP 0 := by ring
  change (∫ q, F q ∂annealedCoupledLaw Q.measure K) = _
  rw [integral_annealedCoupledLaw Q.measure K hK F hF hbF]
  apply integral_congr_ae
  filter_upwards [hK.1, hRestart.1, hUniform.1, hprob, hversion] with ω hω hr hu hp hv
  have : IsProbabilityMeasure (K (0, ω)) := hω
  exact integral_future_endpoint_eq_uniformEndpointAverage Δ δ R i K (0, ω) hr hu hδ hR0 hRpos
    m hp H hH ⟨CH, hCH⟩ hH0 g hg ⟨Cg, hCg⟩ hg0 (fun q => Ψ ((q.1, ω), q.2))
    (hΨ.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd))
    ⟨CP, fun q => hCP _⟩ (fun y => B (y, ω)) (hB.comp measurable_prodMk_right)
    (by obtain ⟨C, hC⟩ := hbB; exact ⟨C, fun y => hC _⟩) (fun y => hB0 _) hv

end EinsteinFull.Regeneration
