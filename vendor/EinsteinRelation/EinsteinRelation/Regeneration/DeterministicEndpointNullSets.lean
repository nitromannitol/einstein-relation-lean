import EinsteinRelation.Regeneration.Coupling
import EinsteinRelation.Diffusion.GMPFamilyAPI

/-!
# Null sets at deterministic restart positions

Source `paper/main.tex:383–407`. A product-a.e. identity of a kernel cannot
be specialized at an arbitrary spatial point. The positive-time heat-kernel
density makes the actual restart pair `(Y_t, ω)` absolutely continuous with
respect to `volume.prod Q`, which justifies that specialization.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

/-- The actual deterministic-time endpoint together with its environment
has law absolutely continuous with respect to the spatial-environment product
law (`paper/main.tex:383–407`). -/
theorem map_endpoint_environment_absolutelyContinuous {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (hpath : HasPathMarginals Q K P)
    (t : ℝ≥0) (hendpoint : ∀ᵐ ω ∂Q,
      (P (0, ω)).map (pathPosition t) ≪ (volume : Measure (Vec d))) :
    (annealedCoupledLaw Q K).map (fun p => (p.2.1 t, p.1)) ≪
      (volume : Measure (Vec d)).prod Q := by
  have hmap : Measurable (fun p : FieldPair d × CoupledSample d => (p.2.1 t, p.1)) :=
    ((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk measurable_fst
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hnull
  have hsects : ∀ᵐ ω ∂Q, (volume : Measure (Vec d)) ((fun x => (x, ω)) ⁻¹' s) = 0 := by
    have hswap : (Q.prod (volume : Measure (Vec d))) (Prod.swap ⁻¹' s) = 0 := by
      rw [← Measure.prod_swap, Measure.map_apply measurable_swap (measurable_swap hs)]
      simpa only [Set.preimage_preimage, Function.comp_def, Prod.swap_swap,
        Set.preimage_id_eq, Set.preimage_id, Set.preimage_id'] using hnull
    exact Measure.measure_ae_null_of_prod_null hswap
  rw [Measure.map_apply hmap hs, annealedCoupledLaw,
    Measure.compProd_apply (hmap hs)]
  rw [← lintegral_zero (μ := Q)]
  apply lintegral_congr_ae
  filter_upwards [hK.1, hpath.1, hendpoint, hsects] with ω hprob hpathω hac hsect
  haveI : IsProbabilityMeasure (originCoupledLaw K ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
  have hcoord : (K (0, ω)).map (fun z : CoupledSample d => z.1 t) =
      (P (0, ω)).map (pathPosition t) := by
    rw [← hpathω, Measure.map_map (measurable_pathPosition t) measurable_fst]
    rfl
  have hsω : MeasurableSet ((fun x : Vec d => (x, ω)) ⁻¹' s) :=
    hs.preimage measurable_prodMk_right
  have hzero := hac hsect
  have hmz : Measurable (fun z : CoupledSample d => z.1 t) :=
    (continuous_eval_const t).measurable.comp measurable_fst
  rw [← hcoord, Measure.map_apply hmz hsω] at hzero
  exact hzero

/-- Product-a.e. kernel facts hold at the actual positive-time GMP restart
pair. This retains the required origin clause in `hK`. -/
theorem ae_at_endpoint_of_product_ae {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (t : ℝ≥0) (ht : 0 < t) (p : Vec d × FieldPair d → Prop)
    (hp : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure, p xω) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q.measure K, p (ωz.2.1 t, ωz.1) := by
  have hac := map_endpoint_environment_absolutelyContinuous Q.measure P K hK hpath t
    ((map_pathPosition_absolutelyContinuous_of_isGMPReducedKernel hd Q.ellipticity_parameter
      Q lam h0 h1 P hP t ht).mono fun _ h => h 0)
  exact ae_of_ae_map
    ((((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk
      measurable_fst).aemeasurable) (hac.ae_le hp)


end EinsteinRelation.Regeneration
