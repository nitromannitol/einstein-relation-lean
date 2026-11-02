import EinsteinRelation.Regeneration.FirstRegenerationEndpointFormula

/-!
# The killed future mean and conditioning on no backtracking

Source `paper/main.tex:401–409`. The actual origin coupled law starts at
zero by its path marginal and the GMP realization. Consequently the mean
of the killed future test is the probability of no backtracking times
the conditional future-record mean. No renewal assertion is used.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

/-- The actual coupled origin paths start at zero, including the
probability-part normalization in the annealed law. -/
theorem ae_origin_start_of_isGMPReducedKernel {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ p ∂annealedCoupledLaw Q.measure K, p.2.1 0 = 0 := by
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp measurable_snd.fst)
      measurable_const)
  filter_upwards [hK.1, hpath.1, hP] with ω hp hm hω
  haveI : IsProbabilityMeasure (originCoupledLaw K ω) := hp
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
  obtain ⟨_, r, hr⟩ := hω
  have hstarts : ∀ᵐ γ ∂P (0, ω), γ 0 = 0 := by
    rw [hr 0]
    exact r.pathLaw_starts_at 0
  rw [← hm] at hstarts
  exact ae_of_ae_map measurable_fst.aemeasurable hstarts

/-- Spatial and temporal origin records agree on paths starting at zero. -/
theorem spatialFutureRecord_origin_eq_iteratedRecord_zero {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (ω : FieldPair d) (z : CoupledSample d)
    (hz : z.1 0 = 0) :
    spatialFutureRecord R i (0, ω) z = iteratedRecord Δ lam R i 0 (ω, z) := by
  have he := spatialFutureRecord_sampleTimeShift Δ R i ω z 0
  rw [sampleTimeShift_zero, hz] at he
  exact he

/-- The mean at the origin of any measurable killed-future version is
the conditional mean times the literal no-backtracking probability. -/
theorem integral_killed_future_origin_eq_condIntegral {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (hstart : ∀ᵐ p ∂annealedCoupledLaw Q K, p.2.1 0 = 0)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (hD : annealedCoupledLaw Q K {p | NoBacktracking R p.2.1 i} ≠ 0)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hb : BoundedRealTest Φ)
    (B : Vec d × FieldPair d → ℝ)
    (hBo : ∀ᵐ ω ∂Q, B (0, ω) = ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω)) :
    (∫ ω, B (0, ω) ∂Q) =
      (annealedCoupledLaw Q K {p | NoBacktracking R p.2.1 i}).toReal *
        ∫ p, Φ (iteratedRecord Δ lam R i 0 p)
          ∂ProbabilityTheory.cond (annealedCoupledLaw Q K) {p | NoBacktracking R p.2.1 i} := by
  let μ := annealedCoupledLaw Q K
  let D : Set (FieldPair d × CoupledSample d) := {p | NoBacktracking R p.2.1 i}
  haveI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q K hK
  have hDm : MeasurableSet D := (measurableSet_NoBacktracking R i).preimage measurable_snd.fst
  let F : FieldPair d × CoupledSample d → ℝ := fun p => killedFutureTest R i Φ ((0, p.1), p.2)
  have hF : Measurable F := (measurable_killedFutureTest R i Φ hΦ).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hbF : BoundedRealTest F := by
    obtain ⟨C, hC⟩ := boundedRealTest_killedFutureTest R i Φ hb
    exact ⟨C, fun p => hC _⟩
  have hmean : (∫ ω, B (0, ω) ∂Q) = ∫ p in D, Φ (iteratedRecord Δ lam R i 0 p) ∂μ := by
    rw [integral_congr_ae hBo, ← integral_annealedCoupledLaw Q K hK F hF hbF,
      ← integral_indicator hDm]
    apply integral_congr_ae
    filter_upwards [hstart] with p hp
    simp only [F, killedFutureTest,
      spatialFutureRecord_origin_eq_iteratedRecord_zero Δ lam R i p.1 p.2 hp]
    by_cases h : p ∈ D <;> simp [D] at h ⊢ <;> simp [h]
  rw [hmean]
  change _ = (μ D).toReal * ∫ p, Φ (iteratedRecord Δ lam R i 0 p) ∂((μ D)⁻¹ • μ.restrict D)
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  have hmass : (μ D).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hD, measure_ne_top μ D⟩
  field_simp


end EinsteinRelation.Regeneration
