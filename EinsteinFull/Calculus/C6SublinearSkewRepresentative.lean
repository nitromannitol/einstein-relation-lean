import EinsteinFull.Calculus.C6SublinearFluxTraceIdentification
import EinsteinRelation.Correctors.WeakGradientCentering

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.External.AKM EinsteinRelation.Correctors
open EinsteinRelation.Environment.AKMTestIntegralSupport ReductionImageV3

/-- A spatially constant matrix shift preserves every field of the source
flux-corrector carrier. In particular, that carrier does not fix its symmetric
additive gauge. -/
def c6SourceFluxCorrectorAddConst {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) (C : Mat d) : FluxCorrector φ where
  potential := fun a x => S.potential a x + C
  grad := S.grad
  measurable_potential := by
    have hc : Continuous (fun A : Mat d => A + C) := continuous_id.add continuous_const
    exact hc.measurable.comp S.measurable_potential
  measurable_grad := S.measurable_grad
  weak_gradient := by
    filter_upwards [S.weak_gradient] with a ha
    intro j k
    simpa only [Matrix.add_apply, sub_neg_eq_add] using
      hasWeakGradient_sub_const Set.univ (ha j k) (-(C j k))
  locally_square_integrable := by
    filter_upwards [S.locally_square_integrable] with a ha
    intro R hR j k
    let : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict_euclideanBall 0 R hR
    exact ⟨(ha R hR j k).1.add (memLp_const (C j k)), (ha R hR j k).2⟩
  heat_selected := S.heat_selected

/-- Heat selection fixes the sign: the column trace is the negative of the
literal row trace used by `sublinear_source_flux_column_trace`. -/
theorem c6_sourceColumnGradientTrace_eq_neg_row {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
      (∑ k : Fin d, S.grad a k j x k) = -c6SourceRowDivergence S a x j := by
  filter_upwards [S.heat_selected] with a ha
  have hswap := ae_all_iff.mpr fun j => ae_all_iff.mpr fun k =>
    c6_heatSelectedFluxGradient_ae_swap ha j k k
  filter_upwards [hswap] with x hx
  intro j
  change (∑ k : Fin d, S.grad a k j x k) = -(∑ k : Fin d, S.grad a j k x k)
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => hx j k

/-- On the actual source law the selected column trace is minus centered
flux. This sign is independent of every additive potential gauge. -/
theorem c6_actualSourceColumnGradientTrace_eq_neg_centeredFlux
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂actualCoefficientLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ j : Fin d, (∑ k : Fin d, S.grad a k j x k) = -centeredFlux φ a x j := by
  filter_upwards [c6_sourceColumnGradientTrace_eq_neg_row S,
    sublinear_source_flux_column_trace d hd D Q hQ i φ S] with a hcol htrace
  filter_upwards [hcol, htrace] with x hx htrace
  intro j
  rw [hx j, htrace]

/-- The skew gauge followed by an identity shift is an admissible source
flux corrector whose diagonal is identically one. -/
theorem c6SourceFluxCorrector_skew_add_one_diagonal {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) (a : Coefficient d K) (x : Vec d) (j : Fin d) :
    (c6SourceFluxCorrectorAddConst (c6SkewSourceFluxCorrector S) 1).potential
      a x j j = 1 := by
  simp only [c6SourceFluxCorrectorAddConst, c6SkewSourceFluxCorrector,
    c6SkewSourcePotential, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.transpose_apply, sub_self, smul_zero,
    Matrix.one_apply_eq, zero_add]

/-- Counterexample to demanding a skew representative in the exact AE
potential class of an arbitrary `FluxCorrector`. The carrier permits a
symmetric constant shift, whereas a skew real matrix has zero diagonal. -/
theorem exists_sourceFluxCorrector_without_skew_representative
    {d : ℕ} (hd : 0 < d) {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} {φ : Corrector P e} (S : FluxCorrector φ) :
    ∃ T : FluxCorrector φ, ∀ a : Coefficient d K,
      ¬ ∃ v : Vec d → Mat d,
        (∀ x, (v x).transpose = -(v x)) ∧
        v =ᵐ[(volume : Measure (Vec d))] T.potential a := by
  refine ⟨c6SourceFluxCorrectorAddConst (c6SkewSourceFluxCorrector S) 1, ?_⟩
  intro a h
  obtain ⟨v, hskew, heq⟩ := h
  obtain ⟨x, hx⟩ := heq.exists
  let j : Fin d := ⟨0, hd⟩
  have hs := congrArg (fun A : Mat d => A j j) (hskew x)
  have hv := congrArg (fun A : Mat d => A j j) hx
  rw [c6SourceFluxCorrector_skew_add_one_diagonal] at hv
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hs
  linarith

/-- The same obstruction holds on the actual source law, even before asking
for smoothness or the column-divergence identity. Thus the planned exact-class
skew-representative contract cannot hold for every source flux corrector. -/
theorem exists_actualSourceFluxCorrector_without_skew_representative
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (S : FluxCorrector φ) :
    ∃ T : FluxCorrector φ, ¬ (∀ᵐ a ∂actualCoefficientLaw Q,
      ∃ v : Vec d → Mat d,
        (∀ x, (v x).transpose = -(v x)) ∧
        v =ᵐ[(volume : Measure (Vec d))] T.potential a) := by
  let : Fact (2 ≤ d) := ⟨hd⟩
  let : IsProbabilityMeasure (actualCoefficientLaw Q) :=
    (lawHypotheses_actualCoefficientLaw Q).1
  obtain ⟨T, hT⟩ := exists_sourceFluxCorrector_without_skew_representative
    (by omega) S
  refine ⟨T, fun h => ?_⟩
  obtain ⟨a, ha⟩ := h.exists
  exact hT a ha

end EinsteinFull.Blueprint
