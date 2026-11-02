import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds
import EinsteinFull.Frozen.ReducedLawStationary
import EinsteinRelation.Environment.SourceReducedBoundSupport

open MeasureTheory

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- The actual reduced joint law inherits the structural bounds of the physical
pair, with all three constants chosen before the dimension and the law. -/
theorem node_eq_u2E_reduced_u2D_bounds_of_deps :
    node_eq_u2E_reduced_u2D_boundsStmt := by
  intro L hL
  have hLp : 0 ≤ L := le_trans (by norm_num) hL
  have hK : 1 ≤ sourceReducedBound L := by
    have he : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by positivity)
    have hp : 1 ≤ 3 * L ^ 2 + L + 1 := by
      nlinarith only [sq_nonneg L, hLp]
    simpa only [one_mul, sourceReducedBound] using
      (mul_le_mul he hp (by norm_num) (Real.exp_pos _).le)
  have hsum : Real.exp (2 * L) * (L + 2 * L ^ 2) +
      Real.exp (2 * L) * (2 * L) ≤ sourceReducedBound L := by
    unfold sourceReducedBound
    have hp : 2 * L ^ 2 + 3 * L ≤ 3 * L ^ 2 + L + 1 := by
      nlinarith only [sq_nonneg (L - 1)]
    calc
      _ = Real.exp (2 * L) * (2 * L ^ 2 + 3 * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
  refine ⟨sourceReducedBound L, Real.exp (2 * L) * (L + 2 * L ^ 2),
    Real.exp (2 * L) * (2 * L), hK, by positivity, by positivity, hsum, ?_⟩
  intro d r₀ Q
  refine ⟨reducedLaw_stationary Q, ?_, ?_⟩
  · intro U W hU hW hgap
    have hind := ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left (Q.finiteRange U W hU hW hgap)
        (Probability.localSigma_reduce_comap_le U))
      (Probability.localSigma_reduce_comap_le W)
    rw [ProbabilityTheory.Indep_iff]
    intro s t hs ht
    have hs' := Probability.localSigma_le_borel U s hs
    have ht' := Probability.localSigma_le_borel W t ht
    change Q.measure.map reduce (s ∩ t) =
      Q.measure.map reduce s * Q.measure.map reduce t
    rw [Measure.map_apply Probability.measurable_reduce (hs'.inter ht'),
      Measure.map_apply Probability.measurable_reduce hs',
      Measure.map_apply Probability.measurable_reduce ht', Set.preimage_inter]
    exact (ProbabilityTheory.Indep_iff _ _ _).1 hind _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · have hn : Continuous (euclideanNorm : Vec d → ℝ) := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    have ha (x : Vec d) : Continuous (fun ω : FieldPair d => ω.1 x) :=
      (continuous_eval_const x).comp continuous_fst
    have hm (x : Vec d) : Continuous (fun ω : FieldPair d => ω.2 x) :=
      (continuous_eval_const x).comp continuous_snd
    have hq (x ξ : Vec d) : Continuous (fun ω : FieldPair d =>
        dot ξ ((ω.1 x).mulVec ξ)) := by
      unfold dot
      exact continuous_finset_sum _ fun j _ => continuous_const.mul
        ((continuous_apply j).comp ((ha x).matrix_mulVec continuous_const))
    have hc : IsClosed {ω : FieldPair d |
        IsElliptic (sourceReducedBound L) ω.1 ∧
        (∀ x, (sourceReducedBound L)⁻¹ ≤ ω.2 x ∧ ω.2 x ≤ sourceReducedBound L) ∧
        IsOperatorLipschitz (Real.exp (2 * L) * (L + 2 * L ^ 2)) ω.1 ∧
        ∀ x y, |ω.2 x - ω.2 y| ≤
          Real.exp (2 * L) * (2 * L) * euclideanNorm (x - y)} := by
      unfold IsElliptic IsOperatorLipschitz
      simp only [Set.setOf_and, Set.setOf_forall]
      refine (isClosed_iInter fun x =>
        (isClosed_eq (ha x).matrix_transpose (ha x)).inter
          (isClosed_iInter fun ξ => (isClosed_le continuous_const (hq x ξ)).inter
            (isClosed_le (hq x ξ) continuous_const))).inter ?_
      refine (isClosed_iInter fun x => (isClosed_le continuous_const (hm x)).inter
        (isClosed_le (hm x) continuous_const)).inter ?_
      refine (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun ξ =>
        isClosed_le (hn.comp (((ha x).sub (ha y)).matrix_mulVec continuous_const))
          continuous_const).inter ?_
      exact isClosed_iInter fun x => isClosed_iInter fun y =>
        isClosed_le ((hm x).sub (hm y)).abs continuous_const
    change ∀ᵐ ω ∂Q.measure.map reduce, _
    rw [ae_map_iff Probability.measurable_reduce.aemeasurable hc.measurableSet]
    filter_upwards [Q.regular] with ω hω
    obtain ⟨_, he, hm, ha, hs, _⟩ := sourceReducedBound_support hL hω
    exact ⟨he, hm, ha, hs⟩

end EinsteinFull.Blueprint
