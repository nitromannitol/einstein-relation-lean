import EinsteinRelation.Environment.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
namespace EinsteinRelation.Sharpness
private theorem regular_closed_elliptic {d : ℕ} (Λ : ℝ) :
    IsClosed {ω : FieldPair d | IsElliptic Λ (ω.1 : Vec d → Mat d)} := by
  have hq (ξ : Vec d) : Continuous (fun M : Mat d => dot ξ (M.mulVec ξ)) := by
    have hm : Continuous (fun M : Mat d => M.mulVec ξ) := continuous_id.matrix_mulVec continuous_const
    unfold dot
    exact continuous_finset_sum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hm)
  have hM : IsClosed {M : Mat d | M.transpose=M ∧ ∀ ξ : Vec d,
      Λ⁻¹*euclideanSq ξ ≤ dot ξ (M.mulVec ξ) ∧ dot ξ (M.mulVec ξ) ≤ Λ*euclideanSq ξ} := by
    simp only [Set.setOf_and, Set.setOf_forall]
    apply IsClosed.inter (isClosed_eq continuous_id.matrix_transpose continuous_id)
    apply isClosed_iInter
    intro ξ
    exact (isClosed_le continuous_const (hq ξ)).inter (isClosed_le (hq ξ) continuous_const)
  have hs : {ω : FieldPair d | IsElliptic Λ (ω.1 : Vec d → Mat d)} =
      ⋂ x : Vec d, (fun ω : FieldPair d => ω.1 x) ⁻¹'
      {M : Mat d | M.transpose=M ∧ ∀ ξ : Vec d,
       Λ⁻¹*euclideanSq ξ ≤ dot ξ (M.mulVec ξ) ∧ dot ξ (M.mulVec ξ) ≤ Λ*euclideanSq ξ} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, IsElliptic]
  rw [hs]
  exact isClosed_iInter fun x => hM.preimage ((continuous_eval_const x).comp continuous_fst)

/-- The literal physical regularity predicate is Borel on the existing compact-open pair carrier.
Source main.tex Assumption1.1 and1218–1231. Every bound is an arbitrary intersection of closed
point-evaluation inequalities, including the literal Euclidean operator condition. -/
theorem measurableSet_isRegular_fieldPair {d : ℕ} (Λ : ℝ) :
    MeasurableSet {ω : FieldPair d | IsRegular Λ ω} := by
  have hn : Continuous (euclideanNorm : Vec d → ℝ) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have heval (x : Vec d) : Continuous (fun ω : FieldPair d => ω.2 x) :=
    (continuous_eval_const x).comp continuous_snd
  have haeval (x : Vec d) : Continuous (fun ω : FieldPair d => ω.1 x) :=
    (continuous_eval_const x).comp continuous_fst
  have hV : IsClosed {ω : FieldPair d | ∀ x : Vec d, |ω.2 x| ≤ Λ} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_le (heval x).abs continuous_const
  have hA : IsClosed {ω : FieldPair d | IsOperatorLipschitz Λ (ω.1 : Vec d → Mat d)} := by
    unfold IsOperatorLipschitz
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun ξ =>
      isClosed_le (hn.comp (((haeval x).sub (haeval y)).matrix_mulVec continuous_const)) continuous_const
  have hVL : IsClosed {ω : FieldPair d | ∀ x y : Vec d,
      |ω.2 x-ω.2 y| ≤ Λ*euclideanNorm (x-y)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le ((heval x).sub (heval y)).abs continuous_const
  have hclosed : IsClosed {ω : FieldPair d | IsRegular Λ ω} := by
    unfold IsRegular
    simp only [Set.setOf_and]
    exact (regular_closed_elliptic Λ).inter (hV.inter (hA.inter hVL))
  exact hclosed.measurableSet
end EinsteinRelation.Sharpness
