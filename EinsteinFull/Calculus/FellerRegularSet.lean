import EinsteinRelation.Environment.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.CompactOpen

/-!
# The regular environments form a closed (hence Borel) subset of `FieldPair d`

`IsRegular Λ₀ ω` is an intersection of conditions, each a closed condition on the pair of
continuous fields `ω` because point evaluation is continuous in the compact-open topology.

-/

open MeasureTheory

namespace EinsteinFull.Calculus.Feller

open EinsteinRelation

theorem continuous_euclideanNorm (d : ℕ) : Continuous (euclideanNorm (d := d)) := by
  unfold euclideanNorm euclideanSq dot
  fun_prop

theorem isClosed_setOf_isRegular (d : ℕ) (Λ₀ : ℝ) :
    IsClosed {ω : FieldPair d | IsRegular Λ₀ ω} := by
  have h1 : ∀ x : Vec d, Continuous fun ω : FieldPair d => ω.1 x :=
    fun x => (continuous_eval_const x).comp continuous_fst
  have h2 : ∀ x : Vec d, Continuous fun ω : FieldPair d => ω.2 x :=
    fun x => (continuous_eval_const x).comp continuous_snd
  have hn := continuous_euclideanNorm d
  have hdot : Continuous (fun p : Vec d × Vec d => dot p.1 p.2) := by
    unfold dot
    fun_prop
  have hmv : ∀ (x : Vec d) (ξ : Vec d),
      Continuous fun ω : FieldPair d => (ω.1 x).mulVec ξ :=
    fun x ξ => (h1 x).matrix_mulVec continuous_const
  have hdotmv : ∀ (x : Vec d) (ξ : Vec d),
      Continuous fun ω : FieldPair d => dot ξ ((ω.1 x).mulVec ξ) :=
    fun x ξ => hdot.comp ((continuous_const).prodMk (hmv x ξ))
  have hdd : ∀ (x y ξ : Vec d),
      Continuous fun ω : FieldPair d => euclideanNorm ((ω.1 x - ω.1 y).mulVec ξ) :=
    fun x y ξ => hn.comp (((h1 x).sub (h1 y)).matrix_mulVec continuous_const)
  have hset : {ω : FieldPair d | IsRegular Λ₀ ω} =
      (⋂ x : Vec d, {ω : FieldPair d | (ω.1 x).transpose = ω.1 x}) ∩
      (⋂ x : Vec d, ⋂ ξ : Vec d,
        {ω : FieldPair d | Λ₀⁻¹ * euclideanSq ξ ≤ dot ξ ((ω.1 x).mulVec ξ)}) ∩
      (⋂ x : Vec d, ⋂ ξ : Vec d,
        {ω : FieldPair d | dot ξ ((ω.1 x).mulVec ξ) ≤ Λ₀ * euclideanSq ξ}) ∩
      (⋂ x : Vec d, {ω : FieldPair d | |ω.2 x| ≤ Λ₀}) ∩
      (⋂ x : Vec d, ⋂ y : Vec d, ⋂ ξ : Vec d,
        {ω : FieldPair d | euclideanNorm ((ω.1 x - ω.1 y).mulVec ξ) ≤
          Λ₀ * euclideanNorm (x - y) * euclideanNorm ξ}) ∩
      (⋂ x : Vec d, ⋂ y : Vec d,
        {ω : FieldPair d | |ω.2 x - ω.2 y| ≤ Λ₀ * euclideanNorm (x - y)}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      EinsteinRelation.IsRegular, IsElliptic, IsOperatorLipschitz]
    constructor
    · rintro ⟨hE, hb, hl, hv⟩
      exact ⟨⟨⟨⟨⟨fun x => (hE x).1, fun x ξ => ((hE x).2 ξ).1⟩, fun x ξ => ((hE x).2 ξ).2⟩, hb⟩,
        hl⟩, hv⟩
    · rintro ⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩
      exact ⟨fun x => ⟨hA x, fun ξ => ⟨hB x ξ, hC x ξ⟩⟩, hD, hE, hF⟩
  rw [hset]
  refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_)
    ?_) ?_) ?_) ?_
  · exact isClosed_iInter fun x => isClosed_eq (h1 x).matrix_transpose (h1 x)
  · exact isClosed_iInter fun x => isClosed_iInter fun ξ =>
      isClosed_le continuous_const (hdotmv x ξ)
  · exact isClosed_iInter fun x => isClosed_iInter fun ξ =>
      isClosed_le (hdotmv x ξ) continuous_const
  · exact isClosed_iInter fun x => isClosed_le (h2 x).abs continuous_const
  · exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun ξ =>
      isClosed_le (hdd x y ξ) continuous_const
  · exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le ((h2 x).sub (h2 y)).abs continuous_const

theorem measurableSet_setOf_isRegular (d : ℕ) (Λ₀ : ℝ) :
    MeasurableSet {ω : FieldPair d | IsRegular Λ₀ ω} :=
  (isClosed_setOf_isRegular d Λ₀).measurableSet

end EinsteinFull.Calculus.Feller
