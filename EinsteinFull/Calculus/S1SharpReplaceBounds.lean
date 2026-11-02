import EinsteinFull.Calculus.S1SharpReplace
import EinsteinFull.Calculus.S1SharpFamilyData
import EinsteinFull.Calculus.S1SharpRegular
import EinsteinFull.Calculus.S1SharpPhysicalBounds

/-! The replacement pair of the constructed physical pairs: uniform derivative bounds of every
order and a uniform regularity constant (`paper/main.tex:1565`). -/

open Set

namespace EinsteinFull.Calculus.S1

open EinsteinRelation EinsteinRelation.Sharpness EinsteinFull.Work.W8

variable {d : ℕ}

theorem dot_unitVector_mulVec (M : Mat d) (i : Fin d) :
    dot (unitVector i) (M.mulVec (unitVector i)) = M i i := by
  simp [dot, Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]

theorem euclideanSq_unitVector (i : Fin d) : euclideanSq (unitVector i) = 1 := by
  simp [euclideanSq, dot, unitVector, Pi.single_apply]

/-- The diagonal entry of the reduced coefficient of a constructed pair lies in `[1/3, 3]`. -/
theorem a11_mem_Icc (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    reducedCoefficient (physicalPair i W) x i i ∈ Icc (1 / 3 : ℝ) 3 := by
  obtain ⟨-, h⟩ := reducedCoefficient_isElliptic i W x
  obtain ⟨h1, h2⟩ := h (unitVector i)
  rw [dot_unitVector_mulVec, euclideanSq_unitVector] at h1 h2
  constructor
  · linarith
  · linarith

theorem unifBdd_a11 (i : Fin d) :
    UnifBdd (fun (W : NoiseSample d) x => reducedCoefficient (physicalPair i W) x i i) :=
  (physicalPair_unifBdd i).2.1 i i

theorem replacePair_unifBdd (i : Fin d) :
    (∀ j k : Fin d, UnifBdd (fun (W : NoiseSample d) x =>
      (replacePair i (physicalPair i W)).1 x j k)) ∧
    UnifBdd (fun (W : NoiseSample d) x => (replacePair i (physicalPair i W)).2 x) := by
  have hmax : ∀ (W : NoiseSample d) x, max (reducedCoefficient (physicalPair i W) x i i) (1 / 4) =
      reducedCoefficient (physicalPair i W) x i i := fun W x =>
    max_eq_left (by linarith [(a11_mem_Icc i W x).1])
  have hinv := (unifBdd_a11 i).inv_Icc (lo := 1 / 3) (hi := 3) (by norm_num) (by norm_num)
    (a11_mem_Icc i)
  refine ⟨fun j k => (hinv.mul ((physicalPair_unifBdd i).2.1 j k)).congr fun W x => ?_, ?_⟩
  · rw [replacePair_fst, hmax]
    simp only [Matrix.smul_apply, smul_eq_mul]
  · exact (((unifBdd_a11 i).log_Icc (lo := 1 / 3) (hi := 3) (by norm_num) (by norm_num)
      (a11_mem_Icc i)).const_mul (-(1 / 2 : ℝ))).congr fun W x => by
        rw [replacePair_snd, hmax]

theorem replacePair_isSmoothFieldPair (i : Fin d) (W : NoiseSample d) :
    IsSmoothFieldPair (replacePair i (physicalPair i W)) :=
  ⟨fun j k => (replacePair_unifBdd i).1 j k |>.1 W, (replacePair_unifBdd i).2.1 W⟩

theorem replacePair_isElliptic (i : Fin d) (W : NoiseSample d) :
    IsElliptic 9 ((replacePair i (physicalPair i W)).1 : Vec d → Mat d) := by
  intro x
  obtain ⟨hs, hξ⟩ := reducedCoefficient_isElliptic i W x
  have hm := a11_mem_Icc i W x
  have hmax : max (reducedCoefficient (physicalPair i W) x i i) (1 / 4) =
      reducedCoefficient (physicalPair i W) x i i := max_eq_left (by linarith [hm.1])
  have hpos : 0 < reducedCoefficient (physicalPair i W) x i i := by linarith [hm.1]
  have hfst : (replacePair i (physicalPair i W)).1 x =
      (reducedCoefficient (physicalPair i W) x i i)⁻¹ • reducedCoefficient (physicalPair i W) x := by
    rw [replacePair_fst, hmax]
  rw [hfst]
  refine ⟨by rw [Matrix.transpose_smul, hs], fun ξ => ?_⟩
  have hq : dot ξ (((reducedCoefficient (physicalPair i W) x i i)⁻¹ •
      reducedCoefficient (physicalPair i W) x).mulVec ξ) =
      (reducedCoefficient (physicalPair i W) x i i)⁻¹ *
        dot ξ ((reducedCoefficient (physicalPair i W) x).mulVec ξ) := by
    rw [Matrix.smul_mulVec]
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hq]
  have hsq := euclideanSq_nonneg' ξ
  obtain ⟨hl, hu⟩ := hξ ξ
  have hinv1 : (1 / 3 : ℝ) ≤ reducedCoefficient (physicalPair i W) x i i := hm.1
  have hinv2 : reducedCoefficient (physicalPair i W) x i i ≤ 3 := hm.2
  have hq0 : 0 ≤ dot ξ ((reducedCoefficient (physicalPair i W) x).mulVec ξ) :=
    le_trans (mul_nonneg (by norm_num) hsq) hl
  have hinv3 : (3 : ℝ)⁻¹ ≤ (reducedCoefficient (physicalPair i W) x i i)⁻¹ :=
    inv_anti₀ hpos hinv2
  have hinv4 : (reducedCoefficient (physicalPair i W) x i i)⁻¹ ≤ 3 := by
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  constructor
  · calc (9 : ℝ)⁻¹ * euclideanSq ξ = (3 : ℝ)⁻¹ * ((3 : ℝ)⁻¹ * euclideanSq ξ) := by ring
      _ ≤ (reducedCoefficient (physicalPair i W) x i i)⁻¹ *
          dot ξ ((reducedCoefficient (physicalPair i W) x).mulVec ξ) :=
        mul_le_mul hinv3 hl (mul_nonneg (by norm_num) hsq) (inv_nonneg.2 hpos.le)
  · calc (reducedCoefficient (physicalPair i W) x i i)⁻¹ *
          dot ξ ((reducedCoefficient (physicalPair i W) x).mulVec ξ)
        ≤ 3 * (3 * euclideanSq ξ) := mul_le_mul hinv4 hu hq0 (by norm_num)
      _ = 9 * euclideanSq ξ := by ring

theorem replacePair_potential_bound (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    |(replacePair i (physicalPair i W)).2 x| ≤ 1 := by
  have hm := a11_mem_Icc i W x
  have hmax : max (reducedCoefficient (physicalPair i W) x i i) (1 / 4) =
      reducedCoefficient (physicalPair i W) x i i := max_eq_left (by linarith [hm.1])
  have hpos : 0 < reducedCoefficient (physicalPair i W) x i i := by linarith [hm.1]
  rw [replacePair_snd, hmax, abs_le]
  have h1 := Real.log_le_sub_one_of_pos hpos
  have h2 := Real.one_sub_inv_le_log_of_pos hpos
  have h3 : (reducedCoefficient (physicalPair i W) x i i)⁻¹ ≤ 3 := by
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith [hm.1]
  constructor <;> linarith [hm.2]

theorem exists_replacePair_regular (i : Fin d) :
    ∃ Λ : ℝ, 9 ≤ Λ ∧ ∀ W : NoiseSample d, IsRegular Λ (replacePair i (physicalPair i W)) := by
  obtain ⟨Λ, h1, -, h⟩ := exists_regular_of_family
    (fun W : NoiseSample d => replacePair i (physicalPair i W))
    (replacePair_unifBdd i).1 (replacePair_unifBdd i).2 (by norm_num)
    (replacePair_isElliptic i) (replacePair_potential_bound i)
  exact ⟨Λ, h1, h⟩

end EinsteinFull.Calculus.S1
