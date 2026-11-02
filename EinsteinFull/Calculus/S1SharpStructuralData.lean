import EinsteinFull.Calculus.S1SharpPhysicalBounds
import EinsteinFull.Frozen.SmoothEnvironment

/-! The structural data of the sharpness example (`paper/main.tex:1534–1541`): one ellipticity
constant, the range `4` and one derivative-bound sequence that precede every noise sample, with
`IsSmoothWithBounds` for every constructed physical pair. -/

namespace EinsteinFull.Calculus.S1

open EinsteinRelation EinsteinRelation.Sharpness EinsteinFull.Work.W8

variable {d : ℕ}

theorem euclideanNorm_le_sum_abs (y : Vec d) : euclideanNorm y ≤ ∑ i, |y i| := by
  unfold euclideanNorm
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun i _ => abs_nonneg _)]
  unfold euclideanSq dot
  calc ∑ i, y i * y i = ∑ i, |y i| * |y i| :=
        Finset.sum_congr rfl fun i _ => (abs_mul_abs_self _).symm
    _ ≤ ∑ i, |y i| * ∑ j, |y j| :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ i)) (abs_nonneg _)
    _ = (∑ i, |y i|) ^ 2 := by rw [← Finset.sum_mul, sq]

/-- Euclidean multilinear bounds of every order for the constructed pair, uniformly in the
sample and the point. -/
theorem exists_physicalPair_smoothBounds (i : Fin d) :
    ∃ A B : ℕ → ℝ, (∀ k, 0 ≤ A k) ∧ (∀ k, 0 ≤ B k) ∧
      ∀ (k : ℕ) (W : NoiseSample d) (x : Vec d) (v : Fin k → Vec d) (ξ : Vec d),
        euclideanNorm (Matrix.mulVec (fun j l => iteratedFDeriv ℝ k
            (fun y => (physicalPair i W).1 y j l) x v) ξ) ≤
          A k * (∏ j, euclideanNorm (v j)) * euclideanNorm ξ ∧
        |iteratedFDeriv ℝ k (fun y => (physicalPair i W).2 y) x v| ≤
          B k * ∏ j, euclideanNorm (v j) := by
  have hk : ∀ k : ℕ, ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (W : NoiseSample d) (x : Vec d) (v : Fin k → Vec d) (ξ : Vec d),
        euclideanNorm (Matrix.mulVec (fun j l => iteratedFDeriv ℝ k
            (fun y => (physicalPair i W).1 y j l) x v) ξ) ≤
          A * (∏ j, euclideanNorm (v j)) * euclideanNorm ξ ∧
        |iteratedFDeriv ℝ k (fun y => (physicalPair i W).2 y) x v| ≤
          B * ∏ j, euclideanNorm (v j) := by
    intro k
    have hent : ∀ j l : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : NoiseSample d) (x : Vec d)
        (v : Fin k → Vec d),
        |iteratedFDeriv ℝ k (fun y => (physicalPair i W).1 y j l) x v| ≤
          C * ∏ j, euclideanNorm (v j) := fun j l => by
      obtain ⟨C, h0, h⟩ := ((physicalPair_unifBdd i).2.2.1 j l).euclid_bound k
      exact ⟨C, h0, fun W x v => h W x v⟩
    choose C hC0 hC using hent
    obtain ⟨CV, hV0, hV⟩ := (physicalPair_unifBdd i).2.2.2.euclid_bound k
    set Cm : ℝ := ∑ j, ∑ l, C j l with hCm
    have hCle : ∀ j l, C j l ≤ Cm := fun j l =>
      (Finset.single_le_sum (f := fun l => C j l) (fun l _ => hC0 j l) (Finset.mem_univ l)).trans
        (Finset.single_le_sum (f := fun j => ∑ l, C j l)
          (fun j _ => Finset.sum_nonneg fun l _ => hC0 j l) (Finset.mem_univ j))
    have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => hC0 j l
    refine ⟨d * d * Cm, CV, by positivity, hV0, fun W x v ξ => ⟨?_, hV W x v⟩⟩
    set P : ℝ := ∏ j, euclideanNorm (v j) with hP
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
    have hM : ∀ j l, |iteratedFDeriv ℝ k (fun y => (physicalPair i W).1 y j l) x v| ≤ Cm * P :=
      fun j l => (hC j l W x v).trans (mul_le_mul_of_nonneg_right (hCle j l) hP0)
    refine (euclideanNorm_le_sum_abs _).trans ?_
    have hξ : ∀ l, |ξ l| ≤ euclideanNorm ξ := fun l => abs_apply_le_euclideanNorm ξ l
    have hterm : ∀ j, |Matrix.mulVec (fun j l => iteratedFDeriv ℝ k
        (fun y => (physicalPair i W).1 y j l) x v) ξ j| ≤ d * (Cm * P * euclideanNorm ξ) := by
      intro j
      simp only [Matrix.mulVec, dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l, |iteratedFDeriv ℝ k (fun y => (physicalPair i W).1 y j l) x v * ξ l|
          ≤ ∑ _l : Fin d, Cm * P * euclideanNorm ξ := by
            apply Finset.sum_le_sum
            intro l _
            rw [abs_mul]
            exact mul_le_mul (hM j l) (hξ l) (abs_nonneg _) (mul_nonneg hCm0 hP0)
        _ = d * (Cm * P * euclideanNorm ξ) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ∑ j, |Matrix.mulVec (fun j l => iteratedFDeriv ℝ k
          (fun y => (physicalPair i W).1 y j l) x v) ξ j|
        ≤ ∑ _j : Fin d, (d : ℝ) * (Cm * P * euclideanNorm ξ) := Finset.sum_le_sum fun j _ => hterm j
      _ = d * d * Cm * P * euclideanNorm ξ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  choose A B hA hB h using hk
  exact ⟨A, B, hA, hB, h⟩

/-- The structural data of the sharpness example. -/
theorem exists_sharpStructuralData (i : Fin d) :
    ∃ D : StructuralData d, D.dependenceRange = 4 ∧
      (∀ W : NoiseSample d, IsRegular D.ellipticity (physicalPair i W)) ∧
      (∀ W : NoiseSample d, IsSmoothWithBounds D.derivativeBound (physicalPair i W)) := by
  obtain ⟨Λ, hΛ, hreg⟩ := exists_physicalPair_regularity i
  obtain ⟨A, B, hA, hB, h⟩ := exists_physicalPair_smoothBounds i
  refine ⟨⟨Λ, 4, fun k => A k + B k + 1, by linarith, by norm_num,
    fun k _ => by linarith [hA k, hB k]⟩, rfl, hreg, fun W => ?_⟩
  refine ⟨physicalPair_isSmooth i W, fun k _ => ⟨A k, B k, hA k, hB k, ?_, ?_, ?_⟩⟩
  · show A k + B k ≤ A k + B k + 1
    linarith
  · intro x v ξ
    exact (h k W x v ξ).1
  · intro x v
    exact (h k W x v 0).2

end EinsteinFull.Calculus.S1
