import EinsteinFull.Calculus.S1SharpStructuralData

/-! Regularity (Assumption 1.1 (S1)–(S3)) of a family of smooth field pairs with uniform
first-derivative bounds, a uniform ellipticity constant and a uniform potential bound
(`paper/main.tex:1565`). -/

namespace EinsteinFull.Calculus.S1

open EinsteinRelation

variable {d : ℕ}

theorem euclideanSq_nonneg' (ξ : Vec d) : 0 ≤ euclideanSq ξ := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem isElliptic_mono {a : Vec d → Mat d} {Λ Λ' : ℝ} (hΛ : 0 < Λ) (h : Λ ≤ Λ')
    (ha : IsElliptic Λ a) : IsElliptic Λ' a := by
  intro x
  obtain ⟨hs, hξ⟩ := ha x
  refine ⟨hs, fun ξ => ⟨?_, ?_⟩⟩
  · calc Λ'⁻¹ * euclideanSq ξ ≤ Λ⁻¹ * euclideanSq ξ :=
          mul_le_mul_of_nonneg_right (inv_anti₀ hΛ h) (euclideanSq_nonneg' ξ)
      _ ≤ _ := (hξ ξ).1
  · exact (hξ ξ).2.trans (mul_le_mul_of_nonneg_right h (euclideanSq_nonneg' ξ))

theorem euclideanNorm_nonneg' (ξ : Vec d) : 0 ≤ euclideanNorm ξ := Real.sqrt_nonneg _

/-- A matrix with entries bounded by `c` has `‖M ξ‖ ≤ d² c ‖ξ‖`. -/
theorem euclideanNorm_mulVec_le (M : Mat d) {c : ℝ} (hc : 0 ≤ c) (hM : ∀ j l, |M j l| ≤ c)
    (ξ : Vec d) : euclideanNorm (M.mulVec ξ) ≤ d * d * c * euclideanNorm ξ := by
  refine (euclideanNorm_le_sum_abs _).trans ?_
  have hξ : ∀ l, |ξ l| ≤ euclideanNorm ξ := fun l => abs_apply_le_euclideanNorm ξ l
  have hterm : ∀ j, |M.mulVec ξ j| ≤ d * (c * euclideanNorm ξ) := by
    intro j
    simp only [Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ l, |M j l * ξ l| ≤ ∑ _l : Fin d, c * euclideanNorm ξ := by
          apply Finset.sum_le_sum
          intro l _
          rw [abs_mul]
          exact mul_le_mul (hM j l) (hξ l) (abs_nonneg _) hc
      _ = d * (c * euclideanNorm ξ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc ∑ j, |M.mulVec ξ j| ≤ ∑ _j : Fin d, (d : ℝ) * (c * euclideanNorm ξ) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = d * d * c * euclideanNorm ξ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- A uniformly bounded family has uniformly Lipschitz members (Euclidean metric). -/
theorem UnifBdd.lipschitz {ι : Type*} {F : ι → Vec d → ℝ} (hF : UnifBdd F) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a x y, |F a x - F a y| ≤ L * euclideanNorm (x - y) := by
  obtain ⟨C, hC⟩ := hF.2 1
  refine ⟨|C|, abs_nonneg _, fun a x y => ?_⟩
  have hd : ∀ z, DifferentiableAt ℝ (F a) z := fun z => (hF.1 a).differentiable (by simp) z
  have hb : ∀ z ∈ (Set.univ : Set (Vec d)), ‖fderiv ℝ (F a) z‖ ≤ |C| := by
    intro z _
    have h1 : ‖fderiv ℝ (F a) z‖ = ‖iteratedFDeriv ℝ 1 (F a) z‖ := by
      have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F a) (x := z) (n := 0)
      rwa [norm_iteratedFDeriv_zero] at this
    rw [h1]
    exact (hC a z).trans (le_abs_self _)
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (fun z _ => hd z) hb
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_le_euclideanNorm _) (abs_nonneg _))

theorem exists_regular_of_family {ι : Type*} (G : ι → FieldPair d)
    (hent : ∀ j k : Fin d, UnifBdd (fun (W : ι) x => (G W).1 x j k))
    (hpot : UnifBdd (fun (W : ι) x => (G W).2 x)) {Λ0 B : ℝ} (hΛ0 : 0 < Λ0)
    (hell : ∀ W, IsElliptic Λ0 (G W).1) (hB : ∀ W x, |(G W).2 x| ≤ B) :
    ∃ Λ : ℝ, Λ0 ≤ Λ ∧ B ≤ Λ ∧ ∀ W, IsRegular Λ (G W) := by
  choose Le hLe0 hLe using fun j k : Fin d => (hent j k).lipschitz
  obtain ⟨Lp, hLp0, hLp⟩ := hpot.lipschitz
  set Lm : ℝ := ∑ j, ∑ k, Le j k with hLm
  have hLm0 : 0 ≤ Lm := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hLe0 j k
  have hLle : ∀ j k, Le j k ≤ Lm := fun j k =>
    (Finset.single_le_sum (f := fun k => Le j k) (fun k _ => hLe0 j k) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun j => ∑ k, Le j k)
        (fun j _ => Finset.sum_nonneg fun k _ => hLe0 j k) (Finset.mem_univ j))
  refine ⟨max (max Λ0 B) (max (d * d * Lm) Lp), (le_max_left _ _).trans (le_max_left _ _),
    (le_max_right _ _).trans (le_max_left _ _), fun W => ?_⟩
  set Λ : ℝ := max (max Λ0 B) (max (d * d * Lm) Lp) with hΛ
  have h1 : Λ0 ≤ Λ := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : B ≤ Λ := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : (d : ℝ) * d * Lm ≤ Λ := (le_max_left _ _).trans (le_max_right _ _)
  have h4 : Lp ≤ Λ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨isElliptic_mono hΛ0 h1 (hell W), fun x => (hB W x).trans h2, ?_, ?_⟩
  · intro x y ξ
    have hM : ∀ j l, |((G W).1 x - (G W).1 y) j l| ≤ Lm * euclideanNorm (x - y) := by
      intro j l
      exact (hLe j l W x y).trans (mul_le_mul_of_nonneg_right (hLle j l) (euclideanNorm_nonneg' _))
    have h := euclideanNorm_mulVec_le ((G W).1 x - (G W).1 y)
      (mul_nonneg hLm0 (euclideanNorm_nonneg' _)) hM ξ
    refine h.trans ?_
    have : (d : ℝ) * d * (Lm * euclideanNorm (x - y)) * euclideanNorm ξ =
        (d * d * Lm) * euclideanNorm (x - y) * euclideanNorm ξ := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h3 (euclideanNorm_nonneg' _)) (euclideanNorm_nonneg' _)
  · intro x y
    exact (hLp W x y).trans (mul_le_mul_of_nonneg_right h4 (euclideanNorm_nonneg' _))

end EinsteinFull.Calculus.S1
