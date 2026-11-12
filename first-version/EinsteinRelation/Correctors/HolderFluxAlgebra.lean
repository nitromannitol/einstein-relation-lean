import EinsteinRelation.External.GilbargTrudinger

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- The physical flux of bounded Hölder coefficients and gradients remains Hölder.
Source: `paper/main.tex:735-739`. -/
theorem exists_holderBound_mulVec {d : ℕ} (U : Set (Vec d))
    (α K H : ℝ) (a : Vec d → Mat d) (g : Vec d → Vec d)
    (ha : ∀ i j, HolderBound U α (fun x => a x i j) K)
    (hg : ∀ i, HolderBound U α (fun x => g x i) H) :
    ∃ C : ℝ, ∀ i, HolderBound U α (fun x => (a x).mulVec (g x) i) C := by
  -- Extract the supremum and Hölder constants from the hypotheses.
  by_cases hd : Nonempty (Fin d)
  · have hK_nonneg : 0 ≤ K := by
      rcases ha (Classical.choice hd) (Classical.choice hd) with ⟨S, H', _, _, hSH, _, _⟩
      linarith
    have hH_nonneg : 0 ≤ H := by
      rcases hg (Classical.choice hd) with ⟨S, H', _, _, hSH, _, _⟩
      linarith
    -- For each i j, get the Hölder bound components
    have ha_bound (i j : Fin d) : ∃ S H' : ℝ, 0 ≤ S ∧ 0 ≤ H' ∧ S + H' ≤ K ∧
        (∀ x ∈ U, |a x i j| ≤ S) ∧
        ∀ x ∈ U, ∀ y ∈ U, |a x i j - a y i j| ≤ H' * euclideanNorm (x - y) ^ α := ha i j
    have hg_bound (j : Fin d) : ∃ S H' : ℝ, 0 ≤ S ∧ 0 ≤ H' ∧ S + H' ≤ H ∧
        (∀ x ∈ U, |g x j| ≤ S) ∧
        ∀ x ∈ U, ∀ y ∈ U, |g x j - g y j| ≤ H' * euclideanNorm (x - y) ^ α := hg j
    -- Choose C = 3 * d * K * H (any finite bound works)
    refine ⟨3 * (d : ℝ) * K * H, λ i => ?_⟩
    -- Supremum part S' = d * K * H, Hölder seminorm part H' = 2 * d * K * H
    refine ⟨(d : ℝ) * K * H, 2 * (d : ℝ) * K * H, ?_, ?_, ?_, ?_, ?_⟩
    · -- 0 ≤ S'
      positivity
    · -- 0 ≤ H'
      positivity
    · -- S' + H' ≤ 3 * d * K * H
      have h_eq : (d : ℝ) * K * H + 2 * (d : ℝ) * K * H = 3 * (d : ℝ) * K * H := by ring
      linarith
    · -- Supremum bound: |(fun x => (a x).mulVec (g x) i) x| ≤ d * K * H for x ∈ U
      intro x hx
      have hsum : (a x).mulVec (g x) i = ∑ j : Fin d, (a x i j) * (g x j) := by
        simp [Matrix.mulVec, dotProduct]
      have hgoal : |(a x).mulVec (g x) i| ≤ (d : ℝ) * K * H := by
        rw [hsum]
        calc
          |∑ j : Fin d, (a x i j) * (g x j)| ≤ ∑ j : Fin d, |(a x i j) * (g x j)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j : Fin d, |a x i j| * |g x j| := by
            refine Finset.sum_congr rfl (λ j _ => ?_)
            rw [abs_mul]
          _ ≤ ∑ j : Fin d, K * H := by
            refine Finset.sum_le_sum (λ j _ => ?_)
            rcases ha_bound i j with ⟨S, H', hS, hH', hSH, hS_bound, hH_bound⟩
            rcases hg_bound j with ⟨Sg, Hg, hSg, hHg, hSgHg, hSg_bound, hHg_bound⟩
            have ha_le_K : |a x i j| ≤ K := by
              have ha_le_S : |a x i j| ≤ S := hS_bound x hx
              have hS_le_K : S ≤ K := by linarith
              linarith
            have hg_le_H : |g x j| ≤ H := by
              have hg_le_Sg : |g x j| ≤ Sg := hSg_bound x hx
              have hSg_le_H : Sg ≤ H := by linarith
              linarith
            exact mul_le_mul ha_le_K hg_le_H (abs_nonneg _) hK_nonneg
          _ = (d : ℝ) * K * H := by
            simp [Finset.sum_const]
            ring
      simpa using hgoal
    · -- Hölder seminorm bound
      intro x hx y hy
      have hsum_sub : (a x).mulVec (g x) i - (a y).mulVec (g y) i =
          (a x).mulVec (g x - g y) i + ((a x) - (a y)).mulVec (g y) i := by
        calc
          (a x).mulVec (g x) i - (a y).mulVec (g y) i =
              ((a x).mulVec (g x) i - (a x).mulVec (g y) i) +
              ((a x).mulVec (g y) i - (a y).mulVec (g y) i) := by ring
          _ = (a x).mulVec (g x - g y) i + ((a x) - (a y)).mulVec (g y) i := by
            simp [Matrix.mulVec_sub, Matrix.sub_mulVec]
      rw [hsum_sub]
      have h_nonneg_pow : ∀ (z : Vec d), 0 ≤ euclideanNorm z ^ α :=
        λ z => Real.rpow_nonneg (Real.sqrt_nonneg _) _
      calc
        |(a x).mulVec (g x - g y) i + ((a x) - (a y)).mulVec (g y) i| ≤
            |(a x).mulVec (g x - g y) i| + |((a x) - (a y)).mulVec (g y) i| :=
          abs_add_le _ _
        _ = |∑ j : Fin d, (a x i j) * ((g x - g y) j)| +
            |∑ j : Fin d, ((a x - a y) i j) * (g y j)| := by
          simp [Matrix.mulVec, dotProduct]
        _ = |∑ j : Fin d, (a x i j) * (g x j - g y j)| +
            |∑ j : Fin d, (a x i j - a y i j) * (g y j)| := by
          simp [Pi.sub_apply]
        _ ≤ (∑ j : Fin d, |a x i j| * |g x j - g y j|) +
            (∑ j : Fin d, |a x i j - a y i j| * |g y j|) := by
          refine add_le_add ?_ ?_
          · calc
              |∑ j : Fin d, (a x i j) * (g x j - g y j)| ≤
                  ∑ j : Fin d, |(a x i j) * (g x j - g y j)| := Finset.abs_sum_le_sum_abs _ _
              _ = ∑ j : Fin d, |a x i j| * |g x j - g y j| := by
                refine Finset.sum_congr rfl (λ j _ => ?_)
                rw [abs_mul]
          · calc
              |∑ j : Fin d, (a x i j - a y i j) * (g y j)| ≤
                  ∑ j : Fin d, |(a x i j - a y i j) * (g y j)| := Finset.abs_sum_le_sum_abs _ _
              _ = ∑ j : Fin d, |a x i j - a y i j| * |g y j| := by
                refine Finset.sum_congr rfl (λ j _ => ?_)
                rw [abs_mul]
        _ ≤ (∑ j : Fin d, K * (H * euclideanNorm (x - y) ^ α)) +
            (∑ j : Fin d, K * euclideanNorm (x - y) ^ α * H) := by
          refine add_le_add ?_ ?_
          · refine Finset.sum_le_sum (λ j _ => ?_)
            rcases ha_bound i j with ⟨S, H', hS, hH', hSH, hS_bound, hH_bound⟩
            have ha_le_K : |a x i j| ≤ K := by
              have ha_le_S : |a x i j| ≤ S := hS_bound x hx
              have hS_le_K : S ≤ K := by linarith
              linarith
            rcases hg_bound j with ⟨Sg, Hg, hSg, hHg, hSgHg, hSg_bound, hHg_bound⟩
            have hg_diff_bound : |g x j - g y j| ≤ H * euclideanNorm (x - y) ^ α := by
              have hHg_bound' := hHg_bound x hx y hy
              have hHg'_le_H : Hg ≤ H := by linarith
              calc
                |g x j - g y j| ≤ Hg * euclideanNorm (x - y) ^ α := hHg_bound'
                _ ≤ H * euclideanNorm (x - y) ^ α :=
                  mul_le_mul_of_nonneg_right hHg'_le_H (h_nonneg_pow (x - y))
            exact mul_le_mul ha_le_K hg_diff_bound (abs_nonneg _) hK_nonneg
          · refine Finset.sum_le_sum (λ j _ => ?_)
            rcases ha_bound i j with ⟨S, H', hS, hH', hSH, hS_bound, hH_bound⟩
            have ha_diff_bound : |a x i j - a y i j| ≤ K * euclideanNorm (x - y) ^ α := by
              have hH_bound' := hH_bound x hx y hy
              have hH'_le_K : H' ≤ K := by linarith
              calc
                |a x i j - a y i j| ≤ H' * euclideanNorm (x - y) ^ α := hH_bound'
                _ ≤ K * euclideanNorm (x - y) ^ α :=
                  mul_le_mul_of_nonneg_right hH'_le_K (h_nonneg_pow (x - y))
            rcases hg_bound j with ⟨Sg, Hg, hSg, hHg, hSgHg, hSg_bound, hHg_bound⟩
            have hg_bound_y : |g y j| ≤ H := by
              have hSg_bound' := hSg_bound y hy
              have hSg_le_H : Sg ≤ H := by linarith
              linarith
            have h_nonneg : 0 ≤ K * euclideanNorm (x - y) ^ α :=
              mul_nonneg hK_nonneg (h_nonneg_pow (x - y))
            exact mul_le_mul ha_diff_bound hg_bound_y (abs_nonneg _) h_nonneg
        _ = ((d : ℝ) * (K * H) + (d : ℝ) * (K * H)) * euclideanNorm (x - y) ^ α := by
          simp [Finset.sum_const]
          ring
        _ = (2 * (d : ℝ) * K * H) * euclideanNorm (x - y) ^ α := by ring
  · -- d = 0 case: Fin d is empty, all sums are 0
    have h_empty : IsEmpty (Fin d) := not_nonempty_iff.mp hd
    refine ⟨0, λ i => ?_⟩
    exact h_empty.elim i

end EinsteinRelation.Correctors
