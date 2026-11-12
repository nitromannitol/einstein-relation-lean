import EinsteinRelation.Correctors.PoissonLiftWeakSolution

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Inside the lifted unit ball, clipping agrees with the normalized bounded Hölder source.
Source: `paper/main.tex:735-739`. -/
theorem exists_holderBound_clippedPoissonSource_lift {d : ℕ}
    (F : Vec d → Vec d) (α K M : ℝ) (hα : 0 ≤ α) (hM : 0 < M)
    (hFn : ∀ x ∈ ball (0 : Vec d) 1, euclideanNorm (F x) ≤ M)
    (hF : ∀ i, HolderBound (ball 0 1) α (fun x => F x i) K) :
    ∃ C : ℝ, ∀ i, HolderBound (ball (0 : Vec (d + 1)) 1) α
      (fun x => clippedPoissonSource F M (poissonLiftBase x) i) C := by
  -- euclideanNorm is nonnegative (polymorphic over dimension)
  have h_norm_nonneg {d' : ℕ} (x : Vec d') : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  -- poissonLiftBase is linear: poissonLiftBase (x - y) = poissonLiftBase x - poissonLiftBase y
  have h_linear (x y : Vec (d + 1)) : poissonLiftBase (x - y) = poissonLiftBase x - poissonLiftBase y := by
    ext i
    simp [poissonLiftBase, Pi.sub_apply, sub_eq_add_neg]
  -- norm of poissonLiftBase of a difference is bounded by norm of the difference
  have h_norm_diff (x y : Vec (d + 1)) :
      euclideanNorm (poissonLiftBase x - poissonLiftBase y) ≤ euclideanNorm (x - y) := by
    rw [← h_linear x y]
    exact euclideanNorm_poissonLiftBase_le (x - y)
  -- if x is in the lifted unit ball, its base projection is in the base unit ball
  have h_base_mem (x : Vec (d + 1)) (hx : x ∈ ball (0 : Vec (d + 1)) 1) :
      poissonLiftBase x ∈ ball (0 : Vec d) 1 := by
    have hx_norm : euclideanNorm x < 1 := by
      simpa [ball, sub_zero] using hx
    have : euclideanNorm (poissonLiftBase x - 0) < 1 := by
      rw [sub_zero]
      exact (euclideanNorm_poissonLiftBase_le x).trans_lt hx_norm
    simpa [ball, sub_zero] using this
  -- take C = M⁻¹ * K; this works uniformly for all i
  refine ⟨M⁻¹ * K, fun i => ?_⟩
  rcases hF i with ⟨S, H, hS, hH, hSH, h_sup, h_hold⟩
  have h_inv_nonneg : 0 ≤ M⁻¹ := inv_nonneg.mpr hM.le
  have h_inv_pos : 0 < M⁻¹ := inv_pos.mpr hM
  refine ⟨M⁻¹ * S, M⁻¹ * H, mul_nonneg h_inv_nonneg hS,
    mul_nonneg h_inv_nonneg hH, ?_, ?_, ?_⟩
  · -- S' + H' ≤ M⁻¹ * K
    calc
      M⁻¹ * S + M⁻¹ * H = M⁻¹ * (S + H) := by ring
      _ ≤ M⁻¹ * K := mul_le_mul_of_nonneg_left hSH h_inv_nonneg
  · -- sup norm bound
    intro x hx
    have hx_base : poissonLiftBase x ∈ ball (0 : Vec d) 1 := h_base_mem x hx
    have hclip : clippedPoissonSource F M (poissonLiftBase x) = M⁻¹ • F (poissonLiftBase x) := by
      unfold clippedPoissonSource
      rw [if_pos (hFn (poissonLiftBase x) hx_base)]
    dsimp
    rw [hclip]
    -- goal: |(M⁻¹ • F (poissonLiftBase x)) i| ≤ M⁻¹ * S
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos h_inv_pos]
    -- goal: M⁻¹ * |F (poissonLiftBase x) i| ≤ M⁻¹ * S
    have h := h_sup (poissonLiftBase x) hx_base
    -- h: |(fun x => F x i) (poissonLiftBase x)| ≤ S  i.e.  |F (poissonLiftBase x) i| ≤ S
    apply mul_le_mul_of_nonneg_left
    · simpa using h
    · exact h_inv_nonneg
  · -- Hölder seminorm bound
    intro x hx y hy
    have hx_base : poissonLiftBase x ∈ ball (0 : Vec d) 1 := h_base_mem x hx
    have hy_base : poissonLiftBase y ∈ ball (0 : Vec d) 1 := h_base_mem y hy
    have hclip_x : clippedPoissonSource F M (poissonLiftBase x) = M⁻¹ • F (poissonLiftBase x) := by
      unfold clippedPoissonSource
      rw [if_pos (hFn (poissonLiftBase x) hx_base)]
    have hclip_y : clippedPoissonSource F M (poissonLiftBase y) = M⁻¹ • F (poissonLiftBase y) := by
      unfold clippedPoissonSource
      rw [if_pos (hFn (poissonLiftBase y) hy_base)]
    dsimp
    rw [hclip_x, hclip_y]
    -- goal: |(M⁻¹ • F (poissonLiftBase x)) i - (M⁻¹ • F (poissonLiftBase y)) i| ≤ M⁻¹ * H * euclideanNorm (x - y) ^ α
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    -- goal: |M⁻¹ * F (poissonLiftBase x) i - M⁻¹ * F (poissonLiftBase y) i| ≤ M⁻¹ * H * euclideanNorm (x - y) ^ α
    rw [← mul_sub, abs_mul, abs_of_pos h_inv_pos]
    -- goal: M⁻¹ * |F (poissonLiftBase x) i - F (poissonLiftBase y) i| ≤ M⁻¹ * H * euclideanNorm (x - y) ^ α
    have h := h_hold (poissonLiftBase x) hx_base (poissonLiftBase y) hy_base
    -- h: |(fun x => F x i) (poissonLiftBase x) - (fun x => F x i) (poissonLiftBase y)| ≤ H * euclideanNorm (poissonLiftBase x - poissonLiftBase y) ^ α
    -- i.e., |F (poissonLiftBase x) i - F (poissonLiftBase y) i| ≤ H * euclideanNorm (poissonLiftBase x - poissonLiftBase y) ^ α
    have h_pow : euclideanNorm (poissonLiftBase x - poissonLiftBase y) ^ α ≤ euclideanNorm (x - y) ^ α :=
      Real.rpow_le_rpow (h_norm_nonneg (poissonLiftBase x - poissonLiftBase y)) (h_norm_diff x y) hα
    calc
      M⁻¹ * |F (poissonLiftBase x) i - F (poissonLiftBase y) i|
          ≤ M⁻¹ * (H * euclideanNorm (poissonLiftBase x - poissonLiftBase y) ^ α) :=
        mul_le_mul_of_nonneg_left (by simpa using h) h_inv_nonneg
      _ = (M⁻¹ * H) * euclideanNorm (poissonLiftBase x - poissonLiftBase y) ^ α := by ring
      _ ≤ (M⁻¹ * H) * euclideanNorm (x - y) ^ α :=
        mul_le_mul_of_nonneg_left h_pow (mul_nonneg h_inv_nonneg hH)
end EinsteinRelation.Correctors
