import EinsteinFull.Calculus.ParabolicLibraryBridgeOscillation

/-!
# One step of oscillation reduction in the unit cylinder
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter PDE

/-- If `m ≤ u ≤ M` a.e. on `B₁ × (-1, 0]` for a weak solution, then on `B_{1/2} × (-1/4, 0]`
the oscillation is at most `(1 - η)(M - m)`. -/
theorem osc_reduction (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      ∀ m M : ℝ, m ≤ M →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        m ≤ u.toFun z ∧ u.toFun z ≤ M) →
      ∃ m' M' : ℝ,
        (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0)),
          m' ≤ u.toFun z ∧ u.toFun z ≤ M') ∧ m ≤ m' ∧ M' ≤ M ∧ m' ≤ M' ∧
          M' - m' ≤ (1 - η) * (M - m) := by
  obtain ⟨η₀, hη₀, hH⟩ := weakHarnack_lower d hd Lam hLam
  refine ⟨min η₀ 1 / 2, by positivity, ?_, ?_⟩
  · have : min η₀ 1 ≤ 1 := min_le_right _ _
    linarith
  intro a ha u hu m M hmM hbd
  set Qm : Set (Vec d × ℝ) := euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2)
    with hQm
  have hsubQp : euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0 ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
    prod_mono (euclideanBall_mono (by norm_num) (by norm_num))
      (Ioc_subset_Ioc_left (by norm_num))
  have hbdQ := ae_restrict_of_ae_restrict_of_subset hsubQp hbd
  by_cases hω : M = m
  · refine ⟨m, M, hbdQ, le_rfl, le_rfl, hmM, ?_⟩
    rw [hω]
    simp
  have hωpos : 0 < M - m := sub_pos.mpr (lt_of_le_of_ne hmM (Ne.symm hω))
  set c : ℝ := (M - m) / 2 with hc
  have hcpos : 0 < c := by positivity
  have hI : MeasurableSet (Ioc (-1 : ℝ) 0) := measurableSet_Ioc
  have hfin : volume (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) ≠ ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top (volume_euclideanBall_ne_top _ zero_le_one) (by simp)
  have hηc : min η₀ 1 / 2 * (M - m) ≤ η₀ * c := by
    have h1 : min η₀ 1 ≤ η₀ := min_le_left _ _
    rw [hc]
    nlinarith
  by_cases hcase : volume Qm ≤ 2 * volume ({z | c ≤ M + (-1) * u.toFun z} ∩ Qm)
  · -- the upper side contracts
    have hw := isParabolicWeakSolution_affine hI hfin M (-1) u hu
    have hnn : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ (affineParH1 hI hfin M (-1) u).toFun z := by
      filter_upwards [hbd] with z hz
      show 0 ≤ M + (-1) * u.toFun z
      linarith [hz.2]
    have hlow := hH a ha _ hw hnn c hcpos hcase
    have hmin : min η₀ 1 / 2 ≤ 1 / 2 := by
      have := min_le_right η₀ 1
      linarith
    have hmin' := mul_le_mul_of_nonneg_right hmin hωpos.le
    refine ⟨m, M - min η₀ 1 / 2 * (M - m), ?_, le_rfl, ?_, ?_, ?_⟩
    · filter_upwards [hlow, hbdQ] with z hz1 hz2
      have hz1' : η₀ * c ≤ M + (-1) * u.toFun z := hz1
      exact ⟨hz2.1, by linarith⟩
    · have : 0 ≤ min η₀ 1 / 2 * (M - m) := by positivity
      linarith
    · linarith
    · linarith
  · -- the lower side contracts
    have hcase' : ¬ volume Qm ≤ 2 * volume ({z | c ≤ M + (-1) * u.toFun z} ∩ Qm) := hcase
    have hw := isParabolicWeakSolution_affine hI hfin (-m) 1 u hu
    have hnn : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ (affineParH1 hI hfin (-m) 1 u).toFun z := by
      filter_upwards [hbd] with z hz
      show 0 ≤ -m + 1 * u.toFun z
      linarith [hz.1]
    have hcover : volume Qm ≤ volume ({z | c ≤ M + (-1) * u.toFun z} ∩ Qm) +
        volume ({z | c ≤ -m + 1 * u.toFun z} ∩ Qm) := by
      have hsub : Qm ⊆ ({z | c ≤ M + (-1) * u.toFun z} ∩ Qm) ∪
          ({z | c ≤ -m + 1 * u.toFun z} ∩ Qm) := by
        intro z hz
        by_cases h : u.toFun z ≤ (M + m) / 2
        · exact Or.inl ⟨by simp only [mem_setOf_eq, hc]; linarith, hz⟩
        · exact Or.inr ⟨by simp only [mem_setOf_eq, hc]; push Not at h; linarith, hz⟩
      exact (measure_mono hsub).trans (measure_union_le _ _)
    have hVfin : volume Qm ≠ ⊤ := by
      rw [hQm, Measure.volume_eq_prod, Measure.prod_prod]
      exact ENNReal.mul_ne_top (volume_euclideanBall_ne_top _ (by norm_num)) (by simp)
    have hcase2 : volume Qm ≤ 2 * volume ({z | c ≤ -m + 1 * u.toFun z} ∩ Qm) := by
      by_contra h2
      have h1' := not_le.mp hcase'
      have h2' := not_le.mp h2
      have h3 : 2 * volume Qm ≤ 2 * volume ({z | c ≤ M + (-1) * u.toFun z} ∩ Qm) +
          2 * volume ({z | c ≤ -m + 1 * u.toFun z} ∩ Qm) := by
        calc 2 * volume Qm ≤ 2 * (volume ({z | c ≤ M + (-1) * u.toFun z} ∩ Qm) +
            volume ({z | c ≤ -m + 1 * u.toFun z} ∩ Qm)) := mul_le_mul' le_rfl hcover
          _ = _ := by ring
      have h4 := ENNReal.add_lt_add h1' h2'
      rw [← two_mul] at h4
      exact absurd (h3.trans_lt h4) (lt_irrefl _)
    have hlow := hH a ha _ hw hnn c hcpos hcase2
    have hmin : min η₀ 1 / 2 ≤ 1 / 2 := by
      have := min_le_right η₀ 1
      linarith
    have hmin' := mul_le_mul_of_nonneg_right hmin hωpos.le
    refine ⟨m + min η₀ 1 / 2 * (M - m), M, ?_, ?_, le_rfl, ?_, ?_⟩
    · filter_upwards [hlow, hbdQ] with z hz1 hz2
      have hz1' : η₀ * c ≤ -m + 1 * u.toFun z := hz1
      exact ⟨by linarith, hz2.2⟩
    · have : 0 ≤ min η₀ 1 / 2 * (M - m) := by positivity
      linarith
    · linarith
    · linarith

end EinsteinFull.ParabolicBridge
