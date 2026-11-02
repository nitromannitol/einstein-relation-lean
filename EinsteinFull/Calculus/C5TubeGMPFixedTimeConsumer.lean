import EinsteinFull.External.GMPDirichletLower

open EinsteinRelation
open EinsteinFull.External.Source.GMP

namespace EinsteinFull

/-- One ellipticity parameter works for all translations and all time scales
in a fixed positive compact interval. -/
theorem c5_uniform_translated_time_scaled_ellipticity {d : ℕ}
    {κ τlo τhi : ℝ} (hκ : 0 < κ) (hlo : 0 < τlo) (hwindow : τlo ≤ τhi)
    {τ : ℝ} (hτ : τ ∈ Set.Icc τlo τhi) (z₀ : Vec d)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α) :
    IsUniformlyElliptic (min κ (min (τlo * κ) (κ / τhi)))
      (fun z => ρ (z + z₀)) (fun z => τ • α (z + z₀)) := by
  let k := min κ (min (τlo * κ) (κ / τhi))
  have hhi : 0 < τhi := lt_of_lt_of_le hlo hwindow
  have ht : 0 < τ := lt_of_lt_of_le hlo hτ.1
  have hk : 0 < k := lt_min hκ (lt_min (mul_pos hlo hκ) (div_pos hκ hhi))
  have hk1 : k ≤ κ := min_le_left _ _
  have hk2 : k ≤ τ * κ := ((min_le_right κ _).trans (min_le_left _ _)).trans
    (mul_le_mul_of_nonneg_right hτ.1 hκ.le)
  have hk3 : k ≤ κ / τhi := (min_le_right κ _).trans (min_le_right _ _)
  have hkinv : κ⁻¹ ≤ k⁻¹ := inv_anti₀ hk hk1
  have hkinvτ : τ * κ⁻¹ ≤ k⁻¹ := by
    have hh := inv_anti₀ hk hk3
    have htinv : τ * κ⁻¹ ≤ τhi * κ⁻¹ := mul_le_mul_of_nonneg_right hτ.2 (inv_nonneg.mpr hκ.le)
    have heq : (κ / τhi)⁻¹ = τhi * κ⁻¹ := by
      rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
    rw [heq] at hh
    exact htinv.trans hh
  have hz : Continuous (fun z : Vec d => z + z₀) := continuous_id.add continuous_const
  refine ⟨h.1.comp hz.measurable, ?_, ?_⟩
  · let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
    let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
    exact (show Continuous (fun a : Mat d => τ • a) from continuous_const_smul τ).measurable.comp
      (h.2.1.comp hz.measurable)
  · intro z
    refine ⟨hk1.trans (h.2.2 (z + z₀)).1, (h.2.2 (z + z₀)).2.1.trans hkinv, ?_, ?_⟩
    · rw [Matrix.transpose_smul, (h.2.2 (z + z₀)).2.2.1]
    · intro v
      have hs : 0 ≤ euclideanSq v := by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      have hd : dot v ((τ • α (z + z₀)).mulVec v) = τ * dot v ((α (z + z₀)).mulVec v) := by
        rw [Matrix.smul_mulVec]
        simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hd]
      constructor
      · calc
          k * euclideanSq v ≤ (τ * κ) * euclideanSq v := mul_le_mul_of_nonneg_right hk2 hs
          _ ≤ τ * dot v ((α (z + z₀)).mulVec v) := by
            nlinarith [mul_le_mul_of_nonneg_left ((h.2.2 (z + z₀)).2.2.2 v).1 ht.le]
      · calc
          τ * dot v ((α (z + z₀)).mulVec v) ≤ (τ * κ⁻¹) * euclideanSq v := by
            nlinarith [mul_le_mul_of_nonneg_left ((h.2.2 (z + z₀)).2.2.2 v).2 ht.le]
          _ ≤ k⁻¹ * euclideanSq v := mul_le_mul_of_nonneg_right hkinvτ hs

/-- GMP's lower constant is uniform over translated coefficients and a
compact positive window of time scalings, for genuine source kernels. -/
theorem c5_gmp_fixed_time_translated_coeff_consumer
    (d : ℕ) (hd : 0 < d) (κ R : ℝ) (hκ : 0 < κ) (hR : 0 < R)
    (center : Vec d) (radius : ℝ) (hradius : 0 < radius)
    (hball : euclideanNorm center + radius < R)
    (τlo τhi : ℝ) (hlo : 0 < τlo) (hwindow : τlo ≤ τhi) :
    ∃ kstar C : ℝ, 0 < kstar ∧ 0 < C ∧
      ∀ τ ∈ Set.Icc τlo τhi, ∀ (z₀ : Vec d) (ρ : Vec d → ℝ) (α : Vec d → Mat d),
        IsUniformlyElliptic κ ρ α →
        IsUniformlyElliptic kstar (fun z => ρ (z + z₀)) (fun z => τ • α (z + z₀)) ∧
        ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
          IsSpectralDirichletFundamentalSolution (fun z => ρ (z + z₀))
            (fun z => τ • α (z + z₀)) R K G →
          ∀ z ∈ sourceBall center radius, C ≤ K 1 z 0 := by
  let k := min κ (min (τlo * κ) (κ / τhi))
  have hk : 0 < k := lt_min hκ (lt_min (mul_pos hlo hκ)
    (div_pos hκ (lt_of_lt_of_le hlo hwindow)))
  obtain ⟨C, hC, hGMP⟩ := External.gmp_dirichlet_lower d hd k R hk hR center radius hradius hball
  refine ⟨k, C, hk, hC, ?_⟩
  intro τ hτ z₀ ρ α h
  have he := c5_uniform_translated_time_scaled_ellipticity hκ hlo hwindow hτ z₀ h
  exact ⟨he, fun K G hK => hGMP _ _ he K G hK⟩

end EinsteinFull
