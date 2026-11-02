import EinsteinFull.Calculus.C9TubeNativeHarnackComparison

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat

noncomputable section
namespace EinsteinFull.Calculus

/-- Uniform parabolic-scale diagonal control from interior survival and the
uniform second moment of the actual spectral kernel. -/
theorem c18_native_uniform_diagonal_of_mass_moment
    (d : ℕ) (hd : 2 ≤ d) (κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ c η : ℝ, 0 < c ∧ 0 < η ∧ ∀ R : ℝ, 0 < R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r t : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < t → t ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K t x y) →
    ∀ (x : Vec d) (r t : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
    0 < t → t ≤ η*r^2 →
    c * Real.rpow t (-(d : ℝ)/2) ≤ K (2*t) x x / ρ x := by
  obtain ⟨M, hM, hmoment⟩ := c9_native_second_moment_uniform_radius hd κ hκ
  let a : ℝ := 2 * (M+1)
  have ha : 0 < a := by dsimp [a]; positivity
  have haM : 4*M ≤ a^2 := by dsimp [a]; nlinarith [sq_nonneg M]
  let V : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal
  have hV : 0 < V := volume_euclideanBall_toReal_pos 0 (by norm_num)
  let D : ℝ := κ⁻¹ * (a^d * V)
  have hD : 0 < D := by dsimp [D]; positivity
  let η : ℝ := min δ (1 / a^2)
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨(1/16) / D, η, div_pos (by norm_num) hD, hη, ?_⟩
  intro R hR ρ α hell K G hK hmass x r t hr hinside ht htime
  have htr : t ≤ δ*r^2 := by
    exact htime.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg r))
  have hta : t ≤ (1 / a^2)*r^2 := by
    exact htime.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg r))
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs2 : (Real.sqrt t)^2 = t := Real.sq_sqrt ht.le
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hsq : (a * Real.sqrt t)^2 = a^2*t := by rw [mul_pow, hs2]
  have hscale : a * Real.sqrt t ≤ 2*r := by
    have hta' : a^2*t ≤ r^2 := by
      have hh : t ≤ r^2 / a^2 := by simpa [div_eq_mul_inv, mul_comm] using hta
      have hh' := (le_div_iff₀ ha2).1 hh
      nlinarith
    rw [← hsq] at hta'
    nlinarith [sq_nonneg (a * Real.sqrt t - r)]
  have hrad : 0 < a * Real.sqrt t := mul_pos ha hs
  have hball : sourceBall x (a * Real.sqrt t) ⊆ sourceBall 0 R := by
    apply Set.Subset.trans _ hinside
    intro y hy
    change Real.sqrt (euclideanSq (y-x)) < a * Real.sqrt t at hy
    change Real.sqrt (euclideanSq (y-x)) < 2*r
    exact lt_of_lt_of_le hy hscale
  have hx : x ∈ sourceBall 0 R := hball (by
    rw [c8_sourceBall_eq_euclideanBall x hrad]
    exact PDE.center_mem_euclideanBall x hrad)
  have hquot : M*t / (a * Real.sqrt t)^2 ≤ (1/4 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hrad)).2
    rw [hsq]
    nlinarith [mul_nonneg (sub_nonneg.mpr haM) ht.le]
  have hdiag := c18_native_spectral_local_diagonal_from_moment_bound hd hκ hR
    ρ α hell K G hK t ht x hx (a * Real.sqrt t) hrad hball
    (1/2) (M*t) (by linarith) (hmass x r t hr hinside ht htr)
    (hmoment R hR ρ α hell K G hK t ht x hx)
  have hnum : (1/16 : ℝ) ≤ (1/2 - M*t / (a * Real.sqrt t)^2)^2 := by
    nlinarith [sq_nonneg (1/2 - M*t / (a * Real.sqrt t)^2 - 1/4)]
  have hp : (Real.sqrt t)^d = Real.rpow t ((d : ℝ)/2) := by
    rw [Real.rpow_eq_pow]
    simpa only [Real.rpow_natCast] using
      (Real.rpow_div_two_eq_sqrt (d : ℝ) ht.le).symm
  have hpow : 0 < Real.rpow t ((d : ℝ)/2) := Real.rpow_pos_of_pos ht _
  have hden : κ⁻¹ * ((a * Real.sqrt t)^d * V) = D * Real.rpow t ((d : ℝ)/2) := by
    rw [mul_pow, hp]; dsimp [D]; ring
  have hbound : (1/16 : ℝ) / (D * Real.rpow t ((d : ℝ)/2)) ≤ K (2*t) x x / ρ x := by
    apply (div_le_div_of_nonneg_right hnum (mul_pos hD hpow).le).trans
    change (1/2 - M*t / (a * Real.sqrt t)^2)^2 /
      (κ⁻¹ * ((a * Real.sqrt t)^d * V)) ≤ K (2*t) x x / ρ x at hdiag
    rw [hden] at hdiag
    exact hdiag
  have hneg : Real.rpow t (-(d : ℝ)/2) = (Real.rpow t ((d : ℝ)/2))⁻¹ := by
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow, neg_div, Real.rpow_neg ht.le]
  rw [hneg]
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hbound

end EinsteinFull.Calculus
