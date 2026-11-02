import EinsteinFull.Calculus.C11TubeNativeLocalMaxAssembly
import EinsteinFull.Calculus.SbxBWeightedUnitGainR01

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- A weighted-caloric function satisfies the unit-cylinder local maximum
estimate, with a constant depending only on the dimension and ellipticity. -/
theorem b_weighted_unit_L2_local_max
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ)
    (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      eLpNorm u ⊤ (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
        ENNReal.ofReal C * eLpNorm u 2
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) := by
  have hSignedGain := b_weighted_signed_unit_gain d hd κ hκ
  let c : ℝ := ((d : ℝ) + 2) / d
  let s : ℝ := 2 / d
  let ν : ℕ → Measure (ℝ × Vec d) := fun n =>
    volume.restrict (Set.Ioo (-(1/4) - 3/(4*(2:ℝ)^n)) (1/4 + 3/(4*(2:ℝ)^n)) ×ˢ
      sourceBall 0 (1/2 + 1/(2*(2:ℝ)^n)))
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc : c = 1 + s := by dsimp [c, s]; field_simp
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hc1 : 1 ≤ c := by rw [hc]; linarith
  obtain ⟨N₀, B₀, hcover⟩ := c11_dyadic_moment_gain_of_uniform_local_norm_gain d
  obtain ⟨C₀, hC₀, hlocal⟩ := c11_dyadic_local_signed_gain_cancelled d κ hSignedGain
  let N : ℝ := (N₀ : ℝ) + 1
  let B : ℝ := (B₀ : ℝ) + 1
  let C : ℝ := max C₀ 1
  have hN : 1 ≤ N := by
    dsimp [N]
    have hn : 0 ≤ (N₀ : ℝ) := Nat.cast_nonneg _
    linarith
  have hB : 1 ≤ B := by
    dsimp [B]
    have hn : 0 ≤ (B₀ : ℝ) := Nat.cast_nonneg _
    linarith
  have hC : 1 ≤ C := le_max_right _ _
  obtain ⟨A, b, hA, hb, hcoef⟩ :=
    c11_dyadic_signed_gain_coefficient_bound N B C c hN hB hC hc1
  apply c11_native_unit_L2_local_max_of_signed_moment_gain d hd κ
  change ∃ A' b' : ℝ, 1 ≤ A' ∧ 1 < b' ∧
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    ∃ K B' E : ℕ → ℝ≥0∞,
      (∀ n, (K n * B' n ^ s * E n) ^ (1 / ((2 * c ^ n) * (1+s))) ≤
        ENNReal.ofReal (Real.rpow (A' * Real.rpow b' (n : ℝ))
          (1 / (2 * Real.rpow c (n : ℝ))))) ∧
      (∀ n, (∫⁻ x, ‖u x‖ₑ ^ ((2 * c ^ n) * (1+s)) ∂(ν (n+1))) ≤
        K n * (B' n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))) ^ s *
          (E n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))))
  refine ⟨A, b, hA, hb, ?_⟩
  intro ρ α hell u G hcal
  let p : ℕ → ℝ := fun n => 2 * c ^ n
  let r : ℕ → ℝ := fun n => 1/(8*(2:ℝ)^n)
  let T : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Real.rpow (r n) (-(2 / p n))) *
      ENNReal.ofReal (Real.rpow (C * (p n)^2) (1 / p n))
  let K : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (N * B^n) * T n ^ (p n * c)
  refine ⟨K, fun _ => 1, fun _ => 1, ?_, ?_⟩
  · intro n
    have hh := hcoef n
    simpa only [K, T, p, r, ← hc, ENNReal.one_rpow, mul_one, Real.rpow_eq_pow, Real.rpow_natCast] using hh
  · intro n
    have hp : 2 ≤ p n := by
      dsimp [p]
      have hh : 1 ≤ c ^ n := one_le_pow₀ hc1
      nlinarith
    have hp0 : 0 < p n := by linarith
    have hr : 0 < r n := by dsimp [r]; positivity
    have hmeas : AEStronglyMeasurable u (ν n) :=
      hcal.1.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono_set volume (c11_moser_dyadic_cylinder_containment d n).2)
    have hloc : ∀ y ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)),
        let μ := volume.restrict (Set.Ioo (y.1 - (r n)^2/4) (y.1 + (r n)^2/4) ×ˢ
          sourceBall y.2 ((r n)/2))
        AEStronglyMeasurable u μ ∧ eLpNorm u (ENNReal.ofReal (p n * (1+s))) μ ≤
          T n * eLpNorm u (ENNReal.ofReal (p n)) (ν n) := by
      intro y hy
      constructor
      · exact hmeas.mono_measure (Measure.restrict_mono_set volume
          (c11_dyadic_inner_local_containment d n y.1 y.2 hy))
      · have hg := hlocal ρ α hell u G hcal n y.1 y.2 hy (p n) hp
        dsimp only at hg
        rw [c11_signed_jacobian_scale d hd0 (p n) (r n) hp0 hr] at hg
        have hq : p n * ((d : ℝ) + 2) / d = p n * (1+s) := by rw [← hc]; dsimp [c]; ring
        rw [hq] at hg
        apply hg.trans
        dsimp only [T, ν]
        apply mul_le_mul_left
        apply mul_le_mul_right
        apply ENNReal.ofReal_le_ofReal
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        apply mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have hmoment := hcover n u (p n) s hp0 hs (T n) hmeas hloc
    have hcard : (↑(N₀ * B₀ ^ n) : ℝ≥0∞) ≤ ENNReal.ofReal (N * B ^ n) := by
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      push_cast
      gcongr <;> dsimp [N, B] <;> linarith
    have hbound := hmoment.trans (mul_le_mul_left hcard _)
    rw [c11_dyadic_inner_cylinder_eq_next] at hbound
    simpa only [K, p, ν, hc, one_mul, mul_one, mul_assoc] using hbound

end EinsteinFull.Calculus
