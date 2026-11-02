import EinsteinFull.Calculus.S3AnnuliSupport

/-!
# Annulus increments of conditional expectations

Generic support for `p:tail#annuli`: for an increasing family of sub-σ-algebras `𝓕 n` of a
probability space, the increments `Δ_n = E_n - E_{n-1}` (`Δ_1 = E_1`) of the `L²` conditional
expectations of a complex class `U` are real and `𝓕 n`-measurable when `U` is a.e. real, centered
and in `L^p` when `U` is, and are uniformly small when `U` has local approximants.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull.AnnuliSupport

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : ℕ → MeasurableSpace Ω}

/-- `Δ_n = E_n - E_{n-1}` for `n ≠ 1` and `Δ_1 = E_1`. -/
noncomputable def annDelta (hm : ∀ n, 𝓕 n ≤ m0) (U : Lp ℂ 2 μ) (n : ℕ) : Lp ℂ 2 μ :=
  if n = 1 then (condExpL2 ℂ ℂ (hm 1) U : Lp ℂ 2 μ)
  else (condExpL2 ℂ ℂ (hm n) U : Lp ℂ 2 μ) - (condExpL2 ℂ ℂ (hm (n - 1)) U : Lp ℂ 2 μ)

theorem annDelta_real (hm : ∀ n, 𝓕 n ≤ m0) (hmono : Monotone 𝓕) (U : Lp ℂ 2 μ)
    (hU : ∀ᵐ ω ∂μ, (U ω).im = 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ f : Ω → ℝ, Measurable[𝓕 n] f ∧
      (fun ω => (f ω : ℂ)) =ᵐ[μ] (annDelta hm U n : Ω → ℂ) := by
  have hE : ∀ k : ℕ, Measurable[𝓕 k] (μ[fun ω => (U ω).re | 𝓕 k]) :=
    fun k => (stronglyMeasurable_condExp (m := 𝓕 k) (μ := μ)
      (f := fun ω => (U ω).re)).measurable
  have hE' := fun k : ℕ => condExpL2_real (hm k) U hU
  by_cases h1 : n = 1
  · subst h1
    refine ⟨μ[fun ω => (U ω).re | 𝓕 1], hE 1, ?_⟩
    rw [annDelta, if_pos rfl]
    exact hE' 1
  · refine ⟨μ[fun ω => (U ω).re | 𝓕 n] - μ[fun ω => (U ω).re | 𝓕 (n - 1)],
      (hE n).sub ((hE (n - 1)).mono (hmono (Nat.sub_le n 1)) le_rfl), ?_⟩
    have h3 := Lp.coeFn_sub (condExpL2 ℂ ℂ (hm n) U : Lp ℂ 2 μ)
      (condExpL2 ℂ ℂ (hm (n - 1)) U : Lp ℂ 2 μ)
    filter_upwards [hE' n, hE' (n - 1), h3] with ω h1' h2' h3'
    rw [annDelta, if_neg h1, h3']
    simp only [Pi.sub_apply, Complex.ofReal_sub]
    rw [← h1', ← h2']

theorem memLp_annDelta (hm : ∀ n, 𝓕 n ≤ m0) (U : Lp ℂ 2 μ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hU : MemLp (U : Ω → ℂ) p μ) (n : ℕ) : MemLp (annDelta hm U n : Ω → ℂ) p μ := by
  by_cases h1 : n = 1
  · rw [annDelta, if_pos h1]
    exact memLp_condExpL2 (hm 1) U hp hU
  · rw [annDelta, if_neg h1]
    exact MemLp.ae_eq (Lp.coeFn_sub _ _).symm
      ((memLp_condExpL2 (hm n) U hp hU).sub (memLp_condExpL2 (hm (n - 1)) U hp hU))

theorem integral_annDelta (hm : ∀ n, 𝓕 n ≤ m0) (U : Lp ℂ 2 μ)
    (hU0 : ∫ ω, (U : Ω → ℂ) ω ∂μ = 0) (n : ℕ) :
    ∫ ω, (annDelta hm U n : Ω → ℂ) ω ∂μ = 0 := by
  by_cases h1 : n = 1
  · rw [annDelta, if_pos h1, integral_condExpL2 (hm 1) U, hU0]
  · rw [annDelta, if_neg h1, integral_congr_ae (Lp.coeFn_sub _ _)]
    have i1 : Integrable (condExpL2 ℂ ℂ (hm n) U : Ω → ℂ) μ :=
      MemLp.integrable one_le_two (Lp.memLp (condExpL2 ℂ ℂ (hm n) U : Lp ℂ 2 μ))
    have i2 : Integrable (condExpL2 ℂ ℂ (hm (n - 1)) U : Ω → ℂ) μ :=
      MemLp.integrable one_le_two (Lp.memLp (condExpL2 ℂ ℂ (hm (n - 1)) U : Lp ℂ 2 μ))
    have e := integral_sub i1 i2
    simp only [Pi.sub_apply]
    rw [e, integral_condExpL2 (hm n) U, integral_condExpL2 (hm (n - 1)) U, sub_self]

theorem normp_annDelta_le_two_mul (hm : ∀ n, 𝓕 n ≤ m0) (U : Lp ℂ 2 μ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hUt : eLpNorm (U : Ω → ℂ) p μ ≠ ⊤) (n : ℕ) :
    (eLpNorm (annDelta hm U n : Ω → ℂ) p μ).toReal ≤ 2 * (eLpNorm (U : Ω → ℂ) p μ).toReal := by
  have h2 : (2 : ℝ≥0∞) * eLpNorm (U : Ω → ℂ) p μ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top hUt
  have key : eLpNorm (annDelta hm U n : Ω → ℂ) p μ ≤ 2 * eLpNorm (U : Ω → ℂ) p μ := by
    by_cases h1 : n = 1
    · rw [annDelta, if_pos h1]
      exact (eLpNorm_condExpL2_le (hm 1) U hp).trans
        (by rw [two_mul]; exact le_self_add)
    · rw [annDelta, if_neg h1, eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
      have a1 := eLpNorm_condExpL2_le (hm n) U hp
      have a2 := eLpNorm_condExpL2_le (hm (n - 1)) U hp
      have a3 := eLpNorm_sub_le (f := (condExpL2 ℂ ℂ (hm n) U : Ω → ℂ))
        (g := (condExpL2 ℂ ℂ (hm (n - 1)) U : Ω → ℂ)) (p := p) (μ := μ) hp
      calc _ ≤ _ := a3
        _ ≤ eLpNorm (U : Ω → ℂ) p μ + eLpNorm (U : Ω → ℂ) p μ := add_le_add a1 a2
        _ = 2 * eLpNorm (U : Ω → ℂ) p μ := (two_mul _).symm
  have := ENNReal.toReal_mono h2 key
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this

theorem ae_norm_annDelta_le (hm : ∀ n, 𝓕 n ≤ m0) (U : Lp ℂ 2 μ) (𝓖 : ℕ → MeasurableSpace Ω)
    (h𝓖 : ∀ n, 𝓖 n ≤ 𝓕 n) (ε : ℕ → ℝ)
    (happ : ∀ n, 1 ≤ n → ∃ V : Ω → ℂ, Measurable[𝓖 n] V ∧
      ∀ᵐ ω ∂μ, ‖U ω - V ω‖ ≤ ε n) {n : ℕ} (hn : 2 ≤ n) :
    ∀ᵐ ω ∂μ, ‖(annDelta hm U n : Ω → ℂ) ω‖ ≤ 2 * ε n + 2 * ε (n - 1) := by
  obtain ⟨V₁, hV₁, h1⟩ := happ n (by omega)
  obtain ⟨V₂, hV₂, h2⟩ := happ (n - 1) (by omega)
  have a1 := ae_norm_condExpL2_sub_le (hm n) (h𝓖 n) U V₁ hV₁ h1
  have a2 := ae_norm_condExpL2_sub_le (hm (n - 1)) (h𝓖 (n - 1)) U V₂ hV₂ h2
  have h3 := Lp.coeFn_sub (condExpL2 ℂ ℂ (hm n) U : Lp ℂ 2 μ)
    (condExpL2 ℂ ℂ (hm (n - 1)) U : Lp ℂ 2 μ)
  filter_upwards [a1, a2, h3] with ω b1 b2 b3
  have e1 : n ≠ 1 := by omega
  rw [annDelta, if_neg e1, b3, Pi.sub_apply]
  calc ‖(condExpL2 ℂ ℂ (hm n) U : Ω → ℂ) ω - (condExpL2 ℂ ℂ (hm (n - 1)) U : Ω → ℂ) ω‖
      = ‖((condExpL2 ℂ ℂ (hm n) U : Ω → ℂ) ω - U ω) -
          ((condExpL2 ℂ ℂ (hm (n - 1)) U : Ω → ℂ) ω - U ω)‖ := by congr 1; ring
    _ ≤ ‖(condExpL2 ℂ ℂ (hm n) U : Ω → ℂ) ω - U ω‖ +
          ‖(condExpL2 ℂ ℂ (hm (n - 1)) U : Ω → ℂ) ω - U ω‖ := norm_sub_le _ _
    _ ≤ 2 * ε n + 2 * ε (n - 1) := add_le_add b1 b2

theorem normp_annDelta_le_of_approx (hm : ∀ n, 𝓕 n ≤ m0) (U : Lp ℂ 2 μ)
    (𝓖 : ℕ → MeasurableSpace Ω) (h𝓖 : ∀ n, 𝓖 n ≤ 𝓕 n) (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n)
    (happ : ∀ n, 1 ≤ n → ∃ V : Ω → ℂ, Measurable[𝓖 n] V ∧
      ∀ᵐ ω ∂μ, ‖U ω - V ω‖ ≤ ε n) {p : ℝ≥0∞} {n : ℕ} (hn : 2 ≤ n) :
    (eLpNorm (annDelta hm U n : Ω → ℂ) p μ).toReal ≤ 2 * ε n + 2 * ε (n - 1) :=
  eLpNorm_toReal_le_of_ae_norm_le (Lp.memLp (annDelta hm U n)).aestronglyMeasurable
    (by linarith [hε n, hε (n - 1)]) (ae_norm_annDelta_le hm U 𝓖 h𝓖 ε happ hn)

end EinsteinFull.AnnuliSupport
