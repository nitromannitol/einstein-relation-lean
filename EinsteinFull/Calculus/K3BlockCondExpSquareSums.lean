import EinsteinFull.Frozen.ReducedLaw
import EinsteinFull.Work.W7.ClockFiniteRangeSupport
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import EinsteinFull.Calculus.K2LatticeColoredSum

/-! Helpers for the conditional block square sums: conditional expectations onto local
σ-algebras are local, `Lᵖ` and centred, and the lattice colour counts are bounded. -/

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Calculus.K3
open EinsteinRelation

/-- A conditional expectation onto a local σ-algebra is local, in `Lᵖ`, and centred. -/
theorem condExp_local_facts {d : ℕ} {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ]
    {p : ℝ} (hp : 1 ≤ p) (U : Set (Vec d)) {f : FieldPair d → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hmean : ∫ ω, f ω ∂μ = 0) :
    StronglyMeasurable[localSigma U] (μ[f | localSigma U]) ∧
      MemLp (μ[f | localSigma U]) (ENNReal.ofReal p) μ ∧
      ∫ ω, (μ[f | localSigma U]) ω ∂μ = 0 := by
  have hp' : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  refine ⟨stronglyMeasurable_condExp, hf.condExp hp', ?_⟩
  rw [integral_condExp (Probability.localSigma_le_borel U), hmean]

/-- The difference of conditional expectations onto nested local σ-algebras is local for the
larger one, in `Lᵖ`, and centred. -/
theorem condExp_sub_local_facts {d : ℕ} {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ]
    {p : ℝ} (hp : 1 ≤ p) {U W : Set (Vec d)} (hUW : U ⊆ W) {f : FieldPair d → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hmean : ∫ ω, f ω ∂μ = 0) :
    StronglyMeasurable[localSigma W]
        (μ[f | localSigma W] - μ[f | localSigma U]) ∧
      MemLp (μ[f | localSigma W] - μ[f | localSigma U])
        (ENNReal.ofReal p) μ ∧
      ∫ ω, (μ[f | localSigma W] - μ[f | localSigma U]) ω ∂μ = 0 := by
  obtain ⟨hsW, hLW, hIW⟩ := condExp_local_facts (μ := μ) hp W hf hmean
  obtain ⟨hsU, hLU, hIU⟩ := condExp_local_facts (μ := μ) hp U hf hmean
  refine ⟨hsW.sub (hsU.mono (Probability.localSigma_mono hUW)), hLW.sub hLU, ?_⟩
  have hiW : Integrable (μ[f | localSigma W]) μ := integrable_condExp
  have hiU : Integrable (μ[f | localSigma U]) μ := integrable_condExp
  have := integral_sub hiW hiU
  simp only [Pi.sub_apply]
  rw [this, hIW, hIU, sub_zero]

/-- A colour count `M` with `B r + r₀ < M r` and `M ≤ B + r₀ + 2`. -/
theorem exists_color_count {B r r₀ : ℝ} (hB : 0 ≤ B) (hr : 1 ≤ r) (hr₀ : 0 ≤ r₀) :
    ∃ M : ℕ, B * r + r₀ < M * r ∧ (M : ℝ) ≤ B + r₀ + 2 := by
  refine ⟨⌈B + r₀⌉₊ + 1, ?_, ?_⟩
  · have h1 : B + r₀ ≤ (⌈B + r₀⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    nlinarith
  · have h1 : (⌈B + r₀⌉₊ : ℝ) < B + r₀ + 1 := Nat.ceil_lt_add_one (by positivity)
    push_cast
    linarith

/-- Power bound for a colour count that is at most `2 ^ n * C`. -/
theorem rpow_color_count_le {d n : ℕ} {M : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hM : (M : ℝ) ≤ 2 ^ n * C) :
    (M : ℝ) ^ ((d : ℝ) / 2) ≤ C ^ ((d : ℝ) / 2) * 2 ^ ((n : ℝ) * (d : ℝ) / 2) := by
  have h0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  calc (M : ℝ) ^ ((d : ℝ) / 2) ≤ (2 ^ n * C) ^ ((d : ℝ) / 2) :=
        Real.rpow_le_rpow h0 hM (by positivity)
    _ = C ^ ((d : ℝ) / 2) * 2 ^ ((n : ℝ) * (d : ℝ) / 2) := by
        rw [Real.mul_rpow (by positivity) hC, mul_comm]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1; ring


/-- Colour-count constant `2 C_p (8R + r₀ + 2)^{d/2}` of the square-sum bounds for the conditional
blocks and their annular increments. -/
noncomputable def blockColorConst (d : ℕ) (p r₀ R : ℝ) : ℝ :=
  2 * K1.lpSqConst p * (8 * R + r₀ + 2) ^ ((d : ℝ) / 2)

theorem block_condExp_square_sums {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {p r R : ℝ} (hp : 2 ≤ p) (hr : 1 ≤ r) (hR : 0 ≤ R)
    (X : (Fin d → ℤ) → FieldPair d → ℂ)
    (hX : ∀ z, MemLp (X z) (ENNReal.ofReal p) (reducedLaw Q))
    (hX0 : ∀ z, ∫ ω, X z ω ∂(reducedLaw Q) = 0) :
    let center := fun (z : Fin d → ℤ) (j : Fin d) => r * (z j : ℝ)
    let CE := fun (n : ℕ) (z : Fin d → ℤ) => (reducedLaw Q)[X z | localSigma
      {y : Vec d | euclideanNorm (y - center z) < R * 2 ^ (n + 1) * r}]
    let A := fun (n : ℕ) (z : Fin d → ℤ) => CE (n + 1) z - CE n z
    let N := fun f : FieldPair d → ℂ => (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal
    (∀ Λ : Finset (Fin d → ℤ),
      N (∑ z ∈ Λ, CE 0 z) ≤ blockColorConst d p r₀ R * Real.sqrt (∑ z ∈ Λ, (N (CE 0 z)) ^ 2)) ∧
    (∀ (n : ℕ) (Λ : Finset (Fin d → ℤ)),
      N (∑ z ∈ Λ, A n z) ≤ blockColorConst d p r₀ R * 2 ^ ((n : ℝ) * (d : ℝ) / 2) *
        Real.sqrt (∑ z ∈ Λ, (N (A n z)) ^ 2)) := by
  intro center CE A N
  have hprob : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hfr := reducedLaw_hasFiniteRange Q
  have hr₀ : 0 ≤ r₀ := by linarith [Q.range_parameter]
  have hr0 : 0 < r := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hC : 0 ≤ K1.lpSqConst p := by
    unfold K1.lpSqConst Homogenization.IndependentSums.rosenthalBennettIntegralConst
    have : 0 ≤ p := by linarith
    positivity
  have hE : 0 ≤ 8 * R + r₀ + 2 := by positivity
  refine ⟨fun Λ => ?_, fun n Λ => ?_⟩
  · obtain ⟨M, hM1, hM2⟩ := exists_color_count (B := 4 * R) (by positivity) hr hr₀
    have hMle : (M : ℝ) ≤ 2 ^ 0 * (8 * R + r₀ + 2) := by
      rw [pow_zero, one_mul]; linarith
    have hpow := rpow_color_count_le (d := d) hE hMle
    have hfacts := fun z => condExp_local_facts (μ := reducedLaw Q) hp1
      {y : Vec d | euclideanNorm (y - center z) < R * 2 ^ (0 + 1) * r} (hX z) (hX0 z)
    have hcol : 2 * (R * 2 ^ (0 + 1) * r) + r₀ < M * r := by
      have : 2 * (R * 2 ^ (0 + 1) * r) = 4 * R * r := by ring
      rw [this]; exact hM1
    have key : N (∑ z ∈ Λ, CE 0 z) ≤ 2 * K1.lpSqConst p * (M : ℝ) ^ ((d : ℝ) / 2) *
        Real.sqrt (∑ z ∈ Λ, (N (CE 0 z)) ^ 2) :=
      K2.lattice_local_eLpNorm_sum_le hfr hr₀ (r := r) (ρ := R * 2 ^ (0 + 1) * r) (p := p)
        hr0 (by positivity) hp M hcol
        (fun z => CE 0 z) (fun z => (hfacts z).1) (fun z => (hfacts z).2.1)
        (fun z => (hfacts z).2.2) Λ
    refine key.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    unfold blockColorConst
    have := mul_le_mul_of_nonneg_left (hpow) (by positivity : 0 ≤ 2 * K1.lpSqConst p)
    simpa using this
  · obtain ⟨M, hM1, hM2⟩ := exists_color_count (B := 2 ^ (n + 3) * R) (by positivity) hr hr₀
    have hMle : (M : ℝ) ≤ 2 ^ n * (8 * R + r₀ + 2) := by
      have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have h8 : (2 : ℝ) ^ (n + 3) = 8 * 2 ^ n := by ring
      rw [h8] at hM2
      nlinarith
    have hpow := rpow_color_count_le (d := d) hE hMle
    have hfacts := fun z => condExp_sub_local_facts (μ := reducedLaw Q) hp1
      (U := {y : Vec d | euclideanNorm (y - center z) < R * 2 ^ (n + 1) * r})
      (W := {y : Vec d | euclideanNorm (y - center z) < R * 2 ^ (n + 1 + 1) * r})
      (fun y hy => lt_of_lt_of_le hy (by
        have h2 : (2:ℝ) ^ (n + 1) ≤ 2 ^ (n + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hR) hr0.le)) (hX z) (hX0 z)
    have hcol : 2 * (R * 2 ^ (n + 1 + 1) * r) + r₀ < M * r := by
      have : 2 * (R * 2 ^ (n + 1 + 1) * r) = 2 ^ (n + 3) * R * r := by ring
      rw [this]; exact hM1
    have key : N (∑ z ∈ Λ, A n z) ≤ 2 * K1.lpSqConst p * (M : ℝ) ^ ((d : ℝ) / 2) *
        Real.sqrt (∑ z ∈ Λ, (N (A n z)) ^ 2) :=
      K2.lattice_local_eLpNorm_sum_le hfr hr₀ (r := r) (ρ := R * 2 ^ (n + 1 + 1) * r) (p := p)
        hr0 (by positivity) hp M hcol
        (fun z => A n z) (fun z => (hfacts z).1) (fun z => (hfacts z).2.1)
        (fun z => (hfacts z).2.2) Λ
    refine key.trans ?_
    unfold blockColorConst
    have h2 : 2 * K1.lpSqConst p * (M : ℝ) ^ ((d : ℝ) / 2) ≤
        2 * K1.lpSqConst p * (8 * R + r₀ + 2) ^ ((d : ℝ) / 2) * 2 ^ ((n : ℝ) * (d : ℝ) / 2) :=
      (mul_le_mul_of_nonneg_left hpow (by positivity)).trans_eq (by ring)
    exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
end EinsteinFull.Calculus.K3
