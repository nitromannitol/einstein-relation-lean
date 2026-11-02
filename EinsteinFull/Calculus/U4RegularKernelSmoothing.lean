import EinsteinFull.Calculus.U2GMPEnvironmentRealization
import EinsteinFull.Calculus.U1GMPNashRepresentation
import EinsteinFull.Calculus.U2GMPRegularRealization
import EinsteinFull.Calculus.U8PhysicalNashDuality
import EinsteinFull.Calculus.U5RegularGaugeGrowth
import EinsteinFull.Calculus.U2GMPKernelReversibility
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal Topology

namespace EinsteinFull

open Set Filter

/-- Gauge-weighted L¹ growth for the actual physical L² evolution. -/
def u4SignedGaugeL1Interval {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
    Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume →
    ∀ (t s : ℝ≥0), s ≤ t →
    Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω s f x) volume ∧
    (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) *
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω s f x|) ≤
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (t : ℝ)) *
        ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|

theorem u4_signed_physical_generator_nash_differential_of_gauge
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hgrowth : u4SignedGaugeL1Interval hd ω lam Λ hΛ hω) :
    let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    ∃ C : ℝ, 0 < C ∧ ∀ (f : S.generatorDomain)
      (hf : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x) volume)
      (t : ℝ≥0) (F : ℝ), 0 < F →
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (t : ℝ)) *
        (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x|) ≤ F →
      ∀ (s : ℝ≥0), 0 < s → s ≤ t →
      let K := C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))
      2 * inner ℝ (S s (S.generator f)) (S s f) ≤
        -(2 / (4 * Λ * K)) * (‖S s f‖ ^ 2) ^ (1 + 2 / (d : ℝ)) +
          (lam ^ 2 / Λ) * ‖S s f‖ ^ 2 := by
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  obtain ⟨C₁, hC₁, hN⟩ := u1_signed_physical_generator_orbit_gauge_nash_raised hd ω lam Λ hΛ hω
  obtain ⟨C₂, hC₂, hM⟩ := hgrowth
  let C := max C₁ (C₂ + 1)
  have hC : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro f hf t F hF hfF s hs hst
  let E : ℝ := -inner ℝ (S s (S.generator f)) (S s f)
  let U : ℝ := ‖S s f‖ ^ 2
  let M : ℝ := ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * S s f x|
  let K : ℝ := C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have hΛp : 0 < Λ := by linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hE : 0 ≤ E := by
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    simpa only [E, S, Real.toNNReal_coe] using
      (SubdiffusiveProcess.Nash.orbit_energy_nonneg S f hsR)
  have hmass := hM (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) hf t s hst
  have hMF : M ≤ F := by
    apply hmass.2.trans
    apply (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ => abs_nonneg _)).trans hfF
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (le_trans (by linarith : C₂ ≤ C₂ + 1) (le_max_right _ _)) t.coe_nonneg
  have hM0 : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  have hn := hN f s hs hmass.1
  have hb : U ^ (1 + 2 / (d : ℝ)) ≤ K * (4 * Λ * E + 2 * lam ^ 2 * U) := by
    calc
      _ ≤ C₁ * (Real.exp (2 * Λ) * (4 * Λ * E + 2 * lam ^ 2 * U)) * M ^ (4 / (d : ℝ)) := hn
      _ ≤ C * (Real.exp (2 * Λ) * (4 * Λ * E + 2 * lam ^ 2 * U)) * F ^ (4 / (d : ℝ)) := by
        gcongr
        exact le_max_left _ _
      _ = K * (4 * Λ * E + 2 * lam ^ 2 * U) := by dsimp [K]; ring
  have hdiv : U ^ (1 + 2 / (d : ℝ)) / (4 * Λ * K) ≤ E + (lam ^ 2 / (2 * Λ)) * U := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * Λ * K)).2
    calc
      _ ≤ K * (4 * Λ * E + 2 * lam ^ 2 * U) := hb
      _ = (E + lam ^ 2 / (2 * Λ) * U) * (4 * Λ * K) := by
        field_simp [ne_of_gt hΛp]
        <;> ring
  have hident : 2 * inner ℝ (S s (S.generator f)) (S s f) = -2 * E := by
    dsimp [E]
    ring
  dsimp only
  rw [hident]
  change -2 * E ≤ -(2 / (4 * Λ * K)) * U ^ (1 + 2 / (d : ℝ)) + (lam ^ 2 / Λ) * U
  have hΛne : Λ ≠ 0 := ne_of_gt hΛp
  have hKne : K ≠ 0 := ne_of_gt hK
  field_simp at hdiv ⊢
  nlinarith


theorem u4_signed_physical_generator_decay_of_gauge
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hgrowth : u4SignedGaugeL1Interval hd ω lam Λ hΛ hω) :
    let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    ∃ C : ℝ, 0 < C ∧ ∀ (f : S.generatorDomain)
      (hf : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
        (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x) volume)
      (t : ℝ≥0) (F : ℝ), 0 < t → 0 < F →
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (t : ℝ)) *
        (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) *
          (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x|) ≤ F →
      ‖S t f‖ ^ 2 ≤ Real.exp ((lam ^ 2 / Λ) * (t : ℝ)) *
        ((1 / ((d : ℝ) * Λ * (C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))))) *
          (t : ℝ)) ^ (-(d : ℝ) / 2) := by
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  obtain ⟨C, hC, hN⟩ := u4_signed_physical_generator_nash_differential_of_gauge hd ω lam Λ hΛ hω hgrowth
  refine ⟨C, hC, ?_⟩
  intro f hf t F ht hF hfF
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have hΛp : 0 < Λ := by linarith
  let K : ℝ := C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))
  have hK : 0 < K := by dsimp [K]; positivity
  let c : ℝ := 1 / ((d : ℝ) * Λ * K)
  have hc : 0 < c := by dsimp [c]; positivity
  let u : ℝ → ℝ := fun s => ‖S (Real.toNNReal s) f‖ ^ 2
  let v : ℝ → ℝ := fun s => 2 * inner ℝ (S (Real.toNNReal s) (S.generator f))
    (S (Real.toNNReal s) f)
  by_cases hut : u t = 0
  · have heq : ‖S t f‖ ^ 2 = 0 := by simpa [u] using hut
    rw [heq]
    positivity
  have hutP : 0 < u t := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hut)
  have huA : Antitone u := by
    intro a b hab
    exact pow_le_pow_left₀ (norm_nonneg _)
      (SubdiffusiveProcess.Nash.orbit_norm_antitone S f (Real.toNNReal_mono hab)) 2
  have hpos (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) : 0 < u s := hutP.trans_le (huA hs.2)
  have hineq (s : ℝ) (hs : s ∈ Ioo 0 (t : ℝ)) :
      v s ≤ -(((d : ℝ) / 2) * c) * u s ^ (1 + 1 / ((d : ℝ) / 2)) +
        (lam ^ 2 / Λ) * u s := by
    have hs0 : (0 : ℝ≥0) < Real.toNNReal s := Real.toNNReal_pos.mpr hs.1
    have hst : Real.toNNReal s ≤ t := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_mono hs.2.le
    have hn := hN f hf t F hF hfF (Real.toNNReal s) hs0 hst
    have hex : 1 + 1 / ((d : ℝ) / 2) = 1 + 2 / (d : ℝ) := by field_simp
    rw [hex]
    change v s ≤ -(2 / (4 * Λ * K)) * u s ^ (1 + 2 / (d : ℝ)) +
      (lam ^ 2 / Λ) * u s at hn
    convert hn using 1
    dsimp [c]
    field_simp [ne_of_gt hdR, ne_of_gt hΛp, ne_of_gt hK] <;> ring
  have hdec := u1_nash_decay_with_linear_term u v ((d : ℝ) / 2) c (lam ^ 2 / Λ) t
    (by positivity) hc (by positivity) ht
    (((S.continuous_operator_toNNReal f).norm.pow 2).continuousOn) hpos
    (fun s hs => SubdiffusiveProcess.Nash.hasDerivAt_orbit_norm_sq S f hs.1) hineq
  simpa only [u, c, K, S, Real.toNNReal_coe, neg_div] using hdec

/-- Signed gauge Nash decay for arbitrary physical L² data, after a half-time shift. -/
theorem u4_signed_physical_L1_L2_decay_of_gauge
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hgrowth : u4SignedGaugeL1Interval hd ω lam Λ hΛ hω) :
    let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧
      ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
        (hf : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume)
        (t : ℝ≥0) (F : ℝ), 0 < t → 0 < F →
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * ((t / 2 : ℝ≥0) : ℝ)) *
        ((Real.exp (2 * Λ)) ^ 2 * Real.exp (B * ((t / 2 : ℝ≥0) : ℝ)) *
          (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|)) ≤ F →
      ‖S t f‖ ^ 2 ≤ Real.exp ((lam ^ 2 / Λ) * ((t / 2 : ℝ≥0) : ℝ)) *
        ((1 / ((d : ℝ) * Λ * (C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))))) *
          ((t / 2 : ℝ≥0) : ℝ)) ^ (-(d : ℝ) / 2) := by
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  obtain ⟨C, hC, hdec⟩ := u4_signed_physical_generator_decay_of_gauge hd ω lam Λ hΛ hω hgrowth
  obtain ⟨B, hB, hb⟩ := hgrowth
  refine ⟨C, B, hC, hB, ?_⟩
  intro f hf t F ht hF hfF
  let r : ℝ≥0 := t / 2
  have hr : 0 < r := div_pos ht (by norm_num)
  have hsum : r + r = t := by ext; simp [r]
  let g : S.generatorDomain := ⟨S r f,
    u1_signed_physical_positive_time_generator hd ω lam Λ hΛ hω f r hr⟩
  have hg := hb f hf r r le_rfl
  have hmass : (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (r : ℝ)) *
      (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) *
        (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x|) ≤ F := by
    calc
      _ ≤ (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (r : ℝ)) *
          ((Real.exp (2 * Λ)) ^ 2 * Real.exp (B * (r : ℝ)) *
            (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|)) :=
        mul_le_mul_of_nonneg_left hg.2 (by positivity)
      _ ≤ F := hfF
  have h := hdec g hg.1 r F hr hF hmass
  change ‖S r (S r f)‖ ^ 2 ≤ _ at h
  rw [← S.add_apply, hsum] at h
  exact h

/-- At every positive time, signed physical evolution maps gauge L¹ data to L². -/
theorem u4_signed_physical_gauge_L1_to_L2_of_gauge
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hgrowth : u4SignedGaugeL1Interval hd ω lam Λ hΛ hω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume →
      ‖Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f‖ ≤
        M * ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x| := by
  obtain ⟨C, B, hC, hB, hdec⟩ := u4_signed_physical_L1_L2_decay_of_gauge hd ω lam Λ hΛ hω hgrowth
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have hΛp : 0 < Λ := by linarith
  let r : ℝ := ((t / 2 : ℝ≥0) : ℝ)
  have hr : 0 < r := by dsimp [r]; exact_mod_cast (div_pos ht (by norm_num) : 0 < t / 2)
  let A : ℝ := (1 / ((d : ℝ) * Λ * (C * Real.exp (2 * Λ)))) * r
  let D : ℝ := Real.exp ((lam ^ 2 / Λ) * r)
  let K : ℝ := (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * r) *
    ((Real.exp (2 * Λ)) ^ 2 * Real.exp (B * r))
  let L : ℝ := Real.sqrt D * A ^ (-(d : ℝ) / 4)
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L * K, mul_pos hL hK, ?_⟩
  intro f hf
  let m : ℝ := ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|
  have hm : 0 ≤ m := integral_nonneg fun _ => abs_nonneg _
  apply le_of_forall_pos_le_add
  intro ε hε
  let F : ℝ := K * m + ε / L
  have hF : 0 < F := by dsimp [F]; positivity
  have hmass : (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * r) *
      ((Real.exp (2 * Λ)) ^ 2 * Real.exp (B * r) * m) ≤ F := by
    dsimp [F, K]
    nlinarith [div_pos hε hL]
  have hb := hdec f hf t F ht hF hmass
  have hp : -(4 / (d : ℝ)) * (-(d : ℝ) / 2) = (2 : ℝ) := by field_simp; ring
  have he : (1 / ((d : ℝ) * Λ * (C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))))) * r =
      A * F ^ (-(4 / (d : ℝ))) := by
    rw [Real.rpow_neg hF.le]
    dsimp [A]
    ring
  change ‖Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f‖ ^ 2 ≤
    D * ((1 / ((d : ℝ) * Λ * (C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))))) * r) ^
      (-(d : ℝ) / 2) at hb
  rw [he, Real.mul_rpow hA.le (Real.rpow_nonneg hF.le _),
    ← Real.rpow_mul hF.le, hp, Real.rpow_two] at hb
  have hp2 : (-(d : ℝ) / 4) * 2 = -(d : ℝ) / 2 := by ring
  have hsq : (L * F) ^ 2 = D * A ^ (-(d : ℝ) / 2) * F ^ 2 := by
    dsimp [L]
    rw [mul_pow, mul_pow, Real.sq_sqrt hD.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hA.le]
    norm_num only [Nat.cast_ofNat]
    rw [hp2]
  have hn : ‖Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f‖ ≤ L * F := by
    rw [← mul_assoc, ← hsq] at hb
    nlinarith [norm_nonneg (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f),
      mul_nonneg hL.le hF.le]
  calc
    _ ≤ L * F := hn
    _ = (L * K) * m + ε := by dsimp [F]; field_simp

#print axioms u4_signed_physical_gauge_L1_to_L2_of_gauge

/-- An almost-everywhere L² bound for the actual regular physical evolution
extends to every starting point by continuity of its C₀ realization. -/
theorem u4_regular_kernel_local_L2_bound_of_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (C : Vec d → ℝ) (hC : Continuous C)
    (hbound : ∀ (f : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f),
      ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        |Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
          ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).toLp f) x| ≤
          C x * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal) :
    ∀ x f, Continuous f → HasCompactSupport f →
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
        C x * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal := by
  intro x f hf hfc
  let F := Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc
  let g : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, hf⟩, hfc.is_zero_at_infty⟩
  have he := u2RegularC0KernelSemigroup_integral_ae hd ω lam Λ hΛ hω t g
    (F.toLp f) F.coeFn_toLp
  have hb := hbound f hf hfc
  have hv : ∀ᵐ z ∂(volume : Measure (Vec d)),
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z| ≤
        C z * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal := by
    apply (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp
    filter_upwards [he, hb] with z he hb
    change (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z) = _ at he
    rw [he]
    exact hb
  have hc : Continuous (fun z => ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z) := by
    change Continuous (fun z => ∫ y, g y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z)
    simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω lam Λ hΛ hω t g).continuous
  have hclosed : IsClosed {z : Vec d |
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z| ≤
        C z * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal} :=
    isClosed_le hc.abs (hC.mul continuous_const)
  have hdense := Measure.dense_of_ae hv
  have hall : {z : Vec d |
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z| ≤
        C z * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal} = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  have hx : x ∈ {z : Vec d |
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z| ≤
        C z * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal} := by
    rw [hall]
    exact Set.mem_univ x
  exact hx

/-- A symmetric L² operator with indicator bounds on a finite-measure region
has a local L²-to-pointwise bound on that same region. -/
theorem u4_symmetric_local_indicator_transpose {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (T : Lp ℝ 2 μ → Lp ℝ 2 μ) (B : Set α)
    (hB : MeasurableSet B) (hBm : μ B ≠ ∞) (C : ℝ)
    (hsymm : ∀ f g, inner ℝ (T f) g = inner ℝ f (T g))
    (hbound : ∀ (s : Set α) (hs : MeasurableSet s) (hm : μ s ≠ ∞), s ⊆ B →
      ‖T (indicatorConstLp 2 hs hm (1 : ℝ))‖ ≤ C * μ.real s)
    (f : Lp ℝ 2 μ) : ∀ᵐ x ∂μ.restrict B, |T f x| ≤ C * ‖f‖ := by
  let ν := μ.restrict B
  haveI : IsFiniteMeasure ν := ⟨by simpa [ν, Measure.restrict_apply_univ] using (lt_top_iff_ne_top.mpr hBm)⟩
  have hi : Integrable (fun x => T f x) ν :=
    integrableOn_Lp_of_measure_ne_top (T f) fact_one_le_two_ennreal.elim hBm
  have hb (s : Set α) (hs : MeasurableSet s) :
      |∫ x in s, T f x ∂ν| ≤ (C * ‖f‖) * ν.real s := by
    have hsB : MeasurableSet (s ∩ B) := hs.inter hB
    have hm : μ (s ∩ B) ≠ ∞ := ne_top_of_le_ne_top hBm (measure_mono Set.inter_subset_right)
    let I : Lp ℝ 2 μ := indicatorConstLp 2 hsB hm (1 : ℝ)
    have he : (∫ x in s ∩ B, T f x ∂μ) = inner ℝ (T I) f := by
      rw [← L2.inner_indicatorConstLp_one hsB hm, ← hsymm, real_inner_comm]
    have h := (abs_real_inner_le_norm (T I) f).trans
      (mul_le_mul_of_nonneg_right (hbound (s ∩ B) hsB hm Set.inter_subset_right) (norm_nonneg f))
    have hh : |∫ x in s ∩ B, T f x ∂μ| ≤ (C * ‖f‖) * μ.real (s ∩ B) := by
      rw [he]
      calc
        _ ≤ (C * μ.real (s ∩ B)) * ‖f‖ := h
        _ = (C * ‖f‖) * μ.real (s ∩ B) := by ring
    simpa [ν, Measure.restrict_restrict hs, Measure.real, Measure.restrict_apply hs] using hh
  have hu := ae_le_of_forall_setIntegral_le hi (integrable_const (C * ‖f‖)) (fun s hs _ => by
    simpa only [integral_const, smul_eq_mul, measureReal_def,
      Measure.restrict_apply_univ, mul_comm] using (le_abs_self _).trans (hb s hs))
  have hl := ae_le_of_forall_setIntegral_le (integrable_const (-(C * ‖f‖))) hi (fun s hs _ => by
    have hh := (abs_le.mp (hb s hs)).1
    simpa only [integral_const, smul_eq_mul, measureReal_def,
      Measure.restrict_apply_univ, mul_neg, neg_mul, mul_comm] using hh)
  filter_upwards [hu, hl] with x hx hy
  exact abs_le.mpr ⟨hy, hx⟩

#print axioms u4_symmetric_local_indicator_transpose

/-- A local almost-everywhere estimate transfers to every start in an open region. -/
theorem u4_regular_kernel_bound_on_open_of_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (U : Set (Vec d)) (hU : IsOpen U) (C : ℝ)
    (hbound : ∀ (f : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f),
      ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam).restrict U,
        |Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
          ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).toLp f) x| ≤
          C * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal) :
    ∀ x ∈ U, ∀ f, Continuous f → HasCompactSupport f →
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
        C * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal := by
  intro x hx f hf hfc
  let F := Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc
  let g : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, hf⟩, hfc.is_zero_at_infty⟩
  let H : Vec d → ℝ := fun z => ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z
  let M := C * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal
  have he := u2RegularC0KernelSemigroup_integral_ae hd ω lam Λ hΛ hω t g
    (F.toLp f) F.coeFn_toLp
  have hp : ∀ᵐ z ∂(physicalReversibleMeasure ω hd lam).restrict U, |H z| ≤ M := by
    filter_upwards [ae_restrict_le he, hbound f hf hfc] with z hz hb
    change H z = _ at hz
    rw [hz]
    exact hb
  have hv : ∀ᵐ z ∂(volume : Measure (Vec d)).restrict U, |H z| ≤ M := by
    apply (ae_restrict_iff' hU.measurableSet).2
    apply (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp
    exact (ae_restrict_iff' hU.measurableSet).1 hp
  have hc : Continuous H := by
    change Continuous (fun z => ∫ y, g y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z)
    simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω lam Λ hΛ hω t g).continuous
  have heq : (fun z => max |H z| M) =ᵐ[(volume : Measure (Vec d)).restrict U] (fun _ => M) :=
    hv.mono fun _ hz => max_eq_right hz
  have hpnt := Measure.eqOn_open_of_ae_eq heq hU
    (hc.continuousOn.abs.sup continuousOn_const) continuousOn_const
  exact (le_max_left _ _).trans_eq (hpnt hx)

#print axioms u4_regular_kernel_bound_on_open_of_ae

/-- Local indicator smoothing for the signed physical semigroup yields the
same local bound for every starting point of its regular kernel. -/
theorem u4_regular_kernel_bound_on_open_of_indicator {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (U : Set (Vec d)) (hU : IsOpen U)
    (hUm : physicalReversibleMeasure ω hd lam U ≠ ∞) (C : ℝ)
    (hbound : ∀ (s : Set (Vec d)) (hs : MeasurableSet s)
      (hm : physicalReversibleMeasure ω hd lam s ≠ ∞), s ⊆ U →
      ‖Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
        (indicatorConstLp 2 hs hm (1 : ℝ))‖ ≤
          C * (physicalReversibleMeasure ω hd lam).real s) :
    ∀ x ∈ U, ∀ f, Continuous f → HasCompactSupport f →
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
        C * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal := by
  apply u4_regular_kernel_bound_on_open_of_ae hd ω lam Λ hΛ hω t U hU C
  intro f hf hfc
  have h := u4_symmetric_local_indicator_transpose
    (physicalReversibleMeasure ω hd lam)
    (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t) U hU.measurableSet hUm C
    (Blueprint.gmpPhysicalSemigroup_inner_comm hd ω lam Λ hΛ hω t) hbound
    ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).toLp f)
  simpa only [Lp.norm_toLp] using h

#print axioms u4_regular_kernel_bound_on_open_of_indicator

/-- The every-start compact-test L² estimate for the unforced physical kernel. -/
theorem u4_regular_unforced_kernel_L2_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ x (f : Vec d → ℝ), Continuous f → HasCompactSupport f →
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x| ≤
        C * (eLpNorm f 2 (physicalReversibleMeasure ω hd 0)).toReal := by
  obtain ⟨C, hC, hbound⟩ := u8_unforced_physical_L2_to_Linfty hd ω Λ hΛ hω t ht
  refine ⟨C, hC, ?_⟩
  apply u4_regular_kernel_local_L2_bound_of_ae hd ω 0 Λ hΛ hω t (fun _ => C) continuous_const
  intro f hf hfc
  have h := hbound ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω 0 f hf hfc).toLp f)
  simpa only [Lp.norm_toLp] using h

#print axioms u4_regular_unforced_kernel_L2_bound

#print axioms u4_regular_kernel_local_L2_bound_of_ae

/-- Gauge L¹-to-L² smoothing controls indicator data on any bounded
coordinate slab in the physical reversible measure. -/
theorem u4_signed_local_indicator_of_gauge {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hgrowth : u4SignedGaugeL1Interval hd ω lam Λ hΛ hω)
    (t : ℝ≥0) (ht : 0 < t) (B : Set (Vec d))
    (hBb : Bornology.IsBounded B) (r a : ℝ)
    (hr : ∀ x ∈ B, r ≤ lam * x (firstCoordinateIndex hd))
    (ha : ∀ x ∈ B, lam * x (firstCoordinateIndex hd) ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Set (Vec d)) (hs : MeasurableSet s)
      (hm : physicalReversibleMeasure ω hd lam s ≠ ∞), s ⊆ B →
      ‖Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
        (indicatorConstLp 2 hs hm (1 : ℝ))‖ ≤
          C * (physicalReversibleMeasure ω hd lam).real s := by
  obtain ⟨M, hM, hbound⟩ := u4_signed_physical_gauge_L1_to_L2_of_gauge
    hd ω lam Λ hΛ hω hgrowth t ht
  refine ⟨M * Real.exp a * Real.exp (2 * Λ - 2 * r), by positivity, ?_⟩
  intro s hs hm hsB
  let I := indicatorConstLp 2 hs hm (1 : ℝ)
  have hsb : Bornology.IsBounded s := hBb.subset hsB
  have hvol : volume s ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono subset_closure) hsb.isCompact_closure.measure_lt_top).ne
  have hc : Continuous (fun x : Vec d => Real.exp (lam * x (firstCoordinateIndex hd))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_apply (firstCoordinateIndex hd)))
  have hint : IntegrableOn (fun x : Vec d => Real.exp (lam * x (firstCoordinateIndex hd))) s volume :=
    (hc.continuousOn.integrableOn_compact hsb.isCompact_closure).mono_set subset_closure
  have hI := u1_signed_physical_ae_to_volume hd ω lam
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hm) (c := (1 : ℝ)))
  have hi : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * I x) volume := by
    apply (hint.integrable_indicator hs).congr
    filter_upwards [hI] with x hx
    change I x = _ at hx
    rw [hx]
    by_cases hx : x ∈ s <;> simp [hx]
  have he : (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * I x|) =
      ∫ x in s, Real.exp (lam * x (firstCoordinateIndex hd)) := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [hI] with x hx
    change I x = _ at hx
    rw [hx]
    by_cases hx : x ∈ s <;> simp [hx, Real.exp_nonneg]
  have hcomp := u1_signed_physical_measure_slab_comparison hd ω lam Λ r hω s hs
    (fun x hx => hr x (hsB hx))
  have hvle : volume s ≤ ENNReal.ofReal (Real.exp (2 * Λ - 2 * r)) *
      physicalReversibleMeasure ω hd lam s := by
    have h := hcomp s
    simpa [Measure.restrict_apply hs] using h
  have hvreal : (volume s).toReal ≤ Real.exp (2 * Λ - 2 * r) *
      (physicalReversibleMeasure ω hd lam s).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top) hm) hvle
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  have hg := u1_signed_gauge_set_integral_le hd lam a s hs hsb
    (fun x hx => ha x (hsB hx))
  calc
    ‖Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t I‖ ≤
        M * ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * I x| := hbound I hi
    _ ≤ M * (Real.exp a * (volume s).toReal) := by rw [he]; gcongr
    _ ≤ M * (Real.exp a * (Real.exp (2 * Λ - 2 * r) *
        (physicalReversibleMeasure ω hd lam s).toReal)) := by gcongr
    _ = _ := by simp only [Measure.real]; ring

#print axioms u4_signed_local_indicator_of_gauge

/-- Regular gauge growth implies the every-start signed kernel L² estimate. -/
theorem u4_regular_signed_kernel_local_L2_bound_of_gauge {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hgrowth : u4SignedGaugeL1Interval hd ω lam Λ hΛ hω)
    (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
        C * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal := by
  let B : Set (Vec d) := Metric.ball x 1
  have hBo : IsOpen B := Metric.isOpen_ball
  have hBb : Bornology.IsBounded B := Metric.isBounded_ball
  let : IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd lam) :=
    EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have hBm : physicalReversibleMeasure ω hd lam B ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono subset_closure) hBb.isCompact_closure.measure_lt_top).ne
  let q : Vec d → ℝ := fun y => lam * y (firstCoordinateIndex hd)
  have hq : Continuous q := continuous_const.mul (continuous_apply _)
  have hcompact : IsCompact (q '' closure B) := hBb.isCompact_closure.image hq
  obtain ⟨r, hr⟩ := hcompact.bddBelow
  obtain ⟨a, ha⟩ := hcompact.bddAbove
  obtain ⟨C, hC, hbound⟩ := u4_signed_local_indicator_of_gauge hd ω lam Λ hΛ hω
    hgrowth t ht B hBb r a
    (fun y hy => hr ⟨y, subset_closure hy, rfl⟩)
    (fun y hy => ha ⟨y, subset_closure hy, rfl⟩)
  refine ⟨C, hC, ?_⟩
  exact u4_regular_kernel_bound_on_open_of_indicator hd ω lam Λ hΛ hω t B hBo hBm C
    hbound x (Metric.mem_ball_self (by norm_num))

#print axioms u4_regular_signed_kernel_local_L2_bound_of_gauge

/-- Weighted L¹ growth for the actual regular transition kernel. -/
def u4RegularKernelGaugeGrowth {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (f : Vec d → ℝ≥0∞), Measurable f →
    (∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) *
      (∫⁻ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
    (ENNReal.ofReal (Real.exp (2 * Λ))) ^ 2 *
      ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) * f x

/-- L² kernel integrability holds almost everywhere in volume. -/
theorem u4_regular_kernel_integrable_ae_volume {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      Integrable f (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) :=
  u1_signed_physical_ae_to_volume hd ω lam
    (u2_regular_kernel_integral_ae_L2 hd ω lam Λ hΛ hω t f hf).1

/-- L² kernel representation holds almost everywhere in volume. -/
theorem u4_regular_kernel_integral_ae_volume {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    (fun x => ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) =ᵐ[volume]
    (fun x => Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf.toLp f) x) :=
  u1_signed_physical_ae_to_volume hd ω lam
    (u2_regular_kernel_integral_ae_L2 hd ω lam Λ hΛ hω t f hf).2

theorem u4_regular_physical_semigroup_gauge_lintegral_le_of_kernel_growth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hkg : u4RegularKernelGaugeGrowth hd ω lam Λ hΛ hω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (f : EinsteinRelation.Vec d → ℝ)
      (hf : Measurable f) (hf2 : MemLp f 2 (physicalReversibleMeasure ω hd lam)),
    (∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) *
      ENNReal.ofReal |Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x|) ≤
    (ENNReal.ofReal (Real.exp (2 * Λ))) ^ 2 *
      ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) * ENNReal.ofReal |f x| := by
  obtain ⟨C, hC, hb⟩ := hkg
  refine ⟨C, hC, ?_⟩
  intro t f hf hf2
  let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t
  let F : EinsteinRelation.Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal |f y|
  have hF : Measurable F := by
    simpa only [F, Real.norm_eq_abs] using hf.norm.ennreal_ofReal
  have hpoint : ∀ᵐ x ∂(volume : Measure (EinsteinRelation.Vec d)),
      ENNReal.ofReal |Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x| ≤
        ∫⁻ y, F y ∂K x := by
    filter_upwards [u4_regular_kernel_integral_ae_volume hd ω lam Λ hΛ hω t f hf2,
      u4_regular_kernel_integrable_ae_volume hd ω lam Λ hΛ hω t f hf2] with x he hi
    rw [← he, ← ofReal_integral_eq_lintegral_ofReal hi.abs
      (ae_of_all _ fun y => abs_nonneg (f y))]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (f := f) (μ := K x)))
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) *
      (∫⁻ y, F y ∂K x) := by
        apply lintegral_mono_ae
        filter_upwards [hpoint] with x hx
        simpa only [mul_comm] using mul_le_mul_left hx
          (ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))))
    _ ≤ _ := hb t F hF

/-- Gauge integrability is preserved by the actual signed physical semigroup. -/
theorem u4_regular_physical_semigroup_gauge_integrable_of_kernel_growth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hkg : u4RegularKernelGaugeGrowth hd ω lam Λ hΛ hω)
    (t : ℝ≥0) (f : EinsteinRelation.Vec d → ℝ) (hf : Measurable f)
    (hf2 : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (hfi : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume) :
    Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x) volume := by
  let G : EinsteinRelation.Vec d → ℝ := fun x =>
    Real.exp (lam * x (firstCoordinateIndex hd)) * f x
  let H : EinsteinRelation.Vec d → ℝ := fun x =>
    Real.exp (lam * x (firstCoordinateIndex hd)) *
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x
  have hG : (∫⁻ x, ENNReal.ofReal |G x|) < ∞ := by
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => abs_nonneg (G x))).mp
    simpa only [Real.norm_eq_abs] using hfi.hasFiniteIntegral.norm
  obtain ⟨C, _, hb⟩ := u4_regular_physical_semigroup_gauge_lintegral_le_of_kernel_growth
    hd ω lam Λ hΛ hω hkg
  have hrewrite (a : ℝ) (x : EinsteinRelation.Vec d) :
      ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) * ENNReal.ofReal |a| =
        ENNReal.ofReal |Real.exp (lam * x (firstCoordinateIndex hd)) * a| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _),
      ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have hH : (∫⁻ x, ENNReal.ofReal |H x|) < ∞ := by
    have h := hb t f hf hf2
    simp_rw [hrewrite] at h
    exact lt_of_le_of_lt h (by
      apply ENNReal.mul_lt_top
      · apply ENNReal.mul_lt_top
        · exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
        · exact ENNReal.ofReal_lt_top
      · exact hG)
  have hm : AEStronglyMeasurable H volume := by
    apply Measurable.aestronglyMeasurable
    exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_apply (firstCoordinateIndex hd)))).measurable.mul
      (Lp.stronglyMeasurable _).measurable
  refine ⟨hm, (hasFiniteIntegral_norm_iff H).mp ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => abs_nonneg (H x))).mpr
  simpa only [Real.norm_eq_abs] using hH

/-- Real-valued gauge L¹ growth for the signed physical semigroup. -/
theorem u4_regular_physical_semigroup_gauge_L1_le_of_kernel_growth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hkg : u4RegularKernelGaugeGrowth hd ω lam Λ hΛ hω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (f : EinsteinRelation.Vec d → ℝ)
      (hf : Measurable f) (hf2 : MemLp f 2 (physicalReversibleMeasure ω hd lam)),
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume →
    (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) *
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x|) ≤
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (t : ℝ)) *
      ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x| := by
  obtain ⟨C, hC, hb⟩ := u4_regular_physical_semigroup_gauge_lintegral_le_of_kernel_growth
    hd ω lam Λ hΛ hω hkg
  refine ⟨C, hC, ?_⟩
  intro t f hf hf2 hfi
  have hfo := u4_regular_physical_semigroup_gauge_integrable_of_kernel_growth
    hd ω lam Λ hΛ hω hkg t f hf hf2 hfi
  have hrewrite (a : ℝ) (x : EinsteinRelation.Vec d) :
      ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) * ENNReal.ofReal |a| =
        ENNReal.ofReal |Real.exp (lam * x (firstCoordinateIndex hd)) * a| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have h := hb t f hf hf2
  simp_rw [hrewrite] at h
  rw [← ofReal_integral_eq_lintegral_ofReal hfo.abs (ae_of_all _ fun x => abs_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hfi.abs (ae_of_all _ fun x => abs_nonneg _),
    ← ENNReal.ofReal_pow (Real.exp_nonneg _),
    ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- On each bounded time interval, the signed physical L² orbit has a
uniform gauge L¹ bound. -/
theorem u4_regular_physical_semigroup_gauge_L1_interval_of_kernel_growth
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hkg : u4RegularKernelGaugeGrowth hd ω lam Λ hΛ hω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume →
      ∀ (t s : ℝ≥0), s ≤ t →
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω s f x) volume ∧
      (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) *
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω s f x|) ≤
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (t : ℝ)) *
        ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x| := by
  obtain ⟨C, hC, hb⟩ := u4_regular_physical_semigroup_gauge_L1_le_of_kernel_growth
    hd ω lam Λ hΛ hω hkg
  refine ⟨C, hC, ?_⟩
  intro f hf t s hst
  have hmeas : Measurable (f : EinsteinRelation.Vec d → ℝ) := (Lp.stronglyMeasurable f).measurable
  have hi := u4_regular_physical_semigroup_gauge_integrable_of_kernel_growth
    hd ω lam Λ hΛ hω hkg s f hmeas (Lp.memLp f) hf
  have hbound := hb s f hmeas (Lp.memLp f) hf
  rw [Lp.toLp_coeFn] at hi hbound
  refine ⟨hi, hbound.trans ?_⟩
  have hExp : Real.exp (C * (s : ℝ)) ≤ Real.exp (C * (t : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hst) hC)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hExp (sq_nonneg _)) (integral_nonneg fun _ => abs_nonneg _)

#print axioms u4_regular_physical_semigroup_gauge_L1_interval_of_kernel_growth

/-- The target follows from gauge growth for the actual regular kernel. -/
theorem u4_regular_signed_kernel_local_L2_bound_of_kernel_growth {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hkg : u4RegularKernelGaugeGrowth hd ω lam Λ hΛ hω)
    (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
        C * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal := by
  apply u4_regular_signed_kernel_local_L2_bound_of_gauge hd ω lam Λ hΛ hω _ t ht x
  exact u4_regular_physical_semigroup_gauge_L1_interval_of_kernel_growth hd ω lam Λ hΛ hω hkg

#print axioms u4_regular_signed_kernel_local_L2_bound_of_kernel_growth

/-- A uniform estimate for pointwise convergent nonnegative barriers passes to
    their limit for the actual regular transition kernel. -/
theorem u4_regular_kernel_barrier_of_approximation {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (C : ℝ) (v : ℕ → Vec d → ℝ≥0∞)
    (hv : ∀ n, Measurable (v n))
    (hlim : ∀ x, Tendsto (fun n => v n x) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (-lam * x (firstCoordinateIndex hd))))))
    (hbound : ∀ n (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, v n y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (Real.exp (-lam * x (firstCoordinateIndex hd))) *
        ENNReal.ofReal (Real.exp (C * (t : ℝ)))) :
    ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (-lam * y (firstCoordinateIndex hd))) ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (Real.exp (-lam * x (firstCoordinateIndex hd))) *
        ENNReal.ofReal (Real.exp (C * (t : ℝ))) := by
  intro t x
  have hf := lintegral_liminf_le (u := atTop) (f := v)
    (μ := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) hv
  have heq : (fun y => Filter.liminf (fun n => v n y) atTop) =
      (fun y => ENNReal.ofReal (Real.exp (-lam * y (firstCoordinateIndex hd)))) :=
    funext fun y => (hlim y).liminf_eq
  rw [heq] at hf
  exact hf.trans (Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall
    (fun n => hbound n t x)))

#print axioms u4_regular_kernel_barrier_of_approximation

/-- Uniform bounds for bounded coordinate-exponential approximations imply the
    full exponential barrier for the same transition kernel. -/
theorem u4_regular_kernel_barrier_of_bounded_exponentials {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (C : ℝ)
    (hbound : ∀ (a : ℝ), 0 < a → ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (-lam * y (firstCoordinateIndex hd)) /
        (1 + a * Real.exp (-lam * y (firstCoordinateIndex hd)))) ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (Real.exp (-lam * x (firstCoordinateIndex hd))) *
        ENNReal.ofReal (Real.exp (C * (t : ℝ)))) :
    ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (-lam * y (firstCoordinateIndex hd))) ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (Real.exp (-lam * x (firstCoordinateIndex hd))) *
        ENNReal.ofReal (Real.exp (C * (t : ℝ))) := by
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let e : Vec d → ℝ := fun x => Real.exp (-lam * x (firstCoordinateIndex hd))
  let v : ℕ → Vec d → ℝ≥0∞ := fun n x => ENNReal.ofReal (e x / (1 + a n * e x))
  have he : Continuous e := Real.continuous_exp.comp
    (continuous_const.mul (continuous_apply (firstCoordinateIndex hd)))
  have ha : ∀ n, 0 < a n := fun n => by dsimp [a]; positivity
  have hv : ∀ n, Measurable (v n) := fun n => by
    apply ENNReal.continuous_ofReal.measurable.comp
    apply (he.measurable.div (measurable_const.add (measurable_const.mul he.measurable)))
  have hlim : ∀ x, Tendsto (fun n => v n x) atTop (𝓝 (ENNReal.ofReal (e x))) := by
    intro x
    have ha0 : Tendsto a atTop (𝓝 0) := by
      simpa only [a] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hv0 : Tendsto (fun n => e x / (1 + a n * e x)) atTop (𝓝 (e x)) := by
      have h := (tendsto_const_nhds (x := e x)).div
        (tendsto_const_nhds.add (ha0.mul tendsto_const_nhds)) (by norm_num : (1 : ℝ) + 0 * e x ≠ 0)
      change Tendsto (fun n => e x / (1 + a n * e x)) atTop
        (𝓝 (e x / (1 + 0 * e x))) at h
      simpa using h
    exact ENNReal.continuous_ofReal.tendsto (e x) |>.comp hv0
  apply u4_regular_kernel_barrier_of_approximation hd ω lam Λ hΛ hω C v hv hlim
  intro n t x
  exact hbound (a n) (ha n) t x

#print axioms u4_regular_kernel_barrier_of_bounded_exponentials


/-- Uniform bounded-exponential estimates give the local L² kernel estimate. -/
theorem u4_regular_signed_kernel_local_L2_bound_of_bounded_exponentials {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (a : ℝ), 0 < a → ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (-lam * y (firstCoordinateIndex hd)) /
        (1 + a * Real.exp (-lam * y (firstCoordinateIndex hd)))) ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (Real.exp (-lam * x (firstCoordinateIndex hd))) *
        ENNReal.ofReal (Real.exp (C * (t : ℝ))))
    (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    ∃ D : ℝ, 0 < D ∧ ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
        D * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal := by
  apply u4_regular_signed_kernel_local_L2_bound_of_kernel_growth hd ω lam Λ hΛ hω _ t ht x
  refine ⟨C, hC, ?_⟩
  exact u5_regular_signed_kernel_gauge_growth_of_barrier hd ω lam Λ hΛ hω C
    (u4_regular_kernel_barrier_of_bounded_exponentials hd ω lam Λ hΛ hω C hbound)

#print axioms u4_regular_signed_kernel_local_L2_bound_of_bounded_exponentials


/-- Every-start local L² bound for the regular signed physical kernel. -/
theorem u4_regular_signed_kernel_local_L2_bound {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
        C * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal := by
  obtain ⟨C, hC, hbarrier⟩ := u5_regular_kernel_coordinate_exp_growth
    hd ω lam Λ hΛ hω (firstCoordinateIndex hd) (-lam)
  apply u4_regular_signed_kernel_local_L2_bound_of_kernel_growth hd ω lam Λ hΛ hω _ t ht x
  refine ⟨C, hC, ?_⟩
  exact u5_regular_signed_kernel_gauge_growth_of_barrier hd ω lam Λ hΛ hω C hbarrier

#print axioms u4_regular_signed_kernel_local_L2_bound

/-- On any bounded open region the signed kernel estimate has one constant
    shared by all starting points in that region. -/
theorem u4_regular_signed_kernel_L2_bound_on_bounded_open_of_gauge {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hgrowth : u4SignedGaugeL1Interval hd ω lam Λ hΛ hω)
    (t : ℝ≥0) (ht : 0 < t) (U : Set (Vec d)) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ U, ∀ f : Vec d → ℝ,
      Continuous f → HasCompactSupport f →
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
        C * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal := by
  let : IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd lam) :=
    EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have hUm : physicalReversibleMeasure ω hd lam U ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono subset_closure) hUb.isCompact_closure.measure_lt_top).ne
  let q : Vec d → ℝ := fun y => lam * y (firstCoordinateIndex hd)
  have hq : Continuous q := continuous_const.mul (continuous_apply _)
  have hcompact : IsCompact (q '' closure U) := hUb.isCompact_closure.image hq
  obtain ⟨r, hr⟩ := hcompact.bddBelow
  obtain ⟨a, ha⟩ := hcompact.bddAbove
  obtain ⟨C, hC, hbound⟩ := u4_signed_local_indicator_of_gauge hd ω lam Λ hΛ hω
    hgrowth t ht U hUb r a
    (fun y hy => hr ⟨y, subset_closure hy, rfl⟩)
    (fun y hy => ha ⟨y, subset_closure hy, rfl⟩)
  exact ⟨C, hC, u4_regular_kernel_bound_on_open_of_indicator hd ω lam Λ hΛ hω
    t U hU hUm C hbound⟩

#print axioms u4_regular_signed_kernel_L2_bound_on_bounded_open_of_gauge

/-- Local uniform L² smoothing for the actual signed regular kernel. -/
theorem u4_regular_signed_kernel_L2_bound_on_bounded_open {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t)
    (U : Set (Vec d)) (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ U, ∀ f : Vec d → ℝ,
      Continuous f → HasCompactSupport f →
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
        C * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal := by
  obtain ⟨C, hC, hbarrier⟩ := u5_regular_kernel_coordinate_exp_growth
    hd ω lam Λ hΛ hω (firstCoordinateIndex hd) (-lam)
  have hkg : u4RegularKernelGaugeGrowth hd ω lam Λ hΛ hω :=
    ⟨C, hC, u5_regular_signed_kernel_gauge_growth_of_barrier hd ω lam Λ hΛ hω C hbarrier⟩
  exact u4_regular_signed_kernel_L2_bound_on_bounded_open_of_gauge hd ω lam Λ hΛ hω
    (u4_regular_physical_semigroup_gauge_L1_interval_of_kernel_growth hd ω lam Λ hΛ hω hkg)
    t ht U hU hUb

#print axioms u4_regular_signed_kernel_L2_bound_on_bounded_open

/-- Compact continuous functions approximate every physical L² class. -/
theorem u4_physical_L2_compact_approximation {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ∃ g : ℕ → Vec d → ℝ,
      (∀ n, Continuous (g n) ∧ HasCompactSupport (g n)) ∧
      Tendsto (fun n => eLpNorm ((f : Vec d → ℝ) - g n) 2
        (physicalReversibleMeasure ω hd lam)) atTop (𝓝 0) := by
  let : IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd lam) :=
    EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have hex : ∀ n : ℕ, ∃ g : Vec d → ℝ,
      Continuous g ∧ HasCompactSupport g ∧
      eLpNorm ((f : Vec d → ℝ) - g) 2 (physicalReversibleMeasure ω hd lam) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    obtain ⟨g, hgcomp, hgap, hgcont, _⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le
      (p := 2) (by norm_num) (ε := ENNReal.ofReal (1 / ((n : ℝ) + 1)))
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    exact ⟨g, hgcont, hgcomp, hgap⟩
  choose g hg using hex
  refine ⟨g, fun n => ⟨(hg n).1, (hg n).2.1⟩, ?_⟩
  have hε : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε
    (fun _ => zero_le) (fun n => (hg n).2.2)

#print axioms u4_physical_L2_compact_approximation

/-- Locally uniform Cauchy estimates produce a continuous pointwise limit. -/
theorem u4_continuous_limit_of_local_cauchy {α : Type*} [TopologicalSpace α]
    (g : ℕ → α → ℝ) (hg : ∀ n, Continuous (g n)) (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (ha0 : ∀ n, 0 ≤ a n)
    (hlocal : ∀ x, ∃ U ∈ 𝓝 x, ∃ C : ℝ, 0 ≤ C ∧
      ∀ m n y, y ∈ U → |g m y - g n y| ≤ C * (a m + a n)) :
    ∃ u : α → ℝ, Continuous u ∧ ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (u x)) := by
  have huc : ∀ x, ∃ U ∈ 𝓝 x, UniformCauchySeqOn g atTop U := by
    intro x
    obtain ⟨U, hU, C, hC, hb⟩ := hlocal x
    refine ⟨U, hU, Metric.uniformCauchySeqOn_iff.mpr ?_⟩
    intro ε hε
    have hδ : 0 < ε / (2 * (C + 1)) := div_pos hε (by positivity)
    have he := (Metric.tendsto_atTop.mp ha) _ hδ
    obtain ⟨N, hN⟩ := he
    refine ⟨N, ?_⟩
    intro m hm n hn y hy
    have hm' := hN m hm
    have hn' := hN n hn
    simp only [Real.dist_eq, sub_zero] at hm' hn'
    have hsmall : C * (a m + a n) < ε := by
      have hmle : a m < ε / (2 * (C + 1)) := (le_abs_self _).trans_lt hm'
      have hnle : a n < ε / (2 * (C + 1)) := (le_abs_self _).trans_lt hn'
      have hmC := mul_lt_mul_of_pos_left (add_lt_add hmle hnle) (show 0 < C + 1 by linarith)
      have hden : 0 < 2 * (C + 1) := by positivity
      have heq : (C + 1) * (ε / (2 * (C + 1)) + ε / (2 * (C + 1))) = ε := by
        field_simp
        <;> ring
      rw [heq] at hmC
      nlinarith [ha0 m, ha0 n]
    simpa only [Real.dist_eq] using (hb m n y hy).trans_lt hsmall
  have hc : ∀ x, CauchySeq (fun n => g n x) := by
    intro x
    obtain ⟨U, hU, h⟩ := huc x
    have hx : x ∈ U := mem_of_mem_nhds hU
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp h ε hε
    exact ⟨N, fun m hm n hn => hN m hm n hn x hx⟩
  choose u hu using fun x => cauchySeq_tendsto_of_complete (hc x)
  refine ⟨u, ?_, hu⟩
  have hloc : TendstoLocallyUniformly g u atTop := by
    apply Metric.tendstoLocallyUniformly_iff.mpr
    intro ε hε x
    obtain ⟨U, hU, h⟩ := huc x
    refine ⟨U, hU, ?_⟩
    exact Metric.tendstoUniformlyOn_iff.mp
      (h.tendstoUniformlyOn_of_tendsto (fun y _ => hu y)) ε hε
  exact hloc.continuous (Filter.Eventually.of_forall hg).frequently

#print axioms u4_continuous_limit_of_local_cauchy

/-- The compact approximants converge in the physical L² space. -/
theorem u4_physical_compact_approximation_Lp {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (g : ℕ → Vec d → ℝ) (hg : ∀ n, Continuous (g n) ∧ HasCompactSupport (g n))
    (hlim : Tendsto (fun n => eLpNorm ((f : Vec d → ℝ) - g n) 2
      (physicalReversibleMeasure ω hd lam)) atTop (𝓝 0)) :
    Tendsto (fun n => (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g n)
      (hg n).1 (hg n).2).toLp (g n)) atTop (𝓝 f) := by
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g
    (fun n => Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g n) (hg n).1 (hg n).2)
    (f : Vec d → ℝ) (Lp.memLp f)).mpr
      (hlim.congr fun n => eLpNorm_sub_comm _ _ 2 (physicalReversibleMeasure ω hd lam))
  simpa only [Lp.toLp_coeFn] using h

#print axioms u4_physical_compact_approximation_Lp

/-- Compact-input kernel evolutions satisfy a locally uniform L² Cauchy bound. -/
theorem u4_compact_kernel_local_cauchy_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (g : ℕ → Vec d → ℝ) (hg : ∀ n, Continuous (g n) ∧ HasCompactSupport (g n)) :
    let G := fun n => (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g n)
      (hg n).1 (hg n).2).toLp (g n)
    ∀ x, ∃ U ∈ 𝓝 x, ∃ C : ℝ, 0 ≤ C ∧ ∀ m n y, y ∈ U →
      |(∫ z, g m z ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t y) -
        (∫ z, g n z ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t y)| ≤
        C * (dist (G m) f + dist (G n) f) := by
  intro G x
  let U := Metric.ball x 1
  have hU : U ∈ 𝓝 x := Metric.ball_mem_nhds x (by norm_num)
  obtain ⟨C, hC, hbound⟩ := u4_regular_signed_kernel_L2_bound_on_bounded_open
    hd ω lam Λ hΛ hω t ht U Metric.isOpen_ball Metric.isBounded_ball
  refine ⟨U, hU, C, hC.le, ?_⟩
  intro m n y hy
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  have hi (k : ℕ) : Integrable (g k) (P t y) :=
    (hg k).1.integrable_of_hasCompactSupport (hg k).2
  have hb := hbound y hy (g m - g n) ((hg m).1.sub (hg n).1) ((hg m).2.sub (hg n).2)
  have he : (eLpNorm (g m - g n) 2 (physicalReversibleMeasure ω hd lam)).toReal =
      dist (G m) (G n) := by
    rw [Lp.dist_def, eLpNorm_congr_ae
      ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g m) (hg m).1 (hg m).2).coeFn_toLp.sub
       (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g n) (hg n).1 (hg n).2).coeFn_toLp)]
  change |∫ z, g m z - g n z ∂P t y| ≤
    C * (eLpNorm (g m - g n) 2 (physicalReversibleMeasure ω hd lam)).toReal at hb
  rw [integral_sub (hi m) (hi n), he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (dist_triangle (G m) f (G n) |>.trans_eq (by rw [dist_comm f (G n)])) hC.le)

#print axioms u4_compact_kernel_local_cauchy_bound

/-- Positive-time physical L² evolution has a continuous representative. -/
theorem u4_regular_signed_continuous_L2_representative {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∀ f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam),
      ∃ u : Vec d → ℝ, Continuous u ∧
        u =ᵐ[physicalReversibleMeasure ω hd lam]
          (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f : Vec d → ℝ) := by
  intro f
  obtain ⟨g, hg, hlim⟩ := u4_physical_L2_compact_approximation hd ω lam f
  let G := fun n => (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g n)
    (hg n).1 (hg n).2).toLp (g n)
  let H := fun n x => ∫ y, g n y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  have hG : Tendsto G atTop (𝓝 f) := u4_physical_compact_approximation_Lp hd ω lam f g hg hlim
  have hH : ∀ n, Continuous (H n) := by
    intro n
    let v : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨g n, (hg n).1⟩, (hg n).2.is_zero_at_infty⟩
    change Continuous (fun x => ∫ y, v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)
    simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω lam Λ hΛ hω t v).continuous
  have ha : Tendsto (fun n => dist (G n) f) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hG
  obtain ⟨u, hu, hpoint⟩ := u4_continuous_limit_of_local_cauchy H hH
    (fun n => dist (G n) f) ha (fun _ => dist_nonneg)
    (u4_compact_kernel_local_cauchy_bound hd ω lam Λ hΛ hω t ht f g hg)
  refine ⟨u, hu, ?_⟩
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
  have hS : Tendsto (fun n => S (G n)) atTop (𝓝 (S f)) :=
    S.continuous.tendsto f |>.comp hG
  obtain ⟨ns, hns, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hS).exists_seq_tendsto_ae
  have heq : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, ∀ n, H (ns n) x = S (G (ns n)) x := by
    apply ae_all_iff.mpr
    intro n
    let v : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨g (ns n), (hg (ns n)).1⟩, (hg (ns n)).2.is_zero_at_infty⟩
    exact u2RegularC0KernelSemigroup_integral_ae hd ω lam Λ hΛ hω t v (G (ns n))
      (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g (ns n))
        (hg (ns n)).1 (hg (ns n)).2).coeFn_toLp
  filter_upwards [hsub, heq] with x hx he
  apply tendsto_nhds_unique ((hpoint x).comp hns.tendsto_atTop)
  simpa only [Function.comp_def, he] using hx

#print axioms u4_regular_signed_continuous_L2_representative

/-- A compact-test L² estimate at every start implies absolute continuity. -/
theorem u4_regular_signed_kernel_ac_of_local_L2_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0)
    (hbound : ∀ x, ∃ C : ℝ, 0 < C ∧ ∀ f : Vec d → ℝ,
      Continuous f → HasCompactSupport f →
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
        C * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal) :
    ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
      (volume : Measure (Vec d)) := by
  intro x
  let μ := physicalReversibleMeasure ω hd lam
  let ν := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  let : IsProbabilityMeasure ν := ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
  obtain ⟨C, hC, hbound⟩ := hbound x
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hAz
  rw [hA.measure_eq_iSup_isCompact ν]
  apply le_antisymm ?_ bot_le
  apply iSup_le
  intro K
  apply iSup_le
  intro hKA
  apply iSup_le
  intro hK
  have hKv : (volume : Measure (Vec d)) K = 0 := measure_mono_null hKA hAz
  have hμv : μ ≪ (volume : Measure (Vec d)) := by
    apply Measure.ae_le_iff_absolutelyContinuous.mp
    intro P hP
    exact (Blueprint.gmpPhysical_ae_iff_volume hd ω lam P).mpr hP
  have hKμ : μ K = 0 := hμv hKv
  obtain ⟨c, f, hc, hcc, hcb, hf, hfb, hfl⟩ := u2_compact_indicator_approximation K hK
  have hlimμ : Tendsto (fun n => ∫ y, f n y ∂μ) atTop (𝓝 0) := by
    have hcint : Integrable c μ := hc.integrable_of_hasCompactSupport hcc
    have hh := tendsto_integral_of_dominated_convergence c
      (fun n => (hf n).1.aestronglyMeasurable) hcint
      (fun n => Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfb n y).1]
        exact (hfb n y).2)
      (Filter.Eventually.of_forall hfl)
    simpa [integral_indicator_const, hK.isClosed.measurableSet, measureReal_def, hKμ] using hh
  have hsq (n : ℕ) : (eLpNorm (f n) 2 μ).toReal ^ 2 ≤ ∫ y, f n y ∂μ := by
    rw [PDE.toReal_eLpNorm_two_sq_eq_integral_sq
      (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (f n) (hf n).1 (hf n).2)]
    apply integral_mono_ae
    · apply ((hf n).1.pow 2).integrable_of_hasCompactSupport
      have hsupp : HasCompactSupport ((f n) * (f n)) := (hf n).2.mul_right
      simpa only [pow_two, Pi.mul_apply] using hsupp
    · exact (hf n).1.integrable_of_hasCompactSupport (hf n).2
    · filter_upwards with y
      nlinarith [(hfb n y).1, (hfb n y).2, (hcb y).2]
  have hnorm : Tendsto (fun n => (eLpNorm (f n) 2 μ).toReal) atTop (𝓝 0) := by
    have hs : Tendsto (fun n => (eLpNorm (f n) 2 μ).toReal ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun n => sq_nonneg _) hsq hlimμ
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def, Real.sqrt_sq (ENNReal.toReal_nonneg), Real.sqrt_zero] using hh
  have hlimν := u2_probability_integral_approximation ν f
    (K.indicator (fun _ => (1 : ℝ))) (fun n => (hf n).1)
    (fun n y => ⟨(hfb n y).1, (hfb n y).2.trans (hcb y).2⟩) hfl
  have hle : (∫ y, K.indicator (fun _ => (1 : ℝ)) y ∂ν) ≤ 0 := by
    apply le_of_tendsto_of_tendsto hlimν (by simpa using hnorm.const_mul C)
    exact Filter.Eventually.of_forall fun n => (le_abs_self _).trans (hbound (f n) (hf n).1 (hf n).2)
  rw [integral_indicator_const (μ := ν) (1 : ℝ) hK.isClosed.measurableSet] at hle
  have hreal : (ν K).toReal = 0 := by
    have hh : (ν K).toReal ≤ 0 := by simpa [measureReal_def] using hle
    exact le_antisymm hh ENNReal.toReal_nonneg
  simpa only [bot_eq_zero, le_zero_iff] using
    ((ENNReal.toReal_eq_zero_iff (ν K)).mp hreal).resolve_right (measure_ne_top ν K)

#print axioms u4_regular_signed_kernel_ac_of_local_L2_bound


/-- Every positive-time signed kernel row is absolutely continuous. -/
theorem u4_regular_signed_kernel_absolutelyContinuous {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) :
    ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
      (volume : Measure (Vec d)) := by
  apply u4_regular_signed_kernel_ac_of_local_L2_bound hd ω lam Λ hΛ hω t
  intro x
  exact u4_regular_signed_kernel_local_L2_bound hd ω lam Λ hΛ hω t ht x

#print axioms u4_regular_signed_kernel_absolutelyContinuous

/-- A bounded physical L² function admits uniformly bounded compact tests. -/
theorem u4_physical_bounded_L2_compact_approximation {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (f : Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (B : ℝ) (hB : ∀ y, |f y| ≤ B) :
    ∃ g : ℕ → Vec d → ℝ,
      (∀ n, Continuous (g n) ∧ HasCompactSupport (g n)) ∧
      (∀ n y, |g n y| ≤ B) ∧
      Tendsto (fun n => eLpNorm (f - g n) 2
        (physicalReversibleMeasure ω hd lam)) atTop (𝓝 0) := by
  let μ := physicalReversibleMeasure ω hd lam
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have hB0 : 0 ≤ B := (abs_nonneg (f 0)).trans (hB 0)
  have hex : ∀ n : ℕ, ∃ g : Vec d → ℝ,
      Continuous g ∧ HasCompactSupport g ∧
      eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    obtain ⟨g, hc, hb, hcont, _⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le
      (by norm_num) (ε := ENNReal.ofReal (1 / ((n : ℝ) + 1)))
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    exact ⟨g, hcont, hc, hb⟩
  choose g hg using hex
  let clip : ℝ → ℝ := fun z => max (-B) (min B z)
  have hclip0 : clip 0 = 0 := by simp [clip, min_eq_right hB0, max_eq_right (neg_nonpos.mpr hB0)]
  let G : ℕ → Vec d → ℝ := fun n => clip ∘ g n
  have hcont (n : ℕ) : Continuous (G n) :=
    continuous_const.max (continuous_const.min (hg n).1)
  have hcomp (n : ℕ) : HasCompactSupport (G n) := (hg n).2.1.comp_left hclip0
  have hb (n : ℕ) (y : Vec d) : |G n y| ≤ B := by
    apply abs_le.mpr
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have herror (n : ℕ) : eLpNorm (f - G n) 2 μ ≤ eLpNorm (f - g n) 2 μ := by
    apply eLpNorm_mono_ae (hf.aestronglyMeasurable.sub (hcont n).aestronglyMeasurable)
    filter_upwards with y
    have hy := abs_le.mp (hB y)
    change ‖f y - clip (g n y)‖ ≤ ‖f y - g n y‖
    simp only [Real.norm_eq_abs]
    dsimp [clip]
    rcases le_total (g n y) (-B) with h | h
    · rw [min_eq_right (by linarith : g n y ≤ B), max_eq_left h]
      rw [sub_neg_eq_add, abs_of_nonneg (by linarith : 0 ≤ f y + B), abs_of_nonneg (by linarith : 0 ≤ f y - g n y)]
      linarith
    · rcases le_total (g n y) B with h' | h'
      · rw [min_eq_right h', max_eq_right h]
      · rw [min_eq_left h', max_eq_right (by linarith : -B ≤ B)]
        rw [abs_of_nonpos (by linarith : f y - B ≤ 0), abs_of_nonpos (by linarith : f y - g n y ≤ 0)]
        linarith
  refine ⟨G, fun n => ⟨hcont n, hcomp n⟩, hb, ?_⟩
  have hε : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε
    (fun _ => zero_le) (fun n => (herror n).trans (hg n).2.2)

#print axioms u4_physical_bounded_L2_compact_approximation

/-- Bounded physical L² inputs have continuous positive-time kernel actions. -/
theorem u4_regular_signed_kernel_integral_continuous_of_memLp {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (B : ℝ) (hB : ∀ y, |f y| ≤ B) :
    Continuous (fun x => ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) := by
  let μ := physicalReversibleMeasure ω hd lam
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let F := hf.toLp f
  obtain ⟨g, hg, hgb, hlim⟩ := u4_physical_bounded_L2_compact_approximation hd ω lam f hf B hB
  let G := fun n => (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g n)
    (hg n).1 (hg n).2).toLp (g n)
  have hlim' : Tendsto (fun n => eLpNorm ((F : Vec d → ℝ) - g n) 2 μ) atTop (𝓝 0) := by
    have he (n : ℕ) : eLpNorm (f - g n) 2 μ = eLpNorm ((F : Vec d → ℝ) - g n) 2 μ := by
      apply eLpNorm_congr_ae
      exact hf.coeFn_toLp.symm.sub (Filter.Eventually.of_forall fun _ => rfl)
    have heq : (fun n => eLpNorm (f - g n) 2 μ) =
        (fun n => eLpNorm ((F : Vec d → ℝ) - g n) 2 μ) := funext he
    rw [← heq]
    exact hlim
  have hG : Tendsto G atTop (𝓝 F) :=
    u4_physical_compact_approximation_Lp hd ω lam F g hg hlim'
  let H := fun n x => ∫ y, g n y ∂P t x
  have hH : ∀ n, Continuous (H n) := by
    intro n
    let v : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨g n, (hg n).1⟩, (hg n).2.is_zero_at_infty⟩
    change Continuous (fun x => ∫ y, v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)
    simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω lam Λ hΛ hω t v).continuous
  have ha : Tendsto (fun n => dist (G n) F) atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.mp hG
  obtain ⟨u, hu, hpoint⟩ := u4_continuous_limit_of_local_cauchy H hH
    (fun n => dist (G n) F) ha (fun _ => dist_nonneg)
    (u4_compact_kernel_local_cauchy_bound hd ω lam Λ hΛ hω t ht F g hg)
  obtain ⟨ns, hns, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hG).exists_seq_tendsto_ae
  have heq : ∀ᵐ y ∂μ, ∀ n, G (ns n) y = g (ns n) y := by
    apply ae_all_iff.mpr
    intro n
    exact (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g (ns n))
      (hg (ns n)).1 (hg (ns n)).2).coeFn_toLp
  have hcon : ∀ᵐ y ∂μ, Tendsto (fun n => g (ns n) y) atTop (𝓝 (f y)) := by
    filter_upwards [hsub, heq, hf.coeFn_toLp] with y hy he hf'
    change F y = f y at hf'
    simpa only [Function.comp_def, he, hf'] using hy
  have hvol := (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp hcon
  have heq : ∀ x, u x = ∫ y, f y ∂P t x := by
    intro x
    let : IsFiniteMeasure (P t x) := ⟨lt_of_le_of_lt (P.measure_univ_le_one t x) ENNReal.one_lt_top⟩
    have hrow := (u4_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht x).ae_le hvol
    have hi : Tendsto (fun n => ∫ y, g (ns n) y ∂P t x) atTop
        (𝓝 (∫ y, f y ∂P t x)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => B)
      · intro n
        exact (hg (ns n)).1.aestronglyMeasurable
      · exact integrable_const B
      · intro n
        exact Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hgb (ns n) y
      · exact hrow
    exact tendsto_nhds_unique ((hpoint x).comp hns.tendsto_atTop) hi
  have hfun : u = (fun x => ∫ y, f y ∂P t x) := funext heq
  change Continuous (fun x => ∫ y, f y ∂P t x)
  rw [← hfun]
  exact hu

#print axioms u4_regular_signed_kernel_integral_continuous_of_memLp


/-- Bounded measurable inputs have continuous positive-time kernel actions. -/
theorem u4_regular_signed_kernel_strongFeller
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t)
    (f : Vec d → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ y, |f y| ≤ B) :
    Continuous (fun x => ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) := by
  let μ := physicalReversibleMeasure ω hd lam
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have hB0 : 0 ≤ B := (abs_nonneg (f 0)).trans (hB 0)
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  let a : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let χ : ℕ → Vec d → ℝ := fun n x => b (a n • x)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hat : Tendsto a atTop (𝓝 0) := by
    simpa only [a, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hc (n : ℕ) : Continuous (χ n) := b.continuous.comp (continuous_const_smul (a n))
  have hs (n : ℕ) : HasCompactSupport (χ n) := b.hasCompactSupport.comp_smul (ha n).ne'
  have hb (n : ℕ) (y : Vec d) : 0 ≤ χ n y ∧ χ n y ≤ 1 := ⟨b.nonneg, b.le_one⟩
  have hb0 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  have hlim (y : Vec d) : Tendsto (fun n => χ n y) atTop (𝓝 1) := by
    have ht' : Tendsto (fun n => a n • y) atTop (𝓝 (0 : Vec d)) := by
      simpa only [zero_smul] using hat.smul (tendsto_const_nhds (x := y))
    simpa only [χ, hb0, Function.comp_def] using (b.continuous.tendsto 0).comp ht'
  let g : ℕ → Vec d → ℝ := fun n y => f y * χ n y
  have hgb (n : ℕ) (y : Vec d) : |g n y| ≤ B := by
    rw [show g n y = f y * χ n y from rfl, abs_mul, abs_of_nonneg (hb n y).1]
    nlinarith [mul_nonneg (sub_nonneg.mpr (hB y)) (hb n y).1,
      mul_nonneg (abs_nonneg (f y)) (sub_nonneg.mpr (hb n y).2)]
  have hgm (n : ℕ) : MemLp (g n) 2 μ := by
    change MemLp (f * χ n) 2 μ
    apply (hs n).mul_left.memLp_of_bound ((hf.mul (hc n).measurable).aestronglyMeasurable) B
    exact Filter.Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs, Pi.mul_apply, g] using hgb n y
  let G : ℕ → Vec d → ℝ := fun n x => ∫ y, g n y ∂P t x
  have hG (n : ℕ) : Continuous (G n) :=
    u4_regular_signed_kernel_integral_continuous_of_memLp hd ω lam Λ hΛ hω t ht (g n) (hgm n) B (hgb n)
  let Q : ℕ → Vec d → ℝ := fun n x => ∫ y, χ n y ∂P t x
  have hQ (n : ℕ) : Continuous (Q n) := by
    let v : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨χ n, hc n⟩, (hs n).is_zero_at_infty⟩
    change Continuous (fun x => ∫ y, v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)
    simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω lam Λ hΛ hω t v).continuous
  have hQlim (x : Vec d) : Tendsto (fun n => Q n x) atTop (𝓝 1) := by
    let : IsProbabilityMeasure (P t x) := ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
    have hh : Tendsto (fun n => ∫ y, χ n y ∂P t x) atTop (𝓝 (∫ _y, (1 : ℝ) ∂P t x)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      · intro n; exact (hc n).aestronglyMeasurable
      · exact integrable_const _
      · intro n; exact Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs, abs_of_nonneg (hb n y).1] using (hb n y).2
      · exact Filter.Eventually.of_forall hlim
    simpa using hh
  have herr (n : ℕ) (x : Vec d) :
      |(∫ y, f y ∂P t x) - G n x| ≤ (B + 1) * (1 - Q n x) := by
    let : IsProbabilityMeasure (P t x) := ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
    have fi : Integrable f (P t x) := by
      apply (integrable_const B).mono' hf.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs, abs_of_nonneg hB0] using hB y
    have gi : Integrable (g n) (P t x) := by
      apply (integrable_const B).mono' ((hf.mul (hc n).measurable).aestronglyMeasurable)
      exact Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hB0, g, Pi.mul_apply] using hgb n y
    have ci : Integrable (χ n) (P t x) := by
      apply (integrable_const (1 : ℝ)).mono' (hc n).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs, abs_of_nonneg (hb n y).1] using (hb n y).2
    have pi : Integrable (fun y => (B + 1) * (1 - χ n y)) (P t x) :=
      (integrable_const 1).sub ci |>.const_mul (B + 1)
    have hp (y : Vec d) : ‖f y - g n y‖ ≤ (B + 1) * (1 - χ n y) := by
      have he : f y - g n y = f y * (1 - χ n y) := by dsimp [g]; ring
      rw [he, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr (hb n y).2)]
      exact mul_le_mul_of_nonneg_right (by linarith [hB y]) (sub_nonneg.mpr (hb n y).2)
    calc
      |(∫ y, f y ∂P t x) - G n x| = ‖∫ y, (f y - g n y) ∂P t x‖ := by
        rw [integral_sub fi gi]; rfl
      _ ≤ ∫ y, ‖f y - g n y‖ ∂P t x := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (B + 1) * (1 - χ n y) ∂P t x :=
        integral_mono (fi.sub gi).norm pi hp
      _ = (B + 1) * (1 - Q n x) := by
        rw [integral_const_mul, integral_sub (integrable_const 1) ci]
        simp [Q]
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hδ : 0 < ε / (6 * (B + 1)) := div_pos hε (by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hQlim x)) _ hδ
  have hx := hN N le_rfl
  simp only [Real.dist_eq] at hx
  obtain ⟨δ₁, hδ₁, hnear₁⟩ := Metric.continuousAt_iff.mp (hQ N).continuousAt _ hδ
  obtain ⟨δ₂, hδ₂, hnear₂⟩ := Metric.continuousAt_iff.mp (hG N).continuousAt (ε / 3) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro y hy
  have hy₁ := hnear₁ (lt_of_lt_of_le hy (min_le_left _ _))
  have hy₂ := hnear₂ (lt_of_lt_of_le hy (min_le_right _ _))
  simp only [Real.dist_eq] at hy₁ hy₂ ⊢
  have hsmallx : (B + 1) * (1 - Q N x) < ε / 6 := by
    have h := (le_abs_self (1 - Q N x)).trans_lt (by simpa [abs_sub_comm] using hx)
    have hp := mul_lt_mul_of_pos_left h (show 0 < B + 1 by linarith)
    have he : (B + 1) * (ε / (6 * (B + 1))) = ε / 6 := by field_simp; <;> ring
    rw [he] at hp
    nlinarith
  have hsmally : (B + 1) * (1 - Q N y) < ε / 3 := by
    have h := (le_abs_self (Q N x - Q N y)).trans_lt (by simpa [abs_sub_comm] using hy₁)
    have hp := mul_lt_mul_of_pos_left h (show 0 < B + 1 by linarith)
    have he : (B + 1) * (ε / (6 * (B + 1))) = ε / 6 := by field_simp; <;> ring
    rw [he] at hp
    nlinarith
  have he₁ := herr N y
  have he₂ := herr N x
  have ht' := abs_sub_le (∫ z, f z ∂P t y) (G N y) (∫ z, f z ∂P t x)
  have ht'' := abs_sub_le (G N y) (G N x) (∫ z, f z ∂P t x)
  rw [abs_sub_comm] at he₂
  linarith

#print axioms u4_regular_signed_kernel_strongFeller


/-- The local kernel bound also controls the integral of the absolute value
of a compact continuous input. -/
theorem u4_regular_signed_kernel_compact_abs_L2_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t)
    (U : Set (Vec d)) (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ U, ∀ f : Vec d → ℝ,
      Continuous f → HasCompactSupport f →
      (∫ y, |f y| ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        C * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal := by
  obtain ⟨C, hC, hb⟩ := u4_regular_signed_kernel_L2_bound_on_bounded_open
    hd ω lam Λ hΛ hω t ht U hU hUb
  refine ⟨C, hC, ?_⟩
  intro x hx f hf hfc
  have h := hb x hx (fun y => |f y|) hf.abs hfc.abs
  have he : eLpNorm (fun y => |f y|) 2 (physicalReversibleMeasure ω hd lam) =
      eLpNorm f 2 (physicalReversibleMeasure ω hd lam) := by
    apply eLpNorm_congr_norm_ae hf.abs.aestronglyMeasurable hf.aestronglyMeasurable
    filter_upwards with y
    simp only [Real.norm_eq_abs, abs_abs]
  rw [he, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at h
  exact h

#print axioms u4_regular_signed_kernel_compact_abs_L2_bound

/-- Every physical L² class is integrable against each positive-time signed row. -/
theorem u4_regular_signed_kernel_integrable_L2 {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (x : Vec d) :
    Integrable (fun y => f y) (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) := by
  let μ := physicalReversibleMeasure ω hd lam
  let ν := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  let : IsFiniteMeasure ν := ⟨lt_of_le_of_lt
    ((u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω).measure_univ_le_one t x)
    ENNReal.one_lt_top⟩
  obtain ⟨g, hg, hlim⟩ := u4_physical_L2_compact_approximation hd ω lam f
  let G := fun n => (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g n)
    (hg n).1 (hg n).2).toLp (g n)
  have hG : Tendsto G atTop (𝓝 f) := u4_physical_compact_approximation_Lp hd ω lam f g hg hlim
  obtain ⟨ns, hns, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hG).exists_seq_tendsto_ae
  have heq : ∀ᵐ y ∂μ, ∀ n, G (ns n) y = g (ns n) y := by
    apply ae_all_iff.mpr
    intro n
    exact (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g (ns n))
      (hg (ns n)).1 (hg (ns n)).2).coeFn_toLp
  have hcon : ∀ᵐ y ∂μ, Tendsto (fun n => g (ns n) y) atTop (𝓝 (f y)) := by
    filter_upwards [hsub, heq] with y hy he
    simpa only [Function.comp_def, he] using hy
  have hrow := (u4_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht x).ae_le
    ((Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp hcon)
  have hmeas : AEStronglyMeasurable (fun y => f y) ν :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hg (ns n)).1.aestronglyMeasurable) hrow
  obtain ⟨C, hC, hb⟩ := u4_regular_signed_kernel_compact_abs_L2_bound
    hd ω lam Λ hΛ hω t ht (Metric.ball x 1) Metric.isOpen_ball Metric.isBounded_ball
  have hx : x ∈ Metric.ball x 1 := Metric.mem_ball_self (by norm_num)
  have hnorm : ∀ᶠ n in atTop, ‖G (ns n)‖ ≤ ‖f‖ + 1 := by
    have hh := (Metric.tendsto_atTop.mp (hG.comp hns.tendsto_atTop)) 1 (by norm_num)
    obtain ⟨N, hN⟩ := hh
    filter_upwards [eventually_ge_atTop N] with n hn
    have h := hN n hn
    exact norm_le_norm_add_const_of_dist_le h.le
  have hbound : ∀ᶠ n in atTop, eLpNorm (g (ns n)) 1 ν ≤ ENNReal.ofReal (C * (‖f‖ + 1)) := by
    filter_upwards [hnorm] with n hn
    have hi : Integrable (g (ns n)) ν := (hg (ns n)).1.integrable_of_hasCompactSupport (hg (ns n)).2
    have hh := hb x hx (g (ns n)) (hg (ns n)).1 (hg (ns n)).2
    have he : (eLpNorm (g (ns n)) 2 μ).toReal = ‖G (ns n)‖ := by
      rw [Lp.norm_def, eLpNorm_congr_ae
        (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g (ns n))
          (hg (ns n)).1 (hg (ns n)).2).coeFn_toLp]
    rw [he] at hh
    rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hi]
    apply ENNReal.ofReal_le_ofReal
    simp only [Real.norm_eq_abs]
    exact hh.trans (mul_le_mul_of_nonneg_left hn hC.le)
  have hfin := Lp.eLpNorm_le_of_ae_tendsto hbound
    (fun n => (hg (ns n)).1.aestronglyMeasurable) hmeas hrow
  apply memLp_one_iff_integrable.mp
  exact lt_of_le_of_lt hfin ENNReal.ofReal_lt_top

#print axioms u4_regular_signed_kernel_integrable_L2

/-- The compact row estimate extends to all physical L² classes. -/
theorem u4_regular_signed_kernel_L2_integral_abs_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t)
    (U : Set (Vec d)) (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ U, ∀ f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam),
      (∫ y, |f y| ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hb⟩ := u4_regular_signed_kernel_compact_abs_L2_bound
    hd ω lam Λ hΛ hω t ht U hU hUb
  refine ⟨C, hC, ?_⟩
  intro x hx f
  let μ := physicalReversibleMeasure ω hd lam
  let ν := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  let : IsFiniteMeasure ν := ⟨lt_of_le_of_lt
    ((u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω).measure_univ_le_one t x)
    ENNReal.one_lt_top⟩
  obtain ⟨g, hg, hlim⟩ := u4_physical_L2_compact_approximation hd ω lam f
  let G := fun n => (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g n)
    (hg n).1 (hg n).2).toLp (g n)
  have hG : Tendsto G atTop (𝓝 f) := u4_physical_compact_approximation_Lp hd ω lam f g hg hlim
  obtain ⟨ns, hns, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hG).exists_seq_tendsto_ae
  have heq : ∀ᵐ y ∂μ, ∀ n, G (ns n) y = g (ns n) y := by
    apply ae_all_iff.mpr
    intro n
    exact (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g (ns n))
      (hg (ns n)).1 (hg (ns n)).2).coeFn_toLp
  have hcon : ∀ᵐ y ∂μ, Tendsto (fun n => g (ns n) y) atTop (𝓝 (f y)) := by
    filter_upwards [hsub, heq] with y hy he
    simpa only [Function.comp_def, he] using hy
  have hrow := (u4_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht x).ae_le
    ((Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp hcon)
  have hi := u4_regular_signed_kernel_integrable_L2 hd ω lam Λ hΛ hω t ht f x
  have hbound (n : ℕ) : eLpNorm (g (ns n)) 1 ν ≤ ENNReal.ofReal (C * ‖G (ns n)‖) := by
    have hgi : Integrable (g (ns n)) ν := (hg (ns n)).1.integrable_of_hasCompactSupport (hg (ns n)).2
    have hh := hb x hx (g (ns n)) (hg (ns n)).1 (hg (ns n)).2
    have he : (eLpNorm (g (ns n)) 2 μ).toReal = ‖G (ns n)‖ := by
      rw [Lp.norm_def, eLpNorm_congr_ae
        (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g (ns n))
          (hg (ns n)).1 (hg (ns n)).2).coeFn_toLp]
    rw [he] at hh
    rw [eLpNorm_one_eq_lintegral_enorm hgi.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hgi]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.norm_eq_abs] using hh
  have hconv : Tendsto (fun n => ENNReal.ofReal (C * ‖G (ns n)‖)) atTop
      (𝓝 (ENNReal.ofReal (C * ‖f‖))) :=
    ENNReal.continuous_ofReal.tendsto _ |>.comp
      ((tendsto_const_nhds.mul ((hG.comp hns.tendsto_atTop).norm)))
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 1)
    (fun n => (hg (ns n)).1.aestronglyMeasurable) (fun y => f y) hi.aestronglyMeasurable hrow
  have hle : eLpNorm (fun y => f y) 1 ν ≤ ENNReal.ofReal (C * ‖f‖) :=
    hfatou.trans ((Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound)).trans_eq hconv.liminf_eq)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _),
    ENNReal.toReal_ofReal (mul_nonneg hC.le (norm_nonneg _))] at hreal
  simpa only [Real.norm_eq_abs] using hreal

#print axioms u4_regular_signed_kernel_L2_integral_abs_bound

/-- The actual signed kernel acts continuously on every physical L² class at every start. -/
theorem u4_regular_signed_pointwise_continuous_L2_kernel_action
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (∀ x, Integrable (fun y => f y)
      (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ∧
    Continuous (fun x => ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
    (fun x => ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) =ᵐ[physicalReversibleMeasure ω hd lam]
      (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f : Vec d → ℝ) := by
  let μ := physicalReversibleMeasure ω hd lam
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  have hi : ∀ x, Integrable (fun y => f y) (P t x) :=
    u4_regular_signed_kernel_integrable_L2 hd ω lam Λ hΛ hω t ht f
  refine ⟨hi, ?_, ?_⟩
  · obtain ⟨g, hg, hlim⟩ := u4_physical_L2_compact_approximation hd ω lam f
    let G := fun n => (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g n)
      (hg n).1 (hg n).2).toLp (g n)
    let H := fun n x => ∫ y, g n y ∂P t x
    have hG : Tendsto G atTop (𝓝 f) := u4_physical_compact_approximation_Lp hd ω lam f g hg hlim
    have hH : ∀ n, Continuous (H n) := by
      intro n
      let v : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨g n, (hg n).1⟩, (hg n).2.is_zero_at_infty⟩
      change Continuous (fun x => ∫ y, v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)
      simp_rw [u2RegularC0KernelSemigroup_integral]
      exact (u2RegularC0Semigroup hd ω lam Λ hΛ hω t v).continuous
    have ha : Tendsto (fun n => dist (G n) f) atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.mp hG
    obtain ⟨u, hu, hpoint⟩ := u4_continuous_limit_of_local_cauchy H hH
      (fun n => dist (G n) f) ha (fun _ => dist_nonneg)
      (u4_compact_kernel_local_cauchy_bound hd ω lam Λ hΛ hω t ht f g hg)
    have heq : ∀ x, u x = ∫ y, f y ∂P t x := by
      intro x
      obtain ⟨C, hC, hb⟩ := u4_regular_signed_kernel_L2_integral_abs_bound
        hd ω lam Λ hΛ hω t ht (Metric.ball x 1) Metric.isOpen_ball Metric.isBounded_ball
      have hx : x ∈ Metric.ball x 1 := Metric.mem_ball_self (by norm_num)
      have herr (n : ℕ) : |(∫ y, f y ∂P t x) - H n x| ≤ C * dist (G n) f := by
        let : IsFiniteMeasure (P t x) := ⟨lt_of_le_of_lt (P.measure_univ_le_one t x) ENNReal.one_lt_top⟩
        have hgi : Integrable (g n) (P t x) := (hg n).1.integrable_of_hasCompactSupport (hg n).2
        have hae : (fun y => (f - G n) y) =ᵐ[P t x] (fun y => f y - g n y) := by
          apply (u4_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht x).ae_le
          apply (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp
          filter_upwards [Lp.coeFn_sub f (G n),
            (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (g n) (hg n).1 (hg n).2).coeFn_toLp] with y hs hg'
          change (f - G n) y = f y - G n y at hs
          change G n y = g n y at hg'
          rw [hg'] at hs
          exact hs
        have hbn := hb x hx (f - G n)
        have habs : (∫ y, |(f - G n) y| ∂P t x) = ∫ y, |f y - g n y| ∂P t x :=
          integral_congr_ae (hae.mono fun _ h => congrArg abs h)
        rw [habs, ← dist_eq_norm, dist_comm f (G n)] at hbn
        calc
          _ = ‖∫ y, (f y - g n y) ∂P t x‖ := by rw [integral_sub (hi x) hgi]; rfl
          _ ≤ ∫ y, ‖f y - g n y‖ ∂P t x := norm_integral_le_integral_norm _
          _ ≤ C * dist (G n) f := by simpa only [Real.norm_eq_abs] using hbn
      have hz : Tendsto (fun n => |(∫ y, f y ∂P t x) - H n x|) atTop (𝓝 0) :=
        squeeze_zero (fun n => abs_nonneg _) herr (by simpa using ha.const_mul C)
      have hh : Tendsto (fun n => H n x) atTop (𝓝 (∫ y, f y ∂P t x)) := by
        apply tendsto_iff_dist_tendsto_zero.mpr
        simpa only [Real.dist_eq, abs_sub_comm] using hz
      exact tendsto_nhds_unique (hpoint x) hh
    have hfun : u = (fun x => ∫ y, f y ∂P t x) := funext heq
    rw [← hfun]
    exact hu
  · filter_upwards [(u2_regular_kernel_integral_ae_L2 hd ω lam Λ hΛ hω t
        (fun y => f y) (Lp.memLp f)).2] with x hx
    simpa only [Lp.toLp_coeFn] using hx

#print axioms u4_regular_signed_pointwise_continuous_L2_kernel_action

end EinsteinFull
