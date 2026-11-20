import EinsteinFull.Calculus.SbxBCenteredTubeChainR03

/-!
# Geometric decay of killed survival

An upper bound on the one-step mass of a killed semigroup iterates to a
geometric survival bound. The specialization uses the actual GMP path law.
-/

open MeasureTheory ProbabilityTheory
open EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A uniform one-step mass bound iterates under the semigroup law. -/
theorem killed_kernel_survival_le_pow {X : Type*} [MeasurableSpace X]
    (K : ℝ≥0 → Kernel X X) (hfinite : ∀ t, IsFiniteKernel (K t))
    (hadd : ∀ s t, K (s + t) = (K t).comp (K s))
    (hzero : ∀ x, K 0 x Set.univ ≤ 1) (τ : ℝ≥0) (q : ℝ≥0∞)
    (hstep : ∀ x, K τ x Set.univ ≤ q) :
    ∀ n : ℕ, ∀ x, K ((n : ℝ≥0) * τ) x Set.univ ≤ q ^ n := by
  intro n
  induction n with
  | zero =>
      intro x
      simpa only [Nat.cast_zero, zero_mul, pow_zero] using hzero x
  | succ n ih =>
      intro x
      letI := hfinite ((n : ℝ≥0) * τ)
      letI := hfinite τ
      calc
        K (((n + 1 : ℕ) : ℝ≥0) * τ) x Set.univ =
            ∫⁻ y, K τ y Set.univ ∂K ((n : ℝ≥0) * τ) x := by
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hadd,
            Kernel.comp_apply' _ _ _ MeasurableSet.univ]
        _ ≤ ∫⁻ _y, q ∂K ((n : ℝ≥0) * τ) x := lintegral_mono hstep
        _ = q * K ((n : ℝ≥0) * τ) x Set.univ := by simp
        _ ≤ q * q ^ n := by simpa only [mul_comm] using mul_le_mul_left (ih x) q
        _ = q ^ (n + 1) := by rw [pow_succ']

/-- Uniform one-step strict survival bounds imply geometric survival for GMP paths. -/
theorem gmp_survival_le_pow {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (τ : ℝ≥0) (q : ℝ≥0∞)
    (hstep : ∀ x, G.pathLaw x {γ : Path d | ∀ t : ℝ≥0, t ≤ τ → γ t ∈ U} ≤ q) :
    ∀ n : ℕ, ∀ x, G.pathLaw x
      {γ : Path d | ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * τ → γ t ∈ U} ≤ q ^ n := by
  have hevent (t : ℝ≥0) (x : Vec d) :
      gmpKilledEndpointKernel G U hU t x Set.univ = G.pathLaw x
        {γ : Path d | ∀ s : ℝ≥0, s ≤ t → γ s ∈ U} := by
    rw [gmpKilledEndpointKernel_apply, Measure.map_apply (measurable_pathPosition t)
      MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ]
    simp only [Set.univ_inter, lt_localityExitTime_iff U hU]
  have hzero : ∀ x, gmpKilledEndpointKernel G U hU 0 x Set.univ ≤ 1 := by
    intro x
    rw [hevent]
    haveI : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
    simpa only [measure_univ] using (measure_mono (Set.subset_univ _) :
      G.pathLaw x {γ : Path d | ∀ t : ℝ≥0, t ≤ 0 → γ t ∈ U} ≤ G.pathLaw x Set.univ)
  have hs : ∀ x, gmpKilledEndpointKernel G U hU τ x Set.univ ≤ q := by
    intro x
    rw [hevent]
    exact hstep x
  intro n x
  rw [← hevent]
  exact killed_kernel_survival_le_pow (gmpKilledEndpointKernel G U hU)
    (isFiniteKernel_gmpKilledEndpointKernel G U hU)
    (gmpKilledEndpointKernel_add G U hU) hzero τ q hs n x

/-- A uniform positive one-step escape probability yields a uniformly small survival mass. -/
theorem exists_gmp_survival_le {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (τ : ℝ≥0) (ε η : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η)
    (hstep : ∀ x, G.pathLaw x {γ : Path d | ∀ t : ℝ≥0, t ≤ τ → γ t ∈ U} ≤
      ENNReal.ofReal (1 - ε)) :
    ∃ n : ℕ, ∀ x, G.pathLaw x
      {γ : Path d | ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * τ → γ t ∈ U} ≤ ENNReal.ofReal η := by
  have hq : 1 - ε < 1 := by linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hη hq
  refine ⟨n, fun x => ?_⟩
  calc
    _ ≤ ENNReal.ofReal (1 - ε) ^ n := gmp_survival_le_pow G U hU τ _ hstep n x
    _ = ENNReal.ofReal ((1 - ε) ^ n) := (ENNReal.ofReal_pow (sub_nonneg.mpr hε1) n).symm
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hn.le

end EinsteinFull.Regeneration
