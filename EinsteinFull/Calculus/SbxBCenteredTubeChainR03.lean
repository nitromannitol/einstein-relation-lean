import EinsteinFull.Work.W1.GMPKilledSemigroupSupport
import EinsteinFull.Calculus.FellerRegularSet
import EinsteinFull.Calculus.SbxAGlobalReducedKernelR04
import EinsteinRelation.Regeneration.RenewalCarriers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Centered killed-path iteration

The finite chain uses one literal killed-return estimate for each starting point
in an inner set.  The existence of that local estimate is a separate analytic
question.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
noncomputable section

/-- Iterate a single return estimate for a finite kernel semigroup.  The
zero-time condition is required only on the set used in the iteration. -/
@[nolint unusedArguments]
theorem b_killed_kernel_return_iterate {X : Type*} [MeasurableSpace X]
    (K : ℝ≥0 → Kernel X X) (hfinite : ∀ t, IsFiniteKernel (K t))
    (hadd : ∀ s t, K (s + t) = (K t).comp (K s))
    (A : Set X) (hA : MeasurableSet A)
    (hzero : ∀ x ∈ A, K 0 x A = 1) (τ : ℝ≥0) (η : ℝ≥0∞)
    (hstep : ∀ x ∈ A, η ≤ K τ x A) :
    ∀ n : ℕ, ∀ x ∈ A, η ^ n ≤ K ((n : ℝ≥0) * τ) x A := by
  classical
  intro n
  induction n with
  | zero =>
      intro x hx
      simpa only [Nat.cast_zero, zero_mul, pow_zero, hzero x hx] using
        (le_refl (1 : ℝ≥0∞))
  | succ n ih =>
      intro x hx
      haveI := hfinite τ
      haveI := hfinite ((n : ℝ≥0) * τ)
      have hpoint : ∀ y, A.indicator (fun _ => η ^ n) y ≤
          K ((n : ℝ≥0) * τ) y A := by
        intro y
        by_cases hy : y ∈ A
        · simpa only [Set.indicator_of_mem hy] using ih y hy
        · simp only [Set.indicator_of_notMem hy, zero_le]
      calc
        η ^ (n + 1) = η ^ n * η := pow_succ η n
        _ ≤ η ^ n * K τ x A := by
          simpa only [mul_comm] using (mul_le_mul_left (hstep x hx) (η ^ n))
        _ = ∫⁻ y, A.indicator (fun _ => η ^ n) y ∂K τ x := by
          rw [lintegral_indicator_const hA]
        _ ≤ ∫⁻ y, K ((n : ℝ≥0) * τ) y A ∂K τ x := lintegral_mono hpoint
        _ = K (((n + 1 : ℕ) : ℝ≥0) * τ) x A := by
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
            add_comm ((n : ℝ≥0) * τ) τ, hadd,
            Kernel.comp_apply' _ _ _ hA]

/-- A path-kernel form of the finite chain.  The kernel `K` is required to be
the actual survival-and-endpoint law, and its composition law is the killed
form of deterministic Markov restart.  No endpoint bound at later times is
assumed. -/
theorem b_path_survival_return_iterate
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (P : Kernel X Ω) (Y : ℝ≥0 → Ω → X) (U A : Set X)
    (K : ℝ≥0 → Kernel X X) (hfinite : ∀ t, IsFiniteKernel (K t))
    (hadd : ∀ s t, K (s + t) = (K t).comp (K s))
    (hA : MeasurableSet A) (hzero : ∀ x ∈ A, K 0 x A = 1)
    (hpath : ∀ t x, K t x A = P x
      {γ | (∀ s : ℝ≥0, s ≤ t → Y s γ ∈ U) ∧ Y t γ ∈ A})
    (τ : ℝ≥0) (η : ℝ≥0∞)
    (hstep : ∀ x ∈ A, η ≤ P x
      {γ | (∀ s : ℝ≥0, s ≤ τ → Y s γ ∈ U) ∧ Y τ γ ∈ A}) :
    ∀ n : ℕ, ∀ x ∈ A, η ^ n ≤ P x
      {γ | (∀ s : ℝ≥0, s ≤ (n : ℝ≥0) * τ → Y s γ ∈ U) ∧
        Y ((n : ℝ≥0) * τ) γ ∈ A} := by
  have hs : ∀ x ∈ A, η ≤ K τ x A := by
    intro x hx
    rw [hpath]
    exact hstep x hx
  intro n x hx
  rw [← hpath]
  exact b_killed_kernel_return_iterate K hfinite hadd A hA hzero τ η hs n x hx

/-- For a GMP path law, a one-step strict survival-and-return estimate
iterates through the whole time interval, with the same return set. -/
theorem b_gmp_centered_return_iterate
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
    {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U A : Set (Vec d)) (hU : IsOpen U) (hA : MeasurableSet A) (hAU : A ⊆ U)
    (τ : ℝ≥0) (η : ℝ≥0∞)
    (hstep : ∀ x ∈ A, η ≤ G.pathLaw x
      {γ : Path d | (∀ t : ℝ≥0, t ≤ τ → γ t ∈ U) ∧ γ τ ∈ A}) :
    ∀ n : ℕ, ∀ x ∈ A, η ^ n ≤ G.pathLaw x
      {γ : Path d | (∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * τ → γ t ∈ U) ∧
        γ ((n : ℝ≥0) * τ) ∈ A} := by
  classical
  have hevent (t : ℝ≥0) (x : Vec d) :
      gmpKilledEndpointKernel G U hU t x A = G.pathLaw x
        {γ : Path d | (∀ s : ℝ≥0, s ≤ t → γ s ∈ U) ∧ γ t ∈ A} := by
    rw [gmpKilledEndpointKernel_apply, Measure.map_apply (measurable_pathPosition t) hA,
      Measure.restrict_apply ((measurable_pathPosition t) hA)]
    apply congrArg (G.pathLaw x)
    ext γ
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      lt_localityExitTime_iff U hU, pathPosition, and_comm]
  have hzero : ∀ x ∈ A, gmpKilledEndpointKernel G U hU 0 x A = 1 := by
    intro x hx
    rw [gmpKilledEndpointKernel_zero, Set.indicator_of_mem (hAU hx), Measure.dirac_apply' _ hA]
    simp [hx]
  have hs : ∀ x ∈ A, η ≤ gmpKilledEndpointKernel G U hU τ x A := by
    intro x hx
    rw [hevent]
    exact hstep x hx
  intro n x hx
  rw [← hevent]
  exact b_killed_kernel_return_iterate (gmpKilledEndpointKernel G U hU)
    (isFiniteKernel_gmpKilledEndpointKernel G U hU)
    (gmpKilledEndpointKernel_add G U hU) A hA hzero τ η hs n x hx

/-- Strict survival through a fixed time together with an endpoint condition is
measurable for continuous paths. -/
theorem b_centered_survival_return_measurable {d : ℕ}
    (U A : Set (Vec d)) (hU : IsOpen U) (hA : MeasurableSet A) (t : ℝ≥0) :
    MeasurableSet {γ : Path d | (∀ s : ℝ≥0, s ≤ t → γ s ∈ U) ∧ γ t ∈ A} := by
  have heq : {γ : Path d | (∀ s : ℝ≥0, s ≤ t → γ s ∈ U) ∧ γ t ∈ A} =
      {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ} ∩
        (pathPosition t) ⁻¹' A := by
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      lt_localityExitTime_iff U hU, pathPosition]
  rw [heq]
  exact (measurableSet_localitySurvival U hU t).inter ((measurable_pathPosition t) hA)

/-- The closed centered tube on any finite interval is a measurable path
event. -/
theorem b_centered_closed_tube_measurable {d : ℕ} (x : Vec d) (R : ℝ) (t : ℝ≥0) :
    MeasurableSet {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0) t,
      euclideanNorm (γ s - x) ≤ R} := by
  have heq : {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0) t,
      euclideanNorm (γ s - x) ≤ R} =
      ⋂ (s : ℝ≥0) (_ : s ∈ Set.Icc (0 : ℝ≥0) t),
        {γ : Path d | euclideanNorm (γ s - x) ≤ R} := by
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact (isClosed_iInter fun s => isClosed_iInter fun _ =>
    isClosed_le ((Calculus.Feller.continuous_euclideanNorm d).comp
      ((continuous_eval_const s).sub continuous_const)) continuous_const).measurableSet

/-- The still-needed analytic input: one rescaled short step, from any point in
the inner Euclidean ball, survives strictly in the outer ball and returns to
the inner ball.  The constants are independent of the environment and force. -/
@[nolint defsWithUnderscore]
def b_centered_local_return_input : Prop :=
  ∀ {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
    ∃ h η : ℝ, 0 < h ∧ 0 < η ∧ η ≤ 1 ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
        (h0 : 0 < |lam|) (h1 : |lam| ≤ 1) (P : QuenchedPathLaws d),
        IsGMPReducedKernel hd Q.ellipticity_parameter Q |lam| h0.le h1 P →
        ∀ᵐ ω ∂Q.measure, ∀ c y : Vec d,
          euclideanNorm (y - c) < (l / |lam|) / 4 →
          ENNReal.ofReal η ≤ P (y, ω)
            {γ : Path d |
              (∀ s : ℝ≥0, s ≤ Real.toNNReal (h / |lam| ^ 2) →
                euclideanNorm (γ s - c) < (l / |lam|) / 2) ∧
              euclideanNorm (γ (Real.toNNReal (h / |lam| ^ 2)) - c) <
                (l / |lam|) / 4}

/-- The structural number of scaled steps covers the complete renewal time.
No lower force cutoff is used. -/
theorem b_scaled_steps_cover_regenDelta (h : ℝ) (hh : 0 < h) :
    ∃ n : ℕ, ∀ lam : ℝ,
      EinsteinRelation.Regeneration.Renewal.regenDelta |lam| ≤
        (n : ℝ≥0) * Real.toNNReal (h / |lam| ^ 2) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / h)
  have hnh : (1 : ℝ) ≤ (n : ℝ) * h := le_of_lt ((div_lt_iff₀ hh).mp hn)
  refine ⟨n, ?_⟩
  intro lam
  apply NNReal.coe_le_coe.mp
  change ((Real.toNNReal ((|lam| ^ 2)⁻¹) : ℝ≥0) : ℝ) ≤
    (((n : ℝ≥0) * Real.toNNReal (h / |lam| ^ 2) : ℝ≥0) : ℝ)
  rw [NNReal.coe_mul, NNReal.coe_natCast,
    Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg |lam|)),
    Real.coe_toNNReal _ (div_nonneg hh.le (sq_nonneg |lam|))]
  calc
    (|lam| ^ 2)⁻¹ = 1 / |lam| ^ 2 := (one_div _).symm
    _ ≤ ((n : ℝ) * h) / |lam| ^ 2 := div_le_div_of_nonneg_right hnh (sq_nonneg _)
    _ = (n : ℝ) * (h / |lam| ^ 2) := mul_div_assoc _ _ _

/-- A single local killed-return estimate implies the centered tube interface
for every positive width and the full signed-force range.  This is a
conditional consumer, not a proof of the local estimate. -/
theorem b_centered_tube_of_local_return (hlocal : b_centered_local_return_input) :
    ∀ {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
          (h0 : 0 < |lam|) (h1 : |lam| ≤ 1),
          ∃ P : QuenchedPathLaws d,
            IsGMPReducedKernel hd Q.ellipticity_parameter Q |lam| h0.le h1 P ∧
            ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
              ENNReal.ofReal ε ≤ P (x, ω)
                {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0)
                    (EinsteinRelation.Regeneration.Renewal.regenDelta |lam|),
                  euclideanNorm (γ s - x) ≤ (l / |lam|) / 2} := by
  intro d hd Λ₀ r₀ l hl
  obtain ⟨h, η, hh, hη, hη1, hstep⟩ := hlocal hd Λ₀ r₀ l hl
  obtain ⟨n, hcover⟩ := b_scaled_steps_cover_regenDelta h hh
  refine ⟨η ^ n, pow_pos hη _, pow_le_one₀ hη.le hη1, ?_⟩
  intro Q lam h0 h1
  obtain ⟨P, hP, _, _, _⟩ := SbxASection3R04.global_reduced_kernel_exists_abs hd Q lam h1
  refine ⟨P, hP, ?_⟩
  filter_upwards [hP, hstep Q lam h0 h1 P hP] with ω hreal hlocalω
  obtain ⟨hω, G, hrow⟩ := hreal
  intro x
  let U : Set (Vec d) := {y | euclideanNorm (y - x) < (l / |lam|) / 2}
  let A : Set (Vec d) := {y | euclideanNorm (y - x) < (l / |lam|) / 4}
  have hU : IsOpen U :=
    isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
      (continuous_id.sub continuous_const)) continuous_const
  have hA : MeasurableSet A :=
    (isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
      (continuous_id.sub continuous_const)) continuous_const).measurableSet
  have hAU : A ⊆ U := by
    intro y hy
    change euclideanNorm (y - x) < (l / |lam|) / 4 at hy
    change euclideanNorm (y - x) < (l / |lam|) / 2
    have hp : 0 < l / |lam| := div_pos hl h0
    linarith
  have hx : x ∈ A := by
    change euclideanNorm (x - x) < (l / |lam|) / 4
    have hz : euclideanNorm (0 : Vec d) = 0 := by
      simp [euclideanNorm, euclideanSq, dot]
    simpa only [sub_self, hz] using
      (div_pos (div_pos hl h0) (by norm_num : (0 : ℝ) < 4))
  have hs : ∀ y ∈ A, ENNReal.ofReal η ≤ G.pathLaw y
      {γ : Path d | (∀ s : ℝ≥0, s ≤ Real.toNNReal (h / |lam| ^ 2) → γ s ∈ U) ∧
        γ (Real.toNNReal (h / |lam| ^ 2)) ∈ A} := by
    intro y hy
    rw [← hrow y]
    exact hlocalω x y hy
  have hchain := b_gmp_centered_return_iterate G U A hU hA hAU
    (Real.toNNReal (h / |lam| ^ 2)) (ENNReal.ofReal η) hs n x hx
  rw [hrow x]
  calc
    ENNReal.ofReal (η ^ n) = (ENNReal.ofReal η) ^ n := ENNReal.ofReal_pow hη.le n
    _ ≤ G.pathLaw x
        {γ : Path d | (∀ s : ℝ≥0,
            s ≤ (n : ℝ≥0) * Real.toNNReal (h / |lam| ^ 2) → γ s ∈ U) ∧
          γ ((n : ℝ≥0) * Real.toNNReal (h / |lam| ^ 2)) ∈ A} := hchain
    _ ≤ G.pathLaw x
        {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0)
            (EinsteinRelation.Regeneration.Renewal.regenDelta |lam|),
          euclideanNorm (γ s - x) ≤ (l / |lam|) / 2} := by
      apply measure_mono
      intro γ hγ s hs
      exact le_of_lt (hγ.1 s (hs.2.trans (hcover lam)))

end
end EinsteinFull
