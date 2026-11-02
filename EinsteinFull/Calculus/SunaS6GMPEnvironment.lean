import EinsteinFull.Calculus.U6RegularSignedPathRealization
import EinsteinFull.Calculus.U5RegularStoppingRestart
import Mathlib.MeasureTheory.Function.Holder
import EinsteinFull.Calculus.PhysicalGaugeCoercivitySupport
import EinsteinFull.Blueprint.G1.Proofs.SbxS9RealizationUniqueness

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal

namespace EinsteinFull

/-- A single measurable origin law realizes the regular GMP construction and
solves the physical martingale problem almost surely. -/
theorem s6_foundation_gmp_physical_origin_law_and_mp
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ K : ProbabilityTheory.Kernel (FieldPair d) (Path d),
      ProbabilityTheory.IsMarkovKernel K ∧
      IsGMPPhysicalOriginLaw hd hΛ₀ Q lam h0 h1 K ∧
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (K ω)) :=
  u6_foundation_regular_signed_origin_law_and_mp hd hΛ₀ Q lam h0 h1

/-- The GMP origin law, martingale problem and probability measures use the
same measurable kernel. -/
theorem s6_gmp_origin_law_same_kernel_mp
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (hΛ : 1 ≤ Λ)
    (Q : EnvironmentLaw d Λ r) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      IsGMPPhysicalOriginLaw hd hΛ Q lam h0 h1 K ∧
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (K ω)) ∧
      (∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (K ω)) := by
  obtain ⟨K, hK, hGMP, hMP⟩ :=
    s6_foundation_gmp_physical_origin_law_and_mp hd hΛ Q lam h0 h1
  letI : IsMarkovKernel K := hK
  exact ⟨K, hK, hGMP, hMP, Filter.Eventually.of_forall fun _ => inferInstance⟩

/-- A uniformly bounded coefficient defect controls an actual physical L²
pairing. This estimate applies to individual diffusion and drift form entries. -/
theorem s6_physical_coefficient_pairing_bound {d : ℕ}
    (c : Vec d → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hc : ∀ x, ‖c x‖ ≤ ε)
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖∫ x, c x * u x * v x‖ ≤
      ε * (Real.sqrt (∫ x, ‖u x‖ ^ 2) * Real.sqrt (∫ x, ‖v x‖ ^ 2)) := by
  have hp : Integrable (fun x => ‖u x‖ * ‖v x‖) volume :=
    (Lp.memLp u).norm.integrable_mul (Lp.memLp v).norm
  have hb := norm_integral_le_of_norm_le (f := fun x => c x * u x * v x)
    (hp.const_mul ε)
    (Filter.Eventually.of_forall fun x => by
      simp only [norm_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hc x) (norm_nonneg _)) (norm_nonneg _))
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using (Lp.memLp u)) (by simpa using (Lp.memLp v))
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
  calc
    _ ≤ ∫ x, ε * (‖u x‖ * ‖v x‖) := hb
    _ = ε * ∫ x, ‖u x‖ * ‖v x‖ := integral_const_mul _ _
    _ ≤ ε * (Real.sqrt (∫ x, ‖u x‖ ^ 2) * Real.sqrt (∫ x, ‖v x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hh hε

/-- A matrix coefficient defect controls the sum of its L² pairings. -/
theorem s6_physical_matrix_pairing_bound {d : ℕ}
    (c : Fin d → Fin d → Vec d → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hc : ∀ j k x, ‖c j k x‖ ≤ ε)
    (u v : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖∑ j, ∑ k, ∫ x, c j k x * u k x * v j x‖ ≤
      ε * ((∑ k, ‖u k‖) * (∑ j, ‖v j‖)) := by
  classical
  have hentry (j k : Fin d) :
      ‖∫ x, c j k x * u k x * v j x‖ ≤ ε * (‖u k‖ * ‖v j‖) := by
    have h := s6_physical_coefficient_pairing_bound (c j k) ε hε (hc j k) (u k) (v j)
    simpa only [← physicalL2_norm_sq, Real.sqrt_sq_eq_abs, abs_norm] using h
  calc
    _ ≤ ∑ j, ∑ k, ‖∫ x, c j k x * u k x * v j x‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j, ∑ k, ε * (‖u k‖ * ‖v j‖) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hentry j k
    _ = ε * ((∑ k, ‖u k‖) * (∑ j, ‖v j‖)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]

/-- The diffusion-form coefficient defect is bounded on the physical L²
gradient components, with the integral taken over the actual finite sum. -/
theorem s6_physical_diffusion_defect_bound {d : ℕ}
    (c : Fin d → Fin d → Vec d → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hc : ∀ j k x, ‖c j k x‖ ≤ ε)
    (hm : ∀ j k, MemLp (c j k) ∞ (volume : Measure (Vec d)))
    (u v : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖∫ x, ∑ j, ∑ k, c j k x * u k x * v j x‖ ≤
      ε * ((∑ k, ‖u k‖) * (∑ j, ‖v j‖)) := by
  classical
  have hi (j k : Fin d) : Integrable (fun x => c j k x * u k x * v j x) volume :=
    ((hm j k).mul (r := 2) (Lp.memLp (u k))).integrable_mul (Lp.memLp (v j))
  have hs (j : Fin d) : Integrable (fun x => ∑ k, c j k x * u k x * v j x) volume :=
    integrable_finsetSum _ fun k _ => hi j k
  have heq : (∫ x, ∑ j, ∑ k, c j k x * u k x * v j x) =
      ∑ j, ∑ k, ∫ x, c j k x * u k x * v j x := by
    rw [integral_finsetSum _ fun j _ => hs j]
    exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun k _ => hi j k
  rw [heq]
  exact s6_physical_matrix_pairing_bound c ε hε hc u v

/-- Every supplied realization has the same almost-everywhere transition
action as the regular physical semigroup. -/
theorem s6_supplied_gmp_transition_C0_action_ae
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1) :
    ∀ t : ℝ≥0, 0 < t → ∀ f : ZeroAtInftyContinuousMap (Vec d) ℝ,
      ∀ᵐ x ∂(volume : Measure (Vec d)),
        (∫ y, f y ∂r.transitionKernel t x) =
          ∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t x := by
  obtain ⟨K, hK, hfdd⟩ := u6_regular_signed_continuous_kernel_exists hd ω lam Λ hΛ hω
  let : IsMarkovKernel K := hK
  have hac := u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω
  obtain ⟨R, _, hR⟩ :=
    u2_regular_fixed_environment_realization_of_ac_fdd hd ω lam Λ hΛ hω h0 h1 K hfdd hac
  intro t _ f
  have he := SbxS9RealizationUniqueness.transitionKernel_eq_ae hd hΛ r R t
  have hv := (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp he
  filter_upwards [hv] with x hx
  rw [hx, hR]

/-- Any supplied GMP realization has the canonical transition kernels, at
every starting point. -/
theorem s6_supplied_gmp_transition_eq_canonical_unconditional
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1) :
    ∀ t : ℝ≥0, r.transitionKernel t = (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t := by
  obtain ⟨K, hK, hfdd⟩ := u6_regular_signed_continuous_kernel_exists hd ω lam Λ hΛ hω
  let : IsMarkovKernel K := hK
  have hac := u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω
  obtain ⟨R, _, hR⟩ :=
    u2_regular_fixed_environment_realization_of_ac_fdd hd ω lam Λ hΛ hω h0 h1 K hfdd hac
  apply u5_supplied_gmp_transition_eq_of_ae_C0_action hd ω lam Λ hΛ hω h0 h1 r
  intro t _ f
  have he := SbxS9RealizationUniqueness.transitionKernel_eq_ae hd hΛ r R t
  have hv := (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp he
  filter_upwards [hv] with x hx
  rw [hx, hR]

/-- The supplied transition kernel agrees pointwise with the canonical kernel. -/
theorem s6_supplied_gmp_transition_eq_canonical_verified
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1) :
    ∀ t : ℝ≥0, r.transitionKernel t = (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t := by
  exact s6_supplied_gmp_transition_eq_canonical_unconditional hd ω lam Λ hΛ hω h0 h1 r

/-- The canonical transition-kernel identification holds for every supplied realization. -/
theorem s6_supplied_gmp_transition_eq_canonical
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1) :
    ∀ t : ℝ≥0, r.transitionKernel t = (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t := by
  exact u5_supplied_gmp_transition_eq_of_ae_C0_action hd ω lam Λ hΛ hω h0 h1 r
    (s6_supplied_gmp_transition_C0_action_ae hd ω lam Λ hΛ hω h0 h1 r)

#print axioms s6_supplied_gmp_transition_eq_canonical_verified
#print axioms s6_supplied_gmp_transition_eq_canonical_unconditional
#print axioms s6_supplied_gmp_transition_eq_canonical

#print axioms s6_supplied_gmp_transition_C0_action_ae
#print axioms s6_physical_diffusion_defect_bound
#print axioms s6_physical_matrix_pairing_bound
#print axioms s6_physical_coefficient_pairing_bound

#print axioms s6_foundation_gmp_physical_origin_law_and_mp
#print axioms s6_gmp_origin_law_same_kernel_mp

/-- A symmetric semigroup has nonnegative quadratic forms at nonnegative times. -/
theorem s6_symmetric_semigroup_quadratic_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ℝ≥0 → E →L[ℝ] E)
    (hadd : ∀ s t, P (s + t) = (P s).comp (P t))
    (hsym : ∀ t u v, inner ℝ u (P t v) = inner ℝ (P t u) v)
    (t : ℝ≥0) (u : E) : 0 ≤ inner ℝ u (P t u) := by
  have htime : t / 2 + t / 2 = t := add_halves t
  have hcomp := hadd (t / 2) (t / 2)
  rw [htime] at hcomp
  rw [hcomp, ContinuousLinearMap.comp_apply, hsym]
  exact real_inner_self_nonneg

#print axioms s6_symmetric_semigroup_quadratic_nonneg

end EinsteinFull
