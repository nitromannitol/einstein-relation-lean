import EinsteinFull.Work.W4.HomogeneousGaussianTimeDerivativeBoundSupport
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0400_1
import EinsteinFull.Blueprint.G3.Proofs.W2Queue0420_1
import EinsteinFull.Blueprint.G3.Proofs.W4Queue0400_2
import EinsteinFull.Work.W4.ActualHomogeneousGaussianSemigroupProof
import EinsteinFull.Work.W3.GaussianDerivativeAveragingSupport
import EinsteinFull.Work.W4.HomogeneousAllDataHorizontalSmoothingSupport
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import EinsteinFull.Blueprint.G3.node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identification
import EinsteinFull.Blueprint.G3.node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacement
import EinsteinFull.Blueprint.Roots.node_l_u3A_finite_u2D_xi
import EinsteinFull.Blueprint.Roots.node_l_u3A_late_u2D_propagation
import EinsteinFull.Blueprint.G3.node_e_u3A_test_u2D_clt
import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport
import EinsteinFull.Calculus.ComplexZeroForceFluxSupport
import EinsteinFull.Work.W2.UnforcedCorrelationIntegrabilitySupport

/-!
Zero-force witness identification and complex Gaussian transfers for
`paper/main.tex:1187–1191`. These identities use the actual bilinear transpose,
flux and commutator witnesses. Half-time Gaussian splitting transfers the
finite-ξ derivative estimates to the literal complex-force flux expression.
The model time replacement now has its relative tau/T bound from the test
CLT and the actual positive-time Gaussian derivative. The final reduction
combines the four prescribed dependencies with the exact flux decomposition
and preserves the common witnesses and structural quantifier order.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Blueprint.UnforcedIdentification
open EinsteinRelation

/-- The bilinear transpose of the zero-force evolution is the same evolution. -/
theorem unforced_transpose {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0) :
    complexL2Transpose (reducedLaw Q) (P t) = P t := by
  apply Eq.symm
  apply complexL2Transpose_unique
  intro f g
  rw [← inner_complexL2Conjugation_eq_integral_mul,
    ← inner_complexL2Conjugation_eq_integral_mul,
    complexL2Conjugation_apply, complexL2Conjugation_apply, ← hP.unforced_star t f]
  exact hP.unforced_isSymmetric t (star f) g

/-- The zero-force evolution preserves the actual reduced-law mean. -/
theorem integral_unforced_orbit {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    (∫ ω, P t f ω ∂reducedLaw Q) = ∫ ω, f ω ∂reducedLaw Q := by
  have he := (hP.integral_orbit_graph f t).integral_eq_zero
  rw [integral_congr_ae (Lp.coeFn_sub (P t f) f)] at he
  change (∫ ω, P t f ω - f ω ∂reducedLaw Q) = 0 at he
  rw [integral_sub (integrable_complexLp Q _) (integrable_complexLp Q _)] at he
  exact sub_eq_zero.mp he

/-- The literal reduced drift has zero mean, by its constant-test weak identity. -/
theorem drift_integral_zero {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (j : Fin d) : (∫ ω, β j ω ∂reducedLaw Q) = 0 := by
  letI := reducedLaw_probability Q
  have he := hβ.integral_mul j (Lp.const 2 (reducedLaw Q) 1) (fun _ => 0)
    (hasComplexHorizontalGradient_const (reducedLaw Q) (reducedLaw_stationary Q) 1)
  have hl : (∫ ω, β j ω * Lp.const 2 (reducedLaw Q) (1 : ℂ) ω ∂reducedLaw Q) =
      ∫ ω, β j ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
    simp only [hω, Function.const_apply, mul_one]
  have hr : (∫ ω, ∑ k, (ω.1 0 k j : ℂ) *
      (0 : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
    simp only [hω, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  rw [hl, hr, mul_zero] at he
  exact he

/-- Centering leaves the zero-force drift orbit unchanged. -/
theorem velocityEndpoint_zero {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {hQ : HasSmoothBounds D Q}
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (j : Fin d) :
    velocityEndpoint Q ⟨0, by omega⟩ j 0 P β a t = P t (β j) := by
  simp only [velocityEndpoint, zero_smul, add_zero]
  unfold centeredComplexLp
  rw [integral_unforced_orbit hP, drift_integral_zero hβ, map_zero, sub_zero]

/-- At zero force the transpose endpoint equals the first velocity endpoint. -/
theorem transposeEndpoint_zero {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {hQ : HasSmoothBounds D Q}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    transposeEndpoint Q ⟨0, by omega⟩ Pdag β t =
      velocityEndpoint Q ⟨0, by omega⟩ ⟨0, by omega⟩ 0 P β a t := by
  rw [transposeEndpoint, velocityEndpoint, hPdag.eq_complexL2Transpose]
  dsimp only
  rw [unforced_transpose hP]
  simp only [zero_smul, add_zero]
  unfold centeredComplexLp
  rw [integral_unforced_orbit hP, drift_integral_zero hβ, map_zero, sub_zero]

/-- Every literal zero-force flux witness has the source identity Q_* = Q_1.
No choice of gradient representative or new flux is made. -/
theorem finiteTimeFlux_transpose_zero {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {hQ : HasSmoothBounds D Q}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q 0 P Pdag β a μ G F)
    (t : ℝ≥0) (j : Fin d) :
    F t (.inr ()) j = F t (.inl ⟨0, by omega⟩) j := by
  obtain ⟨hG, hU, hgrad, hflux⟩ := hF
  have hgeq (s : ℝ≥0) : G s (.inr ()) = G s (.inl ⟨0, by omega⟩) := by
    have ht := hgrad s (.inr ())
    change HasComplexHorizontalGradient _ _
      (transposeEndpoint Q ⟨0, by omega⟩ Pdag β s) _ at ht
    rw [transposeEndpoint_zero hd Q P Pdag hP hPdag β hβ a s] at ht
    exact ht.unique (hgrad s (.inl ⟨0, by omega⟩))
  have hint (k : Fin d) :
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), G s.toNNReal (.inr ()) k) =
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), G s.toNNReal (.inl ⟨0, by omega⟩) k := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun s => congrFun (hgeq s.toNNReal) k
  apply Lp.ext
  filter_upwards [hflux t (.inr ()) j, hflux t (.inl ⟨0, by omega⟩) j] with ω ht hv
  rw [ht, hv]
  simp only [finiteTimeFluxObservation, Sum.elim_inr, Sum.elim_inl, hint,
    mul_zero, zero_mul, sub_zero, id_eq]

/-- The flux witness's integrated gradient is the finite commutator witness's
actual corrector gradient, including the initial time interval. -/
theorem finiteTimeFlux_integratedGradient {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {hQ : HasSmoothBounds D Q}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q 0 P Pdag β a μ G F)
    (t : ℝ≥0) (i : Fin d) (H X : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hX : IsFiniteTimeCommutator Q P hP.2.2.1 β t i H X) (k : Fin d) :
    (∫ s in Set.Icc (0 : ℝ) (t : ℝ), G s.toNNReal (.inl i) k) = H k := by
  letI := reducedLaw_probability Q
  obtain ⟨hG, _hU, hgrad, _hflux⟩ := hF
  have hf := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 (β i)) (t : ℝ)
  have hg := integrableOn_comp_toNNReal_Icc _ (hG (.inl i) k) (t : ℝ)
  have hdG : ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)),
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) k
        (P s.toNNReal (β i)) (G s.toNNReal (.inl i) k) := by
    apply Filter.Eventually.of_forall
    intro s
    have h := hgrad s.toNNReal (.inl i) k
    change HasComplexHorizontalDerivative _ _ k
      (velocityEndpoint Q ⟨0, by omega⟩ i 0 P β a s.toNNReal) _ at h
    rwa [velocityEndpoint_zero hd Q P hP β hβ a s.toNNReal i] at h
  have hi := HasComplexHorizontalDerivative.integral_of_ae hf hg hdG
  exact hi.unique (hX.1 k)

private theorem sum_coe {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 (reducedLaw Q)) :
    (∑ k ∈ s, f k : Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
      fun ω => ∑ k ∈ s, f k ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using! Lp.coeFn_zero ℂ 2 (reducedLaw Q)
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    filter_upwards [Lp.coeFn_add (f k) (∑ b ∈ s, f b), ih] with ω ha hb
    simpa only [Pi.add_apply, hb] using! ha

/-- The actual flux and actual finite commutator witnesses obey the exact
centered decomposition in the source. No asymptotic estimate is assumed. -/
theorem centered_finiteTimeFlux_zero {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {hQ : HasSmoothBounds D Q}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a) (μ : Lp ℂ 2 (reducedLaw Q))
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q 0 P Pdag β a μ G F)
    (t : ℝ≥0) (i : Fin d) (H X : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hX : IsFiniteTimeCommutator Q P hP.2.2.1 β t i H X) (j : Fin d) :
    centeredComplexLp Q (F t (.inl i) j) = centeredComplexLp Q (X j) +
      ∑ k, (homogenizedCoefficient Q j k : ℂ) • H k := by
  letI := reducedLaw_probability Q
  have hint := finiteTimeFlux_integratedGradient hd Q P Pdag hP β hβ a μ G F hF t i H X hX
  obtain ⟨hG, hU, _hgrad, hflux⟩ := hF
  let B := ∑ k, (homogenizedCoefficient Q j k : ℂ) • H k
  let A := Lp.const 2 (reducedLaw Q) (homogenizedCoefficient Q j i : ℂ)
  have hraw : F t (.inl i) j = X j + A + B := by
    apply Lp.ext
    filter_upwards [hflux t (.inl i) j, hX.2 j,
      ae_all_iff.mpr (fun k => ha j k),
      Lp.coeFn_add (X j + A) B, Lp.coeFn_add (X j) A,
      Lp.coeFn_const 2 (reducedLaw Q) (homogenizedCoefficient Q j i : ℂ),
      sum_coe Q Finset.univ (fun k => (homogenizedCoefficient Q j k : ℂ) • H k),
      ae_all_iff.mpr (fun k => Lp.coeFn_smul (homogenizedCoefficient Q j k : ℂ)
        (H k))] with ω hf hx hak hab hxa hc hb hm
    rw [hab, Pi.add_apply, hxa, Pi.add_apply, hc, Function.const_apply, hb]
    rw [hf, hx]
    simp only [finiteTimeFluxObservation, Sum.elim_inl, id_eq, hint, sub_zero,
      hak, hm, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sub,
      sub_mul, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hu : (∑ k, (homogenizedCoefficient Q j k : ℂ) *
        ((unitVector i k : ℝ) : ℂ)) = (homogenizedCoefficient Q j i : ℂ) := by
      classical
      simp [unitVector, Pi.single_apply, apply_ite]
    have hv : (∑ k, (ω.1 0 j k : ℂ) *
        ((unitVector i k : ℝ) : ℂ)) = (ω.1 0 j i : ℂ) := by
      classical
      simp [unitVector, Pi.single_apply, apply_ite]
    rw [hu, hv]
    ring
  have hH (k : Fin d) : centeredComplexLp Q (H k) = H k := by
    unfold centeredComplexLp
    rw [(hX.1 k).integral_eq_zero, map_zero, sub_zero]
  have hA : centeredComplexLp Q A = 0 := by
    unfold centeredComplexLp A
    rw [integral_congr_ae (Lp.coeFn_const 2 (reducedLaw Q) _)]
    simp only [Function.const_apply, integral_const, probReal_univ, one_smul, sub_self]
  rw [← centeredComplexLpCLM_apply, hraw]
  simp only [map_add, map_sum, map_smul, centeredComplexLpCLM_apply,
    hH, hA, add_zero, B]

/-- Translating an integrable stationary kernel translates its actual average. -/
theorem stationary_kernel_shift {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (K : Vec d → ℂ) (a : Vec d)
    (F : Lp ℂ 2 (reducedLaw Q))
    (hK : Integrable (fun x => K x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F)) :
    (∫ x : Vec d, K (x - a) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F) =
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a
      (∫ x : Vec d, K x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F) := by
  calc
    _ = ∫ x : Vec d, K x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (x + a) F := by
      simpa only [add_sub_cancel_right] using!
        (integral_add_right_eq_self (fun x : Vec d => K (x - a) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F) a).symm
    _ = _ := by
      change _ = (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a
        ).toContinuousLinearMap _
      rw [← ContinuousLinearMap.integral_comp_comm _ hK]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [LinearIsometry.coe_toContinuousLinearMap, map_smul, complexTranslation_add,
          add_comm x a]

/-- A real-force homogeneous average is the actual translation of its unforced average. -/
theorem homogeneousAverage_real_force {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) (z : ℝ)
    (F : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousAverage Q ⟨0, by omega⟩ s hs (z : ℂ) F =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
        ((z * s) • (homogenizedCoefficient Q).mulVec (unitVector ⟨0, by omega⟩))
        (gaussianAverage hd Q s hs F) := by
  unfold homogeneousAverage gaussianAverage
  simp_rw [homogenizedGaussianKernel_realForce_eq_translate]
  exact stationary_kernel_shift Q _ _ F
    (integrable_homogeneousAverage_integrand Q ⟨0, by omega⟩ s hs 0 F)

open Filter Set
open scoped Topology BigOperators

variable {d : ℕ} {Λ r : ℝ}
attribute [local instance] reducedLaw_probability

/-- The literal spatial kernel is entire in its force parameter. -/
theorem differentiable_force_kernel (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (x : Vec d) :
    Differentiable ℂ (fun z => homogenizedGaussianKernel Q i s hs z x) := by
  unfold homogenizedGaussianKernel
  fun_prop

/-- A common integrable bound on force discs for the unit kernel and its force derivative. -/
theorem exists_integrable_unit_kernel_force_majorant
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (R : ℝ) :
    ∃ b : Vec d → ℝ, Integrable b ∧
      (∀ x z, ‖z‖ ≤ R →
        ‖homogenizedGaussianKernel Q i 1 zero_lt_one z x‖ ≤ b x) ∧
      (∀ x z, ‖z‖ ≤ R →
        ‖deriv (fun w => homogenizedGaussianKernel Q i 1 zero_lt_one w x) z‖ ≤ b x) := by
  let n := (volume : Measure (Vec d)).integrablePower
  let M (m : ℕ) := gaussianSchwartzBound d Λ m *
    Real.exp (gaussianSchwartzBound d Λ m * (1 + (R + 1)) ^ 2)
  let b (x : Vec d) := (2 : ℝ) ^ n * (M 0 + M n) * (1 + ‖x‖) ^ (-(n : ℝ))
  have hb (x : Vec d) (z : ℂ) (hz : ‖z‖ ≤ R + 1) :
      ‖homogenizedGaussianKernel Q i 1 zero_lt_one z x‖ ≤ b x := by
    have hw (m : ℕ) := (homogenizedGaussianKernel_weighted_coordinate_bounds
      Q i 1 zero_lt_one (by norm_num) le_rfl z x m).1
    have hM (m : ℕ) : (1 + euclideanNorm x) ^ m *
        ‖homogenizedGaussianKernel Q i 1 zero_lt_one z x‖ ≤ M m := by
      apply (hw m).trans
      apply mul_le_mul_of_nonneg_left _ (gaussianSchwartzBound_pos d Λ Q.ellipticity_parameter m).le
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ (gaussianSchwartzBound_pos d Λ Q.ellipticity_parameter m).le
      exact pow_le_pow_left₀ (by positivity) (add_le_add_right hz 1) 2
    have h0 := hM 0
    simp only [pow_zero, one_mul] at h0
    have hn : ‖x‖ ^ (0 + n) *
        ‖homogenizedGaussianKernel Q i 1 zero_lt_one z x‖ ≤ M n := by
      simp only [zero_add]
      apply (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg x)
          ((norm_vec_le_euclideanNorm x).trans (le_add_of_nonneg_left zero_le_one)) n)
        (norm_nonneg _)).trans
      exact hM n
    simpa only [pow_zero, one_mul] using!
      pow_mul_le_of_le_of_pow_mul_le (norm_nonneg x) (norm_nonneg _) h0 hn
  refine ⟨b, (Measure.integrable_pow_neg_integrablePower (volume : Measure (Vec d))).const_mul _,
    (fun x z hz => hb x z (hz.trans (by linarith))), ?_⟩
  intro x z hz
  have H := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1
    (by norm_num : (0 : ℝ) < 1)
    (differentiable_force_kernel Q i 1 zero_lt_one x).differentiableOn.diffContOnCl
    (fun w hw => hb x w (by
      have ht := norm_add_le (w - z) z
      have he : ‖w - z‖ = 1 := by simpa only [Metric.mem_sphere, dist_eq_norm] using! hw
      rw [sub_add_cancel, he] at ht
      linarith))
  simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, one_pow, div_one] using! H

/-- The unit-kernel integral along any scaled stationary translation orbit is entire. -/
theorem differentiable_unit_kernel_integral
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (c : ℝ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Differentiable ℂ (fun z => ∫ x : Vec d,
      homogenizedGaussianKernel Q i 1 zero_lt_one z x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (c • x) f) := by
  let K (z : ℂ) (x : Vec d) :=
    homogenizedGaussianKernel Q i 1 zero_lt_one z x
  let U (x : Vec d) := complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (c • x) f
  have hU : Continuous U := (continuous_complexTranslation _ _).comp
    ((continuous_id.const_smul c).prodMk continuous_const)
  have hK : Continuous (fun p : Vec d × ℂ => K p.2 p.1) := by unfold K homogenizedGaussianKernel; fun_prop
  have hD (z : ℂ) : AEStronglyMeasurable (fun x => deriv (fun w => K w x) z) :=
    ((stronglyMeasurable_deriv_with_param (f := fun x w => K w x) hK).comp_measurable
      (measurable_id.prodMk (measurable_const (a := z)))).aestronglyMeasurable
  intro z
  obtain ⟨b, hb, h0, h1⟩ := exists_integrable_unit_kernel_force_majorant Q i (‖z‖ + 1)
  have hbound (w : ℂ) (hw : w ∈ Metric.ball z 1) : ‖w‖ ≤ ‖z‖ + 1 := by
    have ht := norm_add_le (w - z) z
    have he : ‖w - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using! hw
    rw [sub_add_cancel] at ht
    linarith
  have hmeas (w : ℂ) : AEStronglyMeasurable (fun x => K w x • U x) :=
    (((hK.comp (continuous_id.prodMk continuous_const)).fun_smul hU).aestronglyMeasurable)
  have hint : Integrable (fun x => K z x • U x) := by
    apply (hb.mul_const ‖f‖).mono' (hmeas z)
    filter_upwards with x
    rw [norm_smul, norm_complexTranslation]
    exact mul_le_mul_of_nonneg_right (h0 x z (by linarith [norm_nonneg z])) (norm_nonneg f)
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z zero_lt_one)
    (Eventually.of_forall hmeas) hint ((hD z).smul hU.aestronglyMeasurable)
    (Eventually.of_forall fun x w hw => by
      rw [norm_smul, norm_complexTranslation]
      exact mul_le_mul_of_nonneg_right (h1 x w (hbound w hw)) (norm_nonneg f))
    (hb.mul_const ‖f‖)
    (Eventually.of_forall fun x w _ =>
      ((differentiable_force_kernel Q i 1 zero_lt_one x w).hasDerivAt.smul_const (U x)))
  exact H.2.differentiableAt

/-- Parabolic scaling of the actual stationary average, including its translation orbit. -/
theorem homogeneousAverage_eq_scaled
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousAverage Q i s hs ζ f = ∫ x : Vec d,
      homogenizedGaussianKernel Q i 1 zero_lt_one (ζ * (Real.sqrt s : ℂ)) x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (Real.sqrt s • x) f := by
  let c := Real.sqrt s
  have hc : 0 < c := Real.sqrt_pos.mpr hs
  have hcs : c ^ 2 = s := Real.sq_sqrt hs.le
  have hd (x : Vec d) := homogenizedGaussianKernel_scale Q i c 1 hc zero_lt_one ζ x
  simp only [mul_one, hcs] at hd
  have he := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun x => homogenizedGaussianKernel Q i s hs ζ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) c
  simp only [Module.finrank_pi, Fintype.card_fin,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hc.le _))] at he
  simp_rw [hd, mul_smul, Complex.coe_smul] at he
  erw [integral_smul] at he
  exact (smul_right_injective _ (inv_ne_zero (pow_ne_zero d hc.ne')) he).symm

/-- The actual positive-time stationary Gaussian average is entire in force. -/
theorem differentiable_force_homogeneousAverage
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Differentiable ℂ (fun z => homogeneousAverage Q i s hs z f) := by
  simp_rw [homogeneousAverage_eq_scaled]
  exact (differentiable_unit_kernel_integral Q i (Real.sqrt s) f).comp
    (differentiable_id.mul_const (Real.sqrt s : ℂ))
/-- A half-time unforced inner Gaussian retains the full complex propagation drift. -/
theorem homogeneousAverage_half_split {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousAverage Q ⟨0, by omega⟩ s hs ζ f =
      homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
        (gaussianAverage hd Q (s / 2) (half_pos hs) f) := by
  let F (z : ℂ) := homogeneousAverage Q ⟨0, by omega⟩ s hs z f
  let G (z : ℂ) := homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * z)
    (gaussianAverage hd Q (s / 2) (half_pos hs) f)
  have hf : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
    (differentiable_force_homogeneousAverage Q ⟨0, by omega⟩ s hs f).analyticAt z
  have hg : AnalyticOnNhd ℂ G Set.univ := fun z _ =>
    ((differentiable_force_homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs)
      (gaussianAverage hd Q (s / 2) (half_pos hs) f)).comp
        (differentiable_id.const_mul 2)).analyticAt z
  have hr (z : ℝ) : F (z : ℂ) = G (z : ℂ) := by
    dsimp only [F, G]
    rw [show (2 : ℂ) * (z : ℂ) = ((2 * z : ℝ) : ℂ) by push_cast; rfl]
    rw [homogeneousAverage_real_force hd, homogeneousAverage_real_force hd]
    have hsum := homogeneousAverage_add Q ⟨0, by omega⟩ (s / 2) (s / 2)
      (half_pos hs) (half_pos hs) 0 f
    change gaussianAverage hd Q (s / 2) (half_pos hs)
      (gaussianAverage hd Q (s / 2) (half_pos hs) f) =
      homogeneousAverage Q ⟨0, by omega⟩ (s / 2 + s / 2) _ 0 f at hsum
    have he : s / 2 + s / 2 = s := by ring
    simp only [he] at hsum
    change gaussianAverage hd Q (s / 2) (half_pos hs)
      (gaussianAverage hd Q (s / 2) (half_pos hs) f) = gaussianAverage hd Q s hs f at hsum
    rw [hsum, show 2 * z * (s / 2) = z * s by ring]
  have hc : (0 : ℂ) ∈ closure ({z | F z = G z} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((ε / 2 : ℝ) : ℂ), ⟨hr _, ?_⟩, ?_⟩
    · change ((ε / 2 : ℝ) : ℂ) ≠ 0
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (half_pos hε))
    · simp only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
  exact hf.eqOn_of_preconnected_of_mem_closure hg isPreconnected_univ (mem_univ 0) hc
    (mem_univ ζ)
/-- Stationary Schwartz averaging commutes with actual spatial translations. -/
theorem stationarySchwartzAverage_translation (Q : EnvironmentLaw d Λ r)
    (ψ : SchwartzMap (Vec d) ℂ) (a : Vec d) (f : Lp ℂ 2 (reducedLaw Q)) :
    stationarySchwartzAverage Q ψ (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a f) =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a (stationarySchwartzAverage Q ψ f) := by
  unfold stationarySchwartzAverage
  change _ = (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a).toContinuousLinearMap
    (∫ x : Vec d, ψ (-x) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)
  rw [← (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a).toContinuousLinearMap.integral_comp_comm
    (integrable_stationarySchwartzAverage_integrand Q ψ f)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [map_smul]
    change ψ (-x) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a f) =
      ψ (-x) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)
    rw [← complexTranslation_add, ← complexTranslation_add, add_comm x a]

/-- A Schwartz average preserves any existing strong horizontal derivative. -/
theorem horizontalDerivative_stationarySchwartzAverage
    (Q : EnvironmentLaw d Λ r) (j : Fin d) (ψ : SchwartzMap (Vec d) ℂ)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hf : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (stationarySchwartzAverage Q ψ f) (stationarySchwartzAverage Q ψ g) := by
  let A := stationarySchwartzAverageCLM Q ψ
  have h := (A.continuous.tendsto g).comp hf
  change Tendsto (fun t : ℝ => A ((t : ℂ)⁻¹ •
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector j) f - f)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (A g)) at h
  unfold HasComplexHorizontalDerivative
  simpa only [map_smul, map_sub, A, stationarySchwartzAverageCLM_apply,
    stationarySchwartzAverage_translation] using! h

/-- Spatial integration by parts identifies the derivative kernel on an existing horizontal jet. -/
theorem stationarySchwartzAverage_horizontalDerivative
    (Q : EnvironmentLaw d Λ r) (j : Fin d) (ψ : SchwartzMap (Vec d) ℂ)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hf : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g) :
    stationarySchwartzAverage Q ψ g =
      stationarySchwartzAverage Q ((SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp
        (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) ψ) f := by
  let D := (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) ψ
  have hg (x : Vec d) : HasLineDerivAt ℝ
      (fun y => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y f)
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) x (unitVector j) := by
    have hd := (((complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt 0
      (hf.hasDerivAt_orbit 0)
    simp only [zero_smul, complexTranslation_zero] at hd
    change HasDerivAt (fun t : ℝ => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector j) f))
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) 0 at hd
    simpa only [HasLineDerivAt, ← complexTranslation_add] using! hd
  have hk (x : Vec d) : HasLineDerivAt ℝ (fun y => ψ (-y)) (-D (-x)) x (unitVector j) := by
    convert! ((ψ.hasFDerivAt (-x)).comp x ((hasFDerivAt_id x).neg)).hasLineDerivAt (unitVector j) using 1 <;>
      (try simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, map_neg]) <;> rfl
  have hi := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.lsmul ℝ ℂ)
    (by simpa only [ContinuousLinearMap.lsmul_apply, neg_smul, Pi.neg_apply] using! (integrable_stationarySchwartzAverage_integrand Q D f).neg)
    (integrable_stationarySchwartzAverage_integrand Q ψ g)
    (integrable_stationarySchwartzAverage_integrand Q ψ f) (fun x _ => hk x) (fun x _ => hg x)
  simpa only [ContinuousLinearMap.lsmul_apply, neg_smul, integral_neg, neg_neg, stationarySchwartzAverage, D] using! hi

/-- Every stationary Schwartz average has the literal differentiated-kernel horizontal derivative. -/
theorem stationarySchwartzAverage_hasHorizontalDerivative
    (Q : EnvironmentLaw d Λ r) (j : Fin d) (ψ : SchwartzMap (Vec d) ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (stationarySchwartzAverage Q ψ f)
      (stationarySchwartzAverage Q ((SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp
        (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) ψ) f) := by
  let D := (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) ψ
  let S := {u : Lp ℂ 2 (reducedLaw Q) |
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (stationarySchwartzAverage Q ψ u) (stationarySchwartzAverage Q D u)}
  have hclosed : IsClosed S :=
    (isClosed_complexHorizontalDerivative_graph (reducedLaw Q) (reducedLaw_stationary Q) j).preimage
      ((stationarySchwartzAverageCLM Q ψ).continuous.prodMk (stationarySchwartzAverageCLM Q D).continuous)
  have hsub : {u | IsComplexHorizontallySmooth Q u} ⊆ S := by
    intro u hu
    obtain ⟨J, hJ0, hJ⟩ := hu
    have hjet : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j u (J [j]) := by
      simpa only [hJ0] using! hJ [] j
    have he := stationarySchwartzAverage_horizontalDerivative Q j ψ hjet
    change HasComplexHorizontalDerivative _ _ _ _ _
    rw [← he]
    exact horizontalDerivative_stationarySchwartzAverage Q j ψ hjet
  exact hclosed.closure_subset (closure_mono hsub (dense_complexHorizontallySmooth Q f))

/-- The actual complex-force kernel at arbitrary positive time as a Schwartz test. -/
noncomputable def positiveTimeGaussianSchwartz (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) : SchwartzMap (Vec d) ℂ :=
  let c := Real.sqrt s
  let L := (LinearEquiv.smulOfNeZero (M := Vec d) ℝ c⁻¹
    (inv_ne_zero (Real.sqrt_pos.mpr hs).ne')).toContinuousLinearEquiv
  (((c ^ d)⁻¹ : ℝ) : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L
    (homogenizedGaussianSchwartz Q i 1 zero_lt_one (by norm_num) le_rfl (ζ * (c : ℂ)))

/-- The Schwartz representation evaluates to the literal anisotropic complex-force kernel. -/
theorem positiveTimeGaussianSchwartz_apply (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) (x : Vec d) :
    positiveTimeGaussianSchwartz Q i s hs ζ x = homogenizedGaussianKernel Q i s hs ζ x := by
  let c := Real.sqrt s
  have hc : 0 < c := Real.sqrt_pos.mpr hs
  have hcs : c ^ 2 = s := Real.sq_sqrt hs.le
  change (((c ^ d)⁻¹ : ℝ) : ℂ) *
    homogenizedGaussianSchwartz Q i 1 zero_lt_one (by norm_num) le_rfl (ζ * (c : ℂ)) (c⁻¹ • x) = _
  have he := homogenizedGaussianKernel_scale Q i c 1 hc zero_lt_one ζ (c⁻¹ • x)
  simpa only [mul_one, hcs, smul_smul, mul_inv_cancel₀ hc.ne', one_smul,
    homogenizedGaussianSchwartz_apply] using! he.symm

/-- The backwards Schwartz kernel represents the actual forward stationary average. -/
theorem stationarySchwartzAverage_positiveTimeGaussian (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    stationarySchwartzAverage Q (positiveTimeGaussianSchwartz Q i s hs (-ζ)) f =
      homogeneousAverage Q i s hs ζ f := by
  unfold stationarySchwartzAverage homogeneousAverage
  simp_rw [positiveTimeGaussianSchwartz_apply, homogenizedGaussianKernel_neg_force, neg_neg]

/-- Every two-direction homogeneous derivative average is the actual second horizontal derivative. -/
theorem homogeneousAverage_hasHorizontalJet_two
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (dirs : Fin 2 → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) (dirs 1)
        (homogeneousAverage Q i s hs ζ f) g ∧
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) (dirs 0) g
        (homogeneousDerivativeAverage Q i s hs ζ 2 dirs f) := by
  let K := positiveTimeGaussianSchwartz Q i s hs (-ζ)
  let D := (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector (dirs 1))).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) K
  refine ⟨stationarySchwartzAverage Q D f, ?_, ?_⟩
  · have h := stationarySchwartzAverage_hasHorizontalDerivative Q (dirs 1) K f
    rwa [stationarySchwartzAverage_positiveTimeGaussian] at h
  · have h := stationarySchwartzAverage_hasHorizontalDerivative Q (dirs 0) D f
    convert! h using 1
    unfold homogeneousDerivativeAverage stationarySchwartzAverage
    apply integral_congr_ae
    refine Eventually.of_forall fun x => ?_
    dsimp only
    congr 1
    have he : (K : Vec d → ℂ) = homogenizedGaussianKernel Q i s hs (-ζ) :=
      funext (positiveTimeGaussianSchwartz_apply Q i s hs (-ζ))
    rw [← he, ← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv (f := K)]
    simp only [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_zero]
    rfl

/-- Complex-force Hessians retain a half-time unforced differentiated average. -/
theorem homogeneousDerivativeAverage_two_half_split {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (dirs : Fin 2 → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ζ 2 dirs f =
      homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
        (gaussianDerivativeAverage hd Q (s / 2) (half_pos hs) 2 dirs f) := by
  obtain ⟨g, hg, hg'⟩ := homogeneousAverage_hasHorizontalJet_two Q ⟨0, by omega⟩ s hs ζ dirs f
  obtain ⟨h, hh, hh'⟩ := homogeneousAverage_hasHorizontalJet_two Q ⟨0, by omega⟩
    (s / 2) (half_pos hs) 0 dirs f
  have hfirst := hh.homogeneousAverage ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
  have he : g = homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ) h := by
    apply hg.unique
    change HasComplexHorizontalDerivative _ _ _
      (homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
        (gaussianAverage hd Q (s / 2) (half_pos hs) f)) _ at hfirst
    rwa [← homogeneousAverage_half_split hd Q s hs ζ f] at hfirst
  rw [he] at hg'
  have hsecond := hh'.homogeneousAverage ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
  have hfinal := hg'.unique hsecond
  simpa only [homogeneousDerivativeAverage, neg_zero, gaussianDerivativeAverage] using! hfinal

/-- A first differentiated average is the actual strong horizontal derivative. -/
theorem homogeneousAverage_hasHorizontalDerivative_one
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (dirs : Fin 1 → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) (dirs 0)
      (homogeneousAverage Q i s hs ζ f)
      (homogeneousDerivativeAverage Q i s hs ζ 1 dirs f) := by
  let K := positiveTimeGaussianSchwartz Q i s hs (-ζ)
  have h := stationarySchwartzAverage_hasHorizontalDerivative Q (dirs 0) K f
  rw [stationarySchwartzAverage_positiveTimeGaussian] at h
  convert! h using 1
  unfold homogeneousDerivativeAverage stationarySchwartzAverage
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  dsimp only
  congr 1
  have he : (K : Vec d → ℂ) = homogenizedGaussianKernel Q i s hs (-ζ) :=
    funext (positiveTimeGaussianSchwartz_apply Q i s hs (-ζ))
  rw [← he, iteratedFDeriv_one_apply]
  rfl

/-- Complex-force first derivatives retain a half-time unforced derivative average. -/
theorem homogeneousDerivativeAverage_one_half_split (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (dirs : Fin 1 → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ζ 1 dirs f =
      homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
        (gaussianDerivativeAverage hd Q (s / 2) (half_pos hs) 1 dirs f) := by
  have h := homogeneousAverage_hasHorizontalDerivative_one Q ⟨0, by omega⟩ s hs ζ dirs f
  have hinner := homogeneousAverage_hasHorizontalDerivative_one Q ⟨0, by omega⟩
    (s / 2) (half_pos hs) 0 dirs f
  have houter := hinner.homogeneousAverage ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
  change HasComplexHorizontalDerivative _ _ _
    (homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
      (gaussianAverage hd Q (s / 2) (half_pos hs) f)) _ at houter
  rw [← homogeneousAverage_half_split hd Q s hs ζ f] at houter
  simpa only [homogeneousDerivativeAverage, neg_zero, gaussianDerivativeAverage] using! h.unique houter

/-- Zeroth derivative averaging is the literal homogeneous average. -/
theorem homogeneousDerivativeAverage_zero
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (dirs : Fin 0 → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousDerivativeAverage Q i s hs ζ 0 dirs f = homogeneousAverage Q i s hs ζ f := by
  unfold homogeneousDerivativeAverage homogeneousAverage
  simp only [iteratedFDeriv_zero_apply, homogenizedGaussianKernel_neg_force, neg_neg]

/-- The orders used by the flux reduction split with the same actual inner data. -/
theorem homogeneousDerivativeAverage_half_split (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (k : ℕ) (hk : k ≤ 2) (dirs : Fin k → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ζ k dirs f =
      homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
        (gaussianDerivativeAverage hd Q (s / 2) (half_pos hs) k dirs f) := by
  interval_cases k
  · have he : gaussianDerivativeAverage hd Q (s / 2) (half_pos hs) 0 dirs f =
        gaussianAverage hd Q (s / 2) (half_pos hs) f := by
      unfold gaussianDerivativeAverage gaussianAverage
      simp only [iteratedFDeriv_zero_apply]
      apply integral_congr_ae
      refine Eventually.of_forall fun x => ?_
      have hx := homogenizedGaussianKernel_neg_force Q ⟨0, by omega⟩
        (s / 2) (half_pos hs) 0 (-x)
      simp only [neg_zero, neg_neg] at hx
      dsimp only
      rw [hx]
    rw [he, homogeneousDerivativeAverage_zero, homogeneousAverage_half_split hd]
  · exact homogeneousDerivativeAverage_one_half_split hd Q s hs ζ dirs f
  · exact homogeneousDerivativeAverage_two_half_split hd Q s hs ζ dirs f

/-- Reserving half the time preserves the unforced spatial decay at orders zero through two. -/
theorem norm_homogeneousDerivativeAverage_le_half (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (k : ℕ) (hk : k ≤ 2) (dirs : Fin k → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ζ k dirs f‖ ≤
      Real.exp (sourceReducedBound Λ * ‖ζ‖ ^ 2 * s) *
        ‖gaussianDerivativeAverage hd Q (s / 2) (half_pos hs) k dirs f‖ := by
  rw [homogeneousDerivativeAverage_half_split hd Q s hs ζ k hk dirs f]
  have he : sourceReducedBound Λ * ‖2 * ζ‖ ^ 2 * (s / 2) / 2 =
      sourceReducedBound Λ * ‖ζ‖ ^ 2 * s := by
    rw [norm_mul]
    norm_num
    ring
  exact ((homogeneousAverageCLM Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)).le_opNorm
    _).trans (mul_le_mul_of_nonneg_right
      (by simpa only [he] using! (norm_homogeneousAverageCLM_le Q ⟨0, by omega⟩
        (s / 2) (half_pos hs) (2 * ζ))) (norm_nonneg _))

private theorem le_sqrt_sum_sq {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (j : ι) : a j ≤ Real.sqrt (∑ l, (a l) ^ 2) :=
  Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun l _ => sq_nonneg (a l)) (Finset.mem_univ j))

/-- The supplied finite-ξ witnesses satisfy the complex-force derivative bounds
needed for the unforced flux replacement. Constants and witnesses keep their
original order; the half-time reservation accounts for the range `4τ ≤ s`. -/
theorem finiteTimeCommutator_complex_derivative_bounds
    (hxi : node_l_u3A_finite_u2D_xiStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ gain t₀ : ℝ, ∃ Cder : ℕ → ℝ,
      0 < gain ∧ 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsJointObservation Q Z →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∃ H X : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ (τ : ℝ≥0) (i : Fin d), IsFiniteTimeCommutator Q P hP.2.2.1 β τ i (H τ i) (X τ i)) ∧
      ∀ τ : ℝ≥0, t₀ ≤ (τ : ℝ) → ∀ s : ℝ, 4 * (τ : ℝ) ≤ s → ∀ hs : 0 < s,
      ∀ ζ : ℂ, ∀ k : ℕ, k ≤ 2 → ∀ dirs : Fin k → Fin d,
      (∀ i j : Fin d,
        ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ζ k dirs
          (centeredComplexLp Q (X τ i j) - Z (.inl (j,i)))‖ ≤
          Real.exp (sourceReducedBound D.ellipticity * ‖ζ‖ ^ 2 * s) *
            (Cder k * (τ : ℝ) ^ (-gain) * (s / 2) ^ (-(d : ℝ) / 4 - (k : ℝ) / 2))) ∧
      (1 ≤ k → ∀ i : Fin d,
        ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ζ k dirs
          (finiteTimeCorrector Q P hP.2.2.1 β τ i)‖ ≤
          Real.exp (sourceReducedBound D.ellipticity * ‖ζ‖ ^ 2 * s) *
            (Cder k * (τ : ℝ) * (s / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - (k : ℝ) / 2))) := by
  obtain ⟨gain, t₀, Cder, hgain, ht₀, hCder, hbounds⟩ := hxi d hd D
  refine ⟨gain, t₀, Cder, hgain, ht₀, hCder, ?_⟩
  intro Q hQ β Z hβ hZ P hP
  obtain ⟨H, X, hwitness, hest⟩ := hbounds Q hQ β Z hβ hZ P hP
  refine ⟨H, X, hwitness, ?_⟩
  intro τ hτ s hsτ hs ζ k hk dirs
  obtain ⟨hX, hφ⟩ := hest τ hτ (s / 2) (by linarith) (half_pos hs)
  constructor
  · intro i j
    have hj : ‖gaussianDerivativeAverage hd Q (s / 2) (half_pos hs) k dirs
          (centeredComplexLp Q (X τ i j) - Z (.inl (j,i)))‖ ≤
        Cder k * (τ : ℝ) ^ (-gain) * (s / 2) ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) := by
      exact (le_sqrt_sum_sq (fun l : Fin d =>
        ‖gaussianDerivativeAverage hd Q (s / 2) (half_pos hs) k dirs
          (centeredComplexLp Q (X τ i l) - Z (.inl (l,i)))‖) j).trans (hX i k dirs)
    exact (norm_homogeneousDerivativeAverage_le_half hd Q s hs ζ k hk dirs _).trans
      (mul_le_mul_of_nonneg_left hj (Real.exp_pos _).le)
  · intro hkone i
    exact (norm_homogeneousDerivativeAverage_le_half hd Q s hs ζ k hk dirs _).trans
      (mul_le_mul_of_nonneg_left (hφ i k hkone dirs) (Real.exp_pos _).le)

/-- An arbitrary coordinate derivative of the actual positive-time complex kernel. -/
noncomputable def positiveTimeGaussianDerivativeSchwartz (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) (k : ℕ) (dirs : Fin k → Fin d) :
    SchwartzMap (Vec d) ℂ :=
  LineDeriv.iteratedLineDerivOp (fun j => unitVector (dirs j))
    (positiveTimeGaussianSchwartz Q i s hs ζ)

/-- The Schwartz derivative represents precisely the literal differentiated kernel. -/
theorem positiveTimeGaussianDerivativeSchwartz_apply (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) (k : ℕ) (dirs : Fin k → Fin d) (x : Vec d) :
    positiveTimeGaussianDerivativeSchwartz Q i s hs ζ k dirs x =
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs ζ) x
        (fun j => unitVector (dirs j)) := by
  rw [positiveTimeGaussianDerivativeSchwartz, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  rw [show (positiveTimeGaussianSchwartz Q i s hs ζ : Vec d → ℂ) =
    homogenizedGaussianKernel Q i s hs ζ from funext (positiveTimeGaussianSchwartz_apply Q i s hs ζ)]

/-- Literal homogeneous derivative averaging is stationary Schwartz averaging. -/
theorem homogeneousDerivativeAverage_eq_stationarySchwartzAverage (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) (k : ℕ) (dirs : Fin k → Fin d)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousDerivativeAverage Q i s hs ζ k dirs f =
      stationarySchwartzAverage Q (positiveTimeGaussianDerivativeSchwartz Q i s hs (-ζ) k dirs) f := by
  unfold homogeneousDerivativeAverage stationarySchwartzAverage
  simp_rw [positiveTimeGaussianDerivativeSchwartz_apply]

/-- Spatial integration by parts moves any existing horizontal derivative onto
an arbitrary order of the literal backwards Gaussian kernel. -/
theorem homogeneousDerivativeAverage_horizontalDerivative (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) (k : ℕ) (dirs : Fin k → Fin d)
    (j : Fin d) {f g : Lp ℂ 2 (reducedLaw Q)}
    (hf : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g) :
    homogeneousDerivativeAverage Q i s hs ζ k dirs g =
      homogeneousDerivativeAverage Q i s hs ζ (k + 1) (Fin.cons j dirs) f := by
  simp only [homogeneousDerivativeAverage_eq_stationarySchwartzAverage]
  rw [stationarySchwartzAverage_horizontalDerivative Q j _ hf]
  congr 1

/-- The literal differentiated stationary Gaussian average is a bounded linear map. -/
noncomputable def homogeneousDerivativeAverageCLM (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) (k : ℕ) (dirs : Fin k → Fin d) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  stationarySchwartzAverageCLM Q (positiveTimeGaussianDerivativeSchwartz Q i s hs (-ζ) k dirs)

/-- Evaluation of the bounded linear map is exactly the frozen derivative average. -/
@[simp] theorem homogeneousDerivativeAverageCLM_apply (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) (k : ℕ) (dirs : Fin k → Fin d)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousDerivativeAverageCLM Q i s hs ζ k dirs f =
      homogeneousDerivativeAverage Q i s hs ζ k dirs f :=
  (homogeneousDerivativeAverage_eq_stationarySchwartzAverage Q i s hs ζ k dirs f).symm

/-- The gradient part of every actual finite-time commutator is differentiated
by putting one further coordinate derivative on the same Gaussian kernel. -/
theorem finiteTimeCommutator_gradient_derivative_average (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ r)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : ∀ f : Lp ℂ 2 (reducedLaw Q), Continuous (fun t : ℝ≥0 => P t f))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (τ : ℝ≥0) (i : Fin d)
    (H X : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hX : IsFiniteTimeCommutator Q P hP β τ i H X)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) (k : ℕ) (dirs : Fin k → Fin d) (j : Fin d) :
    homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ζ k dirs (H j) =
      homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ζ (k + 1) (Fin.cons j dirs)
        (finiteTimeCorrector Q P hP β τ i) :=
  homogeneousDerivativeAverage_horizontalDerivative Q ⟨0, by omega⟩ s hs ζ k dirs j (hX.1 j)

/-- Finite-ξ replacement in the literal velocity/transpose flux expression,
including its undifferentiated velocity force term. No extra decay premise is
used: the only graph input is the prescribed finite-ξ proposition. -/
theorem finiteTimeCommutator_flux_replacement
    (hxi : node_l_u3A_finite_u2D_xiStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ gain t₀ : ℝ, ∃ Cder : ℕ → ℝ,
      0 < gain ∧ 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsJointObservation Q Z →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∃ H X : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ (τ : ℝ≥0) (i : Fin d), IsFiniteTimeCommutator Q P hP.2.2.1 β τ i (H τ i) (X τ i)) ∧
      ∀ τ : ℝ≥0, t₀ ≤ (τ : ℝ) → ∀ s : ℝ, 4 * (τ : ℝ) ≤ s → ∀ hs : 0 < s,
      ∀ ζ : ℂ, ∀ ν : FluxIndex d,
      let i := ν.elim id (fun _ => ⟨0, by omega⟩)
      let F := fun j => centeredComplexLp Q (X τ i j) - Z (.inl (j,i))
      let signζ := ν.elim (fun _ => ζ) (fun _ => -ζ)
      ‖(1 / 2 : ℂ) • (∑ j : Fin d,
          homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs signζ 1 (fun _ => j) (F j)) +
        ν.elim (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩))
          (fun _ => 0)‖ ≤
        Real.exp (sourceReducedBound D.ellipticity * ‖ζ‖ ^ 2 * s) *
          ((d : ℝ) / 2 * Cder 1 * (τ : ℝ) ^ (-gain) * (s / 2) ^ (-(d : ℝ) / 4 - 1 / 2) +
            ‖ζ‖ * Cder 0 * (τ : ℝ) ^ (-gain) * (s / 2) ^ (-(d : ℝ) / 4)) := by
  obtain ⟨gain, t₀, Cder, hgain, ht₀, hCder, hbounds⟩ :=
    finiteTimeCommutator_complex_derivative_bounds hxi d hd D
  refine ⟨gain, t₀, Cder, hgain, ht₀, hCder, ?_⟩
  intro Q hQ β Z hβ hZ P hP
  obtain ⟨H, X, hwitness, hest⟩ := hbounds Q hQ β Z hβ hZ P hP
  refine ⟨H, X, hwitness, ?_⟩
  intro τ hτ s hsτ hs ζ ν
  let i : Fin d := ν.elim id (fun _ => ⟨0, by omega⟩)
  let F := fun j => centeredComplexLp Q (X τ i j) - Z (.inl (j,i))
  let signζ := ν.elim (fun _ => ζ) (fun _ => -ζ)
  let E := Real.exp (sourceReducedBound D.ellipticity * ‖ζ‖ ^ 2 * s)
  let B₀ := E * (Cder 0 * (τ : ℝ) ^ (-gain) * (s / 2) ^ (-(d : ℝ) / 4))
  let B₁ := E * (Cder 1 * (τ : ℝ) ^ (-gain) * (s / 2) ^ (-(d : ℝ) / 4 - 1 / 2))
  have hsign : ‖signζ‖ = ‖ζ‖ := by cases ν <;> simp [signζ]
  have hgrad (j : Fin d) :
      ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs signζ 1 (fun _ => j) (F j)‖ ≤ B₁ := by
    have h := (hest τ hτ s hsτ hs signζ 1 (by omega) (fun _ => j)).1 i j
    simpa only [Nat.cast_one, hsign] using! h
  have hmean : ‖homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩)‖ ≤ B₀ := by
    have h := (hest τ hτ s hsτ hs ζ 0 (by omega) (fun j => Fin.elim0 j)).1 i ⟨0, by omega⟩
    rw [homogeneousDerivativeAverage_zero] at h
    simpa only [Nat.cast_zero, zero_div, sub_zero] using! h
  have hsum : ‖∑ j : Fin d,
      homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs signζ 1 (fun _ => j) (F j)‖ ≤
      (d : ℝ) * B₁ := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : Fin d, B₁ := Finset.sum_le_sum (fun j _ => hgrad j)
      _ = _ := by simp
  have hforce : ‖ν.elim
      (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩))
      (fun _ => (0 : Lp ℂ 2 (reducedLaw Q)))‖ ≤ ‖ζ‖ * B₀ := by
    cases ν with
    | inl j => simpa only [Sum.elim_inl, norm_smul] using!
        mul_le_mul_of_nonneg_left hmean (norm_nonneg ζ)
    | inr u =>
      simp only [Sum.elim_inr, norm_zero]
      exact mul_nonneg (norm_nonneg ζ) ((norm_nonneg _).trans hmean)
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  change ‖(1 / 2 : ℂ) • (∑ j : Fin d,
      homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs signζ 1 (fun _ => j) (F j)) +
      ν.elim (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩))
        (fun _ => 0)‖ ≤ _
  calc
    _ ≤ ‖(1 / 2 : ℂ) • (∑ j : Fin d,
        homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs signζ 1 (fun _ => j) (F j))‖ +
        ‖ν.elim (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩))
          (fun _ => (0 : Lp ℂ 2 (reducedLaw Q)))‖ := norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) * ((d : ℝ) * B₁) + ‖ζ‖ * B₀ := by
      rw [norm_smul, hhalf]
      exact add_le_add (mul_le_mul_of_nonneg_left hsum (by norm_num)) hforce
    _ = _ := by dsimp [B₀, B₁, E]; ring

private theorem norm_homogenizedCoefficient_le (Q : EnvironmentLaw d Λ r) (j k : Fin d) :
    ‖(homogenizedCoefficient Q j k : ℂ)‖ ≤ sourceReducedBound Λ := by
  have hcoord (x : Vec d) : |x j| ≤ euclideanNorm x := by
    unfold euclideanNorm euclideanSq dot
    rw [← Real.sqrt_sq_eq_abs (x j)]
    apply Real.sqrt_le_sqrt
    simpa only [pow_two] using!
      (Finset.single_le_sum (fun l _ => mul_self_nonneg (x l)) (Finset.mem_univ j))
  have h := (hcoord ((homogenizedCoefficient Q).mulVec
    (unitVector k))).trans (homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q k)
  simpa [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
    Complex.norm_real, Real.norm_eq_abs] using! h

/-- The anisotropic corrector flux gains one derivative by integration by parts.
The two scalar bounds are ordinary bounds on the actual corrector averages;
no elliptic equation or coefficient isotropy is assumed. -/
theorem finiteTimeCommutator_gradient_flux_bound (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ r)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : ∀ f : Lp ℂ 2 (reducedLaw Q), Continuous (fun t : ℝ≥0 => P t f))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (τ : ℝ≥0) (i : Fin d)
    (H X : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hX : IsFiniteTimeCommutator Q P hP β τ i H X)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) (ν : FluxIndex d) (B₁ B₂ : ℝ)
    (hφ : ∀ w : ℂ, ‖w‖ = ‖ζ‖ →
      (∀ dirs : Fin 1 → Fin d,
        ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs w 1 dirs
          (finiteTimeCorrector Q P hP β τ i)‖ ≤ B₁) ∧
      (∀ dirs : Fin 2 → Fin d,
        ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs w 2 dirs
          (finiteTimeCorrector Q P hP β τ i)‖ ≤ B₂)) :
    let F := fun j => ∑ k : Fin d, (homogenizedCoefficient Q j k : ℂ) • H k
    let signζ := ν.elim (fun _ => ζ) (fun _ => -ζ)
    ‖(1 / 2 : ℂ) • (∑ j : Fin d,
        homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs signζ 1 (fun _ => j) (F j)) +
      ν.elim (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩))
        (fun _ => 0)‖ ≤
      (d : ℝ) ^ 2 / 2 * sourceReducedBound Λ * B₂ +
        ‖ζ‖ * (d : ℝ) * sourceReducedBound Λ * B₁ := by
  let F := fun j => ∑ k : Fin d, (homogenizedCoefficient Q j k : ℂ) • H k
  let signζ := ν.elim (fun _ => ζ) (fun _ => -ζ)
  have hsign : ‖signζ‖ = ‖ζ‖ := by cases ν <;> simp [signζ]
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans ((hφ ζ rfl).1 (fun _ => i))
  have hS : 0 ≤ sourceReducedBound Λ := by
    unfold sourceReducedBound
    exact mul_nonneg (Real.exp_pos _).le (by nlinarith [sq_nonneg Λ])
  have hcoord (w : ℂ) (k : ℕ) (dirs : Fin k → Fin d)
      (B : ℝ)
      (hbound : ∀ dirs : Fin (k + 1) → Fin d,
        ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs w (k + 1) dirs
          (finiteTimeCorrector Q P hP β τ i)‖ ≤ B) (j : Fin d) :
      ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs w k dirs (F j)‖ ≤
        (d : ℝ) * sourceReducedBound Λ * B := by
    rw [← homogeneousDerivativeAverageCLM_apply]
    simp only [F, map_sum, map_smul, homogeneousDerivativeAverageCLM_apply]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _l : Fin d, sourceReducedBound Λ * B := by
        apply Finset.sum_le_sum
        intro l _
        rw [norm_smul, finiteTimeCommutator_gradient_derivative_average hd Q P hP β τ i H X hX]
        exact mul_le_mul (norm_homogenizedCoefficient_le Q j l)
          (hbound _) (norm_nonneg _) hS
      _ = _ := by simp; ring
  have hsum : ‖∑ j : Fin d,
      homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs signζ 1 (fun _ => j) (F j)‖ ≤
      (d : ℝ) * ((d : ℝ) * sourceReducedBound Λ * B₂) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : Fin d, (d : ℝ) * sourceReducedBound Λ * B₂ :=
        Finset.sum_le_sum (fun j _ => hcoord signζ 1 (fun _ => j) B₂
          (hφ signζ hsign).2 j)
      _ = _ := by simp
  have hmean : ‖homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩)‖ ≤
      (d : ℝ) * sourceReducedBound Λ * B₁ := by
    rw [← homogeneousDerivativeAverage_zero Q ⟨0, by omega⟩ s hs ζ (fun j => Fin.elim0 j)]
    exact hcoord ζ 0 (fun j => Fin.elim0 j) B₁ (hφ ζ rfl).1 _
  have hforce : ‖ν.elim
      (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩))
      (fun _ => (0 : Lp ℂ 2 (reducedLaw Q)))‖ ≤
      ‖ζ‖ * ((d : ℝ) * sourceReducedBound Λ * B₁) := by
    cases ν with
    | inl j => simpa only [Sum.elim_inl, norm_smul] using!
        mul_le_mul_of_nonneg_left hmean (norm_nonneg ζ)
    | inr u => simp only [Sum.elim_inr, norm_zero]; positivity
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  change ‖(1 / 2 : ℂ) • (∑ j : Fin d,
      homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs signζ 1 (fun _ => j) (F j)) +
      ν.elim (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩))
        (fun _ => 0)‖ ≤ _
  calc
    _ ≤ ‖(1 / 2 : ℂ) • (∑ j : Fin d,
        homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs signζ 1 (fun _ => j) (F j))‖ +
        ‖ν.elim (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩))
          (fun _ => (0 : Lp ℂ 2 (reducedLaw Q)))‖ := norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) * ((d : ℝ) * ((d : ℝ) * sourceReducedBound Λ * B₂)) +
        ‖ζ‖ * ((d : ℝ) * sourceReducedBound Λ * B₁) := by
      rw [norm_smul, hhalf]
      exact add_le_add (mul_le_mul_of_nonneg_left hsum (by norm_num)) hforce
    _ = _ := by ring

/-- The prescribed finite-ξ graph input bounds the full anisotropic corrector
correction, for the same actual witnesses and complex forces as its derivative
estimates. The two powers give the extra factor `τ / s` after scale comparison. -/
theorem finiteTimeCommutator_flux_correction
    (hxi : node_l_u3A_finite_u2D_xiStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ gain t₀ : ℝ, ∃ Cder : ℕ → ℝ,
      0 < gain ∧ 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsJointObservation Q Z →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∃ H X : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ (τ : ℝ≥0) (i : Fin d), IsFiniteTimeCommutator Q P hP.2.2.1 β τ i (H τ i) (X τ i)) ∧
      ∀ τ : ℝ≥0, t₀ ≤ (τ : ℝ) → ∀ s : ℝ, 4 * (τ : ℝ) ≤ s → ∀ hs : 0 < s,
      ∀ ζ : ℂ, ∀ ν : FluxIndex d,
      let i := ν.elim id (fun _ => ⟨0, by omega⟩)
      let F := fun j => ∑ k : Fin d, (homogenizedCoefficient Q j k : ℂ) • H τ i k
      let signζ := ν.elim (fun _ => ζ) (fun _ => -ζ)
      ‖(1 / 2 : ℂ) • (∑ j : Fin d,
          homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs signζ 1 (fun _ => j) (F j)) +
        ν.elim (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩))
          (fun _ => 0)‖ ≤
        Real.exp (sourceReducedBound D.ellipticity * ‖ζ‖ ^ 2 * s) *
          ((d : ℝ) ^ 2 / 2 * sourceReducedBound D.ellipticity * Cder 2 * (τ : ℝ) *
              (s / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - 1) +
            ‖ζ‖ * (d : ℝ) * sourceReducedBound D.ellipticity * Cder 1 * (τ : ℝ) *
              (s / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - 1 / 2)) := by
  obtain ⟨gain, t₀, Cder, hgain, ht₀, hCder, hbounds⟩ :=
    finiteTimeCommutator_complex_derivative_bounds hxi d hd D
  refine ⟨gain, t₀, Cder, hgain, ht₀, hCder, ?_⟩
  intro Q hQ β Z hβ hZ P hP
  obtain ⟨H, X, hwitness, hest⟩ := hbounds Q hQ β Z hβ hZ P hP
  refine ⟨H, X, hwitness, ?_⟩
  intro τ hτ s hsτ hs ζ ν
  let i : Fin d := ν.elim id (fun _ => ⟨0, by omega⟩)
  let E := Real.exp (sourceReducedBound D.ellipticity * ‖ζ‖ ^ 2 * s)
  let B₁ := E * (Cder 1 * (τ : ℝ) * (s / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - 1 / 2))
  let B₂ := E * (Cder 2 * (τ : ℝ) * (s / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - 1))
  have hφ (w : ℂ) (hw : ‖w‖ = ‖ζ‖) :
      (∀ dirs : Fin 1 → Fin d,
        ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs w 1 dirs
          (finiteTimeCorrector Q P hP.2.2.1 β τ i)‖ ≤ B₁) ∧
      (∀ dirs : Fin 2 → Fin d,
        ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs w 2 dirs
          (finiteTimeCorrector Q P hP.2.2.1 β τ i)‖ ≤ B₂) := by
    constructor
    · intro dirs
      simpa only [Nat.cast_one, hw] using!
        ((hest τ hτ s hsτ hs w 1 (by omega) dirs).2 le_rfl i)
    · intro dirs
      simpa only [Nat.cast_ofNat, show (2 : ℝ) / 2 = 1 by norm_num, hw] using!
        ((hest τ hτ s hsτ hs w 2 (by omega) dirs).2 (by omega) i)
  exact (finiteTimeCommutator_gradient_flux_bound hd Q P hP.2.2.1 β τ i
    (H τ i) (X τ i) (hwitness τ i) s hs ζ ν B₁ B₂ hφ).trans_eq (by dsimp [B₁, B₂, E]; ring)

/-- The literal mesoscopic time eventually lies in the finite-ξ propagation range. -/
theorem exists_unforced_identification_time_threshold (t₀ : ℝ) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      t₀ ≤ T ^ (1 - (1 / 4 : ℝ)) ∧
      4 * T ^ (1 - (1 / 4 : ℝ)) ≤ T - T ^ (1 - (1 / 4 : ℝ)) ∧
      T / 4 ≤ (T - T ^ (1 - (1 / 4 : ℝ))) / 2 ∧
      0 < T - T ^ (1 - (1 / 4 : ℝ)) := by
  have hlarge : ∀ᶠ T : ℝ in atTop, t₀ ≤ T ^ (1 - (1 / 4 : ℝ)) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 - 1 / 4)).eventually
      (eventually_ge_atTop t₀)
  have hsmall : ∀ᶠ T : ℝ in atTop, T ^ (-(1 / 4 : ℝ)) ≤ 1 / 8 :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (hlarge.and hsmall)
  refine ⟨max 2 T₁, le_max_left _ _, ?_⟩
  intro T hT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hT)
  have hh := hT₁ T ((le_max_right _ _).trans hT)
  have he : T ^ (1 - (1 / 4 : ℝ)) = T * T ^ (-(1 / 4 : ℝ)) := by
    calc
      _ = T ^ (1 : ℝ) * T ^ (-(1 / 4 : ℝ)) := by
        rw [← Real.rpow_add hTpos]
        congr 1
      _ = _ := by rw [Real.rpow_one]
  have htau : T ^ (1 - (1 / 4 : ℝ)) ≤ T / 8 := by
    rw [he]
    simpa only [mul_one_div] using! mul_le_mul_of_nonneg_left hh.2 hTpos.le
  exact ⟨hh.1, by linarith, by linarith, by linarith⟩

/-- A structural radius threshold suffices for all mesoscopic time conditions. -/
theorem exists_unforced_identification_radius_threshold (t₀ : ℝ) :
    ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      let T := R ^ 2 / 2
      t₀ ≤ T ^ (1 - (1 / 4 : ℝ)) ∧
      4 * T ^ (1 - (1 / 4 : ℝ)) ≤ T - T ^ (1 - (1 / 4 : ℝ)) ∧
      T / 4 ≤ (T - T ^ (1 - (1 / 4 : ℝ))) / 2 ∧
      0 < T - T ^ (1 - (1 / 4 : ℝ)) := by
  obtain ⟨T₀, hT₀, hh⟩ := exists_unforced_identification_time_threshold t₀
  refine ⟨2 * T₀, by linarith, ?_⟩
  intro R hR
  have hRtwo : 2 ≤ R := by linarith
  have hsq := mul_le_mul_of_nonneg_right hRtwo (by linarith : 0 ≤ R)
  exact hh (R ^ 2 / 2) (by nlinarith only [hT₀, hR, hsq])

/-- The force exponent at any earlier time is bounded at the literal radius scale. -/
theorem unforced_identification_force_scale (R : ℝ) (hR : 0 < R) (z : ℂ)
    (s : ℝ) (hs : s ≤ R ^ 2 / 2) :
    ‖z / (R : ℂ)‖ ^ 2 * s ≤ ‖z‖ ^ 2 / 2 := by
  have hn : ‖z / (R : ℂ)‖ = ‖z‖ / R := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  rw [hn, div_pow]
  calc
    _ ≤ (‖z‖ ^ 2 / R ^ 2) * (R ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by field_simp

/-- The dimensionless force is bounded by the source force parameter. -/
theorem unforced_identification_force_sqrt_scale (R : ℝ) (hR : 0 < R) (z : ℂ) :
    ‖z / (R : ℂ)‖ * Real.sqrt (R ^ 2 / 2) ≤ ‖z‖ := by
  have hn : ‖z / (R : ℂ)‖ = ‖z‖ / R := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hsqrt : Real.sqrt (R ^ 2 / 2) ≤ R := by
    calc
      _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg R])
      _ = R := Real.sqrt_sq hR.le
  rw [hn]
  calc
    _ ≤ (‖z‖ / R) * R := mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = _ := div_mul_cancel₀ _ hR.ne'

/-- First Gaussian derivatives propagate by the same signed-force semigroup. -/
theorem homogeneousDerivativeAverage_one_add
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (ζ : ℂ) (dirs : Fin 1 → Fin d)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousDerivativeAverage Q i (s + t) (add_pos hs ht) ζ 1 dirs f =
      homogeneousAverage Q i s hs ζ
        (homogeneousDerivativeAverage Q i t ht ζ 1 dirs f) := by
  have h := homogeneousAverage_hasHorizontalDerivative_one Q i (s + t)
    (add_pos hs ht) ζ dirs f
  have hinner := homogeneousAverage_hasHorizontalDerivative_one Q i t ht ζ dirs f
  have houter := hinner.homogeneousAverage i s hs ζ
  rw [homogeneousAverage_add] at houter
  exact h.unique houter

/-- The velocity model retains its literal joint field under homogeneous propagation. -/
theorem modelVelocityEndpoint_add (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ r)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) (i : Fin d)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (ζ : ℂ) :
    modelVelocityEndpoint hd Q Z i (s + t) (add_pos hs ht) ζ =
      homogeneousAverage Q ⟨0, by omega⟩ s hs ζ
        (modelVelocityEndpoint hd Q Z i t ht ζ) := by
  classical
  unfold modelVelocityEndpoint
  conv_rhs => rw [← homogeneousAverageCLM_apply]
  simp only [map_add, map_smul, map_sum, homogeneousAverageCLM_apply,
    homogeneousAverage_add, ← homogeneousDerivativeAverage_one_add]

/-- The transpose model propagates at the negative bilinear-transpose force. -/
theorem modelTransposeEndpoint_add (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ r)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (ζ : ℂ) :
    modelTransposeEndpoint hd Q Z (s + t) (add_pos hs ht) ζ =
      homogeneousAverage Q ⟨0, by omega⟩ s hs (-ζ)
        (modelTransposeEndpoint hd Q Z t ht ζ) := by
  classical
  unfold modelTransposeEndpoint
  conv_rhs => rw [← homogeneousAverageCLM_apply]
  simp only [map_smul, map_sum, homogeneousAverageCLM_apply,
    ← homogeneousDerivativeAverage_one_add]

/-- The actual complex-force evolution changes by the time increment times
its scale-explicit positive-time derivative bound. -/
theorem homogeneousAverage_increment_le
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (t s : ℝ)
    (ht : 0 < t) (hs : 0 < s) (ζ : ℂ) (F : Lp ℂ 2 (reducedLaw Q)) :
    ‖homogeneousAverage Q i (t + s) (add_pos ht hs) ζ F -
        homogeneousAverage Q i t ht ζ F‖ ≤
      homogeneousGaussianTimeDerivativeBound d Λ * (t⁻¹ + ‖ζ‖ ^ 2) *
        Real.exp (homogeneousGaussianTimeDerivativeBound d Λ * ‖ζ‖ ^ 2 * (t + s)) *
        ‖F‖ * s := by
  let B := homogeneousGaussianTimeDerivativeBound d Λ
  have hB : 0 < B := homogeneousGaussianTimeDerivativeBound_pos d Λ
  let f : ℝ → Lp ℂ 2 (reducedLaw Q) := fun u =>
    homogeneousGaussianEvolution Q i ζ ⟨max u 0, le_max_right _ _⟩ F
  have hdiff : ∀ u ∈ Set.Icc t (t + s), DifferentiableAt ℝ f u := by
    intro u hu
    exact (hasDerivAt_homogeneousGaussianEvolution_time Q i ζ F u
      (ht.trans_le hu.1)).differentiableAt
  have hbound : ∀ u ∈ Set.Icc t (t + s), ‖deriv f u‖ ≤
      B * (t⁻¹ + ‖ζ‖ ^ 2) * Real.exp (B * ‖ζ‖ ^ 2 * (t + s)) * ‖F‖ := by
    intro u hu
    apply (norm_deriv_homogeneousGaussianEvolution_time_le Q i ζ F u
      (ht.trans_le hu.1)).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg F)
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (by linarith only [inv_anti₀ ht hu.1]) hB.le
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 (by positivity))
    · positivity
    · positivity
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc t (t + s)) (Set.left_mem_Icc.mpr (by linarith))
    (Set.right_mem_Icc.mpr (by linarith))
  have he (u : ℝ) (hu : 0 < u) : f u = homogeneousAverage Q i u hu ζ F := by
    dsimp only [f]
    erw [homogeneousGaussianEvolution_pos Q i ζ _
      (by simpa only [max_eq_left hu.le] using! hu)]
    simp only [max_eq_left hu.le]
    rfl
  simpa only [he (t + s) (add_pos ht hs), he t ht, add_sub_cancel_left,
    Real.norm_eq_abs, abs_of_pos hs] using! h

/-- The prescribed test CLT bounds the actual anisotropic endpoint models.
The constant is chosen before the law, joint field, radius and complex force. -/
theorem modelEndpoint_clt_bound (hclt : node_e_u3A_test_u2D_cltStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ (R : ℝ) (hR : 1 ≤ R) (z : ℂ) (ν : EndpointIndex d),
        ‖(match ν with
          | .inl i => modelVelocityEndpoint hd Q Z i (R ^ 2 / 2) (by positivity)
              (z / (R : ℂ))
          | .inr true => modelTransposeEndpoint hd Q Z (R ^ 2 / 2) (by positivity)
              (z / (R : ℂ))
          | .inr false => modelClockEndpoint hd Q Z (R ^ 2 / 2) (by positivity)
              (z / (R : ℂ)))‖ ≤
          C * Real.exp (C * (1 + ‖z‖) ^ 2) * R ^ (-1 - (d : ℝ) / 2) := by
  obtain ⟨A, hA, ha⟩ := hclt d hd D (2 * d + 11) (by omega)
  obtain ⟨G, hG, hg⟩ := w2ProfileTests_norm_bound d hd (2 * d + 11)
    D.ellipticity D.one_le_ellipticity
  let C := 1 + A * G + G
  have hC : 0 < C := by dsimp [C]; positivity
  have hAG : A * G ≤ C := by dsimp [C]; linarith
  have hGC : G ≤ C := by dsimp [C]; nlinarith [mul_pos hA hG]
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ R hR z ν
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have he := congrArg norm (w2ProfileTests_model hd Q Z R hRpos z ν)
  have hmodel : ‖(match ν with
      | .inl i => modelVelocityEndpoint hd Q Z i (R ^ 2 / 2) (by positivity)
          (z / (R : ℂ))
      | .inr true => modelTransposeEndpoint hd Q Z (R ^ 2 / 2) (by positivity)
          (z / (R : ℂ))
      | .inr false => modelClockEndpoint hd Q Z (R ^ 2 / 2) (by positivity)
          (z / (R : ℂ)))‖ =
        R ^ (-1 - (d : ℝ) / 2) *
          ‖scaledJointPairing Q R hRpos Z (w2ProfileTests hd Q z ν)‖ := by
    cases ν with
    | inl i => simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hRpos.le _)] using! he
    | inr b => cases b <;> simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hRpos.le _)] using! he
  rw [hmodel]
  calc
    _ ≤ R ^ (-1 - (d : ℝ) / 2) *
        (A * (G * Real.exp (G * (1 + ‖z‖) ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hRpos.le _)
      exact (ha Q hQ Z hZ R hR _).trans
        (mul_le_mul_of_nonneg_left (hg _ Q z ν) hA.le)
    _ ≤ R ^ (-1 - (d : ℝ) / 2) *
        (C * Real.exp (C * (1 + ‖z‖) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hRpos.le _)
      rw [← mul_assoc]
      exact mul_le_mul hAG (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hGC (sq_nonneg _))) (Real.exp_pos _).le hC.le
    _ = _ := mul_comm _ _

/-- Reserving a fixed positive smoothing time retains the norm of the actual
velocity model, rather than the unsmoothed joint field, in time replacement. -/
theorem modelVelocityEndpoint_time_increment_le (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ r) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (i : Fin d) (a t s : ℝ) (ha : 0 < a) (ht : 0 < t) (hs : 0 < s) (ζ : ℂ) :
    ‖modelVelocityEndpoint hd Q Z i (t + s + a) (by positivity) ζ -
        modelVelocityEndpoint hd Q Z i (t + a) (by positivity) ζ‖ ≤
      homogeneousGaussianTimeDerivativeBound d Λ * (t⁻¹ + ‖ζ‖ ^ 2) *
        Real.exp (homogeneousGaussianTimeDerivativeBound d Λ * ‖ζ‖ ^ 2 * (t + s)) *
        ‖modelVelocityEndpoint hd Q Z i a ha ζ‖ * s := by
  rw [modelVelocityEndpoint_add hd Q Z i (t + s) a (add_pos ht hs) ha,
    modelVelocityEndpoint_add hd Q Z i t a ht ha]
  exact homogeneousAverage_increment_le Q ⟨0, by omega⟩ t s ht hs ζ _

/-- The identical smoothing argument retains the true negative-force
transpose model and its CLT size. -/
theorem modelTransposeEndpoint_time_increment_le (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ r) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (a t s : ℝ) (ha : 0 < a) (ht : 0 < t) (hs : 0 < s) (ζ : ℂ) :
    ‖modelTransposeEndpoint hd Q Z (t + s + a) (by positivity) ζ -
        modelTransposeEndpoint hd Q Z (t + a) (by positivity) ζ‖ ≤
      homogeneousGaussianTimeDerivativeBound d Λ * (t⁻¹ + ‖ζ‖ ^ 2) *
        Real.exp (homogeneousGaussianTimeDerivativeBound d Λ * ‖ζ‖ ^ 2 * (t + s)) *
        ‖modelTransposeEndpoint hd Q Z a ha ζ‖ * s := by
  rw [modelTransposeEndpoint_add hd Q Z (t + s) a (add_pos ht hs) ha,
    modelTransposeEndpoint_add hd Q Z t a ht ha]
  simpa only [norm_neg] using!
    (homogeneousAverage_increment_le Q ⟨0, by omega⟩ t s ht hs (-ζ)
      (modelTransposeEndpoint hd Q Z a ha ζ))

/-- Parabolic rescaling of the CLT estimate gives the model's time decay
without a bound on the unsmoothed commutator norm. -/
theorem modelEndpoint_clt_time_bound (hclt : node_e_u3A_test_u2D_cltStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ (t : ℝ) (ht : 1 ≤ t) (ζ : ℂ) (ν : EndpointIndex d),
        ‖(match ν with
          | .inl i => modelVelocityEndpoint hd Q Z i t (by positivity) ζ
          | .inr true => modelTransposeEndpoint hd Q Z t (by positivity) ζ
          | .inr false => modelClockEndpoint hd Q Z t (by positivity) ζ)‖ ≤
          C * Real.exp (C * (1 + ‖ζ‖ * Real.sqrt (2 * t)) ^ 2) *
            t ^ (-(1 / 2 + (d : ℝ) / 4)) := by
  obtain ⟨C, hC, hc⟩ := modelEndpoint_clt_bound hclt d hd D
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ t ht ζ ν
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have h2t : 0 < 2 * t := by positivity
  have hRpos : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr h2t
  have hR : 1 ≤ Real.sqrt (2 * t) :=
    (Real.le_sqrt (by norm_num) h2t.le).mpr (by nlinarith)
  have htime : Real.sqrt (2 * t) ^ 2 / 2 = t := by
    rw [Real.sq_sqrt h2t.le]; ring
  have hz : ζ * (Real.sqrt (2 * t) : ℂ) / (Real.sqrt (2 * t) : ℂ) = ζ :=
    mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hRpos.ne')
  have hp : Real.sqrt (2 * t) ^ (-1 - (d : ℝ) / 2) =
      (2 * t) ^ (-(1 / 2 + (d : ℝ) / 4)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h2t.le]
    congr 1
    ring
  have hdecay : Real.sqrt (2 * t) ^ (-1 - (d : ℝ) / 2) ≤
      t ^ (-(1 / 2 + (d : ℝ) / 4)) := by
    rw [hp]
    apply Real.rpow_le_rpow_of_nonpos htpos (by linarith)
    linarith only [Nat.cast_nonneg (α := ℝ) d]
  have h := hc Q hQ Z hZ (Real.sqrt (2 * t)) hR
    (ζ * (Real.sqrt (2 * t) : ℂ)) ν
  simp only [htime, hz, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hRpos] at h
  exact h.trans (mul_le_mul_of_nonneg_left hdecay (by positivity))

/-- In the late window, the positive-time operator increment costs tau/T. -/
theorem homogeneousAverage_late_increment_le
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (T τ : ℝ)
    (hT : 0 < T) (hτ : 0 < τ) (hsmall : τ ≤ T / 8)
    (ζ : ℂ) (F : Lp ℂ 2 (reducedLaw Q)) :
    ‖homogeneousAverage Q i (3 * T / 4) (by positivity) ζ F -
        homogeneousAverage Q i (3 * T / 4 - τ) (by linarith) ζ F‖ ≤
      homogeneousGaussianTimeDerivativeBound d Λ * (2 + ‖ζ‖ ^ 2 * T) *
        Real.exp (homogeneousGaussianTimeDerivativeBound d Λ * ‖ζ‖ ^ 2 * T) *
        ‖F‖ * (τ / T) := by
  let B := homogeneousGaussianTimeDerivativeBound d Λ
  have hB : 0 < B := homogeneousGaussianTimeDerivativeBound_pos d Λ
  have ht : 0 < 3 * T / 4 - τ := by linarith
  have htime : 3 * T / 4 - τ + τ = 3 * T / 4 := by ring
  have hinv : (3 * T / 4 - τ)⁻¹ ≤ 2 / T := by
    have h := inv_anti₀ (half_pos hT) (show T / 2 ≤ 3 * T / 4 - τ by linarith)
    simpa only [inv_div, inv_inv] using! h
  have h := homogeneousAverage_increment_le Q i (3 * T / 4 - τ) τ ht hτ ζ F
  simp only [htime] at h
  apply h.trans
  calc
    _ ≤ B * (2 / T + ‖ζ‖ ^ 2) * Real.exp (B * ‖ζ‖ ^ 2 * T) * ‖F‖ * τ := by
      gcongr
      linarith
    _ = _ := by dsimp only [B]; field_simp

private lemma polynomial_gaussian_absorb (A B K : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 0 ≤ w →
      B * (2 + w ^ 2) * Real.exp (B * w ^ 2) *
        (A * Real.exp (A * (1 + w) ^ 2) * K) ≤
      C * Real.exp (C * (1 + w) ^ 2) := by
  let C := 1 + 3 * B * A * K + A + B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hprod : 3 * B * A * K ≤ C := by dsimp [C]; linarith
  have hexp : A + B + 1 ≤ C := by
    dsimp [C]
    nlinarith only [mul_pos (mul_pos hB hA) hK]
  refine ⟨C, hC, ?_⟩
  intro w hw
  let x := (1 + w) ^ 2
  have hx : 0 ≤ x := sq_nonneg _
  have hwx : w ^ 2 ≤ x := by dsimp [x]; nlinarith
  have he1 : 1 ≤ Real.exp x := Real.one_le_exp hx
  have he2 : x ≤ Real.exp x := (Real.add_one_le_exp x).trans' (by linarith)
  have hp : 2 + w ^ 2 ≤ 3 * Real.exp x := by linarith
  calc
    _ ≤ B * (3 * Real.exp x) * Real.exp (B * x) *
        (A * Real.exp (A * x) * K) := by
      gcongr
    _ = (3 * B * A * K) * Real.exp ((A + B + 1) * x) := by
      rw [show (A + B + 1) * x = x + B * x + A * x by ring,
        Real.exp_add, Real.exp_add]
      ring
    _ ≤ C * Real.exp (C * x) := by
      apply mul_le_mul hprod
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexp hx))
        (Real.exp_pos _).le hC.le

/-- The explicit Gaussian model changes from T-tau to T with relative error
tau/T. This includes both velocity and the actual bilinear transpose, all
complex forces, and a structural constant before the law and joint field. -/
theorem modelEndpoint_late_time_replacement (hclt : node_e_u3A_test_u2D_cltStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ (T τ : ℝ) (hT : 4 ≤ T) (hτ : 0 < τ) (hsmall : τ ≤ T / 8),
      ∀ (ζ : ℂ) (w : ℝ), 0 ≤ w → ‖ζ‖ * Real.sqrt T ≤ w →
      ∀ ν : FluxIndex d,
        let M := fun (t : ℝ) (ht : 0 < t) =>
          ν.elim (fun i => modelVelocityEndpoint hd Q Z i t ht ζ)
            (fun _ => modelTransposeEndpoint hd Q Z t ht ζ)
        ‖M (T - τ) (by linarith) - M T (by positivity)‖ ≤
          C * Real.exp (C * (1 + w) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4)) * (τ / T) := by
  obtain ⟨A, hA, hc⟩ := modelEndpoint_clt_time_bound hclt d hd D
  let B := homogeneousGaussianTimeDerivativeBound d D.ellipticity
  let K := (4 : ℝ) ^ (1 / 2 + (d : ℝ) / 4)
  have hB : 0 < B := homogeneousGaussianTimeDerivativeBound_pos d D.ellipticity
  have hK : 0 < K := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨C, hC, habsorb⟩ := polynomial_gaussian_absorb A B K hA hB hK
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ T τ hT hτ hsmall ζ w hw hforce ν
  let M := fun (t : ℝ) (ht : 0 < t) =>
    ν.elim (fun i => modelVelocityEndpoint hd Q Z i t ht ζ)
      (fun _ => modelTransposeEndpoint hd Q Z t ht ζ)
  have hTpos : 0 < T := by linarith
  have ha : 0 < T / 4 := by positivity
  have ht : 0 < 3 * T / 4 - τ := by linarith
  have hinner : ‖ζ‖ * Real.sqrt (2 * (T / 4)) ≤ w := by
    apply le_trans _ hforce
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (norm_nonneg ζ)
  have hsq : ‖ζ‖ ^ 2 * T ≤ w ^ 2 := by
    calc
      _ = (‖ζ‖ * Real.sqrt T) ^ 2 := by rw [mul_pow, Real.sq_sqrt hTpos.le]
      _ ≤ w ^ 2 := by nlinarith [mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg T)]
  have hp : (T / 4) ^ (-(1 / 2 + (d : ℝ) / 4)) =
      K * T ^ (-(1 / 2 + (d : ℝ) / 4)) := by
    rw [Real.div_rpow hTpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
      div_inv_eq_mul]
    exact mul_comm _ _
  have hm : ‖M (T / 4) ha‖ ≤
      A * Real.exp (A * (1 + w) ^ 2) * K * T ^ (-(1 / 2 + (d : ℝ) / 4)) := by
    have hm0 : ‖M (T / 4) ha‖ ≤
        A * Real.exp (A * (1 + ‖ζ‖ * Real.sqrt (2 * (T / 4))) ^ 2) *
          (T / 4) ^ (-(1 / 2 + (d : ℝ) / 4)) := by
      cases ν with
      | inl i => exact hc Q hQ Z hZ (T / 4) (by linarith) ζ (.inl i)
      | inr u => exact hc Q hQ Z hZ (T / 4) (by linarith) ζ (.inr true)
    rw [hp] at hm0
    apply hm0.trans
    rw [← mul_assoc]
    gcongr
  have hinc : ‖M T hTpos - M (T - τ) (by linarith)‖ ≤
      B * (2 + ‖ζ‖ ^ 2 * T) * Real.exp (B * ‖ζ‖ ^ 2 * T) *
        ‖M (T / 4) ha‖ * (τ / T) := by
    have ht1 : 3 * T / 4 + T / 4 = T := by ring
    have ht2 : 3 * T / 4 - τ + T / 4 = T - τ := by ring
    cases ν with
    | inl i =>
      have h := homogeneousAverage_late_increment_le Q ⟨0, by omega⟩ T τ hTpos hτ
        hsmall ζ (modelVelocityEndpoint hd Q Z i (T / 4) ha ζ)
      rw [← modelVelocityEndpoint_add hd Q Z i _ _ (by positivity) ha,
        ← modelVelocityEndpoint_add hd Q Z i _ _ ht ha] at h
      simp only [ht1, ht2] at h
      exact h
    | inr u =>
      have h := homogeneousAverage_late_increment_le Q ⟨0, by omega⟩ T τ hTpos hτ
        hsmall (-ζ) (modelTransposeEndpoint hd Q Z (T / 4) ha ζ)
      rw [← modelTransposeEndpoint_add hd Q Z _ _ (by positivity) ha,
        ← modelTransposeEndpoint_add hd Q Z _ _ ht ha] at h
      simp only [ht1, ht2, norm_neg] at h
      exact h
  change ‖M (T - τ) _ - M T _‖ ≤ _
  rw [norm_sub_rev]
  apply hinc.trans
  calc
    _ ≤ B * (2 + w ^ 2) * Real.exp (B * w ^ 2) *
        (A * Real.exp (A * (1 + w) ^ 2) * K * T ^ (-(1 / 2 + (d : ℝ) / 4))) *
        (τ / T) := by
      have hpref : B * (2 + ‖ζ‖ ^ 2 * T) * Real.exp (B * ‖ζ‖ ^ 2 * T) ≤
          B * (2 + w ^ 2) * Real.exp (B * w ^ 2) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (by linarith only [hsq]) hB.le
        · apply Real.exp_le_exp.mpr
          nlinarith only [mul_le_mul_of_nonneg_left hsq hB.le]
        · positivity
        · positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul hpref hm (norm_nonneg _)
        (by positivity)) (div_nonneg hτ.le hTpos.le)
    _ = (B * (2 + w ^ 2) * Real.exp (B * w ^ 2) *
        (A * Real.exp (A * (1 + w) ^ 2) * K)) *
        T ^ (-(1 / 2 + (d : ℝ) / 4)) * (τ / T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (habsorb w hw) (Real.rpow_nonneg hTpos.le _))
      (div_nonneg hτ.le hTpos.le)

/-- Literal third estimate of the unforced-identification contract, for every
late-window tau. No covariance assertion or bound on Xi itself is assumed. -/
theorem unforced_flux_model_time_replacement (hclt : node_e_u3A_test_u2D_cltStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ (R : ℝ) (hR : 4 ≤ R) (z : ℂ) (τ : ℝ) (hτ : 0 < τ)
        (hsmall : τ ≤ (R ^ 2 / 2) / 8),
        let T := R ^ 2 / 2
        let ζ := z / (R : ℂ)
        ∀ ν : FluxIndex d,
          let i := ν.elim id (fun _ => ⟨0, by omega⟩)
          let Xi := fun j => Z (.inl (j, i))
          let signζ := ν.elim (fun _ => ζ) (fun _ => -ζ)
          let model := ν.elim
            (fun k => modelVelocityEndpoint hd Q Z k T (by positivity) ζ)
            (fun _ => modelTransposeEndpoint hd Q Z T (by positivity) ζ)
          ‖(1 / 2 : ℂ) • (∑ j : Fin d,
              homogeneousDerivativeAverage Q ⟨0, by omega⟩ (T - τ) (by dsimp [T]; nlinarith)
                signζ 1 (fun _ => j) (Xi j)) +
              ν.elim (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ (T - τ)
                (by dsimp [T]; nlinarith) ζ (Xi ⟨0, by omega⟩)) (fun _ => 0) - model‖ ≤
            C * Real.exp (C * (1 + ‖z‖) ^ 2) *
              T ^ (-(1 / 2 + (d : ℝ) / 4)) * (τ / T) := by
  obtain ⟨C, hC, hc⟩ := modelEndpoint_late_time_replacement hclt d hd D
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ R hR z τ hτ hsmall
  have hRpos : 0 < R := by linarith
  have hT : 4 ≤ R ^ 2 / 2 := by nlinarith
  dsimp only
  intro ν
  have h := hc Q hQ Z hZ (R ^ 2 / 2) τ hT hτ hsmall (z / (R : ℂ)) ‖z‖
    (norm_nonneg z) (unforced_identification_force_sqrt_scale R hRpos z) ν
  cases ν with
  | inl i => simpa only [Sum.elim_inl, modelVelocityEndpoint] using! h
  | inr u => simpa only [Sum.elim_inr, modelTransposeEndpoint, add_zero] using! h

/-- Specializing the completed Gaussian time replacement to the literal
mesoscopic time chooses its constants and radius threshold before the law. -/
theorem unforced_flux_model_mesoscopic_time_replacement
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C R₀ : ℝ, 0 < C ∧ 4 ≤ R₀ ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ (R : ℝ) (hRpos : 0 < R), R₀ ≤ R →
        let T := R ^ 2 / 2
        let τ := T ^ (1 - (1 / 4 : ℝ))
        ∃ hτ : 0 < τ, ∃ hsmall : τ ≤ T / 8,
          ∀ z : ℂ, ∀ ν : FluxIndex d,
            let ζ := z / (R : ℂ)
            let i := ν.elim id (fun _ => ⟨0, by omega⟩)
            let Xi := fun j => Z (.inl (j, i))
            let signζ := ν.elim (fun _ => ζ) (fun _ => -ζ)
            let model := ν.elim
              (fun k => modelVelocityEndpoint hd Q Z k T (by positivity) ζ)
              (fun _ => modelTransposeEndpoint hd Q Z T (by positivity) ζ)
            ‖(1 / 2 : ℂ) • (∑ j : Fin d,
                homogeneousDerivativeAverage Q ⟨0, by omega⟩ (T - τ) (by nlinarith)
                  signζ 1 (fun _ => j) (Xi j)) +
                ν.elim (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ (T - τ)
                  (by nlinarith) ζ (Xi ⟨0, by omega⟩)) (fun _ => 0) - model‖ ≤
              C * Real.exp (C * (1 + ‖z‖) ^ 2) *
                T ^ (-(1 / 2 + (d : ℝ) / 4)) * (τ / T) := by
  obtain ⟨C, hC, hc⟩ := unforced_flux_model_time_replacement hclt d hd D
  have hsmall : ∀ᶠ T : ℝ in atTop, T ^ (-(1 / 4 : ℝ)) ≤ 1 / 8 :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hsmall
  let T₀ := max 4 T₁
  refine ⟨C, 2 * T₀, hC, by dsimp [T₀]; linarith only [le_max_left (4 : ℝ) T₁], ?_⟩
  intro Q hQ Z hZ R hRpos hR
  have hRfour : 4 ≤ R := by dsimp [T₀] at hR; linarith only [le_max_left (4 : ℝ) T₁, hR]
  have hT : T₀ ≤ R ^ 2 / 2 := by
    have hsq := mul_le_mul_of_nonneg_right hRfour (by linarith : 0 ≤ R)
    dsimp [T₀] at hR ⊢
    nlinarith only [hR, hsq, le_max_left (4 : ℝ) T₁]
  have hTpos : 0 < R ^ 2 / 2 := by positivity
  have hh := hT₁ (R ^ 2 / 2) ((le_max_right _ _).trans hT)
  have htau : (R ^ 2 / 2) ^ (1 - (1 / 4 : ℝ)) ≤ (R ^ 2 / 2) / 8 := by
    have he : (R ^ 2 / 2) ^ (1 - (1 / 4 : ℝ)) =
        (R ^ 2 / 2) * (R ^ 2 / 2) ^ (-(1 / 4 : ℝ)) := by
      calc
        _ = (R ^ 2 / 2) ^ (1 : ℝ) * (R ^ 2 / 2) ^ (-(1 / 4 : ℝ)) := by
          rw [← Real.rpow_add hTpos]
          congr 1
        _ = _ := by rw [Real.rpow_one]
    rw [he]
    simpa only [mul_one_div] using! mul_le_mul_of_nonneg_left hh hTpos.le
  refine ⟨Real.rpow_pos_of_pos hTpos _, htau, ?_⟩
  intro z ν
  exact hc Q hQ Z hZ R hRfour z _ (Real.rpow_pos_of_pos hTpos _) htau ν

/-- Actual finite-time commutator witnesses are unique in L2: the gradient
is unique, and the commutator is its literal coefficient expression a.e. -/
theorem finiteTimeCommutator_unique (Q : EnvironmentLaw d Λ r)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : ∀ f : Lp ℂ 2 (reducedLaw Q), Continuous (fun t : ℝ≥0 => P t f))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (τ : ℝ≥0) (i : Fin d)
    {H X H' X' : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (h : IsFiniteTimeCommutator Q P hP β τ i H X)
    (h' : IsFiniteTimeCommutator Q P hP β τ i H' X') : H = H' ∧ X = X' := by
  have hH : H = H' := h.1.unique h'.1
  refine ⟨hH, ?_⟩
  funext j
  apply Lp.ext
  exact (h.2 j).trans (by simpa only [hH] using! (h'.2 j).symm)

private lemma linear_gaussian_absorb (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 0 ≤ w →
      A * Real.exp (B * w ^ 2) * (1 + w) ≤ C * Real.exp (C * (1 + w) ^ 2) := by
  let C := A + B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro w hw
  have hwx : w ^ 2 ≤ (1 + w) ^ 2 := by nlinarith
  have hwexp : 1 + w ≤ Real.exp ((1 + w) ^ 2) := by
    exact (show 1 + w ≤ (1 + w) ^ 2 + 1 by nlinarith).trans (Real.add_one_le_exp _)
  calc
    _ ≤ A * Real.exp (B * (1 + w) ^ 2) * Real.exp ((1 + w) ^ 2) := by gcongr
    _ = A * Real.exp ((B + 1) * (1 + w) ^ 2) := by
      rw [show (B + 1) * (1 + w) ^ 2 = B * (1 + w) ^ 2 + (1 + w) ^ 2 by ring,
        Real.exp_add]
      ring
    _ ≤ C * Real.exp (C * (1 + w) ^ 2) := by
      apply mul_le_mul
      · dsimp [C]; linarith
      · apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg _)
      · positivity
      · exact hC.le

/-- The two differentiated/force decay powers at any comparable time have
one parabolic decay power. All scalar constants precede time and force. -/
theorem comparable_time_flux_decay_le (a b B k : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B) (hk : 0 ≤ k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T u s q w : ℝ), 0 < T → T / 8 ≤ u → s ≤ T →
      0 ≤ q → 0 ≤ w → ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt T ≤ w →
        Real.exp (B * ‖ζ‖ ^ 2 * s) *
          (a * q * u ^ (-k - 1 / 2) + ‖ζ‖ * b * q * u ^ (-k)) ≤
        C * Real.exp (C * (1 + w) ^ 2) * T ^ (-(1 / 2 + k)) * q := by
  let A := a + b + 1
  let K := (8 : ℝ) ^ (1 / 2 + k) + (8 : ℝ) ^ k
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨C, hC, hc⟩ := linear_gaussian_absorb (A * K) B (mul_pos hA hK) hB
  refine ⟨C, hC, ?_⟩
  intro T u s q w hT hu hs hq hw ζ hforce
  have hu' : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hsq : ‖ζ‖ ^ 2 * T ≤ w ^ 2 := by
    calc
      _ = (‖ζ‖ * Real.sqrt T) ^ 2 := by rw [mul_pow, Real.sq_sqrt hT.le]
      _ ≤ w ^ 2 := by nlinarith [mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg T)]
  have he : B * ‖ζ‖ ^ 2 * s ≤ B * w ^ 2 := by
    calc
      _ = B * (‖ζ‖ ^ 2 * s) := by ring
      _ ≤ B * (‖ζ‖ ^ 2 * T) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) hB
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq hB
  have hdecay := LateUnsmoothing.comparable_time_decay_le hT hu (norm_nonneg ζ) hk
  have hcoeff : a * q * u ^ (-k - 1 / 2) + ‖ζ‖ * b * q * u ^ (-k) ≤
      A * (u ^ (-(1 / 2 + k)) + ‖ζ‖ * u ^ (-k)) * q := by
    have haA : a ≤ A := by dsimp [A]; linarith
    have hbA : b ≤ A := by dsimp [A]; linarith
    rw [show -k - 1 / 2 = -(1 / 2 + k) by ring]
    calc
      _ ≤ A * q * u ^ (-(1 / 2 + k)) + ‖ζ‖ * A * q * u ^ (-k) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ Real.exp (B * w ^ 2) * (A *
        (K * (1 + w) * T ^ (-(1 / 2 + k))) * q) := by
      apply mul_le_mul (Real.exp_le_exp.mpr he)
      · apply hcoeff.trans
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (hdecay.trans (by dsimp only [K]; gcongr)) hA.le) hq
      · positivity
      · positivity
    _ = (A * K * Real.exp (B * w ^ 2) * (1 + w)) *
        T ^ (-(1 / 2 + k)) * q := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hc w hw) (by positivity)) hq

/-- The first two estimates of the unforced-identification contract, for
one common actual commutator family. Constants and the radius threshold are
chosen before the law; both bounds hold for every complex force parameter. -/
theorem finiteTimeCommutator_normalized_flux_bounds
    (hxi : node_l_u3A_finite_u2D_xiStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ ε₁ C R₀ : ℝ, 0 < ε₁ ∧ 0 < C ∧ 2 ≤ R₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsJointObservation Q Z →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∃ H X : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ (τ : ℝ≥0) (i : Fin d), IsFiniteTimeCommutator Q P hP.2.2.1 β τ i (H τ i) (X τ i)) ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ z : ℂ,
      let T := R ^ 2 / 2
      let τ := T ^ (1 - (1 / 4 : ℝ))
      let ζ := z / (R : ℂ)
      ∃ ht : 0 < T - τ,
      let E := fun (ν : FluxIndex d) (F : Fin d → Lp ℂ 2 (reducedLaw Q)) =>
        let signζ := ν.elim (fun _ => ζ) (fun _ => -ζ)
        (1 / 2 : ℂ) • (∑ j : Fin d,
          homogeneousDerivativeAverage Q ⟨0, by omega⟩ (T - τ) ht signζ 1 (fun _ => j) (F j)) +
        ν.elim (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ (T - τ) ht ζ (F ⟨0, by omega⟩))
          (fun _ => 0)
      ∀ ν : FluxIndex d,
        let i := ν.elim id (fun _ => ⟨0, by omega⟩)
        ‖E ν (fun j => centeredComplexLp Q (X τ.toNNReal i j) - Z (.inl (j,i)))‖ ≤
          C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4)) * τ ^ (-ε₁) ∧
        ‖E ν (fun j => ∑ k : Fin d,
          (homogenizedCoefficient Q j k : ℂ) • H τ.toNNReal i k)‖ ≤
          C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4)) * (τ / T) := by
  obtain ⟨ε, t₁, A, hε, ht₁, hA, hreplace⟩ := finiteTimeCommutator_flux_replacement hxi d hd D
  obtain ⟨ε', t₂, B, _hε', ht₂, hB, hcorrect⟩ := finiteTimeCommutator_flux_correction hxi d hd D
  have hS : 0 ≤ sourceReducedBound D.ellipticity :=
    (Clock.sourceReducedBound_pos D.one_le_ellipticity).le
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hA0 := hA 0
  have hA1 := hA 1
  have hB1 := hB 1
  have hB2 := hB 2
  obtain ⟨C₁, hC₁, hdecay₁⟩ := comparable_time_flux_decay_le
    ((d : ℝ) / 2 * A 1) (A 0) (sourceReducedBound D.ellipticity) ((d : ℝ) / 4)
    (by positivity) (hA 0).le hS (by positivity)
  obtain ⟨C₂, hC₂, hdecay₂⟩ := comparable_time_flux_decay_le
    ((d : ℝ) ^ 2 / 2 * sourceReducedBound D.ellipticity * B 2)
    ((d : ℝ) * sourceReducedBound D.ellipticity * B 1)
    (sourceReducedBound D.ellipticity) (1 + (d : ℝ) / 4)
    (by positivity) (by positivity) hS (by positivity)
  obtain ⟨R₀, hR₀, htime⟩ := exists_unforced_identification_radius_threshold (max t₁ t₂)
  let C := C₁ + C₂
  have hC : 0 < C := add_pos hC₁ hC₂
  have hC₁C : C₁ ≤ C := by dsimp [C]; linarith
  have hC₂C : C₂ ≤ C := by dsimp [C]; linarith
  refine ⟨ε, C, R₀, hε, hC, hR₀, ?_⟩
  intro Q hQ β Z hβ hZ P hP
  obtain ⟨H, X, hHX, hrep⟩ := hreplace Q hQ β Z hβ hZ P hP
  obtain ⟨H', X', hHX', hcor⟩ := hcorrect Q hQ β Z hβ hZ P hP
  have hHH : H' = H := by
    funext t i
    exact (finiteTimeCommutator_unique Q P hP.2.2.1 β t i (hHX' t i) (hHX t i)).1
  have hXX : X' = X := by
    funext t i
    exact (finiteTimeCommutator_unique Q P hP.2.2.1 β t i (hHX' t i) (hHX t i)).2
  subst H' X'
  refine ⟨H, X, hHX, ?_⟩
  intro R hR z
  let T := R ^ 2 / 2
  let τ := T ^ (1 - (1 / 4 : ℝ))
  let ζ := z / (R : ℂ)
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) (hR₀.trans hR)
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hτpos : 0 < τ := Real.rpow_pos_of_pos hTpos _
  obtain ⟨hτ, hprop, hcomp, ht⟩ := htime R hR
  change max t₁ t₂ ≤ τ at hτ
  change 4 * τ ≤ T - τ at hprop
  change T / 4 ≤ (T - τ) / 2 at hcomp
  change 0 < T - τ at ht
  have hτcoe : ((τ.toNNReal : ℝ≥0) : ℝ) = τ := Real.coe_toNNReal _ hτpos.le
  have hforce : ‖ζ‖ * Real.sqrt T ≤ ‖z‖ :=
    unforced_identification_force_sqrt_scale R hRpos z
  have hcomp' : T / 8 ≤ (T - τ) / 2 := by linarith
  have hbefore : T - τ ≤ T := by linarith
  refine ⟨ht, ?_⟩
  dsimp only
  intro ν
  have hr := hrep τ.toNNReal (by rw [hτcoe]; exact (le_max_left _ _).trans hτ)
    (T - τ) (by simpa only [hτcoe] using! hprop) ht ζ ν
  have hc := hcor τ.toNNReal (by rw [hτcoe]; exact (le_max_right _ _).trans hτ)
    (T - τ) (by simpa only [hτcoe] using! hprop) ht ζ ν
  simp only [hτcoe] at hr hc
  have hs₁ := hdecay₁ T ((T - τ) / 2) (T - τ) (τ ^ (-ε)) ‖z‖
    hTpos hcomp' hbefore (by positivity) (norm_nonneg z) ζ hforce
  have hs₂ := hdecay₂ T ((T - τ) / 2) (T - τ) τ ‖z‖
    hTpos hcomp' hbefore hτpos.le (norm_nonneg z) ζ hforce
  have hp : T ^ (-(1 / 2 + (1 + (d : ℝ) / 4))) * τ =
      T ^ (-(1 / 2 + (d : ℝ) / 4)) * (τ / T) := by
    have he : -(1 / 2 + (1 + (d : ℝ) / 4)) =
        -(1 / 2 + (d : ℝ) / 4) + (-1) := by ring
    rw [he, Real.rpow_add hTpos, Real.rpow_neg_one]
    ring
  constructor
  · apply hr.trans
    calc
      _ = _ := by congr 1; ring_nf
      _ ≤ _ := hs₁
      _ ≤ _ := by gcongr
  · apply hc.trans
    have hs₂' : Real.exp (sourceReducedBound D.ellipticity * ‖ζ‖ ^ 2 * (T - τ)) *
        ((d : ℝ) ^ 2 / 2 * sourceReducedBound D.ellipticity * B 2 * τ *
            ((T - τ) / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - 1) +
          ‖ζ‖ * (d : ℝ) * sourceReducedBound D.ellipticity * B 1 * τ *
            ((T - τ) / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - 1 / 2)) ≤
        C₂ * Real.exp (C₂ * (1 + ‖z‖) ^ 2) *
          T ^ (-(1 / 2 + (d : ℝ) / 4)) * (τ / T) := by
      have he₂ : -(1 + (d : ℝ) / 4) = -(1 / 2 + (d : ℝ) / 4) - 1 / 2 := by ring
      simp only [he₂] at hs₂
      calc
        _ = _ := by congr 1; ring_nf
        _ ≤ _ := hs₂
        _ = _ := by rw [mul_assoc, mul_assoc, hp]; ring
    exact hs₂'.trans (by gcongr)

/-- Bilinear transposition of a first Gaussian derivative reverses force
and contributes the spatial integration-by-parts minus sign, for all L2 data. -/
theorem integral_homogeneousDerivativeAverage_one_bilinear_transpose
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (j : Fin d) (f g : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, homogeneousDerivativeAverage Q i s hs ζ 1 (fun _ => j) f ω * g ω
      ∂reducedLaw Q) =
      -(∫ ω, f ω * homogeneousDerivativeAverage Q i s hs (-ζ) 1 (fun _ => j) g ω
        ∂reducedLaw Q) := by
  have hf := homogeneousDerivativeAverage_one_add Q i (s / 2) (s / 2)
    (half_pos hs) (half_pos hs) ζ (fun _ => j) f
  have hg := homogeneousDerivativeAverage_one_add Q i (s / 2) (s / 2)
    (half_pos hs) (half_pos hs) (-ζ) (fun _ => j) g
  simp only [add_halves] at hf hg
  rw [hf, integral_homogeneousAverage_bilinear_transpose]
  have hparts := (complexHorizontalDerivatives_integration_by_parts
    (homogeneousAverage_hasHorizontalDerivative_one Q i (s / 2) (half_pos hs)
      ζ (fun _ => j) f)
    (homogeneousAverage_hasHorizontalDerivative_one Q i (s / 2) (half_pos hs)
      (-ζ) (fun _ => j) g)).2.2
  rw [hparts]
  congr 1
  rw [integral_homogeneousAverage_bilinear_transpose, hg]

/-- Centering preserves and reflects the actual strong horizontal gradient. -/
theorem hasComplexHorizontalGradient_centered_iff
    (Q : EnvironmentLaw d Λ r) (f : Lp ℂ 2 (reducedLaw Q))
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (centeredComplexLp Q f) G ↔
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G := by
  have he (k : Fin d) (t : ℝ) :
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector k)
        (centeredComplexLp Q f) - centeredComplexLp Q f =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector k) f - f := by
    change complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector k)
      (f - Lp.const 2 (reducedLaw Q) _) - (f - Lp.const 2 (reducedLaw Q) _) = _
    rw [map_sub, complexTranslation_const]
    abel
  unfold HasComplexHorizontalGradient HasComplexHorizontalDerivative
  simp_rw [he]

private noncomputable def fluxPair (Q : EnvironmentLaw d Λ r)
    (f : Lp ℂ 2 (reducedLaw Q)) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 f

private theorem fluxPair_apply (Q : EnvironmentLaw d Λ r)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    fluxPair Q f g = ∫ ω, f ω * g ω ∂reducedLaw Q := by
  rw [fluxPair, ContinuousLinearMap.lpPairing_eq_integral]
  rfl

/-- Gaussian averaging converts the full weak divergence equation to its
literal differentiated-kernel flux, on arbitrary L2 data. -/
theorem homogeneousAverage_eq_flux_of_weak
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ c : ℂ)
    (u : Lp ℂ 2 (reducedLaw Q)) (F : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hw : ∀ (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V →
      (∫ ω, u ω * v ω ∂reducedLaw Q) =
        -(1 / 2 : ℂ) * (∑ j, ∫ ω, F j ω * V j ω ∂reducedLaw Q) +
          c * ∫ ω, F i ω * v ω ∂reducedLaw Q) :
    homogeneousAverage Q i s hs ζ u =
      (1 / 2 : ℂ) • (∑ j, homogeneousDerivativeAverage Q i s hs ζ 1 (fun _ => j) (F j)) +
        c • homogeneousAverage Q i s hs ζ (F i) := by
  classical
  have hpair (g : Lp ℂ 2 (reducedLaw Q)) :
      (∫ ω, homogeneousAverage Q i s hs ζ u ω * g ω ∂reducedLaw Q) =
        ∫ ω, ((1 / 2 : ℂ) • (∑ j, homogeneousDerivativeAverage Q i s hs ζ 1
          (fun _ => j) (F j)) + c • homogeneousAverage Q i s hs ζ (F i)) ω * g ω
          ∂reducedLaw Q := by
    rw [integral_homogeneousAverage_bilinear_transpose]
    have he := hw (homogeneousAverage Q i s hs (-ζ) g)
      (fun j => homogeneousDerivativeAverage Q i s hs (-ζ) 1 (fun _ => j) g)
      (fun j => homogeneousAverage_hasHorizontalDerivative_one Q i s hs (-ζ) (fun _ => j) g)
    rw [he]
    have hp (f : Lp ℂ 2 (reducedLaw Q)) :
        (∫ ω, f ω * g ω ∂reducedLaw Q) = fluxPair Q g f := by
      simp only [fluxPair_apply, mul_comm]
    rw [hp, map_add, map_smul, map_sum, map_smul]
    simp only [smul_eq_mul, fluxPair_apply, mul_comm (g _)]
    simp_rw [integral_homogeneousAverage_bilinear_transpose,
      integral_homogeneousDerivativeAverage_one_bilinear_transpose]
    rw [Finset.sum_neg_distrib]
    ring
  apply ext_inner_left ℂ
  intro g
  have he := hpair (complexL2Conjugation (reducedLaw Q) g)
  have hcomm (f : Lp ℂ 2 (reducedLaw Q)) :
      (∫ ω, f ω * complexL2Conjugation (reducedLaw Q) g ω ∂reducedLaw Q) =
        ∫ ω, complexL2Conjugation (reducedLaw Q) g ω * f ω ∂reducedLaw Q := by
    congr 1
    funext ω
    exact mul_comm _ _
  rw [hcomm, hcomm] at he
  simpa only [← inner_complexL2Conjugation_eq_integral_mul,
    complexL2Conjugation_involutive] using! he

private theorem fluxPair_centered (Q : EnvironmentLaw d Λ r)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    fluxPair Q f (centeredComplexLp Q g) =
      fluxPair Q f g - (∫ ω, f ω ∂reducedLaw Q) * (∫ ω, g ω ∂reducedLaw Q) := by
  change fluxPair Q f (g - Lp.const 2 (reducedLaw Q) _) = _
  rw [map_sub, fluxPair_apply, fluxPair_apply]
  congr 1
  calc
    _ = ∫ ω, f ω * (∫ ω, g ω ∂reducedLaw Q) ∂reducedLaw Q := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (∫ ω, g ω ∂reducedLaw Q)] with ω hω
      simp only [hω, Function.const_apply]
    _ = _ := integral_mul_const _ _

/-- Centering the test gives the centered weak flux equation, since every
actual horizontal test derivative has mean zero. -/
theorem centered_weak_flux
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (c : ℂ)
    (u : Lp ℂ 2 (reducedLaw Q)) (F : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hw : ∀ (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V →
      (∫ ω, u ω * v ω ∂reducedLaw Q) =
        -(1 / 2 : ℂ) * (∑ j, ∫ ω, F j ω * V j ω ∂reducedLaw Q) +
          c * ∫ ω, F i ω * v ω ∂reducedLaw Q) :
    ∀ (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V →
      (∫ ω, centeredComplexLp Q u ω * v ω ∂reducedLaw Q) =
        -(1 / 2 : ℂ) * (∑ j, ∫ ω, centeredComplexLp Q (F j) ω * V j ω ∂reducedLaw Q) +
          c * ∫ ω, centeredComplexLp Q (F i) ω * v ω ∂reducedLaw Q := by
  intro v V hV
  have he := hw (centeredComplexLp Q v) V
    ((hasComplexHorizontalGradient_centered_iff Q v V).mpr hV)
  have hp (f g : Lp ℂ 2 (reducedLaw Q)) :
      (∫ ω, centeredComplexLp Q f ω * g ω ∂reducedLaw Q) =
        fluxPair Q f g - (∫ ω, f ω ∂reducedLaw Q) * (∫ ω, g ω ∂reducedLaw Q) := by
    rw [show (∫ ω, centeredComplexLp Q f ω * g ω ∂reducedLaw Q) =
      fluxPair Q g (centeredComplexLp Q f) by simp only [fluxPair_apply, mul_comm],
      fluxPair_centered]
    simp only [fluxPair_apply, mul_comm]
  simp only [← fluxPair_apply, fluxPair_centered] at he
  simp only [hp, (hV _).integral_eq_zero, mul_zero, sub_zero]
  exact he

/-- The forward weak flux equation holds for every supplied literal finite-time
flux witness, after identifying its integrated gradient with the actual primitive. -/
theorem finiteTimeFlux_forward_weak {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {hQ : HasSmoothBounds D Q}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ) (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (ha : IsReducedCoefficientObservation Q a)
    (μ : Lp ℂ 2 (reducedLaw Q))
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (t : ℝ≥0) (j : Fin d)
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, P t (β j + ζ • a ⟨0, by omega⟩ j) ω * v ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * (∑ k, ∫ ω, F t (.inl j) k ω * V k ω ∂reducedLaw Q) +
        ζ * ∫ ω, F t (.inl j) ⟨0, by omega⟩ ω * v ω ∂reducedLaw Q := by
  classical
  obtain ⟨hGc, hUc, hgrad, hflux⟩ := hF
  have hprimitive := timeFlux_forward_integral_gradient_eq hP
    (β j + ζ • a ⟨0, by omega⟩ j) (fun t => G t (.inl j)) (hGc (.inl j))
    (fun t => (hasComplexHorizontalGradient_centered_iff Q _ _).mp (hgrad t (.inl j))) t
  have hraw (k : Fin d) : (F t (.inl j) k : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (ω.1 0 k j : ℂ) + ∑ l, (ω.1 0 k l : ℂ) *
        (∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit
          (β j + ζ • a ⟨0, by omega⟩ j) s) l ω := by
    have hpk (l : Fin d) := congrFun hprimitive l
    filter_upwards [hflux t (.inl j) k, ae_all_iff.mpr (fun l => ha k l)] with ω hf haω
    simpa only [finiteTimeFluxObservation, Sum.elim_inl, sub_zero, haω, hpk] using! hf
  have hp (k : Fin d) (w : Lp ℂ 2 (reducedLaw Q)) :
      (∫ ω, F t (.inl j) k ω * w ω ∂reducedLaw Q) =
        ∫ ω, ((ω.1 0 k j : ℂ) + ∑ l, (ω.1 0 k l : ℂ) *
          (∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit
            (β j + ζ • a ⟨0, by omega⟩ j) s) l ω) * w ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [hraw k] with ω hω
    rw [hω]
  have hsum : (∑ k, ∫ ω, F t (.inl j) k ω * V k ω ∂reducedLaw Q) =
      ∫ ω, ∑ k, ((ω.1 0 k j : ℂ) + ∑ l, (ω.1 0 k l : ℂ) *
        (∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit
          (β j + ζ • a ⟨0, by omega⟩ j) s) l ω) * V k ω ∂reducedLaw Q := by
    rw [← integral_finset_sum Finset.univ
      (f := fun k ω => F t (.inl j) k ω * V k ω)
      (fun k _ => (Lp.memLp (F t (.inl j) k)).integrable_mul (Lp.memLp (V k)))]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hraw] with ω hω
    simp only [hω]
  rw [hsum, hp]
  exact timeFlux_forward_endpoint_weak hβ ha hP t j v V hV

/-- The transpose weak flux uses the supplied primitive and retains its literal
conservative -2*zeta correction. No forward identification at negative force is used. -/
theorem finiteTimeFlux_transpose_weak {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {hQ : HasSmoothBounds D Q}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ) (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (ha : IsReducedCoefficientObservation Q a)
    (μ : Lp ℂ 2 (reducedLaw Q))
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (t : ℝ≥0)
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, transposeEndpoint Q ⟨0, by omega⟩ Pdag β t ω * v ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * (∑ j, ∫ ω, F t (.inr ()) j ω * V j ω ∂reducedLaw Q) := by
  classical
  obtain ⟨hGc, hUc, hgrad, hflux⟩ := hF
  obtain ⟨H, hH, hw⟩ := timeFlux_transpose_endpoint_weak hβ hP hPdag t
  have hprimitive : H = fun k => ∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal (.inr ()) k :=
    hH.unique (timeFlux_integral_gradient _ (fun s => G s (.inr ()))
      (hUc _) (hGc (.inr ())) (fun s => hgrad s (.inr ())) t)
  have hraw (j : Fin d) : (F t (.inr ()) j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (ω.1 0 j ⟨0, by omega⟩ : ℂ) + (∑ k, (ω.1 0 j k : ℂ) * H k ω) -
        2 * ζ * (ω.1 0 j ⟨0, by omega⟩ : ℂ) *
          (∫ s in Icc (0 : ℝ) (t : ℝ), Pdag s.toNNReal (β ⟨0, by omega⟩)) ω := by
    rw [hprimitive]
    filter_upwards [hflux t (.inr ()) j, ae_all_iff.mpr (fun k => ha j k)] with ω hf haω
    simpa only [finiteTimeFluxObservation, Sum.elim_inr, transposeEndpoint, haω] using! hf
  have hsum : (∑ j, ∫ ω, F t (.inr ()) j ω * V j ω ∂reducedLaw Q) =
      ∫ ω, ∑ j, ((ω.1 0 j ⟨0, by omega⟩ : ℂ) + (∑ k, (ω.1 0 j k : ℂ) * H k ω) -
        2 * ζ * (ω.1 0 j ⟨0, by omega⟩ : ℂ) *
          (∫ s in Icc (0 : ℝ) (t : ℝ), Pdag s.toNNReal (β ⟨0, by omega⟩)) ω) * V j ω
          ∂reducedLaw Q := by
    rw [← integral_finset_sum Finset.univ
      (f := fun j ω => F t (.inr ()) j ω * V j ω)
      (fun j _ => (Lp.memLp (F t (.inr ()) j)).integrable_mul (Lp.memLp (V j)))]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hraw] with ω hω
    simp only [hω]
  rw [hsum]
  exact hw v V hV

/-- Exact Gaussian propagation of the actual early endpoint through its
centered finite-time flux, simultaneously for velocity and true transpose. -/
theorem finiteTimeFlux_homogeneousAverage {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {hQ : HasSmoothBounds D Q}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ) (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (ha : IsReducedCoefficientObservation Q a)
    (μ : Lp ℂ 2 (reducedLaw Q))
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (t : ℝ≥0) (s : ℝ) (hs : 0 < s) (ν : FluxIndex d) :
    homogeneousAverage Q ⟨0, by omega⟩ s hs (ν.elim (fun _ => ζ) (fun _ => -ζ))
        (indexedEndpoint hd Q (ν.elim Sum.inl (fun _ => Sum.inr true)) ζ P Pdag β a μ t) =
      (1 / 2 : ℂ) • (∑ j, homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs
        (ν.elim (fun _ => ζ) (fun _ => -ζ)) 1 (fun _ => j)
        (centeredComplexLp Q (F t ν j))) +
      ν.elim (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ s hs ζ
        (centeredComplexLp Q (F t ν ⟨0, by omega⟩))) (fun _ => 0) := by
  cases ν with
  | inl j =>
    exact homogeneousAverage_eq_flux_of_weak Q ⟨0, by omega⟩ s hs ζ ζ _ _
      (centered_weak_flux Q ⟨0, by omega⟩ ζ _ _
        (finiteTimeFlux_forward_weak hd Q P Pdag ζ hP β hβ a ha μ G F hF t j))
  | inr u =>
    have hw := finiteTimeFlux_transpose_weak hd Q P Pdag ζ hP hPdag β hβ a ha μ G F hF t
    have hcenter : centeredComplexLp Q (transposeEndpoint Q ⟨0, by omega⟩ Pdag β t) =
        transposeEndpoint Q ⟨0, by omega⟩ Pdag β t := by
      unfold centeredComplexLp transposeEndpoint
      rw [hPdag.integral_eq hP, drift_integral_zero hβ, map_zero, sub_zero]
    have he := homogeneousAverage_eq_flux_of_weak Q ⟨0, by omega⟩ s hs (-ζ) 0 _ _
      (centered_weak_flux Q ⟨0, by omega⟩ 0 _ _ (by
        intro v V hV
        simpa only [zero_mul, add_zero] using! hw v V hV))
    cases u
    simpa only [hcenter, zero_smul, add_zero, Sum.elim_inr, indexedEndpoint] using! he

/-- The literal differentiated Gaussian flux is a continuous linear map of
its vector input; the true transpose has negative force and no force term. -/
noncomputable def homogeneousFluxCLM (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) (ν : FluxIndex d) :
    (Fin d → Lp ℂ 2 (reducedLaw Q)) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (1 / 2 : ℂ) • (∑ j, (homogeneousDerivativeAverageCLM Q i s hs
    (ν.elim (fun _ => ζ) (fun _ => -ζ)) 1 (fun _ => j)).comp (ContinuousLinearMap.proj j)) +
    ν.elim (fun _ => ζ • (homogeneousAverageCLM Q i s hs ζ).comp (ContinuousLinearMap.proj i))
      (fun _ => 0)

@[simp] theorem homogeneousFluxCLM_apply (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) (ν : FluxIndex d)
    (F : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    homogeneousFluxCLM Q i s hs ζ ν F =
      (1 / 2 : ℂ) • (∑ j, homogeneousDerivativeAverage Q i s hs
        (ν.elim (fun _ => ζ) (fun _ => -ζ)) 1 (fun _ => j) (F j)) +
      ν.elim (fun _ => ζ • homogeneousAverage Q i s hs ζ (F i)) (fun _ => 0) := by
  classical
  cases ν <;> simp only [homogeneousFluxCLM, Sum.elim_inl, Sum.elim_inr,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    homogeneousDerivativeAverageCLM_apply, homogeneousAverageCLM_apply,
    ContinuousLinearMap.zero_apply]

/-- The propagated early endpoint splits exactly into force replacement,
finite commutator replacement, the anisotropic corrector contribution and
propagation of Xi. The same actual G,F,H,X witnesses occur in every term. -/
theorem finiteTimeFlux_homogeneous_decomposition {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {hQ : HasSmoothBounds D Q}
    (P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : ∀ w, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ w (P w))
    (hPdag : ∀ w, IsComplexTransposeSemigroup Q (P w) (Pdag w))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (ha : IsReducedCoefficientObservation Q a)
    (μ : Lp ℂ 2 (reducedLaw Q))
    (G F : ℂ → ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : ∀ w, IsFiniteTimeFlux hd Q w (P w) (Pdag w) β a μ (G w) (F w))
    (ζ : ℂ) (t : ℝ≥0) (s : ℝ) (hs : 0 < s) (ν : FluxIndex d)
    (H X : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hX : IsFiniteTimeCommutator Q (P 0) (hP 0).2.2.1 β t
      (ν.elim id (fun _ => ⟨0, by omega⟩)) H X)
    (Xi : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    let E := homogeneousFluxCLM Q ⟨0, by omega⟩ s hs ζ ν
    homogeneousAverage Q ⟨0, by omega⟩ s hs (ν.elim (fun _ => ζ) (fun _ => -ζ))
        (indexedEndpoint hd Q (ν.elim Sum.inl (fun _ => Sum.inr true)) ζ
          (P ζ) (Pdag ζ) β a μ t) =
      E (fun j => centeredComplexLp Q (F ζ t ν j - F 0 t ν j)) +
      E (fun j => centeredComplexLp Q (X j) - Xi j) +
      E (fun j => ∑ k, (homogenizedCoefficient Q j k : ℂ) • H k) + E Xi := by
  dsimp only
  let E := homogeneousFluxCLM Q ⟨0, by omega⟩ s hs ζ ν
  have hzero (j : Fin d) : centeredComplexLp Q (F 0 t ν j) =
      centeredComplexLp Q (X j) + ∑ k, (homogenizedCoefficient Q j k : ℂ) • H k := by
    cases ν with
    | inl i =>
      exact centered_finiteTimeFlux_zero hd Q (P 0) (Pdag 0) (hP 0)
        β hβ a ha μ (G 0) (F 0) (hF 0) t i H X hX j
    | inr u =>
      cases u
      rw [finiteTimeFlux_transpose_zero hd Q (P 0) (Pdag 0) (hP 0)
        (hPdag 0) β hβ a μ (G 0) (F 0) (hF 0) t j]
      exact centered_finiteTimeFlux_zero hd Q (P 0) (Pdag 0) (hP 0)
        β hβ a ha μ (G 0) (F 0) (hF 0) t ⟨0, by omega⟩ H X hX j
  have hsplit : (fun j => centeredComplexLp Q (F ζ t ν j)) =
      (fun j => centeredComplexLp Q (F ζ t ν j - F 0 t ν j)) +
      (fun j => centeredComplexLp Q (X j) - Xi j) +
      (fun j => ∑ k, (homogenizedCoefficient Q j k : ℂ) • H k) + Xi := by
    funext j
    simp only [Pi.add_apply, ← centeredComplexLpCLM_apply, map_sub]
    have hz := hzero j
    simp only [← centeredComplexLpCLM_apply] at hz
    rw [hz]
    abel
  have he := finiteTimeFlux_homogeneousAverage hd Q (P ζ) (Pdag ζ) ζ (hP ζ)
    (hPdag ζ) β hβ a ha μ (G ζ) (F ζ) (hF ζ) t s hs ν
  rw [← homogeneousFluxCLM_apply] at he
  rw [he, hsplit, map_add, map_add, map_add]


/-- The prescribed late-propagation dependency at the literal radius scaling,
with one gain before the real window constant and constants before the law. -/
theorem latePropagation_radius_bound
    (hlate : node_l_u3A_late_u2D_propagationStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ gain : ℝ, 0 < gain ∧ ∀ C₀ : ℝ, 0 < C₀ →
      ∃ C R₀ : ℝ, 0 < C ∧ 2 ≤ R₀ ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ → ∀ R : ℝ, 0 < R → R₀ ≤ R → ∀ z : ℂ,
        (‖z‖ ≤ 2 ∨ ∃ x : ℝ, z = (x : ℂ) ∧ |x| ≤ C₀ * Real.log R ^ (1 / 4 : ℝ)) →
        let T := R ^ 2 / 2
        let τ := T ^ (1 - (1 / 4 : ℝ))
        let ζ := z / (R : ℂ)
        ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
          IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
          IsComplexTransposeSemigroup Q P Pdag →
          ∃ ht : 0 < T - τ, ∀ ν : EndpointIndex d,
          ‖indexedEndpoint hd Q ν ζ P Pdag β a μ T.toNNReal -
            homogeneousAverage Q ⟨0, by omega⟩ (T - τ) ht
              ((endpointDriftSign ν : ℂ) * ζ)
              (indexedEndpoint hd Q ν ζ P Pdag β a μ τ.toNNReal)‖ ≤
            C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4) - gain) := by
  obtain ⟨gain, Cd, Td, hg, hCd, hTd, hdisc, hreal⟩ :=
    hlate d hd D (1 / 4) (by norm_num) (by norm_num)
  refine ⟨gain, hg, ?_⟩
  intro C₀ hC₀
  obtain ⟨Cw, Tw, hCw, hTw, hw⟩ := hreal C₀ hC₀
  refine ⟨Cd + Cw, max Td Tw, by positivity, hTd.trans (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ R hRpos hR z hz
  dsimp only
  intro P Pdag hP hPdag
  let T := R ^ 2 / 2
  let τ := T ^ (1 - (1 / 4 : ℝ))
  let ζ := z / (R : ℂ)
  have hRtwo : 2 ≤ R := hTd.trans ((le_max_left _ _).trans hR)
  have hRT : R ≤ T := by dsimp [T]; nlinarith
  have hT : 1 < T := by linarith
  have ht : 0 < T - τ := by
    have he := Real.rpow_lt_self_of_one_lt hT (show 1 - (1 / 4 : ℝ) < 1 by norm_num)
    dsimp only [τ]
    linarith
  refine ⟨ht, ?_⟩
  have hscale : ‖ζ‖ ^ 2 * T ≤ (1 + ‖z‖) ^ 2 := by
    have he := unforced_identification_force_scale R hRpos z T le_rfl
    change ‖ζ‖ ^ 2 * T ≤ ‖z‖ ^ 2 / 2 at he
    nlinarith [norm_nonneg z, sq_nonneg ‖z‖]
  have hbound (B : ℝ) (hB : 0 < B) (hBC : B ≤ Cd + Cw)
      (ν : EndpointIndex d)
      (he : ‖indexedEndpoint hd Q ν ζ P Pdag β a μ T.toNNReal -
        homogeneousAverage Q ⟨0, by omega⟩ (T - τ) ht ((endpointDriftSign ν : ℂ) * ζ)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ τ.toNNReal)‖ ≤
        B * Real.exp (B * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - gain)) :
      ‖indexedEndpoint hd Q ν ζ P Pdag β a μ T.toNNReal -
        homogeneousAverage Q ⟨0, by omega⟩ (T - τ) ht ((endpointDriftSign ν : ℂ) * ζ)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ τ.toNNReal)‖ ≤
        (Cd + Cw) * Real.exp ((Cd + Cw) * (1 + ‖z‖) ^ 2) *
          T ^ (-(1 / 2 + (d : ℝ) / 4) - gain) := by
    apply he.trans
    calc
      _ ≤ B * Real.exp (B * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4) - gain) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hB.le
        apply Real.exp_le_exp.mpr
        simpa only [mul_assoc] using! mul_le_mul_of_nonneg_left hscale hB.le
      _ ≤ _ := LateUnsmoothing.error_constant_le hB.le hBC (sq_nonneg _) (by positivity)
  rcases hz with hz | ⟨x, rfl, hx⟩
  · intro ν
    apply hbound Cd hCd (by linarith) ν
    exact hdisc Q hQ β a μ hβ ha hμ T hT
      ((le_max_left _ _).trans (hR.trans hRT)) ζ
      ((unforced_identification_force_sqrt_scale R hRpos z).trans hz) P Pdag hP hPdag ν
  · let lam := x / R
    have hζ : (lam : ℂ) = ζ := by simp only [lam, ζ, Complex.ofReal_div]
    have hforce : |lam| * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ) := by
      have hs := unforced_identification_force_sqrt_scale R hRpos (x : ℂ)
      have hl : Real.log R ^ (1 / 4 : ℝ) ≤ Real.log T ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith))
          (Real.log_le_log hRpos hRT) (by norm_num)
      have hs' : |lam| * Real.sqrt T ≤ |x| := by
        simp only [Complex.norm_real, Real.norm_eq_abs] at hs
        change ‖ζ‖ * Real.sqrt T ≤ |x| at hs
        simpa only [← hζ, Complex.norm_real, Real.norm_eq_abs] using! hs
      exact hs'.trans (hx.trans (mul_le_mul_of_nonneg_left hl hC₀.le))
    intro ν
    apply hbound Cw hCw (by linarith) ν
    have he := hw Q hQ β a μ hβ ha hμ T hT
      ((le_max_right _ _).trans (hR.trans hRT)) lam hforce P Pdag
      (hζ.symm ▸ hP) hPdag ν
    have hnorm : lam ^ 2 = ‖ζ‖ ^ 2 := by
      rw [← hζ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simpa only [hζ, hnorm] using! he


end EinsteinFull.Blueprint.UnforcedIdentification

namespace EinsteinFull.Blueprint
open EinsteinRelation UnforcedIdentification

/-- The literal unforced-identification reduction, with exactly the four
prescribed graph dependencies and their original order. -/
theorem node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identification_of_deps
    (hforce : node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacementStmt)
    (hxi : node_l_u3A_finite_u2D_xiStmt)
    (hlate : node_l_u3A_late_u2D_propagationStmt)
    (hclt : node_e_u3A_test_u2D_cltStmt) :
    node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identificationStmt := by
  intro d hd D
  obtain ⟨ε, Cx, Rx, hε, hCx, hRx, hx⟩ := finiteTimeCommutator_normalized_flux_bounds hxi d hd D
  obtain ⟨Cm, Rm, hCm, hRm, hm⟩ := unforced_flux_model_mesoscopic_time_replacement hclt d hd D
  obtain ⟨gl, hgl, hl⟩ := latePropagation_radius_bound hlate d hd D
  obtain ⟨_M, hf⟩ := hforce d hd D
  let gain := min gl (min (1 / 16) (min (3 * ε / 4) (1 / 4)))
  have hg : 0 < gain := by dsimp [gain]; positivity
  have hgl' : gain ≤ gl := min_le_left _ _
  have hgf : gain ≤ 1 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hgx : gain ≤ 3 * ε / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hgm : gain ≤ 1 / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, gain, hε, hg, ?_⟩
  intro C₀ hC₀
  obtain ⟨Cf, Rf, hCf, hRf, hf⟩ := hf C₀ hC₀
  obtain ⟨Cl, Rl, hCl, hRl, hl⟩ := hl C₀ hC₀
  let S := Cx + Cm + Cf + Cl
  have hS : 0 < S := by dsimp [S]; positivity
  have hxS : Cx ≤ S := by dsimp [S]; linarith
  have hmS : Cm ≤ S := by dsimp [S]; linarith
  have hfS : Cf ≤ S := by dsimp [S]; linarith
  have hlS : Cl ≤ S := by dsimp [S]; linarith
  have hSC : S ≤ 5 * S := by linarith
  refine ⟨5 * S, Rx + Rm + Rf + Rl, by positivity, by linarith, ?_⟩
  intro Q hQ β a μ hβ ha hμ Z hZ R hRpos hR z hz
  have hRxR : Rx ≤ R := by linarith
  have hRmR : Rm ≤ R := by linarith
  have hRfR : Rf ≤ R := by linarith
  have hRlR : Rl ≤ R := by linarith
  dsimp only
  intro P Pdag hP hPdag
  let T := R ^ 2 / 2
  let τ := T ^ (1 - (1 / 4 : ℝ))
  let ζ := z / (R : ℂ)
  have hRfour : 4 ≤ R := hRm.trans hRmR
  have hT : 1 ≤ T := by dsimp [T]; nlinarith
  have hTpos : 0 < T := by linarith
  obtain ⟨G, F, hGF, ht, _hsmall, hfr⟩ :=
    hf Q hQ β a μ hβ ha hμ R hRpos hRfR z hz P Pdag hP hPdag
  obtain ⟨H, X, hHX, hxc⟩ := hx Q hQ β Z hβ hZ (P 0) (hP 0)
  obtain ⟨_ht', hxc⟩ := hxc R hRxR z
  obtain ⟨_hτ, _hτsmall, hmt⟩ := hm Q hQ Z hZ R hRpos hRmR
  obtain ⟨_htl, hlt⟩ := hl Q hQ β a μ hβ ha hμ R hRpos hRlR z hz
    (P ζ) (Pdag ζ) (hP ζ) (hPdag ζ)
  refine ⟨G, F, hGF, ht, hTpos, H, X, hHX, ?_, ?_, ?_⟩
  · intro i j
    exact centered_finiteTimeFlux_zero hd Q (P 0) (Pdag 0) (hP 0)
      β hβ a ha μ (G 0) (F 0) (hGF 0) τ.toNNReal i (H τ.toNNReal i) (X τ.toNNReal i)
      (hHX τ.toNNReal i) j
  · intro j
    exact finiteTimeFlux_transpose_zero hd Q (P 0) (Pdag 0) (hP 0) (hPdag 0)
      β hβ a μ (G 0) (F 0) (hGF 0) τ.toNNReal j
  · intro ν
    let i : Fin d := ν.elim id (fun _ => ⟨0, by omega⟩)
    let Xi := fun j => Z (.inl (j, i))
    let E := homogeneousFluxCLM Q ⟨0, by omega⟩ (T - τ) ht ζ ν
    let model := ν.elim (fun k => modelVelocityEndpoint hd Q Z k T hTpos ζ)
      (fun _ => modelTransposeEndpoint hd Q Z T hTpos ζ)
    have hmono (A : ℝ) (hA : 0 < A) (hAS : A ≤ S) (q : ℝ) (hq : 0 ≤ q) :
        A * Real.exp (A * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4)) * q ≤
          (5 * S) * Real.exp ((5 * S) * (1 + ‖z‖) ^ 2) *
            T ^ (-(1 / 2 + (d : ℝ) / 4)) * q :=
      mul_le_mul_of_nonneg_right (LateUnsmoothing.error_constant_le hA.le
        (hAS.trans hSC) (sq_nonneg _) (by positivity)) hq
    obtain ⟨h1, h2⟩ := hxc ν
    have h3 := hmt z ν
    dsimp only at h1 h2 h3
    simp only [← homogeneousFluxCLM_apply] at h1 h2 h3 ⊢
    change ‖E (fun j => centeredComplexLp Q (X τ.toNNReal i j) - Xi j)‖ ≤ _ at h1
    change ‖E (fun j => ∑ k, (homogenizedCoefficient Q j k : ℂ) • H τ.toNNReal i k)‖ ≤ _ at h2
    change ‖E Xi - model‖ ≤ _ at h3
    refine ⟨h1.trans (hmono Cx hCx hxS _ (by positivity)),
      h2.trans (hmono Cx hCx hxS _ (by positivity)),
      h3.trans (hmono Cm hCm hmS _ (by positivity)), ?_⟩
    have hpowx : T ^ (-(1 / 2 + (d : ℝ) / 4)) * τ ^ (-ε) =
        T ^ (-(1 / 2 + (d : ℝ) / 4) - 3 * ε / 4) := by
      dsimp [τ]
      rw [← Real.rpow_mul hTpos.le, ← Real.rpow_add hTpos]
      congr 1
      ring
    have hpowt : T ^ (-(1 / 2 + (d : ℝ) / 4)) * (τ / T) =
        T ^ (-(1 / 2 + (d : ℝ) / 4) - 1 / 4) := by
      have he : τ / T = T ^ (-(1 / 4 : ℝ)) := by
        calc
          _ = T ^ ((1 - (1 / 4 : ℝ)) - 1) := by rw [Real.rpow_sub hTpos, Real.rpow_one]
          _ = _ := by congr 1; ring
      rw [he, ← Real.rpow_add hTpos]
      congr 1
    have habs (A e : ℝ) (hA : 0 < A) (hAS : A ≤ S) (he : gain ≤ e) :
        A * Real.exp (A * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4) - e) ≤
          S * Real.exp (S * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4) - gain) := by
      exact (LateUnsmoothing.error_constant_le hA.le hAS (sq_nonneg _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT (by linarith))
          (by positivity))
    let B := S * Real.exp (S * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4) - gain)
    have h1' : ‖E (fun j => centeredComplexLp Q (X τ.toNNReal i j) - Xi j)‖ ≤ B := by
      apply h1.trans
      rw [mul_assoc, mul_assoc, hpowx]
      simpa only [B, mul_assoc] using! habs Cx (3 * ε / 4) hCx hxS hgx
    have h2' : ‖E (fun j => ∑ k, (homogenizedCoefficient Q j k : ℂ) • H τ.toNNReal i k)‖ ≤ B := by
      apply h2.trans
      rw [mul_assoc, mul_assoc, hpowt]
      simpa only [B, mul_assoc] using! habs Cx (1 / 4) hCx hxS hgm
    have h3' : ‖E Xi - model‖ ≤ B := by
      apply h3.trans
      rw [mul_assoc, mul_assoc, hpowt]
      simpa only [B, mul_assoc] using! habs Cm (1 / 4) hCm hmS hgm
    have hfr' := (hfr ν).2
    dsimp only at hfr'
    simp only [← homogeneousFluxCLM_apply] at hfr'
    change ‖E (fun j => centeredComplexLp Q (F ζ τ.toNNReal ν j - F 0 τ.toNNReal ν j))‖ ≤ _ at hfr'
    have h4' : ‖E (fun j => centeredComplexLp Q (F ζ τ.toNNReal ν j - F 0 τ.toNNReal ν j))‖ ≤ B :=
      hfr'.trans (habs Cf (1 / 16) hCf hfS hgf)
    let U := indexedEndpoint hd Q (ν.elim Sum.inl (fun _ => Sum.inr true)) ζ
      (P ζ) (Pdag ζ) β a μ T.toNNReal
    let V := homogeneousAverage Q ⟨0, by omega⟩ (T - τ) ht
      (ν.elim (fun _ => ζ) (fun _ => -ζ))
      (indexedEndpoint hd Q (ν.elim Sum.inl (fun _ => Sum.inr true)) ζ
        (P ζ) (Pdag ζ) β a μ τ.toNNReal)
    have hsign : (endpointDriftSign (ν.elim Sum.inl (fun _ => Sum.inr true)) : ℂ) * ζ =
        ν.elim (fun _ => ζ) (fun _ => -ζ) := by
      cases ν <;> simp [endpointDriftSign]
    have hlν := hlt (ν.elim Sum.inl (fun _ => Sum.inr true))
    rw [hsign] at hlν
    have h5' : ‖U - V‖ ≤ B := hlν.trans (habs Cl gl hCl hlS hgl')
    have hdecomp := finiteTimeFlux_homogeneous_decomposition hd Q P Pdag hP hPdag
      β hβ a ha μ G F hGF ζ τ.toNNReal (T - τ) ht ν
      (H τ.toNNReal i) (X τ.toNNReal i) (hHX τ.toNNReal i) Xi
    change V = E _ + E _ + E _ + E Xi at hdecomp
    have htel : U - model = (U - V) +
        E (fun j => centeredComplexLp Q (F ζ τ.toNNReal ν j - F 0 τ.toNNReal ν j)) +
        E (fun j => centeredComplexLp Q (X τ.toNNReal i j) - Xi j) +
        E (fun j => ∑ k, (homogenizedCoefficient Q j k : ℂ) • H τ.toNNReal i k) +
        (E Xi - model) := by rw [hdecomp]; abel
    change ‖U - model‖ ≤ _
    rw [htel]
    calc
      _ ≤ ‖U - V‖ +
          ‖E (fun j => centeredComplexLp Q (F ζ τ.toNNReal ν j - F 0 τ.toNNReal ν j))‖ +
          ‖E (fun j => centeredComplexLp Q (X τ.toNNReal i j) - Xi j)‖ +
          ‖E (fun j => ∑ k, (homogenizedCoefficient Q j k : ℂ) • H τ.toNNReal i k)‖ +
          ‖E Xi - model‖ := by grw [norm_add_le, norm_add_le, norm_add_le, norm_add_le]
      _ ≤ B + B + B + B + B := by gcongr
      _ ≤ _ := by
        dsimp [B]
        calc
          _ = 5 * S * Real.exp (S * (1 + ‖z‖) ^ 2) *
              T ^ (-(1 / 2 + (d : ℝ) / 4) - gain) := by ring
          _ ≤ _ := by gcongr

end EinsteinFull.Blueprint
