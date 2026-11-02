import EinsteinFull.Calculus.CLTwoSidedAnnealedCovariance
import EinsteinFull.Calculus.CLLaplacePairing
import EinsteinFull.Calculus.CLUnforcedReversibility
import EinsteinFull.Work.W2.MassiveCorrectorGradientSupport
import EinsteinFull.Work.W2.ActualMassiveCorrectorSpatialEllipticRealizationProof
import EinsteinFull.Work.W2.CorrectorReuseSupport

/-!
# The DFGW diffusion matrix is the homogenized coefficient

DFGW's matrix `D = C - 2 ∫₀^∞ E[φ ⊗ P_t φ] dt` for the two-sided environment process equals the
homogenized coefficient. The velocity correlation `E[φ_i P_t φ_j]` is the pairing of the reduced
drift observables under the unforced environment semigroup, so its Laplace transform at mass `s`
is `∫ β_i R_s β_j`; integrating by parts this is `-½ E[(a e_i) · ∇R_s β_j]`, and the massive
gradients converge to the corrector gradient. Hence `∫₀^∞ E[φ_i P_t φ_j] dt = -½ E[(a e_i) · ∇χ_j]`,
while `e · C e = E[e · a(0) e]`; together `e · D e` is `e · ā e`, and both matrices are symmetric.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation EinsteinRelation.Correctors

variable {d : ℕ}

/-- Symmetric matrices with the same quadratic form are equal. -/
theorem matrix_eq_of_quadratic_eq {A B : Mat d} (hA : A.transpose = A) (hB : B.transpose = B)
    (h : ∀ e : Vec d, dot e (A.mulVec e) = dot e (B.mulVec e)) : A = B := by
  have hq : ∀ (M : Mat d) (u v : Vec d), dot (u + v) (M.mulVec (u + v)) =
      dot u (M.mulVec u) + dot u (M.mulVec v) + dot v (M.mulVec u) + dot v (M.mulVec v) := by
    intro M u v
    simp only [dot, Matrix.mulVec_add, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  have hs : ∀ (M : Mat d), M.transpose = M → ∀ u v : Vec d,
      dot v (M.mulVec u) = dot u (M.mulVec v) := by
    intro M hM u v
    have hMe : ∀ a b, M a b = M b a := fun a b => by
      rw [← Matrix.transpose_apply M b a, hM]
    simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hMe]
    ring
  have he : ∀ (M : Mat d) (i j : Fin d), dot (unitVector i) (M.mulVec (unitVector j)) = M i j := by
    intro M i j
    simp [dot, Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
  ext i j
  have h1 := h (unitVector i + unitVector j)
  have h2 := h (unitVector i)
  have h3 := h (unitVector j)
  rw [hq, hq, hs A hA (unitVector i) (unitVector j), hs B hB (unitVector i) (unitVector j)] at h1
  simp only [he] at h1 h2 h3
  linarith

/-- The reduced drift observable `½ Σ_k ∂_k a_{kj}(0)` of a reduced environment. -/
def reducedDriftFn (j : Fin d) (ρ : FieldPair d) : ℝ :=
  (1 / 2 : ℝ) * ∑ k, coordinateDerivative k (fun x => ρ.1 x k j) 0

theorem measurable_reducedDriftFn (j : Fin d) : Measurable (reducedDriftFn (d := d) j) := by
  unfold reducedDriftFn coordinateDerivative
  refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => ?_) _
  have hc : Continuous fun p : FieldPair d × Vec d => p.1.1 p.2 k j :=
    (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).matrix_elem
      k j
  have h := measurable_fderiv_apply_const_with_param ℝ
    (f := fun (ρ : FieldPair d) (z : Vec d) => ρ.1 z k j) hc (unitVector k)
  exact h.comp (measurable_id.prodMk measurable_const)

theorem reducedDriftFn_reduce (hd : 2 ≤ d) (ω : FieldPair d) (j : Fin d) :
    reducedDriftFn j (reduce ω) = envDrift hd ω j := by
  simp only [reducedDriftFn, envDrift, forcedDrift, matrixDivDrift, zero_mul, add_zero]
  rfl

/-- The pairing with the reduced coefficient column `a e_i` as an inner product. -/
theorem inner_coefficientColumn {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    inner ℝ (reducedOriginCoefficientAction Q (correctorAffineField Q i)) G =
      ∫ ρ, ∑ k, ρ.1 0 k i * G ρ k ∂reducedEnvironmentLaw Q := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reducedOriginCoefficientAction_coeFn Q (correctorAffineField Q i),
    Lp.coeFn_const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i)] with ρ hA hc
  have hc' : (correctorAffineField Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
      (reducedEnvironmentLaw Q)) ρ = correctorUnitVector i := hc
  rw [hc'] at hA
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := congrFun hA k
  simp only [RCLike.inner_apply, conj_trivial, hk]
  simp [Matrix.mulVec, dotProduct, correctorUnitVector, mul_comm]

theorem dot_add_vec (e u v : Vec d) : dot e (u + v) = dot e u + dot e v := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Integration by parts of the drift against the massive resolvent, in terms of the real massive
gradient. -/
theorem resolvent_pairing_re_eq {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i₀ i j : Fin d) (s : ℝ) (hs : 0 < s) :
    (∫ ρ, β i ρ * unforcedComplexResolvent Q i₀ s hs (β j) ρ ∂reducedLaw Q).re =
      -(1 / 2) * ∫ ρ, ∑ k, ρ.1 0 k i *
        unforcedComplexResolventRealGradient Q i₀ s hs (β j) Complex.reCLM ρ k ∂reducedLaw Q := by
  rw [hβ.integral_mul i _ _ (hasComplexHorizontalGradient_unforcedComplexResolvent Q i₀ s hs (β j))]
  set G := unforcedComplexResolventRealGradient Q i₀ s hs (β j) Complex.reCLM with hG
  have hV : ∀ᵐ ρ ∂reducedLaw Q, ∀ k,
      unforcedComplexResolventGradient Q i₀ s hs (β j) k ρ = (G ρ k : ℂ) := by
    have h1 := unforcedComplexResolventEuclideanGradient_ae Q i₀ s hs (β j)
    have h2 := (euclideanComplexify d).coeFn_compLpL (p := 2) (μ := reducedLaw Q) G
    rw [hβ.resolvent_gradient_eq_complexify i₀ j s hs] at h1
    filter_upwards [h1, h2] with ρ h1 h2 k
    rw [← h1 k, h2]
    rfl
  have e : ∫ ρ, ∑ k, (ρ.1 0 k i : ℂ) * unforcedComplexResolventGradient Q i₀ s hs (β j) k ρ
      ∂reducedLaw Q = ((∫ ρ, ∑ k, ρ.1 0 k i * G ρ k ∂reducedLaw Q : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hV] with ρ hρ
    simp only [hρ]
    push_cast
    rfl
  rw [e]
  simp [Complex.mul_re]

/-- The pairings of the real massive gradients with a coefficient column converge to those of
the corrector gradient. -/
theorem tendsto_column_pairing {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i₀ i j : Fin d) (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (ht : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ρ, ∑ k, ρ.1 0 k i *
        unforcedComplexResolventRealGradient Q i₀ (s n) (hs n) (β j) Complex.reCLM ρ k
          ∂reducedLaw Q) atTop
      (𝓝 (∫ ρ, ∑ k, ρ.1 0 k i * correctorGradient Q j ρ k ∂reducedLaw Q)) := by
  let A : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) :=
    reducedOriginCoefficientAction Q (correctorAffineField Q i)
  have e : ∀ G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q),
      inner ℝ A G = ∫ ρ, ∑ k, ρ.1 0 k i * G ρ k ∂reducedLaw Q := fun G =>
    inner_coefficientColumn Q i G
  have h := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := A))
    (hβ.tendsto_real_resolvent_gradient i₀ j s hs ht)
  simp only [e] at h
  exact h

section Identification

variable (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
  (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
  (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d)
  {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
    SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))

include hQ hunforced hpath hK in
/-- The DFGW velocity correlation is the semigroup pairing of the reduced drift observables. -/
theorem envDrift_correlation_eq_pairing
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hrealize : ∀ Y : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0 (Y (0, ω))) →
      ∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)), ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
        P t f (reduce ω) = ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω))
    (i j : Fin d) (t : ℝ≥0) :
    ∫ x, envDrift hd x i * ∫ y, envDrift hd y j ∂envKernel K t x ∂Q.measure =
      (∫ ρ, canonicalReducedDrift Q i ρ * P t (canonicalReducedDrift Q j) ρ
        ∂reducedLaw Q).re := by
  have hβ := isReducedDriftObservation_canonicalReducedDrift Q hQ
  have hmj : Measurable fun y : FieldPair d => envDrift hd y j :=
    (measurable_pi_apply j).comp (measurable_envDrift hd)
  have e1 : ∀ x, ∫ y, envDrift hd y j ∂envKernel K t x = kernelObsMean K (reducedDriftFn j) t x :=
    fun x => by
      rw [integral_envKernel K t hmj x,
        kernelPhysMean_eq K (fun ω => reducedDriftFn_reduce hd ω j) t x]
  have e2 : ∀ x, envDrift hd x i = reducedDriftFn i (reduce x) := fun x =>
    (reducedDriftFn_reduce hd x i).symm
  simp_rw [e1, e2]
  exact integral_obs_mul_kernelObsMean hd D Q hQ hunforced hpath hK (measurable_reducedDriftFn i)
    P hrealize _ _ (hβ i) (hβ j) t

include hQ hunforced hpath hK in
/-- The Laplace transform of the DFGW velocity correlation is the resolvent pairing. -/
theorem laplace_envDrift_correlation
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) 0 P)
    (hrealize : ∀ Y : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0 (Y (0, ω))) →
      ∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)), ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
        P t f (reduce ω) = ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω))
    (i j : Fin d) (s : ℝ) (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) *
        ∫ x, envDrift hd x i * ∫ y, envDrift hd y j ∂envKernel K t.toNNReal x ∂Q.measure =
      (∫ ρ, canonicalReducedDrift Q i ρ * unforcedComplexResolvent Q ⟨0, by omega⟩ s hs
        (canonicalReducedDrift Q j) ρ ∂reducedLaw Q).re := by
  obtain ⟨hint, heq⟩ := cl_laplace_pairing_eq_resolvent hP s hs (canonicalReducedDrift Q i)
    (canonicalReducedDrift Q j)
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← heq, ← hre]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [Complex.re_ofReal_mul]
  rw [envDrift_correlation_eq_pairing hd D Q hQ hunforced hpath hK P hrealize i j]

include hQ hunforced hpath hK in
/-- The time integral of the DFGW velocity correlation is `-½ E[(a e_i) · ∇χ_j]`. -/
theorem dfgw_correlation_integral_eq (i j : Fin d)
    (hint : IntegrableOn (fun t : ℝ => ∫ x, envDrift hd x i *
      ∫ y, envDrift hd y j ∂envKernel K t.toNNReal x ∂Q.measure) (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), ∫ x, envDrift hd x i *
        ∫ y, envDrift hd y j ∂envKernel K t.toNNReal x ∂Q.measure =
      -(1 / 2) * ∫ ρ, ∑ k, ρ.1 0 k i * correctorGradient Q j ρ k ∂reducedLaw Q := by
  obtain ⟨P, hP, -, -, -, -, hrealize⟩ := id hunforced
  have hβ := isReducedDriftObservation_canonicalReducedDrift Q hQ
  let s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hs : ∀ n, 0 < s n := fun n => by positivity
  have hs0 : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 := cl_laplace_tendsto_Ioi hint s hs hs0
  have h2 := (tendsto_column_pairing hβ ⟨0, by omega⟩ i j s hs hs0).const_mul (-(1 / 2 : ℝ))
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [laplace_envDrift_correlation hd D Q hQ hunforced hpath hK P hP hrealize i j (s n) (hs n),
    resolvent_pairing_re_eq hβ]

include hQ hunforced hpath hap hK in
/-- DFGW's diffusion matrix for the two-sided environment process is the homogenized
coefficient. -/
theorem dfgw_matrix_eq_homogenizedCoefficient {C Dm : Mat d}
    (hC : ∀ e : Vec d, dot e (C.mulVec e) =
      ∫ ω, dot e (tsDisp 0 1 ω - ∫ τ in (0 : ℝ)..1, envDrift hd (tsState τ ω)) ^ 2 ∂tsLaw Q K)
    (hD : ∀ i j : Fin d,
      IntegrableOn (fun t : ℝ => ∫ x, envDrift hd x i *
        ∫ y, envDrift hd y j ∂envKernel K t.toNNReal x ∂Q.measure) (Set.Ioi 0) ∧
      Dm i j = C i j - 2 * ∫ t in Set.Ioi (0 : ℝ),
        ∫ x, envDrift hd x i * ∫ y, envDrift hd y j ∂envKernel K t.toNNReal x ∂Q.measure)
    (hsym : Dm.transpose = Dm) :
    Dm = homogenizedCoefficient Q := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  have : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let J : Mat d := fun i j => ∫ ρ, ∑ k, ρ.1 0 k i * correctorGradient Q j ρ k ∂reducedLaw Q
  let A : Mat d := fun i j => ∫ ρ, ρ.1 0 i j ∂reducedLaw Q
  have hDm : Dm = C + J := by
    ext i j
    rw [(hD i j).2, dfgw_correlation_integral_eq hd D Q hQ hunforced hpath hK i j (hD i j).1,
      Matrix.add_apply]
    simp only [J]
    ring
  obtain ⟨B, -, hB⟩ := DriftH5.exists_ae_abs_entry_le d D.ellipticity D.dependenceRange
  have hBQ : ∀ᵐ ρ ∂reducedLaw Q, ∀ j k : Fin d, |ρ.1 0 j k| ≤ B := hB Q
  have hell : ∀ᵐ ρ ∂reducedLaw Q,
      IsElliptic (Real.exp (2 * D.ellipticity) * D.ellipticity) (fun _ => ρ.1 0) :=
    ae_reducedEnvironmentLaw_origin_elliptic Q
  have hsymm : ∀ᵐ ρ ∂reducedLaw Q, ∀ k l : Fin d, ρ.1 0 k l = ρ.1 0 l k := by
    filter_upwards [hell] with ρ hρ k l
    have h := congrFun (congrFun (hρ 0).1 l) k
    rw [Matrix.transpose_apply] at h
    exact h
  have hmeas : ∀ k l : Fin d, Measurable fun ρ : FieldPair d => ρ.1 0 k l := fun k l =>
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem
      k l).measurable
  have hAint : ∀ k l : Fin d, Integrable (fun ρ : FieldPair d => ρ.1 0 k l) (reducedLaw Q) :=
    fun k l => Integrable.of_bound (hmeas k l).aestronglyMeasurable B
      (hBQ.mono fun ρ h => by rw [Real.norm_eq_abs]; exact h k l)
  have hJint : ∀ i j k : Fin d,
      Integrable (fun ρ => ρ.1 0 k i * correctorGradient Q j ρ k) (reducedLaw Q) :=
    fun i j k => (integrable_correctorGradient_coordinate Q j k).bdd_mul (c := B)
      (hmeas k i).aestronglyMeasurable
      (hBQ.mono fun ρ h => by rw [Real.norm_eq_abs]; exact h k i)
  have hhom : homogenizedCoefficient Q = A + J := by
    ext i j
    rw [homogenizedCoefficient_eq_integral_flux Q i j, Matrix.add_apply]
    simp only [A, J]
    rw [← integral_add (hAint i j) (integrable_finsetSum _ fun k _ => hJint i j k)]
    refine integral_congr_ae ?_
    filter_upwards [hsymm] with ρ hρ
    have hδ : ∑ k, ρ.1 0 i k * unitVector j k = ρ.1 0 i j := by
      simp [unitVector, Pi.single_apply]
    have hsplit : ∑ k, ρ.1 0 i k * (unitVector j k + correctorGradient Q j ρ k) =
        ∑ k, ρ.1 0 i k * unitVector j k + ∑ k, ρ.1 0 i k * correctorGradient Q j ρ k := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => mul_add _ _ _
    rw [hsplit, hδ]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [hρ i k]
  have hexp : ∀ (e : Vec d) (M : Mat d), dot e (M.mulVec e) = ∑ i, ∑ j, e i * e j * M i j := by
    intro e M
    simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hCA : ∀ e : Vec d, dot e (C.mulVec e) = dot e (A.mulVec e) := by
    intro e
    have h := integral_sq_dot_tsComp hd D Q hQ hunforced hpath hap hK e 1
    simp only [NNReal.coe_one, one_mul] at h
    have hm : Measurable fun ρ : FieldPair d => dot e ((ρ.1 0).mulVec e) := by
      simp only [dot, Matrix.mulVec, dotProduct]
      exact Finset.measurable_sum _ fun i _ => measurable_const.mul
        (Finset.measurable_sum _ fun j _ => (hmeas i j).mul measurable_const)
    have hmap : ∫ ρ, dot e ((ρ.1 0).mulVec e) ∂reducedLaw Q =
        ∫ x, dot e ((reducedCoefficient x 0).mulVec e) ∂Q.measure :=
      integral_map Probability.measurable_reduce.aemeasurable hm.aestronglyMeasurable
    rw [hC e]
    refine h.trans (hmap.symm.trans ?_)
    simp_rw [hexp]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hAint i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hAint i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  refine matrix_eq_of_quadratic_eq hsym (homogenizedCoefficient_transpose Q) fun e => ?_
  rw [hDm, hhom, Matrix.add_mulVec, Matrix.add_mulVec, dot_add_vec, dot_add_vec, hCA]

end Identification

end EinsteinFull.Blueprint
