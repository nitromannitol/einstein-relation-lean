import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelation.Correctors.EllipticOperatorBound
import EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinRelation.Probability.ReductionLocality
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # Bounds on the homogenized matrix and on the mean clock density

Source: `paper/main.tex:698` (the expected corrector flux) and `paper/main.tex:1194-1199`
(the proof of Theorem 1.2, which uses `Λ⁻¹ ≤ η(λ)`, `E μ ∈ [Λ⁻¹, Λ]` and `|ā e₁| ≤ Λ`).

Let `Λ = sourceReducedBound Λ₀`, and let `ā` be the matrix whose `i`-th column is
`expectedCorrectorFlux Q i`. This module proves the quadratic bounds
`Λ⁻¹ |ξ|² ≤ ξ·ā ξ ≤ Λ |ξ|²`, the symmetry `ā = āᵀ`, the column bound `|ā e_i| ≤ Λ`, and the
bounds `Λ⁻¹ ≤ E μ ≤ Λ` for the clock density at the origin.

The identity `ξ·ā ξ = ⟪X, a X⟫` with `X = Σ_j ξ_j (e_j + ∇φ_j)` follows from the variational
equation of the canonical corrector gradient. The upper bound compares the energy of `X` with the
energy of its constant part. The lower bound applies pointwise ellipticity of `a(0)` to `X`,
whose mean is `ξ` because potential gradients have mean zero.
-/

open MeasureTheory
open EinsteinRelation.Correctors

namespace EinsteinRelation

noncomputable section

/-! ### Euclidean and scalar helpers -/

private theorem homog_inner_eq_dot {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) :
    inner ℝ u v = dot u.ofLp v.ofLp := by
  simp [dot, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

private theorem homog_inner_toLp_self {d : ℕ} (ξ : Vec d) :
    inner ℝ (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 ξ) =
      euclideanSq ξ := by
  rw [homog_inner_eq_dot, WithLp.ofLp_toLp]
  rfl

private theorem homog_inner_unitVector {d : ℕ} (j : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (correctorUnitVector j) x = x j := by
  rw [homog_inner_eq_dot]
  simp [correctorUnitVector, dot, Pi.single_apply, ite_mul]

private theorem homog_euclideanSq_nonneg {d : ℕ} (ξ : Vec d) : 0 ≤ euclideanSq ξ := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (ξ i)

private theorem homog_euclideanNorm_unitVector {d : ℕ} (i : Fin d) :
    euclideanNorm (unitVector i) = 1 := by
  simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]

private theorem homog_one_le_sourceReducedBound {L : ℝ} (hL : 1 ≤ L) :
    1 ≤ sourceReducedBound L := by
  unfold sourceReducedBound
  have he : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
  have hp : 1 ≤ 3 * L ^ 2 + L + 1 := by nlinarith [sq_nonneg L]
  nlinarith [mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hp)]

private theorem homog_exp_mul_le_sourceReducedBound {L : ℝ} :
    Real.exp (2 * L) * L ≤ sourceReducedBound L := by
  unfold sourceReducedBound
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg L]) (Real.exp_pos _).le

/-! ### Integrals of constant and potential-gradient fields -/

private theorem homog_inner_const_eq_integral {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : EuclideanSpace ℝ (Fin d))
    (F : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) :
    inner ℝ (Lp.const 2 μ w) F = inner ℝ w (∫ ω, F ω ∂μ) := by
  have hF : Integrable (⇑F) μ := (Lp.memLp F).integrable (by norm_num)
  rw [L2.inner_def, ← integral_inner (𝕜 := ℝ) hF w]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ w] with ω hω
  simp only [hω, Function.const_apply]

private theorem homog_integral_const {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : EuclideanSpace ℝ (Fin d)) :
    ∫ ω, (Lp.const 2 μ w) ω ∂μ = w := by
  rw [integral_congr_ae (Lp.coeFn_const 2 μ w)]
  simp

private theorem homog_constLp_smul {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    Lp.const 2 μ (c • w) = c • Lp.const 2 μ w := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_const 2 μ (c • w), Lp.coeFn_smul c (Lp.const 2 μ w),
    Lp.coeFn_const 2 μ w] with ω h1 h2 h3
  simp only [h1, h2, Pi.smul_apply, h3, Function.const_apply]

private theorem homog_sum_smul_correctorUnitVector {d : ℕ} (ξ : Vec d) :
    ∑ i, ξ i • correctorUnitVector i = (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) := by
  ext k
  simp [correctorUnitVector, Pi.single_apply, mul_ite]

/-- Potential gradients have zero mean in every coordinate, hence zero vector mean. -/
private theorem homog_integral_eq_zero_of_mem {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (hG : G ∈ correctorPotentialDomain Q) :
    ∫ ω, G ω ∂(reducedEnvironmentLaw Q) = 0 := by
  ext j
  have hint : ∀ k : Fin d, Integrable (fun ω => G ω k) (reducedEnvironmentLaw Q) :=
    fun k => ((Lp.memLp G).eval_piLp k).integrable (by norm_num)
  have hmean : ∫ ω, ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j).compLpL 2
      (reducedEnvironmentLaw Q) G) ω ∂(reducedEnvironmentLaw Q) = 0 := by
    have h := correctorPotentialDomain_mean_zero Q G hG j
    rw [euclideanCoordinateMean, ContinuousLinearMap.comp_apply, l2Expectation_apply] at h
    exact h
  rw [PiLp.zero_apply, eval_integral_piLp hint j]
  refine Eq.trans (integral_congr_ae ?_) hmean
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j) G (p := 2)
    (μ := reducedEnvironmentLaw Q)] with ω hω
  simpa only [PiLp.proj_apply] using hω.symm

/-- The mean of `e + H` for a potential gradient `H` is the constant `e`. -/
private theorem homog_integral_const_add {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ξ : Vec d) (H : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (hH : H ∈ correctorPotentialDomain Q) :
    ∫ ω, (Lp.const 2 (reducedEnvironmentLaw Q) (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) + H) ω
        ∂(reducedEnvironmentLaw Q) =
      (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) := by
  have hU : Integrable (⇑(Lp.const 2 (reducedEnvironmentLaw Q)
      (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)))) (reducedEnvironmentLaw Q) :=
    (Lp.memLp (Lp.const 2 (reducedEnvironmentLaw Q)
      (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)))).integrable (by norm_num)
  have hHi : Integrable (⇑H) (reducedEnvironmentLaw Q) :=
    (Lp.memLp H).integrable (by norm_num)
  have hsplit : ∫ ω, (Lp.const 2 (reducedEnvironmentLaw Q)
        (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) + H) ω ∂(reducedEnvironmentLaw Q) =
      ∫ ω, (Lp.const 2 (reducedEnvironmentLaw Q)
        (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d))) ω ∂(reducedEnvironmentLaw Q) +
        ∫ ω, H ω ∂(reducedEnvironmentLaw Q) := by
    rw [← integral_add hU hHi]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (Lp.const 2 (reducedEnvironmentLaw Q)
      (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d))) H] with ω hω
    simp only [hω, Pi.add_apply]
  rw [hsplit, homog_integral_const (reducedEnvironmentLaw Q),
    homog_integral_eq_zero_of_mem Q H hH, add_zero]

private theorem homog_inner_const_self {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ξ : Vec d) :
    inner ℝ (Lp.const 2 (reducedEnvironmentLaw Q) (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)))
      (Lp.const 2 (reducedEnvironmentLaw Q) (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d))) =
      euclideanSq ξ := by
  rw [homog_inner_const_eq_integral (reducedEnvironmentLaw Q),
    homog_integral_const (reducedEnvironmentLaw Q)]
  exact homog_inner_toLp_self ξ

/-! ### Pointwise form of the origin coefficient action on `L²` -/

/-- The Euclidean vector `M u` for a matrix `M` and a vector `u`. -/
private def homogPairAction {d : ℕ} (p : Mat d × EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (p.1.mulVec p.2.ofLp)

private theorem homog_continuous_origin {d : ℕ} :
    Continuous (fun ω : FieldPair d => ω.1 (0 : Vec d)) :=
  (continuous_eval_const (0 : Vec d)).comp continuous_fst

private theorem homog_continuous_pairAction {d : ℕ} :
    Continuous (homogPairAction (d := d)) := by
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℝ)).comp
    (continuous_fst.matrix_mulVec
      ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).comp continuous_snd))

private theorem homog_euclideanNorm_eq_norm {d : ℕ} (v : Vec d) :
    euclideanNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclideanNorm euclideanSq dot
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.norm_eq_abs, pow_two]
  exact (abs_mul_abs_self (v i)).symm

private theorem homog_pairAction_norm_le {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ)
    {M : Mat d} (hM : IsElliptic Λ (fun _ : Vec d => M))
    (u : EuclideanSpace ℝ (Fin d)) :
    ‖homogPairAction (M, u)‖ ≤ Λ * ‖u‖ := by
  have h := isElliptic_mulVec_euclideanNorm_le hΛ hM 0 u.ofLp
  calc
    ‖homogPairAction (M, u)‖ = euclideanNorm (M.mulVec u.ofLp) := by
      rw [homogPairAction, homog_euclideanNorm_eq_norm]
    _ ≤ Λ * euclideanNorm u.ofLp := h
    _ = Λ * ‖u‖ := by
      rw [homog_euclideanNorm_eq_norm]

private theorem homog_pairOrigin_aestronglyMeasurable {d : ℕ} {Q : Measure (FieldPair d)}
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    AEStronglyMeasurable (fun ω : FieldPair d => homogPairAction (ω.1 (0 : Vec d), u ω)) Q := by
  have hPseudo : TopologicalSpace.PseudoMetrizableSpace (Mat d) := by
    change TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ)
    exact inferInstance
  have hSecond : SecondCountableTopology (Mat d) := by
    change SecondCountableTopology (Fin d → Fin d → ℝ)
    exact inferInstance
  apply homog_continuous_pairAction.comp_aestronglyMeasurable
  exact homog_continuous_origin.measurable.aestronglyMeasurable.prodMk
    (Lp.aestronglyMeasurable u)

/-- The origin coefficient action on `L²` is multiplication by `a(0)`, pointwise almost surely. -/
private theorem homog_reducedAction_ae_pair {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    (fun ω => reducedOriginCoefficientAction Q u ω) =ᵐ[reducedEnvironmentLaw Q]
      (fun ω => homogPairAction (ω.1 (0 : Vec d), u ω)) := by
  filter_upwards [reducedOriginCoefficientAction_coeFn Q u] with ω hω
  simpa only [homogPairAction, WithLp.toLp_ofLp] using
    congrArg (WithLp.toLp 2) hω

/-- Pointwise lower bound: `c⁻¹ (2 ξ·X - |ξ|²) ≤ X·a(0) X` with `c = exp(2Λ₀) Λ₀`. -/
private theorem homog_lower_pointwise {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ξ : Vec d) (X : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    ∀ᵐ ω ∂(reducedEnvironmentLaw Q),
      2 * (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * inner ℝ (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) (X ω) -
        (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * euclideanSq ξ ≤
        inner ℝ (X ω) (reducedOriginCoefficientAction Q X ω) := by
  have hc0 : 0 < Real.exp (2 * Λ₀) * Λ₀ :=
    mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hinv : 0 ≤ (Real.exp (2 * Λ₀) * Λ₀)⁻¹ := inv_nonneg.mpr hc0.le
  filter_upwards [ae_reducedEnvironmentLaw_origin_elliptic Q,
    homog_reducedAction_ae_pair Q X] with ω hω hA
  have e1 : inner ℝ (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) (X ω) =
      dot ξ (X ω).ofLp := by
    rw [homog_inner_eq_dot, WithLp.ofLp_toLp]
  have e2 : inner ℝ (X ω) (homogPairAction (ω.1 (0 : Vec d), X ω)) =
      dot (X ω).ofLp ((ω.1 (0 : Vec d)).mulVec (X ω).ofLp) := by
    simp only [homog_inner_eq_dot, homogPairAction, WithLp.ofLp_toLp]
  have hexp : dot ((X ω).ofLp - ξ) ((X ω).ofLp - ξ) =
      euclideanSq (X ω).ofLp - 2 * dot ξ (X ω).ofLp + euclideanSq ξ := by
    change dotProduct ((X ω).ofLp - ξ) ((X ω).ofLp - ξ) =
      dotProduct (X ω).ofLp (X ω).ofLp - 2 * dotProduct ξ (X ω).ofLp + dotProduct ξ ξ
    simp only [dotProduct_sub, sub_dotProduct]
    rw [dotProduct_comm ξ (X ω).ofLp]
    ring
  have hsq : 0 ≤ dot ((X ω).ofLp - ξ) ((X ω).ofLp - ξ) := by
    unfold dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hkey : 2 * dot ξ (X ω).ofLp - euclideanSq ξ ≤ euclideanSq (X ω).ofLp := by
    linarith
  have hq := (hω 0).2 (X ω).ofLp
  rw [hA, e1, e2]
  have hlhs : 2 * (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * dot ξ (X ω).ofLp -
      (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * euclideanSq ξ =
      (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * (2 * dot ξ (X ω).ofLp - euclideanSq ξ) := by
    ring
  rw [hlhs]
  exact (mul_le_mul_of_nonneg_left hkey hinv).trans hq.1

/-- Jensen-type lower bound: a field with mean `ξ` has energy at least `c⁻¹ |ξ|²`. -/
private theorem homog_lower_bound_of_mean {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ξ : Vec d) (X : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (hmean : ∫ ω, X ω ∂(reducedEnvironmentLaw Q) =
      (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d))) :
    (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * euclideanSq ξ ≤
      inner ℝ X (reducedOriginCoefficientAction Q X) := by
  have hXi : Integrable (⇑X) (reducedEnvironmentLaw Q) :=
    (Lp.memLp X).integrable (by norm_num)
  have hint : ∫ ω, inner ℝ (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) (X ω)
      ∂(reducedEnvironmentLaw Q) = euclideanSq ξ := by
    rw [integral_inner (𝕜 := ℝ) hXi (WithLp.toLp 2 ξ), hmean]
    exact homog_inner_toLp_self ξ
  have hL : Integrable (fun ω => 2 * (Real.exp (2 * Λ₀) * Λ₀)⁻¹ *
      inner ℝ (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) (X ω) -
        (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * euclideanSq ξ) (reducedEnvironmentLaw Q) :=
    ((hXi.const_inner (𝕜 := ℝ) (WithLp.toLp 2 ξ)).const_mul (2 * (Real.exp (2 * Λ₀) * Λ₀)⁻¹)).sub
      (integrable_const ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ * euclideanSq ξ))
  have hR : Integrable (fun ω => inner ℝ (X ω) (reducedOriginCoefficientAction Q X ω))
      (reducedEnvironmentLaw Q) :=
    L2.integrable_inner (𝕜 := ℝ) X (reducedOriginCoefficientAction Q X)
  have hLint : ∫ ω, (2 * (Real.exp (2 * Λ₀) * Λ₀)⁻¹ *
      inner ℝ (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) (X ω) -
        (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * euclideanSq ξ) ∂(reducedEnvironmentLaw Q) =
      (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * euclideanSq ξ := by
    rw [integral_sub ((hXi.const_inner (𝕜 := ℝ) (WithLp.toLp 2 ξ)).const_mul
        (2 * (Real.exp (2 * Λ₀) * Λ₀)⁻¹))
      (integrable_const ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ * euclideanSq ξ)),
      integral_const_mul, hint, integral_const, probReal_univ, one_smul]
    ring
  have hmono := integral_mono_ae hL hR (homog_lower_pointwise Q ξ X)
  rw [hLint] at hmono
  rw [L2.inner_def]
  exact hmono

/-! ### Energy identities for the corrector decomposition -/

/-- If `H` is `A`-orthogonal to `U + H`, the energy of `U + H` is `E(U) - E(H)`. -/
private theorem homog_energy_decomp {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (A : F →L[ℝ] F)
    (hsymm : ∀ u v : F, inner ℝ u (A v) = inner ℝ (A u) v) (U H : F)
    (hH : inner ℝ H (A (U + H)) = 0) :
    inner ℝ (U + H) (A (U + H)) = inner ℝ U (A U) - inner ℝ H (A H) := by
  have hUH : inner ℝ U (A H) = inner ℝ H (A U) := by
    rw [hsymm, real_inner_comm]
  rw [map_add, inner_add_right] at hH
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hUH]
  linarith

private theorem homog_energy_le_of_norm {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (A : F →L[ℝ] F) (c : ℝ) (hA : ∀ u, ‖A u‖ ≤ c * ‖u‖)
    (U : F) (s : ℝ) (hUU : inner ℝ U U = s) : inner ℝ U (A U) ≤ c * s := by
  calc
    inner ℝ U (A U) ≤ ‖U‖ * ‖A U‖ := real_inner_le_norm _ _
    _ ≤ ‖U‖ * (c * ‖U‖) := mul_le_mul_of_nonneg_left (hA U) (norm_nonneg _)
    _ = c * inner ℝ U U := by rw [real_inner_self_eq_norm_sq]; ring
    _ = c * s := by rw [hUU]

/-- The reduced energy of a potential gradient is nonnegative, by coercivity. -/
private theorem homog_inner_self_nonneg {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (H : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (hH : H ∈ correctorPotentialDomain Q) :
    0 ≤ inner ℝ H (reducedOriginCoefficientAction Q H) := by
  obtain ⟨C, hC, hco⟩ := correctorEnergyForm_isCoercive Q
  have hnn : 0 ≤ C * ‖(⟨H, hH⟩ : correctorPotentialDomain Q)‖ *
      ‖(⟨H, hH⟩ : correctorPotentialDomain Q)‖ :=
    mul_nonneg (mul_nonneg hC.le (norm_nonneg _)) (norm_nonneg _)
  exact le_trans hnn (hco ⟨H, hH⟩)

/-- Upper energy bound for `U + H` with `H` a potential gradient orthogonal to it. -/
private theorem homog_energy_upper_of_mem {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ξ : Vec d) (H : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (hH : H ∈ correctorPotentialDomain Q)
    (hH0 : inner ℝ H (reducedOriginCoefficientAction Q
      (Lp.const 2 (reducedEnvironmentLaw Q) (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) + H)) =
      0) :
    inner ℝ (Lp.const 2 (reducedEnvironmentLaw Q) (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) + H)
      (reducedOriginCoefficientAction Q
        (Lp.const 2 (reducedEnvironmentLaw Q) (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) + H)) ≤
      sourceReducedBound Λ₀ * euclideanSq ξ := by
  have hU := homog_energy_le_of_norm (reducedOriginCoefficientAction Q)
    (Real.exp (2 * Λ₀) * Λ₀) (norm_reducedOriginCoefficientAction_le Q)
    (Lp.const 2 (reducedEnvironmentLaw Q) (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)))
    (euclideanSq ξ) (homog_inner_const_self Q ξ)
  have hcK : Real.exp (2 * Λ₀) * Λ₀ ≤ sourceReducedBound Λ₀ :=
    homog_exp_mul_le_sourceReducedBound
  have hscale := mul_le_mul_of_nonneg_right hcK (homog_euclideanSq_nonneg ξ)
  have hpos := homog_inner_self_nonneg Q H hH
  rw [homog_energy_decomp (reducedOriginCoefficientAction Q)
    (reducedOriginCoefficientAction_symmetric Q) _ _ hH0]
  linarith

/-! ### The homogenized matrix and the canonical corrector field -/

/-- The homogenized matrix `ā` of `paper/main.tex:698`: its `i`-th column is the expected
corrector flux `E[a(e_i + ∇φ_i)]` under the reduced environment law. -/
noncomputable def homogenizedMatrix {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    Mat d :=
  Matrix.of fun j i => expectedCorrectorFlux Q i j

/-- The canonical corrector field `e_i + ∇φ_i` in the reduced `L²` space. -/
noncomputable def canonicalCorrectorField {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
  correctorAffineField Q i +
    (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))

theorem canonicalCorrectorFlux_eq_action {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) :
    canonicalCorrectorFlux Q i = reducedOriginCoefficientAction Q (canonicalCorrectorField Q i) :=
  rfl

private theorem homog_sum_smul_canonicalCorrectorField {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ξ : Vec d) :
    ∑ i, ξ i • canonicalCorrectorField Q i =
      Lp.const 2 (reducedEnvironmentLaw Q) (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) +
        ∑ i, ξ i • (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) := by
  have hc : ∑ i, ξ i • correctorAffineField Q i =
      Lp.const 2 (reducedEnvironmentLaw Q) (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) := by
    calc
      ∑ i, ξ i • correctorAffineField Q i =
          ∑ i, Lp.const 2 (reducedEnvironmentLaw Q) (ξ i • correctorUnitVector i) :=
        Finset.sum_congr rfl fun i _ =>
          (homog_constLp_smul (reducedEnvironmentLaw Q) (ξ i) (correctorUnitVector i)).symm
      _ = Lp.const 2 (reducedEnvironmentLaw Q) (∑ i, ξ i • correctorUnitVector i) :=
        (map_sum (Lp.const (E := EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) _ _).symm
      _ = Lp.const 2 (reducedEnvironmentLaw Q) (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) := by
        rw [homog_sum_smul_correctorUnitVector]
  simp only [canonicalCorrectorField, smul_add, Finset.sum_add_distrib]
  rw [hc]

/-- The `(j, i)` entry of `ā` is the `L²` pairing of `e_j + ∇φ_j` with `a(e_i + ∇φ_i)`. -/
theorem homogenizedMatrix_eq_inner {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (j i : Fin d) :
    homogenizedMatrix Q j i = inner ℝ (canonicalCorrectorField Q j)
      (reducedOriginCoefficientAction Q (canonicalCorrectorField Q i)) := by
  have hG : inner ℝ (canonicalCorrectorGradient Q j :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (canonicalCorrectorFlux Q i) = 0 :=
    canonicalCorrectorGradient_variational_domain Q i (canonicalCorrectorGradient Q j)
  have hc : (expectedCorrectorFlux Q i) j =
      inner ℝ (correctorAffineField Q j) (canonicalCorrectorFlux Q i) := by
    rw [← homog_inner_unitVector j (expectedCorrectorFlux Q i)]
    exact (homog_inner_const_eq_integral (reducedEnvironmentLaw Q) (correctorUnitVector j)
      (canonicalCorrectorFlux Q i)).symm
  calc
    homogenizedMatrix Q j i = (expectedCorrectorFlux Q i) j := rfl
    _ = inner ℝ (correctorAffineField Q j) (canonicalCorrectorFlux Q i) := hc
    _ = inner ℝ (canonicalCorrectorField Q j) (canonicalCorrectorFlux Q i) := by
      rw [canonicalCorrectorField, inner_add_left, hG, add_zero]
    _ = inner ℝ (canonicalCorrectorField Q j)
        (reducedOriginCoefficientAction Q (canonicalCorrectorField Q i)) := rfl

/-- The homogenized matrix is symmetric entrywise, by symmetry of the coefficient action. -/
theorem homogenizedMatrix_apply_comm {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (j i : Fin d) : homogenizedMatrix Q j i = homogenizedMatrix Q i j := by
  rw [homogenizedMatrix_eq_inner Q j i, homogenizedMatrix_eq_inner Q i j,
    reducedOriginCoefficientAction_symmetric Q, real_inner_comm]

theorem homogenizedMatrix_transpose {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    (homogenizedMatrix Q).transpose = homogenizedMatrix Q := by
  ext j i
  rw [Matrix.transpose_apply]
  exact homogenizedMatrix_apply_comm Q i j

/-- The quadratic form of `ā` is the energy of the combined corrector field. -/
theorem homogenizedMatrix_dot_mulVec_eq_inner {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ξ : Vec d) :
    dot ξ ((homogenizedMatrix Q).mulVec ξ) =
      inner ℝ (∑ j, ξ j • canonicalCorrectorField Q j)
        (reducedOriginCoefficientAction Q (∑ j, ξ j • canonicalCorrectorField Q j)) := by
  have hexp : inner ℝ (∑ j, ξ j • canonicalCorrectorField Q j)
        (reducedOriginCoefficientAction Q (∑ j, ξ j • canonicalCorrectorField Q j)) =
      ∑ k, ∑ j, ξ k * (ξ j * inner ℝ (canonicalCorrectorField Q k)
        (reducedOriginCoefficientAction Q (canonicalCorrectorField Q j))) := by
    simp only [map_sum, map_smul]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
  rw [hexp]
  show ∑ k, ξ k * ∑ j, (homogenizedMatrix Q) k j * ξ j = _
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [homogenizedMatrix_eq_inner]
  ring

/-! ### Quadratic bounds and the operator bound -/

/-- Upper quadratic bound: `ξ·ā ξ ≤ Λ |ξ|²`, by comparison with the zero gradient. -/
theorem homogenizedMatrix_quadratic_upper {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ξ : Vec d) :
    dot ξ ((homogenizedMatrix Q).mulVec ξ) ≤ sourceReducedBound Λ₀ * euclideanSq ξ := by
  have hHmem : (∑ j, ξ j • (canonicalCorrectorGradient Q j :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) ∈
        correctorPotentialDomain Q :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ (ξ j) (canonicalCorrectorGradient Q j).2
  have hH0 : inner ℝ (∑ j, ξ j • (canonicalCorrectorGradient Q j :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)))
      (reducedOriginCoefficientAction Q (∑ j, ξ j • canonicalCorrectorField Q j)) = 0 := by
    simp only [map_sum, map_smul, inner_sum, real_inner_smul_right]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h : inner ℝ (∑ j, ξ j • (canonicalCorrectorGradient Q j :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)))
        (reducedOriginCoefficientAction Q (canonicalCorrectorField Q i)) = 0 :=
      canonicalCorrectorGradient_variational_domain Q i ⟨_, hHmem⟩
    rw [h, mul_zero]
  rw [homog_sum_smul_canonicalCorrectorField Q ξ] at hH0
  rw [homogenizedMatrix_dot_mulVec_eq_inner Q ξ, homog_sum_smul_canonicalCorrectorField Q ξ]
  exact homog_energy_upper_of_mem Q ξ _ hHmem hH0

/-- Lower quadratic bound: `Λ⁻¹ |ξ|² ≤ ξ·ā ξ`, by pointwise ellipticity and mean zero. -/
theorem homogenizedMatrix_quadratic_lower {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ξ : Vec d) :
    (sourceReducedBound Λ₀)⁻¹ * euclideanSq ξ ≤ dot ξ ((homogenizedMatrix Q).mulVec ξ) := by
  have hHmem : (∑ j, ξ j • (canonicalCorrectorGradient Q j :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) ∈
        correctorPotentialDomain Q :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ (ξ j) (canonicalCorrectorGradient Q j).2
  have hmean := homog_integral_const_add Q ξ _ hHmem
  have key := homog_lower_bound_of_mean Q ξ _ hmean
  have hc0 : 0 < Real.exp (2 * Λ₀) * Λ₀ :=
    mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hcK : Real.exp (2 * Λ₀) * Λ₀ ≤ sourceReducedBound Λ₀ :=
    homog_exp_mul_le_sourceReducedBound
  rw [homogenizedMatrix_dot_mulVec_eq_inner Q ξ, homog_sum_smul_canonicalCorrectorField Q ξ]
  exact (mul_le_mul_of_nonneg_right (inv_anti₀ hc0 hcK) (homog_euclideanSq_nonneg ξ)).trans key

/-- The homogenized matrix is elliptic with constant `Λ = sourceReducedBound Λ₀`. -/
theorem homogenizedMatrix_isElliptic {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    IsElliptic (sourceReducedBound Λ₀) (fun _ : Vec d => homogenizedMatrix Q) := by
  intro _
  exact ⟨homogenizedMatrix_transpose Q, fun ξ =>
    ⟨homogenizedMatrix_quadratic_lower Q ξ, homogenizedMatrix_quadratic_upper Q ξ⟩⟩

/-- Every column of the homogenized matrix has Euclidean norm at most `Λ`. -/
theorem homogenizedMatrix_euclideanNorm_mulVec_unitVector_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    euclideanNorm ((homogenizedMatrix Q).mulVec (unitVector i)) ≤ sourceReducedBound Λ₀ := by
  have hK : 0 < sourceReducedBound Λ₀ :=
    lt_of_lt_of_le zero_lt_one (homog_one_le_sourceReducedBound Q.ellipticity_parameter)
  have h := Correctors.mulVec_euclideanNorm_le_of_quadratic (homogenizedMatrix Q) hK
    (homogenizedMatrix_transpose Q)
    (fun ξ => (mul_nonneg (inv_nonneg.mpr hK.le) (homog_euclideanSq_nonneg ξ)).trans
      (homogenizedMatrix_quadratic_lower Q ξ))
    (fun ξ => homogenizedMatrix_quadratic_upper Q ξ) (unitVector i)
  rw [homog_euclideanNorm_unitVector, mul_one] at h
  exact h

/-! ### The mean clock density -/

/-- Source: the clock density at the origin, `E μ ∈ [Λ⁻¹, Λ]` (`paper/main.tex:1194-1199`).
The mean is taken under the reduced law, whose second coordinate is the clock density. -/
theorem reducedClockMean_bounds {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    (sourceReducedBound Λ₀)⁻¹ ≤ ∫ ω, ω.2 (0 : Vec d) ∂(reducedEnvironmentLaw Q) ∧
      ∫ ω, ω.2 (0 : Vec d) ∂(reducedEnvironmentLaw Q) ≤ sourceReducedBound Λ₀ := by
  have hL : (1 : ℝ) ≤ Λ₀ := Q.ellipticity_parameter
  have hcont : Continuous (fun ω : FieldPair d => ω.2 (0 : Vec d)) :=
    (continuous_eval_const (0 : Vec d)).comp continuous_snd
  have hred : ∫ ω, ω.2 (0 : Vec d) ∂(reducedEnvironmentLaw Q) =
      ∫ ω, clockDensity ω 0 ∂Q.measure := by
    rw [reducedEnvironmentLaw]
    exact integral_map Probability.measurable_reduce.aemeasurable
      hcont.aestronglyMeasurable
  have hbd : ∀ᵐ ω ∂Q.measure,
      (sourceReducedBound Λ₀)⁻¹ ≤ clockDensity ω 0 ∧ clockDensity ω 0 ≤ sourceReducedBound Λ₀ := by
    filter_upwards [Q.regular] with ω hω
    exact (sourceReducedBound_support hL hω).2.2.1 0
  have hnorm : ∀ᵐ ω ∂Q.measure, ‖clockDensity ω 0‖ ≤ sourceReducedBound Λ₀ := by
    filter_upwards [hbd] with ω hω
    rw [Real.norm_of_nonneg (clockDensity_pos ω 0).le]
    exact hω.2
  have hcd : Continuous (fun ω : FieldPair d => clockDensity ω 0) := by
    unfold clockDensity
    exact Real.continuous_exp.comp (continuous_const.mul hcont)
  have hint : Integrable (fun ω : FieldPair d => clockDensity ω 0) Q.measure :=
    Integrable.of_bound hcd.aestronglyMeasurable _ hnorm
  rw [hred]
  constructor
  · have h := integral_mono_ae (integrable_const ((sourceReducedBound Λ₀)⁻¹)) hint
      (hbd.mono fun ω hω => hω.1)
    rwa [integral_const, probReal_univ, one_smul] at h
  · have h := integral_mono_ae hint (integrable_const (sourceReducedBound Λ₀))
      (hbd.mono fun ω hω => hω.2)
    rwa [integral_const, probReal_univ, one_smul] at h

end

end EinsteinRelation
