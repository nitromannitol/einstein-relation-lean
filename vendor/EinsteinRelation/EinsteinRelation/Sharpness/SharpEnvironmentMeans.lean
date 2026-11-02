import EinsteinRelation.Sharpness.SharpExampleFromSteps
import EinsteinRelation.Sharpness.DivergenceProfileBounds
import EinsteinRelation.Sharpness.JacobianReconciliation
import EinsteinRelation.Sharpness.SeedField
import EinsteinRelation.Probability.LocalSigma
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The two mean identities of the sharp environment input

Source `paper/main.tex` 1231 (`𝔼μ = 1`) and 1259–1265 (`𝔼a₁₁ - 1 = 𝔼[|G|²/(1+G₁)]`).

The sharp law is `Q = P.map (sharpPhysicalPair …)` for a seed law `P`. Every seed sample is smooth
and has the gradient bound, so the identities are proved on the seed side by transport:

* `𝔼G₁ = 0`: the seed value at `t e₁` is bounded by `ε` and has `t`-derivative `G₁` in law. Its
  mean is constant in `t` by stationarity, hence zero.
* `𝔼μ = 1`: the divergence of the coefficient column is a sum of coordinate derivatives of
  rank-one coefficient entries. Their difference quotients are dominated uniformly, and
  stationarity gives each quotient zero mean, so dominated convergence gives zero mean for the sum.

The corrector items of `SharpEnvironmentInput` (measurability, the `1/4` bound, positivity, and
`ā e₁ = e₁`) enter `sharpEnvironmentInput_of_corrector` as hypotheses.
-/

open MeasureTheory Filter Topology

namespace EinsteinRelation.Sharpness

variable {d : ℕ}

/-! ### Coordinates and the gradient box -/

/-- A coordinate of a vector is bounded in absolute value by its Euclidean norm. -/
private theorem abs_coord_le_euclideanNorm (v : Vec d) (k : Fin d) :
    |v k| ≤ euclideanNorm v := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
    (Finset.mem_univ k)

/-- The box `[-1/4, 1/4]^d` containing every gradient allowed by the sharpness bound. -/
private def gradBox (d : ℕ) : Set (Vec d) :=
  Set.Icc (fun _ => -(1 / 4 : ℝ)) (fun _ => (1 / 4 : ℝ))

private theorem mem_gradBox {g : Vec d} : g ∈ gradBox d ↔ ∀ k, |g k| ≤ 1 / 4 := by
  unfold gradBox
  rw [Set.mem_Icc, Pi.le_def, Pi.le_def]
  constructor
  · rintro ⟨h1, h2⟩ k
    exact abs_le.2 ⟨h1 k, h2 k⟩
  · intro h
    exact ⟨fun k => (abs_le.1 (h k)).1, fun k => (abs_le.1 (h k)).2⟩

private theorem convex_gradBox : Convex ℝ (gradBox d) := convex_Icc _ _

private theorem isCompact_gradBox : IsCompact (gradBox d) := isCompact_Icc

private theorem gradient_mem_gradBox {ψ : Vec d → ℝ} {x : Vec d}
    (h : euclideanNorm (gradient ψ x) ≤ 1 / 4) : gradient ψ x ∈ gradBox d :=
  mem_gradBox.2 fun k => (abs_coord_le_euclideanNorm _ k).trans h

private theorem one_add_pos_of_mem_gradBox {g : Vec d} (hg : g ∈ gradBox d) (i : Fin d) :
    0 < 1 + g i := by
  have h := (abs_le.1 (mem_gradBox.1 hg i)).1
  linarith

/-! ### Regularity of the rank-one coefficient on the gradient box -/

private theorem inverseCandidate_apply_eq (i p q : Fin d) (g : Vec d) :
    inverseCandidate i g p q = (1 : Mat d) p q - (1 + g i)⁻¹ * (unitVector i p * g q) :=
  rfl

private theorem contDiffAt_inverseCandidate_apply (i p q : Fin d) (g₀ : Vec d)
    (h : 1 + g₀ i ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun g : Vec d => inverseCandidate i g p q) g₀ := by
  have hden : ContDiffAt ℝ (⊤ : ℕ∞) (fun g : Vec d => 1 + g i) g₀ :=
    contDiffAt_const.add (contDiff_apply ℝ ℝ i).contDiffAt
  have hinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun g : Vec d => (1 + g i)⁻¹) g₀ := hden.inv h
  have hcoord : ContDiffAt ℝ (⊤ : ℕ∞) (fun g : Vec d => g q) g₀ :=
    (contDiff_apply ℝ ℝ q).contDiffAt
  have heq : (fun g : Vec d => inverseCandidate i g p q) =
      fun g => (1 : Mat d) p q - (1 + g i)⁻¹ * (unitVector i p * g q) :=
    funext fun g => inverseCandidate_apply_eq i p q g
  rw [heq]
  exact contDiffAt_const.sub (hinv.mul (contDiffAt_const.mul hcoord))

private theorem coefficient_apply_eq_sum (i j c : Fin d) (g : Vec d) :
    coefficient i g j c =
      (1 + g i) * ∑ m, inverseCandidate i g j m * inverseCandidate i g c m := by
  simp only [coefficient, jacobianFactor, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply]

private theorem contDiffAt_coefficient_apply (i j c : Fin d) (g₀ : Vec d) (h : 1 + g₀ i ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun g : Vec d => coefficient i g j c) g₀ := by
  have hden : ContDiffAt ℝ (⊤ : ℕ∞) (fun g : Vec d => 1 + g i) g₀ :=
    contDiffAt_const.add (contDiff_apply ℝ ℝ i).contDiffAt
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun g : Vec d => ∑ m, inverseCandidate i g j m * inverseCandidate i g c m) g₀ :=
    ContDiffAt.sum fun m _ =>
      (contDiffAt_inverseCandidate_apply i j m g₀ h).mul
        (contDiffAt_inverseCandidate_apply i c m g₀ h)
  have heq : (fun g : Vec d => coefficient i g j c) =
      fun g => (1 + g i) * ∑ m, inverseCandidate i g j m * inverseCandidate i g c m :=
    funext fun g => coefficient_apply_eq_sum i j c g
  rw [heq]
  exact hden.mul hsum

private theorem differentiableAt_coefficient_apply_gradBox (i j c : Fin d) {g : Vec d}
    (hg : g ∈ gradBox d) : DifferentiableAt ℝ (fun g : Vec d => coefficient i g j c) g :=
  (contDiffAt_coefficient_apply i j c g (one_add_pos_of_mem_gradBox hg i).ne').differentiableAt
    (by simp)

/-- A coefficient entry is bounded on the gradient box and Lipschitz there for the sup norm. -/
private theorem coefficient_apply_gradBox_bounds (i j c : Fin d) :
    ∃ C L : ℝ, 0 ≤ L ∧ (∀ g ∈ gradBox d, |coefficient i g j c| ≤ C) ∧
      ∀ g ∈ gradBox d, ∀ g' ∈ gradBox d,
        |coefficient i g j c - coefficient i g' j c| ≤ L * ‖g - g'‖ := by
  have hfun : ContinuousOn (fun g : Vec d => coefficient i g j c) (gradBox d) := fun g hg =>
    (differentiableAt_coefficient_apply_gradBox i j c hg).continuousAt.continuousWithinAt
  have hfd : ContinuousOn (fderiv ℝ (fun g : Vec d => coefficient i g j c)) (gradBox d) :=
    fun g hg => ((contDiffAt_coefficient_apply i j c g
      (one_add_pos_of_mem_gradBox hg i).ne').continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_gradBox.exists_bound_of_continuousOn hfun
  obtain ⟨L, hL⟩ := isCompact_gradBox.exists_bound_of_continuousOn hfd
  refine ⟨C, max L 0, le_max_right _ _, fun g hg => ?_, fun g hg g' hg' => ?_⟩
  · simpa only [Real.norm_eq_abs] using hC g hg
  · have h := Convex.norm_image_sub_le_of_norm_fderiv_le (C := max L 0)
      (fun x hx => differentiableAt_coefficient_apply_gradBox i j c hx)
      (fun x hx => (hL x hx).trans (le_max_left L 0)) convex_gradBox hg' hg
    simpa only [Real.norm_eq_abs] using h

/-! ### Calculus along coordinate lines -/

private theorem differentiable_coordinateDerivative_contDiff {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (k : Fin d) : Differentiable ℝ (coordinateDerivative k ψ) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x => coordinateDerivative k ψ x) := by
    unfold coordinateDerivative
    exact (hψ.fderiv_right (le_of_eq ENat.coe_top_add_one)).clm_apply contDiff_const
  exact fun y => h.differentiable (by simp) y

private theorem differentiableAt_gradient_contDiff {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : Vec d) : DifferentiableAt ℝ (fun z => gradient ψ z) y :=
  differentiableAt_pi.2 fun k => differentiable_coordinateDerivative_contDiff hψ k y

private theorem hasDerivAt_coordinate_line (F : Vec d → ℝ) (hF : Differentiable ℝ F) (j : Fin d)
    (s : ℝ) :
    HasDerivAt (fun t : ℝ => F (t • unitVector j)) (coordinateDerivative j F (s • unitVector j)) s := by
  have hline : HasDerivAt (fun t : ℝ => t • unitVector j) (unitVector j) s := by
    simpa only [one_smul] using (hasDerivAt_id' s).smul_const (unitVector j)
  exact (hF (s • unitVector j)).hasFDerivAt.comp_hasDerivAt s hline

/-- Along the coordinate line through `0` in direction `j`, the gradient of a smooth function whose
Hessian is bounded by `M` moves by at most `M |t|` in the sup norm. -/
private theorem gradient_line_sub_le {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M : ℝ}
    (hM : 0 ≤ M) (hH : ∀ m n y, |coordinateDerivative m (coordinateDerivative n ψ) y| ≤ M)
    (j : Fin d) (t : ℝ) :
    ‖gradient ψ (t • unitVector j) - gradient ψ 0‖ ≤ M * |t| := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hM (abs_nonneg t))]
  intro k
  rw [Pi.sub_apply, Real.norm_eq_abs]
  show |coordinateDerivative k ψ (t • unitVector j) - coordinateDerivative k ψ 0| ≤ M * |t|
  have hline : ∀ s : ℝ, HasDerivAt (fun u : ℝ => coordinateDerivative k ψ (u • unitVector j))
      (coordinateDerivative j (coordinateDerivative k ψ) (s • unitVector j)) s :=
    fun s => hasDerivAt_coordinate_line _ (differentiable_coordinateDerivative_contDiff hψ k) j s
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (C := M)
    (fun s _ => (hline s).differentiableAt)
    (fun s _ => by
      rw [(hline s).deriv, Real.norm_eq_abs]
      exact hH j k _)
    convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs, zero_smul, sub_zero] using key

/-- Unpack the Hessian and gradient bounds carried by the jet box. -/
private theorem bounds_of_mem_jetBox {M : ℝ} {a : Vec d} {b : Fin d → Fin d → ℝ}
    (hm : (a, b) ∈ coefficientJetBox d M) :
    (∀ k, |a k| ≤ 1 / 4) ∧ ∀ m n, |b m n| ≤ M := by
  unfold coefficientJetBox at hm
  obtain ⟨hlo, hhi⟩ := hm
  exact ⟨fun k => abs_le.2 ⟨hlo.1 k, hhi.1 k⟩, fun m n => abs_le.2 ⟨hlo.2 m n, hhi.2 m n⟩⟩

private theorem euclideanSq_le_of_coord_bound (g : Vec d) (hg : ∀ k, |g k| ≤ 1 / 4) :
    euclideanSq g ≤ (d : ℝ) / 16 := by
  have hk : ∀ k, g k * g k ≤ 1 / 16 := fun k => by
    have h := mul_self_le_mul_self (abs_nonneg (g k)) (hg k)
    rw [abs_mul_abs_self] at h
    linarith
  calc euclideanSq g = ∑ k, g k * g k := rfl
    _ ≤ ∑ _k : Fin d, (1 / 16 : ℝ) := Finset.sum_le_sum fun k _ => hk k
    _ = (d : ℝ) / 16 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The scalar energy of a gradient in the box lies in `[0, d]`. -/
private theorem sharpEnergy_bounds (i : Fin d) (g : Vec d) (hg : ∀ k, |g k| ≤ 1 / 4) :
    0 ≤ sharpEnergy i g ∧ sharpEnergy i g ≤ d := by
  have h3 : (3 / 4 : ℝ) ≤ 1 + g i := by linarith [(abs_le.1 (hg i)).1]
  have hi : 0 < 1 + g i := by linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs : 0 ≤ euclideanSq g := euclideanSq_nonneg g
  refine ⟨div_nonneg hs hi.le, ?_⟩
  unfold sharpEnergy
  rw [div_le_iff₀ hi]
  linarith [euclideanSq_le_of_coord_bound g hg, mul_le_mul_of_nonneg_left h3 hd0]

private theorem measurable_sharpEnergy (i : Fin d) :
    Measurable (fun g : Vec d => sharpEnergy i g) := by
  show Measurable fun g : Vec d => (∑ k, g k * g k) / (1 + g i)
  exact (Finset.measurable_sum _ fun k _ =>
    (measurable_pi_apply k).mul (measurable_pi_apply k)).div
    (measurable_const.add (measurable_pi_apply i))

private theorem mulVec_unitVector_apply (M : Mat d) (j c : Fin d) :
    M.mulVec (unitVector c) j = M j c := by
  simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]

/-- Inversion of the rank-one coefficient: `a⁻¹ e_i = e_i + g` when `a = coefficient i g`. -/
private theorem coefficient_inv_mulVec_unitVector (i : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4) :
    ((coefficient i g)⁻¹).mulVec (unitVector i) = unitVector i + g := by
  have hdet : (coefficient i g).det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hell := (coefficient_uniformlyElliptic i g hg v).1
    rw [hAv] at hell
    have hpos := (euclideanSq_pos_iff v).2 hv
    have hzero : dot v 0 = 0 := by simp [dot]
    linarith
  calc ((coefficient i g)⁻¹).mulVec (unitVector i)
      = ((coefficient i g)⁻¹).mulVec ((coefficient i g).mulVec (unitVector i + g)) := by
        rw [coefficient_mulVec_harmonic i g hg]
    _ = ((coefficient i g)⁻¹ * coefficient i g).mulVec (unitVector i + g) := by
        rw [Matrix.mulVec_mulVec]
    _ = unitVector i + g := by
        rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]

/-! ### The physical pair and its reduced coefficient -/

/-- The reduced coefficient of the physical pair is the rank-one coefficient of the scaled seed's
gradient. -/
private theorem reducedCoefficient_sharpPair (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) (x : Vec d) :
    reducedCoefficient (sharpPhysicalPair i δ ε hgrad hμ W) x =
      coefficient i (gradient (fun y => ε * seedField d W y) x) := by
  have hpos : 0 < densityField i δ (fun y => ε * seedField d W y) x := by
    linarith [(hμ W x).1]
  exact physicalEnvironment_reducedCoefficient i δ (fun y => ε * seedField d W y)
    (sharpSeed_continuous_coefficient i δ ε hgrad hμ W)
    (sharpSeed_continuous_potential i δ ε hgrad hμ W) x hpos

/-- The clock density of the physical pair at a point. -/
private theorem clockDensity_sharpPair (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) (x : Vec d) :
    clockDensity (sharpPhysicalPair i δ ε hgrad hμ W) x =
      densityField i δ (fun y => ε * seedField d W y) x := by
  have hpos : 0 < densityField i δ (fun y => ε * seedField d W y) x := by
    linarith [(hμ W x).1]
  exact physicalEnvironment_clockDensity i δ (fun y => ε * seedField d W y)
    (sharpSeed_continuous_coefficient i δ ε hgrad hμ W)
    (sharpSeed_continuous_potential i δ ε hgrad hμ W) x hpos

/-- Translation covariance of the reduced coefficient. -/
private theorem reducedCoefficient_translate (x y : Vec d) (ω : FieldPair d) :
    reducedCoefficient (translate x ω) y = reducedCoefficient ω (x + y) :=
  rfl

private theorem reducedCoefficient_translate_zero (x : Vec d) (ω : FieldPair d) :
    reducedCoefficient (translate x ω) 0 = reducedCoefficient ω x := by
  rw [reducedCoefficient_translate, add_zero]

private theorem continuous_clockDensity_apply (x : Vec d) :
    Continuous fun ω : FieldPair d => clockDensity ω x := by
  have hB : Continuous fun ω : FieldPair d => ω.2 x :=
    (continuous_eval_const x : Continuous fun H : ContinuousMap (Vec d) ℝ => H x).comp continuous_snd
  exact Real.continuous_exp.comp (continuous_const.mul hB)

private theorem continuous_reducedCoefficient_apply (x : Vec d) (j c : Fin d) :
    Continuous fun ω : FieldPair d => reducedCoefficient ω x j c := by
  have hA : Continuous fun ω : FieldPair d => ω.1 x :=
    (continuous_eval_const x : Continuous fun H : ContinuousMap (Vec d) (Mat d) => H x).comp
      continuous_fst
  have hM : Continuous fun ω : FieldPair d => reducedCoefficient ω x :=
    (continuous_clockDensity_apply x).smul hA
  exact hM.matrix_elem j c

/-- The local gradient at the origin is determined by the reduced coefficient there. -/
private theorem sharpLocalGradient_eq_of_coefficient (hd : 2 ≤ d) (ω : FieldPair d) (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4)
    (h : reducedCoefficient ω 0 = coefficient (⟨0, by omega⟩ : Fin d) g) :
    sharpLocalGradient hd ω = g := by
  unfold sharpLocalGradient
  rw [h, coefficient_inv_mulVec_unitVector _ g hg]
  abel

/-- The local gradient of a translated physical pair is the gradient of the scaled seed. -/
private theorem sharpLocalGradient_translate (hd : 2 ≤ d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ∧
      densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) (y : Vec d) :
    sharpLocalGradient hd (translate y (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)) =
      gradient (fun z => ε * seedField d W z) y := by
  apply sharpLocalGradient_eq_of_coefficient hd _ _ (hgrad W y)
  rw [reducedCoefficient_translate_zero, reducedCoefficient_sharpPair]

/-- At the origin, the local gradient of the physical pair is the gradient of the scaled seed. -/
private theorem sharpLocalGradient_pair (hd : 2 ≤ d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ∧
      densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) :
    sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W) =
      gradient (fun z => ε * seedField d W z) 0 :=
  sharpLocalGradient_eq_of_coefficient hd _ _ (hgrad W 0)
    (reducedCoefficient_sharpPair _ δ ε hgrad hμ W 0)

/-- The diagonal entry `a₁₁` of the physical pair, written through the scaled seed's gradient. -/
private theorem sharpA11_pair (hd : 2 ≤ d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ∧
      densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) :
    sharpA11 hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W) 0 =
      1 - gradient (fun z => ε * seedField d W z) 0 (⟨0, by omega⟩ : Fin d) +
        sharpEnergy (⟨0, by omega⟩ : Fin d) (gradient (fun z => ε * seedField d W z) 0) := by
  unfold sharpA11
  rw [reducedCoefficient_sharpPair, coefficient_apply_self _ _ (hgrad W 0)]
  simp only [sharpEnergy, jacobianFactor]

/-! ### Transport from the sharp law to the seed sample space -/

/-- An observable of `Q = P.map pair` integrates as its composition with `pair` under `P`. -/
private theorem integral_map_pair {P : Measure (NoiseSample d)} {Q : Measure (FieldPair d)}
    {pair : NoiseSample d → FieldPair d} (hpair : Measurable pair) (hQ : Q = P.map pair)
    {f : FieldPair d → ℝ} (hf : Measurable f) :
    ∫ ω, f ω ∂Q = ∫ W, f (pair W) ∂P := by
  rw [hQ]
  exact integral_map hpair.aemeasurable hf.aestronglyMeasurable

/-- Stationarity of `Q` transfers to translation invariance of observables on the seed space. -/
private theorem integral_pair_translate {P : Measure (NoiseSample d)}
    {Q : Measure (FieldPair d)} {pair : NoiseSample d → FieldPair d}
    (hpair : Measurable pair) (hQ : Q = P.map pair) (hst : IsStationary Q)
    {f : FieldPair d → ℝ} (hf : Measurable f) (x : Vec d) :
    ∫ W, f (translate x (pair W)) ∂P = ∫ W, f (pair W) ∂P := by
  have h1 : ∫ ω, f (translate x ω) ∂Q = ∫ W, f (translate x (pair W)) ∂P :=
    integral_map_pair hpair hQ (hf.comp (EinsteinRelation.Probability.measurable_translate x))
  calc ∫ W, f (translate x (pair W)) ∂P = ∫ ω, f (translate x ω) ∂Q := h1.symm
    _ = ∫ ω, f ω ∂Q := EinsteinRelation.Probability.integral_translate Q hst x f hf
    _ = ∫ W, f (pair W) ∂P := integral_map_pair hpair hQ hf

private theorem abs_inv_mul_le {h B X : ℝ} (hh : h ≠ 0) (hX : |X| ≤ B * |h|) :
    |h⁻¹ * X| ≤ B := by
  have hpos : 0 < |h| := abs_pos.2 hh
  rw [abs_mul, abs_inv]
  calc |h|⁻¹ * |X| ≤ |h|⁻¹ * (B * |h|) := mul_le_mul_of_nonneg_left hX (inv_nonneg.2 hpos.le)
    _ = B := by field_simp

/-- A difference quotient along a line converges to the directional derivative. -/
private theorem tendsto_quotient_of_hasDerivAt (F : Vec d → ℝ) (e : Vec d) {D : ℝ}
    (hF : HasDerivAt (fun s : ℝ => F (s • e)) D 0) :
    Tendsto (fun h : ℝ => h⁻¹ * (F (h • e) - F 0)) (𝓝[≠] (0 : ℝ)) (𝓝 D) := by
  refine (hasDerivAt_iff_tendsto_slope_zero.1 hF).congr fun h => ?_
  simp only [zero_add, zero_smul, smul_eq_mul]

/-- The `(j, i)` entry of the rank-one coefficient of the gradient of the scaled seed at `y`. -/
private noncomputable def seedEntry (i j : Fin d) (ε : ℝ) (W : NoiseSample d) (y : Vec d) : ℝ :=
  coefficient i (gradient (fun z => ε * seedField d W z) y) j i

private theorem reducedCoefficient_sharpPair_entry (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) (y : Vec d) (j : Fin d) :
    reducedCoefficient (sharpPhysicalPair i δ ε hgrad hμ W) y j i = seedEntry i j ε W y := by
  rw [reducedCoefficient_sharpPair]
  rfl

/-- The seed entries have zero stationary mean along the divergence: the sum over `j` of the
orbit derivatives of the entries `(j, i)` integrates to zero. This is the mean of `μ - 1`. -/
private theorem integral_seedEntry_divergence_eq_zero (i : Fin d) (δ ε : ℝ) (hε : 0 < ε)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (P : Measure (NoiseSample d)) [IsProbabilityMeasure P]
    (hst : IsStationary (P.map (sharpPhysicalPair i δ ε hgrad hμ))) :
    ∫ W, (∑ j, coordinateDerivative j (seedEntry i j ε W) 0) ∂P = 0 := by
  obtain ⟨M, hM0, hbox⟩ := exists_uniform_scaled_seedField_jet_box ε hgrad
  choose Cf Lf hLf0 hCf hLf using fun j : Fin d => coefficient_apply_gradBox_bounds i j i
  have hpairMeas := measurable_sharpPhysicalPair i δ ε hgrad hμ
  have hEm : ∀ (x : Vec d) (j : Fin d),
      Measurable (fun W : NoiseSample d => seedEntry i j ε W x) := by
    intro x j
    have h : (fun W : NoiseSample d => seedEntry i j ε W x) =
        (fun ω : FieldPair d => reducedCoefficient ω x j i) ∘
          sharpPhysicalPair i δ ε hgrad hμ := by
      funext W
      exact (reducedCoefficient_sharpPair_entry i δ ε hgrad hμ W x j).symm
    rw [h]
    exact (continuous_reducedCoefficient_apply x j i).measurable.comp hpairMeas
  have hEb : ∀ (x : Vec d) (j : Fin d) (W : NoiseSample d), |seedEntry i j ε W x| ≤ Cf j :=
    fun x j W => hCf j _ (gradient_mem_gradBox (hgrad W x))
  have hRint : ∀ (x : Vec d) (j : Fin d),
      Integrable (fun W : NoiseSample d => seedEntry i j ε W x) P :=
    fun x j => Integrable.of_bound (hEm x j).aestronglyMeasurable (Cf j)
      (Filter.Eventually.of_forall fun W => by rw [Real.norm_eq_abs]; exact hEb x j W)
  have hshift : ∀ (x : Vec d) (j : Fin d),
      ∫ W, seedEntry i j ε W x ∂P = ∫ W, seedEntry i j ε W 0 ∂P := by
    intro x j
    have h := integral_pair_translate (P := P) (Q := P.map (sharpPhysicalPair i δ ε hgrad hμ))
      hpairMeas rfl hst (f := fun ω : FieldPair d => reducedCoefficient ω 0 j i)
      (continuous_reducedCoefficient_apply 0 j i).measurable x
    simp only [reducedCoefficient_translate_zero, reducedCoefficient_sharpPair_entry] at h
    exact h
  have hdiffE : ∀ (W : NoiseSample d) (j : Fin d) (y : Vec d),
      DifferentiableAt ℝ (seedEntry i j ε W) y := by
    intro W j y
    exact (differentiableAt_coefficient_apply_gradBox i j i
      (gradient_mem_gradBox (hgrad W y))).comp y
      (differentiableAt_gradient_contDiff (sharpSeed_contDiff ε W) y)
  have hline : ∀ (W : NoiseSample d) (j : Fin d),
      HasDerivAt (fun s : ℝ => seedEntry i j ε W (s • unitVector j))
        (coordinateDerivative j (seedEntry i j ε W) 0) 0 := by
    intro W j
    have h := hasDerivAt_coordinate_line (seedEntry i j ε W) (fun y => hdiffE W j y) j 0
    rwa [zero_smul] at h
  have hlim : ∀ W : NoiseSample d, Tendsto
      (fun h : ℝ => ∑ j, h⁻¹ * (seedEntry i j ε W (h • unitVector j) - seedEntry i j ε W 0))
      (𝓝[≠] (0 : ℝ)) (𝓝 (∑ j, coordinateDerivative j (seedEntry i j ε W) 0)) :=
    fun W => tendsto_finset_sum _ fun j _ =>
      tendsto_quotient_of_hasDerivAt (seedEntry i j ε W) (unitVector j) (hline W j)
  have hquot : ∀ (W : NoiseSample d) (j : Fin d) (h : ℝ),
      |h⁻¹ * (seedEntry i j ε W (h • unitVector j) - seedEntry i j ε W 0)| ≤ Lf j * M := by
    intro W j h
    by_cases hh : h = 0
    · rw [hh, inv_zero, zero_mul, abs_zero]
      exact mul_nonneg (hLf0 j) hM0
    · refine abs_inv_mul_le hh ?_
      have hH : ∀ m n y,
          |coordinateDerivative m (coordinateDerivative n (fun z => ε * seedField d W z)) y| ≤ M :=
        fun m n y => (bounds_of_mem_jetBox (hbox W y)).2 m n
      calc |seedEntry i j ε W (h • unitVector j) - seedEntry i j ε W 0|
          ≤ Lf j * ‖gradient (fun z => ε * seedField d W z) (h • unitVector j) -
              gradient (fun z => ε * seedField d W z) 0‖ :=
            hLf j (gradient (fun z => ε * seedField d W z) (h • unitVector j))
              (gradient_mem_gradBox (hgrad W (h • unitVector j)))
              (gradient (fun z => ε * seedField d W z) 0) (gradient_mem_gradBox (hgrad W 0))
        _ ≤ Lf j * (M * |h|) :=
            mul_le_mul_of_nonneg_left
              (gradient_line_sub_le (sharpSeed_contDiff ε W) hM0 hH j h) (hLf0 j)
        _ = Lf j * M * |h| := by ring
  have hTb : ∀ (h : ℝ) (W : NoiseSample d),
      ‖∑ j, h⁻¹ * (seedEntry i j ε W (h • unitVector j) - seedEntry i j ε W 0)‖ ≤
        ∑ j, Lf j * M := by
    intro h W
    rw [Real.norm_eq_abs]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hquot W j h)
  have hTm : ∀ h : ℝ, Measurable (fun W : NoiseSample d =>
      ∑ j, h⁻¹ * (seedEntry i j ε W (h • unitVector j) - seedEntry i j ε W 0)) := fun h =>
    Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ((hEm (h • unitVector j) j).sub (hEm 0 j))
  have hTzero : ∀ h : ℝ, ∫ W, (∑ j, h⁻¹ *
      (seedEntry i j ε W (h • unitVector j) - seedEntry i j ε W 0)) ∂P = 0 := by
    intro h
    have hint : ∀ j ∈ (Finset.univ : Finset (Fin d)), Integrable
        (fun W : NoiseSample d => h⁻¹ * (seedEntry i j ε W (h • unitVector j) - seedEntry i j ε W 0)) P :=
      fun j _ => ((hRint (h • unitVector j) j).sub (hRint 0 j)).const_mul h⁻¹
    rw [integral_finset_sum _ hint]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, integral_sub (hRint (h • unitVector j) j) (hRint 0 j),
      hshift (h • unitVector j) j, sub_self, mul_zero]
  have hdct := tendsto_integral_filter_of_dominated_convergence (μ := P) (l := 𝓝[≠] (0 : ℝ))
    (F := fun (h : ℝ) (W : NoiseSample d) =>
      ∑ j, h⁻¹ * (seedEntry i j ε W (h • unitVector j) - seedEntry i j ε W 0))
    (f := fun W : NoiseSample d => ∑ j, coordinateDerivative j (seedEntry i j ε W) 0)
    (fun _ => ∑ j, Lf j * M)
    (Filter.Eventually.of_forall fun h => (hTm h).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun h => Filter.Eventually.of_forall fun W => hTb h W)
    (integrable_const _)
    (Filter.Eventually.of_forall hlim)
  have hconst : Tendsto
      (fun h : ℝ => ∫ W, (∑ j, h⁻¹ *
        (seedEntry i j ε W (h • unitVector j) - seedEntry i j ε W 0)) ∂P)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simp only [hTzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hdct hconst

/-! ### Mean one of the clock density -/

/-- Stationarity gives `𝔼μ = 1` for the clock density of the sharp law `Q = P.map pair`. -/
theorem sharp_meanMu_eq_one (i : Fin d) (δ ε : ℝ) (hε : 0 < ε)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (P : Measure (NoiseSample d)) [IsProbabilityMeasure P]
    (Q : Measure (FieldPair d)) (hQ : Q = P.map (sharpPhysicalPair i δ ε hgrad hμ))
    (hst : IsStationary Q) :
    ∫ ω, clockDensity ω 0 ∂Q = 1 := by
  have hpairMeas := measurable_sharpPhysicalPair i δ ε hgrad hμ
  have hst' : IsStationary (P.map (sharpPhysicalPair i δ ε hgrad hμ)) := by
    rw [← hQ]
    exact hst
  have hcd : Measurable (fun ω : FieldPair d => clockDensity ω 0) :=
    (continuous_clockDensity_apply 0).measurable
  have hint1 : ∫ _W : NoiseSample d, (1 : ℝ) ∂P = 1 := by simp
  have hμint : Integrable
      (fun W : NoiseSample d => clockDensity (sharpPhysicalPair i δ ε hgrad hμ W) 0) P := by
    refine Integrable.of_bound ((hcd.comp hpairMeas).aestronglyMeasurable) (5 / 4)
      (Filter.Eventually.of_forall fun W => ?_)
    show ‖clockDensity (sharpPhysicalPair i δ ε hgrad hμ W) 0‖ ≤ 5 / 4
    rw [clockDensity_sharpPair i δ ε hgrad hμ W 0, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hμ W 0).1], (hμ W 0).2⟩
  have hdiv : ∀ W : NoiseSample d,
      divergence (fun y => (coefficientField i (fun z => ε * seedField d W z) y).mulVec
        (unitVector i)) 0 = ∑ j, coordinateDerivative j (seedEntry i j ε W) 0 := by
    intro W
    unfold divergence
    refine Finset.sum_congr rfl fun j _ => ?_
    have hfun : (fun y => (coefficientField i (fun z => ε * seedField d W z) y).mulVec
        (unitVector i) j) = seedEntry i j ε W :=
      funext fun y => mulVec_unitVector_apply _ j i
    exact congrArg (fun F => coordinateDerivative j F 0) hfun
  have hpt : ∀ W : NoiseSample d,
      clockDensity (sharpPhysicalPair i δ ε hgrad hμ W) 0 - 1 =
        δ / 2 * ∑ j, coordinateDerivative j (seedEntry i j ε W) 0 := by
    intro W
    rw [clockDensity_sharpPair i δ ε hgrad hμ W 0]
    unfold densityField
    rw [hdiv W]
    ring
  have hD := integral_seedEntry_divergence_eq_zero i δ ε hε hgrad hμ P hst'
  have hsub : ∫ W, (clockDensity (sharpPhysicalPair i δ ε hgrad hμ W) 0 - 1) ∂P = 0 := by
    calc ∫ W, (clockDensity (sharpPhysicalPair i δ ε hgrad hμ W) 0 - 1) ∂P
        = ∫ W, δ / 2 * ∑ j, coordinateDerivative j (seedEntry i j ε W) 0 ∂P := by
          congr 1
          funext W
          exact hpt W
      _ = δ / 2 * ∫ W, ∑ j, coordinateDerivative j (seedEntry i j ε W) 0 ∂P :=
          integral_const_mul _ _
      _ = 0 := by rw [hD, mul_zero]
  have h1 : ∫ W, (clockDensity (sharpPhysicalPair i δ ε hgrad hμ W) 0 - 1) ∂P =
      ∫ W, clockDensity (sharpPhysicalPair i δ ε hgrad hμ W) 0 ∂P - ∫ _W, (1 : ℝ) ∂P :=
    integral_sub hμint (integrable_const 1)
  rw [hsub, hint1] at h1
  have htr : ∫ ω, clockDensity ω 0 ∂Q =
      ∫ W, clockDensity (sharpPhysicalPair i δ ε hgrad hμ W) 0 ∂P :=
    integral_map_pair hpairMeas hQ hcd
  rw [htr]
  linarith

/-- A coordinate derivative of a function whose gradient lies in the sharpness bound is at most
`1/4` in absolute value. -/
private theorem abs_coordinateDerivative_le_quarter {ψ : Vec d → ℝ} {x : Vec d} (k : Fin d)
    (h : euclideanNorm (gradient ψ x) ≤ 1 / 4) : |coordinateDerivative k ψ x| ≤ 1 / 4 :=
  (abs_coord_le_euclideanNorm (gradient ψ x) k).trans h

/-! ### Zero mean of the local gradient component `G₁` -/

/-- A real function with constant derivative `c` and values bounded by `ε` forces `c = 0`: the
function `t ↦ F t - c t` is constant, so `|c t| ≤ 2ε` for every `t`, which fails at `t = 3ε / c`. -/
private theorem eq_zero_of_hasDerivAt_const_bounded {F : ℝ → ℝ} {c ε : ℝ} (hε : 0 < ε)
    (hF : ∀ s, HasDerivAt F c s) (hb : ∀ t, |F t| ≤ ε) : c = 0 := by
  by_contra hc
  have hc' : c ≠ 0 := hc
  have hG : ∀ s : ℝ, HasDerivAt (fun t : ℝ => F t - c * t) 0 s := fun s => by
    have h := (hF s).sub ((hasDerivAt_id' s).const_mul c)
    rw [mul_one, sub_self] at h
    exact h
  have hfix : ∀ t : ℝ, F t - c * t = F 0 := fun t => by
    have h := is_const_of_deriv_eq_zero (fun s => (hG s).differentiableAt)
      (fun s => (hG s).deriv) t 0
    simpa only [mul_zero, sub_zero] using h
  have hbd : ∀ t : ℝ, |c * t| ≤ 2 * ε := fun t => by
    have h1 := abs_le.1 (hb t)
    have h2 := abs_le.1 (hb 0)
    rw [abs_le]
    constructor <;> linarith [hfix t, h1.1, h1.2, h2.1, h2.2]
  have hcancel : c * (3 * ε * c⁻¹) = 3 * ε := by
    calc c * (3 * ε * c⁻¹) = 3 * ε * (c * c⁻¹) := by ring
      _ = 3 * ε := by rw [mul_inv_cancel₀ hc', mul_one]
  have ht := hbd (3 * ε * c⁻¹)
  rw [hcancel, abs_of_pos (by linarith : (0 : ℝ) < 3 * ε)] at ht
  linarith

/-- The scaled seed is differentiable on the whole space. -/
private theorem differentiable_scaledSeed (ε : ℝ) (W : NoiseSample d) :
    Differentiable ℝ (fun z => ε * seedField d W z) :=
  (sharpSeed_contDiff ε W).differentiable (by simp)

/-- The first coordinate of the local gradient of a translated physical pair is the coordinate
derivative of the scaled seed at the translation point. -/
private theorem sharpLocalGradient_translate_coord (hd : 2 ≤ d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ∧
      densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) (y : Vec d) :
    sharpLocalGradient hd (translate y (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W))
        (⟨0, by omega⟩ : Fin d) =
      coordinateDerivative (⟨0, by omega⟩ : Fin d) (fun z => ε * seedField d W z) y :=
  congrFun (sharpLocalGradient_translate hd δ ε hgrad hμ W y) (⟨0, by omega⟩ : Fin d)

/-- Dominated differentiation of the seed mean along the coordinate line through `0`: the seed
values are bounded by `ε`, and their coordinate derivatives by `1/4`. -/
private theorem hasDerivAt_seedLineMean (i0 : Fin d) (ε : ℝ) (hε : 0 < ε)
    (P : Measure (NoiseSample d)) [IsProbabilityMeasure P]
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hF'm : ∀ t : ℝ, Measurable (fun W : NoiseSample d =>
      coordinateDerivative i0 (fun z => ε * seedField d W z) (t • unitVector i0)))
    (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ W, ε * seedField d W (t • unitVector i0) ∂P)
      (∫ W, coordinateDerivative i0 (fun z => ε * seedField d W z) (s • unitVector i0) ∂P) s := by
  have hmeas : ∀ t : ℝ,
      Measurable (fun W : NoiseSample d => ε * seedField d W (t • unitVector i0)) :=
    fun t => (measurable_seedField d (t • unitVector i0)).const_mul ε
  have hint : Integrable (fun W : NoiseSample d => ε * seedField d W (s • unitVector i0)) P :=
    Integrable.of_bound (hmeas s).aestronglyMeasurable ε
      (Filter.Eventually.of_forall fun W => by
        rw [Real.norm_eq_abs]; exact sharpSeed_abs_le hε W _)
  have hline : ∀ (t : ℝ) (W : NoiseSample d), HasDerivAt
      (fun u : ℝ => ε * seedField d W (u • unitVector i0))
      (coordinateDerivative i0 (fun z => ε * seedField d W z) (t • unitVector i0)) t :=
    fun t W => hasDerivAt_coordinate_line (fun z => ε * seedField d W z)
      (differentiable_scaledSeed ε W) i0 t
  have hbd : ∀ (t : ℝ) (W : NoiseSample d),
      ‖coordinateDerivative i0 (fun z => ε * seedField d W z) (t • unitVector i0)‖ ≤ 1 / 4 :=
    fun t W => by
      rw [Real.norm_eq_abs]
      exact abs_coordinateDerivative_le_quarter i0 (hgrad W _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
    (F := fun (t : ℝ) (W : NoiseSample d) => ε * seedField d W (t • unitVector i0))
    (F' := fun (t : ℝ) (W : NoiseSample d) =>
      coordinateDerivative i0 (fun z => ε * seedField d W z) (t • unitVector i0))
    (x₀ := s) (bound := fun _ => (1 / 4 : ℝ)) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hmeas t).aestronglyMeasurable) hint
    (hF'm s).aestronglyMeasurable
    (Filter.Eventually.of_forall fun W t _ => hbd t W)
    (integrable_const _)
    (Filter.Eventually.of_forall fun W t _ => hline t W)).2

/-- The seed mean along the coordinate line through `0` is bounded by `ε`. -/
private theorem abs_integral_seedLine_le (i0 : Fin d) (ε : ℝ) (hε : 0 < ε)
    (P : Measure (NoiseSample d)) [IsProbabilityMeasure P] (t : ℝ) :
    |∫ W, ε * seedField d W (t • unitVector i0) ∂P| ≤ ε := by
  have h := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun W : NoiseSample d => ε * seedField d W (t • unitVector i0)) (C := ε)
    (Filter.Eventually.of_forall fun W => by
      rw [Real.norm_eq_abs]; exact sharpSeed_abs_le hε W _)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

/-- Stationarity centres the first coordinate `G₁` of the local gradient. Along the coordinate line
through `0`, the seed mean has the constant derivative `𝔼G₁` (the translated values of `G₁` are
seed derivatives), and that mean is bounded by `ε`, so the derivative vanishes. -/
theorem integral_sharpLocalGradient_eq_zero (hd : 2 ≤ d) (δ ε : ℝ) (hε : 0 < ε)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ∧
      densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (P : Measure (NoiseSample d)) [IsProbabilityMeasure P]
    (Q : Measure (FieldPair d))
    (hQ : Q = P.map (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ))
    (hst : IsStationary Q) (hmeas : Measurable (sharpLocalGradient hd)) :
    ∫ ω, sharpLocalGradient hd ω (⟨0, by omega⟩ : Fin d) ∂Q = 0 := by
  have hpairMeas := measurable_sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ
  have hG1m : Measurable (fun ω : FieldPair d => sharpLocalGradient hd ω (⟨0, by omega⟩ : Fin d)) :=
    (measurable_pi_apply (⟨0, by omega⟩ : Fin d)).comp hmeas
  have hF'm : ∀ t : ℝ, Measurable (fun W : NoiseSample d =>
      coordinateDerivative (⟨0, by omega⟩ : Fin d) (fun z => ε * seedField d W z)
        (t • unitVector (⟨0, by omega⟩ : Fin d))) := fun t => by
    have hfun : (fun W : NoiseSample d => coordinateDerivative (⟨0, by omega⟩ : Fin d)
        (fun z => ε * seedField d W z) (t • unitVector (⟨0, by omega⟩ : Fin d))) =
        (fun ω : FieldPair d => sharpLocalGradient hd ω (⟨0, by omega⟩ : Fin d)) ∘
          (translate (t • unitVector (⟨0, by omega⟩ : Fin d)) ∘
            sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ) :=
      funext fun W => (sharpLocalGradient_translate_coord hd δ ε hgrad hμ W
        (t • unitVector (⟨0, by omega⟩ : Fin d))).symm
    rw [hfun]
    exact hG1m.comp ((EinsteinRelation.Probability.measurable_translate
      (t • unitVector (⟨0, by omega⟩ : Fin d))).comp hpairMeas)
  have hconst : ∀ s : ℝ,
      ∫ W, coordinateDerivative (⟨0, by omega⟩ : Fin d) (fun z => ε * seedField d W z)
        (s • unitVector (⟨0, by omega⟩ : Fin d)) ∂P =
        ∫ ω, sharpLocalGradient hd ω (⟨0, by omega⟩ : Fin d) ∂Q := by
    intro s
    have hpt : ∀ W : NoiseSample d, coordinateDerivative (⟨0, by omega⟩ : Fin d)
        (fun z => ε * seedField d W z) (s • unitVector (⟨0, by omega⟩ : Fin d)) =
        sharpLocalGradient hd (translate (s • unitVector (⟨0, by omega⟩ : Fin d))
          (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)) (⟨0, by omega⟩ : Fin d) :=
      fun W => (sharpLocalGradient_translate_coord hd δ ε hgrad hμ W
        (s • unitVector (⟨0, by omega⟩ : Fin d))).symm
    calc ∫ W, coordinateDerivative (⟨0, by omega⟩ : Fin d) (fun z => ε * seedField d W z)
          (s • unitVector (⟨0, by omega⟩ : Fin d)) ∂P
        = ∫ W, sharpLocalGradient hd (translate (s • unitVector (⟨0, by omega⟩ : Fin d))
            (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)) (⟨0, by omega⟩ : Fin d) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ∫ W, sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)
            (⟨0, by omega⟩ : Fin d) ∂P :=
          integral_pair_translate hpairMeas hQ hst hG1m (s • unitVector (⟨0, by omega⟩ : Fin d))
      _ = ∫ ω, sharpLocalGradient hd ω (⟨0, by omega⟩ : Fin d) ∂Q :=
          (integral_map_pair hpairMeas hQ hG1m).symm
  have hFderiv : ∀ s : ℝ, HasDerivAt
      (fun t : ℝ => ∫ W, ε * seedField d W (t • unitVector (⟨0, by omega⟩ : Fin d)) ∂P)
      (∫ ω, sharpLocalGradient hd ω (⟨0, by omega⟩ : Fin d) ∂Q) s :=
    fun s => (hasDerivAt_seedLineMean (⟨0, by omega⟩ : Fin d) ε hε P hgrad hF'm s).congr_deriv
      (hconst s)
  exact eq_zero_of_hasDerivAt_const_bounded hε hFderiv fun t =>
    abs_integral_seedLine_le (⟨0, by omega⟩ : Fin d) ε hε P t

/-! ### The mean identity for `a₁₁` -/

/-- Source `paper/main.tex` 1259–1265: `𝔼a₁₁ - 1 = 𝔼[|G|²/(1+G₁)]`, from the pointwise identity
`a₁₁ = 1 - G₁ + |G|²/(1+G₁)` and `𝔼G₁ = 0`. -/
theorem sharp_integral_a11_identity {d : ℕ} (hd : 2 ≤ d) (δ ε : ℝ) (hε : 0 < ε)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ∧
      densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (P : Measure (NoiseSample d)) [IsProbabilityMeasure P]
    (Q : Measure (FieldPair d))
    (hQ : Q = P.map (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ))
    (hst : IsStationary Q) (hmeas : Measurable (sharpLocalGradient hd)) :
    (∫ ω, sharpA11 hd ω 0 ∂Q) - 1 =
      ∫ ω, sharpEnergy (⟨0, by omega⟩ : Fin d) (sharpLocalGradient hd ω) ∂Q := by
  have hpairMeas := measurable_sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ
  have hAm : Measurable (fun ω : FieldPair d => sharpA11 hd ω 0) :=
    (continuous_reducedCoefficient_apply 0 (⟨0, by omega⟩ : Fin d) (⟨0, by omega⟩ : Fin d)).measurable
  have hEm : Measurable (fun ω : FieldPair d =>
      sharpEnergy (⟨0, by omega⟩ : Fin d) (sharpLocalGradient hd ω)) :=
    (measurable_sharpEnergy (⟨0, by omega⟩ : Fin d)).comp hmeas
  have hG0m : Measurable (fun ω : FieldPair d => sharpLocalGradient hd ω (⟨0, by omega⟩ : Fin d)) :=
    (measurable_pi_apply (⟨0, by omega⟩ : Fin d)).comp hmeas
  have hG0 := integral_sharpLocalGradient_eq_zero hd δ ε hε hgrad hμ P Q hQ hst hmeas
  have hA_P : ∫ ω, sharpA11 hd ω 0 ∂Q =
      ∫ W, sharpA11 hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W) 0 ∂P :=
    integral_map_pair hpairMeas hQ hAm
  have hE_P : ∫ ω, sharpEnergy (⟨0, by omega⟩ : Fin d) (sharpLocalGradient hd ω) ∂Q =
      ∫ W, sharpEnergy (⟨0, by omega⟩ : Fin d)
        (sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)) ∂P :=
    integral_map_pair hpairMeas hQ hEm
  have hG_P : ∫ ω, sharpLocalGradient hd ω (⟨0, by omega⟩ : Fin d) ∂Q =
      ∫ W, sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)
        (⟨0, by omega⟩ : Fin d) ∂P :=
    integral_map_pair hpairMeas hQ hG0m
  have hpt : (fun W : NoiseSample d => sharpA11 hd
      (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W) 0) =
      fun W => 1 - sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)
          (⟨0, by omega⟩ : Fin d) +
        sharpEnergy (⟨0, by omega⟩ : Fin d)
          (sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)) := by
    funext W
    rw [sharpLocalGradient_pair hd δ ε hgrad hμ W]
    exact sharpA11_pair hd δ ε hgrad hμ W
  have hG0bd : ∀ W : NoiseSample d,
      |sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)
        (⟨0, by omega⟩ : Fin d)| ≤ 1 / 4 := by
    intro W
    rw [sharpLocalGradient_pair hd δ ε hgrad hμ W]
    exact abs_coordinateDerivative_le_quarter (⟨0, by omega⟩ : Fin d) (hgrad W 0)
  have hG0Pm : Measurable (fun W : NoiseSample d =>
      sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)
        (⟨0, by omega⟩ : Fin d)) := hG0m.comp hpairMeas
  have hEPm : Measurable (fun W : NoiseSample d =>
      sharpEnergy (⟨0, by omega⟩ : Fin d)
        (sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W))) :=
    hEm.comp hpairMeas
  have hG0int : Integrable (fun W : NoiseSample d =>
      sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)
        (⟨0, by omega⟩ : Fin d)) P :=
    Integrable.of_bound hG0Pm.aestronglyMeasurable (1 / 4)
      (Filter.Eventually.of_forall fun W => by
        rw [Real.norm_eq_abs]; exact hG0bd W)
  have hEint : Integrable (fun W : NoiseSample d =>
      sharpEnergy (⟨0, by omega⟩ : Fin d)
        (sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W))) P := by
    refine Integrable.of_bound hEPm.aestronglyMeasurable (d : ℝ)
      (Filter.Eventually.of_forall fun W => ?_)
    show ‖sharpEnergy (⟨0, by omega⟩ : Fin d)
        (sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W))‖ ≤ d
    rw [sharpLocalGradient_pair hd δ ε hgrad hμ W, Real.norm_eq_abs, abs_le]
    obtain ⟨h0, hle⟩ := sharpEnergy_bounds (⟨0, by omega⟩ : Fin d)
      (gradient (fun z => ε * seedField d W z) 0) (mem_gradBox.1 (gradient_mem_gradBox (hgrad W 0)))
    exact ⟨by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)], hle⟩
  have h1int : Integrable (fun W : NoiseSample d =>
      (1 : ℝ) - sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)
        (⟨0, by omega⟩ : Fin d)) P :=
    (integrable_const 1).sub hG0int
  have hint : ∫ W, sharpA11 hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W) 0 ∂P =
      1 - ∫ W, sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)
        (⟨0, by omega⟩ : Fin d) ∂P +
      ∫ W, sharpEnergy (⟨0, by omega⟩ : Fin d)
        (sharpLocalGradient hd (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ W)) ∂P := by
    have hI1 := integral_add h1int hEint
    have hI2 := integral_sub (integrable_const (1 : ℝ)) hG0int
    rw [hpt, hI1, hI2]
    simp
  linarith

/-! ### Assembly: the sharp environment input -/

/-- The two mean identities of the sharp environment input, from the sharp law `IsSharpLaw` and the
four corrector items: measurability and the `1/4` bound of the local gradient, its positivity
energy, and `ā e₁ = e₁`. Source `paper/main.tex` 1231 and 1259–1265. -/
theorem sharpEnvironmentInput_of_corrector {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (δ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (hsharp : IsSharpLaw hd δ Q)
    (hmeas : Measurable (sharpLocalGradient hd))
    (hbound : ∀ᵐ ω ∂Q.measure, euclideanNorm (sharpLocalGradient hd ω) ≤ 1 / 4)
    (hpos : 0 < ∫ ω, sharpEnergy (⟨0, by omega⟩ : Fin d) (sharpLocalGradient hd ω) ∂Q.measure)
    (hab : (abar Q).mulVec (unitVector (⟨0, by omega⟩ : Fin d)) =
      unitVector (⟨0, by omega⟩ : Fin d)) :
    SharpEnvironmentInput hd Q := by
  unfold IsSharpLaw at hsharp
  obtain ⟨_hδ, ε, P, hgrad, hμ, hε, hQ⟩ := hsharp
  have hpairMeas := measurable_sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ
  haveI : IsProbabilityMeasure P := by
    constructor
    have h := Q.probability.measure_univ
    rw [hQ, Measure.map_apply hpairMeas MeasurableSet.univ] at h
    simpa using h
  unfold SharpEnvironmentInput
  refine ⟨hmeas, hbound, ?_, hpos, ?_, hab⟩
  · exact sharp_integral_a11_identity hd δ ε hε hgrad hμ P Q.measure hQ Q.stationary hmeas
  · exact sharp_meanMu_eq_one (⟨0, by omega⟩ : Fin d) δ ε hε hgrad hμ P Q.measure hQ Q.stationary

end EinsteinRelation.Sharpness
