import EinsteinRelation.Correctors.HorizontalH1EuclideanGradient
import EinsteinRelation.Correctors.HorizontalH1GradientLinear
import EinsteinRelation.Correctors.HorizontalH1GradientMeanZero
import EinsteinRelation.Correctors.VariationalClosure
import EinsteinRelation.Environment.Bounds
import EinsteinRelation.Correctors.EllipticOperatorBound
import EinsteinRelation.Probability.ReductionLocality
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-! # Stationary corrector gradient carriers -/

open MeasureTheory

namespace EinsteinRelation.Correctors

noncomputable section

private theorem inv_exp_two_mul_mul (L : ℝ) :
    (Real.exp (2 * L) * L)⁻¹ = Real.exp (-2 * L) * L⁻¹ := by
  have h : Real.exp (-2 * L) = (Real.exp (2 * L))⁻¹ := by
    rw [← Real.exp_neg, neg_mul]
  rw [mul_inv, h]

private theorem continuous_originMatrix {d : ℕ} :
    Continuous (fun ω : FieldPair d => ω.1 (0 : Vec d)) :=
  (continuous_eval_const (0 : Vec d)).comp continuous_fst

private def matrixActionPair {d : ℕ}
    (p : Mat d × EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (p.1.mulVec p.2.ofLp)

private theorem continuous_matrixActionPair {d : ℕ} :
    Continuous (matrixActionPair (d := d)) := by
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℝ)).comp
    (continuous_fst.matrix_mulVec
      ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).comp
        continuous_snd))

private theorem euclideanNorm_eq_toLp_norm_local {d : ℕ} (v : Vec d) :
    euclideanNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclideanNorm euclideanSq dot
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.norm_eq_abs, pow_two]
  exact (abs_mul_abs_self (v i)).symm

private theorem matrixActionPair_norm_le {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ)
    {M : Mat d} (hM : IsElliptic Λ (fun _ : Vec d => M))
    (u : EuclideanSpace ℝ (Fin d)) :
    ‖matrixActionPair (M, u)‖ ≤ Λ * ‖u‖ := by
  have h := isElliptic_mulVec_euclideanNorm_le hΛ hM 0 u.ofLp
  calc
    ‖matrixActionPair (M, u)‖ = euclideanNorm (M.mulVec u.ofLp) := by
      rw [matrixActionPair, euclideanNorm_eq_toLp_norm_local]
    _ ≤ Λ * euclideanNorm u.ofLp := h
    _ = Λ * ‖u‖ := by
      rw [euclideanNorm_eq_toLp_norm_local]

private theorem continuous_dot_mulVec_origin {d : ℕ} (ξ : Vec d) :
    Continuous (fun ω : FieldPair d => dot ξ ((ω.1 (0 : Vec d)).mulVec ξ)) := by
  have hmul : Continuous (fun M : Mat d => M.mulVec ξ) :=
    continuous_id.matrix_mulVec continuous_const
  show Continuous fun (ω : FieldPair d) => ∑ i, ξ i * ((ω.1 0).mulVec ξ) i
  exact continuous_finset_sum _ fun i _ =>
    continuous_const.mul ((continuous_apply i).comp (hmul.comp continuous_originMatrix))

private theorem isClosed_isElliptic_origin {d : ℕ} (Λ : ℝ) :
    IsClosed {ω : FieldPair d | IsElliptic Λ (fun _ => ω.1 (0 : Vec d))} := by
  have hset : {ω : FieldPair d | IsElliptic Λ (fun _ => ω.1 0)} =
      {ω | (ω.1 0).transpose = ω.1 0} ∩
        ⋂ ξ : Vec d, {ω | Λ⁻¹ * euclideanSq ξ ≤ dot ξ ((ω.1 0).mulVec ξ)} ∩
          {ω | dot ξ ((ω.1 0).mulVec ξ) ≤ Λ * euclideanSq ξ} := by
    ext ω
    simp [IsElliptic]
  rw [hset]
  refine IsClosed.inter ?_ (isClosed_iInter fun ξ => IsClosed.inter ?_ ?_)
  · exact isClosed_eq (continuous_originMatrix.matrix_transpose) continuous_originMatrix
  · exact isClosed_le continuous_const (continuous_dot_mulVec_origin ξ)
  · exact isClosed_le (continuous_dot_mulVec_origin ξ) continuous_const

private theorem reducedMatrixField_elliptic_of_regular {d : ℕ} {Λ₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω) :
    IsElliptic (Real.exp (2 * Λ₀) * Λ₀) (fun x => reducedMatrixField ω x) := by
  intro x
  refine ⟨reducedCoefficient_transpose ω x (hω.1 x).1, fun ξ => ?_⟩
  rw [inv_exp_two_mul_mul Λ₀]
  exact reducedCoefficient_energy_bounds ω x ξ Λ₀ hΛ₀ hω

/-- The actual environment law after the time change of paper/main.tex:198-207. -/
noncomputable def reducedEnvironmentLaw {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : Measure (FieldPair d) :=
  Measure.map reduce Q.measure

theorem reducedEnvironmentLaw_stationary {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    IsStationary (reducedEnvironmentLaw Q) :=
  Probability.isStationary_map_reduce Q.measure Q.stationary

instance reducedEnvironmentLaw_isProbabilityMeasure {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : IsProbabilityMeasure (reducedEnvironmentLaw Q) :=
  by unfold reducedEnvironmentLaw; infer_instance

/-- Ellipticity of the actual coefficient at the origin under the time changed law.
The estimate is transported from the physical regularity event through `reduce`. -/
theorem ae_reducedEnvironmentLaw_origin_elliptic {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      IsElliptic (Real.exp (2 * Λ₀) * Λ₀) (fun _ => ω.1 (0 : Vec d)) := by
  rw [reducedEnvironmentLaw]
  rw [ae_map_iff Probability.measurable_reduce.aemeasurable
    (isClosed_isElliptic_origin (Real.exp (2 * Λ₀) * Λ₀)).measurableSet]
  filter_upwards [Q.regular] with ω hω
  have hred := reducedMatrixField_elliptic_of_regular Q.ellipticity_parameter hω
  intro x
  simpa [reduce, reducedMatrixField] using hred 0

private def originMatrixActionFun {d : ℕ} {Q : Measure (FieldPair d)}
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) : FieldPair d → EuclideanSpace ℝ (Fin d) :=
  fun ω => matrixActionPair (ω.1 0, u ω)

private theorem originMatrixAction_aestronglyMeasurable {d : ℕ}
    {Q : Measure (FieldPair d)} (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    AEStronglyMeasurable (originMatrixActionFun u) Q := by
  have hPseudo : TopologicalSpace.PseudoMetrizableSpace (Mat d) := by
    change TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ)
    exact inferInstance
  have hSecond : SecondCountableTopology (Mat d) := by
    change SecondCountableTopology (Fin d → Fin d → ℝ)
    exact inferInstance
  apply continuous_matrixActionPair.comp_aestronglyMeasurable
  exact (continuous_originMatrix.measurable.aestronglyMeasurable.prodMk
    (Lp.aestronglyMeasurable u))

private theorem originMatrixAction_memLp {d : ℕ} {Q : Measure (FieldPair d)}
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hEll : ∀ᵐ ω ∂Q, IsElliptic Λ (fun _ : Vec d => ω.1 0))
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    MemLp (originMatrixActionFun u) 2 Q := by
  apply (Lp.memLp u).of_le_mul (originMatrixAction_aestronglyMeasurable u)
  filter_upwards [hEll] with ω hω
  exact matrixActionPair_norm_le hΛ hω (u ω)

private noncomputable def originMatrixActionLp {d : ℕ} {Q : Measure (FieldPair d)}
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hEll : ∀ᵐ ω ∂Q, IsElliptic Λ (fun _ : Vec d => ω.1 0))
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) : Lp (EuclideanSpace ℝ (Fin d)) 2 Q :=
  (originMatrixAction_memLp hΛ hEll u).toLp (originMatrixActionFun u)

private theorem originMatrixActionLp_coeFn {d : ℕ} {Q : Measure (FieldPair d)}
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hEll : ∀ᵐ ω ∂Q, IsElliptic Λ (fun _ : Vec d => ω.1 0))
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    (fun ω => originMatrixActionLp hΛ hEll u ω) =ᵐ[Q] originMatrixActionFun u :=
  (originMatrixAction_memLp hΛ hEll u).coeFn_toLp

private theorem matrixActionPair_add {d : ℕ} (M : Mat d)
    (u v : EuclideanSpace ℝ (Fin d)) :
    matrixActionPair (M, u + v) = matrixActionPair (M, u) + matrixActionPair (M, v) := by
  simp [matrixActionPair, Matrix.mulVec_add]

private theorem matrixActionPair_smul {d : ℕ} (M : Mat d) (c : ℝ)
    (u : EuclideanSpace ℝ (Fin d)) :
    matrixActionPair (M, c • u) = c • matrixActionPair (M, u) := by
  simp [matrixActionPair, Matrix.mulVec_smul]

private noncomputable def originCoefficientAction {d : ℕ} {Q : Measure (FieldPair d)}
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hEll : ∀ᵐ ω ∂Q, IsElliptic Λ (fun _ : Vec d => ω.1 0)) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 Q →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin d)) 2 Q where
  toFun := originMatrixActionLp hΛ hEll
  map_add' := by
    intro u v
    apply Lp.ext
    filter_upwards [originMatrixActionLp_coeFn hΛ hEll (u + v),
      originMatrixActionLp_coeFn hΛ hEll u, originMatrixActionLp_coeFn hΛ hEll v,
      Lp.coeFn_add u v, Lp.coeFn_add (originMatrixActionLp hΛ hEll u)
        (originMatrixActionLp hΛ hEll v)] with ω hsum hu hv hin hout
    calc
      originMatrixActionLp hΛ hEll (u + v) ω =
          matrixActionPair (ω.1 0, (u + v) ω) := hsum
      _ = matrixActionPair (ω.1 0, u ω) + matrixActionPair (ω.1 0, v ω) := by
        rw [hin]
        exact matrixActionPair_add _ _ _
      _ = (originMatrixActionLp hΛ hEll u + originMatrixActionLp hΛ hEll v) ω := by
        change originMatrixActionFun u ω + originMatrixActionFun v ω = _
        rw [← hu, ← hv]
        exact hout.symm
  map_smul' := by
    intro c u
    apply Lp.ext
    filter_upwards [originMatrixActionLp_coeFn hΛ hEll (c • u),
      originMatrixActionLp_coeFn hΛ hEll u, Lp.coeFn_smul c u,
      Lp.coeFn_smul c (originMatrixActionLp hΛ hEll u)] with ω hsmul hu hin hout
    calc
      originMatrixActionLp hΛ hEll (c • u) ω =
          matrixActionPair (ω.1 0, (c • u) ω) := hsmul
      _ = c • matrixActionPair (ω.1 0, u ω) := by
        rw [hin]
        exact matrixActionPair_smul _ _ _
      _ = (c • originMatrixActionLp hΛ hEll u) ω := by
        change c • originMatrixActionFun u ω = _
        rw [← hu]
        exact hout.symm

private theorem norm_originCoefficientAction {d : ℕ} {Q : Measure (FieldPair d)}
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hEll : ∀ᵐ ω ∂Q, IsElliptic Λ (fun _ : Vec d => ω.1 0))
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    ‖originCoefficientAction hΛ hEll u‖ ≤ Λ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hEll, originMatrixActionLp_coeFn hΛ hEll u] with ω hω hcoe
  change ‖originMatrixActionLp hΛ hEll u ω‖ ≤ Λ * ‖u ω‖
  rw [hcoe]
  exact matrixActionPair_norm_le hΛ hω (u ω)

private noncomputable def originCoefficientActionCLM {d : ℕ} {Q : Measure (FieldPair d)}
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hEll : ∀ᵐ ω ∂Q, IsElliptic Λ (fun _ : Vec d => ω.1 0)) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 Q →L[ℝ] Lp (EuclideanSpace ℝ (Fin d)) 2 Q :=
  (originCoefficientAction hΛ hEll).mkContinuous Λ (norm_originCoefficientAction hΛ hEll)

/-- Bounded multiplication by the actual reduced coefficient at the origin. -/
noncomputable def reducedOriginCoefficientAction {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
  originCoefficientActionCLM
    (mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter))
    (ae_reducedEnvironmentLaw_origin_elliptic Q)

/-- The reduced origin coefficient action acts pointwise by the coefficient at the origin. -/
theorem reducedOriginCoefficientAction_coeFn {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      (reducedOriginCoefficientAction Q u ω).ofLp = (ω.1 0).mulVec (u ω).ofLp := by
  have hΛ := mul_pos (Real.exp_pos (2 * Λ₀)) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  filter_upwards [originMatrixActionLp_coeFn hΛ (ae_reducedEnvironmentLaw_origin_elliptic Q) u]
    with ω hcoe
  change (originMatrixActionLp hΛ (ae_reducedEnvironmentLaw_origin_elliptic Q) u ω).ofLp = _
  rw [hcoe]
  rfl

theorem norm_reducedOriginCoefficientAction_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    ‖reducedOriginCoefficientAction Q u‖ ≤
      (Real.exp (2 * Λ₀) * Λ₀) * ‖u‖ := by
  exact norm_originCoefficientAction
    (mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter))
    (ae_reducedEnvironmentLaw_origin_elliptic Q) u

/-- Almost everywhere, the reduced coefficient action multiplies the pointwise norm by at most
`e^{2Λ₀} Λ₀`. -/
theorem ae_norm_reducedOriginCoefficientAction_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      ‖reducedOriginCoefficientAction Q u ω‖ ≤ (Real.exp (2 * Λ₀) * Λ₀) * ‖u ω‖ := by
  have hΛ := mul_pos (Real.exp_pos (2 * Λ₀)) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  filter_upwards [ae_reducedEnvironmentLaw_origin_elliptic Q,
    originMatrixActionLp_coeFn hΛ (ae_reducedEnvironmentLaw_origin_elliptic Q) u] with ω hω hcoe
  change ‖originMatrixActionLp hΛ (ae_reducedEnvironmentLaw_origin_elliptic Q) u ω‖ ≤ _
  rw [hcoe]
  exact matrixActionPair_norm_le hΛ hω (u ω)

/-- The Euclidean representative of the horizontal gradient is unique because its
coordinates are the unique strong L2 translation generators. -/
theorem existsUnique_horizontalEuclideanGradient {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (f : horizontalH1 Q hQ) :
    ∃! g : Lp (EuclideanSpace ℝ (Fin d)) 2 Q,
      ∀ i : Fin d, (fun ω => g ω i) =ᵐ[Q]
        (horizontalH1Gradient Q hQ f i : FieldPair d → ℝ) := by
  obtain ⟨g, hg, _⟩ := exists_euclidean_horizontalH1Gradient Q hQ f
  refine ⟨g, hg, ?_⟩
  intro h hh
  apply Lp.ext
  have hcoord : ∀ i : Fin d, (fun ω => h ω i) =ᵐ[Q] (fun ω => g ω i) := by
    intro i
    exact (hh i).trans (hg i).symm
  filter_upwards [ae_all_iff.2 hcoord] with ω hω
  ext i
  exact hω i

/-- The uniquely determined Euclidean-valued representative of the horizontal gradient.
Its coordinates are the strong L2 generators defining H1(Q). -/
noncomputable def horizontalEuclideanGradient {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (f : horizontalH1 Q hQ) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 Q :=
  Classical.choose (existsUnique_horizontalEuclideanGradient Q hQ f)

theorem horizontalEuclideanGradient_coordinates {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (f : horizontalH1 Q hQ) (i : Fin d) :
    (fun ω => horizontalEuclideanGradient Q hQ f ω i) =ᵐ[Q]
      (horizontalH1Gradient Q hQ f i : FieldPair d → ℝ) :=
  (Classical.choose_spec (existsUnique_horizontalEuclideanGradient Q hQ f)).1 i

/-- Additivity of the Euclidean assembly follows from the coordinate generator identity. -/
theorem horizontalEuclideanGradient_add {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (f g : horizontalH1 Q hQ) :
    horizontalEuclideanGradient Q hQ (f + g) =
      horizontalEuclideanGradient Q hQ f + horizontalEuclideanGradient Q hQ g := by
  apply Lp.ext
  have hcoord : ∀ i : Fin d,
      (fun ω => horizontalEuclideanGradient Q hQ (f + g) ω i) =ᵐ[Q]
        (fun ω => (horizontalEuclideanGradient Q hQ f +
          horizontalEuclideanGradient Q hQ g) ω i) := by
    intro i
    filter_upwards [horizontalEuclideanGradient_coordinates Q hQ (f + g) i,
      horizontalEuclideanGradient_coordinates Q hQ f i,
      horizontalEuclideanGradient_coordinates Q hQ g i,
      Lp.coeFn_add (horizontalH1Gradient Q hQ f i) (horizontalH1Gradient Q hQ g i),
      Lp.coeFn_add (horizontalEuclideanGradient Q hQ f)
        (horizontalEuclideanGradient Q hQ g)] with ω hfg hf hg hDcoe hadd
    have hD := EinsteinRelation.horizontalH1Gradient_add Q hQ f g i
    have hDω := congrArg (fun u : Lp ℝ 2 Q => u ω) hD
    calc
      horizontalEuclideanGradient Q hQ (f + g) ω i =
          horizontalH1Gradient Q hQ (f + g) i ω := hfg
      _ = (horizontalH1Gradient Q hQ f i + horizontalH1Gradient Q hQ g i) ω := hDω
      _ = horizontalH1Gradient Q hQ f i ω + horizontalH1Gradient Q hQ g i ω := hDcoe
      _ = (horizontalEuclideanGradient Q hQ f +
          horizontalEuclideanGradient Q hQ g) ω i := by
            rw [← hf, ← hg]
            calc
              _ = (horizontalEuclideanGradient Q hQ f ω +
                  horizontalEuclideanGradient Q hQ g ω).ofLp i :=
                (PiLp.add_apply (fun _ : Fin d => ℝ)
                  (horizontalEuclideanGradient Q hQ f ω)
                  (horizontalEuclideanGradient Q hQ g ω) i).symm
              _ = (horizontalEuclideanGradient Q hQ f +
                  horizontalEuclideanGradient Q hQ g) ω i :=
                congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) hadd.symm
  filter_upwards [ae_all_iff.2 hcoord] with ω hω
  ext i
  exact hω i

/-- Homogeneity of the Euclidean assembly follows from the coordinate generator identity. -/
theorem horizontalEuclideanGradient_smul {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (c : ℝ) (f : horizontalH1 Q hQ) :
    horizontalEuclideanGradient Q hQ (c • f) =
      c • horizontalEuclideanGradient Q hQ f := by
  apply Lp.ext
  have hcoord : ∀ i : Fin d,
      (fun ω => horizontalEuclideanGradient Q hQ (c • f) ω i) =ᵐ[Q]
        (fun ω => (c • horizontalEuclideanGradient Q hQ f) ω i) := by
    intro i
    filter_upwards [horizontalEuclideanGradient_coordinates Q hQ (c • f) i,
      horizontalEuclideanGradient_coordinates Q hQ f i,
      Lp.coeFn_smul c (horizontalH1Gradient Q hQ f i),
      Lp.coeFn_smul c (horizontalEuclideanGradient Q hQ f)] with ω hcf hf hDcoe hsmul
    have hD := EinsteinRelation.horizontalH1Gradient_smul Q hQ c f i
    have hDω := congrArg (fun u : Lp ℝ 2 Q => u ω) hD
    calc
      horizontalEuclideanGradient Q hQ (c • f) ω i =
          horizontalH1Gradient Q hQ (c • f) i ω := hcf
      _ = (c • horizontalH1Gradient Q hQ f i) ω := hDω
      _ = c • horizontalH1Gradient Q hQ f i ω := hDcoe
      _ = (c • horizontalEuclideanGradient Q hQ f) ω i := by
            rw [← hf]
            calc
              _ = (c • horizontalEuclideanGradient Q hQ f ω).ofLp i :=
                (PiLp.smul_apply (fun _ : Fin d => ℝ) c
                  (horizontalEuclideanGradient Q hQ f ω) i).symm
              _ = (c • horizontalEuclideanGradient Q hQ f) ω i :=
                congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) hsmul.symm
  filter_upwards [ae_all_iff.2 hcoord] with ω hω
  ext i
  exact hω i

/-- The actual horizontal gradients form a linear subspace of Euclidean-valued L². -/
noncomputable def horizontalEuclideanGradientMap {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) :
    horizontalH1 Q hQ →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin d)) 2 Q where
  toFun := horizontalEuclideanGradient Q hQ
  map_add' := horizontalEuclideanGradient_add Q hQ
  map_smul' := horizontalEuclideanGradient_smul Q hQ

/-- The stationary potential-gradient domain: the L2 closure of the actual horizontal
gradients of H1(Q) observables. The closure is in the Euclidean-valued L2 norm. -/
def stationaryPotentialGradientSubmodule {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) : Submodule ℝ (Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :=
  (LinearMap.range (horizontalEuclideanGradientMap Q hQ)).topologicalClosure

abbrev stationaryPotentialGradients {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) : Set (Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :=
  stationaryPotentialGradientSubmodule Q hQ

theorem isClosed_stationaryPotentialGradients {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) : IsClosed (stationaryPotentialGradients Q hQ) := by
  change IsClosed ((LinearMap.range (horizontalEuclideanGradientMap Q hQ)).topologicalClosure).carrier
  exact Submodule.isClosed_topologicalClosure _

/-- First consumer: every actual H1(Q) horizontal gradient belongs to the closed
stationary potential-gradient domain. -/
theorem horizontalEuclideanGradient_mem_stationaryPotentialGradients {d : ℕ}
    (Q : Measure (FieldPair d)) (hQ : IsStationary Q) (f : horizontalH1 Q hQ) :
    horizontalEuclideanGradient Q hQ f ∈ stationaryPotentialGradients Q hQ :=
  Submodule.le_topologicalClosure _ ⟨f, rfl⟩

/-- The coordinate mean on Euclidean-valued L² is continuous, using the actual coordinate
projection and the probability-law L² expectation. -/
noncomputable def euclideanCoordinateMean {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (i : Fin d) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 Q →L[ℝ] ℝ :=
  (EinsteinRelation.l2Expectation Q).comp
    ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).compLpL 2 Q)

/-- Each actual horizontal gradient has zero coordinate expectation. -/
theorem horizontalEuclideanGradient_mean_zero {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (f : horizontalH1 Q hQ) (i : Fin d) :
    euclideanCoordinateMean Q i (horizontalEuclideanGradient Q hQ f) = 0 := by
  rw [euclideanCoordinateMean, ContinuousLinearMap.comp_apply,
    EinsteinRelation.l2Expectation_apply]
  have hfull :
      (fun ω => ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).compLpL 2 Q
        (horizontalEuclideanGradient Q hQ f)) ω) =ᵐ[Q]
          (horizontalH1Gradient Q hQ f i : FieldPair d → ℝ) := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL
        (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i)
        (horizontalEuclideanGradient Q hQ f) (p := 2) (μ := Q),
      horizontalEuclideanGradient_coordinates Q hQ f i] with ω hcomp hcoord
    simpa only [PiLp.proj_apply] using hcomp.trans hcoord
  rw [integral_congr_ae hfull]
  exact EinsteinRelation.Correctors.integral_horizontalH1Gradient_eq_zero Q hQ f i

/-- Mean-zero characterization: every vector in the closed stationary potential-gradient
submodule has zero expectation in every coordinate. -/
theorem stationaryPotentialGradient_mean_zero {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (U : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hU : U ∈ stationaryPotentialGradientSubmodule Q hQ) (i : Fin d) :
    euclideanCoordinateMean Q i U = 0 := by
  change U ∈ (LinearMap.range (horizontalEuclideanGradientMap Q hQ)).topologicalClosure at hU
  have hrange : LinearMap.range (horizontalEuclideanGradientMap Q hQ) ≤
      LinearMap.ker ((euclideanCoordinateMean Q i).toLinearMap) := by
    rintro V ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    exact horizontalEuclideanGradient_mean_zero Q hQ f i
  have hclosed : IsClosed
      (LinearMap.ker ((euclideanCoordinateMean Q i).toLinearMap)).carrier := by
    exact ContinuousLinearMap.isClosed_ker (euclideanCoordinateMean Q i)
  have hmem := (LinearMap.range (horizontalEuclideanGradientMap Q hQ)).topologicalClosure_minimal
    hrange hclosed hU
  exact LinearMap.mem_ker.mp hmem

/-- The domain uses the literal reduced law induced by the physical environment law. -/
abbrev correctorPotentialDomain {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :=
  stationaryPotentialGradientSubmodule (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q)

theorem correctorPotentialDomain_mean_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (hG : G ∈ correctorPotentialDomain Q) (i : Fin d) :
    euclideanCoordinateMean (reducedEnvironmentLaw Q) i G = 0 :=
  stationaryPotentialGradient_mean_zero (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) G hG i

end

end EinsteinRelation.Correctors
