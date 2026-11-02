import EinsteinRelation.Correctors.StationaryGradientDomainSupport
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.Holder

open MeasureTheory

/-! Intrinsic construction for the stationary corrector gradient and expected flux column
from `paper/main.tex:693-698`. The potential domain is reused from
`StationaryGradientDomainSupport`. -/

namespace EinsteinRelation.Correctors

noncomputable section

private theorem continuous_originMatrix {d : ℕ} :
    Continuous (fun ω : FieldPair d => ω.1 (0 : Vec d)) :=
  (continuous_eval_const (0 : Vec d)).comp continuous_fst

private def canonicalMatrixActionPair {d : ℕ}
    (p : Mat d × EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (p.1.mulVec p.2.ofLp)

private theorem continuous_canonicalMatrixActionPair {d : ℕ} :
    Continuous (canonicalMatrixActionPair (d := d)) := by
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

private theorem canonicalMatrixActionPair_norm_le {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ)
    {M : Mat d} (hM : IsElliptic Λ (fun _ : Vec d => M))
    (u : EuclideanSpace ℝ (Fin d)) :
    ‖canonicalMatrixActionPair (M, u)‖ ≤ Λ * ‖u‖ := by
  have h := isElliptic_mulVec_euclideanNorm_le hΛ hM 0 u.ofLp
  calc
    ‖canonicalMatrixActionPair (M, u)‖ = euclideanNorm (M.mulVec u.ofLp) := by
      rw [canonicalMatrixActionPair, euclideanNorm_eq_toLp_norm_local]
    _ ≤ Λ * euclideanNorm u.ofLp := h
    _ = Λ * ‖u‖ := by
      rw [euclideanNorm_eq_toLp_norm_local]

private def canonicalOriginMatrixActionFun {d : ℕ} {Q : Measure (FieldPair d)}
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) : FieldPair d → EuclideanSpace ℝ (Fin d) :=
  fun ω => canonicalMatrixActionPair (ω.1 0, u ω)

private theorem canonicalOriginMatrixAction_aestronglyMeasurable {d : ℕ}
    {Q : Measure (FieldPair d)} (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    AEStronglyMeasurable (canonicalOriginMatrixActionFun u) Q := by
  have hPseudo : TopologicalSpace.PseudoMetrizableSpace (Mat d) := by
    change TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ)
    exact inferInstance
  have hSecond : SecondCountableTopology (Mat d) := by
    change SecondCountableTopology (Fin d → Fin d → ℝ)
    exact inferInstance
  apply continuous_canonicalMatrixActionPair.comp_aestronglyMeasurable
  exact (continuous_originMatrix.measurable.aestronglyMeasurable.prodMk
    (Lp.aestronglyMeasurable u))

private theorem canonicalOriginMatrixAction_memLp {d : ℕ} {Q : Measure (FieldPair d)}
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hEll : ∀ᵐ ω ∂Q, IsElliptic Λ (fun _ : Vec d => ω.1 0))
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    MemLp (canonicalOriginMatrixActionFun u) 2 Q := by
  apply (Lp.memLp u).of_le_mul (canonicalOriginMatrixAction_aestronglyMeasurable u)
  filter_upwards [hEll] with ω hω
  exact canonicalMatrixActionPair_norm_le hΛ hω (u ω)

private noncomputable def canonicalOriginMatrixActionLp {d : ℕ} {Q : Measure (FieldPair d)}
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hEll : ∀ᵐ ω ∂Q, IsElliptic Λ (fun _ : Vec d => ω.1 0))
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) : Lp (EuclideanSpace ℝ (Fin d)) 2 Q :=
  (canonicalOriginMatrixAction_memLp hΛ hEll u).toLp (canonicalOriginMatrixActionFun u)

private theorem canonicalOriginMatrixActionLp_coeFn {d : ℕ} {Q : Measure (FieldPair d)}
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hEll : ∀ᵐ ω ∂Q, IsElliptic Λ (fun _ : Vec d => ω.1 0))
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    (fun ω => canonicalOriginMatrixActionLp hΛ hEll u ω) =ᵐ[Q] canonicalOriginMatrixActionFun u :=
  (canonicalOriginMatrixAction_memLp hΛ hEll u).coeFn_toLp



private noncomputable def canonicalOriginMatrixActionForQ {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
  canonicalOriginMatrixActionLp
    (mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter))
    (ae_reducedEnvironmentLaw_origin_elliptic Q) u

private theorem canonicalOriginMatrixActionForQ_eq_existing {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    canonicalOriginMatrixActionForQ Q u = reducedOriginCoefficientAction Q u := by
  rfl

private theorem reducedOriginCoefficientAction_coe_bridge {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    (fun ω => reducedOriginCoefficientAction Q u ω) =ᵐ[reducedEnvironmentLaw Q]
      (fun ω => canonicalMatrixActionPair (ω.1 0, u ω)) := by
  rw [← canonicalOriginMatrixActionForQ_eq_existing]
  exact canonicalOriginMatrixActionLp_coeFn
    (mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter))
    (ae_reducedEnvironmentLaw_origin_elliptic Q) u

/-- The reduced ellipticity parameter inherited from the original environment law. -/
def correctorEllipticityConstant {d : ℕ} {Λ₀ r₀ : ℝ}
    (_Q : EnvironmentLaw d Λ₀ r₀) : ℝ := Real.exp (2 * Λ₀) * Λ₀

theorem correctorEllipticityConstant_pos {d : ℕ} {Λ₀ r₀ : ℝ}
    (_Q : EnvironmentLaw d Λ₀ r₀) : 0 < correctorEllipticityConstant _Q := by
  unfold correctorEllipticityConstant
  exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one _Q.ellipticity_parameter)

private theorem inner_canonicalMatrixActionPair_symm {d : ℕ} (M : Mat d)
    (hM : M.transpose = M) (u v : EuclideanSpace ℝ (Fin d)) :
    inner ℝ u (canonicalMatrixActionPair (M, v)) =
      inner ℝ (canonicalMatrixActionPair (M, u)) v := by
  have hdot : dot u.ofLp (M.mulVec v.ofLp) = dot (M.mulVec u.ofLp) v.ofLp := by
    change dotProduct u.ofLp (M.mulVec v.ofLp) =
      dotProduct (M.mulVec u.ofLp) v.ofLp
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hM]
  have hleft : inner ℝ u (canonicalMatrixActionPair (M, v)) =
      dot u.ofLp (M.mulVec v.ofLp) := by
    simp [canonicalMatrixActionPair, dot, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hright : inner ℝ (canonicalMatrixActionPair (M, u)) v =
      dot (M.mulVec u.ofLp) v.ofLp := by
    simp [canonicalMatrixActionPair, dot, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  rw [hleft, hright, hdot]

private theorem inner_canonicalMatrixActionPair_self_eq_dot {d : ℕ} (M : Mat d)
    (u : EuclideanSpace ℝ (Fin d)) :
    inner ℝ u (canonicalMatrixActionPair (M, u)) = dot u.ofLp (M.mulVec u.ofLp) := by
  simp [canonicalMatrixActionPair, dot, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

private theorem euclideanSq_ofLp_eq_norm_sq {d : ℕ}
    (u : EuclideanSpace ℝ (Fin d)) : euclideanSq u.ofLp = ‖u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [euclideanSq, dot, Real.norm_eq_abs, pow_two]

private theorem norm_sq_eq_integral_norm_sq_corrector {d : ℕ}
    {Q : Measure (FieldPair d)} (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    ‖u‖ ^ 2 = ∫ ω, ‖u ω‖ ^ 2 ∂Q := by
  calc
    ‖u‖ ^ 2 = inner ℝ u u := (real_inner_self_eq_norm_sq u).symm
    _ = ∫ ω, inner ℝ (u ω) (u ω) ∂Q := L2.inner_def u u
    _ = ∫ ω, ‖u ω‖ ^ 2 ∂Q := by
      simp only [real_inner_self_eq_norm_sq]

/-- The symmetric energy pairing on the actual closed potential-gradient domain. -/
noncomputable def correctorEnergyForm {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    correctorPotentialDomain Q →L[ℝ] correctorPotentialDomain Q →L[ℝ] ℝ := by
  let V := correctorPotentialDomain Q
  let A := reducedOriginCoefficientAction Q
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => inner ℝ (u : Lp (EuclideanSpace ℝ (Fin d)) 2
      (reducedEnvironmentLaw Q)) (A (v : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q))))
      (by
        intro u₁ u₂ v
        simp only [Submodule.coe_add, inner_add_left])
      (by
        intro c u v
        simp [inner_smul_left, smul_eq_mul])
      (by
        intro u v₁ v₂
        simp only [Submodule.coe_add, map_add, inner_add_right])
      (by
        intro c u v
        simp [map_smul, inner_smul_right, smul_eq_mul])
  exact B.mkContinuous₂ (correctorEllipticityConstant Q) (by
    intro u v
    have hA := norm_reducedOriginCoefficientAction_le Q
      (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    calc
      ‖inner ℝ (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (A (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)))‖
          ≤ ‖(u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))‖ *
            ‖A (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖(u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))‖ *
          (correctorEllipticityConstant Q *
            ‖(v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))‖) :=
        mul_le_mul_of_nonneg_left (by simpa [correctorEllipticityConstant] using hA)
          (norm_nonneg _)
      _ = correctorEllipticityConstant Q * ‖u‖ * ‖v‖ := by
        simp only [Submodule.norm_coe]
        ring)

theorem reducedOriginCoefficientAction_symmetric {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (u v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    inner ℝ u (reducedOriginCoefficientAction Q v) =
      inner ℝ (reducedOriginCoefficientAction Q u) v := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ae_reducedEnvironmentLaw_origin_elliptic Q,
    reducedOriginCoefficientAction_coe_bridge Q v,
    reducedOriginCoefficientAction_coe_bridge Q u] with ω hω hv hu
  rw [hv, hu]
  exact inner_canonicalMatrixActionPair_symm (ω.1 0) (hω 0).1 (u ω) (v ω)

theorem correctorEnergyForm_symmetric {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (u v : correctorPotentialDomain Q) :
    correctorEnergyForm Q u v = correctorEnergyForm Q v u := by
  change inner ℝ (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
      (reducedOriginCoefficientAction Q
        (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) =
    inner ℝ (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
      (reducedOriginCoefficientAction Q
        (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)))
  calc
    _ = inner ℝ (reducedOriginCoefficientAction Q
        (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)))
        (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :=
      reducedOriginCoefficientAction_symmetric Q _ _
    _ = _ := real_inner_comm _ _

theorem correctorEnergyForm_isCoercive {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : IsCoercive (correctorEnergyForm Q) := by
  let C := correctorEllipticityConstant Q
  let μ := reducedEnvironmentLaw Q
  let A := reducedOriginCoefficientAction Q
  let V := correctorPotentialDomain Q
  have hC : 0 < C := correctorEllipticityConstant_pos Q
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro u
  have hIntSq : Integrable (fun ω => ‖(u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) ω‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using
      (L2.integrable_inner (𝕜 := ℝ) (u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ)
        (u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ))
  have hIntEnergy : Integrable (fun ω => inner ℝ
      ((u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) ω)
      (A (u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) ω)) μ :=
    L2.integrable_inner (𝕜 := ℝ) (u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ)
      (A (u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ))
  have hEll := ae_reducedEnvironmentLaw_origin_elliptic Q
  have hAction := reducedOriginCoefficientAction_coe_bridge Q
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ)
  have hpoint : ∀ᵐ ω ∂μ,
      C⁻¹ * ‖(u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) ω‖ ^ 2 ≤
        inner ℝ ((u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) ω)
          (A (u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) ω) := by
    filter_upwards [hEll, hAction] with ω hω hAω
    rw [hAω]
    have hquad := ((hω 0).2 (WithLp.ofLp
      ((u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) ω))).1
    simpa [C, correctorEllipticityConstant,
      inner_canonicalMatrixActionPair_self_eq_dot, euclideanSq_ofLp_eq_norm_sq] using hquad
  have hmono := integral_mono_ae (hIntSq.const_mul C⁻¹) hIntEnergy hpoint
  have hsq := norm_sq_eq_integral_norm_sq_corrector
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ)
  calc
    C⁻¹ * ‖u‖ * ‖u‖ = C⁻¹ * ‖u‖ ^ 2 := by ring
    _ = ∫ ω, C⁻¹ * ‖(u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) ω‖ ^ 2 ∂μ := by
      rw [integral_const_mul, ← hsq]
      simp only [Submodule.coe_norm]
    _ ≤ ∫ ω, inner ℝ ((u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) ω)
        (A (u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) ω) ∂μ := hmono
    _ = correctorEnergyForm Q u u := by
      change _ = inner ℝ (u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ)
        (A (u : Lp (EuclideanSpace ℝ (Fin d)) 2 μ))
      exact (L2.inner_def _ _).symm

/-- The stationary unit vector in coordinate `i`. -/
def correctorUnitVector {d : ℕ} (i : Fin d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (Pi.single i (1 : ℝ))

private instance correctorPotentialDomain_completeSpace {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : CompleteSpace (correctorPotentialDomain Q) :=
  (isClosed_stationaryPotentialGradients (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q)).completeSpace_coe

/-- The continuous forcing functional `v ↦ E[v · a e_i]` on the actual closed domain. -/
noncomputable def correctorForcingForm {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    correctorPotentialDomain Q →L[ℝ] ℝ :=
  (innerSL ℝ (reducedOriginCoefficientAction Q
      (Lp.const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i)))).comp
    (correctorPotentialDomain Q).subtypeL

theorem correctorForcingForm_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (v : correctorPotentialDomain Q) :
    correctorForcingForm Q i v =
      inner ℝ (reducedOriginCoefficientAction Q
        (Lp.const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i)))
        (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) := by
  rfl

/-- Riesz vector representing the forcing by the Euclidean `L²` inner product. -/
noncomputable def correctorForcingVector {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) : correctorPotentialDomain Q :=
  (InnerProductSpace.toDual ℝ (correctorPotentialDomain Q)).symm
    (correctorForcingForm Q i)

theorem correctorForcingVector_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (v : correctorPotentialDomain Q) :
    inner ℝ (correctorForcingVector Q i) v = correctorForcingForm Q i v := by
  exact InnerProductSpace.toDual_symm_apply

/-- The Lax–Milgram equivalence for the actual stationary potential-gradient domain. -/
noncomputable def correctorEnergyEquiv {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    correctorPotentialDomain Q ≃L[ℝ] correctorPotentialDomain Q :=
  (correctorEnergyForm_isCoercive Q).continuousLinearEquivOfBilin

theorem correctorEnergyEquiv_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (u v : correctorPotentialDomain Q) :
    inner ℝ (correctorEnergyEquiv Q u) v = correctorEnergyForm Q u v := by
  exact IsCoercive.continuousLinearEquivOfBilin_apply
    (correctorEnergyForm_isCoercive Q) u v

/-- Source: `paper/main.tex:693-697`. The unique corrector gradient, obtained from Lax–Milgram
in the closed potential-gradient subspace. It is a stationary vector field, not a stationary
scalar potential. -/
noncomputable def canonicalCorrectorGradient {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) : correctorPotentialDomain Q :=
  (correctorEnergyEquiv Q).symm (-correctorForcingVector Q i)

theorem correctorEnergyForm_canonical_variational {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (v : correctorPotentialDomain Q) :
    correctorEnergyForm Q (canonicalCorrectorGradient Q i) v =
      -correctorForcingForm Q i v := by
  have hsolve : correctorEnergyEquiv Q (canonicalCorrectorGradient Q i) =
      -correctorForcingVector Q i := by
    simp [canonicalCorrectorGradient]
  rw [← correctorEnergyEquiv_apply Q (canonicalCorrectorGradient Q i) v, hsolve,
    inner_neg_left, correctorForcingVector_apply]

theorem correctorPotentialDomain_complete {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : CompleteSpace (correctorPotentialDomain Q) := inferInstance

/-- The affine stationary field for the `i`-th variational problem. -/
noncomputable def correctorAffineField {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
  Lp.const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i)

/-- The flux associated with the canonical stationary gradient. -/
noncomputable def correctorFluxOfGradient {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
  reducedOriginCoefficientAction Q
    (correctorAffineField Q i + G)

noncomputable def canonicalCorrectorFlux {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
  correctorFluxOfGradient Q i (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))

theorem correctorVariational_sum_eq {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : correctorPotentialDomain Q) (v : correctorPotentialDomain Q) :
    correctorForcingForm Q i v + correctorEnergyForm Q v G =
      inner ℝ (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
        (correctorFluxOfGradient Q i (G :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) := by
  rw [correctorForcingForm_apply, real_inner_comm]
  change inner ℝ (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
      (reducedOriginCoefficientAction Q (correctorAffineField Q i)) +
    inner ℝ (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
      (reducedOriginCoefficientAction Q (G :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) =
    inner ℝ (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
      (reducedOriginCoefficientAction Q (correctorAffineField Q i + (G :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))))
  rw [map_add, inner_add_right]

theorem canonicalCorrectorGradient_variational_domain {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (v : correctorPotentialDomain Q) :
    inner ℝ (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
      (canonicalCorrectorFlux Q i) = 0 := by
  have hforcing : correctorForcingForm Q i v =
      inner ℝ (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
        (reducedOriginCoefficientAction Q (correctorAffineField Q i)) := by
    rw [correctorForcingForm_apply, real_inner_comm]
    rfl
  have henergy := correctorEnergyForm_canonical_variational Q i v
  calc
    _ = correctorForcingForm Q i v +
        correctorEnergyForm Q v (canonicalCorrectorGradient Q i) := by
      change inner ℝ (v : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q))
          (reducedOriginCoefficientAction Q
            (correctorAffineField Q i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)))) =
        correctorForcingForm Q i v +
          inner ℝ (v : Lp (EuclideanSpace ℝ (Fin d)) 2
            (reducedEnvironmentLaw Q))
            (reducedOriginCoefficientAction Q
              (canonicalCorrectorGradient Q i :
                Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)))
      rw [map_add, inner_add_right, hforcing]
    _ = correctorForcingForm Q i v +
        correctorEnergyForm Q (canonicalCorrectorGradient Q i) v := by
      rw [correctorEnergyForm_symmetric]
    _ = 0 := by rw [henergy]; ring

/-- The displayed variational equation, tested against each actual horizontal `H¹` gradient. -/
theorem canonicalCorrectorGradient_variational_horizontalH1 {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (f : horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q)) :
    inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) f) (canonicalCorrectorFlux Q i) = 0 := by
  exact canonicalCorrectorGradient_variational_domain Q i
    ⟨horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) f,
      horizontalEuclideanGradient_mem_stationaryPotentialGradients
        (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) f⟩

theorem canonicalCorrectorGradient_mean_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d) :
    euclideanCoordinateMean (reducedEnvironmentLaw Q) j
      (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) = 0 :=
  correctorPotentialDomain_mean_zero Q _ (canonicalCorrectorGradient Q i).property j

theorem canonicalCorrectorFlux_integrable {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    Integrable (canonicalCorrectorFlux Q i) (reducedEnvironmentLaw Q) := by
  exact (Lp.memLp (canonicalCorrectorFlux Q i)).integrable (by norm_num)

theorem correctorPotentialDomain_eq_canonical_of_variational {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (G : correctorPotentialDomain Q)
    (hG : ∀ v : correctorPotentialDomain Q,
      inner ℝ (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
        (correctorFluxOfGradient Q i (G :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) = 0) :
    G = canonicalCorrectorGradient Q i := by
  have henergy : ∀ v : correctorPotentialDomain Q,
      correctorEnergyForm Q G v = -correctorForcingForm Q i v := by
    intro v
    have hsum : correctorForcingForm Q i v + correctorEnergyForm Q v G = 0 := by
      calc
        _ = inner ℝ (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (correctorFluxOfGradient Q i (G :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) :=
          correctorVariational_sum_eq Q i G v
        _ = 0 := hG v
    calc
      correctorEnergyForm Q G v = correctorEnergyForm Q v G :=
        correctorEnergyForm_symmetric Q G v
      _ = -correctorForcingForm Q i v := by
        have : correctorForcingForm Q i v + correctorEnergyForm Q v G = 0 := hsum
        linarith
  have hoperator : correctorEnergyEquiv Q G = -correctorForcingVector Q i := by
    apply (InnerProductSpace.toDual ℝ (correctorPotentialDomain Q)).injective
    ext v
    rw [InnerProductSpace.toDual_apply_apply, InnerProductSpace.toDual_apply_apply,
      correctorEnergyEquiv_apply, henergy, inner_neg_left, correctorForcingVector_apply]
  apply (correctorEnergyEquiv Q).injective
  rw [hoperator]
  simp [canonicalCorrectorGradient]

theorem correctorGradient_eq_canonical_of_horizontal_variational {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : correctorPotentialDomain Q)
    (hG : ∀ f : horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q),
      inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) f)
        (correctorFluxOfGradient Q i (G :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) = 0) :
    G = canonicalCorrectorGradient Q i := by
  let F : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) →L[ℝ] ℝ :=
    innerSL ℝ (correctorFluxOfGradient Q i (G :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)))
  have hrange : LinearMap.range
      (horizontalEuclideanGradientMap (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q)) ≤ LinearMap.ker F.toLinearMap := by
    rintro u ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    change inner ℝ (correctorFluxOfGradient Q i (G :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)))
      (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) f) = 0
    rw [real_inner_comm]
    exact hG f
  have hclosed : IsClosed (LinearMap.ker F.toLinearMap).carrier :=
    ContinuousLinearMap.isClosed_ker F
  have hdomain : ∀ v : correctorPotentialDomain Q,
      inner ℝ (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
        (correctorFluxOfGradient Q i (G :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) = 0 := by
    intro v
    have hmem := (LinearMap.range
        (horizontalEuclideanGradientMap (reducedEnvironmentLaw Q)
          (reducedEnvironmentLaw_stationary Q))).topologicalClosure_minimal
        hrange hclosed v.property
    have hzero : F (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) = 0 :=
      LinearMap.mem_ker.mp hmem
    change inner ℝ (correctorFluxOfGradient Q i (G :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)))
      (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) = 0 at hzero
    rw [real_inner_comm] at hzero
    exact hzero
  exact correctorPotentialDomain_eq_canonical_of_variational Q i G hdomain

theorem existsUnique_canonicalCorrectorGradient_horizontalH1 {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    ∃! G : correctorPotentialDomain Q,
      ∀ f : horizontalH1 (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q),
        inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
          (reducedEnvironmentLaw_stationary Q) f)
          (correctorFluxOfGradient Q i (G :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) = 0 := by
  refine ⟨canonicalCorrectorGradient Q i, ?_, ?_⟩
  · intro f
    exact canonicalCorrectorGradient_variational_horizontalH1 Q i f
  · intro G hG
    exact correctorGradient_eq_canonical_of_horizontal_variational Q i G hG

/-- Source: `paper/main.tex:698`. The expected flux column `E[a(e_i + G_i)]` under the actual
reduced law. -/
noncomputable def expectedCorrectorFlux {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) : EuclideanSpace ℝ (Fin d) :=
  ∫ ω, canonicalCorrectorFlux Q i ω ∂reducedEnvironmentLaw Q

theorem expectedCorrectorFlux_eq_integral {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    expectedCorrectorFlux Q i =
      ∫ ω, canonicalCorrectorFlux Q i ω ∂reducedEnvironmentLaw Q := rfl


end

end EinsteinRelation.Correctors
