import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.Holder
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.StationaryGradientDomainSupport

/-! Restated from the library module `EinsteinRelation.Correctors.CanonicalVariationalGradientSupport`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
noncomputable section
private theorem continuous_originMatrix {d : ℕ} :
    Continuous (fun ω : FieldPair d => ω.1 (0 : Vec d)) :=
  (continuous_eval_const (0 : Vec d)).comp continuous_fst
def canonicalMatrixActionPair {d : ℕ}
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
def canonicalOriginMatrixActionFun {d : ℕ} {Q : Measure (FieldPair d)}
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) : FieldPair d → EuclideanSpace ℝ (Fin d) :=
  fun ω => canonicalMatrixActionPair (ω.1 0, u ω)
private theorem canonicalOriginMatrixAction_aestronglyMeasurable {d : ℕ}
    {Q : Measure (FieldPair d)} (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    AEStronglyMeasurable (canonicalOriginMatrixActionFun u) Q := by
  letI : TopologicalSpace (Mat d) := Pi.topologicalSpace
  have hPseudo : TopologicalSpace.PseudoMetrizableSpace (Mat d) := by
    change TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ)
    exact inferInstance
  letI : TopologicalSpace.PseudoMetrizableSpace (Mat d) := hPseudo
  have hSecond : SecondCountableTopology (Mat d) := by
    change SecondCountableTopology (Fin d → Fin d → ℝ)
    exact inferInstance
  letI : SecondCountableTopology (Mat d) := hSecond
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
instance correctorPotentialDomain_completeSpace {d : ℕ} {Λ₀ r₀ : ℝ}
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
/-- Riesz vector representing the forcing by the Euclidean `L²` inner product. -/
noncomputable def correctorForcingVector {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) : correctorPotentialDomain Q :=
  (InnerProductSpace.toDual ℝ (correctorPotentialDomain Q)).symm
    (correctorForcingForm Q i)
/-- The Lax–Milgram equivalence for the actual stationary potential-gradient domain. -/
noncomputable def correctorEnergyEquiv {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    correctorPotentialDomain Q ≃L[ℝ] correctorPotentialDomain Q :=
  (correctorEnergyForm_isCoercive Q).continuousLinearEquivOfBilin
/-- Source: `paper/main.tex:699-703`. The unique corrector gradient, obtained from Lax–Milgram
in the closed potential-gradient subspace. It is a stationary vector field, not a stationary
scalar potential. -/
noncomputable def canonicalCorrectorGradient {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) : correctorPotentialDomain Q :=
  (correctorEnergyEquiv Q).symm (-correctorForcingVector Q i)
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
/-- Source: `paper/main.tex:704`. The expected flux column `E[a(e_i + G_i)]` under the actual
reduced law. -/
noncomputable def expectedCorrectorFlux {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) : EuclideanSpace ℝ (Fin d) :=
  ∫ ω, canonicalCorrectorFlux Q i ω ∂reducedEnvironmentLaw Q
end
end EinsteinRelation.Correctors
