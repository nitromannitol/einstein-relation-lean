import EinsteinFull.Blueprint.G4.node_app_u3A_sharp_u2D_harmonic
import EinsteinFull.Blueprint.G4.node_app_u3A_sharp_u2D_fields
import EinsteinFull.Blueprint.G4.node_eq_u2E_time_u2D_change_u2D_identities
import EinsteinFull.Calculus.S4SharpHarmonicSupport
import EinsteinFull.Calculus.S1SharpBoundSupport
import EinsteinFull.Calculus.S1SharpPhysicalBounds
import EinsteinFull.Calculus.S4SharpVelocitySupport
import EinsteinFull.Calculus.S2ForwardFamily
import EinsteinFull.Calculus.S4PathwiseV2Support
import EinsteinRelation.Correctors.P53SourceSkewMollifyAlgebra
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.CocompactMap
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import EinsteinRelation.Diffusion.Covariance
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeTimeChange

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation EinsteinRelation.Sharpness

/- SUPERVISOR EXACT CONTRACT. Not a declaration/proof; do not commit a scaffold.
theorem sharp_harmonic_reduction_of_graph_deps
    (h0 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h1 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2) :
    node_app_u3A_sharp_u2D_harmonicStmt
-/

private theorem exists_inverseKernel {d : ℕ} (L : ℝ) (κ : QuenchedPathLaws d) :
    ∃ κ' : QuenchedPathLaws d, ∀ (ω : FieldPair d) (hω : IsRegular L ω),
      IsProbabilityMeasure (κ (0, ω)) →
        κ' (0, ω) = (κ (0, ω)).map (timeChangeMap hω) := by
  classical
  let S : Set (Vec d × FieldPair d) := {a | a.1 = 0 ∧ κ a Set.univ = 1}
  have hS : MeasurableSet S := by
    show MeasurableSet ({a : Vec d × FieldPair d | a.1 = 0} ∩ {a | κ a Set.univ = 1})
    exact ((measurableSet_singleton (0 : Vec d)).preimage measurable_fst).inter
      (measurableSet_eq_fun (Kernel.measurable_coe κ MeasurableSet.univ) measurable_const)
  let κ₁ : QuenchedPathLaws d := Kernel.piecewise hS κ 0
  have : IsFiniteKernel κ₁ := by
    refine ⟨⟨1, ENNReal.one_lt_top, fun a => ?_⟩⟩
    simp only [κ₁, Kernel.piecewise_apply]
    split_ifs with h
    · exact h.2.le
    · simp
  refine ⟨Kernel.map (Kernel.id ×ₖ κ₁) (timeChangeFamily L), fun ω hω hprob => ?_⟩
  have hmem : ((0 : Vec d), ω) ∈ S := ⟨rfl, measure_univ⟩
  have h1 : κ₁ (0, ω) = κ (0, ω) := by
    simp only [κ₁, Kernel.piecewise_apply, hmem, ite_true]
  rw [Kernel.map_apply _ (measurable_timeChangeFamily d L), Kernel.prod_apply,
    Kernel.id_apply, Measure.dirac_prod, h1,
    Measure.map_map (measurable_timeChangeFamily d L) measurable_prodMk_left]
  congr 1
  funext γ
  exact dite_eq_left hω

/-- Inverse clocks turn an arbitrary almost-sure reduced family into a physical family.
No pointwise solution selection or martingale-problem uniqueness is needed. -/
private theorem inverseFamily_of_reducedFamily {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω) (i : Fin d)
    (Y : DiffusionFamily d)
    (hY : ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y lam (0, ω))) :
    ∃ X : DiffusionFamily d, IsSignedPhysicalFamily i Q X ∧
      ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular D.ellipticity ω,
        X lam (0, ω) = (Y lam (0, ω)).map
          (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ D.ellipticity hω) := by
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one D.one_le_ellipticity
  choose X hX using fun lam : ℝ => exists_inverseKernel D.ellipticity (Y lam)
  refine ⟨X, fun lam => ?_, fun lam => ?_⟩
  · filter_upwards [Q.regular, hsm, hY lam] with ω hreg hs hsol
    rw [hX lam ω hreg hsol.1]
    exact timeChange_solves hΛ hreg hs i lam 0 hsol
  · filter_upwards [Q.regular, hY lam] with ω hreg hsol
    exact ⟨hreg, hX lam ω hreg hsol.1⟩

/-- A supplied solution can occupy its own force in the family before applying the
time-change dependency. Thus uniqueness of reduced laws is unnecessary for this step. -/
private theorem velocity_of_reducedFamily
    (htc : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω)
    (b : ℕ → ℝ) (hb : ∀ k : ℕ, 1 ≤ k → 0 < b k)
    (hsmb : ∀ᵐ ω ∂Q.measure, IsSmoothWithBounds b ω)
    (Y₀ : DiffusionFamily d)
    (hY₀ : ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y₀ lam (0, ω)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) :
    ∃ ell : Vec d, HasQuenchedVelocity Q.measure (originLaw Y) ell := by
  classical
  let PY : DiffusionFamily d := fun l => if l = lam then Y else Y₀ l
  have hPY : ∀ l : ℝ, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω l)
        0 (PY l (0, ω)) := by
    intro l
    by_cases he : l = lam
    · subst l
      simpa only [PY, ite_true] using hY
    · simpa only [PY, ite_eq_right he] using hY₀ l
  obtain ⟨PX, hPX, hrel⟩ := inverseFamily_of_reducedFamily D Q hsm
    (⟨0, by omega⟩ : Fin d) PY hPY
  obtain ⟨Λ, -, hall⟩ := htc D.ellipticity D.one_le_ellipticity
  obtain ⟨hvel, -, -⟩ := hall d hd D.dependenceRange b Q D.one_le_dependenceRange hb hsmb
    PX PY hPX hPY hrel
  obtain ⟨η, vX, vY, -, -, -, -, hvY, -⟩ := hvel lam hlam
  exact ⟨vY, by simpa only [PY, ite_true] using hvY⟩

/-- The sharp coordinate map makes the actual diffusion matrix scalar.
This is the second-order part of a possible additive-noise construction. -/
private theorem sharp_coefficient_congruence {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (x : Vec d) :
    let J := jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)
    J * reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x * J.transpose =
      J.det • (1 : Mat d) := by
  dsimp only
  let J := jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)
  have hdet : IsUnit J.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [show J.det = jacobianFactor i
      (gradient (EinsteinFull.Work.W8.corrector W) x) from det_jacobian _ _]
    exact jacobianFactor_ne_zero_of_norm_le i _
      (EinsteinFull.Work.W8.corrector_gradient_bound W x)
  have hinv : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hdet
  have htr : J⁻¹.transpose * J.transpose = 1 := by
    rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
  rw [EinsteinFull.Work.W8.reducedCoefficient_inverse_formula]
  change J * (J.det • (J⁻¹ * J⁻¹.transpose)) * J.transpose = J.det • (1 : Mat d)
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [← Matrix.mul_assoc J J⁻¹, hinv, Matrix.one_mul, htr]


/-- Inversion of the actual sharp map is a contraction on each coordinate line. -/
private theorem sharp_slice_contraction {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (y : Vec d) :
    ContractingWith (1 / 4 : ℝ≥0)
      (fun s : ℝ => -EinsteinFull.Work.W8.corrector W (y + s • unitVector i)) := by
  have hd (s : ℝ) : HasDerivAt
      (fun t : ℝ => -EinsteinFull.Work.W8.corrector W (y + t • unitVector i))
      (-coordinateDerivative i (EinsteinFull.Work.W8.corrector W)
        (y + s • unitVector i)) s := by
    have hψ : DifferentiableAt ℝ (EinsteinFull.Work.W8.corrector W)
        (y + s • unitVector i) :=
      (EinsteinFull.Work.W8.corrector_contDiff W).differentiable (by simp) _
    convert! (hψ.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_const s y).add ((hasDerivAt_id s).smul_const (unitVector i)))).neg
      using 1
    simp [coordinateDerivative]
  refine ⟨by norm_num, lipschitzWith_of_nnnorm_deriv_le
    (fun s => (hd s).differentiableAt) (fun s => ?_)⟩
  rw [(hd s).deriv]
  have hb := (abs_coord_le_euclideanNorm
    (gradient (EinsteinFull.Work.W8.corrector W) (y + s • unitVector i)) i).trans
      (EinsteinFull.Work.W8.corrector_gradient_bound W (y + s • unitVector i))
  change ‖-coordinateDerivative i (EinsteinFull.Work.W8.corrector W)
    (y + s • unitVector i)‖₊ ≤ (1 / 4 : ℝ≥0)
  exact_mod_cast (show ‖-coordinateDerivative i (EinsteinFull.Work.W8.corrector W)
    (y + s • unitVector i)‖ ≤ (1 / 4 : ℝ) by
      simpa only [norm_neg, Real.norm_eq_abs, gradient] using hb)

/-- The bounded smooth sharp perturbation is globally invertible. -/
private theorem sharp_coordinate_bijective {d : ℕ} (i : Fin d) (W : NoiseSample d) :
    Function.Bijective (fun x : Vec d =>
      x + EinsteinFull.Work.W8.corrector W x • unitVector i) := by
  classical
  rw [Function.bijective_iff_existsUnique]
  intro y
  let ψ := EinsteinFull.Work.W8.corrector W
  let f : ℝ → ℝ := fun s => -ψ (y + s • unitVector i)
  have hc : ContractingWith (1 / 4 : ℝ≥0) f := sharp_slice_contraction i W y
  let s := hc.fixedPoint f
  have hs : Function.IsFixedPt f s := hc.fixedPoint_isFixedPt
  have hz : s + ψ (y + s • unitVector i) = 0 := by
    change -ψ (y + s • unitVector i) = s at hs
    linarith
  refine ⟨y + s • unitVector i, ?_, fun x hx => ?_⟩
  · change (y + s • unitVector i) + ψ (y + s • unitVector i) • unitVector i = y
    rw [add_assoc, ← add_smul, hz, zero_smul, add_zero]
  · change x + ψ x • unitVector i = y at hx
    have hxrep : x = y + (-ψ x) • unitVector i := by
      rw [← hx, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
    have hfixed : Function.IsFixedPt f (-ψ x) := by
      change -ψ (y + (-ψ x) • unitVector i) = -ψ x
      rw [← hxrep]
    rw [hxrep, hc.fixedPoint_unique' hfixed hs]

/-- The actual sharp coordinate change has a continuous global inverse. -/
private noncomputable def sharp_coordinate_homeomorph {d : ℕ} (i : Fin d)
    (W : NoiseSample d) : Vec d ≃ₜ Vec d := by
  let φ : Vec d → Vec d := fun x =>
    x + EinsteinFull.Work.W8.corrector W x • unitVector i
  have hφ : Continuous φ := continuous_id.add
    ((EinsteinFull.Work.W8.corrector_contDiff W).continuous.smul continuous_const)
  have hp : IsProperMap φ := by
    refine isProperMap_iff_tendsto_cocompact.mpr ⟨hφ,
      Filter.tendsto_cocompact_cocompact_of_norm (fun ε => ?_)⟩
    refine ⟨ε + EinsteinFull.Work.W8.seedScale d, fun x hx => ?_⟩
    have hb : ‖EinsteinFull.Work.W8.corrector W x • unitVector i‖ ≤
        EinsteinFull.Work.W8.seedScale d := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _)
        (EinsteinFull.Calculus.S1.norm_unitVector_le_one i)).trans
          (EinsteinFull.Work.W8.corrector_abs_le W x)
    have ht := norm_add_le (φ x) (-EinsteinFull.Work.W8.corrector W x • unitVector i)
    have he : φ x + (-EinsteinFull.Work.W8.corrector W x) • unitVector i = x := by
      dsimp only [φ]
      rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
    rw [he, norm_smul, norm_neg] at ht
    rw [norm_smul] at hb
    linarith
  exact (Equiv.ofBijective φ (sharp_coordinate_bijective i W)).toHomeomorphOfContinuousClosed
    hφ hp.isClosedMap

private theorem sharp_coordinate_homeomorph_apply {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (x : Vec d) :
    sharp_coordinate_homeomorph i W x =
      x + EinsteinFull.Work.W8.corrector W x • unitVector i := rfl

/-- The global inverse of the actual sharp coordinate change is smooth. -/
private theorem sharp_coordinate_inverse_contDiff {d : ℕ} (i : Fin d)
    (W : NoiseSample d) :
    ContDiff ℝ (⊤ : ℕ∞) ((sharp_coordinate_homeomorph i W).symm : Vec d → Vec d) := by
  let ψ := EinsteinFull.Work.W8.corrector W
  have hψ := EinsteinFull.Work.W8.corrector_contDiff W
  have hd (x : Vec d) : HasFDerivAt
      (fun y : Vec d => y + ψ y • unitVector i)
      (ContinuousLinearMap.id ℝ (Vec d) + (fderiv ℝ ψ x).smulRight (unitVector i)) x := by
    exact (hasFDerivAt_id x).add
      (((hψ.differentiable (by simp)) x).hasFDerivAt.smul_const (unitVector i))
  have hi (x : Vec d) : Function.Injective
      (ContinuousLinearMap.id ℝ (Vec d) + (fderiv ℝ ψ x).smulRight (unitVector i)) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    change v + (fderiv ℝ ψ x v) • unitVector i = 0 at hv
    have hh := congrArg (fderiv ℝ ψ x) hv
    simp only [map_add, map_smul, map_zero, smul_eq_mul] at hh
    have hn : 1 + fderiv ℝ ψ x (unitVector i) ≠ 0 :=
      jacobianFactor_ne_zero_of_norm_le i _
        (EinsteinFull.Work.W8.corrector_gradient_bound W x)
    have hz : fderiv ℝ ψ x v = 0 := by
      apply (mul_eq_zero.mp (show fderiv ℝ ψ x v *
        (1 + fderiv ℝ ψ x (unitVector i)) = 0 by nlinarith)).resolve_right hn
    simpa only [hz, zero_smul, add_zero] using hv
  let A (x : Vec d) : Vec d ≃L[ℝ] Vec d :=
    (LinearEquiv.ofInjectiveEndo
      (ContinuousLinearMap.id ℝ (Vec d) +
        (fderiv ℝ ψ x).smulRight (unitVector i)).toLinearMap (hi x)).toContinuousLinearEquiv
  apply (sharp_coordinate_homeomorph i W).contDiff_symm (f₀' := A)
  · intro x
    exact hd x
  · exact contDiff_id.add (hψ.smul contDiff_const)

/-- The derivative of the literal coordinate map is its stated Jacobian matrix. -/
private theorem sharp_coordinate_fderiv {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (x v : Vec d) :
    fderiv ℝ (sharp_coordinate_homeomorph i W) x v =
      (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).mulVec v := by
  let ψ := EinsteinFull.Work.W8.corrector W
  have hψ : DifferentiableAt ℝ ψ x :=
    (EinsteinFull.Work.W8.corrector_contDiff W).differentiable (by simp) x
  have hd : HasFDerivAt (fun y : Vec d => y + ψ y • unitVector i)
      (ContinuousLinearMap.id ℝ (Vec d) + (fderiv ℝ ψ x).smulRight (unitVector i)) x :=
    (hasFDerivAt_id x).add (hψ.hasFDerivAt.smul_const (unitVector i))
  have hv : (∑ j : Fin d, v j • unitVector j) = v := by
    ext k
    simp [unitVector, Pi.single_apply]
  have hs : fderiv ℝ ψ x v = ∑ j, gradient ψ x j * v j := by
    conv_lhs => rw [← hv]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  change fderiv ℝ (fun y : Vec d => y + ψ y • unitVector i) x v = _
  rw [hd.fderiv]
  change v + (fderiv ℝ ψ x v) • unitVector i = _
  rw [jacobian, Matrix.add_mulVec, Matrix.one_mulVec]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, outer]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← hs]
  ring

/-- The smooth inverse has the actual inverse Jacobian, at every point and direction. -/
private theorem sharp_coordinate_inverse_fderiv {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (x v : Vec d) :
    fderiv ℝ (sharp_coordinate_homeomorph i W).symm
      (sharp_coordinate_homeomorph i W x) v =
      ((jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x))⁻¹).mulVec v := by
  let φ := sharp_coordinate_homeomorph i W
  let J := jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)
  have hφ : DifferentiableAt ℝ φ x :=
    (differentiableAt_id.add
      (((EinsteinFull.Work.W8.corrector_contDiff W).differentiable (by simp) x).smul_const
        (unitVector i)))
  have hq : DifferentiableAt ℝ φ.symm (φ x) :=
    (sharp_coordinate_inverse_contDiff i W).differentiable (by simp) _
  have hc := hq.hasFDerivAt.comp x hφ.hasFDerivAt
  have he : (fun z => φ.symm (φ z)) = (id : Vec d → Vec d) := by
    funext z
    exact φ.symm_apply_apply z
  change HasFDerivAt (fun z => φ.symm (φ z))
    ((fderiv ℝ φ.symm (φ x)).comp (fderiv ℝ φ x)) x at hc
  rw [he] at hc
  have hlin := congrArg (fun T : Vec d →L[ℝ] Vec d => T (J⁻¹.mulVec v))
    (hc.unique (hasFDerivAt_id x))
  have hdet : IsUnit J.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [show J.det = jacobianFactor i
      (gradient (EinsteinFull.Work.W8.corrector W) x) from det_jacobian _ _]
    exact jacobianFactor_ne_zero_of_norm_le i _
      (EinsteinFull.Work.W8.corrector_gradient_bound W x)
  change fderiv ℝ φ.symm (φ x) (fderiv ℝ φ x (J⁻¹.mulVec v)) = J⁻¹.mulVec v at hlin
  rw [sharp_coordinate_fderiv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv J hdet,
    Matrix.one_mulVec] at hlin
  exact hlin

/-- Every inverse coordinate has the corresponding row of the inverse Jacobian as gradient. -/
private theorem sharp_inverse_coordinate_gradient {d : ℕ} (i k : Fin d)
    (W : NoiseSample d) (x : Vec d) :
    gradient (fun y => (sharp_coordinate_homeomorph i W).symm y k)
      (sharp_coordinate_homeomorph i W x) =
      ((jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x))⁻¹).transpose.mulVec
        (unitVector k) := by
  have hq := (sharp_coordinate_inverse_contDiff i W).differentiable (by simp)
  ext l
  unfold gradient coordinateDerivative
  rw [fderiv_apply (hq _) k]
  change (fderiv ℝ (sharp_coordinate_homeomorph i W).symm
    (sharp_coordinate_homeomorph i W x) (unitVector l)) k = _
  rw [sharp_coordinate_inverse_fderiv]
  simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, Matrix.transpose_apply]
  rfl

/-- The tilted force becomes the gradient of the inverse force coordinate,
with the same scalar speed as the transformed covariance. -/
private theorem sharp_transformed_force {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (x : Vec d) :
    (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).mulVec
      ((reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x).mulVec
        (unitVector i)) =
      (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).det •
        gradient (fun y => (sharp_coordinate_homeomorph i W).symm y i)
          (sharp_coordinate_homeomorph i W x) := by
  rw [sharp_inverse_coordinate_gradient, EinsteinFull.Work.W8.reducedCoefficient_inverse_formula]
  let J := jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)
  have hdet : IsUnit J.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [show J.det = jacobianFactor i
      (gradient (EinsteinFull.Work.W8.corrector W) x) from det_jacobian _ _]
    exact jacobianFactor_ne_zero_of_norm_le i _
      (EinsteinFull.Work.W8.corrector_gradient_bound W x)
  change J.mulVec ((J.det • (J⁻¹ * J⁻¹.transpose)).mulVec (unitVector i)) =
    J.det • J⁻¹.transpose.mulVec (unitVector i)
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hdet, Matrix.one_mul]

/-- Each cofactor column has the explicit rank-one cancellation formula. -/
private theorem sharp_cofactor_column {d : ℕ} (i k : Fin d)
    (W : NoiseSample d) (x : Vec d) :
    (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).det •
        ((jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x))⁻¹).mulVec
          (unitVector k) =
      (1 + coordinateDerivative i (EinsteinFull.Work.W8.corrector W) x) • unitVector k -
        coordinateDerivative k (EinsteinFull.Work.W8.corrector W) x • unitVector i := by
  let g := gradient (EinsteinFull.Work.W8.corrector W) x
  have hj := jacobianFactor_ne_zero_of_norm_le i g
    (EinsteinFull.Work.W8.corrector_gradient_bound W x)
  rw [det_jacobian, ← inverseCandidate_eq_inv i _ hj, inverseCandidate,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  have ho : (outer (unitVector i) g).mulVec (unitVector k) = g k • unitVector i := by
    ext l
    simp [Matrix.mulVec, dotProduct, outer, unitVector, Pi.single_apply, mul_comm]
  change jacobianFactor i g •
    (unitVector k - (jacobianFactor i g)⁻¹ • (outer (unitVector i) g).mulVec (unitVector k)) = _
  rw [ho, smul_sub, smul_smul, mul_inv_cancel₀ hj, one_smul]
  rfl

/-- The cofactor columns are divergence free by equality of mixed derivatives. -/
private theorem sharp_cofactor_divergence {d : ℕ} (i k : Fin d)
    (W : NoiseSample d) (x : Vec d) :
    divergence (fun y =>
      (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) y)).det •
        ((jacobian i (gradient (EinsteinFull.Work.W8.corrector W) y))⁻¹).mulVec
          (unitVector k)) x = 0 := by
  let ψ := EinsteinFull.Work.W8.corrector W
  have hψ := EinsteinFull.Work.W8.corrector_contDiff W
  have hd (l : Fin d) : DifferentiableAt ℝ (coordinateDerivative l ψ) x := by
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ ψ) :=
      hψ.fderiv_right (le_of_eq ENat.coe_top_add_one)
    exact (hF.clm_apply contDiff_const).differentiable (by simp) x
  simp_rw [sharp_cofactor_column]
  unfold divergence
  have he (l : Fin d) :
      coordinateDerivative l (fun y =>
        ((1 + coordinateDerivative i ψ y) • unitVector k -
          coordinateDerivative k ψ y • unitVector i) l) x =
      coordinateDerivative l (coordinateDerivative i ψ) x * unitVector k l -
        coordinateDerivative l (coordinateDerivative k ψ) x * unitVector i l := by
    unfold coordinateDerivative
    change fderiv ℝ (fun y => (1 + coordinateDerivative i ψ y) * unitVector k l -
      coordinateDerivative k ψ y * unitVector i l) x (unitVector l) = _
    rw [fderiv_fun_sub (((hd i).const_add 1).mul_const _) ((hd k).mul_const _),
      fderiv_mul_const ((hd i).const_add 1), fderiv_mul_const (hd k), fderiv_const_add]
    simp only [sub_apply, smul_apply, smul_eq_mul]
    ring_nf
    rfl
  change (∑ l, coordinateDerivative l (fun y =>
    ((1 + coordinateDerivative i ψ y) • unitVector k -
      coordinateDerivative k ψ y • unitVector i) l) x) = 0
  simp_rw [he]
  simp only [Finset.sum_sub_distrib]
  simp only [unitVector, Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact sub_eq_zero.mpr (congrFun (Correctors.coordinateDerivative_comm hψ k i) x)

/-- The forward coordinate gradients are the columns of the transposed Jacobian. -/
private theorem sharp_forward_coordinate_gradient {d : ℕ} (i k : Fin d)
    (W : NoiseSample d) (x : Vec d) :
    gradient (fun y => sharp_coordinate_homeomorph i W y k) x =
      (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).transpose.mulVec
        (unitVector k) := by
  have hφ : DifferentiableAt ℝ (sharp_coordinate_homeomorph i W) x :=
    differentiableAt_id.add
      (((EinsteinFull.Work.W8.corrector_contDiff W).differentiable (by simp) x).smul_const
        (unitVector i))
  ext l
  unfold gradient coordinateDerivative
  rw [fderiv_apply hφ k]
  change (fderiv ℝ (sharp_coordinate_homeomorph i W) x (unitVector l)) k = _
  rw [sharp_coordinate_fderiv]
  simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, Matrix.transpose_apply]
  rfl

/-- The actual diffusion flux of every forward coordinate is its cofactor column. -/
private theorem sharp_forward_coordinate_flux {d : ℕ} (i k : Fin d)
    (W : NoiseSample d) (x : Vec d) :
    (reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x).mulVec
        (gradient (fun y => sharp_coordinate_homeomorph i W y k) x) =
      (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).det •
        ((jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x))⁻¹).mulVec
          (unitVector k) := by
  rw [sharp_forward_coordinate_gradient, EinsteinFull.Work.W8.reducedCoefficient_inverse_formula]
  let J := jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)
  have hdet : IsUnit J.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [show J.det = jacobianFactor i
      (gradient (EinsteinFull.Work.W8.corrector W) x) from det_jacobian _ _]
    exact jacobianFactor_ne_zero_of_norm_le i _
      (EinsteinFull.Work.W8.corrector_gradient_bound W x)
  have ht : J⁻¹.transpose * J.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv J hdet, Matrix.transpose_one]
  change (J.det • (J⁻¹ * J⁻¹.transpose)).mulVec (J.transpose.mulVec (unitVector k)) =
    J.det • J⁻¹.mulVec (unitVector k)
  rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ht, Matrix.mul_one]

/-- Every actual forward coordinate is harmonic for the unforced reduced generator. -/
private theorem sharp_forward_coordinate_harmonic {d : ℕ} (i k : Fin d)
    (W : NoiseSample d) (x : Vec d) :
    reducedGenerator i (EinsteinFull.Work.W8.physicalPair i W) 0
      (fun y => sharp_coordinate_homeomorph i W y k) x = 0 := by
  unfold reducedGenerator
  simp_rw [sharp_forward_coordinate_flux]
  rw [sharp_cofactor_divergence]
  simp

/-- The transformed coordinate drift is the inverse-coordinate gradient,
with exactly the same determinant speed as the transformed covariance. -/
private theorem sharp_forward_coordinate_generator {d : ℕ} (i k : Fin d)
    (W : NoiseSample d) (lam : ℝ) (x : Vec d) :
    reducedGenerator i (EinsteinFull.Work.W8.physicalPair i W) lam
      (fun y => sharp_coordinate_homeomorph i W y k) x =
      lam * (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).det *
        gradient (fun y => (sharp_coordinate_homeomorph i W).symm y i)
          (sharp_coordinate_homeomorph i W x) k := by
  unfold reducedGenerator
  simp_rw [sharp_forward_coordinate_flux]
  rw [sharp_cofactor_divergence, mul_zero, zero_add, sharp_forward_coordinate_gradient]
  have hdot := Matrix.dotProduct_transpose_mulVec
    (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x))
    ((reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x).mulVec (unitVector i))
    (unitVector k)
  change dot _ _ = dot _ _ at hdot
  rw [hdot, sharp_transformed_force]
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  simp [unitVector, Pi.single_apply, mul_assoc]

/-- The spatial derivative is the dot product with the literal coordinate gradient. -/
private theorem derivative_eq_gradient_dot {d : ℕ} (f : Vec d → ℝ) (x v : Vec d) :
    fderiv ℝ f x v = dot (gradient f x) v := by
  have hv : (∑ k : Fin d, v k • unitVector k) = v := by
    ext l
    simp [unitVector, Pi.single_apply]
  conv_lhs => rw [← hv]
  simp only [map_sum, map_smul, smul_eq_mul, dot, gradient, coordinateDerivative]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/-- The literal sharp coordinate change obeys the gradient chain rule. -/
private theorem sharp_gradient_comp {d : ℕ} (i : Fin d) (W : NoiseSample d)
    (f : Vec d → ℝ) (x : Vec d)
    (hf : DifferentiableAt ℝ f (sharp_coordinate_homeomorph i W x)) :
    gradient (fun y => f (sharp_coordinate_homeomorph i W y)) x =
      (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).transpose.mulVec
        (gradient f (sharp_coordinate_homeomorph i W x)) := by
  have hφ : DifferentiableAt ℝ (sharp_coordinate_homeomorph i W) x :=
    differentiableAt_id.add
      (((EinsteinFull.Work.W8.corrector_contDiff W).differentiable (by simp) x).smul_const
        (unitVector i))
  ext k
  unfold gradient coordinateDerivative
  change fderiv ℝ (f ∘ sharp_coordinate_homeomorph i W) x (unitVector k) = _
  rw [fderiv_comp x hf hφ]
  change fderiv ℝ f (sharp_coordinate_homeomorph i W x)
    (fderiv ℝ (sharp_coordinate_homeomorph i W) x (unitVector k)) = _
  rw [sharp_coordinate_fderiv, derivative_eq_gradient_dot]
  simp [dot, Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, Matrix.transpose_apply,
    gradient, coordinateDerivative, mul_comm]
  rfl

/-- Product rule for divergence, stated with the actual coordinate gradient. -/
private theorem divergence_smul_field {d : ℕ} (f : Vec d → ℝ) (F : Vec d → Vec d)
    (x : Vec d) (hf : DifferentiableAt ℝ f x)
    (hF : ∀ k, DifferentiableAt ℝ (fun y => F y k) x) :
    divergence (fun y => f y • F y) x =
      f x * divergence F x + dot (gradient f x) (F x) := by
  unfold divergence dot gradient coordinateDerivative
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [fderiv_fun_mul hf (hF _)]
  simp only [add_apply, smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/-- Divergence commutes with finite sums of differentiable coordinate fields. -/
private theorem divergence_sum_field {d : ℕ} (F : Fin d → Vec d → Vec d)
    (x : Vec d) (hF : ∀ k l, DifferentiableAt ℝ (fun y => F k y l) x) :
    divergence (fun y => ∑ k, F k y) x = ∑ k, divergence (F k) x := by
  unfold divergence coordinateDerivative
  simp only [Finset.sum_apply]
  simp_rw [fderiv_fun_sum (fun k _ => hF k _)]
  simp only [sum_apply]
  exact Finset.sum_comm

/-- Matrix multiplication expands along the coordinate vectors. -/
private theorem mulVec_basis_sum {d : ℕ} (M : Mat d) (v : Vec d) :
    M.mulVec v = ∑ k, v k • M.mulVec (unitVector k) := by
  ext l
  simp [Matrix.mulVec, dotProduct, unitVector, mul_comm]

/-- The full test flux is the sum of the cofactor columns weighted by test derivatives. -/
private theorem sharp_test_flux {d : ℕ} (i : Fin d) (W : NoiseSample d)
    (f : Vec d → ℝ) (x : Vec d)
    (hf : DifferentiableAt ℝ f (sharp_coordinate_homeomorph i W x)) :
    (reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x).mulVec
      (gradient (fun y => f (sharp_coordinate_homeomorph i W y)) x) =
      ∑ k, coordinateDerivative k f (sharp_coordinate_homeomorph i W x) •
        ((jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).det •
          ((jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x))⁻¹).mulVec
            (unitVector k)) := by
  rw [sharp_gradient_comp i W f x hf, Matrix.mulVec_mulVec, mulVec_basis_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Matrix.mulVec_mulVec, ← sharp_forward_coordinate_gradient,
    sharp_forward_coordinate_flux]
  rfl

/-- Piola transport of a differentiated scalar test. -/
private theorem sharp_test_divergence {d : ℕ} (i : Fin d) (W : NoiseSample d)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec d) :
    divergence (fun y => (reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) y).mulVec
      (gradient (fun z => f (sharp_coordinate_homeomorph i W z)) y)) x =
      (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).det *
        divergence (gradient f) (sharp_coordinate_homeomorph i W x) := by
  let φ := sharp_coordinate_homeomorph i W
  let ψ := EinsteinFull.Work.W8.corrector W
  let J := jacobian i (gradient ψ x)
  let C (k : Fin d) (y : Vec d) :=
    (jacobian i (gradient ψ y)).det •
      ((jacobian i (gradient ψ y))⁻¹).mulVec (unitVector k)
  let H (k : Fin d) (y : Vec d) := coordinateDerivative k f (φ y)
  have hφ : DifferentiableAt ℝ φ x := differentiableAt_id.add
    (((EinsteinFull.Work.W8.corrector_contDiff W).differentiable (by simp) x).smul_const
      (unitVector i))
  have hp (k : Fin d) : Differentiable ℝ (coordinateDerivative k f) := by
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
      hf.fderiv_right (le_of_eq ENat.coe_top_add_one)
    exact (hF.clm_apply contDiff_const).differentiable (by simp)
  have hH (k : Fin d) : DifferentiableAt ℝ (H k) x := (hp k (φ x)).comp x hφ
  have hC (k l : Fin d) : DifferentiableAt ℝ (fun y => C k y l) x := by
    have hD (m : Fin d) : DifferentiableAt ℝ (coordinateDerivative m ψ) x := by
      have hF : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ ψ) :=
        (EinsteinFull.Work.W8.corrector_contDiff W).fderiv_right
          (le_of_eq ENat.coe_top_add_one)
      exact (hF.clm_apply contDiff_const).differentiable (by simp) x
    have hcol : (fun y => C k y l) = (fun y =>
        (1 + coordinateDerivative i ψ y) * unitVector k l -
          coordinateDerivative k ψ y * unitVector i l) := by
      funext y
      exact congrArg (fun v : Vec d => v l) (sharp_cofactor_column i k W y)
    rw [hcol]
    exact (((hD i).const_add 1).mul_const _).sub ((hD k).mul_const _)
  have hdet : IsUnit J.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [show J.det = jacobianFactor i (gradient ψ x) from det_jacobian _ _]
    exact jacobianFactor_ne_zero_of_norm_le i _
      (EinsteinFull.Work.W8.corrector_gradient_bound W x)
  have hJC (k : Fin d) : J.mulVec (C k x) = J.det • unitVector k := by
    change J.mulVec (J.det • J⁻¹.mulVec (unitVector k)) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv J hdet,
      Matrix.one_mulVec]
  have he (k : Fin d) : divergence (fun y => H k y • C k y) x =
      J.det * coordinateDerivative k (coordinateDerivative k f) (φ x) := by
    rw [divergence_smul_field _ _ x (hH k) (hC k)]
    have hc : divergence (C k) x = 0 := sharp_cofactor_divergence i k W x
    rw [hc, mul_zero, zero_add]
    change dot (gradient (fun y => coordinateDerivative k f (φ y)) x) (C k x) = _
    rw [sharp_gradient_comp i W _ x (hp k (φ x))]
    have hdot := Matrix.dotProduct_transpose_mulVec J (C k x)
      (gradient (coordinateDerivative k f) (φ x))
    change dot _ _ = dot _ _ at hdot
    rw [show dot (J.transpose.mulVec (gradient (coordinateDerivative k f) (φ x))) (C k x) =
      dot (C k x) (J.transpose.mulVec (gradient (coordinateDerivative k f) (φ x))) from
        dotProduct_comm _ _, hdot, hJC]
    simp [dot, unitVector, Pi.single_apply, gradient, mul_comm]
  have hflux : (fun y => (reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) y).mulVec
      (gradient (fun z => f (φ z)) y)) = (fun y => ∑ k, H k y • C k y) := by
    funext y
    exact sharp_test_flux i W f y (hf.differentiable (by simp) _)
  rw [hflux, divergence_sum_field (fun k y => H k y • C k y) x
    (fun k l => (hH k).mul (hC k l))]
  simp_rw [he]
  rw [← Finset.mul_sum]
  rfl

/-- Full conjugacy of the actual reduced generator on smooth scalar tests. -/
private theorem sharp_test_generator {d : ℕ} (i : Fin d) (W : NoiseSample d)
    (lam : ℝ) (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec d) :
    reducedGenerator i (EinsteinFull.Work.W8.physicalPair i W) lam
      (fun y => f (sharp_coordinate_homeomorph i W y)) x =
      (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).det *
        ((1 / 2 : ℝ) * divergence (gradient f) (sharp_coordinate_homeomorph i W x) +
          lam * dot (gradient (fun y => (sharp_coordinate_homeomorph i W).symm y i)
            (sharp_coordinate_homeomorph i W x))
            (gradient f (sharp_coordinate_homeomorph i W x))) := by
  unfold reducedGenerator
  rw [sharp_test_divergence i W f hf x,
    sharp_gradient_comp i W f x (hf.differentiable (by simp) _)]
  have hdot := Matrix.dotProduct_transpose_mulVec
    (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x))
    ((reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x).mulVec (unitVector i))
    (gradient f (sharp_coordinate_homeomorph i W x))
  change dot _ _ = dot _ _ at hdot
  rw [hdot, sharp_transformed_force]
  have hs (a : ℝ) (v w : Vec d) : dot v (a • w) = a * dot w v := by
    change dotProduct v (a • w) = a * dotProduct w v
    rw [dotProduct_smul, dotProduct_comm]
    rfl
  rw [hs]
  ring

/-- The inverse coordinate drift is uniformly bounded in the explicit Euclidean norm. -/
private theorem sharp_inverse_gradient_bound {d : ℕ} (i k : Fin d)
    (W : NoiseSample d) (z : Vec d) :
    euclideanNorm (gradient (fun y => (sharp_coordinate_homeomorph i W).symm y k) z) ≤
      (4 / 3 : ℝ) := by
  let φ := sharp_coordinate_homeomorph i W
  obtain ⟨x, rfl⟩ := φ.surjective z
  rw [sharp_inverse_coordinate_gradient,
    ← inverseCandidate_eq_inv i _ (jacobianFactor_ne_zero_of_norm_le i _
      (EinsteinFull.Work.W8.corrector_gradient_bound W x))]
  have h := (inverseCandidate_transpose_norm_bounds i
    (gradient (EinsteinFull.Work.W8.corrector W) x) (unitVector k)
    (EinsteinFull.Work.W8.corrector_gradient_bound W x)).2
  have he : euclideanNorm (unitVector k : Vec d) = 1 := by
    simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply]
  simpa only [he, mul_one] using h

/-- A uniform operator bound for the inverse map, in the ambient sup norm. -/
private theorem sharp_inverse_fderiv_bound {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (z : Vec d) :
    ‖fderiv ℝ (sharp_coordinate_homeomorph i W).symm z‖ ≤ 2 * d := by
  let q := (sharp_coordinate_homeomorph i W).symm
  have hq := (sharp_coordinate_inverse_contDiff i W).differentiable (by simp)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  have he : (fderiv ℝ q z v) k =
      dot (gradient (fun y => q y k) z) v := by
    rw [← derivative_eq_gradient_dot]
    exact (congrArg (fun T : Vec d →L[ℝ] ℝ => T v) (fderiv_apply (hq z) k)).symm
  rw [Real.norm_eq_abs, he]
  calc
    |dot (gradient (fun y => q y k) z) v| ≤
        ∑ l, |gradient (fun y => q y k) z l * v l| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin d, 2 * ‖v‖ := by
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul]
      apply mul_le_mul _ (norm_le_pi_norm v l) (abs_nonneg _) (by norm_num)
      exact (abs_coord_le_euclideanNorm _ l).trans
        ((sharp_inverse_gradient_bound i k W z).trans (by norm_num))
    _ = (2 * d) * ‖v‖ := by simp; ring

/-- The sharp inverse is globally Lipschitz, uniformly over the noise sample. -/
private theorem sharp_inverse_lipschitz {d : ℕ} (i : Fin d) (W : NoiseSample d) :
    LipschitzWith (2 * d : ℝ≥0) (sharp_coordinate_homeomorph i W).symm := by
  refine lipschitzWith_of_nnnorm_fderiv_le
    ((sharp_coordinate_inverse_contDiff i W).differentiable (by simp)) fun z => ?_
  exact_mod_cast sharp_inverse_fderiv_bound i W z

/-- The transformed force has a uniform bound for every signed force. -/
private theorem sharp_transformed_drift_bound {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (lam : ℝ) (z : Vec d) :
    euclideanNorm (lam • gradient
      (fun y => (sharp_coordinate_homeomorph i W).symm y i) z) ≤
        |lam| * (4 / 3 : ℝ) := by
  rw [EinsteinRelation.TimeChange.euclideanNorm_smul]
  exact mul_le_mul_of_nonneg_left (sharp_inverse_gradient_bound i i W z) (abs_nonneg lam)

/-- Uniform smooth derivative bounds give a sample-independent scalar Lipschitz constant. -/
private theorem uniform_scalar_lipschitz {ι : Type*} {d : ℕ}
    {F : ι → Vec d → ℝ} (hF : EinsteinFull.Calculus.S1.UnifBdd F) :
    ∃ K : ℝ≥0, ∀ a, LipschitzWith K (F a) := by
  obtain ⟨C, hC⟩ := hF.2 1
  refine ⟨Real.toNNReal C, fun a => lipschitzWith_of_nnnorm_fderiv_le
    ((hF.1 a).differentiable (by simp)) fun x => ?_⟩
  change ‖fderiv ℝ (F a) x‖ ≤ (Real.toNNReal C : ℝ)
  rw [← norm_iteratedFDeriv_one]
  exact (hC a x).trans (Real.le_coe_toNNReal C)

/-- One global Lipschitz constant controls the inverse force gradient for every sample. -/
private theorem sharp_inverse_gradient_lipschitz {d : ℕ} (i : Fin d) :
    ∃ K : ℝ≥0, ∀ W : NoiseSample d, LipschitzWith K
      (gradient (fun y => (sharp_coordinate_homeomorph i W).symm y i)) := by
  classical
  have h (k : Fin d) := uniform_scalar_lipschitz
    (EinsteinFull.Calculus.S1.unifBdd_inverseCandidate i i k)
  choose K hK using h
  refine ⟨(∑ k, K k) * (2 * d), fun W => ?_⟩
  have hrow : LipschitzWith (∑ k, K k)
      (fun x k => inverseCandidate i (gradient (EinsteinFull.Work.W8.corrector W) x) i k) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    refine (dist_pi_le_iff (by positivity)).2 fun k => ?_
    exact ((hK k W).weaken (Finset.single_le_sum (fun _ _ => (zero_le : (0 : ℝ≥0) ≤ _)) (Finset.mem_univ k))).dist_le_mul x y
  have hc := hrow.comp (sharp_inverse_lipschitz i W)
  convert hc using 1
  funext z k
  let φ := sharp_coordinate_homeomorph i W
  obtain ⟨x, rfl⟩ := φ.surjective z
  rw [sharp_inverse_coordinate_gradient,
    ← inverseCandidate_eq_inv i _ (jacobianFactor_ne_zero_of_norm_le i _
      (EinsteinFull.Work.W8.corrector_gradient_bound W x))]
  simp [φ, Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, Matrix.transpose_apply]

/-- The Brownian-coordinate drift is globally Lipschitz for each signed force,
with its constant chosen before the sample. -/
private theorem sharp_transformed_drift_lipschitz {d : ℕ} (i : Fin d) (lam : ℝ) :
    ∃ K : ℝ≥0, ∀ W : NoiseSample d, LipschitzWith K
      (fun z => lam • gradient (fun y => (sharp_coordinate_homeomorph i W).symm y i) z) := by
  obtain ⟨K, hK⟩ := sharp_inverse_gradient_lipschitz i
  refine ⟨‖lam‖₊ * K, fun W => LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simp only [dist_eq_norm, ← smul_sub, norm_smul, NNReal.coe_mul, coe_nnnorm]
  calc
    ‖lam‖ * ‖gradient (fun y => (sharp_coordinate_homeomorph i W).symm y i) x -
      gradient (fun y => (sharp_coordinate_homeomorph i W).symm y i) y‖ ≤
        ‖lam‖ * (K * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using (hK W).dist_le_mul x y)
        (norm_nonneg lam)
    _ = _ := by ring

/-- Conditional assembly of the complete sharp harmonic statement. The explicit
family producer is a coverage request to the process foundation, pending its
proved interface; this helper does not close the graph reduction. -/
theorem sharp_harmonic_of_foundation
    (hFoundationReducedFamily :
      ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
        (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
        (∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω) →
        ∃ Y₀ : DiffusionFamily d, ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
          SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
            0 (Y₀ lam (0, ω)))
    (h0 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h1 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2) :
    node_app_u3A_sharp_u2D_harmonicStmt := by
  intro d hd P hP
  dsimp only
  intro D Q hQ
  let first : Fin d := ⟨0, by omega⟩
  obtain ⟨-, -, D', -, -, -, hD'⟩ := h0 d hd
  obtain ⟨Q', hQ', hsm', hmean'⟩ := hD' P hP
  have hmeasure : Q.measure = Q'.measure := hQ.trans hQ'.symm
  have hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω := by
    rw [hmeasure]
    exact hsm'.mono fun _ h => h.1
  have hsmb : ∀ᵐ ω ∂Q.measure, IsSmoothWithBounds D'.derivativeBound ω := by
    rw [hmeasure]
    exact hsm'
  have hmean : (∫ ω, clockDensity ω 0 ∂Q.measure) = 1 := by
    rw [hmeasure]
    exact hmean'
  have hclock : (∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Q) = 1 := by
    have hc : Continuous fun ω : FieldPair d => ω.2 (0 : Vec d) :=
      (continuous_eval_const (0 : Vec d)).comp continuous_snd
    unfold reducedLaw
    rw [integral_map EinsteinRelation.Probability.measurable_reduce.aemeasurable
      hc.aestronglyMeasurable]
    exact hmean
  refine ⟨fun W x => sharpHarmonic_pointwise first W x,
    homogenizedCoefficient_physicalPair_mulVec first Q hQ, ?_, ?_⟩
  · intro X hX covariance hcovariance
    obtain ⟨Y, hY, hrel⟩ := exists_reducedFamily_of_signedPhysical first Q hsm X hX
    obtain ⟨Λ, -, hall⟩ := h1 D.ellipticity D.one_le_ellipticity
    obtain ⟨-, -, hdiff⟩ := hall d hd D.dependenceRange D'.derivativeBound Q
      D.one_le_dependenceRange D'.derivativeBound_pos hsmb X Y hX hY hrel
    have heq : covariance = homogenizedCoefficient Q := by
      have hdiff' : HasDiffusivity Q.measure (originLaw (X 0))
          (homogenizedCoefficient Q) := by
        simpa only [hclock, inv_one, one_smul] using hdiff
      exact hcovariance.unique hdiff'
    rw [heq]
    exact homogenizedCoefficient_physicalPair_mulVec first Q hQ
  · intro lam hlam Y hY
    obtain ⟨Y₀, hY₀⟩ := hFoundationReducedFamily d hd D Q hsm
    obtain ⟨ell, hell⟩ := velocity_of_reducedFamily h1 hd D Q hsm D'.derivativeBound
      D'.derivativeBound_pos hsmb Y₀ hY₀ lam hlam Y hY
    exact ⟨ell, hell, sharp_velocity_first hd hP Q hQ lam Y hY ell hell⟩

/-- The announced pointwise reduced-law witnesses supply the family required by
the sharp harmonic consumer. This conditional helper gives no graph closure. -/
theorem sharp_harmonic_of_announced_reduced_foundation
    (c16_reduced_mp_exists : ∀ (d : ℕ) (hd : 2 ≤ d) (L R : ℝ)
      (Q : EnvironmentLaw d L R) (i : Fin d) (lam : ℝ),
      ∃ PY : QuenchedPathLaws d, ∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω)))
    (h0 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h1 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2) :
    node_app_u3A_sharp_u2D_harmonicStmt := by
  classical
  apply sharp_harmonic_of_foundation ?_ h0 h1
  intro d hd D Q _hsm
  choose Y hY using fun lam : ℝ =>
    c16_reduced_mp_exists d hd D.ellipticity D.dependenceRange Q
      (⟨0, by omega⟩ : Fin d) lam
  exact ⟨Y, hY⟩

end EinsteinFull.Blueprint
