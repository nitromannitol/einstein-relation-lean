import EinsteinFull.Regeneration.ExitPayoffWeakSolution
import EinsteinFull.Regeneration.WeakGradientRescaling
import EinsteinFull.Regeneration.GMPRescaledEllipticity
import EinsteinRelation.Correctors.SpatialWeakCongruence

/-!
# Rescaled exit payoffs as weak solutions

For a zero-potential environment, the exit payoff of a smooth compactly supported payoff
from a bounded open set, translated by `c` and rescaled by the force `λ`, is a Sobolev
function on every bounded convex domain, with the rescaled weak gradient of its physical
Sobolev representative. Inside every open set mapped into the exit domain it solves the
divergence-form equation with the unit-force weight `exp (2 x₁)` and the rescaled
coefficient. The test functions are carried back to physical coordinates, where the
homogeneous weak equation of the exit payoff applies.
-/

open MeasureTheory Set Filter EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support EinsteinRelation.SpatialDirichlet
open scoped ENNReal Topology InnerProductSpace

namespace EinsteinFull.Regeneration

variable {d : ℕ}

/-- The value representative of a full force-weighted Sobolev element. -/
noncomputable def gmpForceH1ValueRep (hd : 2 ≤ d) (lam : ℝ)
    (u : EinsteinFull.Blueprint.GMPForceH1 hd lam) (x : Vec d) : ℝ :=
  (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u).value x

/-- The coordinate weak-gradient representative of a full force-weighted Sobolev element. -/
noncomputable def gmpForceH1Gradient (hd : 2 ≤ d) (lam : ℝ)
    (u : EinsteinFull.Blueprint.GMPForceH1 hd lam) (x : Vec d) : Vec d :=
  WithLp.ofLp ((densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u).weakGradient x)

theorem hasWeakGradient_gmpForceH1 (hd : 2 ≤ d) (lam : ℝ)
    (u : EinsteinFull.Blueprint.GMPForceH1 hd lam) :
    HasWeakGradient Set.univ (gmpForceH1ValueRep hd lam u) (gmpForceH1Gradient hd lam u) :=
  (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      u).distributionalGradient

theorem memLp_gmpForceH1Gradient (hd : 2 ≤ d) (lam : ℝ)
    (u : EinsteinFull.Blueprint.GMPForceH1 hd lam) (K : Set (Vec d)) (hK : IsCompact K) :
    MemLp (gmpForceH1Gradient hd lam u) 2 (volume.restrict K) := by
  have h := EinsteinFull.sbxS4_memLp_restrict_compact_of_density (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
    (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        u).gradient_memLp K hK
  exact (EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap.comp_memLp' h

/-- The value representative agrees with the physical value almost everywhere. -/
theorem gmpForceH1ValueRep_ae_eq (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hω : IsRegular L ω) (u : EinsteinFull.Blueprint.GMPForceH1 hd lam) :
    gmpForceH1ValueRep hd lam u =ᵐ[volume]
      (EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω u : Vec d → ℝ) := by
  have hr := EinsteinFull.Blueprint.gmpH1Representative_value_ae (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u
  have hp := (Measure.absolutelyContinuous_of_le_smul
    (sourcePhysicalMeasure_le_reduced ω hd lam L hω)).ae_eq hr
  have h : gmpForceH1ValueRep hd lam u =ᵐ[physicalReversibleMeasure ω hd lam]
      (EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω u : Vec d → ℝ) :=
    hp.trans (EinsteinFull.Blueprint.gmpPhysicalH1Value_ae_eq hd ω lam L hω u).symm
  exact (ae_withDensity_iff_volume_of_continuous_pos (physicalReversibleDensity ω hd lam)
    (physicalReversibleDensity_continuous ω hd lam) (physicalReversibleDensity_pos ω hd lam)
      _).mp h

/-- A symmetric matrix moves across the Euclidean dot product. -/
theorem vecDot_matVecMul_eq_dot (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.transpose = A)
    (v w : Vec d) : PDE.vecDot (PDE.matVecMul A v) w = dot v (A.mulVec w) := by
  have hvec : Matrix.vecMul w A = A.mulVec w := by
    rw [← Matrix.mulVec_transpose, hA]
  calc PDE.vecDot (PDE.matVecMul A v) w = dotProduct w (A.mulVec v) := by
        change ∑ k, (∑ j, A k j * v j) * w k = ∑ k, w k * (∑ j, A k j * v j)
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    _ = dotProduct (Matrix.vecMul w A) v := Matrix.dotProduct_mulVec w A v
    _ = dot v (A.mulVec w) := by
        rw [hvec, dotProduct_comm]
        rfl

/-- Scalars factor out of the coordinate flux pairing. -/
theorem vecDot_matVecMul_smul (s t : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (v w : Vec d) :
    PDE.vecDot (PDE.matVecMul (s • A) (t • v)) w = s * t * PDE.vecDot (PDE.matVecMul A v) w := by
  simp only [PDE.vecDot, PDE.matVecMul, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The chain rule for a test function composed with `x ↦ λ • (x - c)`. -/
theorem gradient_comp_affine (ψ : Vec d → ℝ) (hψ : Differentiable ℝ ψ) (lam : ℝ)
    (c x : Vec d) (j : Fin d) :
    gradient (fun y => ψ (lam • (y - c))) x j =
      lam * fderiv ℝ ψ (lam • (x - c)) (PDE.basisVec j) := by
  have hA : HasFDerivAt (fun y : Vec d => lam • (y - c)) (lam • ContinuousLinearMap.id ℝ (Vec d))
      x := ((hasFDerivAt_id x).sub_const c).const_smul lam
  have h : HasFDerivAt (fun y => ψ (lam • (y - c)))
      ((fderiv ℝ ψ (lam • (x - c))).comp (lam • ContinuousLinearMap.id ℝ (Vec d))) x :=
    (hψ (lam • (x - c))).hasFDerivAt.comp x hA
  change fderiv ℝ (fun y => ψ (lam • (y - c))) x (unitVector j) = _
  rw [h.fderiv, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  rfl

/-- The homogeneous physical weak equation of a zero-potential force-weighted Sobolev
element, tested against all zero-boundary elements of `D`, becomes the rescaled
divergence-form equation in every open set mapped into `D` by `z ↦ c + λ⁻¹ • z`. -/
theorem integral_rescaled_flux_eq_zero (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hω : IsRegular L ω) (hV : ∀ x, ω.2 x = 0) (hlam : 0 < lam)
    (u : EinsteinFull.Blueprint.GMPForceH1 hd lam) (D : Set (Vec d))
    (hE : ∀ w : physicalH1ZeroBoundary D hd lam,
      EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω u w.1 = 0)
    (c : Vec d) (S : Set (Vec d)) (hSD : ∀ z ∈ S, c + lam⁻¹ • z ∈ D)
    (ψ : PDE.WeakTestFunction S) :
    ∫ z in S, PDE.vecDot (PDE.matVecMul
        (Real.exp (2 * z (firstCoordinateIndex hd)) • ω.1 (c + lam⁻¹ • z))
        (lam⁻¹ • gmpForceH1Gradient hd lam u (c + lam⁻¹ • z))) (ψ.grad z) = 0 := by
  set i := firstCoordinateIndex hd
  let ψt : Vec d → ℝ := fun x => ψ.toFun (lam • (x - c))
  let h : Vec d ≃ₜ Vec d :=
    (Homeomorph.addRight (-c)).trans (Homeomorph.smulOfNeZero lam hlam.ne')
  have hh : ∀ x, h x = lam • (x - c) := fun x => by
    simp [h, sub_eq_add_neg]
  have hψt : ψt = ψ.toFun ∘ h := by
    funext x
    simp only [ψt, Function.comp_apply, hh]
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψt :=
    ψ.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul lam)
  have hψc : HasCompactSupport ψt := by
    rw [hψt]
    exact ψ.hasCompactSupport.comp_homeomorph h
  have hψD : tsupport ψt ⊆ D := by
    rw [hψt, tsupport_comp_eq_preimage]
    intro x hx
    have hxD := hSD _ (ψ.tsupport_subset hx)
    rwa [hh, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul, add_sub_cancel] at hxD
  let w := physicalH1SmoothTest hd lam ψt hψs hψc
  have hw : w ∈ physicalH1ZeroBoundary D hd lam :=
    physicalH1SmoothTest_mem_zeroBoundary D hd lam ψt ⟨hψs, hψc, hψD⟩
  have h0 : EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω u w = 0 := hE ⟨w, hw⟩
  have hgu := EinsteinFull.Blueprint.gmpPhysicalH1Gradient_ae hd ω lam L hω u
  have hgw : (EinsteinFull.Blueprint.gmpPhysicalH1GradientContinuousLinear hd ω lam L hω w :
      Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[physicalReversibleMeasure ω hd lam]
      fun x => (EuclideanSpace.equiv (Fin d) ℝ).symm (gradient ψt x) :=
    (EinsteinFull.Blueprint.gmpPhysicalH1Gradient_ae_spaceGradient hd ω lam L hω w).trans
      ((Measure.absolutelyContinuous_of_le_smul
        (sourcePhysicalMeasure_le_reduced ω hd lam L hω)).ae_eq
          (physicalH1SmoothTest_gradient hd lam ψt hψs hψc))
  have hint : EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω u w =
      ∫ x, (1 / 2 : ℝ) * dot (gmpForceH1Gradient hd lam u x)
        ((ω.1 x).mulVec (gradient ψt x)) ∂physicalReversibleMeasure ω hd lam := by
    unfold EinsteinFull.Blueprint.gmpPhysicalH1Energy
    apply integral_congr_ae
    filter_upwards [hgu, hgw] with x h1 h2
    rw [h1, h2]
    rfl
  let H : Vec d → ℝ := fun x => physicalReversibleDensity ω hd lam x *
    ((1 / 2 : ℝ) * dot (gmpForceH1Gradient hd lam u x) ((ω.1 x).mulVec (gradient ψt x)))
  have hH0 : ∫ x, H x = 0 := by
    have hc := EinsteinFull.Work.W5.gantert_integral_physicalMeasure hd ω lam
      (fun x => (1 / 2 : ℝ) * dot (gmpForceH1Gradient hd lam u x)
        ((ω.1 x).mulVec (gradient ψt x)))
    exact hc.symm.trans (hint.symm.trans h0)
  have hl : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam.ne'
  let K : ℝ := 2 * lam⁻¹ * lam⁻¹ * Real.exp (-(2 * lam * c i))
  have hpt : ∀ z : Vec d, PDE.vecDot (PDE.matVecMul
      (Real.exp (2 * z i) • ω.1 (c + lam⁻¹ • z))
      (lam⁻¹ • gmpForceH1Gradient hd lam u (c + lam⁻¹ • z))) (ψ.grad z) =
      K * H (c + lam⁻¹ • z) := by
    intro z
    set x := c + lam⁻¹ • z with hxdef
    have hx : lam • (x - c) = z := by
      rw [hxdef, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
    have hgrad : gradient ψt x = lam • ψ.grad z := by
      funext j
      rw [gradient_comp_affine ψ.toFun (ψ.contDiff.differentiable (by simp)) lam c x j, hx]
      rfl
    have hdens : physicalReversibleDensity ω hd lam x =
        Real.exp (2 * lam * c i) * Real.exp (2 * z i) := by
      rw [physicalReversibleDensity_eq_source_formula, hV, ← Real.exp_add]
      congr 1
      have hxi : x i = c i + lam⁻¹ * z i := by
        rw [hxdef]
        rfl
      change 2 * lam * x i - 2 * 0 = _
      rw [hxi]
      linear_combination 2 * z i * hl
    have hsym : (ω.1 x).transpose = ω.1 x := (hω.1 x).1
    rw [vecDot_matVecMul_smul, vecDot_matVecMul_eq_dot _ hsym]
    simp only [H, K, hdens, hgrad, Matrix.mulVec_smul]
    have hdot : dot (gmpForceH1Gradient hd lam u x) (lam • (ω.1 x).mulVec (ψ.grad z)) =
        lam * dot (gmpForceH1Gradient hd lam u x) ((ω.1 x).mulVec (ψ.grad z)) := by
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hdot]
    have he : Real.exp (-(2 * lam * c i)) * Real.exp (2 * lam * c i) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    linear_combination (-(Real.exp (2 * z i) * lam⁻¹ *
      dot (gmpForceH1Gradient hd lam u x) ((ω.1 x).mulVec (ψ.grad z)) * lam * lam⁻¹)) * he +
      (-(Real.exp (2 * z i) * lam⁻¹ *
        dot (gmpForceH1Gradient hd lam u x) ((ω.1 x).mulVec (ψ.grad z)))) * hl
  have hzero : ∀ z, z ∉ S → PDE.vecDot (PDE.matVecMul
      (Real.exp (2 * z i) • ω.1 (c + lam⁻¹ • z))
      (lam⁻¹ • gmpForceH1Gradient hd lam u (c + lam⁻¹ • z))) (ψ.grad z) = 0 := by
    intro z hz
    have hzt : z ∉ tsupport ψ.toFun := fun h' => hz (ψ.tsupport_subset h')
    have hg : ψ.grad z = 0 := by
      funext j
      simp only [PDE.WeakTestFunction.grad_apply, PDE.WeakTestFunction.partialDeriv,
        fderiv_of_notMem_tsupport ℝ hzt, zero_apply, Pi.zero_apply]
    rw [hg]
    simp [PDE.vecDot]
  have hcomp : ∫ z, H (c + lam⁻¹ • z) =
      |((lam⁻¹) ^ Module.finrank ℝ (Vec d))⁻¹| • ∫ y, H (c + y) :=
    Measure.integral_comp_smul volume (fun y => H (c + y)) lam⁻¹
  have htr : ∫ y, H (c + y) = ∫ y, H y := integral_add_left_eq_self (μ := volume) H c
  calc (∫ z in S, PDE.vecDot (PDE.matVecMul
        (Real.exp (2 * z i) • ω.1 (c + lam⁻¹ • z))
        (lam⁻¹ • gmpForceH1Gradient hd lam u (c + lam⁻¹ • z))) (ψ.grad z))
      = ∫ z, PDE.vecDot (PDE.matVecMul
        (Real.exp (2 * z i) • ω.1 (c + lam⁻¹ • z))
        (lam⁻¹ • gmpForceH1Gradient hd lam u (c + lam⁻¹ • z))) (ψ.grad z) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    _ = ∫ z, K * H (c + lam⁻¹ • z) := by
        congr 1
        funext z
        exact hpt z
    _ = K * ∫ z, H (c + lam⁻¹ • z) := integral_const_mul K _
    _ = 0 := by rw [hcomp, htr, hH0, smul_zero, mul_zero]

section Realization

variable {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω}
  {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}

/-- For a zero-potential environment, a function agreeing on a bounded convex domain `U` with
the translated and rescaled exit payoff of a smooth compactly supported payoff is a Sobolev
function on `U`, and it solves the unit-force weighted rescaled equation in every open subset
of `U` mapped into the exit domain. -/
theorem exists_rescaled_exitPayoff_solution
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁) (hV : ∀ x, ω.2 x = 0)
    (hlam : 0 < lam) (D : Set (Vec d)) (hD : IsOpen D)
    (hDm : physicalReversibleMeasure ω hd lam D ≠ ⊤)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hfin : ∀ x, ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime D γ ≠ ⊤)
    (hτ : ∀ x, Integrable (fun γ => (MarkovProcess.ContinuousPath.exitTime D γ).toReal)
      (G.pathLaw x)) (M : ℝ)
    (hM : ∀ x, ∫ γ, (MarkovProcess.ContinuousPath.exitTime D γ).toReal ∂G.pathLaw x ≤ M)
    (c : Vec d) (U : Set (Vec d)) (hU : PDE.IsOpenBoundedConvexDomain U)
    (F : Vec d → ℝ) (hF : ∀ z ∈ U, F z = exitPayoff G D φ (c + lam⁻¹ • z))
    (S : Set (Vec d)) (hS : IsOpen S) (hSU : S ⊆ U) (hSD : ∀ z ∈ S, c + lam⁻¹ • z ∈ D) :
    ∃ u : PDE.H1Function U, u.toFun = F ∧
      PDE.IsWeakDivergenceFormL2SolutionOn
        (fun x => Real.exp (2 * x (firstCoordinateIndex hd)) • gmpRescaledCoefficient ω c lam x)
        S (u.restrict hS hSU) 0 0 := by
  obtain ⟨u, -, hval, hE⟩ := exists_exitPayoff_weak_solution G D hD hDm φ hφ hφc hfin hτ M hM
  obtain ⟨Bφ, hBφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hBφ' : ∀ y, |φ y| ≤ Bφ := fun y => by simpa only [Real.norm_eq_abs] using hBφ y
  have hPm : Measurable (exitPayoff G D φ) :=
    measurable_exitPayoff G D hD φ hφ.continuous.measurable
  have hPb : ∀ x, |exitPayoff G D φ x| ≤ Bφ := abs_exitPayoff_le G D φ Bφ hBφ'
  have hPL : ∀ K : Set (Vec d), IsCompact K →
      MemLp (exitPayoff G D φ) 2 (volume.restrict K) := by
    intro K hK
    have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact MemLp.of_bound hPm.aestronglyMeasurable Bφ
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hPb x)
  have hvol : gmpForceH1ValueRep hd lam u =ᵐ[volume] exitPayoff G D φ :=
    (gmpForceH1ValueRep_ae_eq hd ω lam L hω u).trans
      ((ae_withDensity_iff_volume_of_continuous_pos (physicalReversibleDensity ω hd lam)
        (physicalReversibleDensity_continuous ω hd lam)
          (physicalReversibleDensity_pos ω hd lam) _).mp hval)
  have hwP : HasWeakGradient Set.univ (exitPayoff G D φ) (gmpForceH1Gradient hd lam u) :=
    Correctors.hasWeakGradient_congr_ae isOpen_univ (hasWeakGradient_gmpForceH1 hd lam u)
      (by rw [Measure.restrict_univ]; exact hvol) EventuallyEq.rfl
  have hres := hasWeakGradient_affine_rescale (exitPayoff G D φ) (gmpForceH1Gradient hd lam u)
    hPL (memLp_gmpForceH1Gradient hd lam u) hwP c lam⁻¹ (inv_pos.mpr hlam)
  have hFae : (fun z => exitPayoff G D φ (c + lam⁻¹ • z)) =ᵐ[volume.restrict U] F :=
    ae_restrict_of_forall_mem hU.isOpen.measurableSet fun z hz => (hF z hz).symm
  have hwF : HasWeakGradient U F
      (fun z => lam⁻¹ • gmpForceH1Gradient hd lam u (c + lam⁻¹ • z)) :=
    Correctors.hasWeakGradient_congr_ae hU.isOpen
      (Correctors.hasWeakGradient_mono (subset_univ U) hres) hFae EventuallyEq.rfl
  have hUb : Bornology.IsBounded U := hU.isBoundedDomain.isBounded
  have hUfin : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hUb.measure_lt_top.ne
  have hFL : MemLp F 2 (volume.restrict U) := by
    have hm : Measurable (fun z : Vec d => c + lam⁻¹ • z) :=
      measurable_const.add (measurable_id.const_smul lam⁻¹)
    have h : MemLp (fun z => exitPayoff G D φ (c + lam⁻¹ • z)) 2 (volume.restrict U) :=
      MemLp.of_bound (hPm.comp hm).aestronglyMeasurable Bφ
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hPb _)
    exact h.ae_eq hFae
  have hGL : MemLp (fun z => lam⁻¹ • gmpForceH1Gradient hd lam u (c + lam⁻¹ • z)) 2
      (volume.restrict U) :=
    (memLp_comp_affine (gmpForceH1Gradient hd lam u) (memLp_gmpForceH1Gradient hd lam u) c
      lam⁻¹ lam⁻¹ (inv_pos.mpr hlam) (closure U) hUb.isCompact_closure).mono_measure
      (Measure.restrict_mono_set _ subset_closure)
  let v : PDE.H1Function U :=
    { toFun := F
      grad := fun z => lam⁻¹ • gmpForceH1Gradient hd lam u (c + lam⁻¹ • z)
      memL2 := hFL
      gradMemL2 := fun j => (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).comp_memLp' hGL
      hasWeakGradient := by
        intro j ψ hψ hc hs
        exact (hwF j).2.2 ψ ⟨hψ, hc, hs⟩ }
  refine ⟨v, rfl, ⟨⟨?_, MemLp.zero, fun j => MemLp.zero⟩, ?_⟩⟩
  · obtain ⟨lam', Λ', hEll⟩ :=
      gmpRescaledCoefficient_weighted_elliptic hL ω hω c lam (firstCoordinateIndex hd) hU
    have hfl := PDE.memVectorL2On_matVecMul_of_isEllipticFieldOn hEll v.gradMemL2
    intro j
    exact (hfl j).mono_measure (Measure.restrict_mono hSU le_rfl)
  · intro ψ
    have h := integral_rescaled_flux_eq_zero hd ω lam L hω hV hlam u D hE c S hSD ψ
    have hr : (∫ x in S, (0 : Vec d → ℝ) x * ψ x) -
        ∫ x in S, PDE.vecDot ((0 : Vec d → Vec d) x) (ψ.grad x) = 0 := by
      simp [PDE.vecDot]
    exact h.trans hr.symm

end Realization

end EinsteinFull.Regeneration
