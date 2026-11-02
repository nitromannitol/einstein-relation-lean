import EinsteinFull.Calculus.F2S3Section3KMConditionalAssemblerTakeover02
import EinsteinFull.Blueprint.G1.Proofs.SbxS4RemainderMoment
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeRealSemigroup

/-!
# `rt:km-decomp` from one coupling input

The conditional reduction `c16_km_decomp_of_requested_bounded_action` uses its bounded-action
input only at the path law `P` of the coupling supplied by its nonreturn input. So the two inputs
combine into one: for each force there is a regeneration coupling with nonreturn whose own path
law acts on bounded observables as the forced environment evolution. This replaces the
bounded action for every solution of the reduced martingale problem on every regular law
(`S3KMSuppliedBoundedAction`), which the V2 process inputs do not give off the smooth scope.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- A uniform positive-force regeneration coupling with nonreturn whose path law has the
forced environment evolution as its bounded endpoint action. -/
def S3KMCouplingActionNonreturn : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
  ∃ L : ℝ, 0 < L ∧ r₀ < 2 * L ∧
  ∀ l : ℝ, L ≤ l →
  ∃ δa lamc : ℝ, 0 < δa ∧ δa < 1 ∧ 0 < lamc ∧ lamc ≤ 1 ∧
  ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1),
    lam ≤ lamc → ∃ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∃ _hK : IsRegenerationCoupling hd Q lam l δa h0.le h1 P K,
      Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0 ∧
      letI := reducedLaw_probability Q
      ∀ (t : ℝ≥0) (f : BoundedContinuousFunction (FieldPair d) ℂ),
        (fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)) =ᵐ[Q.measure]
          fun ω => forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd)
            (lam : ℂ) t (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f) (reduce ω)

/-- The two inputs of the conditional assembler give the combined coupling input. -/
theorem s3KMCouplingActionNonreturn_of_supplied
    (haction : S3KMSuppliedBoundedAction) (hcoupling : S3KMAdmissibleCouplingNonreturn) :
    S3KMCouplingActionNonreturn := by
  intro d hd Λ₀ r₀
  obtain ⟨L, hL, hsep, h⟩ := hcoupling d hd Λ₀ r₀
  refine ⟨L, hL, hsep, fun l hl => ?_⟩
  obtain ⟨δa, lamc, hδa0, hδa1, hlamc, hlamc1, hexists⟩ := h l hl
  refine ⟨δa, lamc, hδa0, hδa1, hlamc, hlamc1, fun Q lam h0 h1 hle => ?_⟩
  obtain ⟨P, K, hK, hD⟩ := hexists Q lam h0 h1 hle
  refine ⟨P, K, hK, hD, ?_⟩
  letI := reducedLaw_probability Q
  have hmp : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (P (0, ω)) := by
    filter_upwards [SbxS4Dynkin.reduced_kernel_solves_martingale_problem hd Q lam h0.le h1 P
      hK.2.2.1] with ω hω
    exact hω 0
  exact haction d hd Λ₀ r₀ Q lam h0.le h1 P hmp

/-- Coupling existence with nonreturn and the GMP reduced-kernel action give the combined
coupling input: the coupling's path law is a GMP reduced kernel. -/
theorem s3KMCouplingActionNonreturn_of_gmpAction
    (hact : SbxS4Dynkin.GMPReducedKernelAction) (hcoupling : S3KMAdmissibleCouplingNonreturn) :
    S3KMCouplingActionNonreturn := by
  intro d hd Λ₀ r₀
  obtain ⟨L, hL, hsep, h⟩ := hcoupling d hd Λ₀ r₀
  refine ⟨L, hL, hsep, fun l hl => ?_⟩
  obtain ⟨δa, lamc, hδa0, hδa1, hlamc, hlamc1, hexists⟩ := h l hl
  refine ⟨δa, lamc, hδa0, hδa1, hlamc, hlamc1, fun Q lam h0 h1 hle => ?_⟩
  obtain ⟨P, K, hK, hD⟩ := hexists Q lam h0 h1 hle
  refine ⟨P, K, hK, hD, ?_⟩
  letI := reducedLaw_probability Q
  intro t f
  let F := BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f
  filter_upwards [hact d hd Λ₀ r₀ Q lam h0.le h1 P hK.2.2.1 t F,
    SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q lam h0.le h1 P hK.2.2.1 t
      (Lp.stronglyMeasurable F).measurable f.continuous.measurable
      (BoundedContinuousFunction.coeFn_toLp 2 (reducedLaw Q) ℂ f)] with ω hω hF
  calc ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)
      = ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω) :=
        integral_congr_ae (hF.mono fun _ h => h.symm)
    _ = _ := hω.2.symm

/-- The GMP reduced-kernel action on laws with Assumption 1.2 smoothness. -/
def GMPReducedKernelActionSmooth : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    SbxS4Dynkin.GMPReducedKernelActionAt hd Q

/-- On smooth laws the GMP reduced kernel solves the reduced martingale problem, so the
real-semigroup contract V2 gives its action. -/
theorem gmpReducedKernelActionSmooth_of_real
    (hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2) :
    GMPReducedKernelActionSmooth := by
  intro d hd D Q hQ lam h0 h1 P hP t f
  have hmp : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator
      (EinsteinRelation.External.GantertSection7Support.firstCoordinateIndex hd) ω lam)
      0 (P (0, ω)) := by
    filter_upwards [SbxS4Dynkin.reduced_kernel_solves_martingale_problem hd Q lam h0 h1 P hP]
      with ω hω
    exact hω 0
  exact (hreal d hd D Q hQ lam).2.2.2.2 P hmp t f

/-- `rt:km-decomp` from its four graph dependencies and the combined coupling input. -/
theorem s3_km_decomp_of_coupling_action
    (hcoupling : S3KMCouplingActionNonreturn)
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    node_rt_u3A_km_u2D_decompStmt := by
  intro d hd Λ₀ r₀
  obtain ⟨L, hL, hsepL, hcoupling⟩ := hcoupling d hd Λ₀ r₀
  obtain ⟨lD, hlD, hsepD, hdecay⟩ :=
    c16_km_positive_covariance_of_requested_action hfactor hphase hmany hrem d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hsep, hcommon⟩ :=
    sbxS4_common_positive_witnesses_with_constraints_of_deps hfactor hphase hmany hrem
      d hd Λ₀ r₀ (max L lD)
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ0 hδ1
  have hlL : L ≤ l := (le_max_left L lD).trans (hcommon.1.trans hl)
  have hlD' : lD ≤ l := (le_max_right L lD).trans (hcommon.1.trans hl)
  obtain ⟨δa, lamc, hδa0, hδa1, hlamc, hlamc1, hexists⟩ := hcoupling l hlL
  obtain ⟨pD, cD, CD, hpD, hcD, hCD, hcov⟩ := hdecay l hlD' δa hδa0 hδa1
  obtain ⟨p, c, C, lam₀, hp, hpD', hc, hcD', hC, hCD', hlam₀, hlam₀1,
    hlamc', hkm, _hpath⟩ := hcommon.2 l hl δ hδ0 hδ1 δa hδa0 hδa1 pD cD CD lamc hcD hlamc
  have hpositive : ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ), 0 < lam → lam ≤ lamc →
      ∀ S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q (Regeneration.Renewal.forceCoord hd) (lam : ℂ) S →
      ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / lam) F → IsRealLocalObservation Q (A / lam) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal pD) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal pD) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
        CD * Real.exp (CD * A - cD * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal pD) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal pD) (reducedLaw Q)).toReal := by
    intro Q lam h0 hle S hS A hA F G hF hG hFp hGp hzero t
    let := reducedLaw_probability Q
    have h1 : lam ≤ 1 := hle.trans hlamc1
    obtain ⟨P, K, hK, hD, hact⟩ := hexists Q lam h0 h1 hle
    exact hcov Q lam h0 h1 P K hK hD (fun _ => hact) S hS A hA F G hF hG hFp hGp hzero t
  have hsigned := sbxS4_positive_covariance_bound_mono_signed
    (Λ := Λ₀) (r₀ := r₀) (Regeneration.Renewal.forceCoord hd)
    (l := l) (p := pD) (c := cD) (C := CD) (lam₀ := lamc)
    (p' := p) (c' := c) (C' := C) (lam₀' := lam₀)
    (hl₀.trans_le hl) hCD.le hpD' hcD' hCD' hlamc' hpositive
  refine ⟨p, c, C, lam₀, hp, hc, hC, hlam₀, hlam₀1, ?_⟩
  intro Q
  exact ⟨hkm Q, hsigned Q⟩

end EinsteinFull.Blueprint
