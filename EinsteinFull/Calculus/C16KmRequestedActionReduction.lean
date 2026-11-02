import EinsteinFull.Calculus.C18KmActualCovarianceConsumer
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinFull.Blueprint.G1.Proofs.SbxS4KmWitnessAssembly

/-! Connect the requested bounded action to the supplied coupling covariance. -/

open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The requested martingale-problem action identifies every bounded supplied average. -/
theorem c16_km_bounded_action_of_requested
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (q : ℝ≥0∞) (hq : 2 ≤ q) (lam : ℝ) (t : ℝ≥0) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq⟩
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (hrequested : (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (P (0, ω))) →
      ∀ (t : ℝ≥0) (f : BoundedContinuousFunction (FieldPair d) ℂ),
      (fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)) =ᵐ[Q.measure]
        fun ω => forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd)
          (lam : ℂ) t (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f) (reduce ω))
    (T : Lp ℂ q (reducedLaw Q) →L[ℂ] Lp ℂ 2 Q.measure)
    (hrep : ∀ H, T H =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, H (translate (γ t) (reduce ω)) ∂P (0, ω))
    (f : BoundedContinuousFunction (FieldPair d) ℂ),
    T (BoundedContinuousFunction.toLp q (reducedLaw Q) ℂ f) =ᵐ[Q.measure]
      fun ω => forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd)
        (lam : ℂ) t (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f) (reduce ω) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq⟩
  intro P K l δ h0 h1 hK hrequested T hrep f
  have hmp : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (P (0, ω)) := by
    filter_upwards [SbxS4Dynkin.reduced_kernel_solves_martingale_problem hd Q lam h0 h1 P hK.2.2.1] with ω hω
    exact hω 0
  let F := BoundedContinuousFunction.toLp q (reducedLaw Q) ℂ f
  have he := SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q lam h0 h1 P hK.2.2.1 t
    (Lp.stronglyMeasurable F).measurable f.continuous.measurable
    (BoundedContinuousFunction.coeFn_toLp q (reducedLaw Q) ℂ f)
  have hfirst : T F =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω) := by
    filter_upwards [hrep F, he] with ω ht hω
    exact ht.trans (integral_congr_ae hω)
  exact hfirst.trans (hrequested hmp t f)


/-- The requested action identifies the actual coupled covariance. -/
theorem c16_km_actual_covariance_of_requested_action
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (q : ℝ≥0∞) (hq : 2 ≤ q) (hqfin : q ≠ ∞) (lam : ℝ) (t : ℝ≥0) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq⟩
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (hrequested : (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (P (0, ω))) →
      ∀ (t : ℝ≥0) (f : BoundedContinuousFunction (FieldPair d) ℂ),
      (fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)) =ᵐ[Q.measure]
        fun ω => forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd)
          (lam : ℂ) t (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f) (reduce ω))
    (T : Lp ℂ q (reducedLaw Q) →L[ℂ] Lp ℂ 2 Q.measure)
    (hrep : ∀ H, T H =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, H (translate (γ t) (reduce ω)) ∂P (0, ω))
    (F G : Lp ℂ 2 (reducedLaw Q))
    (hGq : MemLp (G : FieldPair d → ℂ) q (reducedLaw Q))
    (hend : MemLp (fun w => G (sbxS4CoupledEndpoint t w)) 2
      (Regeneration.annealedCoupledLaw Q.measure K)),
    (∫ ω, F ω * forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd)
      (lam : ℂ) t G ω ∂reducedLaw Q) =
      ∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
        ∂Regeneration.annealedCoupledLaw Q.measure K := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq⟩
  intro P K l δ h0 h1 hK hrequested T hrep F G hGq hend
  exact c18_km_actual_covariance_of_dense_action hd Q q hq hqfin lam t
    T P K l δ h0 h1 hK hrep
    (c16_km_bounded_action_of_requested hd Q q hq lam t
      P K l δ h0 h1 hK hrequested T hrep) F G hGq hend

/-- Given the requested action, any compatible coupling transfers the positive
path covariance estimate to the actual complex semigroup. -/
theorem c16_km_positive_covariance_of_requested_action
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀),
    letI := reducedLaw_probability Q
    ∀ (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (_hrequested : (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (P (0, ω))) →
        ∀ (t : ℝ≥0) (f : BoundedContinuousFunction (FieldPair d) ℂ),
        (fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)) =ᵐ[Q.measure]
          fun ω => forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd)
            (lam : ℂ) t (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f) (reduce ω))
      (S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    IsComplexEnvironmentSemigroup Q (Regeneration.Renewal.forceCoord hd) (lam : ℂ) S →
    ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
    IsRealLocalObservation Q (A / lam) F → IsRealLocalObservation Q (A / lam) G →
    MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
    ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
      C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨lD, hlD, hsD, hdecay⟩ :=
    sbxS4_positive_complex_integrable_covariance_of_deps hfactor hphase hmany hrem d hd Λ₀ r₀
  obtain ⟨lR, pR, CR, hlR, hsR, hpR, hCR, hgrowth⟩ :=
    sbxS4_coupled_endpoint_memLp_two_of_remainder hrem d hd Λ₀ r₀
  obtain ⟨lT, pT, CT, hlT, hsT, hpT, hCT, hoperator⟩ :=
    sbxS4_supplied_average_operator_of_remainder hrem d hd Λ₀ r₀
  refine ⟨max lD (max lR lT), hlD.trans_le (le_max_left _ _),
    hsD.trans_le (by linarith only [le_max_left lD (max lR lT)]), ?_⟩
  intro l hl δ hδ0 hδ1
  have hlD' := (le_max_left lD (max lR lT)).trans hl
  have hlR' := (le_max_left lR lT).trans ((le_max_right lD (max lR lT)).trans hl)
  have hlT' := (le_max_right lR lT).trans ((le_max_right lD (max lR lT)).trans hl)
  obtain ⟨pD, c, C, hpD, hc, hC, hbound⟩ := hdecay l hlD' δ hδ0 hδ1
  refine ⟨max pD (max (2 * pR) (2 * pT)), c, C,
    hpD.trans (le_max_left _ _), hc, hC, ?_⟩
  intro Q
  let := reducedLaw_probability Q
  intro lam h0 h1 P K hK hD hrequested S hS A hA F G hFl hGl hFp hGp hmean t
  let p := max pD (max (2 * pR) (2 * pT))
  have hpD' : ENNReal.ofReal pD ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hpR' : 2 * ENNReal.ofReal pR ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_right _ _))
  have hpT' : 2 * ENNReal.ofReal pT ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_right _ _))
  have hq : (2 : ℝ≥0∞) ≤ 2 * ENNReal.ofReal pT := by
    have h : (1 : ℝ≥0∞) ≤ ENNReal.ofReal pT := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ pT by linarith)
    simpa using mul_le_mul_of_nonneg_left h (show (0 : ℝ≥0∞) ≤ 2 by norm_num)
  have hqfin : 2 * ENNReal.ofReal pT ≠ ∞ := by
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  let : Fact (1 ≤ 2 * ENNReal.ofReal pT) := ⟨le_trans (by norm_num) hq⟩
  obtain ⟨T, hrep, _, _⟩ := hoperator Q lam h0 h1 l δ hlT' hδ0 hδ1 P K hK hD t
  have hend := (hgrowth Q lam h0 h1 l δ hlR' hδ0 hδ1 P K hK hD G
    (Lp.stronglyMeasurable G).measurable (hGp.mono_exponent hpR') t).1
  have heq := c16_km_actual_covariance_of_requested_action hd Q
    (2 * ENNReal.ofReal pT) hq hqfin lam t P K l δ h0.le h1 hK hrequested T hrep
    F G (hGp.mono_exponent hpT') hend
  have hb := (hbound Q lam h0 h1 P K hK hD A hA F G hFl hGl
    (hFp.mono_exponent hpD') (hGp.mono_exponent hpD') hmean t).2
  have hFnorm := ENNReal.toReal_mono hFp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (F : FieldPair d → ℂ)) hpD')
  have hGnorm := ENNReal.toReal_mono hGp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (G : FieldPair d → ℂ)) hpD')
  rw [hS.eq_forcedComplexEvolution, heq]
  exact hb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hFnorm (mul_nonneg hC.le (Real.exp_pos _).le))
    hGnorm ENNReal.toReal_nonneg (by positivity))

/-- Conditional consumer for the two requested foundation producers. -/
theorem c16_km_decomp_of_requested_bounded_action
    (foundation_km_supplied_bounded_action :
      ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
      letI := reducedLaw_probability Q
      ∀ (lam : ℝ) (_h0 : 0 ≤ lam) (_h1 : lam ≤ 1) (Y : QuenchedPathLaws d),
        (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
          (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (Y (0,ω))) →
        ∀ (t : ℝ≥0) (f : BoundedContinuousFunction (FieldPair d) ℂ),
        (fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0,ω)) =ᵐ[Q.measure]
          (fun ω => forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd)
            (lam : ℂ) t (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f) (reduce ω)))
    (foundation_km_admissible_coupling_nonreturn :
      ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
        ∃ L : ℝ, 0 < L ∧ r₀ < 2 * L ∧
        ∀ l : ℝ, L ≤ l →
        ∃ δa lamc : ℝ, 0 < δa ∧ δa < 1 ∧ 0 < lamc ∧ lamc ≤ 1 ∧
        ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1),
          lam ≤ lamc → ∃ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
          ∃ _hK : IsRegenerationCoupling hd Q lam l δa h0.le h1 P K,
            Regeneration.annealedCoupledLaw Q.measure K
              (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    node_rt_u3A_km_u2D_decompStmt := by
  intro d hd Λ₀ r₀
  obtain ⟨L, hL, hsepL, hcoupling⟩ :=
    foundation_km_admissible_coupling_nonreturn d hd Λ₀ r₀
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
    obtain ⟨P, K, hK, hD⟩ := hexists Q lam h0 h1 hle
    exact hcov Q lam h0 h1 P K hK hD
      (foundation_km_supplied_bounded_action d hd Λ₀ r₀ Q lam h0.le h1 P)
      S hS A hA F G hF hG hFp hGp hzero t
  have hsigned := sbxS4_positive_covariance_bound_mono_signed
    (Λ := Λ₀) (r₀ := r₀) (Regeneration.Renewal.forceCoord hd)
    (l := l) (p := pD) (c := cD) (C := CD) (lam₀ := lamc)
    (p' := p) (c' := c) (C' := C) (lam₀' := lam₀)
    (hl₀.trans_le hl) hCD.le hpD' hcD' hCD' hlamc' hpositive
  refine ⟨p, c, C, lam₀, hp, hc, hC, hlam₀, hlam₀1, ?_⟩
  intro Q
  exact ⟨hkm Q, hsigned Q⟩

end EinsteinFull.Blueprint
