import EinsteinFull.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.Regeneration.SbxS1JointSplitR01
import EinsteinFull.Calculus.C3RemainderMomentSupport
import EinsteinFull.Calculus.F2S3Section3KMConditionalAssemblerTakeover02

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal

noncomputable section
namespace SbxS1CouplingAssemblyR02

/-- Replace the exceptional environment rows by one good row, uniformly over starts. -/
theorem patch_reduced_kernel
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (hminor : ∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P (x, ω)) Δ δ R i) :
    ∃ P' : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure, ∀ x, P' (x, ω) = P (x, ω)) ∧
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P' ∧
      IsMarkovKernel P' ∧
      (∀ a, ∀ᵐ γ ∂P' a, γ 0 = a.1) ∧
      (∀ ω, HasSourceMinorization (fun x => P' (x, ω)) Δ δ R i) := by
  classical
  let Good : FieldPair d → Prop := fun ω =>
    (∃ hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω),
      ∃ r : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
          (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
          hω lam h0 h1, ∀ x, P (x, ω) = r.pathLaw x) ∧
    HasSourceMinorization (fun x => P (x, ω)) Δ δ R i
  have hgood : ∀ᵐ ω ∂Q.measure, Good ω := hP.and hminor
  obtain ⟨N, hsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hE : ∀ᵐ ω ∂Q.measure, ω ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not, Set.setOf_mem_eq] using hNzero
  obtain ⟨ω₀, hω₀⟩ := hE.exists
  have hG : ∀ ω, ω ∉ N → Good ω := by
    intro ω hω
    by_contra hn
    exact hω (hsub hn)
  let f : FieldPair d → FieldPair d := fun ω => if ω ∈ N then ω₀ else ω
  have hf : Measurable f := measurable_const.piecewise hNm measurable_id
  have hfGood : ∀ ω, Good (f ω) := by
    intro ω
    by_cases hω : ω ∈ N
    · simpa [f, hω] using hG ω₀ hω₀
    · simpa [f, hω] using hG ω hω
  let P' : QuenchedPathLaws d := P.comap (fun a => (a.1, f a.2))
    (measurable_fst.prodMk (hf.comp measurable_snd))
  have heq (x : Vec d) (ω : FieldPair d) : P' (x, ω) = P (x, f ω) := rfl
  have hae : ∀ᵐ ω ∂Q.measure, ∀ x, P' (x, ω) = P (x, ω) := by
    filter_upwards [hE] with ω hω
    intro x
    simp only [heq, f, ite_eq_right hω]
  refine ⟨P', hae, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hP, hae] with ω hω he
    obtain ⟨hr, r, hrow⟩ := hω
    exact ⟨hr, r, fun x => (he x).trans (hrow x)⟩
  · constructor
    intro a
    obtain ⟨_, r, hr⟩ := (hfGood a.2).1
    rw [heq, hr a.1]
    letI := r.pathLaw_isMarkovKernel
    infer_instance
  · intro a
    obtain ⟨_, r, hr⟩ := (hfGood a.2).1
    rw [heq, hr a.1]
    exact r.pathLaw_starts_at a.1
  · intro ω
    have h := (hfGood ω).2
    simpa only [heq] using h


/-- Conditional uniform primitive source minorization, with the coin parameter
chosen before the environment law and force. -/
def UniformSourceMinorization : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∀ l : ℝ, 1 ≤ l → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d),
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀.le h₁ P →
      ∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P (x, ω))
        (Regeneration.Renewal.regenDelta lam) δ (l / lam)
        (Regeneration.Renewal.forceCoord hd)

/-- The primitive uniform minorization and the regeneration-tail estimate give
actual couplings and nonreturn uniformly throughout the full positive range. -/
theorem full_range_coupling_nonreturn_of_uniform_source_minorization
    (htail : EinsteinFull.Blueprint.node_app_u3A_regen_u2D_tailsStmt)
    (hminor : UniformSourceMinorization) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ L : ℝ, 0 < L ∧ r₀ < 2 * L ∧
    ∀ l : ℝ, L ≤ l → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1),
      ∃ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
        ∃ _hK : EinsteinFull.IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K,
          Regeneration.annealedCoupledLaw Q.measure K
            (EinsteinFull.regenerationNoReturn hd (l / lam)) ≠ 0 := by
  classical
  intro d hd Λ₀ r₀
  obtain ⟨L, hL, hsep, htail'⟩ := EinsteinFull.c3Remainder_exists_noReturn_half htail d hd Λ₀ r₀
  refine ⟨max L 1, lt_of_lt_of_le hL (le_max_left _ _), ?_, ?_⟩
  · exact lt_of_lt_of_le hsep (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
  intro l hl
  have hlL : L ≤ l := le_trans (le_max_left _ _) hl
  have hl1 : 1 ≤ l := le_trans (le_max_right _ _) hl
  obtain ⟨δ, hδ₀, hδ₁, hmin⟩ := hminor d hd Λ₀ r₀ l hl1
  refine ⟨δ, hδ₀, hδ₁, ?_⟩
  intro Q lam h₀ h₁
  obtain ⟨P, hP⟩ := SbxS3Section3R01.joint_reduced_kernel_exists hd Q lam h₀.le h₁
  obtain ⟨P', _, hP', hMarkov, hstart, hmin'⟩ :=
    patch_reduced_kernel hd Q lam h₀.le h₁ (Regeneration.Renewal.regenDelta lam)
      δ (l / lam) (Regeneration.Renewal.forceCoord hd) P hP (hmin Q lam h₀ h₁ P hP)
  letI : IsMarkovKernel P' := hMarkov
  have hΔ := EinsteinRelation.regenDelta_pos h₀
  have hR : 0 < l / lam := div_pos (lt_of_lt_of_le zero_lt_one hl1) h₀
  let K := EinsteinFull.Regeneration.splitContinuousCouplingKernel
    (Regeneration.Renewal.regenDelta lam) hΔ δ (l / lam)
    (Regeneration.Renewal.forceCoord hd) hδ₀ hδ₁ hR P' hmin'
  have hK : EinsteinFull.IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P' K := by
    exact EinsteinFull.Regeneration.s1_canonical_all_clauses
      (Regeneration.Renewal.regenDelta lam) hΔ δ (l / lam)
      (Regeneration.Renewal.forceCoord hd) hδ₀ hδ₁ hR P' hmin' hstart hd Q h₀.le h₁ hP'
  refine ⟨P', K, hK, ?_⟩
  have hhalf := htail' l δ hlL hδ₀ hδ₁ Q lam h₀ h₁ P' K hK
  exact ne_of_gt (lt_of_lt_of_le (by norm_num) hhalf)

/-- The conditional full-range construction supplies the existing consumer. -/
theorem coupling_nonreturn_of_uniform_source_minorization
    (htail : EinsteinFull.Blueprint.node_app_u3A_regen_u2D_tailsStmt)
    (hminor : UniformSourceMinorization) :
    EinsteinFull.Blueprint.S3KMAdmissibleCouplingNonreturn := by
  intro d hd Λ₀ r₀
  obtain ⟨L, hL, hsep, hfull⟩ :=
    full_range_coupling_nonreturn_of_uniform_source_minorization htail hminor d hd Λ₀ r₀
  refine ⟨L, hL, hsep, ?_⟩
  intro l hl
  obtain ⟨δ, hδ₀, hδ₁, hc⟩ := hfull l hl
  exact ⟨δ, 1, hδ₀, hδ₁, zero_lt_one, le_rfl,
    fun Q lam h₀ h₁ _ => hc Q lam h₀ h₁⟩

end SbxS1CouplingAssemblyR02
