import EinsteinRelation.Diffusion.GMPFamily
import EinsteinFull.External.Source.GMPSplitCoupling

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal

noncomputable section
namespace SbxS3Section3R01

/-- Replace the exceptional environment rows by one good row, uniformly over starts. -/
theorem clean_patch_reduced_kernel
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

/-- The same patch applies to the positive auxiliary force `|lam|`, throughout
its full range. The minorization is an explicit input. -/
theorem clean_patch_reduced_kernel_abs
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h1 : |lam| ≤ 1)
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q |lam| (abs_nonneg lam) h1 P)
    (hminor : ∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P (x, ω)) Δ δ R i) :
    ∃ P' : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure, ∀ x, P' (x, ω) = P (x, ω)) ∧
      IsGMPReducedKernel hd Q.ellipticity_parameter Q |lam| (abs_nonneg lam) h1 P' ∧
      IsMarkovKernel P' ∧
      (∀ a, ∀ᵐ γ ∂P' a, γ 0 = a.1) ∧
      (∀ ω, HasSourceMinorization (fun x => P' (x, ω)) Δ δ R i) :=
  clean_patch_reduced_kernel hd Q |lam| (abs_nonneg lam) h1 Δ δ R i P hP hminor

end SbxS3Section3R01
