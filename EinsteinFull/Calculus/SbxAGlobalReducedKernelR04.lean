import EinsteinFull.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.Calculus.SbxS3CleanKernelPatchingR02
import EinsteinFull.Calculus.SbxS6SuppliedKernelUniquenessR01

open EinsteinRelation EinsteinFull MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal

noncomputable section
namespace SbxASection3R04

/-- A single exceptional environment set can be replaced by one good row,
without any minorization assumption. The patched family is Markov and starts
at its input globally; its positive-time endpoint laws are all absolutely
continuous. -/
theorem global_patch_reduced_kernel
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EinsteinRelation.EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∃ P' : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure, ∀ x, P' (x, ω) = P (x, ω)) ∧
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P' ∧
      IsMarkovKernel P' ∧
      (∀ a, ∀ᵐ γ ∂P' a, γ 0 = a.1) ∧
      (∀ (a : Vec d × FieldPair d) (t : ℝ≥0), 0 < t →
        (P' a).map (pathPosition t) ≪ (volume : Measure (Vec d))) := by
  classical
  let Good : FieldPair d → Prop := fun ω =>
    ∃ hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω),
      ∃ r : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
          (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
          hω lam h0 h1, ∀ x, P (x, ω) = r.pathLaw x
  have hgood : ∀ᵐ ω ∂Q.measure, Good ω := hP
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
    obtain ⟨_, r, hr⟩ := hfGood a.2
    rw [heq, hr a.1]
    letI := r.pathLaw_isMarkovKernel
    infer_instance
  · intro a
    obtain ⟨_, r, hr⟩ := hfGood a.2
    rw [heq, hr a.1]
    exact r.pathLaw_starts_at a.1
  · intro a t ht
    obtain ⟨_, r, hr⟩ := hfGood a.2
    rw [heq, hr a.1, r.pathLaw_endpoint, r.transitionKernel_eq_heatKernel t ht a.1]
    exact withDensity_absolutelyContinuous _ _

/-- The actual reduced GMP laws admit a globally Markov path kernel with all
starts correct and absolutely continuous positive-time endpoints. -/
theorem global_reduced_kernel_exists
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EinsteinRelation.EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ P : QuenchedPathLaws d,
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P ∧
      IsMarkovKernel P ∧
      (∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) ∧
      (∀ (a : Vec d × FieldPair d) (t : ℝ≥0), 0 < t →
        (P a).map (pathPosition t) ≪ (volume : Measure (Vec d))) := by
  obtain ⟨P, hP⟩ := SbxS3Section3R01.joint_reduced_kernel_exists hd Q lam h0 h1
  obtain ⟨P', _, hP', hmarkov, hstart, hac⟩ :=
    global_patch_reduced_kernel hd Q lam h0 h1 P hP
  exact ⟨P', hP', hmarkov, hstart, hac⟩

/-- The positive auxiliary realization is available for the full signed-force
range, with auxiliary force equal to the absolute value. -/
theorem global_reduced_kernel_exists_abs
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EinsteinRelation.EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h1 : |lam| ≤ 1) :
    ∃ P : QuenchedPathLaws d,
      IsGMPReducedKernel hd Q.ellipticity_parameter Q |lam| (abs_nonneg lam) h1 P ∧
      IsMarkovKernel P ∧
      (∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) ∧
      (∀ (a : Vec d × FieldPair d) (t : ℝ≥0), 0 < t →
        (P a).map (pathPosition t) ≪ (volume : Measure (Vec d))) :=
  global_reduced_kernel_exists hd Q |lam| (abs_nonneg lam) h1

end SbxASection3R04
