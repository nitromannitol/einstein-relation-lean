import EinsteinFull.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.Regeneration.PhysicalKernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.SbxAGlobalReducedKernelR04`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open EinsteinRelation EinsteinFull MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal
noncomputable section
namespace SbxASection3R04
/-- The physical-kernel version of `SbxASection3R04.global_patch_reduced_kernel`. -/
theorem global_patch_reduced_kernel_phys
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EinsteinRelation.EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∃ P' : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure, ∀ x, P' (x, ω) = P (x, ω)) ∧
      EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P' ∧
      IsMarkovKernel P' ∧
      (∀ a, ∀ᵐ γ ∂P' a, γ 0 = a.1) ∧
      (∀ (a : Vec d × FieldPair d) (t : ℝ≥0), 0 < t →
        (P' a).map (pathPosition t) ≪ (volume : Measure (Vec d))) := by
  classical
  let Good : FieldPair d → Prop := fun ω =>
    ∃ hω : IsRegular (sourceReducedBound Λ₀) ω,
      ∃ r : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
          (one_le_sourceReducedBound Q.ellipticity_parameter) ω
          hω lam h0 h1, ∀ x, P (x, ω) = r.pathLaw x
  have hgood : ∀ᵐ ω ∂Q.measure, Good ω := hP
  obtain ⟨N, hsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hE : ∀ᵐ ω ∂Q.measure, ω ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hNzero
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
    let := r.pathLaw_isMarkovKernel
    infer_instance
  · intro a
    obtain ⟨_, r, hr⟩ := hfGood a.2
    rw [heq, hr a.1]
    exact r.pathLaw_starts_at a.1
  · intro a t ht
    obtain ⟨_, r, hr⟩ := hfGood a.2
    rw [heq, hr a.1, r.pathLaw_endpoint, r.transitionKernel_eq_heatKernel t ht a.1]
    exact withDensity_absolutelyContinuous _ _

/-- The physical-kernel version of `SbxASection3R04.global_reduced_kernel_exists_abs`. -/
theorem global_reduced_kernel_exists_abs_phys
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EinsteinRelation.EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h1 : |lam| ≤ 1) :
    ∃ P : QuenchedPathLaws d,
      EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q |lam| (abs_nonneg lam) h1 P ∧
      IsMarkovKernel P ∧
      (∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) ∧
      (∀ (a : Vec d × FieldPair d) (t : ℝ≥0), 0 < t →
        (P a).map (pathPosition t) ≪ (volume : Measure (Vec d))) :=
  EinsteinFull.Regeneration.global_physical_kernel_exists_reducedBound hd Q |lam| (abs_nonneg lam) h1

end SbxASection3R04
