import EinsteinFull.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.SbxBCenteredTubeChainR03`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
noncomputable section
/-- The physical-kernel version of `EinsteinFull.b_centered_local_return_input`. -/
@[nolint defsWithUnderscore]
def b_centered_local_return_input_phys : Prop :=
  ∀ {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
    ∃ h η : ℝ, 0 < h ∧ 0 < η ∧ η ≤ 1 ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
        (h0 : 0 < |lam|) (h1 : |lam| ≤ 1) (P : QuenchedPathLaws d),
        EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q |lam| h0.le h1 P →
        ∀ᵐ ω ∂Q.measure, ∀ c y : Vec d,
          euclideanNorm (y - c) < (l / |lam|) / 4 →
          ENNReal.ofReal η ≤ P (y, ω)
            {γ : Path d |
              (∀ s : ℝ≥0, s ≤ Real.toNNReal (h / |lam| ^ 2) →
                euclideanNorm (γ s - c) < (l / |lam|) / 2) ∧
              euclideanNorm (γ (Real.toNNReal (h / |lam| ^ 2)) - c) <
                (l / |lam|) / 4}

/-- The physical-kernel version of `EinsteinFull.b_centered_tube_of_local_return`. -/
theorem b_centered_tube_of_local_return_phys (hlocal : b_centered_local_return_input_phys) :
    ∀ {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
          (h0 : 0 < |lam|) (h1 : |lam| ≤ 1),
          ∃ P : QuenchedPathLaws d,
            EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q |lam| h0.le h1 P ∧
            ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
              ENNReal.ofReal ε ≤ P (x, ω)
                {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0)
                    (EinsteinRelation.Regeneration.Renewal.regenDelta |lam|),
                  euclideanNorm (γ s - x) ≤ (l / |lam|) / 2} := by
  intro d hd Λ₀ r₀ l hl
  obtain ⟨h, η, hh, hη, hη1, hstep⟩ := hlocal hd Λ₀ r₀ l hl
  obtain ⟨n, hcover⟩ := b_scaled_steps_cover_regenDelta h hh
  refine ⟨η ^ n, pow_pos hη _, pow_le_one₀ hη.le hη1, ?_⟩
  intro Q lam h0 h1
  obtain ⟨P, hP, _, _, _⟩ := SbxASection3R04.global_reduced_kernel_exists_abs_phys hd Q lam h1
  refine ⟨P, hP, ?_⟩
  filter_upwards [hP, hstep Q lam h0 h1 P hP] with ω hreal hlocalω
  obtain ⟨hω, G, hrow⟩ := hreal
  intro x
  let U : Set (Vec d) := {y | euclideanNorm (y - x) < (l / |lam|) / 2}
  let A : Set (Vec d) := {y | euclideanNorm (y - x) < (l / |lam|) / 4}
  have hU : IsOpen U :=
    isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
      (continuous_id.sub continuous_const)) continuous_const
  have hA : MeasurableSet A :=
    (isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
      (continuous_id.sub continuous_const)) continuous_const).measurableSet
  have hAU : A ⊆ U := by
    intro y hy
    change euclideanNorm (y - x) < (l / |lam|) / 4 at hy
    change euclideanNorm (y - x) < (l / |lam|) / 2
    have hp : 0 < l / |lam| := div_pos hl h0
    linarith
  have hx : x ∈ A := by
    change euclideanNorm (x - x) < (l / |lam|) / 4
    have hz : euclideanNorm (0 : Vec d) = 0 := by
      simp [euclideanNorm, euclideanSq, dot]
    simpa only [sub_self, hz] using
      (div_pos (div_pos hl h0) (by norm_num : (0 : ℝ) < 4))
  have hs : ∀ y ∈ A, ENNReal.ofReal η ≤ G.pathLaw y
      {γ : Path d | (∀ s : ℝ≥0, s ≤ Real.toNNReal (h / |lam| ^ 2) → γ s ∈ U) ∧
        γ (Real.toNNReal (h / |lam| ^ 2)) ∈ A} := by
    intro y hy
    rw [← hrow y]
    exact hlocalω x y hy
  have hchain := b_gmp_centered_return_iterate G U A hU hA hAU
    (Real.toNNReal (h / |lam| ^ 2)) (ENNReal.ofReal η) hs n x hx
  rw [hrow x]
  calc
    ENNReal.ofReal (η ^ n) = (ENNReal.ofReal η) ^ n := ENNReal.ofReal_pow hη.le n
    _ ≤ G.pathLaw x
        {γ : Path d | (∀ s : ℝ≥0,
            s ≤ (n : ℝ≥0) * Real.toNNReal (h / |lam| ^ 2) → γ s ∈ U) ∧
          γ ((n : ℝ≥0) * Real.toNNReal (h / |lam| ^ 2)) ∈ A} := hchain
    _ ≤ G.pathLaw x
        {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0)
            (EinsteinRelation.Regeneration.Renewal.regenDelta |lam|),
          euclideanNorm (γ s - x) ≤ (l / |lam|) / 2} := by
      apply measure_mono
      intro γ hγ s hs
      exact le_of_lt (hγ.1 s (hs.2.trans (hcover lam)))

end
end EinsteinFull
