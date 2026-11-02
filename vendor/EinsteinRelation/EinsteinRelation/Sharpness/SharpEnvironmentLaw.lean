import EinsteinRelation.Environment.Basic
import EinsteinRelation.Environment.Smooth
import EinsteinRelation.External.WhiteNoise
import EinsteinRelation.Sharpness.HarmonicField
import EinsteinRelation.Sharpness.PhysicalEnvironment
import EinsteinRelation.Sharpness.SeedDensityBounds
import EinsteinRelation.Sharpness.SeedField
import EinsteinRelation.Sharpness.SeedFieldDerivatives
import EinsteinRelation.Sharpness.SeedLawNondegeneracy
import EinsteinRelation.Sharpness.SeedPhysicalRegularity
import EinsteinRelation.Sharpness.SmoothEnvironment
import EinsteinRelation.Sharpness.SmoothFields

/-! # Step 1 of the sharpness example on the seed space

Source `paper/main.tex`, Proposition 7.1 (`sharp.example`, lines 1202–1231), Step 1.
The physical pair `(μ⁻¹ a, -(1/2) log μ)` of the scaled canonical seed `ε * seedField d W`
is built from proof-carrying bounds. The pointwise properties proved here are: smoothness,
uniform Euclidean regularity, the constant harmonic flux, the gradient and value bounds, and
nondegeneracy of the seed under a white-noise law.

The environment-level statements are not proved here. They are recorded as the propositions
`SharpPhysicalPairMeasurable`, `SharpPhysicalLawStationary`, `SharpPhysicalLawFiniteRange`
and `SharpCorrectorOnLaw`. -/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Each squared coordinate is at most the squared Euclidean norm. -/
private theorem sharpSqCoord_le_euclideanSq {d : ℕ} (v : Vec d) (i : Fin d) :
    v i * v i ≤ euclideanSq v := by
  unfold euclideanSq dot
  exact Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)

/-- Each coordinate is bounded in absolute value by the Euclidean norm. -/
private theorem sharpAbsCoord_le_euclideanNorm {d : ℕ} (v : Vec d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  rw [sq]
  exact sharpSqCoord_le_euclideanSq v i

/-- Under the gradient bound `1/4`, the Jacobian factor `1 + gᵢ` is nonzero. -/
private theorem sharpJacobianFactor_ne_zero {d : ℕ} (i : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4) : jacobianFactor i g ≠ 0 := by
  have hlo : -(1 / 4 : ℝ) ≤ g i :=
    (abs_le.mp ((sharpAbsCoord_le_euclideanNorm g i).trans hg)).1
  have hpos : 0 < 1 + g i := by linarith
  exact hpos.ne'

/-- A clock density in the band `[3/4, 5/4]` is positive. -/
private theorem sharpDensity_pos {μ : ℝ} (h : (3 / 4 : ℝ) ≤ μ ∧ μ ≤ 5 / 4) : 0 < μ := by
  linarith [h.1]

/-- The scaled canonical seed is smooth. -/
theorem sharpSeed_contDiff {d : ℕ} (ε : ℝ) (W : NoiseSample d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => ε * seedField d W y) :=
  ContDiff.mul (contDiff_const (c := ε)) (contDiff_seedField d W)

/-- The physical coefficient of the scaled seed is continuous. -/
theorem sharpSeed_continuous_coefficient {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) :
    Continuous (physicalCoefficientField i δ (fun y => ε * seedField d W y)) :=
  continuous_physicalCoefficientField i δ (fun y => ε * seedField d W y)
    (sharpSeed_contDiff ε W)
    (fun x => sharpJacobianFactor_ne_zero i _ (hgrad W x))
    (fun x => sharpDensity_pos (hμ W x))

/-- The physical potential of the scaled seed is continuous. -/
theorem sharpSeed_continuous_potential {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) :
    Continuous (potentialField i δ (fun y => ε * seedField d W y)) :=
  continuous_potentialField i δ (fun y => ε * seedField d W y)
    (sharpSeed_contDiff ε W)
    (fun x => sharpJacobianFactor_ne_zero i _ (hgrad W x))
    (fun x => sharpDensity_pos (hμ W x))

/-- The physical pair of the scaled canonical seed `ε * seedField d W`, with the clock
parameter `δ`. Its coefficient and potential are the literal fields of `eq.sharp-coefficients`
(`paper/main.tex`, lines 1218–1231). -/
noncomputable def sharpPhysicalPair {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) : FieldPair d :=
  physicalEnvironment i δ (fun y => ε * seedField d W y)
    (sharpSeed_continuous_coefficient i δ ε hgrad hμ W)
    (sharpSeed_continuous_potential i δ ε hgrad hμ W)

/-- The physical pair of the scaled seed is smooth. -/
theorem sharpPhysicalPair_isSmooth {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) :
    IsSmoothFieldPair (sharpPhysicalPair i δ ε hgrad hμ W) :=
  isSmoothFieldPair_physicalEnvironment i δ (fun y => ε * seedField d W y)
    (sharpSeed_continuous_coefficient i δ ε hgrad hμ W)
    (sharpSeed_continuous_potential i δ ε hgrad hμ W) (sharpSeed_contDiff ε W)
    (fun x => sharpJacobianFactor_ne_zero i _ (hgrad W x))
    (fun x => sharpDensity_pos (hμ W x))

/-- One deterministic Euclidean regularity constant `Λ ≥ 4` serves every sample of the
physical pair of the scaled seed. -/
theorem sharpPhysicalPair_regular {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ)) :
    ∃ Λ : ℝ, 4 ≤ Λ ∧ ∀ W : NoiseSample d, IsRegular Λ (sharpPhysicalPair i δ ε hgrad hμ W) := by
  obtain ⟨Λ, hΛ, h⟩ := exists_uniform_seedField_physical_regularity i ε hgrad δ hμ
  exact ⟨Λ, hΛ, h (sharpPhysicalPair i δ ε hgrad hμ) fun W x => ⟨rfl, rfl⟩⟩

/-- The physical pair has the constant harmonic flux `a (e_i + ∇ψ) = e_i` for the scaled seed,
with the reduced coefficient `a` of the pair. -/
theorem sharpPhysicalPair_harmonic {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) (x : Vec d) :
    (reducedCoefficient (sharpPhysicalPair i δ ε hgrad hμ W) x).mulVec
      (unitVector i + gradient (fun y => ε * seedField d W y) x) = unitVector i := by
  unfold sharpPhysicalPair
  rw [physicalEnvironment_reducedCoefficient i δ (fun y => ε * seedField d W y)
    (sharpSeed_continuous_coefficient i δ ε hgrad hμ W)
    (sharpSeed_continuous_potential i δ ε hgrad hμ W) x (sharpDensity_pos (hμ W x))]
  exact coefficientField_harmonic i (fun y => ε * seedField d W y) x
    (sharpJacobianFactor_ne_zero i _ (hgrad W x))

/-- The scaled seed is bounded by its scale. -/
theorem sharpSeed_abs_le {d : ℕ} {ε : ℝ} (hε : 0 < ε) (W : NoiseSample d) (x : Vec d) :
    |ε * seedField d W x| ≤ ε := by
  rw [abs_mul, abs_of_pos hε]
  exact mul_le_of_le_one_right hε.le (abs_seedField_le_one d W x)

/-- The value of the scaled seed at the origin is not almost surely constant under a
white-noise law. -/
theorem sharpSeed_not_ae_const {d : ℕ} {P : Measure (NoiseSample d)}
    (hP : External.IsWhiteNoiseLaw P) {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ c : ℝ, ∀ᵐ W ∂P, ε * seedField d W 0 = c := by
  rintro ⟨c, hc⟩
  apply seedField_zero_not_ae_eq_const hP (c / ε)
  filter_upwards [hc] with W hW
  show seedField d W 0 = c / ε
  rw [eq_div_iff hε.ne', mul_comm]
  exact hW

/-- Step 1 on the seed space, for every direction `i` and every white-noise law `P`: there are
scales `ε, δ > 0` and a regularity constant `Λ ≥ 4` such that the physical pairs of the scaled
seed are smooth and `Λ`-regular for every sample, the reduced coefficient satisfies the constant
harmonic flux identity along the scaled seed, the seed is bounded by `ε`, and its value at the
origin is nondegenerate. -/
theorem exists_sharp_physical_seed_step1 (d : ℕ) (i : Fin d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) :
    ∃ (ε δ Λ : ℝ) (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
        euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
      (hμ : ∀ (W : NoiseSample d) (x : Vec d),
        (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
        densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ)),
      0 < ε ∧ 0 < δ ∧ 4 ≤ Λ ∧
      (∀ W : NoiseSample d, IsSmoothFieldPair (sharpPhysicalPair i δ ε hgrad hμ W)) ∧
      (∀ W : NoiseSample d, IsRegular Λ (sharpPhysicalPair i δ ε hgrad hμ W)) ∧
      (∀ (W : NoiseSample d) (x : Vec d),
        (reducedCoefficient (sharpPhysicalPair i δ ε hgrad hμ W) x).mulVec
          (unitVector i + gradient (fun y => ε * seedField d W y) x) = unitVector i) ∧
      (∀ (W : NoiseSample d) (x : Vec d), |ε * seedField d W x| ≤ ε) ∧
      ¬ ∃ c : ℝ, ∀ᵐ W ∂P, ε * seedField d W 0 = c := by
  obtain ⟨ε, hε, hgrad⟩ := exists_seedField_gradient_scale d
  obtain ⟨δ, hδ, hμ⟩ := exists_uniform_seedField_density_parameter_of_gradient_bound i ε hgrad
  obtain ⟨Λ, hΛ, hreg⟩ := sharpPhysicalPair_regular i δ ε hgrad hμ
  exact ⟨ε, δ, Λ, hgrad, hμ, hε, hδ, hΛ,
    fun W => sharpPhysicalPair_isSmooth i δ ε hgrad hμ W,
    hreg,
    fun W x => sharpPhysicalPair_harmonic i δ ε hgrad hμ W x,
    fun W x => sharpSeed_abs_le hε W x,
    sharpSeed_not_ae_const hP hε⟩

/-- Open environment-level input: the physical pair, as a map from the seed sample space to the
environment space, is Borel measurable. -/
def SharpPhysicalPairMeasurable {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ)) : Prop :=
  Measurable (sharpPhysicalPair i δ ε hgrad hμ)

/-- Open environment-level input: the pushforward of a white-noise law by the physical pair is
stationary under all spatial translations. -/
def SharpPhysicalLawStationary {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (P : Measure (NoiseSample d)) : Prop :=
  IsStationary (Measure.map (sharpPhysicalPair i δ ε hgrad hμ) P)

/-- Open environment-level input: the pushforward of a white-noise law by the physical pair has
joint finite range `r₀`. -/
def SharpPhysicalLawFiniteRange {d : ℕ} (r₀ : ℝ) (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (P : Measure (NoiseSample d)) : Prop :=
  HasFiniteRange r₀ (Measure.map (sharpPhysicalPair i δ ε hgrad hμ) P)

/-- Open environment-level input, the corrector conjunct of `sharp.example`
(`paper/main.tex`, lines 1202–1209) for a law `Q` on coefficient pairs. The corrector must be a
function on the environment space. The physical pair determines the seed only up to an additive
constant, through its gradient field, so the constant must come from a global normalization of
the pair. -/
def SharpCorrectorOnLaw {d : ℕ} (i : Fin d) (Q : Measure (FieldPair d)) : Prop :=
  ∃ (δ : ℝ) (ψ : FieldPair d → ℝ), 0 < δ ∧ Measurable ψ ∧
    (∀ ω : FieldPair d, ContDiff ℝ 1 (fun x => ψ (translate x ω))) ∧
    (∃ M : ℝ, ∀ ω : FieldPair d, |ψ ω| ≤ M) ∧
    (∀ (ω : FieldPair d) (x : Vec d),
      euclideanNorm (gradient (fun y => ψ (translate y ω)) x) ≤ 1 / 4) ∧
    (∀ᵐ ω ∂Q, ∀ x : Vec d,
      (reducedCoefficient ω x).mulVec
        (unitVector i + gradient (fun y => ψ (translate y ω)) x) = unitVector i) ∧
    ¬ ∃ c : ℝ, ∀ᵐ ω ∂Q, ψ ω = c

end EinsteinRelation.Sharpness
