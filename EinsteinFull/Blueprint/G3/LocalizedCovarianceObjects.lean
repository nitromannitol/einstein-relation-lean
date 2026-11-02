import EinsteinFull.External.AKMLocalizedEnergy
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ScaledJointPairing
import EinsteinFull.Frozen.SchwartzTestNorm
import EinsteinFull.Work.W7.ClockFiniteRangeSupport
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Actual variational objects for the covariance argument. No stationarity,
measurability, homogenization identification or estimate is stored as choice data.
The source Gaussian is isotropic; it is not the homogenized Gaussian. -/

open MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM

/-- The scalar parameter window, fixed before any law. -/
def covarianceWindow (d : ℕ) (D : StructuralData d) (s δ γ η β : ℝ) : Prop :=
  1 < AKMUpperEllipticity D.ellipticity ∧ 1 < s ∧ s < 2 ∧ 0 < δ ∧
  (d : ℝ) / 2 * (1 + δ) < γ ∧
  γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) ∧
  (d : ℝ) / (2 * γ) < η ∧ η < (1 + δ)⁻¹ ∧
  1 / 2 < η ∧ η * (1 + δ) < β ∧ β < 1

/-- Structural source choices, followed by genuine coordinate minimizers for
all source laws. Only variational selection is retained in the returned data. -/
def covarianceSourceSelection (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    Σ α σ θ C₀ : ℝ,
      ∀ P : Measure (Coefficient d (AKMUpperEllipticity D.ellipticity)),
        LawHypotheses P → ∀ (a : Coefficient d (AKMUpperEllipticity D.ellipticity))
          (z : Vec d) (r : ℝ), 2 ≤ r →
          LocalizedBasis a z (localizationOuterRadius δ r)
            (localizationIntermediateRadius δ α γ r) σ θ C₀ := by
  let hex := EinsteinFull.External.akm_localized_energy d hd
    (AKMUpperEllipticity D.ellipticity) s δ γ
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
  let α := Classical.choose hex
  let hα := Classical.choose_spec hex
  let σ := Classical.choose hα
  let hσ := Classical.choose_spec hα
  let θ := Classical.choose hσ
  let hθ := Classical.choose_spec hσ
  let C₀ := Classical.choose hθ
  let hC₀ := Classical.choose_spec hθ
  let C := Classical.choose hC₀
  let hC := Classical.choose_spec hC₀
  exact ⟨α, σ, θ, C₀, fun P hP => Classical.choose
    (hC.2.2.2.2.2.2.2.2.2 P hP)⟩

/-- Actual source basis for the proved normalized coefficient-law hypotheses. -/
def covarianceBasis (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) :=
  (covarianceSourceSelection d hd D s δ γ η β h).2.2.2.2
    (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q)

/-- Literal coefficient and spatial normalization of the genuine source J₁.
The zero extension is outside the actual reduced image only. It makes no
claim of global local-sigma measurability of the selected representative. -/
def covarianceCoarseEntry {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (x : Vec d) (j k : Fin d) (ω : FieldPair d) : ℝ :=
  if hω : ω ∈ ReductionImageV3.physicalReducedRange D.ellipticity then
    (ellipticityScale D.ellipticity)⁻¹ * coarsenedCoefficient
      (project (r₀ := D.dependenceRange) Q.ellipticity_parameter
        (ReductionImageV3.inverseReducePhysical ⟨ω, hω⟩))
      (ellipticityScale D.ellipticity • homogenizedCoefficient Q)
      (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) j k
  else 0

/-- Literal centering of the actual source coefficient under its projected law. -/
def covarianceCenteredCoarseEntry {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (x : Vec d) (j k : Fin d) (ω : FieldPair d) : ℝ :=
  covarianceCoarseEntry D Q r x j k ω - (ellipticityScale D.ellipticity)⁻¹ *
    ∫ a, coarsenedCoefficient a
      (ellipticityScale D.ellipticity • homogenizedCoefficient Q)
      (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) j k ∂actualCoefficientLaw Q

/-- The actual selected source J₁, totalized below its source domain r≥2.
No measurability or covariance of this family is presumed. -/
def covarianceSourceLocalizedEnergy (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (a : Coefficient d (AKMUpperEllipticity D.ellipticity))
    (z : Vec d) (r : ℝ) (p q : Vec d) : ℝ :=
  if hr : 2 ≤ r then
    localizedEnergyJ1 (covarianceBasis d hd D s δ γ η β h Q a z r hr) r p q
  else 0

/-- Literal centered polarization of genuine selected minimizers under the
actual normalized coefficient law. The second load is the same in both terms.
The structural source choices precede Q. Spatial/coefficient units are explicit. -/
def covarianceLocalizedEntry (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (x : Vec d) (j k : Fin d) (ω : FieldPair d) : ℝ :=
  if hω : ω ∈ ReductionImageV3.physicalReducedRange D.ellipticity then
    let a := project (r₀ := D.dependenceRange) Q.ellipticity_parameter
      (ReductionImageV3.inverseReducePhysical ⟨ω, hω⟩)
    let A := ellipticityScale D.ellipticity • homogenizedCoefficient Q
    let J := covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q
    let z := D.dependenceRange⁻¹ • x
    let ρ := r / D.dependenceRange
    (ellipticityScale D.ellipticity)⁻¹ *
      (centeredLocalizedEnergy (actualCoefficientLaw Q) J a z ρ
          (unitVector j + unitVector k) (A.mulVec (unitVector j)) -
        centeredLocalizedEnergy (actualCoefficientLaw Q) J a z ρ
          (unitVector j - unitVector k) (A.mulVec (unitVector j))) / 2
  else 0

/-- Physical containing radius after the unit-range source rescaling. -/
def covarianceLocalizationRadius {d : ℕ} (D : StructuralData d) (δ r : ℝ) : ℝ :=
  D.dependenceRange * (r / D.dependenceRange) ^ (1 + δ)

/-- Literal full matrix-clock field. The matrix uses literal centered polarization;
the clock uses the unrenormalized truncated source Gaussian. -/
def covarianceLocalizedField (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (x : Vec d) (ω : FieldPair d) : JointObservationIndex d → ℝ
  | .inl (j,k) => covarianceLocalizedEntry d hd D s δ γ η β h Q r x j k ω
  | .inr _ => ∫ z in ball 0 (covarianceLocalizationRadius D δ r),
      heatKernel 0 r z * centeredClockField Q (x - z) ω

/-- Explicit Euclidean size of the full matrix-clock vector. -/
def covarianceVectorSize {d : ℕ} (v : JointObservationIndex d → ℝ) : ℝ :=
  Real.sqrt (∑ a, (v a) ^ 2)

/-- Frobenius size on the full joint covariance, including cross entries. -/
def covarianceMatrixSize {d : ℕ}
    (A : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ) : ℝ :=
  Real.sqrt (∑ a, ∑ b, (A a b) ^ 2)

/-- L² size of a literal joint random vector. Membership is asserted separately. -/
def covarianceL2Size {d : ℕ} (μ : Measure (FieldPair d))
    (v : FieldPair d → JointObservationIndex d → ℝ) : ℝ :=
  Real.sqrt (∫ ω, (covarianceVectorSize (v ω)) ^ 2 ∂μ)

/-- Actual normalized local block, integrated componentwise. -/
def covarianceBlock (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r L side : ℝ) (x : Vec d) (f : Vec d → ℝ)
    (ω : FieldPair d) (a : JointObservationIndex d) : ℝ :=
  L ^ (-(d : ℝ) / 2) * ∫ y in clockBlockCube x side,
    f y * covarianceLocalizedField d hd D s δ γ η β h Q r y ω a

/-- Literal bilinear matrix covariance of an actual joint block. -/
def covarianceBlockMatrix {d : ℕ} (μ : Measure (FieldPair d))
    (X : FieldPair d → JointObservationIndex d → ℝ) :
    Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ :=
  fun a b => ∫ ω, X ω a * X ω b ∂μ

/-- The genuine source-kernel smoothed joint field on the reduced environment. -/
def covarianceSmoothedField {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (r : ℝ) (x : Vec d) (ω : FieldPair d) (a : JointObservationIndex d) : ℂ :=
  ∫ z : Vec d, (heatKernel 0 r z : ℂ) * Z a (translate (x - z) ω)

/-- Literal spatial test pairing of the actual localized joint field. -/
def covarianceLocalizedPairing (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (R r : ℝ)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (ω : FieldPair d) : ℂ :=
  ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) * ∫ x : Vec d,
    ∑ a, F (R⁻¹ • x) a *
      (covarianceLocalizedField d hd D s δ γ η β h Q r x ω a : ℂ)

/-- The centers of the side-L tiling, indexed by the integer lattice. -/
def covarianceTileCenter {d : ℕ} (L : ℝ) (j : Fin d → ℤ) : Vec d :=
  fun i => L * (j i : ℝ)

/-- Literal frozen-test trimmed-block sum; summability is a Prop obligation. -/
def covarianceTestBlocks (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (R L : ℝ)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (ω : FieldPair d) : ℂ :=
  (((L / R) ^ ((d : ℝ) / 2) : ℝ) : ℂ) * ∑' j : Fin d → ℤ,
    ∑ a, F (R⁻¹ • covarianceTileCenter L j) a *
      (covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
        (covarianceTileCenter L j) (fun _ => 1) ω a : ℂ)

/-- Full-block covariance limit along the actual dyadic sequence. Existence,
PSD and the quantitative rate are asserted by the covariance-rate contract. -/
def covarianceDyadicLimit (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) :
    Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ := fun a b =>
  Filter.limUnder Filter.atTop (fun n : ℕ =>
    covarianceBlockMatrix (reducedLaw Q)
      (covarianceBlock d hd D s δ γ η β h Q
        (((2 : ℝ) ^ n) ^ η) ((2 : ℝ) ^ n) ((2 : ℝ) ^ n) 0 (fun _ => 1)) a b)

/-- Complex L² size, with the ordinary absolute-value norm. -/
def covarianceComplexL2Size {d : ℕ} (μ : Measure (FieldPair d))
    (v : FieldPair d → ℂ) : ℝ := Real.sqrt (∫ ω, ‖v ω‖ ^ 2 ∂μ)

/-- Source-kernel smoothing followed by the physical-scale Schwartz pairing. -/
def covarianceSmoothedPairing {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (R r : ℝ) (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (ω : FieldPair d) : ℂ :=
  ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) * ∫ x : Vec d,
    ∑ a, F (R⁻¹ • x) a * covarianceSmoothedField Q Z r x ω a

end EinsteinFull.Blueprint
