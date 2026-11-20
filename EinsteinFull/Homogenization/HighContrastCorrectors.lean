import EinsteinFull.Homogenization.HighContrastEllipticEvent
import HCPoly.MainResults

/-!
# Correctors of the dilated coefficient law

Theorem C of Armstrong, Kuusi and Loher, *Homogenization at a polynomial scale in high
contrast*, applied to the dilated law of a source law of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*. The law is
`(1, K)`-elliptic, stationary and of unit range, so the theorem provides a homogenized matrix,
a stationary corrector family and a homogenization scale with tail `exp(-t^d)`, above which the
correctors are small in the normalized `H⁻¹` norm, the Liouville classification holds and
solutions satisfy the large-scale Lipschitz estimate. The constants depend only on `d`.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport
  EinsteinRelation.External.AKM
open _root_.Homogenization hiding euclideanBall Vec Mat
open _root_.Homogenization.HighContrast

/-- The conclusions of Theorem C of Armstrong, Kuusi and Loher for the dilated law of a source
law, retaining the clauses on correctors, the Liouville classification and the large-scale
Lipschitz estimate. -/
structure HighContrastCorrectorPackage {d : ℕ} {K : ℝ} (hK : 1 ≤ K)
    (P : Measure (Coefficient d K)) (κ C : ℝ) where
  /-- The homogenized matrix. -/
  abar : Mat d
  /-- The homogenization scale. -/
  X : CoeffSpace d → ℝ
  /-- The corrector potentials. -/
  Phi : Vec d → CoeffSpace d → Vec d → ℝ
  /-- The corrector gradients. -/
  gradPhi : Vec d → CoeffSpace d → Vec d → Vec d
  /-- The event of full probability on which the estimates hold. -/
  Ωend : Set (CoeffSpace d)
  measurable_X : Measurable X
  one_le_X : ∀ b, 1 ≤ X b
  tail : ∀ t : ℝ, 1 ≤ t →
    (P.map (toHighContrast hK)).real {b | C * (2 + K / 1) ^ C * t ≤ X b} ≤
      Real.exp (-(t ^ (d : ℝ)))
  posDef : ∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x)
  measurableSet_Ωend : MeasurableSet Ωend
  full : (P.map (toHighContrast hK)).real Ωend = 1
  equation : ∀ b ∈ Ωend, ∀ e : Vec d,
    HasWeakGradientOn Set.univ (Phi e b) (gradPhi e b) ∧
      IsWeakSolutionOn (fun x => b.1 x) Set.univ (fun x => e + gradPhi e b x)
  corrector : ∀ b ∈ Ωend, ∀ e : Vec d, ∀ r : ℝ, X b ≤ r →
    ENNReal.ofReal r⁻¹ *
        negOneNorm (ellipsoid abar r)
          (fun x => matVecMul (matSqrt (symmPart abar)) (gradPhi e b x)) +
      ENNReal.ofReal r⁻¹ *
        negOneNorm (ellipsoid abar r)
          (fun x => matVecMul (matSqrt (symmPart abar))⁻¹
            (matVecMul (b.1 x - skewPart abar) (e + gradPhi e b x) -
              matVecMul (symmPart abar) e)) ≤
      ENNReal.ofReal
        (C * Real.sqrt (vecDot e (matVecMul (symmPart abar) e)) * (r / X b) ^ (-κ))
  liouville : ∀ b ∈ Ωend, ∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
    (∀ (v : Vec d → ℝ) (Dv : Vec d → Vec d),
      MemLiouvilleClass (fun x => b.1 x) ϑ v Dv →
      ∃ (e : Vec d) (c : ℝ), v =ᵐ[volume] fun x => vecDot e x + Phi e b x + c)
  liouville_mem : ∀ b ∈ Ωend, ∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 → ∀ (e : Vec d) (c : ℝ),
    MemLiouvilleClass (fun x => b.1 x) ϑ (fun x => vecDot e x + Phi e b x + c)
      (fun x => e + gradPhi e b x)
  lipschitz : ∀ b ∈ Ωend, ∀ R : ℝ, X b ≤ R →
    ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
      MemH1a (fun x => b.1 x) (ellipsoid abar R) u Du →
      IsWeakSolutionOn (fun x => b.1 x) (ellipsoid abar R) Du →
      ∀ r : ℝ, r ∈ Set.Icc (X b) R →
        weightedGradNorm (fun x => b.1 x) (ellipsoid abar r) Du ≤
          ENNReal.ofReal C * weightedGradNorm (fun x => b.1 x) (ellipsoid abar R) Du

/-- Theorem C of Armstrong, Kuusi and Loher applies to the dilated law of every source law,
with constants depending only on the dimension. -/
theorem exists_highContrastCorrectorPackage (d : ℕ) (hd : 2 ≤ d) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      ∀ (K : ℝ) (hK : 1 ≤ K) (P : Measure (Coefficient d K)), LawHypotheses P →
        Nonempty (HighContrastCorrectorPackage hK P κ C) := by
  obtain ⟨κ, C, C₀, C₁, hκ, hC, -, -, hmain⟩ := HCPoly.uniform_homogenization d hd
  refine ⟨κ, C, hκ, hC, fun K hK P hP => ?_⟩
  have := isProbabilityMeasure_map_toHighContrast hK hP
  obtain ⟨abar, X, Phi, gradPhi, hXm, hX1, -, -, htail, hpos, Ωend, hΩm, hΩ, -, -,
      heq, hcorr, hliou, hreg⟩ :=
    hmain 1 K one_pos le_rfl hK (P.map (toHighContrast hK)) inferInstance
      (isStationaryLaw_map_toHighContrast hK hP) (isUnitRangeLaw_map_toHighContrast hK hP)
      (ae_isEllipticMatrix_map_toHighContrast hK)
  exact ⟨{
    abar := abar
    X := X
    Phi := Phi
    gradPhi := gradPhi
    Ωend := Ωend
    measurable_X := hXm
    one_le_X := hX1
    tail := htail
    posDef := hpos
    measurableSet_Ωend := hΩm
    full := hΩ
    equation := heq
    corrector := hcorr
    liouville := fun b hb ϑ hϑ => (hliou b hb ϑ hϑ).1
    liouville_mem := fun b hb ϑ hϑ => (hliou b hb ϑ hϑ).2
    lipschitz := fun b hb R hR u Du hu hsol => (hreg b hb R hR u Du hu hsol).1 }⟩

end EinsteinFull.Homogenization
