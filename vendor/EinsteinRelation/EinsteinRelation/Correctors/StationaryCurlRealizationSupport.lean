import EinsteinRelation.Calculus.ClosedPotentialOrbitCurlSupport
import EinsteinRelation.Correctors.StationarySpatialRealizationSupport
import EinsteinRelation.Correctors.StationaryCurlFubiniSupport
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open MeasureTheory
open EinsteinRelation

noncomputable section

namespace EinsteinRelation.Correctors.StationaryCurlRealization

variable {d : ℕ}

/-- Smooth scalar tests on the whole spatial coordinate space. -/
abbrev SpatialTest (d : ℕ) :=
  TestFunction (⊤ : TopologicalSpace.Opens (Vec d)) ℝ ⊤

private theorem contDiff_coordinateDerivative {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i ψ) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ ψ x (unitVector i))
  exact ((contDiff_infty_iff_fderiv.mp hψ).2).clm_apply contDiff_const

private theorem hasCompactSupport_coordinateDerivative {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : HasCompactSupport ψ) (i : Fin d) :
    HasCompactSupport (coordinateDerivative i ψ) := by
  simpa only [coordinateDerivative] using! hψ.fderiv_apply ℝ (unitVector i)

private theorem tsupport_coordinateDerivative_subset {d : ℕ} {ψ : Vec d → ℝ}
    (i : Fin d) : tsupport (coordinateDerivative i ψ) ⊆ tsupport ψ := by
  apply closure_minimal
  · intro x hx
    by_contra hxψ
    apply hx
    have hzero : fderiv ℝ ψ x = 0 := fderiv_of_notMem_tsupport ℝ hxψ
    simp [coordinateDerivative, hzero]
  · exact isClosed_closure

/-- The two test derivatives as actual scalar `L²(volume)` classes. -/
noncomputable def derivativePair (j k : Fin d) (ψ : SpatialTest d) :
    Lp ℝ 2 (volume : Measure (Vec d)) × Lp ℝ 2 (volume : Measure (Vec d)) :=
  (((contDiff_coordinateDerivative ψ.contDiff j).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative ψ.hasCompactSupport j)).toLp
        (coordinateDerivative j ψ),
    ((contDiff_coordinateDerivative ψ.contDiff k).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative ψ.hasCompactSupport k)).toLp
        (coordinateDerivative k ψ))

/-- Derivative pairs of smooth tests supported in one closed ball. -/
def boundedTestPairRange (n : ℕ) (j k : Fin d) :
    Set (Lp ℝ 2 (volume : Measure (Vec d)) × Lp ℝ 2 (volume : Measure (Vec d))) :=
  {p | ∃ ψ : SpatialTest d,
    tsupport (ψ : Vec d → ℝ) ⊆ Metric.closedBall (0 : Vec d) ((n : ℝ) + 1) ∧
    derivativePair j k ψ = p}

/-- Each bounded-support test-derivative range has a countable dense subset in the product
of scalar spatial `L²` spaces. The samplewise curl functional is continuous on this carrier
when the realized field is locally square integrable. -/
theorem exists_countable_dense_boundedTestPairRange (n : ℕ) (j k : Fin d) :
    ∃ D : Set (boundedTestPairRange n j k), D.Countable ∧ Dense D := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology
      (Lp ℝ 2 (volume : Measure (Vec d))) := inferInstance
  letI : SecondCountableTopology
      (Lp ℝ 2 (volume : Measure (Vec d)) × Lp ℝ 2 (volume : Measure (Vec d))) :=
    inferInstance
  letI : SecondCountableTopology (boundedTestPairRange n j k) := inferInstance
  exact TopologicalSpace.exists_countable_dense (boundedTestPairRange n j k)

/-- For each fixed smooth compactly supported test, the orbit curl identity has an ordinary
samplewise representative under the actual reduced environment law. The almost-everywhere event
in this result may depend on the test. -/
theorem ae_samplewise_curl_test {d : ℕ} {Λ₀ r₀ : ℝ} [Fact (2 ≤ d)]
    (Q : EnvironmentLaw d Λ₀ r₀) (ψ : SpatialTest d) (j k : Fin d)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (hG : G ∈ correctorPotentialDomain Q) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      (∫ x : Vec d, coordinateDerivative j ψ x * (G (translate x ω)).ofLp k ∂volume) =
        ∫ x : Vec d, coordinateDerivative k ψ x * (G (translate x ω)).ofLp j ∂volume := by
  let Qr := reducedEnvironmentLaw Q
  let hQr := reducedEnvironmentLaw_stationary Q
  have hleft := StationaryCurlFubini.ae_samplewise_pairing_eq_orbit_pairing
    Qr hQr G k (coordinateDerivative j ψ)
    (contDiff_coordinateDerivative ψ.contDiff j).continuous
    (hasCompactSupport_coordinateDerivative ψ.hasCompactSupport j)
  have hright := StationaryCurlFubini.ae_samplewise_pairing_eq_orbit_pairing
    Qr hQr G j (coordinateDerivative k ψ)
    (contDiff_coordinateDerivative ψ.contDiff k).continuous
    (hasCompactSupport_coordinateDerivative ψ.hasCompactSupport k)
  have horbit := closedPotentialGradient_orbit_curlFree Q ψ.contDiff
    ψ.hasCompactSupport j k G hG
  filter_upwards [hleft, hright] with ω hleftω hrightω
  have horbitω := congrArg (fun P : Lp ℝ 2 Qr => P ω) horbit
  exact hleftω.symm.trans (horbitω.trans hrightω)

end EinsteinRelation.Correctors.StationaryCurlRealization

end
