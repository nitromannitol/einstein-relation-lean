import EinsteinFull.Work.W2.TransposeResolventGradientContinuitySupport
import EinsteinFull.Blueprint.G2.Proofs.C1CrudeEnergy
import EinsteinFull.Calculus.C2RetainedPhysicalMeasurableEvolution
import EinsteinFull.Work.W2.TransposeAllDataHorizonEnergySupport
import EinsteinFull.Work.W3.ForwardFullHorizonEnergySupport
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0400_1
import EinsteinFull.Blueprint.Foundation.Proofs.W2CenteredEquations
import EinsteinFull.Calculus.RadialTransposeEnergySupport
import EinsteinFull.Calculus.ComplexCommonSpatialSupport
import EinsteinFull.Calculus.ComplexTransposeGradientTimeSupport
import EinsteinFull.Work.W3.HomogeneousGaussianH1LegSupport
import EinsteinRelation.Correctors.P53SourceSkewMollifyAlgebra
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Convolution
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

/- One gradient choice for the actual endpoints, before choosing a time
horizon. Smoothness of the initial drift supplies the full transpose
generator domain, so its branch is a genuine gradient at every positive time. -/
private def firstStripGradient {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (ν : EndpointIndex d) (t : ℝ≥0) : Fin d → Lp ℂ 2 (reducedLaw Q) :=
  match ν with
  | .inl k => fun j => if ht : 0 < t then
      hP.forcedGradient t ht (β k + ζ • a ⟨0, by omega⟩ k) j else 0
  | .inr false => fun j => if ht : 0 < t then
      ζ • hP.forcedGradient t ht μ j else 0
  | .inr true => fun j => complexTransposeGradientOrbit Q Pdag (β ⟨0, by omega⟩) t j

private theorem firstStripGradient_forward {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (ν : EndpointIndex d) (hν : ν ≠ .inr true) (t : ℝ≥0) (ht : 0 < t) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t)
      (firstStripGradient hd Q β a μ ζ P Pdag hP ν t) := by
  cases ν with
  | inl k =>
    simpa only [firstStripGradient, uncenteredEndpoint, ht, ↓reduceDIte] using
      hP.forcedGradient_spec t ht (β k + ζ • a ⟨0, by omega⟩ k)
  | inr b =>
    cases b with
    | false =>
      intro j
      simpa only [firstStripGradient, uncenteredEndpoint, ht, ↓reduceDIte] using
        (hP.forcedGradient_spec t ht μ j).smul ζ
    | true => exact (hν rfl).elim

private theorem firstStripGradient_spec {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (hβ : IsReducedDriftObservation Q hQ β)
    (ν : EndpointIndex d) (t : ℝ≥0) (ht : 0 < t) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t)
      (firstStripGradient hd Q β a μ ζ P Pdag hP ν t) := by
  by_cases hν : ν = .inr true
  · subst ν
    obtain ⟨G, _hGc, hG⟩ := timeFlux_transpose_continuous_gradient hβ hP hPdag
      ⟨0, by omega⟩
    have hGt : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (Pdag (t : ℝ).toNNReal (β ⟨0, by omega⟩)) (WithLp.toLp 2 (G t)) := by
      simpa only [Real.toNNReal_coe] using hG t
    have he := complexTransposeGradientOrbit_eq (NNReal.coe_pos.mpr ht) hGt
    simpa only [uncenteredEndpoint, transposeEndpoint, firstStripGradient, he] using hG t
  · exact firstStripGradient_forward hd Q β a μ ζ P Pdag hP ν hν t ht

/-- The smooth actual endpoint data give a time derivative in the full
forward or true bilinear-transpose generator graph, without a domain premise. -/
private theorem firstStrip_evolution_graph {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d) :
    ∃ H : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
      (∀ s : ℝ, 0 ≤ s → HasDerivWithinAt
        (fun r : ℝ => uncenteredEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (H s.toNNReal) (Ici s) s) ∧
      ∀ t : ℝ≥0,
        if ν = .inr true then IsComplexTransposeGeneratorPair Q ⟨0, by omega⟩ ζ
          (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (H t)
        else IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ
          (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (H t) := by
  cases ν with
  | inl k =>
    obtain ⟨b, hb⟩ := timeFlux_drift_generator (i := ⟨0, by omega⟩) (ζ := ζ) hβ k
    obtain ⟨c, hc⟩ := timeFlux_coefficient_generator (i := ⟨0, by omega⟩) (ζ := ζ)
      hQ ha ⟨0, by omega⟩ k
    have hinit := hb.add (hc.smul ζ)
    refine ⟨fun t => P t (b + ζ • c), ?_, ?_⟩
    · intro s hs
      exact hP.hasDerivWithinAt_orbit hinit s hs
    · intro t
      exact hP.map_generator hinit t
  | inr b =>
    cases b with
    | false =>
      obtain ⟨c, hc⟩ := centeredEquations_clock_initial_generator
        (i := ⟨0, by omega⟩) (ζ := ζ) hQ hμ
      refine ⟨fun t => P t (ζ • c), ?_, ?_⟩
      · intro s hs
        simpa only [uncenteredEndpoint, map_smul] using
          hP.hasDerivWithinAt_orbit (hc.smul ζ) s hs
      · intro t
        simpa only [uncenteredEndpoint, map_smul, Sum.inr.injEq, Bool.false_eq_true, reduceCtorEq,
          ↓reduceIte] using hP.map_generator (hc.smul ζ) t
    | true =>
      obtain ⟨c, hc⟩ := timeFlux_transpose_initial_generator
        (i := ⟨0, by omega⟩) (ζ := ζ) hβ ⟨0, by omega⟩
      refine ⟨fun t => Pdag t c, ?_, ?_⟩
      · intro s hs
        exact hPdag.hasDerivWithinAt_orbit hP hc s hs
      · intro t
        exact hPdag.map_generator hP hc t

/-- At each positive time the actual endpoint derivative has the physical
spatial weak equation on an event preceding every compact smooth test.
The transpose force remains inside the divergence with its literal sign. -/
private theorem firstStrip_evolution_spatial {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d) :
    ∃ H : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
      (∀ s : ℝ, 0 ≤ s → HasDerivWithinAt
        (fun r : ℝ => uncenteredEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (H s.toNNReal) (Ici s) s) ∧
      ∀ t : ℝ≥0, 0 < t → ∀ᵐ ω ∂reducedLaw Q,
        ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ x, H t (translate x ω) * (φ x : ℂ)) =
            if ν = .inr true then
              -(1 / 2 : ℂ) * (∫ x, ∑ j,
                ((∑ k, (ω.1 x j k : ℂ) *
                  firstStripGradient hd Q β a μ ζ P Pdag hP ν t k (translate x ω)) -
                  2 * ζ * (ω.1 x j ⟨0, by omega⟩ : ℂ) *
                    uncenteredEndpoint hd Q ν ζ P Pdag β a μ t (translate x ω)) *
                  (coordinateDerivative j φ x : ℂ))
            else
              -(1 / 2 : ℂ) * (∫ x, ∑ j,
                (∑ k, (ω.1 x j k : ℂ) *
                  firstStripGradient hd Q β a μ ζ P Pdag hP ν t k (translate x ω)) *
                    (coordinateDerivative j φ x : ℂ)) +
              ζ * (∫ x, (∑ j, (ω.1 x j ⟨0, by omega⟩ : ℂ) *
                firstStripGradient hd Q β a μ ζ P Pdag hP ν t j (translate x ω)) *
                  (φ x : ℂ)) := by
  obtain ⟨H, hH, hgraph⟩ := firstStrip_evolution_graph hd Q hQ β a μ hβ ha hμ ζ
    P Pdag hP hPdag ν
  refine ⟨H, hH, ?_⟩
  intro t ht
  have hG := firstStripGradient_spec hd Q hQ β a μ ζ P Pdag hP hPdag hβ ν t ht
  by_cases hν : ν = .inr true
  · have hg := hgraph t
    rw [ite_eq_left hν] at hg
    simpa only [ite_eq_left hν] using hg.spatial_flux_all_tests hG
  · have hg := hgraph t
    rw [ite_eq_right hν] at hg
    simpa only [ite_eq_right hν] using hg.spatial_flux_all_tests hG

private def firstStripPair {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (v : Lp ℂ 2 (reducedLaw Q)) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 v

private theorem firstStripPair_apply {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (v f : Lp ℂ 2 (reducedLaw Q)) :
    firstStripPair Q v f = ∫ ω, v ω * f ω ∂reducedLaw Q := by
  rw [firstStripPair, ContinuousLinearMap.lpPairing_eq_integral]
  rfl

/-- Differentiating the actual gradient against an H1 test needs no strong
time derivative of that gradient. Integration by parts transports the actual
endpoint derivative to the test's horizontal derivative. -/
private theorem firstStrip_gradient_weak_time {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d) :
    ∃ H : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
      (∀ s : ℝ, 0 ≤ s → HasDerivWithinAt
        (fun r : ℝ => uncenteredEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (H s.toNNReal) (Ici s) s) ∧
      (∀ t : ℝ≥0,
        if ν = .inr true then IsComplexTransposeGeneratorPair Q ⟨0, by omega⟩ ζ
          (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (H t)
        else IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ
          (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (H t)) ∧
      ∀ (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V →
        ∀ (j : Fin d) (s : ℝ), 0 < s → HasDerivWithinAt
          (fun r : ℝ => ∫ ω,
            firstStripGradient hd Q β a μ ζ P Pdag hP ν r.toNNReal j ω * v ω
              ∂reducedLaw Q)
          (-(∫ ω, H s.toNNReal ω * V j ω ∂reducedLaw Q)) (Ici s) s := by
  obtain ⟨H, hH, hgraph⟩ := firstStrip_evolution_graph hd Q hQ β a μ hβ ha hμ ζ
    P Pdag hP hPdag ν
  refine ⟨H, hH, hgraph, ?_⟩
  intro v V hV j s hs
  have hderiv := ((firstStripPair Q (V j)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt
    s (hH s hs.le)
  have hn : HasDerivWithinAt
      (fun r : ℝ => -(∫ ω,
        uncenteredEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal ω * V j ω ∂reducedLaw Q))
      (-(∫ ω, H s.toNNReal ω * V j ω ∂reducedLaw Q)) (Ici s) s := by
    have hneg := hderiv.neg
    change HasDerivWithinAt
      (fun r : ℝ => -(firstStripPair Q (V j)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)))
      (-(firstStripPair Q (V j) (H s.toNNReal))) (Ici s) s at hneg
    simpa only [firstStripPair_apply, mul_comm] using hneg
  apply hn.congr
  · intro r hr
    have hG := firstStripGradient_spec hd Q hQ β a μ ζ P Pdag hP hPdag hβ ν
      r.toNNReal (Real.toNNReal_pos.mpr (hs.trans_le hr))
    exact (complexHorizontalDerivatives_integration_by_parts (hG j) (hV j)).2.2
  · have hG := firstStripGradient_spec hd Q hQ β a μ ζ P Pdag hP hPdag hβ ν
      s.toNNReal (Real.toNNReal_pos.mpr hs)
    exact (complexHorizontalDerivatives_integration_by_parts (hG j) (hV j)).2.2

/-- The actual gradient satisfies the differentiated parabolic equation
in distribution form. The test has two horizontal derivatives; the endpoint
needs only its proved H1 realization, not a second-derivative premise. -/
private theorem firstStrip_gradient_equation {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V)
    (l : Fin d) (W : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hW : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (V l) W)
    (s : ℝ) (hs : 0 < s) :
    HasDerivWithinAt
      (fun r : ℝ => ∫ ω,
        firstStripGradient hd Q β a μ ζ P Pdag hP ν r.toNNReal l ω * v ω ∂reducedLaw Q)
      ((1 / 2 : ℂ) * (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) *
          firstStripGradient hd Q β a μ ζ P Pdag hP ν s.toNNReal k ω * W j ω
            ∂reducedLaw Q) -
        ζ * (if ν = .inr true then
          ∫ ω, uncenteredEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal ω *
            (∑ j, (ω.1 0 j ⟨0, by omega⟩ : ℂ) * W j ω) ∂reducedLaw Q
        else
          ∫ ω, (∑ j, (ω.1 0 j ⟨0, by omega⟩ : ℂ) *
            firstStripGradient hd Q β a μ ζ P Pdag hP ν s.toNNReal j ω) * V l ω
              ∂reducedLaw Q)) (Ici s) s := by
  obtain ⟨H, _hH, hgraph, hweak⟩ := firstStrip_gradient_weak_time hd Q hQ β a μ
    hβ ha hμ ζ P Pdag hP hPdag ν
  have htime := hweak v V hV l s hs
  have hG := firstStripGradient_spec hd Q hQ β a μ ζ P Pdag hP hPdag hβ ν
    s.toNNReal (Real.toNNReal_pos.mpr hs)
  by_cases hν : ν = .inr true
  · have hg := hgraph s.toNNReal
    rw [ite_eq_left hν] at hg
    obtain ⟨G, hG', hpair⟩ := hg
    have heG := hG'.unique hG
    subst G
    have he := hpair (V l) W hW
    rw [he] at htime
    simp only [ite_eq_left hν]
    convert htime using 1
    ring
  · have hg := hgraph s.toNNReal
    rw [ite_eq_right hν] at hg
    obtain ⟨G, hG', hpair⟩ := hg
    have heG := hG'.unique hG
    subst G
    have he := hpair (V l) W hW
    rw [he] at htime
    simp only [ite_eq_right hν]
    convert htime using 1
    ring

/-- The strong horizontal gradient has its physical distributional meaning on
one event before all coordinates and all compact smooth spatial tests. -/
private theorem firstStrip_spatial_gradient {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ l : Fin d,
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, G l (translate x ω) * (φ x : ℂ)) =
          -(∫ x, f (translate x ω) * (coordinateDerivative l φ x : ℂ)) := by
  let := reducedLaw_probability Q
  apply ae_all_iff.mpr
  intro l
  let F : Fin d → FieldPair d → ℂ := fun j ω => if j = l then f ω else 0
  have hFm (j : Fin d) : Measurable (F j) := by
    by_cases hj : j = l
    · simpa only [F, ite_eq_left hj] using (Lp.stronglyMeasurable f).measurable
    · simp only [F, ite_eq_right hj]
      exact measurable_const
  have hFl (j : Fin d) : MemLp (F j) 2 (reducedLaw Q) := by
    by_cases hj : j = l
    · simpa only [F, ite_eq_left hj] using Lp.memLp f
    · simp only [F, ite_eq_right hj]
      exact MemLp.zero
  have he := ae_complex_spatial_divergence_all_tests (reducedLaw Q)
    (reducedLaw_stationary Q) F (G l) hFm (Lp.stronglyMeasurable _).measurable
    hFl (Lp.memLp _) (fun v V hV => by
      have hi := (complexHorizontalDerivatives_integration_by_parts (hG l) (hV l)).2.2
      simpa only [F, Pi.zero_apply, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte] using (neg_eq_iff_eq_neg.mp hi.symm))
  filter_upwards [he] with ω hω
  intro φ hφ hφc
  simpa only [F, Pi.zero_apply, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] using hω φ hφ hφc

/-- Spatial regularization uses only local integrability, before any pointwise
bound has been obtained. The orientation agrees with the weak spatial tests. -/
private def firstStripSpatialSmooth {d : ℕ} (K : Vec d → ℝ)
    (v : Vec d → ℂ) (x : Vec d) : ℂ :=
  ∫ y, v y * (K (y - x) : ℂ)

private theorem firstStripSpatialSmooth_eq_convolution {d : ℕ}
    (K : Vec d → ℝ) (v : Vec d → ℂ) :
    firstStripSpatialSmooth K v =
      v ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip, volume] (fun y => K (-y)) := by
  funext x
  simp only [firstStripSpatialSmooth, convolution_def, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, Complex.real_smul, neg_sub, mul_comm]

private theorem firstStripSpatialSmooth_contDiff {d : ℕ}
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    {v : Vec d → ℂ} (hv : LocallyIntegrable v volume) :
    ContDiff ℝ (⊤ : ℕ∞) (firstStripSpatialSmooth K v) := by
  rw [firstStripSpatialSmooth_eq_convolution]
  exact (hKc.comp_homeomorph (Homeomorph.neg _)).contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip hv (hK.comp contDiff_id.neg)

/-- Differentiation of the regularization acts on the compact smooth kernel;
no strong spatial derivative of the unsmoothed field is assumed. -/
private theorem firstStripSpatialSmooth_fderiv {d : ℕ}
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    {v : Vec d → ℂ} (hv : LocallyIntegrable v volume) (x : Vec d) (l : Fin d) :
    fderiv ℝ (firstStripSpatialSmooth K v) x (unitVector l) =
      -(∫ y, v y * (coordinateDerivative l K (y - x) : ℂ)) := by
  let L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip
  let Kn : Vec d → ℝ := fun y => K (-y)
  have hKn : ContDiff ℝ (⊤ : ℕ∞) Kn := hK.comp contDiff_id.neg
  have hKnc : HasCompactSupport Kn := hKc.comp_homeomorph (Homeomorph.neg _)
  have hDn : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ Kn) := hKn.fderiv_right (by simp)
  have hi := (hKnc.fderiv ℝ).convolutionExists_right (L.precompR (Vec d))
    hv hDn.continuous x
  rw [firstStripSpatialSmooth_eq_convolution,
    (hKnc.hasFDerivAt_convolution_right L hv (hKn.of_le (by simp)) x).fderiv,
    convolution_def, ContinuousLinearMap.integral_apply hi]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with y
  have hd := (hK.differentiable (by simp)).differentiableAt.hasFDerivAt.comp
    (x - y) (hasFDerivAt_id (x - y)).neg
  have he : fderiv ℝ Kn (x - y) (unitVector l) =
      -coordinateDerivative l K (y - x) := by
    simpa [Kn, Function.comp_def, coordinateDerivative, neg_sub] using
      congrArg (fun D : Vec d →L[ℝ] ℝ => D (unitVector l)) hd.fderiv
  change ((fderiv ℝ Kn (x - y) (unitVector l)) : ℂ) * v y = _
  rw [he]
  push_cast
  ring

/-- Coordinate derivatives of a translated test retain the original sign. -/
private theorem firstStrip_coordinateDerivative_shift {d : ℕ}
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (x : Vec d) (j : Fin d) :
    coordinateDerivative j (fun y => K (y - x)) =
      fun y => coordinateDerivative j K (y - x) := by
  funext y
  have hd := (hK.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
    ((hasFDerivAt_id y).sub (hasFDerivAt_const x y))
  simpa [Function.comp_def, coordinateDerivative] using
    congrArg (fun D : Vec d →L[ℝ] ℝ => D (unitVector j)) hd.fderiv

/-- The Hessian of a spatial regularization differentiates the kernel twice;
no second derivative of the original locally integrable field is required. -/
private theorem firstStripSpatialSmooth_second_fderiv {d : ℕ}
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    {v : Vec d → ℂ} (hv : LocallyIntegrable v volume) (x : Vec d) (j k : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ (firstStripSpatialSmooth K v) y (unitVector j))
      x (unitVector k) =
        ∫ y, v y * (coordinateDerivative k (coordinateDerivative j K) (y - x) : ℂ) := by
  have hDj : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j K) :=
    (hK.fderiv_right (by simp)).clm_apply contDiff_const
  have he : (fun y => fderiv ℝ (firstStripSpatialSmooth K v) y (unitVector j)) =
      fun y => -firstStripSpatialSmooth (coordinateDerivative j K) v y := by
    funext y
    exact firstStripSpatialSmooth_fderiv K hK hKc hv y j
  rw [he, fderiv_fun_neg]
  simp only [_root_.neg_apply]
  rw [firstStripSpatialSmooth_fderiv (coordinateDerivative j K) hDj
    (hKc.fderiv_apply ℝ (unitVector j)) hv x k, neg_neg]

/-- Spatial regularization converts a weak second-order divergence equation
into a classical equation, leaving the time distribution untouched. -/
private theorem firstStripSpatialSmooth_weak_second_order {d : ℕ}
    (V B : Vec d → ℂ) (F : Fin d → Vec d → ℂ)
    (hB : LocallyIntegrable B volume) (hF : ∀ j, LocallyIntegrable (F j) volume)
    (α γ : ℂ) (l : Fin d)
    (he : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ y, V y * (φ y : ℂ)) =
        α * (∫ y, ∑ j, F j y *
          (coordinateDerivative j (coordinateDerivative l φ) y : ℂ)) +
        γ * (∫ y, B y * (coordinateDerivative l φ y : ℂ)))
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (x : Vec d) :
    firstStripSpatialSmooth K V x =
      α * (∑ j, fderiv ℝ
        (fun z => fderiv ℝ (firstStripSpatialSmooth K (F j)) z (unitVector l))
        x (unitVector j)) -
      γ * fderiv ℝ (firstStripSpatialSmooth K B) x (unitVector l) := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y => K (y - x)) :=
    hK.comp (contDiff_id.sub contDiff_const)
  have hφc : HasCompactSupport (fun y => K (y - x)) := by
    have hc := hKc.comp_homeomorph ((Homeomorph.subLeft x).trans (Homeomorph.neg _))
    change HasCompactSupport (fun y => K (-(x - y))) at hc
    simpa only [neg_sub] using hc
  have hDl : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative l K) :=
    (hK.fderiv_right (by simp)).clm_apply contDiff_const
  have hDjl (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (coordinateDerivative j (coordinateDerivative l K)) :=
    (hDl.fderiv_right (by simp)).clm_apply contDiff_const
  have hcjl (j : Fin d) : HasCompactSupport
      (fun y => coordinateDerivative j (coordinateDerivative l K) (y - x)) := by
    have hc := ((hKc.fderiv_apply ℝ (unitVector l)).fderiv_apply ℝ (unitVector j)).comp_homeomorph ((Homeomorph.subLeft x).trans (Homeomorph.neg _))
    change HasCompactSupport
      (fun y => coordinateDerivative j (coordinateDerivative l K) (-(x - y))) at hc
    simpa only [neg_sub] using hc
  have hi (j : Fin d) : Integrable (fun y => F j y *
      (coordinateDerivative j (coordinateDerivative l K) (y - x) : ℂ)) volume := by
    simpa only [Complex.real_smul, mul_comm, Function.comp_def, Pi.sub_apply, id_eq] using
      (hF j).integrable_smul_left_of_hasCompactSupport
        ((hDjl j).continuous.comp (continuous_id.sub continuous_const)) (hcjl j)
  have hw := he _ hφ hφc
  rw [firstStrip_coordinateDerivative_shift K hK x l] at hw
  simp_rw [firstStrip_coordinateDerivative_shift (coordinateDerivative l K) hDl x] at hw
  rw [integral_finsetSum _ (fun j _ => hi j)] at hw
  simp_rw [firstStripSpatialSmooth_second_fderiv K hK hKc (hF _) x l]
  rw [firstStripSpatialSmooth_fderiv K hK hKc hB x l]
  simpa only [firstStripSpatialSmooth, mul_neg, sub_neg_eq_add] using hw

/-- A common local-integrability event works for every continuous physical
coefficient multiplying any member of a finite family of actual fields. -/
private theorem firstStrip_coefficient_orbit_locallyIntegrable {n d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (G : Fin n → Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ a : Fin n, ∀ A : Vec d → ℝ, Continuous A →
      LocallyIntegrable (fun y => G a (translate y ω) * (A y : ℂ)) volume := by
  let := reducedLaw_probability Q
  have hg : ∀ᵐ ω ∂reducedLaw Q, ∀ a : Fin n, ∀ S : Set (Vec d), IsCompact S →
      MemLp (fun y => G a (translate y ω)) 2 (volume.restrict S) :=
    ae_all_iff.mpr fun a => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable (G a)).measurable (Lp.memLp (G a))
  filter_upwards [hg] with ω hω
  intro a A hA
  have hl : LocallyIntegrable (fun y => G a (translate y ω)) volume := by
    rw [locallyIntegrable_iff]
    intro S hS
    let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
    exact (hω a S hS).integrable (by norm_num)
  exact hl.mul_continuous (Complex.continuous_ofReal.comp hA)

/-- Weak spatial gradients commute with every compact smooth regularization,
on one event before choosing the kernel, spatial point, or coordinate. -/
private theorem firstStrip_spatial_regularization {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ K : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) K → HasCompactSupport K →
      ContDiff ℝ (⊤ : ℕ∞)
        (firstStripSpatialSmooth K (fun y => f (translate y ω))) ∧
      (∀ l : Fin d, ContDiff ℝ (⊤ : ℕ∞)
        (firstStripSpatialSmooth K (fun y => G l (translate y ω)))) ∧
      ∀ (x : Vec d) (l : Fin d),
        fderiv ℝ (firstStripSpatialSmooth K (fun y => f (translate y ω))) x
          (unitVector l) = firstStripSpatialSmooth K (fun y => G l (translate y ω)) x := by
  let := reducedLaw_probability Q
  have hf := ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q)
    (reducedLaw_stationary Q) (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
  have hg : ∀ᵐ ω ∂reducedLaw Q, ∀ l : Fin d, ∀ A : Set (Vec d), IsCompact A →
      MemLp (fun y => G l (translate y ω)) 2 (volume.restrict A) :=
    ae_all_iff.mpr fun l => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable (G l)).measurable (Lp.memLp (G l))
  filter_upwards [hf, hg, firstStrip_spatial_gradient Q hG] with ω hfω hgω he
  have hloc {v : Vec d → ℂ}
      (hv : ∀ A : Set (Vec d), IsCompact A → MemLp v 2 (volume.restrict A)) :
      LocallyIntegrable v volume := by
    rw [locallyIntegrable_iff]
    intro A hA
    let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hA.measure_ne_top
    exact (hv A hA).integrable (by norm_num)
  intro K hK hKc
  refine ⟨firstStripSpatialSmooth_contDiff K hK hKc (hloc hfω),
    fun l => firstStripSpatialSmooth_contDiff K hK hKc (hloc (hgω l)), ?_⟩
  intro x l
  rw [firstStripSpatialSmooth_fderiv K hK hKc (hloc hfω)]
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y => K (y - x)) :=
    hK.comp (contDiff_id.sub contDiff_const)
  have hφc : HasCompactSupport (fun y => K (y - x)) := by
    have hc := hKc.comp_homeomorph ((Homeomorph.subLeft x).trans (Homeomorph.neg _))
    change HasCompactSupport (fun y => K (-(x - y))) at hc
    simpa only [neg_sub] using hc
  have heq (y : Vec d) : coordinateDerivative l (fun y => K (y - x)) y =
      coordinateDerivative l K (y - x) := by
    have hd := (hK.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
      ((hasFDerivAt_id y).sub (hasFDerivAt_const x y))
    simpa [Function.comp_def, coordinateDerivative] using
      congrArg (fun D : Vec d →L[ℝ] ℝ => D (unitVector l)) hd.fderiv
  simpa only [firstStripSpatialSmooth, heq] using (he l _ hφ hφc).symm

/-- Normalized radial kernels recover every locally integrable field at
almost every spatial point as their radii shrink. -/
private theorem firstStripSpatialSmooth_tendsto {d : ℕ}
    {φ : ℕ → ContDiffBump (0 : Vec d)} {A : ℝ}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (hφratio : ∀ᶠ n in atTop, (φ n).rOut ≤ A * (φ n).rIn)
    {v : Vec d → ℂ} (hv : LocallyIntegrable v volume) :
    ∀ᵐ x ∂volume, Tendsto (fun n => firstStripSpatialSmooth ((φ n).normed volume) v x)
      atTop (𝓝 (v x)) := by
  have heq (n : ℕ) : firstStripSpatialSmooth ((φ n).normed volume) v =
      (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v := by
    rw [firstStripSpatialSmooth_eq_convolution, convolution_flip]
    simp only [ContDiffBump.normed_neg]
  simpa only [heq] using
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hφratio hv

/-- The smooth spatial fields and their classical gradients recover the
actual stationary field and its actual horizontal gradient, samplewise a.e. -/
private theorem firstStrip_spatial_regularization_recovery {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    {φ : ℕ → ContDiffBump (0 : Vec d)} {A : ℝ}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (hφratio : ∀ᶠ n in atTop, (φ n).rOut ≤ A * (φ n).rIn) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂volume,
      Tendsto (fun n => firstStripSpatialSmooth ((φ n).normed volume)
        (fun y => f (translate y ω)) x) atTop (𝓝 (f (translate x ω))) ∧
      ∀ l : Fin d, Tendsto
        (fun n => fderiv ℝ (firstStripSpatialSmooth ((φ n).normed volume)
          (fun y => f (translate y ω))) x (unitVector l))
        atTop (𝓝 (G l (translate x ω))) := by
  let := reducedLaw_probability Q
  have hf := ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q)
    (reducedLaw_stationary Q) (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
  have hg : ∀ᵐ ω ∂reducedLaw Q, ∀ l : Fin d, ∀ B : Set (Vec d), IsCompact B →
      MemLp (fun y => G l (translate y ω)) 2 (volume.restrict B) :=
    ae_all_iff.mpr fun l => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable (G l)).measurable (Lp.memLp (G l))
  filter_upwards [hf, hg, firstStrip_spatial_regularization Q hG] with ω hfω hgω hreg
  have hloc {v : Vec d → ℂ}
      (hv : ∀ B : Set (Vec d), IsCompact B → MemLp v 2 (volume.restrict B)) :
      LocallyIntegrable v volume := by
    rw [locallyIntegrable_iff]
    intro B hB
    let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hB.measure_ne_top
    exact (hv B hB).integrable (by norm_num)
  have hgc : ∀ᵐ x ∂volume, ∀ l : Fin d,
      Tendsto (fun n => firstStripSpatialSmooth ((φ n).normed volume)
        (fun y => G l (translate y ω)) x) atTop (𝓝 (G l (translate x ω))) :=
    ae_all_iff.mpr fun l => firstStripSpatialSmooth_tendsto hφ hφratio (hloc (hgω l))
  filter_upwards [firstStripSpatialSmooth_tendsto hφ hφratio (hloc hfω), hgc]
    with x hfx hgx
  refine ⟨hfx, fun l => ?_⟩
  exact (hgx l).congr' (Eventually.of_forall fun n =>
    ((hreg _ (φ n).contDiff_normed (φ n).hasCompactSupport_normed).2.2 x l).symm)

/-- Stationarity transfers a measurable spatial a.e. bound back to the
literal environment representatives; no evaluation of a spatial null set at zero. -/
private theorem firstStrip_stationary_bound_of_spatial_bound {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (B : FieldPair d → ℝ) (hB : Measurable B) (M : ℝ)
    (hb : ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      B (translate x ω) ≤ M) : ∀ᵐ ω ∂reducedLaw Q, B ω ≤ M := by
  have hm : MeasurableSet {p : Vec d × FieldPair d | B (translate p.1 p.2) ≤ M} :=
    measurableSet_le (hB.comp Probability.continuous_translate.measurable) measurable_const
  have he : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ᵐ ω ∂reducedLaw Q,
      B (translate x ω) ≤ M := (Measure.ae_ae_comm hm).mpr hb
  obtain ⟨x, hx⟩ := he.exists
  have hn := ((measurePreserving_translate (reducedLaw Q)
    (reducedLaw_stationary Q) (-x)).quasiMeasurePreserving).ae hx
  simpa only [translate_add, add_neg_cancel, translate_zero] using hn

/-- A uniform Bernstein bound on the spatial regularizations passes to the
actual scalar field and Euclidean gradient, and then to the stationary law. -/
private theorem firstStrip_bound_of_regularization {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    {φ : ℕ → ContDiffBump (0 : Vec d)} {A : ℝ}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (hφratio : ∀ᶠ n in atTop, (φ n).rOut ≤ A * (φ n).rIn) (M : ℝ)
    (hb : ∀ n : ℕ, ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂volume,
      ‖firstStripSpatialSmooth ((φ n).normed volume) (fun y => f (translate y ω)) x‖ +
        Real.sqrt (∑ l : Fin d,
          ‖fderiv ℝ (firstStripSpatialSmooth ((φ n).normed volume)
            (fun y => f (translate y ω))) x (unitVector l)‖ ^ 2) ≤ M) :
    ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ + Real.sqrt (∑ l : Fin d, ‖G l ω‖ ^ 2) ≤ M := by
  refine firstStrip_stationary_bound_of_spatial_bound Q
    (fun ω => ‖f ω‖ + Real.sqrt (∑ l : Fin d, ‖G l ω‖ ^ 2)) ?_ M ?_
  · exact (Lp.stronglyMeasurable f).measurable.norm.add
      (Real.continuous_sqrt.measurable.comp
        (Finset.measurable_sum Finset.univ fun l _ => (Lp.stronglyMeasurable (G l)).measurable.norm.pow_const 2))
  · filter_upwards [firstStrip_spatial_regularization_recovery Q hG hφ hφratio,
      ae_all_iff.mpr hb] with ω hrec hbound
    filter_upwards [hrec, ae_all_iff.mpr hbound] with x hlim hx
    have hsum := tendsto_finsetSum Finset.univ
      (fun l _ => (hlim.2 l).norm.pow 2)
    have hnorm := hlim.1.norm.add (Real.continuous_sqrt.continuousAt.tendsto.comp hsum)
    exact le_of_tendsto hnorm (Eventually.of_forall hx)

/-- The differential of a radial test of the entire scalar/gradient
system. Its radial factor is shared by all components. -/
private def firstStripSystemRadialDifferential {n d : ℕ} (b c : ℝ)
    (z : Fin n → ℂ) (H : Fin n → Fin d → ℂ) (a : Fin n) (j : Fin d) : ℂ :=
  b • H a j + (2 * c * (∑ q : Fin n, inner ℝ (z q) (H q j))) • z a

/-- The coupled radial differential is the actual coordinate derivative of
one radial test of a differentiable finite system. -/
private theorem firstStrip_system_radial_fderiv {n d : ℕ}
    (v : Fin n → Vec d → ℂ) (x : Vec d)
    (hv : ∀ a : Fin n, DifferentiableAt ℝ (v a) x)
    (φ : ℝ → ℝ) (c : ℝ)
    (hφ : HasDerivAt φ c (∑ a : Fin n, ‖v a x‖ ^ 2)) (a : Fin n) (j : Fin d) :
    fderiv ℝ (fun y => φ (∑ q : Fin n, ‖v q y‖ ^ 2) • v a y) x (unitVector j) =
      firstStripSystemRadialDifferential (φ (∑ q : Fin n, ‖v q x‖ ^ 2)) c
        (fun q => v q x) (fun q k => fderiv ℝ (v q) x (unitVector k)) a j := by
  have hW := HasFDerivAt.fun_sum (u := Finset.univ) (fun q _ =>
    (hasStrictFDerivAt_norm_sq (v q x)).hasFDerivAt.comp x (hv q).hasFDerivAt)
  have h := (hφ.hasFDerivAt.comp x hW).smul (hv a).hasFDerivAt
  have he := congrArg (fun D : Vec d →L[ℝ] ℂ => D (unitVector j)) h.fderiv
  simp only [Function.comp_def, Pi.smul_def'] at he
  rw [he]
  simp only [firstStripSystemRadialDifferential, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, _root_.sum_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply,
    two_smul, Finset.sum_add_distrib]
  congr 1
  congr 1
  ring

/-- Cauchy--Schwarz for the common radial factor uses the Euclidean sum
of the system components, rather than the supremum norm on a function space. -/
private theorem firstStrip_system_radial_factor_sq {n d : ℕ}
    (z : Fin n → ℂ) (H : Fin n → Fin d → ℂ) (j : Fin d) :
    (∑ a : Fin n, inner ℝ (z a) (H a j)) ^ 2 ≤
      (∑ a : Fin n, ‖z a‖ ^ 2) * (∑ a : Fin n, ‖H a j‖ ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun _ _ => sq_nonneg _) (fun _ _ => sq_nonneg _)
  intro a _
  simpa only [pow_two, real_inner_self_eq_norm_mul_norm] using
    real_inner_mul_inner_self_le (z a) (H a j)

/-- A squared bound for every coordinate of the coupled radial differential.
This is the bound used when absorbing coefficient and force commutators. -/
private theorem firstStrip_system_radial_norm_sq {n d : ℕ} (b c : ℝ)
    (z : Fin n → ℂ) (H : Fin n → Fin d → ℂ) :
    (∑ a : Fin n, ∑ j : Fin d,
      ‖firstStripSystemRadialDifferential b c z H a j‖ ^ 2) ≤
      (2 * b ^ 2 + 8 * c ^ 2 * (∑ a : Fin n, ‖z a‖ ^ 2) ^ 2) *
        (∑ a : Fin n, ∑ j : Fin d, ‖H a j‖ ^ 2) := by
  let R : Fin d → ℝ := fun j => ∑ a : Fin n, inner ℝ (z a) (H a j)
  let W : ℝ := ∑ a : Fin n, ‖z a‖ ^ 2
  have hpoint (a : Fin n) (j : Fin d) :
      ‖firstStripSystemRadialDifferential b c z H a j‖ ^ 2 ≤
        2 * b ^ 2 * ‖H a j‖ ^ 2 + 8 * c ^ 2 * R j ^ 2 * ‖z a‖ ^ 2 := by
    have ht := norm_add_le (b • H a j) ((2 * c * R j) • z a)
    have ht2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
    simp only [norm_smul, Real.norm_eq_abs] at ht2
    have hs := sq_nonneg (|b| * ‖H a j‖ - |2 * c * R j| * ‖z a‖)
    change ‖b • H a j + (2 * c * R j) • z a‖ ^ 2 ≤ _
    nlinarith [sq_abs b, sq_abs (2 * c * R j)]
  have hsum := Finset.sum_le_sum fun (a : Fin n) (_ : a ∈ Finset.univ) =>
    Finset.sum_le_sum fun (j : Fin d) (_ : j ∈ Finset.univ) => hpoint a j
  have hrad := Finset.sum_le_sum fun (j : Fin d) (_ : j ∈ Finset.univ) =>
    firstStrip_system_radial_factor_sq z H j
  have hswap : (∑ a : Fin n, ∑ j : Fin d, R j ^ 2 * ‖z a‖ ^ 2) =
      W * (∑ j : Fin d, R j ^ 2) := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, W]
    ring
  have hsum' : (∑ a : Fin n, ∑ j : Fin d,
      ‖firstStripSystemRadialDifferential b c z H a j‖ ^ 2) ≤
      2 * b ^ 2 * (∑ a : Fin n, ∑ j : Fin d, ‖H a j‖ ^ 2) +
        8 * c ^ 2 * (∑ a : Fin n, ∑ j : Fin d, R j ^ 2 * ‖z a‖ ^ 2) := by
    simpa only [Finset.mul_sum, Finset.sum_add_distrib, mul_assoc] using hsum
  have hcross : (∑ a : Fin n, ∑ j : Fin d, R j ^ 2 * ‖z a‖ ^ 2) ≤
      W ^ 2 * (∑ a : Fin n, ∑ j : Fin d, ‖H a j‖ ^ 2) := by
    rw [hswap]
    have hh := mul_le_mul_of_nonneg_left hrad
      (show 0 ≤ W from Finset.sum_nonneg fun a _ => sq_nonneg ‖z a‖)
    simp only [← Finset.mul_sum] at hh
    change W * (∑ j : Fin d, R j ^ 2) ≤
      W * (W * (∑ j : Fin d, ∑ a : Fin n, ‖H a j‖ ^ 2)) at hh
    have hcomm : (∑ j : Fin d, ∑ a : Fin n, ‖H a j‖ ^ 2) =
        ∑ a : Fin n, ∑ j : Fin d, ‖H a j‖ ^ 2 := Finset.sum_comm
    rw [hcomm] at hh
    simpa only [pow_two, mul_assoc] using hh
  have hc := mul_le_mul_of_nonneg_left hcross
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (sq_nonneg c))
  change _ ≤ (2 * b ^ 2 + 8 * c ^ 2 * W ^ 2) * _
  nlinarith

/-- The coupled radial contribution is one real anisotropic quadratic form,
including all cross terms between the scalar and gradient components. -/
private theorem firstStrip_system_radial_energy {n d : ℕ} (A : Mat d)
    (b c : ℝ) (z : Fin n → ℂ) (H : Fin n → Fin d → ℂ) :
    (∑ a : Fin n, ∑ j : Fin d, ∑ k : Fin d,
      star (firstStripSystemRadialDifferential b c z H a j) * (A j k : ℂ) * H a k).re =
      b * (∑ a : Fin n, (∑ j : Fin d, ∑ k : Fin d,
        star (H a j) * (A j k : ℂ) * H a k).re) +
      2 * c * dot (fun j => ∑ a : Fin n, inner ℝ (z a) (H a j))
        (A.mulVec (fun j => ∑ a : Fin n, inner ℝ (z a) (H a j))) := by
  let R : Fin d → ℝ := fun j => ∑ a : Fin n, inner ℝ (z a) (H a j)
  have he (a : Fin n) (j k : Fin d) :
      (star (firstStripSystemRadialDifferential b c z H a j) *
        (A j k : ℂ) * H a k).re =
      b * (star (H a j) * (A j k : ℂ) * H a k).re +
        2 * c * R j * A j k * inner ℝ (z a) (H a k) := by
    simp only [firstStripSystemRadialDifferential, R, real_inner_eq_re_inner ℂ,
      RCLike.inner_apply, RCLike.re_to_complex, Complex.star_def, Complex.real_smul,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, mul_zero, zero_mul,
      sub_zero, zero_add, add_zero, neg_mul, sub_neg_eq_add]
    ring
  have hr : (∑ a : Fin n, ∑ j : Fin d, ∑ k : Fin d,
      2 * c * R j * A j k * inner ℝ (z a) (H a k)) = 2 * c * dot R (A.mulVec R) := by
    calc
      _ = ∑ j : Fin d, ∑ k : Fin d, ∑ a : Fin n,
          2 * c * R j * A j k * inner ℝ (z a) (H a k) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_comm
      _ = ∑ j : Fin d, ∑ k : Fin d, 2 * c * R j * A j k * R k := by
        simp only [R, ← Finset.mul_sum]
      _ = _ := by
        simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
  change Complex.reCLM (∑ a : Fin n, ∑ j : Fin d, ∑ k : Fin d, _) =
    b * (∑ a : Fin n, Complex.reCLM (∑ j : Fin d, ∑ k : Fin d, _)) + _
  simp only [map_sum, Complex.reCLM_apply, he, Finset.sum_add_distrib]
  rw [hr]
  simp only [← Finset.mul_sum, R]

/-- Increasing radial tests of the full system preserve ellipticity with
the literal Euclidean sum of all component derivatives. -/
private theorem firstStrip_system_radial_coercivity {n d : ℕ} (A : Mat d)
    (m b c : ℝ) (hm : 0 ≤ m) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : ∀ ξ : Vec d, m * euclideanSq ξ ≤ dot ξ (A.mulVec ξ))
    (z : Fin n → ℂ) (H : Fin n → Fin d → ℂ) :
    b * m * (∑ a : Fin n, ∑ j : Fin d, ‖H a j‖ ^ 2) ≤
      (∑ a : Fin n, ∑ j : Fin d, ∑ k : Fin d,
        star (firstStripSystemRadialDifferential b c z H a j) *
          (A j k : ℂ) * H a k).re := by
  rw [firstStrip_system_radial_energy]
  have hbase := Finset.sum_le_sum fun (a : Fin n) (_ : a ∈ Finset.univ) =>
    complex_quadratic_lowerBound A m hA (H a)
  have hbbase := mul_le_mul_of_nonneg_left hbase hb
  simp only [← Finset.mul_sum] at hbbase
  have hrad := hA (fun j => ∑ a : Fin n, inner ℝ (z a) (H a j))
  have hpos : 0 ≤ dot (fun j => ∑ a : Fin n, inner ℝ (z a) (H a j))
      (A.mulVec (fun j => ∑ a : Fin n, inner ℝ (z a) (H a j))) := by
    refine (mul_nonneg hm ?_).trans hrad
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hr := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc) hpos
  simpa only [mul_assoc] using hbbase.trans (le_add_of_nonneg_right hr)

/-- First-order system couplings are absorbed without differentiating the
radial weight. In particular the constant is uniform in that weight's slope. -/
private theorem firstStrip_system_coupling_absorption {n d : ℕ}
    (z F : Fin n → ℂ) (H : Fin n → Fin d → ℂ)
    (b ε K : ℝ) (hb : 0 ≤ b) (hε : 0 < ε) (hK : 0 ≤ K)
    (hF : (∑ a : Fin n, ‖F a‖ ^ 2) ≤
      K * (∑ a : Fin n, ∑ j : Fin d, ‖H a j‖ ^ 2)) :
    2 * b * (∑ a : Fin n, inner ℝ (z a) (F a)) ≤
      b * ε * (∑ a : Fin n, ∑ j : Fin d, ‖H a j‖ ^ 2) +
        b * (K / ε) * (∑ a : Fin n, ‖z a‖ ^ 2) := by
  let W : ℝ := ∑ a : Fin n, ‖z a‖ ^ 2
  let S : ℝ := ∑ a : Fin n, ∑ j : Fin d, ‖H a j‖ ^ 2
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : (∑ a : Fin n, inner ℝ (z a) (F a)) ^ 2 ≤
      W * (∑ a : Fin n, ‖F a‖ ^ 2) :=
    firstStrip_system_radial_factor_sq z (fun a (_ : Fin 1) => F a) 0
  have hs : (∑ a : Fin n, inner ℝ (z a) (F a)) ^ 2 ≤
      (ε * S) * ((K / ε) * W) := by
    calc
      _ ≤ W * (∑ a : Fin n, ‖F a‖ ^ 2) := hcs
      _ ≤ W * (K * S) := mul_le_mul_of_nonneg_left hF hW
      _ = _ := by field_simp
  have hy := two_mul_le_add_of_sq_le_mul (mul_nonneg hε.le hS)
    (mul_nonneg (div_nonneg hK hε.le) hW) hs
  have hby := mul_le_mul_of_nonneg_left hy hb
  change 2 * b * _ ≤ b * ε * S + b * (K / ε) * W
  nlinarith

/-- The radial principal energy absorbs first-order and zeroth-order
couplings while retaining half its elliptic dissipation. The growth constant
is independent of the slope of the increasing radial test. -/
private theorem firstStrip_system_bernstein_dissipation {n d : ℕ} (A : Mat d)
    (m b c K L : ℝ) (hm : 0 < m) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hA : ∀ ξ : Vec d, m * euclideanSq ξ ≤ dot ξ (A.mulVec ξ))
    (z F R : Fin n → ℂ) (H : Fin n → Fin d → ℂ)
    (hF : (∑ a : Fin n, ‖F a‖ ^ 2) ≤
      K * (∑ a : Fin n, ∑ j : Fin d, ‖H a j‖ ^ 2))
    (hR : (∑ a : Fin n, ‖R a‖ ^ 2) ≤ L * (∑ a : Fin n, ‖z a‖ ^ 2)) :
    2 * b * (∑ a : Fin n, inner ℝ (z a) (F a)) +
      2 * b * (∑ a : Fin n, inner ℝ (z a) (R a)) -
      (∑ a : Fin n, ∑ j : Fin d, ∑ k : Fin d,
        star (firstStripSystemRadialDifferential b c z H a j) *
          (A j k : ℂ) * H a k).re ≤
      -(b * m / 2) * (∑ a : Fin n, ∑ j : Fin d, ‖H a j‖ ^ 2) +
        b * (2 * K / m + 1 + L) * (∑ a : Fin n, ‖z a‖ ^ 2) := by
  have hdiff := firstStrip_system_radial_coercivity A m b c hm.le hb hc hA z H
  have hfirst := firstStrip_system_coupling_absorption z F H b (m / 2) K
    hb (half_pos hm) hK hF
  have hR' : (∑ a : Fin n, ‖R a‖ ^ 2) ≤
      L * (∑ a : Fin n, ∑ _j : Fin 1, ‖z a‖ ^ 2) := by
    simpa only [Fin.sum_univ_one] using hR
  have hzero := firstStrip_system_coupling_absorption z R
    (fun a (_j : Fin 1) => z a) b 1 L hb (by norm_num) hL hR'
  simp only [Fin.sum_univ_one, mul_one, div_one] at hzero
  have hdiv : K / (m / 2) = 2 * K / m := by ring
  rw [hdiv] at hfirst
  linarith only [hdiff, hfirst, hzero]

/-- A horizontal gradient has zero physical distributional curl on one
common event, before choosing the compact smooth test. -/
private theorem firstStrip_spatial_curl {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ k l : Fin d,
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, G k (translate x ω) * (coordinateDerivative l φ x : ℂ)) =
          ∫ x, G l (translate x ω) * (coordinateDerivative k φ x : ℂ) := by
  filter_upwards [firstStrip_spatial_gradient Q hG] with ω hω
  intro k l φ hφ hφc
  have hd (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j φ) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  rw [hω k _ (hd l) (hφc.fderiv_apply ℝ (unitVector l)),
    hω l _ (hd k) (hφc.fderiv_apply ℝ (unitVector k)),
    EinsteinRelation.Correctors.coordinateDerivative_comm hφ k l]

/-- The coefficient commutator is justified distributionally using compact
smooth tests and local square integrability of the actual gradient. Coefficients
and tests are selected after the common event. -/
private theorem firstStrip_spatial_coefficient_commutator {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ k l : Fin d,
      ∀ A φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) A →
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, G k (translate x ω) * (A x * coordinateDerivative l φ x : ℝ)) =
          (∫ x, G l (translate x ω) * (A x * coordinateDerivative k φ x : ℝ)) +
          (∫ x, G l (translate x ω) *
            (φ x * coordinateDerivative k A x : ℝ)) -
          (∫ x, G k (translate x ω) *
            (φ x * coordinateDerivative l A x : ℝ)) := by
  let := reducedLaw_probability Q
  have hloc : ∀ᵐ ω ∂reducedLaw Q, ∀ j : Fin d,
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => G j (translate x ω)) 2 (volume.restrict K) :=
    ae_all_iff.mpr fun j => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable (G j)).measurable (Lp.memLp _)
  filter_upwards [firstStrip_spatial_curl Q hG, hloc] with ω hcurl hloc
  intro k l A φ hA hφ hφc
  have hd (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j φ) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hAd (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j A) :=
    (hA.fderiv_right (by simp)).clm_apply contDiff_const
  have hsplit (i j : Fin d) :
      (∫ x, G i (translate x ω) * (coordinateDerivative j (fun x => A x * φ x) x : ℂ)) =
        (∫ x, G i (translate x ω) * (A x * coordinateDerivative j φ x : ℝ)) +
        (∫ x, G i (translate x ω) * (φ x * coordinateDerivative j A x : ℝ)) := by
    have h1 := integrable_spatial_mul_test (hloc i)
      (hA.continuous.mul (hd j).continuous)
      ((hφc.fderiv_apply ℝ (unitVector j)).mul_left (f := A))
    have h2 := integrable_spatial_mul_test (hloc i)
      (hφ.continuous.mul (hAd j).continuous)
      (hφc.mul_right (f' := coordinateDerivative j A))
    simp only [Pi.mul_apply] at h1 h2
    rw [← integral_add h1 h2]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [coordinateDerivative_mul j A φ x
      (hA.differentiable (by simp)).differentiableAt
      (hφ.differentiable (by simp)).differentiableAt]
    push_cast
    ring
  have hc := hcurl k l (fun x => A x * φ x) (hA.mul hφ) (hφc.mul_left (f := A))
  rw [hsplit k l, hsplit l k] at hc
  linear_combination hc

/-- The differentiated diffusion flux splits into the gradient diffusion
and its two coefficient commutators for the actual reduced coefficients. -/
private theorem firstStrip_diffusion_commutator {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ j k l : Fin d,
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, G k (translate x ω) *
          (ω.1 x j k * coordinateDerivative j (coordinateDerivative l φ) x : ℝ)) =
        (∫ x, G l (translate x ω) *
          (ω.1 x j k * coordinateDerivative k (coordinateDerivative j φ) x : ℝ)) +
        (∫ x, G l (translate x ω) *
          (coordinateDerivative j φ x * coordinateDerivative k (fun y => ω.1 y j k) x : ℝ)) -
        (∫ x, G k (translate x ω) *
          (coordinateDerivative j φ x * coordinateDerivative l (fun y => ω.1 y j k) x : ℝ)) := by
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  filter_upwards [firstStrip_spatial_coefficient_commutator Q hG, hM Q hQ] with ω hc hs
  intro j k l φ hφ hφc
  have hd : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j φ) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have he := hc k l (fun y => ω.1 y j k) (coordinateDerivative j φ)
    (hs.1.1 j k) hd (hφc.fderiv_apply ℝ (unitVector j))
  rw [← EinsteinRelation.Correctors.coordinateDerivative_comm hφ j l] at he
  exact he

/-- All finite physical coefficient fluxes can be integrated term by term.
The event is chosen before the smooth coefficient and compact test. -/
private theorem firstStrip_integral_flux_sum {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (G : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ A : Fin d → Fin d → Vec d → ℝ,
      (∀ j k, Continuous (A j k)) →
      ∀ ψ : Fin d → Vec d → ℝ,
      (∀ j, Continuous (ψ j)) → (∀ j, HasCompactSupport (ψ j)) →
        (∫ x, ∑ j, (∑ k, (A j k x : ℂ) * G k (translate x ω)) * (ψ j x : ℂ)) =
          ∑ j, ∑ k, ∫ x, G k (translate x ω) * (A j k x * ψ j x : ℝ) := by
  let := reducedLaw_probability Q
  have hloc : ∀ᵐ ω ∂reducedLaw Q, ∀ j : Fin d,
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => G j (translate x ω)) 2 (volume.restrict K) :=
    ae_all_iff.mpr fun j => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable (G j)).measurable (Lp.memLp _)
  filter_upwards [hloc] with ω hloc
  intro A hA ψ hψ hψc
  have hi (j k : Fin d) : Integrable
      (fun x => G k (translate x ω) * (A j k x * ψ j x : ℝ)) volume :=
    integrable_spatial_mul_test (hloc k) ((hA j k).mul (hψ j))
      ((hψc j).mul_left (f := A j k))
  calc
    _ = ∫ x, ∑ j, ∑ k, G k (translate x ω) * (A j k x * ψ j x : ℝ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring
    _ = _ := by
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi j k))]
      apply Finset.sum_congr rfl
      intro j _
      exact integral_finsetSum _ (fun k _ => hi j k)

/-- The actual anisotropic diffusion flux is expanded with both commutators.
No second strong derivative of the evolved field is required. -/
private theorem firstStrip_diffusion_flux_expansion {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ l : Fin d,
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, ∑ j, (∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) *
          (coordinateDerivative j (coordinateDerivative l φ) x : ℂ)) =
        ∑ j, ∑ k,
          ((∫ x, G l (translate x ω) *
            (ω.1 x j k * coordinateDerivative k (coordinateDerivative j φ) x : ℝ)) +
          (∫ x, G l (translate x ω) *
            (coordinateDerivative j φ x * coordinateDerivative k (fun y => ω.1 y j k) x : ℝ)) -
          (∫ x, G k (translate x ω) *
            (coordinateDerivative j φ x * coordinateDerivative l (fun y => ω.1 y j k) x : ℝ))) := by
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  filter_upwards [firstStrip_integral_flux_sum Q G,
    firstStrip_diffusion_commutator Q hQ hG, hM Q hQ] with ω hsum hc hs
  intro l φ hφ hφc
  have hd (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j φ) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdd (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (coordinateDerivative j (coordinateDerivative l φ)) :=
    ((hd l).fderiv_right (by simp)).clm_apply contDiff_const
  rw [hsum (fun j k x => ω.1 x j k) (fun j k => (hs.1.1 j k).continuous)
    (fun j => coordinateDerivative j (coordinateDerivative l φ))
    (fun j => (hdd j).continuous)
    (fun j => (hφc.fderiv_apply ℝ (unitVector l)).fderiv_apply ℝ (unitVector j))]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact hc j k l φ hφ hφc

/-- The force flux has the matching weak coefficient commutator, with the
original column and complex force coefficient left unchanged. -/
private theorem firstStrip_force_flux_expansion {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ i l : Fin d,
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, (∑ j, (ω.1 x j i : ℂ) * G j (translate x ω)) *
          (coordinateDerivative l φ x : ℂ)) =
        ∑ j,
          ((∫ x, G l (translate x ω) *
            (ω.1 x j i * coordinateDerivative j φ x : ℝ)) +
          (∫ x, G l (translate x ω) *
            (φ x * coordinateDerivative j (fun y => ω.1 y j i) x : ℝ)) -
          (∫ x, G j (translate x ω) *
            (φ x * coordinateDerivative l (fun y => ω.1 y j i) x : ℝ))) := by
  let := reducedLaw_probability Q
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  have hloc : ∀ᵐ ω ∂reducedLaw Q, ∀ j : Fin d,
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => G j (translate x ω)) 2 (volume.restrict K) :=
    ae_all_iff.mpr fun j => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable (G j)).measurable (Lp.memLp _)
  filter_upwards [firstStrip_spatial_coefficient_commutator Q hG,
    hloc, hM Q hQ] with ω hc hloc hs
  intro i l φ hφ hφc
  have hd : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative l φ) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hi (j : Fin d) : Integrable
      (fun x => G j (translate x ω) *
        (ω.1 x j i * coordinateDerivative l φ x : ℝ)) volume :=
    integrable_spatial_mul_test (hloc j) ((hs.1.1 j i).continuous.mul hd.continuous)
      ((hφc.fderiv_apply ℝ (unitVector l)).mul_left (f := fun x => ω.1 x j i))
  calc
    _ = ∫ x, ∑ j, G j (translate x ω) *
        (ω.1 x j i * coordinateDerivative l φ x : ℝ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    _ = ∑ j, ∫ x, G j (translate x ω) *
        (ω.1 x j i * coordinateDerivative l φ x : ℝ) := integral_finsetSum _ (fun j _ => hi j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact hc j l (fun x => ω.1 x j i) φ (hs.1.1 j i) hφ hφc

/-- Differentiating the transpose column flux retains the scalar field in
the coefficient derivative term. This is distinct from the forward commutator. -/
private theorem firstStrip_transpose_force_flux_expansion {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ i l : Fin d,
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, ∑ j, (ω.1 x j i : ℂ) * f (translate x ω) *
          (coordinateDerivative j (coordinateDerivative l φ) x : ℂ)) =
        -(∑ j,
          ((∫ x, G l (translate x ω) *
            (ω.1 x j i * coordinateDerivative j φ x : ℝ)) +
          (∫ x, f (translate x ω) *
            (coordinateDerivative j φ x * coordinateDerivative l (fun y => ω.1 y j i) x : ℝ)))) := by
  let := reducedLaw_probability Q
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  have hloc := ae_complex_function_orbit_memLp_on_all_compacts
    (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
  filter_upwards [firstStrip_spatial_gradient Q hG, hloc, hM Q hQ] with ω hg hf hs
  intro i l φ hφ hφc
  have hd (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j φ) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdd (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (coordinateDerivative j (coordinateDerivative l φ)) :=
    ((hd l).fderiv_right (by simp)).clm_apply contDiff_const
  have hA (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.1 x j i) := hs.1.1 j i
  have hAd (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (coordinateDerivative l (fun x => ω.1 x j i)) :=
    ((hA j).fderiv_right (by simp)).clm_apply contDiff_const
  have h1 (j : Fin d) : Integrable
      (fun x => f (translate x ω) *
        (ω.1 x j i * coordinateDerivative j (coordinateDerivative l φ) x : ℝ)) volume :=
    integrable_spatial_mul_test hf ((hA j).continuous.mul (hdd j).continuous)
      (((hφc.fderiv_apply ℝ (unitVector l)).fderiv_apply ℝ (unitVector j)).mul_left
        (f := fun x => ω.1 x j i))
  have h2 (j : Fin d) : Integrable
      (fun x => f (translate x ω) *
        (coordinateDerivative j φ x * coordinateDerivative l (fun y => ω.1 y j i) x : ℝ)) volume :=
    integrable_spatial_mul_test hf ((hd j).continuous.mul (hAd j).continuous)
      ((hφc.fderiv_apply ℝ (unitVector j)).mul_right
        (f' := coordinateDerivative l (fun y => ω.1 y j i)))
  have hterm (j : Fin d) :
      (∫ x, f (translate x ω) *
        (ω.1 x j i * coordinateDerivative j (coordinateDerivative l φ) x : ℝ)) =
      -((∫ x, G l (translate x ω) * (ω.1 x j i * coordinateDerivative j φ x : ℝ)) +
        (∫ x, f (translate x ω) *
          (coordinateDerivative j φ x * coordinateDerivative l (fun y => ω.1 y j i) x : ℝ))) := by
    have he := hg l (fun x => ω.1 x j i * coordinateDerivative j φ x)
      ((hA j).mul (hd j))
      ((hφc.fderiv_apply ℝ (unitVector j)).mul_left (f := fun x => ω.1 x j i))
    have hprod :
        (∫ x, f (translate x ω) *
          (coordinateDerivative l (fun y => ω.1 y j i * coordinateDerivative j φ y) x : ℂ)) =
        (∫ x, f (translate x ω) *
          (ω.1 x j i * coordinateDerivative j (coordinateDerivative l φ) x : ℝ)) +
        (∫ x, f (translate x ω) *
          (coordinateDerivative j φ x * coordinateDerivative l (fun y => ω.1 y j i) x : ℝ)) := by
      rw [← integral_add (h1 j) (h2 j)]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [coordinateDerivative_mul l (fun y => ω.1 y j i) (coordinateDerivative j φ) x
        ((hA j).differentiable (by simp)).differentiableAt
        ((hd j).differentiable (by simp)).differentiableAt,
        EinsteinRelation.Correctors.coordinateDerivative_comm hφ l j]
      push_cast
      ring
    rw [hprod] at he
    linear_combination he
  calc
    _ = ∫ x, ∑ j, f (translate x ω) *
        (ω.1 x j i * coordinateDerivative j (coordinateDerivative l φ) x : ℝ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    _ = ∑ j, ∫ x, f (translate x ω) *
        (ω.1 x j i * coordinateDerivative j (coordinateDerivative l φ) x : ℝ) :=
      integral_finsetSum _ (fun j _ => h1 j)
    _ = _ := by simp_rw [hterm, Finset.sum_neg_distrib]

/-- The two actual transpose flux terms can be separated under the physical
integral. Local square integrability supplies the necessary integrability. -/
private theorem firstStrip_transpose_flux_split {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (f : Lp ℂ 2 (reducedLaw Q))
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ (i l : Fin d) (ζ : ℂ),
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, ∑ j,
          ((∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) -
            2 * ζ * (ω.1 x j i : ℂ) * f (translate x ω)) *
              (coordinateDerivative j (coordinateDerivative l φ) x : ℂ)) =
        (∫ x, ∑ j, (∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) *
          (coordinateDerivative j (coordinateDerivative l φ) x : ℂ)) -
        2 * ζ * (∫ x, ∑ j, (ω.1 x j i : ℂ) * f (translate x ω) *
          (coordinateDerivative j (coordinateDerivative l φ) x : ℂ)) := by
  let := reducedLaw_probability Q
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  have hlocal (v : Lp ℂ 2 (reducedLaw Q)) :=
    ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q)
      (reducedLaw_stationary Q) (Lp.stronglyMeasurable v).measurable (Lp.memLp v)
  have hlocG := ae_all_iff.mpr (fun k => hlocal (G k))
  filter_upwards [hlocal f, hlocG, hM Q hQ] with ω hf hG hs
  intro i l ζ φ hφ hφc
  let ψ := fun j => coordinateDerivative j (coordinateDerivative l φ)
  have hψ (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (ψ j) := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative l φ) :=
      (hφ.fderiv_right (by simp)).clm_apply contDiff_const
    exact (hd.fderiv_right (by simp)).clm_apply contDiff_const
  have hψc (j : Fin d) : HasCompactSupport (ψ j) :=
    (hφc.fderiv_apply ℝ (unitVector l)).fderiv_apply ℝ (unitVector j)
  have hmul (v : Vec d → ℂ)
      (hv : ∀ K : Set (Vec d), IsCompact K → MemLp v 2 (volume.restrict K))
      (j k : Fin d) : Integrable
        (fun x => (ω.1 x j k : ℂ) * v x * (ψ j x : ℂ)) volume := by
    have hi := integrable_spatial_mul_test hv
      ((hs.1.1 j k).continuous.mul (hψ j).continuous)
      ((hψc j).mul_left (f := fun x => ω.1 x j k))
    convert hi using 1
    funext x
    simp only [Pi.mul_apply]
    push_cast
    ring
  have hD : Integrable (fun x => ∑ j,
      (∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) * (ψ j x : ℂ)) volume := by
    simp_rw [Finset.sum_mul]
    exact integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => hmul _ (hG k) j k
  have hF : Integrable (fun x => ∑ j,
      (ω.1 x j i : ℂ) * f (translate x ω) * (ψ j x : ℂ)) volume :=
    integrable_finsetSum _ fun j _ => hmul _ hf j i
  change (∫ x, ∑ j,
    ((∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) -
      2 * ζ * (ω.1 x j i : ℂ) * f (translate x ω)) * (ψ j x : ℂ)) = _
  calc
    _ = ∫ x, (∑ j, (∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) * (ψ j x : ℂ)) -
        2 * ζ * (∑ j, (ω.1 x j i : ℂ) * f (translate x ω) * (ψ j x : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [integral_sub hD (hF.const_mul (2 * ζ)), integral_const_mul]

/-- The forward physical gradient equation, tested in time. No time derivative
or second strong spatial derivative of the gradient is assumed. -/
private theorem firstStrip_forward_physical_gradient {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ l : Fin d,
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, (∫ s in Icc (0 : ℝ) (t : ℝ), η' s • (hP.gradientOrbit f s) l)
          (translate x ω) * (φ x : ℂ)) =
          -(1 / 2 : ℂ) * (∫ x, ∑ j,
            (∑ k, (ω.1 x j k : ℂ) *
              (∫ s in Icc (0 : ℝ) (t : ℝ), η s • (hP.gradientOrbit f s) k)
                (translate x ω)) * (coordinateDerivative j (coordinateDerivative l φ) x : ℂ)) +
          ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
            (∫ s in Icc (0 : ℝ) (t : ℝ), η s • (hP.gradientOrbit f s) j)
              (translate x ω)) * (coordinateDerivative l φ x : ℂ)) := by
  have hg := firstStrip_spatial_gradient Q (hP.weighted_integral_orbit_gradient f η' hη' t)
  filter_upwards [hg, hP.time_test_spatial_flux_all_tests f η η' hη hη' t hzero ht]
    with ω hg he
  intro l φ hφ hφc
  have hd : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative l φ) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdc : HasCompactSupport (coordinateDerivative l φ) :=
    hφc.fderiv_apply ℝ (unitVector l)
  rw [hg l φ hφ hφc, he (coordinateDerivative l φ) hd hdc]
  ring

/-- The forward actual gradient equation with its differentiated coefficient
terms exposed. The complex force keeps its sign and its full column. -/
private theorem firstStrip_forward_gradient_expanded {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    let G := fun k => ∫ s in Icc (0 : ℝ) (t : ℝ), η s • (hP.gradientOrbit f s) k
    ∀ᵐ ω ∂reducedLaw Q, ∀ l : Fin d,
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, (∫ s in Icc (0 : ℝ) (t : ℝ), η' s • (hP.gradientOrbit f s) l)
          (translate x ω) * (φ x : ℂ)) =
        -(1 / 2 : ℂ) * (∑ j, ∑ k,
          ((∫ x, G l (translate x ω) *
            (ω.1 x j k * coordinateDerivative k (coordinateDerivative j φ) x : ℝ)) +
          (∫ x, G l (translate x ω) *
            (coordinateDerivative j φ x * coordinateDerivative k (fun y => ω.1 y j k) x : ℝ)) -
          (∫ x, G k (translate x ω) *
            (coordinateDerivative j φ x * coordinateDerivative l (fun y => ω.1 y j k) x : ℝ)))) +
        ζ * (∑ j,
          ((∫ x, G l (translate x ω) *
            (ω.1 x j i * coordinateDerivative j φ x : ℝ)) +
          (∫ x, G l (translate x ω) *
            (φ x * coordinateDerivative j (fun y => ω.1 y j i) x : ℝ)) -
          (∫ x, G j (translate x ω) *
            (φ x * coordinateDerivative l (fun y => ω.1 y j i) x : ℝ)))) := by
  have hc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hg := hP.weighted_integral_orbit_gradient f η hc t
  filter_upwards [firstStrip_forward_physical_gradient Q i ζ P hP f η η' hη hη' t hzero ht,
    firstStrip_diffusion_flux_expansion Q hQ hg,
    firstStrip_force_flux_expansion Q hQ hg] with ω he hdiff hforce
  intro l φ hφ hφc
  rw [he l φ hφ hφc, hdiff l φ hφ hφc, hforce i l φ hφ hφc]

/-- The true bilinear-transpose gradient equation keeps the force in the
column flux, including its complex sign, under physical time testing. -/
private theorem firstStrip_transpose_physical_gradient {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (f : Lp ℂ 2 (reducedLaw Q))
    (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ l : Fin d,
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, ((∫ s in Icc (0 : ℝ) (t : ℝ),
          η' s • complexTransposeGradientOrbit Q T f s) l)
          (translate x ω) * (φ x : ℂ)) =
          -(1 / 2 : ℂ) * (∫ x, ∑ j,
            ((∑ k, (ω.1 x j k : ℂ) *
              ((∫ s in Icc (0 : ℝ) (t : ℝ),
                η s • complexTransposeGradientOrbit Q T f s) k) (translate x ω)) -
              2 * ζ * (ω.1 x j i : ℂ) *
                (∫ s in Icc (0 : ℝ) (t : ℝ), η s • T s.toNNReal f) (translate x ω)) *
                  (coordinateDerivative j (coordinateDerivative l φ) x : ℂ)) := by
  have hg := firstStrip_spatial_gradient Q
    (hT.weighted_integral_orbit_gradient hP f η' hη' t)
  filter_upwards [hg,
    hT.time_test_spatial_flux_integrated_gradient hP f η η' hη hη' t hzero ht]
    with ω hg he
  intro l φ hφ hφc
  have hd : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative l φ) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdc : HasCompactSupport (coordinateDerivative l φ) :=
    hφc.fderiv_apply ℝ (unitVector l)
  rw [hg l φ hφ hφc, he (coordinateDerivative l φ) hd hdc]
  ring

/-- The actual transpose gradient equation with both its diffusion and
column-force coefficient derivatives exposed, retaining the bilinear sign. -/
private theorem firstStrip_transpose_gradient_expanded {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (f : Lp ℂ 2 (reducedLaw Q))
    (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    let U := ∫ s in Icc (0 : ℝ) (t : ℝ), η s • T s.toNNReal f
    let G := fun k => (∫ s in Icc (0 : ℝ) (t : ℝ),
      η s • complexTransposeGradientOrbit Q T f s) k
    ∀ᵐ ω ∂reducedLaw Q, ∀ l : Fin d,
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, ((∫ s in Icc (0 : ℝ) (t : ℝ),
          η' s • complexTransposeGradientOrbit Q T f s) l)
          (translate x ω) * (φ x : ℂ)) =
        -(1 / 2 : ℂ) * (∑ j, ∑ k,
          ((∫ x, G l (translate x ω) *
            (ω.1 x j k * coordinateDerivative k (coordinateDerivative j φ) x : ℝ)) +
          (∫ x, G l (translate x ω) *
            (coordinateDerivative j φ x * coordinateDerivative k (fun y => ω.1 y j k) x : ℝ)) -
          (∫ x, G k (translate x ω) *
            (coordinateDerivative j φ x * coordinateDerivative l (fun y => ω.1 y j k) x : ℝ)))) -
        ζ * (∑ j,
          ((∫ x, G l (translate x ω) *
            (ω.1 x j i * coordinateDerivative j φ x : ℝ)) +
          (∫ x, U (translate x ω) *
            (coordinateDerivative j φ x * coordinateDerivative l (fun y => ω.1 y j i) x : ℝ)))) := by
  have hc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hg := hT.weighted_integral_orbit_gradient hP f η hc t
  filter_upwards [firstStrip_transpose_physical_gradient Q i ζ P T hP hT f
    η η' hη hη' t hzero ht,
    firstStrip_transpose_flux_split Q hQ _ _,
    firstStrip_diffusion_flux_expansion Q hQ hg,
    firstStrip_transpose_force_flux_expansion Q hQ hg] with ω he hsplit hdiff hforce
  intro l φ hφ hφc
  rw [he l φ hφ hφc, hsplit i l ζ φ hφ hφc,
    hdiff l φ hφ hφc, hforce i l φ hφ hφc]
  ring

/-- A time orbit of gradients whose integrability follows from the actual
forward/transpose energy theory, with the clock force placed in its datum. -/
private def firstStripTimeGradient {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (ν : EndpointIndex d) (s : ℝ) : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
  match ν with
  | .inl k => hP.gradientOrbit (β k + ζ • a ⟨0, by omega⟩ k) s
  | .inr false => hP.gradientOrbit (ζ • μ) s
  | .inr true => complexTransposeGradientOrbit Q T (β ⟨0, by omega⟩) s

/-- The time-integrable family is exactly the previously chosen actual
endpoint gradient at every positive time, including the clock endpoint. -/
private theorem firstStripTimeGradient_eq {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (ν : EndpointIndex d) {s : ℝ} (hs : 0 < s) :
    (fun j => firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) =
      firstStripGradient hd Q β a μ ζ P T hP ν s.toNNReal := by
  cases ν with
  | inl k =>
    simp only [firstStripTimeGradient, IsComplexEnvironmentSemigroup.gradientOrbit,
      firstStripGradient, dite_eq_left hs, dite_eq_left (Real.toNNReal_pos.mpr hs)]
  | inr b =>
    cases b with
    | false =>
      funext j
      simp only [firstStripTimeGradient, IsComplexEnvironmentSemigroup.gradientOrbit,
        firstStripGradient, dite_eq_left hs, dite_eq_left (Real.toNNReal_pos.mpr hs),
        map_smul, PiLp.smul_apply]
    | true =>
      simp only [firstStripTimeGradient, firstStripGradient, Real.toNNReal_of_nonneg hs.le]
      rfl

/-- Temporal primitives of the actual endpoint have the integrals of its
actual gradients. This is the closed-graph step needed for physical time tests. -/
private theorem firstStrip_time_primitive_gradient {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (η : ℝ → ℝ) (hη : Continuous η) (t : ℝ≥0) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (∫ s in Icc (0 : ℝ) (t : ℝ),
        η s • uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal)
      (fun j => ∫ s in Icc (0 : ℝ) (t : ℝ),
        η s • firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) := by
  have hc : Continuous (fun s : ℝ => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) := by
    cases ν with
    | inl k => exact (hP.2.2.1 _).comp continuous_real_toNNReal
    | inr b =>
      cases b with
      | false =>
        change Continuous (fun s : ℝ => ζ • P s.toNNReal μ)
        exact (continuous_const : Continuous (fun _ : ℝ => ζ)).smul
          ((hP.2.2.1 μ).comp continuous_real_toNNReal)
      | true => exact (hT.continuous_apply hP _).comp continuous_real_toNNReal
  have hi : IntegrableOn (firstStripTimeGradient hd Q β a μ ζ P T hP ν)
      (Icc (0 : ℝ) (t : ℝ)) := by
    cases ν with
    | inl k => exact hP.integrableOn_gradientOrbit _ t
    | inr b =>
      cases b with
      | false => exact hP.integrableOn_gradientOrbit _ t
      | true => exact hT.integrableOn_gradientOrbit hP _ t
  intro j
  let C := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j
  have hji : IntegrableOn
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s j)
      (Icc (0 : ℝ) (t : ℝ)) := C.integrable_comp hi
  apply HasComplexHorizontalDerivative.integral_of_ae
    ((hη.smul hc).continuousOn.integrableOn_compact isCompact_Icc)
    (hji.continuousOn_smul hη.continuousOn isCompact_Icc)
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with s hs hs0
  have hpos := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  have hgrad := firstStripGradient_spec hd Q hQ β a μ ζ P T hP hT hβ ν
    s.toNNReal (Real.toNNReal_pos.mpr hpos)
  rw [← firstStripTimeGradient_eq hd Q β a μ ζ P T hP ν hpos] at hgrad
  simpa only [Complex.coe_smul] using! (hgrad j).smul (η s : ℂ)

/-- Physical distributional gradient evolution for every actual endpoint.
Time integrals are Bochner primitives; each temporal test has one event before
all spatial coordinates and all compact smooth spatial tests. -/
private theorem firstStrip_endpoint_physical_gradient {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ l : Fin d,
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, (∫ s in Icc (0 : ℝ) (t : ℝ),
          η' s • firstStripTimeGradient hd Q β a μ ζ P T hP ν s l)
          (translate x ω) * (φ x : ℂ)) =
        if ν = .inr true then
          -(1 / 2 : ℂ) * (∫ x, ∑ j,
            ((∑ k, (ω.1 x j k : ℂ) *
              (∫ s in Icc (0 : ℝ) (t : ℝ),
                η s • firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) (translate x ω)) -
              2 * ζ * (ω.1 x j ⟨0, by omega⟩ : ℂ) *
                (∫ s in Icc (0 : ℝ) (t : ℝ),
                  η s • uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) (translate x ω)) *
                  (coordinateDerivative j (coordinateDerivative l φ) x : ℂ))
        else
          -(1 / 2 : ℂ) * (∫ x, ∑ j,
            (∑ k, (ω.1 x j k : ℂ) *
              (∫ s in Icc (0 : ℝ) (t : ℝ),
                η s • firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) (translate x ω)) *
                  (coordinateDerivative j (coordinateDerivative l φ) x : ℂ)) +
          ζ * (∫ x, (∑ j, (ω.1 x j ⟨0, by omega⟩ : ℂ) *
            (∫ s in Icc (0 : ℝ) (t : ℝ),
              η s • firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) (translate x ω)) *
                (coordinateDerivative l φ x : ℂ)) := by
  cases ν with
  | inl k =>
    simpa only [firstStripTimeGradient, reduceCtorEq, ↓reduceIte] using
      firstStrip_forward_physical_gradient Q ⟨0, by omega⟩ ζ P hP
        (β k + ζ • a ⟨0, by omega⟩ k) η η' hη hη' t hzero ht
  | inr b =>
    cases b with
    | false =>
      simpa only [firstStripTimeGradient, Sum.inr.injEq, Bool.false_eq_true, ↓reduceIte] using
        firstStrip_forward_physical_gradient Q ⟨0, by omega⟩ ζ P hP
          (ζ • μ) η η' hη hη' t hzero ht
    | true =>
      have hc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
      have hcoord (w : ℝ → ℝ) (hw : Continuous w) (j : Fin d) :
          ((∫ s in Icc (0 : ℝ) (t : ℝ),
            w s • complexTransposeGradientOrbit Q T (β ⟨0, by omega⟩) s) j) =
          ∫ s in Icc (0 : ℝ) (t : ℝ),
            w s • (complexTransposeGradientOrbit Q T (β ⟨0, by omega⟩) s) j := by
        let C := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j
        have hi := C.integral_comp_comm
          (hT.integrableOn_weighted_gradientOrbit hP (β ⟨0, by omega⟩) w hw t)
        simpa only [C, ContinuousLinearMap.map_smul_of_tower, PiLp.proj_apply, PiLp.smul_apply] using hi.symm
      have he := firstStrip_transpose_physical_gradient Q ⟨0, by omega⟩ ζ P T hP hT
        (β ⟨0, by omega⟩) η η' hη hη' t hzero ht
      simp_rw [hcoord η hc, hcoord η' hη'] at he
      simpa only [firstStripTimeGradient, uncenteredEndpoint, transposeEndpoint,
        ↓reduceIte] using he

/-- The actual endpoint gradient equation after spatial smoothing. The event
precedes the smoothing kernel and spatial point; time remains distributional. -/
private theorem firstStrip_endpoint_regularized_gradient {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    let U := ∫ s in Icc (0 : ℝ) (t : ℝ),
      η s • uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal
    let H := fun k => ∫ s in Icc (0 : ℝ) (t : ℝ),
      η s • firstStripTimeGradient hd Q β a μ ζ P T hP ν s k
    let V := fun l => ∫ s in Icc (0 : ℝ) (t : ℝ),
      η' s • firstStripTimeGradient hd Q β a μ ζ P T hP ν s l
    ∀ᵐ ω ∂reducedLaw Q,
      let F := fun j y => (∑ k, (ω.1 y j k : ℂ) * H k (translate y ω)) -
        (if ν = .inr true then 2 * ζ else 0) *
          ((ω.1 y j ⟨0, by omega⟩ : ℂ) * U (translate y ω))
      let B := fun y => ∑ j, (ω.1 y j ⟨0, by omega⟩ : ℂ) * H j (translate y ω)
      ∀ K : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) K → HasCompactSupport K →
        ∀ (x : Vec d) (l : Fin d),
          firstStripSpatialSmooth K (fun y => V l (translate y ω)) x =
            -(1 / 2 : ℂ) * (∑ j, fderiv ℝ
              (fun z => fderiv ℝ (firstStripSpatialSmooth K (F j)) z (unitVector l))
              x (unitVector j)) -
            (if ν = .inr true then 0 else ζ) *
              fderiv ℝ (firstStripSpatialSmooth K B) x (unitVector l) := by
  let U := ∫ s in Icc (0 : ℝ) (t : ℝ),
    η s • uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal
  let H := fun k => ∫ s in Icc (0 : ℝ) (t : ℝ),
    η s • firstStripTimeGradient hd Q β a μ ζ P T hP ν s k
  let V := fun l => ∫ s in Icc (0 : ℝ) (t : ℝ),
    η' s • firstStripTimeGradient hd Q β a μ ζ P T hP ν s l
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  have hH := firstStrip_coefficient_orbit_locallyIntegrable Q H
  have hU := firstStrip_coefficient_orbit_locallyIntegrable Q (fun _ : Fin 1 => U)
  filter_upwards [firstStrip_endpoint_physical_gradient hd Q β a μ ζ P T hP hT ν
    η η' hη hη' t hzero ht, hH, hU, hM Q hQ] with ω he hH hU hs
  let F := fun j y => (∑ k, (ω.1 y j k : ℂ) * H k (translate y ω)) -
    (if ν = .inr true then 2 * ζ else 0) *
      ((ω.1 y j ⟨0, by omega⟩ : ℂ) * U (translate y ω))
  let B := fun y => ∑ j, (ω.1 y j ⟨0, by omega⟩ : ℂ) * H j (translate y ω)
  have hprod (j k : Fin d) : LocallyIntegrable
      (fun y => (ω.1 y j k : ℂ) * H k (translate y ω)) volume := by
    simpa only [mul_comm] using hH k _ (hs.1.1 j k).continuous
  have hF (j : Fin d) : LocallyIntegrable (F j) volume := by
    have hsum := locallyIntegrable_finsetSum Finset.univ (fun k _ => hprod j k)
    have hu := (hU 0 (fun y => ω.1 y j ⟨0, by omega⟩)
      (hs.1.1 j ⟨0, by omega⟩).continuous).smul
        (if ν = .inr true then 2 * ζ else 0)
    convert hsum.sub hu using 1
    funext y
    simp only [F, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hB : LocallyIntegrable B volume := by
    apply locallyIntegrable_finsetSum Finset.univ
    intro j _
    simpa only [mul_comm] using
      hH j (fun y => ω.1 y j ⟨0, by omega⟩) (hs.1.1 j ⟨0, by omega⟩).continuous
  dsimp only
  intro K hK hKc x l
  apply firstStripSpatialSmooth_weak_second_order
    (fun y => V l (translate y ω)) B F hB hF (-(1 / 2 : ℂ))
      (if ν = .inr true then 0 else ζ) l ?_ K hK hKc x
  intro φ hφ hφc
  have hw := he l φ hφ hφc
  by_cases hν : ν = .inr true
  · simpa only [F, U, H, V, hν, ↓reduceIte, zero_mul, add_zero, mul_assoc] using hw
  · simpa only [F, B, U, H, V, hν, ↓reduceIte, zero_mul, sub_zero] using hw

/- Structural bounds for the literal initial jets. The common bound is
chosen before the environment law, as required by the first-strip constant. -/
private def firstStripJetDirections {d : ℕ} (cs : List (Fin d)) :
    Fin cs.length → Vec d :=
  List.rec (motive := fun cs : List (Fin d) => Fin cs.length → Vec d)
    Fin.elim0 (fun k _ ih => Fin.cons (unitVector k) ih) cs

private theorem firstStrip_coordinateIterate_eq {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (cs : List (Fin d)) (x : Vec d) :
    coordinateIterate cs f x =
      iteratedFDeriv ℝ cs.length f x (firstStripJetDirections cs) := by
  induction cs generalizing x with
  | nil => simp [coordinateIterate, iteratedFDeriv_zero_apply]
  | cons k cs ih =>
    have he : coordinateIterate cs f = fun y =>
        iteratedFDeriv ℝ cs.length f y (firstStripJetDirections cs) := funext ih
    simp only [coordinateIterate, List.length_cons, firstStripJetDirections,
      iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]
    rw [he]
    exact fderiv_continuousMultilinear_apply_const_apply
      (hf.differentiable_iteratedFDeriv (m := cs.length) (by
        exact WithTop.coe_lt_coe.mpr (ENat.coe_lt_top _)) x) _ _

private theorem firstStrip_jetDirections_norm {d : ℕ} (cs : List (Fin d))
    (k : Fin cs.length) : euclideanNorm (firstStripJetDirections cs k) = 1 := by
  have hu (j : Fin d) : euclideanNorm (unitVector j) = 1 := by
    change Real.sqrt (dotProduct (Pi.single j (1 : ℝ)) (Pi.single j 1)) = 1
    rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]
  induction cs with
  | nil => exact Fin.elim0 k
  | cons j cs ih => exact Fin.cases (hu j) (fun l => ih l) k

private theorem firstStrip_initial_jet_bounds {d : ℕ} (D : StructuralData d) :
    ∃ M : ℕ → ℝ, (∀ n, 1 ≤ n → 0 < M n) ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
      ∀ (cs : List (Fin d)), 1 ≤ cs.length → ∀ x : Vec d,
        (∀ j k : Fin d,
          |coordinateIterate cs (fun y => ω.1 y j k) x| ≤ M cs.length) ∧
        |coordinateIterate cs (fun y => ω.2 y) x| ≤ M cs.length := by
  obtain ⟨M, hMpos, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  refine ⟨M, hMpos, ?_⟩
  intro Q hQ
  filter_upwards [hM Q hQ] with ω hω
  intro cs hcs x
  obtain ⟨A, B, hApos, hBpos, hAB, hA, hB⟩ := hω.2 cs.length hcs
  constructor
  · intro j k
    rw [firstStrip_coordinateIterate_eq (hω.1.1 j k)]
    have hu : euclideanNorm (unitVector k) = 1 := by
      change Real.sqrt (dotProduct (Pi.single k (1 : ℝ)) (Pi.single k 1)) = 1
      rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]
    have hc := Regeneration.coordinate_abs_le_euclideanNorm
      (Matrix.mulVec (fun j k => iteratedFDeriv ℝ cs.length
        (fun y => ω.1 y j k) x (firstStripJetDirections cs)) (unitVector k)) j
    have hb := hA x (firstStripJetDirections cs) (unitVector k)
    have he (N : Mat d) : (N.mulVec (unitVector k)) j = N j k := by
      change dotProduct (fun l => N j l) (Pi.single k 1) = _
      rw [dotProduct_single, mul_one]
    erw [he] at hc
    simp only [firstStrip_jetDirections_norm, Finset.prod_const_one, hu, mul_one] at hb
    exact (hc.trans hb).trans (by linarith)
  · rw [firstStrip_coordinateIterate_eq hω.1.2]
    have hb := hB x (firstStripJetDirections cs)
    simp only [firstStrip_jetDirections_norm, Finset.prod_const_one, mul_one] at hb
    exact hb.trans (by linarith)

private theorem firstStrip_sum_ae {d : ℕ} (μ : Measure (FieldPair d))
    (s : Finset (Fin d)) (f : Fin d → Lp ℂ 2 μ) :
    (∑ j ∈ s, f j : Lp ℂ 2 μ) =ᵐ[μ] fun ω => ∑ j ∈ s, f j ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using! Lp.coeFn_zero ℂ 2 μ
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (f j) (∑ k ∈ s, f k), ih] with ω h1 h2
    simpa only [Pi.add_apply, h2] using! h1

private theorem firstStrip_initial_drift_bound {d : ℕ} (D : StructuralData d) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → ∀ k : Fin d,
      ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (β k) G ∧
        (∀ᵐ ω ∂reducedLaw Q, ‖β k ω‖ ≤ B ∧ ∀ l, ‖G l ω‖ ≤ B) := by
  classical
  obtain ⟨M, hMpos, hM⟩ := firstStrip_initial_jet_bounds D
  let B : ℝ := (d : ℝ) * (M 1 + M 2)
  have h1 : 0 ≤ M 1 := (hMpos 1 (by omega)).le
  have h2 : 0 ≤ M 2 := (hMpos 2 (by omega)).le
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro Q hQ β hβ k
  let J (j : Fin d) (cs : List (Fin d)) : Lp ℂ 2 (reducedLaw Q) :=
    Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
      ((timeFlux_coefficient_jets hQ j k cs).choose.toLp _)
  have hJ (j : Fin d) (cs : List (Fin d)) : J j cs =ᵐ[reducedLaw Q]
      fun ω => (iteratedHorizontalDerivative cs (fun η : FieldPair d => η.1 0 j k) ω : ℂ) := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL
      ((timeFlux_coefficient_jets hQ j k cs).choose.toLp _),
      (timeFlux_coefficient_jets hQ j k cs).choose.coeFn_toLp] with ω hA hB
    exact hA.trans (congrArg Complex.ofReal hB)
  have hder (j l : Fin d) :
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
        (J j [j]) (J j [l, j]) :=
    hasComplexHorizontalDerivative_ofReal
      ((timeFlux_coefficient_jets hQ j k [j]).choose_spec l).choose_spec
  have hsum (l : Fin d) (s : Finset (Fin d)) :
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
        (∑ j ∈ s, J j [j]) (∑ j ∈ s, J j [l, j]) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using!
        HasComplexHorizontalDerivative.zero (reducedLaw Q) (reducedLaw_stationary Q) l
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (hder j l).add ih
  have he : β k = (1 / 2 : ℂ) • ∑ j, J j [j] := by
    apply Lp.ext
    filter_upwards [hβ k, Lp.coeFn_smul (1 / 2 : ℂ) (∑ j, J j [j]),
      firstStrip_sum_ae (reducedLaw Q) Finset.univ (fun j => J j [j]),
      ae_all_iff.mpr (fun j => hJ j [j])] with ω hb hs hsum hj
    rw [hb, hs, Pi.smul_apply, hsum]
    simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hj j]
    congr 1
    change coordinateDerivative j (fun x => ω.1 x j k) 0 =
      coordinateDerivative j (orbit (fun η : FieldPair d => η.1 0 j k) ω) 0
    congr 1
    funext x
    simp only [orbit, translate_matrix, add_zero]
  let G : Fin d → Lp ℂ 2 (reducedLaw Q) :=
    fun l => (1 / 2 : ℂ) • ∑ j, J j [l, j]
  refine ⟨G, ?_, ?_⟩
  · rw [he]
    exact fun l => (hsum l Finset.univ).smul (1 / 2 : ℂ)
  · have hjbound (cs : List (Fin d)) (hcs : 1 ≤ cs.length) (j : Fin d) :
        ∀ᵐ ω ∂reducedLaw Q, ‖J j cs ω‖ ≤ M cs.length := by
      filter_upwards [hJ j cs, hM Q hQ] with ω hj hω
      rw [hj, Complex.norm_real, Real.norm_eq_abs]
      have he := congrFun (orbit_iteratedHorizontalDerivative cs
        (fun η : FieldPair d => η.1 0 j k) ω) 0
      simp only [orbit, translate_zero] at he
      rw [he]
      have ho : orbit (fun η : FieldPair d => η.1 0 j k) ω = fun x => ω.1 x j k := by
        funext x
        simp only [orbit, translate_matrix, add_zero]
      rw [ho]
      exact (hω cs hcs 0).1 j k
    have hbound (cs : Fin d → List (Fin d)) (n : ℕ)
        (hlen : ∀ j, (cs j).length = n) (hn : 1 ≤ n) :
        ∀ᵐ ω ∂reducedLaw Q, ‖((1 / 2 : ℂ) • ∑ j, J j (cs j)) ω‖ ≤
          (1 / 2 : ℝ) * (d * M n) := by
      filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (∑ j, J j (cs j)),
        firstStrip_sum_ae (reducedLaw Q) Finset.univ (fun j => J j (cs j)),
        ae_all_iff.mpr (fun j => hjbound (cs j) (by rw [hlen]; exact hn) j)]
        with ω hs hsum hj
      rw [hs, Pi.smul_apply, smul_eq_mul, norm_mul, hsum]
      norm_num only [norm_div, norm_one, Complex.norm_ofNat]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      calc
        ‖∑ j, J j (cs j) ω‖ ≤ ∑ j, ‖J j (cs j) ω‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin d, M n := Finset.sum_le_sum fun j _ => by simpa [hlen j] using hj j
        _ = d * M n := by simp
    filter_upwards [hbound (fun j => [j]) 1 (by simp) (by omega),
      ae_all_iff.mpr (fun l => hbound (fun j => [l, j]) 2 (by simp) (by omega))]
      with ω hb hg
    rw [he]
    constructor
    · exact hb.trans (by dsimp [B]; nlinarith [Nat.cast_nonneg (α := ℝ) d])
    · intro l
      exact (hg l).trans (by dsimp [B]; nlinarith [Nat.cast_nonneg (α := ℝ) d])

private theorem firstStrip_initial_drift_euclidean_bound {d : ℕ} (D : StructuralData d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → ∀ k : Fin d,
      ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (β k) G ∧
        (∀ᵐ ω ∂reducedLaw Q,
          ‖β k ω‖ + Real.sqrt (∑ l : Fin d, ‖G l ω‖ ^ 2) ≤ C) := by
  obtain ⟨B, hB, hinit⟩ := firstStrip_initial_drift_bound D
  refine ⟨B + Real.sqrt (d : ℝ) * B, by positivity, ?_⟩
  intro Q hQ β hβ k
  obtain ⟨G, hG, hb⟩ := hinit Q hQ β hβ k
  refine ⟨G, hG, ?_⟩
  filter_upwards [hb] with ω hω
  have hs : (∑ l : Fin d, ‖G l ω‖ ^ 2) ≤ (d : ℝ) * B ^ 2 := by
    calc
      (∑ l : Fin d, ‖G l ω‖ ^ 2) ≤ ∑ _l : Fin d, B ^ 2 :=
        Finset.sum_le_sum fun l _ => (sq_le_sq₀ (norm_nonneg _) hB).mpr (hω.2 l)
      _ = (d : ℝ) * B ^ 2 := by simp
  have hg : Real.sqrt (∑ l : Fin d, ‖G l ω‖ ^ 2) ≤ Real.sqrt (d : ℝ) * B := by
    calc
      _ ≤ Real.sqrt ((d : ℝ) * B ^ 2) := Real.sqrt_le_sqrt hs
      _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hB]
  exact add_le_add hω.1 hg

private theorem firstStrip_initial_coefficient_clock_bound {d : ℕ} (D : StructuralData d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
      (∀ j k, ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (a j k) G ∧
        (∀ᵐ ω ∂reducedLaw Q,
          ‖a j k ω‖ + Real.sqrt (∑ l : Fin d, ‖G l ω‖ ^ 2) ≤ C)) ∧
      (∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) μ G ∧
        (∀ᵐ ω ∂reducedLaw Q,
          ‖μ ω‖ + Real.sqrt (∑ l : Fin d, ‖G l ω‖ ^ 2) ≤ C)) := by
  classical
  obtain ⟨M, hMpos, hM⟩ := firstStrip_initial_jet_bounds D
  obtain ⟨K, A, B, hK, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have h1 : 0 ≤ M 1 := (hMpos 1 (by omega)).le
  refine ⟨K + Real.sqrt (d : ℝ) * M 1, by positivity, ?_⟩
  intro Q hQ a μ ha hμ
  have hbuild (F : FieldPair d → ℝ) (f : Lp ℂ 2 (reducedLaw Q))
      (hfobs : f =ᵐ[reducedLaw Q] fun ω => (F ω : ℂ))
      (hj : ∃ hf : MemLp F 2 (reducedLaw Q),
        ∀ l, ∃ hg : MemLp (horizontalDerivative l F) 2 (reducedLaw Q),
          HasHorizontalLpDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
            (hf.toLp F) (hg.toLp _))
      (hfbound : ∀ᵐ ω ∂reducedLaw Q, |F ω| ≤ K)
      (hgbound : ∀ l, ∀ᵐ ω ∂reducedLaw Q, |horizontalDerivative l F ω| ≤ M 1) :
      ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G ∧
        (∀ᵐ ω ∂reducedLaw Q,
          ‖f ω‖ + Real.sqrt (∑ l : Fin d, ‖G l ω‖ ^ 2) ≤
            K + Real.sqrt (d : ℝ) * M 1) := by
    obtain ⟨hf, hnext⟩ := hj
    choose hg hd using hnext
    let G : Fin d → Lp ℂ 2 (reducedLaw Q) := fun l =>
      Complex.ofRealCLM.compLpL 2 (reducedLaw Q) ((hg l).toLp _)
    have he : f = Complex.ofRealCLM.compLpL 2 (reducedLaw Q) (hf.toLp F) := by
      apply Lp.ext
      filter_upwards [hfobs, Complex.ofRealCLM.coeFn_compLpL (hf.toLp F),
        hf.coeFn_toLp] with ω hobs hc hr
      exact hobs.trans (hc.trans (congrArg Complex.ofReal hr)).symm
    have hrep (l : Fin d) : G l =ᵐ[reducedLaw Q]
        fun ω => (horizontalDerivative l F ω : ℂ) := by
      filter_upwards [Complex.ofRealCLM.coeFn_compLpL ((hg l).toLp _),
        (hg l).coeFn_toLp] with ω hc hr
      exact hc.trans (congrArg Complex.ofReal hr)
    refine ⟨G, ?_, ?_⟩
    · rw [he]
      exact fun l => hasComplexHorizontalDerivative_ofReal (hd l)
    · filter_upwards [hfobs, hfbound, ae_all_iff.mpr hrep,
        ae_all_iff.mpr hgbound] with ω hobs hf hrep hg
      have hgb (l : Fin d) : ‖G l ω‖ ≤ M 1 := by
        simpa only [hrep l, Complex.norm_real, Real.norm_eq_abs] using hg l
      have hs : (∑ l : Fin d, ‖G l ω‖ ^ 2) ≤ (d : ℝ) * M 1 ^ 2 := by
        calc
          _ ≤ ∑ _l : Fin d, M 1 ^ 2 := Finset.sum_le_sum fun l _ =>
            (sq_le_sq₀ (norm_nonneg _) h1).mpr (hgb l)
          _ = _ := by simp
      have hgrad := Real.sqrt_le_sqrt hs
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq h1] at hgrad
      have hscalar : ‖f ω‖ ≤ K := by
        simpa only [hobs, Complex.norm_real, Real.norm_eq_abs] using hf
      exact add_le_add hscalar hgrad
  constructor
  · intro j k
    apply hbuild (fun ω => ω.1 0 j k) (a j k) (ha j k)
    · simpa only [iteratedHorizontalDerivative] using timeFlux_coefficient_jets hQ j k []
    · filter_upwards [(hb d D.dependenceRange Q).2.2] with ω he
      apply abs_entry_le_of_quadratic_bounds hK0 (ω.1 0) (he.1 0).1
      · intro ξ
        exact (mul_nonneg (inv_nonneg.mpr hK0) (euclideanSq_nonneg_coords ξ)).trans
          (((he.1 0).2 ξ).1)
      · exact fun ξ => ((he.1 0).2 ξ).2
    · intro l
      filter_upwards [hM Q hQ] with ω hω
      have ho : orbit (fun η : FieldPair d => η.1 0 j k) ω = fun x => ω.1 x j k := by
        funext x
        simp only [orbit, translate_matrix, add_zero]
      simpa only [horizontalDerivative, ho, coordinateIterate, List.length_cons,
        List.length_nil, zero_add] using
        (hω [l] (by simp) 0).1 j k
  · apply hbuild (fun ω => ω.2 0) μ hμ
    · simpa only [iteratedHorizontalDerivative] using centeredClock_jets hQ []
    · filter_upwards [(hb d D.dependenceRange Q).2.2] with ω he
      have hpos : 0 < ω.2 0 := lt_of_lt_of_le
        (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hK)) (he.2.1 0).1
      rw [abs_of_pos hpos]
      exact (he.2.1 0).2
    · intro l
      filter_upwards [hM Q hQ] with ω hω
      have ho : orbit (fun η : FieldPair d => η.2 0) ω = fun x => ω.2 x := by
        funext x
        simp only [orbit, translate_scalar, add_zero]
      simpa only [horizontalDerivative, ho, coordinateIterate, List.length_cons,
        List.length_nil, zero_add] using
        (hω [l] (by simp) 0).2

private theorem firstStrip_initial_linear_bound {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (f g : Lp ℂ 2 (reducedLaw Q))
    (F G : Fin d → Lp ℂ 2 (reducedLaw Q)) (ζ : ℂ) (A B : ℝ)
    (hF : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f F)
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) g G)
    (hf : ∀ᵐ ω ∂reducedLaw Q,
      ‖f ω‖ + Real.sqrt (∑ l : Fin d, ‖F l ω‖ ^ 2) ≤ A)
    (hg : ∀ᵐ ω ∂reducedLaw Q,
      ‖g ω‖ + Real.sqrt (∑ l : Fin d, ‖G l ω‖ ^ 2) ≤ B) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (f + ζ • g) (fun l => F l + ζ • G l) ∧
    (∀ᵐ ω ∂reducedLaw Q,
      ‖(f + ζ • g) ω‖ + Real.sqrt (∑ l : Fin d, ‖(F l + ζ • G l) ω‖ ^ 2) ≤
        A + ‖ζ‖ * B) := by
  constructor
  · exact fun l => (hF l).add ((hG l).smul ζ)
  · filter_upwards [hf, hg, Lp.coeFn_add f (ζ • g), Lp.coeFn_smul ζ g,
      ae_all_iff.mpr (fun l => Lp.coeFn_add (F l) (ζ • G l)),
      ae_all_iff.mpr (fun l => Lp.coeFn_smul ζ (G l))] with ω hf hg ha hs hGa hGs
    have hn : ‖(f + ζ • g) ω‖ ≤ ‖f ω‖ + ‖ζ‖ * ‖g ω‖ := by
      rw [ha, Pi.add_apply, hs, Pi.smul_apply]
      exact (norm_add_le _ _).trans_eq (by rw [norm_smul])
    have he : Real.sqrt (∑ l : Fin d, ‖(F l + ζ • G l) ω‖ ^ 2) ≤
        Real.sqrt (∑ l : Fin d, ‖F l ω‖ ^ 2) +
          ‖ζ‖ * Real.sqrt (∑ l : Fin d, ‖G l ω‖ ^ 2) := by
      have ht := norm_add_le
        (WithLp.toLp 2 (fun l => F l ω) : EuclideanSpace ℂ (Fin d))
        (ζ • (WithLp.toLp 2 (fun l => G l ω) : EuclideanSpace ℂ (Fin d)))
      rw [norm_smul] at ht
      simpa only [EuclideanSpace.norm_eq, PiLp.add_apply, PiLp.smul_apply,
        PiLp.toLp_apply, hGa, hGs, Pi.add_apply, Pi.smul_apply] using ht
    calc
      _ ≤ (‖f ω‖ + ‖ζ‖ * ‖g ω‖) +
          (Real.sqrt (∑ l : Fin d, ‖F l ω‖ ^ 2) +
            ‖ζ‖ * Real.sqrt (∑ l : Fin d, ‖G l ω‖ ^ 2)) := add_le_add hn he
      _ = (‖f ω‖ + Real.sqrt (∑ l : Fin d, ‖F l ω‖ ^ 2)) +
          ‖ζ‖ * (‖g ω‖ + Real.sqrt (∑ l : Fin d, ‖G l ω‖ ^ 2)) := by ring
      _ ≤ A + ‖ζ‖ * B := add_le_add hf (mul_le_mul_of_nonneg_left hg (norm_nonneg _))

/- Initialization of the actual endpoint, with the same quantifier order as
its finite-time estimate. No point-kernel premise is needed at time zero. -/
private theorem firstStrip_initial_endpoint_bound {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ 4 →
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0) G ∧
        (∀ᵐ ω ∂reducedLaw Q,
          ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0 ω‖ +
            Real.sqrt (∑ l : Fin d, ‖G l ω‖ ^ 2) ≤ C) := by
  obtain ⟨B, hB, hβbound⟩ := firstStrip_initial_drift_euclidean_bound D
  obtain ⟨A, hA, habound⟩ := firstStrip_initial_coefficient_clock_bound D
  refine ⟨B + 4 * A, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν
  obtain ⟨hcoef, Gμ, hGμ, hbμ⟩ := habound Q hQ a μ ha hμ
  cases ν with
  | inl k =>
    obtain ⟨Gβ, hGβ, hbβ⟩ := hβbound Q hQ β hβ k
    obtain ⟨Ga, hGa, hba⟩ := hcoef ⟨0, by omega⟩ k
    obtain ⟨hgrad, hbound⟩ := firstStrip_initial_linear_bound Q (β k)
      (a ⟨0, by omega⟩ k) Gβ Ga ζ B A hGβ hGa hbβ hba
    refine ⟨fun l => Gβ l + ζ • Ga l, ?_, ?_⟩
    · simpa only [uncenteredEndpoint, hP.1, ContinuousLinearMap.id_apply] using hgrad
    · simpa only [uncenteredEndpoint, hP.1, ContinuousLinearMap.id_apply] using
        hbound.mono (fun _ h => h.trans (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hζ hA)))
  | inr flag =>
    cases flag with
    | false =>
      have hz : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (0 : Lp ℂ 2 (reducedLaw Q)) (fun _ => 0) := fun l =>
        HasComplexHorizontalDerivative.zero (reducedLaw Q) (reducedLaw_stationary Q) l
      have hbz : ∀ᵐ ω ∂reducedLaw Q,
          ‖(0 : Lp ℂ 2 (reducedLaw Q)) ω‖ +
            Real.sqrt (∑ _l : Fin d, ‖(0 : Lp ℂ 2 (reducedLaw Q)) ω‖ ^ 2) ≤ 0 := by
        filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω he
        simp only [he, Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, Finset.sum_const_zero, Real.sqrt_zero, add_zero, le_refl]
      obtain ⟨hgrad, hbound⟩ := firstStrip_initial_linear_bound Q 0 μ (fun _ => 0)
        Gμ ζ 0 A hz hGμ hbz hbμ
      refine ⟨fun l => ζ • Gμ l, ?_, ?_⟩
      · simpa only [uncenteredEndpoint, hP.1, ContinuousLinearMap.id_apply, zero_add] using hgrad
      · simpa only [uncenteredEndpoint, hP.1, ContinuousLinearMap.id_apply, zero_add] using
          hbound.mono (fun _ h => h.trans (by nlinarith [mul_le_mul_of_nonneg_right hζ hA]))
    | true =>
      obtain ⟨Gβ, hGβ, hbβ⟩ := hβbound Q hQ β hβ ⟨0, by omega⟩
      refine ⟨Gβ, ?_, ?_⟩
      · simpa only [uncenteredEndpoint, transposeEndpoint, hPdag.zero hP,
          ContinuousLinearMap.id_apply] using hGβ
      · simpa only [uncenteredEndpoint, transposeEndpoint, hPdag.zero hP,
          ContinuousLinearMap.id_apply] using hbβ.mono (fun _ h => h.trans (by linarith))

/- Quantitative coefficient commutators for stationary spatial smoothing. -/
private theorem firstStrip_translation_coefficient_commutator {d : ℕ}
    (D : StructuralData d) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (j k : Fin d) (x : Vec d) (f : Lp ℂ 2 (reducedLaw Q)),
      ‖complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
          (complexCoefficientMul Q j k f) -
        complexCoefficientMul Q j k
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)‖ ≤
        A * euclideanNorm x * ‖f‖ := by
  obtain ⟨K, A, B, _, hA, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  refine ⟨A, hA, ?_⟩
  intro Q j k x f
  let T := complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
  have hm := measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x
  have ht := hm.quasiMeasurePreserving.ae (complexCoefficientMul_coe Q j k f)
  have hp : ∀ᵐ ω ∂reducedLaw Q,
      ‖(T (complexCoefficientMul Q j k f) - complexCoefficientMul Q j k (T f)) ω‖ ≤
        (A * euclideanNorm x) * ‖T f ω‖ := by
    filter_upwards [Lp.coeFn_sub (T (complexCoefficientMul Q j k f))
        (complexCoefficientMul Q j k (T f)),
      coeFn_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (complexCoefficientMul Q j k f),
      complexCoefficientMul_coe Q j k (T f), ht,
      coeFn_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f,
      (hb d D.dependenceRange Q).2.2] with ω hs hT hM hc hf hω
    have ha := hω.2.2.1.entry_bound j k x 0
    simp only [sub_zero] at ha
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hT, hM, hc]
    simp only [translate_matrix, add_zero]
    change ‖(ω.1 x j k : ℂ) * f (translate x ω) -
      (ω.1 0 j k : ℂ) * T f ω‖ ≤ _
    rw [hf, ← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ha (norm_nonneg _)
  have hn := Lp.norm_le_mul_norm_of_ae_le_mul hp
  simpa only [T, norm_complexTranslation, mul_assoc] using hn

private theorem firstStrip_average_coefficient_commutator {d : ℕ}
    (D : StructuralData d) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (j k : Fin d) (κ : Vec d → ℂ), Integrable κ → Continuous κ →
      Integrable (fun x => ‖κ x‖ * euclideanNorm x) →
      ∀ f : Lp ℂ 2 (reducedLaw Q),
      ‖(∫ x, κ x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
          (complexCoefficientMul Q j k f)) -
        complexCoefficientMul Q j k
          (∫ x, κ x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)‖ ≤
        A * (∫ x, ‖κ x‖ * euclideanNorm x) * ‖f‖ := by
  obtain ⟨A, hA, hcomm⟩ := firstStrip_translation_coefficient_commutator D
  refine ⟨A, hA, ?_⟩
  intro Q j k κ hκ hc hmoment f
  letI := reducedLaw_probability Q
  let T := fun x => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
  let M := complexCoefficientMul Q j k
  have hk (g : Lp ℂ 2 (reducedLaw Q)) : Integrable (fun x => κ x • T x g) := by
    have ht : Continuous (fun x : Vec d => T x g) :=
      (continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
        (continuous_id.prodMk continuous_const)
    apply (hκ.norm.mul_const ‖g‖).mono' (hc.fun_smul ht).aestronglyMeasurable
    filter_upwards [] with x
    rw [norm_smul, norm_complexTranslation]
  have h1 := hk (M f)
  have h2 := hk f
  have h3 := M.integrable_comp h2
  rw [← M.integral_comp_comm h2, ← integral_sub h1 h3]
  have hi : Integrable (fun x => A * (‖κ x‖ * euclideanNorm x) * ‖f‖) :=
    (hmoment.const_mul A).mul_const ‖f‖
  calc
    _ ≤ ∫ x, ‖κ x • T x (M f) - M (κ x • T x f)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, A * (‖κ x‖ * euclideanNorm x) * ‖f‖ := by
      apply integral_mono_ae (h1.sub h3).norm hi
      filter_upwards [] with x
      simp only [Pi.sub_apply]
      rw [map_smul, ← smul_sub, norm_smul]
      have hx := mul_le_mul_of_nonneg_left (hcomm Q j k x f) (norm_nonneg (κ x))
      simpa only [T, M, mul_assoc, mul_left_comm, mul_comm] using hx
    _ = A * (∫ x, ‖κ x‖ * euclideanNorm x) * ‖f‖ := by
      rw [integral_mul_const, integral_const_mul]

private theorem firstStrip_average_coefficient_commutator_tendsto {d : ℕ}
    (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (j k : Fin d) (κ : ℕ → Vec d → ℂ)
    (hκ : ∀ n, Integrable (κ n)) (hc : ∀ n, Continuous (κ n))
    (hmoment : ∀ n, Integrable (fun x => ‖κ n x‖ * euclideanNorm x))
    (hsmall : Tendsto (fun n => ∫ x, ‖κ n x‖ * euclideanNorm x) atTop (𝓝 0))
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun n =>
      (∫ x, κ n x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
          (complexCoefficientMul Q j k f)) -
        complexCoefficientMul Q j k
          (∫ x, κ n x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f))
      atTop (𝓝 0) := by
  obtain ⟨A, _, hcomm⟩ := firstStrip_average_coefficient_commutator D
  apply squeeze_zero_norm (fun n => hcomm Q j k (κ n) (hκ n) (hc n) (hmoment n) f)
  simpa only [mul_zero, zero_mul] using (hsmall.const_mul A).mul_const ‖f‖

/- Actual derivative multipliers and the differentiated smoothing remainder. -/
private theorem firstStrip_coefficient_derivative_multiplier {d : ℕ}
    (D : StructuralData d) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (j k l : Fin d),
      ∃ M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
        ‖M‖ ≤ B ∧ ∀ f : Lp ℂ 2 (reducedLaw Q),
          M f =ᵐ[reducedLaw Q] fun ω =>
            (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * f ω := by
  obtain ⟨B, hB, hb⟩ := firstStrip_initial_jet_bounds D
  refine ⟨B 1, (hB 1 (by omega)).le, ?_⟩
  intro Q hQ j k l
  let J : FieldPair d → ℂ := fun ω =>
    (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ)
  have he : iteratedHorizontalDerivative [l] (fun ω : FieldPair d => ω.1 0 j k) =
      fun ω => coordinateDerivative l (fun y => ω.1 y j k) 0 := by
    funext ω
    change coordinateDerivative l (orbit (fun η : FieldPair d => η.1 0 j k) ω) 0 = _
    congr 1
    funext x
    simp only [orbit, translate_matrix, add_zero]
  have hr : MemLp (fun ω : FieldPair d => coordinateDerivative l (fun y => ω.1 y j k) 0)
      2 (reducedLaw Q) := by
    simpa only [he] using (timeFlux_coefficient_jets hQ j k [l]).choose
  have hj : ∀ᵐ ω ∂reducedLaw Q, ‖J ω‖ ≤ B 1 := by
    filter_upwards [hb Q hQ] with ω hω
    simpa only [J, Complex.norm_real, Real.norm_eq_abs, coordinateIterate,
      List.length_cons, List.length_nil, zero_add] using (hω [l] (by simp) 0).1 j k
  have hJ : MemLp J ∞ (reducedLaw Q) :=
    memLp_top_of_bound (Complex.continuous_ofReal.comp_aestronglyMeasurable
      hr.aestronglyMeasurable) (B 1) hj
  let M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
    (ContinuousLinearMap.mul ℂ ℂ).holderL (reducedLaw Q) ∞ 2 2 (hJ.toLp J)
  have hm (f : Lp ℂ 2 (reducedLaw Q)) :
      M f =ᵐ[reducedLaw Q] fun ω => J ω * f ω := by
    have hp := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hJ.toLp J) f
    filter_upwards [hJ.coeFn_toLp, hp] with ω h1 h2
    simpa only [M, ContinuousLinearMap.holderL_apply_apply,
      ContinuousLinearMap.mul_apply', h1] using h2
  refine ⟨M, ?_, hm⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (hB 1 (by omega)).le
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hm f, hj] with ω hmf hbound
  rw [hmf, norm_mul]
  exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

private theorem firstStrip_friedrichs_remainder_bound {d : ℕ}
    (D : StructuralData d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (j k l : Fin d),
      ∃ M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
        (∀ f : Lp ℂ 2 (reducedLaw Q), M f =ᵐ[reducedLaw Q] fun ω =>
          (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * f ω) ∧
        ∀ (κ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) κ → HasCompactSupport κ →
        ∀ f : Lp ℂ 2 (reducedLaw Q),
          ‖((∫ x, (coordinateDerivative l κ x : ℂ) •
              complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
                (complexCoefficientMul Q j k f)) -
            complexCoefficientMul Q j k
              (∫ x, (coordinateDerivative l κ x : ℂ) •
                complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) +
            (∫ x, (κ x : ℂ) •
              complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (M f))‖ ≤
            C * ((∫ x, |coordinateDerivative l κ x| * euclideanNorm x) +
              ∫ x, |κ x|) * ‖f‖ := by
  obtain ⟨A, hA, hcomm⟩ := firstStrip_average_coefficient_commutator D
  obtain ⟨B, hB, hmul⟩ := firstStrip_coefficient_derivative_multiplier D
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro Q hQ j k l
  obtain ⟨M, hM, hrep⟩ := hmul Q hQ j k l
  refine ⟨M, hrep, ?_⟩
  intro κ hκ hκc f
  have hD : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative l κ) :=
    (hκ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDc := hκc.fderiv_apply ℝ (unitVector l)
  have heuc : Continuous (fun x : Vec d => euclideanNorm x) := by
    change Continuous (fun x : Vec d => Real.sqrt (∑ k : Fin d, x k * x k))
    exact Real.continuous_sqrt.comp
      (continuous_finset_sum _ fun k _ => (continuous_apply k).mul (continuous_apply k))
  have hmoment : Integrable (fun x => |coordinateDerivative l κ x| * euclideanNorm x) :=
    (hD.continuous.abs.mul heuc).integrable_of_hasCompactSupport hDc.abs.mul_right
  have hderiv : Integrable (fun x => (coordinateDerivative l κ x : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (hD.continuous.integrable_of_hasCompactSupport hDc)
  have hcx := Complex.continuous_ofReal.comp hD.continuous
  have hmoment' : Integrable (fun x => ‖(coordinateDerivative l κ x : ℂ)‖ *
      euclideanNorm x) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hmoment
  have hprincipal := hcomm Q j k (fun x => (coordinateDerivative l κ x : ℂ))
    hderiv hcx hmoment' f
  simp only [Complex.norm_real, Real.norm_eq_abs] at hprincipal
  have hzero : ‖∫ x, (κ x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (M f)‖ ≤
      B * (∫ x, |κ x|) * ‖f‖ := by
    calc
      _ ≤ ∫ x, ‖(κ x : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (M f)‖ :=
        norm_integral_le_integral_norm _
      _ = (∫ x, |κ x|) * ‖M f‖ := by
        simp only [norm_smul, norm_complexTranslation, Complex.norm_real,
          Real.norm_eq_abs, integral_mul_const]
      _ ≤ (∫ x, |κ x|) * (B * ‖f‖) :=
        mul_le_mul_of_nonneg_left ((M.le_opNorm f).trans
          (mul_le_mul_of_nonneg_right hM (norm_nonneg _)))
          (integral_nonneg fun x => abs_nonneg (κ x))
      _ = _ := by ring
  have hm0 : 0 ≤ ∫ x, |coordinateDerivative l κ x| * euclideanNorm x :=
    integral_nonneg fun x => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hk0 : 0 ≤ ∫ x, |κ x| := integral_nonneg fun x => abs_nonneg _
  calc
    _ ≤ _ + _ := norm_add_le _ _
    _ ≤ A * (∫ x, |coordinateDerivative l κ x| * euclideanNorm x) * ‖f‖ +
        B * (∫ x, |κ x|) * ‖f‖ := add_le_add hprincipal hzero
    _ ≤ (A + B) * (∫ x, |coordinateDerivative l κ x| * euclideanNorm x) * ‖f‖ +
        (A + B) * (∫ x, |κ x|) * ‖f‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) hm0) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) hk0) (norm_nonneg _)
    _ = _ := by ring

private theorem firstStrip_friedrichs_remainder_identity {d : ℕ}
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ j k l : Fin d,
      ∀ κ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) κ → HasCompactSupport κ →
        (∫ x, f (translate x ω) *
          ((ω.1 x j k - ω.1 0 j k) * coordinateDerivative l κ x : ℝ)) +
        (∫ x, f (translate x ω) *
          (coordinateDerivative l (fun y => ω.1 y j k) x * κ x : ℝ)) =
        ∫ x, G l (translate x ω) * ((ω.1 0 j k - ω.1 x j k) * κ x : ℝ) := by
  obtain ⟨M, _, hs⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  have hloc : ∀ᵐ ω ∂reducedLaw Q,
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => f (translate x ω)) 2 (volume.restrict K) :=
    ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
  filter_upwards [firstStrip_spatial_gradient Q hG, hs Q hQ, hloc] with ω hw hω hloc
  intro j k l κ hκ hκc
  let A : Vec d → ℝ := fun x => ω.1 x j k - ω.1 0 j k
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := (hω.1.1 j k).sub contDiff_const
  have hD : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative l κ) :=
    (hκ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDA : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative l A) :=
    (hA.fderiv_right (by simp)).clm_apply contDiff_const
  have he (x : Vec d) : coordinateDerivative l A x =
      coordinateDerivative l (fun y => ω.1 y j k) x := by
    dsimp only [A, coordinateDerivative]
    rw [fderiv_sub_const]
  have h1 : Integrable (fun x => f (translate x ω) *
      (A x * coordinateDerivative l κ x : ℝ)) :=
    integrable_spatial_mul_test hloc (hA.continuous.mul hD.continuous)
    ((hκc.fderiv_apply ℝ (unitVector l)).mul_left (f := A))
  have h2 : Integrable (fun x => f (translate x ω) *
      (coordinateDerivative l A x * κ x : ℝ)) :=
    integrable_spatial_mul_test hloc (hDA.continuous.mul hκ.continuous)
    (hκc.mul_left (f := coordinateDerivative l A))
  have hsplit : (∫ x, f (translate x ω) *
      (coordinateDerivative l (fun x => A x * κ x) x : ℂ)) =
      (∫ x, f (translate x ω) * (A x * coordinateDerivative l κ x : ℝ)) +
      (∫ x, f (translate x ω) * (coordinateDerivative l A x * κ x : ℝ)) := by
    rw [← integral_add h1 h2]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [coordinateDerivative_mul l A κ x
      (hA.differentiable (by simp)).differentiableAt
      (hκ.differentiable (by simp)).differentiableAt]
    push_cast
    ring
  have hwκ := hw l (fun x => A x * κ x) (hA.mul hκ) (hκc.mul_left (f := A))
  rw [hsplit] at hwκ
  have hneg : (∫ x, G l (translate x ω) * ((ω.1 0 j k - ω.1 x j k) * κ x : ℝ)) =
      -(∫ x, G l (translate x ω) * (A x * κ x : ℝ)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [A]
    push_cast
    ring
  simp only [he] at hwκ
  rw [hneg, hwκ, neg_neg]

/- Bochner identification of the differentiated remainder on the actual H1 domain. -/
private theorem firstStrip_kernel_integral_coe {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (f : Lp ℂ 2 (reducedLaw Q))
    (κ : Vec d → ℝ) (hκ : Continuous κ) (hκc : HasCompactSupport κ) :
    (∫ x, (κ x : ℂ) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)
      =ᵐ[reducedLaw Q] fun ω => ∫ x, f (translate x ω) * (κ x : ℂ) := by
  letI := reducedLaw_probability Q
  have hu : Integrable (fun x : Vec d => (κ x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) :=
    ((Complex.continuous_ofReal.comp hκ).smul ((continuous_complexTranslation _ _).comp
      (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        (hκc.comp_left rfl).smul_right
  have hm : Measurable (fun p : Vec d × FieldPair d =>
      f (translate p.1 p.2) * (κ p.1 : ℂ)) :=
    ((Lp.stronglyMeasurable f).measurable.comp Probability.continuous_translate.measurable).mul
      (Complex.measurable_ofReal.comp (hκ.measurable.comp measurable_fst))
  apply coeFn_integral_joint_l2_representative hu hm
  intro x
  filter_upwards [coeFn_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f,
    Lp.coeFn_smul (κ x : ℂ)
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)] with ω ht hs
  rw [hs]
  change _ = (κ x : ℂ) * (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) ω
  rw [ht, mul_comm]

private theorem firstStrip_kernel_commutator_coe {d : ℕ}
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (j k : Fin d) (f : Lp ℂ 2 (reducedLaw Q))
    (κ : Vec d → ℝ) (hκ : Continuous κ) (hκc : HasCompactSupport κ) :
    ((∫ x, (κ x : ℂ) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (complexCoefficientMul Q j k f)) -
      complexCoefficientMul Q j k
        (∫ x, (κ x : ℂ) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f))
      =ᵐ[reducedLaw Q] fun ω => ∫ x, f (translate x ω) *
        ((ω.1 x j k - ω.1 0 j k) * κ x : ℝ) := by
  letI := reducedLaw_probability Q
  obtain ⟨M, _, hs⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  have horbit := ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (complexCoefficientMul Q j k f)).measurable
    ((Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable.mul
      (Lp.stronglyMeasurable f).measurable) (complexCoefficientMul_coe Q j k f)
  have hloc := ae_complex_function_orbit_memLp_on_all_compacts
    (reducedLaw Q) (reducedLaw_stationary Q) (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
  filter_upwards [firstStrip_kernel_integral_coe Q (complexCoefficientMul Q j k f) κ hκ hκc,
    firstStrip_kernel_integral_coe Q f κ hκ hκc,
    complexCoefficientMul_coe Q j k
      (∫ x, (κ x : ℂ) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f),
    Lp.coeFn_sub
      (∫ x, (κ x : ℂ) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (complexCoefficientMul Q j k f))
      (complexCoefficientMul Q j k
        (∫ x, (κ x : ℂ) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)),
    horbit, hloc, hs Q hQ] with ω h1 h2 h3 hsub horb hl hω
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [h1, h3, h2, ← integral_const_mul]
  have hfirst : (∫ x, (complexCoefficientMul Q j k f) (translate x ω) * (κ x : ℂ)) =
      ∫ x, f (translate x ω) * (ω.1 x j k * κ x : ℝ) := by
    apply integral_congr_ae
    filter_upwards [horb] with x hx
    rw [hx]
    change ((translate x ω).1 0 j k : ℂ) * f (translate x ω) * (κ x : ℂ) = _
    simp only [translate_matrix, add_zero]
    push_cast
    ring
  have hsecond : (∫ x, (ω.1 0 j k : ℂ) * (f (translate x ω) * (κ x : ℂ))) =
      ∫ x, f (translate x ω) * (ω.1 0 j k * κ x : ℝ) := by
    apply integral_congr_ae
    filter_upwards [] with x
    push_cast
    ring
  have hi1 : Integrable (fun x => f (translate x ω) * (ω.1 x j k * κ x : ℝ)) :=
    integrable_spatial_mul_test hl ((hω.1.1 j k).continuous.mul hκ) hκc.mul_left
  have hi2 : Integrable (fun x => f (translate x ω) * (ω.1 0 j k * κ x : ℝ)) :=
    integrable_spatial_mul_test hl (continuous_const.mul hκ) hκc.mul_left
  rw [hfirst, hsecond, ← integral_sub hi1 hi2]
  apply integral_congr_ae
  filter_upwards [] with x
  push_cast
  ring

private theorem firstStrip_derivative_multiplier_orbit {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j k l : Fin d)
    (M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hM : ∀ f : Lp ℂ 2 (reducedLaw Q), M f =ᵐ[reducedLaw Q] fun ω =>
      (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * f ω)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      M f (translate x ω) =
        (coordinateDerivative l (fun y => ω.1 y j k) x : ℂ) * f (translate x ω) := by
  letI := reducedLaw_probability Q
  have hc : Continuous (fun p : FieldPair d × Vec d => p.1.1 p.2 j k) :=
    (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd)).matrix_elem j k
  have hm : Measurable (fun ω : FieldPair d =>
      (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((measurable_fderiv_apply_const_with_param ℝ
        (f := fun ω : FieldPair d => fun y : Vec d => ω.1 y j k) hc (unitVector l)).comp
        (measurable_id.prodMk (show Measurable (fun _ : FieldPair d => (0 : Vec d)) from
          measurable_const)))
  have horbit := ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (M f)).measurable
    (hm.mul (Lp.stronglyMeasurable f).measurable) (hM f)
  filter_upwards [horbit] with ω hω
  filter_upwards [hω] with x hx
  rw [hx]
  change (coordinateDerivative l (fun y => (translate x ω).1 y j k) 0 : ℂ) *
    f (translate x ω) = _
  simp only [translate_matrix, coordinateDerivative]
  rw [fderiv_comp_add_left (f := fun y : Vec d => ω.1 y j k) x]
  simp only [add_zero]

private theorem firstStrip_friedrichs_remainder_L2_identity {d : ℕ}
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (j k l : Fin d)
    (M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hM : ∀ f : Lp ℂ 2 (reducedLaw Q), M f =ᵐ[reducedLaw Q] fun ω =>
      (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * f ω)
    {f : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (κ : Vec d → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) :
    ((∫ x, (coordinateDerivative l κ x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
          (complexCoefficientMul Q j k f)) -
      complexCoefficientMul Q j k
        (∫ x, (coordinateDerivative l κ x : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) +
      (∫ x, (κ x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (M f)) =
      -((∫ x, (κ x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
          (complexCoefficientMul Q j k (G l))) -
      complexCoefficientMul Q j k
        (∫ x, (κ x : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G l))) := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative l κ) :=
    (hκ.fderiv_right (by simp)).clm_apply contDiff_const
  let P := (∫ x, (coordinateDerivative l κ x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (complexCoefficientMul Q j k f)) -
    complexCoefficientMul Q j k
      (∫ x, (coordinateDerivative l κ x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)
  let Z := ∫ x, (κ x : ℂ) •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (M f)
  let R := (∫ x, (κ x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (complexCoefficientMul Q j k (G l))) -
    complexCoefficientMul Q j k
      (∫ x, (κ x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G l))
  change P + Z = -R
  apply Lp.ext
  filter_upwards [Lp.coeFn_add P Z, Lp.coeFn_neg R,
    firstStrip_kernel_commutator_coe Q hQ j k f (coordinateDerivative l κ)
      hD.continuous (hκc.fderiv_apply ℝ (unitVector l)),
    firstStrip_kernel_integral_coe Q (M f) κ hκ.continuous hκc,
    firstStrip_kernel_commutator_coe Q hQ j k (G l) κ hκ.continuous hκc,
    firstStrip_derivative_multiplier_orbit Q j k l M hM f,
    firstStrip_friedrichs_remainder_identity Q hQ hG] with ω ha hn hp hz hr ho hi
  rw [ha, hn]
  change P ω + Z ω = -(R ω)
  rw [hp, hz, hr]
  have hz' : (∫ x, M f (translate x ω) * (κ x : ℂ)) =
      ∫ x, f (translate x ω) *
        (coordinateDerivative l (fun y => ω.1 y j k) x * κ x : ℝ) := by
    apply integral_congr_ae
    filter_upwards [ho] with x hx
    rw [hx]
    push_cast
    ring
  rw [hz', hi j k l κ hκ hκc, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  push_cast
  ring

private theorem firstStrip_friedrichs_remainder_tendsto_H1 {d : ℕ}
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (j k l : Fin d)
    (M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hM : ∀ f : Lp ℂ 2 (reducedLaw Q), M f =ᵐ[reducedLaw Q] fun ω =>
      (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * f ω)
    (κ : ℕ → Vec d → ℝ) (hκ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (κ n))
    (hκc : ∀ n, HasCompactSupport (κ n))
    (hsmall : Tendsto (fun n => ∫ x, |κ n x| * euclideanNorm x) atTop (𝓝 0))
    {f : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    Tendsto (fun n =>
      ((∫ x, (coordinateDerivative l (κ n) x : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
            (complexCoefficientMul Q j k f)) -
        complexCoefficientMul Q j k
          (∫ x, (coordinateDerivative l (κ n) x : ℂ) •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) +
        (∫ x, (κ n x : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (M f)))
      atTop (𝓝 0) := by
  have heuc : Continuous (fun x : Vec d => euclideanNorm x) := by
    change Continuous (fun x : Vec d => Real.sqrt (∑ k : Fin d, x k * x k))
    exact Real.continuous_sqrt.comp
      (continuous_finset_sum _ fun k _ => (continuous_apply k).mul (continuous_apply k))
  have hi (n : ℕ) : Integrable (fun x => (κ n x : ℂ)) :=
    Complex.ofRealCLM.integrable_comp
      ((hκ n).continuous.integrable_of_hasCompactSupport (hκc n))
  have hc (n : ℕ) : Continuous (fun x => (κ n x : ℂ)) :=
    Complex.continuous_ofReal.comp (hκ n).continuous
  have hm (n : ℕ) : Integrable (fun x => ‖(κ n x : ℂ)‖ * euclideanNorm x) := by
    have hreal : Integrable (fun x => |κ n x| * euclideanNorm x) :=
      ((hκ n).continuous.abs.mul heuc).integrable_of_hasCompactSupport
        (hκc n).abs.mul_right
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hreal
  have hs : Tendsto (fun n => ∫ x, ‖(κ n x : ℂ)‖ * euclideanNorm x) atTop (𝓝 0) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hsmall
  have ht := (firstStrip_average_coefficient_commutator_tendsto D Q j k
    (fun n x => (κ n x : ℂ)) hi hc hm hs (G l)).neg
  simp only [neg_zero] at ht
  apply ht.congr' (Eventually.of_forall fun n => ?_)
  exact (firstStrip_friedrichs_remainder_L2_identity Q hQ j k l M hM hG
    (κ n) (hκ n) (hκc n)).symm

private def firstStripKernelAverage {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (κ : Vec d → ℝ)
    (hκ : Continuous κ) (hκc : HasCompactSupport κ) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) := by
  let T := complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
  have hi (f : Lp ℂ 2 (reducedLaw Q)) : Integrable (fun x : Vec d => (κ x : ℂ) • T x f) :=
    ((Complex.continuous_ofReal.comp hκ).smul ((continuous_complexTranslation _ _).comp
      (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        (hκc.comp_left rfl).smul_right
  let L : Lp ℂ 2 (reducedLaw Q) →ₗ[ℂ] Lp ℂ 2 (reducedLaw Q) :=
    { toFun := fun f => ∫ x, (κ x : ℂ) • T x f
      map_add' := by
        intro f g
        simp only [map_add, smul_add]
        exact integral_add (hi f) (hi g)
      map_smul' := by
        intro c f
        change (∫ x, (κ x : ℂ) • T x (c • f)) = c • ∫ x, (κ x : ℂ) • T x f
        calc
          _ = ∫ x, c • ((κ x : ℂ) • T x f) := by
            apply integral_congr_ae
            filter_upwards [] with x
            rw [map_smul, smul_comm]
          _ = _ := integral_smul c _ }
  exact L.mkContinuous (∫ x, |κ x|) fun f => by
    change ‖∫ x, (κ x : ℂ) • T x f‖ ≤ _
    calc
      _ ≤ ∫ x, ‖(κ x : ℂ) • T x f‖ := norm_integral_le_integral_norm _
      _ = (∫ x, |κ x|) * ‖f‖ := by
        simp only [T, norm_smul, norm_complexTranslation, Complex.norm_real,
          Real.norm_eq_abs, integral_mul_const]

private theorem firstStrip_tendsto_of_dense_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : ℕ → E →L[ℂ] E) (S : Set E) (hS : Dense S)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ n g, ‖R n g‖ ≤ K * ‖g‖)
    (hs : ∀ u ∈ S, Tendsto (fun n => R n u) atTop (𝓝 0)) (f : E) :
    Tendsto (fun n => R n f) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨u, hu, hfu⟩ := hS.exists_dist_lt f
    (by positivity : 0 < ε / (2 * (K + 1)))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hs u hu) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hdist : dist (R n f) (R n u) ≤ K * dist f u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact hb n (f - u)
  have hsmall : K * dist f u < ε / 2 := by
    have hmul := mul_lt_mul_of_pos_left hfu (by positivity : 0 < K + 1)
    have hcancel : (K + 1) * (ε / (2 * (K + 1))) = ε / 2 := by field_simp
    rw [hcancel] at hmul
    have hnonneg : 0 ≤ dist f u := dist_nonneg
    nlinarith
  calc
    dist (R n f) 0 ≤ dist (R n f) (R n u) + dist (R n u) 0 := dist_triangle _ _ _
    _ ≤ K * dist f u + dist (R n u) 0 := add_le_add hdist le_rfl
    _ < ε := by linarith [hN n hn]

private theorem firstStrip_friedrichs_remainder_tendsto {d : ℕ}
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i j k l : Fin d) :
    ∃ M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ f : Lp ℂ 2 (reducedLaw Q), M f =ᵐ[reducedLaw Q] fun ω =>
        (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * f ω) ∧
      ∀ (κ : ℕ → Vec d → ℝ), (∀ n, ContDiff ℝ (⊤ : ℕ∞) (κ n)) →
        (∀ n, HasCompactSupport (κ n)) →
        ∀ K : ℝ, 0 ≤ K →
          (∀ n, (∫ x, |coordinateDerivative l (κ n) x| * euclideanNorm x) +
            ∫ x, |κ n x| ≤ K) →
          Tendsto (fun n => ∫ x, |κ n x| * euclideanNorm x) atTop (𝓝 0) →
          ∀ f : Lp ℂ 2 (reducedLaw Q),
          Tendsto (fun n =>
            ((∫ x, (coordinateDerivative l (κ n) x : ℂ) •
                complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
                  (complexCoefficientMul Q j k f)) -
              complexCoefficientMul Q j k
                (∫ x, (coordinateDerivative l (κ n) x : ℂ) •
                  complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) +
              (∫ x, (κ n x : ℂ) •
                complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (M f)))
            atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := firstStrip_friedrichs_remainder_bound D
  obtain ⟨M, hM, hbound⟩ := hb Q hQ j k l
  refine ⟨M, hM, ?_⟩
  intro κ hκ hc K hK hmoment hsmall f
  let A := complexCoefficientMul Q j k
  let B := fun n => firstStripKernelAverage Q (κ n) (hκ n).continuous (hc n)
  have hD (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative l (κ n)) :=
    ((hκ n).fderiv_right (by simp)).clm_apply contDiff_const
  let H := fun n => firstStripKernelAverage Q (coordinateDerivative l (κ n))
    (hD n).continuous ((hc n).fderiv_apply ℝ (unitVector l))
  let R : ℕ → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
    fun n => (H n).comp A - A.comp (H n) + (B n).comp M
  have he (n : ℕ) (g : Lp ℂ 2 (reducedLaw Q)) : R n g =
      ((∫ x, (coordinateDerivative l (κ n) x : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
            (complexCoefficientMul Q j k g)) -
        complexCoefficientMul Q j k
          (∫ x, (coordinateDerivative l (κ n) x : ℂ) •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g)) +
        (∫ x, (κ n x : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (M g)) := rfl
  have hnorm (n : ℕ) (g : Lp ℂ 2 (reducedLaw Q)) : ‖R n g‖ ≤ (C * K) * ‖g‖ := by
    rw [he]
    exact (hbound (κ n) (hκ n) (hc n) g).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hmoment n) hC) (norm_nonneg _))
  have ht : Tendsto (fun n => R n f) atTop (𝓝 0) := by
    apply firstStrip_tendsto_of_dense_uniform_bound R
      {u | ∃ v, IsComplexGeneratorPair Q i 0 u v}
      (dense_unforced_complexGenerator_domain Q i) (C * K) (mul_nonneg hC hK) hnorm
    intro u hu
    obtain ⟨v, G, hG, _⟩ := hu
    have hu := firstStrip_friedrichs_remainder_tendsto_H1 D Q hQ j k l M hM
      κ hκ hc hsmall hG
    simpa only [he] using hu
  exact ht.congr' (Eventually.of_forall fun n => he n f)

/- The canonical unit-mass kernel, dilated at an explicit rate. Its moments
use the Euclidean norm even though its coordinate carrier has the sup norm. -/
private def firstStripSpatialKernel (d n : ℕ) (x : Vec d) : ℝ :=
  ((n : ℝ) + 1) ^ d * mollifier d (((n : ℝ) + 1) • x)

private theorem firstStripSpatialKernel_smooth (d n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (firstStripSpatialKernel d n) :=
  contDiff_const.mul ((contDiff_mollifier d).comp (contDiff_id.const_smul _))

private theorem firstStripSpatialKernel_compact (d n : ℕ) :
    HasCompactSupport (firstStripSpatialKernel d n) := by
  have hR : (n : ℝ) + 1 ≠ 0 := by positivity
  exact ((hasCompactSupport_mollifier d).comp_homeomorph
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr hR).unit)).mul_left

private theorem firstStripSpatialKernel_nonneg (d n : ℕ) (x : Vec d) :
    0 ≤ firstStripSpatialKernel d n x :=
  mul_nonneg (by positivity) (mollifier_nonneg d _)

private theorem firstStripSpatialKernel_mass (d n : ℕ) :
    (∫ x, firstStripSpatialKernel d n x) = 1 := by
  have hR : 0 < (n : ℝ) + 1 := by positivity
  unfold firstStripSpatialKernel
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume
    (mollifier d) ((n : ℝ) + 1) (hR := hR.le), Module.finrank_fin_fun,
    smul_eq_mul, integral_mollifier, mul_one, mul_inv_cancel₀ (pow_ne_zero d hR.ne')]

private theorem firstStripSpatialKernel_derivative (d n : ℕ) (l : Fin d) (x : Vec d) :
    coordinateDerivative l (firstStripSpatialKernel d n) x =
      ((n : ℝ) + 1) ^ d * ((n : ℝ) + 1) *
        coordinateDerivative l (mollifier d) (((n : ℝ) + 1) • x) := by
  let R : ℝ := (n : ℝ) + 1
  have hm : DifferentiableAt ℝ (mollifier d) (R • x) :=
    (contDiff_mollifier d).differentiable (by simp) _
  have hs : HasFDerivAt (fun y : Vec d => R • y)
      (R • ContinuousLinearMap.id ℝ (Vec d)) x := (hasFDerivAt_id x).const_smul R
  have he := ((hm.hasFDerivAt.comp x hs).const_mul (R ^ d)).fderiv
  change fderiv ℝ (fun y : Vec d => R ^ d * mollifier d (R • y)) x = _ at he
  change fderiv ℝ (fun y : Vec d => R ^ d * mollifier d (R • y)) x (unitVector l) = _
  rw [he]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, coordinateDerivative, R]
  ring

private theorem firstStripSpatialKernel_first_moment (d n : ℕ) :
    (∫ x, |firstStripSpatialKernel d n x| * euclideanNorm x) =
      ((n : ℝ) + 1)⁻¹ * ∫ x, mollifier d x * euclideanNorm x := by
  let R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by positivity
  have he (x : Vec d) :
      |firstStripSpatialKernel d n x| * euclideanNorm x =
        (R ^ d * R⁻¹) * (mollifier d (R • x) * euclideanNorm (R • x)) := by
    rw [abs_of_nonneg (firstStripSpatialKernel_nonneg d n x),
      TimeChange.euclideanNorm_smul, abs_of_pos hR]
    change R ^ d * mollifier d (R • x) * euclideanNorm x = _
    field_simp
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume
    (fun x : Vec d => mollifier d x * euclideanNorm x) R (hR := hR.le),
    Module.finrank_fin_fun, smul_eq_mul]
  field_simp
  dsimp only [R]
  ring

private theorem firstStripSpatialKernel_derivative_moment (d n : ℕ) (l : Fin d) :
    (∫ x, |coordinateDerivative l (firstStripSpatialKernel d n) x| * euclideanNorm x) =
      ∫ x, |coordinateDerivative l (mollifier d) x| * euclideanNorm x := by
  let R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by positivity
  have he (x : Vec d) :
      |coordinateDerivative l (firstStripSpatialKernel d n) x| * euclideanNorm x =
        R ^ d * (|coordinateDerivative l (mollifier d) (R • x)| *
          euclideanNorm (R • x)) := by
    rw [firstStripSpatialKernel_derivative, abs_mul, abs_mul,
      abs_of_pos (pow_pos hR d), abs_of_pos hR,
      TimeChange.euclideanNorm_smul, abs_of_pos hR]
    ring
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume
    (fun x : Vec d => |coordinateDerivative l (mollifier d) x| * euclideanNorm x)
    R (hR := hR.le), Module.finrank_fin_fun, smul_eq_mul]
  field_simp

private theorem firstStripSpatialKernel_moments (d : ℕ) (l : Fin d) :
    (∀ n, (∫ x, |firstStripSpatialKernel d n x|) = 1) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ n,
      (∫ x, |coordinateDerivative l (firstStripSpatialKernel d n) x| * euclideanNorm x) +
        ∫ x, |firstStripSpatialKernel d n x| ≤ K) ∧
    Tendsto (fun n => ∫ x, |firstStripSpatialKernel d n x| * euclideanNorm x)
      atTop (𝓝 0) := by
  have hm (n : ℕ) : (∫ x, |firstStripSpatialKernel d n x|) = 1 := by
    simp_rw [abs_of_nonneg (firstStripSpatialKernel_nonneg d n _)]
    exact firstStripSpatialKernel_mass d n
  refine ⟨hm, ?_, ?_⟩
  · refine ⟨(∫ x, |coordinateDerivative l (mollifier d) x| * euclideanNorm x) + 1,
      add_nonneg (integral_nonneg fun x => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
        zero_le_one, fun n => ?_⟩
    rw [firstStripSpatialKernel_derivative_moment, hm]
  · simp_rw [firstStripSpatialKernel_first_moment]
    have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa only [zero_mul] using ht.mul_const (∫ x, mollifier d x * euclideanNorm x)

private theorem firstStripSpatialKernel_average {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ x, (firstStripSpatialKernel d n x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) =
    ∫ x, (mollifier d x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
        (((n : ℝ) + 1)⁻¹ • x) f := by
  let R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by positivity
  let T := complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
  let H := fun x : Vec d => mollifier d x • T (R⁻¹ • x) f
  have hi := Measure.integral_comp_smul_of_nonneg volume H R (hR := hR.le)
  rw [Module.finrank_fin_fun] at hi
  have he (x : Vec d) :
      (firstStripSpatialKernel d n x : ℂ) • T x f = R ^ d • H (R • x) := by
    rw [Complex.coe_smul]
    change (R ^ d * mollifier d (R • x)) • T x f =
      R ^ d • (mollifier d (R • x) • T (R⁻¹ • (R • x)) f)
    rw [smul_smul R⁻¹ R x, inv_mul_cancel₀ hR.ne', one_smul, smul_smul]
  change (∫ x, (firstStripSpatialKernel d n x : ℂ) • T x f) = _
  simp_rw [he]
  rw [integral_smul, hi, smul_smul, mul_inv_cancel₀ (pow_ne_zero d hR.ne'), one_smul]
  simp only [H, T, R]
  apply integral_congr_ae
  exact ae_of_all _ fun x => RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

private theorem firstStripSpatialKernel_average_tendsto {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (f : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun n => firstStripKernelAverage Q (firstStripSpatialKernel d n)
      (firstStripSpatialKernel_smooth d n).continuous
      (firstStripSpatialKernel_compact d n) f) atTop (𝓝 f) := by
  let T := complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
  let ε := fun n : ℕ => ((n : ℝ) + 1)⁻¹
  have hε : Tendsto ε atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hc (n : ℕ) : Continuous (fun x : Vec d => (mollifier d x : ℂ) • T (ε n • x) f) :=
    (Complex.continuous_ofReal.comp (contDiff_mollifier d).continuous).smul
      ((continuous_complexTranslation _ _).comp
        ((continuous_id.const_smul (ε n)).prodMk continuous_const))
  have hb (n : ℕ) (x : Vec d) :
      ‖(mollifier d x : ℂ) • T (ε n • x) f‖ ≤ mollifier d x * ‖f‖ := by
    simp only [T, norm_smul, norm_complexTranslation, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg d x), le_refl]
  have hi : Integrable (fun x : Vec d => mollifier d x * ‖f‖) :=
    ((contDiff_mollifier d).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_mollifier d)).mul_const ‖f‖
  have hp (x : Vec d) : Tendsto
      (fun n => (mollifier d x : ℂ) • T (ε n • x) f)
      atTop (𝓝 ((mollifier d x : ℂ) • f)) := by
    have hx : Tendsto (fun n => ε n • x) atTop (𝓝 (0 : Vec d)) := by
      simpa only [zero_smul] using hε.smul_const x
    exact ((tendsto_complexTranslation_zero _ _ f).comp hx).const_smul _
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun x : Vec d => mollifier d x * ‖f‖)
    (Eventually.of_forall fun n => (hc n).aestronglyMeasurable)
    (Eventually.of_forall fun n => ae_of_all _ (hb n)) hi (ae_of_all _ hp)
  have hlim : (∫ x : Vec d, (mollifier d x : ℂ) • f) = f := by
    rw [integral_smul_const, integral_complex_ofReal, integral_mollifier,
      Complex.ofReal_one, one_smul]
  rw [hlim] at ht
  apply ht.congr' (Eventually.of_forall fun n => ?_)
  exact (firstStripSpatialKernel_average Q n f).symm

/-- Actual Friedrichs convergence for the fixed spatial smoothing sequence;
the uniform moment and shrinking-support conditions have been discharged. -/
private theorem firstStripSpatialKernel_friedrichs_tendsto {d : ℕ}
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i j k l : Fin d) :
    ∃ M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ f : Lp ℂ 2 (reducedLaw Q), M f =ᵐ[reducedLaw Q] fun ω =>
        (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * f ω) ∧
      ∀ f : Lp ℂ 2 (reducedLaw Q),
      Tendsto (fun n =>
        ((∫ x, (coordinateDerivative l (firstStripSpatialKernel d n) x : ℂ) •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
              (complexCoefficientMul Q j k f)) -
          complexCoefficientMul Q j k
            (∫ x, (coordinateDerivative l (firstStripSpatialKernel d n) x : ℂ) •
              complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) +
          (∫ x, (firstStripSpatialKernel d n x : ℂ) •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (M f)))
        atTop (𝓝 0) := by
  obtain ⟨M, hM, ht⟩ := firstStrip_friedrichs_remainder_tendsto D Q hQ i j k l
  obtain ⟨_hmass, ⟨K, hK, hbound⟩, hsmall⟩ := firstStripSpatialKernel_moments d l
  exact ⟨M, hM, ht (firstStripSpatialKernel d) (firstStripSpatialKernel_smooth d)
    (firstStripSpatialKernel_compact d) K hK hbound hsmall⟩

/-- Unit-mass spatial smoothing is contractive on the actual environment L² space. -/
private theorem firstStripSpatialKernel_average_norm {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖firstStripKernelAverage Q (firstStripSpatialKernel d n)
      (firstStripSpatialKernel_smooth d n).continuous
      (firstStripSpatialKernel_compact d n) f‖ ≤ ‖f‖ := by
  change ‖∫ x, (firstStripSpatialKernel d n x : ℂ) •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f‖ ≤ ‖f‖
  calc
    _ ≤ ∫ x, ‖(firstStripSpatialKernel d n x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f‖ :=
      norm_integral_le_integral_norm _
    _ = ‖f‖ := by
      simp only [norm_smul, norm_complexTranslation, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (firstStripSpatialKernel_nonneg d n _), integral_mul_const,
        firstStripSpatialKernel_mass, one_mul]

/-- Removing spatial smoothing in time L² requires only the genuine time-L²
energy of the orbit, rather than a pointwise bound on its gradients. -/
private theorem firstStripSpatialKernel_average_timeL2 {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (σ : Measure ℝ)
    (F : ℝ → Lp ℂ 2 (reducedLaw Q)) (hF : MemLp F 2 σ) :
    Tendsto (fun n => ∫ s, ‖firstStripKernelAverage Q (firstStripSpatialKernel d n)
      (firstStripSpatialKernel_smooth d n).continuous
      (firstStripSpatialKernel_compact d n) (F s) - F s‖ ^ 2 ∂σ)
      atTop (𝓝 0) := by
  let A := fun n => firstStripKernelAverage Q (firstStripSpatialKernel d n)
    (firstStripSpatialKernel_smooth d n).continuous (firstStripSpatialKernel_compact d n)
  have hm (n : ℕ) : AEStronglyMeasurable (fun s => ‖A n (F s) - F s‖ ^ 2) σ :=
    (((A n).continuous.comp_aestronglyMeasurable hF.aestronglyMeasurable).sub
      hF.aestronglyMeasurable).norm.pow 2
  have hb (n : ℕ) (s : ℝ) : ‖A n (F s) - F s‖ ^ 2 ≤ 4 * ‖F s‖ ^ 2 := by
    have hn : ‖A n (F s) - F s‖ ≤ 2 * ‖F s‖ := by
      calc
        _ ≤ ‖A n (F s)‖ + ‖F s‖ := norm_sub_le _ _
        _ ≤ ‖F s‖ + ‖F s‖ := add_le_add
          (firstStripSpatialKernel_average_norm Q n (F s)) le_rfl
        _ = _ := by ring
    calc
      _ ≤ (2 * ‖F s‖) ^ 2 := by gcongr
      _ = _ := by ring
  have hi : Integrable (fun s => 4 * ‖F s‖ ^ 2) σ :=
    (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul 4
  have hp (s : ℝ) : Tendsto (fun n => ‖A n (F s) - F s‖ ^ 2) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((firstStripSpatialKernel_average_tendsto Q (F s)).sub_const (F s)).norm.pow 2
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun s => 4 * ‖F s‖ ^ 2) (Eventually.of_forall hm)
    (Eventually.of_forall fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖A n (F s) - F s‖))]
      exact hb n s)
    hi (ae_of_all _ hp)
  simpa only [integral_zero] using ht

/-- The spatial averages converge over the entire horizon for each coordinate
of the same actual forward, clock, or transpose gradient used above. -/
private theorem firstStripTimeGradient_spatial_average_timeL2 {d : ℕ}
    (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (ν : EndpointIndex d) (j : Fin d) (t : ℝ≥0) :
    Tendsto (fun n => ∫ s in Ioc (0 : ℝ) (t : ℝ),
      ‖firstStripKernelAverage Q (firstStripSpatialKernel d n)
        (firstStripSpatialKernel_smooth d n).continuous
        (firstStripSpatialKernel_compact d n)
        (firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) -
        firstStripTimeGradient hd Q β a μ ζ P T hP ν s j‖ ^ 2)
      atTop (𝓝 0) := by
  have hF : MemLp (firstStripTimeGradient hd Q β a μ ζ P T hP ν) 2
      (volume.restrict (Ioc (0 : ℝ) (t : ℝ))) := by
    cases ν with
    | inl k => exact hP.memLp_gradientOrbit_fullHorizon _ t
    | inr b =>
      cases b with
      | false => exact hP.memLp_gradientOrbit_fullHorizon _ t
      | true => exact (hT.gradientOrbit_horizon_energy hP _ t).1
  let C := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j
  exact firstStripSpatialKernel_average_timeL2 Q _ _ (C.comp_memLp' hF)

/-- The actual coefficient Friedrichs remainder vanishes in time L² for the
canonical spatial kernels. The multiplier is fixed before the time orbit. -/
private theorem firstStripSpatialKernel_friedrichs_timeL2 {d : ℕ}
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i j k l : Fin d) :
    ∃ M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ f : Lp ℂ 2 (reducedLaw Q), M f =ᵐ[reducedLaw Q] fun ω =>
        (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * f ω) ∧
      ∀ (σ : Measure ℝ) (F : ℝ → Lp ℂ 2 (reducedLaw Q)), MemLp F 2 σ →
      Tendsto (fun n => ∫ s,
        ‖((∫ x, (coordinateDerivative l (firstStripSpatialKernel d n) x : ℂ) •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
              (complexCoefficientMul Q j k (F s))) -
          complexCoefficientMul Q j k
            (∫ x, (coordinateDerivative l (firstStripSpatialKernel d n) x : ℂ) •
              complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (F s))) +
          (∫ x, (firstStripSpatialKernel d n x : ℂ) •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (M (F s)))‖ ^ 2 ∂σ)
        atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := firstStrip_friedrichs_remainder_bound D
  obtain ⟨M, hM, hbound⟩ := hb Q hQ j k l
  obtain ⟨M', hM', ht⟩ := firstStripSpatialKernel_friedrichs_tendsto D Q hQ i j k l
  have hsame : M' = M := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (hM' f).trans (hM f).symm
  rw [hsame] at ht
  obtain ⟨_, ⟨K, hK, hmoment⟩, _⟩ := firstStripSpatialKernel_moments d l
  let κ := firstStripSpatialKernel d
  let B := fun n => firstStripKernelAverage Q (κ n)
    (firstStripSpatialKernel_smooth d n).continuous (firstStripSpatialKernel_compact d n)
  have hD (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative l (κ n)) :=
    ((firstStripSpatialKernel_smooth d n).fderiv_right (by simp)).clm_apply contDiff_const
  let H := fun n => firstStripKernelAverage Q (coordinateDerivative l (κ n))
    (hD n).continuous ((firstStripSpatialKernel_compact d n).fderiv_apply ℝ (unitVector l))
  let A := complexCoefficientMul Q j k
  let R : ℕ → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
    fun n => (H n).comp A - A.comp (H n) + (B n).comp M
  have hnorm (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) : ‖R n f‖ ≤ (C * K) * ‖f‖ := by
    exact (hbound (κ n) (firstStripSpatialKernel_smooth d n)
      (firstStripSpatialKernel_compact d n) f).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hmoment n) hC) (norm_nonneg _))
  have hp (f : Lp ℂ 2 (reducedLaw Q)) :
      Tendsto (fun n => R n f) atTop (𝓝 0) := ht f
  refine ⟨M, hM, ?_⟩
  intro σ F hF
  have hm (n : ℕ) : AEStronglyMeasurable (fun s => ‖R n (F s)‖ ^ 2) σ :=
    ((R n).continuous.comp_aestronglyMeasurable hF.aestronglyMeasurable).norm.pow 2
  have hdom (n : ℕ) (s : ℝ) : ‖R n (F s)‖ ^ 2 ≤ (C * K) ^ 2 * ‖F s‖ ^ 2 := by
    calc
      _ ≤ ((C * K) * ‖F s‖) ^ 2 := by
        gcongr
        exact hnorm n (F s)
      _ = _ := by ring
  have hi : Integrable (fun s => (C * K) ^ 2 * ‖F s‖ ^ 2) σ :=
    (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _
  have hpoint (s : ℝ) : Tendsto (fun n => ‖R n (F s)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (hp (F s)).norm.pow 2
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun s => (C * K) ^ 2 * ‖F s‖ ^ 2) (Eventually.of_forall hm)
    (Eventually.of_forall fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖R n (F s)‖))]
      exact hdom n s)
    hi (ae_of_all _ hpoint)
  change Tendsto (fun n => ∫ s, ‖R n (F s)‖ ^ 2 ∂σ) atTop (𝓝 0)
  simpa only [integral_zero] using hlim

/-- Time regularization is defined on a finite horizon, where the actual
gradient orbit is integrable even at its initial endpoint. -/
private def firstStripTimeSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : ℝ → ℝ) (F : ℝ → E) (t : ℝ≥0) (u : ℝ) : E :=
  ∫ s in Icc (0 : ℝ) (t : ℝ), κ (u - s) • F s

private theorem firstStripTimeSmooth_eq_convolution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : ℝ → ℝ) (F : ℝ → E)
    (t : ℝ≥0) :
    firstStripTimeSmooth κ F t =
      ((Icc (0 : ℝ) (t : ℝ)).indicator F) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip, volume] κ := by
  funext u
  rw [firstStripTimeSmooth, convolution_def, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by
    by_cases hs : s ∈ Icc (0 : ℝ) (t : ℝ) <;>
      simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
        indicator_of_mem, indicator_of_notMem, hs, not_false_eq_true, smul_zero]

/-- Both time smoothness and its derivative follow from integrability alone;
the derivative falls on the kernel, rather than on the energy-class orbit. -/
private theorem firstStripTimeSmooth_regularization {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    {F : ℝ → E} (t : ℝ≥0) (hF : IntegrableOn F (Icc (0 : ℝ) (t : ℝ))) :
    ContDiff ℝ (⊤ : ℕ∞) (firstStripTimeSmooth κ F t) ∧
      ∀ u, HasDerivAt (firstStripTimeSmooth κ F t)
        (firstStripTimeSmooth (deriv κ) F t u) u := by
  have hi : LocallyIntegrable ((Icc (0 : ℝ) (t : ℝ)).indicator F) volume :=
    ((integrable_indicator_iff measurableSet_Icc).mpr hF).locallyIntegrable
  let L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip
  simp only [firstStripTimeSmooth_eq_convolution]
  exact ⟨hκc.contDiff_convolution_right L hi hκ,
    fun u => hκc.hasDerivAt_convolution_right L hi (hκ.of_le (by simp)) u⟩

/-- Actual forward, clock and transpose gradients admit smooth time
regularizations with an explicit derivative, without a new regularity premise. -/
private theorem firstStripTimeGradient_regularization {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    (t : ℝ≥0) :
    ContDiff ℝ (⊤ : ℕ∞)
      (firstStripTimeSmooth κ (firstStripTimeGradient hd Q β a μ ζ P T hP ν) t) ∧
      ∀ u, HasDerivAt
        (firstStripTimeSmooth κ (firstStripTimeGradient hd Q β a μ ζ P T hP ν) t)
        (firstStripTimeSmooth (deriv κ)
          (firstStripTimeGradient hd Q β a μ ζ P T hP ν) t u) u := by
  apply firstStripTimeSmooth_regularization κ hκ hκc t
  cases ν with
  | inl k => exact hP.integrableOn_gradientOrbit _ t
  | inr b =>
    cases b with
    | false => exact hP.integrableOn_gradientOrbit _ t
    | true => exact hT.integrableOn_gradientOrbit hP _ t

/-- Each coordinate has the same temporal regularization; its integrability
follows by continuous projection of the actual energy-class orbit. -/
private theorem firstStripTimeGradient_coordinate_regularization {d : ℕ} (hd : 2 ≤ d)
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    (t : ℝ≥0) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (firstStripTimeSmooth κ
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) t) ∧
      ∀ u, HasDerivAt (firstStripTimeSmooth κ
        (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) t)
        (firstStripTimeSmooth (deriv κ)
          (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) t u) u := by
  apply firstStripTimeSmooth_regularization κ hκ hκc t
  let C := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j
  have hi : IntegrableOn (firstStripTimeGradient hd Q β a μ ζ P T hP ν)
      (Icc (0 : ℝ) (t : ℝ)) := by
    cases ν with
    | inl k => exact hP.integrableOn_gradientOrbit _ t
    | inr b =>
      cases b with
      | false => exact hP.integrableOn_gradientOrbit _ t
      | true => exact hT.integrableOn_gradientOrbit hP _ t
  exact C.integrable_comp hi

/-- The actual endpoint value has the same smooth time regularization as its
gradient, including the signed clock datum and the transpose branch. -/
private theorem firstStrip_endpoint_time_regularization {d : ℕ} (hd : 2 ≤ d)
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    (t : ℝ≥0) :
    let F := fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal
    ContDiff ℝ (⊤ : ℕ∞) (firstStripTimeSmooth κ F t) ∧
      ∀ u, HasDerivAt (firstStripTimeSmooth κ F t)
        (firstStripTimeSmooth (deriv κ) F t u) u := by
  apply firstStripTimeSmooth_regularization κ hκ hκc t
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply Continuous.continuousOn
  cases ν with
  | inl k => exact (hP.2.2.1 _).comp continuous_real_toNNReal
  | inr b =>
    cases b with
    | false =>
      change Continuous (fun s : ℝ => ζ • P s.toNNReal μ)
      exact (continuous_const : Continuous (fun _ : ℝ => ζ)).smul
        ((hP.2.2.1 μ).comp continuous_real_toNNReal)
    | true => exact (hT.continuous_apply hP _).comp continuous_real_toNNReal

/-- Time regularization preserves the actual endpoint's horizontal gradient;
the energy-class gradient supplies the integrable graph representative. -/
private theorem firstStrip_endpoint_time_gradient {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : Continuous κ) (t : ℝ≥0) (u : ℝ) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (firstStripTimeSmooth κ
        (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u)
      (fun j => firstStripTimeSmooth κ
        (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) t u) :=
  firstStrip_time_primitive_gradient hd Q hQ β a μ hβ ζ P T hP hT ν
    (fun s => κ (u - s)) (hκ.comp (continuous_const.sub continuous_id)) t

/-- After time regularization away from the horizon's endpoints, the
spatially smoothed actual gradient satisfies its differentiated equation.
The left side is the time derivative kernel, with the parabolic sign. -/
private theorem firstStrip_endpoint_space_time_equation {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (t : ℝ≥0) (u : ℝ) (hzero : κ u = 0) (ht : κ (u - t) = 0) :
    let U := firstStripTimeSmooth κ
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
    let H := fun k => firstStripTimeSmooth κ
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
    let V := fun l => firstStripTimeSmooth (deriv κ)
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s l) t u
    ∀ᵐ ω ∂reducedLaw Q,
      let F := fun j y => (∑ k, (ω.1 y j k : ℂ) * H k (translate y ω)) -
        (if ν = .inr true then 2 * ζ else 0) *
          ((ω.1 y j ⟨0, by omega⟩ : ℂ) * U (translate y ω))
      let B := fun y => ∑ j, (ω.1 y j ⟨0, by omega⟩ : ℂ) * H j (translate y ω)
      ∀ K : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) K → HasCompactSupport K →
        ∀ (x : Vec d) (l : Fin d),
          firstStripSpatialSmooth K (fun y => V l (translate y ω)) x =
            (1 / 2 : ℂ) * (∑ j, fderiv ℝ
              (fun z => fderiv ℝ (firstStripSpatialSmooth K (F j)) z (unitVector l))
              x (unitVector j)) +
            (if ν = .inr true then 0 else ζ) *
              fderiv ℝ (firstStripSpatialSmooth K B) x (unitVector l) := by
  let U := firstStripTimeSmooth κ
    (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
  let H := fun k => firstStripTimeSmooth κ
    (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
  let V := fun l => firstStripTimeSmooth (deriv κ)
    (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s l) t u
  have hη (s : ℝ) : HasDerivAt (fun s => κ (u - s)) (-deriv κ (u - s)) s := by
    simpa only [Function.comp_def, id_eq, mul_neg, mul_one] using!
      ((hκ.differentiable (by simp)).differentiableAt.hasDerivAt.comp s
        ((hasDerivAt_id s).const_sub u))
  have hη' : Continuous (fun s => -deriv κ (u - s)) :=
    ((hκ.continuous_deriv (by simp)).comp (continuous_const.sub continuous_id)).neg
  have he := firstStrip_endpoint_regularized_gradient hd D Q hQ β a μ ζ P T hP hT ν
    (fun s => κ (u - s)) (fun s => -deriv κ (u - s)) hη hη' t
    (by simpa only [sub_zero] using hzero) ht
  have hn : ∀ᵐ ω ∂reducedLaw Q, ∀ l : Fin d,
      (fun y => (-V l) (translate y ω)) =ᵐ[volume]
        fun y => -(V l (translate y ω)) :=
    ae_all_iff.mpr fun l => ae_complex_spatial_orbit_congr
      (reducedLaw Q) (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable (-V l)).measurable
      (Lp.stronglyMeasurable (V l)).measurable.neg (Lp.coeFn_neg (V l))
  dsimp only at he ⊢
  simp only [neg_smul, integral_neg] at he
  filter_upwards [he, hn] with ω he hn
  intro K hK hKc x l
  have he := he K hK hKc x l
  have hneg : firstStripSpatialSmooth K (fun y => (-V l) (translate y ω)) x =
      -firstStripSpatialSmooth K (fun y => V l (translate y ω)) x := by
    rw [firstStripSpatialSmooth, firstStripSpatialSmooth, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [hn l] with y hy
    rw [hy, neg_mul]
  change firstStripSpatialSmooth K (fun y => (-V l) (translate y ω)) x = _ at he
  rw [hneg] at he
  dsimp only [V, firstStripTimeSmooth] at he ⊢
  linear_combination -he

/-- The primitive uses the squared norm of the whole real Hilbert vector. -/
private def firstStripHilbertPrimitive {E : Type*} [NormedAddCommGroup E]
    (ε R a : ℝ) (z : E) : ℝ :=
  (1 / 2 : ℝ) * ∫ s in 0..‖z‖ ^ 2, radialTruncationWeight ε R a (max s 0)

private theorem firstStripHilbertWeight_continuous {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) :
    Continuous (fun s : ℝ => radialTruncationWeight ε R a (max s 0)) :=
  (continuousOn_radialTruncationWeight_slope (a := a) hε hR).1.comp_continuous
    (continuous_id.max continuous_const) (fun s => le_max_right s 0)

/-- A dimension-independent derivative bound for the coupled radial test. -/
private theorem firstStripHilbertRadial_lipschitz {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    LipschitzWith ⟨(1 + 2 * a) * (ε + R) ^ a, by positivity⟩
      (fun z : E => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) := by
  let D (z : E) : E →L[ℝ] E :=
    radialTruncationWeight ε R a (‖z‖ ^ 2) • ContinuousLinearMap.id ℝ E +
      ((2 * radialTruncationSlope ε R a (‖z‖ ^ 2)) • innerSL ℝ z).smulRight z
  have hd (z : E) : HasFDerivAt
      (fun w : E => radialTruncationWeight ε R a (‖w‖ ^ 2) • w) (D z) z := by
    have h := ((hasDerivAt_radialTruncationWeight (a := a) hε hR (sq_nonneg ‖z‖)).hasFDerivAt.comp z
      (hasStrictFDerivAt_norm_sq z).hasFDerivAt).smul (hasFDerivAt_id z)
    apply h.congr_fderiv
    ext w
    simp only [D, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      innerSL_apply_apply, Function.comp_apply, id_eq, smul_eq_mul]
    module
  apply lipschitzWith_of_nnnorm_fderiv_le (fun z => (hd z).differentiableAt)
  intro z
  change ‖fderiv ℝ (fun w : E => radialTruncationWeight ε R a (‖w‖ ^ 2) • w) z‖ ≤ _
  rw [(hd z).fderiv]
  calc
    ‖D z‖ ≤ ‖radialTruncationWeight ε R a (‖z‖ ^ 2) • ContinuousLinearMap.id ℝ E‖ +
        ‖((2 * radialTruncationSlope ε R a (‖z‖ ^ 2)) • innerSL ℝ z).smulRight z‖ :=
      norm_add_le _ _
    _ ≤ |radialTruncationWeight ε R a (‖z‖ ^ 2)| +
        2 * |radialTruncationSlope ε R a (‖z‖ ^ 2)| * ‖z‖ ^ 2 := by
      rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, norm_smul,
        innerSL_apply_norm]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith only [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E),
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
          (abs_nonneg (radialTruncationWeight ε R a (‖z‖ ^ 2)))]
    _ ≤ _ := radialTruncationWeight_differential_bound hε hR ha (sq_nonneg ‖z‖)

private theorem firstStripHilbertPrimitive_hasFDerivAt {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (z : E) :
    HasFDerivAt (firstStripHilbertPrimitive ε R a)
      (innerSL ℝ (radialTruncationWeight ε R a (‖z‖ ^ 2) • z)) z := by
  have hc := firstStripHilbertWeight_continuous (a := a) hε hR
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 (‖z‖ ^ 2)) (hc.stronglyMeasurableAtFilter _ _)
    hc.continuousAt).hasFDerivAt.comp z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hh := hd.const_mul (1 / 2 : ℝ)
  apply hh.congr_fderiv
  ext w
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, max_eq_left (sq_nonneg ‖z‖), innerSL_apply_apply,
    real_inner_smul_left]
  ring

/-- The primitive vanishes at the zero function value. -/
private theorem firstStripHilbertPrimitive_zero {E : Type*} [NormedAddCommGroup E]
    (ε R a : ℝ) :
    firstStripHilbertPrimitive ε R a (0 : E) = 0 := by
  simp only [firstStripHilbertPrimitive, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, intervalIntegral.integral_same, mul_zero]

private theorem firstStripHilbert_remainder {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {φ : E → ℝ} {G : E → E} {K : ℝ≥0}
    (hG : LipschitzWith K G) (hd : ∀ z, HasFDerivAt φ (innerSL ℝ (G z)) z)
    (x y : E) :
    ‖φ y - φ x - inner ℝ (G x) (y - x)‖ ≤ (K : ℝ) * ‖y - x‖ ^ 2 := by
  let f (z : E) := φ z - φ x - inner ℝ (G x) (z - x)
  have hf (z : E) : HasFDerivAt f (innerSL ℝ (G z) - innerSL ℝ (G x)) z := by
    simpa only [f, ContinuousLinearMap.comp_id] using!
      ((hd z).sub_const (φ x)).sub
        ((innerSL ℝ (G x)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x))
  have hb (z : E) (hz : z ∈ segment ℝ x y) :
      ‖innerSL ℝ (G z) - innerSL ℝ (G x)‖ ≤ (K : ℝ) * ‖y - x‖ := by
    calc
      _ = ‖innerSL ℝ (G z - G x)‖ := by rw [map_sub]
      _ = ‖G z - G x‖ := innerSL_apply_norm ℝ _
      _ ≤ (K : ℝ) * ‖z - x‖ := hG.norm_sub_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hf z).hasFDerivWithinAt) hb
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [f, sub_self, inner_zero_right, sub_zero, mul_assoc, pow_two] using h

private theorem firstStripHilbertPrimitive_remainder {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (x y : E) :
    ‖firstStripHilbertPrimitive ε R a y - firstStripHilbertPrimitive ε R a x -
      inner ℝ (radialTruncationWeight ε R a (‖x‖ ^ 2) • x) (y - x)‖ ≤
        ((1 + 2 * a) * (ε + R) ^ a) * ‖y - x‖ ^ 2 :=
  firstStripHilbert_remainder (firstStripHilbertRadial_lipschitz hε hR ha)
    (firstStripHilbertPrimitive_hasFDerivAt hε hR) x y

/-- The coupled primitive has at most quadratic growth at every Hilbert vector. -/
private theorem firstStripHilbertPrimitive_growth {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (z : E) :
    ‖firstStripHilbertPrimitive ε R a z‖ ≤
      ((1 + 2 * a) * (ε + R) ^ a) * ‖z‖ ^ 2 := by
  simpa only [firstStripHilbertPrimitive_zero, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, smul_zero, inner_zero_left,
    sub_zero] using firstStripHilbertPrimitive_remainder hε hR ha 0 z

/-- The primitive defines an actual integrable energy on the entire Hilbert-valued L2 space. -/
private theorem firstStripHilbertPrimitive_integrable {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : Lp E 2 μ) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    Integrable (fun ω => firstStripHilbertPrimitive ε R a (f ω)) μ := by
  have hc : Continuous (firstStripHilbertPrimitive (E := E) ε R a) :=
    continuous_iff_continuousAt.mpr fun z =>
      (firstStripHilbertPrimitive_hasFDerivAt hε hR z).continuousAt
  apply ((Lp.memLp f).norm.integrable_sq.const_mul
    ((1 + 2 * a) * (ε + R) ^ a)).mono'
      (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall fun ω => firstStripHilbertPrimitive_growth hε hR ha (f ω)

private theorem firstStripHilbertPrimitive_integral_remainder {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g v : Lp E 2 μ) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a)
    (hv : v =ᵐ[μ] fun ω => radialTruncationWeight ε R a (‖f ω‖ ^ 2) • f ω) :
    ‖(∫ ω, firstStripHilbertPrimitive ε R a (g ω) ∂μ) -
        (∫ ω, firstStripHilbertPrimitive ε R a (f ω) ∂μ) - inner ℝ v (g - f)‖ ≤
      ((1 + 2 * a) * (ε + R) ^ a) * ‖g - f‖ ^ 2 := by
  have hi (u : Lp E 2 μ) := firstStripHilbertPrimitive_integrable μ u hε hR ha
  have hh : Integrable (fun ω => inner ℝ (v ω) ((g - f) ω)) μ :=
    L2.integrable_inner v (g - f)
  have he : ‖g - f‖ ^ 2 = ∫ ω, ‖(g - f) ω‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  have hiDiff : Integrable (fun ω => firstStripHilbertPrimitive ε R a (g ω) -
      firstStripHilbertPrimitive ε R a (f ω)) μ := (hi g).sub (hi f)
  rw [L2.inner_def, ← integral_sub (hi g) (hi f)]
  rw [← integral_sub hiDiff hh, he, ← integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae ((hi g).sub (hi f) |>.sub hh).norm
    ((Lp.memLp (g - f)).norm.integrable_sq.const_mul _)
  filter_upwards [hv, Lp.coeFn_sub g f] with ω hvω hsub
  simp only [hvω, hsub, Pi.sub_apply]
  exact firstStripHilbertPrimitive_remainder hε hR ha (f ω) (g ω)

/-- The primitive integral is Frechet differentiable on the whole actual L2 space.
Its gradient is the actual L2 class of the bounded radial test. -/
private theorem firstStripHilbertPrimitive_integral_hasFDerivAt {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : Lp E 2 μ) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    let hL := firstStripHilbertRadial_lipschitz hε hR ha
    let hz : (fun z : E => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
      by simp only [smul_zero]
    HasFDerivAt (fun u : Lp E 2 μ => ∫ ω, firstStripHilbertPrimitive ε R a (u ω) ∂μ)
      (innerSL ℝ (hL.compLp hz f)) f := by
  dsimp only
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply (Asymptotics.IsBigO.of_bound ((1 + 2 * a) * (ε + R) ^ a) ?_).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := Lp E 2 μ) (by decide : 1 < 2))
  apply Eventually.of_forall
  intro h
  have hb := firstStripHilbertPrimitive_integral_remainder μ f (f + h)
    ((firstStripHilbertRadial_lipschitz hε hR ha).compLp (by simp only [smul_zero]) f)
    hε hR ha ((firstStripHilbertRadial_lipschitz hε hR ha).coeFn_compLp
      (by simp only [smul_zero]) f)
  simpa only [add_sub_cancel_left, innerSL_apply_apply, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖h‖)] using hb

/-- The derivative formula applies directly to every strongly differentiable L2 path. -/
private theorem firstStripHilbertPrimitive_time_chain {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u : ℝ → Lp E 2 μ} {g : Lp E 2 μ} {t : ℝ}
    (hu : HasDerivAt u g t) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    let hL := firstStripHilbertRadial_lipschitz hε hR ha
    let hz : (fun z : E => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
      by simp only [smul_zero]
    HasDerivAt (fun s => ∫ ω, firstStripHilbertPrimitive ε R a (u s ω) ∂μ)
      (inner ℝ (hL.compLp hz (u t)) g) t :=
  (firstStripHilbertPrimitive_integral_hasFDerivAt μ (u t) hε hR ha).comp_hasDerivAt t hu

/-- The same energy derivative is valid for one-sided strong L2 paths. -/
private theorem firstStripHilbertPrimitive_time_chain_within {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : ℝ → Lp E 2 μ} {g : Lp E 2 μ} {t : ℝ} {S : Set ℝ}
    (hu : HasDerivWithinAt u g S t) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    let hL := firstStripHilbertRadial_lipschitz hε hR ha
    let hz : (fun z : E => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
      by simp only [smul_zero]
    HasDerivWithinAt (fun s => ∫ ω, firstStripHilbertPrimitive ε R a (u s ω) ∂μ)
      (inner ℝ (hL.compLp hz (u t)) g) S t :=
  (firstStripHilbertPrimitive_integral_hasFDerivAt μ (u t) hε hR ha).comp_hasDerivWithinAt t hu

/-- The primitive energy is nonnegative at every actual Hilbert vector. -/
private theorem firstStripHilbertPrimitive_nonneg {E : Type*} [NormedAddCommGroup E] {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (z : E) :
    0 ≤ firstStripHilbertPrimitive ε R a z := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply intervalIntegral.integral_nonneg_of_forall (sq_nonneg ‖z‖)
  intro s
  exact Real.rpow_nonneg (radialTruncationBase_pos_le hε hR (le_max_right s 0)).1.le _

/-- The weighted mass is controlled by its primitive uniformly in both cutoffs.
This is the comparison needed to apply Gronwall without a cutoff-dependent rate. -/
private theorem firstStripHilbertPrimitive_mass_le {E : Type*} [NormedAddCommGroup E] {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (z : E) :
    radialTruncationWeight ε R a (‖z‖ ^ 2) * ‖z‖ ^ 2 ≤
      (2 * (1 + a)) * firstStripHilbertPrimitive ε R a z := by
  let F (s : ℝ) := (1 + a) *
    (∫ u in 0..s, radialTruncationWeight ε R a (max u 0)) -
      s * radialTruncationWeight ε R a s
  have hc := firstStripHilbertWeight_continuous (a := a) hε hR
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivAt F
      (a * radialTruncationWeight ε R a s - s * radialTruncationSlope ε R a s) s := by
    have hi := (intervalIntegral.integral_hasDerivAt_right
      (hc.intervalIntegrable 0 s) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt)
    have h := (hi.const_mul (1 + a)).sub
      ((hasDerivAt_id s).mul (hasDerivAt_radialTruncationWeight (a := a) hε hR hs))
    apply h.congr_deriv
    simp only [max_eq_left hs, id_eq]
    ring
  have hm : MonotoneOn F (Set.Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [(hd s (interior_subset hs)).deriv]
      have hb := (radialTruncationSlope_mul_le hε hR ha (interior_subset hs)).2
      nlinarith only [hb])
  have hb := hm (show (0 : ℝ) ∈ Set.Ici 0 by simp) (sq_nonneg ‖z‖) (sq_nonneg ‖z‖)
  simp only [F, intervalIntegral.integral_same, mul_zero, zero_mul, sub_zero] at hb
  unfold firstStripHilbertPrimitive
  nlinarith only [hb]

/-- A finite family of actual L2 classes, packed into a Euclidean-valued L2
class by continuous linear maps. This also transfers strong time derivatives. -/
private def firstStripSystemPack {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (n : ℕ) :
    (Fin n → Lp ℂ 2 μ) →L[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 μ :=
  ∑ j : Fin n,
    ((((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.single ℂ (fun _ : Fin n => ℂ) j)).compLpL 2 μ).comp
      (ContinuousLinearMap.proj j)

/-- All coordinates of a packed system agree on a single almost-everywhere event. -/
private theorem firstStripSystemPack_coe {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (n : ℕ) (f : Fin n → Lp ℂ 2 μ) :
    firstStripSystemPack μ n f =ᵐ[μ]
      fun ω => WithLp.toLp 2 (fun j => f j ω) := by
  let E (j : Fin n) : ℂ →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap |>.comp
      (ContinuousLinearMap.single ℂ (fun _ : Fin n => ℂ) j)
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun j => (E j).compLpL 2 μ (f j))
  have he : ∀ᵐ ω ∂μ, ∀ j : Fin n, (E j).compLpL 2 μ (f j) ω = E j (f j ω) :=
    ae_all_iff.mpr fun j => (E j).coeFn_compLpL (f j)
  simp only [firstStripSystemPack, sum_apply,
    ContinuousLinearMap.comp_apply]
  change (fun ω => (∑ j : Fin n, (E j).compLpL 2 μ (f j)) ω) =ᵐ[μ] _
  filter_upwards [hs, he] with ω hs he
  rw [hs]
  simp_rw [he]
  ext j
  simp [E, ContinuousLinearMap.single_apply]

/-- The packed energy is exactly the primitive of the common Euclidean radius. -/
private theorem firstStripSystemPack_energy {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (n : ℕ) (f : Fin n → Lp ℂ 2 μ) (ε R a : ℝ) :
    (∫ ω, firstStripHilbertPrimitive ε R a (firstStripSystemPack μ n f ω) ∂μ) =
      ∫ ω, firstStripHilbertPrimitive ε R a
        (WithLp.toLp 2 (fun j => f j ω) : EuclideanSpace ℂ (Fin n)) ∂μ := by
  apply integral_congr_ae
  filter_upwards [firstStripSystemPack_coe μ n f] with ω hω
  rw [hω]

/-- The L2 energy differential is the genuine componentwise radial test with
one shared radius, rather than a sum of independent scalar energies. -/
private theorem firstStripSystemPack_radial_pairing {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (n : ℕ) (f g : Fin n → Lp ℂ 2 μ) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    let hL := firstStripHilbertRadial_lipschitz
      (E := EuclideanSpace ℂ (Fin n)) hε hR ha
    let hz : (fun z : EuclideanSpace ℂ (Fin n) =>
      radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 := by simp only [smul_zero]
    inner ℝ (hL.compLp hz (firstStripSystemPack μ n f)) (firstStripSystemPack μ n g) =
      ∫ ω, ∑ j : Fin n,
        inner ℝ (radialTruncationWeight ε R a (∑ k : Fin n, ‖f k ω‖ ^ 2) • f j ω)
          (g j ω) ∂μ := by
  dsimp only
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [firstStripSystemPack_coe μ n f, firstStripSystemPack_coe μ n g,
    (firstStripHilbertRadial_lipschitz hε hR ha).coeFn_compLp
      (by simp only [smul_zero]) (firstStripSystemPack μ n f)] with ω hf hg hv
  rw [hv]
  simp only [Function.comp_apply]
  rw [hf, hg, PiLp.norm_sq_eq_of_L2, PiLp.inner_apply]
  rfl

/-- A strong L2 derivative of the finite system gives the coupled radial
energy derivative, without selecting pointwise time derivatives of L2 classes. -/
private theorem firstStripSystem_energy_chain {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {n : ℕ} {f : ℝ → Fin n → Lp ℂ 2 μ}
    {g : Fin n → Lp ℂ 2 μ} {u : ℝ} (hf : HasDerivAt f g u) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    HasDerivAt (fun s => ∫ ω, firstStripHilbertPrimitive ε R a
      (WithLp.toLp 2 (fun j => f s j ω) : EuclideanSpace ℂ (Fin n)) ∂μ)
      (∫ ω, ∑ j : Fin n,
        inner ℝ (radialTruncationWeight ε R a (∑ k : Fin n, ‖f u k ω‖ ^ 2) • f u j ω)
          (g j ω) ∂μ) u := by
  have hp : HasDerivAt (fun s => firstStripSystemPack μ n (f s))
      (firstStripSystemPack μ n g) u :=
    ((firstStripSystemPack μ n).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt u hf
  have h := firstStripHilbertPrimitive_time_chain hp hε hR ha
  simp_rw [firstStripSystemPack_energy] at h
  rw [firstStripSystemPack_radial_pairing μ n (f u) g hε hR ha] at h
  exact h

/-- The shared-radius energy pairing is continuous along continuous L2
fields. The proof uses bounded nonlinear composition on Euclidean-valued L2. -/
private theorem firstStripSystem_energy_pairing_continuous {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {n : ℕ} {f g : ℝ → Fin n → Lp ℂ 2 μ}
    (hf : Continuous f) (hg : Continuous g) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    Continuous (fun u => ∫ ω, ∑ j : Fin n,
      inner ℝ (radialTruncationWeight ε R a (∑ k : Fin n, ‖f u k ω‖ ^ 2) • f u j ω)
        (g u j ω) ∂μ) := by
  let hL := firstStripHilbertRadial_lipschitz
    (E := EuclideanSpace ℂ (Fin n)) hε hR ha
  have hz : (fun z : EuclideanSpace ℂ (Fin n) =>
      radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 := by simp only [smul_zero]
  have hc : Continuous (fun u => inner ℝ
      (hL.compLp hz (firstStripSystemPack μ n (f u)))
      (firstStripSystemPack μ n (g u))) := ((hL.continuous_compLp hz).comp
    ((firstStripSystemPack μ n).continuous.comp hf)).inner
      ((firstStripSystemPack μ n).continuous.comp hg)
  simpa only [firstStripSystemPack_radial_pairing μ n _ _ hε hR ha] using hc

/-- Fundamental theorem of calculus for the coupled nonlinear system energy.
All time integration is justified in L2 before any pointwise representatives
are chosen. The integral uses the exact shared-radius nonlinear test. -/
private theorem firstStripSystem_energy_FTC {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {n : ℕ} {f g : ℝ → Fin n → Lp ℂ 2 μ}
    (hf : ∀ u, HasDerivAt f (g u) u) (hg : Continuous g) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (u₀ u₁ : ℝ) :
    (∫ u in u₀..u₁, ∫ ω, ∑ j : Fin n,
      inner ℝ (radialTruncationWeight ε R a (∑ k : Fin n, ‖f u k ω‖ ^ 2) • f u j ω)
        (g u j ω) ∂μ) =
      (∫ ω, firstStripHilbertPrimitive ε R a
        (WithLp.toLp 2 (fun j => f u₁ j ω) : EuclideanSpace ℂ (Fin n)) ∂μ) -
      ∫ ω, firstStripHilbertPrimitive ε R a
        (WithLp.toLp 2 (fun j => f u₀ j ω) : EuclideanSpace ℂ (Fin n)) ∂μ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun u => (hf u).continuousAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => firstStripSystem_energy_chain (hf u) hε hR ha)
    ((firstStripSystem_energy_pairing_continuous hfc hg hε hR ha).intervalIntegrable u₀ u₁)

/-- The actual regularized endpoint and every gradient component obey one
coupled radial energy chain rule. Its radius includes the endpoint value, and
its time derivative uses the derivative of the very same temporal kernel. -/
private theorem firstStrip_endpoint_system_energy_chain {d : ℕ} (hd : 2 ≤ d)
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    (t : ℝ≥0) (u : ℝ) {ε R α : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hα : 0 ≤ α) :
    let J : (ℝ → ℝ) → ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) :=
      fun κ u => Fin.cons
      (firstStripTimeSmooth κ
        (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u)
      (fun j => firstStripTimeSmooth κ
        (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) t u)
    HasDerivAt (fun s => ∫ ω, firstStripHilbertPrimitive ε R α
      (WithLp.toLp 2 (fun j => J κ s j ω) : EuclideanSpace ℂ (Fin (d + 1)))
        ∂reducedLaw Q)
      (∫ ω, ∑ j : Fin (d + 1),
        inner ℝ (radialTruncationWeight ε R α
          (∑ k : Fin (d + 1), ‖J κ u k ω‖ ^ 2) • J κ u j ω)
            (J (deriv κ) u j ω) ∂reducedLaw Q) u := by
  dsimp only
  apply firstStripSystem_energy_chain ?_ hε hR hα
  apply hasDerivAt_pi.mpr
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact (firstStrip_endpoint_time_regularization hd Q β a μ ζ P T hP hT ν
      κ hκ hκc t).2 u
  · exact (firstStripTimeGradient_coordinate_regularization hd Q β a μ ζ P T hP hT ν
      κ hκ hκc t j).2 u

/-- Exact time-integrated coupled energy identity for the actual regularized
endpoint and its gradient, for all three endpoint branches and signed forces. -/
private theorem firstStrip_endpoint_system_energy_FTC {d : ℕ} (hd : 2 ≤ d)
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    (t : ℝ≥0) (u₀ u₁ : ℝ) {ε R α : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hα : 0 ≤ α) :
    let J : (ℝ → ℝ) → ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) :=
      fun κ u => Fin.cons
      (firstStripTimeSmooth κ
        (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u)
      (fun j => firstStripTimeSmooth κ
        (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) t u)
    (∫ u in u₀..u₁, ∫ ω, ∑ j : Fin (d + 1),
      inner ℝ (radialTruncationWeight ε R α
        (∑ k : Fin (d + 1), ‖J κ u k ω‖ ^ 2) • J κ u j ω)
          (J (deriv κ) u j ω) ∂reducedLaw Q) =
      (∫ ω, firstStripHilbertPrimitive ε R α
        (WithLp.toLp 2 (fun j => J κ u₁ j ω) : EuclideanSpace ℂ (Fin (d + 1)))
          ∂reducedLaw Q) -
      ∫ ω, firstStripHilbertPrimitive ε R α
        (WithLp.toLp 2 (fun j => J κ u₀ j ω) : EuclideanSpace ℂ (Fin (d + 1)))
          ∂reducedLaw Q := by
  dsimp only
  apply firstStripSystem_energy_FTC ?_ ?_ hε hR hα u₀ u₁
  · intro u
    apply hasDerivAt_pi.mpr
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact (firstStrip_endpoint_time_regularization hd Q β a μ ζ P T hP hT ν
        κ hκ hκc t).2 u
    · exact (firstStripTimeGradient_coordinate_regularization hd Q β a μ ζ P T hP hT ν
        κ hκ hκc t j).2 u
  · have hκ' : ContDiff ℝ (⊤ : ℕ∞) (deriv κ) := hκ.deriv'
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact (firstStrip_endpoint_time_regularization hd Q β a μ ζ P T hP hT ν
        (deriv κ) hκ' hκc.deriv t).1.continuous
    · exact (firstStripTimeGradient_coordinate_regularization hd Q β a μ ζ P T hP hT ν
        (deriv κ) hκ' hκc.deriv t j).1.continuous

/-- A bounded continuous differential on a vector-valued L2 class is an
actual scalar L2 class. The input keeps its norm, including Euclidean systems. -/
private theorem firstStrip_memLp_differential {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : E → E →L[ℝ] ℂ} (hD : Continuous D) {K : ℝ}
    (hK : ∀ z, ‖D z‖ ≤ K) (f g : Lp E 2 μ) :
    MemLp (fun a => D (f a) (g a)) 2 μ := by
  refine (Lp.memLp g).of_le_mul (c := K)
    ((ContinuousLinearMap.id ℝ (E →L[ℝ] ℂ)).aestronglyMeasurable_comp₂
      (hD.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
      (Lp.aestronglyMeasurable g)) (Eventually.of_forall fun a => ?_)
  exact (D (f a)).le_of_opNorm_le (hK _) _

/-- Dominated convergence differentiates a vector-input nonlinear test along
an affine L2 path, with its literal pointwise differential. -/
private theorem firstStrip_Lp_affine_chain {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) (h0 : F 0 = 0)
    {D : E → E →L[ℝ] ℂ} (hD : Continuous D)
    (hFD : ∀ z, HasFDerivAt F (D z) z) (f g : Lp E 2 μ) :
    HasDerivAt (fun t : ℝ => hF.compLp h0 (f + t • g))
      ((firstStrip_memLp_differential μ hD (fun z => (hFD z).le_of_lipschitz hF) f g).toLp
        (fun a => D (f a) (g a))) 0 := by
  let q (t : ℝ) (a : α) := t⁻¹ • (F (f a + t • g a) - F (f a))
  have hq (t : ℝ) (a : α) : ‖q t a‖ ≤ (K : ℝ) * ‖g a‖ := by
    by_cases ht : t = 0
    · simp only [q, ht, inv_zero, zero_smul, norm_zero]
      exact mul_nonneg K.coe_nonneg (norm_nonneg _)
    · calc
        ‖q t a‖ = |t|⁻¹ * ‖F (f a + t • g a) - F (f a)‖ := by
          dsimp only [q]
          rw [norm_smul, Real.norm_eq_abs, abs_inv]
        _ ≤ |t|⁻¹ * ((K : ℝ) * (|t| * ‖g a‖)) := by
          gcongr
          simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] using
            hF.norm_sub_le (f a + t • g a) (f a)
        _ = (K : ℝ) * ‖g a‖ := by
          calc
            _ = (K : ℝ) * (|t|⁻¹ * |t|) * ‖g a‖ := by ring
            _ = _ := by rw [inv_mul_cancel₀ (abs_ne_zero.mpr ht), mul_one]
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add, zero_smul, add_zero]
  refine tendsto_complexLp_of_dominated
    (F := q) (f := fun a => D (f a) (g a)) ?_ (MemLp.coeFn_toLp _)
    (b := fun a => (2 * (K : ℝ)) * ‖g a‖) ?_ ?_ ?_
  · intro t
    filter_upwards [Lp.coeFn_smul t⁻¹
        (hF.compLp h0 (f + t • g) - hF.compLp h0 f),
      Lp.coeFn_sub (hF.compLp h0 (f + t • g)) (hF.compLp h0 f),
      hF.coeFn_compLp h0 (f + t • g), hF.coeFn_compLp h0 f,
      Lp.coeFn_add f (t • g), Lp.coeFn_smul t g] with a ha hb hc hd he hh
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Function.comp_apply] at *
    rw [ha, hb, hc, hd, he, hh]
  · convert ((Lp.memLp g).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul
      ((2 * (K : ℝ)) ^ 2) using 1
    ext a
    ring
  · exact Eventually.of_forall fun t => Eventually.of_forall fun a => calc
      ‖q t a - D (f a) (g a)‖ ≤ ‖q t a‖ + ‖D (f a) (g a)‖ := norm_sub_le _ _
      _ ≤ (K : ℝ) * ‖g a‖ + (K : ℝ) * ‖g a‖ := add_le_add (hq t a)
        ((D (f a)).le_of_opNorm_le ((hFD _).le_of_lipschitz hF) _)
      _ = 2 * (K : ℝ) * ‖g a‖ := by ring
  · exact Eventually.of_forall fun a => by
      have hp := (((hasDerivAt_id (0 : ℝ)).smul_const (g a)).const_add (f a))
      simp only [id_eq, one_smul] at hp
      have hd := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by
        simpa only [zero_smul, add_zero] using hFD (f a)) hp
      change HasDerivAt (fun t : ℝ => F (f a + t • g a)) (D (f a) (g a)) 0 at hd
      simpa only [zero_add, zero_smul, add_zero] using
        (hasDerivAt_iff_tendsto_slope_zero.mp hd)

/-- The vector-input chain rule holds along every strongly differentiable
L2 path; no Frechet differentiability of the composition operator is assumed. -/
private theorem firstStrip_Lp_path_chain {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) (h0 : F 0 = 0)
    {D : E → E →L[ℝ] ℂ} (hD : Continuous D)
    (hFD : ∀ z, HasFDerivAt F (D z) z)
    {u : ℝ → Lp E 2 μ} {g : Lp E 2 μ} (hu : HasDerivAt u g 0) :
    HasDerivAt (fun t : ℝ => hF.compLp h0 (u t))
      ((firstStrip_memLp_differential μ hD (fun z => (hFD z).le_of_lipschitz hF)
        (u 0) g).toLp (fun a => D (u 0 a) (g a))) 0 := by
  let N := hF.compLp (p := (2 : ENNReal)) (μ := μ) h0
  let A (t : ℝ) := t⁻¹ • (N (u t) - N (u 0))
  let B (t : ℝ) := t⁻¹ • (N (u 0 + t • g) - N (u 0))
  have hB := firstStrip_Lp_affine_chain μ hF h0 hD hFD (u 0) g
  rw [hasDerivAt_iff_tendsto_slope_zero] at hu hB ⊢
  simp only [zero_add, zero_smul, add_zero] at hu hB ⊢
  change Tendsto B (𝓝[≠] (0 : ℝ)) _ at hB
  have hbound : ∀ t : ℝ, t ≠ 0 →
      ‖A t - B t‖ ≤ (K : ℝ) * ‖t⁻¹ • (u t - u 0) - g‖ := by
    intro t ht
    have he : t⁻¹ • (u t - (u 0 + t • g)) = t⁻¹ • (u t - u 0) - g := by
      rw [sub_add_eq_sub_sub, smul_sub, smul_smul, inv_mul_cancel₀ ht, one_smul]
    calc
      ‖A t - B t‖ = |t|⁻¹ * ‖N (u t) - N (u 0 + t • g)‖ := by
        dsimp only [A, B]
        rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_inv]
      _ ≤ |t|⁻¹ * ((K : ℝ) * ‖u t - (u 0 + t • g)‖) :=
        mul_le_mul_of_nonneg_left (hF.norm_compLp_sub_le h0 _ _) (inv_nonneg.mpr (abs_nonneg t))
      _ = (K : ℝ) * ‖t⁻¹ • (u t - u 0) - g‖ := by
        rw [← he, norm_smul, Real.norm_eq_abs, abs_inv, mul_left_comm]
  have hzero : Tendsto (fun t => ‖A t - B t‖) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg (A t - B t))
      (show ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖A t - B t‖ ≤
        (K : ℝ) * ‖t⁻¹ • (u t - u 0) - g‖ from
        by
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact hbound t ht)
    simpa only [sub_self, norm_zero, mul_zero] using (hu.sub_const g).norm.const_mul (K : ℝ)
  have hlim := (tendsto_zero_iff_norm_tendsto_zero.mpr hzero).add hB
  simpa only [A, sub_add_cancel, zero_add] using hlim

/-- A nonlinear function of the entire finite system commutes with actual
stationary translations, on a common almost-everywhere event. -/
private theorem firstStripSystem_translation_compLp {d n : ℕ}
    (Q : Measure (FieldPair d)) (hQ : IsStationary Q) (x : Vec d)
    {F : EuclideanSpace ℂ (Fin n) → ℂ} {K : ℝ≥0}
    (hF : LipschitzWith K F) (h0 : F 0 = 0) (f : Fin n → Lp ℂ 2 Q) :
    complexTranslation Q hQ x (hF.compLp h0 (firstStripSystemPack Q n f)) =
      hF.compLp h0 (firstStripSystemPack Q n (fun j => complexTranslation Q hQ x (f j))) := by
  apply Lp.ext
  have hc := (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae
    (hF.coeFn_compLp h0 (firstStripSystemPack Q n f))
  have hp := (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae
    (firstStripSystemPack_coe Q n f)
  have ht : ∀ᵐ ω ∂Q, ∀ j : Fin n,
      complexTranslation Q hQ x (f j) ω = f j (translate x ω) :=
    ae_all_iff.mpr fun j => coeFn_complexTranslation Q hQ x (f j)
  filter_upwards [coeFn_complexTranslation Q hQ x
      (hF.compLp h0 (firstStripSystemPack Q n f)), hc, hp, ht,
    hF.coeFn_compLp h0 (firstStripSystemPack Q n
      (fun j => complexTranslation Q hQ x (f j))),
    firstStripSystemPack_coe Q n (fun j => complexTranslation Q hQ x (f j))]
    with ω ha hb hc hd he hh
  simp only [Function.comp_apply] at *
  rw [ha, hb, hc, he, hh]
  congr 1
  ext j
  exact (hd j).symm

/-- A C1 Lipschitz nonlinear test of the full Euclidean system preserves the
actual stationary derivative domain. The derivative is the vector differential
on the packed horizontal derivative, rather than independent scalar tests. -/
private theorem firstStripSystem_horizontal_chain {d n : ℕ}
    {Q : Measure (FieldPair d)} {hQ : IsStationary Q} {i : Fin d}
    {f g : Fin n → Lp ℂ 2 Q}
    (hf : ∀ j, HasComplexHorizontalDerivative Q hQ i (f j) (g j))
    {F : EuclideanSpace ℂ (Fin n) → ℂ} {K : ℝ≥0}
    (hF : LipschitzWith K F) (h0 : F 0 = 0)
    {D : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ}
    (hD : Continuous D) (hFD : ∀ z, HasFDerivAt F (D z) z) :
    HasComplexHorizontalDerivative Q hQ i
      (hF.compLp h0 (firstStripSystemPack Q n f))
      ((firstStrip_memLp_differential Q hD (fun z => (hFD z).le_of_lipschitz hF)
        (firstStripSystemPack Q n f) (firstStripSystemPack Q n g)).toLp
          (fun ω => D (firstStripSystemPack Q n f ω) (firstStripSystemPack Q n g ω))) := by
  have ho : HasDerivAt
      (fun t : ℝ => firstStripSystemPack Q n
        (fun j => complexTranslation Q hQ (t • unitVector i) (f j)))
      (firstStripSystemPack Q n g) 0 := by
    apply ((firstStripSystemPack Q n).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    apply hasDerivAt_pi.mpr
    intro j
    simpa only [zero_smul, complexTranslation_zero] using (hf j).hasDerivAt_orbit 0
  have hc := firstStrip_Lp_path_chain Q hF h0 hD hFD ho
  simp only [zero_smul, complexTranslation_zero] at hc
  rw [hasDerivAt_iff_tendsto_slope_zero] at hc
  unfold HasComplexHorizontalDerivative
  simp only [← Complex.ofReal_inv, Complex.coe_smul]
  simp only [zero_add, zero_smul, complexTranslation_zero,
    ← firstStripSystem_translation_compLp] at hc
  exact hc

/-- The real differential of the shared-radius test on a Hilbert system. -/
private def firstStripHilbertRadialDifferential {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ε R a : ℝ) (z : E) : E →L[ℝ] E :=
  radialTruncationWeight ε R a (‖z‖ ^ 2) • ContinuousLinearMap.id ℝ E +
    ((2 * radialTruncationSlope ε R a (‖z‖ ^ 2)) • innerSL ℝ z).smulRight z

private theorem firstStripHilbertRadial_hasFDerivAt {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (z : E) :
    HasFDerivAt (fun w : E => radialTruncationWeight ε R a (‖w‖ ^ 2) • w)
      (firstStripHilbertRadialDifferential ε R a z) z := by
  have h := ((hasDerivAt_radialTruncationWeight (a := a) hε hR (sq_nonneg ‖z‖)).hasFDerivAt.comp z
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt).smul (hasFDerivAt_id z)
  apply h.congr_fderiv
  ext w
  simp only [firstStripHilbertRadialDifferential, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    innerSL_apply_apply, Function.comp_apply, id_eq, smul_eq_mul]
  module

private theorem firstStripHilbertRadialDifferential_continuous {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) :
    Continuous (firstStripHilbertRadialDifferential (E := E) ε R a) := by
  have hc := continuousOn_radialTruncationWeight_slope (a := a) hε hR
  have hw := hc.1.comp_continuous (continuous_norm.pow 2) (fun z : E => sq_nonneg ‖z‖)
  have hs := hc.2.comp_continuous (continuous_norm.pow 2) (fun z : E => sq_nonneg ‖z‖)
  exact (hw.smul continuous_const).add
    ((ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp
      (((continuous_const.mul hs).smul (innerSL ℝ).continuous).prodMk continuous_id))

/-- The coupled radial test belongs to the actual strong horizontal H1
domain, with its exact common-radius differential on every component. -/
private theorem firstStripSystem_radial_gradient {d n : ℕ}
    {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {f : Fin n → Lp ℂ 2 Q} {G : Fin n → Fin d → Lp ℂ 2 Q}
    (hf : ∀ q, HasComplexHorizontalGradient Q hQ (f q) (G q))
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    ∃ (V : Fin n → Lp ℂ 2 Q) (H : Fin n → Fin d → Lp ℂ 2 Q),
      (∀ q, HasComplexHorizontalGradient Q hQ (V q) (H q)) ∧
      (∀ q, V q =ᵐ[Q] fun ω =>
        radialTruncationWeight ε R a (∑ k : Fin n, ‖f k ω‖ ^ 2) • f q ω) ∧
      (∀ q j, H q j =ᵐ[Q] fun ω => firstStripSystemRadialDifferential
        (radialTruncationWeight ε R a (∑ k : Fin n, ‖f k ω‖ ^ 2))
        (radialTruncationSlope ε R a (∑ k : Fin n, ‖f k ω‖ ^ 2))
        (fun k => f k ω) (fun k l => G k l ω) q j) := by
  let E := EuclideanSpace ℂ (Fin n)
  let π (q : Fin n) : E →L[ℝ] ℂ :=
    (PiLp.proj 2 (fun _ : Fin n => ℂ) q : E →L[ℂ] ℂ).restrictScalars ℝ
  let W (z : E) := radialTruncationWeight ε R a (‖z‖ ^ 2) • z
  let D := firstStripHilbertRadialDifferential (E := E) ε R a
  have hW := firstStripHilbertRadial_lipschitz (E := E) hε hR ha
  have hD := firstStripHilbertRadialDifferential_continuous (E := E) (a := a) hε hR
  have hLip (q : Fin n) := (π q).lipschitzWith.comp hW
  have hzero (q : Fin n) : (fun z : E => π q (W z)) 0 = 0 := by
    simp only [W, smul_zero, map_zero]
  have hDc (q : Fin n) : Continuous (fun z => (π q).comp (D z)) :=
    hD.const_clm_comp (π q)
  have hFD (q : Fin n) (z : E) : HasFDerivAt (fun w => π q (W w))
      ((π q).comp (D z)) z :=
    (π q).hasFDerivAt.comp z (firstStripHilbertRadial_hasFDerivAt hε hR z)
  let V (q : Fin n) := (hLip q).compLp (hzero q) (firstStripSystemPack Q n f)
  let H (q : Fin n) (j : Fin d) :=
    (firstStrip_memLp_differential Q (hDc q)
      (fun z => (hFD q z).le_of_lipschitz (hLip q))
      (firstStripSystemPack Q n f) (firstStripSystemPack Q n (fun k => G k j))).toLp
        (fun ω => ((π q).comp (D (firstStripSystemPack Q n f ω)))
          (firstStripSystemPack Q n (fun k => G k j) ω))
  refine ⟨V, H, ?_, ?_, ?_⟩
  · intro q j
    exact firstStripSystem_horizontal_chain (fun k => hf k j)
      (hLip q) (hzero q) (hDc q) (hFD q)
  · intro q
    filter_upwards [(hLip q).coeFn_compLp (hzero q) (firstStripSystemPack Q n f),
      firstStripSystemPack_coe Q n f] with ω hv hp
    rw [hv]
    simp only [Function.comp_apply]
    rw [hp]
    change radialTruncationWeight ε R a
      (‖(WithLp.toLp 2 (fun k => f k ω) : EuclideanSpace ℂ (Fin n))‖ ^ 2) • f q ω = _
    rw [PiLp.norm_sq_eq_of_L2]
  · intro q j
    have hH := (firstStrip_memLp_differential Q (hDc q)
      (fun z => (hFD q z).le_of_lipschitz (hLip q))
      (firstStripSystemPack Q n f) (firstStripSystemPack Q n (fun k => G k j))).coeFn_toLp
    filter_upwards [hH, firstStripSystemPack_coe Q n f,
      firstStripSystemPack_coe Q n (fun k => G k j)] with ω hh hp hg
    rw [hh, hp, hg]
    change radialTruncationWeight ε R a
        (‖(WithLp.toLp 2 (fun k => f k ω) : EuclideanSpace ℂ (Fin n))‖ ^ 2) • G q j ω +
      (2 * radialTruncationSlope ε R a
        (‖(WithLp.toLp 2 (fun k => f k ω) : EuclideanSpace ℂ (Fin n))‖ ^ 2) *
          inner ℝ (WithLp.toLp 2 (fun k => f k ω) : EuclideanSpace ℂ (Fin n))
            (WithLp.toLp 2 (fun k => G k j ω))) • f q ω = _
    rw [PiLp.norm_sq_eq_of_L2, PiLp.inner_apply]
    rfl

/-- Compact spatial averaging supplies all the missing horizontal derivatives,
including when the unsmoothed class is only in L2. -/
private theorem firstStripKernelAverage_gradient {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (K : Vec d → ℝ)
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (firstStripKernelAverage Q K hK.continuous hKc f)
      (fun j => -firstStripKernelAverage Q (coordinateDerivative j K)
        ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hKc.fderiv_apply ℝ (unitVector j)) f) := by
  let ψ : SchwartzMap (Vec d) ℂ :=
    ((hKc.comp_homeomorph (Homeomorph.neg (Vec d))).comp_left
      (g := ((↑) : ℝ → ℂ)) (by simp)).toSchwartzMap
        (Complex.ofRealCLM.contDiff.comp (hK.comp contDiff_neg))
  have he : stationarySchwartzAverage Q ψ f =
      firstStripKernelAverage Q K hK.continuous hKc f := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by change (K (- -x) : ℂ) • _ = _; rw [neg_neg]
  intro j
  have hd := hasComplexHorizontalDerivative_schwartzAverage_main Q ψ f j
  rw [he] at hd
  convert hd using 1
  change -(∫ x, (coordinateDerivative j K x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) = _
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  have hder := (Complex.ofRealCLM.hasFDerivAt.comp (-x)
    (((hK.differentiable (by simp)).differentiableAt.hasFDerivAt).comp (-x)
      (hasFDerivAt_id (-x)).neg)).fderiv
  change -((coordinateDerivative j K x : ℂ) • _) =
    (fderiv ℝ (fun y : Vec d => (K (-y) : ℂ)) (-x) (unitVector j)) • _
  simp only [Function.comp_def, Pi.neg_apply, id_eq, neg_neg, Complex.ofRealCLM_apply] at hder
  rw [hder]
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply, map_neg, Complex.ofRealCLM_apply,
    coordinateDerivative, neg_smul]

/-- The actual endpoint and every actual gradient coordinate have one
space-time regularized radial H1 test. The field and its full horizontal jet
are identified on the same event before the nonlinear test is evaluated. -/
private theorem firstStrip_endpoint_regularized_radial_test {d : ℕ} (hd : 2 ≤ d)
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (ν : EndpointIndex d) (κ : ℝ → ℝ) (t : ℝ≥0) (u : ℝ)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    {ε R α : ℝ} (hε : 0 < ε) (hR : 0 < R) (hα : 0 ≤ α) :
    let F : Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := Fin.cons
      (firstStripTimeSmooth κ
        (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u)
      (fun j => firstStripTimeSmooth κ
        (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) t u)
    let J := fun q => firstStripKernelAverage Q K hK.continuous hKc (F q)
    let G := fun q j => -firstStripKernelAverage Q (coordinateDerivative j K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector j)) (F q)
    ∃ (V : Fin (d + 1) → Lp ℂ 2 (reducedLaw Q))
      (H : Fin (d + 1) → Fin d → Lp ℂ 2 (reducedLaw Q)),
      (∀ q, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (J q) (G q)) ∧
      (∀ q, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (V q) (H q)) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        (∀ q, J q ω = firstStripSpatialSmooth K
          (fun y => F q (translate y ω)) 0) ∧
        (∀ q j, G q j ω = -(∫ y, F q (translate y ω) *
          (coordinateDerivative j K y : ℂ))) ∧
        (∀ q j, G q j ω = fderiv ℝ (firstStripSpatialSmooth K
          (fun y => F q (translate y ω))) 0 (unitVector j)) ∧
        (∀ q, V q ω = radialTruncationWeight ε R α
          (∑ k : Fin (d + 1), ‖J k ω‖ ^ 2) • J q ω) ∧
        (∀ q j, H q j ω = firstStripSystemRadialDifferential
          (radialTruncationWeight ε R α (∑ k : Fin (d + 1), ‖J k ω‖ ^ 2))
          (radialTruncationSlope ε R α (∑ k : Fin (d + 1), ‖J k ω‖ ^ 2))
          (fun k => J k ω) (fun k l => G k l ω) q j) := by
  dsimp only
  let F : Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := Fin.cons
    (firstStripTimeSmooth κ
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u)
    (fun j => firstStripTimeSmooth κ
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) t u)
  have hJ := fun q => firstStripKernelAverage_gradient Q K hK hKc (F q)
  obtain ⟨V, H, hV, hval, hgrad⟩ := firstStripSystem_radial_gradient hJ hε hR hα
  refine ⟨V, H, hJ, hV, ?_⟩
  have hj := ae_all_iff.mpr fun q => firstStrip_kernel_integral_coe Q (F q) K hK.continuous hKc
  have hg := ae_all_iff.mpr fun q => ae_all_iff.mpr fun j =>
    (Lp.coeFn_neg (firstStripKernelAverage Q (coordinateDerivative j K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector j)) (F q))).trans
        ((firstStrip_kernel_integral_coe Q (F q) (coordinateDerivative j K)
          ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
          (hKc.fderiv_apply ℝ (unitVector j))).fun_comp Neg.neg)
  filter_upwards [hj, hg, firstStrip_coefficient_orbit_locallyIntegrable Q F,
    ae_all_iff.mpr hval,
    ae_all_iff.mpr (fun q => ae_all_iff.mpr (hgrad q))] with ω hj hg hl hv hh
  refine ⟨?_, hg, ?_, hv, hh⟩
  · intro q
    change (∫ y, (K y : ℂ) • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y (F q)) ω =
        firstStripSpatialSmooth K (fun y => F q (translate y ω)) 0
    simpa only [firstStripSpatialSmooth, sub_zero] using hj q
  · intro q j
    have hloc : LocallyIntegrable (fun y => F q (translate y ω)) volume := by
      simpa only [Complex.ofReal_one, mul_one] using hl q (fun _ => 1) continuous_const
    rw [hg q j]
    symm
    simpa only [F, Function.comp_apply, sub_zero] using
      firstStripSpatialSmooth_fderiv K hK hKc hloc 0 j

/-- The same spatially regularized actual system used for the H1 test has
the exact coupled energy identity. Both regularizations act on every component,
and only the common time kernel is differentiated. -/
private theorem firstStrip_endpoint_space_time_energy_FTC {d : ℕ} (hd : 2 ≤ d)
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    (K : Vec d → ℝ) (hK : Continuous K) (hKc : HasCompactSupport K)
    (t : ℝ≥0) (u₀ u₁ : ℝ) {ε R α : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hα : 0 ≤ α) :
    let J : (ℝ → ℝ) → ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) :=
      fun κ u q => firstStripKernelAverage Q K hK hKc (Fin.cons
        (firstStripTimeSmooth κ
          (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u)
        (fun j => firstStripTimeSmooth κ
          (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) t u)
          (α := fun _ : Fin (d + 1) => Lp ℂ 2 (reducedLaw Q)) q)
    (∫ u in u₀..u₁, ∫ ω, ∑ q : Fin (d + 1),
      inner ℝ (radialTruncationWeight ε R α
        (∑ k : Fin (d + 1), ‖J κ u k ω‖ ^ 2) • J κ u q ω)
          (J (deriv κ) u q ω) ∂reducedLaw Q) =
      (∫ ω, firstStripHilbertPrimitive ε R α
        (WithLp.toLp 2 (fun q => J κ u₁ q ω) : EuclideanSpace ℂ (Fin (d + 1)))
          ∂reducedLaw Q) -
      ∫ ω, firstStripHilbertPrimitive ε R α
        (WithLp.toLp 2 (fun q => J κ u₀ q ω) : EuclideanSpace ℂ (Fin (d + 1)))
          ∂reducedLaw Q := by
  dsimp only
  let A := firstStripKernelAverage Q K hK hKc
  apply firstStripSystem_energy_FTC ?_ ?_ hε hR hα u₀ u₁
  · intro u
    apply hasDerivAt_pi.mpr
    intro q
    apply (A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    refine Fin.cases ?_ (fun j => ?_) q
    · exact (firstStrip_endpoint_time_regularization hd Q β a μ ζ P T hP hT ν
        κ hκ hκc t).2 u
    · exact (firstStripTimeGradient_coordinate_regularization hd Q β a μ ζ P T hP hT ν
        κ hκ hκc t j).2 u
  · have hκ' : ContDiff ℝ (⊤ : ℕ∞) (deriv κ) := hκ.deriv'
    apply continuous_pi
    intro q
    apply A.continuous.comp
    refine Fin.cases ?_ (fun j => ?_) q
    · exact (firstStrip_endpoint_time_regularization hd Q β a μ ζ P T hP hT ν
        (deriv κ) hκ' hκc.deriv t).1.continuous
    · exact (firstStripTimeGradient_coordinate_regularization hd Q β a μ ζ P T hP hT ν
        (deriv κ) hκ' hκc.deriv t j).1.continuous

/- Multiplication by an actual coefficient jet preserves the strong horizontal
L² domain. The difference quotient is controlled by the next actual jet. -/
private theorem firstStrip_coefficient_jet_product {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (j k : Fin d) (cs : List (Fin d))
    (M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hM : ∀ f : Lp ℂ 2 (reducedLaw Q), M f =ᵐ[reducedLaw Q] fun ω =>
      (iteratedHorizontalDerivative cs (fun η : FieldPair d => η.1 0 j k) ω : ℂ) * f ω)
    (i : Fin d) (v V : Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) i v V) :
    ∃ H : Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) i (M v) H ∧
      H =ᵐ[reducedLaw Q] fun ω =>
        (iteratedHorizontalDerivative cs (fun η : FieldPair d => η.1 0 j k) ω : ℂ) * V ω +
        (iteratedHorizontalDerivative (i :: cs) (fun η : FieldPair d => η.1 0 j k) ω : ℂ) * v ω := by
  classical
  have : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let c := iteratedHorizontalDerivative cs (fun η : FieldPair d => η.1 0 j k)
  let μ := reducedLaw Q
  let T := complexTranslation μ (reducedLaw_stationary Q)
  let A (t : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    (T (t • unitVector i)).toContinuousLinearMap.comp
      (M.comp (T (-(t • unitVector i))).toContinuousLinearMap)
  have hAe (t : ℝ) (f : Lp ℂ 2 μ) : A t f =ᵐ[μ] fun ω =>
      (c (translate (t • unitVector i) ω) : ℂ) * f ω := by
    have hm := (measurePreserving_translate μ (reducedLaw_stationary Q) (t • unitVector i)).quasiMeasurePreserving
    have hc := hm.ae (hM (T (-(t • unitVector i)) f))
    have ht := hm.ae (coeFn_complexTranslation μ (reducedLaw_stationary Q)
      (-(t • unitVector i)) f)
    filter_upwards [coeFn_complexTranslation μ (reducedLaw_stationary Q)
      (t • unitVector i) (M (T (-(t • unitVector i)) f)), hc, ht] with ω h1 h2 h3
    change (M (T (-(t • unitVector i)) f)) (translate (t • unitVector i) ω) =
      (c (translate (t • unitVector i) ω) : ℂ) *
        (T (-(t • unitVector i)) f) (translate (t • unitVector i) ω) at h2
    change (T (-(t • unitVector i)) f) (translate (t • unitVector i) ω) =
      f (translate (-(t • unitVector i)) (translate (t • unitVector i) ω)) at h3
    change T (t • unitVector i) (M (T (-(t • unitVector i)) f)) ω = _
    rw [h1, h2, h3]
    simp only [translate_add, neg_add_cancel, translate_zero]
  have hA0 (f : Lp ℂ 2 μ) : A 0 f = M f := by
    simp only [A, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      zero_smul, neg_zero, complexTranslation_zero, T]
  have hAn (t : ℝ) (f : Lp ℂ 2 μ) :
      ‖A t f‖ ≤ ‖M‖ * ‖f‖ := by
    change ‖T _ (M (T _ f))‖ ≤ _
    rw [norm_complexTranslation]
    exact (M.le_opNorm _).trans_eq (by rw [norm_complexTranslation])
  have hAc (f : Lp ℂ 2 μ) : Continuous (fun t : ℝ => A t f) := by
    have hx : Continuous (fun t : ℝ => t • unitVector i) :=
      continuous_id.smul continuous_const
    have hi := (continuous_complexTranslation μ (reducedLaw_stationary Q)).comp
      (hx.neg.prodMk (continuous_const : Continuous (fun _ : ℝ => f)))
    exact (continuous_complexTranslation μ (reducedLaw_stationary Q)).comp
      (hx.prodMk (M.continuous.comp hi))
  let dc : FieldPair d → ℝ :=
    iteratedHorizontalDerivative (i :: cs) (fun ω : FieldPair d => ω.1 0 j k)
  have hdcm : MemLp (fun ω => (dc ω : ℂ)) ∞ μ :=
    Complex.ofRealCLM.comp_memLp' (timeFlux_coefficient_jets_memLp_top hQ j k (i :: cs))
  have hRmem : MemLp (fun ω => (dc ω : ℂ) * v ω) 2 μ :=
    hdcm.fun_mul (Lp.memLp v)
  let R : Lp ℂ 2 μ := hRmem.toLp (fun ω => (dc ω : ℂ) * v ω)
  obtain ⟨B, hB, hb⟩ := timeFlux_coefficient_jets_orbit_bounds hQ j k
  obtain ⟨S, _, hs⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  have hcurve : ∀ᵐ ω ∂μ, ∀ s : ℝ,
      HasDerivAt (fun t : ℝ => c (translate (t • unitVector i) ω))
        (dc (translate (s • unitVector i) ω)) s := by
    filter_upwards [hs Q hQ] with ω hω s
    have horbit : orbit c ω = coordinateIterate cs (fun y => ω.1 y j k) := by
      rw [orbit_iteratedHorizontalDerivative]
      congr 1
      funext y
      simp only [orbit, translate_matrix, add_zero]
    have hc : ContDiff ℝ (⊤ : ℕ∞) (orbit c ω) := by
      rw [horbit]
      exact contDiff_coordinateIterate (hω.1.1 j k) cs
    have hd := (hc.differentiable (by simp) (s • unitVector i)).hasFDerivAt.comp_hasDerivAt
      s ((hasDerivAt_id' s).smul_const (unitVector i))
    change HasDerivAt (fun t => orbit c ω (t • unitVector i))
      (horizontalDerivative i c (translate (s • unitVector i) ω)) s
    rw [horizontalDerivative_translate]
    simpa only [Function.comp_def, one_smul, coordinateDerivative] using hd
  have hbound : ∀ᵐ ω ∂μ, ∀ x : Vec d, |dc (translate x ω)| ≤ B (i :: cs) :=
    hb (i :: cs)
  let q (t : ℝ) (ω : FieldPair d) : ℂ :=
    ((t⁻¹ * (c (translate (t • unitVector i) ω) - c ω) : ℝ) : ℂ) * v ω
  have hqbound (t : ℝ) (ht : t ≠ 0) : ∀ᵐ ω ∂μ,
      ‖q t ω‖ ≤ B (i :: cs) * ‖v ω‖ := by
    filter_upwards [hcurve, hbound] with ω hd hbω
    have hl : ‖c (translate (t • unitVector i) ω) - c ω‖ ≤ B (i :: cs) * ‖t‖ := by
      simpa only [zero_smul, translate_zero, sub_zero] using
        Convex.norm_image_sub_le_of_norm_deriv_le
          (fun s _ => (hd s).differentiableAt)
          (fun s _ => by rw [(hd s).deriv]; exact hbω _)
          convex_univ (mem_univ 0) (mem_univ t)
    have hq : |t⁻¹ * (c (translate (t • unitVector i) ω) - c ω)| ≤ B (i :: cs) := by
      rw [abs_mul, abs_inv, inv_mul_le_iff₀ (abs_pos.mpr ht), mul_comm]
      exact hl
    simpa only [q, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul] using
      mul_le_mul_of_nonneg_right hq (norm_nonneg (v ω))
  have hR : Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (A t v - M v))
      (𝓝[≠] (0 : ℝ)) (𝓝 R) := by
    apply tendsto_complexLp_of_dominated
      (F := q) (f := fun ω => (dc ω : ℂ) * v ω)
      (b := fun ω => 2 * B (i :: cs) * ‖v ω‖)
    · intro t
      filter_upwards [Lp.coeFn_smul (t : ℂ)⁻¹ (A t v - M v),
        Lp.coeFn_sub (A t v) (M v), hAe t v, hM v]
        with ω h1 h2 h3 h4
      change M v ω = _ at h4
      simp only [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4, smul_eq_mul,
        q, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sub]
      ring
    · exact hRmem.coeFn_toLp
    · convert ((Lp.memLp v).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul
        ((2 * B (i :: cs)) ^ 2) using 1
      simp only [mul_pow]
    · filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards [hqbound t ht, hbound] with ω hq hbω
      have hd : |dc ω| ≤ B (i :: cs) := by simpa only [translate_zero] using hbω 0
      calc
        ‖q t ω - (dc ω : ℂ) * v ω‖ ≤ ‖q t ω‖ + ‖(dc ω : ℂ) * v ω‖ := norm_sub_le _ _
        _ ≤ B (i :: cs) * ‖v ω‖ + B (i :: cs) * ‖v ω‖ := by
          gcongr
          simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_right hd (norm_nonneg (v ω))
        _ = _ := by ring
    · filter_upwards [hcurve] with ω hω
      have hd := (hω 0).tendsto_slope_zero
      simp only [zero_smul, translate_zero, zero_add, smul_eq_mul] at hd
      exact ((Complex.continuous_ofReal.tendsto _).comp hd).mul_const (v ω)
  have hfirst : Tendsto (fun t : ℝ =>
      A t ((t : ℂ)⁻¹ • (T (t • unitVector i) v - v)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (M V)) := by
    have hz : Tendsto (fun t : ℝ =>
        A t ((t : ℂ)⁻¹ • (T (t • unitVector i) v - v) - V))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _)
        (Filter.Eventually.of_forall fun t => hAn t _)
      simpa only [mul_zero] using
        ((tendsto_iff_norm_sub_tendsto_zero.mp hV).const_mul ‖M‖)
    have hc : Tendsto (fun t : ℝ => A t V) (𝓝[≠] (0 : ℝ)) (𝓝 (A 0 V)) :=
      ((hAc V).tendsto 0).mono_left nhdsWithin_le_nhds
    rw [hA0] at hc
    convert hz.add hc using 1
    · funext t
      rw [map_sub, sub_add_cancel]
    · simp only [zero_add]
  refine ⟨M V + R, ?_, ?_⟩
  · have hl := hfirst.add hR
    apply hl.congr'
    exact Filter.Eventually.of_forall fun t => by
      change A t ((t : ℂ)⁻¹ • (T (t • unitVector i) v - v)) +
        (t : ℂ)⁻¹ • (A t v - M v) = (t : ℂ)⁻¹ • (T (t • unitVector i) (M v) - M v)
      rw [map_smul, map_sub]
      have he : A t (T (t • unitVector i) v) = T (t • unitVector i) (M v) := by
        change T _ (M (T _ (T _ v))) = _
        rw [complexTranslation_neg_cancel]
      rw [he]
      module
  · filter_upwards [Lp.coeFn_add (M V) R, hM V,
      hRmem.coeFn_toLp] with ω h1 h2 h3
    change M V ω = _ at h2
    change R ω = _ at h3
    simp only [h1, Pi.add_apply, h2, h3, dc]

/-- The actual observable jet is the corresponding spatial jet at the origin. -/
private theorem firstStrip_coefficient_jet_eq {d : ℕ} (j k : Fin d)
    (cs : List (Fin d)) (ω : FieldPair d) :
    iteratedHorizontalDerivative cs (fun η : FieldPair d => η.1 0 j k) ω =
      coordinateIterate cs (fun x => ω.1 x j k) 0 := by
  have h := congrFun (orbit_iteratedHorizontalDerivative cs
    (fun η : FieldPair d => η.1 0 j k) ω) 0
  have he : orbit (fun η : FieldPair d => η.1 0 j k) ω = (fun x => ω.1 x j k) := by
    funext x
    simp only [orbit, translate_matrix, add_zero]
  rw [he] at h
  simpa only [orbit, translate_zero] using h

/-- The derivative-coefficient flux is expanded before testing: the test's
horizontal derivative disappears, leaving only first and second actual
coefficient jets and the first derivative of the smoothed field. -/
private theorem firstStrip_smoothed_derivative_flux_pairing {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (j k l i : Fin d)
    (M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hM : ∀ f : Lp ℂ 2 (reducedLaw Q), M f =ᵐ[reducedLaw Q] fun ω =>
      (coordinateDerivative l (fun x => ω.1 x j k) 0 : ℂ) * f ω)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (f w W : Lp ℂ 2 (reducedLaw Q))
    (hw : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) i w W) :
    let v := firstStripKernelAverage Q K hK.continuous hKc f
    let G := -firstStripKernelAverage Q (coordinateDerivative i K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector i)) f
    let F : FieldPair d → ℂ := fun ω =>
      (coordinateDerivative l (fun x => ω.1 x j k) 0 : ℂ) * G ω +
      (coordinateDerivative i (coordinateDerivative l (fun x => ω.1 x j k)) 0 : ℂ) * v ω
    Integrable (fun ω => star (w ω) * F ω) (reducedLaw Q) ∧
      Integrable (fun ω => star (W ω) *
        ((coordinateDerivative l (fun x => ω.1 x j k) 0 : ℂ) * v ω)) (reducedLaw Q) ∧
      (∫ ω, star (w ω) * F ω ∂reducedLaw Q) =
        -(∫ ω, star (W ω) *
          ((coordinateDerivative l (fun x => ω.1 x j k) 0 : ℂ) * v ω) ∂reducedLaw Q) := by
  classical
  dsimp only
  let v := firstStripKernelAverage Q K hK.continuous hKc f
  let G := -firstStripKernelAverage Q (coordinateDerivative i K)
    ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hKc.fderiv_apply ℝ (unitVector i)) f
  have hM' (u : Lp ℂ 2 (reducedLaw Q)) : M u =ᵐ[reducedLaw Q] fun ω =>
      (iteratedHorizontalDerivative [l] (fun η : FieldPair d => η.1 0 j k) ω : ℂ) * u ω := by
    simpa only [firstStrip_coefficient_jet_eq, coordinateIterate] using hM u
  obtain ⟨H, hH, hHe⟩ := firstStrip_coefficient_jet_product Q hQ j k [l] M hM' i v G
    (firstStripKernelAverage_gradient Q K hK hKc f i)
  have hF : H =ᵐ[reducedLaw Q] fun ω =>
      (coordinateDerivative l (fun x => ω.1 x j k) 0 : ℂ) * G ω +
      (coordinateDerivative i (coordinateDerivative l (fun x => ω.1 x j k)) 0 : ℂ) * v ω := by
    simpa only [firstStrip_coefficient_jet_eq, coordinateIterate] using hHe
  have hi := complexHorizontalDerivatives_integration_by_parts hH hw.star
  have hleft : (fun ω => H ω * (star w) ω) =ᵐ[reducedLaw Q] fun ω => star (w ω) *
      ((coordinateDerivative l (fun x => ω.1 x j k) 0 : ℂ) * G ω +
        (coordinateDerivative i (coordinateDerivative l (fun x => ω.1 x j k)) 0 : ℂ) * v ω) := by
    filter_upwards [hF, Lp.coeFn_star w] with ω h1 h2
    rw [h1, h2]
    exact mul_comm _ _
  have hright : (fun ω => M v ω * (star W) ω) =ᵐ[reducedLaw Q] fun ω => star (W ω) *
      ((coordinateDerivative l (fun x => ω.1 x j k) 0 : ℂ) * v ω) := by
    filter_upwards [hM v, Lp.coeFn_star W] with ω h1 h2
    rw [h1, h2]
    exact mul_comm _ _
  refine ⟨hi.1.congr hleft, hi.2.1.congr hright, ?_⟩
  rw [← integral_congr_ae hleft, ← integral_congr_ae hright]
  exact hi.2.2

/-- The two kernel derivatives in the actual PDE represent strong L2 classes. -/
private theorem firstStripKernelAverage_spatial_jet_coe {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (K : Vec d → ℝ)
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (f : Lp ℂ 2 (reducedLaw Q)) (l j : Fin d) :
    let Dl := coordinateDerivative l K
    let hDl : ContDiff ℝ (⊤ : ℕ∞) Dl :=
      (hK.fderiv_right (by simp)).clm_apply contDiff_const
    let hDlc := hKc.fderiv_apply ℝ (unitVector l)
    ∀ᵐ ω ∂reducedLaw Q,
      (firstStripKernelAverage Q K hK.continuous hKc f ω =
        firstStripSpatialSmooth K (fun y => f (translate y ω)) 0) ∧
      (firstStripKernelAverage Q Dl hDl.continuous hDlc f ω =
        -fderiv ℝ (firstStripSpatialSmooth K (fun y => f (translate y ω))) 0 (unitVector l)) ∧
      (firstStripKernelAverage Q (coordinateDerivative j Dl)
        ((hDl.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hDlc.fderiv_apply ℝ (unitVector j)) f ω =
        fderiv ℝ (fun x => fderiv ℝ
          (firstStripSpatialSmooth K (fun y => f (translate y ω))) x (unitVector l))
          0 (unitVector j)) := by
  dsimp only
  have hDl : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative l K) :=
    (hK.fderiv_right (by simp)).clm_apply contDiff_const
  filter_upwards [firstStrip_kernel_integral_coe Q f K hK.continuous hKc,
    firstStrip_kernel_integral_coe Q f (coordinateDerivative l K) hDl.continuous
      (hKc.fderiv_apply ℝ (unitVector l)),
    firstStrip_kernel_integral_coe Q f (coordinateDerivative j (coordinateDerivative l K))
      ((hDl.continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hKc.fderiv_apply ℝ (unitVector l)).fderiv_apply ℝ (unitVector j)),
    firstStrip_coefficient_orbit_locallyIntegrable Q (fun _ : Fin 1 => f)]
      with ω hv h1 h2 hl
  have hloc : LocallyIntegrable (fun y => f (translate y ω)) volume := by
    simpa only [Complex.ofReal_one, mul_one] using hl 0 (fun _ => 1) continuous_const
  refine ⟨?_, ?_, ?_⟩
  · change (∫ x, (K x : ℂ) • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) x f) ω = _
    simpa only [firstStripSpatialSmooth, sub_zero] using hv
  · rw [firstStripSpatialSmooth_fderiv K hK hKc hloc 0 l, neg_neg]
    change (∫ x, (coordinateDerivative l K x : ℂ) • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) x f) ω = _
    simpa only [sub_zero] using h1
  · rw [firstStripSpatialSmooth_second_fderiv K hK hKc hloc 0 l j]
    change (∫ x, (coordinateDerivative j (coordinateDerivative l K) x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) ω = _
    simpa only [sub_zero] using h2

/-- Actual L2 coefficient fluxes have the physical representatives in the
space-time PDE on a common full-measure event. -/
private theorem firstStrip_flux_orbit {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Lp ℂ 2 (reducedLaw Q))
    (H : Fin d → Lp ℂ 2 (reducedLaw Q)) (i : Fin d) (τ : ℂ) :
    let F := fun j => (∑ k, complexCoefficientMul Q j k (H k)) -
      τ • complexCoefficientMul Q j i U
    let B := ∑ j, complexCoefficientMul Q j i (H j)
    ∀ᵐ ω ∂reducedLaw Q,
      (∀ j, (fun y => F j (translate y ω)) =ᵐ[volume] fun y =>
        (∑ k, (ω.1 y j k : ℂ) * H k (translate y ω)) -
          τ * ((ω.1 y j i : ℂ) * U (translate y ω))) ∧
      ((fun y => B (translate y ω)) =ᵐ[volume] fun y =>
        ∑ j, (ω.1 y j i : ℂ) * H j (translate y ω)) := by
  classical
  dsimp only
  let F := fun j => (∑ k, complexCoefficientMul Q j k (H k)) -
    τ • complexCoefficientMul Q j i U
  let B := ∑ j, complexCoefficientMul Q j i (H j)
  have hc (j k : Fin d) : Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable
  have hF (j : Fin d) : F j =ᵐ[reducedLaw Q] fun ω =>
      (∑ k, (ω.1 0 j k : ℂ) * H k ω) - τ * ((ω.1 0 j i : ℂ) * U ω) := by
    filter_upwards [firstStrip_sum_ae (reducedLaw Q) Finset.univ
      (fun k => complexCoefficientMul Q j k (H k)),
      ae_all_iff.mpr (fun k => complexCoefficientMul_coe Q j k (H k)),
      Lp.coeFn_sub (∑ k, complexCoefficientMul Q j k (H k))
        (τ • complexCoefficientMul Q j i U),
      Lp.coeFn_smul τ (complexCoefficientMul Q j i U), complexCoefficientMul_coe Q j i U]
        with ω hs ha hsub hsmul hu
    change F j ω = _
    simp only [F, hsub, Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul, hs, hu]
    congr 1
    exact Finset.sum_congr rfl (fun k _ => ha k)
  have hB : B =ᵐ[reducedLaw Q] fun ω => ∑ j, (ω.1 0 j i : ℂ) * H j ω := by
    filter_upwards [firstStrip_sum_ae (reducedLaw Q) Finset.univ
      (fun j => complexCoefficientMul Q j i (H j)),
      ae_all_iff.mpr (fun j => complexCoefficientMul_coe Q j i (H j))] with ω hs ha
    rw [hs]
    exact Finset.sum_congr rfl (fun j _ => ha j)
  have hFo (j : Fin d) := ae_complex_spatial_orbit_congr (reducedLaw Q)
    (reducedLaw_stationary Q) (Lp.stronglyMeasurable (F j)).measurable
    ((Finset.measurable_sum Finset.univ (fun k _ => (hc j k).mul
      (Lp.stronglyMeasurable (H k)).measurable)).sub
        (((hc j i).mul (Lp.stronglyMeasurable U).measurable).const_mul τ)) (hF j)
  have hBo := ae_complex_spatial_orbit_congr (reducedLaw Q)
    (reducedLaw_stationary Q) (Lp.stronglyMeasurable B).measurable
    (Finset.measurable_sum Finset.univ (fun j _ =>
      (hc j i).mul (Lp.stronglyMeasurable (H j)).measurable)) hB
  filter_upwards [ae_all_iff.mpr hFo, hBo] with ω hf hb
  constructor
  · intro j
    filter_upwards [hf j] with y hy
    change F j (translate y ω) = _
    simpa only [Finset.sum_apply, Pi.sub_apply, Pi.mul_apply, translate_matrix, add_zero] using hy
  · filter_upwards [hb] with y hy
    change B (translate y ω) = _
    simpa only [Finset.sum_apply, Pi.mul_apply, translate_matrix, add_zero] using hy

/-- The differentiated actual endpoint equation is an identity of strong L2
classes after the common space-time smoothing. No strong derivative of the
unsmoothed gradient appears in the identity. -/
private theorem firstStrip_endpoint_space_time_L2_equation {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (t : ℝ≥0) (u : ℝ) (hzero : κ u = 0) (ht : κ (u - t) = 0)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (l : Fin d) :
    let U := firstStripTimeSmooth κ
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
    let H := fun k => firstStripTimeSmooth κ
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
    let V := firstStripTimeSmooth (deriv κ)
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s l) t u
    let F := fun j => (∑ k, complexCoefficientMul Q j k (H k)) -
      (if ν = .inr true then 2 * ζ else 0) •
        complexCoefficientMul Q j ⟨0, by omega⟩ U
    let B := ∑ j, complexCoefficientMul Q j ⟨0, by omega⟩ (H j)
    let Dl := coordinateDerivative l K
    let hDl : ContDiff ℝ (⊤ : ℕ∞) Dl :=
      (hK.fderiv_right (by simp)).clm_apply contDiff_const
    let hDlc := hKc.fderiv_apply ℝ (unitVector l)
    firstStripKernelAverage Q K hK.continuous hKc V =
      (1 / 2 : ℂ) • (∑ j, firstStripKernelAverage Q (coordinateDerivative j Dl)
        ((hDl.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hDlc.fderiv_apply ℝ (unitVector j)) (F j)) -
      (if ν = .inr true then 0 else ζ) •
        firstStripKernelAverage Q Dl hDl.continuous hDlc B := by
  classical
  let U := firstStripTimeSmooth κ
    (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
  let H := fun k => firstStripTimeSmooth κ
    (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
  let V := firstStripTimeSmooth (deriv κ)
    (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s l) t u
  let τ : ℂ := if ν = .inr true then 2 * ζ else 0
  let zforce : ℂ := if ν = .inr true then 0 else ζ
  let F := fun j => (∑ k, complexCoefficientMul Q j k (H k)) -
    τ • complexCoefficientMul Q j ⟨0, by omega⟩ U
  let B := ∑ j, complexCoefficientMul Q j ⟨0, by omega⟩ (H j)
  let Dl := coordinateDerivative l K
  have hDl : ContDiff ℝ (⊤ : ℕ∞) Dl :=
    (hK.fderiv_right (by simp)).clm_apply contDiff_const
  let hDlc := hKc.fderiv_apply ℝ (unitVector l)
  let A0 := firstStripKernelAverage Q K hK.continuous hKc
  let A1 := firstStripKernelAverage Q Dl hDl.continuous hDlc
  let A2 := fun j => firstStripKernelAverage Q (coordinateDerivative j Dl)
    ((hDl.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hDlc.fderiv_apply ℝ (unitVector j))
  change A0 V = (1 / 2 : ℂ) • (∑ j, A2 j (F j)) - zforce • A1 B
  apply Lp.ext
  filter_upwards [firstStrip_endpoint_space_time_equation hd D Q hQ β a μ ζ P T
    hP hT ν κ hκ t u hzero ht,
    firstStrip_flux_orbit Q U H ⟨0, by omega⟩ τ,
    firstStripKernelAverage_spatial_jet_coe Q K hK hKc V l l,
    ae_all_iff.mpr (fun j => firstStripKernelAverage_spatial_jet_coe Q K hK hKc (F j) l j),
    firstStripKernelAverage_spatial_jet_coe Q K hK hKc B l l,
    firstStrip_sum_ae (reducedLaw Q) Finset.univ (fun j => A2 j (F j)),
    Lp.coeFn_sub ((1 / 2 : ℂ) • (∑ j, A2 j (F j))) (zforce • A1 B),
    Lp.coeFn_smul (1 / 2 : ℂ) (∑ j, A2 j (F j)), Lp.coeFn_smul zforce (A1 B)]
      with ω he hf hv hfs hb hs hsub hc hz
  have hsmF (j : Fin d) :
      firstStripSpatialSmooth K (fun y => F j (translate y ω)) =
        firstStripSpatialSmooth K (fun y => (∑ k, (ω.1 y j k : ℂ) * H k (translate y ω)) -
          τ * ((ω.1 y j ⟨0, by omega⟩ : ℂ) * U (translate y ω))) := by
    funext x
    apply integral_congr_ae
    filter_upwards [hf.1 j] with y hy
    rw [hy]
  have hsmB : firstStripSpatialSmooth K (fun y => B (translate y ω)) =
      firstStripSpatialSmooth K (fun y => ∑ j, (ω.1 y j ⟨0, by omega⟩ : ℂ) *
        H j (translate y ω)) := by
    funext x
    apply integral_congr_ae
    filter_upwards [hf.2] with y hy
    rw [hy]
  have hw := he K hK hKc 0 l
  change firstStripSpatialSmooth K (fun y => V (translate y ω)) 0 =
    (1 / 2 : ℂ) * (∑ j, fderiv ℝ (fun x => fderiv ℝ
      (firstStripSpatialSmooth K (fun y => (∑ k, (ω.1 y j k : ℂ) * H k (translate y ω)) -
        τ * ((ω.1 y j ⟨0, by omega⟩ : ℂ) * U (translate y ω)))) x (unitVector l))
      0 (unitVector j)) +
    zforce * fderiv ℝ (firstStripSpatialSmooth K (fun y =>
      ∑ j, (ω.1 y j ⟨0, by omega⟩ : ℂ) * H j (translate y ω))) 0 (unitVector l) at hw
  simp_rw [← hsmF, ← hsmB] at hw
  rw [hsub]
  simp only [Pi.sub_apply, hc, hz, Pi.smul_apply, smul_eq_mul, hs]
  change A0 V ω = (1 / 2 : ℂ) * (∑ j, A2 j (F j) ω) - zforce * A1 B ω
  rw [hv.1]
  have hsum : (∑ j, A2 j (F j) ω) = ∑ j, fderiv ℝ
      (fun x => fderiv ℝ (firstStripSpatialSmooth K (fun y => F j (translate y ω)))
        x (unitVector l)) 0 (unitVector j) :=
    Finset.sum_congr rfl (fun j _ => (hfs j).2.2)
  rw [hsum, hb.2.1]
  linear_combination hw

/-- The actual smoothed gradient equation accepts every strong H1 test,
including the shared-radius radial test, with only first kernel derivatives
on the flux side. -/
private theorem firstStrip_endpoint_space_time_weak_L2 {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (t : ℝ≥0) (u : ℝ) (hzero : κ u = 0) (ht : κ (u - t) = 0)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (l : Fin d) (w : Lp ℂ 2 (reducedLaw Q)) (W : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hW : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) w W) :
    let U := firstStripTimeSmooth κ
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
    let H := fun k => firstStripTimeSmooth κ
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
    let V := firstStripTimeSmooth (deriv κ)
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s l) t u
    let F := fun j => (∑ k, complexCoefficientMul Q j k (H k)) -
      (if ν = .inr true then 2 * ζ else 0) •
        complexCoefficientMul Q j ⟨0, by omega⟩ U
    let B := ∑ j, complexCoefficientMul Q j ⟨0, by omega⟩ (H j)
    let Dl := coordinateDerivative l K
    let hDl : ContDiff ℝ (⊤ : ℕ∞) Dl :=
      (hK.fderiv_right (by simp)).clm_apply contDiff_const
    let hDlc := hKc.fderiv_apply ℝ (unitVector l)
    inner ℂ w (firstStripKernelAverage Q K hK.continuous hKc V) =
      (1 / 2 : ℂ) * (∑ j, inner ℂ (W j)
        (firstStripKernelAverage Q Dl hDl.continuous hDlc (F j))) -
      (if ν = .inr true then 0 else ζ) * inner ℂ w
        (firstStripKernelAverage Q Dl hDl.continuous hDlc B) := by
  classical
  have he := firstStrip_endpoint_space_time_L2_equation hd D Q hQ β a μ ζ P T hP hT ν
    κ hκ t u hzero ht K hK hKc l
  dsimp only at he ⊢
  rw [he, inner_sub_right, inner_smul_right, inner_smul_right, inner_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hDl : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative l K) :=
    (hK.fderiv_right (by simp)).clm_apply contDiff_const
  let U := firstStripTimeSmooth κ
    (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
  let H := fun k => firstStripTimeSmooth κ
    (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
  let Fj := (∑ k, complexCoefficientMul Q j k (H k)) -
    (if ν = .inr true then 2 * ζ else 0) •
      complexCoefficientMul Q j ⟨0, by omega⟩ U
  have hh := (hW j).inner_eq_neg (firstStripKernelAverage_gradient Q
    (coordinateDerivative l K) hDl (hKc.fderiv_apply ℝ (unitVector l)) Fj j)
  simpa only [inner_neg_right, neg_neg] using hh.symm

/-- Spatial smoothing preserves the actual horizontal gradient and its
zero-curl identity, without assuming second derivatives of the raw field. -/
private theorem firstStripKernelAverage_gradient_curl {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K) :
    let A := firstStripKernelAverage Q K hK.continuous hKc
    let B := fun l => firstStripKernelAverage Q (coordinateDerivative l K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector l))
    (∀ l, -(B l f) = A (G l)) ∧ ∀ k l, B l (G k) = B k (G l) := by
  dsimp only
  let A := firstStripKernelAverage Q K hK.continuous hKc
  let B := fun l => firstStripKernelAverage Q (coordinateDerivative l K)
    ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hKc.fderiv_apply ℝ (unitVector l))
  have ha (v : Lp ℂ 2 (reducedLaw Q)) : A v =ᵐ[reducedLaw Q]
      fun ω => ∫ x, v (translate x ω) * (K x : ℂ) := by
    change (∫ x, (K x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v) =ᵐ[reducedLaw Q] _
    exact firstStrip_kernel_integral_coe Q v K hK.continuous hKc
  have hb (l : Fin d) (v : Lp ℂ 2 (reducedLaw Q)) : B l v =ᵐ[reducedLaw Q]
      fun ω => ∫ x, v (translate x ω) * (coordinateDerivative l K x : ℂ) := by
    change (∫ x, (coordinateDerivative l K x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v) =ᵐ[reducedLaw Q] _
    exact firstStrip_kernel_integral_coe Q v (coordinateDerivative l K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector l))
  constructor
  · intro l
    change -(B l f) = A (G l)
    apply Lp.ext
    filter_upwards [Lp.coeFn_neg (B l f), hb l f, ha (G l),
      firstStrip_spatial_gradient Q hG] with ω hn hf hg hgrad
    rw [hn]
    change -(B l f ω) = A (G l) ω
    rw [hf, hg]
    exact (hgrad l K hK hKc).symm
  · intro k l
    change B l (G k) = B k (G l)
    apply Lp.ext
    filter_upwards [hb l (G k), hb k (G l), firstStrip_spatial_curl Q hG] with ω hk hl hc
    rw [hk, hl]
    exact hc k l K hK hKc

/-- The differentiated smoothing error still tends to zero when the actual
coefficient derivative is moved outside the smoothing. The raw field needs
only L2 regularity. -/
private theorem firstStripSpatialKernel_flux_remainder_tendsto {d : ℕ}
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i j k l : Fin d) :
    ∃ M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ f : Lp ℂ 2 (reducedLaw Q), M f =ᵐ[reducedLaw Q] fun ω =>
        (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * f ω) ∧
      ∀ f : Lp ℂ 2 (reducedLaw Q),
        Tendsto (fun n =>
          firstStripKernelAverage Q (coordinateDerivative l (firstStripSpatialKernel d n))
            (((firstStripSpatialKernel_smooth d n).continuous_fderiv (by simp)).clm_apply
              continuous_const)
            ((firstStripSpatialKernel_compact d n).fderiv_apply ℝ (unitVector l))
            (complexCoefficientMul Q j k f) -
          complexCoefficientMul Q j k
            (firstStripKernelAverage Q (coordinateDerivative l (firstStripSpatialKernel d n))
              (((firstStripSpatialKernel_smooth d n).continuous_fderiv (by simp)).clm_apply
                continuous_const)
              ((firstStripSpatialKernel_compact d n).fderiv_apply ℝ (unitVector l)) f) +
          M (firstStripKernelAverage Q (firstStripSpatialKernel d n)
            (firstStripSpatialKernel_smooth d n).continuous
            (firstStripSpatialKernel_compact d n) f)) atTop (𝓝 0) := by
  obtain ⟨M, hM, ht⟩ := firstStripSpatialKernel_friedrichs_tendsto D Q hQ i j k l
  refine ⟨M, hM, ?_⟩
  intro f
  let A := fun n => firstStripKernelAverage Q (firstStripSpatialKernel d n)
    (firstStripSpatialKernel_smooth d n).continuous (firstStripSpatialKernel_compact d n)
  let B := fun n => firstStripKernelAverage Q (coordinateDerivative l (firstStripSpatialKernel d n))
    (((firstStripSpatialKernel_smooth d n).continuous_fderiv (by simp)).clm_apply continuous_const)
    ((firstStripSpatialKernel_compact d n).fderiv_apply ℝ (unitVector l))
  have hm : Tendsto (fun n => M (A n f)) atTop (𝓝 (M f)) :=
    (M.continuous.tendsto f).comp (firstStripSpatialKernel_average_tendsto Q f)
  have hc : Tendsto (fun n => M (A n f) - A n (M f)) atTop (𝓝 0) := by
    simpa only [sub_self] using hm.sub (firstStripSpatialKernel_average_tendsto Q (M f))
  have hr : Tendsto (fun n =>
      B n (complexCoefficientMul Q j k f) - complexCoefficientMul Q j k (B n f) +
        A n (M f)) atTop (𝓝 0) := ht f
  have hall := hr.add hc
  simp only [add_zero] at hall
  apply hall.congr' (Eventually.of_forall fun n => ?_)
  change (B n (complexCoefficientMul Q j k f) - complexCoefficientMul Q j k (B n f) +
      A n (M f)) + (M (A n f) - A n (M f)) =
    B n (complexCoefficientMul Q j k f) - complexCoefficientMul Q j k (B n f) + M (A n f)
  abel

/-- Exact normalization of the mollified column flux. The principal part
uses the derivative of the same smoothed gradient component. Every derivative
coefficient acts on a smoothed field, and the remaining errors have the form
whose L2 convergence was proved above. -/
private theorem firstStripKernelAverage_flux_normalization {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {f : Lp ℂ 2 (reducedLaw Q)}
    {H : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f H)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (i j l : Fin d) (τ : ℂ)
    (M : Fin d → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) :
    let A := firstStripKernelAverage Q K hK.continuous hKc
    let B := fun k => firstStripKernelAverage Q (coordinateDerivative k K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector k))
    let E := fun k v => B l (complexCoefficientMul Q j k v) -
      complexCoefficientMul Q j k (B l v) + M k (A v)
    B l ((∑ k, complexCoefficientMul Q j k (H k)) -
      τ • complexCoefficientMul Q j i f) =
      -(∑ k, complexCoefficientMul Q j k (-(B k (H l)))) -
        (∑ k, M k (A (H k))) + τ • complexCoefficientMul Q j i (A (H l)) +
        τ • M i (A f) + ((∑ k, E k (H k)) - τ • E i f) := by
  classical
  dsimp only
  let A := firstStripKernelAverage Q K hK.continuous hKc
  let B := fun k => firstStripKernelAverage Q (coordinateDerivative k K)
    ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hKc.fderiv_apply ℝ (unitVector k))
  let E := fun k v => B l (complexCoefficientMul Q j k v) -
    complexCoefficientMul Q j k (B l v) + M k (A v)
  have hcurl := firstStripKernelAverage_gradient_curl Q hH K hK hKc
  have hgrad : B l f = -(A (H l)) := by
    have hh := congrArg Neg.neg (hcurl.1 l)
    simpa only [neg_neg] using hh
  have hh (k : Fin d) : B l (complexCoefficientMul Q j k (H k)) =
      -(complexCoefficientMul Q j k (-(B k (H l)))) -
        M k (A (H k)) + E k (H k) := by
    dsimp only [E]
    rw [show B l (H k) = B k (H l) from hcurl.2 k l, map_neg, neg_neg]
    abel
  have hf : B l (complexCoefficientMul Q j i f) =
      -(complexCoefficientMul Q j i (A (H l))) - M i (A f) + E i f := by
    dsimp only [E]
    rw [hgrad, map_neg]
    abel
  change B l ((∑ k, complexCoefficientMul Q j k (H k)) -
      τ • complexCoefficientMul Q j i f) =
    -(∑ k, complexCoefficientMul Q j k (-(B k (H l)))) -
      (∑ k, M k (A (H k))) + τ • complexCoefficientMul Q j i (A (H l)) +
      τ • M i (A f) + ((∑ k, E k (H k)) - τ • E i f)
  rw [map_sub, map_sum, map_smul, hf]
  simp_rw [hh, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  simp only [smul_add, smul_sub, smul_neg]
  abel

/-- The normalized actual flux error vanishes in time L2 as well as at
each fixed L2 field. This permits its removal after radial energy testing. -/
private theorem firstStripSpatialKernel_flux_remainder_timeL2 {d : ℕ}
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i j k l : Fin d) :
    ∃ M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ f : Lp ℂ 2 (reducedLaw Q), M f =ᵐ[reducedLaw Q] fun ω =>
        (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * f ω) ∧
      ∀ (σ : Measure ℝ) (F : ℝ → Lp ℂ 2 (reducedLaw Q)), MemLp F 2 σ →
        Tendsto (fun n => ∫ s,
          ‖firstStripKernelAverage Q (coordinateDerivative l (firstStripSpatialKernel d n))
            (((firstStripSpatialKernel_smooth d n).continuous_fderiv (by simp)).clm_apply
              continuous_const)
            ((firstStripSpatialKernel_compact d n).fderiv_apply ℝ (unitVector l))
            (complexCoefficientMul Q j k (F s)) -
          complexCoefficientMul Q j k
            (firstStripKernelAverage Q (coordinateDerivative l (firstStripSpatialKernel d n))
              (((firstStripSpatialKernel_smooth d n).continuous_fderiv (by simp)).clm_apply
                continuous_const)
              ((firstStripSpatialKernel_compact d n).fderiv_apply ℝ (unitVector l)) (F s)) +
          M (firstStripKernelAverage Q (firstStripSpatialKernel d n)
            (firstStripSpatialKernel_smooth d n).continuous
            (firstStripSpatialKernel_compact d n) (F s))‖ ^ 2 ∂σ)
          atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := firstStrip_friedrichs_remainder_bound D
  obtain ⟨M, hM, hbound⟩ := hb Q hQ j k l
  obtain ⟨M', hM', ht⟩ := firstStripSpatialKernel_flux_remainder_tendsto D Q hQ i j k l
  have hsame : M' = M := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (hM' f).trans (hM f).symm
  rw [hsame] at ht
  obtain ⟨_, ⟨K, hK, hmoment⟩, _⟩ := firstStripSpatialKernel_moments d l
  let κ := firstStripSpatialKernel d
  let B := fun n => firstStripKernelAverage Q (κ n)
    (firstStripSpatialKernel_smooth d n).continuous (firstStripSpatialKernel_compact d n)
  let H := fun n => firstStripKernelAverage Q (coordinateDerivative l (κ n))
    (((firstStripSpatialKernel_smooth d n).continuous_fderiv (by simp)).clm_apply continuous_const)
    ((firstStripSpatialKernel_compact d n).fderiv_apply ℝ (unitVector l))
  let A := complexCoefficientMul Q j k
  let R : ℕ → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
    fun n => (H n).comp A - A.comp (H n) + M.comp (B n)
  have hnorm (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) :
      ‖R n f‖ ≤ (C * K + 2 * ‖M‖) * ‖f‖ := by
    have he : R n f = (H n (A f) - A (H n f) + B n (M f)) +
        M (B n f) - B n (M f) := by
      change H n (A f) - A (H n f) + M (B n f) = _
      abel
    have hr : ‖H n (A f) - A (H n f) + B n (M f)‖ ≤ C * K * ‖f‖ :=
      (hbound (κ n) (firstStripSpatialKernel_smooth d n)
        (firstStripSpatialKernel_compact d n) f).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hmoment n) hC) (norm_nonneg _))
    have hm : ‖M (B n f)‖ ≤ ‖M‖ * ‖f‖ :=
      (M.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (firstStripSpatialKernel_average_norm Q n f) (norm_nonneg M))
    have hb : ‖B n (M f)‖ ≤ ‖M‖ * ‖f‖ :=
      (firstStripSpatialKernel_average_norm Q n (M f)).trans (M.le_opNorm f)
    rw [he]
    calc
      _ ≤ ‖H n (A f) - A (H n f) + B n (M f)‖ + ‖M (B n f)‖ + ‖B n (M f)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ C * K * ‖f‖ + ‖M‖ * ‖f‖ + ‖M‖ * ‖f‖ :=
        add_le_add (add_le_add hr hm) hb
      _ = _ := by ring
  refine ⟨M, hM, ?_⟩
  intro σ F hF
  have hm (n : ℕ) : AEStronglyMeasurable (fun s => ‖R n (F s)‖ ^ 2) σ :=
    ((R n).continuous.comp_aestronglyMeasurable hF.aestronglyMeasurable).norm.pow 2
  have hdom (n : ℕ) (s : ℝ) :
      ‖R n (F s)‖ ^ 2 ≤ (C * K + 2 * ‖M‖) ^ 2 * ‖F s‖ ^ 2 := by
    calc
      _ ≤ ((C * K + 2 * ‖M‖) * ‖F s‖) ^ 2 := by
        gcongr
        exact hnorm n (F s)
      _ = _ := by ring
  have hi : Integrable (fun s => (C * K + 2 * ‖M‖) ^ 2 * ‖F s‖ ^ 2) σ :=
    (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _
  have hp (s : ℝ) : Tendsto (fun n => ‖R n (F s)‖ ^ 2) atTop (𝓝 0) := by
    have hp0 : Tendsto (fun n => R n (F s)) atTop (𝓝 0) := by
      change Tendsto (fun n => H n (A (F s)) - A (H n (F s)) + M (B n (F s)))
        atTop (𝓝 0)
      exact ht (F s)
    simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      hp0.norm.pow 2
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun s => (C * K + 2 * ‖M‖) ^ 2 * ‖F s‖ ^ 2) (Eventually.of_forall hm)
    (Eventually.of_forall fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖R n (F s)‖))]
      exact hdom n s)
    hi (ae_of_all _ hp)
  change Tendsto (fun n => ∫ s, ‖R n (F s)‖ ^ 2 ∂σ) atTop (𝓝 0)
  simpa only [integral_zero] using hlim

/-- In the differentiated column flux, every nonprincipal derivative of
an actual coefficient product is moved off the H1 test. The remaining test
derivatives pair only with the principal flux and the vanishing errors. -/
private theorem firstStripKernelAverage_flux_pairing_expansion {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    {f : Lp ℂ 2 (reducedLaw Q)} {H : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f H)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (i j l : Fin d) (τ : ℂ)
    (M : Fin d → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hM : ∀ k v, M k v =ᵐ[reducedLaw Q] fun ω =>
      (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * v ω) :
    let A := firstStripKernelAverage Q K hK.continuous hKc
    let B := fun k => firstStripKernelAverage Q (coordinateDerivative k K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector k))
    let E := fun k v => B l (complexCoefficientMul Q j k v) -
      complexCoefficientMul Q j k (B l v) + M k (A v)
    ∃ (C : Fin d → Lp ℂ 2 (reducedLaw Q)) (C₀ L : Lp ℂ 2 (reducedLaw Q)),
      (∀ k, C k =ᵐ[reducedLaw Q] fun ω =>
        (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * (-(B j (H k))) ω +
        (coordinateDerivative j (coordinateDerivative l (fun y => ω.1 y j k)) 0 : ℂ) *
          A (H k) ω) ∧
      (C₀ =ᵐ[reducedLaw Q] fun ω =>
        (coordinateDerivative l (fun y => ω.1 y j i) 0 : ℂ) * (-(B j f)) ω +
        (coordinateDerivative j (coordinateDerivative l (fun y => ω.1 y j i)) 0 : ℂ) *
          A f ω) ∧
      (L =ᵐ[reducedLaw Q] fun ω =>
        (ω.1 0 j i : ℂ) * (-(B j (H l))) ω +
        (coordinateDerivative j (fun y => ω.1 y j i) 0 : ℂ) * A (H l) ω) ∧
      ∀ (w W : Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j w W →
        inner ℂ W (B l ((∑ k, complexCoefficientMul Q j k (H k)) -
            τ • complexCoefficientMul Q j i f)) =
          -(∑ k, inner ℂ W (complexCoefficientMul Q j k (-(B k (H l)))) ) +
            (∑ k, inner ℂ w (C k)) - τ * inner ℂ w L - τ * inner ℂ w C₀ +
            ((∑ k, inner ℂ W (E k (H k))) - τ * inner ℂ W (E i f)) := by
  classical
  dsimp only
  let A := firstStripKernelAverage Q K hK.continuous hKc
  let B := fun k => firstStripKernelAverage Q (coordinateDerivative k K)
    ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hKc.fderiv_apply ℝ (unitVector k))
  let E := fun k v => B l (complexCoefficientMul Q j k v) -
    complexCoefficientMul Q j k (B l v) + M k (A v)
  have hm (k : Fin d) (v : Lp ℂ 2 (reducedLaw Q)) : M k v =ᵐ[reducedLaw Q] fun ω =>
      (iteratedHorizontalDerivative [l] (fun η : FieldPair d => η.1 0 j k) ω : ℂ) * v ω := by
    simpa only [firstStrip_coefficient_jet_eq, coordinateIterate] using hM k v
  have hc (k : Fin d) := firstStrip_coefficient_jet_product Q hQ j k [l] (M k) (hm k)
    j (A (H k)) (-(B j (H k))) (firstStripKernelAverage_gradient Q K hK hKc (H k) j)
  choose C hC hCe using hc
  obtain ⟨C₀, hC₀, hC₀e⟩ := firstStrip_coefficient_jet_product Q hQ j i [l] (M i) (hm i)
    j (A f) (-(B j f)) (firstStripKernelAverage_gradient Q K hK hKc f j)
  have ha (v : Lp ℂ 2 (reducedLaw Q)) : complexCoefficientMul Q j i v =ᵐ[reducedLaw Q]
      fun ω => (iteratedHorizontalDerivative [] (fun η : FieldPair d => η.1 0 j i) ω : ℂ) * v ω := by
    simpa only [iteratedHorizontalDerivative] using complexCoefficientMul_coe Q j i v
  obtain ⟨L, hL, hLe⟩ := firstStrip_coefficient_jet_product Q hQ j i []
    (complexCoefficientMul Q j i) ha j (A (H l)) (-(B j (H l)))
    (firstStripKernelAverage_gradient Q K hK hKc (H l) j)
  refine ⟨C, C₀, L, ?_, ?_, ?_, ?_⟩
  · intro k
    simpa only [firstStrip_coefficient_jet_eq, coordinateIterate] using hCe k
  · simpa only [firstStrip_coefficient_jet_eq, coordinateIterate] using hC₀e
  · simpa only [firstStrip_coefficient_jet_eq, coordinateIterate] using hLe
  · intro w W hw
    have hci (k : Fin d) : inner ℂ W (M k (A (H k))) = -inner ℂ w (C k) :=
      hw.inner_eq_neg (hC k)
    have hdi : inner ℂ W (M i (A f)) = -inner ℂ w C₀ := hw.inner_eq_neg hC₀
    have hli : inner ℂ W (complexCoefficientMul Q j i (A (H l))) = -inner ℂ w L :=
      hw.inner_eq_neg hL
    change inner ℂ W (B l ((∑ k, complexCoefficientMul Q j k (H k)) -
        τ • complexCoefficientMul Q j i f)) =
      -(∑ k, inner ℂ W (complexCoefficientMul Q j k (-(B k (H l))))) +
        (∑ k, inner ℂ w (C k)) - τ * inner ℂ w L - τ * inner ℂ w C₀ +
        ((∑ k, inner ℂ W (E k (H k))) - τ * inner ℂ W (E i f))
    have hn : B l ((∑ k, complexCoefficientMul Q j k (H k)) -
        τ • complexCoefficientMul Q j i f) =
      -(∑ k, complexCoefficientMul Q j k (-(B k (H l)))) -
        (∑ k, M k (A (H k))) + τ • complexCoefficientMul Q j i (A (H l)) +
        τ • M i (A f) + ((∑ k, E k (H k)) - τ • E i f) :=
      firstStripKernelAverage_flux_normalization Q hH K hK hKc i j l τ M
    rw [hn]
    simp only [inner_add_right, inner_sub_right, inner_neg_right, inner_sum, inner_smul_right]
    simp_rw [hci, hdi, hli]
    simp only [Finset.sum_neg_distrib]
    ring

/-- The smooth actual endpoint data have a continuous gradient trace at
zero. At every positive time this trace is the actual energy-class gradient;
no continuity is asserted for the artificial zero-time gradient choice. -/
private theorem firstStrip_endpoint_continuous_gradient_trace {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d) :
    ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)), Continuous G ∧
      (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) (G s)) ∧
      ∀ s, 0 < s → G s = firstStripTimeGradient hd Q β a μ ζ P T hP ν s := by
  have hex : ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      Continuous G ∧ ∀ s, HasComplexHorizontalGradient (reducedLaw Q)
        (reducedLaw_stationary Q) (uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal)
        (G s) := by
    cases ν with
    | inl k =>
      obtain ⟨b, hb⟩ := timeFlux_drift_generator (i := ⟨0, by omega⟩) (ζ := ζ) hβ k
      obtain ⟨c, hc⟩ := timeFlux_coefficient_generator (i := ⟨0, by omega⟩) (ζ := ζ)
        hQ ha ⟨0, by omega⟩ k
      obtain ⟨G, hGc, hG⟩ := hP.exists_continuous_gradient_orbit (hb.add (hc.smul ζ))
      exact ⟨G, hGc, hG⟩
    | inr b =>
      cases b with
      | false =>
        obtain ⟨c, hc⟩ := centeredEquations_clock_initial_generator
          (i := ⟨0, by omega⟩) (ζ := ζ) hQ hμ
        obtain ⟨G, hGc, hG⟩ := hP.exists_continuous_gradient_orbit (hc.smul ζ)
        refine ⟨G, hGc, fun s => ?_⟩
        simpa only [uncenteredEndpoint, map_smul] using hG s
      | true =>
        obtain ⟨c, hc⟩ := timeFlux_transpose_initial_generator
          (i := ⟨0, by omega⟩) (ζ := ζ) hβ ⟨0, by omega⟩
        obtain ⟨G, ⟨hG, hGc⟩, _⟩ := IsComplexTransposeSemigroup.existsUnique_continuous_gradient_orbit hP hT hc
        exact ⟨fun s => G s.toNNReal, hGc.comp continuous_real_toNNReal, fun s => hG s.toNNReal⟩
  obtain ⟨G, hGc, hG⟩ := hex
  refine ⟨G, hGc, hG, ?_⟩
  intro s hs
  apply WithLp.ofLp_injective 2
  exact ((hG s).unique (firstStripGradient_spec hd Q hQ β a μ ζ P T hP hT hβ ν
    s.toNNReal (Real.toNNReal_pos.mpr hs))).trans
      (firstStripTimeGradient_eq hd Q β a μ ζ P T hP ν hs).symm

/-- The actual scalar endpoint and its same chosen gradient satisfy the
undifferentiated weak equation, on a common spatial test event. -/
private theorem firstStrip_endpoint_physical_equation {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    let U := ∫ s in Icc (0 : ℝ) (t : ℝ),
      η s • uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal
    let H := fun k => ∫ s in Icc (0 : ℝ) (t : ℝ),
      η s • firstStripTimeGradient hd Q β a μ ζ P T hP ν s k
    let V := ∫ s in Icc (0 : ℝ) (t : ℝ),
      η' s • uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, V (translate x ω) * (φ x : ℂ)) =
          (1 / 2 : ℂ) * (∫ x, ∑ j,
            ((∑ k, (ω.1 x j k : ℂ) * H k (translate x ω)) -
              (if ν = .inr true then 2 * ζ else 0) *
                ((ω.1 x j ⟨0, by omega⟩ : ℂ) * U (translate x ω))) *
              (coordinateDerivative j φ x : ℂ)) -
          (if ν = .inr true then 0 else ζ) *
            (∫ x, (∑ j, (ω.1 x j ⟨0, by omega⟩ : ℂ) * H j (translate x ω)) *
              (φ x : ℂ)) := by
  cases ν with
  | inl k =>
    simpa only [firstStripTimeGradient, uncenteredEndpoint, reduceCtorEq, ↓reduceIte,
      zero_mul, sub_zero] using
      hP.time_test_spatial_flux_all_tests (β k + ζ • a ⟨0, by omega⟩ k)
        η η' hη hη' t hzero ht
  | inr b =>
    cases b with
    | false =>
      simpa only [firstStripTimeGradient, uncenteredEndpoint, Sum.inr.injEq,
        Bool.false_eq_true, ↓reduceIte, zero_mul, sub_zero, map_smul] using
        hP.time_test_spatial_flux_all_tests (ζ • μ) η η' hη hη' t hzero ht
    | true =>
      have hc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
      have hcoord (j : Fin d) :
          ((∫ s in Icc (0 : ℝ) (t : ℝ),
            η s • complexTransposeGradientOrbit Q T (β ⟨0, by omega⟩) s) j) =
          ∫ s in Icc (0 : ℝ) (t : ℝ),
            η s • (complexTransposeGradientOrbit Q T (β ⟨0, by omega⟩) s) j := by
        let C := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j
        have hi := C.integral_comp_comm
          (hT.integrableOn_weighted_gradientOrbit hP (β ⟨0, by omega⟩) η hc t)
        simpa only [C, ContinuousLinearMap.map_smul_of_tower, PiLp.proj_apply,
          PiLp.smul_apply] using hi.symm
      have he := hT.time_test_spatial_flux_integrated_gradient hP
        (β ⟨0, by omega⟩) η η' hη hη' t hzero ht
      simp_rw [hcoord] at he
      simpa only [firstStripTimeGradient, uncenteredEndpoint, transposeEndpoint,
        ↓reduceIte, zero_mul, sub_zero, mul_assoc] using he

/-- The scalar component of the actual space-time regularized system is
an L2 equality with its original divergence flux. -/
private theorem firstStrip_endpoint_scalar_space_time_L2 {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (t : ℝ≥0) (u : ℝ) (hzero : κ u = 0) (ht : κ (u - t) = 0)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K) :
    let U := firstStripTimeSmooth κ
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
    let H := fun k => firstStripTimeSmooth κ
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
    let V := firstStripTimeSmooth (deriv κ)
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
    let F := fun j => (∑ k, complexCoefficientMul Q j k (H k)) -
      (if ν = .inr true then 2 * ζ else 0) •
        complexCoefficientMul Q j ⟨0, by omega⟩ U
    let B := ∑ j, complexCoefficientMul Q j ⟨0, by omega⟩ (H j)
    firstStripKernelAverage Q K hK.continuous hKc V =
      (-1 / 2 : ℂ) • (∑ j, firstStripKernelAverage Q (coordinateDerivative j K)
        ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hKc.fderiv_apply ℝ (unitVector j)) (F j)) +
      (if ν = .inr true then 0 else ζ) •
        firstStripKernelAverage Q K hK.continuous hKc B := by
  classical
  let U := firstStripTimeSmooth κ
    (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
  let H := fun k => firstStripTimeSmooth κ
    (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
  let V := firstStripTimeSmooth (deriv κ)
    (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
  let τ : ℂ := if ν = .inr true then 2 * ζ else 0
  let zforce : ℂ := if ν = .inr true then 0 else ζ
  let F := fun j => (∑ k, complexCoefficientMul Q j k (H k)) -
    τ • complexCoefficientMul Q j ⟨0, by omega⟩ U
  let B := ∑ j, complexCoefficientMul Q j ⟨0, by omega⟩ (H j)
  let A0 := firstStripKernelAverage Q K hK.continuous hKc
  let A1 := fun j => firstStripKernelAverage Q (coordinateDerivative j K)
    ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hKc.fderiv_apply ℝ (unitVector j))
  have hη (s : ℝ) : HasDerivAt (fun s => κ (u - s)) (-deriv κ (u - s)) s := by
    simpa only [Function.comp_def, id_eq, mul_neg, mul_one] using!
      ((hκ.differentiable (by simp)).differentiableAt.hasDerivAt.comp s
        ((hasDerivAt_id s).const_sub u))
  have hη' : Continuous (fun s => -deriv κ (u - s)) :=
    ((hκ.continuous_deriv (by simp)).comp (continuous_const.sub continuous_id)).neg
  have he := firstStrip_endpoint_physical_equation hd Q β a μ ζ P T hP hT ν
    (fun s => κ (u - s)) (fun s => -deriv κ (u - s)) hη hη' t
    (by simpa only [sub_zero] using hzero) ht
  dsimp only at he
  simp only [neg_smul, integral_neg] at he
  change A0 V = (-1 / 2 : ℂ) • (∑ j, A1 j (F j)) + zforce • A0 B
  apply Lp.ext
  filter_upwards [he, firstStrip_flux_orbit Q U H ⟨0, by omega⟩ τ,
    firstStrip_kernel_integral_coe Q (-V) K hK.continuous hKc,
    ae_all_iff.mpr (fun j => firstStrip_kernel_integral_coe Q (F j)
      (coordinateDerivative j K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector j))),
    firstStrip_kernel_integral_coe Q B K hK.continuous hKc,
    firstStrip_coefficient_orbit_locallyIntegrable Q F,
    firstStrip_sum_ae (reducedLaw Q) Finset.univ (fun j => A1 j (F j)),
    Lp.coeFn_add ((-1 / 2 : ℂ) • (∑ j, A1 j (F j))) (zforce • A0 B),
    Lp.coeFn_smul (-1 / 2 : ℂ) (∑ j, A1 j (F j)),
    Lp.coeFn_smul zforce (A0 B), Lp.coeFn_neg (A0 V)]
      with ω he hf hv hfs hb hloc hs hadd hc hz hneg
  have hw := he K hK hKc
  have hF : (∫ x, ∑ j,
      ((∑ k, (ω.1 x j k : ℂ) * H k (translate x ω)) -
        τ * ((ω.1 x j ⟨0, by omega⟩ : ℂ) * U (translate x ω))) *
        (coordinateDerivative j K x : ℂ)) = ∑ j, A1 j (F j) ω := by
    calc
      _ = ∫ x, ∑ j, F j (translate x ω) * (coordinateDerivative j K x : ℂ) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hf.1] with x hx
        exact Finset.sum_congr rfl (fun j _ => by rw [hx j])
      _ = ∑ j, ∫ x, F j (translate x ω) * (coordinateDerivative j K x : ℂ) := by
        apply integral_finset_sum
        intro j _
        have hl : LocallyIntegrable (fun x => F j (translate x ω)) volume := by
          simpa only [Complex.ofReal_one, mul_one] using hloc j (fun _ => 1) continuous_const
        simpa only [smul_eq_mul, Function.comp_def, coordinateDerivative] using hl.integrable_smul_right_of_hasCompactSupport
          (Complex.continuous_ofReal.comp
            ((hK.continuous_fderiv (by simp)).clm_apply continuous_const))
          ((hKc.fderiv_apply ℝ (unitVector j)).comp_left rfl)
      _ = _ := Finset.sum_congr rfl (fun j _ => (hfs j).symm)
  have hB : (∫ x, (∑ j, (ω.1 x j ⟨0, by omega⟩ : ℂ) * H j (translate x ω)) *
      (K x : ℂ)) = A0 B ω := by
    change _ = (∫ x, (K x : ℂ) • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) x B) ω
    rw [hb]
    apply integral_congr_ae
    filter_upwards [hf.2] with x hx
    rw [hx]
  have hV : -(A0 V ω) = ∫ x, (-V) (translate x ω) * (K x : ℂ) := by
    change A0 (-V) ω = _ at hv
    rw [map_neg, hneg] at hv
    exact hv
  change (∫ x, (-V) (translate x ω) * (K x : ℂ)) =
    (1 / 2 : ℂ) * (∫ x, ∑ j,
      ((∑ k, (ω.1 x j k : ℂ) * H k (translate x ω)) -
        τ * ((ω.1 x j ⟨0, by omega⟩ : ℂ) * U (translate x ω))) *
          (coordinateDerivative j K x : ℂ)) -
    zforce * (∫ x, (∑ j, (ω.1 x j ⟨0, by omega⟩ : ℂ) *
      H j (translate x ω)) * (K x : ℂ)) at hw
  rw [hF, hB, ← hV] at hw
  rw [hadd]
  simp only [Pi.add_apply, hc, hz, Pi.smul_apply, smul_eq_mul, hs]
  change A0 V ω = (-1 / 2 : ℂ) * (∑ j, A1 j (F j) ω) + zforce * A0 B ω
  linear_combination -hw

/-- Every strong H1 scalar test is valid in the actual smoothed endpoint
equation, with the original coefficient flux retained. -/
private theorem firstStrip_endpoint_scalar_space_time_weak_L2 {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (t : ℝ≥0) (u : ℝ) (hzero : κ u = 0) (ht : κ (u - t) = 0)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (w : Lp ℂ 2 (reducedLaw Q)) (W : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hW : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) w W) :
    let U := firstStripTimeSmooth κ
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
    let H := fun k => firstStripTimeSmooth κ
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
    let V := firstStripTimeSmooth (deriv κ)
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
    let F := fun j => (∑ k, complexCoefficientMul Q j k (H k)) -
      (if ν = .inr true then 2 * ζ else 0) •
        complexCoefficientMul Q j ⟨0, by omega⟩ U
    let B := ∑ j, complexCoefficientMul Q j ⟨0, by omega⟩ (H j)
    inner ℂ w (firstStripKernelAverage Q K hK.continuous hKc V) =
      (-1 / 2 : ℂ) * (∑ j, inner ℂ (W j)
        (firstStripKernelAverage Q K hK.continuous hKc (F j))) +
      (if ν = .inr true then 0 else ζ) * inner ℂ w
        (firstStripKernelAverage Q K hK.continuous hKc B) := by
  classical
  have he := firstStrip_endpoint_scalar_space_time_L2 hd Q β a μ ζ P T hP hT ν
    κ hκ t u hzero ht K hK hKc
  dsimp only at he ⊢
  rw [he, inner_add_right, inner_smul_right, inner_smul_right, inner_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  let U := firstStripTimeSmooth κ
    (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
  let H := fun k => firstStripTimeSmooth κ
    (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
  let Fj := (∑ k, complexCoefficientMul Q j k (H k)) -
    (if ν = .inr true then 2 * ζ else 0) •
      complexCoefficientMul Q j ⟨0, by omega⟩ U
  have hh := (hW j).inner_eq_neg (firstStripKernelAverage_gradient Q K hK hKc Fj j)
  simpa only [inner_neg_right, neg_neg] using hh.symm

/-- The forward force column has only first-order, zeroth-order and
normalized remainder terms after smoothing the actual gradient. -/
private theorem firstStripKernelAverage_force_normalization {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {f : Lp ℂ 2 (reducedLaw Q)}
    {H : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f H)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (i l : Fin d)
    (M : Fin d → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) :
    let A := firstStripKernelAverage Q K hK.continuous hKc
    let B := fun k => firstStripKernelAverage Q (coordinateDerivative k K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector k))
    let E := fun j v => B l (complexCoefficientMul Q j i v) -
      complexCoefficientMul Q j i (B l v) + M j (A v)
    B l (∑ j, complexCoefficientMul Q j i (H j)) =
      -(∑ j, complexCoefficientMul Q j i (-(B j (H l)))) -
        (∑ j, M j (A (H j))) + ∑ j, E j (H j) := by
  classical
  dsimp only
  let A := firstStripKernelAverage Q K hK.continuous hKc
  let B := fun k => firstStripKernelAverage Q (coordinateDerivative k K)
    ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hKc.fderiv_apply ℝ (unitVector k))
  let E := fun j v => B l (complexCoefficientMul Q j i v) -
    complexCoefficientMul Q j i (B l v) + M j (A v)
  have hcurl := firstStripKernelAverage_gradient_curl Q hH K hK hKc
  have hh (j : Fin d) : B l (complexCoefficientMul Q j i (H j)) =
      -(complexCoefficientMul Q j i (-(B j (H l)))) - M j (A (H j)) + E j (H j) := by
    dsimp only [E]
    rw [show B l (H j) = B j (H l) from hcurl.2 j l, map_neg, neg_neg]
    abel
  change B l (∑ j, complexCoefficientMul Q j i (H j)) =
    -(∑ j, complexCoefficientMul Q j i (-(B j (H l)))) -
      (∑ j, M j (A (H j))) + ∑ j, E j (H j)
  rw [map_sum]
  simp_rw [hh, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]

/-- The actual differentiated equation has its principal part, actual
coefficient-jet couplings and normalized remainders separated before any
radial test is chosen. -/
private theorem firstStrip_endpoint_normalized_gradient_equation {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (t : ℝ≥0) (u : ℝ) (hzero : κ u = 0) (ht : κ (u - t) = 0)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (l : Fin d) :
    let U := firstStripTimeSmooth κ
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
    let H := fun k => firstStripTimeSmooth κ
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
    let V := firstStripTimeSmooth (deriv κ)
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s l) t u
    let A := firstStripKernelAverage Q K hK.continuous hKc
    let B := fun k => firstStripKernelAverage Q (coordinateDerivative k K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector k))
    let τ : ℂ := if ν = .inr true then 2 * ζ else 0
    let zforce : ℂ := if ν = .inr true then 0 else ζ
    ∃ M : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ j k v, M j k v =ᵐ[reducedLaw Q] fun ω =>
        (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * v ω) ∧
      let E := fun j k v => B l (complexCoefficientMul Q j k v) -
        complexCoefficientMul Q j k (B l v) + M j k (A v)
      ∃ (C : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
        (C₀ L : Fin d → Lp ℂ 2 (reducedLaw Q)),
        (∀ j k, C j k =ᵐ[reducedLaw Q] fun ω =>
          (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * (-(B j (H k))) ω +
          (coordinateDerivative j (coordinateDerivative l (fun y => ω.1 y j k)) 0 : ℂ) *
            A (H k) ω) ∧
        (∀ j, C₀ j =ᵐ[reducedLaw Q] fun ω =>
          (coordinateDerivative l (fun y => ω.1 y j ⟨0, by omega⟩) 0 : ℂ) * (-(B j U)) ω +
          (coordinateDerivative j (coordinateDerivative l
            (fun y => ω.1 y j ⟨0, by omega⟩)) 0 : ℂ) * A U ω) ∧
        (∀ j, L j =ᵐ[reducedLaw Q] fun ω =>
          (ω.1 0 j ⟨0, by omega⟩ : ℂ) * (-(B j (H l))) ω +
          (coordinateDerivative j (fun y => ω.1 y j ⟨0, by omega⟩) 0 : ℂ) * A (H l) ω) ∧
        ∀ (w : Lp ℂ 2 (reducedLaw Q)) (W : Fin d → Lp ℂ 2 (reducedLaw Q)),
          HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) w W →
          inner ℂ w (A V) =
            (1 / 2 : ℂ) * (∑ j,
              (-(∑ k, inner ℂ (W j) (complexCoefficientMul Q j k (-(B k (H l))))) +
                (∑ k, inner ℂ w (C j k)) - τ * inner ℂ w (L j) - τ * inner ℂ w (C₀ j) +
                ((∑ k, inner ℂ (W j) (E j k (H k))) -
                  τ * inner ℂ (W j) (E j ⟨0, by omega⟩ U)))) +
            zforce * ((∑ j, inner ℂ w (complexCoefficientMul Q j ⟨0, by omega⟩
                (-(B j (H l))))) + (∑ j, inner ℂ w (M j ⟨0, by omega⟩ (A (H j)))) -
              ∑ j, inner ℂ w (E j ⟨0, by omega⟩ (H j))) := by
  classical
  dsimp only
  let U := firstStripTimeSmooth κ
    (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
  let H := fun k => firstStripTimeSmooth κ
    (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
  let V := firstStripTimeSmooth (deriv κ)
    (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s l) t u
  let A := firstStripKernelAverage Q K hK.continuous hKc
  let B := fun k => firstStripKernelAverage Q (coordinateDerivative k K)
    ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hKc.fderiv_apply ℝ (unitVector k))
  let τ : ℂ := if ν = .inr true then 2 * ζ else 0
  let zforce : ℂ := if ν = .inr true then 0 else ζ
  obtain ⟨B₀, _, hmult⟩ := firstStrip_coefficient_derivative_multiplier D
  choose M hMb hM using fun j k => hmult Q hQ j k l
  refine ⟨M, hM, ?_⟩
  let E := fun j k v => B l (complexCoefficientMul Q j k v) -
    complexCoefficientMul Q j k (B l v) + M j k (A v)
  have hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) U H :=
    firstStrip_endpoint_time_gradient hd Q hQ β a μ hβ ζ P T hP hT ν κ hκ.continuous t u
  have hpair (j : Fin d) := firstStripKernelAverage_flux_pairing_expansion Q hQ hH
    K hK hKc ⟨0, by omega⟩ j l τ (M j) (hM j)
  choose C C₀ L hC hC₀ hL hpairing using hpair
  refine ⟨C, C₀, L, hC, hC₀, hL, ?_⟩
  intro w W hW
  have he := firstStrip_endpoint_space_time_weak_L2 hd D Q hQ β a μ ζ P T hP hT ν
    κ hκ t u hzero ht K hK hKc l w W hW
  let F := fun j => (∑ k, complexCoefficientMul Q j k (H k)) -
    τ • complexCoefficientMul Q j ⟨0, by omega⟩ U
  change inner ℂ w (A V) = (1 / 2 : ℂ) * (∑ j, inner ℂ (W j) (B l (F j))) -
    zforce * inner ℂ w (B l (∑ j, complexCoefficientMul Q j ⟨0, by omega⟩ (H j))) at he
  have hp (j : Fin d) := hpairing j w (W j) (hW j)
  have hf := firstStripKernelAverage_force_normalization Q hH K hK hKc
    ⟨0, by omega⟩ l (fun j => M j ⟨0, by omega⟩)
  change B l (∑ j, complexCoefficientMul Q j ⟨0, by omega⟩ (H j)) =
    -(∑ j, complexCoefficientMul Q j ⟨0, by omega⟩ (-(B j (H l)))) -
      (∑ j, M j ⟨0, by omega⟩ (A (H j))) + ∑ j, E j ⟨0, by omega⟩ (H j) at hf
  rw [hf] at he
  simp only [inner_add_right, inner_sub_right, inner_neg_right, inner_sum] at he
  have hp' : (∑ j, inner ℂ (W j) (B l (F j))) = ∑ j,
      (-(∑ k, inner ℂ (W j) (complexCoefficientMul Q j k (-(B k (H l))))) +
        (∑ k, inner ℂ w (C j k)) - τ * inner ℂ w (L j) - τ * inner ℂ w (C₀ j) +
        ((∑ k, inner ℂ (W j) (E j k (H k))) -
          τ * inner ℂ (W j) (E j ⟨0, by omega⟩ U))) := by
    apply Finset.sum_congr rfl
    intro j _
    exact hp j
  rw [hp'] at he
  change inner ℂ w (A V) = _
  linear_combination he

/-- The scalar equation exposes its actual coefficient coupling and ordinary
smoothing commutators before a radial test is chosen. -/
private theorem firstStrip_endpoint_normalized_scalar_equation {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (t : ℝ≥0) (u : ℝ) (hzero : κ u = 0) (ht : κ (u - t) = 0)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K) :
    let U := firstStripTimeSmooth κ
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
    let H := fun k => firstStripTimeSmooth κ
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
    let V := firstStripTimeSmooth (deriv κ)
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
    let A := firstStripKernelAverage Q K hK.continuous hKc
    let B := fun j => firstStripKernelAverage Q (coordinateDerivative j K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector j))
    let τ : ℂ := if ν = .inr true then 2 * ζ else 0
    let zforce : ℂ := if ν = .inr true then 0 else ζ
    let S := fun j k v => A (complexCoefficientMul Q j k v) -
      complexCoefficientMul Q j k (A v)
    ∃ L : Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ j, L j =ᵐ[reducedLaw Q] fun ω =>
        (ω.1 0 j ⟨0, by omega⟩ : ℂ) * (-(B j U)) ω +
        (coordinateDerivative j (fun y => ω.1 y j ⟨0, by omega⟩) 0 : ℂ) * A U ω) ∧
      ∀ (w : Lp ℂ 2 (reducedLaw Q)) (W : Fin d → Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) w W →
        inner ℂ w (A V) =
          (-1 / 2 : ℂ) * (∑ j, ∑ k,
            inner ℂ (W j) (complexCoefficientMul Q j k (A (H k)))) -
          (τ / 2) * (∑ j, inner ℂ w (L j)) +
          zforce * (∑ j, inner ℂ w
            (complexCoefficientMul Q j ⟨0, by omega⟩ (A (H j)))) +
          (-1 / 2 : ℂ) * (∑ j, ((∑ k, inner ℂ (W j) (S j k (H k))) -
            τ * inner ℂ (W j) (S j ⟨0, by omega⟩ U))) +
          zforce * (∑ j, inner ℂ w (S j ⟨0, by omega⟩ (H j))) := by
  classical
  dsimp only
  let U := firstStripTimeSmooth κ
    (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
  let H := fun k => firstStripTimeSmooth κ
    (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
  let V := firstStripTimeSmooth (deriv κ)
    (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
  let A := firstStripKernelAverage Q K hK.continuous hKc
  let B := fun j => firstStripKernelAverage Q (coordinateDerivative j K)
    ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hKc.fderiv_apply ℝ (unitVector j))
  let τ : ℂ := if ν = .inr true then 2 * ζ else 0
  let zforce : ℂ := if ν = .inr true then 0 else ζ
  let S := fun j k v => A (complexCoefficientMul Q j k v) -
    complexCoefficientMul Q j k (A v)
  have ha (j : Fin d) (v : Lp ℂ 2 (reducedLaw Q)) :
      complexCoefficientMul Q j ⟨0, by omega⟩ v =ᵐ[reducedLaw Q] fun ω =>
        (iteratedHorizontalDerivative []
          (fun η : FieldPair d => η.1 0 j ⟨0, by omega⟩) ω : ℂ) * v ω := by
    simpa only [iteratedHorizontalDerivative] using
      complexCoefficientMul_coe Q j ⟨0, by omega⟩ v
  have hj (j : Fin d) := firstStrip_coefficient_jet_product Q hQ j ⟨0, by omega⟩ []
    (complexCoefficientMul Q j ⟨0, by omega⟩) (ha j) j (A U) (-(B j U))
    (firstStripKernelAverage_gradient Q K hK hKc U j)
  choose L hL hLe using hj
  refine ⟨L, ?_, ?_⟩
  · intro j
    simpa only [firstStrip_coefficient_jet_eq, coordinateIterate] using hLe j
  intro w W hW
  have hs (j k : Fin d) (v : Lp ℂ 2 (reducedLaw Q)) :
      A (complexCoefficientMul Q j k v) = complexCoefficientMul Q j k (A v) + S j k v := by
    dsimp only [S]
    abel
  have hli (j : Fin d) :
      inner ℂ (W j) (complexCoefficientMul Q j ⟨0, by omega⟩ (A U)) =
        -inner ℂ w (L j) := (hW j).inner_eq_neg (hL j)
  let F := fun j => (∑ k, complexCoefficientMul Q j k (H k)) -
    τ • complexCoefficientMul Q j ⟨0, by omega⟩ U
  have hp (j : Fin d) : inner ℂ (W j) (A (F j)) =
      (∑ k, inner ℂ (W j) (complexCoefficientMul Q j k (A (H k)))) +
      τ * inner ℂ w (L j) +
      ((∑ k, inner ℂ (W j) (S j k (H k))) -
        τ * inner ℂ (W j) (S j ⟨0, by omega⟩ U)) := by
    dsimp only [F]
    rw [map_sub, map_sum, map_smul]
    simp only [inner_sub_right, inner_sum, inner_smul_right]
    simp_rw [hs, inner_add_right, hli]
    rw [Finset.sum_add_distrib]
    ring
  have hf : inner ℂ w (A (∑ j, complexCoefficientMul Q j ⟨0, by omega⟩ (H j))) =
      (∑ j, inner ℂ w (complexCoefficientMul Q j ⟨0, by omega⟩ (A (H j)))) +
      ∑ j, inner ℂ w (S j ⟨0, by omega⟩ (H j)) := by
    rw [map_sum, inner_sum]
    simp_rw [hs, inner_add_right]
    rw [Finset.sum_add_distrib]
  have he := firstStrip_endpoint_scalar_space_time_weak_L2 hd Q β a μ ζ P T hP hT ν
    κ hκ t u hzero ht K hK hKc w W hW
  change inner ℂ w (A V) = (-1 / 2 : ℂ) * (∑ j, inner ℂ (W j) (A (F j))) +
    zforce * inner ℂ w (A (∑ j, complexCoefficientMul Q j ⟨0, by omega⟩ (H j))) at he
  simp_rw [hp] at he
  rw [hf] at he
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at he ⊢
  linear_combination he

/-- At an interior time, normalized bump smoothing of a continuous orbit
on a finite horizon converges in the ambient norm. -/
private theorem firstStripTimeSmooth_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ : ℕ → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (F : ℝ → E) (hF : Continuous F) (t : ℝ≥0) (u : ℝ)
    (hu : 0 < u) (hut : u < (t : ℝ)) :
    Tendsto (fun n => firstStripTimeSmooth ((φ n).normed volume) F t u)
      atTop (𝓝 (F u)) := by
  let G := (Icc (0 : ℝ) (t : ℝ)).indicator F
  have hloc : G =ᶠ[𝓝 u] F := by
    filter_upwards [Icc_mem_nhds hu hut] with s hs
    exact indicator_of_mem hs F
  have hc : ContinuousAt G u := hF.continuousAt.congr_of_eventuallyEq hloc
  have hm : AEStronglyMeasurable G volume :=
    hF.aestronglyMeasurable.indicator measurableSet_Icc
  have he := ContDiffBump.convolution_tendsto_right (μ := volume)
    (g := fun _ : ℕ => G) (k := fun _ : ℕ => u) hφ
    (Eventually.of_forall (fun _ => hm)) (hc.tendsto.comp tendsto_snd) tendsto_const_nhds
  have hgu : G u = F u := indicator_of_mem (show u ∈ Icc (0 : ℝ) (t : ℝ) from ⟨hu.le, hut.le⟩) F
  simpa only [firstStripTimeSmooth_eq_convolution, convolution_flip, hgu] using he

/-- Time smoothing of the actual energy-class gradient converges at every
positive interior time, using the continuous gradient trace of the actual data. -/
private theorem firstStrip_endpoint_gradient_time_smoothing_tendsto {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (φ : ℕ → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (t : ℝ≥0) (u : ℝ) (hu : 0 < u) (hut : u < (t : ℝ)) :
    Tendsto (fun n => firstStripTimeSmooth ((φ n).normed volume)
      (firstStripTimeGradient hd Q β a μ ζ P T hP ν) t u) atTop
      (𝓝 (firstStripTimeGradient hd Q β a μ ζ P T hP ν u)) := by
  obtain ⟨G, hGc, _, hGe⟩ := firstStrip_endpoint_continuous_gradient_trace hd Q hQ
    β a μ hβ ha hμ ζ P T hP hT ν
  have he (n : ℕ) : firstStripTimeSmooth ((φ n).normed volume)
      (firstStripTimeGradient hd Q β a μ ζ P T hP ν) t u =
        firstStripTimeSmooth ((φ n).normed volume) G t u := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with s hs hs0
    have hpos := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    rw [hGe s hpos]
  simpa only [he, hGe u hu] using firstStripTimeSmooth_tendsto φ hφ G hGc t u hu hut

/-- The first-order couplings of the actual endpoint-plus-gradient system. -/
private def firstStripPointwiseFirstOrder {d : ℕ} (i : Fin d)
    (ν : EndpointIndex d) (ζ : ℂ) (ω : FieldPair d)
    (H : Fin (d + 1) → Fin d → ℂ) : Fin (d + 1) → ℂ :=
  Fin.cases
    ((if ν = .inr true then -ζ else ζ) *
      ∑ j, (ω.1 0 j i : ℂ) * H 0 j)
    (fun l => (1 / 2 : ℂ) *
      (∑ j, ∑ k, (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * H k.succ j) +
      (if ν = .inr true then -ζ else ζ) *
        (∑ j, (ω.1 0 j i : ℂ) * H l.succ j) -
      (if ν = .inr true then ζ else 0) *
        ∑ j, (coordinateDerivative l (fun y => ω.1 y j i) 0 : ℂ) * H 0 j)

/-- The zeroth-order couplings of the same actual coupled system. -/
private def firstStripPointwiseZerothOrder {d : ℕ} (i : Fin d)
    (ν : EndpointIndex d) (ζ : ℂ) (ω : FieldPair d)
    (z : Fin (d + 1) → ℂ) : Fin (d + 1) → ℂ :=
  Fin.cases
    (-(if ν = .inr true then ζ else 0) *
      ∑ j, (coordinateDerivative j (fun y => ω.1 y j i) 0 : ℂ) * z 0)
    (fun l => (1 / 2 : ℂ) *
      (∑ j, ∑ k, (coordinateDerivative j
        (coordinateDerivative l (fun y => ω.1 y j k)) 0 : ℂ) * z k.succ) +
      if ν = .inr true then -ζ *
        (∑ j, ((coordinateDerivative j (fun y => ω.1 y j i) 0 : ℂ) * z l.succ +
          (coordinateDerivative j (coordinateDerivative l (fun y => ω.1 y j i)) 0 : ℂ) * z 0))
      else ζ * ∑ j, (coordinateDerivative l (fun y => ω.1 y j i) 0 : ℂ) * z j.succ)

private theorem firstStrip_norm_finite_sum_product_bound {ι : Type*} [Fintype ι]
    (c v : ι → ℂ) (B S : ℝ) (hB : 0 ≤ B)
    (hc : ∀ i, ‖c i‖ ≤ B) (hv : ∀ i, ‖v i‖ ≤ S) :
    ‖∑ i, c i * v i‖ ≤ (Fintype.card ι : ℝ) * B * S := by
  classical
  calc
    ‖∑ i, c i * v i‖ ≤ ∑ i, ‖c i * v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, B * S := Finset.sum_le_sum fun i _ => by
      rw [norm_mul]
      exact mul_le_mul (hc i) (hv i) (norm_nonneg _) hB
    _ = _ := by simp [mul_assoc]

private theorem firstStrip_finite_family_sq_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] (F : ι → ℂ) (v : κ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ q, ‖F q‖ ≤ B * ∑ j, ‖v j‖) :
    (∑ q, ‖F q‖ ^ 2) ≤
      (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ) * B ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
  classical
  have hS : 0 ≤ ∑ j, ‖v j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcs : (∑ j, ‖v j‖) ^ 2 ≤ (Fintype.card κ : ℝ) * ∑ j, ‖v j‖ ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : κ => (1 : ℝ))
        (fun j => ‖v j‖)
  calc
    (∑ q, ‖F q‖ ^ 2) ≤ ∑ _q : ι, (B * ∑ j, ‖v j‖) ^ 2 :=
      Finset.sum_le_sum fun q _ =>
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB hS)).mpr (hF q)
    _ = ((Fintype.card ι : ℝ) * B ^ 2) * (∑ j, ‖v j‖) ^ 2 := by simp [mul_pow, mul_assoc]
    _ ≤ ((Fintype.card ι : ℝ) * B ^ 2) * ((Fintype.card κ : ℝ) * ∑ j, ‖v j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    _ = _ := by ring

/-- Raw actual coefficient jets have one structural bound before the law is
chosen. This bound contains exactly the jets occurring in the coupled PDE. -/
private theorem firstStrip_coupled_coefficient_jet_bounds {d : ℕ} (D : StructuralData d) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
      (∀ j k, ‖(ω.1 0 j k : ℂ)‖ ≤ B) ∧
      (∀ l j k, ‖(coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ)‖ ≤ B) ∧
      (∀ l j k, ‖(coordinateDerivative j
        (coordinateDerivative l (fun y => ω.1 y j k)) 0 : ℂ)‖ ≤ B) := by
  obtain ⟨M, hMpos, hM⟩ := firstStrip_initial_jet_bounds D
  obtain ⟨K, A, C, hK, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have h1 : 0 ≤ M 1 := (hMpos 1 (by omega)).le
  have h2 : 0 ≤ M 2 := (hMpos 2 (by omega)).le
  refine ⟨K + M 1 + M 2, by linarith, ?_⟩
  intro Q hQ
  filter_upwards [hM Q hQ, (hb d D.dependenceRange Q).2.2] with ω hω he
  refine ⟨?_, ?_, ?_⟩
  · intro j k
    have ha : |ω.1 0 j k| ≤ K := by
      apply abs_entry_le_of_quadratic_bounds hK0 (ω.1 0) (he.1 0).1
      · intro ξ
        exact (mul_nonneg (inv_nonneg.mpr hK0) (euclideanSq_nonneg_coords ξ)).trans
          (((he.1 0).2 ξ).1)
      · exact fun ξ => ((he.1 0).2 ξ).2
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      ha.trans (by linarith : K ≤ K + M 1 + M 2)
  · intro l j k
    have ha := (hω [l] (by simp) 0).1 j k
    simp only [coordinateIterate, List.length_cons, List.length_nil, zero_add] at ha
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      ha.trans (by linarith : M 1 ≤ K + M 1 + M 2)
  · intro l j k
    have ha := (hω [j, l] (by simp) 0).1 j k
    simp only [coordinateIterate, List.length_cons, List.length_nil, zero_add] at ha
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      ha.trans (by linarith : M 2 ≤ K + M 1 + M 2)

private theorem firstStrip_pointwise_coupling_norms {d : ℕ} (i : Fin d)
    (ν : EndpointIndex d) (ζ : ℂ) (ω : FieldPair d) (B S Z : ℝ)
    (hB : 0 ≤ B) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hζ : ‖ζ‖ ≤ 4)
    (hA : ∀ j k, ‖(ω.1 0 j k : ℂ)‖ ≤ B)
    (hD : ∀ l j k, ‖(coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ)‖ ≤ B)
    (hDD : ∀ l j k, ‖(coordinateDerivative j
      (coordinateDerivative l (fun y => ω.1 y j k)) 0 : ℂ)‖ ≤ B)
    (z : Fin (d + 1) → ℂ) (H : Fin (d + 1) → Fin d → ℂ)
    (hz : ∀ q, ‖z q‖ ≤ Z) (hH : ∀ q j, ‖H q j‖ ≤ S) :
    ∀ q, ‖firstStripPointwiseFirstOrder i ν ζ ω H q‖ ≤
        10 * B * ((d : ℝ) + 1) ^ 2 * S ∧
      ‖firstStripPointwiseZerothOrder i ν ζ ω z q‖ ≤
        10 * B * ((d : ℝ) + 1) ^ 2 * Z := by
  classical
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hforce : ‖(if ν = .inr true then -ζ else ζ)‖ ≤ 4 := by
    split <;> simpa only [norm_neg] using hζ
  have htrans : ‖(if ν = .inr true then ζ else 0)‖ ≤ 4 := by
    split
    · exact hζ
    · norm_num
  have hcol (q : Fin (d + 1)) :
      ‖∑ j, (ω.1 0 j i : ℂ) * H q j‖ ≤ (d : ℝ) * B * S := by
    simpa only [Fintype.card_fin] using firstStrip_norm_finite_sum_product_bound
      (fun j : Fin d => (ω.1 0 j i : ℂ)) (H q) B S hB (fun j => hA j i) (hH q)
  have hdercol (l : Fin d) (q : Fin (d + 1)) :
      ‖∑ j, (coordinateDerivative l (fun y => ω.1 y j i) 0 : ℂ) * H q j‖ ≤
        (d : ℝ) * B * S := by
    simpa only [Fintype.card_fin] using firstStrip_norm_finite_sum_product_bound
      (fun j : Fin d => (coordinateDerivative l (fun y => ω.1 y j i) 0 : ℂ))
      (H q) B S hB (fun j => hD l j i) (hH q)
  have hgrad (l : Fin d) :
      ‖∑ j, ∑ k, (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * H k.succ j‖ ≤
        (d : ℝ) ^ 2 * B * S := by
    calc
      _ ≤ ∑ j, ‖∑ k, (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * H k.succ j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j : Fin d, (d : ℝ) * B * S := Finset.sum_le_sum fun j _ => by
        simpa only [Fintype.card_fin] using firstStrip_norm_finite_sum_product_bound
          (fun k : Fin d => (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ))
          (fun k => H k.succ j) B S hB (fun k => hD l j k) (fun k => hH k.succ j)
      _ = _ := by simp; ring
  have hzcol (c : Fin d → ℂ) (hc : ∀ j, ‖c j‖ ≤ B) (q : Fin (d + 1)) :
      ‖∑ j, c j * z q‖ ≤ (d : ℝ) * B * Z := by
    simpa only [Fintype.card_fin] using firstStrip_norm_finite_sum_product_bound
      c (fun _ => z q) B Z hB hc (fun _ => hz q)
  have hzder (l : Fin d) :
      ‖∑ j, (coordinateDerivative l (fun y => ω.1 y j i) 0 : ℂ) * z j.succ‖ ≤
        (d : ℝ) * B * Z := by
    simpa only [Fintype.card_fin] using firstStrip_norm_finite_sum_product_bound
      (fun j : Fin d => (coordinateDerivative l (fun y => ω.1 y j i) 0 : ℂ))
      (fun j => z j.succ) B Z hB (fun j => hD l j i) (fun j => hz j.succ)
  have hzero (l : Fin d) :
      ‖∑ j, ∑ k, (coordinateDerivative j
        (coordinateDerivative l (fun y => ω.1 y j k)) 0 : ℂ) * z k.succ‖ ≤
        (d : ℝ) ^ 2 * B * Z := by
    calc
      _ ≤ ∑ j, ‖∑ k, (coordinateDerivative j
          (coordinateDerivative l (fun y => ω.1 y j k)) 0 : ℂ) * z k.succ‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin d, (d : ℝ) * B * Z := Finset.sum_le_sum fun j _ => by
        simpa only [Fintype.card_fin] using firstStrip_norm_finite_sum_product_bound
          (fun k : Fin d => (coordinateDerivative j
            (coordinateDerivative l (fun y => ω.1 y j k)) 0 : ℂ))
          (fun k => z k.succ) B Z hB (fun k => hDD l j k) (fun k => hz k.succ)
      _ = _ := by simp; ring
  have hnum : (d : ℝ) ^ 2 / 2 + 8 * d ≤ 10 * ((d : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (d : ℝ)]
  have hnum0 : 4 * (d : ℝ) ≤ 10 * ((d : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (d : ℝ)]
  have hbound (V : ℝ) (hV : 0 ≤ V) :
      (1 / 2 : ℝ) * ((d : ℝ) ^ 2 * B * V) + 4 * ((d : ℝ) * B * V) +
        4 * ((d : ℝ) * B * V) ≤ 10 * B * ((d : ℝ) + 1) ^ 2 * V := by
    nlinarith [mul_le_mul_of_nonneg_right hnum (mul_nonneg hB hV)]
  have hbound0 (V : ℝ) (hV : 0 ≤ V) :
      4 * ((d : ℝ) * B * V) ≤ 10 * B * ((d : ℝ) + 1) ^ 2 * V := by
    nlinarith [mul_le_mul_of_nonneg_right hnum0 (mul_nonneg hB hV)]
  intro q
  refine Fin.cases ?_ (fun l => ?_) q
  · constructor
    · change ‖(if ν = .inr true then -ζ else ζ) * _‖ ≤ _
      rw [norm_mul]
      exact (mul_le_mul hforce (hcol 0) (norm_nonneg _) (by norm_num)).trans (hbound0 S hS)
    · change ‖(-(if ν = .inr true then ζ else 0)) * _‖ ≤ _
      rw [norm_mul, norm_neg]
      exact (mul_le_mul htrans
        (hzcol (fun j => (coordinateDerivative j (fun y => ω.1 y j i) 0 : ℂ))
          (fun j => hD j j i) 0) (norm_nonneg _) (by norm_num)).trans (hbound0 Z hZ)
  · constructor
    · change ‖(1 / 2 : ℂ) * _ + (if ν = .inr true then -ζ else ζ) * _ -
        (if ν = .inr true then ζ else 0) * _‖ ≤ _
      calc
        _ ≤ ‖(1 / 2 : ℂ) *
            (∑ j, ∑ k, (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * H k.succ j)‖ +
            ‖(if ν = .inr true then -ζ else ζ) *
              (∑ j, (ω.1 0 j i : ℂ) * H l.succ j)‖ +
            ‖(if ν = .inr true then ζ else 0) *
              (∑ j, (coordinateDerivative l (fun y => ω.1 y j i) 0 : ℂ) * H 0 j)‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ (1 / 2 : ℝ) * ((d : ℝ) ^ 2 * B * S) +
            4 * ((d : ℝ) * B * S) + 4 * ((d : ℝ) * B * S) := by
          simp only [norm_mul]
          apply add_le_add
          · apply add_le_add
            · have hh := mul_le_mul_of_nonneg_left (hgrad l)
                (by norm_num : (0 : ℝ) ≤ 1 / 2)
              norm_num at hh ⊢
              exact hh
            · exact mul_le_mul hforce (hcol l.succ) (norm_nonneg _) (by norm_num)
          · exact mul_le_mul htrans (hdercol l 0) (norm_nonneg _) (by norm_num)
        _ ≤ _ := hbound S hS
    · have hzforce : ‖(if ν = .inr true then -ζ *
          (∑ j, ((coordinateDerivative j (fun y => ω.1 y j i) 0 : ℂ) * z l.succ +
            (coordinateDerivative j (coordinateDerivative l (fun y => ω.1 y j i)) 0 : ℂ) * z 0))
          else ζ * ∑ j, (coordinateDerivative l (fun y => ω.1 y j i) 0 : ℂ) * z j.succ)‖ ≤
          8 * ((d : ℝ) * B * Z) := by
        split
        · rw [norm_mul, norm_neg, Finset.sum_add_distrib]
          have ha := hzcol (fun j => (coordinateDerivative j (fun y => ω.1 y j i) 0 : ℂ))
            (fun j => hD j j i) l.succ
          have hb := hzcol (fun j => (coordinateDerivative j
            (coordinateDerivative l (fun y => ω.1 y j i)) 0 : ℂ)) (fun j => hDD l j i) 0
          have hs := (norm_add_le _ _).trans (add_le_add ha hb)
          calc
            _ ≤ 4 * ((d : ℝ) * B * Z + (d : ℝ) * B * Z) :=
              mul_le_mul hζ hs (norm_nonneg _) (by norm_num)
            _ = _ := by ring
        · rw [norm_mul]
          exact (mul_le_mul hζ (hzder l) (norm_nonneg _) (by norm_num)).trans
            (by nlinarith [mul_nonneg (mul_nonneg hd hB) hZ])
      change ‖(1 / 2 : ℂ) * _ + _‖ ≤ _
      calc
        _ ≤ ‖(1 / 2 : ℂ) * (∑ j, ∑ k, (coordinateDerivative j
              (coordinateDerivative l (fun y => ω.1 y j k)) 0 : ℂ) * z k.succ)‖ + _ :=
          norm_add_le _ _
        _ ≤ (1 / 2 : ℝ) * ((d : ℝ) ^ 2 * B * Z) + 8 * ((d : ℝ) * B * Z) := by
          apply add_le_add ?_ hzforce
          rw [norm_mul]
          have hh := mul_le_mul_of_nonneg_left (hzero l)
            (by norm_num : (0 : ℝ) ≤ 1 / 2)
          norm_num at hh ⊢
          exact hh
        _ ≤ _ := by nlinarith [hbound Z hZ]

/-- Both actual lower-order couplings have quadratic bounds with constants
chosen before the environment law, endpoint, force and radial weight. -/
private theorem firstStrip_actual_couplings_sq_bounds {d : ℕ} (D : StructuralData d) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
      ∀ (i : Fin d) (ν : EndpointIndex d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
      ∀ (z : Fin (d + 1) → ℂ) (H : Fin (d + 1) → Fin d → ℂ),
        (∑ q, ‖firstStripPointwiseFirstOrder i ν ζ ω H q‖ ^ 2) ≤
          K * (∑ q, ∑ j, ‖H q j‖ ^ 2) ∧
        (∑ q, ‖firstStripPointwiseZerothOrder i ν ζ ω z q‖ ^ 2) ≤
          L * (∑ q, ‖z q‖ ^ 2) := by
  classical
  obtain ⟨B, hB1, hB⟩ := firstStrip_coupled_coefficient_jet_bounds D
  let A := 10 * B * ((d : ℝ) + 1) ^ 2
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hB1))
    (sq_nonneg _)
  refine ⟨((d : ℝ) + 1) * (((d : ℝ) + 1) * d) * A ^ 2,
    ((d : ℝ) + 1) * ((d : ℝ) + 1) * A ^ 2,
    by positivity, by positivity, ?_⟩
  intro Q hQ
  filter_upwards [hB Q hQ] with ω hω
  intro i ν ζ hζ z H
  let S := ∑ p : Fin (d + 1) × Fin d, ‖H p.1 p.2‖
  let Z := ∑ q, ‖z q‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hH (q : Fin (d + 1)) (j : Fin d) : ‖H q j‖ ≤ S :=
    Finset.single_le_sum (fun p _ => norm_nonneg (H p.1 p.2)) (Finset.mem_univ (q, j))
  have hz (q : Fin (d + 1)) : ‖z q‖ ≤ Z :=
    Finset.single_le_sum (fun q _ => norm_nonneg (z q)) (Finset.mem_univ q)
  have hb := firstStrip_pointwise_coupling_norms i ν ζ ω B S Z
    (zero_le_one.trans hB1) hS hZ hζ hω.1 hω.2.1 hω.2.2 z H hz hH
  constructor
  · have he := firstStrip_finite_family_sq_bound
      (firstStripPointwiseFirstOrder i ν ζ ω H)
      (fun p : Fin (d + 1) × Fin d => H p.1 p.2) A hA (fun q => (hb q).1)
    simpa only [Fintype.card_fin, Fintype.card_prod, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, Fintype.sum_prod_type] using he
  · have he := firstStrip_finite_family_sq_bound
      (firstStripPointwiseZerothOrder i ν ζ ω z) z A hA (fun q => (hb q).2)
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using he

/-- The actual coupled system has a Bernstein growth constant independent of
the environment law, force, endpoint and increasing radial test. -/
private theorem firstStrip_actual_bernstein_dissipation {d : ℕ} (D : StructuralData d) :
    ∃ m C : ℝ, 0 < m ∧ 1 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
      ∀ (i : Fin d) (ν : EndpointIndex d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
      ∀ (b c : ℝ), 0 ≤ b → 0 ≤ c →
      ∀ (z : Fin (d + 1) → ℂ) (H : Fin (d + 1) → Fin d → ℂ),
        2 * b * (∑ q, inner ℝ (z q) (firstStripPointwiseFirstOrder i ν ζ ω H q)) +
          2 * b * (∑ q, inner ℝ (z q) (firstStripPointwiseZerothOrder i ν ζ ω z q)) -
          (∑ q, ∑ j, ∑ k,
            star (firstStripSystemRadialDifferential b c z H q j) *
              (ω.1 0 j k : ℂ) * H q k).re ≤
        -(b * m / 2) * (∑ q, ∑ j, ‖H q j‖ ^ 2) +
          b * C * (∑ q, ‖z q‖ ^ 2) := by
  classical
  obtain ⟨K, L, hK, hL, hcouple⟩ := firstStrip_actual_couplings_sq_bounds D
  obtain ⟨Λ, A, B, hΛ, _, _, _, hbounds⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  have hm : 0 < Λ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hΛ)
  refine ⟨Λ⁻¹, max 1 (2 * K / Λ⁻¹ + 1 + L), hm, le_max_left _ _, ?_⟩
  intro Q hQ
  filter_upwards [hcouple Q hQ, (hbounds d D.dependenceRange Q).2.2] with ω hc he
  intro i ν ζ hζ b c hb hc' z H
  have hbnd := hc i ν ζ hζ z H
  have hell : ∀ ξ : Vec d, Λ⁻¹ * euclideanSq ξ ≤ dot ξ ((ω.1 0).mulVec ξ) :=
    fun ξ => ((he.1 0).2 ξ).1
  have hdiss := firstStrip_system_bernstein_dissipation (ω.1 0)
    Λ⁻¹ b c K L hm hb hc' hK hL hell z
      (firstStripPointwiseFirstOrder i ν ζ ω H)
      (firstStripPointwiseZerothOrder i ν ζ ω z) H hbnd.1 hbnd.2
  apply hdiss.trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (le_max_right 1 _) hb)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Finite-dimensional Young inequality, retaining a freely chosen positive
coefficient on the differentiated factor. -/
private theorem firstStrip_finite_inner_young {ι : Type*} [Fintype ι]
    (x y : ι → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    (∑ i, inner ℝ (x i) (y i)) ≤
      δ * (∑ i, ‖x i‖ ^ 2) + (4 * δ)⁻¹ * (∑ i, ‖y i‖ ^ 2) := by
  classical
  have hp (i : ι) : inner ℝ (x i) (y i) ≤
      δ * ‖x i‖ ^ 2 + (4 * δ)⁻¹ * ‖y i‖ ^ 2 := by
    apply (real_inner_le_norm _ _).trans
    have he : δ * ‖x i‖ ^ 2 + (4 * δ)⁻¹ * ‖y i‖ ^ 2 =
        (4 * δ ^ 2 * ‖x i‖ ^ 2 + ‖y i‖ ^ 2) / (4 * δ) := by
      field_simp [hδ.ne']
      <;> ring
    rw [he]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * δ)).mpr
    nlinarith only [sq_nonneg (2 * δ * ‖x i‖ - ‖y i‖)]
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i)

/-- The actual Bernstein estimate absorbs arbitrary flux and force errors.
The growth constant is chosen before the radial parameters; the error constant
is allowed to depend on the fixed regularization, which is removed afterwards. -/
private theorem firstStrip_actual_radial_remainder_bound {d : ℕ} (D : StructuralData d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a B : ℝ), 0 ≤ a → 0 < B →
      ∃ K : ℝ, 0 ≤ K ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
      ∀ (i : Fin d) (ν : EndpointIndex d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
      ∀ (b c : ℝ), 0 ≤ b → 0 ≤ c → b ≤ B →
      ∀ (z : Fin (d + 1) → ℂ) (H J : Fin (d + 1) → Fin d → ℂ)
        (E : Fin (d + 1) → ℂ), c * (∑ q, ‖z q‖ ^ 2) ≤ a * b →
        2 * b * (∑ q, inner ℝ (z q) (firstStripPointwiseFirstOrder i ν ζ ω H q)) +
          2 * b * (∑ q, inner ℝ (z q) (firstStripPointwiseZerothOrder i ν ζ ω z q)) -
          (∑ q, ∑ j, ∑ k,
            star (firstStripSystemRadialDifferential b c z H q j) *
              (ω.1 0 j k : ℂ) * H q k).re +
          (∑ q, ∑ j, inner ℝ (firstStripSystemRadialDifferential b c z H q j) (J q j)) +
          2 * b * (∑ q, inner ℝ (z q) (E q)) ≤
        b * C * (∑ q, ‖z q‖ ^ 2) +
          K * ((∑ q, ∑ j, ‖J q j‖ ^ 2) + ∑ q, ‖E q‖ ^ 2) := by
  classical
  obtain ⟨m, C, hm, hC, hbern⟩ := firstStrip_actual_bernstein_dissipation D
  refine ⟨C + 1, by linarith, ?_⟩
  intro a B ha hB
  let A : ℝ := 2 + 8 * a ^ 2
  have hA : 0 < A := by dsimp only [A]; positivity
  let δ : ℝ := m / (2 * A * B)
  have hδ : 0 < δ := div_pos hm (by positivity)
  let K := max ((4 * δ)⁻¹) B
  refine ⟨K, le_trans (inv_nonneg.mpr (by positivity)) (le_max_left _ _), ?_⟩
  intro Q hQ
  filter_upwards [hbern Q hQ] with ω hω
  intro i ν ζ hζ b c hb hc hbB z H J E hslope
  let Y : ℝ := ∑ q, ∑ j, ‖H q j‖ ^ 2
  let Z : ℝ := ∑ q, ‖z q‖ ^ 2
  have hY : 0 ≤ Y := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrad := firstStrip_system_radial_norm_sq b c z H
  have hs : c ^ 2 * Z ^ 2 ≤ a ^ 2 * b ^ 2 := by
    have hh := pow_le_pow_left₀ (mul_nonneg hc hZ) hslope 2
    simpa only [mul_pow] using hh
  have hrad' : (∑ q, ∑ j,
      ‖firstStripSystemRadialDifferential b c z H q j‖ ^ 2) ≤ A * B * b * Y := by
    have ht : 2 * b ^ 2 + 8 * c ^ 2 * Z ^ 2 ≤ A * b ^ 2 := by
      dsimp only [A]
      nlinarith only [hs]
    have ht' : A * b ^ 2 ≤ A * B * b := by
      have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbB hb) hA.le
      nlinarith only [hh]
    exact hrad.trans (mul_le_mul_of_nonneg_right (ht.trans ht') hY)
  have hj := firstStrip_finite_inner_young
    (fun x : Fin (d + 1) × Fin d =>
      firstStripSystemRadialDifferential b c z H x.1 x.2)
    (fun x : Fin (d + 1) × Fin d => J x.1 x.2) hδ
  simp only [Fintype.sum_prod_type] at hj
  have hj' : (∑ q, ∑ j,
      inner ℝ (firstStripSystemRadialDifferential b c z H q j) (J q j)) ≤
      b * m / 2 * Y + (4 * δ)⁻¹ * (∑ q, ∑ j, ‖J q j‖ ^ 2) := by
    have ht := mul_le_mul_of_nonneg_left hrad' hδ.le
    have he : δ * (A * B * b * Y) = b * m / 2 * Y := by
      dsimp only [δ]
      field_simp [hA.ne', hB.ne']
      <;> ring
    rw [he] at ht
    exact hj.trans (add_le_add ht le_rfl)
  have he := firstStrip_finite_inner_young z E (by norm_num : (0 : ℝ) < 1 / 2)
  norm_num only at he
  have he' : 2 * b * (∑ q, inner ℝ (z q) (E q)) ≤
      b * Z + B * (∑ q, ‖E q‖ ^ 2) := by
    have ht := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb)
    have hB' := mul_le_mul_of_nonneg_right hbB
      (show 0 ≤ ∑ q, ‖E q‖ ^ 2 from Finset.sum_nonneg fun q _ => sq_nonneg ‖E q‖)
    dsimp only [Z]
    nlinarith only [ht, hB']
  have hkJ := mul_le_mul_of_nonneg_right (le_max_left ((4 * δ)⁻¹) B)
    (show 0 ≤ ∑ q, ∑ j, ‖J q j‖ ^ 2 from
      Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖J q j‖)
  have hkE := mul_le_mul_of_nonneg_right (le_max_right ((4 * δ)⁻¹) B)
    (show 0 ≤ ∑ q, ‖E q‖ ^ 2 from Finset.sum_nonneg fun q _ => sq_nonneg ‖E q‖)
  have hd := hω i ν ζ hζ b c hb hc z H
  dsimp only [Y, Z] at hj' he'
  dsimp only [K]
  nlinarith only [hd, hj', he', hkJ, hkE]

/-- Fixed regularized system energies pass through strong L2 limits. -/
private theorem firstStripSystem_energy_tendsto {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {n : ℕ} {l : Filter ι}
    {f : ι → Fin n → Lp ℂ 2 μ} {g : Fin n → Lp ℂ 2 μ}
    (hf : Tendsto f l (𝓝 g)) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    Tendsto (fun i => ∫ ω, firstStripHilbertPrimitive ε R a
      (WithLp.toLp 2 (fun q => f i q ω) : EuclideanSpace ℂ (Fin n)) ∂μ)
      l (𝓝 (∫ ω, firstStripHilbertPrimitive ε R a
        (WithLp.toLp 2 (fun q => g q ω) : EuclideanSpace ℂ (Fin n)) ∂μ)) := by
  have hc := (firstStripHilbertPrimitive_integral_hasFDerivAt μ
    (firstStripSystemPack μ n g) hε hR ha).continuousAt.tendsto
  have he := hc.comp ((firstStripSystemPack μ n).continuous.tendsto g |>.comp hf)
  simp only [Function.comp_def] at he
  simpa only [firstStripSystemPack_energy] using he

/-- Fatou transfers uniform nonnegative integral bounds on arbitrary carriers.
Both integrability and the upper bound are retained in the limit. -/
private theorem firstStrip_integrable_limit_of_nonnegative_bound {α : Type*}
    [MeasurableSpace α] (μ : Measure α) {f : ℕ → α → ℝ} {g : α → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ n, Integrable (f n) μ)
    (hn : ∀ n, 0 ≤ᵐ[μ] f n) (hg : 0 ≤ᵐ[μ] g)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hb : ∀ n, (∫ ω, f n ω ∂μ) ≤ B) :
    Integrable g μ ∧ (∫ ω, g ω ∂μ) ≤ B := by
  have hgm : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hf n).aestronglyMeasurable) hlim
  have hl : (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with ω hω
        exact (ENNReal.continuous_ofReal.tendsto (g ω) |>.comp hω).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          (hf n).aestronglyMeasurable.aemeasurable)
      _ ≤ ENNReal.ofReal B := by
        apply liminf_le_of_frequently_le'
        apply Eventually.frequently
        apply Eventually.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (hn n)]
        exact ENNReal.ofReal_le_ofReal (hb n)
  have hgi : Integrable g μ := by
    refine ⟨hgm, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have he : (fun ω => ENNReal.ofReal ‖g ω‖) =ᵐ[μ]
        fun ω => ENNReal.ofReal (g ω) := by
      filter_upwards [hg] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg hω]
    rw [lintegral_congr_ae he]
    exact hl.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hgi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hg hgm]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hl).trans_eq (ENNReal.toReal_ofReal hB)

/-- Joint removal of the positive regularization and squared cutoff recovers
the exact power primitive at every radius. -/
private theorem firstStripHilbertPrimitive_joint_tendsto {E : Type*}
    [NormedAddCommGroup E] {a : ℝ} (ha : 0 ≤ a) (z : E) :
    Tendsto (fun n : ℕ => firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹
      ((n : ℝ) + 1) a z) atTop (𝓝 (‖z‖ ^ (2 * (a + 1)) / (2 * (a + 1)))) := by
  let ρ := ‖z‖ ^ 2
  have hρ : 0 ≤ ρ := sq_nonneg _
  have hN (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hNtop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hε : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hNtop
  have hw (s : ℝ) (hs : 0 ≤ s) :
      Tendsto (fun n : ℕ => radialTruncationWeight ((n : ℝ) + 1)⁻¹
        ((n : ℝ) + 1) a s) atTop (𝓝 (s ^ a)) := by
    have hq : Tendsto (fun n : ℕ => s / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hNtop
    have hb := hε.add ((tendsto_const_nhds : Tendsto (fun _n : ℕ => s) atTop (𝓝 s)).div
      (tendsto_const_nhds.add hq) (by norm_num : (1 : ℝ) + 0 ≠ 0))
    simp only [add_zero, div_one, zero_add] at hb
    have he : (fun n : ℕ => radialTruncationBase ((n : ℝ) + 1)⁻¹
        ((n : ℝ) + 1) s) = fun n : ℕ => ((n : ℝ) + 1)⁻¹ + s / (1 + s / ((n : ℝ) + 1)) := by
      funext n
      unfold radialTruncationBase
      have hd : (n : ℝ) + 1 + s ≠ 0 := (add_pos_of_pos_of_nonneg (hN n) hs).ne'
      field_simp [ne_of_gt (hN n), hd]
      <;> ring
    have hbase : Tendsto (fun n : ℕ => radialTruncationBase ((n : ℝ) + 1)⁻¹
        ((n : ℝ) + 1) s) atTop (𝓝 s) := by
      rw [he]
      exact hb
    unfold radialTruncationWeight
    exact (Real.continuousAt_rpow_const s a (Or.inr ha)).tendsto.comp hbase
  have hdom (n : ℕ) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) ρ) :
      ‖radialTruncationWeight ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) a (max s 0)‖ ≤
        (1 + ρ) ^ a := by
    rw [max_eq_left hs.1.le]
    have hp := (radialTruncationBase_pos_le (inv_pos.mpr (hN n)) (hN n) hs.1.le).1
    have hbase : radialTruncationBase ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) s ≤ 1 + ρ := by
      unfold radialTruncationBase
      have hq : ((n : ℝ) + 1) * s / ((n : ℝ) + 1 + s) ≤ s := by
        apply (div_le_iff₀ (add_pos_of_pos_of_nonneg (hN n) hs.1.le)).mpr
        nlinarith [sq_nonneg s]
      have hi : ((n : ℝ) + 1)⁻¹ ≤ 1 := (inv_le_one₀ (hN n)).mpr (by have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
      linarith [hs.2]
    rw [Real.norm_eq_abs, radialTruncationWeight, abs_of_nonneg (Real.rpow_nonneg hp.le _)]
    exact Real.rpow_le_rpow hp.le hbase ha
  have hi := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc (0 : ℝ) ρ)) (fun _ : ℝ => (1 + ρ) ^ a)
    (fun n => (firstStripHilbertWeight_continuous
      (a := a) (inv_pos.mpr (hN n)) (hN n)).aestronglyMeasurable)
    (integrable_const _) (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hdom n s hs) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      simpa only [max_eq_left hs.1.le] using hw s hs.1.le)
  have he := (tendsto_const_nhds : Tendsto (fun _n : ℕ => (1 / 2 : ℝ))
    atTop (𝓝 (1 / 2 : ℝ))).mul hi
  simp_rw [← intervalIntegral.integral_of_le hρ] at he
  have hp : (1 / 2 : ℝ) * (∫ s in 0..ρ, s ^ a) =
      ‖z‖ ^ (2 * (a + 1)) / (2 * (a + 1)) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < a)),
      Real.zero_rpow (by linarith : a + 1 ≠ 0), sub_zero]
    have hz : (‖z‖ ^ 2) ^ (a + 1) = ‖z‖ ^ (2 * (a + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    rw [show ρ = ‖z‖ ^ 2 from rfl, hz]
    field_simp [show a + 1 ≠ 0 by linarith]
    <;> ring
  simpa only [firstStripHilbertPrimitive, ρ, hp] using he

/-- The primitive at bounded initial data is bounded independently of the
squared cutoff, before the moment exponent is chosen. -/
private theorem firstStripHilbertPrimitive_le_initial_bound {E : Type*}
    [NormedAddCommGroup E] {ε R a M : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (hM : 0 ≤ M)
    (z : E) (hz : ‖z‖ ≤ M) :
    firstStripHilbertPrimitive ε R a z ≤ (1 / 2 : ℝ) * M ^ 2 * (ε + M ^ 2) ^ a := by
  have hr : ‖z‖ ^ 2 ≤ M ^ 2 := (sq_le_sq₀ (norm_nonneg _) hM).mpr hz
  have hw (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (‖z‖ ^ 2)) :
      radialTruncationWeight ε R a (max s 0) ≤ (ε + M ^ 2) ^ a := by
    rw [max_eq_left hs.1]
    have hp := (radialTruncationBase_pos_le hε hR hs.1).1
    have hbase : radialTruncationBase ε R s ≤ ε + M ^ 2 := by
      unfold radialTruncationBase
      have hq : R * s / (R + s) ≤ s := by
        apply (div_le_iff₀ (add_pos_of_pos_of_nonneg hR hs.1)).mpr
        nlinarith [sq_nonneg s]
      linarith [hs.2]
    exact Real.rpow_le_rpow hp.le hbase ha
  have hi := intervalIntegral.integral_mono_on (μ := volume) (sq_nonneg ‖z‖)
    ((firstStripHilbertWeight_continuous hε hR).intervalIntegrable 0 _)
    (continuous_const.intervalIntegrable 0 _) hw
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
  unfold firstStripHilbertPrimitive
  have hm := mul_le_mul_of_nonneg_right hr
    (Real.rpow_nonneg (add_nonneg hε.le (sq_nonneg M)) a)
  nlinarith only [hi, hm]

/-- Integral Gronwall in the exact form used after removing the smoothing.
The rate is supplied only after the weighted mass has been compared with its
primitive, so no radial cutoff enters the exponential. -/
private theorem firstStrip_integral_gronwall {E : ℝ → ℝ} {k T : ℝ}
    (hE : Continuous E) (hk : 0 ≤ k)
    (hineq : ∀ s ∈ Icc (0 : ℝ) T,
      E s ≤ E 0 + k * (∫ u in 0..s, E u)) :
    ∀ s ∈ Icc (0 : ℝ) T, E s ≤ E 0 * Real.exp (k * s) := by
  let G := fun s => E 0 + k * (∫ u in 0..s, E u)
  have hd (s : ℝ) : HasDerivAt G (k * E s) s := by
    exact ((intervalIntegral.integral_hasDerivAt_right (hE.intervalIntegrable 0 s)
      (hE.stronglyMeasurableAtFilter _ _) hE.continuousAt).const_mul k).const_add _
  have hG : Continuous G := continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt
  have hb := le_gronwallBound_of_liminf_deriv_right_le
    (f := G) (f' := fun s => k * E s) (δ := E 0) (K := k) (ε := 0)
    (a := 0) (b := T) hG.continuousOn
    (fun s _ _ hr => (hd s).hasDerivWithinAt.liminf_right_slope_le hr)
    (by simp only [G, intervalIntegral.integral_same, mul_zero, add_zero]; exact le_rfl)
    (fun s hs => by
      simpa only [add_zero] using mul_le_mul_of_nonneg_left
        (hineq s ⟨hs.1, hs.2.le⟩) hk)
  intro s hs
  have hgs := hb s hs
  rw [gronwallBound_ε0, sub_zero] at hgs
  exact (hineq s hs).trans hgs

/-- Ordinary coefficient commutators vanish over the same full time-L2
orbit as the differentiated Friedrichs remainders. -/
private theorem firstStripSpatialKernel_coefficient_commutator_timeL2 {d : ℕ}
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) (j k : Fin d)
    (σ : Measure ℝ) (F : ℝ → Lp ℂ 2 (reducedLaw Q)) (hF : MemLp F 2 σ) :
    Tendsto (fun n => ∫ s,
      ‖firstStripKernelAverage Q (firstStripSpatialKernel d n)
        (firstStripSpatialKernel_smooth d n).continuous (firstStripSpatialKernel_compact d n)
          (complexCoefficientMul Q j k (F s)) -
        complexCoefficientMul Q j k (firstStripKernelAverage Q (firstStripSpatialKernel d n)
          (firstStripSpatialKernel_smooth d n).continuous
          (firstStripSpatialKernel_compact d n) (F s))‖ ^ 2 ∂σ)
      atTop (𝓝 0) := by
  let A := fun n => firstStripKernelAverage Q (firstStripSpatialKernel d n)
    (firstStripSpatialKernel_smooth d n).continuous (firstStripSpatialKernel_compact d n)
  let M := complexCoefficientMul Q j k
  let S : ℕ → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
    fun n => (A n).comp M - M.comp (A n)
  have hm (n : ℕ) : AEStronglyMeasurable (fun s => ‖S n (F s)‖ ^ 2) σ :=
    ((S n).continuous.comp_aestronglyMeasurable hF.aestronglyMeasurable).norm.pow 2
  have hb (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) : ‖S n f‖ ≤ 2 * ‖M‖ * ‖f‖ := by
    change ‖A n (M f) - M (A n f)‖ ≤ _
    calc
      _ ≤ ‖A n (M f)‖ + ‖M (A n f)‖ := norm_sub_le _ _
      _ ≤ ‖M‖ * ‖f‖ + ‖M‖ * ‖f‖ := add_le_add
        ((firstStripSpatialKernel_average_norm Q n (M f)).trans (M.le_opNorm f))
        ((M.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (firstStripSpatialKernel_average_norm Q n f) (norm_nonneg M)))
      _ = _ := by ring
  have hdom (n : ℕ) (s : ℝ) : ‖S n (F s)‖ ^ 2 ≤ (2 * ‖M‖) ^ 2 * ‖F s‖ ^ 2 := by
    calc
      _ ≤ (2 * ‖M‖ * ‖F s‖) ^ 2 := by gcongr; exact hb n (F s)
      _ = _ := by ring
  have hp (s : ℝ) : Tendsto (fun n => ‖S n (F s)‖ ^ 2) atTop (𝓝 0) := by
    have he := (firstStripSpatialKernel_average_tendsto Q (M (F s))).sub
      (M.continuous.tendsto (F s) |>.comp (firstStripSpatialKernel_average_tendsto Q (F s)))
    simpa only [S, A, Function.comp_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using he.norm.pow 2
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun s => (2 * ‖M‖) ^ 2 * ‖F s‖ ^ 2) (Eventually.of_forall hm)
    (Eventually.of_forall fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖S n (F s)‖)]
      exact hdom n s)
    ((hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _)
    (ae_of_all _ hp)
  simpa only [S, A, M, sub_apply, ContinuousLinearMap.comp_apply, integral_zero] using ht

/-- The actual scalar and differentiated equations form one coupled weak
system. Coefficient derivative multipliers are fixed before choosing either
smoothing, so their commutators can subsequently be removed in time-L2. -/
private theorem firstStrip_endpoint_coupled_weak_system {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (M : Fin d → Fin d → Fin d →
      Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hM : ∀ l j k v, M l j k v =ᵐ[reducedLaw Q] fun ω =>
      (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * v ω)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (t : ℝ≥0) (u : ℝ) (hzero : κ u = 0) (ht : κ (u - t) = 0)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K) :
    let U := firstStripTimeSmooth κ
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
    let H := fun k => firstStripTimeSmooth κ
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
    let V : Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := Fin.cons
      (firstStripTimeSmooth (deriv κ)
        (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u)
      (fun k => firstStripTimeSmooth (deriv κ)
        (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u)
    let A := firstStripKernelAverage Q K hK.continuous hKc
    let B := fun k => firstStripKernelAverage Q (coordinateDerivative k K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector k))
    let F : Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := Fin.cons U H
    let Z := fun q => A (F q)
    let G := fun q j => -(B j (F q))
    let τ : ℂ := if ν = .inr true then 2 * ζ else 0
    let zforce : ℂ := if ν = .inr true then 0 else ζ
    let S := fun j k v => A (complexCoefficientMul Q j k v) -
      complexCoefficientMul Q j k (A v)
    let R := fun l j k v => B l (complexCoefficientMul Q j k v) -
      complexCoefficientMul Q j k (B l v) + M l j k (A v)
    let J : Fin (d + 1) → Fin d → Lp ℂ 2 (reducedLaw Q) := Fin.cons
      (fun j => -((∑ k, S j k (H k)) - τ • S j ⟨0, by omega⟩ U))
      (fun l j => (∑ k, R l j k (H k)) - τ • R l j ⟨0, by omega⟩ U)
    let E : Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := Fin.cons
      (zforce • ∑ j, S j ⟨0, by omega⟩ (H j))
      (fun l => -zforce • ∑ j, R l j ⟨0, by omega⟩ (H j))
    ∃ C : Fin (d + 1) → Lp ℂ 2 (reducedLaw Q),
      (∀ᵐ ω ∂reducedLaw Q, ∀ q,
        C q ω = firstStripPointwiseFirstOrder ⟨0, by omega⟩ ν ζ ω
          (fun q j => G q j ω) q +
          firstStripPointwiseZerothOrder ⟨0, by omega⟩ ν ζ ω (fun q => Z q ω) q) ∧
      ∀ q (w : Lp ℂ 2 (reducedLaw Q)) (W : Fin d → Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) w W →
        inner ℂ w (A (V q)) =
          (-1 / 2 : ℂ) * (∑ j, ∑ k,
            inner ℂ (W j) (complexCoefficientMul Q j k (G q k))) +
          inner ℂ w (C q) + (1 / 2 : ℂ) * (∑ j, inner ℂ (W j) (J q j)) +
          inner ℂ w (E q) := by
  classical
  dsimp only
  let U := firstStripTimeSmooth κ
    (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
  let H := fun k => firstStripTimeSmooth κ
    (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
  let A := firstStripKernelAverage Q K hK.continuous hKc
  let B := fun k => firstStripKernelAverage Q (coordinateDerivative k K)
    ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hKc.fderiv_apply ℝ (unitVector k))
  let τ : ℂ := if ν = .inr true then 2 * ζ else 0
  let zforce : ℂ := if ν = .inr true then 0 else ζ
  obtain ⟨L₀, hL₀, he₀⟩ := firstStrip_endpoint_normalized_scalar_equation hd Q hQ
    β a μ ζ P T hP hT ν κ hκ t u hzero ht K hK hKc
  have hgrad (l : Fin d) := firstStrip_endpoint_normalized_gradient_equation hd D Q hQ
    β a μ hβ ζ P T hP hT ν κ hκ t u hzero ht K hK hKc l
  have hg (l : Fin d) :
      let R := fun j k v => B l (complexCoefficientMul Q j k v) -
        complexCoefficientMul Q j k (B l v) + M l j k (A v)
      ∃ (C : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
        (C₀ L : Fin d → Lp ℂ 2 (reducedLaw Q)),
        (∀ j k, C j k =ᵐ[reducedLaw Q] fun ω =>
          (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * (-(B j (H k))) ω +
          (coordinateDerivative j (coordinateDerivative l (fun y => ω.1 y j k)) 0 : ℂ) *
            A (H k) ω) ∧
        (∀ j, C₀ j =ᵐ[reducedLaw Q] fun ω =>
          (coordinateDerivative l (fun y => ω.1 y j ⟨0, by omega⟩) 0 : ℂ) * (-(B j U)) ω +
          (coordinateDerivative j (coordinateDerivative l
            (fun y => ω.1 y j ⟨0, by omega⟩)) 0 : ℂ) * A U ω) ∧
        (∀ j, L j =ᵐ[reducedLaw Q] fun ω =>
          (ω.1 0 j ⟨0, by omega⟩ : ℂ) * (-(B j (H l))) ω +
          (coordinateDerivative j (fun y => ω.1 y j ⟨0, by omega⟩) 0 : ℂ) * A (H l) ω) ∧
        ∀ w W, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) w W →
          inner ℂ w (A (firstStripTimeSmooth (deriv κ)
            (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s l) t u)) =
            (1 / 2 : ℂ) * (∑ j,
              (-(∑ k, inner ℂ (W j) (complexCoefficientMul Q j k (-(B k (H l))))) +
                (∑ k, inner ℂ w (C j k)) - τ * inner ℂ w (L j) - τ * inner ℂ w (C₀ j) +
                ((∑ k, inner ℂ (W j) (R j k (H k))) -
                  τ * inner ℂ (W j) (R j ⟨0, by omega⟩ U)))) +
            zforce * ((∑ j, inner ℂ w (complexCoefficientMul Q j ⟨0, by omega⟩
                (-(B j (H l))))) + (∑ j, inner ℂ w (M l j ⟨0, by omega⟩ (A (H j)))) -
              ∑ j, inner ℂ w (R j ⟨0, by omega⟩ (H j))) := by
    obtain ⟨M', hM', C, C₀, L, hC, hC₀, hL, he⟩ := hgrad l
    have hMeq : M' = M l := by
      funext j k
      apply ContinuousLinearMap.ext
      intro v
      exact Lp.ext ((hM' j k v).trans (hM l j k v).symm)
    subst M'
    exact ⟨C, C₀, L, hC, hC₀, hL, he⟩
  choose C₁ C₀ L hC₁ hC₀ hL he₁ using hg
  let C : Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := Fin.cons
    ((-τ / 2) • (∑ j, L₀ j) + zforce •
      (∑ j, complexCoefficientMul Q j ⟨0, by omega⟩ (A (H j))))
    (fun l => (1 / 2 : ℂ) • (∑ j, ∑ k, C₁ l j k) +
      (-τ / 2) • (∑ j, L l j) + (-τ / 2) • (∑ j, C₀ l j) +
      zforce • (∑ j, complexCoefficientMul Q j ⟨0, by omega⟩ (-(B j (H l)))) +
      zforce • (∑ j, M l j ⟨0, by omega⟩ (A (H j))))
  have hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) U H :=
    firstStrip_endpoint_time_gradient hd Q hQ β a μ hβ ζ P T hP hT ν κ hκ.continuous t u
  have hcompat := (firstStripKernelAverage_gradient_curl Q hH K hK hKc).1
  change ∀ l, -(B l U) = A (H l) at hcompat
  have hcompatFull := hcompat
  dsimp only [B, U, A, H] at hcompatFull
  refine ⟨C, ?_, ?_⟩
  · have hsum {ι : Type} [Fintype ι]
        (f : ι → Lp ℂ 2 (reducedLaw Q)) {g : ι → FieldPair d → ℂ}
        (hf : ∀ i, f i =ᵐ[reducedLaw Q] g i) :
        (∑ i, f i) =ᵐ[reducedLaw Q] fun ω => ∑ i, g i ω :=
      (Lp.coeFn_fun_finsetSum Finset.univ f).trans (by
        filter_upwards [ae_all_iff.mpr hf] with ω hω
        exact Finset.sum_congr rfl (fun i _ => hω i))
    have hadd {f g : Lp ℂ 2 (reducedLaw Q)} {F G : FieldPair d → ℂ}
        (hf : f =ᵐ[reducedLaw Q] F) (hg : g =ᵐ[reducedLaw Q] G) :
        (f + g) =ᵐ[reducedLaw Q] fun ω => F ω + G ω :=
      (Lp.coeFn_add f g).trans (hf.add hg)
    have hsmul (c : ℂ) {f : Lp ℂ 2 (reducedLaw Q)} {F : FieldPair d → ℂ}
        (hf : f =ᵐ[reducedLaw Q] F) :
        (c • f) =ᵐ[reducedLaw Q] fun ω => c * F ω :=
      (Lp.coeFn_smul c f).trans (hf.fun_comp fun z => c * z)
    have hSL := hsum L₀ hL₀
    have hSa := hsum (fun j => complexCoefficientMul Q j ⟨0, by omega⟩ (A (H j)))
      (fun j => complexCoefficientMul_coe Q j ⟨0, by omega⟩ (A (H j)))
    have hscalar := hadd (hsmul (-τ / 2) hSL) (hsmul zforce hSa)
    have hdiff (l : Fin d) := hadd (hadd (hadd (hadd
      (hsmul (1 / 2) (hsum (fun j => ∑ k, C₁ l j k)
        (fun j => hsum (C₁ l j) (hC₁ l j))))
      (hsmul (-τ / 2) (hsum (L l) (hL l))))
      (hsmul (-τ / 2) (hsum (C₀ l) (hC₀ l))))
      (hsmul zforce (hsum
        (fun j => complexCoefficientMul Q j ⟨0, by omega⟩ (-(B j (H l))))
        (fun j => complexCoefficientMul_coe Q j ⟨0, by omega⟩ (-(B j (H l)))))))
      (hsmul zforce (hsum (fun j => M l j ⟨0, by omega⟩ (A (H j)))
        (fun j => hM l j ⟨0, by omega⟩ (A (H j)))))
    filter_upwards [hscalar, ae_all_iff.mpr hdiff] with ω hs hg
    intro q
    refine Fin.cases ?_ (fun l => ?_) q
    · change C 0 ω = _
      simp only [C, Fin.cons_zero]
      rw [hs]
      simp only [firstStripPointwiseFirstOrder, firstStripPointwiseZerothOrder,
        Fin.cases_zero, Fin.cons_zero]
      dsimp only [U, H, A, B]
      simp_rw [hcompatFull]
      by_cases hν : ν = .inr true <;>
        simp only [τ, zforce, hν, ite_true, ite_false, zero_mul, mul_zero, zero_div,
          neg_zero, add_zero, zero_add, neg_mul, Fin.cons_zero] <;>
        simp only [Fin.cons_zero, Finset.sum_add_distrib] <;> ring
    · change C l.succ ω = _
      simp only [C, Fin.cons_succ]
      rw [hg l]
      simp only [firstStripPointwiseFirstOrder, firstStripPointwiseZerothOrder,
        Fin.cases_succ, Fin.cons_succ, Fin.cons_zero]
      dsimp only [U, H, A, B]
      by_cases hν : ν = .inr true <;>
        simp only [τ, zforce, hν, ite_true, ite_false, zero_mul, mul_zero, zero_div,
          neg_zero, add_zero, zero_add, neg_mul] <;>
        simp only [Finset.sum_add_distrib] <;> ring
  · intro q w W hW
    refine Fin.cases ?_ (fun l => ?_) q
    · have he := he₀ w W hW
      simp only [Fin.cons_zero, C, inner_add_right, inner_smul_right, inner_sum,
        inner_neg_right, inner_sub_right] at he ⊢
      dsimp only [U, H, A, B] at he ⊢
      simp_rw [hcompatFull] at he ⊢
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at he ⊢
      linear_combination he
    · have he := he₁ l w W hW
      simp only [Fin.cons_succ, C, inner_add_right, inner_smul_right, inner_sum,
        inner_neg_right, inner_sub_right] at he ⊢
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at he ⊢
      linear_combination he

/-- Testing an actual coefficient-coupled weak system by one common-radius
test gives a primitive growth rate linear in the exponent. Only the error
constant depends on the fixed radial regularization. -/
private theorem firstStrip_coupled_radial_weak_energy_bound {d : ℕ} (D : StructuralData d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε R α : ℝ), 0 < ε → 0 < R → 0 ≤ α →
      ∃ K : ℝ, 0 ≤ K ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ν : EndpointIndex d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
      ∀ (z v c e : Fin (d + 1) → Lp ℂ 2 (reducedLaw Q))
        (G J : Fin (d + 1) → Fin d → Lp ℂ 2 (reducedLaw Q)),
      (∀ q, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (z q) (G q)) →
      (∀ᵐ ω ∂reducedLaw Q, ∀ q,
        c q ω = firstStripPointwiseFirstOrder i ν ζ ω (fun q j => G q j ω) q +
          firstStripPointwiseZerothOrder i ν ζ ω (fun q => z q ω) q) →
      (∀ q (w : Lp ℂ 2 (reducedLaw Q)) (W : Fin d → Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) w W →
        inner ℝ w (v q) =
          (-1 / 2 : ℝ) * (∑ j, ∑ k,
            inner ℝ (W j) (complexCoefficientMul Q j k (G q k))) +
          inner ℝ w (c q) + (1 / 2 : ℝ) * (∑ j, inner ℝ (W j) (J q j)) +
          inner ℝ w (e q)) →
      (∫ ω, ∑ q, inner ℝ
        (radialTruncationWeight ε R α (∑ k, ‖z k ω‖ ^ 2) • z q ω) (v q ω)
          ∂reducedLaw Q) ≤
        C * (1 + α) * (∫ ω, firstStripHilbertPrimitive ε R α
          (WithLp.toLp 2 (fun q => z q ω) : EuclideanSpace ℂ (Fin (d + 1)))
            ∂reducedLaw Q) +
        K * ((∑ q, ∑ j, ‖J q j‖ ^ 2) + ∑ q, ‖e q‖ ^ 2) := by
  classical
  obtain ⟨C, hC, hrem⟩ := firstStrip_actual_radial_remainder_bound D
  refine ⟨C, hC, ?_⟩
  intro ε R α hε hR hα
  have hB : 0 < (ε + R) ^ α := Real.rpow_pos_of_pos (add_pos hε hR) _
  obtain ⟨K, hK, hrem⟩ := hrem α ((ε + R) ^ α) hα hB
  refine ⟨K / 2, by positivity, ?_⟩
  intro Q hQ i ν ζ hζ z v c e G J hG hc hweak
  obtain ⟨w, W, hW, hwval, hWval⟩ := firstStripSystem_radial_gradient hG hε hR hα
  let P := fun ω => ∑ q, ∑ j, ∑ k,
    inner ℝ (W q j ω) (complexCoefficientMul Q j k (G q k) ω)
  let Cpair := fun ω => ∑ q, inner ℝ (w q ω) (c q ω)
  let Jpair := fun ω => ∑ q, ∑ j, inner ℝ (W q j ω) (J q j ω)
  let Epair := fun ω => ∑ q, inner ℝ (w q ω) (e q ω)
  let F := fun ω => (-1 / 2 : ℝ) * P ω + Cpair ω + (1 / 2 : ℝ) * Jpair ω + Epair ω
  let Φ := fun ω => firstStripHilbertPrimitive ε R α
    (WithLp.toLp 2 (fun q => z q ω) : EuclideanSpace ℂ (Fin (d + 1)))
  let Berr := fun ω => (∑ q, ∑ j, ‖J q j ω‖ ^ 2) + ∑ q, ‖e q ω‖ ^ 2
  have hiP : Integrable P (reducedLaw Q) := integrable_finsetSum _ fun q _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      L2.integrable_inner (𝕜 := ℝ) (W q j) (complexCoefficientMul Q j k (G q k))
  have hiC : Integrable Cpair (reducedLaw Q) := integrable_finsetSum _ fun q _ =>
    L2.integrable_inner (𝕜 := ℝ) (w q) (c q)
  have hiJ : Integrable Jpair (reducedLaw Q) := integrable_finsetSum _ fun q _ =>
    integrable_finsetSum _ fun j _ => L2.integrable_inner (𝕜 := ℝ) (W q j) (J q j)
  have hiE : Integrable Epair (reducedLaw Q) := integrable_finsetSum _ fun q _ =>
    L2.integrable_inner (𝕜 := ℝ) (w q) (e q)
  have hiF : Integrable F (reducedLaw Q) :=
    (((hiP.const_mul _).add hiC).add (hiJ.const_mul _)).add hiE
  have hiΦ : Integrable Φ (reducedLaw Q) :=
    (firstStripHilbertPrimitive_integrable (reducedLaw Q)
      (firstStripSystemPack (reducedLaw Q) (d + 1) z) hε hR hα).congr
        ((firstStripSystemPack_coe (reducedLaw Q) (d + 1) z).fun_comp
          (firstStripHilbertPrimitive ε R α))
  have hiB : Integrable Berr (reducedLaw Q) :=
    (integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun j _ =>
      (Lp.memLp (J q j)).norm.integrable_sq).add
        (integrable_finsetSum _ fun q _ => (Lp.memLp (e q)).norm.integrable_sq)
  have hpair {ι : Type} [Fintype ι] (f g : ι → Lp ℂ 2 (reducedLaw Q)) :
      (∫ ω, ∑ x, inner ℝ (f x ω) (g x ω) ∂reducedLaw Q) =
        ∑ x, inner ℝ (f x) (g x) := by
    rw [integral_finsetSum _ (fun x _ => L2.integrable_inner (𝕜 := ℝ) (f x) (g x))]
    rfl
  have hPi : (∫ ω, P ω ∂reducedLaw Q) =
      ∑ q, ∑ j, ∑ k, inner ℝ (W q j) (complexCoefficientMul Q j k (G q k)) := by
    simpa only [P, Fintype.sum_prod_type] using
      hpair (fun x : Fin (d + 1) × Fin d × Fin d => W x.1 x.2.1)
        (fun x : Fin (d + 1) × Fin d × Fin d => complexCoefficientMul Q x.2.1 x.2.2 (G x.1 x.2.2))
  have hJi : (∫ ω, Jpair ω ∂reducedLaw Q) =
      ∑ q, ∑ j, inner ℝ (W q j) (J q j) := by
    simpa only [Jpair, Fintype.sum_prod_type] using
      hpair (fun x : Fin (d + 1) × Fin d => W x.1 x.2) (fun x : Fin (d + 1) × Fin d => J x.1 x.2)
  have hFi : (∫ ω, F ω ∂reducedLaw Q) =
      ∑ q, inner ℝ (w q) (v q) := by
    have hsplit₁ : (∫ ω, F ω ∂reducedLaw Q) =
        (∫ ω, (-1 / 2 : ℝ) * P ω + Cpair ω + (1 / 2 : ℝ) * Jpair ω
          ∂reducedLaw Q) + ∫ ω, Epair ω ∂reducedLaw Q :=
      integral_add (((hiP.const_mul _).add hiC).add (hiJ.const_mul _)) hiE
    have hsplit₂ : (∫ ω, (-1 / 2 : ℝ) * P ω + Cpair ω + (1 / 2 : ℝ) * Jpair ω
          ∂reducedLaw Q) =
        (∫ ω, (-1 / 2 : ℝ) * P ω + Cpair ω ∂reducedLaw Q) +
          ∫ ω, (1 / 2 : ℝ) * Jpair ω ∂reducedLaw Q :=
      integral_add ((hiP.const_mul _).add hiC) (hiJ.const_mul _)
    have hsplit₃ : (∫ ω, (-1 / 2 : ℝ) * P ω + Cpair ω ∂reducedLaw Q) =
        (∫ ω, (-1 / 2 : ℝ) * P ω ∂reducedLaw Q) + ∫ ω, Cpair ω ∂reducedLaw Q :=
      integral_add (hiP.const_mul _) hiC
    rw [hsplit₁, hsplit₂, hsplit₃, integral_const_mul, integral_const_mul,
      hPi, hpair w c, hJi, hpair w e]
    simp_rw [hweak _ _ _ (hW _)]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcoef := ae_all_iff.mpr fun q => ae_all_iff.mpr fun j => ae_all_iff.mpr fun k =>
    complexCoefficientMul_coe Q j k (G q k)
  have hbound : ∀ᵐ ω ∂reducedLaw Q,
      F ω ≤ C * (1 + α) * Φ ω + (K / 2) * Berr ω := by
    filter_upwards [hrem Q hQ, hc, ae_all_iff.mpr hwval,
      ae_all_iff.mpr (fun q => ae_all_iff.mpr (hWval q)), hcoef] with ω hr hc hw hW hcM
    let ρ : ℝ := ∑ q, ‖z q ω‖ ^ 2
    have hρ : 0 ≤ ρ := Finset.sum_nonneg fun _ _ => sq_nonneg _
    let b := radialTruncationWeight ε R α ρ
    let s := radialTruncationSlope ε R α ρ
    have hb : 0 ≤ b := Real.rpow_nonneg
      (radialTruncationBase_pos_le hε hR hρ).1.le _
    have hbB : b ≤ (ε + R) ^ α := Real.rpow_le_rpow
      (radialTruncationBase_pos_le hε hR hρ).1.le
      (radialTruncationBase_pos_le hε hR hρ).2 hα
    have hs := radialTruncationSlope_mul_le hε hR hα hρ
    have hr := hr i ν ζ hζ b s hb hs.1 hbB (fun q => z q ω)
      (fun q j => G q j ω) (fun q j => J q j ω) (fun q => e q ω) hs.2
    have hP : P ω = (∑ q, ∑ j, ∑ k,
        star (firstStripSystemRadialDifferential b s
          (fun q => z q ω) (fun q j => G q j ω) q j) *
            (ω.1 0 j k : ℂ) * G q k ω).re := by
      dsimp only [P]
      simp_rw [hcM, hW, real_inner_eq_re_inner ℂ, RCLike.inner_apply',
        RCLike.re_to_complex, ← mul_assoc]
      simp only [Complex.re_sum, Complex.star_def, b, s, ρ]
    have hCp : Cpair ω =
        b * (∑ q, inner ℝ (z q ω)
          (firstStripPointwiseFirstOrder i ν ζ ω (fun q j => G q j ω) q)) +
        b * (∑ q, inner ℝ (z q ω)
          (firstStripPointwiseZerothOrder i ν ζ ω (fun q => z q ω) q)) := by
      dsimp only [Cpair]
      simp_rw [hw, hc, real_inner_smul_left, inner_add_right]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, b, ρ]
      ring
    have hJp : Jpair ω = ∑ q, ∑ j,
        inner ℝ (firstStripSystemRadialDifferential b s
          (fun q => z q ω) (fun q j => G q j ω) q j) (J q j ω) := by
      dsimp only [Jpair]
      simp_rw [hW]
      rfl
    have hEp : Epair ω = b * (∑ q, inner ℝ (z q ω) (e q ω)) := by
      dsimp only [Epair]
      simp_rw [hw, real_inner_smul_left]
      rw [← Finset.mul_sum]
    have hm := firstStripHilbertPrimitive_mass_le hε hR hα
      (WithLp.toLp 2 (fun q => z q ω) : EuclideanSpace ℂ (Fin (d + 1)))
    simp only [PiLp.norm_sq_eq_of_L2, WithLp.ofLp_toLp] at hm
    have hCm := mul_le_mul_of_nonneg_left hm (zero_le_one.trans hC)
    dsimp only [F]
    rw [hP, hCp, hJp, hEp]
    dsimp only [Φ, Berr, b, s, ρ] at *
    nlinarith only [hr, hCm]
  have hint := integral_mono_ae hiF
    ((hiΦ.const_mul (C * (1 + α))).add (hiB.const_mul (K / 2))) hbound
  simp only [Pi.add_apply] at hint
  rw [hFi, integral_add (hiΦ.const_mul _) (hiB.const_mul _),
    integral_const_mul, integral_const_mul] at hint
  have hsq (f : Lp ℂ 2 (reducedLaw Q)) :
      (∫ ω, ‖f ω‖ ^ 2 ∂reducedLaw Q) = ‖f‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) f f).symm
  have hBi : (∫ ω, Berr ω ∂reducedLaw Q) =
      (∑ q, ∑ j, ‖J q j‖ ^ 2) + ∑ q, ‖e q‖ ^ 2 := by
    dsimp only [Berr]
    rw [integral_add
      (integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun j _ =>
        (Lp.memLp (J q j)).norm.integrable_sq)
      (integrable_finsetSum _ fun q _ => (Lp.memLp (e q)).norm.integrable_sq)]
    simp_rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ fun j _ =>
      (Lp.memLp (J q j)).norm.integrable_sq)]
    simp_rw [integral_finsetSum _ (fun j _ => (Lp.memLp (J _ j)).norm.integrable_sq),
      integral_finsetSum _ (fun q _ => (Lp.memLp (e q)).norm.integrable_sq), hsq]
  rw [hBi] at hint
  rw [← hpair w v] at hint
  convert hint using 1
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hwval] with ω hw
  simp_rw [hw]

/-- Uniform bounds for the regularized common-radius primitive give the exact
unregularized radial moment, retaining integrability. -/
private theorem firstStripSystem_moment_of_primitive_bound {α : Type*}
    [MeasurableSpace α] (μ : Measure α) {N : ℕ}
    (z : Fin N → Lp ℂ 2 μ) {a B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hb : ∀ n : ℕ, (∫ ω, firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹
      ((n : ℝ) + 1) a
      (WithLp.toLp 2 (fun q => z q ω) : EuclideanSpace ℂ (Fin N)) ∂μ) ≤ B) :
    Integrable (fun ω => (∑ q, ‖z q ω‖ ^ 2) ^ (a + 1)) μ ∧
      (∫ ω, (∑ q, ‖z q ω‖ ^ 2) ^ (a + 1) ∂μ) ≤ 2 * (a + 1) * B := by
  let c := 2 * (a + 1)
  have hc : 0 < c := by dsimp only [c]; positivity
  let Z := fun ω => (WithLp.toLp 2 (fun q => z q ω) : EuclideanSpace ℂ (Fin N))
  let f := fun (n : ℕ) ω => c * firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹
    ((n : ℝ) + 1) a (Z ω)
  have hN (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hnorm (ω) : ‖Z ω‖ ^ (2 * (a + 1)) = (∑ q, ‖z q ω‖ ^ 2) ^ (a + 1) := by
    rw [Real.rpow_mul (norm_nonneg _)]
    norm_num only [Real.rpow_two]
    simp only [Z, PiLp.norm_sq_eq_of_L2, WithLp.ofLp_toLp]
  have hi (n : ℕ) : Integrable (f n) μ := by
    apply Integrable.const_mul
    exact (firstStripHilbertPrimitive_integrable μ (firstStripSystemPack μ N z)
      (inv_pos.mpr (hN n)) (hN n) ha).congr
        ((firstStripSystemPack_coe μ N z).fun_comp
          (firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) a))
  apply firstStrip_integrable_limit_of_nonnegative_bound μ (mul_nonneg hc.le hB) hi
  · exact fun n => ae_of_all _ fun ω => mul_nonneg hc.le
      (firstStripHilbertPrimitive_nonneg (inv_pos.mpr (hN n)) (hN n) (Z ω))
  · exact ae_of_all _ fun ω => Real.rpow_nonneg
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) _
  · apply ae_of_all
    intro ω
    have ht := (tendsto_const_nhds : Tendsto (fun _n : ℕ => c) atTop (𝓝 c)).mul
      (firstStripHilbertPrimitive_joint_tendsto ha (Z ω))
    have he : c * (‖Z ω‖ ^ (2 * (a + 1)) / (2 * (a + 1))) =
        (∑ q, ‖z q ω‖ ^ 2) ^ (a + 1) := by
      rw [hnorm]
      dsimp only [c] at hc ⊢
      field_simp [hc.ne']
    simpa only [f, he] using ht
  · intro n
    change (∫ ω, c * firstStripHilbertPrimitive _ _ _ (Z ω) ∂μ) ≤ c * B
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hb n) hc.le

/-- The polynomial prefactor from the initial primitive is absorbed into
one structural base to the exact real moment exponent. -/
private theorem firstStrip_initial_power_prefactor_bound {p M : ℝ}
    (hp : 2 ≤ p) :
    (p / 2) * M ^ 2 * (1 + M ^ 2) ^ (p / 2 - 1) ≤
      (Real.exp 1 * (1 + M ^ 2)) ^ p := by
  let b := 1 + M ^ 2
  have hb : 1 ≤ b := by dsimp only [b]; nlinarith only [sq_nonneg M]
  have hbp : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hr : M ^ 2 * b ^ (p / 2 - 1) ≤ b ^ (p / 2) := by
    calc
      _ ≤ b * b ^ (p / 2 - 1) := mul_le_mul_of_nonneg_right
        (by dsimp only [b]; linarith) (Real.rpow_nonneg hbp.le _)
      _ = b ^ (1 : ℝ) * b ^ (p / 2 - 1) := by rw [Real.rpow_one]
      _ = b ^ (p / 2) := by
        rw [← Real.rpow_add hbp]
        congr 1
        ring
  have he : p / 2 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hpow : b ^ (p / 2) ≤ b ^ p :=
    Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  calc
    _ = (p / 2) * (M ^ 2 * b ^ (p / 2 - 1)) := by dsimp only [b]; ring
    _ ≤ (p / 2) * b ^ (p / 2) := mul_le_mul_of_nonneg_left hr (by linarith)
    _ ≤ Real.exp p * b ^ p := mul_le_mul he hpow
      (Real.rpow_nonneg hbp.le _) (Real.exp_pos _).le
    _ = (Real.exp 1 * b) ^ p := by
      rw [Real.mul_rpow (Real.exp_pos _).le hbp.le, ← Real.exp_mul, one_mul]

/-- The actual endpoint and its differentiated coordinates satisfy the
regularized common-radius energy inequality, with structural growth constant
chosen before the law and radial parameters. -/
private theorem firstStrip_endpoint_radial_energy_bound {d : ℕ} (D : StructuralData d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε R α : ℝ), 0 < ε → 0 < R → 0 ≤ α →
      ∃ L : ℝ, 0 ≤ L ∧ ∀
    (hd : 2 ≤ d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (M : Fin d → Fin d → Fin d →
      Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hM : ∀ l j k v, M l j k v =ᵐ[reducedLaw Q] fun ω =>
      (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * v ω)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ζ : ℂ) (hζ : ‖ζ‖ ≤ 4)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (t : ℝ≥0) (u : ℝ) (hzero : κ u = 0) (ht : κ (u - t) = 0)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K),
    let U := firstStripTimeSmooth κ
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
    let H := fun k => firstStripTimeSmooth κ
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
    let V : Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := Fin.cons
      (firstStripTimeSmooth (deriv κ)
        (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u)
      (fun k => firstStripTimeSmooth (deriv κ)
        (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u)
    let A := firstStripKernelAverage Q K hK.continuous hKc
    let B := fun k => firstStripKernelAverage Q (coordinateDerivative k K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector k))
    let F : Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := Fin.cons U H
    let Z := fun q => A (F q)
    let G := fun q j => -(B j (F q))
    let τ : ℂ := if ν = .inr true then 2 * ζ else 0
    let zforce : ℂ := if ν = .inr true then 0 else ζ
    let S := fun j k v => A (complexCoefficientMul Q j k v) -
      complexCoefficientMul Q j k (A v)
    let Rcomm := fun l j k v => B l (complexCoefficientMul Q j k v) -
      complexCoefficientMul Q j k (B l v) + M l j k (A v)
    let J : Fin (d + 1) → Fin d → Lp ℂ 2 (reducedLaw Q) := Fin.cons
      (fun j => -((∑ k, S j k (H k)) - τ • S j ⟨0, by omega⟩ U))
      (fun l j => (∑ k, Rcomm l j k (H k)) - τ • Rcomm l j ⟨0, by omega⟩ U)
    let E : Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := Fin.cons
      (zforce • ∑ j, S j ⟨0, by omega⟩ (H j))
      (fun l => -zforce • ∑ j, Rcomm l j ⟨0, by omega⟩ (H j))
    (∫ ω, ∑ q, inner ℝ
      (radialTruncationWeight ε R α (∑ k, ‖Z k ω‖ ^ 2) • Z q ω)
      (A (V q) ω) ∂reducedLaw Q) ≤
      C * (1 + α) * (∫ ω, firstStripHilbertPrimitive ε R α
        (WithLp.toLp 2 (fun q => Z q ω) : EuclideanSpace ℂ (Fin (d + 1)))
          ∂reducedLaw Q) +
      L * ((∑ q, ∑ j, ‖J q j‖ ^ 2) + ∑ q, ‖E q‖ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := firstStrip_coupled_radial_weak_energy_bound D
  refine ⟨C, hC, ?_⟩
  intro ε R α hε hR hα
  obtain ⟨L, hL, hb⟩ := hb ε R α hε hR hα
  refine ⟨L, hL, ?_⟩
  intro hd Q hQ M hM β a μ hβ ζ hζ P T hP hT ν κ hκ t u hzero ht K hK hKc
  dsimp only
  obtain ⟨Cc, hc, he⟩ := firstStrip_endpoint_coupled_weak_system hd D Q hQ M hM
    β a μ hβ ζ P T hP hT ν κ hκ t u hzero ht K hK hKc
  refine hb Q hQ ⟨0, by omega⟩ ν ζ hζ _ _ Cc _ _ _ ?_ hc ?_
  · intro q
    exact firstStripKernelAverage_gradient Q K hK hKc _
  · intro q w W hW
    have hh := congrArg Complex.re (he q w W hW)
    have hn : (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by norm_num
    have hp : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    have hr (f g : Lp ℂ 2 (reducedLaw Q)) :
        inner ℝ f g = (inner ℂ f g).re := by
      rw [L2.inner_def, L2.inner_def]
      exact integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
    simpa only [hn, hp, Complex.add_re, Complex.re_ofReal_mul, Complex.re_sum,
      hr] using hh

/-- Integrating a regularized radial differential estimate uses the exact
finite-system energy identity and retains the full error integral. -/
private theorem firstStripSystem_integrated_energy_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N : ℕ} {f g : ℝ → Fin N → Lp ℂ 2 μ}
    (hf : ∀ u, HasDerivAt f (g u) u) (hg : Continuous g)
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a)
    {u₀ u₁ c : ℝ} (hu : u₀ ≤ u₁) {err : ℝ → ℝ}
    (herr : IntervalIntegrable err volume u₀ u₁)
    (hbound : ∀ u ∈ Icc u₀ u₁,
      (∫ ω, ∑ q : Fin N, inner ℝ
        (radialTruncationWeight ε R a (∑ k, ‖f u k ω‖ ^ 2) • f u q ω)
        (g u q ω) ∂μ) ≤
      c * (∫ ω, firstStripHilbertPrimitive ε R a
        (WithLp.toLp 2 (fun q => f u q ω) : EuclideanSpace ℂ (Fin N)) ∂μ) + err u) :
    (∫ ω, firstStripHilbertPrimitive ε R a
      (WithLp.toLp 2 (fun q => f u₁ q ω) : EuclideanSpace ℂ (Fin N)) ∂μ) ≤
    (∫ ω, firstStripHilbertPrimitive ε R a
      (WithLp.toLp 2 (fun q => f u₀ q ω) : EuclideanSpace ℂ (Fin N)) ∂μ) +
    c * (∫ u in u₀..u₁, ∫ ω, firstStripHilbertPrimitive ε R a
      (WithLp.toLp 2 (fun q => f u q ω) : EuclideanSpace ℂ (Fin N)) ∂μ) +
    ∫ u in u₀..u₁, err u := by
  let E := fun u => ∫ ω, firstStripHilbertPrimitive ε R a
    (WithLp.toLp 2 (fun q => f u q ω) : EuclideanSpace ℂ (Fin N)) ∂μ
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun u => (hf u).continuousAt
  have hEc : Continuous E := continuous_iff_continuousAt.mpr fun u =>
    (firstStripSystem_energy_chain (hf u) hε hR ha).continuousAt
  have hpc := firstStripSystem_energy_pairing_continuous hfc hg hε hR ha
  have hm := intervalIntegral.integral_mono_on hu (hpc.intervalIntegrable u₀ u₁)
    (((hEc.const_mul c).intervalIntegrable u₀ u₁).add herr) hbound
  rw [firstStripSystem_energy_FTC hf hg hε hR ha u₀ u₁,
    intervalIntegral.integral_add ((hEc.const_mul c).intervalIntegrable u₀ u₁) herr,
    intervalIntegral.integral_const_mul] at hm
  change E u₁ ≤ E u₀ + c * (∫ u in u₀..u₁, E u) + ∫ u in u₀..u₁, err u
  change E u₁ - E u₀ ≤ c * (∫ u in u₀..u₁, E u) + ∫ u in u₀..u₁, err u at hm
  linarith only [hm]

/-- Time-L2 disappearance is stable under the finite error algebra used by
the coupled endpoint system. -/
private theorem firstStrip_timeL2_add_tendsto {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f g : ℕ → α → E}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (htf : Tendsto (fun n => ∫ s, ‖f n s‖ ^ 2 ∂μ) atTop (𝓝 0))
    (htg : Tendsto (fun n => ∫ s, ‖g n s‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, ‖f n s + g n s‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hi {v : α → E} (h : MemLp v 2 μ) : Integrable (fun s => ‖v s‖ ^ 2) μ :=
    h.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hb (n : ℕ) : (∫ s, ‖f n s + g n s‖ ^ 2 ∂μ) ≤
      2 * ((∫ s, ‖f n s‖ ^ 2 ∂μ) + ∫ s, ‖g n s‖ ^ 2 ∂μ) := by
    calc
      _ ≤ ∫ s, 2 * (‖f n s‖ ^ 2 + ‖g n s‖ ^ 2) ∂μ := by
        apply integral_mono (hi ((hf n).add (hg n))) (((hi (hf n)).add (hi (hg n))).const_mul 2)
        intro s
        change ‖f n s + g n s‖ ^ 2 ≤ 2 * (‖f n s‖ ^ 2 + ‖g n s‖ ^ 2)
        have hn := norm_add_le (f n s) (g n s)
        have hsq : ‖f n s + g n s‖ ^ 2 ≤ (‖f n s‖ + ‖g n s‖) ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg _) hn _
        nlinarith only [hsq, sq_nonneg (‖f n s‖ - ‖g n s‖)]
      _ = _ := by rw [integral_const_mul, integral_add (hi (hf n)) (hi (hg n))]
  apply squeeze_zero (fun n => integral_nonneg (fun s => sq_nonneg _)) hb
  simpa only [add_zero, mul_zero] using (htf.add htg).const_mul 2

private theorem firstStrip_timeL2_smul_tendsto {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure α}
    {f : ℕ → α → E} (c : ℂ)
    (ht : Tendsto (fun n => ∫ s, ‖f n s‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, ‖c • f n s‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  simpa only [norm_smul, mul_pow, integral_const_mul, mul_zero] using
    ht.const_mul (‖c‖ ^ 2)

private theorem firstStrip_timeL2_sum_tendsto {α E ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} (S : Finset ι)
    {f : ι → ℕ → α → E}
    (hf : ∀ i ∈ S, ∀ n, MemLp (f i n) 2 μ)
    (ht : ∀ i ∈ S, Tendsto (fun n => ∫ s, ‖f i n s‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, ‖∑ i ∈ S, f i n s‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), integral_zero] using tendsto_const_nhds
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    apply firstStrip_timeL2_add_tendsto
    · exact hf i (Finset.mem_insert_self i S)
    · intro n
      exact memLp_finsetSum S (fun j hj => hf j (Finset.mem_insert_of_mem hj) n)
    · exact ht i (Finset.mem_insert_self i S)
    · exact ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => ht j (Finset.mem_insert_of_mem hj))

/-- The Euclidean packing retains exactly the sum of the component L2 energies. -/
private theorem firstStripSystemPack_norm_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {N : ℕ} (z : Fin N → Lp ℂ 2 μ) :
    ‖firstStripSystemPack μ N z‖ ^ 2 = ∑ q, ‖z q‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ ω, ∑ q, ‖z q ω‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [firstStripSystemPack_coe μ N z] with ω hω
      rw [real_inner_self_eq_norm_sq, hω, PiLp.norm_sq_eq_of_L2]
    _ = ∑ q, ‖z q‖ ^ 2 := by
      rw [integral_finsetSum _ (fun q _ => (Lp.memLp (z q)).norm.integrable_sq)]
      apply Finset.sum_congr rfl
      intro q _
      simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) (z q) (z q)).symm

/-- Fixed radial regularizers have a time-integrable quadratic majorant. -/
private theorem firstStripSystem_energy_growth {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {N : ℕ} (z : Fin N → Lp ℂ 2 μ)
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    ‖∫ ω, firstStripHilbertPrimitive ε R a
      (WithLp.toLp 2 (fun q => z q ω) : EuclideanSpace ℂ (Fin N)) ∂μ‖ ≤
    ((1 + 2 * a) * (ε + R) ^ a) * ∑ q, ‖z q‖ ^ 2 := by
  rw [← firstStripSystemPack_energy]
  calc
    _ ≤ ∫ ω, ‖firstStripHilbertPrimitive ε R a (firstStripSystemPack μ N z ω)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ((1 + 2 * a) * (ε + R) ^ a) * ‖firstStripSystemPack μ N z ω‖ ^ 2 ∂μ :=
      integral_mono (firstStripHilbertPrimitive_integrable μ _ hε hR ha).norm
        ((Lp.memLp (firstStripSystemPack μ N z)).norm.integrable_sq.const_mul _)
        (fun ω => firstStripHilbertPrimitive_growth hε hR ha _)
    _ = _ := by
      rw [integral_const_mul]
      have he := L2.inner_def (𝕜 := ℝ) (firstStripSystemPack μ N z) (firstStripSystemPack μ N z)
      simp only [real_inner_self_eq_norm_sq] at he
      rw [← he, firstStripSystemPack_norm_sq]

/-- Strong coordinate limits with an actual quadratic time-energy majorant
pass under the time integral of the common-radius primitive. -/
private theorem firstStripSystem_energy_time_tendsto {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (σ : Measure ℝ) {N : ℕ}
    (f : ℕ → ℝ → Fin N → Lp ℂ 2 μ) (g : ℝ → Fin N → Lp ℂ 2 μ)
    (hf : ∀ n, Continuous (f n))
    (b : ℝ → ℝ) (hbi : Integrable b σ)
    (ht : ∀ᵐ s ∂σ, Tendsto (fun n => f n s) atTop (𝓝 (g s)))
    (hb : ∀ n s, (∑ q, ‖f n s q‖ ^ 2) ≤ b s)
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    Tendsto (fun n => ∫ s, ∫ ω, firstStripHilbertPrimitive ε R a
      (WithLp.toLp 2 (fun q => f n s q ω) : EuclideanSpace ℂ (Fin N)) ∂μ ∂σ)
      atTop (𝓝 (∫ s, ∫ ω, firstStripHilbertPrimitive ε R a
        (WithLp.toLp 2 (fun q => g s q ω) : EuclideanSpace ℂ (Fin N)) ∂μ ∂σ)) := by
  let C := (1 + 2 * a) * (ε + R) ^ a
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hc : Continuous (fun z : Lp (EuclideanSpace ℂ (Fin N)) 2 μ =>
      ∫ ω, firstStripHilbertPrimitive ε R a (z ω) ∂μ) :=
    continuous_iff_continuousAt.mpr fun z =>
      (firstStripHilbertPrimitive_integral_hasFDerivAt μ z hε hR ha).continuousAt
  apply tendsto_integral_filter_of_dominated_convergence
    (fun s => C * b s)
  · apply Eventually.of_forall
    intro n
    have hm : AEStronglyMeasurable (fun s => ∫ ω, firstStripHilbertPrimitive ε R a
        (firstStripSystemPack μ N (f n s) ω) ∂μ) σ :=
      (hc.comp ((firstStripSystemPack μ N).continuous.comp (hf n))).aestronglyMeasurable
    simpa only [Function.comp_def, firstStripSystemPack_energy] using hm
  · apply Eventually.of_forall
    intro n
    apply ae_of_all
    intro s
    exact (firstStripSystem_energy_growth μ (f n s) hε hR ha).trans
      (mul_le_mul_of_nonneg_left (hb n s) hC)
  · exact hbi.const_mul C
  · filter_upwards [ht] with s hs
    exact firstStripSystem_energy_tendsto hs hε hR ha

/-- A positive normalized time mollifier preserves a uniform orbit bound. -/
private theorem firstStripTimeSmooth_norm_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ContDiffBump (0 : ℝ)) (F : ℝ → E) (hF : Continuous F)
    (t : ℝ≥0) (u M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ s ∈ Icc (0 : ℝ) (t : ℝ), ‖F s‖ ≤ M) :
    ‖firstStripTimeSmooth (φ.normed volume) F t u‖ ≤ M := by
  let κ := φ.normed volume
  have hκ : Continuous κ := φ.continuous_normed
  have hi : Integrable (fun s => κ (u - s)) volume :=
    φ.integrable_normed.comp_sub_left u
  have hmass : (∫ s in Icc (0 : ℝ) (t : ℝ), κ (u - s)) ≤ 1 := by
    calc
      _ ≤ ∫ s, κ (u - s) := integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ fun s => φ.nonneg_normed (u - s)) hi
      _ = 1 := by rw [integral_sub_left_eq_self, φ.integral_normed]
  calc
    _ ≤ ∫ s in Icc (0 : ℝ) (t : ℝ), ‖κ (u - s) • F s‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s in Icc (0 : ℝ) (t : ℝ), κ (u - s) * M := by
      apply integral_mono_ae (((hκ.comp (continuous_const.sub continuous_id)).smul hF).norm.integrableOn_Icc)
        (hi.integrableOn.mul_const M)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      change ‖κ (u - s) • F s‖ ≤ κ (u - s) * M
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed _)]
      exact mul_le_mul_of_nonneg_left (hb s hs) (φ.nonneg_normed _)
    _ ≤ M := by
      rw [integral_mul_const]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass hM

/-- The actual coupled endpoint system satisfies the common-radius energy
inequality on every interior time interval, with its explicit commutator errors. -/
private theorem firstStrip_endpoint_integrated_radial_energy_bound {d : ℕ} (D : StructuralData d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε R α : ℝ), 0 < ε → 0 < R → 0 ≤ α →
      ∃ L : ℝ, 0 ≤ L ∧ ∀
    (hd : 2 ≤ d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (M : Fin d → Fin d → Fin d →
      Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hM : ∀ l j k v, M l j k v =ᵐ[reducedLaw Q] fun ω =>
      (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * v ω)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ζ : ℂ) (hζ : ‖ζ‖ ≤ 4)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    (t : ℝ≥0) (u₀ u₁ : ℝ) (hu : u₀ ≤ u₁)
    (hzero : ∀ u ∈ Icc u₀ u₁, κ u = 0)
    (ht : ∀ u ∈ Icc u₀ u₁, κ (u - t) = 0)
    (K : Vec d → ℝ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K),
    let U := fun u => firstStripTimeSmooth κ
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
    let H := fun u k => firstStripTimeSmooth κ
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
    let A := firstStripKernelAverage Q K hK.continuous hKc
    let B := fun k => firstStripKernelAverage Q (coordinateDerivative k K)
      ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hKc.fderiv_apply ℝ (unitVector k))
    let F : ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := fun u => Fin.cons (U u) (H u)
    let Z := fun u q => A (F u q)
    let τ : ℂ := if ν = .inr true then 2 * ζ else 0
    let zforce : ℂ := if ν = .inr true then 0 else ζ
    let S := fun j k v => A (complexCoefficientMul Q j k v) -
      complexCoefficientMul Q j k (A v)
    let Rcomm := fun l j k v => B l (complexCoefficientMul Q j k v) -
      complexCoefficientMul Q j k (B l v) + M l j k (A v)
    let J : ℝ → Fin (d + 1) → Fin d → Lp ℂ 2 (reducedLaw Q) := fun u => Fin.cons
      (fun j => -((∑ k, S j k (H u k)) - τ • S j ⟨0, by omega⟩ (U u)))
      (fun l j => (∑ k, Rcomm l j k (H u k)) - τ • Rcomm l j ⟨0, by omega⟩ (U u))
    let E : ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := fun u => Fin.cons
      (zforce • ∑ j, S j ⟨0, by omega⟩ (H u j))
      (fun l => -zforce • ∑ j, Rcomm l j ⟨0, by omega⟩ (H u j))
    let energy := fun u => ∫ ω, firstStripHilbertPrimitive ε R α
      (WithLp.toLp 2 (fun q => Z u q ω) : EuclideanSpace ℂ (Fin (d + 1)))
        ∂reducedLaw Q
    energy u₁ ≤ energy u₀ + C * (1 + α) * (∫ u in u₀..u₁, energy u) +
      L * (∫ u in u₀..u₁, (∑ q, ∑ j, ‖J u q j‖ ^ 2) + ∑ q, ‖E u q‖ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := firstStrip_endpoint_radial_energy_bound D
  refine ⟨C, hC, ?_⟩
  intro ε R α hε hR hα
  obtain ⟨L, hL, hb⟩ := hb ε R α hε hR hα
  refine ⟨L, hL, ?_⟩
  intro hd Q hQ M hM β a μ hβ ζ hζ P T hP hT ν κ hκ hκc t u₀ u₁ hu hzero ht K hK hKc
  dsimp only
  let U := fun u => firstStripTimeSmooth κ
    (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u
  let H := fun u k => firstStripTimeSmooth κ
    (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u
  let A := firstStripKernelAverage Q K hK.continuous hKc
  let B := fun k => firstStripKernelAverage Q (coordinateDerivative k K)
    ((hK.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hKc.fderiv_apply ℝ (unitVector k))
  let F : ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := fun u => Fin.cons (U u) (H u)
  let V : ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := fun u => Fin.cons
    (firstStripTimeSmooth (deriv κ)
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u)
    (fun k => firstStripTimeSmooth (deriv κ)
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u)
  let Z := fun u q => A (F u q)
  let τ : ℂ := if ν = .inr true then 2 * ζ else 0
  let zforce : ℂ := if ν = .inr true then 0 else ζ
  let S := fun j k => A.comp (complexCoefficientMul Q j k) -
    (complexCoefficientMul Q j k).comp A
  let Rcomm := fun l j k => (B l).comp (complexCoefficientMul Q j k) -
    (complexCoefficientMul Q j k).comp (B l) + (M l j k).comp A
  let J : ℝ → Fin (d + 1) → Fin d → Lp ℂ 2 (reducedLaw Q) := fun u => Fin.cons
    (fun j => -((∑ k, S j k (H u k)) - τ • S j ⟨0, by omega⟩ (U u)))
    (fun l j => (∑ k, Rcomm l j k (H u k)) - τ • Rcomm l j ⟨0, by omega⟩ (U u))
  let E : ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := fun u => Fin.cons
    (zforce • ∑ j, S j ⟨0, by omega⟩ (H u j))
    (fun l => -zforce • ∑ j, Rcomm l j ⟨0, by omega⟩ (H u j))
  let err := fun u => (∑ q, ∑ j, ‖J u q j‖ ^ 2) + ∑ q, ‖E u q‖ ^ 2
  have hUc : Continuous U := (firstStrip_endpoint_time_regularization hd Q β a μ ζ P T
    hP hT ν κ hκ hκc t).1.continuous
  have hHc (k : Fin d) : Continuous (fun u => H u k) :=
    (firstStripTimeGradient_coordinate_regularization hd Q β a μ ζ P T hP hT ν
      κ hκ hκc t k).1.continuous
  have hJc (q : Fin (d + 1)) (j : Fin d) : Continuous (fun u => J u q j) := by
    refine Fin.cases ?_ (fun l => ?_) q
    · exact ((continuous_finset_sum _ fun k _ => (S j k).continuous.comp (hHc k)).sub
        (((S j ⟨0, by omega⟩).continuous.comp hUc).const_smul τ)).neg
    · exact (continuous_finset_sum _ fun k _ => (Rcomm l j k).continuous.comp (hHc k)).sub
        (((Rcomm l j ⟨0, by omega⟩).continuous.comp hUc).const_smul τ)
  have hEc (q : Fin (d + 1)) : Continuous (fun u => E u q) := by
    refine Fin.cases ?_ (fun l => ?_) q
    · exact (continuous_finset_sum _ fun j _ =>
        (S j ⟨0, by omega⟩).continuous.comp (hHc j)).const_smul zforce
    · exact (continuous_finset_sum _ fun j _ =>
        (Rcomm l j ⟨0, by omega⟩).continuous.comp (hHc j)).const_smul (-zforce)
  have herr : Continuous err :=
    (continuous_finset_sum _ fun q _ => continuous_finset_sum _ fun j _ =>
      (hJc q j).norm.pow 2).add
      (continuous_finset_sum _ fun q _ => (hEc q).norm.pow 2)
  have hder : ∀ u, HasDerivAt Z (fun q => A (V u q)) u := by
    intro u
    apply hasDerivAt_pi.mpr
    intro q
    apply (A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    refine Fin.cases ?_ (fun j => ?_) q
    · exact (firstStrip_endpoint_time_regularization hd Q β a μ ζ P T hP hT ν
        κ hκ hκc t).2 u
    · exact (firstStripTimeGradient_coordinate_regularization hd Q β a μ ζ P T hP hT ν
        κ hκ hκc t j).2 u
  have hvc : Continuous (fun u q => A (V u q)) := by
    have hκ' : ContDiff ℝ (⊤ : ℕ∞) (deriv κ) := hκ.deriv'
    apply continuous_pi
    intro q
    apply A.continuous.comp
    refine Fin.cases ?_ (fun j => ?_) q
    · exact (firstStrip_endpoint_time_regularization hd Q β a μ ζ P T hP hT ν
        (deriv κ) hκ' hκc.deriv t).1.continuous
    · exact (firstStripTimeGradient_coordinate_regularization hd Q β a μ ζ P T hP hT ν
        (deriv κ) hκ' hκc.deriv t j).1.continuous
  have hdiff (u : ℝ) (hu : u ∈ Icc u₀ u₁) :=
    hb hd Q hQ M hM β a μ hβ ζ hζ P T hP hT ν κ hκ t u
      (hzero u hu) (ht u hu) K hK hKc
  have he := firstStripSystem_integrated_energy_bound hder hvc hε hR hα hu
    ((herr.const_mul L).intervalIntegrable u₀ u₁) hdiff
  rw [intervalIntegral.integral_const_mul] at he
  exact he

/-- One fixed family of actual coefficient derivative multipliers removes
all signed errors of the coupled endpoint system in time L2. -/
private theorem firstStrip_timeL2_sub_smul_tendsto {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E]
    {σ : Measure α} {f g : ℕ → α → E} (τ : ℂ)
    (hf : ∀ n, MemLp (f n) 2 σ) (hg : ∀ n, MemLp (g n) 2 σ)
    (htf : Tendsto (fun n => ∫ s, ‖f n s‖ ^ 2 ∂σ) atTop (𝓝 0))
    (htg : Tendsto (fun n => ∫ s, ‖g n s‖ ^ 2 ∂σ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, ‖f n s - τ • g n s‖ ^ 2 ∂σ) atTop (𝓝 0) := by
  have he := firstStrip_timeL2_add_tendsto (f := f) (g := fun n s => (-τ) • g n s)
    hf (fun n => (hg n).const_smul (-τ)) htf
    (firstStrip_timeL2_smul_tendsto (-τ) htg)
  simpa only [neg_smul, sub_eq_add_neg] using he

private theorem firstStrip_coupled_error_algebra_memLp {d : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (σ : Measure ℝ) (τ zforce : ℂ)
    (S : ℕ → Fin d → Fin d → Fin (d + 1) → ℝ → V)
    (Rcomm : ℕ → Fin d → Fin d → Fin d → Fin (d + 1) → ℝ → V)
    (hSm : ∀ n j k q, MemLp (S n j k q) 2 σ)
    (hRm : ∀ n l j k q, MemLp (Rcomm n l j k q) 2 σ)
    (i₀ : Fin d) :
    let J : ℕ → ℝ → Fin (d + 1) → Fin d → V := fun n s => Fin.cons
      (fun j => -((∑ k, S n j k k.succ s) - τ • S n j i₀ 0 s))
      (fun l j => (∑ k, Rcomm n l j k k.succ s) - τ • Rcomm n l j i₀ 0 s)
    let E : ℕ → ℝ → Fin (d + 1) → V := fun n s => Fin.cons
      (zforce • ∑ j, S n j i₀ j.succ s)
      (fun l => -zforce • ∑ j, Rcomm n l j i₀ j.succ s)
    (∀ n q j, MemLp (fun s => J n s q j) 2 σ) ∧
      (∀ n q, MemLp (fun s => E n s q) 2 σ) := by
  classical
  let J : ℕ → ℝ → Fin (d + 1) → Fin d → V := fun n s => Fin.cons
    (fun j => -((∑ k, S n j k k.succ s) - τ • S n j i₀ 0 s))
    (fun l j => (∑ k, Rcomm n l j k k.succ s) - τ • Rcomm n l j i₀ 0 s)
  let E : ℕ → ℝ → Fin (d + 1) → V := fun n s => Fin.cons
    (zforce • ∑ j, S n j i₀ j.succ s)
    (fun l => -zforce • ∑ j, Rcomm n l j i₀ j.succ s)
  have hJm (n : ℕ) (q : Fin (d + 1)) (j : Fin d) :
      MemLp (fun s => J n s q j) 2 σ := by
    refine Fin.cases ?_ (fun l => ?_) q
    · change MemLp (fun s => -((∑ k, S n j k k.succ s) - τ • S n j i₀ 0 s)) 2 σ
      exact ((memLp_finsetSum Finset.univ fun k _ => hSm n j k k.succ).sub
        ((hSm n j i₀ 0).const_smul τ)).neg
    · change MemLp (fun s => (∑ k, Rcomm n l j k k.succ s) - τ • Rcomm n l j i₀ 0 s) 2 σ
      exact (memLp_finsetSum Finset.univ fun k _ => hRm n l j k k.succ).sub
        ((hRm n l j i₀ 0).const_smul τ)
  have hEm (n : ℕ) (q : Fin (d + 1)) : MemLp (fun s => E n s q) 2 σ := by
    refine Fin.cases ?_ (fun l => ?_) q
    · change MemLp (fun s => zforce • ∑ j, S n j i₀ j.succ s) 2 σ
      exact (memLp_finsetSum Finset.univ fun j _ => hSm n j i₀ j.succ).const_smul zforce
    · change MemLp (fun s => -zforce • ∑ j, Rcomm n l j i₀ j.succ s) 2 σ
      exact (memLp_finsetSum Finset.univ fun j _ => hRm n l j i₀ j.succ).const_smul (-zforce)
  exact ⟨hJm, hEm⟩

private theorem firstStrip_timeL2_sum_sub_smul_tendsto {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι]
    (σ : Measure ℝ) (τ : ℂ) (f : ι → ℕ → ℝ → V) (g : ℕ → ℝ → V)
    (hf : ∀ i n, MemLp (f i n) 2 σ) (hg : ∀ n, MemLp (g n) 2 σ)
    (htf : ∀ i, Tendsto (fun n => ∫ s, ‖f i n s‖ ^ 2 ∂σ) atTop (𝓝 0))
    (htg : Tendsto (fun n => ∫ s, ‖g n s‖ ^ 2 ∂σ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, ‖(∑ i, f i n s) - τ • g n s‖ ^ 2 ∂σ)
      atTop (𝓝 0) := by
  classical
  exact firstStrip_timeL2_sub_smul_tendsto (f := fun n s => ∑ i, f i n s)
    (g := g) τ (fun n => memLp_finsetSum Finset.univ (fun i _ => hf i n)) hg
    (firstStrip_timeL2_sum_tendsto Finset.univ (fun i _ n => hf i n) (fun i _ => htf i)) htg

private theorem firstStrip_coupled_error_algebra_timeL2 {d : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (σ : Measure ℝ) (τ zforce : ℂ)
    (S : ℕ → Fin d → Fin d → Fin (d + 1) → ℝ → V)
    (Rcomm : ℕ → Fin d → Fin d → Fin d → Fin (d + 1) → ℝ → V)
    (hSm : ∀ n j k q, MemLp (S n j k q) 2 σ)
    (hRm : ∀ n l j k q, MemLp (Rcomm n l j k q) 2 σ)
    (hSt : ∀ j k q, Tendsto (fun n => ∫ s, ‖S n j k q s‖ ^ 2 ∂σ) atTop (𝓝 0))
    (hRt : ∀ l j k q, Tendsto (fun n => ∫ s, ‖Rcomm n l j k q s‖ ^ 2 ∂σ) atTop (𝓝 0))
    (i₀ : Fin d) :
    let J : ℕ → ℝ → Fin (d + 1) → Fin d → V := fun n s => Fin.cons
      (fun j => -((∑ k, S n j k k.succ s) - τ • S n j i₀ 0 s))
      (fun l j => (∑ k, Rcomm n l j k k.succ s) - τ • Rcomm n l j i₀ 0 s)
    let E : ℕ → ℝ → Fin (d + 1) → V := fun n s => Fin.cons
      (zforce • ∑ j, S n j i₀ j.succ s)
      (fun l => -zforce • ∑ j, Rcomm n l j i₀ j.succ s)
    Tendsto (fun n => ∫ s, (∑ q, ∑ j, ‖J n s q j‖ ^ 2) +
      ∑ q, ‖E n s q‖ ^ 2 ∂σ) atTop (𝓝 0) := by
  classical
  let J : ℕ → ℝ → Fin (d + 1) → Fin d → V := fun n s => Fin.cons
    (fun j => -((∑ k, S n j k k.succ s) - τ • S n j i₀ 0 s))
    (fun l j => (∑ k, Rcomm n l j k k.succ s) - τ • Rcomm n l j i₀ 0 s)
  let E : ℕ → ℝ → Fin (d + 1) → V := fun n s => Fin.cons
    (zforce • ∑ j, S n j i₀ j.succ s)
    (fun l => -zforce • ∑ j, Rcomm n l j i₀ j.succ s)
  obtain ⟨hJm, hEm⟩ := firstStrip_coupled_error_algebra_memLp
    σ τ zforce S Rcomm hSm hRm i₀
  have hJt (q : Fin (d + 1)) (j : Fin d) :
      Tendsto (fun n => ∫ s, ‖J n s q j‖ ^ 2 ∂σ) atTop (𝓝 0) := by
    refine Fin.cases ?_ (fun l => ?_) q
    · change Tendsto (fun n => ∫ s, ‖-((∑ k, S n j k k.succ s) -
          τ • S n j i₀ 0 s)‖ ^ 2 ∂σ) atTop (𝓝 0)
      simpa only [norm_neg] using firstStrip_timeL2_sum_sub_smul_tendsto σ τ
        (fun k n s => S n j k k.succ s) (fun n s => S n j i₀ 0 s)
        (fun k n => hSm n j k k.succ) (fun n => hSm n j i₀ 0)
        (fun k => hSt j k k.succ) (hSt j i₀ 0)
    · change Tendsto (fun n => ∫ s, ‖(∑ k, Rcomm n l j k k.succ s) -
          τ • Rcomm n l j i₀ 0 s‖ ^ 2 ∂σ) atTop (𝓝 0)
      exact firstStrip_timeL2_sum_sub_smul_tendsto σ τ
        (fun k n s => Rcomm n l j k k.succ s) (fun n s => Rcomm n l j i₀ 0 s)
        (fun k n => hRm n l j k k.succ) (fun n => hRm n l j i₀ 0)
        (fun k => hRt l j k k.succ) (hRt l j i₀ 0)
  have hEt (q : Fin (d + 1)) :
      Tendsto (fun n => ∫ s, ‖E n s q‖ ^ 2 ∂σ) atTop (𝓝 0) := by
    refine Fin.cases ?_ (fun l => ?_) q
    · change Tendsto (fun n => ∫ s, ‖zforce • ∑ j, S n j i₀ j.succ s‖ ^ 2 ∂σ)
        atTop (𝓝 0)
      exact firstStrip_timeL2_smul_tendsto zforce
        (firstStrip_timeL2_sum_tendsto Finset.univ
          (f := fun j n s => S n j i₀ j.succ s)
          (fun j _ n => hSm n j i₀ j.succ) (fun j _ => hSt j i₀ j.succ))
    · change Tendsto (fun n => ∫ s, ‖-zforce • ∑ j, Rcomm n l j i₀ j.succ s‖ ^ 2 ∂σ)
        atTop (𝓝 0)
      exact firstStrip_timeL2_smul_tendsto (-zforce)
        (firstStrip_timeL2_sum_tendsto Finset.univ
          (f := fun j n s => Rcomm n l j i₀ j.succ s)
          (fun j _ n => hRm n l j i₀ j.succ) (fun j _ => hRt l j i₀ j.succ))
  have hJi (n : ℕ) (q : Fin (d + 1)) (j : Fin d) :
      Integrable (fun s => ‖J n s q j‖ ^ 2) σ :=
    (hJm n q j).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hEi (n : ℕ) (q : Fin (d + 1)) : Integrable (fun s => ‖E n s q‖ ^ 2) σ :=
    (hEm n q).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have he (n : ℕ) : (∫ s, (∑ q, ∑ j, ‖J n s q j‖ ^ 2) +
      ∑ q, ‖E n s q‖ ^ 2 ∂σ) =
      (∑ q, ∑ j, ∫ s, ‖J n s q j‖ ^ 2 ∂σ) +
        ∑ q, ∫ s, ‖E n s q‖ ^ 2 ∂σ := by
    rw [integral_add (integrable_finsetSum _ fun q _ =>
      integrable_finsetSum _ fun j _ => hJi n q j)
      (integrable_finsetSum _ fun q _ => hEi n q)]
    congr 1
    · rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ fun j _ => hJi n q j)]
      apply Finset.sum_congr rfl
      intro q _
      exact integral_finsetSum _ (fun j _ => hJi n q j)
    · exact integral_finsetSum _ (fun q _ => hEi n q)
  have ht := (tendsto_finset_sum Finset.univ fun q _ =>
      tendsto_finset_sum Finset.univ fun j _ => hJt q j).add
      (tendsto_finset_sum Finset.univ fun q _ => hEt q)
  simp only [Finset.sum_const_zero, add_zero] at ht
  change Tendsto (fun n => ∫ s, (∑ q, ∑ j, ‖J n s q j‖ ^ 2) +
      ∑ q, ‖E n s q‖ ^ 2 ∂σ) atTop (𝓝 0)
  simpa only [he] using ht

/-- One fixed family of actual coefficient derivative multipliers removes
all signed errors of the coupled endpoint system in time L2. -/
private theorem firstStripSpatialKernel_coupled_errors_timeL2 {d : ℕ}
    (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) :
    ∃ M : Fin d → Fin d → Fin d →
      Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ l j k v, M l j k v =ᵐ[reducedLaw Q] fun ω =>
        (coordinateDerivative l (fun y => ω.1 y j k) 0 : ℂ) * v ω) ∧
      ∀ (σ : Measure ℝ) (F : ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q)),
      (∀ q, MemLp (fun s => F s q) 2 σ) → ∀ (τ zforce : ℂ),
    let A := fun n => firstStripKernelAverage Q (firstStripSpatialKernel d n)
      (firstStripSpatialKernel_smooth d n).continuous (firstStripSpatialKernel_compact d n)
    let B := fun n l => firstStripKernelAverage Q
      (coordinateDerivative l (firstStripSpatialKernel d n))
      (((firstStripSpatialKernel_smooth d n).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((firstStripSpatialKernel_compact d n).fderiv_apply ℝ (unitVector l))
    let S := fun n j k v => A n (complexCoefficientMul Q j k v) -
      complexCoefficientMul Q j k (A n v)
    let Rcomm := fun n l j k v => B n l (complexCoefficientMul Q j k v) -
      complexCoefficientMul Q j k (B n l v) + M l j k (A n v)
    let J : ℕ → ℝ → Fin (d + 1) → Fin d → Lp ℂ 2 (reducedLaw Q) := fun n s => Fin.cons
      (fun j => -((∑ k, S n j k (F s k.succ)) -
        τ • S n j ⟨0, by omega⟩ (F s 0)))
      (fun l j => (∑ k, Rcomm n l j k (F s k.succ)) -
        τ • Rcomm n l j ⟨0, by omega⟩ (F s 0))
    let E : ℕ → ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := fun n s => Fin.cons
      (zforce • ∑ j, S n j ⟨0, by omega⟩ (F s j.succ))
      (fun l => -zforce • ∑ j, Rcomm n l j ⟨0, by omega⟩ (F s j.succ))
    Tendsto (fun n => ∫ s, (∑ q, ∑ j, ‖J n s q j‖ ^ 2) +
      ∑ q, ‖E n s q‖ ^ 2 ∂σ) atTop (𝓝 0) := by
  classical
  choose M hM hMt using fun l j k : Fin d =>
    firstStripSpatialKernel_flux_remainder_timeL2 D Q hQ ⟨0, by omega⟩ j k l
  refine ⟨M, hM, ?_⟩
  intro σ F hF τ zforce
  dsimp only
  let A := fun n => firstStripKernelAverage Q (firstStripSpatialKernel d n)
    (firstStripSpatialKernel_smooth d n).continuous (firstStripSpatialKernel_compact d n)
  let B := fun n l => firstStripKernelAverage Q
    (coordinateDerivative l (firstStripSpatialKernel d n))
    (((firstStripSpatialKernel_smooth d n).continuous_fderiv (by simp)).clm_apply continuous_const)
    ((firstStripSpatialKernel_compact d n).fderiv_apply ℝ (unitVector l))
  let S := fun n j k => (A n).comp (complexCoefficientMul Q j k) -
    (complexCoefficientMul Q j k).comp (A n)
  let Rcomm := fun n l j k => (B n l).comp (complexCoefficientMul Q j k) -
    (complexCoefficientMul Q j k).comp (B n l) + (M l j k).comp (A n)
  have hSm (n : ℕ) (j k : Fin d) (q : Fin (d + 1)) :
      MemLp (fun s => S n j k (F s q)) 2 σ := (S n j k).comp_memLp' (hF q)
  have hRm (n : ℕ) (l j k : Fin d) (q : Fin (d + 1)) :
      MemLp (fun s => Rcomm n l j k (F s q)) 2 σ := (Rcomm n l j k).comp_memLp' (hF q)
  have hSt (j k : Fin d) (q : Fin (d + 1)) :
      Tendsto (fun n => ∫ s, ‖S n j k (F s q)‖ ^ 2 ∂σ) atTop (𝓝 0) :=
    firstStripSpatialKernel_coefficient_commutator_timeL2 Q j k σ _ (hF q)
  have hRt (l j k : Fin d) (q : Fin (d + 1)) :
      Tendsto (fun n => ∫ s, ‖Rcomm n l j k (F s q)‖ ^ 2 ∂σ) atTop (𝓝 0) :=
    hMt l j k σ _ (hF q)
  exact firstStrip_coupled_error_algebra_timeL2 σ τ zforce
    (fun n j k q s => S n j k (F s q))
    (fun n l j k q s => Rcomm n l j k (F s q)) hSm hRm hSt hRt ⟨0, by omega⟩

/-- Removing the spatial Friedrichs regularization leaves the actual
time-smoothed endpoint system and the same structural linear-exponent constant. -/
private theorem firstStrip_endpoint_time_smoothed_radial_energy_bound {d : ℕ} (D : StructuralData d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε R α : ℝ), 0 < ε → 0 < R → 0 ≤ α →
      ∀
    (hd : 2 ≤ d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ζ : ℂ) (hζ : ‖ζ‖ ≤ 4)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    (t : ℝ≥0) (u₀ u₁ : ℝ) (hu : u₀ ≤ u₁)
    (hzero : ∀ u ∈ Icc u₀ u₁, κ u = 0)
    (ht : ∀ u ∈ Icc u₀ u₁, κ (u - t) = 0),
    let F : ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := fun u => Fin.cons
      (firstStripTimeSmooth κ
        (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u)
      (fun k => firstStripTimeSmooth κ
        (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u)
    let energy := fun u => ∫ ω, firstStripHilbertPrimitive ε R α
      (WithLp.toLp 2 (fun q => F u q ω) : EuclideanSpace ℂ (Fin (d + 1)))
        ∂reducedLaw Q
    energy u₁ ≤ energy u₀ + C * (1 + α) * (∫ u in u₀..u₁, energy u) := by
  obtain ⟨C, hC, hb⟩ := firstStrip_endpoint_integrated_radial_energy_bound D
  refine ⟨C, hC, ?_⟩
  intro ε R α hε hR hα
  obtain ⟨L, hL, hb⟩ := hb ε R α hε hR hα
  intro hd Q hQ β a μ hβ ζ hζ P T hP hT ν κ hκ hκc t u₀ u₁ hu hzero ht
  dsimp only
  obtain ⟨M, hM, hMt⟩ := firstStripSpatialKernel_coupled_errors_timeL2 hd D Q hQ
  let F : ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := fun u => Fin.cons
    (firstStripTimeSmooth κ
      (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u)
    (fun k => firstStripTimeSmooth κ
      (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s k) t u)
  let A := fun n => firstStripKernelAverage Q (firstStripSpatialKernel d n)
    (firstStripSpatialKernel_smooth d n).continuous (firstStripSpatialKernel_compact d n)
  let B := fun n l => firstStripKernelAverage Q
    (coordinateDerivative l (firstStripSpatialKernel d n))
    (((firstStripSpatialKernel_smooth d n).continuous_fderiv (by simp)).clm_apply continuous_const)
    ((firstStripSpatialKernel_compact d n).fderiv_apply ℝ (unitVector l))
  let S := fun n j k v => A n (complexCoefficientMul Q j k v) -
    complexCoefficientMul Q j k (A n v)
  let Rcomm := fun n l j k v => B n l (complexCoefficientMul Q j k v) -
    complexCoefficientMul Q j k (B n l v) + M l j k (A n v)
  let τ : ℂ := if ν = .inr true then 2 * ζ else 0
  let zforce : ℂ := if ν = .inr true then 0 else ζ
  let J : ℕ → ℝ → Fin (d + 1) → Fin d → Lp ℂ 2 (reducedLaw Q) := fun n s => Fin.cons
    (fun j => -((∑ k, S n j k (F s k.succ)) - τ • S n j ⟨0, by omega⟩ (F s 0)))
    (fun l j => (∑ k, Rcomm n l j k (F s k.succ)) -
      τ • Rcomm n l j ⟨0, by omega⟩ (F s 0))
  let E : ℕ → ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := fun n s => Fin.cons
    (zforce • ∑ j, S n j ⟨0, by omega⟩ (F s j.succ))
    (fun l => -zforce • ∑ j, Rcomm n l j ⟨0, by omega⟩ (F s j.succ))
  let err := fun n s => (∑ q, ∑ j, ‖J n s q j‖ ^ 2) + ∑ q, ‖E n s q‖ ^ 2
  let en := fun n u => ∫ ω, firstStripHilbertPrimitive ε R α
    (WithLp.toLp 2 (fun q => A n (F u q) ω) : EuclideanSpace ℂ (Fin (d + 1)))
      ∂reducedLaw Q
  let energy := fun u => ∫ ω, firstStripHilbertPrimitive ε R α
    (WithLp.toLp 2 (fun q => F u q ω) : EuclideanSpace ℂ (Fin (d + 1)))
      ∂reducedLaw Q
  have hFc (q : Fin (d + 1)) : Continuous (fun u => F u q) := by
    refine Fin.cases ?_ (fun j => ?_) q
    · exact (firstStrip_endpoint_time_regularization hd Q β a μ ζ P T hP hT ν
        κ hκ hκc t).1.continuous
    · exact (firstStripTimeGradient_coordinate_regularization hd Q β a μ ζ P T hP hT ν
        κ hκ hκc t j).1.continuous
  let σ := volume.restrict (Ioc u₀ u₁)
  have hFmem (q : Fin (d + 1)) : MemLp (fun s => F s q) 2 σ :=
    (memLp_two_iff_integrable_sq_norm ((hFc q).aestronglyMeasurable (μ := σ))).mpr
      (((hFc q).norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have he (u : ℝ) : Tendsto (fun n => en n u) atTop (𝓝 (energy u)) :=
    firstStripSystem_energy_tendsto (tendsto_pi_nhds.mpr fun q =>
      firstStripSpatialKernel_average_tendsto Q (F u q)) hε hR hα
  have hbmajor (n : ℕ) (s : ℝ) : (∑ q, ‖A n (F s q)‖ ^ 2) ≤ ∑ q, ‖F s q‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro q _
    exact pow_le_pow_left₀ (norm_nonneg _) (firstStripSpatialKernel_average_norm Q n (F s q)) 2
  have hbcont : Continuous (fun s => ∑ q : Fin (d + 1), ‖F s q‖ ^ 2) :=
    continuous_finsetSum Finset.univ fun q _ => (hFc q).norm.pow 2
  have hbint : Integrable (fun s => ∑ q : Fin (d + 1), ‖F s q‖ ^ 2) σ :=
    hbcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hi : Tendsto (fun n => ∫ u in u₀..u₁, en n u) atTop
      (𝓝 (∫ u in u₀..u₁, energy u)) := by
    have ht := firstStripSystem_energy_time_tendsto (reducedLaw Q) σ
      (fun n s q => A n (F s q)) F
      (fun n => continuous_pi fun q => (A n).continuous.comp (hFc q))
      (fun s => ∑ q, ‖F s q‖ ^ 2)
      hbint
      (ae_of_all _ fun s => tendsto_pi_nhds.mpr fun q =>
        firstStripSpatialKernel_average_tendsto Q (F s q)) hbmajor hε hR hα
    simpa only [intervalIntegral.integral_of_le hu] using ht
  have herr : Tendsto (fun n => ∫ s in u₀..u₁, err n s) atTop (𝓝 0) := by
    have ht := hMt σ F hFmem τ zforce
    simpa only [intervalIntegral.integral_of_le hu] using ht
  have hn (n : ℕ) : en n u₁ ≤ en n u₀ +
      C * (1 + α) * (∫ u in u₀..u₁, en n u) + L * (∫ u in u₀..u₁, err n u) :=
    hb hd Q hQ M hM β a μ hβ ζ hζ P T hP hT ν κ hκ hκc t u₀ u₁ hu hzero ht
      (firstStripSpatialKernel d n) (firstStripSpatialKernel_smooth d n)
      (firstStripSpatialKernel_compact d n)
  have hlimit := le_of_tendsto_of_tendsto' (he u₁)
    (((he u₀).add (hi.const_mul (C * (1 + α)))).add (herr.const_mul L)) hn
  simpa only [mul_zero, add_zero] using hlimit

/-- The same normalized time mollifiers converge under a fixed radial
energy time integral, using only a continuous L2 coordinate orbit. -/
private theorem firstStripTimeSmooth_system_energy_time_tendsto {α : Type*}
    [MeasurableSpace α] (μ : Measure α) {N : ℕ}
    (φ : ℕ → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (F : ℝ → Fin N → Lp ℂ 2 μ) (hF : Continuous F)
    (t : ℝ≥0) {u₀ u₁ : ℝ} (hu₀ : 0 < u₀) (hu₁ : u₁ < (t : ℝ)) (hu : u₀ ≤ u₁)
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    Tendsto (fun n => ∫ u in u₀..u₁, ∫ ω, firstStripHilbertPrimitive ε R a
      (WithLp.toLp 2 (fun q => firstStripTimeSmooth ((φ n).normed volume)
        (fun s => F s q) t u ω) : EuclideanSpace ℂ (Fin N)) ∂μ)
      atTop (𝓝 (∫ u in u₀..u₁, ∫ ω, firstStripHilbertPrimitive ε R a
        (WithLp.toLp 2 (fun q => F u q ω) : EuclideanSpace ℂ (Fin N)) ∂μ)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hF.norm.continuousOn
  let B := max M 0
  have hB : 0 ≤ B := le_max_right _ _
  have hb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) (q : Fin N) : ‖F s q‖ ≤ B :=
    (norm_le_pi_norm (F s) q).trans ((hM (mem_image_of_mem _ hs)).trans (le_max_left _ _))
  let f := fun n u q => firstStripTimeSmooth ((φ n).normed volume) (fun s => F s q) t u
  have hFc (q : Fin N) : Continuous (fun s => F s q) := (continuous_apply q).comp hF
  have hfc (n : ℕ) : Continuous (f n) := by
    apply continuous_pi
    intro q
    exact (firstStripTimeSmooth_regularization ((φ n).normed volume)
      (φ n).contDiff_normed (φ n).hasCompactSupport_normed t (hFc q).integrableOn_Icc).1.continuous
  have hfb (n : ℕ) (s : ℝ) : (∑ q, ‖f n s q‖ ^ 2) ≤ ∑ _q : Fin N, B ^ 2 := by
    apply Finset.sum_le_sum
    intro q _
    exact pow_le_pow_left₀ (norm_nonneg _)
      (firstStripTimeSmooth_norm_le (φ n) _ (hFc q) t s B hB (fun v hv => hb v hv q)) 2
  have ht := firstStripSystem_energy_time_tendsto μ (volume.restrict (Ioc u₀ u₁))
    f F hfc (fun _ => ∑ _q : Fin N, B ^ 2) (integrable_const _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      apply tendsto_pi_nhds.mpr
      intro q
      exact firstStripTimeSmooth_tendsto φ hφ _ (hFc q) t s
        (hu₀.trans hs.1) (hs.2.trans_lt hu₁)) hfb hε hR ha
  simpa only [intervalIntegral.integral_of_le hu] using ht

/-- Removing time regularization retains the continuous actual gradient
trace, including its genuine value at zero. -/
private theorem firstStrip_endpoint_trace_radial_energy_bound {d : ℕ} (D : StructuralData d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (hd : 2 ≤ d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ) (hζ : ‖ζ‖ ≤ 4)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (ν : EndpointIndex d),
    ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)), Continuous G ∧
      (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) (G s)) ∧
      (∀ s, 0 < s → G s = firstStripTimeGradient hd Q β a μ ζ P T hP ν s) ∧
      ∀ (ε R α : ℝ), 0 < ε → 0 < R → 0 ≤ α → ∀ (u₀ u₁ : ℝ),
      0 < u₀ → u₀ ≤ u₁ →
    let F : ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := fun u => Fin.cons (uncenteredEndpoint hd Q ν ζ P T β a μ u.toNNReal)
      (fun j => G u j)
    let energy := fun u => ∫ ω, firstStripHilbertPrimitive ε R α
      (WithLp.toLp 2 (fun q => F u q ω) : EuclideanSpace ℂ (Fin (d + 1))) ∂reducedLaw Q
    energy u₁ ≤ energy u₀ + C * (1 + α) * (∫ u in u₀..u₁, energy u) := by
  obtain ⟨C, hC, hb⟩ := firstStrip_endpoint_time_smoothed_radial_energy_bound D
  refine ⟨C, hC, ?_⟩
  intro hd Q hQ β a μ hβ ha hμ ζ hζ P T hP hT ν
  obtain ⟨G, hGc, hG, hGe⟩ := firstStrip_endpoint_continuous_gradient_trace hd Q hQ
    β a μ hβ ha hμ ζ P T hP hT ν
  refine ⟨G, hGc, hG, hGe, ?_⟩
  intro ε R α hε hR hα u₀ u₁ hu₀ hu
  dsimp only
  let F : ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := fun u => Fin.cons (uncenteredEndpoint hd Q ν ζ P T β a μ u.toNNReal)
    (fun j => G u j)
  have hFc : Continuous F := by
    apply continuous_pi
    intro q
    refine Fin.cases ?_ (fun j => ?_) q
    · cases ν with
      | inl k => exact (hP.2.2.1 _).comp continuous_real_toNNReal
      | inr b =>
        cases b with
        | false =>
          change Continuous (fun s : ℝ => ζ • P s.toNNReal μ)
          exact ((hP.2.2.1 μ).comp continuous_real_toNNReal).const_smul ζ
        | true => exact (hT.continuous_apply hP _).comp continuous_real_toNNReal
    · exact (PiLp.continuous_apply 2 _ j).comp hGc
  let t : ℝ≥0 := ⟨u₁ + 1, by linarith⟩
  have hut : u₁ < (t : ℝ) := by change u₁ < u₁ + 1; linarith
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    ⟨((n : ℝ) + 1)⁻¹, 2 * ((n : ℝ) + 1)⁻¹, by positivity, by
      have h : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have hN : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa only [φ, Function.comp_apply, mul_zero] using (tendsto_inv_atTop_zero.comp hN).const_mul 2
  let f := fun n u q => firstStripTimeSmooth ((φ n).normed volume) (fun s => F s q) t u
  let en := fun n u => ∫ ω, firstStripHilbertPrimitive ε R α
    (WithLp.toLp 2 (fun q => f n u q ω) : EuclideanSpace ℂ (Fin (d + 1))) ∂reducedLaw Q
  let energy := fun u => ∫ ω, firstStripHilbertPrimitive ε R α
    (WithLp.toLp 2 (fun q => F u q ω) : EuclideanSpace ℂ (Fin (d + 1))) ∂reducedLaw Q
  have hsm (κ : ℝ → ℝ) (u : ℝ) (j : Fin d) :
      firstStripTimeSmooth κ (fun s => firstStripTimeGradient hd Q β a μ ζ P T hP ν s j) t u =
      firstStripTimeSmooth κ (fun s => G s j) t u := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with s hs hs0
    rw [hGe s (lt_of_le_of_ne hs.1 (Ne.symm hs0))]
  have hpack (n : ℕ) (u : ℝ) :
      (Fin.cons (firstStripTimeSmooth ((φ n).normed volume)
        (fun s => uncenteredEndpoint hd Q ν ζ P T β a μ s.toNNReal) t u)
        (fun j => firstStripTimeSmooth ((φ n).normed volume) (fun s => G s j) t u)) = f n u := by
    funext q
    refine Fin.cases ?_ (fun j => ?_) q <;> rfl
  have hsmall : ∀ᶠ n in atTop, (φ n).rOut < min u₀ ((t : ℝ) - u₁) :=
    hφ.eventually (gt_mem_nhds (lt_min hu₀ (sub_pos.mpr hut)))
  have hn : ∀ᶠ n in atTop, en n u₁ ≤ en n u₀ +
      C * (1 + α) * (∫ u in u₀..u₁, en n u) := by
    filter_upwards [hsmall] with n hn
    have hz (u : ℝ) (hs : u ∈ Icc u₀ u₁) : (φ n).normed volume u = 0 := by
      rw [ContDiffBump.normed_def, (φ n).zero_of_le_dist ?_, zero_div]
      rw [Real.dist_eq, sub_zero, abs_of_pos (hu₀.trans_le hs.1)]
      exact (hn.le.trans (min_le_left _ _)).trans hs.1
    have ht (u : ℝ) (hs : u ∈ Icc u₀ u₁) : (φ n).normed volume (u - t) = 0 := by
      rw [ContDiffBump.normed_def, (φ n).zero_of_le_dist ?_, zero_div]
      rw [Real.dist_eq, sub_zero, abs_of_neg (sub_neg.mpr (hs.2.trans_lt hut))]
      have hh := hn.le.trans (min_le_right _ _)
      linarith [hs.2]
    have he := hb ε R α hε hR hα hd Q hQ β a μ hβ ζ hζ P T hP hT ν
      ((φ n).normed volume) (φ n).contDiff_normed (φ n).hasCompactSupport_normed
      t u₀ u₁ hu hz ht
    simpa only [hsm, hpack] using he
  have hp (u : ℝ) (hup : 0 < u) (hut : u < (t : ℝ)) :
      Tendsto (fun n => en n u) atTop (𝓝 (energy u)) :=
    firstStripSystem_energy_tendsto (tendsto_pi_nhds.mpr fun q =>
      firstStripTimeSmooth_tendsto φ hφ _ ((continuous_apply q).comp hFc) t u hup hut) hε hR hα
  have hi := firstStripTimeSmooth_system_energy_time_tendsto (reducedLaw Q) φ hφ F hFc
    t hu₀ hut hu hε hR hα
  exact le_of_tendsto_of_tendsto (hp u₁ (hu₀.trans_le hu) hut)
    ((hp u₀ hu₀ (hu.trans_lt hut)).add (hi.const_mul (C * (1 + α)))) hn

/-- The continuous trace extends every positive-time radial inequality
to zero before applying integral Gronwall. -/
private theorem firstStrip_integral_gronwall_of_positive_intervals {E : ℝ → ℝ} {k : ℝ}
    (hE : Continuous E) (hk : 0 ≤ k)
    (hineq : ∀ u₀ u₁ : ℝ, 0 < u₀ → u₀ ≤ u₁ →
      E u₁ ≤ E u₀ + k * (∫ u in u₀..u₁, E u)) :
    ∀ s : ℝ, 0 ≤ s → E s ≤ E 0 * Real.exp (k * s) := by
  have hi (s : ℝ) (hs : 0 ≤ s) : E s ≤ E 0 + k * (∫ u in 0..s, E u) := by
    by_cases hs0 : s = 0
    · subst s
      simp only [intervalIntegral.integral_same, mul_zero, add_zero]
      exact le_rfl
    have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    let v := fun n : ℕ => s / ((n : ℝ) + 1)
    have hvp (n : ℕ) : 0 < v n := div_pos hsp (by positivity)
    have hvs (n : ℕ) : v n ≤ s := div_le_self hs (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
    have hv : Tendsto v atTop (𝓝 0) := tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    have hI : Continuous (fun v => ∫ u in v..s, E u) := by
      convert (intervalIntegral.continuous_primitive (μ := volume)
        (hE.intervalIntegrable (μ := volume)) s).neg using 1
      funext v
      exact intervalIntegral.integral_symm s v
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds
      ((hE.continuousAt.tendsto.comp hv).add ((hI.continuousAt.tendsto.comp hv).const_mul k))
      (fun n => hineq (v n) s (hvp n) (hvs n))
  intro s hs
  exact firstStrip_integral_gronwall hE hk (fun u hu => hi u hu.1) s ⟨hs, le_rfl⟩

/-- The structural initial bound applies to the genuine gradient trace
and hence to the Euclidean norm of the entire coupled system. -/
private theorem firstStrip_initial_trace_packed_bound {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
    IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
    IsReducedClockObservation Q μ → ∀ (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
    IsComplexTransposeSemigroup Q P T → ∀ (ν : EndpointIndex d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)),
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (uncenteredEndpoint hd Q ν ζ P T β a μ 0) G →
    ∀ᵐ ω ∂reducedLaw Q,
      ‖(WithLp.toLp 2 (Fin.cons (uncenteredEndpoint hd Q ν ζ P T β a μ 0 ω)
        (fun j => G j ω)) : EuclideanSpace ℂ (Fin (d + 1)))‖ ≤ M := by
  obtain ⟨M, hM, hb⟩ := firstStrip_initial_endpoint_bound hd D
  refine ⟨M, hM, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P T hP hT ν G hG
  obtain ⟨G₀, hG₀, hb⟩ := hb Q hQ β a μ hβ ha hμ ζ hζ P T hP hT ν
  have he := hG₀.unique hG
  subst G₀
  filter_upwards [hb] with ω hω
  let z : EuclideanSpace ℂ (Fin (d + 1)) :=
    WithLp.toLp 2 (Fin.cons (uncenteredEndpoint hd Q ν ζ P T β a μ 0 ω)
      (fun j => G j ω))
  let S := ∑ j : Fin d, ‖G j ω‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hz : ‖z‖ ^ 2 = ‖uncenteredEndpoint hd Q ν ζ P T β a μ 0 ω‖ ^ 2 + S := by
    simp only [z, S, PiLp.norm_sq_eq_of_L2, WithLp.ofLp_toLp,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have hs : (‖uncenteredEndpoint hd Q ν ζ P T β a μ 0 ω‖ + Real.sqrt S) ^ 2 ≤ M ^ 2 :=
    (sq_le_sq₀ (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg S)) hM).mpr hω
  apply (sq_le_sq₀ (norm_nonneg z) hM).mp
  nlinarith only [hz, hs, Real.sq_sqrt hS,
    mul_nonneg (norm_nonneg (uncenteredEndpoint hd Q ν ζ P T β a μ 0 ω)) (Real.sqrt_nonneg S)]

/-- Uniform integral bounds for every positive integer moment imply an
almost-sure bound, with an inessential factor two. -/
private theorem firstStrip_ae_lt_twice_of_pow_integrals {α : Type*}
    [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) {K : ℝ}
    (hK : 0 < K) (hf : ∀ x, 0 ≤ f x)
    (hi : ∀ n : ℕ, Integrable (fun x => f x ^ (n + 1)) μ)
    (hb : ∀ n : ℕ, (∫ x, f x ^ (n + 1) ∂μ) ≤ K ^ (n + 1)) :
    ∀ᵐ x ∂μ, f x < 2 * K := by
  have hmeasure (n : ℕ) : μ {x | 2 * K ≤ f x} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
    let g := fun x => (f x / (2 * K)) ^ (n + 1)
    have hgi : Integrable g μ := by
      simpa only [g, div_pow] using (hi n).div_const ((2 * K) ^ (n + 1))
    have hgn : 0 ≤ᵐ[μ] g := ae_of_all _ fun x => pow_nonneg
      (div_nonneg (hf x) (by positivity)) _
    have hge : μ {x | 2 * K ≤ f x} ≤ ENNReal.ofReal (∫ x, g x ∂μ) :=
      hgi.measure_le_integral hgn (fun x hx => one_le_pow₀
        ((one_le_div (by positivity : 0 < 2 * K)).mpr hx))
    apply hge.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      (∫ x, g x ∂μ) = (∫ x, f x ^ (n + 1) ∂μ) / (2 * K) ^ (n + 1) := by
        simp only [g, div_pow, integral_div]
      _ ≤ K ^ (n + 1) / (2 * K) ^ (n + 1) :=
        div_le_div_of_nonneg_right (hb n) (by positivity)
      _ = (1 / 2 : ℝ) ^ (n + 1) := by
        rw [← div_pow]
        congr 1
        field_simp [hK.ne']
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)))
      atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have ht := (ENNReal.continuous_ofReal.tendsto 0).comp
      ((h.comp (tendsto_add_atTop_nat 1)))
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ht
  have hz : μ {x | 2 * K ≤ f x} = 0 := le_antisymm
    (ge_of_tendsto' hlim hmeasure) bot_le
  apply ae_iff.mpr
  simpa only [not_lt] using hz

/-- Uniform real radial moments of the actual endpoint and its actual
horizontal gradient, with the structural constant chosen before the law and p. -/
theorem firstStrip_endpoint_uniform_radial_moments :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
    IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
    IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P),
    IsComplexTransposeSemigroup Q P Pdag → ∀ (ν : EndpointIndex d),
    ∀ p : ℝ, 2 ≤ p → ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → (t : ℝ) < 2 → ‖ζ‖ ≤ 4 →
    let E : FieldPair d → ℝ := fun ω =>
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ^ 2 +
      ∑ j : Fin d, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2
    Integrable (fun ω => E ω ^ (p / 2)) (reducedLaw Q) ∧
      (∫ ω, E ω ^ (p / 2) ∂reducedLaw Q) ≤
        C ^ p * Real.exp (C * p * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) := by
  intro d hd D
  obtain ⟨C₀, hC₀, hb⟩ := firstStrip_endpoint_trace_radial_energy_bound D
  obtain ⟨M, hM, hMb⟩ := firstStrip_initial_trace_packed_bound hd D
  let C := max 1 (max (Real.exp 1 * (1 + M ^ 2)) C₀)
  have hC : 1 ≤ C := le_max_left _ _
  have hCM : Real.exp 1 * (1 + M ^ 2) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCC : C₀ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hT ν p hp t ht ht₂ hζ
  letI := reducedLaw_probability Q
  obtain ⟨G, hGc, hG, hGe, hb⟩ := hb hd Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hT ν
  let F : ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := fun u => Fin.cons (uncenteredEndpoint hd Q ν ζ P Pdag β a μ u.toNNReal)
    (fun j => G u j)
  have hFc : Continuous F := by
    apply continuous_pi
    intro q
    refine Fin.cases ?_ (fun j => ?_) q
    · cases ν with
      | inl k => exact (hP.2.2.1 _).comp continuous_real_toNNReal
      | inr b =>
        cases b with
        | false =>
          change Continuous (fun s : ℝ => ζ • P s.toNNReal μ)
          exact ((hP.2.2.1 μ).comp continuous_real_toNNReal).const_smul ζ
        | true => exact (hT.continuous_apply hP _).comp continuous_real_toNNReal
    · exact (PiLp.continuous_apply 2 _ j).comp hGc
  let α := p / 2 - 1
  have hα : 0 ≤ α := by dsimp only [α]; linarith
  have hαp : α + 1 = p / 2 := by dsimp only [α]; ring
  let A₀ := (1 / 2 : ℝ) * M ^ 2 * (1 + M ^ 2) ^ α
  let B := A₀ * Real.exp (C₀ * (1 + α) * (t : ℝ))
  have hA₀ : 0 ≤ A₀ := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (Real.rpow_nonneg (by positivity) _)
  have hB : 0 ≤ B := mul_nonneg hA₀ (Real.exp_pos _).le
  have hini := hMb Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hT ν (fun j => G 0 j)
    (by simpa using hG 0)
  have he (n : ℕ) : (∫ ω, firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹
      ((n : ℝ) + 1) α
      (WithLp.toLp 2 (fun q => F (t : ℝ) q ω) : EuclideanSpace ℂ (Fin (d + 1)))
        ∂reducedLaw Q) ≤ B := by
    have hN : 0 < (n : ℝ) + 1 := by positivity
    have hε : 0 < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr hN
    have hε₁ : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
      (inv_le_one₀ hN).mpr (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
    let en := fun u => ∫ ω, firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹
      ((n : ℝ) + 1) α
      (WithLp.toLp 2 (fun q => F u q ω) : EuclideanSpace ℂ (Fin (d + 1))) ∂reducedLaw Q
    have henc : Continuous en := continuous_iff_continuousAt.mpr fun u =>
      firstStripSystem_energy_tendsto hFc.continuousAt hε hN hα
    have hen₀ : en 0 ≤ A₀ := by
      have hi : Integrable (fun ω => firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹
          ((n : ℝ) + 1) α
          (WithLp.toLp 2 (fun q => F 0 q ω) : EuclideanSpace ℂ (Fin (d + 1))))
          (reducedLaw Q) :=
        (firstStripHilbertPrimitive_integrable (reducedLaw Q)
          (firstStripSystemPack (reducedLaw Q) (d + 1) (F 0)) hε hN hα).congr
          ((firstStripSystemPack_coe (reducedLaw Q) (d + 1) (F 0)).fun_comp
            (firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) α))
      have hiBound : (fun ω => firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹
          ((n : ℝ) + 1) α
          (WithLp.toLp 2 (fun q => F 0 q ω) : EuclideanSpace ℂ (Fin (d + 1)))) ≤ᵐ[reducedLaw Q]
          fun _ => A₀ := by
        filter_upwards [hini] with ω hω
        have hF₀ : (fun q => F 0 q ω) =
            Fin.cons (uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0 ω) (fun j => G 0 j ω) := by
          funext q
          refine Fin.cases ?_ (fun j => ?_) q <;>
            simp only [F, Fin.cons_zero, Fin.cons_succ, Real.toNNReal_zero]
        rw [hF₀]
        apply (firstStripHilbertPrimitive_le_initial_bound hε hN hα hM _ hω).trans
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
          (by linarith : ((n : ℝ) + 1)⁻¹ + M ^ 2 ≤ 1 + M ^ 2) hα)
          (mul_nonneg (by norm_num) (sq_nonneg _))
      simpa using integral_mono_ae hi (integrable_const A₀) hiBound
    have hg := firstStrip_integral_gronwall_of_positive_intervals henc
      (mul_nonneg (le_trans zero_le_one hC₀) (by linarith : 0 ≤ 1 + α))
      (fun u₀ u₁ hu₀ hu => hb _ _ _ hε hN hα u₀ u₁ hu₀ hu) (t : ℝ) t.coe_nonneg
    exact hg.trans (mul_le_mul_of_nonneg_right hen₀ (Real.exp_pos _).le)
  obtain ⟨hi, hb⟩ := firstStripSystem_moment_of_primitive_bound (reducedLaw Q)
    (F (t : ℝ)) hα hB he
  have hgrad : (fun j => G (t : ℝ) j) = firstStripGradient hd Q β a μ ζ P Pdag hP ν t := by
    have he := firstStripTimeGradient_eq hd Q β a μ ζ P Pdag hP ν
      (show 0 < (t : ℝ) by linarith)
    simpa only [Real.toNNReal_coe] using (congrArg (fun g => fun j => g j)
      (hGe (t : ℝ) (by linarith))).trans he
  have hE (ω : FieldPair d) : (∑ q, ‖F (t : ℝ) q ω‖ ^ 2) =
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ^ 2 +
        ∑ j, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2 := by
    simp only [F, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Real.toNNReal_coe]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [congrFun hgrad j]
  refine ⟨?_, ?_⟩
  · simpa only [hE, hαp] using hi
  · have hpref : 2 * (α + 1) * A₀ ≤ C ^ p := by
      have h := firstStrip_initial_power_prefactor_bound (M := M) hp
      have hpC := Real.rpow_le_rpow (by positivity : 0 ≤ Real.exp 1 * (1 + M ^ 2)) hCM
        (by linarith : 0 ≤ p)
      calc
        _ = (p / 2) * M ^ 2 * (1 + M ^ 2) ^ (p / 2 - 1) := by dsimp only [A₀, α]; ring
        _ ≤ (Real.exp 1 * (1 + M ^ 2)) ^ p := h
        _ ≤ C ^ p := hpC
    have hexp : Real.exp (C₀ * (1 + α) * (t : ℝ)) ≤
        Real.exp (C * p * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ t.coe_nonneg
      have hrate : C₀ * (p / 2) ≤ C * p := by
        calc
          _ ≤ C * (p / 2) := mul_le_mul_of_nonneg_right hCC (by linarith)
          _ ≤ C * p := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have hs : C * p ≤ C * p * (1 + ‖ζ‖ ^ 2) := by
        have hz := mul_nonneg (mul_nonneg (show 0 ≤ C by linarith)
          (show 0 ≤ p by linarith)) (sq_nonneg ‖ζ‖)
        nlinarith
      have hα' : 1 + α = p / 2 := by linarith [hαp]
      rw [hα']
      exact hrate.trans hs
    have htotal : 2 * (α + 1) * B ≤
        C ^ p * Real.exp (C * p * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) := by
      dsimp only [B]
      rw [← mul_assoc]
      exact mul_le_mul hpref hexp (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _)
    simpa only [hE, hαp] using hb.trans htotal

theorem crudeEnergy_first_strip_of_pointKernel :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
    IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
    IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
    IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    (∀ t : ℝ≥0, 1 ≤ (t : ℝ) → (t : ℝ) < 2 →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t)) ∧
    (∀ t : ℝ≥0, 1 ≤ (t : ℝ) → (t : ℝ) < 2 → ‖ζ‖ ≤ 4 →
      (∀ᵐ ω ∂reducedLaw Q,
        ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ +
          Real.sqrt (∑ j : Fin d, ‖G t j ω‖ ^ 2) ≤
        C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) ∧
      (∀ (ρ : ℝ) (hρ : 0 < ρ) (x : Vec d), ∀ᵐ ω ∂reducedLaw Q,
        ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ +
          localSpatialEnergy Q t ρ hρ x (G t) 0 ω ≤
        C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)))) := by
  intro d hd D
  obtain ⟨C₀, hC₀, hb⟩ := firstStrip_endpoint_uniform_radial_moments d hd D
  let C := max 1 (8 * C₀ * Real.exp (2 * C₀))
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀n : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hCbase : 8 * C₀ * Real.exp (2 * C₀) ≤ C := le_max_right _ _
  have hCC : C₀ ≤ C := by
    have he := Real.one_le_exp (show 0 ≤ 2 * C₀ by positivity)
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 8 * C₀ by positivity)
    nlinarith
  refine ⟨C, 0, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hT ν
  refine ⟨fun t => firstStripGradient hd Q β a μ ζ P Pdag hP ν t, ?_, ?_⟩
  · intro t ht _
    exact firstStripGradient_spec hd Q hQ β a μ ζ P Pdag hP hT hβ ν t
      (NNReal.coe_pos.mp (by linarith))
  · intro t ht ht₂ hζ
    let E := fun ω : FieldPair d => ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ^ 2 +
      ∑ j, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2
    let K := C₀ * Real.exp (C₀ * (1 + ‖ζ‖ ^ 2) * (t : ℝ))
    have hK : 0 < K := mul_pos hC₀n (Real.exp_pos _)
    have hpow (n : ℕ) : C₀ ^ (2 * ((n : ℝ) + 1)) *
        Real.exp (C₀ * (2 * ((n : ℝ) + 1)) * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) =
        (K ^ 2) ^ (n + 1) := by
      have hCpow : C₀ ^ (2 * ((n : ℝ) + 1)) = C₀ ^ (2 * (n + 1) : ℕ) := by
        rw [← Real.rpow_natCast]
        congr 1
        push_cast
        rfl
      have hepow : Real.exp (C₀ * (2 * ((n : ℝ) + 1)) * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) =
          Real.exp (C₀ * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) ^ (2 * (n + 1)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      calc
        _ = C₀ ^ (2 * (n + 1)) *
            Real.exp (C₀ * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) ^ (2 * (n + 1)) :=
          congrArg₂ (fun x y : ℝ => x * y) hCpow hepow
        _ = K ^ (2 * (n + 1)) := (mul_pow _ _ _).symm
        _ = (K ^ 2) ^ (n + 1) := pow_mul _ _ _
    have hm (n : ℕ) : Integrable (fun ω => E ω ^ (n + 1)) (reducedLaw Q) ∧
        (∫ ω, E ω ^ (n + 1) ∂reducedLaw Q) ≤ (K ^ 2) ^ (n + 1) := by
      have hn : 2 ≤ 2 * ((n : ℝ) + 1) := by have h := Nat.cast_nonneg (α := ℝ) n; linarith
      have h := hb Q hQ β a μ hβ ha hμ ζ P Pdag hP hT ν
        (2 * ((n : ℝ) + 1)) hn t ht ht₂ hζ
      have hp : (2 * ((n : ℝ) + 1)) / 2 = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      simpa only [hp, Real.rpow_natCast, hpow] using h
    have hae := firstStrip_ae_lt_twice_of_pow_integrals (reducedLaw Q) E
      (sq_pos_of_pos hK) (fun ω => add_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (fun n => (hm n).1) (fun n => (hm n).2)
    have hpoint : ∀ᵐ ω ∂reducedLaw Q,
        ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ +
        Real.sqrt (∑ j, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2) ≤ 4 * K := by
      filter_upwards [hae] with ω hω
      have hS : 0 ≤ ∑ j, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hs := Real.sq_sqrt hS
      have hn := norm_nonneg (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω)
      have hr := Real.sqrt_nonneg (∑ j, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2)
      dsimp only [E] at hω
      apply (sq_le_sq₀ (add_nonneg hn hr) (by positivity : 0 ≤ 4 * K)).mp
      nlinarith [sq_nonneg (‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ -
        Real.sqrt (∑ j, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2))]
    have hfinal : 2 * (4 * K) ≤ C * (2 + (t : ℝ)) ^ (0 : ℕ) *
        Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
      have hexp : Real.exp (C₀ * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) ≤
          Real.exp (2 * C₀) * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hCC
          (mul_nonneg (sq_nonneg ‖ζ‖) t.coe_nonneg)
        have ht' := mul_le_mul_of_nonneg_left ht₂.le hC₀n.le
        nlinarith
      calc
        _ = (8 * C₀) * Real.exp (C₀ * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) := by dsimp only [K]; ring
        _ ≤ (8 * C₀) * (Real.exp (2 * C₀) * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
        _ ≤ C * (2 + (t : ℝ)) ^ (0 : ℕ) * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
          simp only [pow_zero, mul_one]
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right hCbase (Real.exp_pos _).le
    refine ⟨hpoint.mono (fun ω hω => hω.trans ((le_mul_of_one_le_left
      (show 0 ≤ 4 * K by positivity) (by norm_num : (1 : ℝ) ≤ 2)).trans hfinal)), ?_⟩
    intro ρ hρ x
    exact (norm_add_localSpatialEnergy_le_of_ae_bound Q _ _ (by positivity : 0 ≤ 4 * K)
      hpoint t ρ hρ x).mono fun ω hω => hω.trans hfinal

end EinsteinFull.Blueprint
