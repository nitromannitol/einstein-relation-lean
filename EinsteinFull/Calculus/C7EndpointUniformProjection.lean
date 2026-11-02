import EinsteinFull.Calculus.S5ExpWeightSupport
import Homogenization.Sobolev.Foundations.Cutoff.DerivativeBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import EllipticRegularity.Parabolic.SliceEstimate.WeakC1
import EllipticRegularity.Parabolic.NashLower.Restrict
import EllipticRegularity.Parabolic.Moser.TimeContinuity
import EinsteinFull.Calculus.C4PhysicalOrbitGradientContinuity
import EinsteinFull.Calculus.C3EndpointLocalizationSupport
import EinsteinFull.Calculus.C1EndpointForceDivision
import EinsteinFull.Calculus.C2EndpointShortTimeProjection
import EinsteinFull.Calculus.C1ShortTimeClockEndpointProjection
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup
import EinsteinFull.Calculus.C1ForcedLocalityClosureSupport
import EinsteinFull.Calculus.C9ShortTimeLocality
import Mathlib.Algebra.Order.Chebyshev
import EinsteinRelation.Sharpness.FieldDerivativeMeasurability
import EinsteinRelation.Sharpness.PhysicalLawSampleBounds
import EinsteinFull.Blueprint.Foundation.Proofs.ReducedBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import PDEFoundation.Measure.AffineNormalizedVolume
import Mathlib.MeasureTheory.Integral.Prod
import EinsteinFull.Calculus.C8EndpointTransposeProjection
import EinsteinFull.Calculus.C25EndpointLocalObservation
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup_u23_endpoints
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
/- SUPERVISOR EXACT TARGET. Replace comment with proved declaration.
theorem endpoint_uniform_projection_of_graph_deps :
∀ (hA : node_stationary_u2D_analytic_u2D_semigroupStmt) (hlocal : node_e_u3A_forced_u2D_localityStmt),
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) (hB : 0 < B) (T : ℝ),
    ∃ R K c : ℝ, 1 ≤ R ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ ρ : ℝ, R ≤ ρ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] indexedEndpoint hd Q ν ζ P Pdag β a μ t →
      ‖E - EndpointProjection.project
        (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        K * Real.exp (-c * ρ ^ 2) := by
-/
/-- Original graph locality gives a uniform fixed-projection error on the
part of the bounded time window at or above unit time. -/
theorem endpoint_uniform_projection_large_time_of_graph_dep :
∀ (hlocal : node_e_u3A_forced_u2D_localityStmt),
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) (hB : 0 < B) (T : ℝ),
    ∃ R K c : ℝ, 1 ≤ R ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → (t : ℝ) ≤ T → ∀ ρ : ℝ, R ≤ ρ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] indexedEndpoint hd Q ν ζ P Pdag β a μ t →
      ‖E - EndpointProjection.project
        (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        K * Real.exp (-c * ρ ^ 2) := by
  intro hlocal d hd D B hB T
  obtain ⟨C, c, N, hC, hc, hdata⟩ := hlocal d hd D
  let S := max 1 T
  let R := C * max 1 (Real.sqrt S)
  let K := 4 * C * (2 + S) ^ N * Real.exp (C * B ^ 2 * S)
  have hS : 1 ≤ S := le_max_left _ _
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hR : 1 ≤ R := hC.trans
    (le_mul_of_one_le_right hC0.le (le_max_left _ _))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨R, K, c / S, hR, hK, div_pos hc hS0, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν t ht htT ρ hρ p _ E hE
  have ht0 : 0 < (t : ℝ) := lt_of_lt_of_le zero_lt_one ht
  have htS : (t : ℝ) ≤ S := htT.trans (le_max_right _ _)
  have hrad : C * Real.sqrt (t : ℝ) ≤ ρ := by
    apply le_trans _ hρ
    dsimp [R]
    apply mul_le_mul_of_nonneg_left _ hC0.le
    exact (Real.sqrt_le_sqrt htS).trans (le_max_right _ _)
  obtain ⟨G, _, hg, _⟩ := hdata Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨V, _, hl, _, he, _⟩ := hg t ht ρ hrad
  let ε := C * (2 + (t : ℝ)) ^ N *
    Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have happ : ∀ᵐ ω ∂reducedLaw Q,
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω - V ω‖ ≤ ε := by
    filter_upwards [he] with ω h
    exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans h
  obtain ⟨W, hw, hew⟩ := EndpointLocalization.indexed_approximation
    hd Q ν ζ P Pdag β a μ t ρ V hl hε happ
  have hb := EndpointLocalization.norm_sub_project_le Q ρ E _ W hE hw
    (mul_nonneg (by norm_num) hε) hew
  have hproj : ‖E - EndpointProjection.project
      (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
      4 * C * (2 + (t : ℝ)) ^ N *
        Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)) := by
    calc
      _ ≤ 2 * (2 * ε) := hb
      _ = _ := by dsimp [ε]; ring
  exact hproj.trans (EndpointLocalization.gaussian_window_bound C c B S ρ t N
    hC0.le hc hB.le hS0 ht0 htS ζ hζ)

/-- The actual drift is measurable from any unit neighborhood of the origin. -/
private theorem initial_drift_local {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    IsComplexLocalObservation Q ρ (β i) := by
  let χ : Vec d → ℝ := fun x => min 1 (max 0 (2 - 2 * euclideanNorm x))
  have hχ : Continuous χ := by
    dsimp only [χ]
    exact continuous_const.min (continuous_const.max
      (continuous_const.sub (continuous_const.mul Entropy.continuous_euclideanNorm')))
  let F (ω : FieldPair d) (j : Fin d) : C(Vec d, ℝ) :=
    ⟨fun x => χ x * ω.1 x j i, hχ.mul ((continuous_apply i).comp ((continuous_apply j).comp ω.1.continuous))⟩
  have hFm (j : Fin d) : @Measurable (FieldPair d) C(Vec d, ℝ)
      (localSigma {x : Vec d | euclideanNorm x < ρ}) (borel _) (fun ω => F ω j) := by
    let : MeasurableSpace (FieldPair d) := localSigma {x : Vec d | euclideanNorm x < ρ}
    apply measurable_continuousMap_of_evaluations
    intro x
    by_cases hx : euclideanNorm x < ρ
    · have hm : Measurable (fun ω : FieldPair d => (ω.1 x, ω.2 x)) := by
        rw [measurable_iff_comap_le]
        exact le_iSup_of_le ⟨x, hx⟩ le_rfl
      exact ((show Continuous (fun A : Mat d => A j i) from
        (continuous_apply i).comp (continuous_apply j)).measurable.comp hm.fst).const_mul (χ x)
    · have hz : χ x = 0 := by
        dsimp only [χ]
        rw [max_eq_left (by linarith : 2 - 2 * euclideanNorm x ≤ 0)]
        norm_num
      simpa only [F, ContinuousMap.coe_mk, hz, zero_mul] using
        (measurable_const : Measurable (fun _ : FieldPair d => (0 : ℝ)))
  have he (ω : FieldPair d) (j : Fin d) :
      coordinateDerivative j (F ω j) 0 = coordinateDerivative j (fun x => ω.1 x j i) 0 := by
    have hn : ∀ᶠ x : Vec d in 𝓝 0, euclideanNorm x < 1 / 2 :=
      (Entropy.continuous_euclideanNorm'.continuousAt.eventually_lt_const (by
        norm_num [euclideanNorm, euclideanSq, dot])).filter_mono le_rfl
    have hh : (fun x => F ω j x) =ᶠ[𝓝 0] (fun x => ω.1 x j i) := by
      filter_upwards [hn] with x hx
      have hxχ : χ x = 1 := by
        dsimp only [χ]
        rw [min_eq_left (le_max_of_le_right (by linarith))]
      simp only [F, ContinuousMap.coe_mk, hxχ, one_mul]
    exact congrArg (fun A => A (unitVector j)) (hh.fderiv_eq (𝕜 := ℝ))
  refine ⟨fun ω => ((1 / 2 : ℝ) * ∑ j, coordinateDerivative j (F ω j) 0 : ℝ), ?_, ?_⟩
  · let : MeasurableSpace (FieldPair d) := localSigma {x : Vec d | euclideanNorm x < ρ}
    exact Complex.measurable_ofReal.comp ((Finset.measurable_sum _ fun j _ =>
      Sharpness.measurable_coordinateDerivative_of_measurable_continuousMap
        (fun ω => F ω j) (hFm j) j 0).const_mul (1 / 2 : ℝ))
  · filter_upwards [hβ i] with ω hω
    simp only [he, hω]

private theorem initial_local_smul {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {ρ : ℝ} {U : Lp ℂ 2 (reducedLaw Q)}
    (hU : IsComplexLocalObservation Q ρ U) (z : ℂ) :
    IsComplexLocalObservation Q ρ (z • U) := by
  obtain ⟨u, hu, heu⟩ := hU
  refine ⟨fun ω => z * u ω, hu.const_mul z, ?_⟩
  filter_upwards [heu, Lp.coeFn_smul z U] with ω h hsmul
  simpa only [Pi.smul_apply, smul_eq_mul, h] using hsmul.symm

private theorem initial_local_add {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {ρ : ℝ} {U V : Lp ℂ 2 (reducedLaw Q)}
    (hU : IsComplexLocalObservation Q ρ U) (hV : IsComplexLocalObservation Q ρ V) :
    IsComplexLocalObservation Q ρ (U + V) := by
  obtain ⟨u, hu, heu⟩ := hU
  obtain ⟨v, hv, hev⟩ := hV
  refine ⟨fun ω => u ω + v ω, hu.add hv, ?_⟩
  filter_upwards [heu, hev, Lp.coeFn_add U V] with ω hU hV hadd
  simpa only [Pi.add_apply, hU, hV] using hadd.symm

/-- Every actual endpoint at zero is measurable from a unit neighborhood.
The drift locality proof uses the same cutoff derivative argument as
`C6UnforcedDriftProductApproximants`, without its endpoint premise. -/
theorem endpoint_initial_local {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (ν : EndpointIndex d) (ρ : ℝ) (hρ : 1 ≤ ρ) :
    IsComplexLocalObservation Q ρ (indexedEndpoint hd Q ν ζ P Pdag β a μ 0) := by
  have hzero : (0 : Vec d) ∈ {x : Vec d | euclideanNorm x < ρ} := by
    simpa only [Set.mem_ofPred_eq, euclideanNorm, euclideanSq, dot, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, Real.sqrt_zero] using
      (lt_of_lt_of_le zero_lt_one hρ)
  have heval : Measurable[EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}]
      (fun ω : FieldPair d => (ω.1 0, ω.2 0)) :=
    Measurable.of_comap_le (le_iSup_of_le ⟨0, hzero⟩ le_rfl)
  have halocal (i j : Fin d) : IsComplexLocalObservation Q ρ (a i j) := by
    refine ⟨fun ω => (ω.1 0 i j : ℂ), ?_, (ha i j).symm⟩
    exact Complex.measurable_ofReal.comp ((show Continuous (fun A : Mat d => A i j) from
      (continuous_apply j).comp (continuous_apply i)).measurable.comp heval.fst)
  have hμlocal : IsComplexLocalObservation Q ρ μ :=
    ⟨fun ω => (ω.2 0 : ℂ), Complex.measurable_ofReal.comp heval.snd, hμ.symm⟩
  rcases ν with j | b
  · simpa only [indexedEndpoint, velocityEndpoint, hP.1, ContinuousLinearMap.id_apply] using
      isComplexLocal_centered Q (initial_local_add Q (initial_drift_local hβ j hρ)
        (initial_local_smul Q (halocal ⟨0, by omega⟩ j) ζ))
  · cases b
    · simpa only [indexedEndpoint, clockEndpoint, hP.1, ContinuousLinearMap.id_apply] using
        initial_local_smul Q (isComplexLocal_centered Q hμlocal) ζ
    · simpa only [indexedEndpoint, transposeEndpoint, hPdag.zero hP,
        ContinuousLinearMap.id_apply] using initial_drift_local hβ ⟨0, by omega⟩ hρ

/-- The fixed projection error is exactly zero initially, on every Lp carrier
in the assigned contract, for arbitrary complex force. -/
theorem endpoint_initial_projection_eq {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (ν : EndpointIndex d) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q))
    (hE : (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      indexedEndpoint hd Q ν ζ P Pdag β a μ 0) :
    EndpointProjection.project
      (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E = E := by
  have hloc := endpoint_initial_local hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν ρ hρ
  have herr := EndpointLocalization.norm_sub_project_le Q ρ E _ _ hE hloc (le_refl 0)
    (Filter.Eventually.of_forall fun ω => by simp only [sub_self, norm_zero, le_refl])
  have hz : E - EndpointProjection.project
      (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E = 0 :=
    norm_eq_zero.mp (le_antisymm (by simpa only [mul_zero] using herr) (norm_nonneg _))
  exact (sub_eq_zero.mp hz).symm

private theorem projection_error_le_initial_increment {Ω : Type*}
    {m0 : MeasurableSpace Ω} {η : Measure Ω} [IsFiniteMeasure η]
    (m : MeasurableSpace Ω) (U V : Lp ℂ 2 η)
    (hV : EndpointProjection.project (m := m) V = V) :
    ‖U - EndpointProjection.project (m := m) U‖ ≤ 2 * ‖U - V‖ := by
  let L : Lp ℂ 2 η →L[ℂ] Lp ℂ 2 η := EndpointProjection.projectionCLM (m := m)
  have hz : L V = V := hV
  have he : U - L U = (U - V) - L (U - V) := by
    rw [map_sub, hz]
    abel
  change ‖U - L U‖ ≤ 2 * ‖U - V‖
  rw [he]
  have hcontract : ‖L (U - V)‖ ≤ ‖U - V‖ :=
    EndpointProjection.norm_project_le (m := m) (U - V)
  calc
    _ ≤ ‖U - V‖ + ‖L (U - V)‖ := norm_sub_le _ _
    _ ≤ ‖U - V‖ + ‖U - V‖ := add_le_add (le_refl _) hcontract
    _ = _ := (two_mul _).symm

/-- The actual L² projection error is controlled by the change from the local
initial endpoint. This estimate asserts no Gaussian rate. -/
theorem endpoint_projection_error_le_initial_increment {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (ν : EndpointIndex d) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (t : ℝ≥0) :
    ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t - EndpointProjection.project
      (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ})
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤
    2 * ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t -
      indexedEndpoint hd Q ν ζ P Pdag β a μ 0‖ := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  exact projection_error_le_initial_increment
    (EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) _ _
    (endpoint_initial_projection_eq hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν ρ hρ
      2 _ Filter.EventuallyEq.rfl)

/-- At every fixed law, force and local radius, the actual L² projection error
tends to zero at time zero. No rate or uniformity in the law is asserted. -/
theorem endpoint_projection_error_tendsto_zero {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (ν : EndpointIndex d) (ρ : ℝ) (hρ : 1 ≤ ρ) :
    Tendsto (fun t : ℝ≥0 =>
      ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t - EndpointProjection.project
        (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ})
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖) (𝓝 0) (𝓝 0) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let F := fun t => indexedEndpoint hd Q ν ζ P Pdag β a μ t
  let L : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
    EndpointProjection.projectionCLM
      (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ})
  have hF : Continuous F := EndpointLocalization.continuous_indexed hd Q ν ζ P Pdag β a μ
    hP hPdag
  have hz : L (F 0) = F 0 :=
    endpoint_initial_projection_eq hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν ρ hρ
      2 (F 0) Filter.EventuallyEq.rfl
  change Tendsto (fun t => ‖F t - L (F t)‖) (𝓝 0) (𝓝 0)
  have hc := ((hF.sub (L.continuous.comp hF)).norm.tendsto 0)
  simpa only [Pi.sub_apply, Function.comp_apply, hz, sub_self, norm_zero] using hc

/-- Integrability on the physical coordinate carrier, with its product volume. -/
private theorem integrable_physical_gaussian {d : ℕ} {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) := by
  have hp : Integrable (fun x : Vec d =>
      ∏ j : Fin d, Real.exp (-κ * x j ^ 2))
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hκ)
  convert hp using 1
  funext x
  rw [← Real.exp_sum]
  congr 1
  simp only [euclideanSq, dot, ← Finset.mul_sum, sq]

/-- Split a physical Gaussian outside a ball, retaining an integrable
Gaussian factor. This is the scalar counterpart of the coefficient-source
calculation in `C10FirstUnitFluxLocality`. -/
private theorem gaussian_energy_tail_le {d : ℕ} (f : Vec d → ℂ)
    (hf : Continuous f) (κ ρ M : ℝ) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    (hM : 0 ≤ M) (hzero : ∀ x, euclideanNorm x < ρ → f x = 0)
    (hbound : ∀ x, ‖f x‖ ≤ M) :
    (∫ x : Vec d, Real.exp (-κ * euclideanSq x) * ‖f x‖ ^ 2) ≤
      M ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
        ∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x) := by
  let K := M ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2)
  let g := fun x : Vec d => Real.exp (-κ * euclideanSq x) * ‖f x‖ ^ 2
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg hM 2) (Real.exp_nonneg _)
  have hpoint (x : Vec d) : g x ≤ K * Real.exp (-(κ / 2) * euclideanSq x) := by
    by_cases hx : euclideanNorm x < ρ
    · simpa only [g, hzero x hx, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero]
        using mul_nonneg hK (Real.exp_nonneg (-(κ / 2) * euclideanSq x))
    have hsq0 : 0 ≤ euclideanSq x := by
      change 0 ≤ ∑ j : Fin d, x j * x j
      exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (x j))
    have hsq : ρ ^ 2 ≤ euclideanSq x := by
      have hn : euclideanNorm x ^ 2 = euclideanSq x := Real.sq_sqrt hsq0
      nlinarith [le_of_not_gt hx]
    have he : Real.exp (-(κ / 2) * euclideanSq x) ≤
        Real.exp (-(κ / 2) * ρ ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      g x ≤ Real.exp (-κ * euclideanSq x) * M ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2)
          (Real.exp_nonneg _)
      _ = (M ^ 2 * Real.exp (-(κ / 2) * euclideanSq x)) *
          Real.exp (-(κ / 2) * euclideanSq x) := by
        have hs : -κ * euclideanSq x =
            -(κ / 2) * euclideanSq x + -(κ / 2) * euclideanSq x := by ring
        rw [hs, Real.exp_add]
        ring
      _ ≤ K * Real.exp (-(κ / 2) * euclideanSq x) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he (sq_nonneg M)) (Real.exp_nonneg _)
  have hg : Integrable (fun x : Vec d => Real.exp (-(κ / 2) * euclideanSq x)) :=
    integrable_physical_gaussian (by positivity)
  have hgc : Continuous g := by
    have hs : Continuous (euclideanSq : Vec d → ℝ) := by
      unfold euclideanSq dot
      fun_prop
    exact (Real.continuous_exp.comp (continuous_const.mul hs)).mul (hf.norm.pow 2)
  have hgi : Integrable g := (hg.const_mul K).mono' hgc.aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [g]; positivity)]
      exact hpoint x)
  exact (integral_mono hgi (hg.const_mul K) hpoint).trans_eq (integral_const_mul _ _)

/-- The actual and retained clock initial sources have Gaussian-small physical
weighted discrepancy. The clock bound is chosen before the environment law.
This supplies the initial-data term, without asserting an evolution comparison. -/
theorem exists_retained_initial_clock_gaussian_energy (d : ℕ) (D : StructuralData d) :
    ∃ M : ℝ, 0 ≤ M ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (κ ρ : ℝ), 0 < κ → 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanNorm x < ρ → χ x = 1) → ∀ ζ : ℂ,
      (∫ x : Vec d, Real.exp (-κ * euclideanSq x) *
        ‖ζ * ((ω.2 x - (ForcedLocality.retainedPair χ ω).2 x : ℝ) : ℂ)‖ ^ 2) ≤
      (‖ζ‖ * M) ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
        ∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x) := by
  obtain ⟨L, A, B, hL, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  refine ⟨L + 1, by linarith, ?_⟩
  intro Q
  filter_upwards [(hb d D.dependenceRange Q).2.2] with ω hω
  intro χ κ ρ hκ hρ hχ hinterior ζ
  let f := fun x => ζ * ((ω.2 x - (ForcedLocality.retainedPair χ ω).2 x : ℝ) : ℂ)
  have hf : Continuous f := Complex.continuous_ofReal.comp
      (ω.2.continuous.sub (ForcedLocality.retainedPair χ ω).2.continuous) |>.const_mul ζ
  apply gaussian_energy_tail_le f hf κ ρ (‖ζ‖ * (L + 1)) hκ hρ (by positivity)
  · intro x hx
    simp only [f, (ForcedLocality.retainedPair_eq_at χ ω (hinterior x hx)).2,
      sub_self, Complex.ofReal_zero, mul_zero]
  · intro x
    have hμ : |ω.2 x| ≤ L := by
      rw [abs_of_nonneg ((inv_nonneg.mpr (zero_le_one.trans hL)).trans (hω.2.1 x).1)]
      exact (hω.2.1 x).2
    have he : ω.2 x - (ForcedLocality.retainedPair χ ω).2 x =
        (1 - χ x) * (ω.2 x - 1) := by
      simp only [ForcedLocality.retainedPair, ContinuousMap.coe_mk]
      ring
    have habs : |ω.2 x - 1| ≤ L + 1 := by
      calc
        _ ≤ |ω.2 x| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ L + 1 := by simpa only [abs_one] using add_le_add hμ (le_refl (1 : ℝ))
    dsimp only [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, he, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr (hχ x).2)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg ζ)
    calc
      (1 - χ x) * |ω.2 x - 1| ≤ 1 * (L + 1) :=
        mul_le_mul (by linarith [(hχ x).1]) habs (abs_nonneg _) (by norm_num)
      _ = L + 1 := one_mul _

/-- The actual retained-clock initial discrepancy has a Gaussian short-time
energy bound. The constants precede the law, and one event covers every time,
cutoff, radius and force in the prescribed disc. -/
theorem exists_retained_initial_clock_short_time_energy (d : ℕ) (D : StructuralData d)
    (L B : ℝ) (hL : 0 < L) (hB : 0 ≤ B) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (ρ t : ℝ), 0 ≤ ρ → 0 < t → t ≤ 1 →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanNorm x < ρ → χ x = 1) →
    ∀ ζ : ℂ, ‖ζ‖ ≤ B →
      (∫ x : Vec d, Real.exp (-2 * euclideanSq x / (L * t)) *
        ‖ζ * ((ω.2 x - (ForcedLocality.retainedPair χ ω).2 x : ℝ) : ℂ)‖ ^ 2) ≤
      K * Real.exp (-c * ρ ^ 2 / t) := by
  obtain ⟨M, hM, hdata⟩ := exists_retained_initial_clock_gaussian_energy d D
  let J : ℝ := ∫ x : Vec d, Real.exp (-(1 / L) * euclideanSq x)
  let K : ℝ := (B * M) ^ 2 * J + 1
  have hJ : 0 ≤ J := integral_nonneg (fun _ => Real.exp_nonneg _)
  have hBM : 0 ≤ B * M := mul_nonneg hB hM
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, 1 / L, hK, one_div_pos.mpr hL, ?_⟩
  intro Q
  filter_upwards [hdata Q] with ω hω
  intro χ ρ t hρ ht ht1 hχ hinterior ζ hζ
  have hden : 0 < L * t := mul_pos hL ht
  have hκ : 0 < 2 / (L * t) := div_pos (by norm_num) hden
  have he := hω χ (2 / (L * t)) ρ hκ hρ hχ hinterior ζ
  have hmass : (∫ x : Vec d, Real.exp (-(2 / (L * t) / 2) * euclideanSq x)) ≤ J := by
    apply integral_mono
      (integrable_physical_gaussian (by positivity))
      (integrable_physical_gaussian (one_div_pos.mpr hL))
    intro x
    apply Real.exp_le_exp.mpr
    have hs : 0 ≤ euclideanSq x := by
      change 0 ≤ ∑ j : Fin d, x j * x j
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    have hi : 1 / L ≤ 2 / (L * t) / 2 := by
      have hd : L * t ≤ L := by nlinarith
      have hi := one_div_le_one_div_of_le hden hd
      convert hi using 1
      field_simp
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hi hs)
  have hfactor : (‖ζ‖ * M) ^ 2 ≤ (B * M) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hM)
      (mul_le_mul_of_nonneg_right hζ hM) 2
  have hmass0 : 0 ≤ ∫ x : Vec d,
      Real.exp (-(2 / (L * t) / 2) * euclideanSq x) :=
    integral_nonneg (fun _ => Real.exp_nonneg _)
  have hexp : -(2 / (L * t) / 2) * ρ ^ 2 = -(1 / L) * ρ ^ 2 / t := by
    field_simp
  have hintegrand : (fun x : Vec d => Real.exp (-(2 / (L * t)) * euclideanSq x) *
      ‖ζ * ((ω.2 x - (ForcedLocality.retainedPair χ ω).2 x : ℝ) : ℂ)‖ ^ 2) =
      (fun x : Vec d => Real.exp (-2 * euclideanSq x / (L * t)) *
      ‖ζ * ((ω.2 x - (ForcedLocality.retainedPair χ ω).2 x : ℝ) : ℂ)‖ ^ 2) := by
    funext x
    congr 2
    ring
  rw [hintegrand, hexp] at he
  have hcoeff : (‖ζ‖ * M) ^ 2 *
      (∫ x : Vec d, Real.exp (-(2 / (L * t) / 2) * euclideanSq x)) ≤ K := by
    calc
      _ ≤ (B * M) ^ 2 * J := mul_le_mul hfactor hmass hmass0 (pow_nonneg hBM 2)
      _ ≤ K := by dsimp [K]; linarith
  exact he.trans (by
    nlinarith only [mul_le_mul_of_nonneg_right hcoeff
      (Real.exp_nonneg (-(1 / L) * ρ ^ 2 / t))])

/-- The conservative initial sources for forward and transpose endpoints have
Gaussian-small physical energy. The coefficient bound precedes the law, and
the event is common to all coefficient columns and retained cutoffs. -/
theorem exists_retained_initial_coefficient_gaussian_energy (d : ℕ) (D : StructuralData d) :
    ∃ M : ℝ, 0 ≤ M ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (κ ρ : ℝ), 0 < κ → 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanNorm x < ρ → χ x = 1) → ∀ i : Fin d,
      (∑ j : Fin d, ∫ x : Vec d, Real.exp (-κ * euclideanSq x) *
        ‖((ω.1 x j i - (ForcedLocality.retainedPair χ ω).1 x j i : ℝ) : ℂ)‖ ^ 2) ≤
      (d : ℝ) * M ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
        ∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x) := by
  obtain ⟨L, A, B, hL, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  refine ⟨L + 1, by linarith, ?_⟩
  intro Q
  filter_upwards [(hb d D.dependenceRange Q).2.2] with ω hω
  intro χ κ ρ hκ hρ hχ hinterior i
  have hentry (x : Vec d) (j k : Fin d) : |ω.1 x j k| ≤ L := by
    apply abs_entry_le_of_quadratic_bounds (zero_le_one.trans hL) (ω.1 x) (hω.1 x).1
    · intro ξ
      exact (mul_nonneg (inv_nonneg.mpr (zero_le_one.trans hL))
        (euclideanSq_nonneg_coords ξ)).trans ((hω.1 x).2 ξ).1
    · exact fun ξ => ((hω.1 x).2 ξ).2
  have hj (j : Fin d) :
      (∫ x : Vec d, Real.exp (-κ * euclideanSq x) *
        ‖((ω.1 x j i - (ForcedLocality.retainedPair χ ω).1 x j i : ℝ) : ℂ)‖ ^ 2) ≤
      (L + 1) ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
        ∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x) := by
    have hf : Continuous (fun x : Vec d =>
        ((ω.1 x j i - (ForcedLocality.retainedPair χ ω).1 x j i : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((ω.1.continuous.matrix_elem j i).sub
        ((ForcedLocality.retainedPair χ ω).1.continuous.matrix_elem j i))
    apply gaussian_energy_tail_le _ hf κ ρ (L + 1) hκ hρ (by linarith)
    · intro x hx
      have he := congrArg (fun a : Mat d => a j i)
        (ForcedLocality.retainedPair_eq_at χ ω (hinterior x hx)).1
      simp only [he, sub_self, Complex.ofReal_zero]
    · intro x
      have he : ω.1 x j i - (ForcedLocality.retainedPair χ ω).1 x j i =
          (1 - χ x) * (ω.1 x j i - (1 : Mat d) j i) := by
        simp only [ForcedLocality.retainedPair, ContinuousMap.coe_mk,
          Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      have hId : |(1 : Mat d) j i| ≤ 1 := by
        simp only [Matrix.one_apply]
        split_ifs <;> norm_num
      rw [Complex.norm_real, Real.norm_eq_abs, he, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr (hχ x).2)]
      calc
        _ ≤ 1 * (L + 1) := mul_le_mul (by linarith [(hχ x).1])
          ((abs_sub _ _).trans (add_le_add (hentry x j i) hId))
          (abs_nonneg _) zero_le_one
        _ = L + 1 := one_mul _
  calc
    _ ≤ ∑ _j : Fin d, (L + 1) ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
        ∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x) :=
      Finset.sum_le_sum fun j _ => hj j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring

/-- Negative powers of time are absorbed by half of the spatial Gaussian
on the first unit interval. The displayed constant is independent of time
and radius. -/
theorem short_time_gaussian_polynomial_bound (c ρ t : ℝ) (N : ℕ)
    (hc : 0 < c) (hρ : 1 ≤ ρ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (t⁻¹) ^ N * Real.exp (-c * ρ ^ 2 / t) ≤
      ((2 / c) ^ N * (N.factorial : ℝ)) * Real.exp (-(c / 2) * ρ ^ 2) := by
  let x : ℝ := c / (2 * t)
  let q : ℝ := c / 2 * ρ ^ 2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hfac : 0 < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hpow : x ^ N ≤ Real.exp x * (N.factorial : ℝ) :=
    (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp x hx N)
  have hr : 1 ≤ ρ ^ 2 := by nlinarith
  have hqr : c / 2 ≤ q := by
    dsimp [q]
    nlinarith
  have hxq : x ≤ q / t := by
    have hh := div_le_div_of_nonneg_right hqr ht.le
    simpa only [x, div_div, mul_comm t 2] using hh
  have hqt : q ≤ q / t := (le_div_iff₀ ht).mpr (by nlinarith)
  have heq : c * ρ ^ 2 / t = 2 * (q / t) := by dsimp [q]; ring
  have hexp : x + (-c * ρ ^ 2 / t) ≤ -(c / 2) * ρ ^ 2 := by
    have hn : -c * ρ ^ 2 / t = -(c * ρ ^ 2 / t) := by ring
    rw [hn, heq]
    have hneg : -(c / 2) * ρ ^ 2 = -q := by dsimp [q]; ring
    rw [hneg]
    linarith only [hxq, hqt]
  have hinv : t⁻¹ = (2 / c) * x := by
    dsimp [x]
    field_simp [ne_of_gt hc, ne_of_gt ht]
  calc
    _ = (2 / c) ^ N * (x ^ N * Real.exp (-c * ρ ^ 2 / t)) := by
      rw [hinv, mul_pow]
      ring
    _ ≤ (2 / c) ^ N *
        ((Real.exp x * (N.factorial : ℝ)) * Real.exp (-c * ρ ^ 2 / t)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)) (by positivity)
    _ = ((2 / c) ^ N * (N.factorial : ℝ)) *
        Real.exp (x + (-c * ρ ^ 2 / t)) := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)

/-- Force growth and a polynomial time singularity fit the uniform endpoint
Gaussian on any prescribed force disc during the first unit interval. -/
theorem short_time_gaussian_force_window_bound (C c B ρ t : ℝ) (N : ℕ)
    (hC : 0 ≤ C) (hc : 0 < c) (hB : 0 ≤ B) (hρ : 1 ≤ ρ)
    (ht : 0 < t) (ht1 : t ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ B) :
    C * (t⁻¹) ^ N * Real.exp (C * ‖z‖ ^ 2 * t - c * ρ ^ 2 / t) ≤
      (C * (2 / c) ^ N * (N.factorial : ℝ) * Real.exp (C * B ^ 2)) *
        Real.exp (-(c / 2) * ρ ^ 2) := by
  have hforce : C * ‖z‖ ^ 2 * t ≤ C * B ^ 2 := by
    calc
      _ ≤ C * B ^ 2 * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hz 2) hC) ht1 ht.le (mul_nonneg hC (pow_nonneg hB 2))
      _ = _ := mul_one _
  have htail := short_time_gaussian_polynomial_bound c ρ t N hc hρ ht ht1
  calc
    _ = C * Real.exp (C * ‖z‖ ^ 2 * t) *
        ((t⁻¹) ^ N * Real.exp (-c * ρ ^ 2 / t)) := by
      rw [show C * ‖z‖ ^ 2 * t - c * ρ ^ 2 / t =
        C * ‖z‖ ^ 2 * t + (-c * ρ ^ 2 / t) by ring, Real.exp_add]
      ring
    _ ≤ (C * Real.exp (C * B ^ 2)) *
        (((2 / c) ^ N * (N.factorial : ℝ)) * Real.exp (-(c / 2) * ρ ^ 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hforce) hC)
        htail (by positivity) (by positivity)
    _ = _ := by ring

/-- A bounded multiplier vanishing on the retained interior transfers a
Gaussian tail to arbitrary measurable data. The data need only have finite
energy for the wider Gaussian; no pointwise bound on them is required. -/
theorem gaussian_multiplier_energy_bound {d : ℕ} (m G : Vec d → ℂ)
    (hm : AEStronglyMeasurable m) (hG : AEStronglyMeasurable G)
    (κ ρ M : ℝ) (hκ : 0 < κ) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hzero : ∀ x, euclideanNorm x < ρ → m x = 0)
    (hbound : ∀ x, ‖m x‖ ≤ M)
    (henergy : Integrable (fun x =>
      Real.exp (-(κ / 2) * euclideanSq x) * ‖G x‖ ^ 2)) :
    Integrable (fun x => Real.exp (-κ * euclideanSq x) * ‖m x * G x‖ ^ 2) ∧
      (∫ x : Vec d, Real.exp (-κ * euclideanSq x) * ‖m x * G x‖ ^ 2) ≤
        M ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
          ∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x) * ‖G x‖ ^ 2 := by
  let K := M ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2)
  let f := fun x : Vec d => Real.exp (-κ * euclideanSq x) * ‖m x * G x‖ ^ 2
  let g := fun x : Vec d => Real.exp (-(κ / 2) * euclideanSq x) * ‖G x‖ ^ 2
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg hM 2) (Real.exp_nonneg _)
  have hp (x : Vec d) : f x ≤ K * g x := by
    by_cases hx : euclideanNorm x < ρ
    · simpa only [f, hzero x hx, zero_mul, norm_zero,
        zero_pow (by omega : 2 ≠ 0), mul_zero] using
        mul_nonneg hK (show 0 ≤ g x by dsimp [g]; positivity)
    have hs0 : 0 ≤ euclideanSq x := euclideanSq_nonneg_coords x
    have hs : ρ ^ 2 ≤ euclideanSq x := by
      have hn : euclideanNorm x ^ 2 = euclideanSq x := Real.sq_sqrt hs0
      nlinarith [le_of_not_gt hx]
    have he : Real.exp (-(κ / 2) * euclideanSq x) ≤
        Real.exp (-(κ / 2) * ρ ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
    have hsplit : Real.exp (-κ * euclideanSq x) =
        Real.exp (-(κ / 2) * euclideanSq x) *
          Real.exp (-(κ / 2) * euclideanSq x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hb : ‖m x * G x‖ ^ 2 ≤ M ^ 2 * ‖G x‖ ^ 2 := by
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2) (sq_nonneg _)
    calc
      f x ≤ Real.exp (-κ * euclideanSq x) * (M ^ 2 * ‖G x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
      _ = (M ^ 2 * Real.exp (-(κ / 2) * euclideanSq x)) * g x := by
        rw [hsplit]; dsimp [g]; ring
      _ ≤ K * g x := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he (sq_nonneg M)) (by dsimp [g]; positivity)
  have hs : Continuous (euclideanSq : Vec d → ℝ) := by
    unfold euclideanSq dot
    fun_prop
  have hfm : AEStronglyMeasurable f :=
    (Real.continuous_exp.comp (continuous_const.mul hs)).aestronglyMeasurable.mul
      ((hm.mul hG).norm.pow 2)
  have hfi : Integrable f := (henergy.const_mul K).mono' hfm
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [f]; positivity)]
      exact hp x)
  exact ⟨hfi, (integral_mono hfi (henergy.const_mul K) hp).trans_eq
    (integral_const_mul _ _)⟩

/-- Actual retained coefficient defects acting on arbitrary finite-energy
spatial gradients have a Gaussian tail, on a single event common to all
cutoffs, entries and data. The multiplier bound precedes the law. -/
theorem exists_retained_coefficient_multiplier_energy (d : ℕ) (D : StructuralData d) :
    ∃ M : ℝ, 0 ≤ M ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (κ ρ : ℝ), 0 < κ → 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanNorm x < ρ → χ x = 1) → ∀ j k : Fin d,
    ∀ G : Vec d → ℂ, AEStronglyMeasurable G →
      Integrable (fun x => Real.exp (-(κ / 2) * euclideanSq x) * ‖G x‖ ^ 2) →
      (∫ x : Vec d, Real.exp (-κ * euclideanSq x) *
        ‖((ω.1 x j k - (ForcedLocality.retainedPair χ ω).1 x j k : ℝ) : ℂ) * G x‖ ^ 2) ≤
      M ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
        ∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x) * ‖G x‖ ^ 2 := by
  obtain ⟨L, A, B, hL, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  refine ⟨L + 1, by linarith, ?_⟩
  intro Q
  filter_upwards [(hb d D.dependenceRange Q).2.2] with ω hω
  intro χ κ ρ hκ hρ hχ hinterior j k G hG henergy
  let m := fun x : Vec d =>
    ((ω.1 x j k - (ForcedLocality.retainedPair χ ω).1 x j k : ℝ) : ℂ)
  have hm : Continuous m := Complex.continuous_ofReal.comp
    ((ω.1.continuous.matrix_elem j k).sub
      ((ForcedLocality.retainedPair χ ω).1.continuous.matrix_elem j k))
  apply (gaussian_multiplier_energy_bound m G hm.aestronglyMeasurable hG
    κ ρ (L + 1) hκ hρ (by linarith) ?_ ?_ henergy).2
  · intro x hx
    have he := congrArg (fun a : Mat d => a j k)
      (ForcedLocality.retainedPair_eq_at χ ω (hinterior x hx)).1
    simp only [m, he, sub_self, Complex.ofReal_zero]
  · intro x
    have hentry : |ω.1 x j k| ≤ L := by
      apply abs_entry_le_of_quadratic_bounds (zero_le_one.trans hL) (ω.1 x) (hω.1 x).1
      · intro ξ
        exact (mul_nonneg (inv_nonneg.mpr (zero_le_one.trans hL))
          (euclideanSq_nonneg_coords ξ)).trans ((hω.1 x).2 ξ).1
      · exact fun ξ => ((hω.1 x).2 ξ).2
    have he : ω.1 x j k - (ForcedLocality.retainedPair χ ω).1 x j k =
        (1 - χ x) * (ω.1 x j k - (1 : Mat d) j k) := by
      simp only [ForcedLocality.retainedPair, ContinuousMap.coe_mk,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hId : |(1 : Mat d) j k| ≤ 1 := by
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num
    change ‖((ω.1 x j k - (ForcedLocality.retainedPair χ ω).1 x j k : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, he, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr (hχ x).2)]
    calc
      _ ≤ 1 * (L + 1) := mul_le_mul (by linarith [(hχ x).1])
        ((abs_sub _ _).trans (add_le_add hentry hId)) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _

/-- Summing coordinate forcing terms costs only the number of coordinates
in squared weighted energy. Integrability is proved along with the bound. -/
theorem integrable_weighted_coordinate_sum {d : ℕ} (w : Vec d → ℝ)
    (F : Fin d → Vec d → ℂ) (hw : AEStronglyMeasurable w)
    (hw0 : ∀ x, 0 ≤ w x) (hF : ∀ j, AEStronglyMeasurable (F j))
    (hI : ∀ j, Integrable (fun x => w x * ‖F j x‖ ^ 2)) :
    Integrable (fun x => w x * ‖∑ j, F j x‖ ^ 2) ∧
      (∫ x : Vec d, w x * ‖∑ j, F j x‖ ^ 2) ≤
        (d : ℝ) * ∑ j, ∫ x : Vec d, w x * ‖F j x‖ ^ 2 := by
  have hp (x : Vec d) : w x * ‖∑ j, F j x‖ ^ 2 ≤
      (d : ℝ) * ∑ j, w x * ‖F j x‖ ^ 2 := by
    have hn : ‖∑ j, F j x‖ ≤ ∑ j, ‖F j x‖ := norm_sum_le _ _
    have hc : (∑ j, ‖F j x‖) ^ 2 ≤ (d : ℝ) * ∑ j, ‖F j x‖ ^ 2 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖F j x‖))
    calc
      _ ≤ w x * ((d : ℝ) * ∑ j, ‖F j x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          ((pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc) (hw0 x)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hi : Integrable (fun x => (d : ℝ) * ∑ j, w x * ‖F j x‖ ^ 2) :=
    (integrable_finsetSum Finset.univ (fun j _ => hI j)).const_mul (d : ℝ)
  have hsm : AEStronglyMeasurable (fun x => ∑ j, F j x) :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ (fun j _ => hF j)
  have hnm : AEStronglyMeasurable (fun x => ‖∑ j, F j x‖) := hsm.norm
  have hpm : AEStronglyMeasurable (fun x => ‖∑ j, F j x‖ ^ 2) := hnm.pow 2
  have hf : AEStronglyMeasurable (fun x => w x * ‖∑ j, F j x‖ ^ 2) := hw.mul hpm
  have hfi : Integrable (fun x => w x * ‖∑ j, F j x‖ ^ 2) := hi.mono' hf
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 x) (sq_nonneg _))]
      exact hp x)
  refine ⟨hfi, (integral_mono hfi hi hp).trans_eq ?_⟩
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hI j)]

/-- The actual signed complex drift forcing in a retained comparison has
Gaussian-small energy against arbitrary measurable finite-energy gradients.
One reduced-law event works for every force, cutoff and gradient. -/
theorem exists_retained_drift_defect_energy (d : ℕ) (D : StructuralData d) :
    ∃ M : ℝ, 0 ≤ M ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (κ ρ : ℝ), 0 < κ → 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanNorm x < ρ → χ x = 1) →
    ∀ (G : Fin d → Vec d → ℂ), (∀ j, AEStronglyMeasurable (G j)) →
      (∀ j, Integrable (fun x => Real.exp (-(κ / 2) * euclideanSq x) * ‖G j x‖ ^ 2)) →
    ∀ (i : Fin d) (ζ : ℂ),
      Integrable (fun x => Real.exp (-κ * euclideanSq x) *
        ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x (fun j => G j x) i ζ‖ ^ 2) ∧
      (∫ x : Vec d, Real.exp (-κ * euclideanSq x) *
        ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x (fun j => G j x) i ζ‖ ^ 2) ≤
      ‖ζ‖ ^ 2 * (d : ℝ) * M ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
        ∑ j : Fin d, ∫ x : Vec d,
          Real.exp (-(κ / 2) * euclideanSq x) * ‖G j x‖ ^ 2 := by
  obtain ⟨L, A, B, hL, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  refine ⟨L + 1, by linarith, ?_⟩
  intro Q
  filter_upwards [(hb d D.dependenceRange Q).2.2] with ω hω
  intro χ κ ρ hκ hρ hχ hinterior G hG henergy i ζ
  let m := fun (j : Fin d) (x : Vec d) =>
    ((ω.1 x j i - (ForcedLocality.retainedPair χ ω).1 x j i : ℝ) : ℂ)
  have hm (j : Fin d) : Continuous (m j) := Complex.continuous_ofReal.comp
    ((ω.1.continuous.matrix_elem j i).sub
      ((ForcedLocality.retainedPair χ ω).1.continuous.matrix_elem j i))
  have hbound (j : Fin d) (x : Vec d) : ‖m j x‖ ≤ L + 1 := by
    have hentry : |ω.1 x j i| ≤ L := by
      apply abs_entry_le_of_quadratic_bounds (zero_le_one.trans hL) (ω.1 x) (hω.1 x).1
      · intro ξ
        exact (mul_nonneg (inv_nonneg.mpr (zero_le_one.trans hL))
          (euclideanSq_nonneg_coords ξ)).trans ((hω.1 x).2 ξ).1
      · exact fun ξ => ((hω.1 x).2 ξ).2
    have hId : |(1 : Mat d) j i| ≤ 1 := by
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num
    dsimp only [m]
    rw [Complex.norm_real, Real.norm_eq_abs, EinsteinFull.C9ShortTimeLocality.retainedPair_coefficient_sub, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr (hχ x).2)]
    calc
      _ ≤ 1 * (L + 1) := mul_le_mul (by linarith [(hχ x).1])
        ((abs_sub _ _).trans (add_le_add hentry hId)) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hj (j : Fin d) := gaussian_multiplier_energy_bound (m j) (G j)
    (hm j).aestronglyMeasurable (hG j) κ ρ (L + 1) hκ hρ (by linarith)
    (by
      intro x hx
      dsimp only [m]
      rw [(congrArg (fun a : Mat d => a j i)
        (ForcedLocality.retainedPair_eq_at χ ω (hinterior x hx)).1), sub_self,
        Complex.ofReal_zero])
    (hbound j) (henergy j)
  have hs : Continuous (euclideanSq : Vec d → ℝ) := by
    unfold euclideanSq dot
    fun_prop
  have hsum := integrable_weighted_coordinate_sum
    (fun x : Vec d => Real.exp (-κ * euclideanSq x))
    (fun j x => m j x * G j x)
    (Real.continuous_exp.comp (continuous_const.mul hs)).aestronglyMeasurable
    (fun _ => Real.exp_nonneg _) (fun j => (hm j).aestronglyMeasurable.mul (hG j))
    (fun j => (hj j).1)
  have heq : (fun x : Vec d => Real.exp (-κ * euclideanSq x) *
      ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x (fun j => G j x) i ζ‖ ^ 2) =
      fun x => ‖ζ‖ ^ 2 * (Real.exp (-κ * euclideanSq x) *
        ‖∑ j, m j x * G j x‖ ^ 2) := by
    funext x
    simp only [EinsteinFull.C9ShortTimeLocality.retainedDriftDefect, m, norm_mul, mul_pow]
    ring
  rw [heq]
  refine ⟨hsum.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  have htot := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hj j).2)
  have hsumbound := hsum.2.trans (mul_le_mul_of_nonneg_left htot (Nat.cast_nonneg d))
  have hfinal := mul_le_mul_of_nonneg_left hsumbound (sq_nonneg ‖ζ‖)
  simpa only [← Finset.mul_sum, mul_assoc] using hfinal

/-- For symmetric actual coefficients, the retained divergence flux is half
of the unit-force drift defect on the same gradient. -/
theorem retained_flux_defect_eq_half_drift {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) (x : Vec d) (X : Fin d → ℂ) (i : Fin d)
    (hsym : (ω.1 x).transpose = ω.1 x) :
    EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x X i =
      (1 / 2 : ℂ) *
        EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x X i 1 := by
  unfold EinsteinFull.C9ShortTimeLocality.retainedFluxDefect
    EinsteinFull.C9ShortTimeLocality.retainedDriftDefect
  rw [one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hentry : ω.1 x i j = ω.1 x j i :=
    congrArg (fun a : Mat d => a j i) hsym
  rw [EinsteinFull.C9ShortTimeLocality.retainedPair_coefficient_sub,
    EinsteinFull.C9ShortTimeLocality.retainedPair_coefficient_sub, hentry]
  simp only [Matrix.one_apply, eq_comm]

/-- The actual retained divergence flux has Gaussian-small physical energy.
The constant precedes the law, and one event works for all cutoffs and data. -/
theorem exists_retained_flux_defect_energy (d : ℕ) (D : StructuralData d) :
    ∃ M : ℝ, 0 ≤ M ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (κ ρ : ℝ), 0 < κ → 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanNorm x < ρ → χ x = 1) →
    ∀ (G : Fin d → Vec d → ℂ), (∀ j, AEStronglyMeasurable (G j)) →
      (∀ j, Integrable (fun x => Real.exp (-(κ / 2) * euclideanSq x) * ‖G j x‖ ^ 2)) →
    ∀ i : Fin d,
      Integrable (fun x => Real.exp (-κ * euclideanSq x) *
        ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x (fun j => G j x) i‖ ^ 2) ∧
      (∫ x : Vec d, Real.exp (-κ * euclideanSq x) *
        ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x (fun j => G j x) i‖ ^ 2) ≤
      (d : ℝ) / 4 * M ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
        ∑ j : Fin d, ∫ x : Vec d,
          Real.exp (-(κ / 2) * euclideanSq x) * ‖G j x‖ ^ 2 := by
  obtain ⟨M, hM, henergy⟩ := exists_retained_drift_defect_energy d D
  obtain ⟨L, A, B, _, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  refine ⟨M, hM, ?_⟩
  intro Q
  filter_upwards [henergy Q, (hb d D.dependenceRange Q).2.2] with ω hω hbounds
  intro χ κ ρ hκ hρ hχ hinterior G hG hGe i
  obtain ⟨hint, hbound⟩ := hω χ κ ρ hκ hρ hχ hinterior G hG hGe i 1
  have heq : (fun x : Vec d => Real.exp (-κ * euclideanSq x) *
      ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x (fun j => G j x) i‖ ^ 2) =
      fun x => (1 / 4 : ℝ) * (Real.exp (-κ * euclideanSq x) *
        ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
          (fun j => G j x) i 1‖ ^ 2) := by
    funext x
    rw [retained_flux_defect_eq_half_drift χ ω x _ i (hbounds.1 x).1, norm_mul]
    norm_num
    ring
  rw [heq]
  refine ⟨hint.const_mul _, ?_⟩
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 1 / 4)
  norm_num only [norm_one, one_pow, one_mul] at h
  convert h using 1; ring

/-- Summing the actual divergence-flux energies preserves the same Gaussian
rate and the law-uniform quantifier order. -/
theorem exists_retained_total_flux_energy (d : ℕ) (D : StructuralData d) :
    ∃ M : ℝ, 0 ≤ M ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (κ ρ : ℝ), 0 < κ → 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanNorm x < ρ → χ x = 1) →
    ∀ (G : Fin d → Vec d → ℂ), (∀ j, AEStronglyMeasurable (G j)) →
      (∀ j, Integrable (fun x => Real.exp (-(κ / 2) * euclideanSq x) * ‖G j x‖ ^ 2)) →
      Integrable (fun x => ∑ i : Fin d, Real.exp (-κ * euclideanSq x) *
        ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x (fun j => G j x) i‖ ^ 2) ∧
      (∫ x : Vec d, ∑ i : Fin d, Real.exp (-κ * euclideanSq x) *
        ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x (fun j => G j x) i‖ ^ 2) ≤
      (d : ℝ) ^ 2 / 4 * M ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
        ∑ j : Fin d, ∫ x : Vec d,
          Real.exp (-(κ / 2) * euclideanSq x) * ‖G j x‖ ^ 2 := by
  obtain ⟨M, hM, henergy⟩ := exists_retained_flux_defect_energy d D
  refine ⟨M, hM, ?_⟩
  intro Q
  filter_upwards [henergy Q] with ω hω
  intro χ κ ρ hκ hρ hχ hinterior G hG hGe
  have hi := hω χ κ ρ hκ hρ hχ hinterior G hG hGe
  refine ⟨integrable_finsetSum _ (fun i _ => (hi i).1), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hi i).1)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hi i).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  convert h using 1; ring

/-- Both sources of the actual retained comparison have jointly bounded
Gaussian energy, uniformly over an arbitrary prescribed complex force disc.
This is a source estimate, without an assumption on a comparison solution. -/
theorem exists_retained_forcing_energy (d : ℕ) (D : StructuralData d)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (κ ρ : ℝ), 0 < κ → 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanNorm x < ρ → χ x = 1) →
    ∀ (G : Fin d → Vec d → ℂ), (∀ j, AEStronglyMeasurable (G j)) →
      (∀ j, Integrable (fun x => Real.exp (-(κ / 2) * euclideanSq x) * ‖G j x‖ ^ 2)) →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
      Integrable (fun x =>
        (∑ j : Fin d, Real.exp (-κ * euclideanSq x) *
          ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x (fun k => G k x) j‖ ^ 2) +
        Real.exp (-κ * euclideanSq x) *
          ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x (fun k => G k x) i ζ‖ ^ 2) ∧
      (∫ x : Vec d,
        (∑ j : Fin d, Real.exp (-κ * euclideanSq x) *
          ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x (fun k => G k x) j‖ ^ 2) +
        Real.exp (-κ * euclideanSq x) *
          ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x (fun k => G k x) i ζ‖ ^ 2) ≤
      C * Real.exp (-(κ / 2) * ρ ^ 2) *
        ∑ j : Fin d, ∫ x : Vec d,
          Real.exp (-(κ / 2) * euclideanSq x) * ‖G j x‖ ^ 2 := by
  obtain ⟨Mf, hMf, hf⟩ := exists_retained_total_flux_energy d D
  obtain ⟨Md, hMd, hd⟩ := exists_retained_drift_defect_energy d D
  refine ⟨(d : ℝ) ^ 2 / 4 * Mf ^ 2 + B ^ 2 * (d : ℝ) * Md ^ 2,
    add_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (pow_nonneg hB 2) (Nat.cast_nonneg d)) (sq_nonneg Md)), ?_⟩
  intro Q
  filter_upwards [hf Q, hd Q] with ω hflux hdrift
  intro χ κ ρ hκ hρ hχ hinterior G hG hGe i ζ hζ
  obtain ⟨hfi, hfe⟩ := hflux χ κ ρ hκ hρ hχ hinterior G hG hGe
  obtain ⟨hdi, hde⟩ := hdrift χ κ ρ hκ hρ hχ hinterior G hG hGe i ζ
  have hs : 0 ≤ ∑ j : Fin d, ∫ x : Vec d,
      Real.exp (-(κ / 2) * euclideanSq x) * ‖G j x‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro j _
    exact integral_nonneg (fun x => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
  have hz : ‖ζ‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have hdisc : ‖ζ‖ ^ 2 * (d : ℝ) * Md ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
      (∑ j : Fin d, ∫ x : Vec d,
        Real.exp (-(κ / 2) * euclideanSq x) * ‖G j x‖ ^ 2) ≤
      B ^ 2 * (d : ℝ) * Md ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
      (∑ j : Fin d, ∫ x : Vec d,
        Real.exp (-(κ / 2) * euclideanSq x) * ‖G j x‖ ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ hs
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg d)
  refine ⟨hfi.add hdi, ?_⟩
  rw [integral_add hfi hdi]
  calc
    _ ≤ _ := add_le_add hfe (hde.trans hdisc)
    _ = _ := by ring

/-- A nonnegative slice estimate controls the product energy without assuming
integrability of the smaller energy in advance. -/
private theorem integrable_prod_energy_of_slice_bound {d : ℕ}
    (ν : Measure ℝ) [SFinite ν] (f g : ℝ × Vec d → ℝ) (K : ℝ)
    (hf : AEStronglyMeasurable f (ν.prod volume))
    (hfn : ∀ y, 0 ≤ f y) (hg : Integrable g (ν.prod volume))
    (hslice : ∀ᵐ t ∂ν, Integrable (fun x => f (t, x)) ∧
      (∫ x : Vec d, f (t, x)) ≤ K * ∫ x : Vec d, g (t, x)) :
    Integrable f (ν.prod volume) ∧
      (∫ y, f y ∂ν.prod volume) ≤ K * ∫ y, g y ∂ν.prod volume := by
  have hfi : Integrable (fun t => ∫ x : Vec d, f (t, x)) ν :=
    (hg.integral_prod_left.const_mul K).mono' hf.integral_prod_right'
      (hslice.mono fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => hfn (t, x)))]
        exact ht.2)
  have hnorm : (fun t => ∫ x : Vec d, ‖f (t, x)‖) =
      fun t => ∫ x : Vec d, f (t, x) := by
    funext t
    apply integral_congr_ae
    exact ae_of_all _ fun x => Real.norm_of_nonneg (hfn (t, x))
  have hprod : Integrable f (ν.prod volume) := (integrable_prod_iff hf).mpr
    ⟨hslice.mono (fun _ ht => ht.1), by rw [hnorm]; exact hfi⟩
  refine ⟨hprod, ?_⟩
  rw [integral_prod _ hprod, integral_prod _ hg, ← integral_const_mul]
  exact integral_mono_ae hfi (hg.integral_prod_left.const_mul K)
    (hslice.mono fun _ ht => ht.2)

/-- The actual retained comparison sources have finite spacetime energy and
a Gaussian bound for every sigma-finite time measure. No integrability of the
comparison forcing is imposed: it follows from the wider gradient energy. -/
theorem exists_retained_spacetime_forcing_energy (d : ℕ) (D : StructuralData d)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (ν : Measure ℝ) [SFinite ν] (χ : C(Vec d, ℝ)) (κ ρ : ℝ),
      0 < κ → 0 ≤ ρ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanNorm x < ρ → χ x = 1) →
    ∀ G : Fin d → ℝ × Vec d → ℂ,
      (∀ j, AEStronglyMeasurable (G j) (ν.prod volume)) →
      (∀ j, Integrable (fun y => Real.exp (-(κ / 2) * euclideanSq y.2) *
        ‖G j y‖ ^ 2) (ν.prod volume)) →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
      Integrable (fun y =>
        (∑ j : Fin d, Real.exp (-κ * euclideanSq y.2) *
          ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω y.2 (fun k => G k y) j‖ ^ 2) +
        Real.exp (-κ * euclideanSq y.2) *
          ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω y.2 (fun k => G k y) i ζ‖ ^ 2)
        (ν.prod volume) ∧
      (∫ y : ℝ × Vec d,
        (∑ j : Fin d, Real.exp (-κ * euclideanSq y.2) *
          ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω y.2 (fun k => G k y) j‖ ^ 2) +
        Real.exp (-κ * euclideanSq y.2) *
          ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω y.2 (fun k => G k y) i ζ‖ ^ 2
        ∂ν.prod volume) ≤
      C * Real.exp (-(κ / 2) * ρ ^ 2) *
        ∑ j : Fin d, ∫ y : ℝ × Vec d,
          Real.exp (-(κ / 2) * euclideanSq y.2) * ‖G j y‖ ^ 2 ∂ν.prod volume := by
  obtain ⟨C, hC, henergy⟩ := exists_retained_forcing_energy d D B hB
  refine ⟨C, hC, ?_⟩
  intro Q
  filter_upwards [henergy Q] with ω hω
  intro ν _ χ κ ρ hκ hρ hχ hinterior G hG hGe i ζ hζ
  let f := fun y : ℝ × Vec d =>
    (∑ j : Fin d, Real.exp (-κ * euclideanSq y.2) *
      ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω y.2 (fun k => G k y) j‖ ^ 2) +
    Real.exp (-κ * euclideanSq y.2) *
      ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω y.2 (fun k => G k y) i ζ‖ ^ 2
  let g := fun y : ℝ × Vec d => ∑ j : Fin d,
    Real.exp (-(κ / 2) * euclideanSq y.2) * ‖G j y‖ ^ 2
  have hc (j k : Fin d) : Continuous (fun x : Vec d =>
      ((ω.1 x j k - (ForcedLocality.retainedPair χ ω).1 x j k : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((ω.1.continuous.matrix_elem j k).sub
      ((ForcedLocality.retainedPair χ ω).1.continuous.matrix_elem j k))
  have hm (j k : Fin d) : AEStronglyMeasurable (fun y : ℝ × Vec d =>
      ((ω.1 y.2 j k - (ForcedLocality.retainedPair χ ω).1 y.2 j k : ℝ) : ℂ))
      (ν.prod volume) := (hc j k).aestronglyMeasurable.comp_snd
  have hs : Continuous (euclideanSq : Vec d → ℝ) := by
    unfold euclideanSq dot
    fun_prop
  have hw : AEStronglyMeasurable (fun y : ℝ × Vec d =>
      Real.exp (-κ * euclideanSq y.2)) (ν.prod volume) :=
    (Real.continuous_exp.comp (continuous_const.mul hs)).aestronglyMeasurable.comp_snd
  have hflux (j : Fin d) : AEStronglyMeasurable (fun y : ℝ × Vec d =>
      EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω y.2 (fun k => G k y) j)
      (ν.prod volume) := by
    exact (Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun k _ => (hm j k).mul (hG k))).const_mul (1 / 2 : ℂ)
  have hdrift : AEStronglyMeasurable (fun y : ℝ × Vec d =>
      EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω y.2 (fun k => G k y) i ζ)
      (ν.prod volume) := by
    exact (Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun j _ => (hm j i).mul (hG j))).const_mul ζ
  have hfm : AEStronglyMeasurable f (ν.prod volume) :=
    (Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun j _ => hw.mul ((hflux j).norm.pow 2))).add (hw.mul (hdrift.norm.pow 2))
  have hgi : Integrable g (ν.prod volume) :=
    integrable_finsetSum _ (fun j _ => hGe j)
  have hGslice : ∀ᵐ t ∂ν, ∀ j, AEStronglyMeasurable (fun x => G j (t, x)) :=
    ae_all_iff.mpr (fun j => (hG j).prodMk_left)
  have hGeslice : ∀ᵐ t ∂ν, ∀ j,
      Integrable (fun x : Vec d => Real.exp (-(κ / 2) * euclideanSq x) * ‖G j (t, x)‖ ^ 2) :=
    ae_all_iff.mpr (fun j => (hGe j).prod_right_ae)
  have hslice : ∀ᵐ t ∂ν, Integrable (fun x => f (t, x)) ∧
      (∫ x : Vec d, f (t, x)) ≤ C * Real.exp (-(κ / 2) * ρ ^ 2) *
        ∫ x : Vec d, g (t, x) := by
    filter_upwards [hGslice, hGeslice] with t ht hte
    have h := hω χ κ ρ hκ hρ hχ hinterior (fun j x => G j (t, x)) ht hte i ζ hζ
    simpa only [f, g, integral_finsetSum _ (fun j _ => hte j)] using h
  have h := integrable_prod_energy_of_slice_bound ν f g
    (C * Real.exp (-(κ / 2) * ρ ^ 2)) hfm (fun y => by dsimp [f]; positivity)
    hgi hslice
  simpa only [g, integral_finsetSum _ (fun j _ => hGe j)] using h

/-- The exact fixed-projection estimate on the union of the two completed
time regimes, using original V1 locality and the actual local initial data. -/
theorem endpoint_uniform_projection_initial_or_large_time_of_graph_dep :
∀ (hlocal : node_e_u3A_forced_u2D_localityStmt),
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) (hB : 0 < B) (T : ℝ),
    ∃ R K c : ℝ, 1 ≤ R ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ t : ℝ≥0, ((t : ℝ) = 0 ∨ 1 ≤ (t : ℝ)) → (t : ℝ) ≤ T → ∀ ρ : ℝ, R ≤ ρ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] indexedEndpoint hd Q ν ζ P Pdag β a μ t →
      ‖E - EndpointProjection.project
        (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        K * Real.exp (-c * ρ ^ 2) := by
  intro hlocal d hd D B hB T
  obtain ⟨R, K, c, hR, hK, hc, hlarge⟩ :=
    endpoint_uniform_projection_large_time_of_graph_dep hlocal d hd D B hB T
  refine ⟨R, K, c, hR, hK, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν t ht htT ρ hρ p _ E hE
  rcases ht with ht | ht
  · have htzero : t = 0 := by exact_mod_cast ht
    subst t
    rw [endpoint_initial_projection_eq hd D Q hQ β a μ hβ ha hμ ζ P Pdag
      hP hPdag ν ρ (hR.trans hρ) p E hE, sub_self, norm_zero]
    exact mul_nonneg hK.le (Real.exp_nonneg _)
  · exact hlarge Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν t ht htT ρ hρ p E hE

open EinsteinFull.EndpointDivision EinsteinFull.EndpointProjection

/-- The original two graph inputs already give the full finite-p holomorphic
endpoint assembly, including local force division, initially and for t ≥ 1.
Only the open short-time interval is excluded from this supporting result. -/
theorem endpoint_initial_or_large_time_of_graph_deps
    (hA : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (hlocal : node_e_u3A_forced_u2D_localityStmt) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (p : ℝ) (hp : 2 ≤ p) (T B : ℝ), 0 ≤ T → 0 < B →
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
      (∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ)) →
    ∀ (ν : EndpointIndex d) (t : ℝ≥0), (t : ℝ) ≤ T → ((t : ℝ) = 0 ∨ 1 ≤ (t : ℝ)) →
    ∃ E H : ℂ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
      (∀ ζ, (E ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        (indexedEndpoint hd Q ν ζ (P ζ) (Pdag ζ) β a μ t : FieldPair d → ℂ)) ∧
      DifferentiableOn ℂ E {ζ | ‖ζ‖ < B + 1} ∧
      DifferentiableOn ℂ H {ζ | ‖ζ‖ < B} ∧
      (∀ ζ, ‖ζ‖ ≤ B + 1 → ‖E ζ‖ ≤ C) ∧
      (∀ ζ, ‖ζ‖ < B → E ζ - E 0 = ζ • H ζ ∧
        (∫ ω, H ζ ω ∂reducedLaw Q) = 0 ∧ ‖H ζ‖ ≤ C) ∧
      ∀ ρ : ℝ, C ≤ ρ →
      ∃ L K : ℂ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
      ∃ L₂ K₂ : ℂ → Lp ℂ 2 (reducedLaw Q),
        (∀ ζ, (L ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q] L₂ ζ ∧
          (K ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q] K₂ ζ ∧
          IsComplexLocalObservation Q ρ (L₂ ζ) ∧
          IsComplexLocalObservation Q ρ (K₂ ζ)) ∧
        DifferentiableOn ℂ L {ζ | ‖ζ‖ < B + 1} ∧
        DifferentiableOn ℂ (fun ζ => E ζ - L ζ) {ζ | ‖ζ‖ < B + 1} ∧
        DifferentiableOn ℂ K {ζ | ‖ζ‖ < B} ∧
        DifferentiableOn ℂ (fun ζ => H ζ - K ζ) {ζ | ‖ζ‖ < B} ∧
        (∀ ζ, ‖ζ‖ ≤ B + 1 →
          (∫ ω, L ζ ω ∂reducedLaw Q) = 0 ∧
          ‖L ζ‖ ≤ C ∧ ‖E ζ - L ζ‖ ≤ C * Real.exp (-c * ρ ^ 2)) ∧
        (∀ ζ, ‖ζ‖ < B →
          L ζ - L 0 = ζ • K ζ ∧
          (E ζ - L ζ) - (E 0 - L 0) = ζ • (H ζ - K ζ) ∧
          (∫ ω, K ζ ω ∂reducedLaw Q) = 0 ∧
          ‖K ζ‖ ≤ C ∧ ‖H ζ - K ζ‖ ≤ C * Real.exp (-c * ρ ^ 2)) := by
  intro d hd D q hq T B hT hB
  let : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  obtain ⟨CE, hCE, hrep⟩ := EndpointFiniteP.exists_representatives hA d hd D q hq T B hT hB
  obtain ⟨R, A, c, hR, hApos, hc, hloc⟩ :=
    endpoint_uniform_projection_initial_or_large_time_of_graph_dep hlocal d hd D (B + 1) (by linarith) T
  let C := max 1 (max R (max (2 * CE) (2 * A)))
  have hC : 1 ≤ C := le_max_left _ _
  have hRC : R ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hEC : 2 * CE ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hAC : 2 * A ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hEC' : CE ≤ C := (by linarith : CE ≤ 2 * CE).trans hEC
  have hAC' : A ≤ C := (by linarith : A ≤ 2 * A).trans hAC
  refine ⟨C, c, hC, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag ν t ht hregime
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨E, he, han, hed, hem, hen⟩ := hrep Q hQ β a μ hβ ha hμ P Pdag hP hPdag ν t ht
  let H := divide E
  have h0 : DifferentiableAt ℂ E 0 := (han 0).differentiableAt
  have hHd : DifferentiableOn ℂ H {z | ‖z‖ < B} :=
    (differentiableOn_divide (by linarith : 0 < B + 1) hed).mono
      (fun z hz => by dsimp at *; linarith)
  have hHn (z : ℂ) (hz : ‖z‖ < B) : ‖H z‖ ≤ C :=
    (norm_divide_le hB hed hen hz).trans hEC
  have hHm (z : ℂ) : (∫ ω, H z ω ∂reducedLaw Q) = 0 :=
    integral_divide_eq_zero h0 hem z
  refine ⟨E, H, he, hed, hHd, fun z hz => (hen z hz).trans hEC',
    fun z hz => ⟨factor E z, hHm z, hHn z hz⟩, ?_⟩
  intro ρ hρ
  let m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}
  have hm := Probability.localSigma_le_borel
    {x : Vec d | euclideanNorm x < ρ}
  let L := fun z => project (m := m) (E z)
  let K := fun z => project (m := m) (H z)
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hq)
  have hL2 (z : ℂ) := exists_local_l2 (p := ENNReal.ofReal q) Q ρ hp2 (E z)
  have hK2 (z : ℂ) := exists_local_l2 (p := ENNReal.ofReal q) Q ρ hp2 (H z)
  choose L₂ hLe hLl using hL2
  choose K₂ hKe hKl using hK2
  have hLd : DifferentiableOn ℂ L {z | ‖z‖ < B + 1} := differentiableOn_project hed
  have hKd : DifferentiableOn ℂ K {z | ‖z‖ < B} := differentiableOn_project hHd
  have herr (z : ℂ) (hz : ‖z‖ ≤ B + 1) :
      ‖E z - L z‖ ≤ A * Real.exp (-c * ρ ^ 2) :=
    hloc Q hQ β a μ hβ ha hμ z hz (P z) (Pdag z) (hP z) (hPdag z)
      ν t hregime ht ρ (hRC.trans hρ) (ENNReal.ofReal q) (E z) (he z)
  have hLfactor (z : ℂ) : L z - L 0 = z • K z := by
    rw [factor L z, divide_project h0 z]
  refine ⟨L, K, L₂, K₂, fun z => ⟨hLe z, hKe z, hLl z, hKl z⟩,
    hLd, hed.sub hLd, hKd, hHd.sub hKd, ?_, ?_⟩
  · intro z hz
    refine ⟨?_, (norm_project_le (E z)).trans ((hen z hz).trans hEC'), ?_⟩
    · exact (integral_project hm (E z)).trans (hem z)
    · exact (herr z hz).trans (mul_le_mul_of_nonneg_right hAC' (Real.exp_pos _).le)
  · intro z hz
    refine ⟨hLfactor z, ?_, ?_, (norm_project_le (H z)).trans (hHn z hz), ?_⟩
    · calc
        (E z - L z) - (E 0 - L 0) = (E z - E 0) - (L z - L 0) := by abel
        _ = z • H z - z • K z := by rw [factor E z, hLfactor z]
        _ = z • (H z - K z) := (smul_sub _ _ _).symm
    · exact (integral_project hm (H z)).trans (hHm z)
    · exact (norm_divide_sub_project_le hB hed herr hz).trans (by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le)
/-- A strictly positive terminal width makes the shrinking Gaussian an
admissible temporal weight, with the exact negative spatial moment term. -/
theorem short_time_moving_gaussian_weight {d : ℕ} (x : Vec d)
    (γ : ℝ) {L r t : ℝ} (hL : 0 < L) (ht : 0 ≤ t) (htr : t < r) :
    let η : ℝ → ℝ := fun s => Real.exp (-γ * s - 2 * euclideanSq x / (L * (r - s)))
    AbsolutelyContinuousOnInterval η 0 t ∧
      ∀ s ∈ Icc (0 : ℝ) t,
        deriv η s = (-γ - 2 * euclideanSq x / (L * (r - s) ^ 2)) * η s := by
  intro η
  have hn (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) t) : L * (r - s) ≠ 0 := by
    rw [uIcc_of_le ht] at hs
    exact ne_of_gt (mul_pos hL (by linarith [hs.2]))
  have hc : ContDiffOn ℝ 1 η (uIcc (0 : ℝ) t) := by
    apply ContDiffOn.exp
    exact (contDiffOn_const.mul contDiffOn_id).sub
      (contDiffOn_const.div
        (contDiffOn_const.mul (contDiffOn_const.sub contDiffOn_id)) hn)
  refine ⟨hc.absolutelyContinuousOnInterval, ?_⟩
  intro s hs
  have hrs : r - s ≠ 0 := ne_of_gt (by linarith [hs.2])
  have hd := (((hasDerivAt_const s (-γ)).mul (hasDerivAt_id s)).sub
    ((hasDerivAt_const s (2 * euclideanSq x)).div
      ((hasDerivAt_const s L).mul ((hasDerivAt_const s r).sub (hasDerivAt_id s)))
      (hn s (by rwa [uIcc_of_le ht])))).exp
  have hd' : HasDerivAt η
      ((-γ - 2 * euclideanSq x / (L * (r - s) ^ 2)) * η s) s := by
    convert hd using 1 <;> dsimp only [η, Pi.mul_apply, Pi.sub_apply, Pi.div_apply, id_eq]
    field_simp [hrs, ne_of_gt hL]
    <;> ring
  exact hd'.deriv

/-- The actual-minus-retained generator evolution obeys the shrinking
Gaussian identity. Both terminal traces are the actual semigroup values;
the negative spatial moment is explicit, ready for the spatial energy estimate. -/
theorem short_time_forward_retained_moving_gaussian_energy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ U : ℝ × FieldPair d → ℂ, Measurable U ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      ∀ t : ℝ≥0, ∀ᵐ ω ∂reducedLaw Q,
      ∀ χ : C(Vec d, ℝ),
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∃ V : ℝ × Vec d → ℂ, Measurable V ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
        ∀ K : Set (Vec d), IsCompact K → ∀ᵐ x ∂volume.restrict K,
          ∀ (γ L r : ℝ), 0 < L → (t : ℝ) < r →
          let w := fun s => f (translate x ω) - fr x +
            ∫ v in (0 : ℝ)..s, U (v, translate x ω) - V (v, x)
          let η := fun s => Real.exp (-γ * s - 2 * euclideanSq x / (L * (r - s)))
          (∫ s in (0 : ℝ)..(t : ℝ),
            η s * (2 * (star (w s) * (U (s, translate x ω) - V (s, x))).re)) +
            (∫ s in (0 : ℝ)..(t : ℝ),
              (-γ - 2 * euclideanSq x / (L * (r - s) ^ 2)) * η s * ‖w s‖ ^ 2) =
              η t * ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2 -
                η 0 * ‖f (translate x ω) - fr x‖ ^ 2 := by
  obtain ⟨U, hU, heU, henergy⟩ :=
    short_time_stationary_retained_generator_weighted_energy hP hfg
  refine ⟨U, hU, heU, ?_⟩
  intro t
  filter_upwards [henergy t] with ω hω
  intro χ Pr hPr fr gr hfrgr
  obtain ⟨V, hV, heV, hVenergy⟩ := hω _ Pr hPr fr gr hfrgr
  refine ⟨V, hV, heV, ?_⟩
  intro K hK
  filter_upwards [hVenergy K hK] with x hx
  intro γ L r hL htr w η
  obtain ⟨hη, hηderiv⟩ := short_time_moving_gaussian_weight x γ hL (NNReal.coe_nonneg t) htr
  have he := hx.2 η hη
  have hd : (∫ s in (0 : ℝ)..(t : ℝ), deriv η s * ‖w s‖ ^ 2) =
      ∫ s in (0 : ℝ)..(t : ℝ),
        (-γ - 2 * euclideanSq x / (L * (r - s) ^ 2)) * η s * ‖w s‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact congrArg (fun z : ℝ => z * ‖w s‖ ^ 2)
      (hηderiv s (by simpa only [uIcc_of_le (NNReal.coe_nonneg t)] using hs))
  change _ = _ - _ - (∫ s in (0 : ℝ)..(t : ℝ), deriv η s * ‖w s‖ ^ 2) at he
  rw [hd] at he
  linarith only [he]

/-- Shrinking the width from `2t` to `t` only decreases the Gaussian.
This domination transfers the checked fixed-weight source energy to the
actual moving weight, without a new source-integrability assumption. -/
private theorem integrable_moving_gaussian_energy_of_fixed {d : ℕ}
    (ν : Measure ℝ) (γ : ℝ) (hγ : 0 ≤ γ) {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (H : ℝ × Vec d → ℝ) (hH : ∀ y, 0 ≤ H y)
    (hi : Integrable (fun y => Real.exp (-((L*t)⁻¹) * euclideanSq y.2) * H y)
      ((ν.restrict (Icc 0 t)).prod volume)) :
    Integrable (fun y => Real.exp (-γ * y.1 - 2 * euclideanSq y.2 / (L * (2*t-y.1))) * H y)
      ((ν.restrict (Icc 0 t)).prod volume) ∧
      (∫ y, Real.exp (-γ * y.1 - 2 * euclideanSq y.2 / (L * (2*t-y.1))) * H y
        ∂(ν.restrict (Icc 0 t)).prod volume) ≤
      ∫ y, Real.exp (-((L*t)⁻¹) * euclideanSq y.2) * H y
        ∂(ν.restrict (Icc 0 t)).prod volume := by
  let m := (ν.restrict (Icc 0 t)).prod (volume : Measure (Vec d))
  let q := fun y : ℝ × Vec d =>
    Real.exp (-γ * y.1 - 2 * euclideanSq y.2 / (L * (2*t-y.1))) /
      Real.exp (-((L*t)⁻¹) * euclideanSq y.2)
  have hqm : Measurable q := by
    dsimp [q]
    unfold euclideanSq dot
    fun_prop
  have heq : (fun y : ℝ × Vec d =>
      Real.exp (-γ * y.1 - 2 * euclideanSq y.2 / (L * (2*t-y.1))) * H y) =
      fun y => q y * (Real.exp (-((L*t)⁻¹) * euclideanSq y.2) * H y) := by
    funext y
    dsimp [q]
    field_simp
  have hm : AEStronglyMeasurable (fun y : ℝ × Vec d =>
      Real.exp (-γ * y.1 - 2 * euclideanSq y.2 / (L * (2*t-y.1))) * H y) m := by
    rw [heq]
    exact hqm.aestronglyMeasurable.mul hi.aestronglyMeasurable
  have hmem : ∀ᵐ y ∂m, y.1 ∈ Icc (0 : ℝ) t :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hb : ∀ᵐ y ∂m,
      Real.exp (-γ * y.1 - 2 * euclideanSq y.2 / (L * (2*t-y.1))) * H y ≤
        Real.exp (-((L*t)⁻¹) * euclideanSq y.2) * H y := by
    filter_upwards [hmem] with y hy
    have hden : 0 < L * (2*t-y.1) := mul_pos hL (by linarith [hy.2])
    have hrat : (L*t)⁻¹ ≤ 2 / (L * (2*t-y.1)) := by
      rw [inv_eq_one_div, div_le_div_iff₀ (mul_pos hL ht) hden]
      nlinarith [mul_nonneg hL.le hy.1]
    have hsq := mul_le_mul_of_nonneg_right hrat (euclideanSq_nonneg_coords y.2)
    apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hH y)
    have hb0 : -2 * euclideanSq y.2 / (L * (2*t-y.1)) ≤
        -((L*t)⁻¹) * euclideanSq y.2 := by
      convert neg_le_neg hsq using 1 <;> ring
    have hn : -γ * y.1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) hy.1
    calc
      _ = -γ * y.1 + (-2 * euclideanSq y.2 / (L * (2*t-y.1))) := by ring
      _ ≤ 0 + (-((L*t)⁻¹) * euclideanSq y.2) := add_le_add hn hb0
      _ = _ := zero_add _
  have hnonneg (y : ℝ × Vec d) :
      0 ≤ Real.exp (-γ * y.1 - 2 * euclideanSq y.2 / (L * (2*t-y.1))) * H y :=
    mul_nonneg (Real.exp_pos _).le (hH y)
  have hmi : Integrable (fun y : ℝ × Vec d =>
      Real.exp (-γ * y.1 - 2 * euclideanSq y.2 / (L * (2*t-y.1))) * H y) m :=
    hi.mono' hm (hb.mono fun y hy => by rw [Real.norm_of_nonneg (hnonneg y)]; exact hy)
  exact ⟨hmi, integral_mono_ae hmi hi hb⟩

/-- The actual retained scalar and flux defects have damped moving-Gaussian
spacetime energy, with the Gaussian tail scale `rho²/t` and constants chosen
before the environment law. Integrability is derived from the wider gradient
energy already used by the retained-source construction. -/
theorem exists_retained_moving_gaussian_forcing_energy (d : ℕ) (D : StructuralData d)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (ν : Measure ℝ) [SFinite ν] (χ : C(Vec d, ℝ)) (γ L t ρ : ℝ),
      0 ≤ γ → 0 < L → 0 < t → 0 ≤ ρ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanNorm x < ρ → χ x = 1) →
    ∀ G : Fin d → ℝ × Vec d → ℂ,
      (∀ j, AEStronglyMeasurable (G j) ((ν.restrict (Icc 0 t)).prod volume)) →
      (∀ j, Integrable (fun y => Real.exp (-((L*t)⁻¹ / 2) * euclideanSq y.2) *
        ‖G j y‖ ^ 2) ((ν.restrict (Icc 0 t)).prod volume)) →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
      let H := fun y : ℝ × Vec d =>
        (∑ j : Fin d,
          ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω y.2 (fun k => G k y) j‖ ^ 2) +
          ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω y.2 (fun k => G k y) i ζ‖ ^ 2
      Integrable (fun y => Real.exp (-γ * y.1 - 2 * euclideanSq y.2 / (L * (2*t-y.1))) * H y)
        ((ν.restrict (Icc 0 t)).prod volume) ∧
      (∫ y, Real.exp (-γ * y.1 - 2 * euclideanSq y.2 / (L * (2*t-y.1))) * H y
        ∂(ν.restrict (Icc 0 t)).prod volume) ≤
      C * Real.exp (-((L*t)⁻¹ / 2) * ρ ^ 2) *
        ∑ j : Fin d, ∫ y : ℝ × Vec d,
          Real.exp (-((L*t)⁻¹ / 2) * euclideanSq y.2) * ‖G j y‖ ^ 2
            ∂(ν.restrict (Icc 0 t)).prod volume := by
  obtain ⟨C, hC, henergy⟩ := exists_retained_spacetime_forcing_energy d D B hB
  refine ⟨C, hC, ?_⟩
  intro Q
  filter_upwards [henergy Q] with ω hω
  intro ν _ χ γ L t ρ hγ hL ht hρ hχ hinterior G hG hGe i ζ hζ H
  have he := hω (ν.restrict (Icc 0 t)) χ ((L*t)⁻¹) ρ
    (inv_pos.mpr (mul_pos hL ht)) hρ hχ hinterior G hG hGe i ζ hζ
  have hfix : Integrable (fun y : ℝ × Vec d =>
      Real.exp (-((L*t)⁻¹) * euclideanSq y.2) * H y)
      ((ν.restrict (Icc 0 t)).prod volume) := by
    simpa only [H, mul_add, Finset.mul_sum] using he.1
  obtain ⟨hi, hb⟩ := integrable_moving_gaussian_energy_of_fixed ν γ hγ hL ht H
    (fun y => by dsimp only [H]; positivity) hfix
  refine ⟨hi, hb.trans ?_⟩
  simpa only [H, mul_add, Finset.mul_sum] using he.2

private theorem endpoint_divergence_projection {d : ℕ} {F : Vec d → Fin d → ℂ}
    {q : Vec d → ℂ}
    (hF : ∀ K : Set (Vec d), IsCompact K →
      ∀ j, MemLp (fun x => F x j) 2 (volume.restrict K))
    (hq : ∀ K : Set (Vec d), IsCompact K → MemLp q 2 (volume.restrict K))
    (hw : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, q x * (φ x : ℂ)) = -(∫ x, ∑ j, F x j * (coordinateDerivative j φ x : ℂ)))
    (L : ℂ →L[ℝ] ℝ) :
    HasWeakDivergence Set.univ (fun x j => L (F x j)) (fun x => L (q x)) := by
  have hloc {v : Vec d → ℂ}
      (hv : ∀ K : Set (Vec d), IsCompact K → MemLp v 2 (volume.restrict K)) :
      LocallyIntegrable (fun x => L (v x)) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact (L.comp_memLp' (hv K hK)).integrable (by norm_num)
  refine ⟨fun j => (hloc (fun K hK => hF K hK j)).locallyIntegrableOn Set.univ,
    (hloc hq).locallyIntegrableOn Set.univ, ?_⟩
  intro φ hφ
  have hi := integrable_spatial_mul_test hq hφ.1.continuous hφ.2.1
  have hj (j : Fin d) : Integrable (fun x => F x j * (coordinateDerivative j φ x : ℂ)) volume := integrable_spatial_mul_test (fun K hK => hF K hK j)
    ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hφ.2.1.fderiv_apply ℝ (unitVector j))
  have hs := integrable_finsetSum Finset.univ (fun j _ => hj j)
  have he := congrArg L (hw φ hφ.1 hφ.2.1)
  rw [map_neg, ← L.integral_comp_comm hi, ← L.integral_comp_comm hs] at he
  have hp (z : ℂ) (c : ℝ) : L (z * (c : ℂ)) = L z * c := by
    rw [mul_comm, ← Complex.real_smul, L.map_smul, smul_eq_mul, mul_comm]
  simp only [map_sum, hp] at he
  simpa only [Measure.restrict_univ, dot, gradient] using (neg_eq_iff_eq_neg.mp he.symm)

private theorem endpoint_physical_generator_divergence {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) f G ∧
      ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence Set.univ
        (fun x j => L ((1 / 2 : ℂ) * ∑ k, (a x j k : ℂ) * G k x))
        (fun x => L (g x - ζ * ∑ j, (a x j i : ℂ) * G j x)) := by
  obtain ⟨G, hG, htest⟩ := hfg
  refine ⟨G, hG, fun L => ?_⟩
  let F : Vec d → Fin d → ℂ := fun x j => (1 / 2 : ℂ) * ∑ k, (a x j k : ℂ) * G k x
  let b : Vec d → ℂ := fun x => ∑ j, (a x j i : ℂ) * G j x
  have hF (j : Fin d) : MemLp (fun x => F x j) 2 volume := by
    apply MemLp.const_mul
    exact memLp_finsetSum _ fun k _ => (ha j k).fun_mul (Lp.memLp (G k))
  have hb : MemLp b 2 volume :=
    memLp_finsetSum _ fun j _ => (ha j i).fun_mul (Lp.memLp (G j))
  apply endpoint_divergence_projection
    (fun K _ j => (hF j).restrict K)
    (fun K _ => ((Lp.memLp g).sub (hb.const_mul ζ)).restrict K)
  intro φ hφ hφc
  have hv : MemLp (fun x => (φ x : ℂ)) 2 volume :=
    Complex.ofRealCLM.comp_memLp' (hφ.continuous.memLp_of_hasCompactSupport hφc)
  have hV (j : Fin d) : MemLp (fun x => (coordinateDerivative j φ x : ℂ)) 2 volume :=
    Complex.ofRealCLM.comp_memLp'
      (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hφc.fderiv_apply ℝ (unitVector j)))
  let v := hv.toLp (fun x => (φ x : ℂ))
  let V (j : Fin d) := (hV j).toLp (fun x => (coordinateDerivative j φ x : ℂ))
  have hvx : (v : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ)) := hv.coeFn_toLp
  have hVx (j : Fin d) : (V j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (coordinateDerivative j φ x : ℂ)) := (hV j).coeFn_toLp
  have hvG : IsPhysicalH1Graph volume (Or.inl rfl) v V := by
    rw [isPhysicalH1Graph_iff_representatives volume (Or.inl rfl)
      v V _ _ hvx hVx]
    constructor
    · intro j
      simpa only [Complex.ofReal_re] using
        hasWeakPartialDerivative_of_contDiff j φ (hφ.of_le (by simp))
    · intro j
      simp only [Complex.ofReal_im]
      have hd : coordinateDerivative j (fun _ : Vec d => (0 : ℝ)) = (fun _ => 0) := by
        funext x
        simp [EinsteinRelation.coordinateDerivative]
      simpa only [hd] using
        hasWeakPartialDerivative_of_contDiff j (fun _ : Vec d => (0 : ℝ)) contDiff_const
  have he := htest v V hvG
  have he' : (∫ x, g x * (φ x : ℂ)) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x *
        (coordinateDerivative j φ x : ℂ)) +
      ζ * (∫ x, b x * (φ x : ℂ)) := by
    convert he using 1
    · exact integral_congr_ae (hvx.mono fun x hx => by dsimp only; rw [hx])
    · congr 1
      · congr 1
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hVx] with x hx
        simp only [hx]
      · congr 1
        exact integral_congr_ae (hvx.mono fun x hx => by dsimp only [b]; rw [hx])
  have hgφ : Integrable (fun x => g x * (φ x : ℂ)) := by
    simpa only [Pi.mul_def] using (Lp.memLp g).integrable_mul hv
  have hbφ : Integrable (fun x => b x * (φ x : ℂ)) := by
    simpa only [Pi.mul_def] using hb.integrable_mul hv
  change (∫ x, (g x - ζ * b x) * (φ x : ℂ)) = -∫ x, ∑ j, F x j * (coordinateDerivative j φ x : ℂ)
  rw [show (fun x => (g x - ζ * b x) * (φ x : ℂ)) =
      (fun x => g x * (φ x : ℂ) - ζ * (b x * (φ x : ℂ))) by funext x; ring]
  have hisub : (∫ x, g x * (φ x : ℂ) - ζ * (b x * (φ x : ℂ))) =
      (∫ x, g x * (φ x : ℂ)) - ∫ x, ζ * (b x * (φ x : ℂ)) := by
    exact integral_sub hgφ (hbφ.const_mul ζ)
  rw [hisub, integral_const_mul, he']
  have hflux : (fun x => ∑ j, F x j * (coordinateDerivative j φ x : ℂ)) =
      (fun x => (1 / 2 : ℂ) * ∑ j, ∑ k,
        (a x j k : ℂ) * G k x * (coordinateDerivative j φ x : ℂ)) := by
    funext x
    simp only [F, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hflux, integral_const_mul]
  ring

/-- The actual stationary generator supplies the spatial equation on one
common event, before the retained cutoff and real projection are chosen.
The two sources are precisely the coefficient defects already estimated above. -/
theorem short_time_stationary_retained_spatial_residual
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ χ : C(Vec d, ℝ), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence Set.univ
        (fun x j => L ((1 / 2 : ℂ) *
          (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * G k (translate x ω)) +
          EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
            (fun k => G k (translate x ω)) j))
        (fun x => L (g (translate x ω) -
          EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
            (fun k => G k (translate x ω)) i ζ -
          ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
            G j (translate x ω)))) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let F : Fin d → FieldPair d → ℂ := fun j ω => (1 / 2 : ℂ) * ∑ k, (ω.1 0 j k : ℂ) * G k ω
  let b : FieldPair d → ℂ := fun ω => ∑ j, (ω.1 0 j i : ℂ) * G j ω
  let q : FieldPair d → ℂ := fun ω => g ω - ζ * b ω
  have hm (j k : Fin d) : Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable
  have hFm (j : Fin d) : Measurable (F j) := measurable_const.mul
    (Finset.measurable_sum _ fun k _ => (hm j k).mul (Lp.stronglyMeasurable _).measurable)
  have hbm : Measurable b := Finset.measurable_sum _ fun j _ =>
    (hm j i).mul (Lp.stronglyMeasurable _).measurable
  have hb : MemLp b 2 (reducedLaw Q) := by
    apply memLp_finsetSum
    intro j _
    exact (Lp.memLp (complexCoefficientMul Q j i (G j))).ae_eq
      (complexCoefficientMul_coe Q j i (G j))
  have hqm : Measurable q := (Lp.stronglyMeasurable g).measurable.sub (measurable_const.mul hbm)
  have hq : MemLp q 2 (reducedLaw Q) := (Lp.memLp g).sub (hb.const_mul ζ)
  have hF j : MemLp (F j) 2 (reducedLaw Q) := (memLp_complex_coefficient_flux Q G j).const_mul _
  have hw := ae_complex_spatial_divergence_all_tests (reducedLaw Q) (reducedLaw_stationary Q)
    F q hFm hqm hF hq (by
      intro v V hV
      have he := hfg.horizontal_flux hG v V hV
      have hg : Integrable (fun ω => g ω * v ω) (reducedLaw Q) :=
        (Lp.memLp g).integrable_mul (Lp.memLp v)
      have hd : Integrable (fun ω => b ω * v ω) (reducedLaw Q) :=
        hb.integrable_mul (Lp.memLp v)
      have heq : (fun ω => (2 * g ω - 2 * ζ *
          (∑ j, (ω.1 0 j i : ℂ) * G j ω)) * v ω) =
          (fun ω => 2 * (g ω * v ω) - (2 * ζ) * (b ω * v ω)) := by
        funext ω
        dsimp only [b]
        ring
      rw [heq, integral_sub (hg.const_mul 2) (hd.const_mul (2 * ζ)),
        integral_const_mul, integral_const_mul] at he
      have hqe : (fun ω => q ω * v ω) =
          (fun ω => g ω * v ω - ζ * (b ω * v ω)) := by
        funext ω
        dsimp only [q]
        ring
      rw [hqe, integral_sub hg (hd.const_mul ζ), integral_const_mul]
      simp only [F, mul_assoc, ← Finset.mul_sum, integral_const_mul]
      linear_combination (1 / 2 : ℂ) * he)
  filter_upwards [hw,
    ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q)
      (reducedLaw_stationary Q) hqm hq,
    ae_all_iff.mpr (fun j => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (hFm j) (hF j))]
      with ω hw hqω hFω
  intro χ L
  have hd := endpoint_divergence_projection (fun K hK j => hFω j K hK) hqω hw L
  have hf (x : Vec d) (j : Fin d) :
      (1 / 2 : ℂ) *
          (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * G k (translate x ω)) +
          EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
            (fun k => G k (translate x ω)) j = F j (translate x ω) := by
    simp only [F, EinsteinFull.C9ShortTimeLocality.retainedFluxDefect,
      Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib, translate_matrix, add_zero]
    ring
  have hs (x : Vec d) :
      g (translate x ω) -
          EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
            (fun k => G k (translate x ω)) i ζ -
          ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
            G j (translate x ω)) = q (translate x ω) := by
    simp only [q, b, EinsteinFull.C9ShortTimeLocality.retainedDriftDefect,
      Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib, translate_matrix, add_zero]
    ring
  simpa only [hf, hs] using hd

/-- The difference of the actual stationary and retained physical generators
has the retained principal coefficient and the already estimated actual-gradient
sources. Neither a weak equation nor a comparison bound is an input. -/
theorem short_time_actual_retained_spatial_residual
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ χ : C(Vec d, ℝ),
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) fr H ∧
        ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence Set.univ
          (fun x j => L ((1 / 2 : ℂ) *
            (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
              (G k (translate x ω) - H k x)) +
            EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => G k (translate x ω)) j))
          (fun x => L ((g (translate x ω) - gr x) -
            EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => G k (translate x ω)) i ζ -
            ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
              (G j (translate x ω) - H j x)))) := by
  filter_upwards [short_time_stationary_retained_spatial_residual Q hfg hG,
    c4_ae_reduced_physical_elliptic Q] with ω hω hA
  intro χ hχ fr gr hfr
  let Λ := Real.exp (2 * Λ₀) * Λ₀
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have ha (j k : Fin d) : MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry _ _ Λ hΛ hA
      (fun j k => ω.1.continuous.matrix_elem j k) j k
  have hc : MemLp (fun x => (χ x : ℂ)) ∞ volume := by
    apply memLp_top_of_bound
      (Complex.continuous_ofReal.comp χ.continuous).aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      change ‖(χ x : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ x).1]
      exact (hχ x).2
  have hr (j k : Fin d) :
      MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ)) ∞ volume := by
    convert (hc.fun_mul (ha j k)).add
      (((memLp_top_const (1 : ℂ) : MemLp (fun _ : Vec d => (1 : ℂ)) ∞ volume).sub hc).mul_const
        ((1 : Mat d) j k : ℂ)) using 1
    funext x
    simp only [ForcedLocality.retainedPair, ContinuousMap.coe_mk,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Pi.add_apply, Pi.sub_apply]
  obtain ⟨H, hH, hdiv⟩ := endpoint_physical_generator_divergence
    (ForcedLocality.retainedPair χ ω).1 i ζ hr hfr
  refine ⟨H, hH, fun L => ?_⟩
  have he := Correctors.hasWeakDivergence_sub (hω χ L) (hdiv L)
  have hf (x : Vec d) (j : Fin d) :
      (1 / 2 : ℂ) * (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
        (G k (translate x ω) - H k x)) +
        EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
          (fun k => G k (translate x ω)) j =
      ((1 / 2 : ℂ) * (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
        G k (translate x ω)) +
        EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
          (fun k => G k (translate x ω)) j) -
        (1 / 2 : ℂ) * (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * H k x) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hs (x : Vec d) :
      (g (translate x ω) - gr x) -
        EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
          (fun k => G k (translate x ω)) i ζ -
        ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
          (G j (translate x ω) - H j x)) =
      (g (translate x ω) -
        EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
          (fun k => G k (translate x ω)) i ζ -
        ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) * G j (translate x ω))) -
      (gr x - ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) * H j x)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  simpa only [hf, hs, map_sub, Pi.sub_def] using he

private theorem endpoint_retained_elliptic {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) (x : Vec d) {Λ : ℝ} (hA : S5Elliptic (ω.1 x) Λ)
    (hχ0 : 0 ≤ χ x) (hχ1 : χ x ≤ 1) :
    S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ := by
  have hform (ξ : Fin d → ℝ) :
      s5Bil ((ForcedLocality.retainedPair χ ω).1 x) ξ ξ =
        χ x * s5Bil (ω.1 x) ξ ξ + (1 - χ x) * ∑ j, ξ j ^ 2 := by
    change (∑ j, ∑ k, ξ j *
      (χ x * ω.1 x j k + (1 - χ x) * (1 : Mat d) j k) * ξ k) = _
    simp only [mul_add, add_mul, Finset.sum_add_distrib, Matrix.one_apply,
      mul_ite, ite_mul, mul_zero, zero_mul, mul_one]
    unfold s5Bil
    simp only [Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring
  refine ⟨hA.one_le, ?_, ?_, ?_⟩
  · intro j k
    change χ x * ω.1 x j k + (1 - χ x) * (1 : Mat d) j k =
      χ x * ω.1 x k j + (1 - χ x) * (1 : Mat d) k j
    rw [hA.symm j k]
    simp only [Matrix.one_apply, eq_comm]
  · intro ξ
    rw [hform]
    have hs : 0 ≤ ∑ j, ξ j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hl := mul_le_mul_of_nonneg_left (hA.lower ξ) hχ0
    have hi := mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hA.one_le) hs
    have he := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hχ1)
    linarith only [hl, he]
  · intro ξ
    rw [hform]
    have hs : 0 ≤ ∑ j, ξ j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hu := mul_le_mul_of_nonneg_left (hA.upper ξ) hχ0
    have hi := mul_le_mul_of_nonneg_right hA.one_le hs
    have he := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hχ1)
    linarith only [hu, he]

/-- Spatial coercivity for the actual stationary-minus-retained generator
pair. All Gaussian admissibility conditions follow from stationary L2 and the
physical graph; the statement has no residual or weighted comparison premise. -/
theorem short_time_actual_retained_gaussian_coercivity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ χ : C(Vec d, ℝ),
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) fr H ∧
        ∀ L r : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
        let u : Vec d → ℂ := fun x => f (translate x ω) - fr x
        let J : Fin d → Vec d → ℂ := fun j x => G j (translate x ω) - H j x
        let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
        let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
        Integrable (fun x => η x ^ 2 * ∑ j, ‖J j x‖ ^ 2) ∧
        Integrable (fun x => W x * ‖u x‖ ^ 2) ∧
        2 * (∫ x, (g (translate x ω) - gr x) *
            (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re +
          (∫ x, W x * ‖u x‖ ^ 2) +
          (Λ⁻¹ / 4) * (∫ x, η x ^ 2 * ∑ j, ‖J j x‖ ^ 2) ≤
        (16 * Λ ^ 3 * ‖ζ‖ ^ 2 + 1) * (∫ x, η x ^ 2 * ‖u x‖ ^ 2) +
        (4 * Λ + 16 / L) * (∫ x, η x ^ 2 * ∑ j,
          ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
            (fun k => G k (translate x ω)) j‖ ^ 2) +
        (∫ x, η x ^ 2 *
          ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
            (fun k => G k (translate x ω)) i ζ‖ ^ 2) := by
  intro Λ
  let : Fact (2 ≤ d) := ⟨hd⟩
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hΛ₀ : 1 ≤ Λ₀ := Q.ellipticity_parameter
  have hexp : 1 ≤ Real.exp (2 * Λ₀) := Real.one_le_exp (by linarith)
  have hΛ1 : 1 ≤ Λ := by dsimp only [Λ]; nlinarith
  have hΛ : 0 < Λ := by linarith
  filter_upwards [short_time_actual_retained_spatial_residual Q hfg hG,
    hG.ae_reduced_spatial Q, c4_ae_reduced_physical_elliptic Q,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q) (reducedLaw_stationary Q) f,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_all_iff.mpr (fun j => ae_stationary_spatial_orbit_gaussian_memLp d hd
      (reducedLaw Q) (reducedLaw_stationary Q) (G j))]
    with ω hres hsp hA hf hg hGrad
  intro χ hχ fr gr hfr
  obtain ⟨H, hH, hdiv⟩ := hres χ hχ fr gr hfr
  have haret (x : Vec d) : S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ :=
    endpoint_retained_elliptic χ ω x (s5Elliptic_of_isElliptic hΛ1 hA x)
      (hχ x).1 (hχ x).2
  have har (j k : Fin d) :
      MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ)) ∞ volume := by
    apply memLp_top_of_bound
      (Complex.continuous_ofReal.comp
        ((ForcedLocality.retainedPair χ ω).1.continuous.matrix_elem j k)).aestronglyMeasurable Λ
    exact ae_of_all _ fun x => by
      change ‖((ForcedLocality.retainedPair χ ω).1 x j k : ℂ)‖ ≤ Λ
      simpa only [Complex.norm_real, Real.norm_eq_abs] using (haret x).entry_abs_le j k
  have hao (j k : Fin d) : MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry _ _ Λ hΛ hA (fun j k => ω.1.continuous.matrix_elem j k) j k
  have had (j k : Fin d) : MemLp
      (fun x => ((ω.1 x j k - (ForcedLocality.retainedPair χ ω).1 x j k : ℝ) : ℂ)) ∞ volume := by
    simpa only [Complex.ofReal_sub, Pi.sub_def] using (hao j k).sub (har j k)
  refine ⟨H, hH, fun L r hL hr => ?_⟩
  intro u J η W
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  let w : Vec d → ℂ := fun x => (Real.exp (-euclideanSq x / (4 * L * r)) : ℂ)
  have hw : MemLp w ∞ volume := by
    have hc : Continuous w := by dsimp only [w, euclideanSq, dot]; fun_prop
    apply memLp_top_of_bound hc.aestronglyMeasurable 1
    refine ae_of_all _ fun x => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    apply neg_nonpos.mpr
    exact euclideanSq_nonneg_coords x
  have hwp (v : Lp ℂ 2 (volume : Measure (Vec d))) :
      MemLp (fun x => w x * v x) 2 volume := hw.fun_mul (Lp.memLp v)
  have hwu : MemLp (fun x => w x * u x) 2 volume := by
    simpa only [u, w, mul_sub, Pi.sub_def] using (hf (4 * L * r) (by positivity)).sub (hwp fr)
  have hwg : MemLp (fun x => w x * (g (translate x ω) - gr x)) 2 volume := by
    simpa only [w, mul_sub, Pi.sub_def] using (hg (4 * L * r) (by positivity)).sub (hwp gr)
  have hwJ (j : Fin d) : MemLp (fun x => w x * J j x) 2 volume := by
    simpa only [J, w, mul_sub, Pi.sub_def] using (hGrad j (4 * L * r) (by positivity)).sub (hwp (H j))
  let R : Fin d → Vec d → ℂ := fun j x =>
    -EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
      (fun k => G k (translate x ω)) j
  let S : Vec d → ℂ := fun x =>
    EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
      (fun k => G k (translate x ω)) i ζ
  have hwR (j : Fin d) : MemLp (fun x => w x * R j x) 2 volume := by
    convert ((memLp_finsetSum Finset.univ (fun k _ =>
      (had j k).fun_mul (r := (2 : ℝ≥0∞)) (hGrad k (4 * L * r) (by positivity)))).const_mul (1 / 2 : ℂ)).neg using 1
    funext x
    simp only [R, w, EinsteinFull.C9ShortTimeLocality.retainedFluxDefect,
      Finset.mul_sum, Pi.neg_apply, mul_neg]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hwS : MemLp (fun x => w x * S x) 2 volume := by
    convert (memLp_finsetSum Finset.univ (fun j _ =>
      (had j i).fun_mul (r := (2 : ℝ≥0∞)) (hGrad j (4 * L * r) (by positivity)))).const_mul ζ using 1
    funext x
    simp only [S, w, EinsteinFull.C9ShortTimeLocality.retainedDriftDefect, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hre j : HasWeakPartialDerivative Set.univ j
      (fun x => (u x).re) (fun x => (J j x).re) := by
    simpa only [u, J, Complex.sub_re] using
      Correctors.hasWeakPartialDerivative_sub (hsp.1 j) (hH.1 j)
  have him j : HasWeakPartialDerivative Set.univ j
      (fun x => (u x).im) (fun x => (J j x).im) := by
    simpa only [u, J, Complex.sub_im] using
      Correctors.hasWeakPartialDerivative_sub (hsp.2.1 j) (hH.2 j)
  have hdre := hdiv Complex.reCLM
  have hdim := hdiv Complex.imCLM
  have he := short_time_scalar_flux_gaussian_energy
    (ForcedLocality.retainedPair χ ω).1 i ζ har (ae_of_all _ haret)
    u (fun x => g (translate x ω) - gr x) S J R hre him
    (by simpa only [J, R, S, sub_neg_eq_add, Complex.reCLM_apply] using hdre)
    (by simpa only [J, R, S, sub_neg_eq_add, Complex.imCLM_apply] using hdim)
    hΛ hL hr hwu hwg hwS hwJ hwR
  simpa only [η, W, R, norm_neg] using he

/-- The scalar moving-Gaussian inequality for the actual difference.  The
physical gradient is eliminated using its nonnegative dissipation, so the
remaining quantities admit the temporal representatives of the actual orbits. -/
theorem short_time_actual_retained_gaussian_scalar_bound
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ χ : C(Vec d, ℝ),
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∀ L r : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
      let u : Vec d → ℂ := fun x => f (translate x ω) - fr x
      let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
      let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
      Integrable (fun x => W x * ‖u x‖ ^ 2) ∧
      2 * (∫ x, (g (translate x ω) - gr x) *
          (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re +
        (∫ x, W x * ‖u x‖ ^ 2) ≤
      (16 * Λ ^ 3 * ‖ζ‖ ^ 2 + 1) * (∫ x, η x ^ 2 * ‖u x‖ ^ 2) +
      (4 * Λ + 16 / L) * (∫ x, η x ^ 2 * ∑ j,
        ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
          (fun k => G k (translate x ω)) j‖ ^ 2) +
      (∫ x, η x ^ 2 *
        ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
          (fun k => G k (translate x ω)) i ζ‖ ^ 2) := by
  intro Λ
  filter_upwards [short_time_actual_retained_gaussian_coercivity hd Q hfg hG] with ω hω
  intro χ hχ fr gr hfr L r hL hr u η W
  obtain ⟨H, hH, he⟩ := hω χ hχ fr gr hfr
  obtain ⟨hJ, hW, hbound⟩ := he L r hL hr
  refine ⟨hW, ?_⟩
  have hΛ : 0 < Λ := by
    dsimp only [Λ]
    exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hnonneg : 0 ≤ (Λ⁻¹ / 4) *
      (∫ x, η x ^ 2 * ∑ j, ‖G j (translate x ω) - H j x‖ ^ 2) := by
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro x
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact (le_add_of_nonneg_right hnonneg).trans hbound

/-- On a force disc the damping constant is chosen before the environment.
It absorbs the solution energy in the actual moving-Gaussian comparison,
leaving only the retained coefficient defects. -/
theorem short_time_actual_retained_damped_gaussian_bound
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (B : ℝ) (hζ : ‖ζ‖ ≤ B) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let γ := 16 * Λ ^ 3 * B ^ 2 + 1
    ∀ᵐ ω ∂reducedLaw Q, ∀ χ : C(Vec d, ℝ),
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∀ L r s : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
      let u : Vec d → ℂ := fun x => f (translate x ω) - fr x
      let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
      let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
      Integrable (fun x => W x * ‖u x‖ ^ 2) ∧
      Real.exp (-γ * s) * (
        2 * (∫ x, (g (translate x ω) - gr x) *
          (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re +
        (∫ x, W x * ‖u x‖ ^ 2) -
        γ * (∫ x, η x ^ 2 * ‖u x‖ ^ 2)) ≤
      Real.exp (-γ * s) * (
        (4 * Λ + 16 / L) * (∫ x, η x ^ 2 * ∑ j,
        ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
          (fun k => G k (translate x ω)) j‖ ^ 2) +
      (∫ x, η x ^ 2 *
        ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
          (fun k => G k (translate x ω)) i ζ‖ ^ 2)) := by
  intro Λ γ
  filter_upwards [short_time_actual_retained_gaussian_scalar_bound hd Q hfg hG] with ω hω
  intro χ hχ fr gr hfr L r s hL hr u η W
  obtain ⟨hW, hb⟩ := hω χ hχ fr gr hfr L r hL hr
  refine ⟨hW, ?_⟩
  have hΛ : 0 < Λ := by
    dsimp only [Λ]
    exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hsq : ‖ζ‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have hcoef : 16 * Λ ^ 3 * ‖ζ‖ ^ 2 + 1 ≤ γ := by
    dsimp only [γ]
    exact add_le_add (mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ (16 : ℝ) * Λ ^ 3 from mul_nonneg (by norm_num) (pow_nonneg hΛ.le _)))
      (le_refl (1 : ℝ))
  have hm : 0 ≤ ∫ x, η x ^ 2 * ‖u x‖ ^ 2 :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hmass := mul_le_mul_of_nonneg_right hcoef hm
  dsimp only at hb
  nlinarith only [hb, hmass]

/-- Measurable joint representatives have locally L2 spatial sections on
one product event. No time-integrability assumption is needed for this
section statement. -/
private theorem endpoint_joint_spatial_local_memLp {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure ℝ) {U : ℝ × FieldPair d → ℂ}
    (hU : Measurable U) (hUs : ∀ s, MemLp (fun ω => U (s, ω)) 2 Q) :
    ∀ᵐ p ∂ν.prod Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => U (p.1, translate x p.2)) 2 (volume.restrict K) := by
  have hshift : Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
      U (q.1.1, translate q.2 q.1.2)) :=
    hU.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  let I (n : ℕ) (p : ℝ × FieldPair d) : ℝ≥0∞ :=
    ∫⁻ x in Metric.closedBall (0 : Vec d) (n : ℝ),
      ENNReal.ofReal (‖U (p.1, translate x p.2)‖ ^ 2)
  have hI (n : ℕ) : Measurable (I n) :=
    (hshift.norm.pow_const 2).ennreal_ofReal.lintegral_prod_right'
  have hfinite (n : ℕ) : ∀ᵐ p ∂ν.prod Q, I n p < ∞ := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt (hI n) measurable_const)).mpr
    exact ae_of_all _ fun s => by
      filter_upwards [ae_complex_function_orbit_memLp_on_all_compacts Q hQ
        (hU.comp (measurable_const.prodMk measurable_id)) (hUs s)] with ω hω
      have hm : Measurable (fun x : Vec d => U (s, translate x ω)) :=
        hU.comp (measurable_const.prodMk
          (Probability.continuous_translate.measurable.comp
            (measurable_id.prodMk measurable_const)))
      have hmem : MemLp (fun x : Vec d => U (s, translate x ω)) 2
          (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))) := by
        simpa only [Function.comp_apply, id_eq] using
          hω _ (isCompact_closedBall (0 : Vec d) (n : ℝ))
      exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).mp
        ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hmem).hasFiniteIntegral
  filter_upwards [ae_all_iff.mpr hfinite] with p hp
  intro K hK
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp hK.isBounded
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hs : K ⊆ Metric.closedBall (0 : Vec d) (n : ℝ) :=
    hR.trans (Metric.closedBall_subset_closedBall hn.le)
  have hm : Measurable (fun x => U (p.1, translate x p.2)) :=
    hshift.comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun x => ‖U (p.1, translate x p.2)‖ ^ 2)
      (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))) :=
    ⟨(hm.norm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).mpr (hp n)⟩
  exact ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hi).mono_measure
    (Measure.restrict_mono hs le_rfl)

/-- Joint measurable fluxes with the actual horizontal weak equation admit
one product event before every compact smooth spatial test. This is the
countable-test step needed to apply spatial coercivity to evolving data. -/
private theorem endpoint_joint_spatial_divergence_all_tests {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure ℝ)
    (F : Fin d → ℝ × FieldPair d → ℂ) (q : ℝ × FieldPair d → ℂ)
    (hF : ∀ j, Measurable (F j)) (hq : Measurable q)
    (hFs : ∀ j s, MemLp (fun ω => F j (s, ω)) 2 Q)
    (hqs : ∀ s, MemLp (fun ω => q (s, ω)) 2 Q)
    (hw : ∀ᵐ s ∂ν, ∀ (v : Lp ℂ 2 Q) (V : Fin d → Lp ℂ 2 Q),
      HasComplexHorizontalGradient Q hQ v V →
      (∫ ω, ∑ j, F j (s, ω) * V j ω ∂Q) = -(∫ ω, q (s, ω) * v ω ∂Q)) :
    ∀ᵐ p ∂ν.prod Q,
      ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, q (p.1, translate x p.2) * (φ x : ℂ) +
        ∑ j, F j (p.1, translate x p.2) * (coordinateDerivative j φ x : ℂ)) = 0 := by
  have hloc : ∀ᵐ p ∂ν.prod Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => q (p.1, translate x p.2)) 2 (volume.restrict K) ∧
      ∀ j, MemLp (fun x => F j (p.1, translate x p.2)) 2 (volume.restrict K) := by
    filter_upwards [endpoint_joint_spatial_local_memLp Q hQ ν hq hqs,
      ae_all_iff.mpr (fun j => endpoint_joint_spatial_local_memLp Q hQ ν (hF j) (hFs j))]
      with p hp hFp
    exact fun K hK => ⟨hp K hK, fun j => hFp j K hK⟩
  apply ae_all_spatial_tests_of_ae_fixed_test (ν.prod Q)
    (fun p x => q (p.1, translate x p.2))
    (fun p j x => F j (p.1, translate x p.2)) hloc
  intro φ hφ hφc
  have hshift {U : ℝ × FieldPair d → ℂ} (hU : Measurable U) :
      Measurable (fun z : (ℝ × FieldPair d) × Vec d => U (z.1.1, translate z.2 z.1.2)) :=
    hU.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hd (j : Fin d) : Measurable (fun x => (coordinateDerivative j φ x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).measurable)
  have hm : Measurable (fun p : ℝ × FieldPair d =>
      ∫ x, q (p.1, translate x p.2) * (φ x : ℂ) +
        ∑ j, F j (p.1, translate x p.2) * (coordinateDerivative j φ x : ℂ)) :=
    (((hshift hq).mul (Complex.continuous_ofReal.measurable.comp
      (hφ.continuous.measurable.comp measurable_snd))).add
        (Finset.measurable_sum _ fun j _ => (hshift (hF j)).mul ((hd j).comp measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm measurable_const)).mpr
  filter_upwards [hw] with s hs
  filter_upwards [ae_complex_spatial_divergence_all_tests Q hQ
    (fun j ω => F j (s, ω)) (fun ω => q (s, ω))
    (fun j => (hF j).comp (measurable_const.prodMk measurable_id))
    (hq.comp (measurable_const.prodMk measurable_id))
    (fun j => hFs j s) (hqs s) hs,
    ae_complex_function_orbit_memLp_on_all_compacts Q hQ
      (hq.comp (measurable_const.prodMk measurable_id)) (hqs s),
    ae_all_iff.mpr (fun j => ae_complex_function_orbit_memLp_on_all_compacts Q hQ
      ((hF j).comp (measurable_const.prodMk measurable_id)) (hFs j s))]
    with ω he hqω hFω
  have hiq := integrable_spatial_mul_test hqω hφ.continuous hφc
  have hiF : Integrable (fun x => ∑ j, F j (s, translate x ω) *
      (coordinateDerivative j φ x : ℂ)) volume :=
    integrable_finsetSum _ fun j _ => integrable_spatial_mul_test (hFω j)
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ (unitVector j))
  simp only [Function.comp_apply, id_eq] at hiq hiF he
  rw [integral_add hiq hiF, he φ hφ hφc, neg_add_cancel]

/-- Every joint representative of the actual graph orbit satisfies the retained
spatial residual on one event in positive time and environment. The event is
chosen before the cutoff and the real projection of the complex equation. -/
theorem short_time_joint_stationary_retained_spatial_residual
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (U : ℝ × FieldPair d → ℂ) (D : Fin d → ℝ × FieldPair d → ℂ)
    (hU : Measurable U) (hD : ∀ j, Measurable (D j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) :
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ))).prod (reducedLaw Q),
      ∀ χ : C(Vec d, ℝ), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence Set.univ
        (fun x j => L ((1 / 2 : ℂ) *
          (∑ k, ((ForcedLocality.retainedPair χ p.2).1 x j k : ℂ) *
            D k (p.1, translate x p.2)) +
          EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ p.2 x
            (fun k => D k (p.1, translate x p.2)) j))
        (fun x => L (U (p.1, translate x p.2) -
          EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ p.2 x
            (fun k => D k (p.1, translate x p.2)) i ζ -
          ζ * (∑ j, ((ForcedLocality.retainedPair χ p.2).1 x j i : ℂ) *
            D j (p.1, translate x p.2)))) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let F : Fin d → ℝ × FieldPair d → ℂ := fun j p =>
    (1 / 2 : ℂ) * ∑ k, (p.2.1 0 j k : ℂ) * D k p
  let b : ℝ × FieldPair d → ℂ := fun p => ∑ j, (p.2.1 0 j i : ℂ) * D j p
  let q : ℝ × FieldPair d → ℂ := fun p => U p - ζ * b p
  have hm (j k : Fin d) : Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable
  have hFm (j : Fin d) : Measurable (F j) := measurable_const.mul
    (Finset.measurable_sum _ fun k _ => ((hm j k).comp measurable_snd).mul (hD k))
  have hbm : Measurable b := Finset.measurable_sum _ fun j _ =>
    ((hm j i).comp measurable_snd).mul (hD j)
  have hqm : Measurable q := hU.sub (measurable_const.mul hbm)
  have hDs (j : Fin d) (s : ℝ) : MemLp (fun ω => D j (s, ω)) 2 (reducedLaw Q) :=
    (Lp.memLp _).ae_eq (heD j s).symm
  have hb (s : ℝ) : MemLp (fun ω => b (s, ω)) 2 (reducedLaw Q) :=
    memLp_finsetSum _ fun j _ =>
      (memLp_reduced_coefficient_complex Q j i).fun_mul (hDs j s)
  have hqs (s : ℝ) : MemLp (fun ω => q (s, ω)) 2 (reducedLaw Q) :=
    ((Lp.memLp _).ae_eq (heU s).symm).sub ((hb s).const_mul ζ)
  have hFs (j : Fin d) (s : ℝ) : MemLp (fun ω => F j (s, ω)) 2 (reducedLaw Q) :=
    (memLp_finsetSum _ fun k _ =>
      (memLp_reduced_coefficient_complex Q j k).fun_mul (hDs k s)).const_mul _
  have hw : ∀ᵐ s ∂ν, ∀ (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V →
      (∫ ω, ∑ j, F j (s, ω) * V j ω ∂reducedLaw Q) =
        -(∫ ω, q (s, ω) * v ω ∂reducedLaw Q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro v V hV
    have he := (hP.map_generator hfg s.toNNReal).horizontal_flux
      (hP.gradientOrbit_spec f hs) v V hV
    have heDall := ae_all_iff.mpr (fun j => heD j s)
    have hleft : (∫ ω, ∑ j, F j (s, ω) * V j ω ∂reducedLaw Q) =
        (1 / 2 : ℂ) * (∫ ω, ∑ j,
          (∑ k, (ω.1 0 j k : ℂ) * (hP.gradientOrbit f s) k ω) * V j ω ∂reducedLaw Q) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [heDall] with ω hω
      simp only [F, hω, mul_assoc, ← Finset.mul_sum]
    have hright : (∫ ω, q (s, ω) * v ω ∂reducedLaw Q) =
        (1 / 2 : ℂ) * (∫ ω, (2 * (P s.toNNReal g) ω - 2 * ζ *
          (∑ j, (ω.1 0 j i : ℂ) * (hP.gradientOrbit f s) j ω)) * v ω ∂reducedLaw Q) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [heDall, heU s] with ω hω hu
      simp only [q, b, hu, hω]
      ring
    rw [hleft, hright, he, mul_neg]
  have htest := endpoint_joint_spatial_divergence_all_tests (reducedLaw Q)
    (reducedLaw_stationary Q) ν F q hFm hqm hFs hqs hw
  filter_upwards [htest,
    endpoint_joint_spatial_local_memLp (reducedLaw Q) (reducedLaw_stationary Q) ν hqm hqs,
    ae_all_iff.mpr (fun j => endpoint_joint_spatial_local_memLp
      (reducedLaw Q) (reducedLaw_stationary Q) ν (hFm j) (hFs j))] with p hp hqp hFp
  intro χ L
  have hd := endpoint_divergence_projection (fun K hK j => hFp j K hK) hqp
    (fun φ hφ hφc => eq_neg_of_add_eq_zero_left (by
      exact (integral_add
        (integrable_spatial_mul_test hqp hφ.continuous hφc)
        (integrable_finsetSum _ fun j _ => integrable_spatial_mul_test (hFp j)
          ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
          (hφc.fderiv_apply ℝ (unitVector j)))).symm.trans (hp φ hφ hφc))) L
  have hf (x : Vec d) (j : Fin d) :
      (1 / 2 : ℂ) *
          (∑ k, ((ForcedLocality.retainedPair χ p.2).1 x j k : ℂ) *
            D k (p.1, translate x p.2)) +
          EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ p.2 x
            (fun k => D k (p.1, translate x p.2)) j = F j (p.1, translate x p.2) := by
    simp only [F, EinsteinFull.C9ShortTimeLocality.retainedFluxDefect,
      Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib, translate_matrix, add_zero]
    ring
  have hs (x : Vec d) :
      U (p.1, translate x p.2) -
          EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ p.2 x
            (fun k => D k (p.1, translate x p.2)) i ζ -
          ζ * (∑ j, ((ForcedLocality.retainedPair χ p.2).1 x j i : ℂ) *
            D j (p.1, translate x p.2)) = q (p.1, translate x p.2) := by
    simp only [q, b, EinsteinFull.C9ShortTimeLocality.retainedDriftDefect,
      Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib, translate_matrix, add_zero]
    ring
  simpa only [hf, hs] using hd

/-- The same actual joint orbit and gradient representatives have spatial weak
gradients on one positive-time product event, before all real projections. -/
theorem short_time_joint_stationary_spatial_gradient
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (U : ℝ × FieldPair d → ℂ) (D : Fin d → ℝ × FieldPair d → ℂ)
    (hU : Measurable U) (hD : ∀ j, Measurable (D j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) :
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ))).prod (reducedLaw Q),
      ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakGradient Set.univ (fun x => L (U (p.1, translate x p.2)))
        (fun x j => L (D j (p.1, translate x p.2))) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hUs (s : ℝ) : MemLp (fun ω => U (s, ω)) 2 (reducedLaw Q) :=
    (Lp.memLp _).ae_eq (heU s).symm
  have hDs (j : Fin d) (s : ℝ) : MemLp (fun ω => D j (s, ω)) 2 (reducedLaw Q) :=
    (Lp.memLp _).ae_eq (heD j s).symm
  have hj (j : Fin d) : ∀ᵐ p ∂ν.prod (reducedLaw Q), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakPartialDerivative Set.univ j (fun x => L (U (p.1, translate x p.2)))
        (fun x => L (D j (p.1, translate x p.2))) := by
    let F : Fin d → ℝ × FieldPair d → ℂ := fun k p => if k = j then U p else 0
    have hFm (k : Fin d) : Measurable (F k) := by
      by_cases hk : k = j <;> simp only [F, hk, ite_true, ite_false]
      · exact hU
      · exact measurable_const
    have hFs (k : Fin d) (s : ℝ) : MemLp (fun ω => F k (s, ω)) 2 (reducedLaw Q) := by
      by_cases hk : k = j <;> simp only [F, hk, ite_true, ite_false]
      · exact hUs s
      · exact MemLp.zero
    have hw : ∀ᵐ s ∂ν, ∀ (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V →
        (∫ ω, ∑ k, F k (s, ω) * V k ω ∂reducedLaw Q) =
          -(∫ ω, D j (s, ω) * v ω ∂reducedLaw Q) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      intro v V hV
      have he := (complexHorizontalDerivatives_integration_by_parts
        (hP.gradientOrbit_spec f hs j) (hV j)).2.2
      have hl : (∫ ω, ∑ k, F k (s, ω) * V k ω ∂reducedLaw Q) =
          ∫ ω, (P s.toNNReal f) ω * V j ω ∂reducedLaw Q := by
        apply integral_congr_ae
        filter_upwards [heU s] with ω hω
        simp [F, hω]
      have hr : (∫ ω, D j (s, ω) * v ω ∂reducedLaw Q) =
          ∫ ω, (hP.gradientOrbit f s) j ω * v ω ∂reducedLaw Q :=
        integral_congr_ae ((heD j s).mono fun ω hω => congrArg (· * v ω) hω)
      rw [hl, hr]
      exact neg_eq_iff_eq_neg.mp he.symm
    have ht := endpoint_joint_spatial_divergence_all_tests (reducedLaw Q)
      (reducedLaw_stationary Q) ν F (D j) hFm (hD j) hFs (hDs j) hw
    filter_upwards [ht,
      endpoint_joint_spatial_local_memLp (reducedLaw Q) (reducedLaw_stationary Q) ν hU hUs,
      endpoint_joint_spatial_local_memLp (reducedLaw Q) (reducedLaw_stationary Q) ν (hD j) (hDs j)]
      with p hp hUp hDp
    intro L
    have hFp (K : Set (Vec d)) (hK : IsCompact K) (k : Fin d) :
        MemLp (fun x => F k (p.1, translate x p.2)) 2 (volume.restrict K) := by
      by_cases hk : k = j <;> simp only [F, hk, ite_true, ite_false]
      · exact hUp K hK
      · exact MemLp.zero
    have hd := endpoint_divergence_projection hFp hDp
      (fun φ hφ hφc => eq_neg_of_add_eq_zero_left (by
        exact (integral_add
          (integrable_spatial_mul_test hDp hφ.continuous hφc)
          (integrable_finsetSum _ fun k _ => integrable_spatial_mul_test (fun K hK => hFp K hK k)
            ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
            (hφc.fderiv_apply ℝ (unitVector k)))).symm.trans (hp φ hφ hφc))) L
    refine ⟨?_, hd.2.1, ?_⟩
    · simpa only [F, ite_eq_left rfl] using hd.1 j
    · intro φ hφ
      simpa [F, dot, gradient, apply_ite] using hd.2.2 φ hφ
  filter_upwards [ae_all_iff.mpr hj] with p hp
  exact fun L j => hp j L

/-- Joint L2 representatives have Gaussian-admissible spatial slices on one
product event before every positive Gaussian width. -/
private theorem endpoint_joint_spatial_gaussian_memLp {d : ℕ} (hd : 2 ≤ d)
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure ℝ) {U : ℝ × FieldPair d → ℂ}
    (hU : Measurable U) (hUs : ∀ s, MemLp (fun ω => U (s, ω)) 2 Q) :
    ∀ᵐ p ∂ν.prod Q, ∀ r : ℝ, 0 < r →
      MemLp (fun x : Vec d => (Real.exp (-euclideanSq x / r) : ℂ) *
        U (p.1, translate x p.2)) 2 volume := by
  have hweight (r : ℝ) : Measurable (fun x : Vec d =>
      (Real.exp (-euclideanSq x / r) : ℂ)) := by
    have hs : Continuous (euclideanSq : Vec d → ℝ) := by
      unfold euclideanSq dot
      fun_prop
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (hs.neg.div_const r))).measurable
  have hshift : Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
      U (q.1.1, translate q.2 q.1.2)) :=
    hU.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  let I (n : ℕ) (p : ℝ × FieldPair d) : ℝ≥0∞ := ∫⁻ x,
    ENNReal.ofReal (‖(Real.exp (-euclideanSq x / ((n : ℝ) + 1)) : ℂ) *
      U (p.1, translate x p.2)‖ ^ 2)
  have hI (n : ℕ) : Measurable (I n) :=
    ((((hweight ((n : ℝ) + 1)).comp measurable_snd).mul hshift).norm.pow_const 2).ennreal_ofReal.lintegral_prod_right'
  have hn (n : ℕ) : ∀ᵐ p ∂ν.prod Q, I n p < ∞ := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt (hI n) measurable_const)).mpr
    exact ae_of_all _ fun s => by
      let v := (hUs s).toLp (fun ω => U (s, ω))
      have hm : Measurable (fun ω => U (s, ω)) :=
        hU.comp (measurable_const.prodMk measurable_id)
      filter_upwards [ae_stationary_spatial_orbit_gaussian_memLp d hd Q hQ v,
        ae_spatial_complex_orbit_congr Q hQ (Lp.stronglyMeasurable v).measurable hm
          (hUs s).coeFn_toLp] with ω hg he
      have hmsp : Measurable (fun x : Vec d =>
          (Real.exp (-euclideanSq x / ((n : ℝ) + 1)) : ℂ) * U (s, translate x ω)) :=
        (hweight _).mul (hm.comp (Probability.continuous_translate.measurable.comp
          (measurable_id.prodMk measurable_const)))
      have hmem := (hg ((n : ℝ) + 1) (by positivity)).ae_eq
        (he.mono fun x hx => congrArg ((Real.exp (-euclideanSq x / ((n : ℝ) + 1)) : ℂ) * ·) hx)
      exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).mp
        ((memLp_two_iff_integrable_sq_norm hmsp.aestronglyMeasurable).mp hmem).hasFiniteIntegral
  filter_upwards [ae_all_iff.mpr hn] with p hp
  have hm (r : ℝ) : Measurable (fun x : Vec d =>
      (Real.exp (-euclideanSq x / r) : ℂ) * U (p.1, translate x p.2)) :=
    (hweight r).mul (hshift.comp (measurable_const.prodMk measurable_id))
  have hmem (n : ℕ) : MemLp (fun x : Vec d =>
      (Real.exp (-euclideanSq x / ((n : ℝ) + 1)) : ℂ) * U (p.1, translate x p.2)) 2 volume :=
    (memLp_two_iff_integrable_sq_norm (hm _).aestronglyMeasurable).mpr
      ⟨((hm _).norm.pow_const 2).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).mpr (hp n)⟩
  intro r hr
  obtain ⟨n, hn⟩ := exists_nat_gt r
  apply (hmem n).mono (hm r).aestronglyMeasurable
  refine ae_of_all _ fun x => ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hh : euclideanSq x / ((n : ℝ) + 1) ≤ euclideanSq x / r :=
    div_le_div_of_nonneg_left (euclideanSq_nonneg_coords x) hr (by linarith)
  simpa only [neg_div] using neg_le_neg hh

/-- Subtraction of the actual retained physical graph on the common positive-time
product event; the retained datum is selected after that event. -/
theorem short_time_joint_actual_retained_spatial_residual
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    (U : ℝ × FieldPair d → ℂ) (D : Fin d → ℝ × FieldPair d → ℂ)
    (hU : Measurable U) (hD : ∀ j, Measurable (D j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) :
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ))).prod (reducedLaw Q), ∀ χ : C(Vec d, ℝ),
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ p.2).1 i ζ fr gr →
      ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) fr H ∧
        ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence Set.univ
          (fun x j => L ((1 / 2 : ℂ) *
            (∑ k, ((ForcedLocality.retainedPair χ p.2).1 x j k : ℂ) *
              (D k (p.1, translate x p.2) - H k x)) +
            EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ p.2 x
              (fun k => D k (p.1, translate x p.2)) j))
          (fun x => L ((U (p.1, translate x p.2) - gr x) -
            EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ p.2 x
              (fun k => D k (p.1, translate x p.2)) i ζ -
            ζ * (∑ j, ((ForcedLocality.retainedPair χ p.2).1 x j i : ℂ) *
              (D j (p.1, translate x p.2) - H j x)))) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  filter_upwards [short_time_joint_stationary_retained_spatial_residual Q hP hfg U D hU hD heU heD,
    Measure.quasiMeasurePreserving_snd.ae (c4_ae_reduced_physical_elliptic Q)] with p hω hA
  intro χ hχ fr gr hfr
  let Λ := Real.exp (2 * Λ₀) * Λ₀
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have ha (j k : Fin d) : MemLp (fun x => (p.2.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry _ _ Λ hΛ hA
      (fun j k => p.2.1.continuous.matrix_elem j k) j k
  have hc : MemLp (fun x => (χ x : ℂ)) ∞ volume := by
    apply memLp_top_of_bound
      (Complex.continuous_ofReal.comp χ.continuous).aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      change ‖(χ x : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ x).1]
      exact (hχ x).2
  have hr (j k : Fin d) :
      MemLp (fun x => ((ForcedLocality.retainedPair χ p.2).1 x j k : ℂ)) ∞ volume := by
    convert (hc.fun_mul (ha j k)).add
      (((memLp_top_const (1 : ℂ) : MemLp (fun _ : Vec d => (1 : ℂ)) ∞ volume).sub hc).mul_const
        ((1 : Mat d) j k : ℂ)) using 1
    funext x
    simp only [ForcedLocality.retainedPair, ContinuousMap.coe_mk,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Pi.add_apply, Pi.sub_apply]
  obtain ⟨H, hH, hdiv⟩ := endpoint_physical_generator_divergence
    (ForcedLocality.retainedPair χ p.2).1 i ζ hr hfr
  refine ⟨H, hH, fun L => ?_⟩
  have he := Correctors.hasWeakDivergence_sub (hω χ L) (hdiv L)
  have hf (x : Vec d) (j : Fin d) :
      (1 / 2 : ℂ) * (∑ k, ((ForcedLocality.retainedPair χ p.2).1 x j k : ℂ) *
        (D k (p.1, translate x p.2) - H k x)) +
        EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ p.2 x
          (fun k => D k (p.1, translate x p.2)) j =
      ((1 / 2 : ℂ) * (∑ k, ((ForcedLocality.retainedPair χ p.2).1 x j k : ℂ) *
        D k (p.1, translate x p.2)) +
        EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ p.2 x
          (fun k => D k (p.1, translate x p.2)) j) -
        (1 / 2 : ℂ) * (∑ k, ((ForcedLocality.retainedPair χ p.2).1 x j k : ℂ) * H k x) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hs (x : Vec d) :
      (U (p.1, translate x p.2) - gr x) -
        EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ p.2 x
          (fun k => D k (p.1, translate x p.2)) i ζ -
        ζ * (∑ j, ((ForcedLocality.retainedPair χ p.2).1 x j i : ℂ) *
          (D j (p.1, translate x p.2) - H j x)) =
      (U (p.1, translate x p.2) -
        EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ p.2 x
          (fun k => D k (p.1, translate x p.2)) i ζ -
        ζ * (∑ j, ((ForcedLocality.retainedPair χ p.2).1 x j i : ℂ) * D j (p.1, translate x p.2))) -
      (gr x - ζ * (∑ j, ((ForcedLocality.retainedPair χ p.2).1 x j i : ℂ) * H j x)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  simpa only [hf, hs, map_sub, Pi.sub_def] using he

/-- Actual coercivity on one positive-time product event with the temporal
joint representatives retained literally. -/
theorem short_time_joint_actual_retained_gaussian_coercivity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    (F U : ℝ × FieldPair d → ℂ) (D : Fin d → ℝ × FieldPair d → ℂ)
    (hF : Measurable F) (hU : Measurable U) (hD : ∀ j, Measurable (D j))
    (heF : ∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ))).prod (reducedLaw Q), ∀ χ : C(Vec d, ℝ),
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ p.2).1 i ζ fr gr →
      ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) fr H ∧
        ∀ L r : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
        let u : Vec d → ℂ := fun x => F (p.1, translate x p.2) - fr x
        let J : Fin d → Vec d → ℂ := fun j x => D j (p.1, translate x p.2) - H j x
        let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
        let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
        Integrable (fun x => η x ^ 2 * ∑ j, ‖J j x‖ ^ 2) ∧
        Integrable (fun x => W x * ‖u x‖ ^ 2) ∧
        2 * (∫ x, (U (p.1, translate x p.2) - gr x) *
            (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re +
          (∫ x, W x * ‖u x‖ ^ 2) +
          (Λ⁻¹ / 4) * (∫ x, η x ^ 2 * ∑ j, ‖J j x‖ ^ 2) ≤
        (16 * Λ ^ 3 * ‖ζ‖ ^ 2 + 1) * (∫ x, η x ^ 2 * ‖u x‖ ^ 2) +
        (4 * Λ + 16 / L) * (∫ x, η x ^ 2 * ∑ j,
          ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ p.2 x
            (fun k => D k (p.1, translate x p.2)) j‖ ^ 2) +
        (∫ x, η x ^ 2 *
          ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ p.2 x
            (fun k => D k (p.1, translate x p.2)) i ζ‖ ^ 2) := by
  intro Λ
  let : Fact (2 ≤ d) := ⟨hd⟩
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hΛ₀ : 1 ≤ Λ₀ := Q.ellipticity_parameter
  have hexp : 1 ≤ Real.exp (2 * Λ₀) := Real.one_le_exp (by linarith)
  have hΛ1 : 1 ≤ Λ := by dsimp only [Λ]; nlinarith
  have hΛ : 0 < Λ := by linarith
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hFs (s : ℝ) : MemLp (fun ω => F (s, ω)) 2 (reducedLaw Q) :=
    (Lp.memLp _).ae_eq (heF s).symm
  have hUs (s : ℝ) : MemLp (fun ω => U (s, ω)) 2 (reducedLaw Q) :=
    (Lp.memLp _).ae_eq (heU s).symm
  have hDs (j : Fin d) (s : ℝ) : MemLp (fun ω => D j (s, ω)) 2 (reducedLaw Q) :=
    (Lp.memLp _).ae_eq (heD j s).symm
  filter_upwards [short_time_joint_actual_retained_spatial_residual Q hP hfg U D hU hD heU heD,
    short_time_joint_stationary_spatial_gradient Q hP f F D hF hD heF heD,
    Measure.quasiMeasurePreserving_snd.ae (c4_ae_reduced_physical_elliptic Q),
    endpoint_joint_spatial_gaussian_memLp hd (reducedLaw Q) (reducedLaw_stationary Q) ν hF hFs,
    endpoint_joint_spatial_gaussian_memLp hd (reducedLaw Q) (reducedLaw_stationary Q) ν hU hUs,
    ae_all_iff.mpr (fun j => endpoint_joint_spatial_gaussian_memLp hd
      (reducedLaw Q) (reducedLaw_stationary Q) ν (hD j) (hDs j))]
    with p hres hsp hA hf hg hGrad
  intro χ hχ fr gr hfr
  obtain ⟨H, hH, hdiv⟩ := hres χ hχ fr gr hfr
  have haret (x : Vec d) : S5Elliptic ((ForcedLocality.retainedPair χ p.2).1 x) Λ :=
    endpoint_retained_elliptic χ p.2 x (s5Elliptic_of_isElliptic hΛ1 hA x)
      (hχ x).1 (hχ x).2
  have har (j k : Fin d) :
      MemLp (fun x => ((ForcedLocality.retainedPair χ p.2).1 x j k : ℂ)) ∞ volume := by
    apply memLp_top_of_bound
      (Complex.continuous_ofReal.comp
        ((ForcedLocality.retainedPair χ p.2).1.continuous.matrix_elem j k)).aestronglyMeasurable Λ
    exact ae_of_all _ fun x => by
      change ‖((ForcedLocality.retainedPair χ p.2).1 x j k : ℂ)‖ ≤ Λ
      simpa only [Complex.norm_real, Real.norm_eq_abs] using (haret x).entry_abs_le j k
  have hao (j k : Fin d) : MemLp (fun x => (p.2.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry _ _ Λ hΛ hA (fun j k => p.2.1.continuous.matrix_elem j k) j k
  have had (j k : Fin d) : MemLp
      (fun x => ((p.2.1 x j k - (ForcedLocality.retainedPair χ p.2).1 x j k : ℝ) : ℂ)) ∞ volume := by
    simpa only [Complex.ofReal_sub, Pi.sub_def] using (hao j k).sub (har j k)
  refine ⟨H, hH, fun L r hL hr => ?_⟩
  intro u J η W
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  let w : Vec d → ℂ := fun x => (Real.exp (-euclideanSq x / (4 * L * r)) : ℂ)
  have hw : MemLp w ∞ volume := by
    have hc : Continuous w := by dsimp only [w, euclideanSq, dot]; fun_prop
    apply memLp_top_of_bound hc.aestronglyMeasurable 1
    refine ae_of_all _ fun x => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    apply neg_nonpos.mpr
    exact euclideanSq_nonneg_coords x
  have hwp (v : Lp ℂ 2 (volume : Measure (Vec d))) :
      MemLp (fun x => w x * v x) 2 volume := hw.fun_mul (Lp.memLp v)
  have hwu : MemLp (fun x => w x * u x) 2 volume := by
    simpa only [u, w, mul_sub, Pi.sub_def] using (hf (4 * L * r) (by positivity)).sub (hwp fr)
  have hwg : MemLp (fun x => w x * (U (p.1, translate x p.2) - gr x)) 2 volume := by
    simpa only [w, mul_sub, Pi.sub_def] using (hg (4 * L * r) (by positivity)).sub (hwp gr)
  have hwJ (j : Fin d) : MemLp (fun x => w x * J j x) 2 volume := by
    simpa only [J, w, mul_sub, Pi.sub_def] using (hGrad j (4 * L * r) (by positivity)).sub (hwp (H j))
  let R : Fin d → Vec d → ℂ := fun j x =>
    -EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ p.2 x
      (fun k => D k (p.1, translate x p.2)) j
  let S : Vec d → ℂ := fun x =>
    EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ p.2 x
      (fun k => D k (p.1, translate x p.2)) i ζ
  have hwR (j : Fin d) : MemLp (fun x => w x * R j x) 2 volume := by
    convert ((memLp_finsetSum Finset.univ (fun k _ =>
      (had j k).fun_mul (r := (2 : ℝ≥0∞)) (hGrad k (4 * L * r) (by positivity)))).const_mul (1 / 2 : ℂ)).neg using 1
    funext x
    simp only [R, w, EinsteinFull.C9ShortTimeLocality.retainedFluxDefect,
      Finset.mul_sum, Pi.neg_apply, mul_neg]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hwS : MemLp (fun x => w x * S x) 2 volume := by
    convert (memLp_finsetSum Finset.univ (fun j _ =>
      (had j i).fun_mul (r := (2 : ℝ≥0∞)) (hGrad j (4 * L * r) (by positivity)))).const_mul ζ using 1
    funext x
    simp only [S, w, EinsteinFull.C9ShortTimeLocality.retainedDriftDefect, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hre j : HasWeakPartialDerivative Set.univ j
      (fun x => (u x).re) (fun x => (J j x).re) := by
    simpa only [u, J, Complex.sub_re, Complex.reCLM_apply] using
      Correctors.hasWeakPartialDerivative_sub (hsp Complex.reCLM j) (hH.1 j)
  have him j : HasWeakPartialDerivative Set.univ j
      (fun x => (u x).im) (fun x => (J j x).im) := by
    simpa only [u, J, Complex.sub_im, Complex.imCLM_apply] using
      Correctors.hasWeakPartialDerivative_sub (hsp Complex.imCLM j) (hH.2 j)
  have hdre := hdiv Complex.reCLM
  have hdim := hdiv Complex.imCLM
  have he := short_time_scalar_flux_gaussian_energy
    (ForcedLocality.retainedPair χ p.2).1 i ζ har (ae_of_all _ haret)
    u (fun x => U (p.1, translate x p.2) - gr x) S J R hre him
    (by simpa only [J, R, S, sub_neg_eq_add, Complex.reCLM_apply] using hdre)
    (by simpa only [J, R, S, sub_neg_eq_add, Complex.imCLM_apply] using hdim)
    hΛ hL hr hwu hwg hwS hwJ hwR
  simpa only [η, W, R, norm_neg] using he

/-- Force-disc damping for the actual joint orbits, on one environment event
before almost every positive time and every retained physical graph datum. -/
theorem short_time_joint_actual_retained_damped_gaussian_bound
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    (F U : ℝ × FieldPair d → ℂ) (D : Fin d → ℝ × FieldPair d → ℂ)
    (hF : Measurable F) (hU : Measurable U) (hD : ∀ j, Measurable (D j))
    (heF : ∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j)
    (B : ℝ) (hζ : ‖ζ‖ ≤ B) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let γ := 16 * Λ ^ 3 * B ^ 2 + 1
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ τ ∂volume.restrict (Ioi (0 : ℝ)), ∀ χ : C(Vec d, ℝ),
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∀ L r s : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
      let u : Vec d → ℂ := fun x => F (τ, translate x ω) - fr x
      let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
      let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
      Integrable (fun x => W x * ‖u x‖ ^ 2) ∧
      Real.exp (-γ * s) * (
        2 * (∫ x, (U (τ, translate x ω) - gr x) *
          (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re +
        (∫ x, W x * ‖u x‖ ^ 2) -
        γ * (∫ x, η x ^ 2 * ‖u x‖ ^ 2)) ≤
      Real.exp (-γ * s) * (
        (4 * Λ + 16 / L) * (∫ x, η x ^ 2 * ∑ j,
        ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
          (fun k => D k (τ, translate x ω)) j‖ ^ 2) +
      (∫ x, η x ^ 2 *
        ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
          (fun k => D k (τ, translate x ω)) i ζ‖ ^ 2)) := by
  intro Λ γ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hj := short_time_joint_actual_retained_gaussian_coercivity hd Q hP hfg
    F U D hF hU hD heF heU heD
  have hj' := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hj)
  filter_upwards [hj'] with ω hω
  filter_upwards [hω] with τ hp
  let p : ℝ × FieldPair d := (τ, ω)
  intro χ hχ fr gr hfr L r s hL hr u η W
  obtain ⟨H, hH, he⟩ := hp χ hχ fr gr hfr
  obtain ⟨hJ, hW, hb⟩ := he L r hL hr
  refine ⟨hW, ?_⟩
  have hΛ : 0 < Λ := by
    dsimp only [Λ]
    exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hnonneg : 0 ≤ (Λ⁻¹ / 4) *
      (∫ x, η x ^ 2 * ∑ j, ‖D j (p.1, translate x p.2) - H j x‖ ^ 2) := by
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro x
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hsq : ‖ζ‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have hcoef : 16 * Λ ^ 3 * ‖ζ‖ ^ 2 + 1 ≤ γ := by
    dsimp only [γ]
    exact add_le_add (mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ (16 : ℝ) * Λ ^ 3 from mul_nonneg (by norm_num) (pow_nonneg hΛ.le _)))
      (le_refl (1 : ℝ))
  have hm : 0 ≤ ∫ x, η x ^ 2 * ‖u x‖ ^ 2 :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hmass := mul_le_mul_of_nonneg_right hcoef hm
  dsimp only [Prod.swap, p, u, η, W, Λ] at hb hmass hnonneg ⊢
  nlinarith only [hb, hmass, hnonneg]

/-- The square norm of a measurable joint representative inherits the actual
orbit's time-integrated L2 norm. -/
private theorem endpoint_joint_sq_integrable {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {ν : Measure T} {u : T → Lp ℂ 2 μ}
    (hu : Integrable (fun t => ‖u t‖ ^ 2) ν)
    {U : T × Ω → ℂ} (hU : Measurable U)
    (heq : ∀ t, (fun ω => U (t, ω)) =ᵐ[μ] u t) :
    Integrable (fun p => ‖U p‖ ^ 2) (ν.prod μ) := by
  apply (integrable_prod_iff (hU.norm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun t => ((Lp.memLp (u t)).norm.integrable_sq).congr
    ((heq t).symm.mono fun ω h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)), ?_⟩
  apply hu.congr
  filter_upwards with t
  have hn : ‖u t‖ ^ 2 = ∫ ω, ‖(u t) ω‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [hn]
  apply integral_congr_ae
  filter_upwards [heq t] with ω hω
  simp only [hω, Real.norm_eq_abs]
  exact (abs_of_nonneg (sq_nonneg ‖(u t) ω‖)).symm

/-- The moving Gaussian is dominated by the fixed wider Gaussian throughout
the short-time interval. -/
private theorem endpoint_joint_moving_gaussian_memLp {d : ℕ} {T L : ℝ}
    (hT : T ≤ 1) (hL : 0 < L) {u : ℝ × Vec d → ℂ} (hu : Measurable u)
    (h2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * u p) 2
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume)) :
    MemLp (fun p => (Real.exp (-euclideanSq p.2 / (L * (2 - p.1))) : ℂ) * u p) 2
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := by
  apply h2.of_le (by
    apply Measurable.aestronglyMeasurable
    exact (by dsimp only [euclideanSq, dot]; fun_prop :
      Measurable (fun p : ℝ × Vec d =>
        (Real.exp (-euclideanSq p.2 / (L * (2 - p.1))) : ℂ))).mul hu)
  have htime : ∀ᵐ p : ℝ × Vec d ∂((volume.restrict (Icc (0 : ℝ) T)).prod volume),
      p.1 ∈ Icc (0 : ℝ) T := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact ae_of_all _ fun _ => hs
  filter_upwards [htime] with p hp
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  rw [neg_div, neg_div]
  apply neg_le_neg
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * L)
    (mul_pos hL (by linarith [hp.2] : 0 < 2 - p.1))).mpr
  have hq := euclideanSq_nonneg_coords p.2
  nlinarith [mul_nonneg hq (mul_nonneg hL.le hp.1)]

/-- Integrating the actual retained spatial residual against the damped
moving-Gaussian temporal identity. Finiteness of the source is derived from the
actual continuous generator-domain gradient orbit, without a comparison premise. -/
theorem short_time_actual_retained_integrated_comparison
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (B : ℝ) (hζ : ‖ζ‖ ≤ B) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let γ := 16 * Λ ^ 3 * B ^ 2 + 1
    ∃ D : Fin d → ℝ × FieldPair d → ℂ, (∀ j, Measurable (D j)) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
      ∀ χ : C(Vec d, ℝ), (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∀ L : ℝ, 64 * Λ ^ 3 ≤ L →
      let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
      Integrable (fun s => Real.exp (-γ * s) *
          ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) i ζ‖ ^ 2)))
        (volume.restrict (Icc (0 : ℝ) (t : ℝ))) ∧
      Real.exp (-γ * (t : ℝ)) *
        (∫ x, η (t, x) ^ 2 * ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2) ≤
      (∫ x, η (0, x) ^ 2 * ‖f (translate x ω) - fr x‖ ^ 2) +
        ∫ s in Icc (0 : ℝ) (t : ℝ), Real.exp (-γ * s) *
          ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) i ζ‖ ^ 2)) := by
  intro Λ γ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨F, U, hF, hU, heF, heU, htime⟩ :=
    short_time_stationary_physical_damped_moving_gaussian_energy hd hP hfg
  obtain ⟨D, hD, heD⟩ := hP.exists_joint_gradient_representative f
  refine ⟨D, hD, heD, ?_⟩
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  have hsp := short_time_joint_actual_retained_damped_gaussian_bound hd Q hP hfg
    F U D hF hU hD heF heU heD B hζ
  intro t ht
  have joint (v : Lp ℂ 2 (reducedLaw Q)) (V : ℝ × FieldPair d → ℂ)
      (hV : Measurable V) (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal v) :=
    endpoint_joint_sq_integrable (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
      ((((hP.2.2.1 v).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hV heV
  have hFG := ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg F hF (joint f F hF heF)
  have hUG := ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg U hU (joint g U hU heU)
  obtain ⟨G, hGc, hG⟩ := hP.exists_continuous_gradient_orbit hfg
  have hDi (j : Fin d) : Integrable (fun p => ‖D j p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod (reducedLaw Q)) := by
    apply endpoint_joint_sq_integrable (u := fun s => (hP.gradientOrbit f s) j) _ (hD j) (heD j)
    have hj : Continuous (fun s : ℝ => G s j) := by fun_prop
    have hi := ((hj.norm.pow 2).continuousOn.integrableOn_compact
      (μ := volume) (K := Icc (0 : ℝ) (t : ℝ)) isCompact_Icc)
    change Integrable (fun s : ℝ => ‖G s j‖ ^ 2)
      (volume.restrict (Icc (0 : ℝ) (t : ℝ))) at hi
    rw [← restrict_Ioc_eq_restrict_Icc] at hi ⊢
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [(hP.gradientOrbit_spec f hs.1).unique (hG s)]
  have hDG : ∀ᵐ ω ∂reducedLaw Q, ∀ j : Fin d, ∀ r : ℝ, 0 < r →
      MemLp (fun p : ℝ × Vec d => (Real.exp (-euclideanSq p.2 / r) : ℂ) *
        D j (p.1, translate p.2 ω)) 2
        ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod volume) :=
    ae_all_iff.mpr fun j => ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg (D j) (hD j) (hDi j)
  filter_upwards [htime t ht, hsp, hFG, hUG, hDG, c4_ae_reduced_physical_elliptic Q]
    with ω hω hspω hFω hUω hDω hAω
  intro χ hχ Pr hPr fr gr hfr L hL η
  have hLp : 0 < L := (by positivity : 0 < 64 * Λ ^ 3).trans_le hL
  obtain ⟨V, Z, hV, hZ, heV, heZ, he⟩ := hω _ Pr hPr fr gr hfr
  specialize he L hLp γ hγ
  let X : ℝ × Vec d → ℂ := fun p => F (p.1, translate p.2 ω) - V p
  let Y : ℝ × Vec d → ℂ := fun p => U (p.1, translate p.2 ω) - Z p
  let W : ℝ × Vec d → ℝ := fun p => -2 * euclideanSq p.2 / (L * (2 - p.1) ^ 2) * η p ^ 2
  let m : ℝ → ℝ := fun s => Real.exp (-γ * s)
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) (t : ℝ))
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hX : Measurable X := (hF.comp hshift).sub hV
  have hY : Measurable Y := (hU.comp hshift).sub hZ
  have physical (v : Lp ℂ 2 (volume : Measure (Vec d))) (V : ℝ × Vec d → ℂ)
      (hV : Measurable V) (heV : ∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal v) :
      MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * V p) 2 (ν.prod volume) := by
    have hVi := endpoint_joint_sq_integrable (ν := ν)
      ((((hPr.2.2.1 v).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hV heV
    have h2 := (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mpr hVi
    apply h2.of_le (by
      apply Measurable.aestronglyMeasurable
      exact (by dsimp only [euclideanSq, dot]; fun_prop : Measurable (fun p : ℝ × Vec d =>
        (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ))).mul hV)
    filter_upwards with p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_of_le_one_left (norm_nonneg _)
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (euclideanSq_nonneg_coords _)) (by positivity)
  have hX2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * X p) 2
      (ν.prod volume) := by
    simpa only [X, mul_sub, Pi.sub_def] using
      (hFω (4 * L) (by positivity)).sub (physical fr V hV heV)
  have hY2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * Y p) 2
      (ν.prod volume) := by
    simpa only [Y, mul_sub, Pi.sub_def] using
      (hUω (4 * L) (by positivity)).sub (physical gr Z hZ heZ)
  have hηX := endpoint_joint_moving_gaussian_memLp ht hLp hX hX2
  have hηY := endpoint_joint_moving_gaussian_memLp ht hLp hY hY2
  change MemLp (fun p => (η p : ℂ) * X p) 2 (ν.prod volume) at hηX
  change MemLp (fun p => (η p : ℂ) * Y p) 2 (ν.prod volume) at hηY
  have hC : Integrable (fun p => η p ^ 2 * ‖X p‖ ^ 2) (ν.prod volume) := by
    convert hηX.norm.integrable_sq using 1
    funext p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hJ : Integrable (fun p => Y p * (((η p ^ 2 : ℝ) : ℂ) * star (X p))) (ν.prod volume) := by
    convert hηY.integrable_mul hηX.star using 1
    funext p
    simp only [Pi.mul_apply, Pi.star_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  obtain ⟨hA, hW⟩ := short_time_moving_gaussian_spacetime_integrable hLp ht X Y hX hY hX2 hY2
  have hν : ∀ᵐ s ∂ν, s ∈ Icc (0 : ℝ) (t : ℝ) := ae_restrict_mem measurableSet_Icc
  have damp (a : ℝ × Vec d → ℝ) (ha : Integrable a (ν.prod volume)) :
      Integrable (fun p => m p.1 * a p) (ν.prod volume) := by
    apply ha.norm.mono' (((by dsimp only [m]; fun_prop : Measurable
      (fun p : ℝ × Vec d => m p.1)).aestronglyMeasurable).mul ha.aestronglyMeasurable)
    have hp : ∀ᵐ p : ℝ × Vec d ∂ν.prod volume, 0 ≤ p.1 := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ici.preimage measurable_fst)).mpr
      filter_upwards [hν] with s hs
      exact ae_of_all _ fun _ => hs.1
    filter_upwards [hp] with p hp
    change ‖m p.1 * a p‖ ≤ ‖a p‖
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) hp))
  have ha (j k : Fin d) : MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry _ _ Λ hΛ hAω
      (fun j k => ω.1.continuous.matrix_elem j k) j k
  have hc : MemLp (fun x => (χ x : ℂ)) ∞ volume := by
    apply memLp_top_of_bound
      (Complex.continuous_ofReal.comp χ.continuous).aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      change ‖(χ x : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ x).1]
      exact (hχ x).2
  have hr (j k : Fin d) :
      MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ)) ∞ volume := by
    convert (hc.fun_mul (ha j k)).add
      (((memLp_top_const (1 : ℂ) : MemLp (fun _ : Vec d => (1 : ℂ)) ∞ volume).sub hc).mul_const
        ((1 : Mat d) j k : ℂ)) using 1
    funext x
    simp only [ForcedLocality.retainedPair, ContinuousMap.coe_mk,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Pi.add_apply, Pi.sub_apply]
  have had (j k : Fin d) := ((ha j k).sub (hr j k)).comp_snd ν
  have hηD (j : Fin d) : MemLp (fun p => (η p : ℂ) * D j (p.1, translate p.2 ω)) 2
      (ν.prod volume) :=
    endpoint_joint_moving_gaussian_memLp ht hLp ((hD j).comp hshift)
      (hDω j (4 * L) (by positivity))
  let RF : Fin d → ℝ × Vec d → ℂ := fun j p =>
    EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω p.2
      (fun k => D k (p.1, translate p.2 ω)) j
  let RS : ℝ × Vec d → ℂ := fun p =>
    EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω p.2
      (fun k => D k (p.1, translate p.2 ω)) i ζ
  have hRF (j : Fin d) : MemLp (fun p => (η p : ℂ) * RF j p) 2 (ν.prod volume) := by
    convert (memLp_finsetSum Finset.univ (fun k _ =>
      (had j k).fun_mul (r := (2 : ℝ≥0∞)) (hηD k))).const_mul (1 / 2 : ℂ) using 1
    funext p
    simp only [RF, EinsteinFull.C9ShortTimeLocality.retainedFluxDefect, Finset.mul_sum,
      Pi.sub_apply, Complex.ofReal_sub]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hRS : MemLp (fun p => (η p : ℂ) * RS p) 2 (ν.prod volume) := by
    convert (memLp_finsetSum Finset.univ (fun j _ =>
      (had j i).fun_mul (r := (2 : ℝ≥0∞)) (hηD j))).const_mul ζ using 1
    funext p
    simp only [RS, EinsteinFull.C9ShortTimeLocality.retainedDriftDefect, Finset.mul_sum,
      Pi.sub_apply, Complex.ofReal_sub]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have sqint (u : ℝ × Vec d → ℂ)
      (hu : MemLp (fun p => (η p : ℂ) * u p) 2 (ν.prod volume)) :
      Integrable (fun p => η p ^ 2 * ‖u p‖ ^ 2) (ν.prod volume) := by
    convert hu.norm.integrable_sq using 1
    funext p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hRFi : Integrable (fun p => η p ^ 2 * ∑ j, ‖RF j p‖ ^ 2) (ν.prod volume) := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun j _ => sqint _ (hRF j))
  have hRSi := sqint RS hRS
  let b : ℝ → ℝ := fun s => m s *
    ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j, ‖RF j (s, x)‖ ^ 2) +
      ∫ x, η (s, x) ^ 2 * ‖RS (s, x)‖ ^ 2)
  have hbi : Integrable b ν := by
    have hi := (damp _ ((hRFi.const_mul (4 * Λ + 16 / L)).add hRSi)).integral_prod_left
    apply hi.congr
    filter_upwards [hRFi.prod_right_ae, hRSi.prod_right_ae] with s hfs hss
    simp only [b, Pi.add_apply, integral_const_mul,
      integral_add (hfs.const_mul (4 * Λ + 16 / L)) hss]
  have hb0 (s : ℝ) : 0 ≤ b s := by
    dsimp only [b]
    apply mul_nonneg (Real.exp_nonneg _)
    apply add_nonneg
    · exact mul_nonneg (by positivity) (integral_nonneg fun x => by positivity)
    · exact integral_nonneg fun x => by positivity
  refine ⟨hbi, ?_⟩
  let A : ℝ × Vec d → ℝ := fun p => m p.1 *
    (η p ^ 2 * (2 * (star (X p) * Y p).re) - γ * (η p ^ 2 * ‖X p‖ ^ 2))
  let C : ℝ × Vec d → ℝ := fun p => m p.1 * (W p * ‖X p‖ ^ 2)
  have hAi : Integrable A (ν.prod volume) := damp _ (hA.sub (hC.const_mul γ))
  have hCi : Integrable C (ν.prod volume) := damp _ hW
  let a : ℝ → ℝ := fun s => (∫ x, A (s, x)) + ∫ x, C (s, x)
  have hai : Integrable a ν := hAi.integral_prod_left.add hCi.integral_prod_left
  have hid : (∫ s, a s ∂ν) = m t *
      (∫ x, η (t, x) ^ 2 * ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2) -
      (∫ x, η (0, x) ^ 2 * ‖f (translate x ω) - fr x‖ ^ 2) := by
    rw [integral_add hAi.integral_prod_left hCi.integral_prod_left]
    dsimp only [ν, A, C, m, X, Y, W, η] at he ⊢
    linarith only [he]
  have hmap (s : ℝ≥0) : IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ
      (Pr s fr) (Pr s gr) := by
    apply (hPr.2.2.2 _ _).mp
    have h := ((Pr s).continuous.tendsto gr).comp ((hPr.2.2.2 fr gr).mpr hfr)
    convert h using 1
    ext r
    simp only [Function.comp_apply, map_smul, map_sub]
    have hc : Pr s (Pr r fr) = Pr r (Pr s fr) := by
      rw [← ContinuousLinearMap.comp_apply, ← hPr.2.1, add_comm,
        hPr.2.1, ContinuousLinearMap.comp_apply]
    rw [hc]
  have hspν := ae_restrict_of_ae_restrict_of_subset
    (show Ioc (0 : ℝ) (t : ℝ) ⊆ Ioi (0 : ℝ) from Ioc_subset_Ioi_self) hspω
  rw [restrict_Ioc_eq_restrict_Icc] at hspν
  have hle : ∀ᵐ s ∂ν, a s ≤ m s *
      ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
        ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
          (fun k => D k (s, translate x ω)) j‖ ^ 2) +
      (∫ x, η (s, x) ^ 2 *
        ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
          (fun k => D k (s, translate x ω)) i ζ‖ ^ 2)) := by
    filter_upwards [hspν, hν, hJ.prod_right_ae, hC.prod_right_ae, hA.prod_right_ae]
      with s hs hsI hJs hCs hAs
    obtain ⟨_, hb⟩ := hs χ hχ (Pr s.toNNReal fr) (Pr s.toNNReal gr) (hmap s.toNNReal)
      L (2 - s) s hL (by linarith [hsI.2])
    have hpair : (∫ x, η (s, x) ^ 2 * (2 * (star (X (s, x)) * Y (s, x)).re)) =
        2 * (∫ x, Y (s, x) * (((η (s, x) ^ 2 : ℝ) : ℂ) * star (X (s, x)))).re := by
      have hr : (∫ x, Y (s, x) * (((η (s, x) ^ 2 : ℝ) : ℂ) * star (X (s, x)))).re =
          ∫ x, (Y (s, x) * (((η (s, x) ^ 2 : ℝ) : ℂ) * star (X (s, x)))).re :=
        (integral_re hJs).symm
      rw [hr, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero, sub_zero, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    have hmass := integral_sub hAs (hCs.const_mul γ)
    have hrewrite : a s = m s * (
        2 * (∫ x, Y (s, x) * (((η (s, x) ^ 2 : ℝ) : ℂ) * star (X (s, x)))).re +
        (∫ x, W (s, x) * ‖X (s, x)‖ ^ 2) - γ * ∫ x, η (s, x) ^ 2 * ‖X (s, x)‖ ^ 2) := by
      dsimp only [a, A, C]
      simp only [integral_const_mul]
      rw [hmass, hpair, integral_const_mul]
      ring
    rw [hrewrite]
    convert hb using 1
    apply congrArg (fun q : ℝ => m s * q)
    apply congrArg₂ (fun b c : ℝ => b - γ * c)
    · apply congrArg₂ (fun b c : ℝ => b + c)
      · apply congrArg (fun z : ℂ => 2 * z.re)
        apply integral_congr_ae
        filter_upwards [heV s, heZ s] with x hx hz
        simp only [X, Y, hx, hz, η]
      · apply integral_congr_ae
        filter_upwards [heV s] with x hx
        simp only [X, hx, W, η]
    · apply integral_congr_ae
      filter_upwards [heV s] with x hx
      simp only [X, hx, η]
  have hpos : Integrable (fun s => max (a s) 0) ν := hai.pos_part
  have hpos0 : ∀ᵐ s ∂ν, 0 ≤ max (a s) 0 := ae_of_all _ fun _ => le_max_right _ _
  have hi := integral_mono_ae hai hpos (ae_of_all _ fun s => le_max_left (a s) 0)
  have hupper : ENNReal.ofReal (∫ s, a s ∂ν) ≤
      ∫⁻ s, ENNReal.ofReal (m s *
        ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
          ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
            (fun k => D k (s, translate x ω)) j‖ ^ 2) +
        (∫ x, η (s, x) ^ 2 *
          ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
            (fun k => D k (s, translate x ω)) i ζ‖ ^ 2))) ∂ν := by
    apply (ENNReal.ofReal_le_ofReal hi).trans
    rw [ofReal_integral_eq_lintegral_ofReal hpos hpos0]
    apply lintegral_mono_ae
    filter_upwards [hle] with s hs
    simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (zero_le : (0 : ℝ≥0∞) ≤ _)] using
      ENNReal.ofReal_le_ofReal hs
  let e0 := ∫ x, η (0, x) ^ 2 * ‖f (translate x ω) - fr x‖ ^ 2
  have hend : m t * (∫ x, η (t, x) ^ 2 *
      ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2) = e0 + ∫ s, a s ∂ν := by
    dsimp only [e0]
    linarith only [hid]
  have hc : ENNReal.ofReal (m t * (∫ x, η (t, x) ^ 2 *
      ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2)) ≤
      ENNReal.ofReal e0 + ∫⁻ s, ENNReal.ofReal (b s) ∂ν := by
    rw [hend]
    exact ENNReal.ofReal_add_le.trans (add_le_add_right hupper _)
  rw [← ofReal_integral_eq_lintegral_ofReal hbi (ae_of_all _ hb0),
    ← ENNReal.ofReal_add (integral_nonneg fun x => by positivity)
      (integral_nonneg hb0)] at hc
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg
    (integral_nonneg fun x => by positivity) (integral_nonneg hb0))).mp hc

/-- The actual retained comparison extends to every physical L2 initial datum.
The source and its integrability are unchanged, and no physical graph-domain
assumption is imposed on that datum. -/
theorem short_time_actual_retained_l2_integrated_comparison
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (B : ℝ) (hζ : ‖ζ‖ ≤ B) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let γ := 16 * Λ ^ 3 * B ^ 2 + 1
    ∃ D : Fin d → ℝ × FieldPair d → ℂ, (∀ j, Measurable (D j)) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
      ∀ χ : C(Vec d, ℝ), (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      ∀ L : ℝ, 64 * Λ ^ 3 ≤ L →
      let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
      Integrable (fun s => Real.exp (-γ * s) *
          ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) i ζ‖ ^ 2)))
        (volume.restrict (Icc (0 : ℝ) (t : ℝ))) ∧
      Real.exp (-γ * (t : ℝ)) *
        (∫ x, η (t, x) ^ 2 * ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2) ≤
      (∫ x, η (0, x) ^ 2 * ‖f (translate x ω) - fr x‖ ^ 2) +
        ∫ s in Icc (0 : ℝ) (t : ℝ), Real.exp (-γ * s) *
          ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) i ζ‖ ^ 2)) := by
  intro Λ γ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨D, hD, heD, hcomp⟩ :=
    short_time_actual_retained_integrated_comparison hd Q hP hfg B hζ
  refine ⟨D, hD, heD, ?_⟩
  intro t ht
  filter_upwards [hcomp t ht,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) f,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) (P t f)] with ω hc hfω htω
  intro χ hχ Pr hPr fr L hL η
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := (by positivity : 0 < 64 * Λ ^ 3).trans_le hL
  have hrt : 0 < L * (2 - (t : ℝ)) / 2 := by
    apply div_pos _ (by norm_num)
    exact mul_pos hLp (by linarith)
  obtain ⟨v, g, hg, hv, henergy⟩ :=
    short_time_physical_generator_gaussian_approximation hPr fr
  have weight (s : ℝ) (hs : 0 < L * (2 - s)) (x : Vec d) :
      η (s, x) ^ 2 = Real.exp (-euclideanSq x / (L * (2 - s) / 2)) := by
    dsimp only [η]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hinitial := short_time_gaussian_comparison_energy_tendsto L hLp
    (fun x => f (translate x ω)) (by
      simpa only using hfω (2 * L) (by positivity)) v fr hv
  have hfinal := henergy t (L * (2 - (t : ℝ)) / 2) hrt
    (fun x => (P t f) (translate x ω)) (by
      simpa only using htω (2 * (L * (2 - (t : ℝ)) / 2)) (by positivity))
  have hw0 (x : Vec d) : η (0, x) ^ 2 = Real.exp (-euclideanSq x / L) := by
    simpa only [sub_zero, mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      weight 0 (by positivity) x
  simp_rw [← hw0] at hinitial
  simp_rw [← weight (t : ℝ) (mul_pos hLp (by linarith))] at hfinal
  refine ⟨(hc χ hχ Pr hPr (v 0) (g 0) (hg 0) L hL).1, ?_⟩
  exact le_of_tendsto_of_tendsto' (hfinal.const_mul _) (hinitial.add_const _)
    (fun n => (hc χ hχ Pr hPr (v n) (g n) (hg n) L hL).2)

/-- Actual forward and clock endpoint data admit retained cutoff evolutions
with the finite integrated comparison. The stationary generator pairs and
physical cutoff representatives are constructed from the observations. -/
theorem short_time_forward_clock_retained_cutoff_comparison
    {d : ℕ} (hd : 2 ≤ d) (S : StructuralData d)
    (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (B : ℝ) (hζ : ‖ζ‖ ≤ B) (ν : Fin d ⊕ Unit) :
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
    let γ := 16 * Λ ^ 3 * B ^ 2 + 1
    ∃ D : Fin d → ℝ × FieldPair d → ℂ, (∀ j, Measurable (D j)) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
      ∀ χ : C(Vec d, ℝ), (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → HasCompactSupport χ →
      ∃ fr : Lp ℂ 2 (volume : Measure (Vec d)),
        (fr : Vec d → ℂ) =ᵐ[volume] (fun x => (χ x : ℂ) * f (translate x ω)) ∧
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr →
      ∀ L : ℝ, 64 * Λ ^ 3 ≤ L →
      let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
      Integrable (fun s => Real.exp (-γ * s) *
          ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2)))
        (volume.restrict (Icc (0 : ℝ) (t : ℝ))) ∧
      Real.exp (-γ * (t : ℝ)) *
        (∫ x, η (t, x) ^ 2 * ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2) ≤
      (∫ x, η (0, x) ^ 2 * ‖f (translate x ω) - (χ x : ℂ) * f (translate x ω)‖ ^ 2) +
        ∫ s in Icc (0 : ℝ) (t : ℝ), Real.exp (-γ * s) *
          ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2)) := by
  intro f Λ γ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hgen : ∃ g, IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ f g := by
    cases ν with
    | inl j =>
      obtain ⟨b, hb⟩ := timeFlux_drift_generator (i := ⟨0, by omega⟩) (ζ := ζ) hβ j
      obtain ⟨c, hc⟩ := timeFlux_coefficient_generator (i := ⟨0, by omega⟩) (ζ := ζ)
        hQ ha ⟨0, by omega⟩ j
      exact ⟨b + ζ • c, hb.add (hc.smul ζ)⟩
    | inr u =>
      obtain ⟨c, hc⟩ := centeredEquations_clock_initial_generator
        (i := ⟨0, by omega⟩) (ζ := ζ) hQ hμ
      exact ⟨ζ • c, hc.smul ζ⟩
  obtain ⟨g, hfg⟩ := hgen
  obtain ⟨D, hD, heD, hcomp⟩ :=
    short_time_actual_retained_l2_integrated_comparison hd Q hP hfg B hζ
  refine ⟨D, hD, heD, ?_⟩
  intro t ht
  filter_upwards [hcomp t ht,
    short_time_stationary_cutoff_generator_approximation hd (reducedLaw Q)
      (reducedLaw_stationary Q) f] with ω hc hcut
  intro χ hχ hcompact
  obtain ⟨fr, hfr, _⟩ := hcut χ χ.continuous hcompact
  refine ⟨fr, hfr, ?_⟩
  intro Pr hPr L hL η
  have h := hc χ hχ Pr hPr fr L hL
  have he : (∫ x, η (0, x) ^ 2 * ‖f (translate x ω) - fr x‖ ^ 2) =
      ∫ x, η (0, x) ^ 2 *
        ‖f (translate x ω) - (χ x : ℂ) * f (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hfr] with x hx
    rw [hx]
  dsimp only at h
  rw [he] at h
  exact h


/-- The cutoff of the actual clock field has a jointly locally measurable
physical evolution. Both the initial class and the evolved class are chosen
before any law; on elliptic retained fields they are the actual semigroup. -/
theorem short_time_clock_cutoff_measurable_evolution {d : ℕ}
    (χ : C(Vec d, ℝ)) (hcompact : HasCompactSupport χ) (U : Set (Vec d))
    (hsupport : ∀ x, x ∉ U → χ x = 0) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (i : Fin d) (ζ : ℂ) :
    let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
    let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∃ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)),
      Measurable fr ∧ Measurable (Function.uncurry V) ∧
      (∀ ω, (fr ω : Vec d → ℂ) =ᵐ[volume]
        (fun x => ζ * (χ x : ℂ) * (ω.2 x : ℂ))) ∧
      ∀ ω, (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
        ∃ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr ∧
          ∀ t, V ω t = Pr t (fr ω) := by
  classical
  let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  have hbase : ∃ u : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
      Measurable u ∧ ∀ ω, (u ω : Vec d → ℂ) =ᵐ[volume]
        (fun x => ((ForcedLocality.retainedPair χ ω).2 x : ℂ) - 1) := by
    refine ⟨_, short_time_clock_retained_initial_measurable χ hcompact U hsupport, ?_⟩
    intro ω
    exact MemLp.coeFn_toLp _
  obtain ⟨u, hu, heu⟩ := hbase
  have hk : MemLp (fun x : Vec d => (χ x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp χ.continuous).memLp_of_hasCompactSupport
      (hcompact.comp_left rfl)
  let k := hk.toLp (fun x => (χ x : ℂ))
  let fr (ω : FieldPair d) := ζ • (u ω + k)
  have hfr : Measurable fr := (hu.add_const k).const_smul ζ
  have hefr (ω : FieldPair d) : (fr ω : Vec d → ℂ) =ᵐ[volume]
      (fun x => ζ * (χ x : ℂ) * (ω.2 x : ℂ)) := by
    filter_upwards [Lp.coeFn_smul ζ (u ω + k), Lp.coeFn_add (u ω) k,
      heu ω, hk.coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, h4]
    change ζ * (((χ x * ω.2 x + (1 - χ x) : ℝ) : ℂ) - 1 + (χ x : ℂ)) = _
    push_cast
    ring
  have hgood : MeasurableSet
      {ω : FieldPair d | ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ} := by
    have hc : IsClosed {ω : FieldPair d | ∀ x, S5Elliptic (ω.1 x) Λ} := by
      have he : {ω : FieldPair d | ∀ x, S5Elliptic (ω.1 x) Λ} =
          ⋂ x : Vec d,
            ((⋂ j : Fin d, ⋂ k : Fin d, {ω : FieldPair d | ω.1 x j k = ω.1 x k j}) ∩
              ⋂ ξ : Fin d → ℝ,
                ({ω : FieldPair d | Λ⁻¹ * ∑ j, ξ j ^ 2 ≤ s5Bil (ω.1 x) ξ ξ} ∩
                 {ω : FieldPair d | s5Bil (ω.1 x) ξ ξ ≤ Λ * ∑ j, ξ j ^ 2})) := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
        constructor
        · intro h x
          exact ⟨(h x).symm, fun ξ => ⟨(h x).lower ξ, (h x).upper ξ⟩⟩
        · intro h x
          exact ⟨hΛ, (h x).1, fun ξ => ((h x).2 ξ).1, fun ξ => ((h x).2 ξ).2⟩
      rw [he]
      apply isClosed_iInter
      intro x
      refine IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun k => ?_)
        (isClosed_iInter fun ξ => IsClosed.inter ?_ ?_)
      · apply isClosed_eq <;> fun_prop
      · apply isClosed_le continuous_const
        unfold s5Bil
        fun_prop
      · apply isClosed_le _ continuous_const
        unfold s5Bil
        fun_prop
    have hcm : @MeasurableSet (FieldPair d) (borel _)
        {ω | ∀ x, S5Elliptic (ω.1 x) Λ} := by
      let : MeasurableSpace (FieldPair d) := borel _
      exact hc.measurableSet
    exact hcm.preimage (ForcedLocality.measurable_retainedPair χ U hsupport)
  obtain ⟨Pr, Prdag, hPr, _, hmPr, _⟩ :=
    short_time_clock_retained_physical_evolution χ U hsupport Λ hΛ i ζ
  let good := {ω : FieldPair d | ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ}
  let Ω := {ω : FieldPair d // ω ∈ good}
  let V (ω : FieldPair d) (t : ℝ≥0) :=
    if h : ω ∈ good then Pr ⟨ω, h⟩ t (fr ω) else 0
  refine ⟨fr, V, hfr, ?_, hefr, ?_⟩
  · let s : Set (FieldPair d × ℝ≥0) := {q | q.1 ∈ good}
    have hs : MeasurableSet s := hgood.preimage measurable_fst
    have hv : Measurable (fun q : s => (⟨q.val.1, q.property⟩ : Ω)) :=
      (measurable_subtype_coe.fst).subtype_mk
    have ht : Measurable (fun q : s => q.val.2) := measurable_subtype_coe.snd
    have hf : Measurable (fun q : s => fr q.val.1) :=
      hfr.comp measurable_subtype_coe.fst
    exact Measurable.dite (hmPr.comp (hv.prodMk (ht.prodMk hf))) measurable_const hs
  · intro ω hω
    exact ⟨Pr ⟨ω, hω⟩, (hPr ⟨ω, hω⟩).1, fun t => dite_eq_left hω⟩


/-- The actual clock comparison uses a single locally measurable retained
orbit, chosen before the law. The spatial cutoff and ellipticity events are
derived from the actual clock observation and the environment law. -/
theorem short_time_clock_local_retained_comparison
    {d : ℕ} (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ ≤ B)
    (χ : C(Vec d, ℝ)) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hcompact : HasCompactSupport χ) (U : Set (Vec d))
    (hsupport : ∀ x, x ∉ U → χ x = 0) :
    ∃ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)),
      @Measurable _ _ (EinsteinRelation.localSigma U) (borel _) fr ∧
      @Measurable _ _ ((EinsteinRelation.localSigma U).prod inferInstance) (borel _)
        (Function.uncurry V) ∧
      (∀ ω, (fr ω : Vec d → ℂ) =ᵐ[volume]
        (fun x => ζ * (χ x : ℂ) * (ω.2 x : ℂ))) ∧
      ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange)
        (hQ : HasSmoothBounds S Q) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedClockObservation Q μ →
      ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P,
      let f := ζ • μ
      let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
      let γ := 16 * Λ ^ 3 * B ^ 2 + 1
      ∃ D : Fin d → ℝ × FieldPair d → ℂ, (∀ j, Measurable (D j)) ∧
        (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
        ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
        ∀ L : ℝ, 64 * Λ ^ 3 ≤ L →
        let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
        Integrable (fun s => Real.exp (-γ * s) * ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2)))
          (volume.restrict (Icc (0 : ℝ) (t : ℝ))) ∧
        Real.exp (-γ * (t : ℝ)) *
          (∫ x, η (t, x) ^ 2 * ‖(P t f) (translate x ω) - (V ω t) x‖ ^ 2) ≤
        (∫ x, η (0, x) ^ 2 *
          ‖f (translate x ω) - (χ x : ℂ) * f (translate x ω)‖ ^ 2) +
          ∫ s in Icc (0 : ℝ) (t : ℝ), Real.exp (-γ * s) * ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2)) := by
  let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
  have hexp : 1 ≤ Real.exp (2 * S.ellipticity) :=
    Real.one_le_exp (by linarith [S.one_le_ellipticity])
  have hΛ : 1 ≤ Λ := by dsimp only [Λ]; nlinarith [S.one_le_ellipticity]
  obtain ⟨fr, V, hfr, hV, hefr, hactual⟩ :=
    short_time_clock_cutoff_measurable_evolution χ hcompact U hsupport Λ hΛ
      ⟨0, by omega⟩ ζ
  refine ⟨fr, V, hfr, hV, hefr, ?_⟩
  intro Q hQ μ hμ P hP f Λ' γ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨g, hg⟩ := centeredEquations_clock_initial_generator
    (i := ⟨0, by omega⟩) (ζ := ζ) hQ hμ
  obtain ⟨D, hD, heD, hcomp⟩ := short_time_actual_retained_l2_integrated_comparison
    hd Q hP (hg.smul ζ) B hζ
  refine ⟨D, hD, heD, ?_⟩
  have hf : (f : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      (fun ω => ζ * (ω.2 0 : ℂ)) := by
    filter_upwards [Lp.coeFn_smul ζ μ, hμ] with ω h1 h2
    change (ζ • μ : Lp ℂ 2 (reducedLaw Q)) ω = _
    rw [h1, Pi.smul_apply, h2]
    rfl
  have hsp := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable f).measurable
    (by fun_prop : Measurable (fun ω : FieldPair d => ζ * (ω.2 0 : ℂ))) hf
  intro t ht
  filter_upwards [hcomp t ht, hsp, c4_ae_reduced_physical_elliptic Q]
    with ω hc hs hA
  have hgood (x : Vec d) : S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ :=
    endpoint_retained_elliptic χ ω x (s5Elliptic_of_isElliptic hΛ hA x)
      (hχ x).1 (hχ x).2
  obtain ⟨Pr, hPr, heV⟩ := hactual ω hgood
  have hcut : (fr ω : Vec d → ℂ) =ᵐ[volume]
      (fun x => (χ x : ℂ) * f (translate x ω)) := by
    filter_upwards [hefr ω, hs] with x h1 h2
    rw [h1, h2]
    simp only [translate_scalar, add_zero]
    ring
  intro L hL η
  have h := hc χ hχ Pr hPr (fr ω) L hL
  have he : (∫ x, η (0, x) ^ 2 * ‖f (translate x ω) - fr ω x‖ ^ 2) =
      ∫ x, η (0, x) ^ 2 *
        ‖f (translate x ω) - (χ x : ℂ) * f (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hcut] with x hx
    rw [hx]
  dsimp only at h
  rw [he, ← heV t] at h
  exact h

/-- Jointly measurable square-integrable spatial data give Borel L2 classes. -/
private theorem endpoint_measurable_physical_toLp {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (f : Ω → Vec d → ℂ)
    (hf : Measurable (fun s : Ω × Vec d => f s.1 s.2))
    (hL : ∀ ω, MemLp (f ω) 2 (volume : Measure (Vec d))) :
    @Measurable Ω (Lp ℂ 2 (volume : Measure (Vec d))) _ (borel _)
      (fun ω => (hL ω).toLp (f ω)) := by
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 (volume : Measure (Vec d))) :=
    Lp.SecondCountableTopology
  have hcriterion (g : Ω → Lp ℂ 2 (volume : Measure (Vec d)))
      (hg : ∀ y, Measurable (fun ω => dist (g ω) y)) : Measurable g := by
    apply measurable_of_isOpen
    intro s hs
    let I := {b : Lp ℂ 2 (volume : Measure (Vec d)) × ℝ // Metric.ball b.1 b.2 ⊆ s}
    have heq : (⋃ b : I, Metric.ball b.val.1 b.val.2) = s := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset fun b => b.property
      · intro y hy
        obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hs y hy
        exact Set.mem_iUnion.mpr ⟨⟨(y, ε), hsub⟩, Metric.mem_ball_self hε⟩
    obtain ⟨T, hT, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun b : I => Metric.ball b.val.1 b.val.2) (fun _ => Metric.isOpen_ball)
    rw [← heq, ← hcover, Set.preimage_iUnion₂]
    exact MeasurableSet.biUnion hT
      (fun b _ => measurableSet_lt (hg b.val.1) measurable_const)
  apply hcriterion
  intro u
  have hm : Measurable (fun s : Ω × Vec d => f s.1 s.2 - u s.2) :=
    hf.sub ((Lp.stronglyMeasurable u).measurable.comp measurable_snd)
  have hnorm : Measurable
      (fun ω => eLpNorm (fun x => f ω x - u x) 2 volume) := by
    have hformula (ω : Ω) : eLpNorm (fun x => f ω x - u x) 2 volume =
        (∫⁻ x, ‖f ω x - u x‖ₑ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal) :=
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        ((hL ω).aestronglyMeasurable.sub (Lp.aestronglyMeasurable u))
    simp_rw [hformula]
    exact ENNReal.continuous_rpow_const.measurable.comp
      ((ENNReal.continuous_rpow_const.measurable.comp hm.enorm).lintegral_prod_right')
  have heq : (fun ω => dist ((hL ω).toLp (f ω)) u) =
      (fun ω => (eLpNorm (fun x => f ω x - u x) 2 volume).toReal) := by
    funext ω
    rw [Lp.dist_def, eLpNorm_congr_ae ((hL ω).coeFn_toLp.sub Filter.EventuallyEq.rfl)]
    rfl
  rw [heq]
  exact hnorm.ennreal_toReal

/-- The actual forward cutoff datum admits a locally measurable physical L2
representative. An outer retained field records derivatives on the support of
the inner cutoff; nonsmooth retained fields are assigned zero. -/
theorem short_time_forward_cutoff_initial_measurable {d : ℕ}
    (χ θ : C(Vec d, ℝ)) (hcompact : HasCompactSupport χ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (U W : Set (Vec d))
    (hsupport : ∀ x, x ∉ U → θ x = 0) (hW : IsOpen W)
    (hinterior : ∀ x ∈ W, θ x = 1) (hχ : ∀ x, χ x ≠ 0 → x ∈ W)
    (i j : Fin d) (ζ : ℂ) :
    ∃ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
      @Measurable _ _ (EinsteinRelation.localSigma U) (borel _) fr ∧
      ∀ ω, IsSmoothFieldPair ω →
        (fr ω : Vec d → ℂ) =ᵐ[volume] fun x => (χ x : ℂ) *
          ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
            (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ)) := by
  classical
  let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
  have hp : @Measurable (FieldPair d) (FieldPair d)
      (EinsteinRelation.localSigma U) (borel _) (ForcedLocality.retainedPair θ) :=
    ForcedLocality.measurable_retainedPair θ U hsupport
  have hgood : MeasurableSet
      {ω : FieldPair d | IsSmoothFieldPair (ForcedLocality.retainedPair θ ω)} :=
    Sharpness.measurableSet_isSmoothFieldPair_fieldPair.preimage hp
  let F (ω : FieldPair d) (k : Fin d) : C(Vec d, ℝ) :=
    ⟨fun x => (ForcedLocality.retainedPair θ ω).1 x k j,
      (ForcedLocality.retainedPair θ ω).1.continuous.matrix_elem k j⟩
  have hFm (k : Fin d) : Measurable (fun ω => F ω k) := by
    apply measurable_continuousMap_of_evaluations
    intro x
    have he : @Measurable (FieldPair d) ℝ (borel _) inferInstance
        (fun ω => ω.1 x k j) := by
      let : MeasurableSpace (FieldPair d) := borel _
      exact (by fun_prop : Continuous (fun ω : FieldPair d => ω.1 x k j)).measurable
    exact he.comp hp
  let b (ω : FieldPair d) (x : Vec d) : ℂ :=
    (χ x : ℂ) * ((((1 / 2 : ℝ) * ∑ k : Fin d,
      coordinateDerivative k (F ω k) x : ℝ) : ℂ) +
        ζ * ((ForcedLocality.retainedPair θ ω).1 x i j : ℂ))
  have hbm : Measurable (fun p : FieldPair d × Vec d => b p.1 p.2) := by
    have hder (k : Fin d) : Measurable (fun p : FieldPair d × Vec d =>
        coordinateDerivative k (F p.1 k) p.2) :=
      (Sharpness.measurable_continuousMap_coordinateDerivative d k).comp
        ((hFm k |>.comp measurable_fst).prodMk measurable_snd)
    have he : @Measurable (FieldPair d × Vec d) ℂ
        ((borel (FieldPair d)).prod inferInstance) inferInstance
        (fun p => (p.1.1 p.2 i j : ℂ)) := by
      let : MeasurableSpace (FieldPair d) := borel _
      exact (by fun_prop : Continuous (fun p : FieldPair d × Vec d =>
        (p.1.1 p.2 i j : ℂ))).measurable
    have ha : Measurable (fun p : FieldPair d × Vec d =>
        ((ForcedLocality.retainedPair θ p.1).1 p.2 i j : ℂ)) :=
      he.comp ((hp.comp measurable_fst).prodMk measurable_snd)
    exact (Complex.measurable_ofReal.comp (χ.continuous.measurable.comp measurable_snd)).mul
      ((Complex.measurable_ofReal.comp ((Finset.measurable_sum _ fun k _ => hder k).const_mul
        (1 / 2 : ℝ))).add (ha.const_mul ζ))
  let b₀ (ω : FieldPair d) (x : Vec d) : ℂ :=
    if IsSmoothFieldPair (ForcedLocality.retainedPair θ ω) then b ω x else 0
  have hb₀m : Measurable (fun p : FieldPair d × Vec d => b₀ p.1 p.2) :=
    Measurable.ite (hgood.preimage measurable_fst) hbm measurable_const
  have hbL (ω : FieldPair d) : MemLp (b₀ ω) 2 volume := by
    by_cases hω : IsSmoothFieldPair (ForcedLocality.retainedPair θ ω)
    · have hder (k : Fin d) : Continuous (coordinateDerivative k (F ω k)) :=
        (((hω.1 k j).of_le (by simp) : ContDiff ℝ 1 (F ω k)).continuous_fderiv_apply
          one_ne_zero).comp (continuous_id.prodMk continuous_const)
      have hb : Continuous (b ω) := by
        apply (Complex.continuous_ofReal.comp χ.continuous).mul
        apply Continuous.add
        · exact Complex.continuous_ofReal.comp
            ((continuous_finsetSum _ fun k _ => hder k).const_mul (1 / 2 : ℝ))
        · exact (Complex.continuous_ofReal.comp
            ((ForcedLocality.retainedPair θ ω).1.continuous.matrix_elem i j)).const_mul ζ
      have hc : HasCompactSupport (b ω) :=
        (hcompact.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)).mul_right
      simpa only [b₀, ite_eq_left hω] using hb.memLp_of_hasCompactSupport (p := 2) (μ := volume) hc
    · simp only [b₀, ite_eq_right hω]
      exact MemLp.zero'
  refine ⟨fun ω => (hbL ω).toLp (b₀ ω),
    endpoint_measurable_physical_toLp b₀ hb₀m hbL, ?_⟩
  intro ω hω
  have hs : IsSmoothFieldPair (ForcedLocality.retainedPair θ ω) := by
    constructor
    · intro k l
      simp only [ForcedLocality.retainedPair, ContinuousMap.coe_mk, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul]
      change ContDiff ℝ (⊤ : ℕ∞) (fun x => θ x * ω.1 x k l + (1 - θ x) * (1 : Mat d) k l)
      exact (hθ.mul (hω.1 k l)).add ((contDiff_const.sub hθ).mul contDiff_const)
    · exact (hθ.mul hω.2).add (contDiff_const.sub hθ)
  filter_upwards [(hbL ω).coeFn_toLp] with x hx
  rw [hx]
  simp only [b₀, ite_eq_left hs, b, F, ContinuousMap.coe_mk]
  by_cases hxχ : χ x = 0
  · simp only [hxχ, Complex.ofReal_zero, zero_mul]
  · rw [ForcedLocality.retainedPair_drift θ ω hW hinterior (hχ x hxχ) j,
      (ForcedLocality.retainedPair_eq_at θ ω (hinterior x (hχ x hxχ))).1]

/-- A single locally measurable physical evolution for the actual forward
cutoff datum, chosen before the law. The initial identity holds on every smooth
field and the orbit is the actual retained semigroup on its ellipticity event. -/
theorem short_time_forward_cutoff_measurable_evolution {d : ℕ}
    (χ θ : C(Vec d, ℝ)) (hcompact : HasCompactSupport χ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (U W : Set (Vec d))
    (hsupport : ∀ x, x ∉ U → θ x = 0) (hW : IsOpen W)
    (hinterior : ∀ x ∈ W, θ x = 1) (hχ : ∀ x, χ x ≠ 0 → x ∈ W)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (i j : Fin d) (ζ : ℂ) :
    let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
    let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∃ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)),
      Measurable fr ∧ Measurable (Function.uncurry V) ∧
      (∀ ω, IsSmoothFieldPair ω →
        (fr ω : Vec d → ℂ) =ᵐ[volume] fun x => (χ x : ℂ) *
          ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
            (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ))) ∧
      ∀ ω, (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
        ∃ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr ∧
          ∀ t, V ω t = Pr t (fr ω) := by
  classical
  let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  obtain ⟨fr, hfr, hefr⟩ := short_time_forward_cutoff_initial_measurable
    χ θ hcompact hθ U W hsupport hW hinterior hχ i j ζ
  have hχsupport : ∀ x, x ∉ U → χ x = 0 := by
    intro x hx
    by_contra hne
    have h1 := hinterior x (hχ x hne)
    rw [hsupport x hx] at h1
    exact zero_ne_one h1
  have hgood : MeasurableSet
      {ω : FieldPair d | ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ} := by
    have hc : IsClosed {ω : FieldPair d | ∀ x, S5Elliptic (ω.1 x) Λ} := by
      have he : {ω : FieldPair d | ∀ x, S5Elliptic (ω.1 x) Λ} =
          ⋂ x : Vec d,
            ((⋂ j : Fin d, ⋂ k : Fin d, {ω : FieldPair d | ω.1 x j k = ω.1 x k j}) ∩
              ⋂ ξ : Fin d → ℝ,
                ({ω : FieldPair d | Λ⁻¹ * ∑ j, ξ j ^ 2 ≤ s5Bil (ω.1 x) ξ ξ} ∩
                 {ω : FieldPair d | s5Bil (ω.1 x) ξ ξ ≤ Λ * ∑ j, ξ j ^ 2})) := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
        constructor
        · intro h x
          exact ⟨(h x).symm, fun ξ => ⟨(h x).lower ξ, (h x).upper ξ⟩⟩
        · intro h x
          exact ⟨hΛ, (h x).1, fun ξ => ((h x).2 ξ).1, fun ξ => ((h x).2 ξ).2⟩
      rw [he]
      apply isClosed_iInter
      intro x
      refine IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun k => ?_)
        (isClosed_iInter fun ξ => IsClosed.inter ?_ ?_)
      · apply isClosed_eq <;> fun_prop
      · apply isClosed_le continuous_const
        unfold s5Bil
        fun_prop
      · apply isClosed_le _ continuous_const
        unfold s5Bil
        fun_prop
    have hcm : @MeasurableSet (FieldPair d) (borel _)
        {ω | ∀ x, S5Elliptic (ω.1 x) Λ} := by
      let : MeasurableSpace (FieldPair d) := borel _
      exact hc.measurableSet
    exact hcm.preimage (ForcedLocality.measurable_retainedPair χ U hχsupport)
  obtain ⟨Pr, Prdag, hPr, _, hmPr, _⟩ :=
    short_time_clock_retained_physical_evolution χ U hχsupport Λ hΛ i ζ
  let good := {ω : FieldPair d | ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ}
  let Ω := {ω : FieldPair d // ω ∈ good}
  let V (ω : FieldPair d) (t : ℝ≥0) :=
    if h : ω ∈ good then Pr ⟨ω, h⟩ t (fr ω) else 0
  refine ⟨fr, V, hfr, ?_, hefr, ?_⟩
  · let s : Set (FieldPair d × ℝ≥0) := {q | q.1 ∈ good}
    have hs : MeasurableSet s := hgood.preimage measurable_fst
    have hv : Measurable (fun q : s => (⟨q.val.1, q.property⟩ : Ω)) :=
      (measurable_subtype_coe.fst).subtype_mk
    have ht : Measurable (fun q : s => q.val.2) := measurable_subtype_coe.snd
    have hf : Measurable (fun q : s => fr q.val.1) :=
      hfr.comp measurable_subtype_coe.fst
    exact Measurable.dite (hmPr.comp (hv.prodMk (ht.prodMk hf))) measurable_const hs
  · intro ω hω
    exact ⟨Pr ⟨ω, hω⟩, (hPr ⟨ω, hω⟩).1, fun t => dite_eq_left hω⟩

/-- The actual forward finite comparison with one jointly locally measurable
retained orbit. Smoothness, initial identity, generator data and ellipticity are
derived from the original observations and structural law. -/
theorem short_time_forward_local_retained_comparison
    {d : ℕ} (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ ≤ B)
    (χ θ : C(Vec d, ℝ)) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hcompact : HasCompactSupport χ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (U W : Set (Vec d)) (hsupport : ∀ x, x ∉ U → θ x = 0)
    (hW : IsOpen W) (hinterior : ∀ x ∈ W, θ x = 1)
    (hχW : ∀ x, χ x ≠ 0 → x ∈ W) (j : Fin d) :
    ∃ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)),
      @Measurable _ _ (EinsteinRelation.localSigma U) (borel _) fr ∧
      @Measurable _ _ ((EinsteinRelation.localSigma U).prod inferInstance) (borel _)
        (Function.uncurry V) ∧
      ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange)
        (hQ : HasSmoothBounds S Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P,
      let f := β j + ζ • a ⟨0, by omega⟩ j
      let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
      let γ := 16 * Λ ^ 3 * B ^ 2 + 1
      ∃ D : Fin d → ℝ × FieldPair d → ℂ, (∀ j, Measurable (D j)) ∧
        (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
        ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
        ∀ L : ℝ, 64 * Λ ^ 3 ≤ L →
        let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
        Integrable (fun s => Real.exp (-γ * s) * ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2)))
          (volume.restrict (Icc (0 : ℝ) (t : ℝ))) ∧
        Real.exp (-γ * (t : ℝ)) *
          (∫ x, η (t, x) ^ 2 * ‖(P t f) (translate x ω) - (V ω t) x‖ ^ 2) ≤
        (∫ x, η (0, x) ^ 2 *
          ‖f (translate x ω) - (χ x : ℂ) * f (translate x ω)‖ ^ 2) +
          ∫ s in Icc (0 : ℝ) (t : ℝ), Real.exp (-γ * s) * ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2)) := by
  let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
  have hexp : 1 ≤ Real.exp (2 * S.ellipticity) :=
    Real.one_le_exp (by linarith [S.one_le_ellipticity])
  have hΛ : 1 ≤ Λ := by dsimp only [Λ]; nlinarith [S.one_le_ellipticity]
  obtain ⟨fr, V, hfr, hV, hefr, hactual⟩ :=
    short_time_forward_cutoff_measurable_evolution χ θ hcompact hθ U W hsupport hW
      hinterior hχW Λ hΛ ⟨0, by omega⟩ j ζ
  refine ⟨fr, V, hfr, hV, ?_⟩
  intro Q hQ β a hβ ha P hP f Λ' γ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨b, hb⟩ := timeFlux_drift_generator (i := ⟨0, by omega⟩) (ζ := ζ) hβ j
  obtain ⟨c, hc⟩ := timeFlux_coefficient_generator (i := ⟨0, by omega⟩) (ζ := ζ)
    hQ ha ⟨0, by omega⟩ j
  obtain ⟨D, hD, heD, hcomp⟩ := short_time_actual_retained_l2_integrated_comparison
    hd Q hP (hb.add (hc.smul ζ)) B hζ
  refine ⟨D, hD, heD, ?_⟩
  let f₀ : FieldPair d → ℂ := fun ω =>
    ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
      (fun y => ω.1 y k j) 0 : ℝ) : ℂ) + ζ * (ω.1 0 ⟨0, by omega⟩ j : ℂ))
  have hf : (f : FieldPair d → ℂ) =ᵐ[reducedLaw Q] f₀ := by
    filter_upwards [Lp.coeFn_add (β j) (ζ • a ⟨0, by omega⟩ j),
      Lp.coeFn_smul ζ (a ⟨0, by omega⟩ j), hβ j, ha ⟨0, by omega⟩ j]
      with ω h1 h2 h3 h4
    change (β j + ζ • a ⟨0, by omega⟩ j : Lp ℂ 2 (reducedLaw Q)) ω = _
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]
    rfl
  have hf₀ : Measurable f₀ := by
    have hdm (k : Fin d) : Measurable (fun ω : FieldPair d =>
        coordinateDerivative k (fun y => ω.1 y k j) 0) :=
      (measurable_fderiv_apply_const_with_param ℝ
        (f := fun (ω : FieldPair d) (y : Vec d) => ω.1 y k j)
        (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
          |>.matrix_elem k j) (unitVector k)).comp (measurable_id.prodMk measurable_const)
    exact (Complex.measurable_ofReal.comp
      ((Finset.measurable_sum _ fun k _ => hdm k).const_mul (1 / 2 : ℝ))).add
        ((by fun_prop : Measurable (fun ω : FieldPair d =>
          (ω.1 0 ⟨0, by omega⟩ j : ℂ))).const_mul ζ)
  have hsp := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable f).measurable hf₀ hf
  obtain ⟨M, _, hsmooth⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d S
  intro t ht
  filter_upwards [hcomp t ht, hsp, c4_ae_reduced_physical_elliptic Q,
    hsmooth Q hQ] with ω hcompω hspω hA hsmoothω
  have hgood (x : Vec d) : S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ :=
    endpoint_retained_elliptic χ ω x (s5Elliptic_of_isElliptic hΛ hA x)
      (hχ x).1 (hχ x).2
  obtain ⟨Pr, hPr, heV⟩ := hactual ω hgood
  have hcut : (fr ω : Vec d → ℂ) =ᵐ[volume]
      (fun x => (χ x : ℂ) * f (translate x ω)) := by
    filter_upwards [hefr ω hsmoothω.1, hspω] with x h1 h2
    rw [h1, h2]
    have hshift (k : Fin d) : coordinateDerivative k
        (fun y => (translate x ω).1 y k j) 0 =
          coordinateDerivative k (fun y => ω.1 y k j) x := by
      have hh := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : Vec d => ω.1 y k j)
        (x := (0 : Vec d)) x
      rw [add_zero] at hh
      exact congrArg (fun A : Vec d →L[ℝ] ℝ => A (unitVector k)) hh
    dsimp only [f₀]
    simp_rw [hshift]
    simp only [translate_matrix, add_zero]
  intro L hL η
  have h := hcompω χ hχ Pr hPr (fr ω) L hL
  have he : (∫ x, η (0, x) ^ 2 * ‖f (translate x ω) - fr ω x‖ ^ 2) =
      ∫ x, η (0, x) ^ 2 *
        ‖f (translate x ω) - (χ x : ℂ) * f (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hcut] with x hx
    rw [hx]
  dsimp only at h
  rw [he, ← heV t] at h
  exact h

/-- Compatible smooth Euclidean cutoffs for the actual retained forward datum.
Both choices precede the law. The outer cutoff is identically one on an open
neighborhood of the inner support, so it preserves drift derivatives there. -/
theorem short_time_compatible_euclidean_cutoffs (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ →
    ∃ χ θ : C(Vec d, ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ ContDiff ℝ (⊤ : ℕ∞) θ ∧
      HasCompactSupport χ ∧ HasCompactSupport θ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧
      (∀ x, euclideanNorm x ≤ ρ / 4 → χ x = 1) ∧
      (∀ x, ρ / 2 ≤ euclideanNorm x → χ x = 0) ∧
      (∀ x, 3 * ρ / 4 ≤ euclideanNorm x → θ x = 0) ∧
      (∀ x, euclideanNorm x ≤ ρ / 2 → θ x = 1) ∧
      (∀ x, χ x ≠ 0 → euclideanNorm x < ρ / 2) ∧
      (∀ x, x ∉ {y : Vec d | euclideanNorm y < ρ} → θ x = 0) ∧
      (∀ j x, |coordinateDerivative j χ x| ≤ C / ρ) ∧
      (∀ j x, |coordinateDerivative j θ x| ≤ C / ρ) := by
  obtain ⟨B, hB, hcut⟩ := exists_physical_gap_euclidean_cutoff d
  refine ⟨4 * B, by positivity, ?_⟩
  intro ρ hρ
  obtain ⟨χ, hχ, hχb, hχone, hχzero, hχder⟩ :=
    hcut 0 (ρ / 4) (ρ / 2) (by positivity) (by linarith)
  obtain ⟨θ, hθ, hθb, hθone, hθzero, hθder⟩ :=
    hcut 0 (ρ / 2) (3 * ρ / 4) (by positivity) (by linarith)
  have hχone' : ∀ x, euclideanNorm x ≤ ρ / 4 → χ x = 1 := by
    simpa only [sub_zero] using hχone
  have hχzero' : ∀ x, ρ / 2 ≤ euclideanNorm x → χ x = 0 := by
    simpa only [sub_zero] using hχzero
  have hθone' : ∀ x, euclideanNorm x ≤ ρ / 2 → θ x = 1 := by
    simpa only [sub_zero] using hθone
  have hθzero' : ∀ x, 3 * ρ / 4 ≤ euclideanNorm x → θ x = 0 := by
    simpa only [sub_zero] using hθzero
  refine ⟨⟨χ, hχ.1.continuous⟩, ⟨θ, hθ.1.continuous⟩,
    hχ.1, hθ.1, hχ.2.1, hθ.2.1, hχb, hθb, hχone', hχzero', hθzero', hθone',
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact lt_of_not_ge (fun hn => hx (hχzero' x hn))
  · intro x hx
    apply hθzero'
    have h : ρ ≤ euclideanNorm x := not_lt.mp hx
    linarith
  · intro j x
    convert hχder j x using 1 <;> ring
  · intro j x
    convert hθder j x using 1 <;> ring

/-- Deterministic radius cutoffs give an actual forward comparison whose
locally measurable retained orbit is chosen before the environment law. -/
theorem short_time_forward_radius_local_retained_comparison
    {d : ℕ} (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ ≤ B)
    (j : Fin d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ →
    ∃ χ : C(Vec d, ℝ), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x, euclideanNorm x ≤ ρ / 4 → χ x = 1) ∧
      (∀ x, ρ / 2 ≤ euclideanNorm x → χ x = 0) ∧
      (∀ k x, |coordinateDerivative k χ x| ≤ C / ρ) ∧
    ∃ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)),
      @Measurable _ _ (EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) (borel _) fr ∧
      @Measurable _ _ ((EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}).prod inferInstance) (borel _)
        (Function.uncurry V) ∧
      ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange)
        (hQ : HasSmoothBounds S Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P,
      let f := β j + ζ • a ⟨0, by omega⟩ j
      let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
      let γ := 16 * Λ ^ 3 * B ^ 2 + 1
      ∃ D : Fin d → ℝ × FieldPair d → ℂ, (∀ j, Measurable (D j)) ∧
        (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
        ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
        ∀ L : ℝ, 64 * Λ ^ 3 ≤ L →
        let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
        Integrable (fun s => Real.exp (-γ * s) * ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2)))
          (volume.restrict (Icc (0 : ℝ) (t : ℝ))) ∧
        Real.exp (-γ * (t : ℝ)) *
          (∫ x, η (t, x) ^ 2 * ‖(P t f) (translate x ω) - (V ω t) x‖ ^ 2) ≤
        (∫ x, η (0, x) ^ 2 *
          ‖f (translate x ω) - (χ x : ℂ) * f (translate x ω)‖ ^ 2) +
          ∫ s in Icc (0 : ℝ) (t : ℝ), Real.exp (-γ * s) * ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2)) := by
  obtain ⟨C, hC, hcuts⟩ := short_time_compatible_euclidean_cutoffs d
  refine ⟨C, hC, ?_⟩
  intro ρ hρ
  obtain ⟨χ, θ, hχsmooth, hθsmooth, hχcompact, _, hχb, _, hχone, hχzero,
    _, hθone, hχsupport, hθsupport, hχder, _⟩ := hcuts ρ hρ
  refine ⟨χ, hχsmooth, hχcompact, hχb, hχone, hχzero, hχder, ?_⟩
  have hnorm : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finset_sum _ fun k _ => (continuous_apply k).mul (continuous_apply k))
  exact short_time_forward_local_retained_comparison hd S B ζ hζ χ θ hχb hχcompact
    hθsmooth {x : Vec d | euclideanNorm x < ρ} {x : Vec d | euclideanNorm x < ρ / 2}
    hθsupport (isOpen_lt hnorm continuous_const) (fun x hx => hθone x hx.le)
    hχsupport j

/-- The same deterministic Euclidean cutoff construction gives the actual
clock comparison with its locally measurable physical initial datum and orbit. -/
theorem short_time_clock_radius_local_retained_comparison
    {d : ℕ} (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ →
    ∃ χ : C(Vec d, ℝ), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x, euclideanNorm x ≤ ρ / 4 → χ x = 1) ∧
      (∀ x, ρ / 2 ≤ euclideanNorm x → χ x = 0) ∧
      (∀ k x, |coordinateDerivative k χ x| ≤ C / ρ) ∧
    ∃ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)),
      @Measurable _ _ (EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) (borel _) fr ∧
      @Measurable _ _ ((EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}).prod inferInstance) (borel _)
        (Function.uncurry V) ∧
      (∀ ω, (fr ω : Vec d → ℂ) =ᵐ[volume]
        (fun x => ζ * (χ x : ℂ) * (ω.2 x : ℂ))) ∧
      ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange)
        (hQ : HasSmoothBounds S Q) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedClockObservation Q μ →
      ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P,
      let f := ζ • μ
      let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
      let γ := 16 * Λ ^ 3 * B ^ 2 + 1
      ∃ D : Fin d → ℝ × FieldPair d → ℂ, (∀ j, Measurable (D j)) ∧
        (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
        ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
        ∀ L : ℝ, 64 * Λ ^ 3 ≤ L →
        let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
        Integrable (fun s => Real.exp (-γ * s) * ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2)))
          (volume.restrict (Icc (0 : ℝ) (t : ℝ))) ∧
        Real.exp (-γ * (t : ℝ)) *
          (∫ x, η (t, x) ^ 2 * ‖(P t f) (translate x ω) - (V ω t) x‖ ^ 2) ≤
        (∫ x, η (0, x) ^ 2 *
          ‖f (translate x ω) - (χ x : ℂ) * f (translate x ω)‖ ^ 2) +
          ∫ s in Icc (0 : ℝ) (t : ℝ), Real.exp (-γ * s) * ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j,
            ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
              (fun k => D k (s, translate x ω)) j‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 *
            ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
              (fun k => D k (s, translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2)) := by
  obtain ⟨C, hC, hcuts⟩ := short_time_compatible_euclidean_cutoffs d
  refine ⟨C, hC, ?_⟩
  intro ρ hρ
  obtain ⟨χ, _, hχsmooth, _, hχcompact, _, hχb, _, hχone, hχzero,
    _, _, _, _, hχder, _⟩ := hcuts ρ hρ
  refine ⟨χ, hχsmooth, hχcompact, hχb, hχone, hχzero, hχder, ?_⟩
  apply short_time_clock_local_retained_comparison hd S B ζ hζ χ hχb hχcompact
    {x : Vec d | euclideanNorm x < ρ}
  intro x hx
  apply hχzero
  have h : ρ ≤ euclideanNorm x := not_lt.mp hx
  linarith

/-- Stationarity transfers equality of jointly measurable time-dependent
representatives to physical spacetime, on one sample event for any fixed
sigma-finite time measure. -/
theorem ae_stationary_spacetime_orbit_congr {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : Measure ℝ) [SFinite ν]
    {F G : ℝ × FieldPair d → ℂ} (hF : Measurable F) (hG : Measurable G)
    (he : ∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] (fun ω => G (s, ω))) :
    ∀ᵐ ω ∂reducedLaw Q,
      (fun p : ℝ × Vec d => F (p.1, translate p.2 ω)) =ᵐ[ν.prod volume]
        (fun p : ℝ × Vec d => G (p.1, translate p.2 ω)) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hm : Measurable (fun q : (ℝ × Vec d) × FieldPair d =>
      (q.1.1, translate q.1.2 q.2)) :=
    measurable_fst.fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_fst.snd.prodMk measurable_snd))
  apply (Measure.ae_ae_comm (μ := ν.prod volume) (ν := reducedLaw Q)
    (p := fun p ω => F (p.1, translate p.2 ω) = G (p.1, translate p.2 ω))
    (measurableSet_eq_fun (hF.comp hm) (hG.comp hm))).mp
  exact ae_of_all _ fun p =>
    (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) p.2).quasiMeasurePreserving.ae
      (he p.1)

/-- Deterministic Gaussian energy of the actual retained flux and drift
forcing, for any joint representative of the actual forward or clock gradient.
The sample event works for every cutoff and radius. -/
theorem short_time_forward_clock_actual_retained_forcing_energy
    (d : ℕ) (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (hB : 0 < B) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P, ∀ ι : Fin d ⊕ Unit,
    let f := ι.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
    ∀ D : Fin d → ℝ × FieldPair d → ℂ, (∀ j, Measurable (D j)) →
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) →
    ∀ T : ℝ≥0, (T : ℝ) ≤ 1 → ∀ L : ℝ, 64 * Λ ^ 3 ≤ L →
    ∀ᵐ ω ∂reducedLaw Q, ∀ (χ : C(Vec d, ℝ)) (ρ : ℝ), 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → (∀ x, euclideanNorm x < ρ → χ x = 1) →
      Integrable (fun p : ℝ × Vec d =>
        (∑ j, Real.exp (-euclideanSq p.2 / L) *
          ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω p.2
            (fun k => D k (p.1, translate p.2 ω)) j‖ ^ 2) +
        Real.exp (-euclideanSq p.2 / L) *
          ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω p.2
            (fun k => D k (p.1, translate p.2 ω)) ⟨0, by omega⟩ ζ‖ ^ 2)
        ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume) ∧
      (∫ p : ℝ × Vec d,
        (∑ j, Real.exp (-euclideanSq p.2 / L) *
          ‖EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω p.2
            (fun k => D k (p.1, translate p.2 ω)) j‖ ^ 2) +
        Real.exp (-euclideanSq p.2 / L) *
          ‖EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω p.2
            (fun k => D k (p.1, translate p.2 ω)) ⟨0, by omega⟩ ζ‖ ^ 2
        ∂(volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume) ≤
        K * Real.exp (-ρ ^ 2 / (2 * L)) *
          (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L))) := by
  obtain ⟨C, hC, hforce⟩ := exists_retained_spacetime_forcing_energy d S B hB.le
  obtain ⟨K₀, hK₀, hwide⟩ := short_time_forward_clock_uniform_gradient_energy d hd S B hB
  refine ⟨(C + 1) * K₀, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P hP ι f Λ D hD heD T hT L hL
  obtain ⟨D₀, hD₀, heD₀, hwide₀⟩ := hwide Q hQ β a μ hβ ha hμ ζ hζ P hP ι
  let ν := volume.restrict (Icc (0 : ℝ) (T : ℝ))
  have hsp : ∀ᵐ ω ∂reducedLaw Q, ∀ j,
      (fun p : ℝ × Vec d => D j (p.1, translate p.2 ω)) =ᵐ[ν.prod volume]
        (fun p : ℝ × Vec d => D₀ j (p.1, translate p.2 ω)) := by
    rw [ae_all_iff]
    intro j
    exact ae_stationary_spacetime_orbit_congr Q ν (hD j) (hD₀ j)
      (fun s => (heD j s).trans (heD₀ j s).symm)
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one S.one_le_ellipticity)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hweight (z : ℝ) : -(L⁻¹ / 2) * z = -z / (2 * L) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hweight' (z : ℝ) : -L⁻¹ * z = -z / L := by
    simp only [div_eq_mul_inv]
    ring
  filter_upwards [hforce Q, hwide₀ T hT L hL, hsp] with ω hf hw heω
  have he : (fun p : ℝ × Vec d => Real.exp (-euclideanSq p.2 / (2 * L)) *
      ∑ j, ‖D j (p.1, translate p.2 ω)‖ ^ 2) =ᵐ[ν.prod volume]
      (fun p : ℝ × Vec d => Real.exp (-euclideanSq p.2 / (2 * L)) *
      ∑ j, ‖D₀ j (p.1, translate p.2 ω)‖ ^ 2) := by
    filter_upwards [ae_all_iff.mpr heω] with p hp
    simp_rw [hp]
  have hi := hw.1.congr he.symm
  have hb : (∫ p : ℝ × Vec d, Real.exp (-euclideanSq p.2 / (2 * L)) *
      ∑ j, ‖D j (p.1, translate p.2 ω)‖ ^ 2 ∂ν.prod volume) ≤
      K₀ * (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L))) := by
    rw [integral_congr_ae he, integral_prod _ hw.1]
    exact hw.2
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hG (j : Fin d) := (hD j).comp hshift
  have hwgt : Measurable (fun p : ℝ × Vec d => Real.exp (-euclideanSq p.2 / (2 * L))) := by
    unfold euclideanSq dot
    fun_prop
  have hGi (j : Fin d) : Integrable (fun p : ℝ × Vec d =>
      Real.exp (-euclideanSq p.2 / (2 * L)) * ‖D j (p.1, translate p.2 ω)‖ ^ 2)
      (ν.prod volume) := by
    apply hi.mono' (hwgt.mul ((hG j).norm.pow_const 2)).aestronglyMeasurable
    apply ae_of_all
    intro p
    dsimp only [Pi.mul_apply, Function.comp_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun k : Fin d => ‖D k (p.1, translate p.2 ω)‖ ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)) (Real.exp_nonneg _)
  intro χ ρ hρ hχ hχone
  have h := hf ν χ L⁻¹ ρ (inv_pos.mpr hLp) hρ hχ hχone
    (fun j p => D j (p.1, translate p.2 ω))
    (fun j => (hG j).aestronglyMeasurable)
    (fun j => by simpa only [hweight] using hGi j) ⟨0, by omega⟩ ζ hζ
  simp only [hweight, hweight'] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have heq : (∑ j : Fin d, ∫ p : ℝ × Vec d,
      Real.exp (-euclideanSq p.2 / (2 * L)) * ‖D j (p.1, translate p.2 ω)‖ ^ 2
      ∂ν.prod volume) = ∫ p : ℝ × Vec d,
      Real.exp (-euclideanSq p.2 / (2 * L)) * ∑ j, ‖D j (p.1, translate p.2 ω)‖ ^ 2
      ∂ν.prod volume := by
    rw [← integral_finsetSum _ (fun j _ => hGi j)]
    congr 1
    funext p
    exact (Finset.mul_sum _ _ _).symm
  rw [heq]
  calc
    _ ≤ C * Real.exp (-ρ ^ 2 / (2 * L)) *
        (K₀ * (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L)))) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg hC (Real.exp_nonneg _))
    _ ≤ (C + 1) * K₀ * Real.exp (-ρ ^ 2 / (2 * L)) *
        (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L))) := by
      have hI : 0 ≤ ∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L)) :=
        integral_nonneg (fun _ => Real.exp_nonneg _)
      calc
        _ = C * (K₀ * Real.exp (-ρ ^ 2 / (2 * L)) *
            (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L)))) := by ring
        _ ≤ (C + 1) * (K₀ * Real.exp (-ρ ^ 2 / (2 * L)) *
            (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L)))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring

/-- Cauchy--Schwarz for a complex temporal primitive on a finite interval. -/
private theorem endpoint_primitive_sq_bound {u : ℝ → ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hu : MemLp u 2 (volume.restrict (Icc (0 : ℝ) t))) :
    ‖∫ s in Icc (0 : ℝ) t, u s‖ ^ 2 ≤
      t * ∫ s in Icc (0 : ℝ) t, ‖u s‖ ^ 2 := by
  have hc : MemLp (fun _ : ℝ => (1 : ℂ)) 2 (volume.restrict (Icc (0 : ℝ) t)) :=
    memLp_const _
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hc) (by simpa using hu)
  have hv : (volume (Icc (0 : ℝ) t)).toReal = t := by
    simp only [Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal ht]
  simp only [norm_one, one_mul, Real.rpow_two, integral_const, smul_eq_mul,
    mul_one, one_pow, Measure.real, Measure.restrict_apply_univ, hv,
    ← Real.sqrt_eq_rpow] at h
  have hn := norm_integral_le_integral_norm (μ := volume.restrict (Icc (0 : ℝ) t)) u
  have hI : 0 ≤ ∫ s in Icc (0 : ℝ) t, ‖u s‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hs := Real.sq_sqrt hI
  have ht' := Real.sq_sqrt ht
  have hp := mul_nonneg (Real.sqrt_nonneg t)
    (Real.sqrt_nonneg (∫ s in Icc (0 : ℝ) t, ‖u s‖ ^ 2))
  have hsq := sq_le_sq₀ (norm_nonneg _) hp |>.mpr (hn.trans h)
  simpa only [mul_pow, ht', hs] using hsq

/-- A square-integrable space-time derivative gives a quantitative strong
local trace for its literal temporal primitive. -/
private theorem endpoint_local_primitive_trace {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {U : ℝ × X → ℂ} (hU : Measurable U)
    (hI : Integrable (fun p => ‖U p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod μ)) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Integrable (fun x => ‖∫ s in Icc (0 : ℝ) t, U (s, x)‖ ^ 2) μ ∧
      (∫ x, ‖∫ s in Icc (0 : ℝ) t, U (s, x)‖ ^ 2 ∂μ) ≤
        t * ∫ x, (∫ s in Icc (0 : ℝ) 1, ‖U (s, x)‖ ^ 2) ∂μ) ∧
    Tendsto (fun t : ℝ≥0 => ∫ x, ‖∫ s in Icc (0 : ℝ) (t : ℝ), U (s, x)‖ ^ 2 ∂μ)
      (𝓝 0) (𝓝 0) := by
  have hb (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
      ∀ᵐ x ∂μ, ‖∫ s in Icc (0 : ℝ) t, U (s, x)‖ ^ 2 ≤
        t * ∫ s in Icc (0 : ℝ) 1, ‖U (s, x)‖ ^ 2 := by
    filter_upwards [hI.prod_left_ae] with x hx
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl ht1
    have hmem : MemLp (fun s => U (s, x)) 2 (volume.restrict (Icc (0 : ℝ) 1)) :=
      (memLp_two_iff_integrable_sq_norm
        (hU.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hx
    exact (endpoint_primitive_sq_bound ht
      (hmem.mono_measure (Measure.restrict_mono_set _ hsub))).trans
      (mul_le_mul_of_nonneg_left (setIntegral_mono_set hx
        (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ fun _ hx => hsub hx)) ht)
  have hi (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
      Integrable (fun x => ‖∫ s in Icc (0 : ℝ) t, U (s, x)‖ ^ 2) μ := by
    have hm : Measurable (fun x => ∫ s in Icc (0 : ℝ) t, U (s, x)) :=
      (hU.stronglyMeasurable.integral_prod_left'
        (μ := volume.restrict (Icc (0 : ℝ) t))).measurable
    apply (hI.integral_prod_right.const_mul t).mono' (hm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hb t ht ht1] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hx
  have hall (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :=
    integral_mono_ae (hi t ht ht1) (hI.integral_prod_right.const_mul t) (hb t ht ht1)
  refine ⟨fun t ht ht1 => ⟨hi t ht ht1, ?_⟩, ?_⟩
  · simpa only [integral_const_mul] using hall t ht ht1
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) _
    (by
      simpa only [NNReal.coe_zero, zero_mul] using
        ((NNReal.continuous_coe.tendsto 0).mul_const
          (∫ x, (∫ s in Icc (0 : ℝ) 1, ‖U (s, x)‖ ^ 2) ∂μ)))
  filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ≥0) < 1)] with t ht
  simpa only [integral_const_mul] using hall t t.coe_nonneg (by exact_mod_cast ht.le)

/-- One actual stationary primitive has a local strong-L2 initial trace on
one sample event, simultaneously for every compact spatial region. The trace
uses a coherent representative rather than point evaluations of L2 classes. -/
theorem short_time_stationary_primitive_local_strong_trace
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ s ω, F (s, ω) = f ω + ∫ v in Icc (0 : ℝ) s, U (v, ω)) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
        (∀ t : ℝ≥0, (t : ℝ) ≤ 1 →
          Integrable (fun x => ‖F (t, translate x ω) - f (translate x ω)‖ ^ 2)
            (volume.restrict K)) ∧
        Tendsto (fun t : ℝ≥0 =>
          ∫ x in K, ‖F (t, translate x ω) - f (translate x ω)‖ ^ 2)
          (𝓝 0) (𝓝 0) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨F, U, hF, hU, heF, heU, hprim⟩ := short_time_stationary_joint_primitive hP hfg
  refine ⟨F, U, hF, hU, heF, heU, hprim, ?_⟩
  have hI : Integrable (fun p => ‖U p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (reducedLaw Q)) :=
    endpoint_joint_sq_integrable
      ((((hP.2.2.1 g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hU heU
  have hloc := ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hI.ofReal
  filter_upwards [hloc] with ω hω
  intro K hK
  have hi : Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) := by
    exact (Integrable.iff_ofReal (𝕜 := ℂ)).mpr (hω K hK).swap
  have hm : Measurable (fun p : ℝ × Vec d => U (p.1, translate p.2 ω)) :=
    hU.comp (measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const)))
  obtain ⟨hbound, htrace⟩ := endpoint_local_primitive_trace (volume.restrict K) hm hi
  have he (t : ℝ) (x : Vec d) :
      F (t, translate x ω) - f (translate x ω) =
        ∫ v in Icc (0 : ℝ) t, U (v, translate x ω) := by
    rw [hprim, add_sub_cancel_left]
  refine ⟨fun t ht => ?_, ?_⟩
  · simpa only [he] using (hbound t t.coe_nonneg ht).1
  · simpa only [he] using htrace

/-- The actual stationary-minus-retained evolution has a local zero strong-L2
trace wherever the physical initial datum agrees with the stationary datum.
Only actual semigroup continuity is used for the retained orbit. -/
theorem short_time_stationary_retained_local_zero_trace
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F : ℝ × FieldPair d → ℂ, Measurable F ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
      ∀ (a : Vec d → Mat d)
        (Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup a i ζ Pr →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        Tendsto (fun t : ℝ≥0 =>
          ∫ x in K, ‖F (t, translate x ω) - (Pr t fr) x‖ ^ 2)
          (𝓝 0) (𝓝 0) := by
  obtain ⟨F, U, hF, _, heF, _, _, htrace⟩ :=
    short_time_stationary_primitive_local_strong_trace Q hP hfg
  refine ⟨F, hF, heF, ?_⟩
  filter_upwards [htrace] with ω hω
  intro K hK a Pr hPr fr hinit
  obtain ⟨hFi, hFt⟩ := hω K hK
  have hphys (t : ℝ≥0) :
      Integrable (fun x => ‖(Pr t fr) x - fr x‖ ^ 2) volume ∧
      (∫ x, ‖(Pr t fr) x - fr x‖ ^ 2) = ‖Pr t fr - fr‖ ^ 2 := by
    have he := Lp.coeFn_sub (Pr t fr) fr
    have hi := (Lp.memLp (Pr t fr - fr)).norm.integrable_sq
    have he' : (fun x => ‖(Pr t fr - fr) x‖ ^ 2) =ᵐ[volume]
        (fun x => ‖(Pr t fr) x - fr x‖ ^ 2) := by
      filter_upwards [he] with x hx
      rw [hx]
      rfl
    refine ⟨hi.congr he', ?_⟩
    rw [← integral_congr_ae he', ← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  have hupper (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) :
      (∫ x in K, ‖F (t, translate x ω) - (Pr t fr) x‖ ^ 2) ≤
        2 * (∫ x in K, ‖F (t, translate x ω) - f (translate x ω)‖ ^ 2) +
        2 * ‖Pr t fr - fr‖ ^ 2 := by
    have hBi : Integrable (fun x => ‖(Pr t fr) x - fr x‖ ^ 2) (volume.restrict K) :=
      (hphys t).1.mono_measure (Measure.restrict_le_self)
    have hb : ∀ᵐ x ∂volume.restrict K,
        ‖F (t, translate x ω) - (Pr t fr) x‖ ^ 2 ≤
          2 * ‖F (t, translate x ω) - f (translate x ω)‖ ^ 2 +
          2 * ‖(Pr t fr) x - fr x‖ ^ 2 := by
      filter_upwards [hinit] with x hx
      have hn := norm_sub_le_norm_sub_add_norm_sub
        (F (t, translate x ω)) (f (translate x ω)) ((Pr t fr) x)
      rw [hx, norm_sub_rev (fr x)] at hn
      rw [hx]
      have hn2 := (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
      nlinarith [sq_nonneg (‖F (t, translate x ω) - fr x‖ - ‖(Pr t fr) x - fr x‖),
        norm_nonneg (F (t, translate x ω) - (Pr t fr) x), norm_nonneg ((Pr t fr) x - fr x),
        norm_nonneg (F (t, translate x ω) - fr x)]
    have hmajor := ((hFi t ht).const_mul 2).add (hBi.const_mul 2)
    have hm : AEStronglyMeasurable
        (fun x => ‖F (t, translate x ω) - (Pr t fr) x‖ ^ 2) (volume.restrict K) := by
      have hshift : Measurable (fun x : Vec d => ((t : ℝ), translate x ω)) :=
        measurable_const.prodMk (Probability.continuous_translate.measurable.comp
          (measurable_id.prodMk measurable_const))
      exact (((hF.comp hshift).sub
        (Lp.stronglyMeasurable (Pr t fr)).measurable).norm.pow_const 2).aestronglyMeasurable
    have hi := hmajor.mono' hm (hb.mono fun x hx => by
      rwa [Real.norm_of_nonneg (sq_nonneg _)])
    calc
      _ ≤ ∫ x in K, 2 * ‖F (t, translate x ω) - f (translate x ω)‖ ^ 2 +
          2 * ‖(Pr t fr) x - fr x‖ ^ 2 := integral_mono_ae hi hmajor hb
      _ = 2 * (∫ x in K, ‖F (t, translate x ω) - f (translate x ω)‖ ^ 2) +
          2 * (∫ x in K, ‖(Pr t fr) x - fr x‖ ^ 2) := by
        rw [integral_add ((hFi t ht).const_mul 2) (hBi.const_mul 2), integral_const_mul,
          integral_const_mul]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        ((setIntegral_le_integral (s := K) (hphys t).1 (ae_of_all _ fun _ => sq_nonneg _)).trans_eq
          (hphys t).2) (show (0 : ℝ) ≤ 2 by norm_num))
  have hpt : Tendsto (fun t : ℝ≥0 => ‖Pr t fr - fr‖ ^ 2) (𝓝 0) (𝓝 0) := by
    have h := (((hPr.2.2.1 fr).tendsto 0).sub_const fr).norm.pow 2
    simpa only [hPr.1, ContinuousLinearMap.id_apply, sub_self, norm_zero, zero_pow
      (by norm_num : (2 : ℕ) ≠ 0)] using h
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) _
    (by simpa only [mul_zero, add_zero] using (hFt.const_mul 2).add (hpt.const_mul 2))
  filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ≥0) < 1)] with t ht
  exact hupper t (by exact_mod_cast ht.le)


/-- A time primitive supported to the right of zero has no boundary mass at
zero. The weak identity allows tests which do not vanish at zero. -/
private theorem endpoint_zero_extension_primitive
    {D : ℝ → ℂ} (hD : IntegrableOn D (Icc (0 : ℝ) 1)) :
    let Y := (Ioc (0 : ℝ) 1).indicator D
    let X := fun t : ℝ => ∫ s in Icc (0 : ℝ) t, Y s
    (∀ t : ℝ, t ≤ 0 → X t = 0) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → X t = ∫ s in Icc (0 : ℝ) t, D s) ∧
    ∀ L : ℂ →L[ℝ] ℝ,
      AbsolutelyContinuousOnInterval (fun t => L (X t)) (-1) 1 ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
        (∫ t in (-1 : ℝ)..1, deriv ψ t * L (X t) + ψ t * L (Y t)) = 0 := by
  intro Y X
  have hY : Integrable Y :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (hD.mono_set Ioc_subset_Icc_self)
  have he (t : ℝ) : X t = ∫ s in (0 : ℝ)..t, Y s := by
    by_cases ht : 0 ≤ t
    · rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
    · have ht' : t < 0 := lt_of_not_ge ht
      have hz : ∫ s in Ioc t (0 : ℝ), Y s = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro s hs
        exact indicator_of_notMem (fun h => (not_lt_of_ge hs.2) h.1) _
      simp only [X, Icc_eq_empty_of_lt ht', Measure.restrict_empty, integral_zero_measure,
        intervalIntegral.integral_of_ge ht'.le, hz, neg_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    by_cases ht' : t = 0
    · subst t
      simp [X]
    · simp only [X, Icc_eq_empty_of_lt (lt_of_le_of_ne ht ht'), Measure.restrict_empty, integral_zero_measure]
  · intro t ht ht1
    rw [he, intervalIntegral.integral_of_le ht, integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change (Ioc (0 : ℝ) 1).indicator D s = D s
    simp only [indicator_of_mem (show s ∈ Ioc (0 : ℝ) 1 from ⟨hs.1, hs.2.trans ht1⟩)]
  · intro L
    have hLY : Integrable (fun t => L (Y t)) := L.integrable_comp hY
    have hcomm (t : ℝ) : L (X t) = ∫ s in (0 : ℝ)..t, L (Y s) := by
      rw [he, L.intervalIntegral_comp_comm hY.intervalIntegrable]
    have hac : AbsolutelyContinuousOnInterval (fun t => L (X t)) (-1) 1 := by
      simp only [hcomm]
      exact hLY.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
        (by norm_num [uIcc_of_le])
    refine ⟨hac, ?_⟩
    intro ψ hψ hψa hψb
    have hψac := hψ.contDiffOn.absolutelyContinuousOnInterval (a := (-1 : ℝ)) (b := 1)
    have hprod := hψac.integral_deriv_mul_eq_sub hac
    have hd : ∀ᵐ t ∂volume, deriv (fun s => L (X s)) t = L (Y t) := by
      have hdiff := LocallyIntegrable.ae_hasDerivAt_integral hLY.locallyIntegrable
      filter_upwards [hdiff] with t ht
      simpa only [hcomm] using (ht 0).deriv
    have hi : (∫ t in (-1 : ℝ)..1, deriv ψ t * L (X t) + ψ t * L (Y t)) =
        ∫ t in (-1 : ℝ)..1, deriv ψ t * L (X t) + ψ t * deriv (fun s => L (X s)) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hd] with t ht _
      rw [ht]
    rw [hi, hprod, hψa, hψb, zero_mul, zero_mul, sub_self]


/-- An actual stationary-minus-retained evolution has a measurable temporal
zero extension near zero. On every region where the initial data agree, its
real projections satisfy the weak time identity across zero, without a
boundary term at zero. The retained datum is in the actual generator graph. -/
theorem short_time_stationary_retained_temporal_zero_extension
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      ∀ (a : Vec d → Mat d)
        (Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup a i ζ Pr →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair a i ζ fr gr →
      ∃ V Z X Y : ℝ × Vec d → ℂ,
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          ∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0 := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨F, U, hF, hU, heF, heU, hprim⟩ := short_time_stationary_joint_primitive hP hfg
  refine ⟨F, U, hF, hU, heF, heU, ?_⟩
  have hI : Integrable (fun p => ‖U p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (reducedLaw Q)) :=
    endpoint_joint_sq_integrable
      ((((hP.2.2.1 g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hU heU
  have hIU : Integrable U ((volume.restrict (Icc (0 : ℝ) 1)).prod (reducedLaw Q)) :=
    ((memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mpr hI).integrable (by norm_num)
  filter_upwards [ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hIU] with ω hω
  intro a Pr hPr fr gr hfr
  obtain ⟨V, Z, hV, hZ, heV, heZ, hprimR⟩ := short_time_physical_joint_primitive hPr hfr
  let Y : ℝ × Vec d → ℂ := fun p => (Ioc (0 : ℝ) 1).indicator
    (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1
  let X : ℝ × Vec d → ℂ := fun p => ∫ s in Icc (0 : ℝ) p.1, Y (s, p.2)
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hY : Measurable Y := by
    exact Measurable.ite (measurableSet_Ioc.preimage measurable_fst)
      ((hU.comp hshift).sub hZ) measurable_const
  have hX : Measurable X := measurable_complexPrimitive hY 0
  refine ⟨V, Z, X, Y, hV, hZ, hX, hY, heV, heZ, fun _ => rfl, ?_, ?_⟩
  · intro s hs x
    by_cases hs' : s = 0
    · subst s
      simp [X]
    · simp only [X, Icc_eq_empty_of_lt (lt_of_le_of_ne hs hs'),
        Measure.restrict_empty, integral_zero_measure]
  · have hZI : Integrable (fun p => ‖Z p‖ ^ 2)
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume : Measure (Vec d))) :=
      endpoint_joint_sq_integrable
        ((((hPr.2.2.1 gr).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
          isCompact_Icc) hZ heZ
    have hZtime : ∀ᵐ x ∂(volume : Measure (Vec d)),
        IntegrableOn (fun s => Z (s, x)) (Icc (0 : ℝ) 1) := by
      filter_upwards [hZI.prod_left_ae] with x hx
      exact ((memLp_two_iff_integrable_sq_norm
        (hZ.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hx).integrable
          (by norm_num)
    intro K hK hinit
    have htime : ∀ᵐ x ∂volume.restrict K,
        IntegrableOn (fun s => U (s, translate x ω) - Z (s, x)) (Icc (0 : ℝ) 1) := by
      filter_upwards [(hω K hK).prod_right_ae, ae_restrict_of_ae hZtime] with x hx hz
      exact hx.sub hz
    refine ⟨?_, ?_⟩
    · intro s hs hs1
      filter_upwards [htime, hinit, (hω K hK).prod_right_ae,
        ae_restrict_of_ae hZtime] with x hx hix hu hz
      have he := (endpoint_zero_extension_primitive hx).2.1 s hs hs1
      change (∫ t in Icc (0 : ℝ) s,
        (Ioc (0 : ℝ) 1).indicator (fun v => U (v, translate x ω) - Z (v, x)) t) = _
      dsimp only at he
      rw [he, hprim, hprimR, hix]
      have hu' : IntegrableOn (fun t => U (t, translate x ω)) (Icc (0 : ℝ) 1) := hu
      have hz' : IntegrableOn (fun t => Z (t, x)) (Icc (0 : ℝ) 1) := hz
      rw [integral_sub (hu'.mono_set (Icc_subset_Icc le_rfl hs1))
        (hz'.mono_set (Icc_subset_Icc le_rfl hs1))]
      ring
    · filter_upwards [htime] with x hx
      exact (endpoint_zero_extension_primitive hx).2.2


/-- The actual retained difference has one temporal zero extension and one
continuous physical gradient orbit. On the same event and with the same
representatives, its positive-time spatial residual uses exactly the derivative
in the weak time identity. The initial agreement is imposed only on the compact
set where the zero extension represents the difference. -/
theorem short_time_stationary_retained_coherent_weak_equations
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ Measurable U ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ χ : C(Vec d, ℝ), (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∃ V Z X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pr s.toNNReal fr) (H s)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakGradient Set.univ (fun x => L (F (s, translate x ω)))
            (fun x j => L (D j (s, translate x ω))) ∧
          HasWeakDivergence Set.univ
            (fun x j => L ((1 / 2 : ℂ) *
              (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (D k (s, translate x ω) - H s k x)) +
              EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
                (fun k => D k (s, translate x ω)) j))
            (fun x => L (Y (s, x) -
              EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
                (fun k => D k (s, translate x ω)) i ζ -
              ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (D j (s, translate x ω) - H s j x))))) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          ∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0 := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨F, U, hF, hU, heF, heU, htime⟩ :=
    short_time_stationary_retained_temporal_zero_extension Q hP hfg
  obtain ⟨D, hD, heD⟩ := hP.exists_joint_gradient_representative f
  refine ⟨F, U, D, hF, hU, hD, heF, heU, heD, ?_⟩
  have hres := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae
      (short_time_joint_actual_retained_spatial_residual Q hP hfg U D hU hD heU heD))
  have hgrad := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae
      (short_time_joint_stationary_spatial_gradient Q hP f F D hF hD heF heD))
  filter_upwards [htime, hres, hgrad, c4_ae_reduced_physical_elliptic Q]
    with ω ht hr hg hA
  intro χ hχ Pr hPr fr gr hfr
  obtain ⟨V, Z, X, Y, hV, hZ, hX, hY, heV, heZ, heY, hX0, hlocal⟩ :=
    ht (ForcedLocality.retainedPair χ ω).1 Pr hPr fr gr hfr
  have hmap (s : ℝ≥0) : IsPhysicalComplexGeneratorPair
      (ForcedLocality.retainedPair χ ω).1 i ζ (Pr s fr) (Pr s gr) := by
    apply (hPr.2.2.2 _ _).mp
    have h := ((Pr s).continuous.tendsto gr).comp ((hPr.2.2.2 fr gr).mpr hfr)
    convert h using 1
    ext t
    simp only [Function.comp_apply, map_smul, map_sub]
    have hc : Pr s (Pr t fr) = Pr t (Pr s fr) := by
      rw [← ContinuousLinearMap.comp_apply, ← hPr.2.1, add_comm,
        hPr.2.1, ContinuousLinearMap.comp_apply]
    rw [hc]
  let Λ := Real.exp (2 * Λ₀) * Λ₀
  have hΛ1 : 1 ≤ Λ := by
    have he : 1 ≤ Real.exp (2 * Λ₀) := Real.one_le_exp
      (mul_nonneg (by norm_num) (zero_le_one.trans Q.ellipticity_parameter))
    exact (one_le_mul_of_one_le_of_one_le he Q.ellipticity_parameter)
  have hΛ : 0 < Λ := zero_lt_one.trans_le hΛ1
  have har (x : Vec d) : S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ :=
    endpoint_retained_elliptic χ ω x (s5Elliptic_of_isElliptic hΛ1 hA x)
      (hχ x).1 (hχ x).2
  have ha (j k : Fin d) :
      MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ)) ∞ volume := by
    apply memLp_top_of_bound
      (Complex.continuous_ofReal.comp
        ((ForcedLocality.retainedPair χ ω).1.continuous.matrix_elem j k)).aestronglyMeasurable Λ
    exact ae_of_all _ fun x => by
      change ‖((ForcedLocality.retainedPair χ ω).1 x j k : ℂ)‖ ≤ Λ
      simpa only [Complex.norm_real, Real.norm_eq_abs] using (har x).entry_abs_le j k
  obtain ⟨H, hH, hHc⟩ := physical_generator_orbit_continuous_gradient
    (ForcedLocality.retainedPair χ ω).1 i ζ ha hΛ (ae_of_all _ har)
      (fun s : ℝ => Pr s.toNNReal fr) (fun s : ℝ => Pr s.toNNReal gr)
      ((hPr.2.2.1 fr).comp continuous_real_toNNReal)
      ((hPr.2.2.1 gr).comp continuous_real_toNNReal) (fun s => hmap s.toNNReal)
  refine ⟨V, Z, X, Y, H, hV, hZ, hX, hY, heV, heZ, heY, hX0, hHc, hH, ?_, hlocal⟩
  have hr' := ae_restrict_of_ae_restrict_of_subset
    (show Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) from Ioc_subset_Ioi_self) hr
  have hg' := ae_restrict_of_ae_restrict_of_subset
    (show Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) from Ioc_subset_Ioi_self) hg
  filter_upwards [hr', hg', ae_restrict_mem measurableSet_Ioc] with s hrs hgs hs
  intro L
  refine ⟨hgs L, ?_⟩
  obtain ⟨J, hJ, hdiv⟩ := hrs χ hχ (Pr s.toNNReal fr) (Pr s.toNNReal gr) (hmap s.toNNReal)
  have heH := physicalH1Graph_gradient_unique volume (Or.inl rfl)
    (Pr s.toNNReal fr) J (H s) hJ (hH s)
  rw [heH] at hdiv
  apply Correctors.hasWeakDivergence_congr_ae isOpen_univ (hdiv L)
  · exact Filter.EventuallyEq.rfl
  · rw [Measure.restrict_univ]
    filter_upwards [heZ s] with x hx
    rw [heY, indicator_of_mem hs, hx]
    rfl


/-- The actual forward and clock retained comparison has a deterministic
Gaussian right-hand side. Both constants precede the law and force, and the
forcing uses the same gradient representative as the finite comparison. -/
theorem short_time_forward_clock_actual_gaussian_comparison
    (d : ℕ) (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (hB : 0 < B) :
    ∃ M K : ℝ, 0 < M ∧ 0 < K ∧
    ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
    let γ := 16 * Λ ^ 3 * B ^ 2 + 1
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ L : ℝ, 64 * Λ ^ 3 ≤ L →
    ∀ᵐ ω ∂reducedLaw Q, ∀ (χ : C(Vec d, ℝ)) (ρ : ℝ), 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → HasCompactSupport χ →
      (∀ x, euclideanNorm x ≤ ρ → χ x = 1) →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
        (fr : Vec d → ℂ) =ᵐ[volume] (fun x => (χ x : ℂ) * f (translate x ω)) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr →
      Real.exp (-γ * (t : ℝ)) *
        (∫ x, Real.exp (-euclideanSq x / (L * (2 - (t : ℝ)))) ^ 2 *
          ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2) ≤
      Real.exp (-ρ ^ 2 / (2 * L)) *
        (M ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))) +
          (4 * Λ + 16 / L + 1) * K *
            (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L)))) := by
  obtain ⟨M₀, hM₀, hb⟩ := EndpointFiniteP.observation_bounds d S
  obtain ⟨K, hK, hforce⟩ := short_time_forward_clock_actual_retained_forcing_energy d hd S B hB
  let M := M₀ * (1 + B)
  refine ⟨M, K, by dsimp [M]; positivity, hK, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P hP ν f Λ γ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨hβb, hab, hμb⟩ := hb Q hQ β a μ hβ ha hμ
  have hfb : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ M := by
    cases ν with
    | inl j =>
      filter_upwards [hβb j, hab ⟨0, by omega⟩ j,
        Lp.coeFn_add (β j) (ζ • a ⟨0, by omega⟩ j),
        Lp.coeFn_smul ζ (a ⟨0, by omega⟩ j)] with ω hβω haω hadd hsmul
      change ‖(β j + ζ • a ⟨0, by omega⟩ j) ω‖ ≤ M
      rw [hadd]
      change ‖β j ω + (ζ • a ⟨0, by omega⟩ j) ω‖ ≤ M
      rw [hsmul]
      change ‖β j ω + ζ * a ⟨0, by omega⟩ j ω‖ ≤ M
      calc
        _ ≤ ‖β j ω‖ + ‖ζ‖ * ‖a ⟨0, by omega⟩ j ω‖ := by
          simpa only [norm_mul] using norm_add_le (β j ω) (ζ * a ⟨0, by omega⟩ j ω)
        _ ≤ M₀ + B * M₀ := add_le_add hβω (mul_le_mul hζ haω (norm_nonneg _) hB.le)
        _ = M := by dsimp only [M]; ring
    | inr u =>
      filter_upwards [hμb, Lp.coeFn_smul ζ μ] with ω hμω hsmul
      change ‖(ζ • μ) ω‖ ≤ M
      rw [hsmul]
      change ‖ζ * μ ω‖ ≤ M
      rw [norm_mul]
      exact (mul_le_mul hζ hμω (norm_nonneg _) hB.le).trans
        (by dsimp only [M]; nlinarith)
  have hfsp : ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      ‖f (translate x ω)‖ ≤ M := by
    apply (Measure.ae_ae_comm ?_).mp (ae_of_all _ fun x =>
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae hfb)
    exact measurableSet_le (((Lp.stronglyMeasurable f).measurable.comp
      Probability.continuous_translate.measurable).norm) measurable_const
  obtain ⟨D, hD, heD, hcomp⟩ :=
    short_time_forward_clock_retained_cutoff_comparison hd S Q hQ β a μ hβ ha hμ hP B hζ ν
  intro t ht L hL
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one S.one_le_ellipticity)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  filter_upwards [hfsp, hcomp t ht,
    hforce Q hQ β a μ hβ ha hμ ζ hζ P hP ν D hD heD t ht L hL] with ω hf hc hs
  intro χ ρ hρ hχ hcompact hin fr hfr Pr hPr
  obtain ⟨fr₀, hfr₀, hcompare⟩ := hc χ hχ hcompact
  have hefr : fr = fr₀ := Lp.ext (hfr.trans hfr₀.symm)
  subst fr₀
  obtain ⟨hi, hsource⟩ := hs χ ρ hρ hχ (fun x hx => hin x hx.le)
  let F : Fin d → ℝ × Vec d → ℂ := fun j p =>
    EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω p.2
      (fun k => D k (p.1, translate p.2 ω)) j
  let G : ℝ × Vec d → ℂ := fun p =>
    EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω p.2
      (fun k => D k (p.1, translate p.2 ω)) ⟨0, by omega⟩ ζ
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hDj (j : Fin d) := (hD j).comp hshift
  have hcoeff (j k : Fin d) : Measurable (fun p : ℝ × Vec d =>
      ((ω.1 p.2 j k - (ForcedLocality.retainedPair χ ω).1 p.2 j k : ℝ) : ℂ)) :=
    ((Complex.continuous_ofReal.comp ((ω.1.continuous.matrix_elem j k).sub
      ((ForcedLocality.retainedPair χ ω).1.continuous.matrix_elem j k))).measurable).comp
        measurable_snd
  have hF : ∀ j, Measurable (F j) := by
    intro j
    exact measurable_const.mul (Finset.measurable_sum _ (fun k _ => (hcoeff j k).mul (hDj k)))
  have hG : Measurable G :=
    measurable_const.mul (Finset.measurable_sum _ (fun j _ =>
      (hcoeff j ⟨0, by omega⟩).mul (hDj j)))
  have hu : Measurable (fun x => f (translate x ω)) :=
    (Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  have hbound := short_time_cutoff_comparison_gaussian_rhs_bound t ht L Λ γ ρ M K
    hLp hΛ.le hγ hρ (fun x => f (translate x ω)) hu hf χ hχ hin F G hF hG hi hsource
  exact (hcompare Pr hPr L hL).2.trans hbound.2.2



/-- A single deterministic Gaussian scale gives the actual forward and clock
comparison an undamped exponential radius bound, uniformly down to time zero. -/
theorem short_time_forward_clock_actual_gaussian_decay
    (d : ℕ) (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (hB : 0 < B) :
    let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
    ∃ L K c : ℝ, 64 * Λ ^ 3 ≤ L ∧ 0 < L ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (ρ : ℝ), 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → HasCompactSupport χ →
      (∀ x, euclideanNorm x ≤ ρ → χ x = 1) →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
        (fr : Vec d → ℂ) =ᵐ[volume] (fun x => (χ x : ℂ) * f (translate x ω)) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr →
      (∫ x, Real.exp (-euclideanSq x / (L * (2 - (t : ℝ)))) ^ 2 *
        ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2) ≤
        K * Real.exp (-c * ρ ^ 2) := by
  intro Λ
  obtain ⟨M, K₀, hM, hK₀, hbound⟩ :=
    short_time_forward_clock_actual_gaussian_comparison d hd S B hB
  let L := 64 * Λ ^ 3 + 1
  let γ := 16 * Λ ^ 3 * B ^ 2 + 1
  let A := M ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))) +
    (4 * Λ + 16 / L + 1) * K₀ *
      (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L)))
  let K := Real.exp γ * (A + 1)
  let c := 1 / (2 * L)
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one S.one_le_ellipticity)
  have hL : 0 < L := by dsimp only [L]; positivity
  have hscale : 64 * Λ ^ 3 ≤ L := by dsimp only [L]; linarith
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  have hA : 0 ≤ A := by
    have hI₂ : 0 ≤ ∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L)) :=
      integral_nonneg (fun _ => Real.exp_nonneg _)
    have hI₄ : 0 ≤ ∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L)) :=
      integral_nonneg (fun _ => Real.exp_nonneg _)
    dsimp only [A]
    positivity
  refine ⟨L, K, c, hscale, hL, by dsimp only [K]; positivity,
    by dsimp only [c]; positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P hP ν f t ht
  filter_upwards [hbound Q hQ β a μ hβ ha hμ ζ hζ P hP ν t ht L hscale] with ω hw
  intro χ ρ hρ hχ hcompact hin fr hfr Pr hPr
  have hw' := hw χ ρ hρ hχ hcompact hin fr hfr Pr hPr
  have he : -ρ ^ 2 / (2 * L) = -c * ρ ^ 2 := by dsimp only [c]; ring
  rw [he] at hw'
  have hexp : Real.exp (γ * (t : ℝ)) ≤ Real.exp γ :=
    Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left ht hγ])
  calc
    _ = Real.exp (γ * (t : ℝ)) *
        (Real.exp (-γ * (t : ℝ)) *
          (∫ x, Real.exp (-euclideanSq x / (L * (2 - (t : ℝ)))) ^ 2 *
            ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2)) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp only [neg_mul, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (γ * (t : ℝ)) * (Real.exp (-c * ρ ^ 2) * A) :=
      mul_le_mul_of_nonneg_left hw' (Real.exp_nonneg _)
    _ ≤ Real.exp γ * (Real.exp (-c * ρ ^ 2) * A) :=
      mul_le_mul_of_nonneg_right hexp (mul_nonneg (Real.exp_nonneg _) hA)
    _ ≤ Real.exp γ * (Real.exp (-c * ρ ^ 2) * (A + 1)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = K * Real.exp (-c * ρ ^ 2) := by dsimp only [K]; ring



/-- Joint representatives of physical L² paths on infinite volume. -/
private theorem endpoint_physical_joint_l2_representative {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω}
    {u : T → Lp ℂ 2 μ} (hu : StronglyMeasurable u) :
    ∃ U : T × Ω → ℂ, Measurable U ∧ ∀ t, (fun ω => U (t, ω)) =ᵐ[μ] u t := by
  obtain ⟨v, hv, herr⟩ := StronglyMeasurable.exists_joint_l2_approx hu
  let U : T × Ω → ℂ := fun p =>
    (limsup (fun n => (v n p.1 p.2).re) atTop : ℝ) +
      (limsup (fun n => (v n p.1 p.2).im) atTop : ℝ) * Complex.I
  have hUm : Measurable U :=
    (Complex.measurable_ofReal.comp (.limsup fun n => Complex.measurable_re.comp (hv n))).add
      ((Complex.measurable_ofReal.comp (.limsup fun n => Complex.measurable_im.comp (hv n))).mul
        measurable_const)
  refine ⟨U, hUm, fun t => ?_⟩
  have hB : (∑' n : ℕ, ENNReal.ofReal (4 * (1 / 2 : ℝ) ^ n)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (summable_geometric_two.mul_left 4)]
    exact ENNReal.ofReal_ne_top
  have hca : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm ((fun ω => v n t ω) - (fun ω => v m t ω)) 2 μ <
        ENNReal.ofReal (4 * (1 / 2 : ℝ) ^ N) := by
    intro N n m hn hm
    rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm, ← Lp.enorm_def, ← ofReal_norm]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    have hnm : ‖v n t - v m t‖ ≤ ‖v n t - u t‖ + ‖v m t - u t‖ :=
      by simpa only [norm_sub_rev (u t) (v m t)] using!
        norm_sub_le_norm_sub_add_norm_sub (v n t) (u t) (v m t)
    have hnN : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    have hmN : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    have hpos : 0 < (1 / 2 : ℝ) ^ N := by positivity
    linarith [herr n t, herr m t]
  have hlim := Lp.ae_tendsto_of_cauchy_eLpNorm
    (fun n => Lp.aestronglyMeasurable (v n t)) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hB hca
  have hpoint : ∀ᵐ ω ∂μ, Tendsto (fun n => v n t ω) atTop (𝓝 (U (t, ω))) := by
    filter_upwards [hlim] with ω hω
    obtain ⟨z, hz⟩ := hω
    have hre := (Complex.continuous_re.tendsto z |>.comp hz).limsup_eq
    have him := (Complex.continuous_im.tendsto z |>.comp hz).limsup_eq
    simp only [Function.comp_def] at hre him
    have he : U (t, ω) = z := by
      dsimp only [U]
      rw [hre, him, Complex.re_add_im]
    rw [he]
    exact hz
  have hvlim : Tendsto (fun n => v n t) atTop (𝓝 (u t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (herr n t).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hvlim).exists_seq_tendsto_ae
  filter_upwards [hpoint, hae] with ω hω hω'
  exact tendsto_nhds_unique (hω.comp hns.tendsto_atTop) hω'


/-- The coherent actual equations use one jointly measurable retained gradient,
whose square is integrable on every compact time interval and all of space. -/
theorem short_time_stationary_retained_joint_weak_equations
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ Measurable U ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      (∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : ℝ × Vec d => ‖F (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        ∀ j, Integrable (fun p : ℝ × Vec d => ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K))) ∧
      ∀ χ : C(Vec d, ℝ), (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∃ V Z X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∃ W : Fin d → ℝ × Vec d → ℂ,
        (∀ j, Measurable (W j)) ∧
        (∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j) ∧
        (∀ (j : Fin d) (l r : ℝ), Integrable (fun p => ‖W j p‖ ^ 2)
          ((volume.restrict (Icc l r)).prod volume)) ∧
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pr s.toNNReal fr) (H s)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakGradient Set.univ (fun x => L (F (s, translate x ω)))
            (fun x j => L (D j (s, translate x ω))) ∧
          HasWeakDivergence Set.univ
            (fun x j => L ((1 / 2 : ℂ) *
              (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (D k (s, translate x ω) - W k (s, x))) +
              EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
                (fun k => D k (s, translate x ω)) j))
            (fun x => L (Y (s, x) -
              EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
                (fun k => D k (s, translate x ω)) i ζ -
              ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (D j (s, translate x ω) - W j (s, x)))))) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          ∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0 := by
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_stationary_retained_coherent_weak_equations Q hP hfg
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hfi := endpoint_joint_sq_integrable
    ((((hP.2.2.1 f).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      (μ := volume) (K := Icc (0 : ℝ) 1) isCompact_Icc) hF heF
  have hui := endpoint_joint_sq_integrable
    ((((hP.2.2.1 g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      (μ := volume) (K := Icc (0 : ℝ) 1) isCompact_Icc) hU heU
  obtain ⟨G, hGc, hG⟩ := hP.exists_continuous_gradient_orbit hfg
  have hdi (j : Fin d) : Integrable (fun p => ‖D j p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (reducedLaw Q)) := by
    apply endpoint_joint_sq_integrable (u := fun s => (hP.gradientOrbit f s) j)
      _ (hD j) (heD j)
    have hj : Continuous (fun s : ℝ => G s j) := by fun_prop
    have hi := (hj.norm.pow 2).continuousOn.integrableOn_compact
      (μ := volume) (K := Icc (0 : ℝ) 1) isCompact_Icc
    change Integrable (fun s : ℝ => ‖G s j‖ ^ 2)
      (volume.restrict (Icc (0 : ℝ) 1)) at hi
    rw [← restrict_Ioc_eq_restrict_Icc] at hi ⊢
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [(hP.gradientOrbit_spec f hs.1).unique (hG s)]
  have hfLoc := ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hfi.ofReal
  have huLoc := ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hui.ofReal
  have hdLoc := ae_all_iff.mpr (fun j =>
    ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
      (reducedLaw_stationary Q) (hdi j).ofReal)
  refine ⟨F, U, D, hF, hU, hD, heF, heU, heD, ?_⟩
  filter_upwards [hcoh, hfLoc, huLoc, hdLoc] with ω hω hfω huω hdω
  refine ⟨?_, ?_⟩
  · intro K hK
    refine ⟨(Integrable.iff_ofReal (𝕜 := ℂ)).mpr (hfω K hK).swap,
      (Integrable.iff_ofReal (𝕜 := ℂ)).mpr (huω K hK).swap, ?_⟩
    intro j
    exact (Integrable.iff_ofReal (𝕜 := ℂ)).mpr (hdω j K hK).swap
  intro χ hχ Pr hPr fr gr hfr
  obtain ⟨V, Z, X, Y, H, hV, hZ, hX, hY, heV, heZ, heY, hX0, hHc, hH, hres, hlocal⟩ :=
    hω χ hχ Pr hPr fr gr hfr
  have hex (j : Fin d) :=
    endpoint_physical_joint_l2_representative (hHc j).stronglyMeasurable
  choose W hW heW using hex
  have hi (j : Fin d) (l r : ℝ) : Integrable (fun p => ‖W j p‖ ^ 2)
      ((volume.restrict (Icc l r)).prod volume) := by
    apply endpoint_joint_sq_integrable
      (((hHc j).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
      (hW j) (heW j)
  refine ⟨V, Z, X, Y, H, W, hW, heW, hi, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, ?_, hlocal⟩
  filter_upwards [hres] with s hs
  intro L
  refine ⟨(hs L).1, ?_⟩
  have he : ∀ᵐ x ∂volume, ∀ j, W j (s, x) = H s j x :=
    ae_all_iff.mpr (fun j => heW j s)
  apply Correctors.hasWeakDivergence_congr_ae isOpen_univ (hs L).2
  · rw [Measure.restrict_univ]
    filter_upwards [he] with x hx
    simp only [hx]
  · rw [Measure.restrict_univ]
    filter_upwards [he] with x hx
    simp only [hx]


/-- On every retained interior, the actual coherent residual extends by zero
through initial time and satisfies the homogeneous spatial equation there. -/
theorem short_time_stationary_retained_zero_extended_interior_equations
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ Measurable U ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      (∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : ℝ × Vec d => ‖F (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        ∀ j, Integrable (fun p : ℝ × Vec d => ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K))) ∧
      ∀ χ : C(Vec d, ℝ), (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∃ V Z X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∃ W : Fin d → ℝ × Vec d → ℂ,
        (∀ j, Measurable (W j)) ∧
        (∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j) ∧
        (∀ (j : Fin d) (l r : ℝ), Integrable (fun p => ‖W j p‖ ^ 2)
          ((volume.restrict (Icc l r)).prod volume)) ∧
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pr s.toNNReal fr) (H s)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakGradient Set.univ (fun x => L (F (s, translate x ω)))
            (fun x j => L (D j (s, translate x ω))) ∧
          HasWeakDivergence Set.univ
            (fun x j => L ((1 / 2 : ℂ) *
              (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (D k (s, translate x ω) - W k (s, x))) +
              EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
                (fun k => D k (s, translate x ω)) j))
            (fun x => L (Y (s, x) -
              EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
                (fun k => D k (s, translate x ω)) i ζ -
              ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (D j (s, translate x ω) - W j (s, x)))))) ∧
        (∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          ∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0 ) ∧
        (∀ A : Set (Vec d), MeasurableSet A → (∀ x ∈ A, χ x = 1) →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakDivergence A
            (fun x j => L ((1 / 2 : ℂ) *
              ∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D k (t, translate x ω) - W k (t, x)) s))
            (fun x => L (Y (s, x) - ζ *
              ∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D j (t, translate x ω) - W j (t, x)) s)) ) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1),
          HasWeakGradient K (fun x => (X (s, x)).re)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).re) ∧
          HasWeakGradient K (fun x => (X (s, x)).im)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).im) := by
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_stationary_retained_joint_weak_equations Q hP hfg
  refine ⟨F, U, D, hF, hU, hD, heF, heU, heD, ?_⟩
  filter_upwards [hcoh] with ω hω
  refine ⟨hω.1, ?_⟩
  intro χ hχ Pr hPr fr gr hfr
  obtain ⟨V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, hlocal⟩ := hω.2 χ hχ Pr hPr fr gr hfr
  refine ⟨V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, hlocal, ?_, ?_⟩
  · intro A hA hχA
    have hr := (ae_restrict_iff' measurableSet_Ioc).mp hres
    filter_upwards [ae_restrict_of_ae hr] with s hs
    intro L
    by_cases ht : s ∈ Ioc (0 : ℝ) 1
    · apply (HasWeakDivergence.restrict_subset (Set.subset_univ A)
        MeasurableSet.univ (hs ht L).2).congr_ae
      · filter_upwards [ae_restrict_mem hA] with x hx
        funext j
        obtain ⟨hf, _⟩ := EinsteinFull.C9ShortTimeLocality.retainedDefects_eq_zero
          χ ω (hχA x hx) (fun k => D k (s, translate x ω)) i ζ
        simp only [indicator_of_mem ht, hf j, add_zero]
      · filter_upwards [ae_restrict_mem hA] with x hx
        obtain ⟨_, hb⟩ := EinsteinFull.C9ShortTimeLocality.retainedDefects_eq_zero
          χ ω (hχA x hx) (fun k => D k (s, translate x ω)) i ζ
        simp only [indicator_of_mem ht, hb, sub_zero]
    · have hz : HasWeakDivergence A (fun _ _ => 0) (fun _ => 0) := by
        convert hasWeakDivergence_zero (d := d) A using 1
      simpa only [heY, indicator_of_notMem ht, mul_zero, Finset.sum_const_zero,
        sub_zero, map_zero] using hz
  · intro K hK hinit
    obtain ⟨hmatch, _⟩ := hlocal K hK hinit
    have hr := (ae_restrict_iff' measurableSet_Ioc).mp hres
    filter_upwards [ae_restrict_of_ae hr, ae_restrict_mem measurableSet_Icc]
      with s hs hsIcc
    by_cases ht : s ∈ Ioc (0 : ℝ) 1
    · have gradient (L : ℂ →L[ℝ] ℝ)
          (hL : HasWeakGradient Set.univ (fun x => L ((Pr s.toNNReal fr) x))
            (fun x j => L (H s j x))) :
          HasWeakGradient K (fun x => L (X (s, x)))
            (fun x j => L ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s)) := by
        have hd := Correctors.hasWeakGradient_sub (hs ht L).1 hL
        intro j
        apply (HasWeakPartialDerivative.restrict_subset (Set.subset_univ K)
          MeasurableSet.univ (hd j)).congr_ae
        · filter_upwards [hmatch s ht.1.le ht.2, ae_restrict_of_ae (heV s)]
            with x hx hxV
          rw [hx, hxV, map_sub]
        · filter_upwards [ae_restrict_of_ae (heW j s)] with x hx
          simp only [indicator_of_mem ht, hx, map_sub, Pi.sub_apply]
      exact ⟨gradient Complex.reCLM (hH s).1, gradient Complex.imCLM (hH s).2⟩
    · have hs0 : s ≤ 0 := by
        by_contra hn
        exact ht ⟨lt_of_not_ge hn, hsIcc.2⟩
      have hz : HasWeakGradient K (fun _ => 0) (fun _ _ => 0) := by
        intro j
        exact ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, by
          intro φ hφ
          simp only [zero_mul, integral_zero, neg_zero]⟩
      constructor <;>
        simpa only [hX0 s hs0, indicator_of_notMem ht, Complex.zero_re, Complex.zero_im]
          using hz

/-- Zero extension preserves local spacetime L² on the enlarged time interval. -/
private theorem endpoint_zero_extension_memLp {d : ℕ} (K : Set (Vec d))
    (u : ℝ × Vec d → ℂ)
    (hu : MemLp u 2 ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K))) :
    MemLp (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
      (fun s => u (s, p.2)) p.1) 2
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) := by
  let S : Set (ℝ × Vec d) := Prod.fst ⁻¹' Ioc (0 : ℝ) 1
  have hS : MeasurableSet S := measurableSet_Ioc.preimage measurable_fst
  have hm : (((volume.restrict (Icc (-1 : ℝ) 1)).prod
      (volume.restrict K)).restrict S) ≤
      (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K) := by
    rw [Measure.prod_restrict, Measure.restrict_restrict hS, Measure.prod_restrict]
    apply Measure.restrict_mono_set
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2.2⟩
  change MemLp (S.indicator u) 2 _
  exact (memLp_indicator_iff_restrict hS).mpr (hu.mono_measure hm)


/-- The actual zero-extended residual and its SAME physical gradient are locally
L² in spacetime, including across the initial-time boundary. -/
theorem short_time_stationary_retained_zero_extended_local_memLp
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ Measurable U ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      (∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : ℝ × Vec d => ‖F (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        ∀ j, Integrable (fun p : ℝ × Vec d => ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K))) ∧
      ∀ χ : C(Vec d, ℝ), (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∃ V Z X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∃ W : Fin d → ℝ × Vec d → ℂ,
        (∀ j, Measurable (W j)) ∧
        (∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j) ∧
        (∀ (j : Fin d) (l r : ℝ), Integrable (fun p => ‖W j p‖ ^ 2)
          ((volume.restrict (Icc l r)).prod volume)) ∧
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pr s.toNNReal fr) (H s)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakGradient Set.univ (fun x => L (F (s, translate x ω)))
            (fun x j => L (D j (s, translate x ω))) ∧
          HasWeakDivergence Set.univ
            (fun x j => L ((1 / 2 : ℂ) *
              (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (D k (s, translate x ω) - W k (s, x))) +
              EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
                (fun k => D k (s, translate x ω)) j))
            (fun x => L (Y (s, x) -
              EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
                (fun k => D k (s, translate x ω)) i ζ -
              ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (D j (s, translate x ω) - W j (s, x)))))) ∧
        (∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          (∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0) ∧
          MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          ∀ j, MemLp (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
            (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1) 2
            ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K))) ∧
        (∀ A : Set (Vec d), MeasurableSet A → (∀ x ∈ A, χ x = 1) →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakDivergence A
            (fun x j => L ((1 / 2 : ℂ) *
              ∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D k (t, translate x ω) - W k (t, x)) s))
            (fun x => L (Y (s, x) - ζ *
              ∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D j (t, translate x ω) - W j (t, x)) s)) ) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1),
          HasWeakGradient K (fun x => (X (s, x)).re)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).re) ∧
          HasWeakGradient K (fun x => (X (s, x)).im)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).im) := by
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_stationary_retained_zero_extended_interior_equations Q hP hfg
  refine ⟨F, U, D, hF, hU, hD, heF, heU, heD, ?_⟩
  filter_upwards [hcoh] with ω hω
  refine ⟨hω.1, ?_⟩
  intro χ hχ Pr hPr fr gr hfr
  obtain ⟨V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, hlocal, hdiv, hgrad⟩ :=
    hω.2 χ hχ Pr hPr fr gr hfr
  refine ⟨V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, ?_, hdiv, hgrad⟩
  intro K hK hinit
  obtain ⟨hmatch, htime⟩ := hlocal K hK hinit
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hm : (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K) ≤
      (volume.restrict (Icc (0 : ℝ) 1)).prod (volume : Measure (Vec d)) :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hv2 : MemLp V 2 ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
    apply (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mpr
    exact endpoint_joint_sq_integrable
      ((((hPr.2.2.1 fr).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hV heV
  have hz2 : MemLp Z 2 ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
    apply (memLp_two_iff_integrable_sq_norm hZ.aestronglyMeasurable).mpr
    exact endpoint_joint_sq_integrable
      ((((hPr.2.2.1 gr).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hZ heZ
  obtain ⟨hf2, hu2, hd2⟩ := hω.1 K hK
  have hfm := (memLp_two_iff_integrable_sq_norm
    (hF.comp hshift).aestronglyMeasurable).mpr hf2
  have hum := (memLp_two_iff_integrable_sq_norm
    (hU.comp hshift).aestronglyMeasurable).mpr hu2
  have hXm := endpoint_zero_extension_memLp K _ (hfm.sub (hv2.mono_measure hm))
  have hYm := endpoint_zero_extension_memLp K _ (hum.sub (hz2.mono_measure hm))
  refine ⟨hmatch, htime, ?_, ?_, ?_⟩
  · apply hXm.ae_eq
    have hq : Measurable (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
        (fun s => F (s, translate p.2 ω) - V (s, p.2)) p.1) :=
      Measurable.ite (measurableSet_Ioc.preimage measurable_fst)
        ((hF.comp hshift).sub hV) measurable_const
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hq hX)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    by_cases ht : s ∈ Ioc (0 : ℝ) 1
    · filter_upwards [hmatch s ht.1.le ht.2] with x hx
      simpa only [indicator_of_mem ht, Pi.sub_apply] using hx.symm
    · have hs0 : s ≤ 0 := by
        by_contra hn
        exact ht ⟨lt_of_not_ge hn, hs.2⟩
      exact ae_of_all _ fun x => by rw [indicator_of_notMem ht, hX0 s hs0 x]
  · exact hYm.ae_eq (ae_of_all _ fun p => (heY p).symm)
  · intro j
    have hdm := (memLp_two_iff_integrable_sq_norm
      ((hD j).comp hshift).aestronglyMeasurable).mpr (hd2 j)
    have hwm := (memLp_two_iff_integrable_sq_norm
      (hW j).aestronglyMeasurable).mpr (hiW j 0 1)
    exact endpoint_zero_extension_memLp K _ (hdm.sub (hwm.mono_measure hm))

/-- The SAME locally L² zero-extended stationary-minus-retained residual satisfies
its homogeneous spacetime equation on every compact interior region. Test
integrability is derived from compactness, rather than supplied as a premise. -/
theorem short_time_stationary_retained_spacetime_equation
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ Measurable U ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      (∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : ℝ × Vec d => ‖F (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        ∀ j, Integrable (fun p : ℝ × Vec d => ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K))) ∧
      ∀ χ : C(Vec d, ℝ), (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∃ V Z X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∃ W : Fin d → ℝ × Vec d → ℂ,
        (∀ j, Measurable (W j)) ∧
        (∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j) ∧
        (∀ (j : Fin d) (l r : ℝ), Integrable (fun p => ‖W j p‖ ^ 2)
          ((volume.restrict (Icc l r)).prod volume)) ∧
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pr s.toNNReal fr) (H s)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakGradient Set.univ (fun x => L (F (s, translate x ω)))
            (fun x j => L (D j (s, translate x ω))) ∧
          HasWeakDivergence Set.univ
            (fun x j => L ((1 / 2 : ℂ) *
              (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (D k (s, translate x ω) - W k (s, x))) +
              EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
                (fun k => D k (s, translate x ω)) j))
            (fun x => L (Y (s, x) -
              EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
                (fun k => D k (s, translate x ω)) i ζ -
              ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (D j (s, translate x ω) - W j (s, x)))))) ∧
        (∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          (∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0) ∧
          MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          (∀ j, MemLp (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
            (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1) 2
            ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K))) ∧
          ∀ φ : ℝ × Vec d → ℝ,
            Continuous φ →
            Continuous (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1) →
            (∀ j, Continuous (fun p : ℝ × Vec d =>
              gradient (fun x => φ (p.1, x)) p.2 j)) →
            (∀ x, ContDiff ℝ 1 (fun s => φ (s, x))) →
            (∀ x, φ (-1, x) = 0) → (∀ x, φ (1, x) = 0) →
            (∀ s, IsSpatialTest K (fun x => φ (s, x))) →
            (∀ x ∈ K, χ x = 1) → ∀ L : ℂ →L[ℝ] ℝ,
            (∫ p : ℝ × Vec d,
              deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
              dot (fun j => L ((1 / 2 : ℂ) *
                ∑ k, ((ForcedLocality.retainedPair χ ω).1 p.2 j k : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D k (t, translate p.2 ω) - W k (t, p.2)) p.1))
                (gradient (fun x => φ (p.1, x)) p.2) +
              φ p * L (ζ * ∑ j,
                ((ForcedLocality.retainedPair χ ω).1 p.2 j i : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1)
              ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) = 0) ∧
        (∀ A : Set (Vec d), MeasurableSet A → (∀ x ∈ A, χ x = 1) →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakDivergence A
            (fun x j => L ((1 / 2 : ℂ) *
              ∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D k (t, translate x ω) - W k (t, x)) s))
            (fun x => L (Y (s, x) - ζ *
              ∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D j (t, translate x ω) - W j (t, x)) s)) ) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1),
          HasWeakGradient K (fun x => (X (s, x)).re)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).re) ∧
          HasWeakGradient K (fun x => (X (s, x)).im)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).im) := by
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_stationary_retained_zero_extended_local_memLp Q hP hfg
  refine ⟨F, U, D, hF, hU, hD, heF, heU, heD, ?_⟩
  filter_upwards [hcoh] with ω hω
  refine ⟨hω.1, ?_⟩
  intro χ hχ Pr hPr fr gr hfr
  obtain ⟨V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, hlocal, hdiv, hgrad⟩ :=
    hω.2 χ hχ Pr hPr fr gr hfr
  refine ⟨V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, ?_, hdiv, hgrad⟩
  intro K hK hinit
  obtain ⟨hmatch, htime, hX2, hY2, hJ2⟩ := hlocal K hK hinit
  refine ⟨hmatch, htime, hX2, hY2, hJ2, ?_⟩
  intro φ hφ hdt hdφ hφt hφl hφr hφx hχK L
  let J (j : Fin d) (p : ℝ × Vec d) : ℂ := (Ioc (0 : ℝ) 1).indicator
    (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1
  let a := (ForcedLocality.retainedPair χ ω).1
  let μ := (volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hmul {u v : ℝ × Vec d → ℂ} (hu : Continuous u) (hv : Integrable v μ) :
      Integrable (fun p => u p * v p) μ := by
    dsimp only [μ] at hv ⊢
    rw [Measure.prod_restrict] at hv ⊢
    exact IntegrableOn.continuousOn_mul hu.continuousOn hv (isCompact_Icc.prod hK)
  have hmulR {u v : ℝ × Vec d → ℝ} (hu : Continuous u) (hv : Integrable v μ) :
      Integrable (fun p => u p * v p) μ := by
    dsimp only [μ] at hv ⊢
    rw [Measure.prod_restrict] at hv ⊢
    exact IntegrableOn.continuousOn_mul hu.continuousOn hv (isCompact_Icc.prod hK)
  have hJ1 (j : Fin d) : Integrable (J j) μ :=
    (hJ2 j).integrable (by norm_num)
  have ha (j k : Fin d) : Continuous (fun p : ℝ × Vec d => (a p.2 j k : ℂ)) :=
    Complex.continuous_ofReal.comp ((a.continuous.matrix_elem j k).comp continuous_snd)
  have hflux (j : Fin d) : Integrable
      (fun p : ℝ × Vec d => L ((1 / 2 : ℂ) * ∑ k, (a p.2 j k : ℂ) * J k p)) μ :=
    L.integrable_comp ((integrable_finsetSum _ fun k _ => hmul (ha j k) (hJ1 k)).const_mul _)
  have hlow : Integrable
      (fun p : ℝ × Vec d => L (ζ * ∑ j, (a p.2 j i : ℂ) * J j p)) μ :=
    L.integrable_comp ((integrable_finsetSum _ fun j _ => hmul (ha j i) (hJ1 j)).const_mul _)
  apply short_time_spacetime_weak_equation K (fun p => L (X p)) (fun p => L (Y p))
    (fun p => L (ζ * ∑ j, (a p.2 j i : ℂ) * J j p))
    (fun p j => L ((1 / 2 : ℂ) * ∑ k, (a p.2 j k : ℂ) * J k p))
  · filter_upwards [htime] with x hx
    exact (hx L).2
  · filter_upwards [hdiv K hK.measurableSet hχK] with s hs
    simpa only [map_sub] using hs L
  · exact hφt
  · exact hφl
  · exact hφr
  · exact hφx
  · exact hmulR hdt (L.integrable_comp (hX2.integrable (by norm_num)))
  · exact hmulR hφ (L.integrable_comp (hY2.integrable (by norm_num)))
  · change Integrable (fun p : ℝ × Vec d =>
      ∑ j, L ((1 / 2 : ℂ) * ∑ k, (a p.2 j k : ℂ) * J k p) *
        gradient (fun x => φ (p.1, x)) p.2 j) μ
    exact integrable_finsetSum _ fun j _ => by
      simpa only [mul_comm] using hmulR (hdφ j) (hflux j)
  · exact hmulR hφ hlow

/-- A real smooth compact datum and its actual coordinate derivatives give the
physical complex H¹ graph. -/
private theorem endpoint_smooth_compact_physical_h1 {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ (v : Lp ℂ 2 (volume : Measure (Vec d)))
      (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) v G ∧
      (v : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ)) ∧
      ∀ j, (G j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (coordinateDerivative j φ x : ℂ)) := by
  have hv : MemLp (fun x => (φ x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hc.comp_left rfl)
  have hG (j : Fin d) : MemLp (fun x => (coordinateDerivative j φ x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
        ((hc.fderiv_apply ℝ (unitVector j)).comp_left rfl)
  refine ⟨hv.toLp _, fun j => (hG j).toLp _, ?_, hv.coeFn_toLp,
    fun j => (hG j).coeFn_toLp⟩
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _ _ _
    hv.coeFn_toLp (fun j => (hG j).coeFn_toLp)).mpr
  constructor
  · intro j
    simpa only [Complex.ofReal_re] using
      hasWeakPartialDerivative_of_contDiff j φ (hφ.of_le (by simp))
  · intro j
    simp only [Complex.ofReal_im]
    have hz : coordinateDerivative j (fun _ : Vec d => (0 : ℝ)) = fun _ => 0 := by
      funext x
      simp only [coordinateDerivative, fderiv_const_apply, zero_apply]
    simpa only [hz] using
      hasWeakPartialDerivative_of_contDiff j (fun _ : Vec d => (0 : ℝ)) contDiff_const

/-- Every real smooth compact datum lies in the full physical generator graph
for a smooth coefficient field. The weak identity is tested on all physical H¹
data, using whole-space integration by parts for the actual flux. -/
theorem short_time_smooth_compact_physical_generator {d : ℕ}
    (a : Vec d → Mat d) (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (i : Fin d) (ζ : ℂ) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ v g : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ)) ∧
      IsPhysicalComplexGeneratorPair a i ζ v g := by
  classical
  have hd (k : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative k φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ).2).clm_apply contDiff_const
  have hdc (k : Fin d) : HasCompactSupport (coordinateDerivative k φ) :=
    hc.fderiv_apply ℝ (unitVector k)
  let F (j : Fin d) (x : Vec d) : ℝ := ∑ k, a x j k * coordinateDerivative k φ x
  have hFs (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (F j) :=
    ContDiff.sum fun k _ => (ha j k).mul (hd k)
  have hFc (j : Fin d) : HasCompactSupport (F j) := by
    convert HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun k x => a x j k * coordinateDerivative k φ x)
      (fun k _ => (hdc k).mul_left) using 1
    funext x
    simp only [F, Finset.sum_apply]
  obtain ⟨v, G, hv, hev, heG⟩ := endpoint_smooth_compact_physical_h1 φ hφ hc
  choose U H hU heU heH using fun j => endpoint_smooth_compact_physical_h1 (F j) (hFs j) (hFc j)
  let b (x : Vec d) : ℝ := ∑ j, a x j i * coordinateDerivative j φ x
  have hbs : ContDiff ℝ (⊤ : ℕ∞) b :=
    ContDiff.sum fun j _ => (ha j i).mul (hd j)
  have hbc : HasCompactSupport b := by
    convert HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun j x => a x j i * coordinateDerivative j φ x)
      (fun j _ => (hdc j).mul_left) using 1
    funext x
    simp only [b, Finset.sum_apply]
  have hb : MemLp (fun x => (b x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hbs.continuous).memLp_of_hasCompactSupport
      (hbc.comp_left rfl)
  let bL := hb.toLp (fun x => (b x : ℂ))
  let g := (1 / 2 : ℂ) • ∑ j, H j j + ζ • bL
  refine ⟨v, g, hev, G, hv, ?_⟩
  intro w J hw
  have heF (j : Fin d) : (U j : Vec d → ℂ) =ᵐ[volume]
      (fun x => ∑ k, (a x j k : ℂ) * G k x) := by
    filter_upwards [heU j, ae_all_iff.mpr heG] with x hx hGx
    rw [hx]
    simp only [F, Complex.ofReal_sum, Complex.ofReal_mul, hGx]
  have heb : (bL : Vec d → ℂ) =ᵐ[volume]
      (fun x => ∑ j, (a x j i : ℂ) * G j x) := by
    filter_upwards [hb.coeFn_toLp, ae_all_iff.mpr heG] with x hx hGx
    rw [hx]
    simp only [b, Complex.ofReal_sum, Complex.ofReal_mul, hGx]
  have hparts (j : Fin d) :
      (∫ x, H j j x * w x) = -(∫ x, U j x * J j x) := by
    have h := physicalH1Graph_integral_mul_gradient (U j) w (H j) J (hU j) hw j
    exact (neg_eq_iff_eq_neg.mp h.symm)
  have hcoe (s : Finset (Fin d)) : (∑ j ∈ s, H j j : Lp ℂ 2 volume) =ᵐ[volume]
      (fun x => ∑ j ∈ s, H j j x) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty, Pi.zero_apply] using! Lp.coeFn_zero ℂ 2 volume
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      filter_upwards [Lp.coeFn_add (H j j) (∑ k ∈ s, H k k), ih] with x hx hy
      simpa only [Pi.add_apply, hy] using hx
  have hsum : (∫ x, (∑ j, H j j) x * w x) =
      -(∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * J j x) := by
    have hel : (fun x => (∑ j, H j j) x * w x) =ᵐ[volume]
        (fun x => ∑ j, H j j x * w x) := by
      filter_upwards [hcoe Finset.univ] with x hx
      rw [hx, Finset.sum_mul]
    rw [integral_congr_ae hel, integral_finsetSum (f := fun j x => H j j x * w x) _
      (fun j _ => (Lp.memLp (H j j)).integrable_mul (Lp.memLp w))]
    simp_rw [hparts]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum (f := fun j x => U j x * J j x) _
      (fun j _ => (Lp.memLp (U j)).integrable_mul (Lp.memLp (J j)))]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr heF] with x hx
    simp only [hx, Finset.sum_mul]
  have hel : (fun x => g x * w x) =ᵐ[volume]
      (fun x => (1 / 2 : ℂ) * ((∑ j, H j j) x * w x) + ζ * (bL x * w x)) := by
    filter_upwards [Lp.coeFn_add ((1 / 2 : ℂ) • ∑ j, H j j) (ζ • bL),
      Lp.coeFn_smul (1 / 2 : ℂ) (∑ j, H j j), Lp.coeFn_smul ζ bL] with x hx hy hz
    dsimp only [g]
    rw [hx]
    simp only [Pi.add_apply, hy, hz, Pi.smul_apply, smul_eq_mul]
    ring
  rw [integral_congr_ae hel,
    integral_add (f := fun x => (1 / 2 : ℂ) * ((∑ j, H j j) x * w x))
      (g := fun x => ζ * (bL x * w x)) (((Lp.memLp (∑ j, H j j)).integrable_mul (Lp.memLp w)).const_mul _)
      (((Lp.memLp bL).integrable_mul (Lp.memLp w)).const_mul _),
    integral_const_mul, integral_const_mul, hsum]
  rw [mul_neg, neg_mul]
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards [heb] with x hx
  exact congrArg (fun z : ℂ => z * w x) hx

private theorem endpoint_complex_smooth_compact_generator {d : ℕ}
    (a : Vec d → Mat d) (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hab : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ c q : ℂ) (φ ψ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (fr : Lp ℂ 2 (volume : Measure (Vec d)))
    (hfr : (fr : Vec d → ℂ) =ᵐ[volume] fun x => c * (φ x : ℂ) + q * (ψ x : ℂ)) :
    ∃ gr : Lp ℂ 2 (volume : Measure (Vec d)), IsPhysicalComplexGeneratorPair a i ζ fr gr := by
  obtain ⟨u, g, heu, hu⟩ := short_time_smooth_compact_physical_generator a ha i ζ φ hφ hcφ
  obtain ⟨v, h, hev, hv⟩ := short_time_smooth_compact_physical_generator a ha i ζ ψ hψ hcψ
  have he : fr = c • u + q • v := by
    apply Lp.ext
    filter_upwards [hfr, heu, hev, Lp.coeFn_add (c • u) (q • v),
      Lp.coeFn_smul c u, Lp.coeFn_smul q v] with x hf hx hy hsum hc hq
    rw [hf, hsum]
    simp only [Pi.add_apply, hc, hq, Pi.smul_apply, smul_eq_mul, hx, hy]
  rw [he]
  exact ⟨c • g + q • h,
    physical_complex_generator_graph_linear_combination a i ζ c q hab hu hv⟩

/-- The actual forward and clock cutoff observations belong to the retained
physical generator graph on every smooth elliptic sample. The initial L²
representative is arbitrary, so this applies to the locally measurable datum
already used by the retained evolution. -/
theorem short_time_forward_clock_cutoff_generator {d : ℕ}
    (χ : C(Vec d, ℝ)) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (ω : FieldPair d) (hω : IsSmoothFieldPair ω)
    (Λ : ℝ) (hA : ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ)
    (i : Fin d) (ζ : ℂ) (ν : Fin d ⊕ Unit)
    (fr : Lp ℂ 2 (volume : Measure (Vec d)))
    (hfr : (fr : Vec d → ℂ) =ᵐ[volume] fun x => match ν with
      | Sum.inl j => (χ x : ℂ) *
          ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
            (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ))
      | Sum.inr _ => ζ * (χ x : ℂ) * (ω.2 x : ℂ)) :
    ∃ gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr := by
  let a := (ForcedLocality.retainedPair χ ω).1
  have has (j k : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * ω.1 x j k + (1 - χ x) * (1 : Mat d) j k)
    exact ((hχ.mul (hω.1 j k)).add ((contDiff_const.sub hχ).mul contDiff_const))
  have hab (j k : Fin d) : MemLp (fun x => (a x j k : ℂ)) ∞ volume := by
    apply memLp_top_of_bound
      (Complex.continuous_ofReal.comp
        (a.continuous.matrix_elem j k)).aestronglyMeasurable Λ
    exact ae_of_all _ fun x => by
      change ‖(a x j k : ℂ)‖ ≤ Λ
      simpa only [Complex.norm_real, Real.norm_eq_abs] using (hA x).entry_abs_le j k
  cases ν with
  | inl j =>
    let b (x : Vec d) : ℝ := (1 / 2 : ℝ) * ∑ k : Fin d,
      coordinateDerivative k (fun y => ω.1 y k j) x
    have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
      exact contDiff_const.mul (ContDiff.sum fun k _ =>
        ((contDiff_infty_iff_fderiv.mp (hω.1 k j)).2).clm_apply contDiff_const)
    apply endpoint_complex_smooth_compact_generator a has hab i ζ 1 ζ
      (fun x => χ x * b x) (fun x => χ x * ω.1 x i j)
      (hχ.mul hb) hc.mul_right (hχ.mul (hω.1 i j)) hc.mul_right fr
    filter_upwards [hfr] with x hx
    rw [hx]
    simp only [b, Complex.ofReal_mul, one_mul]
    ring
  | inr u =>
    apply endpoint_complex_smooth_compact_generator a has hab i ζ 0 ζ
      (fun _ => 0) (fun x => χ x * ω.2 x)
      contDiff_const HasCompactSupport.zero (hχ.mul hω.2) hc.mul_right fr
    simpa only [Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_mul, mul_assoc] using hfr


/-- The actual compact forward and clock cutoff data supply the retained
physical generator pair internally. The SAME representative, gradient, temporal
zero extension and homogeneous interior spacetime equation are retained. -/
theorem short_time_forward_clock_cutoff_spacetime_equation
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ Measurable U ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      (∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : ℝ × Vec d => ‖F (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        ∀ j, Integrable (fun p : ℝ × Vec d => ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K))) ∧
      ∀ (_ : IsSmoothFieldPair ω) (χ : C(Vec d, ℝ)),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ Λ : ℝ, (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ (ν : Fin d ⊕ Unit) (fr : Lp ℂ 2 (volume : Measure (Vec d))),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => match ν with
        | Sum.inl j => (χ x : ℂ) *
            ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
              (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ))
        | Sum.inr _ => ζ * (χ x : ℂ) * (ω.2 x : ℂ)) →
      ∃ gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr ∧
      ∃ V Z X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∃ W : Fin d → ℝ × Vec d → ℂ,
        (∀ j, Measurable (W j)) ∧
        (∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j) ∧
        (∀ (j : Fin d) (l r : ℝ), Integrable (fun p => ‖W j p‖ ^ 2)
          ((volume.restrict (Icc l r)).prod volume)) ∧
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pr s.toNNReal fr) (H s)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakGradient Set.univ (fun x => L (F (s, translate x ω)))
            (fun x j => L (D j (s, translate x ω))) ∧
          HasWeakDivergence Set.univ
            (fun x j => L ((1 / 2 : ℂ) *
              (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (D k (s, translate x ω) - W k (s, x))) +
              EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
                (fun k => D k (s, translate x ω)) j))
            (fun x => L (Y (s, x) -
              EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
                (fun k => D k (s, translate x ω)) i ζ -
              ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (D j (s, translate x ω) - W j (s, x)))))) ∧
        (∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          (∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0) ∧
          MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          (∀ j, MemLp (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
            (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1) 2
            ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K))) ∧
          ∀ φ : ℝ × Vec d → ℝ,
            Continuous φ →
            Continuous (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1) →
            (∀ j, Continuous (fun p : ℝ × Vec d =>
              gradient (fun x => φ (p.1, x)) p.2 j)) →
            (∀ x, ContDiff ℝ 1 (fun s => φ (s, x))) →
            (∀ x, φ (-1, x) = 0) → (∀ x, φ (1, x) = 0) →
            (∀ s, IsSpatialTest K (fun x => φ (s, x))) →
            (∀ x ∈ K, χ x = 1) → ∀ L : ℂ →L[ℝ] ℝ,
            (∫ p : ℝ × Vec d,
              deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
              dot (fun j => L ((1 / 2 : ℂ) *
                ∑ k, ((ForcedLocality.retainedPair χ ω).1 p.2 j k : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D k (t, translate p.2 ω) - W k (t, p.2)) p.1))
                (gradient (fun x => φ (p.1, x)) p.2) +
              φ p * L (ζ * ∑ j,
                ((ForcedLocality.retainedPair χ ω).1 p.2 j i : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1)
              ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) = 0) ∧
        (∀ A : Set (Vec d), MeasurableSet A → (∀ x ∈ A, χ x = 1) →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakDivergence A
            (fun x j => L ((1 / 2 : ℂ) *
              ∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D k (t, translate x ω) - W k (t, x)) s))
            (fun x => L (Y (s, x) - ζ *
              ∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D j (t, translate x ω) - W j (t, x)) s)) ) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1),
          HasWeakGradient K (fun x => (X (s, x)).re)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).re) ∧
          HasWeakGradient K (fun x => (X (s, x)).im)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).im) := by
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_stationary_retained_spacetime_equation Q hP hfg
  refine ⟨F, U, D, hF, hU, hD, heF, heU, heD, ?_⟩
  filter_upwards [hcoh] with ω hω
  refine ⟨hω.1, ?_⟩
  intro hωs χ hχs hc hχ Λ hA Pr hPr ν fr hfr
  obtain ⟨gr, hgr⟩ := short_time_forward_clock_cutoff_generator
    χ hχs hc ω hωs Λ hA i ζ ν fr hfr
  exact ⟨gr, hgr, hω.2 χ hχ Pr hPr fr gr hgr⟩


/-- The scalar weak time identity used by the retained residual is the native
one-dimensional weak derivative predicate, with the same representative. -/
private theorem endpoint_time_weak_derivative
    {v g : ℝ → ℝ}
    (hv : ContinuousOn v (Icc (-1 : ℝ) 1))
    (hg : MemLp g 2 (volume.restrict (Icc (-1 : ℝ) 1)))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
      (∫ t in (-1 : ℝ)..1, deriv ψ t * v t + ψ t * g t) = 0) :
    PDE.HasWeakDerivOnIoo (-1) 1 v g := by
  unfold PDE.HasWeakDerivOnIoo
  intro φ hφ hφc hφs
  let ψ : ℝ → ℝ := PDE.scalarPullbackOne φ
  have hψ : ContDiff ℝ 1 ψ := PDE.ContDiff.scalarPullbackOne (hφ.of_le (by simp))
  have hs : tsupport ψ ⊆ Ioo (-1 : ℝ) 1 :=
    PDE.tsupport_scalarPullbackOne_subset_Ioo hφs
  have hψa : ψ (-1) = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h; have := (hs h).1; linarith)
  have hψb : ψ 1 = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h; have := (hs h).2; linarith)
  have hi₁ : IntegrableOn (fun t => deriv ψ t * v t) (Icc (-1 : ℝ) 1) :=
    ((hψ.continuous_deriv (by norm_num)).continuousOn.mul hv).integrableOn_Icc
  have hi₂ : IntegrableOn (fun t => ψ t * g t) (Icc (-1 : ℝ) 1) :=
    IntegrableOn.continuousOn_mul hψ.continuous.continuousOn
      (hg.integrable (by norm_num) : IntegrableOn g (Icc (-1 : ℝ) 1) volume) isCompact_Icc
  have he := hweak ψ hψ hψa hψb
  rw [intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc, integral_add hi₁ hi₂] at he
  rw [PDE.setIntegral_oneDimensionalAxisBox_eq_scalarPullbackOne,
    PDE.setIntegral_oneDimensionalAxisBox_eq_scalarPullbackOne]
  have hleft :
      (fun t => PDE.scalarPullbackOne
        (fun x => PDE.liftOneDimensional v x *
          (fderiv ℝ φ x) (PDE.basisVec (0 : Fin 1))) t) =
      (fun t => v t * deriv ψ t) := by
    funext t
    simp only [PDE.scalarPullbackOne, PDE.liftOneDimensional,
      PDE.vecOneCoordinate_scalarToVecOne]
    rw [← PDE.deriv_scalarPullbackOne_eq_native_directional (hφ.of_le (by simp))]
  have hright :
      (fun t => PDE.scalarPullbackOne
        (fun x => PDE.liftOneDimensional g x * φ x) t) =
      (fun t => g t * ψ t) := by
    funext t
    simp only [PDE.scalarPullbackOne, PDE.liftOneDimensional,
      PDE.vecOneCoordinate_scalarToVecOne, ψ]
  change (∫ t in Ioo (-1 : ℝ) 1,
      PDE.scalarPullbackOne (fun x => PDE.liftOneDimensional v x *
        (fderiv ℝ φ x) (PDE.basisVec (0 : Fin 1))) t) =
    -(∫ t in Ioo (-1 : ℝ) 1,
      PDE.scalarPullbackOne (fun x => PDE.liftOneDimensional g x * φ x) t)
  rw [hleft, hright, Measure.restrict_congr_set Ioo_ae_eq_Icc]
  simpa only [mul_comm] using (eq_neg_iff_add_eq_zero.mpr he)

/-- A complex residual with the actual weak time identity and zero initial
trace is the literal primitive of its already chosen time derivative. -/
theorem short_time_zero_extended_primitive_identity
    {v g : ℝ → ℂ}
    (hv : MemLp v 2 (volume.restrict (Icc (-1 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Icc (-1 : ℝ) 1)))
    (hv0 : v 0 = 0)
    (hweak : ∀ L : ℂ →L[ℝ] ℝ,
      AbsolutelyContinuousOnInterval (fun s => L (v s)) (-1) 1 ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
        (∫ t in (-1 : ℝ)..1, deriv ψ t * L (v t) + ψ t * L (g t)) = 0) :
    ∀ t ∈ Icc (-1 : ℝ) 1, v t = ∫ s in (0 : ℝ)..t, g s := by
  intro t ht
  have he (L : ℂ →L[ℝ] ℝ) : L (v t) = L (∫ s in (0 : ℝ)..t, g s) := by
    have hLv : MemLp (fun s => L (v s)) 2 (volume.restrict (Icc (-1 : ℝ) 1)) :=
      L.comp_memLp' hv
    have hLg : MemLp (fun s => L (g s)) 2 (volume.restrict (Icc (-1 : ℝ) 1)) :=
      L.comp_memLp' hg
    have hcv : ContinuousOn (fun s => L (v s)) (Icc (-1 : ℝ) 1) := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using (hweak L).1.continuousOn
    have hw := endpoint_time_weak_derivative hcv hLg (hweak L).2
    have hi := PDE.ContinuousOn.increment_eq_intervalIntegral_of_hasWeakDerivOnIoo
      (by norm_num : (-1 : ℝ) < 1) hcv
      (hLv.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl))
      hLg hw (s := 0) (by norm_num) ht
    have hgi : IntervalIntegrable g volume 0 t :=
      MeasureTheory.IntegrableOn.intervalIntegrable (MeasureTheory.IntegrableOn.mono_set
        (hg.integrable (by norm_num) : IntegrableOn g (Icc (-1 : ℝ) 1) volume)
        (uIcc_subset_Icc (by norm_num) ht))
    rw [hv0, map_zero, sub_zero, L.intervalIntegral_comp_comm hgi] at hi
    exact hi
  apply Complex.ext
  · exact he Complex.reCLM
  · exact he Complex.imCLM


/-- The already chosen zero-extended residual is strongly continuous locally
in spatial `L²` at every time in `[-1,1]`, including zero and both endpoints.
Its spacetime derivative and weak time identity determine the same slices. -/
theorem short_time_zero_extended_local_strong_continuous
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [SFinite μ]
    {X Y : ℝ × S → ℂ} (hX : Measurable X) (hY : Measurable Y)
    (hX2 : MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod μ))
    (hY2 : MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod μ))
    (hX0 : ∀ t : ℝ, t ≤ 0 → ∀ x, X (t, x) = 0)
    (hweak : ∀ᵐ x ∂μ, ∀ L : ℂ →L[ℝ] ℝ,
      AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
        (∫ t in (-1 : ℝ)..1,
          deriv ψ t * L (X (t, x)) + ψ t * L (Y (t, x))) = 0) :
    (∀ t ∈ Icc (-1 : ℝ) 1, MemLp (fun x => X (t, x)) 2 μ) ∧
    ∀ a ∈ Icc (-1 : ℝ) 1,
      Tendsto (fun t => ∫ x, ‖X (t, x) - X (a, x)‖ ^ 2 ∂μ)
        (𝓝[Icc (-1 : ℝ) 1] a) (𝓝 0) := by
  have hXI := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX2
  have hYI := (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mp hY2
  have hprim : ∀ᵐ x ∂μ, ∀ t ∈ Icc (-1 : ℝ) 1,
      X (t, x) = ∫ s in (0 : ℝ)..t, Y (s, x) := by
    filter_upwards [hXI.prod_left_ae, hYI.prod_left_ae, hweak] with x hx hy hw
    apply short_time_zero_extended_primitive_identity
      ((memLp_two_iff_integrable_sq_norm
        (hX.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hx)
      ((memLp_two_iff_integrable_sq_norm
        (hY.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hy)
      (hX0 0 le_rfl x) hw
  have hYpos : Integrable (fun p => ‖Y p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod μ) :=
    hYI.mono_measure (Measure.prod_mono
      (Measure.restrict_mono (Icc_subset_Icc (by norm_num) le_rfl) le_rfl) le_rfl)
  obtain ⟨hmem, hcont⟩ := short_time_local_primitive_continuous μ hY hYpos
  have hclamp (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      max 0 t ∈ Icc (0 : ℝ) 1 := ⟨le_max_left _ _, max_le (by norm_num) ht.2⟩
  have he (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      (fun x => X (t, x)) =ᵐ[μ]
        (fun x => ∫ s in Icc (0 : ℝ) (max 0 t), Y (s, x)) := by
    filter_upwards [hprim] with x hx
    by_cases ht0 : 0 ≤ t
    · rw [max_eq_right ht0, hx t ht, intervalIntegral.integral_of_le ht0,
        integral_Icc_eq_integral_Ioc]
    · rw [hX0 t (le_of_not_ge ht0) x, max_eq_left (le_of_not_ge ht0)]
      simp
  refine ⟨fun t ht => (hmem _ (hclamp t ht)).ae_eq (he t ht).symm, ?_⟩
  intro a ha
  have hm : MapsTo (fun t : ℝ => max 0 t) (Icc (-1 : ℝ) 1) (Icc (0 : ℝ) 1) :=
    fun t ht => hclamp t ht
  have hc : Tendsto (fun t : ℝ => max 0 t)
      (𝓝[Icc (-1 : ℝ) 1] a) (𝓝[Icc (0 : ℝ) 1] (max 0 a)) :=
    (continuous_const.max continuous_id).continuousWithinAt.tendsto_nhdsWithin hm
  have htend := (hcont _ (hclamp a ha)).comp hc
  apply htend.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  apply integral_congr_ae
  filter_upwards [he t ht, he a ha] with x hx ha'
  rw [hx, ha']

/-- The actual cutoff residual has locally square-integrable slices and strong
time continuity on the entire zero-extended interval, with the same witnesses
as its homogeneous spacetime equation. -/
theorem short_time_forward_clock_cutoff_spacetime_continuous
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ Measurable U ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      (∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : ℝ × Vec d => ‖F (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        ∀ j, Integrable (fun p : ℝ × Vec d => ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K))) ∧
      ∀ (_ : IsSmoothFieldPair ω) (χ : C(Vec d, ℝ)),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ Λ : ℝ, (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ (ν : Fin d ⊕ Unit) (fr : Lp ℂ 2 (volume : Measure (Vec d))),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => match ν with
        | Sum.inl j => (χ x : ℂ) *
            ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
              (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ))
        | Sum.inr _ => ζ * (χ x : ℂ) * (ω.2 x : ℂ)) →
      ∃ gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr ∧
      ∃ V Z X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∃ W : Fin d → ℝ × Vec d → ℂ,
        (∀ j, Measurable (W j)) ∧
        (∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j) ∧
        (∀ (j : Fin d) (l r : ℝ), Integrable (fun p => ‖W j p‖ ^ 2)
          ((volume.restrict (Icc l r)).prod volume)) ∧
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pr s.toNNReal fr) (H s)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakGradient Set.univ (fun x => L (F (s, translate x ω)))
            (fun x j => L (D j (s, translate x ω))) ∧
          HasWeakDivergence Set.univ
            (fun x j => L ((1 / 2 : ℂ) *
              (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (D k (s, translate x ω) - W k (s, x))) +
              EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
                (fun k => D k (s, translate x ω)) j))
            (fun x => L (Y (s, x) -
              EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
                (fun k => D k (s, translate x ω)) i ζ -
              ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (D j (s, translate x ω) - W j (s, x)))))) ∧
        (∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          (∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0) ∧
          (∀ s ∈ Icc (-1 : ℝ) 1,
            MemLp (fun x => X (s, x)) 2 (volume.restrict K)) ∧
          (∀ a ∈ Icc (-1 : ℝ) 1,
            Tendsto (fun s => ∫ x in K, ‖X (s, x) - X (a, x)‖ ^ 2)
              (𝓝[Icc (-1 : ℝ) 1] a) (𝓝 0)) ∧
          MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          (∀ j, MemLp (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
            (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1) 2
            ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K))) ∧
          ∀ φ : ℝ × Vec d → ℝ,
            Continuous φ →
            Continuous (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1) →
            (∀ j, Continuous (fun p : ℝ × Vec d =>
              gradient (fun x => φ (p.1, x)) p.2 j)) →
            (∀ x, ContDiff ℝ 1 (fun s => φ (s, x))) →
            (∀ x, φ (-1, x) = 0) → (∀ x, φ (1, x) = 0) →
            (∀ s, IsSpatialTest K (fun x => φ (s, x))) →
            (∀ x ∈ K, χ x = 1) → ∀ L : ℂ →L[ℝ] ℝ,
            (∫ p : ℝ × Vec d,
              deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
              dot (fun j => L ((1 / 2 : ℂ) *
                ∑ k, ((ForcedLocality.retainedPair χ ω).1 p.2 j k : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D k (t, translate p.2 ω) - W k (t, p.2)) p.1))
                (gradient (fun x => φ (p.1, x)) p.2) +
              φ p * L (ζ * ∑ j,
                ((ForcedLocality.retainedPair χ ω).1 p.2 j i : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1)
              ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) = 0) ∧
        (∀ A : Set (Vec d), MeasurableSet A → (∀ x ∈ A, χ x = 1) →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakDivergence A
            (fun x j => L ((1 / 2 : ℂ) *
              ∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D k (t, translate x ω) - W k (t, x)) s))
            (fun x => L (Y (s, x) - ζ *
              ∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D j (t, translate x ω) - W j (t, x)) s)) ) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1),
          HasWeakGradient K (fun x => (X (s, x)).re)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).re) ∧
          HasWeakGradient K (fun x => (X (s, x)).im)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).im) := by
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_forward_clock_cutoff_spacetime_equation Q hP hfg
  refine ⟨F, U, D, hF, hU, hD, heF, heU, heD, ?_⟩
  filter_upwards [hcoh] with ω hω
  refine ⟨hω.1, ?_⟩
  intro hωs χ hχs hc hχ Λ hA Pr hPr ν fr hfr
  obtain ⟨gr, hgr, V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, hlocal, hdiv, hgrad⟩ :=
      hω.2 hωs χ hχs hc hχ Λ hA Pr hPr ν fr hfr
  refine ⟨gr, hgr, V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, ?_, hdiv, hgrad⟩
  intro K hK hinit
  obtain ⟨hmatch, htime, hX2, hY2, hJ2, hPDE⟩ := hlocal K hK hinit
  obtain ⟨hslice, hcont⟩ := short_time_zero_extended_local_strong_continuous
    (volume.restrict K) hX hY hX2 hY2 hX0 htime
  exact ⟨hmatch, htime, hslice, hcont, hX2, hY2, hJ2, hPDE⟩

/-- Reordering time and space preserves the actual local spacetime `L²` class. -/
private theorem endpoint_memLp_space_time {d : ℕ} {K : Set (Vec d)} {I : Set ℝ}
    {X : ℝ × Vec d → ℂ}
    (hX : MemLp X 2 ((volume.restrict I).prod (volume.restrict K))) :
    MemLp (fun p : Vec d × ℝ => X (p.2, p.1)) 2
      (volume.restrict (K ×ˢ I)) := by
  have hs := hX.comp_measurePreserving
    (Measure.measurePreserving_swap (μ := volume.restrict K) (ν := volume.restrict I))
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact hs

/-- The retained spatial weak gradient has the same coordinate identities as
PDEFoundation's weak gradient. -/
private theorem endpoint_weak_gradient_pde {d : ℕ} {K : Set (Vec d)}
    {v : Vec d → ℝ} {J : Vec d → Vec d} (h : HasWeakGradient K v J) :
    PDE.HasWeakGradientOn K v J := by
  intro j φ hφ hφc hφK
  simpa only [coordinateDerivative, unitVector, PDE.basisVec] using
    (h j).2.2 φ ⟨hφ, hφc, hφK⟩

/-- The exponential lift of the already chosen residual is a parabolic energy
function on every interior cylinder. The literal value and all gradient
coordinates are retained, including at time zero. -/
theorem short_time_residual_complex_lift_ParH1 {d : ℕ}
    {K U : Set (Vec d)} {V : Set (PDE.Vec 2)}
    (hU : IsOpen U) (hUK : U ⊆ K) (hV : IsOpen V)
    (hVfinite : volume V < ⊤) (r : ℝ) (hr : ∀ y ∈ V, y 0 ≤ r)
    (X : ℝ × Vec d → ℂ) (J : Fin d → ℝ × Vec d → ℂ)
    (hX2 : MemLp X 2
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (hJ2 : ∀ j, MemLp (J j) 2
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (hslice : ∀ t ∈ Icc (-1 : ℝ) 1,
      MemLp (fun x => X (t, x)) 2 (volume.restrict K))
    (hcont : ∀ t ∈ Icc (-1 : ℝ) 1,
      Tendsto (fun s => ∫ x in K, ‖X (s, x) - X (t, x)‖ ^ 2)
        (𝓝[Icc (-1 : ℝ) 1] t) (𝓝 0))
    (hgrad : ∀ᵐ t ∂volume.restrict (Icc (-1 : ℝ) 1),
      HasWeakGradient K (fun x => (X (t, x)).re) (fun x j => (J j (t, x)).re) ∧
      HasWeakGradient K (fun x => (X (t, x)).im) (fun x j => (J j (t, x)).im)) :
    ∃ w : PDE.ParH1Function (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V))
        (Icc (-1 : ℝ) 1),
      (∀ z, w.toFun z = (Complex.exp
        ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          X (z.2, (PDE.vecAppendEquiv d 2 z.1).1)).re) ∧
      (∀ z j, w.grad z (Fin.castAdd 2 j) = (Complex.exp
        ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          J j (z.2, (PDE.vecAppendEquiv d 2 z.1).1)).re) ∧
      (∀ z, w.grad z (Fin.natAdd d (0 : Fin 2)) = w.toFun z) ∧
      (∀ z, w.grad z (Fin.natAdd d (1 : Fin 2)) = -(Complex.exp
        ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          X (z.2, (PDE.vecAppendEquiv d 2 z.1).1)).im) := by
  apply short_time_complex_lift_ParH1 hU hV measurableSet_Icc hVfinite r hr
    (fun p => X (p.2, p.1)) (fun j p => J j (p.2, p.1))
  · exact endpoint_memLp_space_time (hX2.mono_measure
      (Measure.prod_mono le_rfl (Measure.restrict_mono hUK le_rfl)))
  · intro j
    exact endpoint_memLp_space_time ((hJ2 j).mono_measure
      (Measure.prod_mono le_rfl (Measure.restrict_mono hUK le_rfl)))
  · filter_upwards [hgrad] with t ht
    exact ⟨(endpoint_weak_gradient_pde ht.1).restrict hU hUK,
      (endpoint_weak_gradient_pde ht.2).restrict hU hUK⟩
  · intro t ht L hL hLU
    exact (hslice t ht).mono_measure (Measure.restrict_mono (hLU.trans hUK) le_rfl)
  · intro t ht L hL hLU
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hcont t ht)
    · exact Eventually.of_forall fun s => integral_nonneg (fun x => sq_nonneg _)
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      exact setIntegral_mono_set (((hslice s hs).sub (hslice t ht)).norm.integrable_sq)
        (ae_of_all _ (fun x => sq_nonneg _)) (Eventually.of_forall (hLU.trans hUK))

/-- The actual forward/clock cutoff residual has the literal exponential
parabolic lift on every interior cylinder, with the same physical gradient
and homogeneous spacetime equation. -/
theorem short_time_forward_clock_cutoff_parabolic_lift
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ Measurable U ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      (∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : ℝ × Vec d => ‖F (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        ∀ j, Integrable (fun p : ℝ × Vec d => ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K))) ∧
      ∀ (_ : IsSmoothFieldPair ω) (χ : C(Vec d, ℝ)),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ Λ : ℝ, (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ (ν : Fin d ⊕ Unit) (fr : Lp ℂ 2 (volume : Measure (Vec d))),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => match ν with
        | Sum.inl j => (χ x : ℂ) *
            ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
              (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ))
        | Sum.inr _ => ζ * (χ x : ℂ) * (ω.2 x : ℂ)) →
      ∃ gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr ∧
      ∃ V Z X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∃ W : Fin d → ℝ × Vec d → ℂ,
        (∀ j, Measurable (W j)) ∧
        (∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j) ∧
        (∀ (j : Fin d) (l r : ℝ), Integrable (fun p => ‖W j p‖ ^ 2)
          ((volume.restrict (Icc l r)).prod volume)) ∧
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pr s.toNNReal fr) (H s)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakGradient Set.univ (fun x => L (F (s, translate x ω)))
            (fun x j => L (D j (s, translate x ω))) ∧
          HasWeakDivergence Set.univ
            (fun x j => L ((1 / 2 : ℂ) *
              (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (D k (s, translate x ω) - W k (s, x))) +
              EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
                (fun k => D k (s, translate x ω)) j))
            (fun x => L (Y (s, x) -
              EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
                (fun k => D k (s, translate x ω)) i ζ -
              ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (D j (s, translate x ω) - W j (s, x)))))) ∧
        (∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          (∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0) ∧
          (∀ s ∈ Icc (-1 : ℝ) 1,
            MemLp (fun x => X (s, x)) 2 (volume.restrict K)) ∧
          (∀ a ∈ Icc (-1 : ℝ) 1,
            Tendsto (fun s => ∫ x in K, ‖X (s, x) - X (a, x)‖ ^ 2)
              (𝓝[Icc (-1 : ℝ) 1] a) (𝓝 0)) ∧
          MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          (∀ j, MemLp (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
            (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1) 2
            ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K))) ∧
          (∀ A : Set (Vec d), IsOpen A → A ⊆ K →
            ∀ B : Set (PDE.Vec 2), IsOpen B → volume B < ⊤ →
            ∀ r : ℝ, (∀ y ∈ B, y 0 ≤ r) →
            ∃ w : PDE.ParH1Function (PDE.vecAppendEquiv d 2 ⁻¹' (A ×ˢ B))
                (Icc (-1 : ℝ) 1),
              (∀ z, w.toFun z = (Complex.exp
                ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
                  X (z.2, (PDE.vecAppendEquiv d 2 z.1).1)).re) ∧
              (∀ z j, w.grad z (Fin.castAdd 2 j) = (Complex.exp
                ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D j (t, translate (PDE.vecAppendEquiv d 2 z.1).1 ω) -
                      W j (t, (PDE.vecAppendEquiv d 2 z.1).1)) z.2).re) ∧
              (∀ z, w.grad z (Fin.natAdd d (0 : Fin 2)) = w.toFun z) ∧
              (∀ z, w.grad z (Fin.natAdd d (1 : Fin 2)) = -(Complex.exp
                ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
                  X (z.2, (PDE.vecAppendEquiv d 2 z.1).1)).im)) ∧
          ∀ φ : ℝ × Vec d → ℝ,
            Continuous φ →
            Continuous (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1) →
            (∀ j, Continuous (fun p : ℝ × Vec d =>
              gradient (fun x => φ (p.1, x)) p.2 j)) →
            (∀ x, ContDiff ℝ 1 (fun s => φ (s, x))) →
            (∀ x, φ (-1, x) = 0) → (∀ x, φ (1, x) = 0) →
            (∀ s, IsSpatialTest K (fun x => φ (s, x))) →
            (∀ x ∈ K, χ x = 1) → ∀ L : ℂ →L[ℝ] ℝ,
            (∫ p : ℝ × Vec d,
              deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
              dot (fun j => L ((1 / 2 : ℂ) *
                ∑ k, ((ForcedLocality.retainedPair χ ω).1 p.2 j k : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D k (t, translate p.2 ω) - W k (t, p.2)) p.1))
                (gradient (fun x => φ (p.1, x)) p.2) +
              φ p * L (ζ * ∑ j,
                ((ForcedLocality.retainedPair χ ω).1 p.2 j i : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1)
              ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) = 0) ∧
        (∀ A : Set (Vec d), MeasurableSet A → (∀ x ∈ A, χ x = 1) →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakDivergence A
            (fun x j => L ((1 / 2 : ℂ) *
              ∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D k (t, translate x ω) - W k (t, x)) s))
            (fun x => L (Y (s, x) - ζ *
              ∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D j (t, translate x ω) - W j (t, x)) s)) ) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1),
          HasWeakGradient K (fun x => (X (s, x)).re)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).re) ∧
          HasWeakGradient K (fun x => (X (s, x)).im)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).im) := by
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_forward_clock_cutoff_spacetime_continuous Q hP hfg
  refine ⟨F, U, D, hF, hU, hD, heF, heU, heD, ?_⟩
  filter_upwards [hcoh] with ω hω
  refine ⟨hω.1, ?_⟩
  intro hωs χ hχs hc hχ Λ hA Pr hPr ν fr hfr
  obtain ⟨gr, hgr, V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, hlocal, hdiv, hgrad⟩ :=
      hω.2 hωs χ hχs hc hχ Λ hA Pr hPr ν fr hfr
  refine ⟨gr, hgr, V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, ?_, hdiv, hgrad⟩
  intro K hK hinit
  obtain ⟨hmatch, htime, hslice, hcont, hX2, hY2, hJ2, hPDE⟩ := hlocal K hK hinit
  refine ⟨hmatch, htime, hslice, hcont, hX2, hY2, hJ2, ?_, hPDE⟩
  intro A hA hAK B hB hBfinite r hr
  exact short_time_residual_complex_lift_ParH1 hA hAK hB hBfinite r hr X
    (fun j p => (Ioc (0 : ℝ) 1).indicator
      (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1)
    hX2 hJ2 hslice hcont (hgrad K hK hinit)

open PDE PDE.Parabolic.Energy Metric in
/-- A compactly supported `C¹` test admits a smooth approximation with simultaneous
uniform control of its value and every coordinate derivative. -/
private theorem endpoint_C1_test_approximation {d : ℕ} {φ : EinsteinRelation.Vec d → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    {K : Set (EinsteinRelation.Vec d)} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ)
    (hδK : cthickening δ (tsupport φ) ⊆ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : EinsteinRelation.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ K ∧ (∀ x, |φ x - ψ x| ≤ ε) ∧
      ∀ j x, |coordinateDerivative j φ x - coordinateDerivative j ψ x| ≤ ε := by
  let Dφ : Fin d → EinsteinRelation.Vec d → ℝ := fun j x => fderiv ℝ φ x (basisVec j)
  have hDc (j : Fin d) : Continuous (Dφ j) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDzero (j : Fin d) (x : EinsteinRelation.Vec d) (hx : x ∉ tsupport φ) : Dφ j x = 0 := by
    simp [Dφ, fderiv_of_notMem_tsupport ℝ hx]
  have hDcs (j : Fin d) : HasCompactSupport (Dφ j) := by
    refine HasCompactSupport.of_support_subset_isCompact hφc.isCompact ?_
    intro x hx
    by_contra h
    exact hx (hDzero j x h)
  obtain ⟨a₀, ha₀, hclose₀⟩ :=
    exists_forall_dist_wholeSpaceMollify_le hφ.continuous hφc hε
  have hex (j : Fin d) := exists_forall_dist_wholeSpaceMollify_le (hDc j) (hDcs j) hε
  choose a₁ ha₁ hclose₁ using hex
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      0 < a ∧ a ≤ δ ∧ a ≤ a₀ ∧ ∀ j, a ≤ a₁ j := by
    have hall : ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ j, a ≤ a₁ j := by
      rw [eventually_all]
      intro j
      filter_upwards [Ioc_mem_nhdsGT (ha₁ j)] with a ha using ha.2
    filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT hδ,
      Ioc_mem_nhdsGT ha₀, hall] with a ha hδa h₀a h₁a
    exact ⟨ha, hδa.2, h₀a.2, h₁a⟩
  obtain ⟨a, ha, haδ, haa₀, haa₁⟩ := hev.exists
  let ψ := wholeSpaceMollify a φ
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := moll_contDiff ha hφ.continuous.locallyIntegrable
  have hsupp : Function.support ψ ⊆ cthickening a (tsupport φ) :=
    PDE.Ch4Infra.support_wholeSpaceMollify_subset_cthickening ha
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact (hφc.isCompact.cthickening (r := a)) hsupp
  have hψK : tsupport ψ ⊆ K :=
    closure_minimal (hsupp.trans ((cthickening_mono haδ _).trans hδK)) hK.isClosed
  refine ⟨ψ, hψ, hψc, hψK, ?_, ?_⟩
  · intro x
    have hb := hclose₀ a ha haa₀ x
    rwa [Real.dist_eq, abs_sub_comm] at hb
  · intro j x
    have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
    have hd : fderiv ℝ ψ x (basisVec j) = wholeSpaceMollify a (Dφ j) x :=
      congrFun (euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn
        (hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport ha)
        (contDiff_scaledConvexApproxKernel hρ _) hφ.continuous.locallyIntegrable
        (HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := j) hφ)) x
    have hb := hclose₁ j a ha (haa₁ j) x
    rw [Real.dist_eq, abs_sub_comm] at hb
    rw [← hd] at hb
    simpa only [coordinateDerivative, unitVector, basisVec, Dφ] using hb

/-- A locally integrable weak divergence can be tested against compactly
supported `C¹` functions. This extends the test class without changing the
flux or its divergence. -/
theorem short_time_weak_divergence_C1 {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {F : Vec d → Vec d} {g : Vec d → ℝ} (hw : HasWeakDivergence U F g)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ interior U) :
    (∫ x in U, dot (F x) (gradient φ x)) = -(∫ x in U, g x * φ x) := by
  obtain ⟨δ, hδ, hδU⟩ := hφc.isCompact.exists_cthickening_subset_open isOpen_interior hφU
  let K := Metric.cthickening δ (tsupport φ)
  have hK : IsCompact K := hφc.isCompact.cthickening
  have hKU : K ⊆ U := hδU.trans interior_subset
  have hφK : tsupport φ ⊆ K := Metric.self_subset_cthickening _
  have hF (j : Fin d) : Integrable (fun x => F x j) (volume.restrict K) :=
    (hw.1 j).integrableOn_compact_subset hKU hK
  have hg : Integrable g (volume.restrict K) :=
    hw.2.1.integrableOn_compact_subset hKU hK
  have hbd {f q : Vec d → ℝ} (hf : Integrable f (volume.restrict K))
      (hq : Continuous q) (hqc : HasCompactSupport q) :
      Integrable (fun x => f x * q x) (volume.restrict K) := by
    obtain ⟨C, hC⟩ := hq.bounded_above_of_compact_support hqc
    exact hf.mul_bdd hq.aestronglyMeasurable (c := C) (Eventually.of_forall hC)
  have hder {q : Vec d → ℝ} (hq : ContDiff ℝ 1 q) (hqc : HasCompactSupport q)
      (j : Fin d) : Continuous (coordinateDerivative j q) ∧
      HasCompactSupport (coordinateDerivative j q) := by
    refine ⟨(hq.continuous_fderiv one_ne_zero).clm_apply continuous_const, ?_⟩
    refine HasCompactSupport.of_support_subset_isCompact hqc.isCompact ?_
    intro x hx
    by_contra h
    exact hx (by simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ h])
  have hcut {q : Vec d → ℝ} (hqK : tsupport q ⊆ K) :
      (∫ x in U, dot (F x) (gradient q x)) =
        ∫ x in K, dot (F x) (gradient q x) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hKU
    intro x hx
    have hxq : x ∉ tsupport q := fun h => hx.2 (hqK h)
    simp [dot, gradient, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxq]
  have hcutg {q : Vec d → ℝ} (hqK : tsupport q ⊆ K) :
      (∫ x in U, g x * q x) = ∫ x in K, g x * q x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hKU
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx.2 (hqK h)), mul_zero]
  have hsum {q : Vec d → ℝ} (hq : ContDiff ℝ 1 q) (hqc : HasCompactSupport q) :
      (∫ x in K, dot (F x) (gradient q x)) =
        ∑ j, ∫ x in K, F x j * coordinateDerivative j q x := by
    exact integral_finsetSum _ (fun j _ => hbd (hF j) (hder hq hqc j).1
      (hder hq hqc j).2)
  let E := (∫ x in K, dot (F x) (gradient φ x)) + ∫ x in K, g x * φ x
  let C := (∑ j, ∫ x in K, |F x j|) + ∫ x in K, |g x|
  have hmain (ε : ℝ) (hε : 0 < ε) : |E| ≤ ε * C := by
    obtain ⟨ψ, hψ, hψc, hψK, hclose, hDclose⟩ :=
      endpoint_C1_test_approximation hφ hφc hK hδ (Subset.refl K) hε
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
    have hid := hw.2.2 ψ ⟨hψ, hψc, hψK.trans hKU⟩
    rw [hcut hψK, hcutg hψK] at hid
    have hdiff : E = (∑ j, ∫ x in K, F x j *
        (coordinateDerivative j φ x - coordinateDerivative j ψ x)) +
        ∫ x in K, g x * (φ x - ψ x) := by
      simp_rw [mul_sub]
      rw [integral_sub (hbd hg hφ.continuous hφc) (hbd hg hψ.continuous hψc)]
      have hj (j : Fin d) := integral_sub
        (hbd (hF j) (hder hφ hφc j).1 (hder hφ hφc j).2)
        (hbd (hF j) (hder hψ1 hψc j).1 (hder hψ1 hψc j).2)
      simp_rw [hj]
      rw [Finset.sum_sub_distrib, ← hsum hφ hφc, ← hsum hψ1 hψc]
      dsimp [E]
      linarith
    have hb {f q : Vec d → ℝ} (hf : Integrable f (volume.restrict K))
        (hq : ∀ x, |q x| ≤ ε) :
        |∫ x in K, f x * q x| ≤ ε * ∫ x in K, |f x| := by
      calc
        |∫ x in K, f x * q x| ≤ ∫ x in K, |f x * q x| :=
          abs_integral_le_integral_abs
        _ ≤ ∫ x in K, ε * |f x| := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            (hf.abs.const_mul ε) (Eventually.of_forall ?_)
          intro x
          change |f x * q x| ≤ ε * |f x|
          rw [abs_mul]
          nlinarith [hq x, abs_nonneg (f x)]
        _ = ε * ∫ x in K, |f x| := integral_const_mul _ _
    rw [hdiff]
    calc
      _ ≤ |∑ j, ∫ x in K, F x j *
          (coordinateDerivative j φ x - coordinateDerivative j ψ x)| +
          |∫ x in K, g x * (φ x - ψ x)| := abs_add_le _ _
      _ ≤ (∑ j, |∫ x in K, F x j *
          (coordinateDerivative j φ x - coordinateDerivative j ψ x)|) +
          |∫ x in K, g x * (φ x - ψ x)| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl
      _ ≤ (∑ j, ε * ∫ x in K, |F x j|) + ε * ∫ x in K, |g x| :=
        add_le_add (Finset.sum_le_sum fun j _ => hb (hF j) (hDclose j)) (hb hg hclose)
      _ = ε * C := by rw [← Finset.mul_sum]; dsimp [C]; ring
  have hC : 0 ≤ C := add_nonneg
    (Finset.sum_nonneg fun j _ => integral_nonneg fun x => abs_nonneg _)
    (integral_nonneg fun x => abs_nonneg _)
  have hE : E = 0 := by
    by_contra hne
    have hpos := abs_pos.mpr hne
    have hb := hmain (|E| / (2 * (C + 1))) (by positivity)
    have hh : |E| / (2 * (C + 1)) * C < |E| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [hcut hφK, hcutg hφK]
  dsimp [E] at hE
  linarith

/-- The actual temporal weak identity and spatial divergence combine for `C¹`
spacetime tests compactly supported in the interior of the region. -/
theorem short_time_spacetime_weak_equation_C1 {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (u v b : ℝ × Vec d → ℝ)
    (F : ℝ × Vec d → Vec d)
    (htime : ∀ᵐ x ∂volume.restrict U, ∀ ψ : ℝ → ℝ,
      ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
      (∫ s in (-1 : ℝ)..1, deriv ψ s * u (s, x) + ψ s * v (s, x)) = 0)
    (hspace : ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1),
      HasWeakDivergence U (fun x => F (s, x)) (fun x => v (s, x) - b (s, x)))
    (φ : ℝ × Vec d → ℝ)
    (hφt : ∀ x, ContDiff ℝ 1 (fun s => φ (s, x)))
    (hφl : ∀ x, φ (-1, x) = 0) (hφr : ∀ x, φ (1, x) = 0)
    (hφx : ∀ s, ContDiff ℝ 1 (fun x => φ (s, x)) ∧
      HasCompactSupport (fun x => φ (s, x)) ∧ tsupport (fun x => φ (s, x)) ⊆ interior U)
    (hu : Integrable (fun p : ℝ × Vec d =>
      deriv (fun s => φ (s, p.2)) p.1 * u p)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)))
    (hv : Integrable (fun p : ℝ × Vec d => φ p * v p)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)))
    (hF : Integrable (fun p : ℝ × Vec d =>
      dot (F p) (gradient (fun x => φ (p.1, x)) p.2))
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)))
    (hb : Integrable (fun p : ℝ × Vec d => φ p * b p)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U))) :
    (∫ p : ℝ × Vec d,
      deriv (fun s => φ (s, p.2)) p.1 * u p -
        dot (F p) (gradient (fun x => φ (p.1, x)) p.2) + φ p * b p
      ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) = 0 := by
  have ht : (∫ p : ℝ × Vec d,
      deriv (fun s => φ (s, p.2)) p.1 * u p + φ p * v p
      ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) = 0 := by
    have hp := integral_prod_symm _ (hu.add hv)
    simp only [Pi.add_apply] at hp
    rw [hp]
    apply integral_eq_zero_of_ae
    filter_upwards [htime] with x hx
    have he := hx (fun s => φ (s, x)) (hφt x) (hφl x) (hφr x)
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc] at he
    exact he
  have hs : (∫ p : ℝ × Vec d,
      dot (F p) (gradient (fun x => φ (p.1, x)) p.2)
      ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) =
      -(∫ p : ℝ × Vec d, φ p * v p - φ p * b p
        ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) := by
    have hp := integral_prod _ (hv.sub hb)
    simp only [Pi.sub_apply] at hp
    rw [integral_prod _ hF, hp, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [hspace] with s hs
    have he := short_time_weak_divergence_C1 hU hs
      (hφx s).1 (hφx s).2.1 (hφx s).2.2
    rw [he]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hsum := integral_add (hu.sub hF) hb
  have hdiff := integral_sub hu hF
  have htv := integral_add hu hv
  have hvb := integral_sub hv hb
  simp only [Pi.sub_apply] at hsum hdiff htv hvb
  rw [hsum, hdiff]
  rw [htv] at ht
  rw [hvb] at hs
  linarith


/-- The same actual cutoff residual and its literal parabolic lift retain
both the smooth spatial identity and its `C¹` extension for tests compactly
supported inside the compact comparison region. -/
theorem short_time_forward_clock_cutoff_parabolic_lift_C1
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ Measurable U ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      (∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : ℝ × Vec d => ‖F (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        ∀ j, Integrable (fun p : ℝ × Vec d => ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K))) ∧
      ∀ (_ : IsSmoothFieldPair ω) (χ : C(Vec d, ℝ)),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ Λ : ℝ, (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ (ν : Fin d ⊕ Unit) (fr : Lp ℂ 2 (volume : Measure (Vec d))),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => match ν with
        | Sum.inl j => (χ x : ℂ) *
            ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
              (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ))
        | Sum.inr _ => ζ * (χ x : ℂ) * (ω.2 x : ℂ)) →
      ∃ gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr ∧
      ∃ V Z X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∃ W : Fin d → ℝ × Vec d → ℂ,
        (∀ j, Measurable (W j)) ∧
        (∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j) ∧
        (∀ (j : Fin d) (l r : ℝ), Integrable (fun p => ‖W j p‖ ^ 2)
          ((volume.restrict (Icc l r)).prod volume)) ∧
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pr s.toNNReal fr) (H s)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakGradient Set.univ (fun x => L (F (s, translate x ω)))
            (fun x j => L (D j (s, translate x ω))) ∧
          HasWeakDivergence Set.univ
            (fun x j => L ((1 / 2 : ℂ) *
              (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (D k (s, translate x ω) - W k (s, x))) +
              EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
                (fun k => D k (s, translate x ω)) j))
            (fun x => L (Y (s, x) -
              EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
                (fun k => D k (s, translate x ω)) i ζ -
              ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (D j (s, translate x ω) - W j (s, x)))))) ∧
        (∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          (∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0) ∧
          (∀ s ∈ Icc (-1 : ℝ) 1,
            MemLp (fun x => X (s, x)) 2 (volume.restrict K)) ∧
          (∀ a ∈ Icc (-1 : ℝ) 1,
            Tendsto (fun s => ∫ x in K, ‖X (s, x) - X (a, x)‖ ^ 2)
              (𝓝[Icc (-1 : ℝ) 1] a) (𝓝 0)) ∧
          MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          (∀ j, MemLp (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
            (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1) 2
            ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K))) ∧
          (∀ A : Set (Vec d), IsOpen A → A ⊆ K →
            ∀ B : Set (PDE.Vec 2), IsOpen B → volume B < ⊤ →
            ∀ r : ℝ, (∀ y ∈ B, y 0 ≤ r) →
            ∃ w : PDE.ParH1Function (PDE.vecAppendEquiv d 2 ⁻¹' (A ×ˢ B))
                (Icc (-1 : ℝ) 1),
              (∀ z, w.toFun z = (Complex.exp
                ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
                  X (z.2, (PDE.vecAppendEquiv d 2 z.1).1)).re) ∧
              (∀ z j, w.grad z (Fin.castAdd 2 j) = (Complex.exp
                ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D j (t, translate (PDE.vecAppendEquiv d 2 z.1).1 ω) -
                      W j (t, (PDE.vecAppendEquiv d 2 z.1).1)) z.2).re) ∧
              (∀ z, w.grad z (Fin.natAdd d (0 : Fin 2)) = w.toFun z) ∧
              (∀ z, w.grad z (Fin.natAdd d (1 : Fin 2)) = -(Complex.exp
                ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
                  X (z.2, (PDE.vecAppendEquiv d 2 z.1).1)).im)) ∧
          (∀ φ : ℝ × Vec d → ℝ,
            Continuous φ →
            Continuous (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1) →
            (∀ j, Continuous (fun p : ℝ × Vec d =>
              gradient (fun x => φ (p.1, x)) p.2 j)) →
            (∀ x, ContDiff ℝ 1 (fun s => φ (s, x))) →
            (∀ x, φ (-1, x) = 0) → (∀ x, φ (1, x) = 0) →
            (∀ s, IsSpatialTest K (fun x => φ (s, x))) →
            (∀ x ∈ K, χ x = 1) → ∀ L : ℂ →L[ℝ] ℝ,
            (∫ p : ℝ × Vec d,
              deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
              dot (fun j => L ((1 / 2 : ℂ) *
                ∑ k, ((ForcedLocality.retainedPair χ ω).1 p.2 j k : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D k (t, translate p.2 ω) - W k (t, p.2)) p.1))
                (gradient (fun x => φ (p.1, x)) p.2) +
              φ p * L (ζ * ∑ j,
                ((ForcedLocality.retainedPair χ ω).1 p.2 j i : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1)
              ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) = 0) ∧
          ∀ φ : ℝ × Vec d → ℝ,
            Continuous φ →
            Continuous (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1) →
            (∀ j, Continuous (fun p : ℝ × Vec d =>
              gradient (fun x => φ (p.1, x)) p.2 j)) →
            (∀ x, ContDiff ℝ 1 (fun s => φ (s, x))) →
            (∀ x, φ (-1, x) = 0) → (∀ x, φ (1, x) = 0) →
            (∀ s, ContDiff ℝ 1 (fun x => φ (s, x)) ∧
              HasCompactSupport (fun x => φ (s, x)) ∧
              tsupport (fun x => φ (s, x)) ⊆ interior K) →
            (∀ x ∈ K, χ x = 1) → ∀ L : ℂ →L[ℝ] ℝ,
            (∫ p : ℝ × Vec d,
              deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
              dot (fun j => L ((1 / 2 : ℂ) *
                ∑ k, ((ForcedLocality.retainedPair χ ω).1 p.2 j k : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D k (t, translate p.2 ω) - W k (t, p.2)) p.1))
                (gradient (fun x => φ (p.1, x)) p.2) +
              φ p * L (ζ * ∑ j,
                ((ForcedLocality.retainedPair χ ω).1 p.2 j i : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1)
              ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) = 0) ∧
        (∀ A : Set (Vec d), MeasurableSet A → (∀ x ∈ A, χ x = 1) →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakDivergence A
            (fun x j => L ((1 / 2 : ℂ) *
              ∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D k (t, translate x ω) - W k (t, x)) s))
            (fun x => L (Y (s, x) - ζ *
              ∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D j (t, translate x ω) - W j (t, x)) s)) ) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1),
          HasWeakGradient K (fun x => (X (s, x)).re)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).re) ∧
          HasWeakGradient K (fun x => (X (s, x)).im)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).im) := by
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_forward_clock_cutoff_parabolic_lift Q hP hfg
  refine ⟨F, U, D, hF, hU, hD, heF, heU, heD, ?_⟩
  filter_upwards [hcoh] with ω hω
  refine ⟨hω.1, ?_⟩
  intro hωs χ hχs hc hχ Λ hA Pr hPr ν fr hfr
  obtain ⟨gr, hgr, V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, hlocal, hdiv, hgrad⟩ :=
      hω.2 hωs χ hχs hc hχ Λ hA Pr hPr ν fr hfr
  refine ⟨gr, hgr, V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, ?_, hdiv, hgrad⟩
  intro K hK hinit
  obtain ⟨hmatch, htime, hslice, hcont, hX2, hY2, hJ2, hlift, hPDE⟩ := hlocal K hK hinit
  refine ⟨hmatch, htime, hslice, hcont, hX2, hY2, hJ2, hlift, hPDE, ?_⟩
  intro φ hφ hdt hdφ hφt hφl hφr hφx hχK L
  let J (j : Fin d) (p : ℝ × Vec d) : ℂ := (Ioc (0 : ℝ) 1).indicator
    (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1
  let a := (ForcedLocality.retainedPair χ ω).1
  let μ := (volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hmul {u v : ℝ × Vec d → ℂ} (hu : Continuous u) (hv : Integrable v μ) :
      Integrable (fun p => u p * v p) μ := by
    dsimp only [μ] at hv ⊢
    rw [Measure.prod_restrict] at hv ⊢
    exact IntegrableOn.continuousOn_mul hu.continuousOn hv (isCompact_Icc.prod hK)
  have hmulR {u v : ℝ × Vec d → ℝ} (hu : Continuous u) (hv : Integrable v μ) :
      Integrable (fun p => u p * v p) μ := by
    dsimp only [μ] at hv ⊢
    rw [Measure.prod_restrict] at hv ⊢
    exact IntegrableOn.continuousOn_mul hu.continuousOn hv (isCompact_Icc.prod hK)
  have hJ1 (j : Fin d) : Integrable (J j) μ :=
    (hJ2 j).integrable (by norm_num)
  have ha (j k : Fin d) : Continuous (fun p : ℝ × Vec d => (a p.2 j k : ℂ)) :=
    Complex.continuous_ofReal.comp ((a.continuous.matrix_elem j k).comp continuous_snd)
  have hflux (j : Fin d) : Integrable
      (fun p : ℝ × Vec d => L ((1 / 2 : ℂ) * ∑ k, (a p.2 j k : ℂ) * J k p)) μ :=
    L.integrable_comp ((integrable_finsetSum _ fun k _ => hmul (ha j k) (hJ1 k)).const_mul _)
  have hlow : Integrable
      (fun p : ℝ × Vec d => L (ζ * ∑ j, (a p.2 j i : ℂ) * J j p)) μ :=
    L.integrable_comp ((integrable_finsetSum _ fun j _ => hmul (ha j i) (hJ1 j)).const_mul _)
  apply short_time_spacetime_weak_equation_C1 K hK.measurableSet (fun p => L (X p)) (fun p => L (Y p))
    (fun p => L (ζ * ∑ j, (a p.2 j i : ℂ) * J j p))
    (fun p j => L ((1 / 2 : ℂ) * ∑ k, (a p.2 j k : ℂ) * J k p))
  · filter_upwards [htime] with x hx
    exact (hx L).2
  · filter_upwards [hdiv K hK.measurableSet hχK] with s hs
    simpa only [map_sub] using hs L
  · exact hφt
  · exact hφl
  · exact hφr
  · exact hφx
  · exact hmulR hdt (L.integrable_comp (hX2.integrable (by norm_num)))
  · exact hmulR hφ (L.integrable_comp (hY2.integrable (by norm_num)))
  · change Integrable (fun p : ℝ × Vec d =>
      ∑ j, L ((1 / 2 : ℂ) * ∑ k, (a p.2 j k : ℂ) * J k p) *
        gradient (fun x => φ (p.1, x)) p.2 j) μ
    exact integrable_finsetSum _ fun j _ => by
      simpa only [mul_comm] using hmulR (hdφ j) (hflux j)
  · exact hmulR hφ hlow


/-- The compact-region C1 identity gives the literal physical parabolic test
identity on every open subset, without changing the residual or its flux. -/
theorem short_time_C1_equation_parabolic_test {d : ℕ}
    {K A : Set (Vec d)} (hK : IsCompact K) (hA : IsOpen A) (hAK : A ⊆ K)
    (X b : ℝ × Vec d → ℂ) (P : Fin d → ℝ × Vec d → ℂ)
    (hweak : ∀ φ : ℝ × Vec d → ℝ,
      Continuous φ →
      Continuous (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1) →
      (∀ j, Continuous (fun p : ℝ × Vec d =>
        gradient (fun x => φ (p.1, x)) p.2 j)) →
      (∀ x, ContDiff ℝ 1 (fun s => φ (s, x))) →
      (∀ x, φ (-1, x) = 0) → (∀ x, φ (1, x) = 0) →
      (∀ s, ContDiff ℝ 1 (fun x => φ (s, x)) ∧
        HasCompactSupport (fun x => φ (s, x)) ∧
        tsupport (fun x => φ (s, x)) ⊆ interior K) →
      ∀ L : ℂ →L[ℝ] ℝ,
      (∫ p : ℝ × Vec d,
        deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
          dot (fun j => L (P j p)) (gradient (fun x => φ (p.1, x)) p.2) +
          φ p * L (b p)
        ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) = 0)
    (ψ : PDE.ParTestFunction A (interior (Icc (-1 : ℝ) 1))) (e : ℂ) :
    (∫ z in A ×ˢ Icc (-1 : ℝ) 1,
      -((e * X (z.2, z.1)).re * PDE.parTimeDeriv ψ.toFun z) +
        (∑ j, (e * P j (z.2, z.1)).re * PDE.parSpaceGrad ψ.toFun z j) -
        (e * b (z.2, z.1)).re * ψ.toFun z) = 0 := by
  let φ : ℝ × Vec d → ℝ := fun p => ψ.toFun (p.2, p.1)
  have ht (s : ℝ) (x : Vec d) :
      deriv (fun t => φ (t, x)) s = PDE.parTimeDeriv ψ.toFun (x, s) := by
    exact (((ψ.contDiff.differentiable (by norm_num)) (x, s)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_const s x).prodMk (hasDerivAt_id s))).deriv
  have hx (s : ℝ) (x : Vec d) (j : Fin d) :
      gradient (fun y => φ (s, y)) x j = PDE.parSpaceGrad ψ.toFun (x, s) j := by
    have hd := ((ψ.contDiff.differentiable (by norm_num)) (x, s)).hasFDerivAt
    have he := hd.comp x ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const s x))
    change HasFDerivAt (fun y => ψ.toFun (y, s)) _ x at he
    change fderiv ℝ (fun y => ψ.toFun (y, s)) x (unitVector j) = _
    rw [he.fderiv]
    rfl
  have hφc : Continuous φ := ψ.contDiff.continuous.comp continuous_swap
  have hdt : Continuous (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1) := by
    simp_rw [ht]
    exact ((ψ.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      continuous_swap
  have hdx (j : Fin d) : Continuous (fun p : ℝ × Vec d =>
      gradient (fun x => φ (p.1, x)) p.2 j) := by
    simp_rw [hx]
    exact ((ψ.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      continuous_swap
  have hφt (x : Vec d) : ContDiff ℝ 1 (fun s => φ (s, x)) :=
    ψ.contDiff.comp (contDiff_const.prodMk contDiff_id)
  have hend (s : ℝ) (hs : s ∉ interior (Icc (-1 : ℝ) 1)) (x : Vec d) : φ (s, x) = 0 := by
    change ψ.toFun (x, s) = 0
    exact image_eq_zero_of_notMem_tsupport (fun hz => hs (ψ.tsupport_subset hz).2)
  have hφx (s : ℝ) : ContDiff ℝ 1 (fun x => φ (s, x)) ∧
      HasCompactSupport (fun x => φ (s, x)) ∧
      tsupport (fun x => φ (s, x)) ⊆ interior K := by
    refine ⟨ψ.contDiff.comp (contDiff_id.prodMk contDiff_const), ?_, ?_⟩
    · apply ψ.hasCompactSupport.comp_isClosedEmbedding
      refine ⟨isEmbedding_prodMkLeft s, ?_⟩
      convert isClosed_eq (continuous_snd : Continuous (Prod.snd : Vec d × ℝ → ℝ))
        (continuous_const : Continuous (fun _ : Vec d × ℝ => s)) using 1
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        rfl
      · intro hz
        exact ⟨z.1, Prod.ext rfl hz.symm⟩
    · intro x hx'
      exact (hA.subset_interior_iff.mpr hAK) ((ψ.tsupport_subset
        (tsupport_comp_subset_preimage ψ.toFun (continuous_id.prodMk continuous_const) hx')).1)
  let L : ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ e)
  have hw := hweak φ hφc hdt hdx hφt
    (hend (-1) (by simp)) (hend 1 (by simp)) hφx L
  let f : Vec d × ℝ → ℝ := fun z =>
    -((e * X (z.2, z.1)).re * PDE.parTimeDeriv ψ.toFun z) +
      (∑ j, (e * P j (z.2, z.1)).re * PDE.parSpaceGrad ψ.toFun z j) -
      (e * b (z.2, z.1)).re * ψ.toFun z
  have hform : (fun p : ℝ × Vec d =>
      deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
        dot (fun j => L (P j p)) (gradient (fun x => φ (p.1, x)) p.2) +
        φ p * L (b p)) = fun p => -f p.swap := by
    funext p
    simp only [ht, dot, hx]
    dsimp [f, L, φ, Prod.swap]
    ring
  rw [hform, integral_neg, integral_prod_swap] at hw
  have hzK : (∫ z in K ×ˢ Icc (-1 : ℝ) 1, f z) = 0 := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    linarith
  have hoff (z : Vec d × ℝ) (hz : z.1 ∉ A) : f z = 0 := by
    have hs : z ∉ tsupport ψ.toFun := fun hz' => hz (ψ.tsupport_subset hz').1
    have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hs
    simp [f, PDE.parTimeDeriv, PDE.parSpaceGrad, hd, image_eq_zero_of_notMem_tsupport hs]
  have heq : (∫ z in K ×ˢ Icc (-1 : ℝ) 1, f z) =
      ∫ z in A ×ˢ Icc (-1 : ℝ) 1, f z := by
    calc
      _ = ∫ z in K ×ˢ Icc (-1 : ℝ) 1, (A ×ˢ Icc (-1 : ℝ) 1).indicator f z := by
        apply setIntegral_congr_fun (hK.measurableSet.prod measurableSet_Icc)
        intro z hz
        by_cases ha : z.1 ∈ A
        · simp [ha, hz.2]
        · simp [ha, hoff z ha]
      _ = ∫ z in (K ×ˢ Icc (-1 : ℝ) 1) ∩ (A ×ˢ Icc (-1 : ℝ) 1), f z :=
        setIntegral_indicator (hA.measurableSet.prod measurableSet_Icc)
      _ = _ := by rw [inter_eq_right.mpr (prod_mono hAK subset_rfl)]
  exact heq ▸ hzK


/-- The actual SAME cutoff residual has a homogeneous lifted parabolic equation
on every interior cylinder where the cutoff equals one. -/
theorem short_time_forward_clock_cutoff_homogeneous_lift
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ Measurable U ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      (∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : ℝ × Vec d => ‖F (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        ∀ j, Integrable (fun p : ℝ × Vec d => ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K))) ∧
      ∀ (_ : IsSmoothFieldPair ω) (χ : C(Vec d, ℝ)),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ Λ : ℝ, (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ (ν : Fin d ⊕ Unit) (fr : Lp ℂ 2 (volume : Measure (Vec d))),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => match ν with
        | Sum.inl j => (χ x : ℂ) *
            ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
              (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ))
        | Sum.inr _ => ζ * (χ x : ℂ) * (ω.2 x : ℂ)) →
      ∃ gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr ∧
      ∃ V Z X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∃ W : Fin d → ℝ × Vec d → ℂ,
        (∀ j, Measurable (W j)) ∧
        (∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j) ∧
        (∀ (j : Fin d) (l r : ℝ), Integrable (fun p => ‖W j p‖ ^ 2)
          ((volume.restrict (Icc l r)).prod volume)) ∧
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pr s.toNNReal fr) (H s)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakGradient Set.univ (fun x => L (F (s, translate x ω)))
            (fun x j => L (D j (s, translate x ω))) ∧
          HasWeakDivergence Set.univ
            (fun x j => L ((1 / 2 : ℂ) *
              (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (D k (s, translate x ω) - W k (s, x))) +
              EinsteinFull.C9ShortTimeLocality.retainedFluxDefect χ ω x
                (fun k => D k (s, translate x ω)) j))
            (fun x => L (Y (s, x) -
              EinsteinFull.C9ShortTimeLocality.retainedDriftDefect χ ω x
                (fun k => D k (s, translate x ω)) i ζ -
              ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (D j (s, translate x ω) - W j (s, x)))))) ∧
        (∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          (∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0) ∧
          (∀ s ∈ Icc (-1 : ℝ) 1,
            MemLp (fun x => X (s, x)) 2 (volume.restrict K)) ∧
          (∀ a ∈ Icc (-1 : ℝ) 1,
            Tendsto (fun s => ∫ x in K, ‖X (s, x) - X (a, x)‖ ^ 2)
              (𝓝[Icc (-1 : ℝ) 1] a) (𝓝 0)) ∧
          MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          (∀ j, MemLp (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
            (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1) 2
            ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K))) ∧
          ((∀ x ∈ K, χ x = 1) →
            ∀ A : Set (Vec d), IsOpen A → A ⊆ K →
            ∀ B : Set (PDE.Vec 2), IsOpen B → volume B < ⊤ →
            ∀ r : ℝ, (∀ y ∈ B, y 0 ≤ r) →
            ∃ w : PDE.ParH1Function (PDE.vecAppendEquiv d 2 ⁻¹' (A ×ˢ B))
                (Icc (-1 : ℝ) 1),
              (∀ z, w.toFun z = (Complex.exp
                ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
                  X (z.2, (PDE.vecAppendEquiv d 2 z.1).1)).re) ∧
              (∀ z j, w.grad z (Fin.castAdd 2 j) = (Complex.exp
                ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D j (t, translate (PDE.vecAppendEquiv d 2 z.1).1 ω) -
                      W j (t, (PDE.vecAppendEquiv d 2 z.1).1)) z.2).re) ∧
              (∀ z, w.grad z (Fin.natAdd d (0 : Fin 2)) = w.toFun z) ∧
              (∀ z, w.grad z (Fin.natAdd d (1 : Fin 2)) = -(Complex.exp
                ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
                  X (z.2, (PDE.vecAppendEquiv d 2 z.1).1)).im) ∧
              ∀ M : ℝ, PDE.IsParabolicWeakSolution
                (fun z => shortTimeComplexLiftMatrix
                  ((ForcedLocality.retainedPair χ ω).1 (PDE.vecAppendEquiv d 2 z.1).1)
                  i ζ M)
                (PDE.vecAppendEquiv d 2 ⁻¹' (A ×ˢ B)) (Icc (-1 : ℝ) 1) w) ∧
          (∀ φ : ℝ × Vec d → ℝ,
            Continuous φ →
            Continuous (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1) →
            (∀ j, Continuous (fun p : ℝ × Vec d =>
              gradient (fun x => φ (p.1, x)) p.2 j)) →
            (∀ x, ContDiff ℝ 1 (fun s => φ (s, x))) →
            (∀ x, φ (-1, x) = 0) → (∀ x, φ (1, x) = 0) →
            (∀ s, IsSpatialTest K (fun x => φ (s, x))) →
            (∀ x ∈ K, χ x = 1) → ∀ L : ℂ →L[ℝ] ℝ,
            (∫ p : ℝ × Vec d,
              deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
              dot (fun j => L ((1 / 2 : ℂ) *
                ∑ k, ((ForcedLocality.retainedPair χ ω).1 p.2 j k : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D k (t, translate p.2 ω) - W k (t, p.2)) p.1))
                (gradient (fun x => φ (p.1, x)) p.2) +
              φ p * L (ζ * ∑ j,
                ((ForcedLocality.retainedPair χ ω).1 p.2 j i : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1)
              ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) = 0) ∧
          ∀ φ : ℝ × Vec d → ℝ,
            Continuous φ →
            Continuous (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1) →
            (∀ j, Continuous (fun p : ℝ × Vec d =>
              gradient (fun x => φ (p.1, x)) p.2 j)) →
            (∀ x, ContDiff ℝ 1 (fun s => φ (s, x))) →
            (∀ x, φ (-1, x) = 0) → (∀ x, φ (1, x) = 0) →
            (∀ s, ContDiff ℝ 1 (fun x => φ (s, x)) ∧
              HasCompactSupport (fun x => φ (s, x)) ∧
              tsupport (fun x => φ (s, x)) ⊆ interior K) →
            (∀ x ∈ K, χ x = 1) → ∀ L : ℂ →L[ℝ] ℝ,
            (∫ p : ℝ × Vec d,
              deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
              dot (fun j => L ((1 / 2 : ℂ) *
                ∑ k, ((ForcedLocality.retainedPair χ ω).1 p.2 j k : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D k (t, translate p.2 ω) - W k (t, p.2)) p.1))
                (gradient (fun x => φ (p.1, x)) p.2) +
              φ p * L (ζ * ∑ j,
                ((ForcedLocality.retainedPair χ ω).1 p.2 j i : ℂ) *
                  (Ioc (0 : ℝ) 1).indicator
                    (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1)
              ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) = 0) ∧
        (∀ A : Set (Vec d), MeasurableSet A → (∀ x ∈ A, χ x = 1) →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakDivergence A
            (fun x j => L ((1 / 2 : ℂ) *
              ∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D k (t, translate x ω) - W k (t, x)) s))
            (fun x => L (Y (s, x) - ζ *
              ∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
                (Ioc (0 : ℝ) 1).indicator
                  (fun t => D j (t, translate x ω) - W j (t, x)) s)) ) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1),
          HasWeakGradient K (fun x => (X (s, x)).re)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).re) ∧
          HasWeakGradient K (fun x => (X (s, x)).im)
            (fun x j => ((Ioc (0 : ℝ) 1).indicator
              (fun t => D j (t, translate x ω) - W j (t, x)) s).im) := by
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_forward_clock_cutoff_parabolic_lift_C1 Q hP hfg
  refine ⟨F, U, D, hF, hU, hD, heF, heU, heD, ?_⟩
  filter_upwards [hcoh] with ω hω
  refine ⟨hω.1, ?_⟩
  intro hωs χ hχs hc hχ Λ hA Pr hPr ν fr hfr
  obtain ⟨gr, hgr, V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, hlocal, hdiv, hgrad⟩ :=
      hω.2 hωs χ hχs hc hχ Λ hA Pr hPr ν fr hfr
  refine ⟨gr, hgr, V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, ?_, hdiv, hgrad⟩
  intro K hK hinit
  obtain ⟨hmatch, htime, hslice, hcont, hX2, hY2, hJ2, hlift, hPDE, hC1⟩ := hlocal K hK hinit
  refine ⟨hmatch, htime, hslice, hcont, hX2, hY2, hJ2, ?_, hPDE, hC1⟩
  intro hχK A hAo hAK B hBo hBfinite r hr
  obtain ⟨w, hw, hDw, h0, h1⟩ := hlift A hAo hAK B hBo hBfinite r hr
  refine ⟨w, hw, hDw, h0, h1, ?_⟩
  intro M
  let J (j : Fin d) (z : Vec d × ℝ) : ℂ := (Ioc (0 : ℝ) 1).indicator
    (fun t => D j (t, translate z.1 ω) - W j (t, z.1)) z.2
  let a := (ForcedLocality.retainedPair χ ω).1
  let : IsFiniteMeasure (volume.restrict (K ×ˢ Icc (-1 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (hK.prod isCompact_Icc).measure_ne_top
  have hmul {u v : Vec d × ℝ → ℂ} (hu : Continuous u)
      (hv : IntegrableOn v (K ×ˢ Icc (-1 : ℝ) 1)) :
      IntegrableOn (fun z => u z * v z) (K ×ˢ Icc (-1 : ℝ) 1) :=
    IntegrableOn.continuousOn_mul hu.continuousOn hv (hK.prod isCompact_Icc)
  have hJ1 (j : Fin d) : IntegrableOn (J j) (K ×ˢ Icc (-1 : ℝ) 1) :=
    (endpoint_memLp_space_time (hJ2 j)).integrable (by norm_num)
  have ha (j k : Fin d) : Continuous (fun z : Vec d × ℝ => (a z.1 j k : ℂ)) :=
    Complex.continuous_ofReal.comp ((a.continuous.matrix_elem j k).comp continuous_fst)
  have hflux (j : Fin d) : IntegrableOn
      (fun z : Vec d × ℝ => (1 / 2 : ℂ) * ∑ k, (a z.1 j k : ℂ) * J k z)
      (A ×ˢ Icc (-1 : ℝ) 1) :=
    IntegrableOn.mono_set ((integrable_finsetSum _ fun k _ => hmul (ha j k) (hJ1 k)).const_mul _)
      (prod_mono hAK subset_rfl)
  have hlow : IntegrableOn
      (fun z : Vec d × ℝ => ∑ j, (a z.1 j i : ℂ) * J j z)
      (A ×ˢ Icc (-1 : ℝ) 1) :=
    IntegrableOn.mono_set (integrable_finsetSum _ fun j _ => hmul (ha j i) (hJ1 j))
      (prod_mono hAK subset_rfl)
  apply short_time_complex_lift_isParabolicWeakSolution hAo.measurableSet hBo.measurableSet
    measurableSet_Icc hBfinite r hr a i (fun z => X (z.2, z.1)) J ζ M
    (IntegrableOn.mono_set ((endpoint_memLp_space_time hX2).integrable (by norm_num))
      (prod_mono hAK subset_rfl)) hflux hlow ?_ w hw hDw h0 h1
  intro ψ e
  apply short_time_C1_equation_parabolic_test hK hAo hAK X
    (fun p => ζ * ∑ j, (a p.2 j i : ℂ) * J j (p.2, p.1))
    (fun j p => (1 / 2 : ℂ) * ∑ k, (a p.2 j k : ℂ) * J k (p.2, p.1)) ?_ ψ e
  intro φ hφ hdt hdφ hφt hφl hφr hφx L
  exact hC1 φ hφ hdt hdφ hφt hφl hφr hφx hχK L



private theorem endpoint_normalized_lift_local_max
    {d : ℕ} (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Afield : EinsteinRelation.CoefficientField d),
    (∀ x, S5Elliptic (Afield x) Λ) → ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (X : ℝ × Vec d → ℂ)
      (w : PDE.ParH1Function (PDE.vecAppendEquiv d 2 ⁻¹'
        (PDE.euclideanBall (0 : PDE.Vec d) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec 2) 1))
        (Icc (-1 : ℝ) 1)),
    (∀ z, w.toFun z = (Complex.exp
      ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
        X (z.2, (PDE.vecAppendEquiv d 2 z.1).1)).re) →
    (∀ M : ℝ, PDE.IsParabolicWeakSolution
      (fun z => shortTimeComplexLiftMatrix (Afield (PDE.vecAppendEquiv d 2 z.1).1) i ζ M)
      (PDE.vecAppendEquiv d 2 ⁻¹'
        (PDE.euclideanBall (0 : PDE.Vec d) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec 2) 1))
      (Icc (-1 : ℝ) 1) w) →
          ∀ (q : ℝ), 0 < q → q ≤ 1 → ∀ T : ℝ,
          -1 ≤ T - 4 * Λ * q ^ 2 → T ≤ 1 →
          let v : PDE.Vec (d + 2) × ℝ → ℝ := fun z =>
            (Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
              q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
                X (T + 4 * Λ * q ^ 2 * z.2,
                  q • (PDE.vecAppendEquiv d 2 z.1).1)).re
          MemLp v 2 (volume.restrict
            (PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1 ×ˢ Ioc (-1 : ℝ) 0)) ∧
          essSup (fun z => ENNReal.ofReal |v z|)
            (volume.restrict (EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (3 / 8) (-11 / 16))) ≤
            ENNReal.ofReal C *
              (∫⁻ z in EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (1 / 2) (-3 / 4),
                ENNReal.ofReal |v z| ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹  := by
  obtain ⟨L, hL, hmatrix⟩ := short_time_complex_lift_normalized_ellipticity Λ B hΛ hB
  obtain ⟨C₀, hC₀, hstep⟩ := EinsteinFull.SignedLocalMax.power_step_S (d + 2) (by omega)
  obtain ⟨C, hC, hmax⟩ :=
    EinsteinFull.SignedLocalMax.signed_local_max_L2 (d + 2) (by omega) hC₀ hstep L hL
  refine ⟨C, hC, ?_⟩
  intro Afield hA i ζ hζ X w hw hweak q hq hq1 T hT₀ hT₁
  let E := PDE.vecAppendEquiv d 2 ⁻¹'
    (PDE.euclideanBall (0 : PDE.Vec d) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec 2) 1)
  have hqE : PDE.euclideanBall (0 : PDE.Vec (d + 2)) q ⊆ E :=
    (PDE.euclideanBall_mono hq.le hq1).trans
      (PDE.euclideanBall_subset_preimage_vecAppendEquiv_prod d 2 zero_lt_one)
  let wq := PDE.Parabolic.NashLower.restrictParH1 hqE (Subset.rfl : Icc (-1 : ℝ) 1 ⊆ _) w
  let M := 4 * Λ ^ 3 * (B ^ 2 + 1)
  let a : PDE.ParCoeffField (d + 2) := fun z =>
    shortTimeComplexLiftMatrix
      (Afield (PDE.vecAppendEquiv d 2 z.1).1) i ζ M
  have hwq : PDE.IsParabolicWeakSolution a _ _ wq :=
    PDE.Parabolic.NashLower.isParabolicWeakSolution_restrict hqE Subset.rfl (hweak M)
  have hΛ₀ : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let r := Real.sqrt (4 * Λ)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 4 * Λ := Real.sq_sqrt (by positivity)
  let J : Set ℝ := Ioc (-(q ^ 2)) 0
  have hJI : PDE.Parabolic.Rescale.timeMap T r '' J ⊆ Icc (-1 : ℝ) 1 := by
    rintro _ ⟨s, hs, rfl⟩
    change -1 ≤ T + r ^ 2 * s ∧ T + r ^ 2 * s ≤ 1
    rw [hr2]
    have hlo := mul_le_mul_of_nonneg_left hs.1.le (by positivity : 0 ≤ 4 * Λ)
    have hhi := mul_le_mul_of_nonneg_left hs.2 (by positivity : 0 ≤ 4 * Λ)
    constructor <;> linarith only [hlo, hhi, hT₀, hT₁]
  let wt := shortTimeParabolicTimeRescale T hr hJI wq
  have hwt : PDE.IsParabolicWeakSolution
      (fun z => r ^ 2 • a (shortTimeParabolicTimeHomeomorph (d + 2) T hr z))
      (PDE.euclideanBall (0 : PDE.Vec (d + 2)) q) J wt :=
    short_time_time_rescale_isParabolicWeakSolution T hr
    (PDE.isOpen_euclideanBall _ _).measurableSet measurableSet_Icc hJI a wq hwq
  have hqJ : Ioc (0 - q ^ 2) 0 ⊆ J := by simp only [zero_sub]; exact Subset.rfl
  let wn := PDE.Parabolic.Rescale.rescaleParH1 (0 : PDE.Vec (d + 2)) hq 0 hqJ wt
  let an : PDE.ParCoeffField (d + 2) := fun z =>
    r ^ 2 • a (shortTimeParabolicTimeHomeomorph (d + 2) T hr
      (PDE.Parabolic.Rescale.cylMap 0 q 0 z))
  have hwn : PDE.IsParabolicWeakSolution an _ _ wn :=
    PDE.Parabolic.Rescale.isParabolicWeakSolution_rescale
      (fun z => r ^ 2 • a (shortTimeParabolicTimeHomeomorph (d + 2) T hr z)) 0 hq 0
      measurableSet_Ioc hqJ wt hwt
  have hean : an = fun z => (4 * Λ) • shortTimeComplexLiftMatrix
      (Afield
        (q • (PDE.vecAppendEquiv d 2 z.1).1)) i ζ M := by
    funext z
    simp [an, a, shortTimeParabolicTimeHomeomorph, PDE.Parabolic.Rescale.cylMap,
      PDE.Parabolic.Rescale.spaceMap_apply, hr2, map_smul]
  have hcoeff : PDE.IsParabolicCoeff 1 L an
      (PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1) (Ioc (-1 : ℝ) 0) := by
    rw [hean]
    refine ⟨fun j k => ?_, ?_⟩
    · have hentry := short_time_continuous_lift_entry_continuous
        Afield i ζ M (4 * Λ) j k
      have hmap : Continuous (fun z : PDE.Vec (d + 2) × ℝ => (q • z.1, z.2)) :=
        (continuous_fst.const_smul q).prodMk continuous_snd
      simpa only [Function.comp_def, map_smul, ContinuousLinearEquiv.coe_coe, Prod.smul_fst] using
        (hentry.comp hmap).measurable.aemeasurable
    · exact Filter.Eventually.of_forall fun z => hmatrix _ (hA _) i ζ hζ
  have hbound := hmax an hcoeff wn hwn
  have hewn : wn.toFun = fun z : PDE.Vec (d + 2) × ℝ =>
      (Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
        q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
        X (T + 4 * Λ * q ^ 2 * z.2, q • (PDE.vecAppendEquiv d 2 z.1).1)).re := by
    funext z
    change w.toFun _ = _
    rw [hw]
    simp [shortTimeParabolicTimeHomeomorph, PDE.Parabolic.Rescale.cylMap,
      PDE.Parabolic.Rescale.spaceMap_apply, PDE.Parabolic.Rescale.timeMap, hr2, map_smul, mul_assoc]
  exact ⟨by simpa only [hewn] using wn.memL2, by simpa only [hewn] using hbound⟩


/-- A force-disc-uniform local maximum for the actual SAME cutoff residual.
The two auxiliary coordinates and the physical time change remain explicit. -/
theorem short_time_forward_clock_cutoff_normalized_local_max
    {d : ℕ} (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    IsComplexEnvironmentSemigroup Q i ζ P →
    ∀ (f g : Lp ℂ 2 (reducedLaw Q)), IsComplexGeneratorPair Q i ζ f g →
    ∃ F : ℝ × FieldPair d → ℂ, Measurable F ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ (_ : IsSmoothFieldPair ω) (χ : C(Vec d, ℝ)),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ (ν : Fin d ⊕ Unit) (fr : Lp ℂ 2 (volume : Measure (Vec d))),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => match ν with
        | Sum.inl j => (χ x : ℂ) *
            ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
              (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ))
        | Sum.inr _ => ζ * (χ x : ℂ) * (ω.2 x : ℂ)) →
      ∃ V X : ℝ × Vec d → ℂ, Measurable V ∧ Measurable X ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        (∀ x ∈ K, χ x = 1) →
        PDE.euclideanBall (0 : PDE.Vec d) 1 ⊆ K →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          ∀ (q : ℝ), 0 < q → q ≤ 1 → ∀ T : ℝ,
          -1 ≤ T - 4 * Λ * q ^ 2 → T ≤ 1 →
          let v : PDE.Vec (d + 2) × ℝ → ℝ := fun z =>
            (Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
              q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
                X (T + 4 * Λ * q ^ 2 * z.2,
                  q • (PDE.vecAppendEquiv d 2 z.1).1)).re
          MemLp v 2 (volume.restrict
            (PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1 ×ˢ Ioc (-1 : ℝ) 0)) ∧
          essSup (fun z => ENNReal.ofReal |v z|)
            (volume.restrict (EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (3 / 8) (-11 / 16))) ≤
            ENNReal.ofReal C *
              (∫⁻ z in EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (1 / 2) (-3 / 4),
                ENNReal.ofReal |v z| ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹  := by
  obtain ⟨C, hC, hmax⟩ := endpoint_normalized_lift_local_max Λ B hΛ hB
  refine ⟨C, hC, ?_⟩
  intro Λ₀ r₀ Q i ζ hζ P hP f g hfg
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_forward_clock_cutoff_homogeneous_lift Q hP hfg
  refine ⟨F, hF, heF, ?_⟩
  filter_upwards [hcoh] with ω hω
  intro hωs χ hχs hc hχ hA Pr hPr ν fr hfr
  obtain ⟨gr, hgr, V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, hlocal, hdiv, hgrad⟩ :=
      hω.2 hωs χ hχs hc hχ Λ hA Pr hPr ν fr hfr
  refine ⟨V, X, hV, hX, heV, hX0, ?_⟩
  intro K hK hinit hχK hball
  obtain ⟨hmatch, htime, hslice, hcont, hX2, hY2, hJ2, hlift, hPDE, hC1⟩ := hlocal K hK hinit
  refine ⟨hmatch, hX2, ?_⟩
  intro q hq hq1 T hT₀ hT₁
  let A := PDE.euclideanBall (0 : PDE.Vec d) 1
  let B₂ := PDE.euclideanBall (0 : PDE.Vec 2) 1
  have hAo : IsOpen A := PDE.isOpen_euclideanBall _ _
  have hBo : IsOpen B₂ := PDE.isOpen_euclideanBall _ _
  have hBfinite : volume B₂ < ⊤ := (PDE.volume_euclideanBall_ne_top _ zero_le_one).lt_top
  have hBr : ∀ y ∈ B₂, y 0 ≤ (1 : ℝ) := by
    intro y hy
    have hn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one).1 hy
    simp only [sub_zero] at hn
    exact ((le_abs_self _).trans (PDE.abs_apply_le_vecEuclideanNorm y 0)).trans hn.le
  obtain ⟨w, hw, hDw, hw0, hw1, hweak⟩ :=
    hlift hχK A hAo hball B₂ hBo hBfinite 1 hBr
  exact hmax (ForcedLocality.retainedPair χ ω).1 hA i ζ hζ X w hw hweak
    q hq hq1 T hT₀ hT₁

/-- The SAME residual belongs to the physical slab used by the normalized
local maximum; its time and space restrictions are both literal. -/
private theorem endpoint_residual_memLp_normalized_slab {d : ℕ}
    {K : Set (Vec d)} {X : ℝ × Vec d → ℂ}
    (hX : MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (hball : PDE.euclideanBall (0 : PDE.Vec d) 1 ⊆ K)
    {q T Λ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hT₀ : -1 ≤ T - 4 * Λ * q ^ 2) (hT₁ : T ≤ 1) :
    MemLp X 2 (volume.restrict
      (Icc (T - 4 * Λ * q ^ 2) T ×ˢ PDE.euclideanBall (0 : PDE.Vec d) q)) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hX
  apply hX.mono_measure
  apply Measure.restrict_mono_set
  exact prod_mono (Icc_subset_Icc hT₀ hT₁)
    ((PDE.euclideanBall_mono hq.le hq1).trans hball)

/-- Two non-collinear phases of the real exponential lift control the full
complex value. This is the scalar step in recovering both residual components. -/
private theorem endpoint_complex_norm_le_of_two_phases (z : ℂ) {θ L : ℝ}
    (hθ : 0 < Real.sin θ) (h₀ : |z.re| ≤ L)
    (h₁ : |(Complex.exp ⟨0, θ⟩ * z).re| ≤ L) :
    ‖z‖ ≤ (1 + 2 / Real.sin θ) * L := by
  have he : Real.sin θ * z.im =
      Real.cos θ * z.re - (Complex.exp ⟨0, θ⟩ * z).re := by
    simp only [Complex.mul_re, Complex.exp_re, Complex.exp_im,
      Real.exp_zero, one_mul]
    ring
  have hi : Real.sin θ * |z.im| ≤ 2 * L := by
    calc
      Real.sin θ * |z.im| = |Real.sin θ * z.im| := by
        rw [abs_mul, abs_of_pos hθ]
      _ = |Real.cos θ * z.re - (Complex.exp ⟨0, θ⟩ * z).re| := congrArg abs he
      _ ≤ |Real.cos θ * z.re| + |(Complex.exp ⟨0, θ⟩ * z).re| := abs_sub _ _
      _ ≤ |z.re| + L := add_le_add (by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one θ)) h₁
      _ ≤ 2 * L := by linarith only [h₀]
  have him : |z.im| ≤ 2 * L / Real.sin θ :=
    (le_div_iff₀ hθ).2 (by simpa only [mul_comm] using hi)
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ L + 2 * L / Real.sin θ := add_le_add h₀ him
    _ = (1 + 2 / Real.sin θ) * L := by ring

/-- The auxiliary exponential is continuous, so its almost-everywhere bound
controls both non-collinear phases at every auxiliary point. -/
private theorem endpoint_complex_norm_le_of_auxiliary_ae_bound
    (z : ℂ) {q r L : ℝ} (hr : 0 < r)
    (hθ : 0 < Real.sin (q * (r / 2)))
    (h : ∀ᵐ y ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec 2) r),
      |(Complex.exp ⟨q * y 0, q * y 1⟩ * z).re| ≤ L) :
    ‖z‖ ≤ (1 + 2 / Real.sin (q * (r / 2))) * L := by
  have hc : Continuous (fun y : PDE.Vec 2 =>
      |(Complex.exp ⟨q * y 0, q * y 1⟩ * z).re|) := by
    simpa only [Complex.mul_re, Complex.exp_re, Complex.exp_im] using
      (show Continuous (fun y : PDE.Vec 2 =>
        |Real.exp (q * y 0) * Real.cos (q * y 1) * z.re -
          Real.exp (q * y 0) * Real.sin (q * y 1) * z.im|) by fun_prop)
  have hp := PDE.Parabolic.Moser.continuousOn_le_of_ae_restrict_le
    (PDE.isOpen_euclideanBall (0 : PDE.Vec 2) r) hc.continuousOn h
  have hzero : (0 : PDE.Vec 2) ∈ PDE.euclideanBall (0 : PDE.Vec 2) r := by
    change PDE.vecNormSq ((0 : PDE.Vec 2) - 0) < r ^ 2
    simpa only [sub_self, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero] using sq_pos_of_pos hr
  have hphase : (![0, r / 2] : PDE.Vec 2) ∈
      PDE.euclideanBall (0 : PDE.Vec 2) r := by
    change PDE.vecNormSq ((![0, r / 2] : PDE.Vec 2) - 0) < r ^ 2
    simp only [sub_zero, PDE.vecNormSq, PDE.vecDot, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_add]
    nlinarith only [sq_pos_of_pos hr]
  apply endpoint_complex_norm_le_of_two_phases z hθ
  · have hzero' := hp 0 hzero
    simpa only [Pi.zero_apply, mul_zero, Complex.mul_re, Complex.exp_re,
      Complex.exp_im, Real.exp_zero, Real.cos_zero, Real.sin_zero,
      one_mul, zero_mul, sub_zero] using hzero'
  · simpa using hp (![0, r / 2] : PDE.Vec 2) hphase

/-- The actual normalized residual maximum, bounded by its literal physical energy. -/
theorem short_time_forward_clock_cutoff_normalized_local_max_energy
    {d : ℕ} (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    IsComplexEnvironmentSemigroup Q i ζ P →
    ∀ (f g : Lp ℂ 2 (reducedLaw Q)), IsComplexGeneratorPair Q i ζ f g →
    ∃ F : ℝ × FieldPair d → ℂ, Measurable F ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ (_ : IsSmoothFieldPair ω) (χ : C(Vec d, ℝ)),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ (ν : Fin d ⊕ Unit) (fr : Lp ℂ 2 (volume : Measure (Vec d))),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => match ν with
        | Sum.inl j => (χ x : ℂ) *
            ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
              (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ))
        | Sum.inr _ => ζ * (χ x : ℂ) * (ω.2 x : ℂ)) →
      ∃ V X : ℝ × Vec d → ℂ, Measurable V ∧ Measurable X ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        (∀ x ∈ K, χ x = 1) →
        PDE.euclideanBall (0 : PDE.Vec d) 1 ⊆ K →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          ∀ (q : ℝ), 0 < q → q ≤ 1 → ∀ T : ℝ,
          -1 ≤ T - 4 * Λ * q ^ 2 → T ≤ 1 →
          let v : PDE.Vec (d + 2) × ℝ → ℝ := fun z =>
            (Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
              q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
                X (T + 4 * Λ * q ^ 2 * z.2,
                  q • (PDE.vecAppendEquiv d 2 z.1).1)).re
          MemLp v 2 (volume.restrict
            (PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1 ×ˢ Ioc (-1 : ℝ) 0)) ∧
          essSup (fun z => ENNReal.ofReal |v z|)
            (volume.restrict (EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (3 / 8) (-11 / 16))) ≤
            ENNReal.ofReal C *
              (ENNReal.ofReal ((1 : ℝ) / q ^ (d + 2)) *
                ∫⁻ z in Set.Icc (T - 4 * Λ * q ^ 2) T ×ˢ PDE.euclideanBall (0 : PDE.Vec d) q,
                  ENNReal.ofReal ‖X z‖ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := by
  obtain ⟨C₀, hC₀, hmax⟩ := short_time_forward_clock_cutoff_normalized_local_max Λ B hΛ hB
  obtain ⟨C₁, hC₁, henergy⟩ := short_time_normalized_lift_energy d
  refine ⟨C₀ * C₁ ^ (2 : ℝ)⁻¹,
    mul_pos hC₀ (Real.rpow_pos_of_pos hC₁ _), ?_⟩
  intro Λ₀ r₀ Q i ζ hζ P hP f g hfg
  obtain ⟨F, hF, heF, hcoh⟩ := hmax Q i ζ hζ P hP f g hfg
  refine ⟨F, hF, heF, ?_⟩
  filter_upwards [hcoh] with ω hω
  intro hωs χ hχs hc hχ hA Pr hPr ν fr hfr
  obtain ⟨V, X, hV, hX, heV, hX0, hlocal⟩ :=
    hω hωs χ hχs hc hχ hA Pr hPr ν fr hfr
  refine ⟨V, X, hV, hX, heV, hX0, ?_⟩
  intro K hK hinit hχK hball
  obtain ⟨hmatch, hX2, hbound⟩ := hlocal K hK hinit hχK hball
  refine ⟨hmatch, hX2, ?_⟩
  intro q hq hq1 T hT₀ hT₁
  obtain ⟨hv, hmaxv⟩ := hbound q hq hq1 T hT₀ hT₁
  refine ⟨hv, ?_⟩
  have hslab := endpoint_residual_memLp_normalized_slab hX2 hball hq hq1 hT₀ hT₁
  have he := henergy Λ q T hΛ hq hq1 1 (by norm_num) X hslab
  simp only [mul_one] at he
  refine hmaxv.trans ((mul_le_mul' (le_refl (ENNReal.ofReal C₀))
    (ENNReal.rpow_le_rpow he (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹))).trans_eq ?_)
  have hfactor : ENNReal.ofReal (C₁ / q ^ (d + 2)) =
      ENNReal.ofReal C₁ * ENNReal.ofReal ((1 : ℝ) / q ^ (d + 2)) := by
    rw [← ENNReal.ofReal_mul hC₁.le]
    congr 1
    ring
  rw [hfactor, mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← mul_assoc, ENNReal.ofReal_rpow_of_nonneg hC₁.le (by positivity),
    ← ENNReal.ofReal_mul hC₀.le]

/-- Rational short-time bounds extend to the closed interval, including both
endpoints, by continuity of the quantity being bounded. -/
private theorem endpoint_le_of_rational_short_times {H : ℝ → ℝ} {A : ℝ}
    (hH : ContinuousOn H (Icc (0 : ℝ) 1))
    (hQ : ∀ r : ℚ, 0 ≤ (r : ℝ) → (r : ℝ) ≤ 1 → H r ≤ A) :
    ∀ t ∈ Icc (0 : ℝ) 1, H t ≤ A := by
  let S : Set ℝ := Ioo (0 : ℝ) 1 ∩ Set.range ((↑) : ℚ → ℝ)
  have hS : closure S ⊆ Icc (0 : ℝ) 1 :=
    closure_minimal (fun _ hx => ⟨hx.1.1.le, hx.1.2.le⟩) isClosed_Icc
  have hI : Icc (0 : ℝ) 1 ⊆ closure S := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact closure_minimal
      (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo) isClosed_closure
  intro t ht
  apply le_on_closure (s := S) ?_ (hH.mono hS) continuousOn_const (hI ht)
  rintro x ⟨hx, r, rfl⟩
  exact hQ r hx.1.le hx.2.le

/-- Multiplication by a positive Gaussian is a contraction on physical L². -/
private theorem endpoint_physical_gaussian_memLp {d : ℕ} (L : ℝ) (hL : 0 < L)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    MemLp (fun x => (Real.exp (-euclideanSq x / L) : ℂ) * f x) 2 volume := by
  have hw : Measurable (fun x : Vec d => (Real.exp (-euclideanSq x / L) : ℂ)) := by
    dsimp only [euclideanSq, dot]
    fun_prop
  apply (Lp.memLp f).of_le_mul (c := 1)
    (hw.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards with x
  change ‖(Real.exp (-euclideanSq x / L) : ℂ) * f x‖ ≤ 1 * ‖f x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (euclideanSq_nonneg_coords x)) hL.le))

/-- The fixed Gaussian is below the comparison Gaussian throughout short time.
The wider L² weight supplies the integrability needed by the real integral. -/
private theorem endpoint_fixed_gaussian_energy_le_moving {d : ℕ} {L t : ℝ}
    (hL : 0 < L) (ht : t ∈ Icc (0 : ℝ) 1) (Y : Vec d → ℂ)
    (hY : Measurable Y)
    (hY2 : MemLp (fun x => (Real.exp (-euclideanSq x / (2 * L)) : ℂ) * Y x)
      2 volume) :
    (∫ x, Real.exp (-euclideanSq x / L) ^ 2 * ‖Y x‖ ^ 2) ≤
      ∫ x, Real.exp (-euclideanSq x / (L * (2 - t))) ^ 2 * ‖Y x‖ ^ 2 := by
  have hw (l : ℝ) : Measurable (fun x : Vec d =>
      (Real.exp (-euclideanSq x / l) : ℂ) * Y x) := by
    have hm : Measurable (fun x : Vec d => (Real.exp (-euclideanSq x / l) : ℂ)) := by
      dsimp only [euclideanSq, dot]
      fun_prop
    exact hm.mul hY
  have hden : 0 < L * (2 - t) := mul_pos hL (by linarith only [ht.2])
  have he (x : Vec d) :
      Real.exp (-euclideanSq x / L) ≤
        Real.exp (-euclideanSq x / (L * (2 - t))) ∧
      Real.exp (-euclideanSq x / (L * (2 - t))) ≤
        Real.exp (-euclideanSq x / (2 * L)) := by
    constructor <;> apply Real.exp_le_exp.mpr
    · apply (div_le_div_iff₀ hL hden).2
      nlinarith only [mul_nonneg (euclideanSq_nonneg_coords x)
        (mul_nonneg hL.le (sub_nonneg.mpr ht.2))]
    · apply (div_le_div_iff₀ hden (by positivity : 0 < 2 * L)).2
      nlinarith only [mul_nonneg (euclideanSq_nonneg_coords x) (mul_nonneg hL.le ht.1)]
  have hm : MemLp (fun x => (Real.exp (-euclideanSq x / (L * (2 - t))) : ℂ) * Y x)
      2 volume := by
    apply hY2.of_le (hw _).aestronglyMeasurable
    filter_upwards with x
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (he x).2 (norm_nonneg _)
  have hi : Integrable (fun x =>
      Real.exp (-euclideanSq x / (L * (2 - t))) ^ 2 * ‖Y x‖ ^ 2) volume := by
    simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using hm.norm.integrable_sq
  apply integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) hi
  filter_upwards with x
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Real.exp_nonneg _) (he x).1 2) (sq_nonneg _)

/-- The actual forward/clock Gaussian error is controlled on one event for
all short times. The event is chosen before the cutoff, retained datum,
physical semigroup, and representative; no measurable choice of them is used. -/
theorem short_time_forward_clock_actual_gaussian_decay_common_event
    (d : ℕ) (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (hB : 0 < B) :
    let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
    ∃ L K c : ℝ, 64 * Λ ^ 3 ≤ L ∧ 0 < L ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ (g : Lp ℂ 2 (reducedLaw Q)) (F U : ℝ × FieldPair d → ℂ),
      Measurable F → Measurable U →
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) →
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) →
      (∀ s ω, F (s, ω) = f ω + ∫ v in Icc (0 : ℝ) s, U (v, ω)) →
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (ρ : ℝ), 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → HasCompactSupport χ →
      (∀ x, euclideanNorm x ≤ ρ → χ x = 1) →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
        (fr : Vec d → ℂ) =ᵐ[volume] (fun x => (χ x : ℂ) * f (translate x ω)) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr →
      ∀ V : ℝ × Vec d → ℂ,
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
          ‖F (t, translate x ω) - V (t, x)‖ ^ 2) ≤
        K * Real.exp (-c * ρ ^ 2) := by
  intro Λ
  obtain ⟨L, K, c, hscale, hL, hK, hc, hdec⟩ :=
    short_time_forward_clock_actual_gaussian_decay d hd S B hB
  refine ⟨L, K, c, hscale, hL, hK, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P hP ν f g F U hF hU heF heU hprim
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hrat := ae_all_iff.mpr fun r : ℚ =>
    ae_all_iff.mpr fun hr0 : 0 ≤ (r : ℝ) =>
      ae_all_iff.mpr fun hr1 : (r : ℝ) ≤ 1 =>
        hdec Q hQ β a μ hβ ha hμ ζ hζ P hP ν (r : ℝ).toNNReal
          (by simpa only [Real.coe_toNNReal _ hr0] using hr1)
  have hsp := ae_all_iff.mpr fun r : ℚ =>
    ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
      (hF.comp (measurable_const.prodMk measurable_id))
      (Lp.stronglyMeasurable (P (r : ℝ).toNNReal f)).measurable (heF r)
  filter_upwards [hrat, hsp,
    short_time_stationary_physical_gaussian_energy_continuous hd Q hP f g F U hU heU hprim,
    short_time_stationary_primitive_gaussian_strong_continuous hd Q hP f g F U hU heU hprim]
    with ω hω hspω hcont hmem
  intro χ ρ hρ hχ hcompact hin fr hfr Pr hPr V heV
  apply endpoint_le_of_rational_short_times
    (hcont L hL (ForcedLocality.retainedPair χ ω).1 Pr hPr fr V heV)
  intro r hr0 hr1
  have hr : (r : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨hr0, hr1⟩
  let Y : Vec d → ℂ := fun x => F ((r : ℝ), translate x ω) - (Pr (r : ℝ).toNNReal fr) x
  have hFω : Measurable (fun x : Vec d => F ((r : ℝ), translate x ω)) :=
    hF.comp (measurable_const.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_id.prodMk measurable_const)))
  have hY : Measurable Y := hFω.sub (Lp.stronglyMeasurable _).measurable
  have hY2 : MemLp (fun x => (Real.exp (-euclideanSq x / (2 * L)) : ℂ) * Y x)
      2 volume := by
    have hf := (hmem (2 * L) (by positivity)).1 r hr
    have hp := endpoint_physical_gaussian_memLp (2 * L) (by positivity)
      (Pr (r : ℝ).toNNReal fr)
    convert hf.sub hp using 1
    funext x
    exact mul_sub _ _ _
  have hle := endpoint_fixed_gaussian_energy_le_moving hL hr Y hY hY2
  have heq : Y =ᵐ[volume] (fun x =>
      (P (r : ℝ).toNNReal f) (translate x ω) - (Pr (r : ℝ).toNNReal fr) x) := by
    filter_upwards [hspω r] with x hx
    exact congrArg (fun z => z - (Pr (r : ℝ).toNNReal fr) x) hx
  have hbound := hω r hr0 hr1 χ ρ hρ hχ hcompact hin fr hfr Pr hPr
  rw [Real.coe_toNNReal _ hr0] at hbound
  calc
    _ = ∫ x, Real.exp (-euclideanSq x / L) ^ 2 * ‖Y x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [heV (r : ℝ)] with x hx
      dsimp only [Y]
      rw [hx]
    _ ≤ _ := hle
    _ = ∫ x, Real.exp (-euclideanSq x / (L * (2 - (r : ℝ)))) ^ 2 *
        ‖(P (r : ℝ).toNNReal f) (translate x ω) - (Pr (r : ℝ).toNNReal fr) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    _ ≤ _ := hbound

/-- A uniform integrable spatial energy bound integrates over the unit time
interval with exactly unit mass. -/
private theorem endpoint_unit_spacetime_energy_le {d : ℕ}
    (H : ℝ × Vec d → ℝ) (hH : Measurable H) (hH0 : ∀ z, 0 ≤ H z)
    (A : ℝ) (hb : ∀ t ∈ Icc (0 : ℝ) 1,
      Integrable (fun x => H (t, x)) volume ∧ (∫ x, H (t, x)) ≤ A) :
    (∫⁻ z in Icc (0 : ℝ) 1 ×ˢ (univ : Set (Vec d)), ENNReal.ofReal (H z)) ≤
      ENNReal.ofReal A := by
  rw [Measure.volume_eq_prod, setLIntegral_prod
    (fun z : ℝ × Vec d => ENNReal.ofReal (H z)) hH.ennreal_ofReal.aemeasurable,
    Measure.restrict_univ]
  calc
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal A := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [← ofReal_integral_eq_lintegral_ofReal (hb t ht).1
        (ae_of_all _ fun x => hH0 (t, x))]
      exact ENNReal.ofReal_le_ofReal (hb t ht).2
    _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- Gaussian spacetime decay for any measurable representative of the actual
stationary orbit. The primitive used for continuity disappears from the
conclusion by stationary spacetime congruence, so the local maximum can use
its SAME previously constructed residual. -/
theorem short_time_forward_clock_actual_gaussian_spacetime_decay
    (d : ℕ) (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (hB : 0 < B) :
    let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
    ∃ L K c : ℝ, 64 * Λ ^ 3 ≤ L ∧ 0 < L ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ (g : Lp ℂ 2 (reducedLaw Q)), IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ f g →
    ∀ F : ℝ × FieldPair d → ℂ, Measurable F →
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) →
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (ρ : ℝ), 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → HasCompactSupport χ →
      (∀ x, euclideanNorm x ≤ ρ → χ x = 1) →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
        (fr : Vec d → ℂ) =ᵐ[volume] (fun x => (χ x : ℂ) * f (translate x ω)) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr →
      ∀ V : ℝ × Vec d → ℂ, Measurable V →
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) →
        (∫⁻ z in Icc (0 : ℝ) 1 ×ˢ (univ : Set (Vec d)),
          ENNReal.ofReal (Real.exp (-euclideanSq z.2 / L) ^ 2 *
            ‖F (z.1, translate z.2 ω) - V z‖ ^ 2)) ≤
          ENNReal.ofReal (K * Real.exp (-c * ρ ^ 2)) := by
  intro Λ
  obtain ⟨L, K, c, hscale, hL, hK, hc, hcommon⟩ :=
    short_time_forward_clock_actual_gaussian_decay_common_event d hd S B hB
  refine ⟨L, K, c, hscale, hL, hK, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P hP ν f g hfg F hF heF
  obtain ⟨F₀, U, hF₀, hU, heF₀, heU, hprim⟩ := short_time_stationary_joint_primitive hP hfg
  have hcong := ae_stationary_spacetime_orbit_congr Q (volume.restrict (Icc (0 : ℝ) 1))
    hF hF₀ (fun s => (heF s).trans (heF₀ s).symm)
  filter_upwards [hcommon Q hQ β a μ hβ ha hμ ζ hζ P hP ν
    g F₀ U hF₀ hU heF₀ heU hprim, hcong,
    short_time_stationary_primitive_gaussian_strong_continuous hd Q hP f g F₀ U hU heU hprim]
    with ω hbound heω hmem
  intro χ ρ hρ hχ hcompact hin fr hfr Pr hPr V hV heV
  let H : ℝ × Vec d → ℝ := fun z => Real.exp (-euclideanSq z.2 / L) ^ 2 *
    ‖F₀ (z.1, translate z.2 ω) - V z‖ ^ 2
  have hshift : Measurable (fun z : ℝ × Vec d => (z.1, translate z.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hw : Measurable (fun z : ℝ × Vec d => Real.exp (-euclideanSq z.2 / L) ^ 2) := by
    dsimp only [euclideanSq, dot]
    fun_prop
  have hH : Measurable H := hw.mul (((hF₀.comp hshift).sub hV).norm.pow_const 2)
  have hhi (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Integrable (fun x => H (t, x)) volume := by
    have hm := ((hmem L hL).1 t ht).sub
      (endpoint_physical_gaussian_memLp L hL (Pr t.toNNReal fr))
    apply hm.norm.integrable_sq.congr
    filter_upwards [heV t] with x hx
    change ‖(Real.exp (-euclideanSq x / L) : ℂ) * F₀ (t, translate x ω) -
      (Real.exp (-euclideanSq x / L) : ℂ) * (Pr t.toNNReal fr) x‖ ^ 2 = H (t, x)
    dsimp only [H]
    rw [← hx, ← mul_sub, norm_mul, mul_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have henergy := endpoint_unit_spacetime_energy_le H hH (fun z => by
    dsimp only [H]; positivity) (K * Real.exp (-c * ρ ^ 2))
      (fun t ht => ⟨hhi t ht, hbound χ ρ hρ hχ hcompact hin fr hfr Pr hPr V heV t ht⟩)
  have heω' : (fun z : ℝ × Vec d => F (z.1, translate z.2 ω)) =ᵐ[
      volume.restrict (Icc (0 : ℝ) 1 ×ˢ (univ : Set (Vec d)))]
      (fun z => F₀ (z.1, translate z.2 ω)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    exact heω
  refine (lintegral_congr_ae ?_).trans_le henergy
  filter_upwards [heω'] with z hz
  dsimp only [H]
  rw [hz]

/-- The SAME normalized residual maximum is controlled by the Gaussian
energy of the actual stationary-minus-physical orbit. Local matching suffices;
no global equality of the zero-extended residual is asserted. -/
theorem short_time_forward_clock_cutoff_normalized_local_max_gaussian_energy
    {d : ℕ} (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    IsComplexEnvironmentSemigroup Q i ζ P →
    ∀ (f g : Lp ℂ 2 (reducedLaw Q)), IsComplexGeneratorPair Q i ζ f g →
    ∃ F : ℝ × FieldPair d → ℂ, Measurable F ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ (_ : IsSmoothFieldPair ω) (χ : C(Vec d, ℝ)),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ (ν : Fin d ⊕ Unit) (fr : Lp ℂ 2 (volume : Measure (Vec d))),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => match ν with
        | Sum.inl j => (χ x : ℂ) *
            ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
              (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ))
        | Sum.inr _ => ζ * (χ x : ℂ) * (ω.2 x : ℂ)) →
      ∃ V X : ℝ × Vec d → ℂ, Measurable V ∧ Measurable X ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        (∀ x ∈ K, χ x = 1) →
        PDE.euclideanBall (0 : PDE.Vec d) 1 ⊆ K →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          ∀ (q : ℝ), 0 < q → q ≤ 1 → ∀ T : ℝ,
          -1 ≤ T - 4 * Λ * q ^ 2 → T ≤ 1 → ∀ L : ℝ, 0 < L →
          let v : PDE.Vec (d + 2) × ℝ → ℝ := fun z =>
            (Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
              q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
                X (T + 4 * Λ * q ^ 2 * z.2,
                  q • (PDE.vecAppendEquiv d 2 z.1).1)).re
          MemLp v 2 (volume.restrict
            (PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1 ×ˢ Ioc (-1 : ℝ) 0)) ∧
          essSup (fun z => ENNReal.ofReal |v z|)
            (volume.restrict (EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (3 / 8) (-11 / 16))) ≤
            ENNReal.ofReal C *
              (ENNReal.ofReal ((1 : ℝ) / q ^ (d + 2)) *
                (ENNReal.ofReal (Real.exp (2 * q ^ 2 / L)) *
                  ∫⁻ z in Icc (0 : ℝ) 1 ×ˢ (univ : Set (Vec d)),
                    ENNReal.ofReal (Real.exp (-euclideanSq z.2 / L) *
                      ‖F (z.1, translate z.2 ω) - V z‖ ^ 2))) ^ (2 : ℝ)⁻¹ := by
  obtain ⟨C, hC, hmax⟩ := short_time_forward_clock_cutoff_normalized_local_max_energy Λ B hΛ hB
  refine ⟨C, hC, ?_⟩
  intro Λ₀ r₀ Q i ζ hζ P hP f g hfg
  obtain ⟨F, hF, heF, hcoh⟩ := hmax Q i ζ hζ P hP f g hfg
  refine ⟨F, hF, heF, ?_⟩
  filter_upwards [hcoh] with ω hω
  intro hωs χ hχs hc hχ hA Pr hPr ν fr hfr
  obtain ⟨V, X, hV, hX, heV, hX0, hlocal⟩ :=
    hω hωs χ hχs hc hχ hA Pr hPr ν fr hfr
  refine ⟨V, X, hV, hX, heV, hX0, ?_⟩
  intro K hK hinit hχK hball
  obtain ⟨hmatch, hX2, hbound⟩ := hlocal K hK hinit hχK hball
  refine ⟨hmatch, hX2, ?_⟩
  intro q hq hq1 T hT₀ hT₁ L hL
  obtain ⟨hv, hmaxv⟩ := hbound q hq hq1 T hT₀ hT₁
  refine ⟨hv, hmaxv.trans ?_⟩
  have hshift : Measurable (fun z : ℝ × Vec d => (z.1, translate z.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hsub : PDE.euclideanBall (0 : PDE.Vec d) q ⊆ K :=
    (PDE.euclideanBall_mono hq.le hq1).trans hball
  have he := short_time_zero_extended_local_gaussian_energy
    (T - 4 * Λ * q ^ 2) T q L hT₁ hL X
    (fun z => F (z.1, translate z.2 ω) - V z) hX ((hF.comp hshift).sub hV) hX0
    (fun s hs hs1 => (hmatch s hs hs1).filter_mono
      (ae_mono (Measure.restrict_mono_set _ hsub)))
  exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
    (mul_le_mul' le_rfl he) (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹))


/-- Splitting off the two lift coordinates commutes with retaining the time
coordinate, including all restricted product measures. -/
private theorem endpoint_lift_spacetime_measurePreserving {d : ℕ}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)} {I : Set ℝ}
    (hU : MeasurableSet U) (hV : MeasurableSet V) :
    MeasurePreserving
      (fun z : PDE.Vec (d + 2) × ℝ =>
        (((PDE.vecAppendEquiv d 2 z.1).1, z.2),
          (PDE.vecAppendEquiv d 2 z.1).2))
      (volume.restrict ((PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) ×ˢ I))
      ((volume.restrict (U ×ˢ I)).prod (volume.restrict V)) := by
  let μ := (volume : Measure (PDE.Vec d)).restrict U
  let ν := (volume : Measure (PDE.Vec 2)).restrict V
  let τ := (volume : Measure ℝ).restrict I
  have hs := (PDE.measurePreserving_vecAppendEquiv_restrict d 2 hU hV).prod
    (MeasurePreserving.id τ)
  have ha := measurePreserving_prodAssoc μ ν τ
  have hb := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := τ))
  have hc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ τ ν)
  have h := hc.comp (hb.comp (ha.comp hs))
  simpa [μ, ν, τ, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Function.comp_def, MeasurableEquiv.prodAssoc] using h

/-- An almost-everywhere bound for the real lift controls both components of
its physical residual on the half-radius physical cylinder. -/
private theorem endpoint_complex_bound_of_lift_ae {d : ℕ}
    {Z : PDE.Vec d × ℝ → ℂ} (hZ : Measurable Z)
    {R q L : ℝ} (hR : 0 < R)
    (hθ : 0 < Real.sin (q * ((R / 2) / 2))) {I : Set ℝ}
    (h : ∀ᵐ z ∂volume.restrict
        (PDE.euclideanBall (0 : PDE.Vec (d + 2)) R ×ˢ I),
      |(Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
          q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          Z ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re| ≤ L) :
    ∀ᵐ z ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (R / 2) ×ˢ I),
      ‖Z z‖ ≤ (1 + 2 / Real.sin (q * ((R / 2) / 2))) * L := by
  let U := PDE.euclideanBall (0 : PDE.Vec d) (R / 2)
  let V := PDE.euclideanBall (0 : PDE.Vec 2) (R / 2)
  have hs := endpoint_lift_spacetime_measurePreserving (U := U) (V := V) (I := I)
    (PDE.isOpen_euclideanBall _ _).measurableSet
    (PDE.isOpen_euclideanBall _ _).measurableSet
  have hsmall := h.filter_mono (ae_mono (Measure.restrict_mono_set _
    (prod_mono (PDE.preimage_vecAppendEquiv_prod_halfBall_subset_euclideanBall d 2 hR)
      Subset.rfl)))
  have hm : Measurable (fun z : (PDE.Vec d × ℝ) × PDE.Vec 2 =>
      |(Complex.exp ⟨q * z.2 0, q * z.2 1⟩ * Z z.1).re|) := by
    simpa only [Complex.mul_re, Complex.exp_re, Complex.exp_im] using
      (show Measurable (fun z : (PDE.Vec d × ℝ) × PDE.Vec 2 =>
        |Real.exp (q * z.2 0) * Real.cos (q * z.2 1) * (Z z.1).re -
          Real.exp (q * z.2 0) * Real.sin (q * z.2 1) * (Z z.1).im|) by fun_prop)
  have hp : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)).prod (volume.restrict V),
      |(Complex.exp ⟨q * z.2 0, q * z.2 1⟩ * Z z.1).re| ≤ L := by
    rw [← hs.map_eq]
    exact (ae_map_iff hs.measurable.aemeasurable
      (measurableSet_le hm measurable_const)).2 hsmall
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with z hz
  exact endpoint_complex_norm_le_of_auxiliary_ae_bound (Z z) (half_pos hR) hθ hz

/-- The Moser essential maximum bounds the full complex residual on the
physical cylinder, with the exact two-phase factor. -/
private theorem endpoint_complex_bound_of_lift_essSup {d : ℕ}
    {Z : PDE.Vec d × ℝ → ℂ} (hZ : Measurable Z)
    {R q L : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hθ : 0 < Real.sin (q * ((R / 2) / 2))) {I : Set ℝ}
    (h : essSup (fun z : PDE.Vec (d + 2) × ℝ =>
        ENNReal.ofReal |(Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
          q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          Z ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re|)
        (volume.restrict (PDE.euclideanBall (0 : PDE.Vec (d + 2)) R ×ˢ I)) ≤
        ENNReal.ofReal L) :
    ∀ᵐ z ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (R / 2) ×ˢ I),
      ‖Z z‖ ≤ (1 + 2 / Real.sin (q * ((R / 2) / 2))) * L := by
  apply endpoint_complex_bound_of_lift_ae hZ hR hθ
  filter_upwards [ENNReal.ae_le_essSup (fun z : PDE.Vec (d + 2) × ℝ =>
    ENNReal.ofReal |(Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
      q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
      Z ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re|)] with z hz
  exact (ENNReal.ofReal_le_ofReal_iff hL).1 (hz.trans h)


/-- The normalized two-phase bound controls every physical short-time trace
of the supplied residual. Its almost-everywhere continuous time paths retain
both endpoints, including the upper boundary of the Moser cylinder. -/
private theorem endpoint_complex_bound_of_normalized_lift_trace {d : ℕ}
    {X : ℝ × Vec d → ℂ} (hX : Measurable X)
    {q M : ℝ} (hq : 0 < q) (hM : 0 ≤ M)
    (hθ : 0 < Real.sin (q * (3 / 32)))
    (hc : ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16))),
      ContinuousOn (fun s => X (s, x)) (Icc (-1 : ℝ) 1))
    (hb : essSup (fun z : PDE.Vec (d + 2) × ℝ =>
        ENNReal.ofReal |(Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
            q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
            X (1 + 2 * z.2, q • (PDE.vecAppendEquiv d 2 z.1).1)).re|)
        (volume.restrict
          (EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (3 / 8) (-11 / 16))) ≤
        ENNReal.ofReal M) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16))),
        ‖X (s, x)‖ ≤ (1 + 2 / Real.sin (q * (3 / 32))) * M := by
  have hZ : Measurable (fun z : PDE.Vec d × ℝ => X (1 + 2 * z.2, q • z.1)) :=
    hX.comp (by fun_prop)
  have he := endpoint_complex_bound_of_lift_essSup hZ
    (by norm_num : (0 : ℝ) < 3 / 8) hM (by convert hθ using 1; ring) hb
  simp only [show (3 / 8 : ℝ) / 2 = 3 / 16 by norm_num,
    show (3 / 16 : ℝ) / 2 = 3 / 32 by norm_num] at he
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at he
  have hslice := Measure.ae_ae_of_ae_prod he
  have hmaps : MapsTo (fun x : Vec d => q⁻¹ • x)
      (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16)))
      (PDE.euclideanBall (0 : PDE.Vec d) (3 / 16)) := by
    intro x hx
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 3 / 16),
      sub_zero, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hq)]
    apply (inv_mul_lt_iff₀ hq).2
    simpa only [sub_zero] using
      (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity : (0 : ℝ) < q * (3 / 16))).1 hx
  have hp := ((Measure.quasiMeasurePreserving_smul
    (volume : Measure (Vec d)) (inv_ne_zero hq.ne')).restrict hmaps).ae hslice
  intro s hs
  filter_upwards [hc, hp] with x hcx hx
  simp only [smul_inv_smul₀ hq.ne'] at hx
  have hcont : ContinuousOn (fun t : ℝ => ‖X (1 + 2 * t, x)‖)
      (Icc (-11 / 16 : ℝ) 0) := by
    apply hcx.norm.comp (by fun_prop)
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hopen := PDE.Parabolic.Moser.continuousOn_le_of_ae_restrict_le
    isOpen_Ioo (hcont.mono Ioo_subset_Icc_self) hx
  have hcl : closure (Ioo (-11 / 16 : ℝ) 0) = Icc (-11 / 16 : ℝ) 0 :=
    closure_Ioo (by norm_num)
  have ht : (s - 1) / 2 ∈ closure (Ioo (-11 / 16 : ℝ) 0) := by
    rw [hcl]
    constructor <;> linarith [hs.1, hs.2]
  have hb' := le_on_closure hopen (by simpa only [hcl] using hcont) continuousOn_const ht
  simpa only [show 1 + 2 * ((s - 1) / 2) = s by ring] using hb'

/-- Gaussian energy controls every short-time spatial trace of the actual
stationary-minus-retained evolution. The representative and the environment
event precede all cutoff, normalization, energy-bound and time choices. -/
theorem short_time_forward_clock_cutoff_gaussian_local_trace
    {d : ℕ} (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    IsComplexEnvironmentSemigroup Q i ζ P →
    ∀ (f g : Lp ℂ 2 (reducedLaw Q)), IsComplexGeneratorPair Q i ζ f g →
    ∃ F : ℝ × FieldPair d → ℂ, Measurable F ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ (_ : IsSmoothFieldPair ω) (χ : C(Vec d, ℝ)),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr →
      ∀ (ν : Fin d ⊕ Unit) (fr : Lp ℂ 2 (volume : Measure (Vec d))),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => match ν with
        | Sum.inl j => (χ x : ℂ) *
            ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
              (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ))
        | Sum.inr _ => ζ * (χ x : ℂ) * (ω.2 x : ℂ)) →
      ∃ V : ℝ × Vec d → ℂ, Measurable V ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        (∀ x ∈ K, χ x = 1) →
        PDE.euclideanBall (0 : PDE.Vec d) 1 ⊆ K →
        ∀ (q : ℝ), 0 < q → q ≤ 1 → 4 * Λ * q ^ 2 = 2 →
        ∀ (L : ℝ), 0 < L → ∀ (M : ℝ), 0 ≤ M →
        ENNReal.ofReal C *
          (ENNReal.ofReal ((1 : ℝ) / q ^ (d + 2)) *
            (ENNReal.ofReal (Real.exp (2 * q ^ 2 / L)) *
              ∫⁻ z in Icc (0 : ℝ) 1 ×ˢ (univ : Set (Vec d)),
                ENNReal.ofReal (Real.exp (-euclideanSq z.2 / L) *
                  ‖F (z.1, translate z.2 ω) - V z‖ ^ 2))) ^ (2 : ℝ)⁻¹ ≤
          ENNReal.ofReal M →
        ∀ s ∈ Icc (0 : ℝ) 1,
          ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16))),
            ‖F (s, translate x ω) - V (s, x)‖ ≤
              (1 + 2 / Real.sin (q * (3 / 32))) * M := by
  obtain ⟨C₀, hC₀, hmax⟩ := endpoint_normalized_lift_local_max Λ B hΛ hB
  obtain ⟨C₁, hC₁, henergy⟩ := short_time_normalized_lift_energy d
  refine ⟨C₀ * C₁ ^ (2 : ℝ)⁻¹,
    mul_pos hC₀ (Real.rpow_pos_of_pos hC₁ _), ?_⟩
  intro Λ₀ r₀ Q i ζ hζ P hP f g hfg
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_forward_clock_cutoff_homogeneous_lift Q hP hfg
  refine ⟨F, hF, heF, ?_⟩
  filter_upwards [hcoh] with ω hω
  intro hωs χ hχs hc hχ hA Pr hPr ν fr hfr
  obtain ⟨gr, hgr, V, Z, X, Y, H, W, hW, heW, hiW, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, hres, hlocal, hdiv, hgrad⟩ :=
      hω.2 hωs χ hχs hc hχ Λ hA Pr hPr ν fr hfr
  refine ⟨V, hV, heV, ?_⟩
  intro K hK hinit hχK hball q hq hq1 hscale L hL M hM hbound
  obtain ⟨hmatch, htime, hslice, hcont, hX2, hY2, hJ2, hlift, hPDE, hC1⟩ := hlocal K hK hinit
  have hcx : ∀ᵐ x ∂volume.restrict K,
      ContinuousOn (fun s => X (s, x)) (Icc (-1 : ℝ) 1) := by
    filter_upwards [htime] with x hx
    have hr : ContinuousOn (fun s => (X (s, x)).re) (Icc (-1 : ℝ) 1) := by
      simpa only [Complex.reCLM_apply, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
        (hx Complex.reCLM).1.continuousOn
    have hi : ContinuousOn (fun s => (X (s, x)).im) (Icc (-1 : ℝ) 1) := by
      simpa only [Complex.imCLM_apply, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
        (hx Complex.imCLM).1.continuousOn
    have hsum := (Complex.continuous_ofReal.comp_continuousOn hr).add
      ((Complex.continuous_ofReal.comp_continuousOn hi).mul
        (continuousOn_const : ContinuousOn (fun _ : ℝ => Complex.I) (Icc (-1 : ℝ) 1)))
    change ContinuousOn (fun s => ((X (s, x)).re : ℂ) +
      ((X (s, x)).im : ℂ) * Complex.I) (Icc (-1 : ℝ) 1) at hsum
    simpa only [Complex.re_add_im] using hsum
  let A := PDE.euclideanBall (0 : PDE.Vec d) 1
  let B₂ := PDE.euclideanBall (0 : PDE.Vec 2) 1
  have hBr : ∀ y ∈ B₂, y 0 ≤ (1 : ℝ) := by
    intro y hy
    have hn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one).1 hy
    simp only [sub_zero] at hn
    exact ((le_abs_self _).trans (PDE.abs_apply_le_vecEuclideanNorm y 0)).trans hn.le
  obtain ⟨w, hw, hDw, hw0, hw1, hweak⟩ :=
    hlift hχK A (PDE.isOpen_euclideanBall _ _) hball B₂ (PDE.isOpen_euclideanBall _ _)
      (PDE.volume_euclideanBall_ne_top _ zero_le_one).lt_top 1 hBr
  have hT₀ : -1 ≤ 1 - 4 * Λ * q ^ 2 := by rw [hscale]; norm_num
  obtain ⟨hv, hmaxv⟩ := hmax (ForcedLocality.retainedPair χ ω).1 hA i ζ hζ
    X w hw hweak q hq hq1 1 hT₀ le_rfl
  have hslab := endpoint_residual_memLp_normalized_slab hX2 hball hq hq1 hT₀ le_rfl
  have he := henergy Λ q 1 hΛ hq hq1 1 (by norm_num) X hslab
  simp only [mul_one] at he
  have hshift : Measurable (fun z : ℝ × Vec d => (z.1, translate z.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hqK : PDE.euclideanBall (0 : PDE.Vec d) q ⊆ K :=
    (PDE.euclideanBall_mono hq.le hq1).trans hball
  have hg := short_time_zero_extended_local_gaussian_energy
    (1 - 4 * Λ * q ^ 2) 1 q L le_rfl hL X
    (fun z => F (z.1, translate z.2 ω) - V z) hX ((hF.comp hshift).sub hV) hX0
    (fun s hs hs1 => (hmatch s hs hs1).filter_mono
      (ae_mono (Measure.restrict_mono_set _ hqK)))
  have hfactor : ENNReal.ofReal (C₁ / q ^ (d + 2)) =
      ENNReal.ofReal C₁ * ENNReal.ofReal ((1 : ℝ) / q ^ (d + 2)) := by
    rw [← ENNReal.ofReal_mul hC₁.le]
    congr 1
    ring
  have hmaxE := hmaxv.trans (mul_le_mul' le_rfl
    (ENNReal.rpow_le_rpow he (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)))
  rw [hfactor, mul_assoc (ENNReal.ofReal C₁),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← mul_assoc, ENNReal.ofReal_rpow_of_nonneg hC₁.le (by positivity),
    ← ENNReal.ofReal_mul hC₀.le] at hmaxE
  have hmaxG := hmaxE.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
    (mul_le_mul' le_rfl hg) (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)))
  have hbM := hmaxG.trans hbound
  rw [hscale] at hbM
  have hsmall : PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16)) ⊆ K := by
    apply Subset.trans (PDE.euclideanBall_mono (by positivity) (show q * (3 / 16) ≤ q by nlinarith)) hqK
  have hθ : 0 < Real.sin (q * (3 / 32)) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    nlinarith [Real.pi_gt_three]
  have ht := endpoint_complex_bound_of_normalized_lift_trace hX hq hM hθ
    (hcx.filter_mono (ae_mono (Measure.restrict_mono_set _ hsmall))) hbM
  intro s hs
  filter_upwards [ht s hs, (hmatch s hs.1 hs.2).filter_mono
    (ae_mono (Measure.restrict_mono_set _ hsmall))] with x hx heq
  rwa [heq] at hx

/-- Taking the Moser square root halves the Gaussian decay exponent; all
normalization factors remain deterministic and independent of the law. -/
private theorem endpoint_gaussian_energy_moser_bound {d : ℕ}
    {q L C K c ρ : ℝ} (hq : 0 < q) (hC : 0 ≤ C) (hK : 0 ≤ K)
    {E : ℝ≥0∞} (hE : E ≤ ENNReal.ofReal (K * Real.exp (-c * ρ ^ 2))) :
    ENNReal.ofReal C *
      (ENNReal.ofReal ((1 : ℝ) / q ^ (d + 2)) *
        (ENNReal.ofReal (Real.exp (2 * q ^ 2 / L)) * E)) ^ (2 : ℝ)⁻¹ ≤
      ENNReal.ofReal
        ((C * (((1 : ℝ) / q ^ (d + 2)) * Real.exp (2 * q ^ 2 / L) * K) ^ (2 : ℝ)⁻¹) *
          Real.exp (-(c / 2) * ρ ^ 2)) := by
  refine (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
    (mul_le_mul' le_rfl (mul_le_mul' le_rfl hE))
      (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹))).trans_eq ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / q ^ (d + 2)),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    ← ENNReal.ofReal_mul hC]
  congr 1
  rw [show (1 / q ^ (d + 2)) *
      (Real.exp (2 * q ^ 2 / L) * (K * Real.exp (-c * ρ ^ 2))) =
      ((1 / q ^ (d + 2)) * Real.exp (2 * q ^ 2 / L) * K) *
        Real.exp (-c * ρ ^ 2) by ring,
    Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
  rw [show -c * ρ ^ 2 * (2 : ℝ)⁻¹ = -(c / 2) * ρ ^ 2 by ring]
  ring

/-- Actual forward and clock residuals have Gaussian decay on a deterministic
physical ball at every short time, including zero and one. Constants precede
the law and the common environment event precedes every cutoff and time. -/
theorem short_time_forward_clock_actual_local_trace_decay
    (d : ℕ) (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (hB : 0 < B) :
    let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
    let q := (Real.sqrt (2 * Λ))⁻¹
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ (g : Lp ℂ 2 (reducedLaw Q)), IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ f g →
    ∃ F : ℝ × FieldPair d → ℂ, Measurable F ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
    ∀ᵐ ω ∂reducedLaw Q, ∀ (_ : IsSmoothFieldPair ω) (χ : C(Vec d, ℝ)) (ρ : ℝ),
      0 ≤ ρ → ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanNorm x ≤ ρ → χ x = 1) →
      (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => match ν with
        | Sum.inl j => (χ x : ℂ) *
            ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
              (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x ⟨0, by omega⟩ j : ℂ))
        | Sum.inr _ => ζ * (χ x : ℂ) * (ω.2 x : ℂ)) →
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => (χ x : ℂ) * f (translate x ω)) →
      ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr →
      ∀ A : Set (Vec d), IsCompact A →
      (fun x => f (translate x ω)) =ᵐ[volume.restrict A] fr →
      (∀ x ∈ A, χ x = 1) → PDE.euclideanBall (0 : PDE.Vec d) 1 ⊆ A →
      ∀ t ∈ Icc (0 : ℝ) 1,
        ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16))),
          ‖F (t, translate x ω) - (Pr t.toNNReal fr) x‖ ≤
            K * Real.exp (-c * ρ ^ 2) := by
  intro Λ q
  have hexp : 1 ≤ Real.exp (2 * S.ellipticity) :=
    Real.one_le_exp (by linarith [S.one_le_ellipticity])
  have hΛ : 1 ≤ Λ := by dsimp only [Λ]; nlinarith [S.one_le_ellipticity]
  have hroot : 0 < Real.sqrt (2 * Λ) := Real.sqrt_pos.2 (by positivity)
  have hroot2 : Real.sqrt (2 * Λ) ^ 2 = 2 * Λ := Real.sq_sqrt (by positivity)
  have hq : 0 < q := inv_pos.mpr hroot
  have hq1 : q ≤ 1 := (inv_le_one₀ hroot).2 (by nlinarith [Real.sqrt_nonneg (2 * Λ)])
  have hscale : 4 * Λ * q ^ 2 = 2 := by
    change 4 * Λ * ((Real.sqrt (2 * Λ))⁻¹) ^ 2 = 2
    rw [inv_pow, hroot2]
    field_simp
    ring
  have hθ : 0 < Real.sin (q * (3 / 32)) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    nlinarith [Real.pi_gt_three]
  obtain ⟨L, K₀, c₀, hscaleL, hL, hK₀, hc₀, hgauss⟩ :=
    short_time_forward_clock_actual_gaussian_spacetime_decay d hd S B hB
  obtain ⟨C, hC, htrace⟩ := short_time_forward_clock_cutoff_gaussian_local_trace Λ B hΛ hB.le
  let J := C * (((1 : ℝ) / q ^ (d + 2)) * Real.exp (2 * q ^ 2 / (L / 2)) * K₀) ^ (2 : ℝ)⁻¹
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hphase : 0 < 1 + 2 / Real.sin (q * (3 / 32)) := by positivity
  refine ⟨(1 + 2 / Real.sin (q * (3 / 32))) * J, c₀ / 2,
    mul_pos hphase hJ, half_pos hc₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P hP ν f g hfg
  obtain ⟨F, hF, heF, ht⟩ := htrace Q ⟨0, by omega⟩ ζ hζ P hP f g hfg
  refine ⟨F, hF, heF, ?_⟩
  filter_upwards [ht, hgauss Q hQ β a μ hβ ha hμ ζ hζ P hP ν g hfg F hF heF]
    with ω htω hgω
  intro hωs χ ρ hρ hχs hcompact hχ hin hA fr hfr hfrf Pr hPr A hAc hinit hχA hball
  obtain ⟨V, hV, heV, hlocal⟩ := htω hωs χ hχs hcompact hχ hA Pr hPr ν fr hfr
  have hE := hgω χ ρ hρ hχ hcompact hin fr hfrf Pr hPr V hV heV
  have hw (x : Vec d) : Real.exp (-euclideanSq x / (L / 2)) =
      Real.exp (-euclideanSq x / L) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [← hw] at hE
  have hb := endpoint_gaussian_energy_moser_bound (d := d) (L := L / 2) hq hC.le hK₀.le hE
  have htall := hlocal A hAc hinit hχA hball q hq hq1 hscale (L / 2) (half_pos hL)
    (J * Real.exp (-(c₀ / 2) * ρ ^ 2)) (by positivity) hb
  intro t htime
  filter_upwards [htall t htime, (heV t).filter_mono
    (ae_mono (Measure.restrict_le_self : volume.restrict
      (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16))) ≤ volume))] with x hx he
  rw [he] at hx
  simpa only [mul_assoc] using hx


/-- Finite-volume physical averages are continuous linear functionals of the
retained L² state, hence preserve its local measurability. -/
private theorem endpoint_local_physical_average_measurable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {V : Ω → Lp ℂ 2 (volume : Measure (Vec d))}
    (hV : @Measurable Ω (Lp ℂ 2 (volume : Measure (Vec d))) _ (borel _) V)
    {A : Set (Vec d)} (hA : MeasurableSet A) (hμA : volume A ≠ ∞) :
    Measurable (fun ω => ⨍ x in A, (V ω) x) := by
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  have hm := (innerSL ℂ (indicatorConstLp 2 hA hμA (1 : ℂ))).continuous.measurable.comp hV
  have hs := hm.const_smul ((volume.restrict A).real univ)⁻¹
  change Measurable (fun ω => ((volume.restrict A).real univ)⁻¹ •
    innerSL ℂ (indicatorConstLp 2 hA hμA (1 : ℂ)) (V ω)) at hs
  simpa only [average_eq, innerSL_apply_apply, L2.inner_indicatorConstLp_one] using hs

private theorem endpoint_unit_ball_probability (d : ℕ) :
    IsProbabilityMeasure (PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1)) :=
  PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
    (PDE.volume_euclideanBall_pos _ (by norm_num))
    (lt_top_iff_ne_top.mpr (PDE.volume_euclideanBall_ne_top _ (by norm_num)))

/-- Positive dilation turns normalized unit-ball integration into the literal
average on the smaller physical ball. This holds for every representative. -/
private theorem endpoint_scaled_unit_ball_average {d : ℕ} {r : ℝ} (hr : 0 < r)
    (f : Vec d → ℂ) :
    (⨍ x, f (r • x) ∂PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1)) =
      ⨍ x in PDE.euclideanBall (0 : PDE.Vec d) r, f x := by
  let := endpoint_unit_ball_probability d
  rw [average_eq_integral]
  have hp := PDE.measurePreserving_smul_addRight_normalizedVolumeOn_euclideanBall hr
    (0 : PDE.Vec d)
  have hm : MeasurableEmbedding (fun x : Vec d => r • x + (0 : Vec d)) := by
    convert (Homeomorph.smulOfNeZero r hr.ne' : Vec d ≃ₜ Vec d).measurableEmbedding using 1
    ext x
    simp
  have he := hp.integral_comp hm f
  simp only [add_zero] at he
  rw [he, PDE.normalizedVolumeOn, integral_smul_measure, ENNReal.toReal_inv, setAverage_eq]
  rfl

/-- The actual shrinking-ball averages of a local L²-valued family are local
measurable functions; no spatial point value is selected. -/
theorem short_time_local_retained_average_measurable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {V : Ω → Lp ℂ 2 (volume : Measure (Vec d))}
    (hV : @Measurable Ω (Lp ℂ 2 (volume : Measure (Vec d))) _ (borel _) V)
    {r : ℝ} (hr : 0 < r) :
    Measurable (fun ω => ⨍ x, (V ω) (r • x)
      ∂PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1)) := by
  simp_rw [endpoint_scaled_unit_ball_average hr]
  exact endpoint_local_physical_average_measurable hV
    (PDE.isOpen_euclideanBall _ _).measurableSet (PDE.volume_euclideanBall_ne_top _ hr.le)


/-- A literal stationary spatial average inherits the same residual error as
the actual retained L² state on every smaller physical ball. -/
theorem short_time_stationary_retained_average_error {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℂ 2 (reducedLaw Q))
    (F : FieldPair d → ℂ) (hF : Measurable F) (heF : F =ᵐ[reducedLaw Q] f)
    (V : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)))
    {R r ε : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (herr : ∀ᵐ ω ∂reducedLaw Q,
      ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) R),
        ‖F (translate x ω) - (V ω) x‖ ≤ ε) :
    ∀ᵐ ω ∂reducedLaw Q,
      ‖(⨍ x, f (translate (r • x) ω)
          ∂PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1)) -
        (⨍ x, (V ω) (r • x)
          ∂PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1))‖ ≤ ε := by
  let := reducedLaw_probability Q
  have hsp := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    hF (Lp.stronglyMeasurable f).measurable heF
  let A := PDE.euclideanBall (0 : PDE.Vec d) r
  have hApos := PDE.volume_euclideanBall_pos (0 : PDE.Vec d) hr
  have hAtop := PDE.volume_euclideanBall_ne_top (0 : PDE.Vec d) hr.le
  let : IsProbabilityMeasure (PDE.normalizedVolumeOn A) :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hApos
      (lt_top_iff_ne_top.mpr hAtop)
  have hsub : A ⊆ PDE.euclideanBall (0 : PDE.Vec d) R := by
    intro x hx
    change PDE.euclideanSqDist x 0 < r ^ 2 at hx
    change PDE.euclideanSqDist x 0 < R ^ 2
    nlinarith
  filter_upwards [herr, hsp] with ω hω hsω
  rw [endpoint_scaled_unit_ball_average hr (fun y => f (translate y ω)),
    endpoint_scaled_unit_ball_average hr (V ω)]
  have he : (fun x => F (translate x ω)) =ᵐ[volume.restrict A]
      (fun x => f (translate x ω)) := ae_restrict_of_ae hsω
  rw [← average_congr he]
  have hb : ∀ᵐ x ∂PDE.normalizedVolumeOn A, ‖F (translate x ω) - (V ω) x‖ ≤ ε := by
    exact Measure.ae_smul_measure
      (hω.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))) (volume A)⁻¹
  have hVi : Integrable (V ω) (PDE.normalizedVolumeOn A) :=
    PDE.integrable_normalizedVolumeOn_of_integrableOn
      (integrableOn_Lp_of_measure_ne_top (V ω) (by norm_num) hAtop) hApos
  have hFm : Measurable (fun x : Vec d => F (translate x ω)) :=
    hF.comp (Probability.continuous_translate.measurable.comp
      (measurable_id.prodMk measurable_const))
  have hDi : Integrable (fun x => F (translate x ω) - (V ω) x)
      (PDE.normalizedVolumeOn A) :=
    (integrable_const ε).mono'
      (hFm.aestronglyMeasurable.sub (Lp.stronglyMeasurable (V ω)).aestronglyMeasurable) hb
  have hFi : Integrable (fun x => F (translate x ω)) (PDE.normalizedVolumeOn A) := by
    exact (hDi.add hVi).congr (Filter.Eventually.of_forall fun x =>
      sub_add_cancel (F (translate x ω)) ((V ω) x))
  have hn := norm_integral_le_of_norm_le_const hb
  have heq (g : Vec d → ℂ) : (⨍ x in A, g x) = ∫ x, g x ∂PDE.normalizedVolumeOn A := by
    rw [setAverage_eq', PDE.normalizedVolumeOn]
  rw [heq, heq, ← integral_sub hFi hVi]
  simpa only [probReal_univ, mul_one] using hn


/-- The forward and clock retained families have the same local measurability
and the literal physical cutoff datum used by the residual estimate. -/
theorem short_time_forward_clock_cutoff_measurable_evolution {d : ℕ}
    (χ θ : C(Vec d, ℝ)) (hcompact : HasCompactSupport χ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (U W : Set (Vec d))
    (hsupport : ∀ x, x ∉ U → θ x = 0) (hW : IsOpen W)
    (hinterior : ∀ x ∈ W, θ x = 1) (hχ : ∀ x, χ x ≠ 0 → x ∈ W)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (i : Fin d) (ζ : ℂ) (ν : Fin d ⊕ Unit) :
    let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
    let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∃ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)),
      Measurable fr ∧ Measurable (Function.uncurry V) ∧
      (∀ ω, IsSmoothFieldPair ω →
        (fr ω : Vec d → ℂ) =ᵐ[volume] fun x => match ν with
          | Sum.inl j => (χ x : ℂ) *
              ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
                (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ))
          | Sum.inr _ => ζ * (χ x : ℂ) * (ω.2 x : ℂ)) ∧
      ∀ ω, (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
        ∃ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr ∧
          ∀ t, V ω t = Pr t (fr ω) := by
  let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  cases ν with
  | inl j =>
      exact short_time_forward_cutoff_measurable_evolution χ θ hcompact hθ U W
        hsupport hW hinterior hχ Λ hΛ i j ζ
  | inr u =>
      have hχsupport : ∀ x, x ∉ U → χ x = 0 := by
        intro x hx
        by_contra hne
        have h1 := hinterior x (hχ x hne)
        rw [hsupport x hx] at h1
        exact zero_ne_one h1
      obtain ⟨fr, V, hfr, hV, hefr, hactual⟩ :=
        short_time_clock_cutoff_measurable_evolution χ hcompact U hχsupport Λ hΛ i ζ
      exact ⟨fr, V, hfr, hV, fun ω _ => hefr ω, hactual⟩

/-- The actual forward or clock observable agrees spatially with its literal
coefficient formula on one stationary environment event. -/
private theorem endpoint_forward_clock_spatial_datum
    {d : ℕ} (hd : 2 ≤ d) (S : StructuralData d)
    (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ) (ν : Fin d ⊕ Unit) :
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      f (translate x ω) = match ν with
        | Sum.inl j =>
            ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
              (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x ⟨0, by omega⟩ j : ℂ))
        | Sum.inr _ => ζ * (ω.2 x : ℂ) := by
  intro f
  let := reducedLaw_probability Q
  cases ν with
  | inl j =>
      let f₀ : FieldPair d → ℂ := fun ω =>
        ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
          (fun y => ω.1 y k j) 0 : ℝ) : ℂ) + ζ * (ω.1 0 ⟨0, by omega⟩ j : ℂ))
      have hf : (f : FieldPair d → ℂ) =ᵐ[reducedLaw Q] f₀ := by
        filter_upwards [Lp.coeFn_add (β j) (ζ • a ⟨0, by omega⟩ j),
          Lp.coeFn_smul ζ (a ⟨0, by omega⟩ j), hβ j, ha ⟨0, by omega⟩ j]
          with ω h1 h2 h3 h4
        change (β j + ζ • a ⟨0, by omega⟩ j : Lp ℂ 2 (reducedLaw Q)) ω = _
        rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]
        rfl
      have hf₀ : Measurable f₀ := by
        have hdm (k : Fin d) : Measurable (fun ω : FieldPair d =>
            coordinateDerivative k (fun y => ω.1 y k j) 0) :=
          (measurable_fderiv_apply_const_with_param ℝ
            (f := fun (ω : FieldPair d) (y : Vec d) => ω.1 y k j)
            (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
              |>.matrix_elem k j) (unitVector k)).comp (measurable_id.prodMk measurable_const)
        exact (Complex.measurable_ofReal.comp
          ((Finset.measurable_sum _ fun k _ => hdm k).const_mul (1 / 2 : ℝ))).add
            ((by fun_prop : Measurable (fun ω : FieldPair d =>
              (ω.1 0 ⟨0, by omega⟩ j : ℂ))).const_mul ζ)
      filter_upwards [ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
        (Lp.stronglyMeasurable f).measurable hf₀ hf] with ω hω
      filter_upwards [hω] with x hx
      rw [hx]
      have hshift (k : Fin d) : coordinateDerivative k
          (fun y => (translate x ω).1 y k j) 0 =
            coordinateDerivative k (fun y => ω.1 y k j) x := by
        have hh := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : Vec d => ω.1 y k j)
          (x := (0 : Vec d)) x
        rw [add_zero] at hh
        exact congrArg (fun A : Vec d →L[ℝ] ℝ => A (unitVector k)) hh
      dsimp only [f₀]
      simp_rw [hshift]
      simp only [translate_matrix, add_zero]
  | inr u =>
      have hf : (f : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          (fun ω => ζ * (ω.2 0 : ℂ)) := by
        filter_upwards [Lp.coeFn_smul ζ μ, hμ] with ω h1 h2
        change (ζ • μ : Lp ℂ 2 (reducedLaw Q)) ω = _
        rw [h1, Pi.smul_apply, h2]
        rfl
      filter_upwards [ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
        (Lp.stronglyMeasurable f).measurable
        (by fun_prop : Measurable (fun ω : FieldPair d => ζ * (ω.2 0 : ℂ))) hf] with ω hω
      filter_upwards [hω] with x hx
      simpa only [translate_scalar, add_zero] using hx


/-- The actual locally measurable retained evolution approximates every literal
shrinking stationary average, with deterministic Gaussian constants before the
law and both endpoints of the short-time interval included. -/
theorem short_time_forward_clock_actual_local_averages
    (d : ℕ) (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (hB : 0 < B) :
    let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
    let q := (Real.sqrt (2 * Λ))⁻¹
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
    ∀ ρ : ℝ, 4 ≤ ρ → ∀ ζ : ℂ, ‖ζ‖ ≤ B → ∀ ν : Fin d ⊕ Unit,
    ∃ V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)),
      @Measurable _ _
        ((EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}).prod inferInstance)
        (borel _) (Function.uncurry V) ∧
    ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ r : ℝ, 0 < r → r ≤ q * (3 / 16) →
      ∀ᵐ ω ∂reducedLaw Q,
        ‖(⨍ x, (P t f) (translate (r • x) ω)
            ∂PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1)) -
          (⨍ x, (V ω t) (r • x)
            ∂PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1))‖ ≤
          K * Real.exp (-c * ρ ^ 2) := by
  intro Λ q
  obtain ⟨K, c, hK, hc, htrace⟩ :=
    short_time_forward_clock_actual_local_trace_decay d hd S B hB
  have hexp : 1 ≤ Real.exp (2 * S.ellipticity) :=
    Real.one_le_exp (by linarith [S.one_le_ellipticity])
  have hΛ : 1 ≤ Λ := by dsimp only [Λ]; nlinarith [S.one_le_ellipticity]
  refine ⟨K, c / 16, hK, by positivity, ?_⟩
  intro ρ hρ ζ hζ ν
  obtain ⟨C, _, hcuts⟩ := short_time_compatible_euclidean_cutoffs d
  obtain ⟨χ, θ, hχs, hθs, hχc, _, hχb, _, hχone, _, _, hθone,
    hχsupport, hθsupport, _, _⟩ := hcuts ρ (by linarith)
  have hnorm : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finsetSum _ fun k _ => (continuous_apply k).mul (continuous_apply k))
  obtain ⟨fr, V, _, hVm, hefr, hactual⟩ :=
    short_time_forward_clock_cutoff_measurable_evolution χ θ hχc hθs
      {x : Vec d | euclideanNorm x < ρ} {x : Vec d | euclideanNorm x < ρ / 2}
      hθsupport (isOpen_lt hnorm continuous_const) (fun x hx => hθone x hx.le)
      hχsupport Λ hΛ ⟨0, by omega⟩ ζ ν
  refine ⟨V, hVm, ?_⟩
  intro Q hQ β a μ hβ ha hμ P hP f
  let := reducedLaw_probability Q
  have hgen : ∃ g, IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ f g := by
    cases ν with
    | inl j =>
        obtain ⟨b, hb⟩ := timeFlux_drift_generator (i := ⟨0, by omega⟩) (ζ := ζ) hβ j
        obtain ⟨g, hg⟩ := timeFlux_coefficient_generator (i := ⟨0, by omega⟩) (ζ := ζ)
          hQ ha ⟨0, by omega⟩ j
        exact ⟨b + ζ • g, hb.add (hg.smul ζ)⟩
    | inr u =>
        obtain ⟨g, hg⟩ := centeredEquations_clock_initial_generator
          (i := ⟨0, by omega⟩) (ζ := ζ) hQ hμ
        exact ⟨ζ • g, hg.smul ζ⟩
  obtain ⟨g, hg⟩ := hgen
  obtain ⟨F, hF, heF, ht⟩ := htrace Q hQ β a μ hβ ha hμ ζ hζ P hP ν g hg
  have hsp := endpoint_forward_clock_spatial_datum hd S Q hQ β a μ hβ ha hμ ζ ν
  obtain ⟨M, _, hsmooth⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d S
  intro t ht1 r hr hrq
  apply short_time_stationary_retained_average_error Q (P t f) (fun ω => F (t, ω))
    (hF.comp (measurable_const.prodMk measurable_id)) (by simpa using heF (t : ℝ))
    (fun ω => V ω t) hr hrq
  filter_upwards [ht, hsp, c4_ae_reduced_physical_elliptic Q, hsmooth Q hQ]
    with ω htω hspω hA hsω
  have hgood (x : Vec d) : S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ :=
    endpoint_retained_elliptic χ ω x (s5Elliptic_of_isElliptic hΛ hA x)
      (hχb x).1 (hχb x).2
  obtain ⟨Pr, hPr, heV⟩ := hactual ω hgood
  have hcut : (fr ω : Vec d → ℂ) =ᵐ[volume]
      (fun x => (χ x : ℂ) * f (translate x ω)) := by
    filter_upwards [hefr ω hsω.1, hspω] with x h1 h2
    rw [h1, h2]
    cases ν with
    | inl j => rfl
    | inr u => dsimp only [Sum.elim]; ring
  let A := PDE.euclideanClosedBall (0 : PDE.Vec d) 1
  have hAc : IsCompact A := PDE.isCompact_euclideanClosedBall _ (by norm_num)
  have hχA : ∀ x ∈ A, χ x = 1 := by
    intro x hx
    apply hχone x
    have hx1 : euclideanNorm x ≤ 1 := by
      have hn := (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (by norm_num : (0 : ℝ) ≤ 1)).1 hx
      simpa only [sub_zero, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot,
        euclideanNorm, euclideanSq, dot] using hn
    linarith
  have hinit : (fun x => f (translate x ω)) =ᵐ[volume.restrict A] fr ω := by
    filter_upwards [ae_restrict_of_ae hcut, ae_restrict_mem hAc.measurableSet] with x hx hxA
    simpa only [hχA x hxA, Complex.ofReal_one, one_mul] using hx.symm
  have hb := htω hsω.1 χ (ρ / 4) (by linarith) hχs hχc hχb hχone hgood
    (fr ω) (hefr ω hsω.1) hcut Pr hPr A hAc hinit hχA
    (PDE.euclideanBall_subset_euclideanClosedBall _ _) (t : ℝ) ⟨t.coe_nonneg, ht1⟩
  have he : -c * (ρ / 4) ^ 2 = -(c / 16) * ρ ^ 2 := by ring
  rw [he] at hb
  simpa only [Real.toNNReal_coe, ← heV t] using hb

/-- The actual short-time forward and clock endpoints admit local L²
approximants, obtained from their retained spatial averages. -/
theorem short_time_forward_clock_actual_local_observation
    (d : ℕ) (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (hB : 0 < B) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ ρ : ℝ, 4 ≤ ρ →
    ∃ V : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ V ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖(P t f) ω - V ω‖ ≤ K * Real.exp (-c * ρ ^ 2) := by
  let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
  let q := (Real.sqrt (2 * Λ))⁻¹
  obtain ⟨K, c, hK, hc, havg⟩ :=
    short_time_forward_clock_actual_local_averages d hd S B hB
  have hΛ : 0 < Λ := by
    dsimp only [Λ]
    exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one S.one_le_ellipticity)
  have hq : 0 < q := inv_pos.mpr (Real.sqrt_pos.2 (by positivity))
  let r : ℕ → ℝ := fun n => (q * (3 / 16)) / ((n : ℝ) + 1)
  have hrpos (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  have hrle (n : ℕ) : r n ≤ q * (3 / 16) := by
    apply div_le_self (by positivity)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hr : Tendsto r atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := q * (3 / 16))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [mul_zero, mul_one_div] using hh
  refine ⟨2 * K, c, by positivity, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P hP ν f t ht ρ hρ
  obtain ⟨W, hWm, hW⟩ := havg ρ hρ ζ hζ ν
  let A : ℕ → FieldPair d → ℂ := fun n ω =>
    ⨍ x, (W ω t) (r n • x)
      ∂PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1)
  have hA (n : ℕ) : Measurable[EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}] (A n) := by
    let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}
    exact short_time_local_retained_average_measurable
      (hWm.comp (measurable_id.prodMk measurable_const)) (hrpos n)
  let := endpoint_unit_ball_probability d
  obtain ⟨V, hV, he⟩ := short_time_local_observation_of_shrinking_averages Q ρ
    (by positivity : 0 ≤ K * Real.exp (-c * ρ ^ 2))
    (PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1))
    (P t f) r hr A hA
    (fun n => hW Q hQ β a μ hβ ha hμ P hP t ht (r n) (hrpos n) (hrle n))
  exact ⟨V, hV, by simpa only [mul_assoc] using he⟩

/-- The short-time forward and clock endpoints satisfy the fixed local
projection estimate for every p ≥ 1, including infinity. -/
theorem short_time_forward_clock_uniform_projection
    (d : ℕ) (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (hB : 0 < B) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → ∀ ν : Fin d ⊕ Unit,
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ ρ : ℝ, 4 ≤ ρ →
    let ν' : EndpointIndex d := ν.elim Sum.inl (fun _ => Sum.inr false)
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] indexedEndpoint hd Q ν' ζ P P β a μ t →
      ‖E - EndpointProjection.project
        (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        K * Real.exp (-c * ρ ^ 2) := by
  obtain ⟨K, c, hK, hc, happ⟩ :=
    short_time_forward_clock_actual_local_observation d hd S B hB
  refine ⟨4 * K, c, by positivity, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P hP ν t ht ρ hρ ν' p _ E hE
  obtain ⟨V, hV, he⟩ := happ Q hQ β a μ hβ ha hμ ζ hζ P hP ν t ht ρ hρ
  have herr : ∀ᵐ ω ∂reducedLaw Q,
      ‖uncenteredEndpoint hd Q ν' ζ P P β a μ t ω - V ω‖ ≤
        K * Real.exp (-c * ρ ^ 2) := by
    cases ν with
    | inl j => exact he
    | inr u => simpa only [ν', uncenteredEndpoint, Sum.elim, map_smul] using he
  obtain ⟨W, hW, hWe⟩ := EndpointLocalization.indexed_approximation
    hd Q ν' ζ P P β a μ t ρ V hV (by positivity) herr
  have hb := EndpointLocalization.norm_sub_project_le Q ρ E _ W hE hW (by positivity) hWe
  simpa only [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using hb

/-- The coherent actual equations use one jointly measurable retained gradient,
whose square is integrable on every compact time interval and all of space. -/
theorem short_time_transpose_retained_joint_weak_equations
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ Measurable U ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (complexTransposeGradientOrbit Q Pdag f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      (∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : ℝ × Vec d => ‖F (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        ∀ j, Integrable (fun p : ℝ × Vec d => ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K))) ∧
      ∀ χ : C(Vec d, ℝ),
      (∀ j k, MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ))
        ∞ volume) →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ᵐ x ∂volume, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ (Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∃ V Z X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∃ W : Fin d → ℝ × Vec d → ℂ,
        (∀ j, Measurable (W j)) ∧
        (∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j) ∧
        (∀ (j : Fin d) (l r : ℝ), Integrable (fun p => ‖W j p‖ ^ 2)
          ((volume.restrict (Icc l r)).prod volume)) ∧
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Tr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Tr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Tr s.toNNReal fr) (H s)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakGradient Set.univ (fun x => L (F (s, translate x ω)))
            (fun x j => L (D j (s, translate x ω))) ∧
          ∀ O : Set (Vec d), IsOpen O → (∀ x ∈ O, χ x = 1) →
          HasWeakDivergence O
            (fun x j => L ((∑ k, (ω.1 x j k : ℂ) *
              (D k (s, translate x ω) - W k (s, x))) -
              2 * ζ * (ω.1 x j i : ℂ) * (F (s, translate x ω) - V (s, x))))
            (fun x => L (2 * Y (s, x)))) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          (∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0 ) ∧
          MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          ∀ j, MemLp (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
            (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1) 2
            ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) := by
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_transpose_retained_coherent_weak_equations Q hP hPdag hfg
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hfi := endpoint_joint_sq_integrable
    ((((hPdag.continuous_apply hP f).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      (μ := volume) (K := Icc (0 : ℝ) 1) isCompact_Icc) hF heF
  have hui := endpoint_joint_sq_integrable
    ((((hPdag.continuous_apply hP g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      (μ := volume) (K := Icc (0 : ℝ) 1) isCompact_Icc) hU heU
  obtain ⟨G, hG, _⟩ := hPdag.existsUnique_continuous_gradient_orbit hP hfg
  have hdi (j : Fin d) : Integrable (fun p => ‖D j p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (reducedLaw Q)) := by
    apply endpoint_joint_sq_integrable (u := fun s => (complexTransposeGradientOrbit Q Pdag f s) j)
      _ (hD j) (heD j)
    let C : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) →L[ℂ]
        Lp ℂ 2 (reducedLaw Q) := PiLp.proj 2 _ j
    have hj : Continuous (fun s : ℝ => (G s.toNNReal) j) :=
      C.continuous.comp (hG.2.comp continuous_real_toNNReal)
    have hi := (hj.norm.pow 2).continuousOn.integrableOn_compact
      (μ := volume) (K := Icc (0 : ℝ) 1) isCompact_Icc
    change Integrable (fun s : ℝ => ‖(G s.toNNReal) j‖ ^ 2)
      (volume.restrict (Icc (0 : ℝ) 1)) at hi
    rw [← restrict_Ioc_eq_restrict_Icc] at hi ⊢
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [complexTransposeGradientOrbit_eq hs.1 (hG.1 s.toNNReal)]
  have hfLoc := ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hfi.ofReal
  have huLoc := ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hui.ofReal
  have hdLoc := ae_all_iff.mpr (fun j =>
    ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
      (reducedLaw_stationary Q) (hdi j).ofReal)
  refine ⟨F, U, D, hF, hU, hD, heF, heU, heD, ?_⟩
  filter_upwards [hcoh, hfLoc, huLoc, hdLoc] with ω hω hfω huω hdω
  refine ⟨?_, ?_⟩
  · intro K hK
    refine ⟨(Integrable.iff_ofReal (𝕜 := ℂ)).mpr (hfω K hK).swap,
      (Integrable.iff_ofReal (𝕜 := ℂ)).mpr (huω K hK).swap, ?_⟩
    intro j
    exact (Integrable.iff_ofReal (𝕜 := ℂ)).mpr (hdω j K hK).swap
  intro χ ha Λ hΛ hA Pr Tr hPr fr gr hfr
  obtain ⟨V, Z, X, Y, H, hV, hZ, hX, hY, heV, heZ, heY, hX0, hHc, hH, hres, hlocal⟩ :=
    hω χ ha Λ hΛ hA Pr Tr hPr fr gr hfr
  have hex (j : Fin d) :=
    endpoint_physical_joint_l2_representative (hHc j).stronglyMeasurable
  choose W hW heW using hex
  have hi (j : Fin d) (l r : ℝ) : Integrable (fun p => ‖W j p‖ ^ 2)
      ((volume.restrict (Icc l r)).prod volume) := by
    apply endpoint_joint_sq_integrable
      (((hHc j).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
      (hW j) (heW j)
  refine ⟨V, Z, X, Y, H, W, hW, heW, hi, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, ?_, ?_⟩
  · filter_upwards [hres] with s hs
    intro L
    refine ⟨(hs L).1, ?_⟩
    have he : ∀ᵐ x ∂volume, ∀ j, W j (s, x) = H s j x :=
      ae_all_iff.mpr (fun j => heW j s)
    intro O hO hχO
    apply Correctors.hasWeakDivergence_congr_ae hO ((hs L).2 O hO.measurableSet hχO)
    · filter_upwards [ae_restrict_of_ae he] with x hx
      simp only [hx]
    · exact Filter.EventuallyEq.rfl
  · intro K hK hinit
    obtain ⟨hmatch, htime⟩ := hlocal K hK hinit
    have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
      measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk measurable_const))
    have hm : (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K) ≤
        (volume.restrict (Icc (0 : ℝ) 1)).prod (volume : Measure (Vec d)) :=
      Measure.prod_mono le_rfl Measure.restrict_le_self
    have hv2 : MemLp V 2 ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
      apply (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mpr
      exact endpoint_joint_sq_integrable
        ((((hPr.2.2.1 fr).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
          isCompact_Icc) hV heV
    have hz2 : MemLp Z 2 ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
      apply (memLp_two_iff_integrable_sq_norm hZ.aestronglyMeasurable).mpr
      exact endpoint_joint_sq_integrable
        ((((hPr.2.2.1 gr).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
          isCompact_Icc) hZ heZ
    have hf2 := (Integrable.iff_ofReal (𝕜 := ℂ)).mpr (hfω K hK).swap
    have hu2 := (Integrable.iff_ofReal (𝕜 := ℂ)).mpr (huω K hK).swap
    have hd2 (j : Fin d) := (Integrable.iff_ofReal (𝕜 := ℂ)).mpr (hdω j K hK).swap
    have hfm := (memLp_two_iff_integrable_sq_norm
      (hF.comp hshift).aestronglyMeasurable).mpr hf2
    have hum := (memLp_two_iff_integrable_sq_norm
      (hU.comp hshift).aestronglyMeasurable).mpr hu2
    have hXm := endpoint_zero_extension_memLp K _ (hfm.sub (hv2.mono_measure hm))
    have hYm := endpoint_zero_extension_memLp K _ (hum.sub (hz2.mono_measure hm))
    refine ⟨hmatch, htime, ?_, ?_, ?_⟩
    · apply hXm.ae_eq
      have hq : Measurable (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
          (fun s => F (s, translate p.2 ω) - V (s, p.2)) p.1) :=
        Measurable.ite (measurableSet_Ioc.preimage measurable_fst)
          ((hF.comp hshift).sub hV) measurable_const
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hq hX)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      by_cases ht : s ∈ Ioc (0 : ℝ) 1
      · filter_upwards [hmatch s ht.1.le ht.2] with x hx
        simpa only [indicator_of_mem ht, Pi.sub_apply] using hx.symm
      · have hs0 : s ≤ 0 := by
          by_contra hn
          exact ht ⟨lt_of_not_ge hn, hs.2⟩
        exact ae_of_all _ fun x => by rw [indicator_of_notMem ht, hX0 s hs0 x]
    · exact hYm.ae_eq (ae_of_all _ fun p => (heY p).symm)
    · intro j
      have hdm := (memLp_two_iff_integrable_sq_norm
        ((hD j).comp hshift).aestronglyMeasurable).mpr (hd2 j)
      have hwm := (memLp_two_iff_integrable_sq_norm
        (hW j).aestronglyMeasurable).mpr (hi j 0 1)
      exact endpoint_zero_extension_memLp K _ (hdm.sub (hwm.mono_measure hm))

/-- The actual forward and clock endpoints obey the uniform fixed-projection
bound throughout every bounded time window. -/
theorem forward_clock_uniform_projection_of_graph_dep
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (d : ℕ) (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (hB : 0 < B) (T : ℝ) :
    ∃ R K c : ℝ, 1 ≤ R ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : Fin d ⊕ Unit,
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ ρ : ℝ, R ≤ ρ →
    let ν' : EndpointIndex d := ν.elim Sum.inl (fun _ => Sum.inr false)
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] indexedEndpoint hd Q ν' ζ P Pdag β a μ t →
      ‖E - EndpointProjection.project
        (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        K * Real.exp (-c * ρ ^ 2) := by
  obtain ⟨RL, KL, cL, hRL, hKL, hcL, hlarge⟩ :=
    endpoint_uniform_projection_large_time_of_graph_dep hlocal d hd S B hB T
  obtain ⟨KS, cS, hKS, hcS, hshort⟩ :=
    short_time_forward_clock_uniform_projection d hd S B hB
  refine ⟨max RL 4, KL + KS, min cL cS,
    hRL.trans (le_max_left _ _), add_pos hKL hKS, lt_min hcL hcS, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν t htT ρ hρ ν' p _ E hE
  by_cases ht : (t : ℝ) ≤ 1
  · have he : (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν' ζ P P β a μ t := by
      cases ν <;> exact hE
    have hb := hshort Q hQ β a μ hβ ha hμ ζ hζ P hP ν t ht ρ
      ((le_max_right RL 4).trans hρ) p E he
    exact hb.trans (mul_le_mul (le_add_of_nonneg_left hKL.le)
      (Real.exp_le_exp.mpr (by nlinarith [min_le_right cL cS, sq_nonneg ρ]))
      (Real.exp_nonneg _) (add_nonneg hKL.le hKS.le))
  · have hb := hlarge Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν' t
      (le_of_lt (lt_of_not_ge ht)) htT ρ ((le_max_left RL 4).trans hρ) p E hE
    exact hb.trans (mul_le_mul (le_add_of_nonneg_right hKS.le)
      (Real.exp_le_exp.mpr (by nlinarith [min_le_left cL cS, sq_nonneg ρ]))
      (Real.exp_nonneg _) (add_nonneg hKL.le hKS.le))

/-- Assemble the endpoint estimate from the exact announced transpose local
observation producer. The original root consumes this helper only after that
producer is checked. -/
theorem endpoint_uniform_projection_of_transpose_local_observation
    (htranspose : ∀
      (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) (hB : 0 < B),
      ∃ R K c : ℝ, 1 ≤ R ∧ 0 < K ∧ 0 < c ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
        IsComplexTransposeSemigroup Q P Pdag → ∀ t : ℝ≥0, (t : ℝ) ≤ 1 →
      ∀ ρ : ℝ, R ≤ ρ → ∃ V : Lp ℂ 2 (reducedLaw Q),
        IsComplexLocalObservation Q ρ V ∧
        ∀ᵐ ω ∂reducedLaw Q,
          ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β t ω - V ω‖ ≤
            K * Real.exp (-c * ρ ^ 2)) :
∀ (hlocal : node_e_u3A_forced_u2D_localityStmt),
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) (hB : 0 < B) (T : ℝ),
    ∃ R K c : ℝ, 1 ≤ R ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ ρ : ℝ, R ≤ ρ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] indexedEndpoint hd Q ν ζ P Pdag β a μ t →
      ‖E - EndpointProjection.project
        (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        K * Real.exp (-c * ρ ^ 2) := by
  intro hlocal d hd D B hB T
  obtain ⟨RF, KF, cF, hRF, hKF, hcF, hforward⟩ :=
    forward_clock_uniform_projection_of_graph_dep hlocal d hd D B hB T
  obtain ⟨RL, KL, cL, hRL, hKL, hcL, hlarge⟩ :=
    endpoint_uniform_projection_large_time_of_graph_dep hlocal d hd D B hB T
  obtain ⟨RT, KT, cT, hRT, hKT, hcT, htrans⟩ := htranspose d hd D B hB
  refine ⟨max RF (max RL RT), KF + KL + 2 * KT, min cF (min cL cT),
    hRF.trans (le_max_left _ _), by positivity, lt_min hcF (lt_min hcL hcT), ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν t htT ρ hρ p _ E hE
  have hρF : RF ≤ ρ := (le_max_left RF (max RL RT)).trans hρ
  have hρL : RL ≤ ρ := (le_max_left RL RT).trans ((le_max_right RF _).trans hρ)
  have hρT : RT ≤ ρ := (le_max_right RL RT).trans ((le_max_right RF _).trans hρ)
  have hF : KF * Real.exp (-cF * ρ ^ 2) ≤
      (KF + KL + 2 * KT) * Real.exp (-min cF (min cL cT) * ρ ^ 2) := by
    apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (by positivity)
    nlinarith [min_le_left cF (min cL cT), sq_nonneg ρ]
  have hL : KL * Real.exp (-cL * ρ ^ 2) ≤
      (KF + KL + 2 * KT) * Real.exp (-min cF (min cL cT) * ρ ^ 2) := by
    apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (by positivity)
    have hc := (min_le_right cF (min cL cT)).trans (min_le_left cL cT)
    nlinarith [sq_nonneg ρ]
  have hT : 2 * (KT * Real.exp (-cT * ρ ^ 2)) ≤
      (KF + KL + 2 * KT) * Real.exp (-min cF (min cL cT) * ρ ^ 2) := by
    rw [← mul_assoc]
    apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (by positivity)
    have hc := (min_le_right cF (min cL cT)).trans (min_le_right cL cT)
    nlinarith [sq_nonneg ρ]
  cases ν with
  | inl j =>
    exact (hforward Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag (.inl j)
      t htT ρ hρF p E hE).trans hF
  | inr b =>
    cases b with
    | false =>
      exact (hforward Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag (.inr ())
        t htT ρ hρF p E hE).trans hF
    | true =>
      by_cases ht : (t : ℝ) ≤ 1
      · obtain ⟨V, hV, he⟩ := htrans Q hQ β hβ ζ hζ P Pdag hP hPdag t ht ρ hρT
        exact (EndpointLocalization.norm_sub_project_le Q ρ E _ V hE hV
          (by positivity) he).trans hT
      · exact (hlarge Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag (.inr true)
          t (le_of_lt (lt_of_not_ge ht)) htT ρ hρL p E hE).trans hL

/-- The rational radial weight is smooth and separates the inner and outer balls. -/
theorem c7_bounded_radial_weight_values {d : ℕ} (z : Vec d)
    {ρ : ℝ} (hρ : 0 < ρ) :
    let ψ : Vec d → ℝ := fun x =>
      ρ * euclideanSq (x-z) / (ρ^2 + euclideanSq (x-z))
    ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ ρ) ∧
      (∀ x, euclideanNorm (x-z) ≤ ρ/2 → ψ x ≤ ρ/5) ∧
      (∀ x, ρ ≤ euclideanNorm (x-z) → ρ/2 ≤ ψ x) := by
  let R : Vec d → ℝ := fun x => euclideanSq (x-z)
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := by
    unfold R euclideanSq dot
    fun_prop
  have hpos (x : Vec d) : 0 < ρ ^ 2 + R x := by
    dsimp [R]
    have := euclideanSq_nonneg_coords (x-z)
    positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (contDiff_const.mul hR).div (contDiff_const.add hR) (fun x => ne_of_gt (hpos x))
  · intro x
    have hr : 0 ≤ R x := euclideanSq_nonneg_coords (x-z)
    constructor
    · exact div_nonneg (mul_nonneg hρ.le hr) (hpos x).le
    · apply (div_le_iff₀ (hpos x)).2
      nlinarith [mul_nonneg hρ.le (sq_nonneg ρ)]
  · intro x hx
    have hr : 0 ≤ R x := euclideanSq_nonneg_coords (x-z)
    have hn : euclideanNorm (x-z) ^ 2 = R x := Real.sq_sqrt hr
    have hn0 : 0 ≤ euclideanNorm (x-z) := Real.sqrt_nonneg _
    have hs : 4 * R x ≤ ρ ^ 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ ρ / 2 - euclideanNorm (x-z))
        (by positivity : 0 ≤ ρ / 2 + euclideanNorm (x-z))]
    apply (div_le_iff₀ (hpos x)).2
    nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hs)]
  · intro x hx
    have hr : 0 ≤ R x := euclideanSq_nonneg_coords (x-z)
    have hn : euclideanNorm (x-z) ^ 2 = R x := Real.sq_sqrt hr
    have hs : ρ ^ 2 ≤ R x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by linarith : 0 ≤ euclideanNorm (x-z) + ρ)]
    apply (le_div_iff₀ (hpos x)).2
    nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hs)]

/-- Coordinate derivative of the rational radial weight. -/
theorem c7_bounded_radial_weight_derivative {d : ℕ} (z x : Vec d)
    {ρ : ℝ} (hρ : 0 < ρ) (j : Fin d) :
    fderiv ℝ (fun y : Vec d =>
      ρ * euclideanSq (y-z) / (ρ^2 + euclideanSq (y-z))) x (unitVector j) =
      2 * ρ ^ 3 * (x j - z j) / (ρ ^ 2 + euclideanSq (x-z)) ^ 2 := by
  let R : Vec d → ℝ := fun y => euclideanSq (y-z)
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := by
    unfold R euclideanSq dot
    fun_prop
  have hpos : 0 < ρ ^ 2 + R x := by
    have := euclideanSq_nonneg_coords (x-z)
    dsimp [R]
    positivity
  have hcoord : fderiv ℝ R x (unitVector j) = 2 * (x j - z j) := by
    have h := Homogenization.fderiv_euclideanSqDist_apply_basisVec z x j
    simpa [R, Homogenization.euclideanSqDist, Homogenization.vecNormSq,
      Homogenization.vecDot, euclideanSq, dot, Homogenization.basisVec, unitVector] using h
  have hscalar := ((hasDerivAt_id (R x)).const_mul ρ).div
    ((hasDerivAt_id (R x)).const_add (ρ ^ 2)) (ne_of_gt hpos)
  have hD := hscalar.comp_hasFDerivAt x ((hR.differentiable (by simp)) x).hasFDerivAt
  have h := congrArg (fun D : Vec d →L[ℝ] ℝ => D (unitVector j)) hD.fderiv
  simp only [Function.comp_def, smul_apply, smul_eq_mul, hcoord] at h
  dsimp [R] at h ⊢
  rw [h]
  ring

/-- A smooth bounded radial weight with a dimension-free Euclidean gradient bound. -/
theorem c7_bounded_radial_weight_geometry {d : ℕ} (z : Vec d)
    {ρ : ℝ} (hρ : 0 < ρ) :
    let ψ : Vec d → ℝ := fun x =>
      ρ * euclideanSq (x-z) / (ρ^2 + euclideanSq (x-z))
    ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ ρ) ∧
      (∀ x, euclideanSq (fun j : Fin d => fderiv ℝ ψ x (unitVector j)) ≤ 1) ∧
      (∀ x, euclideanNorm (x-z) ≤ ρ/2 → ψ x ≤ ρ/5) ∧
      (∀ x, ρ ≤ euclideanNorm (x-z) → ρ/2 ≤ ψ x) := by
  obtain ⟨hsmooth, hvalues, hinner, houter⟩ := c7_bounded_radial_weight_values z hρ
  refine ⟨hsmooth, hvalues, ?_, hinner, houter⟩
  intro x
  let r := euclideanNorm (x-z)
  let D := ρ ^ 2 + euclideanSq (x-z)
  let K := 2 * ρ ^ 3 / D ^ 2
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hs : 0 ≤ euclideanSq (x-z) := euclideanSq_nonneg_coords _
  have hrsq : r ^ 2 = euclideanSq (x-z) := Real.sq_sqrt hs
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hfirst : 2 * ρ * r ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg (ρ-r)]
  have hsecond : ρ ^ 2 ≤ D := by dsimp [D]; linarith
  have hproduct := mul_le_mul hfirst hsecond (sq_nonneg ρ) hD.le
  have hKr : K * r ≤ 1 := by
    dsimp [K]
    rw [div_mul_eq_mul_div, div_le_one (sq_pos_of_pos hD)]
    nlinarith [hproduct]
  have hsq : euclideanSq (fun j : Fin d =>
      fderiv ℝ (fun y : Vec d =>
        ρ * euclideanSq (y-z) / (ρ^2 + euclideanSq (y-z))) x (unitVector j)) =
      (K * r) ^ 2 := by
    calc
      _ = K ^ 2 * euclideanSq (x-z) := by
        change (∑ j : Fin d, (fderiv ℝ (fun y : Vec d =>
          ρ * euclideanSq (y-z) / (ρ^2 + euclideanSq (y-z))) x (unitVector j)) *
          (fderiv ℝ (fun y : Vec d =>
          ρ * euclideanSq (y-z) / (ρ^2 + euclideanSq (y-z))) x (unitVector j))) =
          K ^ 2 * ∑ j : Fin d, (x-z) j * (x-z) j
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [c7_bounded_radial_weight_derivative z x hρ j]
        simp only [Pi.sub_apply]
        dsimp [K, D]
        ring
      _ = (K * r) ^ 2 := by rw [← hrsq]; ring
  rw [hsq]
  nlinarith [mul_nonneg hK hr, sq_nonneg (1 - K*r)]

/-- A linear factor is absorbed by retaining half of a Gaussian exponent. -/
theorem c7_linear_mul_gaussian_le (x : ℝ) :
    x * Real.exp (-x ^ 2) ≤ Real.exp (-(x ^ 2 / 2)) := by
  have hx : x ≤ Real.exp (x ^ 2 / 2) := by
    have he := Real.add_one_le_exp (x ^ 2 / 2)
    nlinarith [sq_nonneg (x - 1)]
  calc
    x * Real.exp (-x ^ 2) ≤ Real.exp (x ^ 2 / 2) * Real.exp (-x ^ 2) :=
      mul_le_mul_of_nonneg_right hx (Real.exp_nonneg _)
    _ = Real.exp (-(x ^ 2 / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The bounded radial exponential is an admissible Davies weight. -/
theorem c7_radial_exp_s5Weight {d : ℕ} (z : Vec d)
    {ρ q : ℝ} (hρ : 0 < ρ) (hq : 0 ≤ q) :
    let ψ : Vec d → ℝ := fun x =>
      ρ * euclideanSq (x-z) / (ρ^2 + euclideanSq (x-z))
    S5Weight (fun x => Real.exp (q * ψ x)) (Real.exp (q * ρ)) q := by
  let ψ : Vec d → ℝ := fun x =>
    ρ * euclideanSq (x-z) / (ρ^2 + euclideanSq (x-z))
  obtain ⟨hsmooth, hvalues, hgrad, _, _⟩ := c7_bounded_radial_weight_geometry z hρ
  have hn (x : Vec d) : s5Nrm (fun j => coordinateDerivative j ψ x) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (hgrad x)
    simpa [s5Nrm, coordinateDerivative, euclideanSq, dot, pow_two, ψ] using h
  refine ⟨Real.contDiff_exp.comp (contDiff_const.mul hsmooth),
    (Real.exp_pos _).le, hq, ?_, ?_⟩
  · intro x
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hvalues x).2 hq)
  · intro x
    have hd : DifferentiableAt ℝ ψ x := (hsmooth.differentiable (by simp)).differentiableAt
    have he : (fun j => coordinateDerivative j (fun y => Real.exp (q * ψ y)) x) =
        (fun j => (q * Real.exp (q * ψ x)) * coordinateDerivative j ψ x) := by
      funext j
      have hder := ((hasDerivAt_id (ψ x)).const_mul q).exp
      have hh := s5_coordDeriv_comp hder hd j
      simpa [mul_comm] using hh
    rw [he, s5Nrm_smul, abs_of_nonneg (mul_nonneg hq (Real.exp_pos _).le),
      abs_of_pos (Real.exp_pos _)]
    nlinarith [mul_nonneg (mul_nonneg hq (Real.exp_pos (q * ψ x)).le)
      (sub_nonneg.mpr (hn x))]

/-- The inner and outer radial regions are separated by an exponential gap. -/
theorem c7_radial_exp_separation {d : ℕ} (z x y : Vec d)
    {ρ q : ℝ} (hρ : 0 < ρ) (hq : 0 ≤ q)
    (hx : euclideanNorm (x-z) ≤ ρ/2) (hy : ρ ≤ euclideanNorm (y-z)) :
    Real.exp (q * (ρ * euclideanSq (x-z) / (ρ^2 + euclideanSq (x-z)))) ≤
      Real.exp (-(3 * q * ρ / 10)) *
        Real.exp (q * (ρ * euclideanSq (y-z) / (ρ^2 + euclideanSq (y-z)))) := by
  obtain ⟨_, _, _, hinner, houter⟩ := c7_bounded_radial_weight_geometry z hρ
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (hinner x hx) hq
  have h' := mul_le_mul_of_nonneg_left (houter y hy) hq
  linarith

/-- Optimizing the radial gap against a quadratic weighted-energy cost. -/
theorem c7_radial_gap_optimized {A t ρ : ℝ} (hA : 0 < A) (ht : 0 < t) :
    let q := 3 * ρ / (20 * A * t)
    A * t * q ^ 2 - 3 * q * ρ / 10 = -(9 * ρ ^ 2 / (400 * A * t)) := by
  dsimp
  field_simp
  <;> ring

/-- An admissible bounded weight preserves the actual physical H¹ graph. -/
theorem c7_s5Weight_mul_physicalGraph {d : ℕ} {φ : Vec d → ℝ} {B q : ℝ}
    (hφ : S5Weight φ B q)
    (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G) :
    ∃ (w : Lp ℂ 2 (volume : Measure (Vec d)))
      (J : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) w J ∧
      (w : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ) * u x) ∧
      ∀ j, (J j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (φ x : ℂ) * G j x + u x * (coordinateDerivative j φ x : ℂ)) := by
  have hb : MemLp (fun x => (φ x : ℂ)) ∞ (volume : Measure (Vec d)) := by
    refine memLp_top_of_bound ?_ B (Filter.Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_ofReal.comp hφ.smooth.continuous).aestronglyMeasurable
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hφ.bound x
  have hd (j : Fin d) : MemLp (fun x => (coordinateDerivative j φ x : ℂ)) ∞
      (volume : Measure (Vec d)) := by
    refine memLp_top_of_bound ?_ (q * B) (Filter.Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_ofReal.comp
        ((hφ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)).aestronglyMeasurable
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact (s5_abs_le_nrm _ j).trans ((hφ.grad x).trans
        (mul_le_mul_of_nonneg_left (hφ.bound x) hφ.q_nonneg))
  exact physicalH1Graph_mul_smooth φ hφ.smooth hb hd u G hu

/-- The Euclidean weight-gradient condition bounds the full correction
without introducing a dimension-dependent coordinate estimate. -/
theorem c7_weight_gradient_correction_pointwise {d : ℕ}
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (x : Vec d) (u : ℂ) :
    (∑ j, ‖(coordinateDerivative j φ x : ℂ) * u‖ ^ 2) ≤
      q ^ 2 * ‖(φ x : ℂ) * u‖ ^ 2 := by
  have hg := hφ.grad x
  have hs : (∑ j, coordinateDerivative j φ x ^ 2) ≤ (q * |φ x|) ^ 2 := by
    have hn : 0 ≤ ∑ j, coordinateDerivative j φ x ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have he : s5Nrm (fun j => coordinateDerivative j φ x) ^ 2 =
        ∑ j, coordinateDerivative j φ x ^ 2 := by
      exact Real.sq_sqrt hn
    have hnon : 0 ≤ s5Nrm (fun j => coordinateDerivative j φ x) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (q * |φ x| - s5Nrm (fun j => coordinateDerivative j φ x))]
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖u‖)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    ← Finset.sum_mul] at ⊢
  simpa only [mul_pow, sq_abs, mul_assoc] using hm

/-- The pointwise weight-gradient correction also holds in the physical L²
norm, for any representatives of the actual weighted products. -/
theorem c7_weight_gradient_correction_L2 {d : ℕ}
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (u w : Lp ℂ 2 (volume : Measure (Vec d)))
    (V : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hw : (w : Vec d → ℂ) =ᵐ[volume] fun x => (φ x : ℂ) * u x)
    (hV : ∀ j, (V j : Vec d → ℂ) =ᵐ[volume]
      fun x => (coordinateDerivative j φ x : ℂ) * u x) :
    (∑ j, ‖V j‖ ^ 2) ≤ q ^ 2 * ‖w‖ ^ 2 := by
  have hleft : Integrable (fun x => ∑ j, ‖V j x‖ ^ 2) volume :=
    integrable_finsetSum _ fun j _ => (Lp.memLp (V j)).norm.integrable_sq
  have hright : Integrable (fun x => q ^ 2 * ‖w x‖ ^ 2) volume :=
    ((Lp.memLp w).norm.integrable_sq).const_mul _
  have hpoint : ∀ᵐ x ∂volume, (∑ j, ‖V j x‖ ^ 2) ≤ q ^ 2 * ‖w x‖ ^ 2 := by
    filter_upwards [hw, ae_all_iff.mpr hV] with x hx hxy
    simp only [hx, hxy]
    exact c7_weight_gradient_correction_pointwise hφ x (u x)
  have hi := integral_mono_ae hleft hright hpoint
  rw [integral_finsetSum _ (fun j _ => (Lp.memLp (V j)).norm.integrable_sq),
    integral_const_mul] at hi
  simpa only [← physicalL2_norm_sq] using hi

/-- The actual transpose graph tested against a weighted physical H¹ function. -/
theorem c7_transpose_weak_weighted_test {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    (∫ x, g x * ((φ x : ℂ) * v x)) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x *
        ((φ x : ℂ) * H j x + v x * (coordinateDerivative j φ x : ℂ))) +
      ζ * (∫ x, u x * (∑ j, (a x j i : ℂ) *
        ((φ x : ℂ) * H j x + v x * (coordinateDerivative j φ x : ℂ)))) := by
  obtain ⟨K, hK, hweak⟩ := hug
  have hKG := physicalH1Graph_gradient_unique volume (Or.inl rfl) u K G hK hu
  rw [hKG] at hweak
  obtain ⟨w, J, hw, hwrep, hJrep⟩ := c7_s5Weight_mul_physicalGraph hφ v H hv
  have ht := hweak w J hw
  have hleft : (∫ x, g x * w x) = ∫ x, g x * ((φ x : ℂ) * v x) := by
    apply integral_congr_ae
    filter_upwards [hwrep] with x hx
    rw [hx]
  have hpr : (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x * J j x) =
      ∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x *
        ((φ x : ℂ) * H j x + v x * (coordinateDerivative j φ x : ℂ)) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hJrep] with x hx
    simp only [hx]
  have hdr : (∫ x, u x * (∑ j, (a x j i : ℂ) * J j x)) =
      ∫ x, u x * (∑ j, (a x j i : ℂ) *
        ((φ x : ℂ) * H j x + v x * (coordinateDerivative j φ x : ℂ))) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hJrep] with x hx
    simp only [hx]
  rwa [hleft, hpr, hdr] at ht

/-- Squaring an admissible weight gives the weight used in the energy test. -/
theorem c7_s5Weight_sq {d : ℕ} {φ : Vec d → ℝ} {B q : ℝ}
    (hφ : S5Weight φ B q) :
    S5Weight (fun x => φ x * φ x) (B * B) (2 * q) := by
  refine ⟨hφ.sq_smooth, mul_nonneg hφ.B_nonneg hφ.B_nonneg,
    mul_nonneg (by norm_num) hφ.q_nonneg, hφ.sq_bound, ?_⟩
  intro x
  simpa only [abs_of_nonneg (mul_self_nonneg (φ x)), mul_assoc] using hφ.sq_grad x


/-- The transpose weak graph paired with the conjugate of an H¹ function,
using the square of the weight required by the shifted energy argument. -/
theorem c7_transpose_weak_squared_weight_test {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    (∫ x, g x * (((φ x * φ x : ℝ) : ℂ) * star (v x))) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x *
        (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
          star (v x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ))) +
      ζ * (∫ x, u x * (∑ j, (a x j i : ℂ) *
        (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
          star (v x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)))) := by
  have ht := c7_transpose_weak_weighted_test a i ζ hug G hu
    (c7_s5Weight_sq hφ) (star v) (fun j => star (H j))
    (s5_isPhysicalH1Graph_star v H hv)
  have hleft : (∫ x, g x * (((φ x * φ x : ℝ) : ℂ) * (star v) x)) =
      ∫ x, g x * (((φ x * φ x : ℝ) : ℂ) * star (v x)) := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star v] with x hx
    simpa only [Pi.star_apply] using congrArg (fun z => g x * (((φ x * φ x : ℝ) : ℂ) * z)) hx
  have hpr : (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x *
      (((φ x * φ x : ℝ) : ℂ) * (star (H j)) x +
        (star v) x * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ))) =
      ∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x *
      (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
        star (v x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star v, ae_all_iff.mpr (fun j => Lp.coeFn_star (H j))] with x hvx hHx
    simp only [hvx, hHx, Pi.star_apply]
  have hdr : (∫ x, u x * (∑ j, (a x j i : ℂ) *
      (((φ x * φ x : ℝ) : ℂ) * (star (H j)) x +
        (star v) x * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)))) =
      ∫ x, u x * (∑ j, (a x j i : ℂ) *
      (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
        star (v x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ))) := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star v, ae_all_iff.mpr (fun j => Lp.coeFn_star (H j))] with x hvx hHx
    simp only [hvx, hHx, Pi.star_apply]
  rwa [hleft, hpr, hdr] at ht

/-- Uniform endpoint projection from the locality graph dependency. -/
theorem endpoint_uniform_projection_of_graph_deps :
∀ (hlocal : node_e_u3A_forced_u2D_localityStmt),
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) (hB : 0 < B) (T : ℝ),
    ∃ R K c : ℝ, 1 ≤ R ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ ρ : ℝ, R ≤ ρ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] indexedEndpoint hd Q ν ζ P Pdag β a μ t →
      ‖E - EndpointProjection.project
        (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        K * Real.exp (-c * ρ ^ 2) :=
  endpoint_uniform_projection_of_transpose_local_observation
    short_time_transpose_local_observation_of_graph_deps

theorem node_stationary_u2D_analytic_u2D_semigroup_u23_endpoints_of_deps
    (hA : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (hlocal : node_e_u3A_forced_u2D_localityStmt) :
    node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt := by
  intro d hd D q hq T B hT hB
  let : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  obtain ⟨CE, hCE, hrep⟩ := EndpointFiniteP.exists_representatives hA d hd D q hq T B hT hB
  obtain ⟨R, A, c, hR, hApos, hc, hloc⟩ :=
    endpoint_uniform_projection_of_graph_deps hlocal d hd D (B + 1) (by linarith) T
  let C := max 1 (max R (max (2 * CE) (2 * A)))
  have hC : 1 ≤ C := le_max_left _ _
  have hRC : R ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hEC : 2 * CE ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hAC : 2 * A ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hEC' : CE ≤ C := (by linarith : CE ≤ 2 * CE).trans hEC
  have hAC' : A ≤ C := (by linarith : A ≤ 2 * A).trans hAC
  refine ⟨C, c, hC, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag ν t ht
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨E, he, han, hed, hem, hen⟩ := hrep Q hQ β a μ hβ ha hμ P Pdag hP hPdag ν t ht
  let H := divide E
  have h0 : DifferentiableAt ℂ E 0 := (han 0).differentiableAt
  have hHd : DifferentiableOn ℂ H {z | ‖z‖ < B} :=
    (differentiableOn_divide (by linarith : 0 < B + 1) hed).mono
      (fun z hz => by dsimp at *; linarith)
  have hHn (z : ℂ) (hz : ‖z‖ < B) : ‖H z‖ ≤ C :=
    (norm_divide_le hB hed hen hz).trans hEC
  have hHm (z : ℂ) : (∫ ω, H z ω ∂reducedLaw Q) = 0 :=
    integral_divide_eq_zero h0 hem z
  refine ⟨E, H, he, hed, hHd, fun z hz => (hen z hz).trans hEC',
    fun z hz => ⟨factor E z, hHm z, hHn z hz⟩, ?_⟩
  intro ρ hρ
  let m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}
  have hm := Probability.localSigma_le_borel
    {x : Vec d | euclideanNorm x < ρ}
  let L := fun z => project (m := m) (E z)
  let K := fun z => project (m := m) (H z)
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hq)
  have hL2 (z : ℂ) := exists_local_l2 (p := ENNReal.ofReal q) Q ρ hp2 (E z)
  have hK2 (z : ℂ) := exists_local_l2 (p := ENNReal.ofReal q) Q ρ hp2 (H z)
  choose L₂ hLe hLl using hL2
  choose K₂ hKe hKl using hK2
  have hLd : DifferentiableOn ℂ L {z | ‖z‖ < B + 1} := differentiableOn_project hed
  have hKd : DifferentiableOn ℂ K {z | ‖z‖ < B} := differentiableOn_project hHd
  have herr (z : ℂ) (hz : ‖z‖ ≤ B + 1) :
      ‖E z - L z‖ ≤ A * Real.exp (-c * ρ ^ 2) :=
    hloc Q hQ β a μ hβ ha hμ z hz (P z) (Pdag z) (hP z) (hPdag z)
      ν t ht ρ (hRC.trans hρ) (ENNReal.ofReal q) (E z) (he z)
  have hLfactor (z : ℂ) : L z - L 0 = z • K z := by
    rw [factor L z, divide_project h0 z]
  refine ⟨L, K, L₂, K₂, fun z => ⟨hLe z, hKe z, hLl z, hKl z⟩,
    hLd, hed.sub hLd, hKd, hHd.sub hKd, ?_, ?_⟩
  · intro z hz
    refine ⟨?_, (norm_project_le (E z)).trans ((hen z hz).trans hEC'), ?_⟩
    · exact (integral_project hm (E z)).trans (hem z)
    · exact (herr z hz).trans (mul_le_mul_of_nonneg_right hAC' (Real.exp_pos _).le)
  · intro z hz
    refine ⟨hLfactor z, ?_, ?_, (norm_project_le (H z)).trans (hHn z hz), ?_⟩
    · calc
        (E z - L z) - (E 0 - L 0) = (E z - E 0) - (L z - L 0) := by abel
        _ = z • H z - z • K z := by rw [factor E z, hLfactor z]
        _ = z • (H z - K z) := (smul_sub _ _ _).symm
    · exact (integral_project hm (H z)).trans (hHm z)
    · exact (norm_divide_sub_project_le hB hed herr hz).trans (by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le)


end EinsteinFull.Blueprint
