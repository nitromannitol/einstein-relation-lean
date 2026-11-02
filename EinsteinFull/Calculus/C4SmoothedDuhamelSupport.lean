import EinsteinFull.Blueprint.Foundation.node_e_u3A_centered_u2D_equations
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import EinsteinFull.Frozen.GaussianAverage
import EinsteinFull.Calculus.ComplexGeneratorUniquenessSupport
import EinsteinFull.Work.W4.HomogeneousForwardPairingTimeDerivativeSupport
import EinsteinFull.Work.W4.HomogeneousGaussianTimeIntegralSupport
import EinsteinFull.Calculus.ComplexSpatialFluxSupport
import EinsteinRelation.Correctors.StationaryWeightedOrbit
import EinsteinRelation.Correctors.HorizontalCoreDivergence
import EinsteinRelation.Correctors.SpatialWeakProduct
import EinsteinRelation.Calculus.Mollifier
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
Internal prerequisites for the smoothed late-time identity. These lemmas use
actual indexed endpoints. They do not assert the smoothed Duhamel estimate.
-/

open MeasureTheory
open scoped NNReal Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The gradient and the literal coefficient-defect flux are unique. Thus the
flux chosen by the decay proposition is the one in the centered equation. -/
theorem endpointWeakFlux_unique {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {ν : EndpointIndex d} {ζ : ℂ}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    {U : Lp ℂ 2 (reducedLaw Q)}
    {G J G' J' : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (h : IsEndpointWeakFlux hd Q ν ζ a U G J)
    (h' : IsEndpointWeakFlux hd Q ν ζ a U G' J') :
    G = G' ∧ J = J' := by
  have hG := h.1.unique h'.1
  refine ⟨hG, ?_⟩
  subst G'
  funext j
  exact Lp.ext ((h.2 j).trans (h'.2 j).symm)

/-- Bilinear L2 pairing used for the signed backward homogeneous test. -/
def c4EndpointPairing {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) :
    Lp ℂ 2 (reducedLaw Q) →L[ℝ] Lp ℂ 2 (reducedLaw Q) →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2).bilinearRestrictScalars ℝ

/-- This pairing has no complex conjugation. -/
theorem c4EndpointPairing_apply {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    c4EndpointPairing Q f g = ∫ ω, f ω * g ω ∂reducedLaw Q :=
  ContinuousLinearMap.lpPairing_eq_integral _ _ _

/-- Moving an actual homogeneous average to the second bilinear slot reverses
its force. This includes the anisotropic unforced Gaussian used for smoothing. -/
theorem c4EndpointPairing_homogeneousAverage {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    c4EndpointPairing Q (homogeneousAverage Q i s hs ζ f) g =
      c4EndpointPairing Q f (homogeneousAverage Q i s hs (-ζ) g) := by
  simpa only [c4EndpointPairing_apply] using
    integral_homogeneousAverage_bilinear_transpose Q i s hs ζ f g

/-- The boundary difference for the backward Gaussian interaction is exactly
that of the smoothed physical endpoint and its actual signed homogeneous
propagation. The zero-time homogeneous evolution is evaluated as the identity;
no endpoint is replaced by an independently chosen mild solution. -/
theorem c4SmoothedEndpoint_boundary {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (s : ℝ) (hs : 0 < s) (T τ : ℝ) (hτT : τ < T)
    (g : Lp ℂ 2 (reducedLaw Q)) :
    let U := fun t : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ t.toNNReal
    let ξ := (endpointDriftSign ν : ℂ) * ζ
    let v := homogeneousAverage Q ⟨0, by omega⟩ (T - τ) (sub_pos.mpr hτT) ξ (U τ)
    let test := gaussianAverage hd Q s hs g
    c4EndpointPairing Q (gaussianAverage hd Q s hs (U T - v)) g =
      c4EndpointPairing Q (U T)
        (homogeneousGaussianEvolution Q ⟨0, by omega⟩ (-ξ) (T - T).toNNReal test) -
      c4EndpointPairing Q (U τ)
        (homogeneousGaussianEvolution Q ⟨0, by omega⟩ (-ξ) (T - τ).toNNReal test) := by
  dsimp only
  have ht : 0 < ((T - τ).toNNReal : ℝ) := by
    simpa only [Real.coe_toNNReal (T - τ) (sub_pos.mpr hτT).le] using sub_pos.mpr hτT
  simp only [sub_self, Real.toNNReal_zero, homogeneousGaussianEvolution_zero,
    ContinuousLinearMap.id_apply]
  rw [homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩
    (-((endpointDriftSign ν : ℂ) * ζ)) (T - τ).toNNReal ht]
  simp only [Real.coe_toNNReal (T - τ) (sub_pos.mpr hτT).le]
  change c4EndpointPairing Q (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 _) _ = _
  rw [c4EndpointPairing_homogeneousAverage, neg_zero, map_sub]
  exact congrArg (fun z => _ - z)
    (c4EndpointPairing_homogeneousAverage Q ⟨0, by omega⟩ (T - τ)
      (sub_pos.mpr hτT) ((endpointDriftSign ν : ℂ) * ζ) _ _)

/-- The late-time flux decay is integrable with the required gain at the
lower endpoint; the upper endpoint contributes a nonnegative term. -/
theorem c4LateFlux_tail_integral {ε τ T : ℝ} (hε : 0 < ε) (hτ : 0 < τ)
    (hτT : τ ≤ T) :
    (∫ r in τ..T, r ^ (-1 - ε)) ≤ τ ^ (-ε) / ε := by
  have hzero : (0 : ℝ) ∉ Set.uIcc τ T := by
    rw [Set.uIcc_of_le hτT]
    exact fun h => (not_le_of_gt hτ) h.1
  rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩)]
  have hexp : -1 - ε + 1 = -ε := by ring
  rw [hexp]
  have heq : (T ^ (-ε) - τ ^ (-ε)) / -ε =
      (τ ^ (-ε) - T ^ (-ε)) / ε := by ring
  rw [heq]
  exact div_le_div_of_nonneg_right
    (sub_le_self _ (Real.rpow_nonneg (hτ.le.trans hτT) _)) hε.le

/-- Product rule with the literal signed backward Gaussian derivative. -/
theorem c4BackwardGaussian_hasDerivAt {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ξ : ℂ)
    (g : Lp ℂ 2 (reducedLaw Q)) (T t : ℝ) (htT : t < T)
    {u : ℝ → Lp ℂ 2 (reducedLaw Q)} {u' : Lp ℂ 2 (reducedLaw Q)}
    (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s : ℝ => c4EndpointPairing Q (u s)
      (homogeneousGaussianEvolution Q i (-ξ) (T - s).toNNReal g))
      (c4EndpointPairing Q u'
          (homogeneousGaussianEvolution Q i (-ξ) (T - t).toNNReal g) -
        c4EndpointPairing Q (u t)
          (homogeneousGaussianEvolutionTimeDerivative Q i (-ξ) g (T - t))) t := by
  have hg := (hasDerivAt_homogeneousGaussianEvolution_time Q i (-ξ) g
    (T - t) (sub_pos.mpr htT)).scomp t ((hasDerivAt_id t).const_sub T)
  have hh := (c4EndpointPairing Q).hasDerivAt_of_bilinear (fun _ => hu) (fun _ => hg)
  rw [homogeneousGaussianEvolutionTimeDerivative, dite_eq_left (sub_pos.mpr htT)]
  simpa only [Function.comp_apply, zero_sub, neg_smul, one_smul, map_neg,
    sub_eq_add_neg, add_comm] using! hh

section ActualEndpoint

variable (hc : Blueprint.node_e_u3A_centered_u2D_equationsStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)

include hc hQ hβ ha hμ hP hPdag

/-- The centered-equation contract supplies ordinary real differentiability
of each actual endpoint at every positive time, including the transpose. -/
theorem c4IndexedEndpoint_differentiableAt (t : ℝ) (ht : 0 < t) :
    DifferentiableAt ℝ (fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal) t := by
  obtain ⟨G, J, V, _, hV, _⟩ :=
    hc d hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t.toNNReal
      (by simpa only [Real.coe_toNNReal t ht.le] using ht)
  rw [Real.coe_toNNReal t ht.le] at hV
  exact hV.differentiableAt

/-- Differentiation of the actual centered endpoint against the signed
backward Gaussian, without a generator-domain premise on the endpoint datum.
The remaining PDE-testing step must identify this derivative with the flux. -/
theorem c4IndexedEndpoint_backwardGaussian_hasDerivAt
    (g : Lp ℂ 2 (reducedLaw Q)) (T t : ℝ) (ht : 0 < t) (htT : t < T) :
    let U := fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal
    let ξ := (endpointDriftSign ν : ℂ) * ζ
    HasDerivAt (fun s : ℝ => c4EndpointPairing Q (U s)
      (homogeneousGaussianEvolution Q ⟨0, by omega⟩ (-ξ) (T - s).toNNReal g))
      (c4EndpointPairing Q (deriv U t)
          (homogeneousGaussianEvolution Q ⟨0, by omega⟩ (-ξ) (T - t).toNNReal g) -
        c4EndpointPairing Q (U t)
          (homogeneousGaussianEvolutionTimeDerivative Q ⟨0, by omega⟩ (-ξ) g (T - t))) t := by
  exact c4BackwardGaussian_hasDerivAt Q ⟨0, by omega⟩
    ((endpointDriftSign ν : ℂ) * ζ) g T t htT
    (c4IndexedEndpoint_differentiableAt hc hd D Q hQ β a μ hβ ha hμ
      ζ P Pdag hP hPdag ν t ht).hasDerivAt

end ActualEndpoint

open EinsteinRelation.Correctors

private theorem c4Continuous_coordinateDerivative {d : ℕ} {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (i : Fin d) :
    Continuous (coordinateDerivative i η) :=
  ((contDiff_infty_iff_fderiv.mp hη).2.clm_apply contDiff_const).continuous

/-- A compact smooth spatial test has zero integrated coordinate derivative.
Source: `paper/main.tex:779–806`, spatial to horizontal weak equations. -/
private theorem c4Integral_coordinateDerivative_eq_zero {d : ℕ} {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) (i : Fin d) :
    (∫ x, coordinateDerivative i η x ∂volume) = 0 := by
  have hint : Integrable (coordinateDerivative i η) volume :=
    (c4Continuous_coordinateDerivative hη i).integrable_of_hasCompactSupport
    (hηc.fderiv_apply ℝ (unitVector i))
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Vec d))) (f := fun _ => (1 : ℝ))
    (g := η) (v := unitVector i)
    (by simp)
    (by simpa only [one_mul] using! hint)
    (by simpa only [one_mul] using hη.continuous.integrable_of_hasCompactSupport hηc)
    (fun _ _ => differentiableAt_const (1 : ℝ)) (fun x _ => hη.differentiable (by simp) x)
  simpa [coordinateDerivative] using h


private theorem c4StationarySpatialDivergence_integral_test {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {W : FieldPair d → Vec d} {h : FieldPair d → ℝ}
    (hWm : Measurable W) (hhm : Measurable h)
    (hW : ∀ i, MemLp (fun ω => W ω i) 2 Q) (hh : MemLp h 2 Q)
    (hweak : ∀ᵐ ω ∂Q, HasWeakDivergence Set.univ
      (fun x => W (translate x ω)) (orbit h ω))
    {H : FieldPair d → ℝ} (hH : IsHorizontalTest H) :
    (∫ ω, ∑ i, W ω i * horizontalDerivative i H ω ∂Q) =
      -(∫ ω, h ω * H ω ∂Q) := by
  let η := mollifier d
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := contDiff_mollifier d
  have hηc : HasCompactSupport η := hasCompactSupport_mollifier d
  have hη1 : (∫ x, η x ∂volume) = 1 := integral_mollifier d
  have hηi : Integrable η volume := hη.continuous.integrable_of_hasCompactSupport hηc
  have hηD (i : Fin d) : Continuous (coordinateDerivative i η) :=
    ((contDiff_infty_iff_fderiv.mp hη).2.clm_apply contDiff_const).continuous
  have hηDi (i : Fin d) : Integrable (coordinateDerivative i η) volume :=
    (hηD i).integrable_of_hasCompactSupport (hηc.fderiv_apply ℝ (unitVector i))
  have hWim (i : Fin d) : Measurable (fun ω => W ω i) :=
    (measurable_pi_apply i).comp hWm
  have hA (i : Fin d) := integrable_weighted_orbit Q hQ hη.continuous.measurable hηi
    ((hWim i).mul (hH.measurable_derivative i))
    ((hW i).integrable_mul (hH.memLp_derivative Q 2 i))
  have hB (i : Fin d) := integrable_weighted_orbit Q hQ (hηD i).measurable (hηDi i)
    ((hWim i).mul hH.1) ((hW i).integrable_mul (hH.memLp Q 2))
  dsimp only [Pi.mul_apply] at hA hB
  have hsections : ∀ᵐ ω ∂Q, ∀ i : Fin d,
      Integrable (fun x => η x * (W (translate x ω) i *
        horizontalDerivative i H (translate x ω))) volume ∧
      Integrable (fun x => coordinateDerivative i η x *
        (W (translate x ω) i * H (translate x ω))) volume :=
    ae_all_iff.mpr fun i => (hA i).prod_left_ae.and (hB i).prod_left_ae
  have heq :
      (fun ω => (∑ i : Fin d, ∫ x, η x * (W (translate x ω) i *
          horizontalDerivative i H (translate x ω))) +
        ∑ i : Fin d, ∫ x, coordinateDerivative i η x *
          (W (translate x ω) i * H (translate x ω))) =ᵐ[Q]
      fun ω => -(∫ x, η x * (h (translate x ω) * H (translate x ω))) := by
    filter_upwards [hweak, hsections] with ω hω hs
    have ht : IsSpatialTest Set.univ (fun x => η x * orbit H ω x) :=
      ⟨hη.mul (hH.2.1 ω), hηc.mul_right, Set.subset_univ _⟩
    have hw := hω.2.2 _ ht
    rw [Measure.restrict_univ] at hw
    rw [← integral_finsetSum Finset.univ (fun i _ => (hs i).1),
      ← integral_finsetSum Finset.univ (fun i _ => (hs i).2),
      ← integral_add (integrable_finsetSum Finset.univ (fun i _ => (hs i).1))
        (integrable_finsetSum Finset.univ (fun i _ => (hs i).2))]
    calc
      _ = ∫ x, dot (W (translate x ω))
          (gradient (fun y => η y * orbit H ω y) x) := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          dsimp only
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          change _ = W (translate x ω) i *
            coordinateDerivative i (fun y => η y * orbit H ω y) x
          rw [coordinateDerivative_mul i η (orbit H ω) x
            (hη.differentiable (by simp) x) ((hH.2.1 ω).differentiable (by simp) x)]
          rw [← horizontalDerivative_translate]
          simp only [orbit]
          ring
      _ = -(∫ x, orbit h ω x * (η x * orbit H ω x)) := hw
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun x => by simp only [orbit]; ring
  have hexp := integral_congr_ae heq
  rw [integral_add (integrable_finsetSum Finset.univ
      (fun i _ => (hA i).integral_prod_right))
      (integrable_finsetSum Finset.univ (fun i _ => (hB i).integral_prod_right)),
    integral_finsetSum Finset.univ (fun i _ => (hA i).integral_prod_right),
    integral_finsetSum Finset.univ (fun i _ => (hB i).integral_prod_right),
    integral_neg] at hexp
  have hEA (i : Fin d) :
      (∫ ω, ∫ x, η x * (W (translate x ω) i *
        horizontalDerivative i H (translate x ω)) ∂volume ∂Q) =
      ∫ ω, W ω i * horizontalDerivative i H ω ∂Q := by
    simpa only [Pi.mul_apply, hη1, one_mul] using! integral_weighted_orbit Q hQ
      hη.continuous.measurable hηi ((hWim i).mul (hH.measurable_derivative i))
      ((hW i).integrable_mul (hH.memLp_derivative Q 2 i))
  have hEB (i : Fin d) :
      (∫ ω, ∫ x, coordinateDerivative i η x *
        (W (translate x ω) i * H (translate x ω)) ∂volume ∂Q) = 0 := by
    simpa only [Pi.mul_apply, c4Integral_coordinateDerivative_eq_zero hη hηc i, zero_mul]
      using! integral_weighted_orbit Q hQ (hηD i).measurable (hηDi i)
        ((hWim i).mul hH.1) ((hW i).integrable_mul (hH.memLp Q 2))
  have hEC : (∫ ω, ∫ x, η x * (h (translate x ω) * H (translate x ω)) ∂volume ∂Q) =
      ∫ ω, h ω * H ω ∂Q := by
    simpa only [Pi.mul_apply, hη1, one_mul] using! integral_weighted_orbit Q hQ
      hη.continuous.measurable hηi (hhm.mul hH.1) (hh.integrable_mul (hH.memLp Q 2))
  dsimp only [Prod.fst, Prod.snd] at hexp
  rw [hEC] at hexp
  simp only [hEA, hEB, Finset.sum_const_zero, add_zero] at hexp
  rw [integral_finsetSum (f := fun i ω => W ω i * horizontalDerivative i H ω) Finset.univ
    (fun i _ => (hW i).integrable_mul (hH.memLp_derivative Q 2 i))]
  exact hexp

private theorem c4WeakHorizontalDivergence_of_spatial {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {W : FieldPair d → Vec d} {h : FieldPair d → ℝ}
    (hWm : Measurable W) (hhm : Measurable h)
    (hW : ∀ i, MemLp (fun ω => W ω i) 2 Q) (hh : MemLp h 2 Q)
    (hweak : ∀ᵐ ω ∂Q, HasWeakDivergence Set.univ
      (fun x => W (translate x ω)) (orbit h ω)) :
    HasWeakHorizontalDivergence Q hQ W h := by
  exact weakHorizontalDivergence_of_core Q hQ hW hh fun _ hH =>
    c4StationarySpatialDivergence_integral_test Q hQ hWm hhm hW hh hweak hH

/-- A literal complex spatial divergence transfers to the full real horizontal
divergence after any real scalar projection. Local integrability follows from
the measurable stationary L2 representatives, rather than being assumed. -/
theorem c4SpatialDivergence_scalarProjection {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : Fin d → FieldPair d → ℂ) (h : FieldPair d → ℂ)
    (hFm : ∀ j, Measurable (F j)) (hhm : Measurable h)
    (hF : ∀ j, MemLp (F j) 2 Q) (hh : MemLp h 2 Q)
    (hweak : ∀ᵐ ω ∂Q, ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, ∑ j, F j (translate x ω) * (coordinateDerivative j φ x : ℂ)) =
        -(∫ x, h (translate x ω) * (φ x : ℂ)))
    (L : ℂ →L[ℝ] ℝ) :
    HasWeakHorizontalDivergence Q hQ (fun ω j => L (F j ω)) (fun ω => L (h ω)) := by
  apply c4WeakHorizontalDivergence_of_spatial Q hQ
    (Measurable.of_eval fun j => L.continuous.measurable.comp (hFm j))
    (L.continuous.measurable.comp hhm)
    (fun j => L.comp_memLp' (hF j)) (L.comp_memLp' hh)
  filter_upwards [hweak,
    ae_complex_function_orbit_memLp_on_all_compacts Q hQ hhm hh,
    ae_all_iff.mpr fun j => ae_complex_function_orbit_memLp_on_all_compacts Q hQ
      (hFm j) (hF j)] with ω hw hhω hFω
  have hlocal {u : Vec d → ℂ}
      (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u 2 (volume.restrict K)) :
      LocallyIntegrableOn (fun x => L (u x)) Set.univ volume := by
    rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro K hK
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact (L.comp_memLp' (hu K hK)).integrable one_le_two
  refine ⟨fun j => hlocal (hFω j), hlocal hhω, ?_⟩
  intro φ hφ
  have hi := integrable_spatial_mul_test hhω hφ.1.continuous hφ.2.1
  have hj (j : Fin d) : Integrable (fun x => F j (translate x ω) *
      (coordinateDerivative j φ x : ℂ)) volume := by
    simpa only [coordinateDerivative] using! integrable_spatial_mul_test (hFω j)
      ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφ.2.1.fderiv_apply ℝ (unitVector j))
  have he := congrArg L (hw φ hφ.1 hφ.2.1)
  rw [map_neg, ← L.integral_comp_comm (integrable_finsetSum _ fun j _ => hj j),
    ← L.integral_comp_comm hi] at he
  have hmul (z : ℂ) (r : ℝ) : L (z * (r : ℂ)) = L z * r := by
    simpa only [Complex.real_smul, smul_eq_mul, mul_comm] using L.map_smul r z
  simpa only [Measure.restrict_univ, dot, gradient, map_sum, hmul, orbit, Function.comp_apply] using! he

/-- The stationary complex divergence identity holds against every genuine
complex horizontal H1 test, including the backward homogeneous Gaussian. -/
theorem c4SpatialDivergence_pairing {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : Fin d → FieldPair d → ℂ) (h : FieldPair d → ℂ)
    (hFm : ∀ j, Measurable (F j)) (hhm : Measurable h)
    (hF : ∀ j, MemLp (F j) 2 Q) (hh : MemLp h 2 Q)
    (hweak : ∀ᵐ ω ∂Q, ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, ∑ j, F j (translate x ω) * (coordinateDerivative j φ x : ℂ)) =
        -(∫ x, h (translate x ω) * (φ x : ℂ)))
    (v : Lp ℂ 2 Q) (V : Fin d → Lp ℂ 2 Q)
    (hV : HasComplexHorizontalGradient Q hQ v V) :
    (∫ ω, ∑ j, F j ω * V j ω ∂Q) = -(∫ ω, h ω * v ω ∂Q) := by
  have hp (L K : ℂ →L[ℝ] ℝ) :
      (∫ ω, ∑ j, L (F j ω) * K (V j ω) ∂Q) =
        -(∫ ω, L (h ω) * K (v ω) ∂Q) := by
    let w := K.compLpL 2 Q v
    let W := fun j => K.compLpL 2 Q (V j)
    have hw : HasWeakHorizontalGradient Q hQ w (fun ω j => W j ω) := by
      refine ⟨(Lp.memLp w).integrable one_le_two,
        fun j => (Lp.memLp (W j)).integrable one_le_two, ?_⟩
      intro j z Z _ hz
      have he := horizontalGenerators_integration_by_parts Q hQ j z Z w (W j)
        hz ((hV j).scalarProjection K)
      simpa only [mul_comm] using he.2.2
    have he := Entropy.sum_integral_mul_eq_neg_of_div hQ
      (Lp.stronglyMeasurable w).measurable (Lp.memLp w)
      (Measurable.of_eval fun j => (Lp.stronglyMeasurable (W j)).measurable)
      (fun j => Lp.memLp (W j)) hw
      (c4SpatialDivergence_scalarProjection Q hQ F h hFm hhm hF hh hweak L)
      (fun j => L.comp_memLp' (hF j)) (L.comp_memLp' hh)
    rw [← integral_finsetSum Finset.univ (f := fun j ω => L (F j ω) * W j ω)
      (fun j _ => (L.comp_memLp' (hF j)).integrable_mul (Lp.memLp (W j)))] at he
    have heleft : (fun ω => ∑ j, L (F j ω) * W j ω) =ᵐ[Q]
        fun ω => ∑ j, L (F j ω) * K (V j ω) := by
      filter_upwards [ae_all_iff.mpr fun j => K.coeFn_compLpL (V j)] with ω hω
      simp only [W, hω]
    have heright : (fun ω => L (h ω) * w ω) =ᵐ[Q]
        fun ω => L (h ω) * K (v ω) := by
      filter_upwards [K.coeFn_compLpL v] with ω hω
      simp only [w, hω]
    rw [integral_congr_ae heleft, integral_congr_ae heright] at he
    exact he
  have hi (L K : ℂ →L[ℝ] ℝ) :
      Integrable (fun ω => ∑ j, L (F j ω) * K (V j ω)) Q :=
    integrable_finsetSum _ fun j _ =>
      (L.comp_memLp' (hF j)).integrable_mul (K.comp_memLp' (Lp.memLp (V j)))
  have hhint (L K : ℂ →L[ℝ] ℝ) : Integrable (fun ω => L (h ω) * K (v ω)) Q :=
    (L.comp_memLp' hh).integrable_mul (K.comp_memLp' (Lp.memLp v))
  have hleft : Integrable (fun ω => ∑ j, F j ω * V j ω) Q :=
    integrable_finsetSum Finset.univ fun j _ =>
    (hF j).integrable_mul (Lp.memLp (V j))
  have hright : Integrable (fun ω => h ω * v ω) Q := hh.integrable_mul (Lp.memLp v)
  have hsumR (f : Fin d → ℂ) : (∑ j, f j).re = ∑ j, (f j).re :=
    map_sum Complex.reCLM _ _
  have hsumI (f : Fin d → ℂ) : (∑ j, f j).im = ∑ j, (f j).im :=
    map_sum Complex.imCLM _ _
  have hrr := hp Complex.reCLM Complex.reCLM
  have hirr := hi Complex.reCLM Complex.reCLM
  have hhrr := hhint Complex.reCLM Complex.reCLM
  simp only [Complex.reCLM_apply] at hrr hirr hhrr
  have hii := hp Complex.imCLM Complex.imCLM
  have hiii := hi Complex.imCLM Complex.imCLM
  have hhii := hhint Complex.imCLM Complex.imCLM
  simp only [Complex.imCLM_apply] at hii hiii hhii
  have hri := hp Complex.reCLM Complex.imCLM
  have hiri := hi Complex.reCLM Complex.imCLM
  have hhri := hhint Complex.reCLM Complex.imCLM
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hri hiri hhri
  have hir := hp Complex.imCLM Complex.reCLM
  have hiir := hi Complex.imCLM Complex.reCLM
  have hhir := hhint Complex.imCLM Complex.reCLM
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hir hiir hhir
  apply Complex.ext
  · have hl : (∫ ω, (∑ j, F j ω * V j ω).re ∂Q) =
        (∫ ω, ∑ j, F j ω * V j ω ∂Q).re := Complex.reCLM.integral_comp_comm hleft
    have hr : (∫ ω, (h ω * v ω).re ∂Q) =
        (∫ ω, h ω * v ω ∂Q).re := Complex.reCLM.integral_comp_comm hright
    rw [Complex.neg_re, ← hl, ← hr]
    simp only [hsumR, Complex.mul_re,
      Finset.sum_sub_distrib]
    rw [integral_sub hirr hiii,
      integral_sub hhrr hhii]
    rw [hrr, hii]
    ring
  · have hl : (∫ ω, (∑ j, F j ω * V j ω).im ∂Q) =
        (∫ ω, ∑ j, F j ω * V j ω ∂Q).im := Complex.imCLM.integral_comp_comm hleft
    have hr : (∫ ω, (h ω * v ω).im ∂Q) =
        (∫ ω, h ω * v ω ∂Q).im := Complex.imCLM.integral_comp_comm hright
    rw [Complex.neg_im, ← hl, ← hr]
    simp only [hsumI, Complex.mul_im,
      Finset.sum_add_distrib]
    rw [integral_add hiri hiir,
      integral_add hhri hhir]
    rw [hri, hir]
    ring

/-- Algebraic passage from the centered spatial equation to the stationary
complex divergence pairing. All source and flux representatives remain literal. -/
theorem c4CenteredEquation_stationaryFlux {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (A : Fin d → Fin d → ℂ) (i : Fin d) (ξ κ : ℂ)
    (G J : Fin d → Lp ℂ 2 Q) (V : Lp ℂ 2 Q)
    (hsp : ∀ᵐ ω ∂Q, ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, V (translate x ω) * (φ x : ℂ)) +
        (1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k,
          A j k * G k (translate x ω) * (coordinateDerivative j φ x : ℂ)) -
        ξ * (∫ x, (∑ j, A j i * G j (translate x ω)) * (φ x : ℂ)) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j,
        J j (translate x ω) * (coordinateDerivative j φ x : ℂ)) +
      κ * (∫ x, (J i (translate x ω) - ∫ ω', J i ω' ∂Q) * (φ x : ℂ)))
    (v : Lp ℂ 2 Q) (W : Fin d → Lp ℂ 2 Q)
    (hW : HasComplexHorizontalGradient Q hQ v W) :
    (∫ ω, ∑ j, ((∑ k, A j k * G k ω) + J j ω) * W j ω ∂Q) =
      -(∫ ω, (2 : ℂ) * (V ω - ξ * (∑ j, A j i * G j ω) -
        κ * (J i ω - ∫ ω', J i ω' ∂Q)) * v ω ∂Q) := by
  let F := fun j ω => (∑ k, A j k * G k ω) + J j ω
  let H := fun ω => (2 : ℂ) * (V ω - ξ * (∑ j, A j i * G j ω) -
    κ * (J i ω - ∫ ω', J i ω' ∂Q))
  have hGm (j : Fin d) : Measurable (G j) := (Lp.stronglyMeasurable _).measurable
  have hJm (j : Fin d) : Measurable (J j) := (Lp.stronglyMeasurable _).measurable
  have hVm : Measurable V := (Lp.stronglyMeasurable _).measurable
  have hFm (j : Fin d) : Measurable (F j) :=
    (Finset.measurable_sum _ fun k _ => measurable_const.mul (hGm k)).add (hJm j)
  have hHm : Measurable H := measurable_const.mul
    ((hVm.sub (measurable_const.mul (Finset.measurable_sum _ fun j _ =>
      measurable_const.mul (hGm j)))).sub
      (measurable_const.mul ((hJm i).sub measurable_const)))
  have hF (j : Fin d) : MemLp (F j) 2 Q :=
    (memLp_finsetSum _ fun k _ => (Lp.memLp (G k)).const_mul (A j k)).add (Lp.memLp (J j))
  have hH : MemLp H 2 Q :=
    (((Lp.memLp V).sub ((memLp_finsetSum _ fun j _ =>
      (Lp.memLp (G j)).const_mul (A j i)).const_mul ξ)).sub
        (((Lp.memLp (J i)).sub (memLp_const _)).const_mul κ)).const_mul 2
  apply c4SpatialDivergence_pairing Q hQ F H hFm hHm hF hH _ v W hW
  filter_upwards [hsp,
    ae_complex_function_orbit_memLp_on_all_compacts Q hQ hVm (Lp.memLp V),
    ae_all_iff.mpr fun j => ae_complex_function_orbit_memLp_on_all_compacts Q hQ
      (hGm j) (Lp.memLp (G j)),
    ae_all_iff.mpr fun j => ae_complex_function_orbit_memLp_on_all_compacts Q hQ
      (hJm j) (Lp.memLp (J j))] with ω hw hVω hGω hJω
  intro φ hφ hφc
  have hVG := integrable_spatial_mul_test hVω hφ.continuous hφc
  have hGG (j : Fin d) := integrable_spatial_mul_test (hGω j) hφ.continuous hφc
  have hJG := integrable_spatial_mul_test (hJω i) hφ.continuous hφc
  have hGD (j k : Fin d) : Integrable (fun x => A j k * G k (translate x ω) *
      (coordinateDerivative j φ x : ℂ)) volume := by
    simpa only [mul_assoc, coordinateDerivative] using!
      (integrable_spatial_mul_test (hGω k)
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hφc.fderiv_apply ℝ (unitVector j))).const_mul (A j k)
  have hJD (j : Fin d) : Integrable (fun x => J j (translate x ω) *
      (coordinateDerivative j φ x : ℂ)) volume := by
    simpa only [coordinateDerivative] using! integrable_spatial_mul_test (hJω j)
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ (unitVector j))
  have hAG : Integrable (fun x => (∑ j, A j i * G j (translate x ω)) * (φ x : ℂ)) volume := by
    simp_rw [Finset.sum_mul]
    exact integrable_finsetSum _ fun j _ => by
      simpa only [mul_assoc] using! (hGG j).const_mul (A j i)
  have hCG : Integrable (fun x => (J i (translate x ω) - ∫ ω', J i ω' ∂Q) * (φ x : ℂ)) volume := by
    simpa only [Pi.sub_apply, sub_mul] using! hJG.sub
      (((Complex.continuous_ofReal.comp hφ.continuous).integrable_of_hasCompactSupport
        (hφc.comp_left rfl)).const_mul (∫ ω', J i ω' ∂Q))
  have he := hw φ hφ hφc
  have hFexpand :
      (∫ x, ∑ j, F j (translate x ω) * (coordinateDerivative j φ x : ℂ)) =
      (∫ x, ∑ j, ∑ k, A j k * G k (translate x ω) * (coordinateDerivative j φ x : ℂ)) +
      (∫ x, ∑ j, J j (translate x ω) * (coordinateDerivative j φ x : ℂ)) := by
    simp only [F, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    exact integral_add (integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => hGD j k) (integrable_finsetSum _ fun j _ => hJD j)
  have hHexpand : (∫ x, H (translate x ω) * (φ x : ℂ)) =
      2 * ((∫ x, V (translate x ω) * (φ x : ℂ)) -
        ξ * (∫ x, (∑ j, A j i * G j (translate x ω)) * (φ x : ℂ)) -
        κ * (∫ x, (J i (translate x ω) - ∫ ω', J i ω' ∂Q) * (φ x : ℂ))) := by
    have hfun : (fun x => H (translate x ω) * (φ x : ℂ)) =
        fun x => 2 * ((V (translate x ω) * (φ x : ℂ) -
          ξ * ((∑ j, A j i * G j (translate x ω)) * (φ x : ℂ))) -
          κ * ((J i (translate x ω) - ∫ ω', J i ω' ∂Q) * (φ x : ℂ))) := by
      funext x
      dsimp only [H]
      ring
    have hsub : Integrable (fun x => V (translate x ω) * (φ x : ℂ) -
        ξ * ((∑ j, A j i * G j (translate x ω)) * (φ x : ℂ))) volume :=
      hVG.sub (hAG.const_mul ξ)
    rw [hfun, integral_const_mul, integral_sub hsub (hCG.const_mul κ),
      integral_sub hVG (hAG.const_mul ξ), integral_const_mul, integral_const_mul]
  rw [hFexpand, hHexpand]
  linear_combination 2 * he

/-- The centered zeroth-order flux coefficient is zero for the conservative
transpose endpoint and is the physical force for every forward endpoint. -/
def c4EndpointSourceCoefficient {d : ℕ} (ν : EndpointIndex d) (ζ : ℂ) : ℂ :=
  match ν with | .inr true => 0 | _ => ζ

private theorem c4EndpointSource_mul {d : ℕ} (ν : EndpointIndex d) (ζ z : ℂ) :
    (match ν with | .inr true => 0 | _ => ζ * z) =
      c4EndpointSourceCoefficient ν ζ * z := by
  cases ν with
  | inl j => rfl
  | inr b => cases b <;> simp only [c4EndpointSourceCoefficient, zero_mul]

section StationaryEndpoint

variable (hc : Blueprint.node_e_u3A_centered_u2D_equationsStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)

include hc hQ hβ ha hμ hP hPdag

/-- The centered-equation hypothesis yields a stationary flux identity for the
actual indexed endpoint, with its actual derivative and unique physical flux. -/
theorem c4IndexedEndpoint_stationaryFlux
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
    let ξ := (endpointDriftSign ν : ℂ) * ζ
    let κ := c4EndpointSourceCoefficient ν ζ
    ∃ (G J : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q)),
      IsEndpointWeakFlux hd Q ν ζ a U G J ∧
      HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal) V (t : ℝ) ∧
      ∀ (v : Lp ℂ 2 (reducedLaw Q)) (W : Fin d → Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v W →
        (∫ ω, ∑ j, ((∑ k, (homogenizedCoefficient Q j k : ℂ) * G k ω) + J j ω) * W j ω
          ∂reducedLaw Q) =
        -(∫ ω, (2 : ℂ) * (V ω - ξ * (∑ j, (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) *
          G j ω) - κ * (J ⟨0, by omega⟩ ω - ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q)) *
          v ω ∂reducedLaw Q) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨G, J, V, hflux, hV, _, hsp⟩ :=
    hc d hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht
  refine ⟨G, J, V, hflux, hV, ?_⟩
  intro v W hW
  have hsp' := hsp.mono fun ω hω φ hφ hφc =>
    (hω φ hφ hφc).trans (congrArg
      (fun z : ℂ => -(1 / 2 : ℂ) * (∫ x, ∑ j : Fin d,
        J j (translate x ω) * (coordinateDerivative j φ x : ℂ)) + z)
      (c4EndpointSource_mul ν ζ (∫ x,
        (J ⟨0, by omega⟩ (translate x ω) - ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) *
          (φ x : ℂ))))
  have he := c4CenteredEquation_stationaryFlux (reducedLaw Q) (reducedLaw_stationary Q)
    (fun j k => (homogenizedCoefficient Q j k : ℂ)) ⟨0, by omega⟩
    ((endpointDriftSign ν : ℂ) * ζ) (c4EndpointSourceCoefficient ν ζ)
    G J V hsp' v W hW
  simpa only using! he

end StationaryEndpoint
end EinsteinFull
